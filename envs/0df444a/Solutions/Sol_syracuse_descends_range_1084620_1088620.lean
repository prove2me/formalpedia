-- Prove2me | solution 1 for syracuse_descends_range_1084620_1088620
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:34.554674+00:00
-- url     : https://prove2.me/submissions/d652f90d-2fed-44ab-adc2-ee8624bdc87a

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


theorem B1835021 : Blo 1084620 1835021 := bbase (se 3 (by rfl) ⟨344066, by rfl⟩ : syracuseStep 1835021 = 688133) (by norm_num)
theorem B1376281 : Blo 1084620 1376281 := bbase (se 2 (by rfl) ⟨516105, by rfl⟩ : syracuseStep 1376281 = 1032211) (by norm_num)
theorem B2064437 : Blo 1084620 2064437 := bbase (se 5 (by rfl) ⟨96770, by rfl⟩ : syracuseStep 2064437 = 193541) (by norm_num)
theorem B2752613 : Blo 1084620 2752613 := bbase (se 4 (by rfl) ⟨258057, by rfl⟩ : syracuseStep 2752613 = 516115) (by norm_num)
theorem B1835149 : Blo 1084620 1835149 := bbase (se 3 (by rfl) ⟨344090, by rfl⟩ : syracuseStep 1835149 = 688181) (by norm_num)
theorem B4128965 : Blo 1084620 4128965 := bbase (se 4 (by rfl) ⟨387090, by rfl⟩ : syracuseStep 4128965 = 774181) (by norm_num)
theorem B1376453 : Blo 1084620 1376453 := bbase (se 4 (by rfl) ⟨129042, by rfl⟩ : syracuseStep 1376453 = 258085) (by norm_num)
theorem B1835237 : Blo 1084620 1835237 := bbase (se 4 (by rfl) ⟨172053, by rfl⟩ : syracuseStep 1835237 = 344107) (by norm_num)
theorem B1376509 : Blo 1084620 1376509 := bbase (se 3 (by rfl) ⟨258095, by rfl⟩ : syracuseStep 1376509 = 516191) (by norm_num)
theorem B2752805 : Blo 1084620 2752805 := bbase (se 4 (by rfl) ⟨258075, by rfl⟩ : syracuseStep 2752805 = 516151) (by norm_num)
theorem B3670325 : Blo 1084620 3670325 := bbase (se 5 (by rfl) ⟨172046, by rfl⟩ : syracuseStep 3670325 = 344093) (by norm_num)
theorem B6193493 : Blo 1084620 6193493 := bbase (se 10 (by rfl) ⟨9072, by rfl⟩ : syracuseStep 6193493 = 18145) (by norm_num)
theorem B1376605 : Blo 1084620 1376605 := bbase (se 3 (by rfl) ⟨258113, by rfl⟩ : syracuseStep 1376605 = 516227) (by norm_num)
theorem B1835365 : Blo 1084620 1835365 := bbase (se 4 (by rfl) ⟨172065, by rfl⟩ : syracuseStep 1835365 = 344131) (by norm_num)
theorem B1835453 : Blo 1084620 1835453 := bbase (se 3 (by rfl) ⟨344147, by rfl⟩ : syracuseStep 1835453 = 688295) (by norm_num)
theorem B1376777 : Blo 1084620 1376777 := bbase (se 2 (by rfl) ⟨516291, by rfl⟩ : syracuseStep 1376777 = 1032583) (by norm_num)
theorem B1835581 : Blo 1084620 1835581 := bbase (se 3 (by rfl) ⟨344171, by rfl⟩ : syracuseStep 1835581 = 688343) (by norm_num)
theorem B1376833 : Blo 1084620 1376833 := bbase (se 2 (by rfl) ⟨516312, by rfl⟩ : syracuseStep 1376833 = 1032625) (by norm_num)
theorem B9273973 : Blo 1084620 9273973 := bbase (se 5 (by rfl) ⟨434717, by rfl⟩ : syracuseStep 9273973 = 869435) (by norm_num)
theorem B2753149 : Blo 1084620 2753149 := bbase (se 3 (by rfl) ⟨516215, by rfl⟩ : syracuseStep 2753149 = 1032431) (by norm_num)
theorem B1835669 : Blo 1084620 1835669 := bbase (se 6 (by rfl) ⟨43023, by rfl⟩ : syracuseStep 1835669 = 86047) (by norm_num)
theorem B1376929 : Blo 1084620 1376929 := bbase (se 2 (by rfl) ⟨516348, by rfl⟩ : syracuseStep 1376929 = 1032697) (by norm_num)
theorem B1737397 : Blo 1084620 1737397 := bbase (se 5 (by rfl) ⟨81440, by rfl⟩ : syracuseStep 1737397 = 162881) (by norm_num)
theorem B1671869 : Blo 1084620 1671869 := bbase (se 3 (by rfl) ⟨313475, by rfl⟩ : syracuseStep 1671869 = 626951) (by norm_num)
theorem B3670757 : Blo 1084620 3670757 := bbase (se 4 (by rfl) ⟨344133, by rfl⟩ : syracuseStep 3670757 = 688267) (by norm_num)
theorem B2753261 : Blo 1084620 2753261 := bbase (se 3 (by rfl) ⟨516236, by rfl⟩ : syracuseStep 2753261 = 1032473) (by norm_num)
theorem B1835797 : Blo 1084620 1835797 := bbase (se 6 (by rfl) ⟨43026, by rfl⟩ : syracuseStep 1835797 = 86053) (by norm_num)
theorem B2065189 : Blo 1084620 2065189 := bbase (se 4 (by rfl) ⟨193611, by rfl⟩ : syracuseStep 2065189 = 387223) (by norm_num)
theorem B1377101 : Blo 1084620 1377101 := bbase (se 3 (by rfl) ⟨258206, by rfl⟩ : syracuseStep 1377101 = 516413) (by norm_num)
theorem B5505893 : Blo 1084620 5505893 := bbase (se 4 (by rfl) ⟨516177, by rfl⟩ : syracuseStep 5505893 = 1032355) (by norm_num)
theorem B1835885 : Blo 1084620 1835885 := bbase (se 3 (by rfl) ⟨344228, by rfl⟩ : syracuseStep 1835885 = 688457) (by norm_num)
theorem B1377157 : Blo 1084620 1377157 := bbase (se 4 (by rfl) ⟨129108, by rfl⟩ : syracuseStep 1377157 = 258217) (by norm_num)
theorem B2753453 : Blo 1084620 2753453 := bbase (se 3 (by rfl) ⟨516272, by rfl⟩ : syracuseStep 2753453 = 1032545) (by norm_num)
theorem B2065333 : Blo 1084620 2065333 := bbase (se 5 (by rfl) ⟨96812, by rfl⟩ : syracuseStep 2065333 = 193625) (by norm_num)
theorem B1377253 : Blo 1084620 1377253 := bbase (se 4 (by rfl) ⟨129117, by rfl⟩ : syracuseStep 1377253 = 258235) (by norm_num)
theorem B1836013 : Blo 1084620 1836013 := bbase (se 3 (by rfl) ⟨344252, by rfl⟩ : syracuseStep 1836013 = 688505) (by norm_num)
theorem B1836101 : Blo 1084620 1836101 := bbase (se 4 (by rfl) ⟨172134, by rfl⟩ : syracuseStep 1836101 = 344269) (by norm_num)
theorem B2065493 : Blo 1084620 2065493 := bbase (se 8 (by rfl) ⟨12102, by rfl⟩ : syracuseStep 2065493 = 24205) (by norm_num)
theorem B1377425 : Blo 1084620 1377425 := bbase (se 2 (by rfl) ⟨516534, by rfl⟩ : syracuseStep 1377425 = 1033069) (by norm_num)
theorem B3671189 : Blo 1084620 3671189 := bbase (se 6 (by rfl) ⟨86043, by rfl⟩ : syracuseStep 3671189 = 172087) (by norm_num)
theorem B1836229 : Blo 1084620 1836229 := bbase (se 4 (by rfl) ⟨172146, by rfl⟩ : syracuseStep 1836229 = 344293) (by norm_num)
theorem B1377481 : Blo 1084620 1377481 := bbase (se 2 (by rfl) ⟨516555, by rfl⟩ : syracuseStep 1377481 = 1033111) (by norm_num)
theorem B2065637 : Blo 1084620 2065637 := bbase (se 4 (by rfl) ⟨193653, by rfl⟩ : syracuseStep 2065637 = 387307) (by norm_num)
theorem B2753797 : Blo 1084620 2753797 := bbase (se 4 (by rfl) ⟨258168, by rfl⟩ : syracuseStep 2753797 = 516337) (by norm_num)
theorem B1836317 : Blo 1084620 1836317 := bbase (se 3 (by rfl) ⟨344309, by rfl⟩ : syracuseStep 1836317 = 688619) (by norm_num)
theorem B1377577 : Blo 1084620 1377577 := bbase (se 2 (by rfl) ⟨516591, by rfl⟩ : syracuseStep 1377577 = 1033183) (by norm_num)
theorem B4130149 : Blo 1084620 4130149 := bbase (se 4 (by rfl) ⟨387201, by rfl⟩ : syracuseStep 4130149 = 774403) (by norm_num)
theorem B2753909 : Blo 1084620 2753909 := bbase (se 5 (by rfl) ⟨129089, by rfl⟩ : syracuseStep 2753909 = 258179) (by norm_num)
theorem B1836445 : Blo 1084620 1836445 := bbase (se 3 (by rfl) ⟨344333, by rfl⟩ : syracuseStep 1836445 = 688667) (by norm_num)
theorem B1377749 : Blo 1084620 1377749 := bbase (se 7 (by rfl) ⟨16145, by rfl⟩ : syracuseStep 1377749 = 32291) (by norm_num)
theorem B6194677 : Blo 1084620 6194677 := bbase (se 5 (by rfl) ⟨290375, by rfl⟩ : syracuseStep 6194677 = 580751) (by norm_num)
theorem B1836533 : Blo 1084620 1836533 := bbase (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) (by norm_num)
theorem B2065925 : Blo 1084620 2065925 := bbase (se 4 (by rfl) ⟨193680, by rfl⟩ : syracuseStep 2065925 = 387361) (by norm_num)
theorem B2754101 : Blo 1084620 2754101 := bbase (se 5 (by rfl) ⟨129098, by rfl⟩ : syracuseStep 2754101 = 258197) (by norm_num)
theorem B3671621 : Blo 1084620 3671621 := bbase (se 4 (by rfl) ⟨344214, by rfl⟩ : syracuseStep 3671621 = 688429) (by norm_num)
theorem B1836661 : Blo 1084620 1836661 := bbase (se 5 (by rfl) ⟨86093, by rfl⟩ : syracuseStep 1836661 = 172187) (by norm_num)
theorem B4130453 : Blo 1084620 4130453 := bbase (se 6 (by rfl) ⟨96807, by rfl⟩ : syracuseStep 4130453 = 193615) (by norm_num)
theorem B2066077 : Blo 1084620 2066077 := bbase (se 3 (by rfl) ⟨387389, by rfl⟩ : syracuseStep 2066077 = 774779) (by norm_num)
theorem B1836749 : Blo 1084620 1836749 := bbase (se 3 (by rfl) ⟨344390, by rfl⟩ : syracuseStep 1836749 = 688781) (by norm_num)
theorem B1738525 : Blo 1084620 1738525 := bbase (se 3 (by rfl) ⟨325973, by rfl⟩ : syracuseStep 1738525 = 651947) (by norm_num)
theorem B1836877 : Blo 1084620 1836877 := bbase (se 3 (by rfl) ⟨344414, by rfl⟩ : syracuseStep 1836877 = 688829) (by norm_num)
theorem B2754445 : Blo 1084620 2754445 := bbase (se 3 (by rfl) ⟨516458, by rfl⟩ : syracuseStep 2754445 = 1032917) (by norm_num)
theorem B1836965 : Blo 1084620 1836965 := bbase (se 4 (by rfl) ⟨172215, by rfl⟩ : syracuseStep 1836965 = 344431) (by norm_num)
theorem B2066381 : Blo 1084620 2066381 := bbase (se 3 (by rfl) ⟨387446, by rfl⟩ : syracuseStep 2066381 = 774893) (by norm_num)
theorem B3672053 : Blo 1084620 3672053 := bbase (se 5 (by rfl) ⟨172127, by rfl⟩ : syracuseStep 3672053 = 344255) (by norm_num)
theorem B2754557 : Blo 1084620 2754557 := bbase (se 3 (by rfl) ⟨516479, by rfl⟩ : syracuseStep 2754557 = 1032959) (by norm_num)
theorem B5507189 : Blo 1084620 5507189 := bbase (se 5 (by rfl) ⟨258149, by rfl⟩ : syracuseStep 5507189 = 516299) (by norm_num)
theorem B2754749 : Blo 1084620 2754749 := bbase (se 3 (by rfl) ⟨516515, by rfl⟩ : syracuseStep 2754749 = 1033031) (by norm_num)
theorem B1738973 : Blo 1084620 1738973 := bbase (se 3 (by rfl) ⟨326057, by rfl⟩ : syracuseStep 1738973 = 652115) (by norm_num)
theorem B3475781 : Blo 1084620 3475781 := bbase (se 4 (by rfl) ⟨325854, by rfl⟩ : syracuseStep 3475781 = 651709) (by norm_num)
theorem B3672485 : Blo 1084620 3672485 := bbase (se 4 (by rfl) ⟨344295, by rfl⟩ : syracuseStep 3672485 = 688591) (by norm_num)
theorem B5212613 : Blo 1084620 5212613 := bbase (se 4 (by rfl) ⟨488682, by rfl⟩ : syracuseStep 5212613 = 977365) (by norm_num)
theorem B2755093 : Blo 1084620 2755093 := bbase (se 6 (by rfl) ⟨64572, by rfl⟩ : syracuseStep 2755093 = 129145) (by norm_num)
theorem B9275957 : Blo 1084620 9275957 := bbase (se 5 (by rfl) ⟨434810, by rfl⟩ : syracuseStep 9275957 = 869621) (by norm_num)
theorem B2787901 : Blo 1084620 2787901 := bbase (se 3 (by rfl) ⟨522731, by rfl⟩ : syracuseStep 2787901 = 1045463) (by norm_num)
theorem B2755205 : Blo 1084620 2755205 := bbase (se 4 (by rfl) ⟨258300, by rfl⟩ : syracuseStep 2755205 = 516601) (by norm_num)
theorem B2755397 : Blo 1084620 2755397 := bbase (se 4 (by rfl) ⟨258318, by rfl⟩ : syracuseStep 2755397 = 516637) (by norm_num)
theorem B3672917 : Blo 1084620 3672917 := bbase (se 9 (by rfl) ⟨10760, by rfl⟩ : syracuseStep 3672917 = 21521) (by norm_num)
theorem B1674373 : Blo 1084620 1674373 := bbase (se 4 (by rfl) ⟨156972, by rfl⟩ : syracuseStep 1674373 = 313945) (by norm_num)
theorem B3673349 : Blo 1084620 3673349 := bbase (se 4 (by rfl) ⟨344376, by rfl⟩ : syracuseStep 3673349 = 688753) (by norm_num)
theorem B2198909 : Blo 1084620 2198909 := bbase (se 3 (by rfl) ⟨412295, by rfl⟩ : syracuseStep 2198909 = 824591) (by norm_num)
theorem B5508485 : Blo 1084620 5508485 := bbase (se 4 (by rfl) ⟨516420, by rfl⟩ : syracuseStep 5508485 = 1032841) (by norm_num)
theorem B6196661 : Blo 1084620 6196661 := bbase (se 5 (by rfl) ⟨290468, by rfl⟩ : syracuseStep 6196661 = 580937) (by norm_num)
theorem B1412597 : Blo 1084620 1412597 := bbase (se 5 (by rfl) ⟨66215, by rfl⟩ : syracuseStep 1412597 = 132431) (by norm_num)
theorem B29724245 : Blo 1084620 29724245 := bbase (se 8 (by rfl) ⟨174165, by rfl⟩ : syracuseStep 29724245 = 348331) (by norm_num)
theorem B3477125 : Blo 1084620 3477125 := bbase (se 4 (by rfl) ⟨325980, by rfl⟩ : syracuseStep 3477125 = 651961) (by norm_num)
theorem B3673781 : Blo 1084620 3673781 := bbase (se 5 (by rfl) ⟨172208, by rfl⟩ : syracuseStep 3673781 = 344417) (by norm_num)
theorem B1740485 : Blo 1084620 1740485 := bbase (se 4 (by rfl) ⟨163170, by rfl⟩ : syracuseStep 1740485 = 326341) (by norm_num)
theorem B4132565 : Blo 1084620 4132565 := bbase (se 7 (by rfl) ⟨48428, by rfl⟩ : syracuseStep 4132565 = 96857) (by norm_num)
theorem B9899765 : Blo 1084620 9899765 := bbase (se 5 (by rfl) ⟨464051, by rfl⟩ : syracuseStep 9899765 = 928103) (by norm_num)
theorem B7835413 : Blo 1084620 7835413 := bbase (se 6 (by rfl) ⟨183642, by rfl⟩ : syracuseStep 7835413 = 367285) (by norm_num)
theorem B1740613 : Blo 1084620 1740613 := bbase (se 4 (by rfl) ⟨163182, by rfl⟩ : syracuseStep 1740613 = 326365) (by norm_num)
theorem B1118053 : Blo 1084620 1118053 := bbase (se 4 (by rfl) ⟨104817, by rfl⟩ : syracuseStep 1118053 = 209635) (by norm_num)
theorem B35229653 : Blo 1084620 35229653 := bbase (se 7 (by rfl) ⟨412847, by rfl⟩ : syracuseStep 35229653 = 825695) (by norm_num)
theorem B4132853 : Blo 1084620 4132853 := bbase (se 5 (by rfl) ⟨193727, by rfl⟩ : syracuseStep 4132853 = 387455) (by norm_num)
theorem B1544341 : Blo 1084620 1544341 := bbase (se 6 (by rfl) ⟨36195, by rfl⟩ : syracuseStep 1544341 = 72391) (by norm_num)
theorem B14094485 : Blo 1084620 14094485 := bbase (se 6 (by rfl) ⟨330339, by rfl⟩ : syracuseStep 14094485 = 660679) (by norm_num)
theorem B4526293 : Blo 1084620 4526293 := bbase (se 7 (by rfl) ⟨53042, by rfl⟩ : syracuseStep 4526293 = 106085) (by norm_num)
theorem B9539797 : Blo 1084620 9539797 := bbase (se 7 (by rfl) ⟨111794, by rfl⟩ : syracuseStep 9539797 = 223589) (by norm_num)
theorem B2789893 : Blo 1084620 2789893 := bbase (se 4 (by rfl) ⟨261552, by rfl⟩ : syracuseStep 2789893 = 523105) (by norm_num)
theorem B1544717 : Blo 1084620 1544717 := bbase (se 3 (by rfl) ⟨289634, by rfl⟩ : syracuseStep 1544717 = 579269) (by norm_num)
theorem B5509781 : Blo 1084620 5509781 := bbase (se 6 (by rfl) ⟨129135, by rfl⟩ : syracuseStep 5509781 = 258271) (by norm_num)
theorem B8262485 : Blo 1084620 8262485 := bbase (se 9 (by rfl) ⟨24206, by rfl⟩ : syracuseStep 8262485 = 48413) (by norm_num)
theorem B27858005 : Blo 1084620 27858005 := bbase (se 8 (by rfl) ⟨163230, by rfl⟩ : syracuseStep 27858005 = 326461) (by norm_num)
theorem B1741997 : Blo 1084620 1741997 := bbase (se 3 (by rfl) ⟨326624, by rfl⟩ : syracuseStep 1741997 = 653249) (by norm_num)
theorem B6952405 : Blo 1084620 6952405 := bbase (se 7 (by rfl) ⟨81473, by rfl⟩ : syracuseStep 6952405 = 162947) (by norm_num)
theorem B2201165 : Blo 1084620 2201165 := bbase (se 3 (by rfl) ⟨412718, by rfl⟩ : syracuseStep 2201165 = 825437) (by norm_num)
theorem B3479125 : Blo 1084620 3479125 := bbase (se 8 (by rfl) ⟨20385, by rfl⟩ : syracuseStep 3479125 = 40771) (by norm_num)
theorem B6198869 : Blo 1084620 6198869 := bbase (se 8 (by rfl) ⟨36321, by rfl⟩ : syracuseStep 6198869 = 72643) (by norm_num)
theorem B1546141 : Blo 1084620 1546141 := bbase (se 3 (by rfl) ⟨289901, by rfl⟩ : syracuseStep 1546141 = 579803) (by norm_num)
theorem B5511077 : Blo 1084620 5511077 := bbase (se 4 (by rfl) ⟨516663, by rfl⟩ : syracuseStep 5511077 = 1033327) (by norm_num)
theorem B1742933 : Blo 1084620 1742933 := bbase (se 8 (by rfl) ⟨10212, by rfl⟩ : syracuseStep 1742933 = 20425) (by norm_num)
theorem B4954229 : Blo 1084620 4954229 := bbase (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) (by norm_num)
theorem B2201861 : Blo 1084620 2201861 := bbase (se 4 (by rfl) ⟨206424, by rfl⟩ : syracuseStep 2201861 = 412849) (by norm_num)
theorem B1546733 : Blo 1084620 1546733 := bbase (se 3 (by rfl) ⟨290012, by rfl⟩ : syracuseStep 1546733 = 580025) (by norm_num)
theorem B1546813 : Blo 1084620 1546813 := bbase (se 3 (by rfl) ⟨290027, by rfl⟩ : syracuseStep 1546813 = 580055) (by norm_num)
theorem B1546933 : Blo 1084620 1546933 := bbase (se 5 (by rfl) ⟨72512, by rfl⟩ : syracuseStep 1546933 = 145025) (by norm_num)
theorem B1743581 : Blo 1084620 1743581 := bbase (se 3 (by rfl) ⟨326921, by rfl⟩ : syracuseStep 1743581 = 653843) (by norm_num)
theorem B1547029 : Blo 1084620 1547029 := bbase (se 6 (by rfl) ⟨36258, by rfl⟩ : syracuseStep 1547029 = 72517) (by norm_num)
theorem B4234133 : Blo 1084620 4234133 := bbase (se 6 (by rfl) ⟨99237, by rfl⟩ : syracuseStep 4234133 = 198475) (by norm_num)
theorem B8919989 : Blo 1084620 8919989 := bbase (se 5 (by rfl) ⟨418124, by rfl⟩ : syracuseStep 8919989 = 836249) (by norm_num)
theorem B1547525 : Blo 1084620 1547525 := bbase (se 4 (by rfl) ⟨145080, by rfl⟩ : syracuseStep 1547525 = 290161) (by norm_num)
theorem B10722709 : Blo 1084620 10722709 := bbase (se 6 (by rfl) ⟨251313, by rfl⟩ : syracuseStep 10722709 = 502627) (by norm_num)
theorem B4398533 : Blo 1084620 4398533 := bbase (se 4 (by rfl) ⟨412362, by rfl⟩ : syracuseStep 4398533 = 824725) (by norm_num)
theorem B4398661 : Blo 1084620 4398661 := bbase (se 4 (by rfl) ⟨412374, by rfl⟩ : syracuseStep 4398661 = 824749) (by norm_num)
theorem B1220233 : Blo 1084620 1220233 := bbase (se 2 (by rfl) ⟨457587, by rfl⟩ : syracuseStep 1220233 = 915175) (by norm_num)
theorem B1220269 : Blo 1084620 1220269 := bbase (se 3 (by rfl) ⟨228800, by rfl⟩ : syracuseStep 1220269 = 457601) (by norm_num)
theorem B1220305 : Blo 1084620 1220305 := bbase (se 2 (by rfl) ⟨457614, by rfl⟩ : syracuseStep 1220305 = 915229) (by norm_num)
theorem B1220341 : Blo 1084620 1220341 := bbase (se 5 (by rfl) ⟨57203, by rfl⟩ : syracuseStep 1220341 = 114407) (by norm_num)
theorem B1220377 : Blo 1084620 1220377 := bbase (se 2 (by rfl) ⟨457641, by rfl⟩ : syracuseStep 1220377 = 915283) (by norm_num)
theorem B1548077 : Blo 1084620 1548077 := bbase (se 3 (by rfl) ⟨290264, by rfl⟩ : syracuseStep 1548077 = 580529) (by norm_num)
theorem B1220413 : Blo 1084620 1220413 := bbase (se 3 (by rfl) ⟨228827, by rfl⟩ : syracuseStep 1220413 = 457655) (by norm_num)
theorem B1220449 : Blo 1084620 1220449 := bbase (se 2 (by rfl) ⟨457668, by rfl⟩ : syracuseStep 1220449 = 915337) (by norm_num)
theorem B2236261 : Blo 1084620 2236261 := bbase (se 4 (by rfl) ⟨209649, by rfl⟩ : syracuseStep 2236261 = 419299) (by norm_num)
theorem B2203517 : Blo 1084620 2203517 := bbase (se 3 (by rfl) ⟨413159, by rfl⟩ : syracuseStep 2203517 = 826319) (by norm_num)
theorem B1220485 : Blo 1084620 1220485 := bbase (se 4 (by rfl) ⟨114420, by rfl⟩ : syracuseStep 1220485 = 228841) (by norm_num)
theorem B1220521 : Blo 1084620 1220521 := bbase (se 2 (by rfl) ⟨457695, by rfl⟩ : syracuseStep 1220521 = 915391) (by norm_num)
theorem B1220557 : Blo 1084620 1220557 := bbase (se 3 (by rfl) ⟨228854, by rfl⟩ : syracuseStep 1220557 = 457709) (by norm_num)
theorem B1220593 : Blo 1084620 1220593 := bbase (se 2 (by rfl) ⟨457722, by rfl⟩ : syracuseStep 1220593 = 915445) (by norm_num)
theorem B1220629 : Blo 1084620 1220629 := bbase (se 6 (by rfl) ⟨28608, by rfl⟩ : syracuseStep 1220629 = 57217) (by norm_num)
theorem B1220665 : Blo 1084620 1220665 := bbase (se 2 (by rfl) ⟨457749, by rfl⟩ : syracuseStep 1220665 = 915499) (by norm_num)
theorem B1220701 : Blo 1084620 1220701 := bbase (se 3 (by rfl) ⟨228881, by rfl⟩ : syracuseStep 1220701 = 457763) (by norm_num)
theorem B1220737 : Blo 1084620 1220737 := bbase (se 2 (by rfl) ⟨457776, by rfl⟩ : syracuseStep 1220737 = 915553) (by norm_num)
theorem B1220773 : Blo 1084620 1220773 := bbase (se 4 (by rfl) ⟨114447, by rfl⟩ : syracuseStep 1220773 = 228895) (by norm_num)
theorem B1220809 : Blo 1084620 1220809 := bbase (se 2 (by rfl) ⟨457803, by rfl⟩ : syracuseStep 1220809 = 915607) (by norm_num)
theorem B1220845 : Blo 1084620 1220845 := bbase (se 3 (by rfl) ⟨228908, by rfl⟩ : syracuseStep 1220845 = 457817) (by norm_num)
theorem B6955253 : Blo 1084620 6955253 := bbase (se 5 (by rfl) ⟨326027, by rfl⟩ : syracuseStep 6955253 = 652055) (by norm_num)
theorem B1220881 : Blo 1084620 1220881 := bbase (se 2 (by rfl) ⟨457830, by rfl⟩ : syracuseStep 1220881 = 915661) (by norm_num)
theorem B1220917 : Blo 1084620 1220917 := bbase (se 5 (by rfl) ⟨57230, by rfl⟩ : syracuseStep 1220917 = 114461) (by norm_num)
theorem B1220953 : Blo 1084620 1220953 := bbase (se 2 (by rfl) ⟨457857, by rfl⟩ : syracuseStep 1220953 = 915715) (by norm_num)
theorem B1220989 : Blo 1084620 1220989 := bbase (se 3 (by rfl) ⟨228935, by rfl⟩ : syracuseStep 1220989 = 457871) (by norm_num)
theorem B1221025 : Blo 1084620 1221025 := bbase (se 2 (by rfl) ⟨457884, by rfl⟩ : syracuseStep 1221025 = 915769) (by norm_num)
theorem B1221061 : Blo 1084620 1221061 := bbase (se 4 (by rfl) ⟨114474, by rfl⟩ : syracuseStep 1221061 = 228949) (by norm_num)
theorem B1221097 : Blo 1084620 1221097 := bbase (se 2 (by rfl) ⟨457911, by rfl⟩ : syracuseStep 1221097 = 915823) (by norm_num)
theorem B1221133 : Blo 1084620 1221133 := bbase (se 3 (by rfl) ⟨228962, by rfl⟩ : syracuseStep 1221133 = 457925) (by norm_num)
theorem B1548829 : Blo 1084620 1548829 := bbase (se 3 (by rfl) ⟨290405, by rfl⟩ : syracuseStep 1548829 = 580811) (by norm_num)
theorem B3482149 : Blo 1084620 3482149 := bbase (se 4 (by rfl) ⟨326451, by rfl⟩ : syracuseStep 3482149 = 652903) (by norm_num)
theorem B1221169 : Blo 1084620 1221169 := bbase (se 2 (by rfl) ⟨457938, by rfl⟩ : syracuseStep 1221169 = 915877) (by norm_num)
theorem B1221205 : Blo 1084620 1221205 := bbase (se 8 (by rfl) ⟨7155, by rfl⟩ : syracuseStep 1221205 = 14311) (by norm_num)
theorem B5218901 : Blo 1084620 5218901 := bbase (se 8 (by rfl) ⟨30579, by rfl⟩ : syracuseStep 5218901 = 61159) (by norm_num)
theorem B1221241 : Blo 1084620 1221241 := bbase (se 2 (by rfl) ⟨457965, by rfl⟩ : syracuseStep 1221241 = 915931) (by norm_num)
theorem B4956821 : Blo 1084620 4956821 := bbase (se 6 (by rfl) ⟨116175, by rfl⟩ : syracuseStep 4956821 = 232351) (by norm_num)
theorem B1221277 : Blo 1084620 1221277 := bbase (se 3 (by rfl) ⟨228989, by rfl⟩ : syracuseStep 1221277 = 457979) (by norm_num)
theorem B1221313 : Blo 1084620 1221313 := bbase (se 2 (by rfl) ⟨457992, by rfl⟩ : syracuseStep 1221313 = 915985) (by norm_num)
theorem B1221349 : Blo 1084620 1221349 := bbase (se 4 (by rfl) ⟨114501, by rfl⟩ : syracuseStep 1221349 = 229003) (by norm_num)
theorem B1221385 : Blo 1084620 1221385 := bbase (se 2 (by rfl) ⟨458019, by rfl⟩ : syracuseStep 1221385 = 916039) (by norm_num)
theorem B1221421 : Blo 1084620 1221421 := bbase (se 3 (by rfl) ⟨229016, by rfl⟩ : syracuseStep 1221421 = 458033) (by norm_num)
theorem B1221457 : Blo 1084620 1221457 := bbase (se 2 (by rfl) ⟨458046, by rfl⟩ : syracuseStep 1221457 = 916093) (by norm_num)
theorem B1221493 : Blo 1084620 1221493 := bbase (se 5 (by rfl) ⟨57257, by rfl⟩ : syracuseStep 1221493 = 114515) (by norm_num)
theorem B1221529 : Blo 1084620 1221529 := bbase (se 2 (by rfl) ⟨458073, by rfl⟩ : syracuseStep 1221529 = 916147) (by norm_num)
theorem B1221565 : Blo 1084620 1221565 := bbase (se 3 (by rfl) ⟨229043, by rfl⟩ : syracuseStep 1221565 = 458087) (by norm_num)
theorem B1221601 : Blo 1084620 1221601 := bbase (se 2 (by rfl) ⟨458100, by rfl⟩ : syracuseStep 1221601 = 916201) (by norm_num)
theorem B1221637 : Blo 1084620 1221637 := bbase (se 4 (by rfl) ⟨114528, by rfl⟩ : syracuseStep 1221637 = 229057) (by norm_num)
theorem B1221673 : Blo 1084620 1221673 := bbase (se 2 (by rfl) ⟨458127, by rfl⟩ : syracuseStep 1221673 = 916255) (by norm_num)
theorem B1221709 : Blo 1084620 1221709 := bbase (se 3 (by rfl) ⟨229070, by rfl⟩ : syracuseStep 1221709 = 458141) (by norm_num)
theorem B2204749 : Blo 1084620 2204749 := bbase (se 3 (by rfl) ⟨413390, by rfl⟩ : syracuseStep 2204749 = 826781) (by norm_num)
theorem B1221745 : Blo 1084620 1221745 := bbase (se 2 (by rfl) ⟨458154, by rfl⟩ : syracuseStep 1221745 = 916309) (by norm_num)
theorem B1221781 : Blo 1084620 1221781 := bbase (se 6 (by rfl) ⟨28635, by rfl⟩ : syracuseStep 1221781 = 57271) (by norm_num)
theorem B1221817 : Blo 1084620 1221817 := bbase (se 2 (by rfl) ⟨458181, by rfl⟩ : syracuseStep 1221817 = 916363) (by norm_num)
theorem B1221853 : Blo 1084620 1221853 := bbase (se 3 (by rfl) ⟨229097, by rfl⟩ : syracuseStep 1221853 = 458195) (by norm_num)
theorem B1221889 : Blo 1084620 1221889 := bbase (se 2 (by rfl) ⟨458208, by rfl⟩ : syracuseStep 1221889 = 916417) (by norm_num)
theorem B1221925 : Blo 1084620 1221925 := bbase (se 4 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 1221925 = 229111) (by norm_num)
theorem B1549621 : Blo 1084620 1549621 := bbase (se 5 (by rfl) ⟨72638, by rfl⟩ : syracuseStep 1549621 = 145277) (by norm_num)
theorem B10462517 : Blo 1084620 10462517 := bbase (se 5 (by rfl) ⟨490430, by rfl⟩ : syracuseStep 10462517 = 980861) (by norm_num)
theorem B1221961 : Blo 1084620 1221961 := bbase (se 2 (by rfl) ⟨458235, by rfl⟩ : syracuseStep 1221961 = 916471) (by norm_num)
theorem B3089765 : Blo 1084620 3089765 := bbase (se 4 (by rfl) ⟨289665, by rfl⟩ : syracuseStep 3089765 = 579331) (by norm_num)
theorem B1221997 : Blo 1084620 1221997 := bbase (se 3 (by rfl) ⟨229124, by rfl⟩ : syracuseStep 1221997 = 458249) (by norm_num)
theorem B1222033 : Blo 1084620 1222033 := bbase (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) (by norm_num)
theorem B2860469 : Blo 1084620 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B1222069 : Blo 1084620 1222069 := bbase (se 5 (by rfl) ⟨57284, by rfl⟩ : syracuseStep 1222069 = 114569) (by norm_num)
theorem B1222105 : Blo 1084620 1222105 := bbase (se 2 (by rfl) ⟨458289, by rfl⟩ : syracuseStep 1222105 = 916579) (by norm_num)
theorem B1222141 : Blo 1084620 1222141 := bbase (se 3 (by rfl) ⟨229151, by rfl⟩ : syracuseStep 1222141 = 458303) (by norm_num)
theorem B1222177 : Blo 1084620 1222177 := bbase (se 2 (by rfl) ⟨458316, by rfl⟩ : syracuseStep 1222177 = 916633) (by norm_num)
theorem B1222213 : Blo 1084620 1222213 := bbase (se 4 (by rfl) ⟨114582, by rfl⟩ : syracuseStep 1222213 = 229165) (by norm_num)
theorem B1222249 : Blo 1084620 1222249 := bbase (se 2 (by rfl) ⟨458343, by rfl⟩ : syracuseStep 1222249 = 916687) (by norm_num)
theorem B1549957 : Blo 1084620 1549957 := bbase (se 4 (by rfl) ⟨145308, by rfl⟩ : syracuseStep 1549957 = 290617) (by norm_num)
theorem B1222285 : Blo 1084620 1222285 := bbase (se 3 (by rfl) ⟨229178, by rfl⟩ : syracuseStep 1222285 = 458357) (by norm_num)
theorem B1222321 : Blo 1084620 1222321 := bbase (se 2 (by rfl) ⟨458370, by rfl⟩ : syracuseStep 1222321 = 916741) (by norm_num)
theorem B1222357 : Blo 1084620 1222357 := bbase (se 7 (by rfl) ⟨14324, by rfl⟩ : syracuseStep 1222357 = 28649) (by norm_num)
theorem B1222393 : Blo 1084620 1222393 := bbase (se 2 (by rfl) ⟨458397, by rfl⟩ : syracuseStep 1222393 = 916795) (by norm_num)
theorem B1222429 : Blo 1084620 1222429 := bbase (se 3 (by rfl) ⟨229205, by rfl⟩ : syracuseStep 1222429 = 458411) (by norm_num)
theorem B1222465 : Blo 1084620 1222465 := bbase (se 2 (by rfl) ⟨458424, by rfl⟩ : syracuseStep 1222465 = 916849) (by norm_num)
theorem B1222501 : Blo 1084620 1222501 := bbase (se 4 (by rfl) ⟨114609, by rfl⟩ : syracuseStep 1222501 = 229219) (by norm_num)
theorem B1222537 : Blo 1084620 1222537 := bbase (se 2 (by rfl) ⟨458451, by rfl⟩ : syracuseStep 1222537 = 916903) (by norm_num)
theorem B1222573 : Blo 1084620 1222573 := bbase (se 3 (by rfl) ⟨229232, by rfl⟩ : syracuseStep 1222573 = 458465) (by norm_num)
theorem B1222609 : Blo 1084620 1222609 := bbase (se 2 (by rfl) ⟨458478, by rfl⟩ : syracuseStep 1222609 = 916957) (by norm_num)
theorem B1222645 : Blo 1084620 1222645 := bbase (se 5 (by rfl) ⟨57311, by rfl⟩ : syracuseStep 1222645 = 114623) (by norm_num)
theorem B3090437 : Blo 1084620 3090437 := bbase (se 4 (by rfl) ⟨289728, by rfl⟩ : syracuseStep 3090437 = 579457) (by norm_num)
theorem B1222681 : Blo 1084620 1222681 := bbase (se 2 (by rfl) ⟨458505, by rfl⟩ : syracuseStep 1222681 = 917011) (by norm_num)
theorem B1222717 : Blo 1084620 1222717 := bbase (se 3 (by rfl) ⟨229259, by rfl⟩ : syracuseStep 1222717 = 458519) (by norm_num)
theorem B1222753 : Blo 1084620 1222753 := bbase (se 2 (by rfl) ⟨458532, by rfl⟩ : syracuseStep 1222753 = 917065) (by norm_num)
theorem B1222789 : Blo 1084620 1222789 := bbase (se 4 (by rfl) ⟨114636, by rfl⟩ : syracuseStep 1222789 = 229273) (by norm_num)
theorem B1222825 : Blo 1084620 1222825 := bbase (se 2 (by rfl) ⟨458559, by rfl⟩ : syracuseStep 1222825 = 917119) (by norm_num)
theorem B3582133 : Blo 1084620 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B1222861 : Blo 1084620 1222861 := bbase (se 3 (by rfl) ⟨229286, by rfl⟩ : syracuseStep 1222861 = 458573) (by norm_num)
theorem B1222897 : Blo 1084620 1222897 := bbase (se 2 (by rfl) ⟨458586, by rfl⟩ : syracuseStep 1222897 = 917173) (by norm_num)
theorem B1222933 : Blo 1084620 1222933 := bbase (se 6 (by rfl) ⟨28662, by rfl⟩ : syracuseStep 1222933 = 57325) (by norm_num)
theorem B1222969 : Blo 1084620 1222969 := bbase (se 2 (by rfl) ⟨458613, by rfl⟩ : syracuseStep 1222969 = 917227) (by norm_num)
theorem B11741525 : Blo 1084620 11741525 := bbase (se 10 (by rfl) ⟨17199, by rfl⟩ : syracuseStep 11741525 = 34399) (by norm_num)
theorem B1223005 : Blo 1084620 1223005 := bbase (se 3 (by rfl) ⟨229313, by rfl⟩ : syracuseStep 1223005 = 458627) (by norm_num)
theorem B1223041 : Blo 1084620 1223041 := bbase (se 2 (by rfl) ⟨458640, by rfl⟩ : syracuseStep 1223041 = 917281) (by norm_num)
theorem B1223077 : Blo 1084620 1223077 := bbase (se 4 (by rfl) ⟨114663, by rfl⟩ : syracuseStep 1223077 = 229327) (by norm_num)
theorem B3090869 : Blo 1084620 3090869 := bbase (se 5 (by rfl) ⟨144884, by rfl⟩ : syracuseStep 3090869 = 289769) (by norm_num)
theorem B1223113 : Blo 1084620 1223113 := bbase (se 2 (by rfl) ⟨458667, by rfl⟩ : syracuseStep 1223113 = 917335) (by norm_num)
theorem B1223149 : Blo 1084620 1223149 := bbase (se 3 (by rfl) ⟨229340, by rfl⟩ : syracuseStep 1223149 = 458681) (by norm_num)
theorem B9415157 : Blo 1084620 9415157 := bbase (se 5 (by rfl) ⟨441335, by rfl⟩ : syracuseStep 9415157 = 882671) (by norm_num)
theorem B1223185 : Blo 1084620 1223185 := bbase (se 2 (by rfl) ⟨458694, by rfl⟩ : syracuseStep 1223185 = 917389) (by norm_num)
theorem B5286421 : Blo 1084620 5286421 := bbase (se 6 (by rfl) ⟨123900, by rfl⟩ : syracuseStep 5286421 = 247801) (by norm_num)
theorem B1223221 : Blo 1084620 1223221 := bbase (se 5 (by rfl) ⟨57338, by rfl⟩ : syracuseStep 1223221 = 114677) (by norm_num)
theorem B1223257 : Blo 1084620 1223257 := bbase (se 2 (by rfl) ⟨458721, by rfl⟩ : syracuseStep 1223257 = 917443) (by norm_num)
theorem B1223293 : Blo 1084620 1223293 := bbase (se 3 (by rfl) ⟨229367, by rfl⟩ : syracuseStep 1223293 = 458735) (by norm_num)
theorem B1223329 : Blo 1084620 1223329 := bbase (se 2 (by rfl) ⟨458748, by rfl⟩ : syracuseStep 1223329 = 917497) (by norm_num)
theorem B1649317 : Blo 1084620 1649317 := bbase (se 4 (by rfl) ⟨154623, by rfl⟩ : syracuseStep 1649317 = 309247) (by norm_num)
theorem B1223365 : Blo 1084620 1223365 := bbase (se 4 (by rfl) ⟨114690, by rfl⟩ : syracuseStep 1223365 = 229381) (by norm_num)
theorem B1223401 : Blo 1084620 1223401 := bbase (se 2 (by rfl) ⟨458775, by rfl⟩ : syracuseStep 1223401 = 917551) (by norm_num)
theorem B1223437 : Blo 1084620 1223437 := bbase (se 3 (by rfl) ⟨229394, by rfl⟩ : syracuseStep 1223437 = 458789) (by norm_num)
theorem B1223473 : Blo 1084620 1223473 := bbase (se 2 (by rfl) ⟨458802, by rfl⟩ : syracuseStep 1223473 = 917605) (by norm_num)
theorem B1223509 : Blo 1084620 1223509 := bbase (se 9 (by rfl) ⟨3584, by rfl⟩ : syracuseStep 1223509 = 7169) (by norm_num)
theorem B4402021 : Blo 1084620 4402021 := bbase (se 4 (by rfl) ⟨412689, by rfl⟩ : syracuseStep 4402021 = 825379) (by norm_num)
theorem B1223545 : Blo 1084620 1223545 := bbase (se 2 (by rfl) ⟨458829, by rfl⟩ : syracuseStep 1223545 = 917659) (by norm_num)
theorem B2206597 : Blo 1084620 2206597 := bbase (se 4 (by rfl) ⟨206868, by rfl⟩ : syracuseStep 2206597 = 413737) (by norm_num)
theorem B1223581 : Blo 1084620 1223581 := bbase (se 3 (by rfl) ⟨229421, by rfl⟩ : syracuseStep 1223581 = 458843) (by norm_num)
theorem B1223617 : Blo 1084620 1223617 := bbase (se 2 (by rfl) ⟨458856, by rfl⟩ : syracuseStep 1223617 = 917713) (by norm_num)
theorem B1223653 : Blo 1084620 1223653 := bbase (se 4 (by rfl) ⟨114717, by rfl⟩ : syracuseStep 1223653 = 229435) (by norm_num)
theorem B1223689 : Blo 1084620 1223689 := bbase (se 2 (by rfl) ⟨458883, by rfl⟩ : syracuseStep 1223689 = 917767) (by norm_num)
theorem B1223725 : Blo 1084620 1223725 := bbase (se 3 (by rfl) ⟨229448, by rfl⟩ : syracuseStep 1223725 = 458897) (by norm_num)
theorem B1223761 : Blo 1084620 1223761 := bbase (se 2 (by rfl) ⟨458910, by rfl⟩ : syracuseStep 1223761 = 917821) (by norm_num)
theorem B1223797 : Blo 1084620 1223797 := bbase (se 5 (by rfl) ⟨57365, by rfl⟩ : syracuseStep 1223797 = 114731) (by norm_num)
theorem B1223833 : Blo 1084620 1223833 := bbase (se 2 (by rfl) ⟨458937, by rfl⟩ : syracuseStep 1223833 = 917875) (by norm_num)
theorem B3091621 : Blo 1084620 3091621 := bbase (se 4 (by rfl) ⟨289839, by rfl⟩ : syracuseStep 3091621 = 579679) (by norm_num)
theorem B1223869 : Blo 1084620 1223869 := bbase (se 3 (by rfl) ⟨229475, by rfl⟩ : syracuseStep 1223869 = 458951) (by norm_num)
theorem B1223905 : Blo 1084620 1223905 := bbase (se 2 (by rfl) ⟨458964, by rfl⟩ : syracuseStep 1223905 = 917929) (by norm_num)
theorem B1223941 : Blo 1084620 1223941 := bbase (se 4 (by rfl) ⟨114744, by rfl⟩ : syracuseStep 1223941 = 229489) (by norm_num)
theorem B1223977 : Blo 1084620 1223977 := bbase (se 2 (by rfl) ⟨458991, by rfl⟩ : syracuseStep 1223977 = 917983) (by norm_num)
theorem B5221685 : Blo 1084620 5221685 := bbase (se 5 (by rfl) ⟨244766, by rfl⟩ : syracuseStep 5221685 = 489533) (by norm_num)
theorem B1158457 : Blo 1084620 1158457 := bbase (se 2 (by rfl) ⟨434421, by rfl⟩ : syracuseStep 1158457 = 868843) (by norm_num)
theorem B1224013 : Blo 1084620 1224013 := bbase (se 3 (by rfl) ⟨229502, by rfl⟩ : syracuseStep 1224013 = 459005) (by norm_num)
theorem B1224049 : Blo 1084620 1224049 := bbase (se 2 (by rfl) ⟨459018, by rfl⟩ : syracuseStep 1224049 = 918037) (by norm_num)
theorem B3485045 : Blo 1084620 3485045 := bbase (se 5 (by rfl) ⟨163361, by rfl⟩ : syracuseStep 3485045 = 326723) (by norm_num)
theorem B1224085 : Blo 1084620 1224085 := bbase (se 6 (by rfl) ⟨28689, by rfl⟩ : syracuseStep 1224085 = 57379) (by norm_num)
theorem B1224121 : Blo 1084620 1224121 := bbase (se 2 (by rfl) ⟨459045, by rfl⟩ : syracuseStep 1224121 = 918091) (by norm_num)
theorem B1224157 : Blo 1084620 1224157 := bbase (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) (by norm_num)
theorem B1224193 : Blo 1084620 1224193 := bbase (se 2 (by rfl) ⟨459072, by rfl⟩ : syracuseStep 1224193 = 918145) (by norm_num)
theorem B1224229 : Blo 1084620 1224229 := bbase (se 4 (by rfl) ⟨114771, by rfl⟩ : syracuseStep 1224229 = 229543) (by norm_num)
theorem B1224265 : Blo 1084620 1224265 := bbase (se 2 (by rfl) ⟨459099, by rfl⟩ : syracuseStep 1224265 = 918199) (by norm_num)
theorem B1224301 : Blo 1084620 1224301 := bbase (se 3 (by rfl) ⟨229556, by rfl⟩ : syracuseStep 1224301 = 459113) (by norm_num)
theorem B1224337 : Blo 1084620 1224337 := bbase (se 2 (by rfl) ⟨459126, by rfl⟩ : syracuseStep 1224337 = 918253) (by norm_num)
theorem B1158833 : Blo 1084620 1158833 := bbase (se 2 (by rfl) ⟨434562, by rfl⟩ : syracuseStep 1158833 = 869125) (by norm_num)
theorem B1224373 : Blo 1084620 1224373 := bbase (se 5 (by rfl) ⟨57392, by rfl⟩ : syracuseStep 1224373 = 114785) (by norm_num)
theorem B1224409 : Blo 1084620 1224409 := bbase (se 2 (by rfl) ⟨459153, by rfl⟩ : syracuseStep 1224409 = 918307) (by norm_num)
theorem B1158905 : Blo 1084620 1158905 := bbase (se 2 (by rfl) ⟨434589, by rfl⟩ : syracuseStep 1158905 = 869179) (by norm_num)
theorem B1224445 : Blo 1084620 1224445 := bbase (se 3 (by rfl) ⟨229583, by rfl⟩ : syracuseStep 1224445 = 459167) (by norm_num)
theorem B1224481 : Blo 1084620 1224481 := bbase (se 2 (by rfl) ⟨459180, by rfl⟩ : syracuseStep 1224481 = 918361) (by norm_num)
theorem B1650485 : Blo 1084620 1650485 := bbase (se 5 (by rfl) ⟨77366, by rfl⟩ : syracuseStep 1650485 = 154733) (by norm_num)
theorem B1224517 : Blo 1084620 1224517 := bbase (se 4 (by rfl) ⟨114798, by rfl⟩ : syracuseStep 1224517 = 229597) (by norm_num)
theorem B1224553 : Blo 1084620 1224553 := bbase (se 2 (by rfl) ⟨459207, by rfl⟩ : syracuseStep 1224553 = 918415) (by norm_num)
theorem B1224589 : Blo 1084620 1224589 := bbase (se 3 (by rfl) ⟨229610, by rfl⟩ : syracuseStep 1224589 = 459221) (by norm_num)
theorem B1224625 : Blo 1084620 1224625 := bbase (se 2 (by rfl) ⟨459234, by rfl⟩ : syracuseStep 1224625 = 918469) (by norm_num)
theorem B1159093 : Blo 1084620 1159093 := bbase (se 5 (by rfl) ⟨54332, by rfl⟩ : syracuseStep 1159093 = 108665) (by norm_num)
theorem B3715013 : Blo 1084620 3715013 := bbase (se 4 (by rfl) ⟨348282, by rfl⟩ : syracuseStep 3715013 = 696565) (by norm_num)
theorem B1224661 : Blo 1084620 1224661 := bbase (se 7 (by rfl) ⟨14351, by rfl⟩ : syracuseStep 1224661 = 28703) (by norm_num)
theorem B1224697 : Blo 1084620 1224697 := bbase (se 2 (by rfl) ⟨459261, by rfl⟩ : syracuseStep 1224697 = 918523) (by norm_num)
theorem B1159277 : Blo 1084620 1159277 := bbase (se 3 (by rfl) ⟨217364, by rfl⟩ : syracuseStep 1159277 = 434729) (by norm_num)
theorem B3486341 : Blo 1084620 3486341 := bbase (se 4 (by rfl) ⟨326844, by rfl⟩ : syracuseStep 3486341 = 653689) (by norm_num)
theorem B1651445 : Blo 1084620 1651445 := bbase (se 5 (by rfl) ⟨77411, by rfl⟩ : syracuseStep 1651445 = 154823) (by norm_num)
theorem B1160029 : Blo 1084620 1160029 := bbase (se 3 (by rfl) ⟨217505, by rfl⟩ : syracuseStep 1160029 = 435011) (by norm_num)
theorem B1160101 : Blo 1084620 1160101 := bbase (se 4 (by rfl) ⟨108759, by rfl⟩ : syracuseStep 1160101 = 217519) (by norm_num)
theorem B12530645 : Blo 1084620 12530645 := bbase (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) (by norm_num)
theorem B1160281 : Blo 1084620 1160281 := bbase (se 2 (by rfl) ⟨435105, by rfl⟩ : syracuseStep 1160281 = 870211) (by norm_num)
theorem B1652005 : Blo 1084620 1652005 := bbase (se 4 (by rfl) ⟨154875, by rfl⟩ : syracuseStep 1652005 = 309751) (by norm_num)
theorem B4634117 : Blo 1084620 4634117 := bbase (se 4 (by rfl) ⟨434448, by rfl⟩ : syracuseStep 4634117 = 868897) (by norm_num)
theorem B1160725 : Blo 1084620 1160725 := bbase (se 6 (by rfl) ⟨27204, by rfl⟩ : syracuseStep 1160725 = 54409) (by norm_num)
theorem B1652285 : Blo 1084620 1652285 := bbase (se 3 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 1652285 = 619607) (by norm_num)
theorem B1488461 : Blo 1084620 1488461 := bbase (se 3 (by rfl) ⟨279086, by rfl⟩ : syracuseStep 1488461 = 558173) (by norm_num)
theorem B8795765 : Blo 1084620 8795765 := bbase (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) (by norm_num)
theorem B1160849 : Blo 1084620 1160849 := bbase (se 2 (by rfl) ⟨435318, by rfl⟩ : syracuseStep 1160849 = 870637) (by norm_num)
theorem B9418517 : Blo 1084620 9418517 := bbase (se 6 (by rfl) ⟨220746, by rfl⟩ : syracuseStep 9418517 = 441493) (by norm_num)
theorem B1161101 : Blo 1084620 1161101 := bbase (se 3 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 1161101 = 435413) (by norm_num)
theorem B3094469 : Blo 1084620 3094469 := bbase (se 4 (by rfl) ⟨290106, by rfl⟩ : syracuseStep 3094469 = 580213) (by norm_num)
theorem B8239157 : Blo 1084620 8239157 := bbase (se 5 (by rfl) ⟨386210, by rfl⟩ : syracuseStep 8239157 = 772421) (by norm_num)
theorem B1161545 : Blo 1084620 1161545 := bbase (se 2 (by rfl) ⟨435579, by rfl⟩ : syracuseStep 1161545 = 871159) (by norm_num)
theorem B12368213 : Blo 1084620 12368213 := bbase (se 10 (by rfl) ⟨18117, by rfl⟩ : syracuseStep 12368213 = 36235) (by norm_num)
theorem B9288053 : Blo 1084620 9288053 := bbase (se 5 (by rfl) ⟨435377, by rfl⟩ : syracuseStep 9288053 = 870755) (by norm_num)
theorem B1489469 : Blo 1084620 1489469 := bbase (se 3 (by rfl) ⟨279275, by rfl⟩ : syracuseStep 1489469 = 558551) (by norm_num)
theorem B1161793 : Blo 1084620 1161793 := bbase (se 2 (by rfl) ⟨435672, by rfl⟩ : syracuseStep 1161793 = 871345) (by norm_num)
theorem B10566389 : Blo 1084620 10566389 := bbase (se 5 (by rfl) ⟨495299, by rfl⟩ : syracuseStep 10566389 = 990599) (by norm_num)
theorem B5651333 : Blo 1084620 5651333 := bbase (se 4 (by rfl) ⟨529812, by rfl⟩ : syracuseStep 5651333 = 1059625) (by norm_num)
theorem B1162237 : Blo 1084620 1162237 := bbase (se 3 (by rfl) ⟨217919, by rfl⟩ : syracuseStep 1162237 = 435839) (by norm_num)
theorem B1653805 : Blo 1084620 1653805 := bbase (se 3 (by rfl) ⟨310088, by rfl⟩ : syracuseStep 1653805 = 620177) (by norm_num)
theorem B1162297 : Blo 1084620 1162297 := bbase (se 2 (by rfl) ⟨435861, by rfl⟩ : syracuseStep 1162297 = 871723) (by norm_num)
theorem B1653853 : Blo 1084620 1653853 := bbase (se 3 (by rfl) ⟨310097, by rfl⟩ : syracuseStep 1653853 = 620195) (by norm_num)
theorem B3095653 : Blo 1084620 3095653 := bbase (se 4 (by rfl) ⟨290217, by rfl⟩ : syracuseStep 3095653 = 580435) (by norm_num)
theorem B1653877 : Blo 1084620 1653877 := bbase (se 5 (by rfl) ⟨77525, by rfl⟩ : syracuseStep 1653877 = 155051) (by norm_num)
theorem B2440421 : Blo 1084620 2440421 := bbase (se 4 (by rfl) ⟨228789, by rfl⟩ : syracuseStep 2440421 = 457579) (by norm_num)
theorem B4635893 : Blo 1084620 4635893 := bbase (se 5 (by rfl) ⟨217307, by rfl⟩ : syracuseStep 4635893 = 434615) (by norm_num)
theorem B3095813 : Blo 1084620 3095813 := bbase (se 4 (by rfl) ⟨290232, by rfl⟩ : syracuseStep 3095813 = 580465) (by norm_num)
theorem B2440493 : Blo 1084620 2440493 := bbase (se 3 (by rfl) ⟨457592, by rfl⟩ : syracuseStep 2440493 = 915185) (by norm_num)
theorem B2440565 : Blo 1084620 2440565 := bbase (se 5 (by rfl) ⟨114401, by rfl⟩ : syracuseStep 2440565 = 228803) (by norm_num)
theorem B2440637 : Blo 1084620 2440637 := bbase (se 3 (by rfl) ⟨457619, by rfl⟩ : syracuseStep 2440637 = 915239) (by norm_num)
theorem B3096053 : Blo 1084620 3096053 := bbase (se 5 (by rfl) ⟨145127, by rfl⟩ : syracuseStep 3096053 = 290255) (by norm_num)
theorem B2440709 : Blo 1084620 2440709 := bbase (se 4 (by rfl) ⟨228816, by rfl⟩ : syracuseStep 2440709 = 457633) (by norm_num)
theorem B2440781 : Blo 1084620 2440781 := bbase (se 3 (by rfl) ⟨457646, by rfl⟩ : syracuseStep 2440781 = 915293) (by norm_num)
theorem B2440853 : Blo 1084620 2440853 := bbase (se 6 (by rfl) ⟨57207, by rfl⟩ : syracuseStep 2440853 = 114415) (by norm_num)
theorem B3096245 : Blo 1084620 3096245 := bbase (se 5 (by rfl) ⟨145136, by rfl⟩ : syracuseStep 3096245 = 290273) (by norm_num)
theorem B2440925 : Blo 1084620 2440925 := bbase (se 3 (by rfl) ⟨457673, by rfl⟩ : syracuseStep 2440925 = 915347) (by norm_num)
theorem B2440997 : Blo 1084620 2440997 := bbase (se 4 (by rfl) ⟨228843, by rfl⟩ : syracuseStep 2440997 = 457687) (by norm_num)
theorem B2441069 : Blo 1084620 2441069 := bbase (se 3 (by rfl) ⟨457700, by rfl⟩ : syracuseStep 2441069 = 915401) (by norm_num)
theorem B2441141 : Blo 1084620 2441141 := bbase (se 5 (by rfl) ⟨114428, by rfl⟩ : syracuseStep 2441141 = 228857) (by norm_num)
theorem B2441213 : Blo 1084620 2441213 := bbase (se 3 (by rfl) ⟨457727, by rfl⟩ : syracuseStep 2441213 = 915455) (by norm_num)
theorem B2441285 : Blo 1084620 2441285 := bbase (se 4 (by rfl) ⟨228870, by rfl⟩ : syracuseStep 2441285 = 457741) (by norm_num)
theorem B1392709 : Blo 1084620 1392709 := bbase (se 4 (by rfl) ⟨130566, by rfl⟩ : syracuseStep 1392709 = 261133) (by norm_num)
theorem B2441357 : Blo 1084620 2441357 := bbase (se 3 (by rfl) ⟨457754, by rfl⟩ : syracuseStep 2441357 = 915509) (by norm_num)
theorem B2441429 : Blo 1084620 2441429 := bbase (se 7 (by rfl) ⟨28610, by rfl⟩ : syracuseStep 2441429 = 57221) (by norm_num)
theorem B4636885 : Blo 1084620 4636885 := bbase (se 7 (by rfl) ⟨54338, by rfl⟩ : syracuseStep 4636885 = 108677) (by norm_num)
theorem B1654997 : Blo 1084620 1654997 := bbase (se 7 (by rfl) ⟨19394, by rfl⟩ : syracuseStep 1654997 = 38789) (by norm_num)
theorem B3916021 : Blo 1084620 3916021 := bbase (se 5 (by rfl) ⟨183563, by rfl⟩ : syracuseStep 3916021 = 367127) (by norm_num)
theorem B2441501 : Blo 1084620 2441501 := bbase (se 3 (by rfl) ⟨457781, by rfl⟩ : syracuseStep 2441501 = 915563) (by norm_num)
theorem B2441573 : Blo 1084620 2441573 := bbase (se 4 (by rfl) ⟨228897, by rfl⟩ : syracuseStep 2441573 = 457795) (by norm_num)
theorem B2441645 : Blo 1084620 2441645 := bbase (se 3 (by rfl) ⟨457808, by rfl⟩ : syracuseStep 2441645 = 915617) (by norm_num)
theorem B3523061 : Blo 1084620 3523061 := bbase (se 5 (by rfl) ⟨165143, by rfl⟩ : syracuseStep 3523061 = 330287) (by norm_num)
theorem B2441717 : Blo 1084620 2441717 := bbase (se 5 (by rfl) ⟨114455, by rfl⟩ : syracuseStep 2441717 = 228911) (by norm_num)
theorem B2441789 : Blo 1084620 2441789 := bbase (se 3 (by rfl) ⟨457835, by rfl⟩ : syracuseStep 2441789 = 915671) (by norm_num)
theorem B2441861 : Blo 1084620 2441861 := bbase (se 4 (by rfl) ⟨228924, by rfl⟩ : syracuseStep 2441861 = 457849) (by norm_num)
theorem B3097237 : Blo 1084620 3097237 := bbase (se 6 (by rfl) ⟨72591, by rfl⟩ : syracuseStep 3097237 = 145183) (by norm_num)
theorem B2441933 : Blo 1084620 2441933 := bbase (se 3 (by rfl) ⟨457862, by rfl⟩ : syracuseStep 2441933 = 915725) (by norm_num)
theorem B2442005 : Blo 1084620 2442005 := bbase (se 6 (by rfl) ⟨57234, by rfl⟩ : syracuseStep 2442005 = 114469) (by norm_num)
theorem B2442077 : Blo 1084620 2442077 := bbase (se 3 (by rfl) ⟨457889, by rfl⟩ : syracuseStep 2442077 = 915779) (by norm_num)
theorem B2474869 : Blo 1084620 2474869 := bbase (se 5 (by rfl) ⟨116009, by rfl⟩ : syracuseStep 2474869 = 232019) (by norm_num)
theorem B2442149 : Blo 1084620 2442149 := bbase (se 4 (by rfl) ⟨228951, by rfl⟩ : syracuseStep 2442149 = 457903) (by norm_num)
theorem B13943765 : Blo 1084620 13943765 := bbase (se 7 (by rfl) ⟨163403, by rfl⟩ : syracuseStep 13943765 = 326807) (by norm_num)
theorem B2442221 : Blo 1084620 2442221 := bbase (se 3 (by rfl) ⟨457916, by rfl⟩ : syracuseStep 2442221 = 915833) (by norm_num)
theorem B2442293 : Blo 1084620 2442293 := bbase (se 5 (by rfl) ⟨114482, by rfl⟩ : syracuseStep 2442293 = 228965) (by norm_num)
theorem B1393777 : Blo 1084620 1393777 := bbase (se 2 (by rfl) ⟨522666, by rfl⟩ : syracuseStep 1393777 = 1045333) (by norm_num)
theorem B2442365 : Blo 1084620 2442365 := bbase (se 3 (by rfl) ⟨457943, by rfl⟩ : syracuseStep 2442365 = 915887) (by norm_num)
theorem B2606269 : Blo 1084620 2606269 := bbase (se 3 (by rfl) ⟨488675, by rfl⟩ : syracuseStep 2606269 = 977351) (by norm_num)
theorem B2442437 : Blo 1084620 2442437 := bbase (se 4 (by rfl) ⟨228978, by rfl⟩ : syracuseStep 2442437 = 457957) (by norm_num)
theorem B2442509 : Blo 1084620 2442509 := bbase (se 3 (by rfl) ⟨457970, by rfl⟩ : syracuseStep 2442509 = 915941) (by norm_num)
theorem B2934085 : Blo 1084620 2934085 := bbase (se 4 (by rfl) ⟨275070, by rfl⟩ : syracuseStep 2934085 = 550141) (by norm_num)
theorem B2442581 : Blo 1084620 2442581 := bbase (se 12 (by rfl) ⟨894, by rfl⟩ : syracuseStep 2442581 = 1789) (by norm_num)
theorem B2442653 : Blo 1084620 2442653 := bbase (se 3 (by rfl) ⟨457997, by rfl⟩ : syracuseStep 2442653 = 915995) (by norm_num)
theorem B2442725 : Blo 1084620 2442725 := bbase (se 4 (by rfl) ⟨229005, by rfl⟩ : syracuseStep 2442725 = 458011) (by norm_num)
theorem B1394209 : Blo 1084620 1394209 := bbase (se 2 (by rfl) ⟨522828, by rfl⟩ : syracuseStep 1394209 = 1045657) (by norm_num)
theorem B2442797 : Blo 1084620 2442797 := bbase (se 3 (by rfl) ⟨458024, by rfl⟩ : syracuseStep 2442797 = 916049) (by norm_num)
theorem B2442869 : Blo 1084620 2442869 := bbase (se 5 (by rfl) ⟨114509, by rfl⟩ : syracuseStep 2442869 = 229019) (by norm_num)
theorem B2442941 : Blo 1084620 2442941 := bbase (se 3 (by rfl) ⟨458051, by rfl⟩ : syracuseStep 2442941 = 916103) (by norm_num)
theorem B3098341 : Blo 1084620 3098341 := bbase (se 4 (by rfl) ⟨290469, by rfl⟩ : syracuseStep 3098341 = 580939) (by norm_num)
theorem B2606845 : Blo 1084620 2606845 := bbase (se 3 (by rfl) ⟨488783, by rfl⟩ : syracuseStep 2606845 = 977567) (by norm_num)
theorem B2443013 : Blo 1084620 2443013 := bbase (se 4 (by rfl) ⟨229032, by rfl⟩ : syracuseStep 2443013 = 458065) (by norm_num)
theorem B2443085 : Blo 1084620 2443085 := bbase (se 3 (by rfl) ⟨458078, by rfl⟩ : syracuseStep 2443085 = 916157) (by norm_num)
theorem B2443157 : Blo 1084620 2443157 := bbase (se 6 (by rfl) ⟨57261, by rfl⟩ : syracuseStep 2443157 = 114523) (by norm_num)
theorem B2443229 : Blo 1084620 2443229 := bbase (se 3 (by rfl) ⟨458105, by rfl⟩ : syracuseStep 2443229 = 916211) (by norm_num)
theorem B19810325 : Blo 1084620 19810325 := bbase (se 6 (by rfl) ⟨464304, by rfl⟩ : syracuseStep 19810325 = 928609) (by norm_num)
theorem B2443301 : Blo 1084620 2443301 := bbase (se 4 (by rfl) ⟨229059, by rfl⟩ : syracuseStep 2443301 = 458119) (by norm_num)
theorem B2607173 : Blo 1084620 2607173 := bbase (se 4 (by rfl) ⟨244422, by rfl⟩ : syracuseStep 2607173 = 488845) (by norm_num)
theorem B2476109 : Blo 1084620 2476109 := bbase (se 3 (by rfl) ⟨464270, by rfl⟩ : syracuseStep 2476109 = 928541) (by norm_num)
theorem B3917909 : Blo 1084620 3917909 := bbase (se 8 (by rfl) ⟨22956, by rfl⟩ : syracuseStep 3917909 = 45913) (by norm_num)
theorem B4245605 : Blo 1084620 4245605 := bbase (se 4 (by rfl) ⟨398025, by rfl⟩ : syracuseStep 4245605 = 796051) (by norm_num)
theorem B2443373 : Blo 1084620 2443373 := bbase (se 3 (by rfl) ⟨458132, by rfl⟩ : syracuseStep 2443373 = 916265) (by norm_num)
theorem B2607229 : Blo 1084620 2607229 := bbase (se 3 (by rfl) ⟨488855, by rfl⟩ : syracuseStep 2607229 = 977711) (by norm_num)
theorem B2443445 : Blo 1084620 2443445 := bbase (se 5 (by rfl) ⟨114536, by rfl⟩ : syracuseStep 2443445 = 229073) (by norm_num)
theorem B2443517 : Blo 1084620 2443517 := bbase (se 3 (by rfl) ⟨458159, by rfl⟩ : syracuseStep 2443517 = 916319) (by norm_num)
theorem B5228837 : Blo 1084620 5228837 := bbase (se 4 (by rfl) ⟨490203, by rfl⟩ : syracuseStep 5228837 = 980407) (by norm_num)
theorem B2443589 : Blo 1084620 2443589 := bbase (se 4 (by rfl) ⟨229086, by rfl⟩ : syracuseStep 2443589 = 458173) (by norm_num)
theorem B2607461 : Blo 1084620 2607461 := bbase (se 4 (by rfl) ⟨244449, by rfl⟩ : syracuseStep 2607461 = 488899) (by norm_num)
theorem B2443661 : Blo 1084620 2443661 := bbase (se 3 (by rfl) ⟨458186, by rfl⟩ : syracuseStep 2443661 = 916373) (by norm_num)
theorem B4180405 : Blo 1084620 4180405 := bbase (se 5 (by rfl) ⟨195956, by rfl⟩ : syracuseStep 4180405 = 391913) (by norm_num)
theorem B2443733 : Blo 1084620 2443733 := bbase (se 7 (by rfl) ⟨28637, by rfl⟩ : syracuseStep 2443733 = 57275) (by norm_num)
theorem B19843541 : Blo 1084620 19843541 := bbase (se 7 (by rfl) ⟨232541, by rfl⟩ : syracuseStep 19843541 = 465083) (by norm_num)
theorem B2443805 : Blo 1084620 2443805 := bbase (se 3 (by rfl) ⟨458213, by rfl⟩ : syracuseStep 2443805 = 916427) (by norm_num)
theorem B2607653 : Blo 1084620 2607653 := bbase (se 4 (by rfl) ⟨244467, by rfl⟩ : syracuseStep 2607653 = 488935) (by norm_num)
theorem B3820117 : Blo 1084620 3820117 := bbase (se 8 (by rfl) ⟨22383, by rfl⟩ : syracuseStep 3820117 = 44767) (by norm_num)
theorem B2443877 : Blo 1084620 2443877 := bbase (se 4 (by rfl) ⟨229113, by rfl⟩ : syracuseStep 2443877 = 458227) (by norm_num)
theorem B1100461 : Blo 1084620 1100461 := bbase (se 3 (by rfl) ⟨206336, by rfl⟩ : syracuseStep 1100461 = 412673) (by norm_num)
theorem B2443949 : Blo 1084620 2443949 := bbase (se 3 (by rfl) ⟨458240, by rfl⟩ : syracuseStep 2443949 = 916481) (by norm_num)
theorem B1100477 : Blo 1084620 1100477 := bbase (se 3 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 1100477 = 412679) (by norm_num)
theorem B20859605 : Blo 1084620 20859605 := bbase (se 7 (by rfl) ⟨244448, by rfl⟩ : syracuseStep 20859605 = 488897) (by norm_num)
theorem B2444021 : Blo 1084620 2444021 := bbase (se 5 (by rfl) ⟨114563, by rfl⟩ : syracuseStep 2444021 = 229127) (by norm_num)
theorem B2444093 : Blo 1084620 2444093 := bbase (se 3 (by rfl) ⟨458267, by rfl⟩ : syracuseStep 2444093 = 916535) (by norm_num)
theorem B1395541 : Blo 1084620 1395541 := bbase (se 9 (by rfl) ⟨4088, by rfl⟩ : syracuseStep 1395541 = 8177) (by norm_num)
theorem B5884757 : Blo 1084620 5884757 := bbase (se 9 (by rfl) ⟨17240, by rfl⟩ : syracuseStep 5884757 = 34481) (by norm_num)
theorem B2444165 : Blo 1084620 2444165 := bbase (se 4 (by rfl) ⟨229140, by rfl⟩ : syracuseStep 2444165 = 458281) (by norm_num)
theorem B5491637 : Blo 1084620 5491637 := bbase (se 5 (by rfl) ⟨257420, by rfl⟩ : syracuseStep 5491637 = 514841) (by norm_num)
theorem B5721013 : Blo 1084620 5721013 := bbase (se 5 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 5721013 = 536345) (by norm_num)
theorem B2444237 : Blo 1084620 2444237 := bbase (se 3 (by rfl) ⟨458294, by rfl⟩ : syracuseStep 2444237 = 916589) (by norm_num)
theorem B4410325 : Blo 1084620 4410325 := bbase (se 7 (by rfl) ⟨51683, by rfl⟩ : syracuseStep 4410325 = 103367) (by norm_num)
theorem B2444309 : Blo 1084620 2444309 := bbase (se 6 (by rfl) ⟨57288, by rfl⟩ : syracuseStep 2444309 = 114577) (by norm_num)
theorem B3918917 : Blo 1084620 3918917 := bbase (se 4 (by rfl) ⟨367398, by rfl⟩ : syracuseStep 3918917 = 734797) (by norm_num)
theorem B2444381 : Blo 1084620 2444381 := bbase (se 3 (by rfl) ⟨458321, by rfl⟩ : syracuseStep 2444381 = 916643) (by norm_num)
theorem B2444453 : Blo 1084620 2444453 := bbase (se 4 (by rfl) ⟨229167, by rfl⟩ : syracuseStep 2444453 = 458335) (by norm_num)
theorem B3099845 : Blo 1084620 3099845 := bbase (se 4 (by rfl) ⟨290610, by rfl⟩ : syracuseStep 3099845 = 581221) (by norm_num)
theorem B2444525 : Blo 1084620 2444525 := bbase (se 3 (by rfl) ⟨458348, by rfl⟩ : syracuseStep 2444525 = 916697) (by norm_num)
theorem B1101061 : Blo 1084620 1101061 := bbase (se 4 (by rfl) ⟨103224, by rfl⟩ : syracuseStep 1101061 = 206449) (by norm_num)
theorem B2444597 : Blo 1084620 2444597 := bbase (se 5 (by rfl) ⟨114590, by rfl⟩ : syracuseStep 2444597 = 229181) (by norm_num)
theorem B2444669 : Blo 1084620 2444669 := bbase (se 3 (by rfl) ⟨458375, by rfl⟩ : syracuseStep 2444669 = 916751) (by norm_num)
theorem B2444741 : Blo 1084620 2444741 := bbase (se 4 (by rfl) ⟨229194, by rfl⟩ : syracuseStep 2444741 = 458389) (by norm_num)
theorem B2608613 : Blo 1084620 2608613 := bbase (se 4 (by rfl) ⟨244557, by rfl⟩ : syracuseStep 2608613 = 489115) (by norm_num)
theorem B2444813 : Blo 1084620 2444813 := bbase (se 3 (by rfl) ⟨458402, by rfl⟩ : syracuseStep 2444813 = 916805) (by norm_num)
theorem B2444885 : Blo 1084620 2444885 := bbase (se 8 (by rfl) ⟨14325, by rfl⟩ : syracuseStep 2444885 = 28651) (by norm_num)
theorem B2444957 : Blo 1084620 2444957 := bbase (se 3 (by rfl) ⟨458429, by rfl⟩ : syracuseStep 2444957 = 916859) (by norm_num)
theorem B10440373 : Blo 1084620 10440373 := bbase (se 5 (by rfl) ⟨489392, by rfl⟩ : syracuseStep 10440373 = 978785) (by norm_num)
theorem B2445029 : Blo 1084620 2445029 := bbase (se 4 (by rfl) ⟨229221, by rfl⟩ : syracuseStep 2445029 = 458443) (by norm_num)
theorem B2445101 : Blo 1084620 2445101 := bbase (se 3 (by rfl) ⟨458456, by rfl⟩ : syracuseStep 2445101 = 916913) (by norm_num)
theorem B2445173 : Blo 1084620 2445173 := bbase (se 5 (by rfl) ⟨114617, by rfl⟩ : syracuseStep 2445173 = 229235) (by norm_num)
theorem B2445245 : Blo 1084620 2445245 := bbase (se 3 (by rfl) ⟨458483, by rfl⟩ : syracuseStep 2445245 = 916967) (by norm_num)
theorem B2445317 : Blo 1084620 2445317 := bbase (se 4 (by rfl) ⟨229248, by rfl⟩ : syracuseStep 2445317 = 458497) (by norm_num)
theorem B2445389 : Blo 1084620 2445389 := bbase (se 3 (by rfl) ⟨458510, by rfl⟩ : syracuseStep 2445389 = 917021) (by norm_num)
theorem B4182101 : Blo 1084620 4182101 := bbase (se 8 (by rfl) ⟨24504, by rfl⟩ : syracuseStep 4182101 = 49009) (by norm_num)
theorem B2445461 : Blo 1084620 2445461 := bbase (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) (by norm_num)
theorem B3723413 : Blo 1084620 3723413 := bbase (se 6 (by rfl) ⟨87267, by rfl⟩ : syracuseStep 3723413 = 174535) (by norm_num)
theorem B5492933 : Blo 1084620 5492933 := bbase (se 4 (by rfl) ⟨514962, by rfl⟩ : syracuseStep 5492933 = 1029925) (by norm_num)
theorem B2445533 : Blo 1084620 2445533 := bbase (se 3 (by rfl) ⟨458537, by rfl⟩ : syracuseStep 2445533 = 917075) (by norm_num)
theorem B2445605 : Blo 1084620 2445605 := bbase (se 4 (by rfl) ⟨229275, by rfl⟩ : syracuseStep 2445605 = 458551) (by norm_num)
theorem B23482709 : Blo 1084620 23482709 := bbase (se 10 (by rfl) ⟨34398, by rfl⟩ : syracuseStep 23482709 = 68797) (by norm_num)
theorem B2445677 : Blo 1084620 2445677 := bbase (se 3 (by rfl) ⟨458564, by rfl⟩ : syracuseStep 2445677 = 917129) (by norm_num)
theorem B2445749 : Blo 1084620 2445749 := bbase (se 5 (by rfl) ⟨114644, by rfl⟩ : syracuseStep 2445749 = 229289) (by norm_num)
theorem B1102325 : Blo 1084620 1102325 := bbase (se 5 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 1102325 = 103343) (by norm_num)
theorem B2445821 : Blo 1084620 2445821 := bbase (se 3 (by rfl) ⟨458591, by rfl⟩ : syracuseStep 2445821 = 917183) (by norm_num)
theorem B2642453 : Blo 1084620 2642453 := bbase (se 6 (by rfl) ⟨61932, by rfl⟩ : syracuseStep 2642453 = 123865) (by norm_num)
theorem B2445893 : Blo 1084620 2445893 := bbase (se 4 (by rfl) ⟨229302, by rfl⟩ : syracuseStep 2445893 = 458605) (by norm_num)
theorem B2445965 : Blo 1084620 2445965 := bbase (se 3 (by rfl) ⟨458618, by rfl⟩ : syracuseStep 2445965 = 917237) (by norm_num)
theorem B2446037 : Blo 1084620 2446037 := bbase (se 7 (by rfl) ⟨28664, by rfl⟩ : syracuseStep 2446037 = 57329) (by norm_num)
theorem B2478845 : Blo 1084620 2478845 := bbase (se 3 (by rfl) ⟨464783, by rfl⟩ : syracuseStep 2478845 = 929567) (by norm_num)
theorem B2446109 : Blo 1084620 2446109 := bbase (se 3 (by rfl) ⟨458645, by rfl⟩ : syracuseStep 2446109 = 917291) (by norm_num)
theorem B1626941 : Blo 1084620 1626941 := bbase (se 3 (by rfl) ⟨305051, by rfl⟩ : syracuseStep 1626941 = 610103) (by norm_num)
theorem B1626965 : Blo 1084620 1626965 := bbase (se 9 (by rfl) ⟨4766, by rfl⟩ : syracuseStep 1626965 = 9533) (by norm_num)
theorem B2446181 : Blo 1084620 2446181 := bbase (se 4 (by rfl) ⟨229329, by rfl⟩ : syracuseStep 2446181 = 458659) (by norm_num)
theorem B1626989 : Blo 1084620 1626989 := bbase (se 3 (by rfl) ⟨305060, by rfl⟩ : syracuseStep 1626989 = 610121) (by norm_num)
theorem B1627013 : Blo 1084620 1627013 := bbase (se 4 (by rfl) ⟨152532, by rfl⟩ : syracuseStep 1627013 = 305065) (by norm_num)
theorem B1627037 : Blo 1084620 1627037 := bbase (se 3 (by rfl) ⟨305069, by rfl⟩ : syracuseStep 1627037 = 610139) (by norm_num)
theorem B2446253 : Blo 1084620 2446253 := bbase (se 3 (by rfl) ⟨458672, by rfl⟩ : syracuseStep 2446253 = 917345) (by norm_num)
theorem B1627061 : Blo 1084620 1627061 := bbase (se 5 (by rfl) ⟨76268, by rfl⟩ : syracuseStep 1627061 = 152537) (by norm_num)
theorem B1627085 : Blo 1084620 1627085 := bbase (se 3 (by rfl) ⟨305078, by rfl⟩ : syracuseStep 1627085 = 610157) (by norm_num)
theorem B1627109 : Blo 1084620 1627109 := bbase (se 4 (by rfl) ⟨152541, by rfl⟩ : syracuseStep 1627109 = 305083) (by norm_num)
theorem B2446325 : Blo 1084620 2446325 := bbase (se 5 (by rfl) ⟨114671, by rfl⟩ : syracuseStep 2446325 = 229343) (by norm_num)
theorem B1627133 : Blo 1084620 1627133 := bbase (se 3 (by rfl) ⟨305087, by rfl⟩ : syracuseStep 1627133 = 610175) (by norm_num)
theorem B1627157 : Blo 1084620 1627157 := bbase (se 6 (by rfl) ⟨38136, by rfl⟩ : syracuseStep 1627157 = 76273) (by norm_num)
theorem B1627181 : Blo 1084620 1627181 := bbase (se 3 (by rfl) ⟨305096, by rfl⟩ : syracuseStep 1627181 = 610193) (by norm_num)
theorem B2446397 : Blo 1084620 2446397 := bbase (se 3 (by rfl) ⟨458699, by rfl⟩ : syracuseStep 2446397 = 917399) (by norm_num)
theorem B1627205 : Blo 1084620 1627205 := bbase (se 4 (by rfl) ⟨152550, by rfl⟩ : syracuseStep 1627205 = 305101) (by norm_num)
theorem B3822661 : Blo 1084620 3822661 := bbase (se 4 (by rfl) ⟨358374, by rfl⟩ : syracuseStep 3822661 = 716749) (by norm_num)
theorem B1627229 : Blo 1084620 1627229 := bbase (se 3 (by rfl) ⟨305105, by rfl⟩ : syracuseStep 1627229 = 610211) (by norm_num)
theorem B4641893 : Blo 1084620 4641893 := bbase (se 4 (by rfl) ⟨435177, by rfl⟩ : syracuseStep 4641893 = 870355) (by norm_num)
theorem B1627253 : Blo 1084620 1627253 := bbase (se 5 (by rfl) ⟨76277, by rfl⟩ : syracuseStep 1627253 = 152555) (by norm_num)
theorem B2446469 : Blo 1084620 2446469 := bbase (se 4 (by rfl) ⟨229356, by rfl⟩ : syracuseStep 2446469 = 458713) (by norm_num)
theorem B1627277 : Blo 1084620 1627277 := bbase (se 3 (by rfl) ⟨305114, by rfl⟩ : syracuseStep 1627277 = 610229) (by norm_num)
theorem B1627301 : Blo 1084620 1627301 := bbase (se 4 (by rfl) ⟨152559, by rfl⟩ : syracuseStep 1627301 = 305119) (by norm_num)
theorem B6968501 : Blo 1084620 6968501 := bbase (se 5 (by rfl) ⟨326648, by rfl⟩ : syracuseStep 6968501 = 653297) (by norm_num)
theorem B1627325 : Blo 1084620 1627325 := bbase (se 3 (by rfl) ⟨305123, by rfl⟩ : syracuseStep 1627325 = 610247) (by norm_num)
theorem B2446541 : Blo 1084620 2446541 := bbase (se 3 (by rfl) ⟨458726, by rfl⟩ : syracuseStep 2446541 = 917453) (by norm_num)
theorem B1627349 : Blo 1084620 1627349 := bbase (se 7 (by rfl) ⟨19070, by rfl⟩ : syracuseStep 1627349 = 38141) (by norm_num)
theorem B1627373 : Blo 1084620 1627373 := bbase (se 3 (by rfl) ⟨305132, by rfl⟩ : syracuseStep 1627373 = 610265) (by norm_num)
theorem B1627397 : Blo 1084620 1627397 := bbase (se 4 (by rfl) ⟨152568, by rfl⟩ : syracuseStep 1627397 = 305137) (by norm_num)
theorem B2446613 : Blo 1084620 2446613 := bbase (se 6 (by rfl) ⟨57342, by rfl⟩ : syracuseStep 2446613 = 114685) (by norm_num)
theorem B1627421 : Blo 1084620 1627421 := bbase (se 3 (by rfl) ⟨305141, by rfl⟩ : syracuseStep 1627421 = 610283) (by norm_num)
theorem B1627445 : Blo 1084620 1627445 := bbase (se 5 (by rfl) ⟨76286, by rfl⟩ : syracuseStep 1627445 = 152573) (by norm_num)
theorem B1627469 : Blo 1084620 1627469 := bbase (se 3 (by rfl) ⟨305150, by rfl⟩ : syracuseStep 1627469 = 610301) (by norm_num)
theorem B2446685 : Blo 1084620 2446685 := bbase (se 3 (by rfl) ⟨458753, by rfl⟩ : syracuseStep 2446685 = 917507) (by norm_num)
theorem B1627493 : Blo 1084620 1627493 := bbase (se 4 (by rfl) ⟨152577, by rfl⟩ : syracuseStep 1627493 = 305155) (by norm_num)
theorem B1627517 : Blo 1084620 1627517 := bbase (se 3 (by rfl) ⟨305159, by rfl⟩ : syracuseStep 1627517 = 610319) (by norm_num)
theorem B4642181 : Blo 1084620 4642181 := bbase (se 4 (by rfl) ⟨435204, by rfl⟩ : syracuseStep 4642181 = 870409) (by norm_num)
theorem B1627541 : Blo 1084620 1627541 := bbase (se 6 (by rfl) ⟨38145, by rfl⟩ : syracuseStep 1627541 = 76291) (by norm_num)
theorem B2446757 : Blo 1084620 2446757 := bbase (se 4 (by rfl) ⟨229383, by rfl⟩ : syracuseStep 2446757 = 458767) (by norm_num)
theorem B1627565 : Blo 1084620 1627565 := bbase (se 3 (by rfl) ⟨305168, by rfl⟩ : syracuseStep 1627565 = 610337) (by norm_num)
theorem B1627589 : Blo 1084620 1627589 := bbase (se 4 (by rfl) ⟨152586, by rfl⟩ : syracuseStep 1627589 = 305173) (by norm_num)
theorem B5494229 : Blo 1084620 5494229 := bbase (se 7 (by rfl) ⟨64385, by rfl⟩ : syracuseStep 5494229 = 128771) (by norm_num)
theorem B1627613 : Blo 1084620 1627613 := bbase (se 3 (by rfl) ⟨305177, by rfl⟩ : syracuseStep 1627613 = 610355) (by norm_num)
theorem B2446829 : Blo 1084620 2446829 := bbase (se 3 (by rfl) ⟨458780, by rfl⟩ : syracuseStep 2446829 = 917561) (by norm_num)
theorem B1627637 : Blo 1084620 1627637 := bbase (se 5 (by rfl) ⟨76295, by rfl⟩ : syracuseStep 1627637 = 152591) (by norm_num)
theorem B1627661 : Blo 1084620 1627661 := bbase (se 3 (by rfl) ⟨305186, by rfl⟩ : syracuseStep 1627661 = 610373) (by norm_num)
theorem B1627685 : Blo 1084620 1627685 := bbase (se 4 (by rfl) ⟨152595, by rfl⟩ : syracuseStep 1627685 = 305191) (by norm_num)
theorem B2446901 : Blo 1084620 2446901 := bbase (se 5 (by rfl) ⟨114698, by rfl⟩ : syracuseStep 2446901 = 229397) (by norm_num)
theorem B1627709 : Blo 1084620 1627709 := bbase (se 3 (by rfl) ⟨305195, by rfl⟩ : syracuseStep 1627709 = 610391) (by norm_num)
theorem B1103429 : Blo 1084620 1103429 := bbase (se 4 (by rfl) ⟨103446, by rfl⟩ : syracuseStep 1103429 = 206893) (by norm_num)
theorem B1627733 : Blo 1084620 1627733 := bbase (se 8 (by rfl) ⟨9537, by rfl⟩ : syracuseStep 1627733 = 19075) (by norm_num)
theorem B1627757 : Blo 1084620 1627757 := bbase (se 3 (by rfl) ⟨305204, by rfl⟩ : syracuseStep 1627757 = 610409) (by norm_num)
theorem B2446973 : Blo 1084620 2446973 := bbase (se 3 (by rfl) ⟨458807, by rfl⟩ : syracuseStep 2446973 = 917615) (by norm_num)
theorem B1627781 : Blo 1084620 1627781 := bbase (se 4 (by rfl) ⟨152604, by rfl⟩ : syracuseStep 1627781 = 305209) (by norm_num)
theorem B8246933 : Blo 1084620 8246933 := bbase (se 6 (by rfl) ⟨193287, by rfl⟩ : syracuseStep 8246933 = 386575) (by norm_num)
theorem B1627805 : Blo 1084620 1627805 := bbase (se 3 (by rfl) ⟨305213, by rfl⟩ : syracuseStep 1627805 = 610427) (by norm_num)
theorem B1627829 : Blo 1084620 1627829 := bbase (se 5 (by rfl) ⟨76304, by rfl⟩ : syracuseStep 1627829 = 152609) (by norm_num)
theorem B2447045 : Blo 1084620 2447045 := bbase (se 4 (by rfl) ⟨229410, by rfl⟩ : syracuseStep 2447045 = 458821) (by norm_num)
theorem B1627853 : Blo 1084620 1627853 := bbase (se 3 (by rfl) ⟨305222, by rfl⟩ : syracuseStep 1627853 = 610445) (by norm_num)
theorem B1627877 : Blo 1084620 1627877 := bbase (se 4 (by rfl) ⟨152613, by rfl⟩ : syracuseStep 1627877 = 305227) (by norm_num)
theorem B1627901 : Blo 1084620 1627901 := bbase (se 3 (by rfl) ⟨305231, by rfl⟩ : syracuseStep 1627901 = 610463) (by norm_num)
theorem B2447117 : Blo 1084620 2447117 := bbase (se 3 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 2447117 = 917669) (by norm_num)
theorem B1627925 : Blo 1084620 1627925 := bbase (se 6 (by rfl) ⟨38154, by rfl⟩ : syracuseStep 1627925 = 76309) (by norm_num)
theorem B1627949 : Blo 1084620 1627949 := bbase (se 3 (by rfl) ⟨305240, by rfl⟩ : syracuseStep 1627949 = 610481) (by norm_num)
theorem B1627973 : Blo 1084620 1627973 := bbase (se 4 (by rfl) ⟨152622, by rfl⟩ : syracuseStep 1627973 = 305245) (by norm_num)
theorem B2447189 : Blo 1084620 2447189 := bbase (se 9 (by rfl) ⟨7169, by rfl⟩ : syracuseStep 2447189 = 14339) (by norm_num)
theorem B1627997 : Blo 1084620 1627997 := bbase (se 3 (by rfl) ⟨305249, by rfl⟩ : syracuseStep 1627997 = 610499) (by norm_num)
theorem B1628021 : Blo 1084620 1628021 := bbase (se 5 (by rfl) ⟨76313, by rfl⟩ : syracuseStep 1628021 = 152627) (by norm_num)
theorem B1628045 : Blo 1084620 1628045 := bbase (se 3 (by rfl) ⟨305258, by rfl⟩ : syracuseStep 1628045 = 610517) (by norm_num)
theorem B2447261 : Blo 1084620 2447261 := bbase (se 3 (by rfl) ⟨458861, by rfl⟩ : syracuseStep 2447261 = 917723) (by norm_num)
theorem B1628069 : Blo 1084620 1628069 := bbase (se 4 (by rfl) ⟨152631, by rfl⟩ : syracuseStep 1628069 = 305263) (by norm_num)
theorem B1628093 : Blo 1084620 1628093 := bbase (se 3 (by rfl) ⟨305267, by rfl⟩ : syracuseStep 1628093 = 610535) (by norm_num)
theorem B4118485 : Blo 1084620 4118485 := bbase (se 7 (by rfl) ⟨48263, by rfl⟩ : syracuseStep 4118485 = 96527) (by norm_num)
theorem B1628117 : Blo 1084620 1628117 := bbase (se 7 (by rfl) ⟨19079, by rfl⟩ : syracuseStep 1628117 = 38159) (by norm_num)
theorem B2447333 : Blo 1084620 2447333 := bbase (se 4 (by rfl) ⟨229437, by rfl⟩ : syracuseStep 2447333 = 458875) (by norm_num)
theorem B1628141 : Blo 1084620 1628141 := bbase (se 3 (by rfl) ⟨305276, by rfl⟩ : syracuseStep 1628141 = 610553) (by norm_num)
theorem B1628165 : Blo 1084620 1628165 := bbase (se 4 (by rfl) ⟨152640, by rfl⟩ : syracuseStep 1628165 = 305281) (by norm_num)
theorem B1628189 : Blo 1084620 1628189 := bbase (se 3 (by rfl) ⟨305285, by rfl⟩ : syracuseStep 1628189 = 610571) (by norm_num)
theorem B2447405 : Blo 1084620 2447405 := bbase (se 3 (by rfl) ⟨458888, by rfl⟩ : syracuseStep 2447405 = 917777) (by norm_num)
theorem B1628213 : Blo 1084620 1628213 := bbase (se 5 (by rfl) ⟨76322, by rfl⟩ : syracuseStep 1628213 = 152645) (by norm_num)
theorem B1628237 : Blo 1084620 1628237 := bbase (se 3 (by rfl) ⟨305294, by rfl⟩ : syracuseStep 1628237 = 610589) (by norm_num)
theorem B1628261 : Blo 1084620 1628261 := bbase (se 4 (by rfl) ⟨152649, by rfl⟩ : syracuseStep 1628261 = 305299) (by norm_num)
theorem B4642933 : Blo 1084620 4642933 := bbase (se 5 (by rfl) ⟨217637, by rfl⟩ : syracuseStep 4642933 = 435275) (by norm_num)
theorem B2447477 : Blo 1084620 2447477 := bbase (se 5 (by rfl) ⟨114725, by rfl⟩ : syracuseStep 2447477 = 229451) (by norm_num)
theorem B1628285 : Blo 1084620 1628285 := bbase (se 3 (by rfl) ⟨305303, by rfl⟩ : syracuseStep 1628285 = 610607) (by norm_num)
theorem B1628309 : Blo 1084620 1628309 := bbase (se 6 (by rfl) ⟨38163, by rfl⟩ : syracuseStep 1628309 = 76327) (by norm_num)
theorem B1628333 : Blo 1084620 1628333 := bbase (se 3 (by rfl) ⟨305312, by rfl⟩ : syracuseStep 1628333 = 610625) (by norm_num)
theorem B2611381 : Blo 1084620 2611381 := bbase (se 5 (by rfl) ⟨122408, by rfl⟩ : syracuseStep 2611381 = 244817) (by norm_num)
theorem B2447549 : Blo 1084620 2447549 := bbase (se 3 (by rfl) ⟨458915, by rfl⟩ : syracuseStep 2447549 = 917831) (by norm_num)
theorem B1628357 : Blo 1084620 1628357 := bbase (se 4 (by rfl) ⟨152658, by rfl⟩ : syracuseStep 1628357 = 305317) (by norm_num)
theorem B1628381 : Blo 1084620 1628381 := bbase (se 3 (by rfl) ⟨305321, by rfl⟩ : syracuseStep 1628381 = 610643) (by norm_num)
theorem B1628405 : Blo 1084620 1628405 := bbase (se 5 (by rfl) ⟨76331, by rfl⟩ : syracuseStep 1628405 = 152663) (by norm_num)
theorem B9296117 : Blo 1084620 9296117 := bbase (se 5 (by rfl) ⟨435755, by rfl⟩ : syracuseStep 9296117 = 871511) (by norm_num)
theorem B4118789 : Blo 1084620 4118789 := bbase (se 4 (by rfl) ⟨386136, by rfl⟩ : syracuseStep 4118789 = 772273) (by norm_num)
theorem B2447621 : Blo 1084620 2447621 := bbase (se 4 (by rfl) ⟨229464, by rfl⟩ : syracuseStep 2447621 = 458929) (by norm_num)
theorem B1628429 : Blo 1084620 1628429 := bbase (se 3 (by rfl) ⟨305330, by rfl⟩ : syracuseStep 1628429 = 610661) (by norm_num)
theorem B1628453 : Blo 1084620 1628453 := bbase (se 4 (by rfl) ⟨152667, by rfl⟩ : syracuseStep 1628453 = 305335) (by norm_num)
theorem B1628477 : Blo 1084620 1628477 := bbase (se 3 (by rfl) ⟨305339, by rfl⟩ : syracuseStep 1628477 = 610679) (by norm_num)
theorem B2447693 : Blo 1084620 2447693 := bbase (se 3 (by rfl) ⟨458942, by rfl⟩ : syracuseStep 2447693 = 917885) (by norm_num)
theorem B1628501 : Blo 1084620 1628501 := bbase (se 10 (by rfl) ⟨2385, by rfl⟩ : syracuseStep 1628501 = 4771) (by norm_num)
theorem B1628525 : Blo 1084620 1628525 := bbase (se 3 (by rfl) ⟨305348, by rfl⟩ : syracuseStep 1628525 = 610697) (by norm_num)
theorem B1628549 : Blo 1084620 1628549 := bbase (se 4 (by rfl) ⟨152676, by rfl⟩ : syracuseStep 1628549 = 305353) (by norm_num)
theorem B2447765 : Blo 1084620 2447765 := bbase (se 6 (by rfl) ⟨57369, by rfl⟩ : syracuseStep 2447765 = 114739) (by norm_num)
theorem B1628573 : Blo 1084620 1628573 := bbase (se 3 (by rfl) ⟨305357, by rfl⟩ : syracuseStep 1628573 = 610715) (by norm_num)
theorem B1628597 : Blo 1084620 1628597 := bbase (se 5 (by rfl) ⟨76340, by rfl⟩ : syracuseStep 1628597 = 152681) (by norm_num)
theorem B1628621 : Blo 1084620 1628621 := bbase (se 3 (by rfl) ⟨305366, by rfl⟩ : syracuseStep 1628621 = 610733) (by norm_num)
theorem B2447837 : Blo 1084620 2447837 := bbase (se 3 (by rfl) ⟨458969, by rfl⟩ : syracuseStep 2447837 = 917939) (by norm_num)
theorem B1628645 : Blo 1084620 1628645 := bbase (se 4 (by rfl) ⟨152685, by rfl⟩ : syracuseStep 1628645 = 305371) (by norm_num)
theorem B1628669 : Blo 1084620 1628669 := bbase (se 3 (by rfl) ⟨305375, by rfl⟩ : syracuseStep 1628669 = 610751) (by norm_num)
theorem B1628693 : Blo 1084620 1628693 := bbase (se 6 (by rfl) ⟨38172, by rfl⟩ : syracuseStep 1628693 = 76345) (by norm_num)
theorem B2447909 : Blo 1084620 2447909 := bbase (se 4 (by rfl) ⟨229491, by rfl⟩ : syracuseStep 2447909 = 458983) (by norm_num)
theorem B1628717 : Blo 1084620 1628717 := bbase (se 3 (by rfl) ⟨305384, by rfl⟩ : syracuseStep 1628717 = 610769) (by norm_num)
theorem B2611757 : Blo 1084620 2611757 := bbase (se 3 (by rfl) ⟨489704, by rfl⟩ : syracuseStep 2611757 = 979409) (by norm_num)
theorem B2316853 : Blo 1084620 2316853 := bbase (se 5 (by rfl) ⟨108602, by rfl⟩ : syracuseStep 2316853 = 217205) (by norm_num)
theorem B1628741 : Blo 1084620 1628741 := bbase (se 4 (by rfl) ⟨152694, by rfl⟩ : syracuseStep 1628741 = 305389) (by norm_num)
theorem B1628765 : Blo 1084620 1628765 := bbase (se 3 (by rfl) ⟨305393, by rfl⟩ : syracuseStep 1628765 = 610787) (by norm_num)
theorem B2447981 : Blo 1084620 2447981 := bbase (se 3 (by rfl) ⟨458996, by rfl⟩ : syracuseStep 2447981 = 917993) (by norm_num)
theorem B1628789 : Blo 1084620 1628789 := bbase (se 5 (by rfl) ⟨76349, by rfl⟩ : syracuseStep 1628789 = 152699) (by norm_num)
theorem B1628813 : Blo 1084620 1628813 := bbase (se 3 (by rfl) ⟨305402, by rfl⟩ : syracuseStep 1628813 = 610805) (by norm_num)
theorem B1628837 : Blo 1084620 1628837 := bbase (se 4 (by rfl) ⟨152703, by rfl⟩ : syracuseStep 1628837 = 305407) (by norm_num)
theorem B2448053 : Blo 1084620 2448053 := bbase (se 5 (by rfl) ⟨114752, by rfl⟩ : syracuseStep 2448053 = 229505) (by norm_num)
theorem B1628861 : Blo 1084620 1628861 := bbase (se 3 (by rfl) ⟨305411, by rfl⟩ : syracuseStep 1628861 = 610823) (by norm_num)
theorem B1628885 : Blo 1084620 1628885 := bbase (se 7 (by rfl) ⟨19088, by rfl⟩ : syracuseStep 1628885 = 38177) (by norm_num)
theorem B5495525 : Blo 1084620 5495525 := bbase (se 4 (by rfl) ⟨515205, by rfl⟩ : syracuseStep 5495525 = 1030411) (by norm_num)
theorem B1628909 : Blo 1084620 1628909 := bbase (se 3 (by rfl) ⟨305420, by rfl⟩ : syracuseStep 1628909 = 610841) (by norm_num)
theorem B2448125 : Blo 1084620 2448125 := bbase (se 3 (by rfl) ⟨459023, by rfl⟩ : syracuseStep 2448125 = 918047) (by norm_num)
theorem B1628933 : Blo 1084620 1628933 := bbase (se 4 (by rfl) ⟨152712, by rfl⟩ : syracuseStep 1628933 = 305425) (by norm_num)
theorem B1628957 : Blo 1084620 1628957 := bbase (se 3 (by rfl) ⟨305429, by rfl⟩ : syracuseStep 1628957 = 610859) (by norm_num)
theorem B1628981 : Blo 1084620 1628981 := bbase (se 5 (by rfl) ⟨76358, by rfl⟩ : syracuseStep 1628981 = 152717) (by norm_num)
theorem B2448197 : Blo 1084620 2448197 := bbase (se 4 (by rfl) ⟨229518, by rfl⟩ : syracuseStep 2448197 = 459037) (by norm_num)
theorem B1629005 : Blo 1084620 1629005 := bbase (se 3 (by rfl) ⟨305438, by rfl⟩ : syracuseStep 1629005 = 610877) (by norm_num)
theorem B4643669 : Blo 1084620 4643669 := bbase (se 9 (by rfl) ⟨13604, by rfl⟩ : syracuseStep 4643669 = 27209) (by norm_num)
theorem B1629029 : Blo 1084620 1629029 := bbase (se 4 (by rfl) ⟨152721, by rfl⟩ : syracuseStep 1629029 = 305443) (by norm_num)
theorem B1629053 : Blo 1084620 1629053 := bbase (se 3 (by rfl) ⟨305447, by rfl⟩ : syracuseStep 1629053 = 610895) (by norm_num)
theorem B2448269 : Blo 1084620 2448269 := bbase (se 3 (by rfl) ⟨459050, by rfl⟩ : syracuseStep 2448269 = 918101) (by norm_num)
theorem B1629077 : Blo 1084620 1629077 := bbase (se 6 (by rfl) ⟨38181, by rfl⟩ : syracuseStep 1629077 = 76363) (by norm_num)
theorem B1629101 : Blo 1084620 1629101 := bbase (se 3 (by rfl) ⟨305456, by rfl⟩ : syracuseStep 1629101 = 610913) (by norm_num)
theorem B1629125 : Blo 1084620 1629125 := bbase (se 4 (by rfl) ⟨152730, by rfl⟩ : syracuseStep 1629125 = 305461) (by norm_num)
theorem B2448341 : Blo 1084620 2448341 := bbase (se 7 (by rfl) ⟨28691, by rfl⟩ : syracuseStep 2448341 = 57383) (by norm_num)
theorem B1629149 : Blo 1084620 1629149 := bbase (se 3 (by rfl) ⟨305465, by rfl⟩ : syracuseStep 1629149 = 610931) (by norm_num)
theorem B2612189 : Blo 1084620 2612189 := bbase (se 3 (by rfl) ⟨489785, by rfl⟩ : syracuseStep 2612189 = 979571) (by norm_num)
theorem B1629173 : Blo 1084620 1629173 := bbase (se 5 (by rfl) ⟨76367, by rfl⟩ : syracuseStep 1629173 = 152735) (by norm_num)
theorem B1629197 : Blo 1084620 1629197 := bbase (se 3 (by rfl) ⟨305474, by rfl⟩ : syracuseStep 1629197 = 610949) (by norm_num)
theorem B3660821 : Blo 1084620 3660821 := bbase (se 6 (by rfl) ⟨85800, by rfl⟩ : syracuseStep 3660821 = 171601) (by norm_num)
theorem B2448413 : Blo 1084620 2448413 := bbase (se 3 (by rfl) ⟨459077, by rfl⟩ : syracuseStep 2448413 = 918155) (by norm_num)
theorem B2317349 : Blo 1084620 2317349 := bbase (se 4 (by rfl) ⟨217251, by rfl⟩ : syracuseStep 2317349 = 434503) (by norm_num)
theorem B1629221 : Blo 1084620 1629221 := bbase (se 4 (by rfl) ⟨152739, by rfl⟩ : syracuseStep 1629221 = 305479) (by norm_num)
theorem B1629245 : Blo 1084620 1629245 := bbase (se 3 (by rfl) ⟨305483, by rfl⟩ : syracuseStep 1629245 = 610967) (by norm_num)
theorem B1629269 : Blo 1084620 1629269 := bbase (se 8 (by rfl) ⟨9546, by rfl⟩ : syracuseStep 1629269 = 19093) (by norm_num)
theorem B2939989 : Blo 1084620 2939989 := bbase (se 8 (by rfl) ⟨17226, by rfl⟩ : syracuseStep 2939989 = 34453) (by norm_num)
theorem B2448485 : Blo 1084620 2448485 := bbase (se 4 (by rfl) ⟨229545, by rfl⟩ : syracuseStep 2448485 = 459091) (by norm_num)
theorem B1956973 : Blo 1084620 1956973 := bbase (se 3 (by rfl) ⟨366932, by rfl⟩ : syracuseStep 1956973 = 733865) (by norm_num)
theorem B1629293 : Blo 1084620 1629293 := bbase (se 3 (by rfl) ⟨305492, by rfl⟩ : syracuseStep 1629293 = 610985) (by norm_num)
theorem B1629317 : Blo 1084620 1629317 := bbase (se 4 (by rfl) ⟨152748, by rfl⟩ : syracuseStep 1629317 = 305497) (by norm_num)
theorem B1629341 : Blo 1084620 1629341 := bbase (se 3 (by rfl) ⟨305501, by rfl⟩ : syracuseStep 1629341 = 611003) (by norm_num)
theorem B2448557 : Blo 1084620 2448557 := bbase (se 3 (by rfl) ⟨459104, by rfl⟩ : syracuseStep 2448557 = 918209) (by norm_num)
theorem B1629365 : Blo 1084620 1629365 := bbase (se 5 (by rfl) ⟨76376, by rfl⟩ : syracuseStep 1629365 = 152753) (by norm_num)
theorem B1629389 : Blo 1084620 1629389 := bbase (se 3 (by rfl) ⟨305510, by rfl⟩ : syracuseStep 1629389 = 611021) (by norm_num)
theorem B1629413 : Blo 1084620 1629413 := bbase (se 4 (by rfl) ⟨152757, by rfl⟩ : syracuseStep 1629413 = 305515) (by norm_num)
theorem B2448629 : Blo 1084620 2448629 := bbase (se 5 (by rfl) ⟨114779, by rfl⟩ : syracuseStep 2448629 = 229559) (by norm_num)
theorem B1629437 : Blo 1084620 1629437 := bbase (se 3 (by rfl) ⟨305519, by rfl⟩ : syracuseStep 1629437 = 611039) (by norm_num)
theorem B1629461 : Blo 1084620 1629461 := bbase (se 6 (by rfl) ⟨38190, by rfl⟩ : syracuseStep 1629461 = 76381) (by norm_num)
theorem B1629485 : Blo 1084620 1629485 := bbase (se 3 (by rfl) ⟨305528, by rfl⟩ : syracuseStep 1629485 = 611057) (by norm_num)
theorem B2448701 : Blo 1084620 2448701 := bbase (se 3 (by rfl) ⟨459131, by rfl⟩ : syracuseStep 2448701 = 918263) (by norm_num)
theorem B1629509 : Blo 1084620 1629509 := bbase (se 4 (by rfl) ⟨152766, by rfl⟩ : syracuseStep 1629509 = 305533) (by norm_num)
theorem B1629533 : Blo 1084620 1629533 := bbase (se 3 (by rfl) ⟨305537, by rfl⟩ : syracuseStep 1629533 = 611075) (by norm_num)
theorem B1629557 : Blo 1084620 1629557 := bbase (se 5 (by rfl) ⟨76385, by rfl⟩ : syracuseStep 1629557 = 152771) (by norm_num)
theorem B2448773 : Blo 1084620 2448773 := bbase (se 4 (by rfl) ⟨229572, by rfl⟩ : syracuseStep 2448773 = 459145) (by norm_num)
theorem B1629581 : Blo 1084620 1629581 := bbase (se 3 (by rfl) ⟨305546, by rfl⟩ : syracuseStep 1629581 = 611093) (by norm_num)
theorem B1629605 : Blo 1084620 1629605 := bbase (se 4 (by rfl) ⟨152775, by rfl⟩ : syracuseStep 1629605 = 305551) (by norm_num)
theorem B1629629 : Blo 1084620 1629629 := bbase (se 3 (by rfl) ⟨305555, by rfl⟩ : syracuseStep 1629629 = 611111) (by norm_num)
theorem B3661253 : Blo 1084620 3661253 := bbase (se 4 (by rfl) ⟨343242, by rfl⟩ : syracuseStep 3661253 = 686485) (by norm_num)
theorem B2645453 : Blo 1084620 2645453 := bbase (se 3 (by rfl) ⟨496022, by rfl⟩ : syracuseStep 2645453 = 992045) (by norm_num)
theorem B2448845 : Blo 1084620 2448845 := bbase (se 3 (by rfl) ⟨459158, by rfl⟩ : syracuseStep 2448845 = 918317) (by norm_num)
theorem B1629653 : Blo 1084620 1629653 := bbase (se 7 (by rfl) ⟨19097, by rfl⟩ : syracuseStep 1629653 = 38195) (by norm_num)
theorem B1629677 : Blo 1084620 1629677 := bbase (se 3 (by rfl) ⟨305564, by rfl⟩ : syracuseStep 1629677 = 611129) (by norm_num)
theorem B1629701 : Blo 1084620 1629701 := bbase (se 4 (by rfl) ⟨152784, by rfl⟩ : syracuseStep 1629701 = 305569) (by norm_num)
theorem B2448917 : Blo 1084620 2448917 := bbase (se 6 (by rfl) ⟨57396, by rfl⟩ : syracuseStep 2448917 = 114793) (by norm_num)
theorem B1629725 : Blo 1084620 1629725 := bbase (se 3 (by rfl) ⟨305573, by rfl⟩ : syracuseStep 1629725 = 611147) (by norm_num)
theorem B2612765 : Blo 1084620 2612765 := bbase (se 3 (by rfl) ⟨489893, by rfl⟩ : syracuseStep 2612765 = 979787) (by norm_num)
theorem B1629749 : Blo 1084620 1629749 := bbase (se 5 (by rfl) ⟨76394, by rfl⟩ : syracuseStep 1629749 = 152789) (by norm_num)
theorem B1629773 : Blo 1084620 1629773 := bbase (se 3 (by rfl) ⟨305582, by rfl⟩ : syracuseStep 1629773 = 611165) (by norm_num)
theorem B2448989 : Blo 1084620 2448989 := bbase (se 3 (by rfl) ⟨459185, by rfl⟩ : syracuseStep 2448989 = 918371) (by norm_num)
theorem B1629797 : Blo 1084620 1629797 := bbase (se 4 (by rfl) ⟨152793, by rfl⟩ : syracuseStep 1629797 = 305587) (by norm_num)
theorem B1629821 : Blo 1084620 1629821 := bbase (se 3 (by rfl) ⟨305591, by rfl⟩ : syracuseStep 1629821 = 611183) (by norm_num)
theorem B1629845 : Blo 1084620 1629845 := bbase (se 6 (by rfl) ⟨38199, by rfl⟩ : syracuseStep 1629845 = 76399) (by norm_num)
theorem B2449061 : Blo 1084620 2449061 := bbase (se 4 (by rfl) ⟨229599, by rfl⟩ : syracuseStep 2449061 = 459199) (by norm_num)
theorem B1629869 : Blo 1084620 1629869 := bbase (se 3 (by rfl) ⟨305600, by rfl⟩ : syracuseStep 1629869 = 611201) (by norm_num)
theorem B1629893 : Blo 1084620 1629893 := bbase (se 4 (by rfl) ⟨152802, by rfl⟩ : syracuseStep 1629893 = 305605) (by norm_num)
theorem B1629917 : Blo 1084620 1629917 := bbase (se 3 (by rfl) ⟨305609, by rfl⟩ : syracuseStep 1629917 = 611219) (by norm_num)
theorem B1957613 : Blo 1084620 1957613 := bbase (se 3 (by rfl) ⟨367052, by rfl⟩ : syracuseStep 1957613 = 734105) (by norm_num)
theorem B2449133 : Blo 1084620 2449133 := bbase (se 3 (by rfl) ⟨459212, by rfl⟩ : syracuseStep 2449133 = 918425) (by norm_num)
theorem B1629941 : Blo 1084620 1629941 := bbase (se 5 (by rfl) ⟨76403, by rfl⟩ : syracuseStep 1629941 = 152807) (by norm_num)
theorem B1629965 : Blo 1084620 1629965 := bbase (se 3 (by rfl) ⟨305618, by rfl⟩ : syracuseStep 1629965 = 611237) (by norm_num)
theorem B10444565 : Blo 1084620 10444565 := bbase (se 6 (by rfl) ⟨244794, by rfl⟩ : syracuseStep 10444565 = 489589) (by norm_num)
theorem B1629989 : Blo 1084620 1629989 := bbase (se 4 (by rfl) ⟨152811, by rfl⟩ : syracuseStep 1629989 = 305623) (by norm_num)
theorem B2449205 : Blo 1084620 2449205 := bbase (se 5 (by rfl) ⟨114806, by rfl⟩ : syracuseStep 2449205 = 229613) (by norm_num)
theorem B1630013 : Blo 1084620 1630013 := bbase (se 3 (by rfl) ⟨305627, by rfl⟩ : syracuseStep 1630013 = 611255) (by norm_num)
theorem B1630037 : Blo 1084620 1630037 := bbase (se 9 (by rfl) ⟨4775, by rfl⟩ : syracuseStep 1630037 = 9551) (by norm_num)
theorem B3137381 : Blo 1084620 3137381 := bbase (se 4 (by rfl) ⟨294129, by rfl⟩ : syracuseStep 3137381 = 588259) (by norm_num)
theorem B1630061 : Blo 1084620 1630061 := bbase (se 3 (by rfl) ⟨305636, by rfl⟩ : syracuseStep 1630061 = 611273) (by norm_num)
theorem B3661685 : Blo 1084620 3661685 := bbase (se 5 (by rfl) ⟨171641, by rfl⟩ : syracuseStep 3661685 = 343283) (by norm_num)
theorem B2449277 : Blo 1084620 2449277 := bbase (se 3 (by rfl) ⟨459239, by rfl⟩ : syracuseStep 2449277 = 918479) (by norm_num)
theorem B2318213 : Blo 1084620 2318213 := bbase (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) (by norm_num)
theorem B1630085 : Blo 1084620 1630085 := bbase (se 4 (by rfl) ⟨152820, by rfl⟩ : syracuseStep 1630085 = 305641) (by norm_num)
theorem B1630109 : Blo 1084620 1630109 := bbase (se 3 (by rfl) ⟨305645, by rfl⟩ : syracuseStep 1630109 = 611291) (by norm_num)
theorem B1630133 : Blo 1084620 1630133 := bbase (se 5 (by rfl) ⟨76412, by rfl⟩ : syracuseStep 1630133 = 152825) (by norm_num)
theorem B2449349 : Blo 1084620 2449349 := bbase (se 4 (by rfl) ⟨229626, by rfl⟩ : syracuseStep 2449349 = 459253) (by norm_num)
theorem B1630157 : Blo 1084620 1630157 := bbase (se 3 (by rfl) ⟨305654, by rfl⟩ : syracuseStep 1630157 = 611309) (by norm_num)
theorem B1630181 : Blo 1084620 1630181 := bbase (se 4 (by rfl) ⟨152829, by rfl⟩ : syracuseStep 1630181 = 305659) (by norm_num)
theorem B5496821 : Blo 1084620 5496821 := bbase (se 5 (by rfl) ⟨257663, by rfl⟩ : syracuseStep 5496821 = 515327) (by norm_num)
theorem B1859573 : Blo 1084620 1859573 := bbase (se 5 (by rfl) ⟨87167, by rfl⟩ : syracuseStep 1859573 = 174335) (by norm_num)
theorem B2940917 : Blo 1084620 2940917 := bbase (se 5 (by rfl) ⟨137855, by rfl⟩ : syracuseStep 2940917 = 275711) (by norm_num)
theorem B1630205 : Blo 1084620 1630205 := bbase (se 3 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 1630205 = 611327) (by norm_num)
theorem B2318357 : Blo 1084620 2318357 := bbase (se 6 (by rfl) ⟨54336, by rfl⟩ : syracuseStep 2318357 = 108673) (by norm_num)
theorem B1630229 : Blo 1084620 1630229 := bbase (se 6 (by rfl) ⟨38208, by rfl⟩ : syracuseStep 1630229 = 76417) (by norm_num)
theorem B1630253 : Blo 1084620 1630253 := bbase (se 3 (by rfl) ⟨305672, by rfl⟩ : syracuseStep 1630253 = 611345) (by norm_num)
theorem B1630277 : Blo 1084620 1630277 := bbase (se 4 (by rfl) ⟨152838, by rfl⟩ : syracuseStep 1630277 = 305677) (by norm_num)
theorem B1630301 : Blo 1084620 1630301 := bbase (se 3 (by rfl) ⟨305681, by rfl⟩ : syracuseStep 1630301 = 611363) (by norm_num)
theorem B1630325 : Blo 1084620 1630325 := bbase (se 5 (by rfl) ⟨76421, by rfl⟩ : syracuseStep 1630325 = 152843) (by norm_num)
theorem B1630349 : Blo 1084620 1630349 := bbase (se 3 (by rfl) ⟨305690, by rfl⟩ : syracuseStep 1630349 = 611381) (by norm_num)
theorem B1630373 : Blo 1084620 1630373 := bbase (se 4 (by rfl) ⟨152847, by rfl⟩ : syracuseStep 1630373 = 305695) (by norm_num)
theorem B1630397 : Blo 1084620 1630397 := bbase (se 3 (by rfl) ⟨305699, by rfl⟩ : syracuseStep 1630397 = 611399) (by norm_num)
theorem B1630421 : Blo 1084620 1630421 := bbase (se 7 (by rfl) ⟨19106, by rfl⟩ : syracuseStep 1630421 = 38213) (by norm_num)
theorem B1630445 : Blo 1084620 1630445 := bbase (se 3 (by rfl) ⟨305708, by rfl⟩ : syracuseStep 1630445 = 611417) (by norm_num)
theorem B2515181 : Blo 1084620 2515181 := bbase (se 3 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 2515181 = 943193) (by norm_num)
theorem B1630469 : Blo 1084620 1630469 := bbase (se 4 (by rfl) ⟨152856, by rfl⟩ : syracuseStep 1630469 = 305713) (by norm_num)
theorem B1630493 : Blo 1084620 1630493 := bbase (se 3 (by rfl) ⟨305717, by rfl⟩ : syracuseStep 1630493 = 611435) (by norm_num)
theorem B3662117 : Blo 1084620 3662117 := bbase (se 4 (by rfl) ⟨343323, by rfl⟩ : syracuseStep 3662117 = 686647) (by norm_num)
theorem B1630517 : Blo 1084620 1630517 := bbase (se 5 (by rfl) ⟨76430, by rfl⟩ : syracuseStep 1630517 = 152861) (by norm_num)
theorem B4120901 : Blo 1084620 4120901 := bbase (se 4 (by rfl) ⟨386334, by rfl⟩ : syracuseStep 4120901 = 772669) (by norm_num)
theorem B1630541 : Blo 1084620 1630541 := bbase (se 3 (by rfl) ⟨305726, by rfl⟩ : syracuseStep 1630541 = 611453) (by norm_num)
theorem B1630565 : Blo 1084620 1630565 := bbase (se 4 (by rfl) ⟨152865, by rfl⟩ : syracuseStep 1630565 = 305731) (by norm_num)
theorem B1630589 : Blo 1084620 1630589 := bbase (se 3 (by rfl) ⟨305735, by rfl⟩ : syracuseStep 1630589 = 611471) (by norm_num)
theorem B1630613 : Blo 1084620 1630613 := bbase (se 6 (by rfl) ⟨38217, by rfl⟩ : syracuseStep 1630613 = 76435) (by norm_num)
theorem B1630637 : Blo 1084620 1630637 := bbase (se 3 (by rfl) ⟨305744, by rfl⟩ : syracuseStep 1630637 = 611489) (by norm_num)
theorem B1630661 : Blo 1084620 1630661 := bbase (se 4 (by rfl) ⟨152874, by rfl⟩ : syracuseStep 1630661 = 305749) (by norm_num)
theorem B6185429 : Blo 1084620 6185429 := bbase (se 7 (by rfl) ⟨72485, by rfl⟩ : syracuseStep 6185429 = 144971) (by norm_num)
theorem B1630685 : Blo 1084620 1630685 := bbase (se 3 (by rfl) ⟨305753, by rfl⟩ : syracuseStep 1630685 = 611507) (by norm_num)
theorem B1630709 : Blo 1084620 1630709 := bbase (se 5 (by rfl) ⟨76439, by rfl⟩ : syracuseStep 1630709 = 152879) (by norm_num)
theorem B1630733 : Blo 1084620 1630733 := bbase (se 3 (by rfl) ⟨305762, by rfl⟩ : syracuseStep 1630733 = 611525) (by norm_num)
theorem B1630757 : Blo 1084620 1630757 := bbase (se 4 (by rfl) ⟨152883, by rfl⟩ : syracuseStep 1630757 = 305767) (by norm_num)
theorem B1630781 : Blo 1084620 1630781 := bbase (se 3 (by rfl) ⟨305771, by rfl⟩ : syracuseStep 1630781 = 611543) (by norm_num)
theorem B1630805 : Blo 1084620 1630805 := bbase (se 8 (by rfl) ⟨9555, by rfl⟩ : syracuseStep 1630805 = 19111) (by norm_num)
theorem B4121189 : Blo 1084620 4121189 := bbase (se 4 (by rfl) ⟨386361, by rfl⟩ : syracuseStep 4121189 = 772723) (by norm_num)
theorem B1630829 : Blo 1084620 1630829 := bbase (se 3 (by rfl) ⟨305780, by rfl⟩ : syracuseStep 1630829 = 611561) (by norm_num)
theorem B1630853 : Blo 1084620 1630853 := bbase (se 4 (by rfl) ⟨152892, by rfl⟩ : syracuseStep 1630853 = 305785) (by norm_num)
theorem B1630877 : Blo 1084620 1630877 := bbase (se 3 (by rfl) ⟨305789, by rfl⟩ : syracuseStep 1630877 = 611579) (by norm_num)
theorem B1630901 : Blo 1084620 1630901 := bbase (se 5 (by rfl) ⟨76448, by rfl⟩ : syracuseStep 1630901 = 152897) (by norm_num)
theorem B1630925 : Blo 1084620 1630925 := bbase (se 3 (by rfl) ⟨305798, by rfl⟩ : syracuseStep 1630925 = 611597) (by norm_num)
theorem B3662549 : Blo 1084620 3662549 := bbase (se 7 (by rfl) ⟨42920, by rfl⟩ : syracuseStep 3662549 = 85841) (by norm_num)
theorem B1630949 : Blo 1084620 1630949 := bbase (se 4 (by rfl) ⟨152901, by rfl⟩ : syracuseStep 1630949 = 305803) (by norm_num)
theorem B2319101 : Blo 1084620 2319101 := bbase (se 3 (by rfl) ⟨434831, by rfl⟩ : syracuseStep 2319101 = 869663) (by norm_num)
theorem B1630973 : Blo 1084620 1630973 := bbase (se 3 (by rfl) ⟨305807, by rfl⟩ : syracuseStep 1630973 = 611615) (by norm_num)
theorem B1630997 : Blo 1084620 1630997 := bbase (se 6 (by rfl) ⟨38226, by rfl⟩ : syracuseStep 1630997 = 76453) (by norm_num)
theorem B1631021 : Blo 1084620 1631021 := bbase (se 3 (by rfl) ⟨305816, by rfl⟩ : syracuseStep 1631021 = 611633) (by norm_num)
theorem B1631045 : Blo 1084620 1631045 := bbase (se 4 (by rfl) ⟨152910, by rfl⟩ : syracuseStep 1631045 = 305821) (by norm_num)
theorem B1631069 : Blo 1084620 1631069 := bbase (se 3 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 1631069 = 611651) (by norm_num)
theorem B1631093 : Blo 1084620 1631093 := bbase (se 5 (by rfl) ⟨76457, by rfl⟩ : syracuseStep 1631093 = 152915) (by norm_num)
theorem B1631117 : Blo 1084620 1631117 := bbase (se 3 (by rfl) ⟨305834, by rfl⟩ : syracuseStep 1631117 = 611669) (by norm_num)
theorem B1237909 : Blo 1084620 1237909 := bbase (se 6 (by rfl) ⟨29013, by rfl⟩ : syracuseStep 1237909 = 58027) (by norm_num)
theorem B1631141 : Blo 1084620 1631141 := bbase (se 4 (by rfl) ⟨152919, by rfl⟩ : syracuseStep 1631141 = 305839) (by norm_num)
theorem B1631165 : Blo 1084620 1631165 := bbase (se 3 (by rfl) ⟨305843, by rfl⟩ : syracuseStep 1631165 = 611687) (by norm_num)
theorem B1631189 : Blo 1084620 1631189 := bbase (se 7 (by rfl) ⟨19115, by rfl⟩ : syracuseStep 1631189 = 38231) (by norm_num)
theorem B1631213 : Blo 1084620 1631213 := bbase (se 3 (by rfl) ⟨305852, by rfl⟩ : syracuseStep 1631213 = 611705) (by norm_num)
theorem B1631237 : Blo 1084620 1631237 := bbase (se 4 (by rfl) ⟨152928, by rfl⟩ : syracuseStep 1631237 = 305857) (by norm_num)
theorem B1631261 : Blo 1084620 1631261 := bbase (se 3 (by rfl) ⟨305861, by rfl⟩ : syracuseStep 1631261 = 611723) (by norm_num)
theorem B1631285 : Blo 1084620 1631285 := bbase (se 5 (by rfl) ⟨76466, by rfl⟩ : syracuseStep 1631285 = 152933) (by norm_num)
theorem B1631309 : Blo 1084620 1631309 := bbase (se 3 (by rfl) ⟨305870, by rfl⟩ : syracuseStep 1631309 = 611741) (by norm_num)
theorem B1631333 : Blo 1084620 1631333 := bbase (se 4 (by rfl) ⟨152937, by rfl⟩ : syracuseStep 1631333 = 305875) (by norm_num)
theorem B1631357 : Blo 1084620 1631357 := bbase (se 3 (by rfl) ⟨305879, by rfl⟩ : syracuseStep 1631357 = 611759) (by norm_num)
theorem B3662981 : Blo 1084620 3662981 := bbase (se 4 (by rfl) ⟨343404, by rfl⟩ : syracuseStep 3662981 = 686809) (by norm_num)
theorem B2745485 : Blo 1084620 2745485 := bbase (se 3 (by rfl) ⟨514778, by rfl⟩ : syracuseStep 2745485 = 1029557) (by norm_num)
theorem B1631381 : Blo 1084620 1631381 := bbase (se 6 (by rfl) ⟨38235, by rfl⟩ : syracuseStep 1631381 = 76471) (by norm_num)
theorem B1631405 : Blo 1084620 1631405 := bbase (se 3 (by rfl) ⟨305888, by rfl⟩ : syracuseStep 1631405 = 611777) (by norm_num)
theorem B1631429 : Blo 1084620 1631429 := bbase (se 4 (by rfl) ⟨152946, by rfl⟩ : syracuseStep 1631429 = 305893) (by norm_num)
theorem B1631453 : Blo 1084620 1631453 := bbase (se 3 (by rfl) ⟨305897, by rfl⟩ : syracuseStep 1631453 = 611795) (by norm_num)
theorem B1631477 : Blo 1084620 1631477 := bbase (se 5 (by rfl) ⟨76475, by rfl⟩ : syracuseStep 1631477 = 152951) (by norm_num)
theorem B5498117 : Blo 1084620 5498117 := bbase (se 4 (by rfl) ⟨515448, by rfl⟩ : syracuseStep 5498117 = 1030897) (by norm_num)
theorem B1631501 : Blo 1084620 1631501 := bbase (se 3 (by rfl) ⟨305906, by rfl⟩ : syracuseStep 1631501 = 611813) (by norm_num)
theorem B1631525 : Blo 1084620 1631525 := bbase (se 4 (by rfl) ⟨152955, by rfl⟩ : syracuseStep 1631525 = 305911) (by norm_num)
theorem B1631549 : Blo 1084620 1631549 := bbase (se 3 (by rfl) ⟨305915, by rfl⟩ : syracuseStep 1631549 = 611831) (by norm_num)
theorem B2745677 : Blo 1084620 2745677 := bbase (se 3 (by rfl) ⟨514814, by rfl⟩ : syracuseStep 2745677 = 1029629) (by norm_num)
theorem B1631573 : Blo 1084620 1631573 := bbase (se 12 (by rfl) ⟨597, by rfl⟩ : syracuseStep 1631573 = 1195) (by norm_num)
theorem B1762661 : Blo 1084620 1762661 := bbase (se 4 (by rfl) ⟨165249, by rfl⟩ : syracuseStep 1762661 = 330499) (by norm_num)
theorem B1631597 : Blo 1084620 1631597 := bbase (se 3 (by rfl) ⟨305924, by rfl⟩ : syracuseStep 1631597 = 611849) (by norm_num)
theorem B1631621 : Blo 1084620 1631621 := bbase (se 4 (by rfl) ⟨152964, by rfl⟩ : syracuseStep 1631621 = 305929) (by norm_num)
theorem B1631645 : Blo 1084620 1631645 := bbase (se 3 (by rfl) ⟨305933, by rfl⟩ : syracuseStep 1631645 = 611867) (by norm_num)
theorem B1631669 : Blo 1084620 1631669 := bbase (se 5 (by rfl) ⟨76484, by rfl⟩ : syracuseStep 1631669 = 152969) (by norm_num)
theorem B1631693 : Blo 1084620 1631693 := bbase (se 3 (by rfl) ⟨305942, by rfl⟩ : syracuseStep 1631693 = 611885) (by norm_num)
theorem B2516437 : Blo 1084620 2516437 := bbase (se 7 (by rfl) ⟨29489, by rfl⟩ : syracuseStep 2516437 = 58979) (by norm_num)
theorem B1304033 : Blo 1084620 1304033 := bbase (se 2 (by rfl) ⟨489012, by rfl⟩ : syracuseStep 1304033 = 978025) (by norm_num)
theorem B1631717 : Blo 1084620 1631717 := bbase (se 4 (by rfl) ⟨152973, by rfl⟩ : syracuseStep 1631717 = 305947) (by norm_num)
theorem B2319853 : Blo 1084620 2319853 := bbase (se 3 (by rfl) ⟨434972, by rfl⟩ : syracuseStep 2319853 = 869945) (by norm_num)
theorem B1304057 : Blo 1084620 1304057 := bbase (se 2 (by rfl) ⟨489021, by rfl⟩ : syracuseStep 1304057 = 978043) (by norm_num)
theorem B1631741 : Blo 1084620 1631741 := bbase (se 3 (by rfl) ⟨305951, by rfl⟩ : syracuseStep 1631741 = 611903) (by norm_num)
theorem B1631765 : Blo 1084620 1631765 := bbase (se 6 (by rfl) ⟨38244, by rfl⟩ : syracuseStep 1631765 = 76489) (by norm_num)
theorem B1631789 : Blo 1084620 1631789 := bbase (se 3 (by rfl) ⟨305960, by rfl⟩ : syracuseStep 1631789 = 611921) (by norm_num)
theorem B3663413 : Blo 1084620 3663413 := bbase (se 5 (by rfl) ⟨171722, by rfl⟩ : syracuseStep 3663413 = 343445) (by norm_num)
theorem B1467973 : Blo 1084620 1467973 := bbase (se 4 (by rfl) ⟨137622, by rfl⟩ : syracuseStep 1467973 = 275245) (by norm_num)
theorem B1631813 : Blo 1084620 1631813 := bbase (se 4 (by rfl) ⟨152982, by rfl⟩ : syracuseStep 1631813 = 305965) (by norm_num)
theorem B1631837 : Blo 1084620 1631837 := bbase (se 3 (by rfl) ⟨305969, by rfl⟩ : syracuseStep 1631837 = 611939) (by norm_num)
theorem B1631861 : Blo 1084620 1631861 := bbase (se 5 (by rfl) ⟨76493, by rfl⟩ : syracuseStep 1631861 = 152987) (by norm_num)
theorem B2319997 : Blo 1084620 2319997 := bbase (se 3 (by rfl) ⟨434999, by rfl⟩ : syracuseStep 2319997 = 869999) (by norm_num)
theorem B1631885 : Blo 1084620 1631885 := bbase (se 3 (by rfl) ⟨305978, by rfl⟩ : syracuseStep 1631885 = 611957) (by norm_num)
theorem B1238689 : Blo 1084620 1238689 := bbase (se 2 (by rfl) ⟨464508, by rfl⟩ : syracuseStep 1238689 = 929017) (by norm_num)
theorem B2746021 : Blo 1084620 2746021 := bbase (se 4 (by rfl) ⟨257439, by rfl⟩ : syracuseStep 2746021 = 514879) (by norm_num)
theorem B1631909 : Blo 1084620 1631909 := bbase (se 4 (by rfl) ⟨152991, by rfl⟩ : syracuseStep 1631909 = 305983) (by norm_num)
theorem B1631933 : Blo 1084620 1631933 := bbase (se 3 (by rfl) ⟨305987, by rfl⟩ : syracuseStep 1631933 = 611975) (by norm_num)
theorem B1631957 : Blo 1084620 1631957 := bbase (se 7 (by rfl) ⟨19124, by rfl⟩ : syracuseStep 1631957 = 38249) (by norm_num)
theorem B1631981 : Blo 1084620 1631981 := bbase (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) (by norm_num)
theorem B4122373 : Blo 1084620 4122373 := bbase (se 4 (by rfl) ⟨386472, by rfl⟩ : syracuseStep 4122373 = 772945) (by norm_num)
theorem B1632005 : Blo 1084620 1632005 := bbase (se 4 (by rfl) ⟨153000, by rfl⟩ : syracuseStep 1632005 = 306001) (by norm_num)
theorem B2746133 : Blo 1084620 2746133 := bbase (se 6 (by rfl) ⟨64362, by rfl⟩ : syracuseStep 2746133 = 128725) (by norm_num)
theorem B1632029 : Blo 1084620 1632029 := bbase (se 3 (by rfl) ⟨306005, by rfl⟩ : syracuseStep 1632029 = 612011) (by norm_num)
theorem B1304365 : Blo 1084620 1304365 := bbase (se 3 (by rfl) ⟨244568, by rfl⟩ : syracuseStep 1304365 = 489137) (by norm_num)
theorem B1632053 : Blo 1084620 1632053 := bbase (se 5 (by rfl) ⟨76502, by rfl⟩ : syracuseStep 1632053 = 153005) (by norm_num)
theorem B1632077 : Blo 1084620 1632077 := bbase (se 3 (by rfl) ⟨306014, by rfl⟩ : syracuseStep 1632077 = 612029) (by norm_num)
theorem B1632101 : Blo 1084620 1632101 := bbase (se 4 (by rfl) ⟨153009, by rfl⟩ : syracuseStep 1632101 = 306019) (by norm_num)
theorem B1959805 : Blo 1084620 1959805 := bbase (se 3 (by rfl) ⟨367463, by rfl⟩ : syracuseStep 1959805 = 734927) (by norm_num)
theorem B1632125 : Blo 1084620 1632125 := bbase (se 3 (by rfl) ⟨306023, by rfl⟩ : syracuseStep 1632125 = 612047) (by norm_num)
theorem B1632149 : Blo 1084620 1632149 := bbase (se 6 (by rfl) ⟨38253, by rfl⟩ : syracuseStep 1632149 = 76507) (by norm_num)
theorem B1632173 : Blo 1084620 1632173 := bbase (se 3 (by rfl) ⟨306032, by rfl⟩ : syracuseStep 1632173 = 612065) (by norm_num)
theorem B1959877 : Blo 1084620 1959877 := bbase (se 4 (by rfl) ⟨183738, by rfl⟩ : syracuseStep 1959877 = 367477) (by norm_num)
theorem B1632197 : Blo 1084620 1632197 := bbase (se 4 (by rfl) ⟨153018, by rfl⟩ : syracuseStep 1632197 = 306037) (by norm_num)
theorem B2746325 : Blo 1084620 2746325 := bbase (se 7 (by rfl) ⟨32183, by rfl⟩ : syracuseStep 2746325 = 64367) (by norm_num)
theorem B1304537 : Blo 1084620 1304537 := bbase (se 2 (by rfl) ⟨489201, by rfl⟩ : syracuseStep 1304537 = 978403) (by norm_num)
theorem B1632221 : Blo 1084620 1632221 := bbase (se 3 (by rfl) ⟨306041, by rfl⟩ : syracuseStep 1632221 = 612083) (by norm_num)
theorem B3663845 : Blo 1084620 3663845 := bbase (se 4 (by rfl) ⟨343485, by rfl⟩ : syracuseStep 3663845 = 686971) (by norm_num)
theorem B2320373 : Blo 1084620 2320373 := bbase (se 5 (by rfl) ⟨108767, by rfl⟩ : syracuseStep 2320373 = 217535) (by norm_num)
theorem B1632245 : Blo 1084620 1632245 := bbase (se 5 (by rfl) ⟨76511, by rfl⟩ : syracuseStep 1632245 = 153023) (by norm_num)
theorem B1632269 : Blo 1084620 1632269 := bbase (se 3 (by rfl) ⟨306050, by rfl⟩ : syracuseStep 1632269 = 612101) (by norm_num)
theorem B1632293 : Blo 1084620 1632293 := bbase (se 4 (by rfl) ⟨153027, by rfl⟩ : syracuseStep 1632293 = 306055) (by norm_num)
theorem B2615341 : Blo 1084620 2615341 := bbase (se 3 (by rfl) ⟨490376, by rfl⟩ : syracuseStep 2615341 = 980753) (by norm_num)
theorem B4122677 : Blo 1084620 4122677 := bbase (se 5 (by rfl) ⟨193250, by rfl⟩ : syracuseStep 4122677 = 386501) (by norm_num)
theorem B4646965 : Blo 1084620 4646965 := bbase (se 5 (by rfl) ⟨217826, by rfl⟩ : syracuseStep 4646965 = 435653) (by norm_num)
theorem B1632317 : Blo 1084620 1632317 := bbase (se 3 (by rfl) ⟨306059, by rfl⟩ : syracuseStep 1632317 = 612119) (by norm_num)
theorem B1304653 : Blo 1084620 1304653 := bbase (se 3 (by rfl) ⟨244622, by rfl⟩ : syracuseStep 1304653 = 489245) (by norm_num)
theorem B1632341 : Blo 1084620 1632341 := bbase (se 8 (by rfl) ⟨9564, by rfl⟩ : syracuseStep 1632341 = 19129) (by norm_num)
theorem B1632365 : Blo 1084620 1632365 := bbase (se 3 (by rfl) ⟨306068, by rfl⟩ : syracuseStep 1632365 = 612137) (by norm_num)
theorem B1632389 : Blo 1084620 1632389 := bbase (se 4 (by rfl) ⟨153036, by rfl⟩ : syracuseStep 1632389 = 306073) (by norm_num)
theorem B1632413 : Blo 1084620 1632413 := bbase (se 3 (by rfl) ⟨306077, by rfl⟩ : syracuseStep 1632413 = 612155) (by norm_num)
theorem B1304749 : Blo 1084620 1304749 := bbase (se 3 (by rfl) ⟨244640, by rfl⟩ : syracuseStep 1304749 = 489281) (by norm_num)
theorem B1632437 : Blo 1084620 1632437 := bbase (se 5 (by rfl) ⟨76520, by rfl⟩ : syracuseStep 1632437 = 153041) (by norm_num)
theorem B1239241 : Blo 1084620 1239241 := bbase (se 2 (by rfl) ⟨464715, by rfl⟩ : syracuseStep 1239241 = 929431) (by norm_num)
theorem B1632461 : Blo 1084620 1632461 := bbase (se 3 (by rfl) ⟨306086, by rfl⟩ : syracuseStep 1632461 = 612173) (by norm_num)
theorem B1632485 : Blo 1084620 1632485 := bbase (se 4 (by rfl) ⟨153045, by rfl⟩ : syracuseStep 1632485 = 306091) (by norm_num)
theorem B1632509 : Blo 1084620 1632509 := bbase (se 3 (by rfl) ⟨306095, by rfl⟩ : syracuseStep 1632509 = 612191) (by norm_num)
theorem B1632533 : Blo 1084620 1632533 := bbase (se 6 (by rfl) ⟨38262, by rfl⟩ : syracuseStep 1632533 = 76525) (by norm_num)
theorem B2746669 : Blo 1084620 2746669 := bbase (se 3 (by rfl) ⟨515000, by rfl⟩ : syracuseStep 2746669 = 1030001) (by norm_num)
theorem B1632557 : Blo 1084620 1632557 := bbase (se 3 (by rfl) ⟨306104, by rfl⟩ : syracuseStep 1632557 = 612209) (by norm_num)
theorem B1304893 : Blo 1084620 1304893 := bbase (se 3 (by rfl) ⟨244667, by rfl⟩ : syracuseStep 1304893 = 489335) (by norm_num)
theorem B1632581 : Blo 1084620 1632581 := bbase (se 4 (by rfl) ⟨153054, by rfl⟩ : syracuseStep 1632581 = 306109) (by norm_num)
theorem B1632605 : Blo 1084620 1632605 := bbase (se 3 (by rfl) ⟨306113, by rfl⟩ : syracuseStep 1632605 = 612227) (by norm_num)
theorem B2320741 : Blo 1084620 2320741 := bbase (se 4 (by rfl) ⟨217569, by rfl⟩ : syracuseStep 2320741 = 435139) (by norm_num)
theorem B1632629 : Blo 1084620 1632629 := bbase (se 5 (by rfl) ⟨76529, by rfl⟩ : syracuseStep 1632629 = 153059) (by norm_num)
theorem B1632653 : Blo 1084620 1632653 := bbase (se 3 (by rfl) ⟨306122, by rfl⟩ : syracuseStep 1632653 = 612245) (by norm_num)
theorem B3664277 : Blo 1084620 3664277 := bbase (se 6 (by rfl) ⟨85881, by rfl⟩ : syracuseStep 3664277 = 171763) (by norm_num)
theorem B2746781 : Blo 1084620 2746781 := bbase (se 3 (by rfl) ⟨515021, by rfl⟩ : syracuseStep 2746781 = 1030043) (by norm_num)
theorem B1632677 : Blo 1084620 1632677 := bbase (se 4 (by rfl) ⟨153063, by rfl⟩ : syracuseStep 1632677 = 306127) (by norm_num)
theorem B1632701 : Blo 1084620 1632701 := bbase (se 3 (by rfl) ⟨306131, by rfl⟩ : syracuseStep 1632701 = 612263) (by norm_num)
theorem B1632725 : Blo 1084620 1632725 := bbase (se 7 (by rfl) ⟨19133, by rfl⟩ : syracuseStep 1632725 = 38267) (by norm_num)
theorem B1632749 : Blo 1084620 1632749 := bbase (se 3 (by rfl) ⟨306140, by rfl⟩ : syracuseStep 1632749 = 612281) (by norm_num)
theorem B1632773 : Blo 1084620 1632773 := bbase (se 4 (by rfl) ⟨153072, by rfl⟩ : syracuseStep 1632773 = 306145) (by norm_num)
theorem B5499413 : Blo 1084620 5499413 := bbase (se 6 (by rfl) ⟨128892, by rfl⟩ : syracuseStep 5499413 = 257785) (by norm_num)
theorem B1272349 : Blo 1084620 1272349 := bbase (se 3 (by rfl) ⟨238565, by rfl⟩ : syracuseStep 1272349 = 477131) (by norm_num)
theorem B1632797 : Blo 1084620 1632797 := bbase (se 3 (by rfl) ⟨306149, by rfl⟩ : syracuseStep 1632797 = 612299) (by norm_num)
theorem B1632821 : Blo 1084620 1632821 := bbase (se 5 (by rfl) ⟨76538, by rfl⟩ : syracuseStep 1632821 = 153077) (by norm_num)
theorem B1632845 : Blo 1084620 1632845 := bbase (se 3 (by rfl) ⟨306158, by rfl⟩ : syracuseStep 1632845 = 612317) (by norm_num)
theorem B2746973 : Blo 1084620 2746973 := bbase (se 3 (by rfl) ⟨515057, by rfl⟩ : syracuseStep 2746973 = 1030115) (by norm_num)
theorem B1632869 : Blo 1084620 1632869 := bbase (se 4 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 1632869 = 306163) (by norm_num)
theorem B1632893 : Blo 1084620 1632893 := bbase (se 3 (by rfl) ⟨306167, by rfl⟩ : syracuseStep 1632893 = 612335) (by norm_num)
theorem B1632917 : Blo 1084620 1632917 := bbase (se 6 (by rfl) ⟨38271, by rfl⟩ : syracuseStep 1632917 = 76543) (by norm_num)
theorem B3664709 : Blo 1084620 3664709 := bbase (se 4 (by rfl) ⟨343566, by rfl⟩ : syracuseStep 3664709 = 687133) (by norm_num)
theorem B21752725 : Blo 1084620 21752725 := bbase (se 6 (by rfl) ⟨509829, by rfl⟩ : syracuseStep 21752725 = 1019659) (by norm_num)
theorem B2747317 : Blo 1084620 2747317 := bbase (se 5 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 2747317 = 257561) (by norm_num)
theorem B4025285 : Blo 1084620 4025285 := bbase (se 4 (by rfl) ⟨377370, by rfl⟩ : syracuseStep 4025285 = 754741) (by norm_num)
theorem B3533765 : Blo 1084620 3533765 := bbase (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) (by norm_num)
theorem B1469389 : Blo 1084620 1469389 := bbase (se 3 (by rfl) ⟨275510, by rfl⟩ : syracuseStep 1469389 = 551021) (by norm_num)
theorem B2747429 : Blo 1084620 2747429 := bbase (se 4 (by rfl) ⟨257571, by rfl⟩ : syracuseStep 2747429 = 515143) (by norm_num)
theorem B6974549 : Blo 1084620 6974549 := bbase (se 8 (by rfl) ⟨40866, by rfl⟩ : syracuseStep 6974549 = 81733) (by norm_num)
theorem B2059357 : Blo 1084620 2059357 := bbase (se 3 (by rfl) ⟨386129, by rfl⟩ : syracuseStep 2059357 = 772259) (by norm_num)
theorem B2747621 : Blo 1084620 2747621 := bbase (se 4 (by rfl) ⟨257589, by rfl⟩ : syracuseStep 2747621 = 515179) (by norm_num)
theorem B1961189 : Blo 1084620 1961189 := bbase (se 4 (by rfl) ⟨183861, by rfl⟩ : syracuseStep 1961189 = 367723) (by norm_num)
theorem B2059501 : Blo 1084620 2059501 := bbase (se 3 (by rfl) ⟨386156, by rfl⟩ : syracuseStep 2059501 = 772313) (by norm_num)
theorem B3665141 : Blo 1084620 3665141 := bbase (se 5 (by rfl) ⟨171803, by rfl⟩ : syracuseStep 3665141 = 343607) (by norm_num)
theorem B1961261 : Blo 1084620 1961261 := bbase (se 3 (by rfl) ⟨367736, by rfl⟩ : syracuseStep 1961261 = 735473) (by norm_num)
theorem B2092405 : Blo 1084620 2092405 := bbase (se 5 (by rfl) ⟨98081, by rfl⟩ : syracuseStep 2092405 = 196163) (by norm_num)
theorem B2059661 : Blo 1084620 2059661 := bbase (se 3 (by rfl) ⟨386186, by rfl⟩ : syracuseStep 2059661 = 772373) (by norm_num)
theorem B1830397 : Blo 1084620 1830397 := bbase (se 3 (by rfl) ⟨343199, by rfl⟩ : syracuseStep 1830397 = 686399) (by norm_num)
theorem B2059805 : Blo 1084620 2059805 := bbase (se 3 (by rfl) ⟨386213, by rfl⟩ : syracuseStep 2059805 = 772427) (by norm_num)
theorem B2747965 : Blo 1084620 2747965 := bbase (se 3 (by rfl) ⟨515243, by rfl⟩ : syracuseStep 2747965 = 1030487) (by norm_num)
theorem B1830485 : Blo 1084620 1830485 := bbase (se 8 (by rfl) ⟨10725, by rfl⟩ : syracuseStep 1830485 = 21451) (by norm_num)
theorem B2092637 : Blo 1084620 2092637 := bbase (se 3 (by rfl) ⟨392369, by rfl⟩ : syracuseStep 2092637 = 784739) (by norm_num)
theorem B3665573 : Blo 1084620 3665573 := bbase (se 4 (by rfl) ⟨343647, by rfl⟩ : syracuseStep 3665573 = 687295) (by norm_num)
theorem B2748077 : Blo 1084620 2748077 := bbase (se 3 (by rfl) ⟨515264, by rfl⟩ : syracuseStep 2748077 = 1030529) (by norm_num)
theorem B1175233 : Blo 1084620 1175233 := bbase (se 2 (by rfl) ⟨440712, by rfl⟩ : syracuseStep 1175233 = 881425) (by norm_num)
theorem B1830613 : Blo 1084620 1830613 := bbase (se 7 (by rfl) ⟨21452, by rfl⟩ : syracuseStep 1830613 = 42905) (by norm_num)
theorem B5500709 : Blo 1084620 5500709 := bbase (se 4 (by rfl) ⟨515691, by rfl⟩ : syracuseStep 5500709 = 1031383) (by norm_num)
theorem B1830701 : Blo 1084620 1830701 := bbase (se 3 (by rfl) ⟨343256, by rfl⟩ : syracuseStep 1830701 = 686513) (by norm_num)
theorem B2060093 : Blo 1084620 2060093 := bbase (se 3 (by rfl) ⟨386267, by rfl⟩ : syracuseStep 2060093 = 772535) (by norm_num)
theorem B2322245 : Blo 1084620 2322245 := bbase (se 4 (by rfl) ⟨217710, by rfl⟩ : syracuseStep 2322245 = 435421) (by norm_num)
theorem B2748269 : Blo 1084620 2748269 := bbase (se 3 (by rfl) ⟨515300, by rfl⟩ : syracuseStep 2748269 = 1030601) (by norm_num)
theorem B1470325 : Blo 1084620 1470325 := bbase (se 5 (by rfl) ⟨68921, by rfl⟩ : syracuseStep 1470325 = 137843) (by norm_num)
theorem B1830829 : Blo 1084620 1830829 := bbase (se 3 (by rfl) ⟨343280, by rfl⟩ : syracuseStep 1830829 = 686561) (by norm_num)
theorem B1241029 : Blo 1084620 1241029 := bbase (se 4 (by rfl) ⟨116346, by rfl⟩ : syracuseStep 1241029 = 232693) (by norm_num)
theorem B2060245 : Blo 1084620 2060245 := bbase (se 7 (by rfl) ⟨24143, by rfl⟩ : syracuseStep 2060245 = 48287) (by norm_num)
theorem B2322389 : Blo 1084620 2322389 := bbase (se 7 (by rfl) ⟨27215, by rfl⟩ : syracuseStep 2322389 = 54431) (by norm_num)
theorem B1306613 : Blo 1084620 1306613 := bbase (se 5 (by rfl) ⟨61247, by rfl⟩ : syracuseStep 1306613 = 122495) (by norm_num)
theorem B1830917 : Blo 1084620 1830917 := bbase (se 4 (by rfl) ⟨171648, by rfl⟩ : syracuseStep 1830917 = 343297) (by norm_num)
theorem B3666005 : Blo 1084620 3666005 := bbase (se 8 (by rfl) ⟨21480, by rfl⟩ : syracuseStep 3666005 = 42961) (by norm_num)
theorem B1306729 : Blo 1084620 1306729 := bbase (se 2 (by rfl) ⟨490023, by rfl⟩ : syracuseStep 1306729 = 980047) (by norm_num)
theorem B4124789 : Blo 1084620 4124789 := bbase (se 5 (by rfl) ⟨193349, by rfl⟩ : syracuseStep 4124789 = 386699) (by norm_num)
theorem B2650229 : Blo 1084620 2650229 := bbase (se 5 (by rfl) ⟨124229, by rfl⟩ : syracuseStep 2650229 = 248459) (by norm_num)
theorem B1831045 : Blo 1084620 1831045 := bbase (se 4 (by rfl) ⟨171660, by rfl⟩ : syracuseStep 1831045 = 343321) (by norm_num)
theorem B1306801 : Blo 1084620 1306801 := bbase (se 2 (by rfl) ⟨490050, by rfl⟩ : syracuseStep 1306801 = 980101) (by norm_num)
theorem B2748613 : Blo 1084620 2748613 := bbase (se 4 (by rfl) ⟨257682, by rfl⟩ : syracuseStep 2748613 = 515365) (by norm_num)
theorem B1831133 : Blo 1084620 1831133 := bbase (se 3 (by rfl) ⟨343337, by rfl⟩ : syracuseStep 1831133 = 686675) (by norm_num)
theorem B2060549 : Blo 1084620 2060549 := bbase (se 4 (by rfl) ⟨193176, by rfl⟩ : syracuseStep 2060549 = 386353) (by norm_num)
theorem B1306921 : Blo 1084620 1306921 := bbase (se 2 (by rfl) ⟨490095, by rfl⟩ : syracuseStep 1306921 = 980191) (by norm_num)
theorem B2748725 : Blo 1084620 2748725 := bbase (se 5 (by rfl) ⟨128846, by rfl⟩ : syracuseStep 2748725 = 257693) (by norm_num)
theorem B2322749 : Blo 1084620 2322749 := bbase (se 3 (by rfl) ⟨435515, by rfl⟩ : syracuseStep 2322749 = 871031) (by norm_num)
theorem B1765709 : Blo 1084620 1765709 := bbase (se 3 (by rfl) ⟨331070, by rfl⟩ : syracuseStep 1765709 = 662141) (by norm_num)
theorem B1831261 : Blo 1084620 1831261 := bbase (se 3 (by rfl) ⟨343361, by rfl⟩ : syracuseStep 1831261 = 686723) (by norm_num)
theorem B4125077 : Blo 1084620 4125077 := bbase (se 6 (by rfl) ⟨96681, by rfl⟩ : syracuseStep 4125077 = 193363) (by norm_num)
theorem B9925013 : Blo 1084620 9925013 := bbase (se 6 (by rfl) ⟨232617, by rfl⟩ : syracuseStep 9925013 = 465235) (by norm_num)
theorem B1831349 : Blo 1084620 1831349 := bbase (se 5 (by rfl) ⟨85844, by rfl⟩ : syracuseStep 1831349 = 171689) (by norm_num)
theorem B2748917 : Blo 1084620 2748917 := bbase (se 5 (by rfl) ⟨128855, by rfl⟩ : syracuseStep 2748917 = 257711) (by norm_num)
theorem B3666437 : Blo 1084620 3666437 := bbase (se 4 (by rfl) ⟨343728, by rfl⟩ : syracuseStep 3666437 = 687457) (by norm_num)
theorem B3306005 : Blo 1084620 3306005 := bbase (se 6 (by rfl) ⟨77484, by rfl⟩ : syracuseStep 3306005 = 154969) (by norm_num)
theorem B1831477 : Blo 1084620 1831477 := bbase (se 5 (by rfl) ⟨85850, by rfl⟩ : syracuseStep 1831477 = 171701) (by norm_num)
theorem B1569397 : Blo 1084620 1569397 := bbase (se 5 (by rfl) ⟨73565, by rfl⟩ : syracuseStep 1569397 = 147131) (by norm_num)
theorem B1831565 : Blo 1084620 1831565 := bbase (se 3 (by rfl) ⟨343418, by rfl⟩ : syracuseStep 1831565 = 686837) (by norm_num)
theorem B1307305 : Blo 1084620 1307305 := bbase (se 2 (by rfl) ⟨490239, by rfl⟩ : syracuseStep 1307305 = 980479) (by norm_num)
theorem B1274573 : Blo 1084620 1274573 := bbase (se 3 (by rfl) ⟨238982, by rfl⟩ : syracuseStep 1274573 = 477965) (by norm_num)
theorem B1372889 : Blo 1084620 1372889 := bbase (se 2 (by rfl) ⟨514833, by rfl⟩ : syracuseStep 1372889 = 1029667) (by norm_num)
theorem B1176293 : Blo 1084620 1176293 := bbase (se 4 (by rfl) ⟨110277, by rfl⟩ : syracuseStep 1176293 = 220555) (by norm_num)
theorem B1831693 : Blo 1084620 1831693 := bbase (se 3 (by rfl) ⟨343442, by rfl⟩ : syracuseStep 1831693 = 686885) (by norm_num)
theorem B1372945 : Blo 1084620 1372945 := bbase (se 2 (by rfl) ⟨514854, by rfl⟩ : syracuseStep 1372945 = 1029709) (by norm_num)
theorem B2749261 : Blo 1084620 2749261 := bbase (se 3 (by rfl) ⟨515486, by rfl⟩ : syracuseStep 2749261 = 1030973) (by norm_num)
theorem B1831781 : Blo 1084620 1831781 := bbase (se 4 (by rfl) ⟨171729, by rfl⟩ : syracuseStep 1831781 = 343459) (by norm_num)
theorem B2683757 : Blo 1084620 2683757 := bbase (se 3 (by rfl) ⟨503204, by rfl⟩ : syracuseStep 2683757 = 1006409) (by norm_num)
theorem B1373041 : Blo 1084620 1373041 := bbase (se 2 (by rfl) ⟨514890, by rfl⟩ : syracuseStep 1373041 = 1029781) (by norm_num)
theorem B3666869 : Blo 1084620 3666869 := bbase (se 5 (by rfl) ⟨171884, by rfl⟩ : syracuseStep 3666869 = 343769) (by norm_num)
theorem B2749373 : Blo 1084620 2749373 := bbase (se 3 (by rfl) ⟨515507, by rfl⟩ : syracuseStep 2749373 = 1031015) (by norm_num)
theorem B1831909 : Blo 1084620 1831909 := bbase (se 4 (by rfl) ⟨171741, by rfl⟩ : syracuseStep 1831909 = 343483) (by norm_num)
theorem B4649957 : Blo 1084620 4649957 := bbase (se 4 (by rfl) ⟨435933, by rfl⟩ : syracuseStep 4649957 = 871867) (by norm_num)
theorem B2061301 : Blo 1084620 2061301 := bbase (se 5 (by rfl) ⟨96623, by rfl⟩ : syracuseStep 2061301 = 193247) (by norm_num)
theorem B1373213 : Blo 1084620 1373213 := bbase (se 3 (by rfl) ⟨257477, by rfl⟩ : syracuseStep 1373213 = 514955) (by norm_num)
theorem B5502005 : Blo 1084620 5502005 := bbase (se 5 (by rfl) ⟨257906, by rfl⟩ : syracuseStep 5502005 = 515813) (by norm_num)
theorem B1831997 : Blo 1084620 1831997 := bbase (se 3 (by rfl) ⟨343499, by rfl⟩ : syracuseStep 1831997 = 686999) (by norm_num)
theorem B1373269 : Blo 1084620 1373269 := bbase (se 8 (by rfl) ⟨8046, by rfl⟩ : syracuseStep 1373269 = 16093) (by norm_num)
theorem B2749565 : Blo 1084620 2749565 := bbase (se 3 (by rfl) ⟨515543, by rfl⟩ : syracuseStep 2749565 = 1031087) (by norm_num)
theorem B2061445 : Blo 1084620 2061445 := bbase (se 4 (by rfl) ⟨193260, by rfl⟩ : syracuseStep 2061445 = 386521) (by norm_num)
theorem B1373365 : Blo 1084620 1373365 := bbase (se 5 (by rfl) ⟨64376, by rfl⟩ : syracuseStep 1373365 = 128753) (by norm_num)
theorem B2323637 : Blo 1084620 2323637 := bbase (se 5 (by rfl) ⟨108920, by rfl⟩ : syracuseStep 2323637 = 217841) (by norm_num)
theorem B1832125 : Blo 1084620 1832125 := bbase (se 3 (by rfl) ⟨343523, by rfl⟩ : syracuseStep 1832125 = 687047) (by norm_num)
theorem B8254709 : Blo 1084620 8254709 := bbase (se 5 (by rfl) ⟨386939, by rfl⟩ : syracuseStep 8254709 = 773879) (by norm_num)
theorem B1832213 : Blo 1084620 1832213 := bbase (se 6 (by rfl) ⟨42942, by rfl⟩ : syracuseStep 1832213 = 85885) (by norm_num)
theorem B2061605 : Blo 1084620 2061605 := bbase (se 4 (by rfl) ⟨193275, by rfl⟩ : syracuseStep 2061605 = 386551) (by norm_num)
theorem B1373537 : Blo 1084620 1373537 := bbase (se 2 (by rfl) ⟨515076, by rfl⟩ : syracuseStep 1373537 = 1030153) (by norm_num)
theorem B3667301 : Blo 1084620 3667301 := bbase (se 4 (by rfl) ⟨343809, by rfl⟩ : syracuseStep 3667301 = 687619) (by norm_num)
theorem B1832341 : Blo 1084620 1832341 := bbase (se 6 (by rfl) ⟨42945, by rfl⟩ : syracuseStep 1832341 = 85891) (by norm_num)
theorem B1373593 : Blo 1084620 1373593 := bbase (se 2 (by rfl) ⟨515097, by rfl⟩ : syracuseStep 1373593 = 1030195) (by norm_num)
theorem B2323885 : Blo 1084620 2323885 := bbase (se 3 (by rfl) ⟨435728, by rfl⟩ : syracuseStep 2323885 = 871457) (by norm_num)
theorem B2061749 : Blo 1084620 2061749 := bbase (se 5 (by rfl) ⟨96644, by rfl⟩ : syracuseStep 2061749 = 193289) (by norm_num)
theorem B2749909 : Blo 1084620 2749909 := bbase (se 7 (by rfl) ⟨32225, by rfl⟩ : syracuseStep 2749909 = 64451) (by norm_num)
theorem B1832429 : Blo 1084620 1832429 := bbase (se 3 (by rfl) ⟨343580, by rfl⟩ : syracuseStep 1832429 = 687161) (by norm_num)
theorem B1373689 : Blo 1084620 1373689 := bbase (se 2 (by rfl) ⟨515133, by rfl⟩ : syracuseStep 1373689 = 1030267) (by norm_num)
theorem B4126261 : Blo 1084620 4126261 := bbase (se 5 (by rfl) ⟨193418, by rfl⟩ : syracuseStep 4126261 = 386837) (by norm_num)
theorem B2750021 : Blo 1084620 2750021 := bbase (se 4 (by rfl) ⟨257814, by rfl⟩ : syracuseStep 2750021 = 515629) (by norm_num)
theorem B1832557 : Blo 1084620 1832557 := bbase (se 3 (by rfl) ⟨343604, by rfl⟩ : syracuseStep 1832557 = 687209) (by norm_num)
theorem B1373861 : Blo 1084620 1373861 := bbase (se 4 (by rfl) ⟨128799, by rfl⟩ : syracuseStep 1373861 = 257599) (by norm_num)
theorem B1832645 : Blo 1084620 1832645 := bbase (se 4 (by rfl) ⟨171810, by rfl⟩ : syracuseStep 1832645 = 343621) (by norm_num)
theorem B2062037 : Blo 1084620 2062037 := bbase (se 7 (by rfl) ⟨24164, by rfl⟩ : syracuseStep 2062037 = 48329) (by norm_num)
theorem B1373917 : Blo 1084620 1373917 := bbase (se 3 (by rfl) ⟨257609, by rfl⟩ : syracuseStep 1373917 = 515219) (by norm_num)
theorem B2750213 : Blo 1084620 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B3667733 : Blo 1084620 3667733 := bbase (se 6 (by rfl) ⟨85962, by rfl⟩ : syracuseStep 3667733 = 171925) (by norm_num)
theorem B1374013 : Blo 1084620 1374013 := bbase (se 3 (by rfl) ⟨257627, by rfl⟩ : syracuseStep 1374013 = 515255) (by norm_num)
theorem B1832773 : Blo 1084620 1832773 := bbase (se 4 (by rfl) ⟨171822, by rfl⟩ : syracuseStep 1832773 = 343645) (by norm_num)
theorem B4126565 : Blo 1084620 4126565 := bbase (se 4 (by rfl) ⟨386865, by rfl⟩ : syracuseStep 4126565 = 773731) (by norm_num)
theorem B2062189 : Blo 1084620 2062189 := bbase (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) (by norm_num)
theorem B1832861 : Blo 1084620 1832861 := bbase (se 3 (by rfl) ⟨343661, by rfl⟩ : syracuseStep 1832861 = 687323) (by norm_num)
theorem B2324389 : Blo 1084620 2324389 := bbase (se 4 (by rfl) ⟨217911, by rfl⟩ : syracuseStep 2324389 = 435823) (by norm_num)
theorem B1374185 : Blo 1084620 1374185 := bbase (se 2 (by rfl) ⟨515319, by rfl⟩ : syracuseStep 1374185 = 1030639) (by norm_num)
theorem B1832989 : Blo 1084620 1832989 := bbase (se 3 (by rfl) ⟨343685, by rfl⟩ : syracuseStep 1832989 = 687371) (by norm_num)
theorem B1374241 : Blo 1084620 1374241 := bbase (se 2 (by rfl) ⟨515340, by rfl⟩ : syracuseStep 1374241 = 1030681) (by norm_num)
theorem B5568581 : Blo 1084620 5568581 := bbase (se 4 (by rfl) ⟨522054, by rfl⟩ : syracuseStep 5568581 = 1044109) (by norm_num)
theorem B2750557 : Blo 1084620 2750557 := bbase (se 3 (by rfl) ⟨515729, by rfl⟩ : syracuseStep 2750557 = 1031459) (by norm_num)
theorem B1833077 : Blo 1084620 1833077 := bbase (se 5 (by rfl) ⟨85925, by rfl⟩ : syracuseStep 1833077 = 171851) (by norm_num)
theorem B1374337 : Blo 1084620 1374337 := bbase (se 2 (by rfl) ⟨515376, by rfl⟩ : syracuseStep 1374337 = 1030753) (by norm_num)
theorem B2062493 : Blo 1084620 2062493 := bbase (se 3 (by rfl) ⟨386717, by rfl⟩ : syracuseStep 2062493 = 773435) (by norm_num)
theorem B3668165 : Blo 1084620 3668165 := bbase (se 4 (by rfl) ⟨343890, by rfl⟩ : syracuseStep 3668165 = 687781) (by norm_num)
theorem B2750669 : Blo 1084620 2750669 := bbase (se 3 (by rfl) ⟨515750, by rfl⟩ : syracuseStep 2750669 = 1031501) (by norm_num)
theorem B1833205 : Blo 1084620 1833205 := bbase (se 5 (by rfl) ⟨85931, by rfl⟩ : syracuseStep 1833205 = 171863) (by norm_num)
theorem B1374509 : Blo 1084620 1374509 := bbase (se 3 (by rfl) ⟨257720, by rfl⟩ : syracuseStep 1374509 = 515441) (by norm_num)
theorem B5503301 : Blo 1084620 5503301 := bbase (se 4 (by rfl) ⟨515934, by rfl⟩ : syracuseStep 5503301 = 1031869) (by norm_num)
theorem B1833293 : Blo 1084620 1833293 := bbase (se 3 (by rfl) ⟨343742, by rfl⟩ : syracuseStep 1833293 = 687485) (by norm_num)
theorem B2783573 : Blo 1084620 2783573 := bbase (se 10 (by rfl) ⟨4077, by rfl⟩ : syracuseStep 2783573 = 8155) (by norm_num)
theorem B1374565 : Blo 1084620 1374565 := bbase (se 4 (by rfl) ⟨128865, by rfl⟩ : syracuseStep 1374565 = 257731) (by norm_num)
theorem B2750861 : Blo 1084620 2750861 := bbase (se 3 (by rfl) ⟨515786, by rfl⟩ : syracuseStep 2750861 = 1031573) (by norm_num)
theorem B1374661 : Blo 1084620 1374661 := bbase (se 4 (by rfl) ⟨128874, by rfl⟩ : syracuseStep 1374661 = 257749) (by norm_num)
theorem B2783693 : Blo 1084620 2783693 := bbase (se 3 (by rfl) ⟨521942, by rfl⟩ : syracuseStep 2783693 = 1043885) (by norm_num)
theorem B1833421 : Blo 1084620 1833421 := bbase (se 3 (by rfl) ⟨343766, by rfl⟩ : syracuseStep 1833421 = 687533) (by norm_num)
theorem B1833509 : Blo 1084620 1833509 := bbase (se 4 (by rfl) ⟨171891, by rfl⟩ : syracuseStep 1833509 = 343783) (by norm_num)
theorem B1374833 : Blo 1084620 1374833 := bbase (se 2 (by rfl) ⟨515562, by rfl⟩ : syracuseStep 1374833 = 1031125) (by norm_num)
theorem B3668597 : Blo 1084620 3668597 := bbase (se 5 (by rfl) ⟨171965, by rfl⟩ : syracuseStep 3668597 = 343931) (by norm_num)
theorem B1833637 : Blo 1084620 1833637 := bbase (se 4 (by rfl) ⟨171903, by rfl⟩ : syracuseStep 1833637 = 343807) (by norm_num)
theorem B1374889 : Blo 1084620 1374889 := bbase (se 2 (by rfl) ⟨515583, by rfl⟩ : syracuseStep 1374889 = 1031167) (by norm_num)
theorem B2751205 : Blo 1084620 2751205 := bbase (se 4 (by rfl) ⟨257925, by rfl⟩ : syracuseStep 2751205 = 515851) (by norm_num)
theorem B1833725 : Blo 1084620 1833725 := bbase (se 3 (by rfl) ⟨343823, by rfl⟩ : syracuseStep 1833725 = 687647) (by norm_num)
theorem B1374985 : Blo 1084620 1374985 := bbase (se 2 (by rfl) ⟨515619, by rfl⟩ : syracuseStep 1374985 = 1031239) (by norm_num)
theorem B2751317 : Blo 1084620 2751317 := bbase (se 9 (by rfl) ⟨8060, by rfl⟩ : syracuseStep 2751317 = 16121) (by norm_num)
theorem B1833853 : Blo 1084620 1833853 := bbase (se 3 (by rfl) ⟨343847, by rfl⟩ : syracuseStep 1833853 = 687695) (by norm_num)
theorem B2063245 : Blo 1084620 2063245 := bbase (se 3 (by rfl) ⟨386858, by rfl⟩ : syracuseStep 2063245 = 773717) (by norm_num)
theorem B11140021 : Blo 1084620 11140021 := bbase (se 5 (by rfl) ⟨522188, by rfl⟩ : syracuseStep 11140021 = 1044377) (by norm_num)
theorem B1375157 : Blo 1084620 1375157 := bbase (se 5 (by rfl) ⟨64460, by rfl⟩ : syracuseStep 1375157 = 128921) (by norm_num)
theorem B3308485 : Blo 1084620 3308485 := bbase (se 4 (by rfl) ⟨310170, by rfl⟩ : syracuseStep 3308485 = 620341) (by norm_num)
theorem B1833941 : Blo 1084620 1833941 := bbase (se 7 (by rfl) ⟨21491, by rfl⟩ : syracuseStep 1833941 = 42983) (by norm_num)
theorem B1375213 : Blo 1084620 1375213 := bbase (se 3 (by rfl) ⟨257852, by rfl⟩ : syracuseStep 1375213 = 515705) (by norm_num)
theorem B2751509 : Blo 1084620 2751509 := bbase (se 6 (by rfl) ⟨64488, by rfl⟩ : syracuseStep 2751509 = 128977) (by norm_num)
theorem B2063389 : Blo 1084620 2063389 := bbase (se 3 (by rfl) ⟨386885, by rfl⟩ : syracuseStep 2063389 = 773771) (by norm_num)
theorem B3669029 : Blo 1084620 3669029 := bbase (se 4 (by rfl) ⟨343971, by rfl⟩ : syracuseStep 3669029 = 687943) (by norm_num)
theorem B1375309 : Blo 1084620 1375309 := bbase (se 3 (by rfl) ⟨257870, by rfl⟩ : syracuseStep 1375309 = 515741) (by norm_num)
theorem B1834069 : Blo 1084620 1834069 := bbase (se 8 (by rfl) ⟨10746, by rfl⟩ : syracuseStep 1834069 = 21493) (by norm_num)
theorem B1834157 : Blo 1084620 1834157 := bbase (se 3 (by rfl) ⟨343904, by rfl⟩ : syracuseStep 1834157 = 687809) (by norm_num)
theorem B2063549 : Blo 1084620 2063549 := bbase (se 3 (by rfl) ⟨386915, by rfl⟩ : syracuseStep 2063549 = 773831) (by norm_num)
theorem B1375481 : Blo 1084620 1375481 := bbase (se 2 (by rfl) ⟨515805, by rfl⟩ : syracuseStep 1375481 = 1031611) (by norm_num)
theorem B1834285 : Blo 1084620 1834285 := bbase (se 3 (by rfl) ⟨343928, by rfl⟩ : syracuseStep 1834285 = 687857) (by norm_num)
theorem B1375537 : Blo 1084620 1375537 := bbase (se 2 (by rfl) ⟨515826, by rfl⟩ : syracuseStep 1375537 = 1031653) (by norm_num)
theorem B2063693 : Blo 1084620 2063693 := bbase (se 3 (by rfl) ⟨386942, by rfl⟩ : syracuseStep 2063693 = 773885) (by norm_num)
theorem B2751853 : Blo 1084620 2751853 := bbase (se 3 (by rfl) ⟨515972, by rfl⟩ : syracuseStep 2751853 = 1031945) (by norm_num)
theorem B1834373 : Blo 1084620 1834373 := bbase (se 4 (by rfl) ⟨171972, by rfl⟩ : syracuseStep 1834373 = 343945) (by norm_num)
theorem B1375633 : Blo 1084620 1375633 := bbase (se 2 (by rfl) ⟨515862, by rfl⟩ : syracuseStep 1375633 = 1031725) (by norm_num)
theorem B3669461 : Blo 1084620 3669461 := bbase (se 7 (by rfl) ⟨43001, by rfl⟩ : syracuseStep 3669461 = 86003) (by norm_num)
theorem B2751965 : Blo 1084620 2751965 := bbase (se 3 (by rfl) ⟨515993, by rfl⟩ : syracuseStep 2751965 = 1031987) (by norm_num)
theorem B1834501 : Blo 1084620 1834501 := bbase (se 4 (by rfl) ⟨171984, by rfl⟩ : syracuseStep 1834501 = 343969) (by norm_num)
theorem B1375805 : Blo 1084620 1375805 := bbase (se 3 (by rfl) ⟨257963, by rfl⟩ : syracuseStep 1375805 = 515927) (by norm_num)
theorem B1343045 : Blo 1084620 1343045 := bbase (se 4 (by rfl) ⟨125910, by rfl⟩ : syracuseStep 1343045 = 251821) (by norm_num)
theorem B5504597 : Blo 1084620 5504597 := bbase (se 8 (by rfl) ⟨32253, by rfl⟩ : syracuseStep 5504597 = 64507) (by norm_num)
theorem B1834589 : Blo 1084620 1834589 := bbase (se 3 (by rfl) ⟨343985, by rfl⟩ : syracuseStep 1834589 = 687971) (by norm_num)
theorem B2063981 : Blo 1084620 2063981 := bbase (se 3 (by rfl) ⟨386996, by rfl⟩ : syracuseStep 2063981 = 773993) (by norm_num)
theorem B1375861 : Blo 1084620 1375861 := bbase (se 5 (by rfl) ⟨64493, by rfl⟩ : syracuseStep 1375861 = 128987) (by norm_num)
theorem B4947605 : Blo 1084620 4947605 := bbase (se 6 (by rfl) ⟨115959, by rfl⟩ : syracuseStep 4947605 = 231919) (by norm_num)
theorem B2752157 : Blo 1084620 2752157 := bbase (se 3 (by rfl) ⟨516029, by rfl⟩ : syracuseStep 2752157 = 1032059) (by norm_num)
theorem B1375957 : Blo 1084620 1375957 := bbase (se 7 (by rfl) ⟨16124, by rfl⟩ : syracuseStep 1375957 = 32249) (by norm_num)
theorem B1834717 : Blo 1084620 1834717 := bbase (se 3 (by rfl) ⟨344009, by rfl⟩ : syracuseStep 1834717 = 688019) (by norm_num)
theorem B2064133 : Blo 1084620 2064133 := bbase (se 4 (by rfl) ⟨193512, by rfl⟩ : syracuseStep 2064133 = 387025) (by norm_num)
theorem B4947749 : Blo 1084620 4947749 := bbase (se 4 (by rfl) ⟨463851, by rfl⟩ : syracuseStep 4947749 = 927703) (by norm_num)
theorem B1343281 : Blo 1084620 1343281 := bbase (se 2 (by rfl) ⟨503730, by rfl⟩ : syracuseStep 1343281 = 1007461) (by norm_num)
theorem B1834805 : Blo 1084620 1834805 := bbase (se 5 (by rfl) ⟨86006, by rfl⟩ : syracuseStep 1834805 = 172013) (by norm_num)
theorem B1376129 : Blo 1084620 1376129 := bbase (se 2 (by rfl) ⟨516048, by rfl⟩ : syracuseStep 1376129 = 1032097) (by norm_num)
theorem B3669893 : Blo 1084620 3669893 := bbase (se 4 (by rfl) ⟨344052, by rfl⟩ : syracuseStep 3669893 = 688105) (by norm_num)
theorem B4128677 : Blo 1084620 4128677 := bbase (se 4 (by rfl) ⟨387063, by rfl⟩ : syracuseStep 4128677 = 774127) (by norm_num)
theorem B1834933 : Blo 1084620 1834933 := bbase (se 5 (by rfl) ⟨86012, by rfl⟩ : syracuseStep 1834933 = 172025) (by norm_num)
theorem B1376185 : Blo 1084620 1376185 := bbase (se 2 (by rfl) ⟨516069, by rfl⟩ : syracuseStep 1376185 = 1032139) (by norm_num)
theorem B2752501 : Blo 1084620 2752501 := bbase (se 5 (by rfl) ⟨129023, by rfl⟩ : syracuseStep 2752501 = 258047) (by norm_num)
theorem B1835041 : Blo 1084620 1835041 := bstep (se 2 (by rfl) ⟨688140, by rfl⟩ : syracuseStep 1835041 = 1376281) B1376281
theorem B1376291 : Blo 1084620 1376291 := bstep (se 1 (by rfl) ⟨1032218, by rfl⟩ : syracuseStep 1376291 = 2064437) B2064437
theorem B1835075 : Blo 1084620 1835075 := bstep (se 1 (by rfl) ⟨1376306, by rfl⟩ : syracuseStep 1835075 = 2752613) B2752613
theorem B2752643 : Blo 1084620 2752643 := bstep (se 1 (by rfl) ⟨2064482, by rfl⟩ : syracuseStep 2752643 = 4128965) B4128965
theorem B1835203 : Blo 1084620 1835203 := bstep (se 1 (by rfl) ⟨1376402, by rfl⟩ : syracuseStep 1835203 = 2752805) B2752805
theorem B4128995 : Blo 1084620 4128995 := bstep (se 1 (by rfl) ⟨3096746, by rfl⟩ : syracuseStep 4128995 = 6193493) B6193493
theorem B1835345 : Blo 1084620 1835345 := bstep (se 2 (by rfl) ⟨688254, by rfl⟩ : syracuseStep 1835345 = 1376509) B1376509
theorem B9929101 : Blo 1084620 9929101 := bstep (se 3 (by rfl) ⟨1861706, by rfl⟩ : syracuseStep 9929101 = 3723413) B3723413
theorem B1835473 : Blo 1084620 1835473 := bstep (se 2 (by rfl) ⟨688302, by rfl⟩ : syracuseStep 1835473 = 1376605) B1376605
theorem B1114579 : Blo 1084620 1114579 := bstep (se 1 (by rfl) ⟨835934, by rfl⟩ : syracuseStep 1114579 = 1671869) B1671869
theorem B1835507 : Blo 1084620 1835507 := bstep (se 1 (by rfl) ⟨1376630, by rfl⟩ : syracuseStep 1835507 = 2753261) B2753261
theorem B3670541 : Blo 1084620 3670541 := bstep (se 3 (by rfl) ⟨688226, by rfl⟩ : syracuseStep 3670541 = 1376453) B1376453
theorem B3670595 : Blo 1084620 3670595 := bstep (se 1 (by rfl) ⟨2752946, by rfl⟩ : syracuseStep 3670595 = 5505893) B5505893
theorem B1835635 : Blo 1084620 1835635 := bstep (se 1 (by rfl) ⟨1376726, by rfl⟩ : syracuseStep 1835635 = 2753453) B2753453
theorem B2065105 : Blo 1084620 2065105 := bstep (se 2 (by rfl) ⟨774414, by rfl⟩ : syracuseStep 2065105 = 1548829) B1548829
theorem B1376995 : Blo 1084620 1376995 := bstep (se 1 (by rfl) ⟨1032746, by rfl⟩ : syracuseStep 1376995 = 2065493) B2065493
theorem B1835777 : Blo 1084620 1835777 := bstep (se 2 (by rfl) ⟨688416, by rfl⟩ : syracuseStep 1835777 = 1376833) B1376833
theorem B1377091 : Blo 1084620 1377091 := bstep (se 1 (by rfl) ⟨1032818, by rfl⟩ : syracuseStep 1377091 = 2065637) B2065637
theorem B3670865 : Blo 1084620 3670865 := bstep (se 2 (by rfl) ⟨1376574, by rfl⟩ : syracuseStep 3670865 = 2753149) B2753149
theorem B4129649 : Blo 1084620 4129649 := bstep (se 2 (by rfl) ⟨1548618, by rfl⟩ : syracuseStep 4129649 = 3097237) B3097237
theorem B1835905 : Blo 1084620 1835905 := bstep (se 2 (by rfl) ⟨688464, by rfl⟩ : syracuseStep 1835905 = 1376929) B1376929
theorem B1835939 : Blo 1084620 1835939 := bstep (se 1 (by rfl) ⟨1376954, by rfl⟩ : syracuseStep 1835939 = 2753909) B2753909
theorem B19104709 : Blo 1084620 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B1836067 : Blo 1084620 1836067 := bstep (se 1 (by rfl) ⟨1377050, by rfl⟩ : syracuseStep 1836067 = 2754101) B2754101
theorem B2753585 : Blo 1084620 2753585 := bstep (se 2 (by rfl) ⟨1032594, by rfl⟩ : syracuseStep 2753585 = 2065189) B2065189
theorem B2753635 : Blo 1084620 2753635 := bstep (se 1 (by rfl) ⟨2065226, by rfl⟩ : syracuseStep 2753635 = 4130453) B4130453
theorem B1836209 : Blo 1084620 1836209 := bstep (se 2 (by rfl) ⟨688578, by rfl⟩ : syracuseStep 1836209 = 1377157) B1377157
theorem B2753777 : Blo 1084620 2753777 := bstep (se 2 (by rfl) ⟨1032666, by rfl⟩ : syracuseStep 2753777 = 2065333) B2065333
theorem B1836337 : Blo 1084620 1836337 := bstep (se 2 (by rfl) ⟨688626, by rfl⟩ : syracuseStep 1836337 = 1377253) B1377253
theorem B1377587 : Blo 1084620 1377587 := bstep (se 1 (by rfl) ⟨1033190, by rfl⟩ : syracuseStep 1377587 = 2066381) B2066381
theorem B1836371 : Blo 1084620 1836371 := bstep (se 1 (by rfl) ⟨1377278, by rfl⟩ : syracuseStep 1836371 = 2754557) B2754557
theorem B13206883 : Blo 1084620 13206883 := bstep (se 1 (by rfl) ⟨9905162, by rfl⟩ : syracuseStep 13206883 = 19810325) B19810325
theorem B3671405 : Blo 1084620 3671405 := bstep (se 3 (by rfl) ⟨688388, by rfl⟩ : syracuseStep 3671405 = 1376777) B1376777
theorem B1738115 : Blo 1084620 1738115 := bstep (se 1 (by rfl) ⟨1303586, by rfl⟩ : syracuseStep 1738115 = 2607173) B2607173
theorem B3671459 : Blo 1084620 3671459 := bstep (se 1 (by rfl) ⟨2753594, by rfl⟩ : syracuseStep 3671459 = 5507189) B5507189
theorem B1836499 : Blo 1084620 1836499 := bstep (se 1 (by rfl) ⟨1377374, by rfl⟩ : syracuseStep 1836499 = 2754749) B2754749
theorem B1738307 : Blo 1084620 1738307 := bstep (se 1 (by rfl) ⟨1303730, by rfl⟩ : syracuseStep 1738307 = 2607461) B2607461
theorem B3475025 : Blo 1084620 3475025 := bstep (se 2 (by rfl) ⟨1303134, by rfl⟩ : syracuseStep 3475025 = 2606269) B2606269
theorem B1836641 : Blo 1084620 1836641 := bstep (se 2 (by rfl) ⟨688740, by rfl⟩ : syracuseStep 1836641 = 1377481) B1377481
theorem B3475075 : Blo 1084620 3475075 := bstep (se 1 (by rfl) ⟨2606306, by rfl⟩ : syracuseStep 3475075 = 5212613) B5212613
theorem B3671729 : Blo 1084620 3671729 := bstep (se 2 (by rfl) ⟨1376898, by rfl⟩ : syracuseStep 3671729 = 2753797) B2753797
theorem B1738435 : Blo 1084620 1738435 := bstep (se 1 (by rfl) ⟨1303826, by rfl⟩ : syracuseStep 1738435 = 2607653) B2607653
theorem B1836769 : Blo 1084620 1836769 := bstep (se 2 (by rfl) ⟨688788, by rfl⟩ : syracuseStep 1836769 = 1377577) B1377577
theorem B2066161 : Blo 1084620 2066161 := bstep (se 2 (by rfl) ⟨774810, by rfl⟩ : syracuseStep 2066161 = 1549621) B1549621
theorem B1836803 : Blo 1084620 1836803 := bstep (se 1 (by rfl) ⟨1377602, by rfl⟩ : syracuseStep 1836803 = 2755205) B2755205
theorem B5506865 : Blo 1084620 5506865 := bstep (se 2 (by rfl) ⟨2065074, by rfl⟩ : syracuseStep 5506865 = 4130149) B4130149
theorem B1836931 : Blo 1084620 1836931 := bstep (se 1 (by rfl) ⟨1377698, by rfl⟩ : syracuseStep 1836931 = 2755397) B2755397
theorem B8259569 : Blo 1084620 8259569 := bstep (se 2 (by rfl) ⟨3097338, by rfl⟩ : syracuseStep 8259569 = 6194677) B6194677
theorem B2066563 : Blo 1084620 2066563 := bstep (se 1 (by rfl) ⟨1549922, by rfl⟩ : syracuseStep 2066563 = 3099845) B3099845
theorem B2066609 : Blo 1084620 2066609 := bstep (se 2 (by rfl) ⟨774978, by rfl⟩ : syracuseStep 2066609 = 1549957) B1549957
theorem B3672269 : Blo 1084620 3672269 := bstep (se 3 (by rfl) ⟨688550, by rfl⟩ : syracuseStep 3672269 = 1377101) B1377101
theorem B2754769 : Blo 1084620 2754769 := bstep (se 2 (by rfl) ⟨1033038, by rfl⟩ : syracuseStep 2754769 = 2066077) B2066077
theorem B3672323 : Blo 1084620 3672323 := bstep (se 1 (by rfl) ⟨2754242, by rfl⟩ : syracuseStep 3672323 = 5508485) B5508485
theorem B4131107 : Blo 1084620 4131107 := bstep (se 1 (by rfl) ⟨3098330, by rfl⟩ : syracuseStep 4131107 = 6196661) B6196661
theorem B4131121 : Blo 1084620 4131121 := bstep (se 2 (by rfl) ⟨1549170, by rfl⟩ : syracuseStep 4131121 = 3098341) B3098341
theorem B1739075 : Blo 1084620 1739075 := bstep (se 1 (by rfl) ⟨1304306, by rfl⟩ : syracuseStep 1739075 = 2608613) B2608613
theorem B3475793 : Blo 1084620 3475793 := bstep (se 2 (by rfl) ⟨1303422, by rfl⟩ : syracuseStep 3475793 = 2606845) B2606845
theorem B1739153 : Blo 1084620 1739153 := bstep (se 2 (by rfl) ⟨652182, by rfl⟩ : syracuseStep 1739153 = 1304365) B1304365
theorem B2755043 : Blo 1084620 2755043 := bstep (se 1 (by rfl) ⟨2066282, by rfl⟩ : syracuseStep 2755043 = 4132565) B4132565
theorem B3672593 : Blo 1084620 3672593 := bstep (se 2 (by rfl) ⟨1377222, by rfl⟩ : syracuseStep 3672593 = 2754445) B2754445
theorem B2755235 : Blo 1084620 2755235 := bstep (se 1 (by rfl) ⟨2066426, by rfl⟩ : syracuseStep 2755235 = 4132853) B4132853
theorem B2788067 : Blo 1084620 2788067 := bstep (se 1 (by rfl) ⟨2091050, by rfl⟩ : syracuseStep 2788067 = 4182101) B4182101
theorem B6195953 : Blo 1084620 6195953 := bstep (se 2 (by rfl) ⟨2323482, by rfl⟩ : syracuseStep 6195953 = 4646965) B4646965
theorem B1739537 : Blo 1084620 1739537 := bstep (se 2 (by rfl) ⟨652326, by rfl⟩ : syracuseStep 1739537 = 1304653) B1304653
theorem B3476305 : Blo 1084620 3476305 := bstep (se 2 (by rfl) ⟨1303614, by rfl⟩ : syracuseStep 3476305 = 2607229) B2607229
theorem B1739665 : Blo 1084620 1739665 := bstep (se 2 (by rfl) ⟨652374, by rfl⟩ : syracuseStep 1739665 = 1304749) B1304749
theorem B12356549 : Blo 1084620 12356549 := bstep (se 4 (by rfl) ⟨1158426, by rfl⟩ : syracuseStep 12356549 = 2316853) B2316853
theorem B3673133 : Blo 1084620 3673133 := bstep (se 3 (by rfl) ⟨688712, by rfl⟩ : syracuseStep 3673133 = 1377425) B1377425
theorem B3673187 : Blo 1084620 3673187 := bstep (se 1 (by rfl) ⟨2754890, by rfl⟩ : syracuseStep 3673187 = 5509781) B5509781
theorem B1084627 : Blo 1084620 1084627 := bstep (se 1 (by rfl) ⟨813470, by rfl⟩ : syracuseStep 1084627 = 1626941) B1626941
theorem B1084643 : Blo 1084620 1084643 := bstep (se 1 (by rfl) ⟨813482, by rfl⟩ : syracuseStep 1084643 = 1626965) B1626965
theorem B5508323 : Blo 1084620 5508323 := bstep (se 1 (by rfl) ⟨4131242, by rfl⟩ : syracuseStep 5508323 = 8262485) B8262485
theorem B5573873 : Blo 1084620 5573873 := bstep (se 2 (by rfl) ⟨2090202, by rfl⟩ : syracuseStep 5573873 = 4180405) B4180405
theorem B1084659 : Blo 1084620 1084659 := bstep (se 1 (by rfl) ⟨813494, by rfl⟩ : syracuseStep 1084659 = 1626989) B1626989
theorem B1084675 : Blo 1084620 1084675 := bstep (se 1 (by rfl) ⟨813506, by rfl⟩ : syracuseStep 1084675 = 1627013) B1627013
theorem B1084691 : Blo 1084620 1084691 := bstep (se 1 (by rfl) ⟨813518, by rfl⟩ : syracuseStep 1084691 = 1627037) B1627037
theorem B1084707 : Blo 1084620 1084707 := bstep (se 1 (by rfl) ⟨813530, by rfl⟩ : syracuseStep 1084707 = 1627061) B1627061
theorem B1084723 : Blo 1084620 1084723 := bstep (se 1 (by rfl) ⟨813542, by rfl⟩ : syracuseStep 1084723 = 1627085) B1627085
theorem B1084739 : Blo 1084620 1084739 := bstep (se 1 (by rfl) ⟨813554, by rfl⟩ : syracuseStep 1084739 = 1627109) B1627109
theorem B1084755 : Blo 1084620 1084755 := bstep (se 1 (by rfl) ⟨813566, by rfl⟩ : syracuseStep 1084755 = 1627133) B1627133
theorem B1084771 : Blo 1084620 1084771 := bstep (se 1 (by rfl) ⟨813578, by rfl⟩ : syracuseStep 1084771 = 1627157) B1627157
theorem B7048561 : Blo 1084620 7048561 := bstep (se 2 (by rfl) ⟨2643210, by rfl⟩ : syracuseStep 7048561 = 5286421) B5286421
theorem B3673457 : Blo 1084620 3673457 := bstep (se 2 (by rfl) ⟨1377546, by rfl⟩ : syracuseStep 3673457 = 2755093) B2755093
theorem B1084787 : Blo 1084620 1084787 := bstep (se 1 (by rfl) ⟨813590, by rfl⟩ : syracuseStep 1084787 = 1627181) B1627181
theorem B1084803 : Blo 1084620 1084803 := bstep (se 1 (by rfl) ⟨813602, by rfl⟩ : syracuseStep 1084803 = 1627205) B1627205
theorem B1084819 : Blo 1084620 1084819 := bstep (se 1 (by rfl) ⟨813614, by rfl⟩ : syracuseStep 1084819 = 1627229) B1627229
theorem B1084835 : Blo 1084620 1084835 := bstep (se 1 (by rfl) ⟨813626, by rfl⟩ : syracuseStep 1084835 = 1627253) B1627253
theorem B1084851 : Blo 1084620 1084851 := bstep (se 1 (by rfl) ⟨813638, by rfl⟩ : syracuseStep 1084851 = 1627277) B1627277
theorem B1084867 : Blo 1084620 1084867 := bstep (se 1 (by rfl) ⟨813650, by rfl⟩ : syracuseStep 1084867 = 1627301) B1627301
theorem B1084883 : Blo 1084620 1084883 := bstep (se 1 (by rfl) ⟨813662, by rfl⟩ : syracuseStep 1084883 = 1627325) B1627325
theorem B1084899 : Blo 1084620 1084899 := bstep (se 1 (by rfl) ⟨813674, by rfl⟩ : syracuseStep 1084899 = 1627349) B1627349
theorem B1084915 : Blo 1084620 1084915 := bstep (se 1 (by rfl) ⟨813686, by rfl⟩ : syracuseStep 1084915 = 1627373) B1627373
theorem B1084931 : Blo 1084620 1084931 := bstep (se 1 (by rfl) ⟨813698, by rfl⟩ : syracuseStep 1084931 = 1627397) B1627397
theorem B1084947 : Blo 1084620 1084947 := bstep (se 1 (by rfl) ⟨813710, by rfl⟩ : syracuseStep 1084947 = 1627421) B1627421
theorem B1084963 : Blo 1084620 1084963 := bstep (se 1 (by rfl) ⟨813722, by rfl⟩ : syracuseStep 1084963 = 1627445) B1627445
theorem B2199089 : Blo 1084620 2199089 := bstep (se 2 (by rfl) ⟨824658, by rfl⟩ : syracuseStep 2199089 = 1649317) B1649317
theorem B1084979 : Blo 1084620 1084979 := bstep (se 1 (by rfl) ⟨813734, by rfl⟩ : syracuseStep 1084979 = 1627469) B1627469
theorem B1084995 : Blo 1084620 1084995 := bstep (se 1 (by rfl) ⟨813746, by rfl⟩ : syracuseStep 1084995 = 1627493) B1627493
theorem B1085011 : Blo 1084620 1085011 := bstep (se 1 (by rfl) ⟨813758, by rfl⟩ : syracuseStep 1085011 = 1627517) B1627517
theorem B1085027 : Blo 1084620 1085027 := bstep (se 1 (by rfl) ⟨813770, by rfl⟩ : syracuseStep 1085027 = 1627541) B1627541
theorem B1085043 : Blo 1084620 1085043 := bstep (se 1 (by rfl) ⟨813782, by rfl⟩ : syracuseStep 1085043 = 1627565) B1627565
theorem B1085059 : Blo 1084620 1085059 := bstep (se 1 (by rfl) ⟨813794, by rfl⟩ : syracuseStep 1085059 = 1627589) B1627589
theorem B1085075 : Blo 1084620 1085075 := bstep (se 1 (by rfl) ⟨813806, by rfl⟩ : syracuseStep 1085075 = 1627613) B1627613
theorem B1085091 : Blo 1084620 1085091 := bstep (se 1 (by rfl) ⟨813818, by rfl⟩ : syracuseStep 1085091 = 1627637) B1627637
theorem B1085107 : Blo 1084620 1085107 := bstep (se 1 (by rfl) ⟨813830, by rfl⟩ : syracuseStep 1085107 = 1627661) B1627661
theorem B1085123 : Blo 1084620 1085123 := bstep (se 1 (by rfl) ⟨813842, by rfl⟩ : syracuseStep 1085123 = 1627685) B1627685
theorem B1085139 : Blo 1084620 1085139 := bstep (se 1 (by rfl) ⟨813854, by rfl⟩ : syracuseStep 1085139 = 1627709) B1627709
theorem B1085155 : Blo 1084620 1085155 := bstep (se 1 (by rfl) ⟨813866, by rfl⟩ : syracuseStep 1085155 = 1627733) B1627733
theorem B4132579 : Blo 1084620 4132579 := bstep (se 1 (by rfl) ⟨3099434, by rfl⟩ : syracuseStep 4132579 = 6198869) B6198869
theorem B1085171 : Blo 1084620 1085171 := bstep (se 1 (by rfl) ⟨813878, by rfl⟩ : syracuseStep 1085171 = 1627757) B1627757
theorem B1085187 : Blo 1084620 1085187 := bstep (se 1 (by rfl) ⟨813890, by rfl⟩ : syracuseStep 1085187 = 1627781) B1627781
theorem B1085203 : Blo 1084620 1085203 := bstep (se 1 (by rfl) ⟨813902, by rfl⟩ : syracuseStep 1085203 = 1627805) B1627805
theorem B1085219 : Blo 1084620 1085219 := bstep (se 1 (by rfl) ⟨813914, by rfl⟩ : syracuseStep 1085219 = 1627829) B1627829
theorem B5869361 : Blo 1084620 5869361 := bstep (se 2 (by rfl) ⟨2201010, by rfl⟩ : syracuseStep 5869361 = 4402021) B4402021
theorem B1085235 : Blo 1084620 1085235 := bstep (se 1 (by rfl) ⟨813926, by rfl⟩ : syracuseStep 1085235 = 1627853) B1627853
theorem B1085251 : Blo 1084620 1085251 := bstep (se 1 (by rfl) ⟨813938, by rfl⟩ : syracuseStep 1085251 = 1627877) B1627877
theorem B1085267 : Blo 1084620 1085267 := bstep (se 1 (by rfl) ⟨813950, by rfl⟩ : syracuseStep 1085267 = 1627901) B1627901
theorem B1085283 : Blo 1084620 1085283 := bstep (se 1 (by rfl) ⟨813962, by rfl⟩ : syracuseStep 1085283 = 1627925) B1627925
theorem B29003633 : Blo 1084620 29003633 := bstep (se 2 (by rfl) ⟨10876362, by rfl⟩ : syracuseStep 29003633 = 21752725) B21752725
theorem B1085299 : Blo 1084620 1085299 := bstep (se 1 (by rfl) ⟨813974, by rfl⟩ : syracuseStep 1085299 = 1627949) B1627949
theorem B1085315 : Blo 1084620 1085315 := bstep (se 1 (by rfl) ⟨813986, by rfl⟩ : syracuseStep 1085315 = 1627973) B1627973
theorem B3673997 : Blo 1084620 3673997 := bstep (se 3 (by rfl) ⟨688874, by rfl⟩ : syracuseStep 3673997 = 1377749) B1377749
theorem B1085331 : Blo 1084620 1085331 := bstep (se 1 (by rfl) ⟨813998, by rfl⟩ : syracuseStep 1085331 = 1627997) B1627997
theorem B1085347 : Blo 1084620 1085347 := bstep (se 1 (by rfl) ⟨814010, by rfl⟩ : syracuseStep 1085347 = 1628021) B1628021
theorem B3477421 : Blo 1084620 3477421 := bstep (se 3 (by rfl) ⟨652016, by rfl⟩ : syracuseStep 3477421 = 1304033) B1304033
theorem B1085363 : Blo 1084620 1085363 := bstep (se 1 (by rfl) ⟨814022, by rfl⟩ : syracuseStep 1085363 = 1628045) B1628045
theorem B1085379 : Blo 1084620 1085379 := bstep (se 1 (by rfl) ⟨814034, by rfl⟩ : syracuseStep 1085379 = 1628069) B1628069
theorem B3674051 : Blo 1084620 3674051 := bstep (se 1 (by rfl) ⟨2755538, by rfl⟩ : syracuseStep 3674051 = 5511077) B5511077
theorem B1085395 : Blo 1084620 1085395 := bstep (se 1 (by rfl) ⟨814046, by rfl⟩ : syracuseStep 1085395 = 1628093) B1628093
theorem B1085411 : Blo 1084620 1085411 := bstep (se 1 (by rfl) ⟨814058, by rfl⟩ : syracuseStep 1085411 = 1628117) B1628117
theorem B3477485 : Blo 1084620 3477485 := bstep (se 3 (by rfl) ⟨652028, by rfl⟩ : syracuseStep 3477485 = 1304057) B1304057
theorem B1085427 : Blo 1084620 1085427 := bstep (se 1 (by rfl) ⟨814070, by rfl⟩ : syracuseStep 1085427 = 1628141) B1628141
theorem B1085443 : Blo 1084620 1085443 := bstep (se 1 (by rfl) ⟨814082, by rfl⟩ : syracuseStep 1085443 = 1628165) B1628165
theorem B5509133 : Blo 1084620 5509133 := bstep (se 3 (by rfl) ⟨1032962, by rfl⟩ : syracuseStep 5509133 = 2065925) B2065925
theorem B1085459 : Blo 1084620 1085459 := bstep (se 1 (by rfl) ⟨814094, by rfl⟩ : syracuseStep 1085459 = 1628189) B1628189
theorem B1085475 : Blo 1084620 1085475 := bstep (se 1 (by rfl) ⟨814106, by rfl⟩ : syracuseStep 1085475 = 1628213) B1628213
theorem B1085491 : Blo 1084620 1085491 := bstep (se 1 (by rfl) ⟨814118, by rfl⟩ : syracuseStep 1085491 = 1628237) B1628237
theorem B1085507 : Blo 1084620 1085507 := bstep (se 1 (by rfl) ⟨814130, by rfl⟩ : syracuseStep 1085507 = 1628261) B1628261
theorem B1085523 : Blo 1084620 1085523 := bstep (se 1 (by rfl) ⟨814142, by rfl⟩ : syracuseStep 1085523 = 1628285) B1628285
theorem B1085539 : Blo 1084620 1085539 := bstep (se 1 (by rfl) ⟨814154, by rfl⟩ : syracuseStep 1085539 = 1628309) B1628309
theorem B1085555 : Blo 1084620 1085555 := bstep (se 1 (by rfl) ⟨814166, by rfl⟩ : syracuseStep 1085555 = 1628333) B1628333
theorem B1085571 : Blo 1084620 1085571 := bstep (se 1 (by rfl) ⟨814178, by rfl⟩ : syracuseStep 1085571 = 1628357) B1628357
theorem B1085587 : Blo 1084620 1085587 := bstep (se 1 (by rfl) ⟨814190, by rfl⟩ : syracuseStep 1085587 = 1628381) B1628381
theorem B1085603 : Blo 1084620 1085603 := bstep (se 1 (by rfl) ⟨814202, by rfl⟩ : syracuseStep 1085603 = 1628405) B1628405
theorem B6197411 : Blo 1084620 6197411 := bstep (se 1 (by rfl) ⟨4648058, by rfl⟩ : syracuseStep 6197411 = 9296117) B9296117
theorem B2232497 : Blo 1084620 2232497 := bstep (se 2 (by rfl) ⟨837186, by rfl⟩ : syracuseStep 2232497 = 1674373) B1674373
theorem B1085619 : Blo 1084620 1085619 := bstep (se 1 (by rfl) ⟨814214, by rfl⟩ : syracuseStep 1085619 = 1628429) B1628429
theorem B1085635 : Blo 1084620 1085635 := bstep (se 1 (by rfl) ⟨814226, by rfl⟩ : syracuseStep 1085635 = 1628453) B1628453
theorem B1085651 : Blo 1084620 1085651 := bstep (se 1 (by rfl) ⟨814238, by rfl⟩ : syracuseStep 1085651 = 1628477) B1628477
theorem B1085667 : Blo 1084620 1085667 := bstep (se 1 (by rfl) ⟨814250, by rfl⟩ : syracuseStep 1085667 = 1628501) B1628501
theorem B1085683 : Blo 1084620 1085683 := bstep (se 1 (by rfl) ⟨814262, by rfl⟩ : syracuseStep 1085683 = 1628525) B1628525
theorem B1085699 : Blo 1084620 1085699 := bstep (se 1 (by rfl) ⟨814274, by rfl⟩ : syracuseStep 1085699 = 1628549) B1628549
theorem B1085715 : Blo 1084620 1085715 := bstep (se 1 (by rfl) ⟨814286, by rfl⟩ : syracuseStep 1085715 = 1628573) B1628573
theorem B1085731 : Blo 1084620 1085731 := bstep (se 1 (by rfl) ⟨814298, by rfl⟩ : syracuseStep 1085731 = 1628597) B1628597
theorem B1085747 : Blo 1084620 1085747 := bstep (se 1 (by rfl) ⟨814310, by rfl⟩ : syracuseStep 1085747 = 1628621) B1628621
theorem B1085763 : Blo 1084620 1085763 := bstep (se 1 (by rfl) ⟨814322, by rfl⟩ : syracuseStep 1085763 = 1628645) B1628645
theorem B1085779 : Blo 1084620 1085779 := bstep (se 1 (by rfl) ⟨814334, by rfl⟩ : syracuseStep 1085779 = 1628669) B1628669
theorem B1085795 : Blo 1084620 1085795 := bstep (se 1 (by rfl) ⟨814346, by rfl⟩ : syracuseStep 1085795 = 1628693) B1628693
theorem B1085811 : Blo 1084620 1085811 := bstep (se 1 (by rfl) ⟨814358, by rfl⟩ : syracuseStep 1085811 = 1628717) B1628717
theorem B1741171 : Blo 1084620 1741171 := bstep (se 1 (by rfl) ⟨1305878, by rfl⟩ : syracuseStep 1741171 = 2611757) B2611757
theorem B1085827 : Blo 1084620 1085827 := bstep (se 1 (by rfl) ⟨814370, by rfl⟩ : syracuseStep 1085827 = 1628741) B1628741
theorem B1085843 : Blo 1084620 1085843 := bstep (se 1 (by rfl) ⟨814382, by rfl⟩ : syracuseStep 1085843 = 1628765) B1628765
theorem B1544609 : Blo 1084620 1544609 := bstep (se 2 (by rfl) ⟨579228, by rfl⟩ : syracuseStep 1544609 = 1158457) B1158457
theorem B1085859 : Blo 1084620 1085859 := bstep (se 1 (by rfl) ⟨814394, by rfl⟩ : syracuseStep 1085859 = 1628789) B1628789
theorem B1085875 : Blo 1084620 1085875 := bstep (se 1 (by rfl) ⟨814406, by rfl⟩ : syracuseStep 1085875 = 1628813) B1628813
theorem B1085891 : Blo 1084620 1085891 := bstep (se 1 (by rfl) ⟨814418, by rfl⟩ : syracuseStep 1085891 = 1628837) B1628837
theorem B7442885 : Blo 1084620 7442885 := bstep (se 4 (by rfl) ⟨697770, by rfl⟩ : syracuseStep 7442885 = 1395541) B1395541
theorem B1085907 : Blo 1084620 1085907 := bstep (se 1 (by rfl) ⟨814430, by rfl⟩ : syracuseStep 1085907 = 1628861) B1628861
theorem B1085923 : Blo 1084620 1085923 := bstep (se 1 (by rfl) ⟨814442, by rfl⟩ : syracuseStep 1085923 = 1628885) B1628885
theorem B2789873 : Blo 1084620 2789873 := bstep (se 2 (by rfl) ⟨1046202, by rfl⟩ : syracuseStep 2789873 = 2092405) B2092405
theorem B1085939 : Blo 1084620 1085939 := bstep (se 1 (by rfl) ⟨814454, by rfl⟩ : syracuseStep 1085939 = 1628909) B1628909
theorem B1085955 : Blo 1084620 1085955 := bstep (se 1 (by rfl) ⟨814466, by rfl⟩ : syracuseStep 1085955 = 1628933) B1628933
theorem B1085971 : Blo 1084620 1085971 := bstep (se 1 (by rfl) ⟨814478, by rfl⟩ : syracuseStep 1085971 = 1628957) B1628957
theorem B1085987 : Blo 1084620 1085987 := bstep (se 1 (by rfl) ⟨814490, by rfl⟩ : syracuseStep 1085987 = 1628981) B1628981
theorem B1086003 : Blo 1084620 1086003 := bstep (se 1 (by rfl) ⟨814502, by rfl⟩ : syracuseStep 1086003 = 1629005) B1629005
theorem B30511669 : Blo 1084620 30511669 := bstep (se 5 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 30511669 = 2860469) B2860469
theorem B1086019 : Blo 1084620 1086019 := bstep (se 1 (by rfl) ⟨814514, by rfl⟩ : syracuseStep 1086019 = 1629029) B1629029
theorem B1086035 : Blo 1084620 1086035 := bstep (se 1 (by rfl) ⟨814526, by rfl⟩ : syracuseStep 1086035 = 1629053) B1629053
theorem B2822755 : Blo 1084620 2822755 := bstep (se 1 (by rfl) ⟨2117066, by rfl⟩ : syracuseStep 2822755 = 4234133) B4234133
theorem B1086051 : Blo 1084620 1086051 := bstep (se 1 (by rfl) ⟨814538, by rfl⟩ : syracuseStep 1086051 = 1629077) B1629077
theorem B1086067 : Blo 1084620 1086067 := bstep (se 1 (by rfl) ⟨814550, by rfl⟩ : syracuseStep 1086067 = 1629101) B1629101
theorem B1086083 : Blo 1084620 1086083 := bstep (se 1 (by rfl) ⟨814562, by rfl⟩ : syracuseStep 1086083 = 1629125) B1629125
theorem B1086099 : Blo 1084620 1086099 := bstep (se 1 (by rfl) ⟨814574, by rfl⟩ : syracuseStep 1086099 = 1629149) B1629149
theorem B1086115 : Blo 1084620 1086115 := bstep (se 1 (by rfl) ⟨814586, by rfl⟩ : syracuseStep 1086115 = 1629173) B1629173
theorem B1086131 : Blo 1084620 1086131 := bstep (se 1 (by rfl) ⟨814598, by rfl⟩ : syracuseStep 1086131 = 1629197) B1629197
theorem B1086147 : Blo 1084620 1086147 := bstep (se 1 (by rfl) ⟨814610, by rfl⟩ : syracuseStep 1086147 = 1629221) B1629221
theorem B1086163 : Blo 1084620 1086163 := bstep (se 1 (by rfl) ⟨814622, by rfl⟩ : syracuseStep 1086163 = 1629245) B1629245
theorem B1086179 : Blo 1084620 1086179 := bstep (se 1 (by rfl) ⟨814634, by rfl⟩ : syracuseStep 1086179 = 1629269) B1629269
theorem B1086195 : Blo 1084620 1086195 := bstep (se 1 (by rfl) ⟨814646, by rfl⟩ : syracuseStep 1086195 = 1629293) B1629293
theorem B1086211 : Blo 1084620 1086211 := bstep (se 1 (by rfl) ⟨814658, by rfl⟩ : syracuseStep 1086211 = 1629317) B1629317
theorem B1086227 : Blo 1084620 1086227 := bstep (se 1 (by rfl) ⟨814670, by rfl⟩ : syracuseStep 1086227 = 1629341) B1629341
theorem B1086243 : Blo 1084620 1086243 := bstep (se 1 (by rfl) ⟨814682, by rfl⟩ : syracuseStep 1086243 = 1629365) B1629365
theorem B1086259 : Blo 1084620 1086259 := bstep (se 1 (by rfl) ⟨814694, by rfl⟩ : syracuseStep 1086259 = 1629389) B1629389
theorem B1086275 : Blo 1084620 1086275 := bstep (se 1 (by rfl) ⟨814706, by rfl⟩ : syracuseStep 1086275 = 1629413) B1629413
theorem B1086291 : Blo 1084620 1086291 := bstep (se 1 (by rfl) ⟨814718, by rfl⟩ : syracuseStep 1086291 = 1629437) B1629437
theorem B1086307 : Blo 1084620 1086307 := bstep (se 1 (by rfl) ⟨814730, by rfl⟩ : syracuseStep 1086307 = 1629461) B1629461
theorem B1086323 : Blo 1084620 1086323 := bstep (se 1 (by rfl) ⟨814742, by rfl⟩ : syracuseStep 1086323 = 1629485) B1629485
theorem B1086339 : Blo 1084620 1086339 := bstep (se 1 (by rfl) ⟨814754, by rfl⟩ : syracuseStep 1086339 = 1629509) B1629509
theorem B1086355 : Blo 1084620 1086355 := bstep (se 1 (by rfl) ⟨814766, by rfl⟩ : syracuseStep 1086355 = 1629533) B1629533
theorem B1086371 : Blo 1084620 1086371 := bstep (se 1 (by rfl) ⟨814778, by rfl⟩ : syracuseStep 1086371 = 1629557) B1629557
theorem B1086387 : Blo 1084620 1086387 := bstep (se 1 (by rfl) ⟨814790, by rfl⟩ : syracuseStep 1086387 = 1629581) B1629581
theorem B1086403 : Blo 1084620 1086403 := bstep (se 1 (by rfl) ⟨814802, by rfl⟩ : syracuseStep 1086403 = 1629605) B1629605
theorem B59413445 : Blo 1084620 59413445 := bstep (se 4 (by rfl) ⟨5570010, by rfl⟩ : syracuseStep 59413445 = 11140021) B11140021
theorem B1086419 : Blo 1084620 1086419 := bstep (se 1 (by rfl) ⟨814814, by rfl⟩ : syracuseStep 1086419 = 1629629) B1629629
theorem B1086435 : Blo 1084620 1086435 := bstep (se 1 (by rfl) ⟨814826, by rfl⟩ : syracuseStep 1086435 = 1629653) B1629653
theorem B1086451 : Blo 1084620 1086451 := bstep (se 1 (by rfl) ⟨814838, by rfl⟩ : syracuseStep 1086451 = 1629677) B1629677
theorem B1086467 : Blo 1084620 1086467 := bstep (se 1 (by rfl) ⟨814850, by rfl⟩ : syracuseStep 1086467 = 1629701) B1629701
theorem B1086483 : Blo 1084620 1086483 := bstep (se 1 (by rfl) ⟨814862, by rfl⟩ : syracuseStep 1086483 = 1629725) B1629725
theorem B1741843 : Blo 1084620 1741843 := bstep (se 1 (by rfl) ⟨1306382, by rfl⟩ : syracuseStep 1741843 = 2612765) B2612765
theorem B1086499 : Blo 1084620 1086499 := bstep (se 1 (by rfl) ⟨814874, by rfl⟩ : syracuseStep 1086499 = 1629749) B1629749
theorem B1086515 : Blo 1084620 1086515 := bstep (se 1 (by rfl) ⟨814886, by rfl⟩ : syracuseStep 1086515 = 1629773) B1629773
theorem B1086531 : Blo 1084620 1086531 := bstep (se 1 (by rfl) ⟨814898, by rfl⟩ : syracuseStep 1086531 = 1629797) B1629797
theorem B1086547 : Blo 1084620 1086547 := bstep (se 1 (by rfl) ⟨814910, by rfl⟩ : syracuseStep 1086547 = 1629821) B1629821
theorem B1086563 : Blo 1084620 1086563 := bstep (se 1 (by rfl) ⟨814922, by rfl⟩ : syracuseStep 1086563 = 1629845) B1629845
theorem B1086579 : Blo 1084620 1086579 := bstep (se 1 (by rfl) ⟨814934, by rfl⟩ : syracuseStep 1086579 = 1629869) B1629869
theorem B1086595 : Blo 1084620 1086595 := bstep (se 1 (by rfl) ⟨814946, by rfl⟩ : syracuseStep 1086595 = 1629893) B1629893
theorem B1086611 : Blo 1084620 1086611 := bstep (se 1 (by rfl) ⟨814958, by rfl⟩ : syracuseStep 1086611 = 1629917) B1629917
theorem B1086627 : Blo 1084620 1086627 := bstep (se 1 (by rfl) ⟨814970, by rfl⟩ : syracuseStep 1086627 = 1629941) B1629941
theorem B1086643 : Blo 1084620 1086643 := bstep (se 1 (by rfl) ⟨814982, by rfl⟩ : syracuseStep 1086643 = 1629965) B1629965
theorem B1086659 : Blo 1084620 1086659 := bstep (se 1 (by rfl) ⟨814994, by rfl⟩ : syracuseStep 1086659 = 1629989) B1629989
theorem B1086675 : Blo 1084620 1086675 := bstep (se 1 (by rfl) ⟨815006, by rfl⟩ : syracuseStep 1086675 = 1630013) B1630013
theorem B1086691 : Blo 1084620 1086691 := bstep (se 1 (by rfl) ⟨815018, by rfl⟩ : syracuseStep 1086691 = 1630037) B1630037
theorem B1086707 : Blo 1084620 1086707 := bstep (se 1 (by rfl) ⟨815030, by rfl⟩ : syracuseStep 1086707 = 1630061) B1630061
theorem B1545475 : Blo 1084620 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B1086723 : Blo 1084620 1086723 := bstep (se 1 (by rfl) ⟨815042, by rfl⟩ : syracuseStep 1086723 = 1630085) B1630085
theorem B1086739 : Blo 1084620 1086739 := bstep (se 1 (by rfl) ⟨815054, by rfl⟩ : syracuseStep 1086739 = 1630109) B1630109
theorem B1086755 : Blo 1084620 1086755 := bstep (se 1 (by rfl) ⟨815066, by rfl⟩ : syracuseStep 1086755 = 1630133) B1630133
theorem B1086771 : Blo 1084620 1086771 := bstep (se 1 (by rfl) ⟨815078, by rfl⟩ : syracuseStep 1086771 = 1630157) B1630157
theorem B1086787 : Blo 1084620 1086787 := bstep (se 1 (by rfl) ⟨815090, by rfl⟩ : syracuseStep 1086787 = 1630181) B1630181
theorem B1086803 : Blo 1084620 1086803 := bstep (se 1 (by rfl) ⟨815102, by rfl⟩ : syracuseStep 1086803 = 1630205) B1630205
theorem B1545571 : Blo 1084620 1545571 := bstep (se 1 (by rfl) ⟨1159178, by rfl⟩ : syracuseStep 1545571 = 2318357) B2318357
theorem B1086819 : Blo 1084620 1086819 := bstep (se 1 (by rfl) ⟨815114, by rfl⟩ : syracuseStep 1086819 = 1630229) B1630229
theorem B1086835 : Blo 1084620 1086835 := bstep (se 1 (by rfl) ⟨815126, by rfl⟩ : syracuseStep 1086835 = 1630253) B1630253
theorem B1086851 : Blo 1084620 1086851 := bstep (se 1 (by rfl) ⟨815138, by rfl⟩ : syracuseStep 1086851 = 1630277) B1630277
theorem B1086867 : Blo 1084620 1086867 := bstep (se 1 (by rfl) ⟨815150, by rfl⟩ : syracuseStep 1086867 = 1630301) B1630301
theorem B1086883 : Blo 1084620 1086883 := bstep (se 1 (by rfl) ⟨815162, by rfl⟩ : syracuseStep 1086883 = 1630325) B1630325
theorem B1086899 : Blo 1084620 1086899 := bstep (se 1 (by rfl) ⟨815174, by rfl⟩ : syracuseStep 1086899 = 1630349) B1630349
theorem B1086915 : Blo 1084620 1086915 := bstep (se 1 (by rfl) ⟨815186, by rfl⟩ : syracuseStep 1086915 = 1630373) B1630373
theorem B1086931 : Blo 1084620 1086931 := bstep (se 1 (by rfl) ⟨815198, by rfl⟩ : syracuseStep 1086931 = 1630397) B1630397
theorem B1742305 : Blo 1084620 1742305 := bstep (se 2 (by rfl) ⟨653364, by rfl⟩ : syracuseStep 1742305 = 1306729) B1306729
theorem B1086947 : Blo 1084620 1086947 := bstep (se 1 (by rfl) ⟨815210, by rfl⟩ : syracuseStep 1086947 = 1630421) B1630421
theorem B1086963 : Blo 1084620 1086963 := bstep (se 1 (by rfl) ⟨815222, by rfl⟩ : syracuseStep 1086963 = 1630445) B1630445
theorem B1086979 : Blo 1084620 1086979 := bstep (se 1 (by rfl) ⟨815234, by rfl⟩ : syracuseStep 1086979 = 1630469) B1630469
theorem B1086995 : Blo 1084620 1086995 := bstep (se 1 (by rfl) ⟨815246, by rfl⟩ : syracuseStep 1086995 = 1630493) B1630493
theorem B1087011 : Blo 1084620 1087011 := bstep (se 1 (by rfl) ⟨815258, by rfl⟩ : syracuseStep 1087011 = 1630517) B1630517
theorem B1087027 : Blo 1084620 1087027 := bstep (se 1 (by rfl) ⟨815270, by rfl⟩ : syracuseStep 1087027 = 1630541) B1630541
theorem B1742401 : Blo 1084620 1742401 := bstep (se 2 (by rfl) ⟨653400, by rfl⟩ : syracuseStep 1742401 = 1306801) B1306801
theorem B1087043 : Blo 1084620 1087043 := bstep (se 1 (by rfl) ⟨815282, by rfl⟩ : syracuseStep 1087043 = 1630565) B1630565
theorem B1087059 : Blo 1084620 1087059 := bstep (se 1 (by rfl) ⟨815294, by rfl⟩ : syracuseStep 1087059 = 1630589) B1630589
theorem B1087075 : Blo 1084620 1087075 := bstep (se 1 (by rfl) ⟨815306, by rfl⟩ : syracuseStep 1087075 = 1630613) B1630613
theorem B6035057 : Blo 1084620 6035057 := bstep (se 2 (by rfl) ⟨2263146, by rfl⟩ : syracuseStep 6035057 = 4526293) B4526293
theorem B12719729 : Blo 1084620 12719729 := bstep (se 2 (by rfl) ⟨4769898, by rfl⟩ : syracuseStep 12719729 = 9539797) B9539797
theorem B1087091 : Blo 1084620 1087091 := bstep (se 1 (by rfl) ⟨815318, by rfl⟩ : syracuseStep 1087091 = 1630637) B1630637
theorem B1087107 : Blo 1084620 1087107 := bstep (se 1 (by rfl) ⟨815330, by rfl⟩ : syracuseStep 1087107 = 1630661) B1630661
theorem B1087123 : Blo 1084620 1087123 := bstep (se 1 (by rfl) ⟨815342, by rfl⟩ : syracuseStep 1087123 = 1630685) B1630685
theorem B1087139 : Blo 1084620 1087139 := bstep (se 1 (by rfl) ⟨815354, by rfl⟩ : syracuseStep 1087139 = 1630709) B1630709
theorem B1087155 : Blo 1084620 1087155 := bstep (se 1 (by rfl) ⟨815366, by rfl⟩ : syracuseStep 1087155 = 1630733) B1630733
theorem B1087171 : Blo 1084620 1087171 := bstep (se 1 (by rfl) ⟨815378, by rfl⟩ : syracuseStep 1087171 = 1630757) B1630757
theorem B1087187 : Blo 1084620 1087187 := bstep (se 1 (by rfl) ⟨815390, by rfl⟩ : syracuseStep 1087187 = 1630781) B1630781
theorem B1742561 : Blo 1084620 1742561 := bstep (se 2 (by rfl) ⟨653460, by rfl⟩ : syracuseStep 1742561 = 1306921) B1306921
theorem B3479267 : Blo 1084620 3479267 := bstep (se 1 (by rfl) ⟨2609450, by rfl⟩ : syracuseStep 3479267 = 5218901) B5218901
theorem B1087203 : Blo 1084620 1087203 := bstep (se 1 (by rfl) ⟨815402, by rfl⟩ : syracuseStep 1087203 = 1630805) B1630805
theorem B1087219 : Blo 1084620 1087219 := bstep (se 1 (by rfl) ⟨815414, by rfl⟩ : syracuseStep 1087219 = 1630829) B1630829
theorem B1087235 : Blo 1084620 1087235 := bstep (se 1 (by rfl) ⟨815426, by rfl⟩ : syracuseStep 1087235 = 1630853) B1630853
theorem B1087251 : Blo 1084620 1087251 := bstep (se 1 (by rfl) ⟨815438, by rfl⟩ : syracuseStep 1087251 = 1630877) B1630877
theorem B1087267 : Blo 1084620 1087267 := bstep (se 1 (by rfl) ⟨815450, by rfl⟩ : syracuseStep 1087267 = 1630901) B1630901
theorem B1087283 : Blo 1084620 1087283 := bstep (se 1 (by rfl) ⟨815462, by rfl⟩ : syracuseStep 1087283 = 1630925) B1630925
theorem B1087299 : Blo 1084620 1087299 := bstep (se 1 (by rfl) ⟨815474, by rfl⟩ : syracuseStep 1087299 = 1630949) B1630949
theorem B1546067 : Blo 1084620 1546067 := bstep (se 1 (by rfl) ⟨1159550, by rfl⟩ : syracuseStep 1546067 = 2319101) B2319101
theorem B1087315 : Blo 1084620 1087315 := bstep (se 1 (by rfl) ⟨815486, by rfl⟩ : syracuseStep 1087315 = 1630973) B1630973
theorem B1087331 : Blo 1084620 1087331 := bstep (se 1 (by rfl) ⟨815498, by rfl⟩ : syracuseStep 1087331 = 1630997) B1630997
theorem B1087347 : Blo 1084620 1087347 := bstep (se 1 (by rfl) ⟨815510, by rfl⟩ : syracuseStep 1087347 = 1631021) B1631021
theorem B1087363 : Blo 1084620 1087363 := bstep (se 1 (by rfl) ⟨815522, by rfl⟩ : syracuseStep 1087363 = 1631045) B1631045
theorem B1087379 : Blo 1084620 1087379 := bstep (se 1 (by rfl) ⟨815534, by rfl⟩ : syracuseStep 1087379 = 1631069) B1631069
theorem B1087395 : Blo 1084620 1087395 := bstep (se 1 (by rfl) ⟨815546, by rfl⟩ : syracuseStep 1087395 = 1631093) B1631093
theorem B1087411 : Blo 1084620 1087411 := bstep (se 1 (by rfl) ⟨815558, by rfl⟩ : syracuseStep 1087411 = 1631117) B1631117
theorem B1087427 : Blo 1084620 1087427 := bstep (se 1 (by rfl) ⟨815570, by rfl⟩ : syracuseStep 1087427 = 1631141) B1631141
theorem B8820677 : Blo 1084620 8820677 := bstep (se 4 (by rfl) ⟨826938, by rfl⟩ : syracuseStep 8820677 = 1653877) B1653877
theorem B1087443 : Blo 1084620 1087443 := bstep (se 1 (by rfl) ⟨815582, by rfl⟩ : syracuseStep 1087443 = 1631165) B1631165
theorem B1087459 : Blo 1084620 1087459 := bstep (se 1 (by rfl) ⟨815594, by rfl⟩ : syracuseStep 1087459 = 1631189) B1631189
theorem B1087475 : Blo 1084620 1087475 := bstep (se 1 (by rfl) ⟨815606, by rfl⟩ : syracuseStep 1087475 = 1631213) B1631213
theorem B1087491 : Blo 1084620 1087491 := bstep (se 1 (by rfl) ⟨815618, by rfl⟩ : syracuseStep 1087491 = 1631237) B1631237
theorem B5871629 : Blo 1084620 5871629 := bstep (se 3 (by rfl) ⟨1100930, by rfl⟩ : syracuseStep 5871629 = 2201861) B2201861
theorem B1087507 : Blo 1084620 1087507 := bstep (se 1 (by rfl) ⟨815630, by rfl⟩ : syracuseStep 1087507 = 1631261) B1631261
theorem B1087523 : Blo 1084620 1087523 := bstep (se 1 (by rfl) ⟨815642, by rfl⟩ : syracuseStep 1087523 = 1631285) B1631285
theorem B1087539 : Blo 1084620 1087539 := bstep (se 1 (by rfl) ⟨815654, by rfl⟩ : syracuseStep 1087539 = 1631309) B1631309
theorem B1087555 : Blo 1084620 1087555 := bstep (se 1 (by rfl) ⟨815666, by rfl⟩ : syracuseStep 1087555 = 1631333) B1631333
theorem B1087571 : Blo 1084620 1087571 := bstep (se 1 (by rfl) ⟨815678, by rfl⟩ : syracuseStep 1087571 = 1631357) B1631357
theorem B1087587 : Blo 1084620 1087587 := bstep (se 1 (by rfl) ⟨815690, by rfl⟩ : syracuseStep 1087587 = 1631381) B1631381
theorem B1087603 : Blo 1084620 1087603 := bstep (se 1 (by rfl) ⟨815702, by rfl⟩ : syracuseStep 1087603 = 1631405) B1631405
theorem B1087619 : Blo 1084620 1087619 := bstep (se 1 (by rfl) ⟨815714, by rfl⟩ : syracuseStep 1087619 = 1631429) B1631429
theorem B1087635 : Blo 1084620 1087635 := bstep (se 1 (by rfl) ⟨815726, by rfl⟩ : syracuseStep 1087635 = 1631453) B1631453
theorem B1087651 : Blo 1084620 1087651 := bstep (se 1 (by rfl) ⟨815738, by rfl⟩ : syracuseStep 1087651 = 1631477) B1631477
theorem B1087667 : Blo 1084620 1087667 := bstep (se 1 (by rfl) ⟨815750, by rfl⟩ : syracuseStep 1087667 = 1631501) B1631501
theorem B1087683 : Blo 1084620 1087683 := bstep (se 1 (by rfl) ⟨815762, by rfl⟩ : syracuseStep 1087683 = 1631525) B1631525
theorem B1087699 : Blo 1084620 1087699 := bstep (se 1 (by rfl) ⟨815774, by rfl⟩ : syracuseStep 1087699 = 1631549) B1631549
theorem B1087715 : Blo 1084620 1087715 := bstep (se 1 (by rfl) ⟨815786, by rfl⟩ : syracuseStep 1087715 = 1631573) B1631573
theorem B1087731 : Blo 1084620 1087731 := bstep (se 1 (by rfl) ⟨815798, by rfl⟩ : syracuseStep 1087731 = 1631597) B1631597
theorem B1087747 : Blo 1084620 1087747 := bstep (se 1 (by rfl) ⟨815810, by rfl⟩ : syracuseStep 1087747 = 1631621) B1631621
theorem B1087763 : Blo 1084620 1087763 := bstep (se 1 (by rfl) ⟨815822, by rfl⟩ : syracuseStep 1087763 = 1631645) B1631645
theorem B1087779 : Blo 1084620 1087779 := bstep (se 1 (by rfl) ⟨815834, by rfl⟩ : syracuseStep 1087779 = 1631669) B1631669
theorem B1087795 : Blo 1084620 1087795 := bstep (se 1 (by rfl) ⟨815846, by rfl⟩ : syracuseStep 1087795 = 1631693) B1631693
theorem B1087811 : Blo 1084620 1087811 := bstep (se 1 (by rfl) ⟨815858, by rfl⟩ : syracuseStep 1087811 = 1631717) B1631717
theorem B1087827 : Blo 1084620 1087827 := bstep (se 1 (by rfl) ⟨815870, by rfl⟩ : syracuseStep 1087827 = 1631741) B1631741
theorem B1087843 : Blo 1084620 1087843 := bstep (se 1 (by rfl) ⟨815882, by rfl⟩ : syracuseStep 1087843 = 1631765) B1631765
theorem B1087859 : Blo 1084620 1087859 := bstep (se 1 (by rfl) ⟨815894, by rfl⟩ : syracuseStep 1087859 = 1631789) B1631789
theorem B1087875 : Blo 1084620 1087875 := bstep (se 1 (by rfl) ⟨815906, by rfl⟩ : syracuseStep 1087875 = 1631813) B1631813
theorem B1087891 : Blo 1084620 1087891 := bstep (se 1 (by rfl) ⟨815918, by rfl⟩ : syracuseStep 1087891 = 1631837) B1631837
theorem B1087907 : Blo 1084620 1087907 := bstep (se 1 (by rfl) ⟨815930, by rfl⟩ : syracuseStep 1087907 = 1631861) B1631861
theorem B1087923 : Blo 1084620 1087923 := bstep (se 1 (by rfl) ⟨815942, by rfl⟩ : syracuseStep 1087923 = 1631885) B1631885
theorem B1087939 : Blo 1084620 1087939 := bstep (se 1 (by rfl) ⟨815954, by rfl⟩ : syracuseStep 1087939 = 1631909) B1631909
theorem B1546705 : Blo 1084620 1546705 := bstep (se 2 (by rfl) ⟨580014, by rfl⟩ : syracuseStep 1546705 = 1160029) B1160029
theorem B1087955 : Blo 1084620 1087955 := bstep (se 1 (by rfl) ⟨815966, by rfl⟩ : syracuseStep 1087955 = 1631933) B1631933
theorem B1087971 : Blo 1084620 1087971 := bstep (se 1 (by rfl) ⟨815978, by rfl⟩ : syracuseStep 1087971 = 1631957) B1631957
theorem B1087987 : Blo 1084620 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B1088003 : Blo 1084620 1088003 := bstep (se 1 (by rfl) ⟨816002, by rfl⟩ : syracuseStep 1088003 = 1632005) B1632005
theorem B1088019 : Blo 1084620 1088019 := bstep (se 1 (by rfl) ⟨816014, by rfl⟩ : syracuseStep 1088019 = 1632029) B1632029
theorem B1088035 : Blo 1084620 1088035 := bstep (se 1 (by rfl) ⟨816026, by rfl⟩ : syracuseStep 1088035 = 1632053) B1632053
theorem B1088051 : Blo 1084620 1088051 := bstep (se 1 (by rfl) ⟨816038, by rfl⟩ : syracuseStep 1088051 = 1632077) B1632077
theorem B1088067 : Blo 1084620 1088067 := bstep (se 1 (by rfl) ⟨816050, by rfl⟩ : syracuseStep 1088067 = 1632101) B1632101
theorem B1088083 : Blo 1084620 1088083 := bstep (se 1 (by rfl) ⟨816062, by rfl⟩ : syracuseStep 1088083 = 1632125) B1632125
theorem B1088099 : Blo 1084620 1088099 := bstep (se 1 (by rfl) ⟨816074, by rfl⟩ : syracuseStep 1088099 = 1632149) B1632149
theorem B1088115 : Blo 1084620 1088115 := bstep (se 1 (by rfl) ⟨816086, by rfl⟩ : syracuseStep 1088115 = 1632173) B1632173
theorem B1088131 : Blo 1084620 1088131 := bstep (se 1 (by rfl) ⟨816098, by rfl⟩ : syracuseStep 1088131 = 1632197) B1632197
theorem B25107085 : Blo 1084620 25107085 := bstep (se 3 (by rfl) ⟨4707578, by rfl⟩ : syracuseStep 25107085 = 9415157) B9415157
theorem B1088147 : Blo 1084620 1088147 := bstep (se 1 (by rfl) ⟨816110, by rfl⟩ : syracuseStep 1088147 = 1632221) B1632221
theorem B1088163 : Blo 1084620 1088163 := bstep (se 1 (by rfl) ⟨816122, by rfl⟩ : syracuseStep 1088163 = 1632245) B1632245
theorem B1088179 : Blo 1084620 1088179 := bstep (se 1 (by rfl) ⟨816134, by rfl⟩ : syracuseStep 1088179 = 1632269) B1632269
theorem B1088195 : Blo 1084620 1088195 := bstep (se 1 (by rfl) ⟨816146, by rfl⟩ : syracuseStep 1088195 = 1632293) B1632293
theorem B1088211 : Blo 1084620 1088211 := bstep (se 1 (by rfl) ⟨816158, by rfl⟩ : syracuseStep 1088211 = 1632317) B1632317
theorem B1088227 : Blo 1084620 1088227 := bstep (se 1 (by rfl) ⟨816170, by rfl⟩ : syracuseStep 1088227 = 1632341) B1632341
theorem B1088243 : Blo 1084620 1088243 := bstep (se 1 (by rfl) ⟨816182, by rfl⟩ : syracuseStep 1088243 = 1632365) B1632365
theorem B1088259 : Blo 1084620 1088259 := bstep (se 1 (by rfl) ⟨816194, by rfl⟩ : syracuseStep 1088259 = 1632389) B1632389
theorem B1088275 : Blo 1084620 1088275 := bstep (se 1 (by rfl) ⟨816206, by rfl⟩ : syracuseStep 1088275 = 1632413) B1632413
theorem B1547041 : Blo 1084620 1547041 := bstep (se 2 (by rfl) ⟨580140, by rfl⟩ : syracuseStep 1547041 = 1160281) B1160281
theorem B1088291 : Blo 1084620 1088291 := bstep (se 1 (by rfl) ⟨816218, by rfl⟩ : syracuseStep 1088291 = 1632437) B1632437
theorem B1088307 : Blo 1084620 1088307 := bstep (se 1 (by rfl) ⟨816230, by rfl⟩ : syracuseStep 1088307 = 1632461) B1632461
theorem B1088323 : Blo 1084620 1088323 := bstep (se 1 (by rfl) ⟨816242, by rfl⟩ : syracuseStep 1088323 = 1632485) B1632485
theorem B3971917 : Blo 1084620 3971917 := bstep (se 3 (by rfl) ⟨744734, by rfl⟩ : syracuseStep 3971917 = 1489469) B1489469
theorem B1088339 : Blo 1084620 1088339 := bstep (se 1 (by rfl) ⟨816254, by rfl⟩ : syracuseStep 1088339 = 1632509) B1632509
theorem B1088355 : Blo 1084620 1088355 := bstep (se 1 (by rfl) ⟨816266, by rfl⟩ : syracuseStep 1088355 = 1632533) B1632533
theorem B1088371 : Blo 1084620 1088371 := bstep (se 1 (by rfl) ⟨816278, by rfl⟩ : syracuseStep 1088371 = 1632557) B1632557
theorem B1088387 : Blo 1084620 1088387 := bstep (se 1 (by rfl) ⟨816290, by rfl⟩ : syracuseStep 1088387 = 1632581) B1632581
theorem B1088403 : Blo 1084620 1088403 := bstep (se 1 (by rfl) ⟨816302, by rfl⟩ : syracuseStep 1088403 = 1632605) B1632605
theorem B1088419 : Blo 1084620 1088419 := bstep (se 1 (by rfl) ⟨816314, by rfl⟩ : syracuseStep 1088419 = 1632629) B1632629
theorem B1088435 : Blo 1084620 1088435 := bstep (se 1 (by rfl) ⟨816326, by rfl⟩ : syracuseStep 1088435 = 1632653) B1632653
theorem B1088451 : Blo 1084620 1088451 := bstep (se 1 (by rfl) ⟨816338, by rfl⟩ : syracuseStep 1088451 = 1632677) B1632677
theorem B1088467 : Blo 1084620 1088467 := bstep (se 1 (by rfl) ⟨816350, by rfl⟩ : syracuseStep 1088467 = 1632701) B1632701
theorem B1088483 : Blo 1084620 1088483 := bstep (se 1 (by rfl) ⟨816362, by rfl⟩ : syracuseStep 1088483 = 1632725) B1632725
theorem B1088499 : Blo 1084620 1088499 := bstep (se 1 (by rfl) ⟨816374, by rfl⟩ : syracuseStep 1088499 = 1632749) B1632749
theorem B1088515 : Blo 1084620 1088515 := bstep (se 1 (by rfl) ⟨816386, by rfl⟩ : syracuseStep 1088515 = 1632773) B1632773
theorem B1088531 : Blo 1084620 1088531 := bstep (se 1 (by rfl) ⟨816398, by rfl⟩ : syracuseStep 1088531 = 1632797) B1632797
theorem B1088547 : Blo 1084620 1088547 := bstep (se 1 (by rfl) ⟨816410, by rfl⟩ : syracuseStep 1088547 = 1632821) B1632821
theorem B1088563 : Blo 1084620 1088563 := bstep (se 1 (by rfl) ⟨816422, by rfl⟩ : syracuseStep 1088563 = 1632845) B1632845
theorem B1088579 : Blo 1084620 1088579 := bstep (se 1 (by rfl) ⟨816434, by rfl⟩ : syracuseStep 1088579 = 1632869) B1632869
theorem B1088595 : Blo 1084620 1088595 := bstep (se 1 (by rfl) ⟨816446, by rfl⟩ : syracuseStep 1088595 = 1632893) B1632893
theorem B1088611 : Blo 1084620 1088611 := bstep (se 1 (by rfl) ⟨816458, by rfl⟩ : syracuseStep 1088611 = 1632917) B1632917
theorem B1547633 : Blo 1084620 1547633 := bstep (se 2 (by rfl) ⟨580362, by rfl⟩ : syracuseStep 1547633 = 1160725) B1160725
theorem B57187781 : Blo 1084620 57187781 := bstep (se 4 (by rfl) ⟨5361354, by rfl⟩ : syracuseStep 57187781 = 10722709) B10722709
theorem B1220323 : Blo 1084620 1220323 := bstep (se 1 (by rfl) ⟨915242, by rfl⟩ : syracuseStep 1220323 = 1830485) B1830485
theorem B1220467 : Blo 1084620 1220467 := bstep (se 1 (by rfl) ⟨915350, by rfl⟩ : syracuseStep 1220467 = 1830701) B1830701
theorem B1548163 : Blo 1084620 1548163 := bstep (se 1 (by rfl) ⟨1161122, by rfl⟩ : syracuseStep 1548163 = 2322245) B2322245
theorem B1220611 : Blo 1084620 1220611 := bstep (se 1 (by rfl) ⟨915458, by rfl⟩ : syracuseStep 1220611 = 1830917) B1830917
theorem B1220755 : Blo 1084620 1220755 := bstep (se 1 (by rfl) ⟨915566, by rfl⟩ : syracuseStep 1220755 = 1831133) B1831133
theorem B1548499 : Blo 1084620 1548499 := bstep (se 1 (by rfl) ⟨1161374, by rfl⟩ : syracuseStep 1548499 = 2322749) B2322749
theorem B3481841 : Blo 1084620 3481841 := bstep (se 2 (by rfl) ⟨1305690, by rfl⟩ : syracuseStep 3481841 = 2611381) B2611381
theorem B1220899 : Blo 1084620 1220899 := bstep (se 1 (by rfl) ⟨915674, by rfl⟩ : syracuseStep 1220899 = 1831349) B1831349
theorem B2204003 : Blo 1084620 2204003 := bstep (se 1 (by rfl) ⟨1653002, by rfl⟩ : syracuseStep 2204003 = 3306005) B3306005
theorem B1221043 : Blo 1084620 1221043 := bstep (se 1 (by rfl) ⟨915782, by rfl⟩ : syracuseStep 1221043 = 1831565) B1831565
theorem B1221187 : Blo 1084620 1221187 := bstep (se 1 (by rfl) ⟨915890, by rfl⟩ : syracuseStep 1221187 = 1831781) B1831781
theorem B12362381 : Blo 1084620 12362381 := bstep (se 3 (by rfl) ⟨2317946, by rfl⟩ : syracuseStep 12362381 = 4635893) B4635893
theorem B1221331 : Blo 1084620 1221331 := bstep (se 1 (by rfl) ⟨915998, by rfl⟩ : syracuseStep 1221331 = 1831997) B1831997
theorem B1549057 : Blo 1084620 1549057 := bstep (se 2 (by rfl) ⟨580896, by rfl⟩ : syracuseStep 1549057 = 1161793) B1161793
theorem B1549091 : Blo 1084620 1549091 := bstep (se 1 (by rfl) ⟨1161818, by rfl⟩ : syracuseStep 1549091 = 2323637) B2323637
theorem B1221475 : Blo 1084620 1221475 := bstep (se 1 (by rfl) ⟨916106, by rfl⟩ : syracuseStep 1221475 = 1832213) B1832213
theorem B1221619 : Blo 1084620 1221619 := bstep (se 1 (by rfl) ⟨916214, by rfl⟩ : syracuseStep 1221619 = 1832429) B1832429
theorem B3089411 : Blo 1084620 3089411 := bstep (se 1 (by rfl) ⟨2317058, by rfl⟩ : syracuseStep 3089411 = 4634117) B4634117
theorem B1221763 : Blo 1084620 1221763 := bstep (se 1 (by rfl) ⟨916322, by rfl⟩ : syracuseStep 1221763 = 1832645) B1832645
theorem B1221907 : Blo 1084620 1221907 := bstep (se 1 (by rfl) ⟨916430, by rfl⟩ : syracuseStep 1221907 = 1832861) B1832861
theorem B1549649 : Blo 1084620 1549649 := bstep (se 2 (by rfl) ⟨581118, by rfl⟩ : syracuseStep 1549649 = 1162237) B1162237
theorem B3712387 : Blo 1084620 3712387 := bstep (se 1 (by rfl) ⟨2784290, by rfl⟩ : syracuseStep 3712387 = 5568581) B5568581
theorem B2205073 : Blo 1084620 2205073 := bstep (se 2 (by rfl) ⟨826902, by rfl⟩ : syracuseStep 2205073 = 1653805) B1653805
theorem B1549729 : Blo 1084620 1549729 := bstep (se 2 (by rfl) ⟨581148, by rfl⟩ : syracuseStep 1549729 = 1162297) B1162297
theorem B1222051 : Blo 1084620 1222051 := bstep (se 1 (by rfl) ⟨916538, by rfl⟩ : syracuseStep 1222051 = 1833077) B1833077
theorem B2205137 : Blo 1084620 2205137 := bstep (se 2 (by rfl) ⟨826926, by rfl⟩ : syracuseStep 2205137 = 1653853) B1653853
theorem B3581453 : Blo 1084620 3581453 := bstep (se 3 (by rfl) ⟨671522, by rfl⟩ : syracuseStep 3581453 = 1343045) B1343045
theorem B1222195 : Blo 1084620 1222195 := bstep (se 1 (by rfl) ⟨916646, by rfl⟩ : syracuseStep 1222195 = 1833293) B1833293
theorem B1222339 : Blo 1084620 1222339 := bstep (se 1 (by rfl) ⟨916754, by rfl⟩ : syracuseStep 1222339 = 1833509) B1833509
theorem B3090221 : Blo 1084620 3090221 := bstep (se 3 (by rfl) ⟨579416, by rfl⟩ : syracuseStep 3090221 = 1158833) B1158833
theorem B1222483 : Blo 1084620 1222483 := bstep (se 1 (by rfl) ⟨916862, by rfl⟩ : syracuseStep 1222483 = 1833725) B1833725
theorem B5220301 : Blo 1084620 5220301 := bstep (se 3 (by rfl) ⟨978806, by rfl⟩ : syracuseStep 5220301 = 1957613) B1957613
theorem B1222627 : Blo 1084620 1222627 := bstep (se 1 (by rfl) ⟨916970, by rfl⟩ : syracuseStep 1222627 = 1833941) B1833941
theorem B3090413 : Blo 1084620 3090413 := bstep (se 3 (by rfl) ⟨579452, by rfl⟩ : syracuseStep 3090413 = 1158905) B1158905
theorem B1222771 : Blo 1084620 1222771 := bstep (se 1 (by rfl) ⟨917078, by rfl⟩ : syracuseStep 1222771 = 1834157) B1834157
theorem B1222915 : Blo 1084620 1222915 := bstep (se 1 (by rfl) ⟨917186, by rfl⟩ : syracuseStep 1222915 = 1834373) B1834373
theorem B1223059 : Blo 1084620 1223059 := bstep (se 1 (by rfl) ⟨917294, by rfl⟩ : syracuseStep 1223059 = 1834589) B1834589
theorem B1223203 : Blo 1084620 1223203 := bstep (se 1 (by rfl) ⟨917402, by rfl⟩ : syracuseStep 1223203 = 1834805) B1834805
theorem B31369781 : Blo 1084620 31369781 := bstep (se 5 (by rfl) ⟨1470458, by rfl⟩ : syracuseStep 31369781 = 2940917) B2940917
theorem B3484301 : Blo 1084620 3484301 := bstep (se 3 (by rfl) ⟨653306, by rfl⟩ : syracuseStep 3484301 = 1306613) B1306613
theorem B1223347 : Blo 1084620 1223347 := bstep (se 1 (by rfl) ⟨917510, by rfl⟩ : syracuseStep 1223347 = 1835021) B1835021
theorem B1223491 : Blo 1084620 1223491 := bstep (se 1 (by rfl) ⟨917618, by rfl⟩ : syracuseStep 1223491 = 1835237) B1835237
theorem B3091405 : Blo 1084620 3091405 := bstep (se 3 (by rfl) ⟨579638, by rfl⟩ : syracuseStep 3091405 = 1159277) B1159277
theorem B1223635 : Blo 1084620 1223635 := bstep (se 1 (by rfl) ⟨917726, by rfl⟩ : syracuseStep 1223635 = 1835453) B1835453
theorem B5221361 : Blo 1084620 5221361 := bstep (se 2 (by rfl) ⟨1958010, by rfl⟩ : syracuseStep 5221361 = 3916021) B3916021
theorem B1223779 : Blo 1084620 1223779 := bstep (se 1 (by rfl) ⟨917834, by rfl⟩ : syracuseStep 1223779 = 1835669) B1835669
theorem B1223923 : Blo 1084620 1223923 := bstep (se 1 (by rfl) ⟨917942, by rfl⟩ : syracuseStep 1223923 = 1835885) B1835885
theorem B1224067 : Blo 1084620 1224067 := bstep (se 1 (by rfl) ⟨918050, by rfl⟩ : syracuseStep 1224067 = 1836101) B1836101
theorem B12365297 : Blo 1084620 12365297 := bstep (se 2 (by rfl) ⟨4636986, by rfl⟩ : syracuseStep 12365297 = 9273973) B9273973
theorem B1224211 : Blo 1084620 1224211 := bstep (se 1 (by rfl) ⟨918158, by rfl⟩ : syracuseStep 1224211 = 1836317) B1836317
theorem B1224355 : Blo 1084620 1224355 := bstep (se 1 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 1224355 = 1836533) B1836533
theorem B1224499 : Blo 1084620 1224499 := bstep (se 1 (by rfl) ⟨918374, by rfl⟩ : syracuseStep 1224499 = 1836749) B1836749
theorem B1650545 : Blo 1084620 1650545 := bstep (se 2 (by rfl) ⟨618954, by rfl⟩ : syracuseStep 1650545 = 1237909) B1237909
theorem B1224643 : Blo 1084620 1224643 := bstep (se 1 (by rfl) ⟨918482, by rfl⟩ : syracuseStep 1224643 = 1836965) B1836965
theorem B2830403 : Blo 1084620 2830403 := bstep (se 1 (by rfl) ⟨2122802, by rfl⟩ : syracuseStep 2830403 = 4245605) B4245605
theorem B1159315 : Blo 1084620 1159315 := bstep (se 1 (by rfl) ⟨869486, by rfl⟩ : syracuseStep 1159315 = 1738973) B1738973
theorem B3485891 : Blo 1084620 3485891 := bstep (se 1 (by rfl) ⟨2614418, by rfl⟩ : syracuseStep 3485891 = 5228837) B5228837
theorem B6959429 : Blo 1084620 6959429 := bstep (se 4 (by rfl) ⟨652446, by rfl⟩ : syracuseStep 6959429 = 1304893) B1304893
theorem B3912113 : Blo 1084620 3912113 := bstep (se 2 (by rfl) ⟨1467042, by rfl⟩ : syracuseStep 3912113 = 2934085) B2934085
theorem B13906403 : Blo 1084620 13906403 := bstep (se 1 (by rfl) ⟨10429802, by rfl⟩ : syracuseStep 13906403 = 20859605) B20859605
theorem B3093137 : Blo 1084620 3093137 := bstep (se 2 (by rfl) ⟨1159926, by rfl⟩ : syracuseStep 3093137 = 2319853) B2319853
theorem B3093329 : Blo 1084620 3093329 := bstep (se 2 (by rfl) ⟨1159998, by rfl⟩ : syracuseStep 3093329 = 2319997) B2319997
theorem B1651585 : Blo 1084620 1651585 := bstep (se 2 (by rfl) ⟨619344, by rfl⟩ : syracuseStep 1651585 = 1238689) B1238689
theorem B6599843 : Blo 1084620 6599843 := bstep (se 1 (by rfl) ⟨4949882, by rfl⟩ : syracuseStep 6599843 = 9899765) B9899765
theorem B3487121 : Blo 1084620 3487121 := bstep (se 2 (by rfl) ⟨1307670, by rfl⟩ : syracuseStep 3487121 = 2615341) B2615341
theorem B1652321 : Blo 1084620 1652321 := bstep (se 2 (by rfl) ⟨619620, by rfl⟩ : syracuseStep 1652321 = 1239241) B1239241
theorem B3094321 : Blo 1084620 3094321 := bstep (se 2 (by rfl) ⟨1160370, by rfl⟩ : syracuseStep 3094321 = 2320741) B2320741
theorem B3094595 : Blo 1084620 3094595 := bstep (se 1 (by rfl) ⟨2320946, by rfl⟩ : syracuseStep 3094595 = 4641893) B4641893
theorem B5093489 : Blo 1084620 5093489 := bstep (se 2 (by rfl) ⟨1910058, by rfl⟩ : syracuseStep 5093489 = 3820117) B3820117
theorem B3094787 : Blo 1084620 3094787 := bstep (se 1 (by rfl) ⟨2321090, by rfl⟩ : syracuseStep 3094787 = 4642181) B4642181
theorem B4700429 : Blo 1084620 4700429 := bstep (se 3 (by rfl) ⟨881330, by rfl⟩ : syracuseStep 4700429 = 1762661) B1762661
theorem B5880433 : Blo 1084620 5880433 := bstep (se 2 (by rfl) ⟨2205162, by rfl⟩ : syracuseStep 5880433 = 4410325) B4410325
theorem B1161955 : Blo 1084620 1161955 := bstep (se 1 (by rfl) ⟨871466, by rfl⟩ : syracuseStep 1161955 = 1742933) B1742933
theorem B3095597 : Blo 1084620 3095597 := bstep (se 3 (by rfl) ⟨580424, by rfl⟩ : syracuseStep 3095597 = 1160849) B1160849
theorem B1162387 : Blo 1084620 1162387 := bstep (se 1 (by rfl) ⟨871790, by rfl⟩ : syracuseStep 1162387 = 1743581) B1743581
theorem B3095779 : Blo 1084620 3095779 := bstep (se 1 (by rfl) ⟨2321834, by rfl⟩ : syracuseStep 3095779 = 4643669) B4643669
theorem B5946659 : Blo 1084620 5946659 := bstep (se 1 (by rfl) ⟨4459994, by rfl⟩ : syracuseStep 5946659 = 8919989) B8919989
theorem B2440529 : Blo 1084620 2440529 := bstep (se 2 (by rfl) ⟨915198, by rfl⟩ : syracuseStep 2440529 = 1830397) B1830397
theorem B2440547 : Blo 1084620 2440547 := bstep (se 1 (by rfl) ⟨1830410, by rfl⟩ : syracuseStep 2440547 = 3660821) B3660821
theorem B2440817 : Blo 1084620 2440817 := bstep (se 2 (by rfl) ⟨915306, by rfl⟩ : syracuseStep 2440817 = 1830613) B1830613
theorem B2440835 : Blo 1084620 2440835 := bstep (se 1 (by rfl) ⟨1830626, by rfl⟩ : syracuseStep 2440835 = 3661253) B3661253
theorem B2932355 : Blo 1084620 2932355 := bstep (se 1 (by rfl) ⟨2199266, by rfl⟩ : syracuseStep 2932355 = 4398533) B4398533
theorem B3096269 : Blo 1084620 3096269 := bstep (se 3 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 3096269 = 1161101) B1161101
theorem B1490737 : Blo 1084620 1490737 := bstep (se 2 (by rfl) ⟨559026, by rfl⟩ : syracuseStep 1490737 = 1118053) B1118053
theorem B6963043 : Blo 1084620 6963043 := bstep (se 1 (by rfl) ⟨5222282, by rfl⟩ : syracuseStep 6963043 = 10444565) B10444565
theorem B2441105 : Blo 1084620 2441105 := bstep (se 2 (by rfl) ⟨915414, by rfl⟩ : syracuseStep 2441105 = 1830829) B1830829
theorem B2441123 : Blo 1084620 2441123 := bstep (se 1 (by rfl) ⟨1830842, by rfl⟩ : syracuseStep 2441123 = 3661685) B3661685
theorem B1654705 : Blo 1084620 1654705 := bstep (se 2 (by rfl) ⟨620514, by rfl⟩ : syracuseStep 1654705 = 1241029) B1241029
theorem B4636835 : Blo 1084620 4636835 := bstep (se 1 (by rfl) ⟨3477626, by rfl⟩ : syracuseStep 4636835 = 6955253) B6955253
theorem B2441393 : Blo 1084620 2441393 := bstep (se 2 (by rfl) ⟨915522, by rfl⟩ : syracuseStep 2441393 = 1831045) B1831045
theorem B2441411 : Blo 1084620 2441411 := bstep (se 1 (by rfl) ⟨1831058, by rfl⟩ : syracuseStep 2441411 = 3662117) B3662117
theorem B6602957 : Blo 1084620 6602957 := bstep (se 3 (by rfl) ⟨1238054, by rfl⟩ : syracuseStep 6602957 = 2476109) B2476109
theorem B2441681 : Blo 1084620 2441681 := bstep (se 2 (by rfl) ⟨915630, by rfl⟩ : syracuseStep 2441681 = 1831261) B1831261
theorem B2441699 : Blo 1084620 2441699 := bstep (se 1 (by rfl) ⟨1831274, by rfl⟩ : syracuseStep 2441699 = 3662549) B3662549
theorem B3719857 : Blo 1084620 3719857 := bstep (se 2 (by rfl) ⟨1394946, by rfl⟩ : syracuseStep 3719857 = 2789893) B2789893
theorem B2441969 : Blo 1084620 2441969 := bstep (se 2 (by rfl) ⟨915738, by rfl⟩ : syracuseStep 2441969 = 1831477) B1831477
theorem B2441987 : Blo 1084620 2441987 := bstep (se 1 (by rfl) ⟨1831490, by rfl⟩ : syracuseStep 2441987 = 3662981) B3662981
theorem B15876917 : Blo 1084620 15876917 := bstep (se 5 (by rfl) ⟨744230, by rfl⟩ : syracuseStep 15876917 = 1488461) B1488461
theorem B3097453 : Blo 1084620 3097453 := bstep (se 3 (by rfl) ⟨580772, by rfl⟩ : syracuseStep 3097453 = 1161545) B1161545
theorem B2442257 : Blo 1084620 2442257 := bstep (se 2 (by rfl) ⟨915846, by rfl⟩ : syracuseStep 2442257 = 1831693) B1831693
theorem B2442275 : Blo 1084620 2442275 := bstep (se 1 (by rfl) ⟨1831706, by rfl⟩ : syracuseStep 2442275 = 3663413) B3663413
theorem B2442545 : Blo 1084620 2442545 := bstep (se 2 (by rfl) ⟨915954, by rfl⟩ : syracuseStep 2442545 = 1831909) B1831909
theorem B2442563 : Blo 1084620 2442563 := bstep (se 1 (by rfl) ⟨1831922, by rfl⟩ : syracuseStep 2442563 = 3663845) B3663845
theorem B5096881 : Blo 1084620 5096881 := bstep (se 2 (by rfl) ⟨1911330, by rfl⟩ : syracuseStep 5096881 = 3822661) B3822661
theorem B2442833 : Blo 1084620 2442833 := bstep (se 2 (by rfl) ⟨916062, by rfl⟩ : syracuseStep 2442833 = 1832125) B1832125
theorem B2442851 : Blo 1084620 2442851 := bstep (se 1 (by rfl) ⟨1832138, by rfl⟩ : syracuseStep 2442851 = 3664277) B3664277
theorem B2934605 : Blo 1084620 2934605 := bstep (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) B1100477
theorem B2443121 : Blo 1084620 2443121 := bstep (se 2 (by rfl) ⟨916170, by rfl⟩ : syracuseStep 2443121 = 1832341) B1832341
theorem B2443139 : Blo 1084620 2443139 := bstep (se 1 (by rfl) ⟨1832354, by rfl⟩ : syracuseStep 2443139 = 3664709) B3664709
theorem B3098513 : Blo 1084620 3098513 := bstep (se 2 (by rfl) ⟨1161942, by rfl⟩ : syracuseStep 3098513 = 2323885) B2323885
theorem B4638833 : Blo 1084620 4638833 := bstep (se 2 (by rfl) ⟨1739562, by rfl⟩ : syracuseStep 4638833 = 3479125) B3479125
theorem B2443409 : Blo 1084620 2443409 := bstep (se 2 (by rfl) ⟨916278, by rfl⟩ : syracuseStep 2443409 = 1832557) B1832557
theorem B2443427 : Blo 1084620 2443427 := bstep (se 1 (by rfl) ⟨1832570, by rfl⟩ : syracuseStep 2443427 = 3665141) B3665141
theorem B1395091 : Blo 1084620 1395091 := bstep (se 1 (by rfl) ⟨1046318, by rfl⟩ : syracuseStep 1395091 = 2092637) B2092637
theorem B2443697 : Blo 1084620 2443697 := bstep (se 2 (by rfl) ⟨916386, by rfl⟩ : syracuseStep 2443697 = 1832773) B1832773
theorem B2443715 : Blo 1084620 2443715 := bstep (se 1 (by rfl) ⟨1832786, by rfl⟩ : syracuseStep 2443715 = 3665573) B3665573
theorem B13420997 : Blo 1084620 13420997 := bstep (se 4 (by rfl) ⟨1258218, by rfl⟩ : syracuseStep 13420997 = 2516437) B2516437
theorem B9423373 : Blo 1084620 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B1100323 : Blo 1084620 1100323 := bstep (se 1 (by rfl) ⟨825242, by rfl⟩ : syracuseStep 1100323 = 1650485) B1650485
theorem B3099185 : Blo 1084620 3099185 := bstep (se 2 (by rfl) ⟨1162194, by rfl⟩ : syracuseStep 3099185 = 2324389) B2324389
theorem B6965837 : Blo 1084620 6965837 := bstep (se 3 (by rfl) ⟨1306094, by rfl⟩ : syracuseStep 6965837 = 2612189) B2612189
theorem B5491313 : Blo 1084620 5491313 := bstep (se 2 (by rfl) ⟨2059242, by rfl⟩ : syracuseStep 5491313 = 4118485) B4118485
theorem B2476675 : Blo 1084620 2476675 := bstep (se 1 (by rfl) ⟨1857506, by rfl⟩ : syracuseStep 2476675 = 3715013) B3715013
theorem B2443985 : Blo 1084620 2443985 := bstep (se 2 (by rfl) ⟨916494, by rfl⟩ : syracuseStep 2443985 = 1832989) B1832989
theorem B2444003 : Blo 1084620 2444003 := bstep (se 1 (by rfl) ⟨1833002, by rfl⟩ : syracuseStep 2444003 = 3666005) B3666005
theorem B6179597 : Blo 1084620 6179597 := bstep (se 3 (by rfl) ⟨1158674, by rfl⟩ : syracuseStep 6179597 = 2317349) B2317349
theorem B2444273 : Blo 1084620 2444273 := bstep (se 2 (by rfl) ⟨916602, by rfl⟩ : syracuseStep 2444273 = 1833205) B1833205
theorem B2444291 : Blo 1084620 2444291 := bstep (se 1 (by rfl) ⟨1833218, by rfl⟩ : syracuseStep 2444291 = 3666437) B3666437
theorem B1100963 : Blo 1084620 1100963 := bstep (se 1 (by rfl) ⟨825722, by rfl⟩ : syracuseStep 1100963 = 1651445) B1651445
theorem B1789171 : Blo 1084620 1789171 := bstep (se 1 (by rfl) ⟨1341878, by rfl⟩ : syracuseStep 1789171 = 2683757) B2683757
theorem B2444561 : Blo 1084620 2444561 := bstep (se 2 (by rfl) ⟨916710, by rfl⟩ : syracuseStep 2444561 = 1833421) B1833421
theorem B2444579 : Blo 1084620 2444579 := bstep (se 1 (by rfl) ⟨1833434, by rfl⟩ : syracuseStep 2444579 = 3666869) B3666869
theorem B3099971 : Blo 1084620 3099971 := bstep (se 1 (by rfl) ⟨2324978, by rfl⟩ : syracuseStep 3099971 = 4649957) B4649957
theorem B2444849 : Blo 1084620 2444849 := bstep (se 2 (by rfl) ⟨916818, by rfl⟩ : syracuseStep 2444849 = 1833637) B1833637
theorem B2444867 : Blo 1084620 2444867 := bstep (se 1 (by rfl) ⟨1833650, by rfl⟩ : syracuseStep 2444867 = 3667301) B3667301
theorem B9293453 : Blo 1084620 9293453 := bstep (se 3 (by rfl) ⟨1742522, by rfl⟩ : syracuseStep 9293453 = 3485045) B3485045
theorem B1101523 : Blo 1084620 1101523 := bstep (se 1 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 1101523 = 1652285) B1652285
theorem B2445137 : Blo 1084620 2445137 := bstep (se 2 (by rfl) ⟨916926, by rfl⟩ : syracuseStep 2445137 = 1833853) B1833853
theorem B2445155 : Blo 1084620 2445155 := bstep (se 1 (by rfl) ⟨1833866, by rfl⟩ : syracuseStep 2445155 = 3667733) B3667733
theorem B6279011 : Blo 1084620 6279011 := bstep (se 1 (by rfl) ⟨4709258, by rfl⟩ : syracuseStep 6279011 = 9418517) B9418517
theorem B4411313 : Blo 1084620 4411313 := bstep (se 2 (by rfl) ⟨1654242, by rfl⟩ : syracuseStep 4411313 = 3308485) B3308485
theorem B5492771 : Blo 1084620 5492771 := bstep (se 1 (by rfl) ⟨4119578, by rfl⟩ : syracuseStep 5492771 = 8239157) B8239157
theorem B2445425 : Blo 1084620 2445425 := bstep (se 2 (by rfl) ⟨917034, by rfl⟩ : syracuseStep 2445425 = 1834069) B1834069
theorem B3919985 : Blo 1084620 3919985 := bstep (se 2 (by rfl) ⟨1469994, by rfl⟩ : syracuseStep 3919985 = 2939989) B2939989
theorem B2445443 : Blo 1084620 2445443 := bstep (se 1 (by rfl) ⟨1834082, by rfl⟩ : syracuseStep 2445443 = 3668165) B3668165
theorem B2609297 : Blo 1084620 2609297 := bstep (se 2 (by rfl) ⟨978486, by rfl⟩ : syracuseStep 2609297 = 1956973) B1956973
theorem B1855715 : Blo 1084620 1855715 := bstep (se 1 (by rfl) ⟨1391786, by rfl⟩ : syracuseStep 1855715 = 2783573) B2783573
theorem B8245475 : Blo 1084620 8245475 := bstep (se 1 (by rfl) ⟨6184106, by rfl⟩ : syracuseStep 8245475 = 12368213) B12368213
theorem B1855795 : Blo 1084620 1855795 := bstep (se 1 (by rfl) ⟨1391846, by rfl⟩ : syracuseStep 1855795 = 2783693) B2783693
theorem B2445713 : Blo 1084620 2445713 := bstep (se 2 (by rfl) ⟨917142, by rfl⟩ : syracuseStep 2445713 = 1834285) B1834285
theorem B2445731 : Blo 1084620 2445731 := bstep (se 1 (by rfl) ⟨1834298, by rfl⟩ : syracuseStep 2445731 = 3668597) B3668597
theorem B4641293 : Blo 1084620 4641293 := bstep (se 3 (by rfl) ⟨870242, by rfl⟩ : syracuseStep 4641293 = 1740485) B1740485
theorem B2446001 : Blo 1084620 2446001 := bstep (se 2 (by rfl) ⟨917250, by rfl⟩ : syracuseStep 2446001 = 1834501) B1834501
theorem B2446019 : Blo 1084620 2446019 := bstep (se 1 (by rfl) ⟨1834514, by rfl⟩ : syracuseStep 2446019 = 3669029) B3669029
theorem B1626947 : Blo 1084620 1626947 := bstep (se 1 (by rfl) ⟨1220210, by rfl⟩ : syracuseStep 1626947 = 2440421) B2440421
theorem B5493581 : Blo 1084620 5493581 := bstep (se 3 (by rfl) ⟨1030046, by rfl⟩ : syracuseStep 5493581 = 2060093) B2060093
theorem B1626977 : Blo 1084620 1626977 := bstep (se 2 (by rfl) ⟨610116, by rfl⟩ : syracuseStep 1626977 = 1220233) B1220233
theorem B1626995 : Blo 1084620 1626995 := bstep (se 1 (by rfl) ⟨1220246, by rfl⟩ : syracuseStep 1626995 = 2440493) B2440493
theorem B1627025 : Blo 1084620 1627025 := bstep (se 2 (by rfl) ⟨610134, by rfl⟩ : syracuseStep 1627025 = 1220269) B1220269
theorem B1627043 : Blo 1084620 1627043 := bstep (se 1 (by rfl) ⟨1220282, by rfl⟩ : syracuseStep 1627043 = 2440565) B2440565
theorem B13915061 : Blo 1084620 13915061 := bstep (se 5 (by rfl) ⟨652268, by rfl⟩ : syracuseStep 13915061 = 1304537) B1304537
theorem B1627073 : Blo 1084620 1627073 := bstep (se 2 (by rfl) ⟨610152, by rfl⟩ : syracuseStep 1627073 = 1220305) B1220305
theorem B6181829 : Blo 1084620 6181829 := bstep (se 4 (by rfl) ⟨579546, by rfl⟩ : syracuseStep 6181829 = 1159093) B1159093
theorem B2446289 : Blo 1084620 2446289 := bstep (se 2 (by rfl) ⟨917358, by rfl⟩ : syracuseStep 2446289 = 1834717) B1834717
theorem B1627091 : Blo 1084620 1627091 := bstep (se 1 (by rfl) ⟨1220318, by rfl⟩ : syracuseStep 1627091 = 2440637) B2440637
theorem B2446307 : Blo 1084620 2446307 := bstep (se 1 (by rfl) ⟨1834730, by rfl⟩ : syracuseStep 2446307 = 3669461) B3669461
theorem B1627121 : Blo 1084620 1627121 := bstep (se 2 (by rfl) ⟨610170, by rfl⟩ : syracuseStep 1627121 = 1220341) B1220341
theorem B1627139 : Blo 1084620 1627139 := bstep (se 1 (by rfl) ⟨1220354, by rfl⟩ : syracuseStep 1627139 = 2440709) B2440709
theorem B1627169 : Blo 1084620 1627169 := bstep (se 2 (by rfl) ⟨610188, by rfl⟩ : syracuseStep 1627169 = 1220377) B1220377
theorem B1627187 : Blo 1084620 1627187 := bstep (se 1 (by rfl) ⟨1220390, by rfl⟩ : syracuseStep 1627187 = 2440781) B2440781
theorem B1791041 : Blo 1084620 1791041 := bstep (se 2 (by rfl) ⟨671640, by rfl⟩ : syracuseStep 1791041 = 1343281) B1343281
theorem B1627217 : Blo 1084620 1627217 := bstep (se 2 (by rfl) ⟨610206, by rfl⟩ : syracuseStep 1627217 = 1220413) B1220413
theorem B3298403 : Blo 1084620 3298403 := bstep (se 1 (by rfl) ⟨2473802, by rfl⟩ : syracuseStep 3298403 = 4947605) B4947605
theorem B1627235 : Blo 1084620 1627235 := bstep (se 1 (by rfl) ⟨1220426, by rfl⟩ : syracuseStep 1627235 = 2440853) B2440853
theorem B1627265 : Blo 1084620 1627265 := bstep (se 2 (by rfl) ⟨610224, by rfl⟩ : syracuseStep 1627265 = 1220449) B1220449
theorem B1627283 : Blo 1084620 1627283 := bstep (se 1 (by rfl) ⟨1220462, by rfl⟩ : syracuseStep 1627283 = 2440925) B2440925
theorem B1627313 : Blo 1084620 1627313 := bstep (se 2 (by rfl) ⟨610242, by rfl⟩ : syracuseStep 1627313 = 1220485) B1220485
theorem B3298499 : Blo 1084620 3298499 := bstep (se 1 (by rfl) ⟨2473874, by rfl⟩ : syracuseStep 3298499 = 4947749) B4947749
theorem B1627331 : Blo 1084620 1627331 := bstep (se 1 (by rfl) ⟨1220498, by rfl⟩ : syracuseStep 1627331 = 2440997) B2440997
theorem B1627361 : Blo 1084620 1627361 := bstep (se 2 (by rfl) ⟨610260, by rfl⟩ : syracuseStep 1627361 = 1220521) B1220521
theorem B2446577 : Blo 1084620 2446577 := bstep (se 2 (by rfl) ⟨917466, by rfl⟩ : syracuseStep 2446577 = 1834933) B1834933
theorem B1627379 : Blo 1084620 1627379 := bstep (se 1 (by rfl) ⟨1220534, by rfl⟩ : syracuseStep 1627379 = 2441069) B2441069
theorem B2446595 : Blo 1084620 2446595 := bstep (se 1 (by rfl) ⟨1834946, by rfl⟩ : syracuseStep 2446595 = 3669893) B3669893
theorem B1627409 : Blo 1084620 1627409 := bstep (se 2 (by rfl) ⟨610278, by rfl⟩ : syracuseStep 1627409 = 1220557) B1220557
theorem B1627427 : Blo 1084620 1627427 := bstep (se 1 (by rfl) ⟨1220570, by rfl⟩ : syracuseStep 1627427 = 2441141) B2441141
theorem B1627457 : Blo 1084620 1627457 := bstep (se 2 (by rfl) ⟨610296, by rfl⟩ : syracuseStep 1627457 = 1220593) B1220593
theorem B1627475 : Blo 1084620 1627475 := bstep (se 1 (by rfl) ⟨1220606, by rfl⟩ : syracuseStep 1627475 = 2441213) B2441213
theorem B1627505 : Blo 1084620 1627505 := bstep (se 2 (by rfl) ⟨610314, by rfl⟩ : syracuseStep 1627505 = 1220629) B1220629
theorem B1627523 : Blo 1084620 1627523 := bstep (se 1 (by rfl) ⟨1220642, by rfl⟩ : syracuseStep 1627523 = 2441285) B2441285
theorem B1627553 : Blo 1084620 1627553 := bstep (se 2 (by rfl) ⟨610332, by rfl⟩ : syracuseStep 1627553 = 1220665) B1220665
theorem B1856945 : Blo 1084620 1856945 := bstep (se 2 (by rfl) ⟨696354, by rfl⟩ : syracuseStep 1856945 = 1392709) B1392709
theorem B1627571 : Blo 1084620 1627571 := bstep (se 1 (by rfl) ⟨1220678, by rfl⟩ : syracuseStep 1627571 = 2441357) B2441357
theorem B1627601 : Blo 1084620 1627601 := bstep (se 2 (by rfl) ⟨610350, by rfl⟩ : syracuseStep 1627601 = 1220701) B1220701
theorem B1627619 : Blo 1084620 1627619 := bstep (se 1 (by rfl) ⟨1220714, by rfl⟩ : syracuseStep 1627619 = 2441429) B2441429
theorem B1627649 : Blo 1084620 1627649 := bstep (se 2 (by rfl) ⟨610368, by rfl⟩ : syracuseStep 1627649 = 1220737) B1220737
theorem B2446865 : Blo 1084620 2446865 := bstep (se 2 (by rfl) ⟨917574, by rfl⟩ : syracuseStep 2446865 = 1835149) B1835149
theorem B1627667 : Blo 1084620 1627667 := bstep (se 1 (by rfl) ⟨1220750, by rfl⟩ : syracuseStep 1627667 = 2441501) B2441501
theorem B2446883 : Blo 1084620 2446883 := bstep (se 1 (by rfl) ⟨1835162, by rfl⟩ : syracuseStep 2446883 = 3670325) B3670325
theorem B1627697 : Blo 1084620 1627697 := bstep (se 2 (by rfl) ⟨610386, by rfl⟩ : syracuseStep 1627697 = 1220773) B1220773
theorem B1627715 : Blo 1084620 1627715 := bstep (se 1 (by rfl) ⟨1220786, by rfl⟩ : syracuseStep 1627715 = 2441573) B2441573
theorem B1627745 : Blo 1084620 1627745 := bstep (se 2 (by rfl) ⟨610404, by rfl⟩ : syracuseStep 1627745 = 1220809) B1220809
theorem B6182513 : Blo 1084620 6182513 := bstep (se 2 (by rfl) ⟨2318442, by rfl⟩ : syracuseStep 6182513 = 4636885) B4636885
theorem B1627763 : Blo 1084620 1627763 := bstep (se 1 (by rfl) ⟨1220822, by rfl⟩ : syracuseStep 1627763 = 2441645) B2441645
theorem B1627793 : Blo 1084620 1627793 := bstep (se 2 (by rfl) ⟨610422, by rfl⟩ : syracuseStep 1627793 = 1220845) B1220845
theorem B1627811 : Blo 1084620 1627811 := bstep (se 1 (by rfl) ⟨1220858, by rfl⟩ : syracuseStep 1627811 = 2441717) B2441717
theorem B1627841 : Blo 1084620 1627841 := bstep (se 2 (by rfl) ⟨610440, by rfl⟩ : syracuseStep 1627841 = 1220881) B1220881
theorem B1627859 : Blo 1084620 1627859 := bstep (se 1 (by rfl) ⟨1220894, by rfl⟩ : syracuseStep 1627859 = 2441789) B2441789
theorem B1627889 : Blo 1084620 1627889 := bstep (se 2 (by rfl) ⟨610458, by rfl⟩ : syracuseStep 1627889 = 1220917) B1220917
theorem B1627907 : Blo 1084620 1627907 := bstep (se 1 (by rfl) ⟨1220930, by rfl⟩ : syracuseStep 1627907 = 2441861) B2441861
theorem B1627937 : Blo 1084620 1627937 := bstep (se 2 (by rfl) ⟨610476, by rfl⟩ : syracuseStep 1627937 = 1220953) B1220953
theorem B2447153 : Blo 1084620 2447153 := bstep (se 2 (by rfl) ⟨917682, by rfl⟩ : syracuseStep 2447153 = 1835365) B1835365
theorem B1627955 : Blo 1084620 1627955 := bstep (se 1 (by rfl) ⟨1220966, by rfl⟩ : syracuseStep 1627955 = 2441933) B2441933
theorem B2447171 : Blo 1084620 2447171 := bstep (se 1 (by rfl) ⟨1835378, by rfl⟩ : syracuseStep 2447171 = 3670757) B3670757
theorem B1627985 : Blo 1084620 1627985 := bstep (se 2 (by rfl) ⟨610494, by rfl⟩ : syracuseStep 1627985 = 1220989) B1220989
theorem B1628003 : Blo 1084620 1628003 := bstep (se 1 (by rfl) ⟨1221002, by rfl⟩ : syracuseStep 1628003 = 2442005) B2442005
theorem B1628033 : Blo 1084620 1628033 := bstep (se 2 (by rfl) ⟨610512, by rfl⟩ : syracuseStep 1628033 = 1221025) B1221025
theorem B4413325 : Blo 1084620 4413325 := bstep (se 3 (by rfl) ⟨827498, by rfl⟩ : syracuseStep 4413325 = 1654997) B1654997
theorem B1628051 : Blo 1084620 1628051 := bstep (se 1 (by rfl) ⟨1221038, by rfl⟩ : syracuseStep 1628051 = 2442077) B2442077
theorem B1628081 : Blo 1084620 1628081 := bstep (se 2 (by rfl) ⟨610530, by rfl⟩ : syracuseStep 1628081 = 1221061) B1221061
theorem B1628099 : Blo 1084620 1628099 := bstep (se 1 (by rfl) ⟨1221074, by rfl⟩ : syracuseStep 1628099 = 2442149) B2442149
theorem B1628129 : Blo 1084620 1628129 := bstep (se 2 (by rfl) ⟨610548, by rfl⟩ : syracuseStep 1628129 = 1221097) B1221097
theorem B9295843 : Blo 1084620 9295843 := bstep (se 1 (by rfl) ⟨6971882, by rfl⟩ : syracuseStep 9295843 = 13943765) B13943765
theorem B1628147 : Blo 1084620 1628147 := bstep (se 1 (by rfl) ⟨1221110, by rfl⟩ : syracuseStep 1628147 = 2442221) B2442221
theorem B1628177 : Blo 1084620 1628177 := bstep (se 2 (by rfl) ⟨610566, by rfl⟩ : syracuseStep 1628177 = 1221133) B1221133
theorem B1628195 : Blo 1084620 1628195 := bstep (se 1 (by rfl) ⟨1221146, by rfl⟩ : syracuseStep 1628195 = 2442293) B2442293
theorem B4642865 : Blo 1084620 4642865 := bstep (se 2 (by rfl) ⟨1741074, by rfl⟩ : syracuseStep 4642865 = 3482149) B3482149
theorem B1628225 : Blo 1084620 1628225 := bstep (se 2 (by rfl) ⟨610584, by rfl⟩ : syracuseStep 1628225 = 1221169) B1221169
theorem B2447441 : Blo 1084620 2447441 := bstep (se 2 (by rfl) ⟨917790, by rfl⟩ : syracuseStep 2447441 = 1835581) B1835581
theorem B1628243 : Blo 1084620 1628243 := bstep (se 1 (by rfl) ⟨1221182, by rfl⟩ : syracuseStep 1628243 = 2442365) B2442365
theorem B2447459 : Blo 1084620 2447459 := bstep (se 1 (by rfl) ⟨1835594, by rfl⟩ : syracuseStep 2447459 = 3671189) B3671189
theorem B1628273 : Blo 1084620 1628273 := bstep (se 2 (by rfl) ⟨610602, by rfl⟩ : syracuseStep 1628273 = 1221205) B1221205
theorem B1628291 : Blo 1084620 1628291 := bstep (se 1 (by rfl) ⟨1221218, by rfl⟩ : syracuseStep 1628291 = 2442437) B2442437
theorem B1628321 : Blo 1084620 1628321 := bstep (se 2 (by rfl) ⟨610620, by rfl⟩ : syracuseStep 1628321 = 1221241) B1221241
theorem B1628339 : Blo 1084620 1628339 := bstep (se 1 (by rfl) ⟨1221254, by rfl⟩ : syracuseStep 1628339 = 2442509) B2442509
theorem B1628369 : Blo 1084620 1628369 := bstep (se 2 (by rfl) ⟨610638, by rfl⟩ : syracuseStep 1628369 = 1221277) B1221277
theorem B1628387 : Blo 1084620 1628387 := bstep (se 1 (by rfl) ⟨1221290, by rfl⟩ : syracuseStep 1628387 = 2442581) B2442581
theorem B2316529 : Blo 1084620 2316529 := bstep (se 2 (by rfl) ⟨868698, by rfl⟩ : syracuseStep 2316529 = 1737397) B1737397
theorem B1628417 : Blo 1084620 1628417 := bstep (se 2 (by rfl) ⟨610656, by rfl⟩ : syracuseStep 1628417 = 1221313) B1221313
theorem B1628435 : Blo 1084620 1628435 := bstep (se 1 (by rfl) ⟨1221326, by rfl⟩ : syracuseStep 1628435 = 2442653) B2442653
theorem B1628465 : Blo 1084620 1628465 := bstep (se 2 (by rfl) ⟨610674, by rfl⟩ : syracuseStep 1628465 = 1221349) B1221349
theorem B1628483 : Blo 1084620 1628483 := bstep (se 1 (by rfl) ⟨1221362, by rfl⟩ : syracuseStep 1628483 = 2442725) B2442725
theorem B1628513 : Blo 1084620 1628513 := bstep (se 2 (by rfl) ⟨610692, by rfl⟩ : syracuseStep 1628513 = 1221385) B1221385
theorem B2447729 : Blo 1084620 2447729 := bstep (se 2 (by rfl) ⟨917898, by rfl⟩ : syracuseStep 2447729 = 1835797) B1835797
theorem B1628531 : Blo 1084620 1628531 := bstep (se 1 (by rfl) ⟨1221398, by rfl⟩ : syracuseStep 1628531 = 2442797) B2442797
theorem B2447747 : Blo 1084620 2447747 := bstep (se 1 (by rfl) ⟨1835810, by rfl⟩ : syracuseStep 2447747 = 3671621) B3671621
theorem B1628561 : Blo 1084620 1628561 := bstep (se 2 (by rfl) ⟨610710, by rfl⟩ : syracuseStep 1628561 = 1221421) B1221421
theorem B1628579 : Blo 1084620 1628579 := bstep (se 1 (by rfl) ⟨1221434, by rfl⟩ : syracuseStep 1628579 = 2442869) B2442869
theorem B1628609 : Blo 1084620 1628609 := bstep (se 2 (by rfl) ⟨610728, by rfl⟩ : syracuseStep 1628609 = 1221457) B1221457
theorem B1628627 : Blo 1084620 1628627 := bstep (se 1 (by rfl) ⟨1221470, by rfl⟩ : syracuseStep 1628627 = 2442941) B2442941
theorem B3299825 : Blo 1084620 3299825 := bstep (se 2 (by rfl) ⟨1237434, by rfl⟩ : syracuseStep 3299825 = 2474869) B2474869
theorem B1628657 : Blo 1084620 1628657 := bstep (se 2 (by rfl) ⟨610746, by rfl⟩ : syracuseStep 1628657 = 1221493) B1221493
theorem B1628675 : Blo 1084620 1628675 := bstep (se 1 (by rfl) ⟨1221506, by rfl⟩ : syracuseStep 1628675 = 2443013) B2443013
theorem B1628705 : Blo 1084620 1628705 := bstep (se 2 (by rfl) ⟨610764, by rfl⟩ : syracuseStep 1628705 = 1221529) B1221529
theorem B1628723 : Blo 1084620 1628723 := bstep (se 1 (by rfl) ⟨1221542, by rfl⟩ : syracuseStep 1628723 = 2443085) B2443085
theorem B1628753 : Blo 1084620 1628753 := bstep (se 2 (by rfl) ⟨610782, by rfl⟩ : syracuseStep 1628753 = 1221565) B1221565
theorem B1628771 : Blo 1084620 1628771 := bstep (se 1 (by rfl) ⟨1221578, by rfl⟩ : syracuseStep 1628771 = 2443157) B2443157
theorem B1628801 : Blo 1084620 1628801 := bstep (se 2 (by rfl) ⟨610800, by rfl⟩ : syracuseStep 1628801 = 1221601) B1221601
theorem B9394829 : Blo 1084620 9394829 := bstep (se 3 (by rfl) ⟨1761530, by rfl⟩ : syracuseStep 9394829 = 3523061) B3523061
theorem B2939533 : Blo 1084620 2939533 := bstep (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) B1102325
theorem B2448017 : Blo 1084620 2448017 := bstep (se 2 (by rfl) ⟨918006, by rfl⟩ : syracuseStep 2448017 = 1836013) B1836013
theorem B1628819 : Blo 1084620 1628819 := bstep (se 1 (by rfl) ⟨1221614, by rfl⟩ : syracuseStep 1628819 = 2443229) B2443229
theorem B2448035 : Blo 1084620 2448035 := bstep (se 1 (by rfl) ⟨1836026, by rfl⟩ : syracuseStep 2448035 = 3672053) B3672053
theorem B1628849 : Blo 1084620 1628849 := bstep (se 2 (by rfl) ⟨610818, by rfl⟩ : syracuseStep 1628849 = 1221637) B1221637
theorem B1628867 : Blo 1084620 1628867 := bstep (se 1 (by rfl) ⟨1221650, by rfl⟩ : syracuseStep 1628867 = 2443301) B2443301
theorem B4119245 : Blo 1084620 4119245 := bstep (se 3 (by rfl) ⟨772358, by rfl⟩ : syracuseStep 4119245 = 1544717) B1544717
theorem B1628897 : Blo 1084620 1628897 := bstep (se 2 (by rfl) ⟨610836, by rfl⟩ : syracuseStep 1628897 = 1221673) B1221673
theorem B2611939 : Blo 1084620 2611939 := bstep (se 1 (by rfl) ⟨1958954, by rfl⟩ : syracuseStep 2611939 = 3917909) B3917909
theorem B1628915 : Blo 1084620 1628915 := bstep (se 1 (by rfl) ⟨1221686, by rfl⟩ : syracuseStep 1628915 = 2443373) B2443373
theorem B1628945 : Blo 1084620 1628945 := bstep (se 2 (by rfl) ⟨610854, by rfl⟩ : syracuseStep 1628945 = 1221709) B1221709
theorem B2939665 : Blo 1084620 2939665 := bstep (se 2 (by rfl) ⟨1102374, by rfl⟩ : syracuseStep 2939665 = 2204749) B2204749
theorem B1628963 : Blo 1084620 1628963 := bstep (se 1 (by rfl) ⟨1221722, by rfl⟩ : syracuseStep 1628963 = 2443445) B2443445
theorem B1628993 : Blo 1084620 1628993 := bstep (se 2 (by rfl) ⟨610872, by rfl⟩ : syracuseStep 1628993 = 1221745) B1221745
theorem B1629011 : Blo 1084620 1629011 := bstep (se 1 (by rfl) ⟨1221758, by rfl⟩ : syracuseStep 1629011 = 2443517) B2443517
theorem B1629041 : Blo 1084620 1629041 := bstep (se 2 (by rfl) ⟨610890, by rfl⟩ : syracuseStep 1629041 = 1221781) B1221781
theorem B2317187 : Blo 1084620 2317187 := bstep (se 1 (by rfl) ⟨1737890, by rfl⟩ : syracuseStep 2317187 = 3475781) B3475781
theorem B1629059 : Blo 1084620 1629059 := bstep (se 1 (by rfl) ⟨1221794, by rfl⟩ : syracuseStep 1629059 = 2443589) B2443589
theorem B1629089 : Blo 1084620 1629089 := bstep (se 2 (by rfl) ⟨610908, by rfl⟩ : syracuseStep 1629089 = 1221817) B1221817
theorem B2448305 : Blo 1084620 2448305 := bstep (se 2 (by rfl) ⟨918114, by rfl⟩ : syracuseStep 2448305 = 1836229) B1836229
theorem B1629107 : Blo 1084620 1629107 := bstep (se 1 (by rfl) ⟨1221830, by rfl⟩ : syracuseStep 1629107 = 2443661) B2443661
theorem B2448323 : Blo 1084620 2448323 := bstep (se 1 (by rfl) ⟨1836242, by rfl⟩ : syracuseStep 2448323 = 3672485) B3672485
theorem B1629137 : Blo 1084620 1629137 := bstep (se 2 (by rfl) ⟨610926, by rfl⟩ : syracuseStep 1629137 = 1221853) B1221853
theorem B1629155 : Blo 1084620 1629155 := bstep (se 1 (by rfl) ⟨1221866, by rfl⟩ : syracuseStep 1629155 = 2443733) B2443733
theorem B13229027 : Blo 1084620 13229027 := bstep (se 1 (by rfl) ⟨9921770, by rfl⟩ : syracuseStep 13229027 = 19843541) B19843541
theorem B1629185 : Blo 1084620 1629185 := bstep (se 2 (by rfl) ⟨610944, by rfl⟩ : syracuseStep 1629185 = 1221889) B1221889
theorem B1629203 : Blo 1084620 1629203 := bstep (se 1 (by rfl) ⟨1221902, by rfl⟩ : syracuseStep 1629203 = 2443805) B2443805
theorem B6183971 : Blo 1084620 6183971 := bstep (se 1 (by rfl) ⟨4637978, by rfl⟩ : syracuseStep 6183971 = 9275957) B9275957
theorem B1629233 : Blo 1084620 1629233 := bstep (se 2 (by rfl) ⟨610962, by rfl⟩ : syracuseStep 1629233 = 1221925) B1221925
theorem B1629251 : Blo 1084620 1629251 := bstep (se 1 (by rfl) ⟨1221938, by rfl⟩ : syracuseStep 1629251 = 2443877) B2443877
theorem B1629281 : Blo 1084620 1629281 := bstep (se 2 (by rfl) ⟨610980, by rfl⟩ : syracuseStep 1629281 = 1221961) B1221961
theorem B1629299 : Blo 1084620 1629299 := bstep (se 1 (by rfl) ⟨1221974, by rfl⟩ : syracuseStep 1629299 = 2443949) B2443949
theorem B1629329 : Blo 1084620 1629329 := bstep (se 2 (by rfl) ⟨610998, by rfl⟩ : syracuseStep 1629329 = 1221997) B1221997
theorem B1629347 : Blo 1084620 1629347 := bstep (se 1 (by rfl) ⟨1222010, by rfl⟩ : syracuseStep 1629347 = 2444021) B2444021
theorem B1629377 : Blo 1084620 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B3398861 : Blo 1084620 3398861 := bstep (se 3 (by rfl) ⟨637286, by rfl⟩ : syracuseStep 3398861 = 1274573) B1274573
theorem B2448593 : Blo 1084620 2448593 := bstep (se 2 (by rfl) ⟨918222, by rfl⟩ : syracuseStep 2448593 = 1836445) B1836445
theorem B1629395 : Blo 1084620 1629395 := bstep (se 1 (by rfl) ⟨1222046, by rfl⟩ : syracuseStep 1629395 = 2444093) B2444093
theorem B2448611 : Blo 1084620 2448611 := bstep (se 1 (by rfl) ⟨1836458, by rfl⟩ : syracuseStep 2448611 = 3672917) B3672917
theorem B3923171 : Blo 1084620 3923171 := bstep (se 1 (by rfl) ⟨2942378, by rfl⟩ : syracuseStep 3923171 = 5884757) B5884757
theorem B3661037 : Blo 1084620 3661037 := bstep (se 3 (by rfl) ⟨686444, by rfl⟩ : syracuseStep 3661037 = 1372889) B1372889
theorem B1629425 : Blo 1084620 1629425 := bstep (se 2 (by rfl) ⟨611034, by rfl⟩ : syracuseStep 1629425 = 1222069) B1222069
theorem B1629443 : Blo 1084620 1629443 := bstep (se 1 (by rfl) ⟨1222082, by rfl⟩ : syracuseStep 1629443 = 2444165) B2444165
theorem B3136781 : Blo 1084620 3136781 := bstep (se 3 (by rfl) ⟨588146, by rfl⟩ : syracuseStep 3136781 = 1176293) B1176293
theorem B1629473 : Blo 1084620 1629473 := bstep (se 2 (by rfl) ⟨611052, by rfl⟩ : syracuseStep 1629473 = 1222105) B1222105
theorem B3661091 : Blo 1084620 3661091 := bstep (se 1 (by rfl) ⟨2745818, by rfl⟩ : syracuseStep 3661091 = 5491637) B5491637
theorem B1629491 : Blo 1084620 1629491 := bstep (se 1 (by rfl) ⟨1222118, by rfl⟩ : syracuseStep 1629491 = 2444237) B2444237
theorem B6610253 : Blo 1084620 6610253 := bstep (se 3 (by rfl) ⟨1239422, by rfl⟩ : syracuseStep 6610253 = 2478845) B2478845
theorem B1629521 : Blo 1084620 1629521 := bstep (se 2 (by rfl) ⟨611070, by rfl⟩ : syracuseStep 1629521 = 1222141) B1222141
theorem B1629539 : Blo 1084620 1629539 := bstep (se 1 (by rfl) ⟨1222154, by rfl⟩ : syracuseStep 1629539 = 2444309) B2444309
theorem B1629569 : Blo 1084620 1629569 := bstep (se 2 (by rfl) ⟨611088, by rfl⟩ : syracuseStep 1629569 = 1222177) B1222177
theorem B1858945 : Blo 1084620 1858945 := bstep (se 2 (by rfl) ⟨697104, by rfl⟩ : syracuseStep 1858945 = 1394209) B1394209
theorem B2612611 : Blo 1084620 2612611 := bstep (se 1 (by rfl) ⟨1959458, by rfl⟩ : syracuseStep 2612611 = 3918917) B3918917
theorem B1629587 : Blo 1084620 1629587 := bstep (se 1 (by rfl) ⟨1222190, by rfl⟩ : syracuseStep 1629587 = 2444381) B2444381
theorem B1957297 : Blo 1084620 1957297 := bstep (se 2 (by rfl) ⟨733986, by rfl⟩ : syracuseStep 1957297 = 1467973) B1467973
theorem B1629617 : Blo 1084620 1629617 := bstep (se 2 (by rfl) ⟨611106, by rfl⟩ : syracuseStep 1629617 = 1222213) B1222213
theorem B1629635 : Blo 1084620 1629635 := bstep (se 1 (by rfl) ⟨1222226, by rfl⟩ : syracuseStep 1629635 = 2444453) B2444453
theorem B1629665 : Blo 1084620 1629665 := bstep (se 2 (by rfl) ⟨611124, by rfl⟩ : syracuseStep 1629665 = 1222249) B1222249
theorem B2448881 : Blo 1084620 2448881 := bstep (se 2 (by rfl) ⟨918330, by rfl⟩ : syracuseStep 2448881 = 1836661) B1836661
theorem B1629683 : Blo 1084620 1629683 := bstep (se 1 (by rfl) ⟨1222262, by rfl⟩ : syracuseStep 1629683 = 2444525) B2444525
theorem B2448899 : Blo 1084620 2448899 := bstep (se 1 (by rfl) ⟨1836674, by rfl⟩ : syracuseStep 2448899 = 3673349) B3673349
theorem B1629713 : Blo 1084620 1629713 := bstep (se 2 (by rfl) ⟨611142, by rfl⟩ : syracuseStep 1629713 = 1222285) B1222285
theorem B1629731 : Blo 1084620 1629731 := bstep (se 1 (by rfl) ⟨1222298, by rfl⟩ : syracuseStep 1629731 = 2444597) B2444597
theorem B3661361 : Blo 1084620 3661361 := bstep (se 2 (by rfl) ⟨1373010, by rfl⟩ : syracuseStep 3661361 = 2746021) B2746021
theorem B1629761 : Blo 1084620 1629761 := bstep (se 2 (by rfl) ⟨611160, by rfl⟩ : syracuseStep 1629761 = 1222321) B1222321
theorem B1629779 : Blo 1084620 1629779 := bstep (se 1 (by rfl) ⟨1222334, by rfl⟩ : syracuseStep 1629779 = 2444669) B2444669
theorem B1629809 : Blo 1084620 1629809 := bstep (se 2 (by rfl) ⟨611178, by rfl⟩ : syracuseStep 1629809 = 1222357) B1222357
theorem B1629827 : Blo 1084620 1629827 := bstep (se 1 (by rfl) ⟨1222370, by rfl⟩ : syracuseStep 1629827 = 2444741) B2444741
theorem B1629857 : Blo 1084620 1629857 := bstep (se 2 (by rfl) ⟨611196, by rfl⟩ : syracuseStep 1629857 = 1222393) B1222393
theorem B5496497 : Blo 1084620 5496497 := bstep (se 2 (by rfl) ⟨2061186, by rfl⟩ : syracuseStep 5496497 = 4122373) B4122373
theorem B1629875 : Blo 1084620 1629875 := bstep (se 1 (by rfl) ⟨1222406, by rfl⟩ : syracuseStep 1629875 = 2444813) B2444813
theorem B2318033 : Blo 1084620 2318033 := bstep (se 2 (by rfl) ⟨869262, by rfl⟩ : syracuseStep 2318033 = 1738525) B1738525
theorem B1629905 : Blo 1084620 1629905 := bstep (se 2 (by rfl) ⟨611214, by rfl⟩ : syracuseStep 1629905 = 1222429) B1222429
theorem B19816163 : Blo 1084620 19816163 := bstep (se 1 (by rfl) ⟨14862122, by rfl⟩ : syracuseStep 19816163 = 29724245) B29724245
theorem B1629923 : Blo 1084620 1629923 := bstep (se 1 (by rfl) ⟨1222442, by rfl⟩ : syracuseStep 1629923 = 2444885) B2444885
theorem B1629953 : Blo 1084620 1629953 := bstep (se 2 (by rfl) ⟨611232, by rfl⟩ : syracuseStep 1629953 = 1222465) B1222465
theorem B2449169 : Blo 1084620 2449169 := bstep (se 2 (by rfl) ⟨918438, by rfl⟩ : syracuseStep 2449169 = 1836877) B1836877
theorem B1629971 : Blo 1084620 1629971 := bstep (se 1 (by rfl) ⟨1222478, by rfl⟩ : syracuseStep 1629971 = 2444957) B2444957
theorem B2449187 : Blo 1084620 2449187 := bstep (se 1 (by rfl) ⟨1836890, by rfl⟩ : syracuseStep 2449187 = 3673781) B3673781
theorem B1630001 : Blo 1084620 1630001 := bstep (se 2 (by rfl) ⟨611250, by rfl⟩ : syracuseStep 1630001 = 1222501) B1222501
theorem B26828597 : Blo 1084620 26828597 := bstep (se 5 (by rfl) ⟨1257590, by rfl⟩ : syracuseStep 26828597 = 2515181) B2515181
theorem B1630019 : Blo 1084620 1630019 := bstep (se 1 (by rfl) ⟨1222514, by rfl⟩ : syracuseStep 1630019 = 2445029) B2445029
theorem B2613073 : Blo 1084620 2613073 := bstep (se 2 (by rfl) ⟨979902, by rfl⟩ : syracuseStep 2613073 = 1959805) B1959805
theorem B1630049 : Blo 1084620 1630049 := bstep (se 2 (by rfl) ⟨611268, by rfl⟩ : syracuseStep 1630049 = 1222537) B1222537
theorem B1630067 : Blo 1084620 1630067 := bstep (se 1 (by rfl) ⟨1222550, by rfl⟩ : syracuseStep 1630067 = 2445101) B2445101
theorem B1630097 : Blo 1084620 1630097 := bstep (se 2 (by rfl) ⟨611286, by rfl⟩ : syracuseStep 1630097 = 1222573) B1222573
theorem B1630115 : Blo 1084620 1630115 := bstep (se 1 (by rfl) ⟨1222586, by rfl⟩ : syracuseStep 1630115 = 2445173) B2445173
theorem B2613169 : Blo 1084620 2613169 := bstep (se 2 (by rfl) ⟨979938, by rfl⟩ : syracuseStep 2613169 = 1959877) B1959877
theorem B1630145 : Blo 1084620 1630145 := bstep (se 2 (by rfl) ⟨611304, by rfl⟩ : syracuseStep 1630145 = 1222609) B1222609
theorem B1630163 : Blo 1084620 1630163 := bstep (se 1 (by rfl) ⟨1222622, by rfl⟩ : syracuseStep 1630163 = 2445245) B2445245
theorem B23486435 : Blo 1084620 23486435 := bstep (se 1 (by rfl) ⟨17614826, by rfl⟩ : syracuseStep 23486435 = 35229653) B35229653
theorem B1630193 : Blo 1084620 1630193 := bstep (se 2 (by rfl) ⟨611322, by rfl⟩ : syracuseStep 1630193 = 1222645) B1222645
theorem B1630211 : Blo 1084620 1630211 := bstep (se 1 (by rfl) ⟨1222658, by rfl⟩ : syracuseStep 1630211 = 2445317) B2445317
theorem B1630241 : Blo 1084620 1630241 := bstep (se 2 (by rfl) ⟨611340, by rfl⟩ : syracuseStep 1630241 = 1222681) B1222681
theorem B1630259 : Blo 1084620 1630259 := bstep (se 1 (by rfl) ⟨1222694, by rfl⟩ : syracuseStep 1630259 = 2445389) B2445389
theorem B3661901 : Blo 1084620 3661901 := bstep (se 3 (by rfl) ⟨686606, by rfl⟩ : syracuseStep 3661901 = 1373213) B1373213
theorem B1630289 : Blo 1084620 1630289 := bstep (se 2 (by rfl) ⟨611358, by rfl⟩ : syracuseStep 1630289 = 1222717) B1222717
theorem B9396323 : Blo 1084620 9396323 := bstep (se 1 (by rfl) ⟨7047242, by rfl⟩ : syracuseStep 9396323 = 14094485) B14094485
theorem B1630307 : Blo 1084620 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B1630337 : Blo 1084620 1630337 := bstep (se 2 (by rfl) ⟨611376, by rfl⟩ : syracuseStep 1630337 = 1222753) B1222753
theorem B3661955 : Blo 1084620 3661955 := bstep (se 1 (by rfl) ⟨2746466, by rfl⟩ : syracuseStep 3661955 = 5492933) B5492933
theorem B1630355 : Blo 1084620 1630355 := bstep (se 1 (by rfl) ⟨1222766, by rfl⟩ : syracuseStep 1630355 = 2445533) B2445533
theorem B1630385 : Blo 1084620 1630385 := bstep (se 2 (by rfl) ⟨611394, by rfl⟩ : syracuseStep 1630385 = 1222789) B1222789
theorem B1630403 : Blo 1084620 1630403 := bstep (se 1 (by rfl) ⟨1222802, by rfl⟩ : syracuseStep 1630403 = 2445605) B2445605
theorem B1630433 : Blo 1084620 1630433 := bstep (se 2 (by rfl) ⟨611412, by rfl⟩ : syracuseStep 1630433 = 1222825) B1222825
theorem B15655139 : Blo 1084620 15655139 := bstep (se 1 (by rfl) ⟨11741354, by rfl⟩ : syracuseStep 15655139 = 23482709) B23482709
theorem B1630451 : Blo 1084620 1630451 := bstep (se 1 (by rfl) ⟨1222838, by rfl⟩ : syracuseStep 1630451 = 2445677) B2445677
theorem B1630481 : Blo 1084620 1630481 := bstep (se 2 (by rfl) ⟨611430, by rfl⟩ : syracuseStep 1630481 = 1222861) B1222861
theorem B1630499 : Blo 1084620 1630499 := bstep (se 1 (by rfl) ⟨1222874, by rfl⟩ : syracuseStep 1630499 = 2445749) B2445749
theorem B1630529 : Blo 1084620 1630529 := bstep (se 2 (by rfl) ⟨611448, by rfl⟩ : syracuseStep 1630529 = 1222897) B1222897
theorem B14868805 : Blo 1084620 14868805 := bstep (se 4 (by rfl) ⟨1393950, by rfl⟩ : syracuseStep 14868805 = 2787901) B2787901
theorem B1630547 : Blo 1084620 1630547 := bstep (se 1 (by rfl) ⟨1222910, by rfl⟩ : syracuseStep 1630547 = 2445821) B2445821
theorem B1761635 : Blo 1084620 1761635 := bstep (se 1 (by rfl) ⟨1321226, by rfl⟩ : syracuseStep 1761635 = 2642453) B2642453
theorem B1630577 : Blo 1084620 1630577 := bstep (se 2 (by rfl) ⟨611466, by rfl⟩ : syracuseStep 1630577 = 1222933) B1222933
theorem B1630595 : Blo 1084620 1630595 := bstep (se 1 (by rfl) ⟨1222946, by rfl⟩ : syracuseStep 1630595 = 2445893) B2445893
theorem B3662225 : Blo 1084620 3662225 := bstep (se 2 (by rfl) ⟨1373334, by rfl⟩ : syracuseStep 3662225 = 2746669) B2746669
theorem B1630625 : Blo 1084620 1630625 := bstep (se 2 (by rfl) ⟨611484, by rfl⟩ : syracuseStep 1630625 = 1222969) B1222969
theorem B1630643 : Blo 1084620 1630643 := bstep (se 1 (by rfl) ⟨1222982, by rfl⟩ : syracuseStep 1630643 = 2445965) B2445965
theorem B4645325 : Blo 1084620 4645325 := bstep (se 3 (by rfl) ⟨870998, by rfl⟩ : syracuseStep 4645325 = 1741997) B1741997
theorem B1630673 : Blo 1084620 1630673 := bstep (se 2 (by rfl) ⟨611502, by rfl⟩ : syracuseStep 1630673 = 1223005) B1223005
theorem B1630691 : Blo 1084620 1630691 := bstep (se 1 (by rfl) ⟨1223018, by rfl⟩ : syracuseStep 1630691 = 2446037) B2446037
theorem B1630721 : Blo 1084620 1630721 := bstep (se 2 (by rfl) ⟨611520, by rfl⟩ : syracuseStep 1630721 = 1223041) B1223041
theorem B1630739 : Blo 1084620 1630739 := bstep (se 1 (by rfl) ⟨1223054, by rfl⟩ : syracuseStep 1630739 = 2446109) B2446109
theorem B1630769 : Blo 1084620 1630769 := bstep (se 2 (by rfl) ⟨611538, by rfl⟩ : syracuseStep 1630769 = 1223077) B1223077
theorem B1630787 : Blo 1084620 1630787 := bstep (se 1 (by rfl) ⟨1223090, by rfl⟩ : syracuseStep 1630787 = 2446181) B2446181
theorem B1630817 : Blo 1084620 1630817 := bstep (se 2 (by rfl) ⟨611556, by rfl⟩ : syracuseStep 1630817 = 1223113) B1223113
theorem B1630835 : Blo 1084620 1630835 := bstep (se 1 (by rfl) ⟨1223126, by rfl⟩ : syracuseStep 1630835 = 2446253) B2446253
theorem B1630865 : Blo 1084620 1630865 := bstep (se 2 (by rfl) ⟨611574, by rfl⟩ : syracuseStep 1630865 = 1223149) B1223149
theorem B1630883 : Blo 1084620 1630883 := bstep (se 1 (by rfl) ⟨1223162, by rfl⟩ : syracuseStep 1630883 = 2446325) B2446325
theorem B1630913 : Blo 1084620 1630913 := bstep (se 2 (by rfl) ⟨611592, by rfl⟩ : syracuseStep 1630913 = 1223185) B1223185
theorem B1696465 : Blo 1084620 1696465 := bstep (se 2 (by rfl) ⟨636174, by rfl⟩ : syracuseStep 1696465 = 1272349) B1272349
theorem B1630931 : Blo 1084620 1630931 := bstep (se 1 (by rfl) ⟨1223198, by rfl⟩ : syracuseStep 1630931 = 2446397) B2446397
theorem B18572003 : Blo 1084620 18572003 := bstep (se 1 (by rfl) ⟨13929002, by rfl⟩ : syracuseStep 18572003 = 27858005) B27858005
theorem B1630961 : Blo 1084620 1630961 := bstep (se 2 (by rfl) ⟨611610, by rfl⟩ : syracuseStep 1630961 = 1223221) B1223221
theorem B1630979 : Blo 1084620 1630979 := bstep (se 1 (by rfl) ⟨1223234, by rfl⟩ : syracuseStep 1630979 = 2446469) B2446469
theorem B1631009 : Blo 1084620 1631009 := bstep (se 2 (by rfl) ⟨611628, by rfl⟩ : syracuseStep 1631009 = 1223257) B1223257
theorem B4645667 : Blo 1084620 4645667 := bstep (se 1 (by rfl) ⟨3484250, by rfl⟩ : syracuseStep 4645667 = 6968501) B6968501
theorem B1631027 : Blo 1084620 1631027 := bstep (se 1 (by rfl) ⟨1223270, by rfl⟩ : syracuseStep 1631027 = 2446541) B2446541
theorem B1631057 : Blo 1084620 1631057 := bstep (se 2 (by rfl) ⟨611646, by rfl⟩ : syracuseStep 1631057 = 1223293) B1223293
theorem B1631075 : Blo 1084620 1631075 := bstep (se 1 (by rfl) ⟨1223306, by rfl⟩ : syracuseStep 1631075 = 2446613) B2446613
theorem B1631105 : Blo 1084620 1631105 := bstep (se 2 (by rfl) ⟨611664, by rfl⟩ : syracuseStep 1631105 = 1223329) B1223329
theorem B6972293 : Blo 1084620 6972293 := bstep (se 4 (by rfl) ⟨653652, by rfl⟩ : syracuseStep 6972293 = 1307305) B1307305
theorem B1467281 : Blo 1084620 1467281 := bstep (se 2 (by rfl) ⟨550230, by rfl⟩ : syracuseStep 1467281 = 1100461) B1100461
theorem B1631123 : Blo 1084620 1631123 := bstep (se 1 (by rfl) ⟨1223342, by rfl⟩ : syracuseStep 1631123 = 2446685) B2446685
theorem B3662765 : Blo 1084620 3662765 := bstep (se 3 (by rfl) ⟨686768, by rfl⟩ : syracuseStep 3662765 = 1373537) B1373537
theorem B1631153 : Blo 1084620 1631153 := bstep (se 2 (by rfl) ⟨611682, by rfl⟩ : syracuseStep 1631153 = 1223365) B1223365
theorem B1631171 : Blo 1084620 1631171 := bstep (se 1 (by rfl) ⟨1223378, by rfl⟩ : syracuseStep 1631171 = 2446757) B2446757
theorem B1631201 : Blo 1084620 1631201 := bstep (se 2 (by rfl) ⟨611700, by rfl⟩ : syracuseStep 1631201 = 1223401) B1223401
theorem B3662819 : Blo 1084620 3662819 := bstep (se 1 (by rfl) ⟨2747114, by rfl⟩ : syracuseStep 3662819 = 5494229) B5494229
theorem B1631219 : Blo 1084620 1631219 := bstep (se 1 (by rfl) ⟨1223414, by rfl⟩ : syracuseStep 1631219 = 2446829) B2446829
theorem B1631249 : Blo 1084620 1631249 := bstep (se 2 (by rfl) ⟨611718, by rfl⟩ : syracuseStep 1631249 = 1223437) B1223437
theorem B1631267 : Blo 1084620 1631267 := bstep (se 1 (by rfl) ⟨1223450, by rfl⟩ : syracuseStep 1631267 = 2446901) B2446901
theorem B1467443 : Blo 1084620 1467443 := bstep (se 1 (by rfl) ⟨1100582, by rfl⟩ : syracuseStep 1467443 = 2201165) B2201165
theorem B1631297 : Blo 1084620 1631297 := bstep (se 2 (by rfl) ⟨611736, by rfl⟩ : syracuseStep 1631297 = 1223473) B1223473
theorem B1631315 : Blo 1084620 1631315 := bstep (se 1 (by rfl) ⟨1223486, by rfl⟩ : syracuseStep 1631315 = 2446973) B2446973
theorem B5497955 : Blo 1084620 5497955 := bstep (se 1 (by rfl) ⟨4123466, by rfl⟩ : syracuseStep 5497955 = 8246933) B8246933
theorem B1631345 : Blo 1084620 1631345 := bstep (se 2 (by rfl) ⟨611754, by rfl⟩ : syracuseStep 1631345 = 1223509) B1223509
theorem B1631363 : Blo 1084620 1631363 := bstep (se 1 (by rfl) ⟨1223522, by rfl⟩ : syracuseStep 1631363 = 2447045) B2447045
theorem B1631393 : Blo 1084620 1631393 := bstep (se 2 (by rfl) ⟨611772, by rfl⟩ : syracuseStep 1631393 = 1223545) B1223545
theorem B2942129 : Blo 1084620 2942129 := bstep (se 2 (by rfl) ⟨1103298, by rfl⟩ : syracuseStep 2942129 = 2206597) B2206597
theorem B1631411 : Blo 1084620 1631411 := bstep (se 1 (by rfl) ⟨1223558, by rfl⟩ : syracuseStep 1631411 = 2447117) B2447117
theorem B1631441 : Blo 1084620 1631441 := bstep (se 2 (by rfl) ⟨611790, by rfl⟩ : syracuseStep 1631441 = 1223581) B1223581
theorem B1631459 : Blo 1084620 1631459 := bstep (se 1 (by rfl) ⟨1223594, by rfl⟩ : syracuseStep 1631459 = 2447189) B2447189
theorem B7628017 : Blo 1084620 7628017 := bstep (se 2 (by rfl) ⟨2860506, by rfl⟩ : syracuseStep 7628017 = 5721013) B5721013
theorem B3663089 : Blo 1084620 3663089 := bstep (se 2 (by rfl) ⟨1373658, by rfl⟩ : syracuseStep 3663089 = 2747317) B2747317
theorem B1631489 : Blo 1084620 1631489 := bstep (se 2 (by rfl) ⟨611808, by rfl⟩ : syracuseStep 1631489 = 1223617) B1223617
theorem B1959185 : Blo 1084620 1959185 := bstep (se 2 (by rfl) ⟨734694, by rfl⟩ : syracuseStep 1959185 = 1469389) B1469389
theorem B1631507 : Blo 1084620 1631507 := bstep (se 1 (by rfl) ⟨1223630, by rfl⟩ : syracuseStep 1631507 = 2447261) B2447261
theorem B1631537 : Blo 1084620 1631537 := bstep (se 2 (by rfl) ⟨611826, by rfl⟩ : syracuseStep 1631537 = 1223653) B1223653
theorem B1631555 : Blo 1084620 1631555 := bstep (se 1 (by rfl) ⟨1223666, by rfl⟩ : syracuseStep 1631555 = 2447333) B2447333
theorem B1631585 : Blo 1084620 1631585 := bstep (se 2 (by rfl) ⟨611844, by rfl⟩ : syracuseStep 1631585 = 1223689) B1223689
theorem B1631603 : Blo 1084620 1631603 := bstep (se 1 (by rfl) ⟨1223702, by rfl⟩ : syracuseStep 1631603 = 2447405) B2447405
theorem B1631633 : Blo 1084620 1631633 := bstep (se 2 (by rfl) ⟨611862, by rfl⟩ : syracuseStep 1631633 = 1223725) B1223725
theorem B3302819 : Blo 1084620 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B1631651 : Blo 1084620 1631651 := bstep (se 1 (by rfl) ⟨1223738, by rfl⟩ : syracuseStep 1631651 = 2447477) B2447477
theorem B1631681 : Blo 1084620 1631681 := bstep (se 2 (by rfl) ⟨611880, by rfl⟩ : syracuseStep 1631681 = 1223761) B1223761
theorem B8250821 : Blo 1084620 8250821 := bstep (se 4 (by rfl) ⟨773514, by rfl⟩ : syracuseStep 8250821 = 1547029) B1547029
theorem B2745809 : Blo 1084620 2745809 := bstep (se 2 (by rfl) ⟨1029678, by rfl⟩ : syracuseStep 2745809 = 2059357) B2059357
theorem B1631699 : Blo 1084620 1631699 := bstep (se 1 (by rfl) ⟨1223774, by rfl⟩ : syracuseStep 1631699 = 2447549) B2447549
theorem B1631729 : Blo 1084620 1631729 := bstep (se 2 (by rfl) ⟨611898, by rfl⟩ : syracuseStep 1631729 = 1223797) B1223797
theorem B2745859 : Blo 1084620 2745859 := bstep (se 1 (by rfl) ⟨2059394, by rfl⟩ : syracuseStep 2745859 = 4118789) B4118789
theorem B1631747 : Blo 1084620 1631747 := bstep (se 1 (by rfl) ⟨1223810, by rfl⟩ : syracuseStep 1631747 = 2447621) B2447621
theorem B2942477 : Blo 1084620 2942477 := bstep (se 3 (by rfl) ⟨551714, by rfl⟩ : syracuseStep 2942477 = 1103429) B1103429
theorem B1631777 : Blo 1084620 1631777 := bstep (se 2 (by rfl) ⟨611916, by rfl⟩ : syracuseStep 1631777 = 1223833) B1223833
theorem B4122161 : Blo 1084620 4122161 := bstep (se 2 (by rfl) ⟨1545810, by rfl⟩ : syracuseStep 4122161 = 3091621) B3091621
theorem B1631795 : Blo 1084620 1631795 := bstep (se 1 (by rfl) ⟨1223846, by rfl⟩ : syracuseStep 1631795 = 2447693) B2447693
theorem B1631825 : Blo 1084620 1631825 := bstep (se 2 (by rfl) ⟨611934, by rfl⟩ : syracuseStep 1631825 = 1223869) B1223869
theorem B1631843 : Blo 1084620 1631843 := bstep (se 1 (by rfl) ⟨1223882, by rfl⟩ : syracuseStep 1631843 = 2447765) B2447765
theorem B1631873 : Blo 1084620 1631873 := bstep (se 2 (by rfl) ⟨611952, by rfl⟩ : syracuseStep 1631873 = 1223905) B1223905
theorem B2746001 : Blo 1084620 2746001 := bstep (se 2 (by rfl) ⟨1029750, by rfl⟩ : syracuseStep 2746001 = 2059501) B2059501
theorem B1631891 : Blo 1084620 1631891 := bstep (se 1 (by rfl) ⟨1223918, by rfl⟩ : syracuseStep 1631891 = 2447837) B2447837
theorem B1468081 : Blo 1084620 1468081 := bstep (se 2 (by rfl) ⟨550530, by rfl⟩ : syracuseStep 1468081 = 1101061) B1101061
theorem B1631921 : Blo 1084620 1631921 := bstep (se 2 (by rfl) ⟨611970, by rfl⟩ : syracuseStep 1631921 = 1223941) B1223941
theorem B1631939 : Blo 1084620 1631939 := bstep (se 1 (by rfl) ⟨1223954, by rfl⟩ : syracuseStep 1631939 = 2447909) B2447909
theorem B1631969 : Blo 1084620 1631969 := bstep (se 2 (by rfl) ⟨611988, by rfl⟩ : syracuseStep 1631969 = 1223977) B1223977
theorem B1631987 : Blo 1084620 1631987 := bstep (se 1 (by rfl) ⟨1223990, by rfl⟩ : syracuseStep 1631987 = 2447981) B2447981
theorem B3663629 : Blo 1084620 3663629 := bstep (se 3 (by rfl) ⟨686930, by rfl⟩ : syracuseStep 3663629 = 1373861) B1373861
theorem B1632017 : Blo 1084620 1632017 := bstep (se 2 (by rfl) ⟨612006, by rfl⟩ : syracuseStep 1632017 = 1224013) B1224013
theorem B1632035 : Blo 1084620 1632035 := bstep (se 1 (by rfl) ⟨1224026, by rfl⟩ : syracuseStep 1632035 = 2448053) B2448053
theorem B1632065 : Blo 1084620 1632065 := bstep (se 2 (by rfl) ⟨612024, by rfl⟩ : syracuseStep 1632065 = 1224049) B1224049
theorem B3663683 : Blo 1084620 3663683 := bstep (se 1 (by rfl) ⟨2747762, by rfl⟩ : syracuseStep 3663683 = 5495525) B5495525
theorem B1632083 : Blo 1084620 1632083 := bstep (se 1 (by rfl) ⟨1224062, by rfl⟩ : syracuseStep 1632083 = 2448125) B2448125
theorem B1632113 : Blo 1084620 1632113 := bstep (se 2 (by rfl) ⟨612042, by rfl⟩ : syracuseStep 1632113 = 1224085) B1224085
theorem B1632131 : Blo 1084620 1632131 := bstep (se 1 (by rfl) ⟨1224098, by rfl⟩ : syracuseStep 1632131 = 2448197) B2448197
theorem B5498765 : Blo 1084620 5498765 := bstep (se 3 (by rfl) ⟨1031018, by rfl⟩ : syracuseStep 5498765 = 2062037) B2062037
theorem B1632161 : Blo 1084620 1632161 := bstep (se 2 (by rfl) ⟨612060, by rfl⟩ : syracuseStep 1632161 = 1224121) B1224121
theorem B1632179 : Blo 1084620 1632179 := bstep (se 1 (by rfl) ⟨1224134, by rfl⟩ : syracuseStep 1632179 = 2448269) B2448269
theorem B1632209 : Blo 1084620 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B1632227 : Blo 1084620 1632227 := bstep (se 1 (by rfl) ⟨1224170, by rfl⟩ : syracuseStep 1632227 = 2448341) B2448341
theorem B1632257 : Blo 1084620 1632257 := bstep (se 2 (by rfl) ⟨612096, by rfl⟩ : syracuseStep 1632257 = 1224193) B1224193
theorem B1632275 : Blo 1084620 1632275 := bstep (se 1 (by rfl) ⟨1224206, by rfl⟩ : syracuseStep 1632275 = 2448413) B2448413
theorem B1632305 : Blo 1084620 1632305 := bstep (se 2 (by rfl) ⟨612114, by rfl⟩ : syracuseStep 1632305 = 1224229) B1224229
theorem B1632323 : Blo 1084620 1632323 := bstep (se 1 (by rfl) ⟨1224242, by rfl⟩ : syracuseStep 1632323 = 2448485) B2448485
theorem B3663953 : Blo 1084620 3663953 := bstep (se 2 (by rfl) ⟨1373982, by rfl⟩ : syracuseStep 3663953 = 2747965) B2747965
theorem B1632353 : Blo 1084620 1632353 := bstep (se 2 (by rfl) ⟨612132, by rfl⟩ : syracuseStep 1632353 = 1224265) B1224265
theorem B1632371 : Blo 1084620 1632371 := bstep (se 1 (by rfl) ⟨1224278, by rfl⟩ : syracuseStep 1632371 = 2448557) B2448557
theorem B1632401 : Blo 1084620 1632401 := bstep (se 2 (by rfl) ⟨612150, by rfl⟩ : syracuseStep 1632401 = 1224301) B1224301
theorem B1632419 : Blo 1084620 1632419 := bstep (se 1 (by rfl) ⟨1224314, by rfl⟩ : syracuseStep 1632419 = 2448629) B2448629
theorem B1632449 : Blo 1084620 1632449 := bstep (se 2 (by rfl) ⟨612168, by rfl⟩ : syracuseStep 1632449 = 1224337) B1224337
theorem B6187205 : Blo 1084620 6187205 := bstep (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) B1160101
theorem B1632467 : Blo 1084620 1632467 := bstep (se 1 (by rfl) ⟨1224350, by rfl⟩ : syracuseStep 1632467 = 2448701) B2448701
theorem B13920497 : Blo 1084620 13920497 := bstep (se 2 (by rfl) ⟨5220186, by rfl⟩ : syracuseStep 13920497 = 10440373) B10440373
theorem B1632497 : Blo 1084620 1632497 := bstep (se 2 (by rfl) ⟨612186, by rfl⟩ : syracuseStep 1632497 = 1224373) B1224373
theorem B1566977 : Blo 1084620 1566977 := bstep (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) B1175233
theorem B1632515 : Blo 1084620 1632515 := bstep (se 1 (by rfl) ⟨1224386, by rfl⟩ : syracuseStep 1632515 = 2448773) B2448773
theorem B1632545 : Blo 1084620 1632545 := bstep (se 2 (by rfl) ⟨612204, by rfl⟩ : syracuseStep 1632545 = 1224409) B1224409
theorem B1763635 : Blo 1084620 1763635 := bstep (se 1 (by rfl) ⟨1322726, by rfl⟩ : syracuseStep 1763635 = 2645453) B2645453
theorem B1632563 : Blo 1084620 1632563 := bstep (se 1 (by rfl) ⟨1224422, by rfl⟩ : syracuseStep 1632563 = 2448845) B2448845
theorem B1632593 : Blo 1084620 1632593 := bstep (se 2 (by rfl) ⟨612222, by rfl⟩ : syracuseStep 1632593 = 1224445) B1224445
theorem B1632611 : Blo 1084620 1632611 := bstep (se 1 (by rfl) ⟨1224458, by rfl⟩ : syracuseStep 1632611 = 2448917) B2448917
theorem B10447217 : Blo 1084620 10447217 := bstep (se 2 (by rfl) ⟨3917706, by rfl⟩ : syracuseStep 10447217 = 7835413) B7835413
theorem B1632641 : Blo 1084620 1632641 := bstep (se 2 (by rfl) ⟨612240, by rfl⟩ : syracuseStep 1632641 = 1224481) B1224481
theorem B1632659 : Blo 1084620 1632659 := bstep (se 1 (by rfl) ⟨1224494, by rfl⟩ : syracuseStep 1632659 = 2448989) B2448989
theorem B2320817 : Blo 1084620 2320817 := bstep (se 2 (by rfl) ⟨870306, by rfl⟩ : syracuseStep 2320817 = 1740613) B1740613
theorem B1632689 : Blo 1084620 1632689 := bstep (se 2 (by rfl) ⟨612258, by rfl⟩ : syracuseStep 1632689 = 1224517) B1224517
theorem B1632707 : Blo 1084620 1632707 := bstep (se 1 (by rfl) ⟨1224530, by rfl⟩ : syracuseStep 1632707 = 2449061) B2449061
theorem B1632737 : Blo 1084620 1632737 := bstep (se 2 (by rfl) ⟨612276, by rfl⟩ : syracuseStep 1632737 = 1224553) B1224553
theorem B1960433 : Blo 1084620 1960433 := bstep (se 2 (by rfl) ⟨735162, by rfl⟩ : syracuseStep 1960433 = 1470325) B1470325
theorem B1632755 : Blo 1084620 1632755 := bstep (se 1 (by rfl) ⟨1224566, by rfl⟩ : syracuseStep 1632755 = 2449133) B2449133
theorem B1632785 : Blo 1084620 1632785 := bstep (se 2 (by rfl) ⟨612294, by rfl⟩ : syracuseStep 1632785 = 1224589) B1224589
theorem B1632803 : Blo 1084620 1632803 := bstep (se 1 (by rfl) ⟨1224602, by rfl⟩ : syracuseStep 1632803 = 2449205) B2449205
theorem B1632833 : Blo 1084620 1632833 := bstep (se 2 (by rfl) ⟨612312, by rfl⟩ : syracuseStep 1632833 = 1224625) B1224625
theorem B2091587 : Blo 1084620 2091587 := bstep (se 1 (by rfl) ⟨1568690, by rfl⟩ : syracuseStep 2091587 = 3137381) B3137381
theorem B1469011 : Blo 1084620 1469011 := bstep (se 1 (by rfl) ⟨1101758, by rfl⟩ : syracuseStep 1469011 = 2203517) B2203517
theorem B1632851 : Blo 1084620 1632851 := bstep (se 1 (by rfl) ⟨1224638, by rfl⟩ : syracuseStep 1632851 = 2449277) B2449277
theorem B3664493 : Blo 1084620 3664493 := bstep (se 3 (by rfl) ⟨687092, by rfl⟩ : syracuseStep 3664493 = 1374185) B1374185
theorem B2746993 : Blo 1084620 2746993 := bstep (se 2 (by rfl) ⟨1030122, by rfl⟩ : syracuseStep 2746993 = 2060245) B2060245
theorem B1632881 : Blo 1084620 1632881 := bstep (se 2 (by rfl) ⟨612330, by rfl⟩ : syracuseStep 1632881 = 1224661) B1224661
theorem B1632899 : Blo 1084620 1632899 := bstep (se 1 (by rfl) ⟨1224674, by rfl⟩ : syracuseStep 1632899 = 2449349) B2449349
theorem B6187661 : Blo 1084620 6187661 := bstep (se 3 (by rfl) ⟨1160186, by rfl⟩ : syracuseStep 6187661 = 2320373) B2320373
theorem B1632929 : Blo 1084620 1632929 := bstep (se 2 (by rfl) ⟨612348, by rfl⟩ : syracuseStep 1632929 = 1224697) B1224697
theorem B3664547 : Blo 1084620 3664547 := bstep (se 1 (by rfl) ⟨2748410, by rfl⟩ : syracuseStep 3664547 = 5496821) B5496821
theorem B1239715 : Blo 1084620 1239715 := bstep (se 1 (by rfl) ⟨929786, by rfl⟩ : syracuseStep 1239715 = 1859573) B1859573
theorem B2059121 : Blo 1084620 2059121 := bstep (se 2 (by rfl) ⟨772170, by rfl⟩ : syracuseStep 2059121 = 1544341) B1544341
theorem B2747267 : Blo 1084620 2747267 := bstep (se 1 (by rfl) ⟨2060450, by rfl⟩ : syracuseStep 2747267 = 4120901) B4120901
theorem B3664817 : Blo 1084620 3664817 := bstep (se 2 (by rfl) ⟨1374306, by rfl⟩ : syracuseStep 3664817 = 2748613) B2748613
theorem B4123619 : Blo 1084620 4123619 := bstep (se 1 (by rfl) ⟨3092714, by rfl⟩ : syracuseStep 4123619 = 6185429) B6185429
theorem B2747459 : Blo 1084620 2747459 := bstep (se 1 (by rfl) ⟨2060594, by rfl⟩ : syracuseStep 2747459 = 4121189) B4121189
theorem B3304547 : Blo 1084620 3304547 := bstep (se 1 (by rfl) ⟨2478410, by rfl⟩ : syracuseStep 3304547 = 4956821) B4956821
theorem B7433477 : Blo 1084620 7433477 := bstep (se 4 (by rfl) ⟨696888, by rfl⟩ : syracuseStep 7433477 = 1393777) B1393777
theorem B1830323 : Blo 1084620 1830323 := bstep (se 1 (by rfl) ⟨1372742, by rfl⟩ : syracuseStep 1830323 = 2745485) B2745485
theorem B3665357 : Blo 1084620 3665357 := bstep (se 3 (by rfl) ⟨687254, by rfl⟩ : syracuseStep 3665357 = 1374509) B1374509
theorem B2092529 : Blo 1084620 2092529 := bstep (se 2 (by rfl) ⟨784698, by rfl⟩ : syracuseStep 2092529 = 1569397) B1569397
theorem B3665411 : Blo 1084620 3665411 := bstep (se 1 (by rfl) ⟨2749058, by rfl⟩ : syracuseStep 3665411 = 5498117) B5498117
theorem B6975011 : Blo 1084620 6975011 := bstep (se 1 (by rfl) ⟨5231258, by rfl⟩ : syracuseStep 6975011 = 10462517) B10462517
theorem B1830451 : Blo 1084620 1830451 := bstep (se 1 (by rfl) ⟨1372838, by rfl⟩ : syracuseStep 1830451 = 2745677) B2745677
theorem B2059843 : Blo 1084620 2059843 := bstep (se 1 (by rfl) ⟨1544882, by rfl⟩ : syracuseStep 2059843 = 3089765) B3089765
theorem B1830593 : Blo 1084620 1830593 := bstep (se 2 (by rfl) ⟨686472, by rfl⟩ : syracuseStep 1830593 = 1372945) B1372945
theorem B3665681 : Blo 1084620 3665681 := bstep (se 2 (by rfl) ⟨1374630, by rfl⟩ : syracuseStep 3665681 = 2749261) B2749261
theorem B1830721 : Blo 1084620 1830721 := bstep (se 2 (by rfl) ⟨686520, by rfl⟩ : syracuseStep 1830721 = 1373041) B1373041
theorem B1830755 : Blo 1084620 1830755 := bstep (se 1 (by rfl) ⟨1373066, by rfl⟩ : syracuseStep 1830755 = 2746133) B2746133
theorem B4124621 : Blo 1084620 4124621 := bstep (se 3 (by rfl) ⟨773366, by rfl⟩ : syracuseStep 4124621 = 1546733) B1546733
theorem B1830883 : Blo 1084620 1830883 := bstep (se 1 (by rfl) ⟨1373162, by rfl⟩ : syracuseStep 1830883 = 2746325) B2746325
theorem B2748401 : Blo 1084620 2748401 := bstep (se 2 (by rfl) ⟨1030650, by rfl⟩ : syracuseStep 2748401 = 2061301) B2061301
theorem B2060291 : Blo 1084620 2060291 := bstep (se 1 (by rfl) ⟨1545218, by rfl⟩ : syracuseStep 2060291 = 3090437) B3090437
theorem B2748451 : Blo 1084620 2748451 := bstep (se 1 (by rfl) ⟨2061338, by rfl⟩ : syracuseStep 2748451 = 4122677) B4122677
theorem B1831025 : Blo 1084620 1831025 := bstep (se 2 (by rfl) ⟨686634, by rfl⟩ : syracuseStep 1831025 = 1373269) B1373269
theorem B2748593 : Blo 1084620 2748593 := bstep (se 2 (by rfl) ⟨1030722, by rfl⟩ : syracuseStep 2748593 = 2061445) B2061445
theorem B8810693 : Blo 1084620 8810693 := bstep (se 4 (by rfl) ⟨826002, by rfl⟩ : syracuseStep 8810693 = 1652005) B1652005
theorem B7827683 : Blo 1084620 7827683 := bstep (se 1 (by rfl) ⟨5870762, by rfl⟩ : syracuseStep 7827683 = 11741525) B11741525
theorem B1831153 : Blo 1084620 1831153 := bstep (se 2 (by rfl) ⟨686682, by rfl⟩ : syracuseStep 1831153 = 1373365) B1373365
theorem B1831187 : Blo 1084620 1831187 := bstep (se 1 (by rfl) ⟨1373390, by rfl⟩ : syracuseStep 1831187 = 2746781) B2746781
theorem B2060579 : Blo 1084620 2060579 := bstep (se 1 (by rfl) ⟨1545434, by rfl⟩ : syracuseStep 2060579 = 3090869) B3090869
theorem B3666221 : Blo 1084620 3666221 := bstep (se 3 (by rfl) ⟨687416, by rfl⟩ : syracuseStep 3666221 = 1374833) B1374833
theorem B3666275 : Blo 1084620 3666275 := bstep (se 1 (by rfl) ⟨2749706, by rfl⟩ : syracuseStep 3666275 = 5499413) B5499413
theorem B1831315 : Blo 1084620 1831315 := bstep (se 1 (by rfl) ⟨1373486, by rfl⟩ : syracuseStep 1831315 = 2746973) B2746973
theorem B1831457 : Blo 1084620 1831457 := bstep (se 2 (by rfl) ⟨686796, by rfl⟩ : syracuseStep 1831457 = 1373593) B1373593
theorem B9269873 : Blo 1084620 9269873 := bstep (se 2 (by rfl) ⟨3476202, by rfl⟩ : syracuseStep 9269873 = 6952405) B6952405
theorem B3666545 : Blo 1084620 3666545 := bstep (se 2 (by rfl) ⟨1374954, by rfl⟩ : syracuseStep 3666545 = 2749909) B2749909
theorem B2683523 : Blo 1084620 2683523 := bstep (se 1 (by rfl) ⟨2012642, by rfl⟩ : syracuseStep 2683523 = 4025285) B4025285
theorem B1831585 : Blo 1084620 1831585 := bstep (se 2 (by rfl) ⟨686844, by rfl⟩ : syracuseStep 1831585 = 1373689) B1373689
theorem B1831619 : Blo 1084620 1831619 := bstep (se 1 (by rfl) ⟨1373714, by rfl⟩ : syracuseStep 1831619 = 2747429) B2747429
theorem B4649699 : Blo 1084620 4649699 := bstep (se 1 (by rfl) ⟨3487274, by rfl⟩ : syracuseStep 4649699 = 6974549) B6974549
theorem B5501681 : Blo 1084620 5501681 := bstep (se 2 (by rfl) ⟨2063130, by rfl⟩ : syracuseStep 5501681 = 4126261) B4126261
theorem B1831747 : Blo 1084620 1831747 := bstep (se 1 (by rfl) ⟨1373810, by rfl⟩ : syracuseStep 1831747 = 2747621) B2747621
theorem B1307459 : Blo 1084620 1307459 := bstep (se 1 (by rfl) ⟨980594, by rfl⟩ : syracuseStep 1307459 = 1961189) B1961189
theorem B1307507 : Blo 1084620 1307507 := bstep (se 1 (by rfl) ⟨980630, by rfl⟩ : syracuseStep 1307507 = 1961261) B1961261
theorem B1373107 : Blo 1084620 1373107 := bstep (se 1 (by rfl) ⟨1029830, by rfl⟩ : syracuseStep 1373107 = 2059661) B2059661
theorem B1831889 : Blo 1084620 1831889 := bstep (se 2 (by rfl) ⟨686958, by rfl⟩ : syracuseStep 1831889 = 1373917) B1373917
theorem B1373203 : Blo 1084620 1373203 := bstep (se 1 (by rfl) ⟨1029902, by rfl⟩ : syracuseStep 1373203 = 2059805) B2059805
theorem B1832017 : Blo 1084620 1832017 := bstep (se 2 (by rfl) ⟨687006, by rfl⟩ : syracuseStep 1832017 = 1374013) B1374013
theorem B1832051 : Blo 1084620 1832051 := bstep (se 1 (by rfl) ⟨1374038, by rfl⟩ : syracuseStep 1832051 = 2748077) B2748077
theorem B3667085 : Blo 1084620 3667085 := bstep (se 3 (by rfl) ⟨687578, by rfl⟩ : syracuseStep 3667085 = 1375157) B1375157
theorem B2749585 : Blo 1084620 2749585 := bstep (se 2 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 2749585 = 2062189) B2062189
theorem B3667139 : Blo 1084620 3667139 := bstep (se 1 (by rfl) ⟨2750354, by rfl⟩ : syracuseStep 3667139 = 5500709) B5500709
theorem B2061521 : Blo 1084620 2061521 := bstep (se 2 (by rfl) ⟨773070, by rfl⟩ : syracuseStep 2061521 = 1546141) B1546141
theorem B1832179 : Blo 1084620 1832179 := bstep (se 1 (by rfl) ⟨1374134, by rfl⟩ : syracuseStep 1832179 = 2748269) B2748269
theorem B1832321 : Blo 1084620 1832321 := bstep (se 2 (by rfl) ⟨687120, by rfl⟩ : syracuseStep 1832321 = 1374241) B1374241
theorem B2749859 : Blo 1084620 2749859 := bstep (se 1 (by rfl) ⟨2062394, by rfl⟩ : syracuseStep 2749859 = 4124789) B4124789
theorem B1766819 : Blo 1084620 1766819 := bstep (se 1 (by rfl) ⟨1325114, by rfl⟩ : syracuseStep 1766819 = 2650229) B2650229
theorem B3667409 : Blo 1084620 3667409 := bstep (se 2 (by rfl) ⟨1375278, by rfl⟩ : syracuseStep 3667409 = 2750557) B2750557
theorem B6190577 : Blo 1084620 6190577 := bstep (se 2 (by rfl) ⟨2321466, by rfl⟩ : syracuseStep 6190577 = 4642933) B4642933
theorem B1832449 : Blo 1084620 1832449 := bstep (se 2 (by rfl) ⟨687168, by rfl⟩ : syracuseStep 1832449 = 1374337) B1374337
theorem B1373699 : Blo 1084620 1373699 := bstep (se 1 (by rfl) ⟨1030274, by rfl⟩ : syracuseStep 1373699 = 2060549) B2060549
theorem B1832483 : Blo 1084620 1832483 := bstep (se 1 (by rfl) ⟨1374362, by rfl⟩ : syracuseStep 1832483 = 2748725) B2748725
theorem B1177139 : Blo 1084620 1177139 := bstep (se 1 (by rfl) ⟨882854, by rfl⟩ : syracuseStep 1177139 = 1765709) B1765709
theorem B2750051 : Blo 1084620 2750051 := bstep (se 1 (by rfl) ⟨2062538, by rfl⟩ : syracuseStep 2750051 = 4125077) B4125077
theorem B6616675 : Blo 1084620 6616675 := bstep (se 1 (by rfl) ⟨4962506, by rfl⟩ : syracuseStep 6616675 = 9925013) B9925013
theorem B1832611 : Blo 1084620 1832611 := bstep (se 1 (by rfl) ⟨1374458, by rfl⟩ : syracuseStep 1832611 = 2748917) B2748917
theorem B2324227 : Blo 1084620 2324227 := bstep (se 1 (by rfl) ⟨1743170, by rfl⟩ : syracuseStep 2324227 = 3486341) B3486341
theorem B1832753 : Blo 1084620 1832753 := bstep (se 2 (by rfl) ⟨687282, by rfl⟩ : syracuseStep 1832753 = 1374565) B1374565
theorem B1832881 : Blo 1084620 1832881 := bstep (se 2 (by rfl) ⟨687330, by rfl⟩ : syracuseStep 1832881 = 1374661) B1374661
theorem B1832915 : Blo 1084620 1832915 := bstep (se 1 (by rfl) ⟨1374686, by rfl⟩ : syracuseStep 1832915 = 2749373) B2749373
theorem B8353763 : Blo 1084620 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B3667949 : Blo 1084620 3667949 := bstep (se 3 (by rfl) ⟨687740, by rfl⟩ : syracuseStep 3667949 = 1375481) B1375481
theorem B4126733 : Blo 1084620 4126733 := bstep (se 3 (by rfl) ⟨773762, by rfl⟩ : syracuseStep 4126733 = 1547525) B1547525
theorem B3668003 : Blo 1084620 3668003 := bstep (se 1 (by rfl) ⟨2751002, by rfl⟩ : syracuseStep 3668003 = 5502005) B5502005
theorem B2062417 : Blo 1084620 2062417 := bstep (se 2 (by rfl) ⟨773406, by rfl⟩ : syracuseStep 2062417 = 1546813) B1546813
theorem B1833043 : Blo 1084620 1833043 := bstep (se 1 (by rfl) ⟨1374782, by rfl⟩ : syracuseStep 1833043 = 2749565) B2749565
theorem B13924493 : Blo 1084620 13924493 := bstep (se 3 (by rfl) ⟨2610842, by rfl⟩ : syracuseStep 13924493 = 5221685) B5221685
theorem B5503139 : Blo 1084620 5503139 := bstep (se 1 (by rfl) ⟨4127354, by rfl⟩ : syracuseStep 5503139 = 8254709) B8254709
theorem B1374403 : Blo 1084620 1374403 := bstep (se 1 (by rfl) ⟨1030802, by rfl⟩ : syracuseStep 1374403 = 2061605) B2061605
theorem B1833185 : Blo 1084620 1833185 := bstep (se 2 (by rfl) ⟨687444, by rfl⟩ : syracuseStep 1833185 = 1374889) B1374889
theorem B2062577 : Blo 1084620 2062577 := bstep (se 2 (by rfl) ⟨773466, by rfl⟩ : syracuseStep 2062577 = 1546933) B1546933
theorem B1374499 : Blo 1084620 1374499 := bstep (se 1 (by rfl) ⟨1030874, by rfl⟩ : syracuseStep 1374499 = 2061749) B2061749
theorem B3668273 : Blo 1084620 3668273 := bstep (se 2 (by rfl) ⟨1375602, by rfl⟩ : syracuseStep 3668273 = 2751205) B2751205
theorem B5863757 : Blo 1084620 5863757 := bstep (se 3 (by rfl) ⟨1099454, by rfl⟩ : syracuseStep 5863757 = 2198909) B2198909
theorem B1833313 : Blo 1084620 1833313 := bstep (se 2 (by rfl) ⟨687492, by rfl⟩ : syracuseStep 1833313 = 1374985) B1374985
theorem B1833347 : Blo 1084620 1833347 := bstep (se 1 (by rfl) ⟨1375010, by rfl⟩ : syracuseStep 1833347 = 2750021) B2750021
theorem B5863843 : Blo 1084620 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B1833475 : Blo 1084620 1833475 := bstep (se 1 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 1833475 = 2750213) B2750213
theorem B2750993 : Blo 1084620 2750993 := bstep (se 2 (by rfl) ⟨1031622, by rfl⟩ : syracuseStep 2750993 = 2063245) B2063245
theorem B2751043 : Blo 1084620 2751043 := bstep (se 1 (by rfl) ⟨2063282, by rfl⟩ : syracuseStep 2751043 = 4126565) B4126565
theorem B2062979 : Blo 1084620 2062979 := bstep (se 1 (by rfl) ⟨1547234, by rfl⟩ : syracuseStep 2062979 = 3094469) B3094469
theorem B3766925 : Blo 1084620 3766925 := bstep (se 3 (by rfl) ⟨706298, by rfl⟩ : syracuseStep 3766925 = 1412597) B1412597
theorem B1833617 : Blo 1084620 1833617 := bstep (se 2 (by rfl) ⟨687606, by rfl⟩ : syracuseStep 1833617 = 1375213) B1375213
theorem B2751185 : Blo 1084620 2751185 := bstep (se 2 (by rfl) ⟨1031694, by rfl⟩ : syracuseStep 2751185 = 2063389) B2063389
theorem B1833745 : Blo 1084620 1833745 := bstep (se 2 (by rfl) ⟨687654, by rfl⟩ : syracuseStep 1833745 = 1375309) B1375309
theorem B1374995 : Blo 1084620 1374995 := bstep (se 1 (by rfl) ⟨1031246, by rfl⟩ : syracuseStep 1374995 = 2062493) B2062493
theorem B4127537 : Blo 1084620 4127537 := bstep (se 2 (by rfl) ⟨1547826, by rfl⟩ : syracuseStep 4127537 = 3095653) B3095653
theorem B1833779 : Blo 1084620 1833779 := bstep (se 1 (by rfl) ⟨1375334, by rfl⟩ : syracuseStep 1833779 = 2750669) B2750669
theorem B3668813 : Blo 1084620 3668813 := bstep (se 3 (by rfl) ⟨687902, by rfl⟩ : syracuseStep 3668813 = 1375805) B1375805
theorem B3668867 : Blo 1084620 3668867 := bstep (se 1 (by rfl) ⟨2751650, by rfl⟩ : syracuseStep 3668867 = 5503301) B5503301
theorem B6192035 : Blo 1084620 6192035 := bstep (se 1 (by rfl) ⟨4644026, by rfl⟩ : syracuseStep 6192035 = 9288053) B9288053
theorem B1833907 : Blo 1084620 1833907 := bstep (se 1 (by rfl) ⟨1375430, by rfl⟩ : syracuseStep 1833907 = 2750861) B2750861
theorem B5503949 : Blo 1084620 5503949 := bstep (se 3 (by rfl) ⟨1031990, by rfl⟩ : syracuseStep 5503949 = 2063981) B2063981
theorem B9272333 : Blo 1084620 9272333 := bstep (se 3 (by rfl) ⟨1738562, by rfl⟩ : syracuseStep 9272333 = 3477125) B3477125
theorem B1834049 : Blo 1084620 1834049 := bstep (se 2 (by rfl) ⟨687768, by rfl⟩ : syracuseStep 1834049 = 1375537) B1375537
theorem B8256653 : Blo 1084620 8256653 := bstep (se 3 (by rfl) ⟨1548122, by rfl⟩ : syracuseStep 8256653 = 3096245) B3096245
theorem B3669137 : Blo 1084620 3669137 := bstep (se 2 (by rfl) ⟨1375926, by rfl⟩ : syracuseStep 3669137 = 2751853) B2751853
theorem B7044259 : Blo 1084620 7044259 := bstep (se 1 (by rfl) ⟨5283194, by rfl⟩ : syracuseStep 7044259 = 10566389) B10566389
theorem B1834177 : Blo 1084620 1834177 := bstep (se 2 (by rfl) ⟨687816, by rfl⟩ : syracuseStep 1834177 = 1375633) B1375633
theorem B1834211 : Blo 1084620 1834211 := bstep (se 1 (by rfl) ⟨1375658, by rfl⟩ : syracuseStep 1834211 = 2751317) B2751317
theorem B3767555 : Blo 1084620 3767555 := bstep (se 1 (by rfl) ⟨2825666, by rfl⟩ : syracuseStep 3767555 = 5651333) B5651333
theorem B1834339 : Blo 1084620 1834339 := bstep (se 1 (by rfl) ⟨1375754, by rfl⟩ : syracuseStep 1834339 = 2751509) B2751509
theorem B5864881 : Blo 1084620 5864881 := bstep (se 2 (by rfl) ⟨2199330, by rfl⟩ : syracuseStep 5864881 = 4398661) B4398661
theorem B4128205 : Blo 1084620 4128205 := bstep (se 3 (by rfl) ⟨774038, by rfl⟩ : syracuseStep 4128205 = 1548077) B1548077
theorem B1375699 : Blo 1084620 1375699 := bstep (se 1 (by rfl) ⟨1031774, by rfl⟩ : syracuseStep 1375699 = 2063549) B2063549
theorem B1834481 : Blo 1084620 1834481 := bstep (se 2 (by rfl) ⟨687930, by rfl⟩ : syracuseStep 1834481 = 1375861) B1375861
theorem B2063875 : Blo 1084620 2063875 := bstep (se 1 (by rfl) ⟨1547906, by rfl⟩ : syracuseStep 2063875 = 3095813) B3095813
theorem B1375795 : Blo 1084620 1375795 := bstep (se 1 (by rfl) ⟨1031846, by rfl⟩ : syracuseStep 1375795 = 2063693) B2063693
theorem B1834609 : Blo 1084620 1834609 := bstep (se 2 (by rfl) ⟨687978, by rfl⟩ : syracuseStep 1834609 = 1375957) B1375957
theorem B1834643 : Blo 1084620 1834643 := bstep (se 1 (by rfl) ⟨1375982, by rfl⟩ : syracuseStep 1834643 = 2751965) B2751965
theorem B2064035 : Blo 1084620 2064035 := bstep (se 1 (by rfl) ⟨1548026, by rfl⟩ : syracuseStep 2064035 = 3096053) B3096053
theorem B3669677 : Blo 1084620 3669677 := bstep (se 3 (by rfl) ⟨688064, by rfl⟩ : syracuseStep 3669677 = 1376129) B1376129
theorem B2752177 : Blo 1084620 2752177 := bstep (se 2 (by rfl) ⟨1032066, by rfl⟩ : syracuseStep 2752177 = 2064133) B2064133
theorem B3669731 : Blo 1084620 3669731 := bstep (se 1 (by rfl) ⟨2752298, by rfl⟩ : syracuseStep 3669731 = 5504597) B5504597
theorem B1834771 : Blo 1084620 1834771 := bstep (se 1 (by rfl) ⟨1376078, by rfl⟩ : syracuseStep 1834771 = 2752157) B2752157
theorem B2981681 : Blo 1084620 2981681 := bstep (se 2 (by rfl) ⟨1118130, by rfl⟩ : syracuseStep 2981681 = 2236261) B2236261
theorem B6193037 : Blo 1084620 6193037 := bstep (se 3 (by rfl) ⟨1161194, by rfl⟩ : syracuseStep 6193037 = 2322389) B2322389
theorem B1834913 : Blo 1084620 1834913 := bstep (se 2 (by rfl) ⟨688092, by rfl⟩ : syracuseStep 1834913 = 1376185) B1376185
theorem B2752451 : Blo 1084620 2752451 := bstep (se 1 (by rfl) ⟨2064338, by rfl⟩ : syracuseStep 2752451 = 4128677) B4128677
theorem B3670001 : Blo 1084620 3670001 := bstep (se 2 (by rfl) ⟨1376250, by rfl⟩ : syracuseStep 3670001 = 2752501) B2752501
theorem B1835095 : Blo 1084620 1835095 := bstep (se 1 (by rfl) ⟨1376321, by rfl⟩ : syracuseStep 1835095 = 2752643) B2752643
theorem B3670109 : Blo 1084620 3670109 := bstep (se 3 (by rfl) ⟨688145, by rfl⟩ : syracuseStep 3670109 = 1376291) B1376291
theorem B2752663 : Blo 1084620 2752663 := bstep (se 1 (by rfl) ⟨2064497, by rfl⟩ : syracuseStep 2752663 = 4128995) B4128995
theorem B2064665 : Blo 1084620 2064665 := bstep (se 2 (by rfl) ⟨774249, by rfl⟩ : syracuseStep 2064665 = 1548499) B1548499
theorem B19825073 : Blo 1084620 19825073 := bstep (se 2 (by rfl) ⟨7434402, by rfl⟩ : syracuseStep 19825073 = 14868805) B14868805
theorem B13238801 : Blo 1084620 13238801 := bstep (se 2 (by rfl) ⟨4964550, by rfl⟩ : syracuseStep 13238801 = 9929101) B9929101
theorem B10584611 : Blo 1084620 10584611 := bstep (se 1 (by rfl) ⟨7938458, by rfl⟩ : syracuseStep 10584611 = 15876917) B15876917
theorem B2753099 : Blo 1084620 2753099 := bstep (se 1 (by rfl) ⟨2064824, by rfl⟩ : syracuseStep 2753099 = 4129649) B4129649
theorem B4948573 : Blo 1084620 4948573 := bstep (se 3 (by rfl) ⟨927857, by rfl⟩ : syracuseStep 4948573 = 1855715) B1855715
theorem B20873821 : Blo 1084620 20873821 := bstep (se 3 (by rfl) ⟨3913841, by rfl⟩ : syracuseStep 20873821 = 7827683) B7827683
theorem B19104437 : Blo 1084620 19104437 := bstep (se 5 (by rfl) ⟨895520, by rfl⟩ : syracuseStep 19104437 = 1791041) B1791041
theorem B1835723 : Blo 1084620 1835723 := bstep (se 1 (by rfl) ⟨1376792, by rfl⟩ : syracuseStep 1835723 = 2753585) B2753585
theorem B1835851 : Blo 1084620 1835851 := bstep (se 1 (by rfl) ⟨1376888, by rfl⟩ : syracuseStep 1835851 = 2753777) B2753777
theorem B2261953 : Blo 1084620 2261953 := bstep (se 2 (by rfl) ⟨848232, by rfl⟩ : syracuseStep 2261953 = 1696465) B1696465
theorem B2753473 : Blo 1084620 2753473 := bstep (se 2 (by rfl) ⟨1032552, by rfl⟩ : syracuseStep 2753473 = 2065105) B2065105
theorem B1835993 : Blo 1084620 1835993 := bstep (se 2 (by rfl) ⟨688497, by rfl⟩ : syracuseStep 1835993 = 1376995) B1376995
theorem B2065409 : Blo 1084620 2065409 := bstep (se 2 (by rfl) ⟨774528, by rfl⟩ : syracuseStep 2065409 = 1549057) B1549057
theorem B1836121 : Blo 1084620 1836121 := bstep (se 2 (by rfl) ⟨688545, by rfl⟩ : syracuseStep 1836121 = 1377091) B1377091
theorem B4129937 : Blo 1084620 4129937 := bstep (se 2 (by rfl) ⟨1548726, by rfl⟩ : syracuseStep 4129937 = 3097453) B3097453
theorem B3671243 : Blo 1084620 3671243 := bstep (se 1 (by rfl) ⟨2753432, by rfl⟩ : syracuseStep 3671243 = 5506865) B5506865
theorem B2065675 : Blo 1084620 2065675 := bstep (se 1 (by rfl) ⟨1549256, by rfl⟩ : syracuseStep 2065675 = 3098513) B3098513
theorem B5506379 : Blo 1084620 5506379 := bstep (se 1 (by rfl) ⟨4129784, by rfl⟩ : syracuseStep 5506379 = 8259569) B8259569
theorem B1377739 : Blo 1084620 1377739 := bstep (se 1 (by rfl) ⟨1033304, by rfl⟩ : syracuseStep 1377739 = 2066609) B2066609
theorem B3671513 : Blo 1084620 3671513 := bstep (se 2 (by rfl) ⟨1376817, by rfl⟩ : syracuseStep 3671513 = 2753635) B2753635
theorem B2754071 : Blo 1084620 2754071 := bstep (se 1 (by rfl) ⟨2065553, by rfl⟩ : syracuseStep 2754071 = 4131107) B4131107
theorem B8947331 : Blo 1084620 8947331 := bstep (se 1 (by rfl) ⟨6710498, by rfl⟩ : syracuseStep 8947331 = 13420997) B13420997
theorem B1836695 : Blo 1084620 1836695 := bstep (se 1 (by rfl) ⟨1377521, by rfl⟩ : syracuseStep 1836695 = 2755043) B2755043
theorem B2066123 : Blo 1084620 2066123 := bstep (se 1 (by rfl) ⟨1549592, by rfl⟩ : syracuseStep 2066123 = 3099185) B3099185
theorem B1836823 : Blo 1084620 1836823 := bstep (se 1 (by rfl) ⟨1377617, by rfl⟩ : syracuseStep 1836823 = 2755235) B2755235
theorem B4130635 : Blo 1084620 4130635 := bstep (se 1 (by rfl) ⟨3097976, by rfl⟩ : syracuseStep 4130635 = 6195953) B6195953
theorem B4949849 : Blo 1084620 4949849 := bstep (se 2 (by rfl) ⟨1856193, by rfl⟩ : syracuseStep 4949849 = 3712387) B3712387
theorem B2066305 : Blo 1084620 2066305 := bstep (se 2 (by rfl) ⟨774864, by rfl⟩ : syracuseStep 2066305 = 1549729) B1549729
theorem B4130909 : Blo 1084620 4130909 := bstep (se 3 (by rfl) ⟨774545, by rfl⟩ : syracuseStep 4130909 = 1549091) B1549091
theorem B3672215 : Blo 1084620 3672215 := bstep (se 1 (by rfl) ⟨2754161, by rfl⟩ : syracuseStep 3672215 = 5508323) B5508323
theorem B2066647 : Blo 1084620 2066647 := bstep (se 1 (by rfl) ⟨1549985, by rfl⟩ : syracuseStep 2066647 = 3099971) B3099971
theorem B2754881 : Blo 1084620 2754881 := bstep (se 2 (by rfl) ⟨1033080, by rfl⟩ : syracuseStep 2754881 = 2066161) B2066161
theorem B6195635 : Blo 1084620 6195635 := bstep (se 1 (by rfl) ⟨4646726, by rfl⟩ : syracuseStep 6195635 = 9293453) B9293453
theorem B19335755 : Blo 1084620 19335755 := bstep (se 1 (by rfl) ⟨14501816, by rfl⟩ : syracuseStep 19335755 = 29003633) B29003633
theorem B3672755 : Blo 1084620 3672755 := bstep (se 1 (by rfl) ⟨2754566, by rfl⟩ : syracuseStep 3672755 = 5509133) B5509133
theorem B16714421 : Blo 1084620 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B1739531 : Blo 1084620 1739531 := bstep (se 1 (by rfl) ⟨1304648, by rfl⟩ : syracuseStep 1739531 = 2609297) B2609297
theorem B4131607 : Blo 1084620 4131607 := bstep (se 1 (by rfl) ⟨3098705, by rfl⟩ : syracuseStep 4131607 = 6197411) B6197411
theorem B2755417 : Blo 1084620 2755417 := bstep (se 2 (by rfl) ⟨1033281, by rfl⟩ : syracuseStep 2755417 = 2066563) B2066563
theorem B5868389 : Blo 1084620 5868389 := bstep (se 4 (by rfl) ⟨550161, by rfl⟩ : syracuseStep 5868389 = 1100323) B1100323
theorem B3673025 : Blo 1084620 3673025 := bstep (se 2 (by rfl) ⟨1377384, by rfl⟩ : syracuseStep 3673025 = 2754769) B2754769
theorem B5508161 : Blo 1084620 5508161 := bstep (se 2 (by rfl) ⟨2065560, by rfl⟩ : syracuseStep 5508161 = 4131121) B4131121
theorem B1084631 : Blo 1084620 1084631 := bstep (se 1 (by rfl) ⟨813473, by rfl⟩ : syracuseStep 1084631 = 1626947) B1626947
theorem B1084651 : Blo 1084620 1084651 := bstep (se 1 (by rfl) ⟨813488, by rfl⟩ : syracuseStep 1084651 = 1626977) B1626977
theorem B1084663 : Blo 1084620 1084663 := bstep (se 1 (by rfl) ⟨813497, by rfl⟩ : syracuseStep 1084663 = 1626995) B1626995
theorem B1084683 : Blo 1084620 1084683 := bstep (se 1 (by rfl) ⟨813512, by rfl⟩ : syracuseStep 1084683 = 1627025) B1627025
theorem B1084695 : Blo 1084620 1084695 := bstep (se 1 (by rfl) ⟨813521, by rfl⟩ : syracuseStep 1084695 = 1627043) B1627043
theorem B9276707 : Blo 1084620 9276707 := bstep (se 1 (by rfl) ⟨6957530, by rfl⟩ : syracuseStep 9276707 = 13915061) B13915061
theorem B1084715 : Blo 1084620 1084715 := bstep (se 1 (by rfl) ⟨813536, by rfl⟩ : syracuseStep 1084715 = 1627073) B1627073
theorem B1084727 : Blo 1084620 1084727 := bstep (se 1 (by rfl) ⟨813545, by rfl⟩ : syracuseStep 1084727 = 1627091) B1627091
theorem B1084747 : Blo 1084620 1084747 := bstep (se 1 (by rfl) ⟨813560, by rfl⟩ : syracuseStep 1084747 = 1627121) B1627121
theorem B1084759 : Blo 1084620 1084759 := bstep (se 1 (by rfl) ⟨813569, by rfl⟩ : syracuseStep 1084759 = 1627139) B1627139
theorem B13208933 : Blo 1084620 13208933 := bstep (se 4 (by rfl) ⟨1238337, by rfl⟩ : syracuseStep 13208933 = 2476675) B2476675
theorem B1084779 : Blo 1084620 1084779 := bstep (se 1 (by rfl) ⟨813584, by rfl⟩ : syracuseStep 1084779 = 1627169) B1627169
theorem B18550133 : Blo 1084620 18550133 := bstep (se 5 (by rfl) ⟨869537, by rfl⟩ : syracuseStep 18550133 = 1739075) B1739075
theorem B1084791 : Blo 1084620 1084791 := bstep (se 1 (by rfl) ⟨813593, by rfl⟩ : syracuseStep 1084791 = 1627187) B1627187
theorem B1084811 : Blo 1084620 1084811 := bstep (se 1 (by rfl) ⟨813608, by rfl⟩ : syracuseStep 1084811 = 1627217) B1627217
theorem B2198935 : Blo 1084620 2198935 := bstep (se 1 (by rfl) ⟨1649201, by rfl⟩ : syracuseStep 2198935 = 3298403) B3298403
theorem B1084823 : Blo 1084620 1084823 := bstep (se 1 (by rfl) ⟨813617, by rfl⟩ : syracuseStep 1084823 = 1627235) B1627235
theorem B1084843 : Blo 1084620 1084843 := bstep (se 1 (by rfl) ⟨813632, by rfl⟩ : syracuseStep 1084843 = 1627265) B1627265
theorem B1084855 : Blo 1084620 1084855 := bstep (se 1 (by rfl) ⟨813641, by rfl⟩ : syracuseStep 1084855 = 1627283) B1627283
theorem B1084875 : Blo 1084620 1084875 := bstep (se 1 (by rfl) ⟨813656, by rfl⟩ : syracuseStep 1084875 = 1627313) B1627313
theorem B2198999 : Blo 1084620 2198999 := bstep (se 1 (by rfl) ⟨1649249, by rfl⟩ : syracuseStep 2198999 = 3298499) B3298499
theorem B1084887 : Blo 1084620 1084887 := bstep (se 1 (by rfl) ⟨813665, by rfl⟩ : syracuseStep 1084887 = 1627331) B1627331
theorem B3673565 : Blo 1084620 3673565 := bstep (se 3 (by rfl) ⟨688793, by rfl⟩ : syracuseStep 3673565 = 1377587) B1377587
theorem B1084907 : Blo 1084620 1084907 := bstep (se 1 (by rfl) ⟨813680, by rfl⟩ : syracuseStep 1084907 = 1627361) B1627361
theorem B1084919 : Blo 1084620 1084919 := bstep (se 1 (by rfl) ⟨813689, by rfl⟩ : syracuseStep 1084919 = 1627379) B1627379
theorem B1084939 : Blo 1084620 1084939 := bstep (se 1 (by rfl) ⟨813704, by rfl⟩ : syracuseStep 1084939 = 1627409) B1627409
theorem B1084951 : Blo 1084620 1084951 := bstep (se 1 (by rfl) ⟨813713, by rfl⟩ : syracuseStep 1084951 = 1627427) B1627427
theorem B1084971 : Blo 1084620 1084971 := bstep (se 1 (by rfl) ⟨813728, by rfl⟩ : syracuseStep 1084971 = 1627457) B1627457
theorem B4132397 : Blo 1084620 4132397 := bstep (se 3 (by rfl) ⟨774824, by rfl⟩ : syracuseStep 4132397 = 1549649) B1549649
theorem B1084983 : Blo 1084620 1084983 := bstep (se 1 (by rfl) ⟨813737, by rfl⟩ : syracuseStep 1084983 = 1627475) B1627475
theorem B1085003 : Blo 1084620 1085003 := bstep (se 1 (by rfl) ⟨813752, by rfl⟩ : syracuseStep 1085003 = 1627505) B1627505
theorem B1085015 : Blo 1084620 1085015 := bstep (se 1 (by rfl) ⟨813761, by rfl⟩ : syracuseStep 1085015 = 1627523) B1627523
theorem B1085035 : Blo 1084620 1085035 := bstep (se 1 (by rfl) ⟨813776, by rfl⟩ : syracuseStep 1085035 = 1627553) B1627553
theorem B1085047 : Blo 1084620 1085047 := bstep (se 1 (by rfl) ⟨813785, by rfl⟩ : syracuseStep 1085047 = 1627571) B1627571
theorem B1085067 : Blo 1084620 1085067 := bstep (se 1 (by rfl) ⟨813800, by rfl⟩ : syracuseStep 1085067 = 1627601) B1627601
theorem B1085079 : Blo 1084620 1085079 := bstep (se 1 (by rfl) ⟨813809, by rfl⟩ : syracuseStep 1085079 = 1627619) B1627619
theorem B1085099 : Blo 1084620 1085099 := bstep (se 1 (by rfl) ⟨813824, by rfl⟩ : syracuseStep 1085099 = 1627649) B1627649
theorem B1085111 : Blo 1084620 1085111 := bstep (se 1 (by rfl) ⟨813833, by rfl⟩ : syracuseStep 1085111 = 1627667) B1627667
theorem B1085131 : Blo 1084620 1085131 := bstep (se 1 (by rfl) ⟨813848, by rfl⟩ : syracuseStep 1085131 = 1627697) B1627697
theorem B1085143 : Blo 1084620 1085143 := bstep (se 1 (by rfl) ⟨813857, by rfl⟩ : syracuseStep 1085143 = 1627715) B1627715
theorem B1085163 : Blo 1084620 1085163 := bstep (se 1 (by rfl) ⟨813872, by rfl⟩ : syracuseStep 1085163 = 1627745) B1627745
theorem B1085175 : Blo 1084620 1085175 := bstep (se 1 (by rfl) ⟨813881, by rfl⟩ : syracuseStep 1085175 = 1627763) B1627763
theorem B1085195 : Blo 1084620 1085195 := bstep (se 1 (by rfl) ⟨813896, by rfl⟩ : syracuseStep 1085195 = 1627793) B1627793
theorem B1085207 : Blo 1084620 1085207 := bstep (se 1 (by rfl) ⟨813905, by rfl⟩ : syracuseStep 1085207 = 1627811) B1627811
theorem B1085227 : Blo 1084620 1085227 := bstep (se 1 (by rfl) ⟨813920, by rfl⟩ : syracuseStep 1085227 = 1627841) B1627841
theorem B4951853 : Blo 1084620 4951853 := bstep (se 3 (by rfl) ⟨928472, by rfl⟩ : syracuseStep 4951853 = 1856945) B1856945
theorem B1085239 : Blo 1084620 1085239 := bstep (se 1 (by rfl) ⟨813929, by rfl⟩ : syracuseStep 1085239 = 1627859) B1627859
theorem B1085259 : Blo 1084620 1085259 := bstep (se 1 (by rfl) ⟨813944, by rfl⟩ : syracuseStep 1085259 = 1627889) B1627889
theorem B1085271 : Blo 1084620 1085271 := bstep (se 1 (by rfl) ⟨813953, by rfl⟩ : syracuseStep 1085271 = 1627907) B1627907
theorem B6197093 : Blo 1084620 6197093 := bstep (se 4 (by rfl) ⟨580977, by rfl⟩ : syracuseStep 6197093 = 1161955) B1161955
theorem B1085291 : Blo 1084620 1085291 := bstep (se 1 (by rfl) ⟨813968, by rfl⟩ : syracuseStep 1085291 = 1627937) B1627937
theorem B1085303 : Blo 1084620 1085303 := bstep (se 1 (by rfl) ⟨813977, by rfl⟩ : syracuseStep 1085303 = 1627955) B1627955
theorem B1085323 : Blo 1084620 1085323 := bstep (se 1 (by rfl) ⟨813992, by rfl⟩ : syracuseStep 1085323 = 1627985) B1627985
theorem B1085335 : Blo 1084620 1085335 := bstep (se 1 (by rfl) ⟨814001, by rfl⟩ : syracuseStep 1085335 = 1628003) B1628003
theorem B1085355 : Blo 1084620 1085355 := bstep (se 1 (by rfl) ⟨814016, by rfl⟩ : syracuseStep 1085355 = 1628033) B1628033
theorem B1085367 : Blo 1084620 1085367 := bstep (se 1 (by rfl) ⟨814025, by rfl⟩ : syracuseStep 1085367 = 1628051) B1628051
theorem B1085387 : Blo 1084620 1085387 := bstep (se 1 (by rfl) ⟨814040, by rfl⟩ : syracuseStep 1085387 = 1628081) B1628081
theorem B1085399 : Blo 1084620 1085399 := bstep (se 1 (by rfl) ⟨814049, by rfl⟩ : syracuseStep 1085399 = 1628099) B1628099
theorem B1085419 : Blo 1084620 1085419 := bstep (se 1 (by rfl) ⟨814064, by rfl⟩ : syracuseStep 1085419 = 1628129) B1628129
theorem B1085431 : Blo 1084620 1085431 := bstep (se 1 (by rfl) ⟨814073, by rfl⟩ : syracuseStep 1085431 = 1628147) B1628147
theorem B1085451 : Blo 1084620 1085451 := bstep (se 1 (by rfl) ⟨814088, by rfl⟩ : syracuseStep 1085451 = 1628177) B1628177
theorem B1085463 : Blo 1084620 1085463 := bstep (se 1 (by rfl) ⟨814097, by rfl⟩ : syracuseStep 1085463 = 1628195) B1628195
theorem B1085483 : Blo 1084620 1085483 := bstep (se 1 (by rfl) ⟨814112, by rfl⟩ : syracuseStep 1085483 = 1628225) B1628225
theorem B1085495 : Blo 1084620 1085495 := bstep (se 1 (by rfl) ⟨814121, by rfl⟩ : syracuseStep 1085495 = 1628243) B1628243
theorem B1085515 : Blo 1084620 1085515 := bstep (se 1 (by rfl) ⟨814136, by rfl⟩ : syracuseStep 1085515 = 1628273) B1628273
theorem B1085527 : Blo 1084620 1085527 := bstep (se 1 (by rfl) ⟨814145, by rfl⟩ : syracuseStep 1085527 = 1628291) B1628291
theorem B1085547 : Blo 1084620 1085547 := bstep (se 1 (by rfl) ⟨814160, by rfl⟩ : syracuseStep 1085547 = 1628321) B1628321
theorem B1085559 : Blo 1084620 1085559 := bstep (se 1 (by rfl) ⟨814169, by rfl⟩ : syracuseStep 1085559 = 1628339) B1628339
theorem B1085579 : Blo 1084620 1085579 := bstep (se 1 (by rfl) ⟨814184, by rfl⟩ : syracuseStep 1085579 = 1628369) B1628369
theorem B1085591 : Blo 1084620 1085591 := bstep (se 1 (by rfl) ⟨814193, by rfl⟩ : syracuseStep 1085591 = 1628387) B1628387
theorem B1085611 : Blo 1084620 1085611 := bstep (se 1 (by rfl) ⟨814208, by rfl⟩ : syracuseStep 1085611 = 1628417) B1628417
theorem B1085623 : Blo 1084620 1085623 := bstep (se 1 (by rfl) ⟨814217, by rfl⟩ : syracuseStep 1085623 = 1628435) B1628435
theorem B1085643 : Blo 1084620 1085643 := bstep (se 1 (by rfl) ⟨814232, by rfl⟩ : syracuseStep 1085643 = 1628465) B1628465
theorem B1085655 : Blo 1084620 1085655 := bstep (se 1 (by rfl) ⟨814241, by rfl⟩ : syracuseStep 1085655 = 1628483) B1628483
theorem B1085675 : Blo 1084620 1085675 := bstep (se 1 (by rfl) ⟨814256, by rfl⟩ : syracuseStep 1085675 = 1628513) B1628513
theorem B1085687 : Blo 1084620 1085687 := bstep (se 1 (by rfl) ⟨814265, by rfl⟩ : syracuseStep 1085687 = 1628531) B1628531
theorem B1085707 : Blo 1084620 1085707 := bstep (se 1 (by rfl) ⟨814280, by rfl⟩ : syracuseStep 1085707 = 1628561) B1628561
theorem B1085719 : Blo 1084620 1085719 := bstep (se 1 (by rfl) ⟨814289, by rfl⟩ : syracuseStep 1085719 = 1628579) B1628579
theorem B1085739 : Blo 1084620 1085739 := bstep (se 1 (by rfl) ⟨814304, by rfl⟩ : syracuseStep 1085739 = 1628609) B1628609
theorem B1085751 : Blo 1084620 1085751 := bstep (se 1 (by rfl) ⟨814313, by rfl⟩ : syracuseStep 1085751 = 1628627) B1628627
theorem B2199883 : Blo 1084620 2199883 := bstep (se 1 (by rfl) ⟨1649912, by rfl⟩ : syracuseStep 2199883 = 3299825) B3299825
theorem B1085771 : Blo 1084620 1085771 := bstep (se 1 (by rfl) ⟨814328, by rfl⟩ : syracuseStep 1085771 = 1628657) B1628657
theorem B1085783 : Blo 1084620 1085783 := bstep (se 1 (by rfl) ⟨814337, by rfl⟩ : syracuseStep 1085783 = 1628675) B1628675
theorem B1085803 : Blo 1084620 1085803 := bstep (se 1 (by rfl) ⟨814352, by rfl⟩ : syracuseStep 1085803 = 1628705) B1628705
theorem B1085815 : Blo 1084620 1085815 := bstep (se 1 (by rfl) ⟨814361, by rfl⟩ : syracuseStep 1085815 = 1628723) B1628723
theorem B1085835 : Blo 1084620 1085835 := bstep (se 1 (by rfl) ⟨814376, by rfl⟩ : syracuseStep 1085835 = 1628753) B1628753
theorem B1085847 : Blo 1084620 1085847 := bstep (se 1 (by rfl) ⟨814385, by rfl⟩ : syracuseStep 1085847 = 1628771) B1628771
theorem B1085867 : Blo 1084620 1085867 := bstep (se 1 (by rfl) ⟨814400, by rfl⟩ : syracuseStep 1085867 = 1628801) B1628801
theorem B6263219 : Blo 1084620 6263219 := bstep (se 1 (by rfl) ⟨4697414, by rfl⟩ : syracuseStep 6263219 = 9394829) B9394829
theorem B1085879 : Blo 1084620 1085879 := bstep (se 1 (by rfl) ⟨814409, by rfl⟩ : syracuseStep 1085879 = 1628819) B1628819
theorem B1085899 : Blo 1084620 1085899 := bstep (se 1 (by rfl) ⟨814424, by rfl⟩ : syracuseStep 1085899 = 1628849) B1628849
theorem B1085911 : Blo 1084620 1085911 := bstep (se 1 (by rfl) ⟨814433, by rfl⟩ : syracuseStep 1085911 = 1628867) B1628867
theorem B1085931 : Blo 1084620 1085931 := bstep (se 1 (by rfl) ⟨814448, by rfl⟩ : syracuseStep 1085931 = 1628897) B1628897
theorem B1085943 : Blo 1084620 1085943 := bstep (se 1 (by rfl) ⟨814457, by rfl⟩ : syracuseStep 1085943 = 1628915) B1628915
theorem B1085963 : Blo 1084620 1085963 := bstep (se 1 (by rfl) ⟨814472, by rfl⟩ : syracuseStep 1085963 = 1628945) B1628945
theorem B1085975 : Blo 1084620 1085975 := bstep (se 1 (by rfl) ⟨814481, by rfl⟩ : syracuseStep 1085975 = 1628963) B1628963
theorem B1085995 : Blo 1084620 1085995 := bstep (se 1 (by rfl) ⟨814496, by rfl⟩ : syracuseStep 1085995 = 1628993) B1628993
theorem B1086007 : Blo 1084620 1086007 := bstep (se 1 (by rfl) ⟨814505, by rfl⟩ : syracuseStep 1086007 = 1629011) B1629011
theorem B1086027 : Blo 1084620 1086027 := bstep (se 1 (by rfl) ⟨814520, by rfl⟩ : syracuseStep 1086027 = 1629041) B1629041
theorem B1086039 : Blo 1084620 1086039 := bstep (se 1 (by rfl) ⟨814529, by rfl⟩ : syracuseStep 1086039 = 1629059) B1629059
theorem B1086059 : Blo 1084620 1086059 := bstep (se 1 (by rfl) ⟨814544, by rfl⟩ : syracuseStep 1086059 = 1629089) B1629089
theorem B1086071 : Blo 1084620 1086071 := bstep (se 1 (by rfl) ⟨814553, by rfl⟩ : syracuseStep 1086071 = 1629107) B1629107
theorem B1086091 : Blo 1084620 1086091 := bstep (se 1 (by rfl) ⟨814568, by rfl⟩ : syracuseStep 1086091 = 1629137) B1629137
theorem B1086103 : Blo 1084620 1086103 := bstep (se 1 (by rfl) ⟨814577, by rfl⟩ : syracuseStep 1086103 = 1629155) B1629155
theorem B8819351 : Blo 1084620 8819351 := bstep (se 1 (by rfl) ⟨6614513, by rfl⟩ : syracuseStep 8819351 = 13229027) B13229027
theorem B1086123 : Blo 1084620 1086123 := bstep (se 1 (by rfl) ⟨814592, by rfl⟩ : syracuseStep 1086123 = 1629185) B1629185
theorem B1086135 : Blo 1084620 1086135 := bstep (se 1 (by rfl) ⟨814601, by rfl⟩ : syracuseStep 1086135 = 1629203) B1629203
theorem B1086155 : Blo 1084620 1086155 := bstep (se 1 (by rfl) ⟨814616, by rfl⟩ : syracuseStep 1086155 = 1629233) B1629233
theorem B1086167 : Blo 1084620 1086167 := bstep (se 1 (by rfl) ⟨814625, by rfl⟩ : syracuseStep 1086167 = 1629251) B1629251
theorem B1086187 : Blo 1084620 1086187 := bstep (se 1 (by rfl) ⟨814640, by rfl⟩ : syracuseStep 1086187 = 1629281) B1629281
theorem B1086199 : Blo 1084620 1086199 := bstep (se 1 (by rfl) ⟨814649, by rfl⟩ : syracuseStep 1086199 = 1629299) B1629299
theorem B1086219 : Blo 1084620 1086219 := bstep (se 1 (by rfl) ⟨814664, by rfl⟩ : syracuseStep 1086219 = 1629329) B1629329
theorem B1086231 : Blo 1084620 1086231 := bstep (se 1 (by rfl) ⟨814673, by rfl⟩ : syracuseStep 1086231 = 1629347) B1629347
theorem B1086251 : Blo 1084620 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B2265907 : Blo 1084620 2265907 := bstep (se 1 (by rfl) ⟨1699430, by rfl⟩ : syracuseStep 2265907 = 3398861) B3398861
theorem B1086263 : Blo 1084620 1086263 := bstep (se 1 (by rfl) ⟨814697, by rfl⟩ : syracuseStep 1086263 = 1629395) B1629395
theorem B1086283 : Blo 1084620 1086283 := bstep (se 1 (by rfl) ⟨814712, by rfl⟩ : syracuseStep 1086283 = 1629425) B1629425
theorem B1086295 : Blo 1084620 1086295 := bstep (se 1 (by rfl) ⟨814721, by rfl⟩ : syracuseStep 1086295 = 1629443) B1629443
theorem B1086315 : Blo 1084620 1086315 := bstep (se 1 (by rfl) ⟨814736, by rfl⟩ : syracuseStep 1086315 = 1629473) B1629473
theorem B1086327 : Blo 1084620 1086327 := bstep (se 1 (by rfl) ⟨814745, by rfl⟩ : syracuseStep 1086327 = 1629491) B1629491
theorem B1086347 : Blo 1084620 1086347 := bstep (se 1 (by rfl) ⟨814760, by rfl⟩ : syracuseStep 1086347 = 1629521) B1629521
theorem B1086359 : Blo 1084620 1086359 := bstep (se 1 (by rfl) ⟨814769, by rfl⟩ : syracuseStep 1086359 = 1629539) B1629539
theorem B1086379 : Blo 1084620 1086379 := bstep (se 1 (by rfl) ⟨814784, by rfl⟩ : syracuseStep 1086379 = 1629569) B1629569
theorem B1086391 : Blo 1084620 1086391 := bstep (se 1 (by rfl) ⟨814793, by rfl⟩ : syracuseStep 1086391 = 1629587) B1629587
theorem B1086411 : Blo 1084620 1086411 := bstep (se 1 (by rfl) ⟨814808, by rfl⟩ : syracuseStep 1086411 = 1629617) B1629617
theorem B1086423 : Blo 1084620 1086423 := bstep (se 1 (by rfl) ⟨814817, by rfl⟩ : syracuseStep 1086423 = 1629635) B1629635
theorem B5510105 : Blo 1084620 5510105 := bstep (se 2 (by rfl) ⟨2066289, by rfl⟩ : syracuseStep 5510105 = 4132579) B4132579
theorem B1086443 : Blo 1084620 1086443 := bstep (se 1 (by rfl) ⟨814832, by rfl⟩ : syracuseStep 1086443 = 1629665) B1629665
theorem B1086455 : Blo 1084620 1086455 := bstep (se 1 (by rfl) ⟨814841, by rfl⟩ : syracuseStep 1086455 = 1629683) B1629683
theorem B1086475 : Blo 1084620 1086475 := bstep (se 1 (by rfl) ⟨814856, by rfl⟩ : syracuseStep 1086475 = 1629713) B1629713
theorem B1086487 : Blo 1084620 1086487 := bstep (se 1 (by rfl) ⟨814865, by rfl⟩ : syracuseStep 1086487 = 1629731) B1629731
theorem B1086507 : Blo 1084620 1086507 := bstep (se 1 (by rfl) ⟨814880, by rfl⟩ : syracuseStep 1086507 = 1629761) B1629761
theorem B1086519 : Blo 1084620 1086519 := bstep (se 1 (by rfl) ⟨814889, by rfl⟩ : syracuseStep 1086519 = 1629779) B1629779
theorem B1086539 : Blo 1084620 1086539 := bstep (se 1 (by rfl) ⟨814904, by rfl⟩ : syracuseStep 1086539 = 1629809) B1629809
theorem B1086551 : Blo 1084620 1086551 := bstep (se 1 (by rfl) ⟨814913, by rfl⟩ : syracuseStep 1086551 = 1629827) B1629827
theorem B1086571 : Blo 1084620 1086571 := bstep (se 1 (by rfl) ⟨814928, by rfl⟩ : syracuseStep 1086571 = 1629857) B1629857
theorem B1086583 : Blo 1084620 1086583 := bstep (se 1 (by rfl) ⟨814937, by rfl⟩ : syracuseStep 1086583 = 1629875) B1629875
theorem B1545355 : Blo 1084620 1545355 := bstep (se 1 (by rfl) ⟨1159016, by rfl⟩ : syracuseStep 1545355 = 2318033) B2318033
theorem B1086603 : Blo 1084620 1086603 := bstep (se 1 (by rfl) ⟨814952, by rfl⟩ : syracuseStep 1086603 = 1629905) B1629905
theorem B13210775 : Blo 1084620 13210775 := bstep (se 1 (by rfl) ⟨9908081, by rfl⟩ : syracuseStep 13210775 = 19816163) B19816163
theorem B1086615 : Blo 1084620 1086615 := bstep (se 1 (by rfl) ⟨814961, by rfl⟩ : syracuseStep 1086615 = 1629923) B1629923
theorem B1086635 : Blo 1084620 1086635 := bstep (se 1 (by rfl) ⟨814976, by rfl⟩ : syracuseStep 1086635 = 1629953) B1629953
theorem B1086647 : Blo 1084620 1086647 := bstep (se 1 (by rfl) ⟨814985, by rfl⟩ : syracuseStep 1086647 = 1629971) B1629971
theorem B1086667 : Blo 1084620 1086667 := bstep (se 1 (by rfl) ⟨815000, by rfl⟩ : syracuseStep 1086667 = 1630001) B1630001
theorem B1086679 : Blo 1084620 1086679 := bstep (se 1 (by rfl) ⟨815009, by rfl⟩ : syracuseStep 1086679 = 1630019) B1630019
theorem B1086699 : Blo 1084620 1086699 := bstep (se 1 (by rfl) ⟨815024, by rfl⟩ : syracuseStep 1086699 = 1630049) B1630049
theorem B1086711 : Blo 1084620 1086711 := bstep (se 1 (by rfl) ⟨815033, by rfl⟩ : syracuseStep 1086711 = 1630067) B1630067
theorem B1086731 : Blo 1084620 1086731 := bstep (se 1 (by rfl) ⟨815048, by rfl⟩ : syracuseStep 1086731 = 1630097) B1630097
theorem B1086743 : Blo 1084620 1086743 := bstep (se 1 (by rfl) ⟨815057, by rfl⟩ : syracuseStep 1086743 = 1630115) B1630115
theorem B1086763 : Blo 1084620 1086763 := bstep (se 1 (by rfl) ⟨815072, by rfl⟩ : syracuseStep 1086763 = 1630145) B1630145
theorem B1086775 : Blo 1084620 1086775 := bstep (se 1 (by rfl) ⟨815081, by rfl⟩ : syracuseStep 1086775 = 1630163) B1630163
theorem B1086795 : Blo 1084620 1086795 := bstep (se 1 (by rfl) ⟨815096, by rfl⟩ : syracuseStep 1086795 = 1630193) B1630193
theorem B1086807 : Blo 1084620 1086807 := bstep (se 1 (by rfl) ⟨815105, by rfl⟩ : syracuseStep 1086807 = 1630211) B1630211
theorem B1086827 : Blo 1084620 1086827 := bstep (se 1 (by rfl) ⟨815120, by rfl⟩ : syracuseStep 1086827 = 1630241) B1630241
theorem B1086839 : Blo 1084620 1086839 := bstep (se 1 (by rfl) ⟨815129, by rfl⟩ : syracuseStep 1086839 = 1630259) B1630259
theorem B1086859 : Blo 1084620 1086859 := bstep (se 1 (by rfl) ⟨815144, by rfl⟩ : syracuseStep 1086859 = 1630289) B1630289
theorem B6264215 : Blo 1084620 6264215 := bstep (se 1 (by rfl) ⟨4698161, by rfl⟩ : syracuseStep 6264215 = 9396323) B9396323
theorem B1086871 : Blo 1084620 1086871 := bstep (se 1 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 1086871 = 1630307) B1630307
theorem B1086891 : Blo 1084620 1086891 := bstep (se 1 (by rfl) ⟨815168, by rfl⟩ : syracuseStep 1086891 = 1630337) B1630337
theorem B1086903 : Blo 1084620 1086903 := bstep (se 1 (by rfl) ⟨815177, by rfl⟩ : syracuseStep 1086903 = 1630355) B1630355
theorem B1086923 : Blo 1084620 1086923 := bstep (se 1 (by rfl) ⟨815192, by rfl⟩ : syracuseStep 1086923 = 1630385) B1630385
theorem B1086935 : Blo 1084620 1086935 := bstep (se 1 (by rfl) ⟨815201, by rfl⟩ : syracuseStep 1086935 = 1630403) B1630403
theorem B1086955 : Blo 1084620 1086955 := bstep (se 1 (by rfl) ⟨815216, by rfl⟩ : syracuseStep 1086955 = 1630433) B1630433
theorem B1086967 : Blo 1084620 1086967 := bstep (se 1 (by rfl) ⟨815225, by rfl⟩ : syracuseStep 1086967 = 1630451) B1630451
theorem B1086987 : Blo 1084620 1086987 := bstep (se 1 (by rfl) ⟨815240, by rfl⟩ : syracuseStep 1086987 = 1630481) B1630481
theorem B1086999 : Blo 1084620 1086999 := bstep (se 1 (by rfl) ⟨815249, by rfl⟩ : syracuseStep 1086999 = 1630499) B1630499
theorem B1087019 : Blo 1084620 1087019 := bstep (se 1 (by rfl) ⟨815264, by rfl⟩ : syracuseStep 1087019 = 1630529) B1630529
theorem B1087031 : Blo 1084620 1087031 := bstep (se 1 (by rfl) ⟨815273, by rfl⟩ : syracuseStep 1087031 = 1630547) B1630547
theorem B1087051 : Blo 1084620 1087051 := bstep (se 1 (by rfl) ⟨815288, by rfl⟩ : syracuseStep 1087051 = 1630577) B1630577
theorem B1087063 : Blo 1084620 1087063 := bstep (se 1 (by rfl) ⟨815297, by rfl⟩ : syracuseStep 1087063 = 1630595) B1630595
theorem B1087083 : Blo 1084620 1087083 := bstep (se 1 (by rfl) ⟨815312, by rfl⟩ : syracuseStep 1087083 = 1630625) B1630625
theorem B1087095 : Blo 1084620 1087095 := bstep (se 1 (by rfl) ⟨815321, by rfl⟩ : syracuseStep 1087095 = 1630643) B1630643
theorem B1087115 : Blo 1084620 1087115 := bstep (se 1 (by rfl) ⟨815336, by rfl⟩ : syracuseStep 1087115 = 1630673) B1630673
theorem B1087127 : Blo 1084620 1087127 := bstep (se 1 (by rfl) ⟨815345, by rfl⟩ : syracuseStep 1087127 = 1630691) B1630691
theorem B1087147 : Blo 1084620 1087147 := bstep (se 1 (by rfl) ⟨815360, by rfl⟩ : syracuseStep 1087147 = 1630721) B1630721
theorem B1087159 : Blo 1084620 1087159 := bstep (se 1 (by rfl) ⟨815369, by rfl⟩ : syracuseStep 1087159 = 1630739) B1630739
theorem B1087179 : Blo 1084620 1087179 := bstep (se 1 (by rfl) ⟨815384, by rfl⟩ : syracuseStep 1087179 = 1630769) B1630769
theorem B1087191 : Blo 1084620 1087191 := bstep (se 1 (by rfl) ⟨815393, by rfl⟩ : syracuseStep 1087191 = 1630787) B1630787
theorem B1087211 : Blo 1084620 1087211 := bstep (se 1 (by rfl) ⟨815408, by rfl⟩ : syracuseStep 1087211 = 1630817) B1630817
theorem B1087223 : Blo 1084620 1087223 := bstep (se 1 (by rfl) ⟨815417, by rfl⟩ : syracuseStep 1087223 = 1630835) B1630835
theorem B1087243 : Blo 1084620 1087243 := bstep (se 1 (by rfl) ⟨815432, by rfl⟩ : syracuseStep 1087243 = 1630865) B1630865
theorem B1087255 : Blo 1084620 1087255 := bstep (se 1 (by rfl) ⟨815441, by rfl⟩ : syracuseStep 1087255 = 1630883) B1630883
theorem B1087275 : Blo 1084620 1087275 := bstep (se 1 (by rfl) ⟨815456, by rfl⟩ : syracuseStep 1087275 = 1630913) B1630913
theorem B1087287 : Blo 1084620 1087287 := bstep (se 1 (by rfl) ⟨815465, by rfl⟩ : syracuseStep 1087287 = 1630931) B1630931
theorem B1087307 : Blo 1084620 1087307 := bstep (se 1 (by rfl) ⟨815480, by rfl⟩ : syracuseStep 1087307 = 1630961) B1630961
theorem B1087319 : Blo 1084620 1087319 := bstep (se 1 (by rfl) ⟨815489, by rfl⟩ : syracuseStep 1087319 = 1630979) B1630979
theorem B1087339 : Blo 1084620 1087339 := bstep (se 1 (by rfl) ⟨815504, by rfl⟩ : syracuseStep 1087339 = 1631009) B1631009
theorem B1087351 : Blo 1084620 1087351 := bstep (se 1 (by rfl) ⟨815513, by rfl⟩ : syracuseStep 1087351 = 1631027) B1631027
theorem B1087371 : Blo 1084620 1087371 := bstep (se 1 (by rfl) ⟨815528, by rfl⟩ : syracuseStep 1087371 = 1631057) B1631057
theorem B1087383 : Blo 1084620 1087383 := bstep (se 1 (by rfl) ⟨815537, by rfl⟩ : syracuseStep 1087383 = 1631075) B1631075
theorem B1087403 : Blo 1084620 1087403 := bstep (se 1 (by rfl) ⟨815552, by rfl⟩ : syracuseStep 1087403 = 1631105) B1631105
theorem B1087415 : Blo 1084620 1087415 := bstep (se 1 (by rfl) ⟨815561, by rfl⟩ : syracuseStep 1087415 = 1631123) B1631123
theorem B1087435 : Blo 1084620 1087435 := bstep (se 1 (by rfl) ⟨815576, by rfl⟩ : syracuseStep 1087435 = 1631153) B1631153
theorem B1087447 : Blo 1084620 1087447 := bstep (se 1 (by rfl) ⟨815585, by rfl⟩ : syracuseStep 1087447 = 1631171) B1631171
theorem B1087467 : Blo 1084620 1087467 := bstep (se 1 (by rfl) ⟨815600, by rfl⟩ : syracuseStep 1087467 = 1631201) B1631201
theorem B1087479 : Blo 1084620 1087479 := bstep (se 1 (by rfl) ⟨815609, by rfl⟩ : syracuseStep 1087479 = 1631219) B1631219
theorem B1087499 : Blo 1084620 1087499 := bstep (se 1 (by rfl) ⟨815624, by rfl⟩ : syracuseStep 1087499 = 1631249) B1631249
theorem B1087511 : Blo 1084620 1087511 := bstep (se 1 (by rfl) ⟨815633, by rfl⟩ : syracuseStep 1087511 = 1631267) B1631267
theorem B1087531 : Blo 1084620 1087531 := bstep (se 1 (by rfl) ⟨815648, by rfl⟩ : syracuseStep 1087531 = 1631297) B1631297
theorem B1087543 : Blo 1084620 1087543 := bstep (se 1 (by rfl) ⟨815657, by rfl⟩ : syracuseStep 1087543 = 1631315) B1631315
theorem B1087563 : Blo 1084620 1087563 := bstep (se 1 (by rfl) ⟨815672, by rfl⟩ : syracuseStep 1087563 = 1631345) B1631345
theorem B1087575 : Blo 1084620 1087575 := bstep (se 1 (by rfl) ⟨815681, by rfl⟩ : syracuseStep 1087575 = 1631363) B1631363
theorem B1087595 : Blo 1084620 1087595 := bstep (se 1 (by rfl) ⟨815696, by rfl⟩ : syracuseStep 1087595 = 1631393) B1631393
theorem B1087607 : Blo 1084620 1087607 := bstep (se 1 (by rfl) ⟨815705, by rfl⟩ : syracuseStep 1087607 = 1631411) B1631411
theorem B1087627 : Blo 1084620 1087627 := bstep (se 1 (by rfl) ⟨815720, by rfl⟩ : syracuseStep 1087627 = 1631441) B1631441
theorem B1087639 : Blo 1084620 1087639 := bstep (se 1 (by rfl) ⟨815729, by rfl⟩ : syracuseStep 1087639 = 1631459) B1631459
theorem B1087659 : Blo 1084620 1087659 := bstep (se 1 (by rfl) ⟨815744, by rfl⟩ : syracuseStep 1087659 = 1631489) B1631489
theorem B1087671 : Blo 1084620 1087671 := bstep (se 1 (by rfl) ⟨815753, by rfl⟩ : syracuseStep 1087671 = 1631507) B1631507
theorem B1087691 : Blo 1084620 1087691 := bstep (se 1 (by rfl) ⟨815768, by rfl⟩ : syracuseStep 1087691 = 1631537) B1631537
theorem B15636685 : Blo 1084620 15636685 := bstep (se 3 (by rfl) ⟨2931878, by rfl⟩ : syracuseStep 15636685 = 5863757) B5863757
theorem B1087703 : Blo 1084620 1087703 := bstep (se 1 (by rfl) ⟨815777, by rfl⟩ : syracuseStep 1087703 = 1631555) B1631555
theorem B1087723 : Blo 1084620 1087723 := bstep (se 1 (by rfl) ⟨815792, by rfl⟩ : syracuseStep 1087723 = 1631585) B1631585
theorem B1087735 : Blo 1084620 1087735 := bstep (se 1 (by rfl) ⟨815801, by rfl⟩ : syracuseStep 1087735 = 1631603) B1631603
theorem B1087755 : Blo 1084620 1087755 := bstep (se 1 (by rfl) ⟨815816, by rfl⟩ : syracuseStep 1087755 = 1631633) B1631633
theorem B2201879 : Blo 1084620 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B1087767 : Blo 1084620 1087767 := bstep (se 1 (by rfl) ⟨815825, by rfl⟩ : syracuseStep 1087767 = 1631651) B1631651
theorem B1087787 : Blo 1084620 1087787 := bstep (se 1 (by rfl) ⟨815840, by rfl⟩ : syracuseStep 1087787 = 1631681) B1631681
theorem B1087799 : Blo 1084620 1087799 := bstep (se 1 (by rfl) ⟨815849, by rfl⟩ : syracuseStep 1087799 = 1631699) B1631699
theorem B1087819 : Blo 1084620 1087819 := bstep (se 1 (by rfl) ⟨815864, by rfl⟩ : syracuseStep 1087819 = 1631729) B1631729
theorem B1087831 : Blo 1084620 1087831 := bstep (se 1 (by rfl) ⟨815873, by rfl⟩ : syracuseStep 1087831 = 1631747) B1631747
theorem B1087851 : Blo 1084620 1087851 := bstep (se 1 (by rfl) ⟨815888, by rfl⟩ : syracuseStep 1087851 = 1631777) B1631777
theorem B1087863 : Blo 1084620 1087863 := bstep (se 1 (by rfl) ⟨815897, by rfl⟩ : syracuseStep 1087863 = 1631795) B1631795
theorem B1087883 : Blo 1084620 1087883 := bstep (se 1 (by rfl) ⟨815912, by rfl⟩ : syracuseStep 1087883 = 1631825) B1631825
theorem B1087895 : Blo 1084620 1087895 := bstep (se 1 (by rfl) ⟨815921, by rfl⟩ : syracuseStep 1087895 = 1631843) B1631843
theorem B1087915 : Blo 1084620 1087915 := bstep (se 1 (by rfl) ⟨815936, by rfl⟩ : syracuseStep 1087915 = 1631873) B1631873
theorem B1087927 : Blo 1084620 1087927 := bstep (se 1 (by rfl) ⟨815945, by rfl⟩ : syracuseStep 1087927 = 1631891) B1631891
theorem B1087947 : Blo 1084620 1087947 := bstep (se 1 (by rfl) ⟨815960, by rfl⟩ : syracuseStep 1087947 = 1631921) B1631921
theorem B1087959 : Blo 1084620 1087959 := bstep (se 1 (by rfl) ⟨815969, by rfl⟩ : syracuseStep 1087959 = 1631939) B1631939
theorem B1087979 : Blo 1084620 1087979 := bstep (se 1 (by rfl) ⟨815984, by rfl⟩ : syracuseStep 1087979 = 1631969) B1631969
theorem B1087991 : Blo 1084620 1087991 := bstep (se 1 (by rfl) ⟨815993, by rfl⟩ : syracuseStep 1087991 = 1631987) B1631987
theorem B2202113 : Blo 1084620 2202113 := bstep (se 2 (by rfl) ⟨825792, by rfl⟩ : syracuseStep 2202113 = 1651585) B1651585
theorem B1088011 : Blo 1084620 1088011 := bstep (se 1 (by rfl) ⟨816008, by rfl⟩ : syracuseStep 1088011 = 1632017) B1632017
theorem B1088023 : Blo 1084620 1088023 := bstep (se 1 (by rfl) ⟨816017, by rfl⟩ : syracuseStep 1088023 = 1632035) B1632035
theorem B1088043 : Blo 1084620 1088043 := bstep (se 1 (by rfl) ⟨816032, by rfl⟩ : syracuseStep 1088043 = 1632065) B1632065
theorem B1088055 : Blo 1084620 1088055 := bstep (se 1 (by rfl) ⟨816041, by rfl⟩ : syracuseStep 1088055 = 1632083) B1632083
theorem B1088075 : Blo 1084620 1088075 := bstep (se 1 (by rfl) ⟨816056, by rfl⟩ : syracuseStep 1088075 = 1632113) B1632113
theorem B1088087 : Blo 1084620 1088087 := bstep (se 1 (by rfl) ⟨816065, by rfl⟩ : syracuseStep 1088087 = 1632131) B1632131
theorem B1088107 : Blo 1084620 1088107 := bstep (se 1 (by rfl) ⟨816080, by rfl⟩ : syracuseStep 1088107 = 1632161) B1632161
theorem B1088119 : Blo 1084620 1088119 := bstep (se 1 (by rfl) ⟨816089, by rfl⟩ : syracuseStep 1088119 = 1632179) B1632179
theorem B1088139 : Blo 1084620 1088139 := bstep (se 1 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 1088139 = 1632209) B1632209
theorem B1088151 : Blo 1084620 1088151 := bstep (se 1 (by rfl) ⟨816113, by rfl⟩ : syracuseStep 1088151 = 1632227) B1632227
theorem B1088171 : Blo 1084620 1088171 := bstep (se 1 (by rfl) ⟨816128, by rfl⟩ : syracuseStep 1088171 = 1632257) B1632257
theorem B1088183 : Blo 1084620 1088183 := bstep (se 1 (by rfl) ⟨816137, by rfl⟩ : syracuseStep 1088183 = 1632275) B1632275
theorem B1088203 : Blo 1084620 1088203 := bstep (se 1 (by rfl) ⟨816152, by rfl⟩ : syracuseStep 1088203 = 1632305) B1632305
theorem B1088215 : Blo 1084620 1088215 := bstep (se 1 (by rfl) ⟨816161, by rfl⟩ : syracuseStep 1088215 = 1632323) B1632323
theorem B1088235 : Blo 1084620 1088235 := bstep (se 1 (by rfl) ⟨816176, by rfl⟩ : syracuseStep 1088235 = 1632353) B1632353
theorem B1088247 : Blo 1084620 1088247 := bstep (se 1 (by rfl) ⟨816185, by rfl⟩ : syracuseStep 1088247 = 1632371) B1632371
theorem B1088267 : Blo 1084620 1088267 := bstep (se 1 (by rfl) ⟨816200, by rfl⟩ : syracuseStep 1088267 = 1632401) B1632401
theorem B1088279 : Blo 1084620 1088279 := bstep (se 1 (by rfl) ⟨816209, by rfl⟩ : syracuseStep 1088279 = 1632419) B1632419
theorem B1088299 : Blo 1084620 1088299 := bstep (se 1 (by rfl) ⟨816224, by rfl⟩ : syracuseStep 1088299 = 1632449) B1632449
theorem B1088311 : Blo 1084620 1088311 := bstep (se 1 (by rfl) ⟨816233, by rfl⟩ : syracuseStep 1088311 = 1632467) B1632467
theorem B9280331 : Blo 1084620 9280331 := bstep (se 1 (by rfl) ⟨6960248, by rfl⟩ : syracuseStep 9280331 = 13920497) B13920497
theorem B1088331 : Blo 1084620 1088331 := bstep (se 1 (by rfl) ⟨816248, by rfl⟩ : syracuseStep 1088331 = 1632497) B1632497
theorem B1088343 : Blo 1084620 1088343 := bstep (se 1 (by rfl) ⟨816257, by rfl⟩ : syracuseStep 1088343 = 1632515) B1632515
theorem B1088363 : Blo 1084620 1088363 := bstep (se 1 (by rfl) ⟨816272, by rfl⟩ : syracuseStep 1088363 = 1632545) B1632545
theorem B1088375 : Blo 1084620 1088375 := bstep (se 1 (by rfl) ⟨816281, by rfl⟩ : syracuseStep 1088375 = 1632563) B1632563
theorem B1088395 : Blo 1084620 1088395 := bstep (se 1 (by rfl) ⟨816296, by rfl⟩ : syracuseStep 1088395 = 1632593) B1632593
theorem B1088407 : Blo 1084620 1088407 := bstep (se 1 (by rfl) ⟨816305, by rfl⟩ : syracuseStep 1088407 = 1632611) B1632611
theorem B1088427 : Blo 1084620 1088427 := bstep (se 1 (by rfl) ⟨816320, by rfl⟩ : syracuseStep 1088427 = 1632641) B1632641
theorem B1088439 : Blo 1084620 1088439 := bstep (se 1 (by rfl) ⟨816329, by rfl⟩ : syracuseStep 1088439 = 1632659) B1632659
theorem B1088459 : Blo 1084620 1088459 := bstep (se 1 (by rfl) ⟨816344, by rfl⟩ : syracuseStep 1088459 = 1632689) B1632689
theorem B1088471 : Blo 1084620 1088471 := bstep (se 1 (by rfl) ⟨816353, by rfl⟩ : syracuseStep 1088471 = 1632707) B1632707
theorem B1088491 : Blo 1084620 1088491 := bstep (se 1 (by rfl) ⟨816368, by rfl⟩ : syracuseStep 1088491 = 1632737) B1632737
theorem B1088503 : Blo 1084620 1088503 := bstep (se 1 (by rfl) ⟨816377, by rfl⟩ : syracuseStep 1088503 = 1632755) B1632755
theorem B1088523 : Blo 1084620 1088523 := bstep (se 1 (by rfl) ⟨816392, by rfl⟩ : syracuseStep 1088523 = 1632785) B1632785
theorem B1088535 : Blo 1084620 1088535 := bstep (se 1 (by rfl) ⟨816401, by rfl⟩ : syracuseStep 1088535 = 1632803) B1632803
theorem B20913187 : Blo 1084620 20913187 := bstep (se 1 (by rfl) ⟨15684890, by rfl⟩ : syracuseStep 20913187 = 31369781) B31369781
theorem B1088555 : Blo 1084620 1088555 := bstep (se 1 (by rfl) ⟨816416, by rfl⟩ : syracuseStep 1088555 = 1632833) B1632833
theorem B1088567 : Blo 1084620 1088567 := bstep (se 1 (by rfl) ⟨816425, by rfl⟩ : syracuseStep 1088567 = 1632851) B1632851
theorem B1088587 : Blo 1084620 1088587 := bstep (se 1 (by rfl) ⟨816440, by rfl⟩ : syracuseStep 1088587 = 1632881) B1632881
theorem B1088599 : Blo 1084620 1088599 := bstep (se 1 (by rfl) ⟨816449, by rfl⟩ : syracuseStep 1088599 = 1632899) B1632899
theorem B1088619 : Blo 1084620 1088619 := bstep (se 1 (by rfl) ⟨816464, by rfl⟩ : syracuseStep 1088619 = 1632929) B1632929
theorem B3480907 : Blo 1084620 3480907 := bstep (se 1 (by rfl) ⟨2610680, by rfl⟩ : syracuseStep 3480907 = 5221361) B5221361
theorem B2203031 : Blo 1084620 2203031 := bstep (se 1 (by rfl) ⟨1652273, by rfl⟩ : syracuseStep 2203031 = 3304547) B3304547
theorem B8822233 : Blo 1084620 8822233 := bstep (se 2 (by rfl) ⟨3308337, by rfl⟩ : syracuseStep 8822233 = 6616675) B6616675
theorem B4955651 : Blo 1084620 4955651 := bstep (se 1 (by rfl) ⟨3716738, by rfl⟩ : syracuseStep 4955651 = 7433477) B7433477
theorem B1220215 : Blo 1084620 1220215 := bstep (se 1 (by rfl) ⟨915161, by rfl⟩ : syracuseStep 1220215 = 1830323) B1830323
theorem B1220395 : Blo 1084620 1220395 := bstep (se 1 (by rfl) ⟨915296, by rfl⟩ : syracuseStep 1220395 = 1830593) B1830593
theorem B1220503 : Blo 1084620 1220503 := bstep (se 1 (by rfl) ⟨915377, by rfl⟩ : syracuseStep 1220503 = 1830755) B1830755
theorem B12394457 : Blo 1084620 12394457 := bstep (se 2 (by rfl) ⟨4647921, by rfl⟩ : syracuseStep 12394457 = 9295843) B9295843
theorem B1220683 : Blo 1084620 1220683 := bstep (se 1 (by rfl) ⟨915512, by rfl⟩ : syracuseStep 1220683 = 1831025) B1831025
theorem B5873795 : Blo 1084620 5873795 := bstep (se 1 (by rfl) ⟨4405346, by rfl⟩ : syracuseStep 5873795 = 8810693) B8810693
theorem B1220791 : Blo 1084620 1220791 := bstep (se 1 (by rfl) ⟨915593, by rfl⟩ : syracuseStep 1220791 = 1831187) B1831187
theorem B3088705 : Blo 1084620 3088705 := bstep (se 2 (by rfl) ⟨1158264, by rfl⟩ : syracuseStep 3088705 = 2316529) B2316529
theorem B1220971 : Blo 1084620 1220971 := bstep (se 1 (by rfl) ⟨915728, by rfl⟩ : syracuseStep 1220971 = 1831457) B1831457
theorem B1221079 : Blo 1084620 1221079 := bstep (se 1 (by rfl) ⟨915809, by rfl⟩ : syracuseStep 1221079 = 1831619) B1831619
theorem B1221259 : Blo 1084620 1221259 := bstep (se 1 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 1221259 = 1831889) B1831889
theorem B1221367 : Blo 1084620 1221367 := bstep (se 1 (by rfl) ⟨916025, by rfl⟩ : syracuseStep 1221367 = 1832051) B1832051
theorem B4399895 : Blo 1084620 4399895 := bstep (se 1 (by rfl) ⟨3299921, by rfl⟩ : syracuseStep 4399895 = 6599843) B6599843
theorem B7840577 : Blo 1084620 7840577 := bstep (se 2 (by rfl) ⟨2940216, by rfl⟩ : syracuseStep 7840577 = 5880433) B5880433
theorem B1221547 : Blo 1084620 1221547 := bstep (se 1 (by rfl) ⟨916160, by rfl⟩ : syracuseStep 1221547 = 1832321) B1832321
theorem B3482585 : Blo 1084620 3482585 := bstep (se 2 (by rfl) ⟨1305969, by rfl⟩ : syracuseStep 3482585 = 2611939) B2611939
theorem B1221655 : Blo 1084620 1221655 := bstep (se 1 (by rfl) ⟨916241, by rfl⟩ : syracuseStep 1221655 = 1832483) B1832483
theorem B1221835 : Blo 1084620 1221835 := bstep (se 1 (by rfl) ⟨916376, by rfl⟩ : syracuseStep 1221835 = 1832753) B1832753
theorem B1221943 : Blo 1084620 1221943 := bstep (se 1 (by rfl) ⟨916457, by rfl⟩ : syracuseStep 1221943 = 1832915) B1832915
theorem B9282995 : Blo 1084620 9282995 := bstep (se 1 (by rfl) ⟨6962246, by rfl⟩ : syracuseStep 9282995 = 13924493) B13924493
theorem B1222123 : Blo 1084620 1222123 := bstep (se 1 (by rfl) ⟨916592, by rfl⟩ : syracuseStep 1222123 = 1833185) B1833185
theorem B1549849 : Blo 1084620 1549849 := bstep (se 2 (by rfl) ⟨581193, by rfl⟩ : syracuseStep 1549849 = 1162387) B1162387
theorem B1222231 : Blo 1084620 1222231 := bstep (se 1 (by rfl) ⟨916673, by rfl⟩ : syracuseStep 1222231 = 1833347) B1833347
theorem B1222411 : Blo 1084620 1222411 := bstep (se 1 (by rfl) ⟨916808, by rfl⟩ : syracuseStep 1222411 = 1833617) B1833617
theorem B3483481 : Blo 1084620 3483481 := bstep (se 2 (by rfl) ⟨1306305, by rfl⟩ : syracuseStep 3483481 = 2612611) B2612611
theorem B1222519 : Blo 1084620 1222519 := bstep (se 1 (by rfl) ⟨916889, by rfl⟩ : syracuseStep 1222519 = 1833779) B1833779
theorem B1222699 : Blo 1084620 1222699 := bstep (se 1 (by rfl) ⟨917024, by rfl⟩ : syracuseStep 1222699 = 1834049) B1834049
theorem B1222807 : Blo 1084620 1222807 := bstep (se 1 (by rfl) ⟨917105, by rfl⟩ : syracuseStep 1222807 = 1834211) B1834211
theorem B1222987 : Blo 1084620 1222987 := bstep (se 1 (by rfl) ⟨917240, by rfl⟩ : syracuseStep 1222987 = 1834481) B1834481
theorem B1223095 : Blo 1084620 1223095 := bstep (se 1 (by rfl) ⟨917321, by rfl⟩ : syracuseStep 1223095 = 1834643) B1834643
theorem B3484097 : Blo 1084620 3484097 := bstep (se 2 (by rfl) ⟨1306536, by rfl⟩ : syracuseStep 3484097 = 2613073) B2613073
theorem B9284057 : Blo 1084620 9284057 := bstep (se 2 (by rfl) ⟨3481521, by rfl⟩ : syracuseStep 9284057 = 6963043) B6963043
theorem B3484225 : Blo 1084620 3484225 := bstep (se 2 (by rfl) ⟨1306584, by rfl⟩ : syracuseStep 3484225 = 2613169) B2613169
theorem B2206273 : Blo 1084620 2206273 := bstep (se 2 (by rfl) ⟨827352, by rfl⟩ : syracuseStep 2206273 = 1654705) B1654705
theorem B1223275 : Blo 1084620 1223275 := bstep (se 1 (by rfl) ⟨917456, by rfl⟩ : syracuseStep 1223275 = 1834913) B1834913
theorem B1223383 : Blo 1084620 1223383 := bstep (se 1 (by rfl) ⟨917537, by rfl⟩ : syracuseStep 1223383 = 1835075) B1835075
theorem B3091223 : Blo 1084620 3091223 := bstep (se 1 (by rfl) ⟨2318417, by rfl⟩ : syracuseStep 3091223 = 4636835) B4636835
theorem B4401971 : Blo 1084620 4401971 := bstep (se 1 (by rfl) ⟨3301478, by rfl⟩ : syracuseStep 4401971 = 6602957) B6602957
theorem B1223563 : Blo 1084620 1223563 := bstep (se 1 (by rfl) ⟨917672, by rfl⟩ : syracuseStep 1223563 = 1835345) B1835345
theorem B1223671 : Blo 1084620 1223671 := bstep (se 1 (by rfl) ⟨917753, by rfl⟩ : syracuseStep 1223671 = 1835507) B1835507
theorem B1223851 : Blo 1084620 1223851 := bstep (se 1 (by rfl) ⟨917888, by rfl⟩ : syracuseStep 1223851 = 1835777) B1835777
theorem B1223959 : Blo 1084620 1223959 := bstep (se 1 (by rfl) ⟨917969, by rfl⟩ : syracuseStep 1223959 = 1835939) B1835939
theorem B1224139 : Blo 1084620 1224139 := bstep (se 1 (by rfl) ⟨918104, by rfl⟩ : syracuseStep 1224139 = 1836209) B1836209
theorem B1224247 : Blo 1084620 1224247 := bstep (se 1 (by rfl) ⟨918185, by rfl⟩ : syracuseStep 1224247 = 1836371) B1836371
theorem B4959809 : Blo 1084620 4959809 := bstep (se 2 (by rfl) ⟨1859928, by rfl⟩ : syracuseStep 4959809 = 3719857) B3719857
theorem B1158743 : Blo 1084620 1158743 := bstep (se 1 (by rfl) ⟨869057, by rfl⟩ : syracuseStep 1158743 = 1738115) B1738115
theorem B1158871 : Blo 1084620 1158871 := bstep (se 1 (by rfl) ⟨869153, by rfl⟩ : syracuseStep 1158871 = 1738307) B1738307
theorem B1224427 : Blo 1084620 1224427 := bstep (se 1 (by rfl) ⟨918320, by rfl⟩ : syracuseStep 1224427 = 1836641) B1836641
theorem B1224535 : Blo 1084620 1224535 := bstep (se 1 (by rfl) ⟨918401, by rfl⟩ : syracuseStep 1224535 = 1836803) B1836803
theorem B25472945 : Blo 1084620 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B3092555 : Blo 1084620 3092555 := bstep (se 1 (by rfl) ⟨2319416, by rfl⟩ : syracuseStep 3092555 = 4638833) B4638833
theorem B1159435 : Blo 1084620 1159435 := bstep (se 1 (by rfl) ⟨869576, by rfl⟩ : syracuseStep 1159435 = 1739153) B1739153
theorem B10170689 : Blo 1084620 10170689 := bstep (se 2 (by rfl) ⟨3814008, by rfl⟩ : syracuseStep 10170689 = 7628017) B7628017
theorem B17609177 : Blo 1084620 17609177 := bstep (se 2 (by rfl) ⟨6603441, by rfl⟩ : syracuseStep 17609177 = 13206883) B13206883
theorem B1159691 : Blo 1084620 1159691 := bstep (se 1 (by rfl) ⟨869768, by rfl⟩ : syracuseStep 1159691 = 1739537) B1739537
theorem B6795841 : Blo 1084620 6795841 := bstep (se 2 (by rfl) ⟨2548440, by rfl⟩ : syracuseStep 6795841 = 5096881) B5096881
theorem B8237699 : Blo 1084620 8237699 := bstep (se 1 (by rfl) ⟨6178274, by rfl⟩ : syracuseStep 8237699 = 12356549) B12356549
theorem B3715915 : Blo 1084620 3715915 := bstep (se 1 (by rfl) ⟨2786936, by rfl⟩ : syracuseStep 3715915 = 5573873) B5573873
theorem B4633433 : Blo 1084620 4633433 := bstep (se 2 (by rfl) ⟨1737537, by rfl⟩ : syracuseStep 4633433 = 3475075) B3475075
theorem B3486557 : Blo 1084620 3486557 := bstep (se 3 (by rfl) ⟨653729, by rfl⟩ : syracuseStep 3486557 = 1307459) B1307459
theorem B3912749 : Blo 1084620 3912749 := bstep (se 3 (by rfl) ⟨733640, by rfl⟩ : syracuseStep 3912749 = 1467281) B1467281
theorem B5944421 : Blo 1084620 5944421 := bstep (se 4 (by rfl) ⟨557289, by rfl⟩ : syracuseStep 5944421 = 1114579) B1114579
theorem B6960401 : Blo 1084620 6960401 := bstep (se 2 (by rfl) ⟨2610150, by rfl⟩ : syracuseStep 6960401 = 5220301) B5220301
theorem B1488331 : Blo 1084620 1488331 := bstep (se 1 (by rfl) ⟨1116248, by rfl⟩ : syracuseStep 1488331 = 2232497) B2232497
theorem B3913181 : Blo 1084620 3913181 := bstep (se 3 (by rfl) ⟨733721, by rfl⟩ : syracuseStep 3913181 = 1467443) B1467443
theorem B3094195 : Blo 1084620 3094195 := bstep (se 1 (by rfl) ⟨2320646, by rfl⟩ : syracuseStep 3094195 = 4641293) B4641293
theorem B12564497 : Blo 1084620 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B5224493 : Blo 1084620 5224493 := bstep (se 3 (by rfl) ⟨979592, by rfl⟩ : syracuseStep 5224493 = 1959185) B1959185
theorem B1652953 : Blo 1084620 1652953 := bstep (se 2 (by rfl) ⟨619857, by rfl⟩ : syracuseStep 1652953 = 1239715) B1239715
theorem B4635073 : Blo 1084620 4635073 := bstep (se 2 (by rfl) ⟨1738152, by rfl⟩ : syracuseStep 4635073 = 3476305) B3476305
theorem B1161707 : Blo 1084620 1161707 := bstep (se 1 (by rfl) ⟨871280, by rfl⟩ : syracuseStep 1161707 = 1742561) B1742561
theorem B5880365 : Blo 1084620 5880365 := bstep (se 3 (by rfl) ⟨1102568, by rfl⟩ : syracuseStep 5880365 = 2205137) B2205137
theorem B5880451 : Blo 1084620 5880451 := bstep (se 1 (by rfl) ⟨4410338, by rfl⟩ : syracuseStep 5880451 = 8820677) B8820677
theorem B3914419 : Blo 1084620 3914419 := bstep (se 1 (by rfl) ⟨2935814, by rfl⟩ : syracuseStep 3914419 = 5871629) B5871629
theorem B3095243 : Blo 1084620 3095243 := bstep (se 1 (by rfl) ⟨2321432, by rfl⟩ : syracuseStep 3095243 = 4642865) B4642865
theorem B9550541 : Blo 1084620 9550541 := bstep (se 3 (by rfl) ⟨1790726, by rfl⟩ : syracuseStep 9550541 = 3581453) B3581453
theorem B2440601 : Blo 1084620 2440601 := bstep (se 2 (by rfl) ⟨915225, by rfl⟩ : syracuseStep 2440601 = 1830451) B1830451
theorem B2440691 : Blo 1084620 2440691 := bstep (se 1 (by rfl) ⟨1830518, by rfl⟩ : syracuseStep 2440691 = 3661037) B3661037
theorem B2440727 : Blo 1084620 2440727 := bstep (se 1 (by rfl) ⟨1830545, by rfl⟩ : syracuseStep 2440727 = 3661091) B3661091
theorem B38125187 : Blo 1084620 38125187 := bstep (se 1 (by rfl) ⟨28593890, by rfl⟩ : syracuseStep 38125187 = 57187781) B57187781
theorem B2440907 : Blo 1084620 2440907 := bstep (se 1 (by rfl) ⟨1830680, by rfl⟩ : syracuseStep 2440907 = 3661361) B3661361
theorem B2440961 : Blo 1084620 2440961 := bstep (se 2 (by rfl) ⟨915360, by rfl⟩ : syracuseStep 2440961 = 1830721) B1830721
theorem B4636561 : Blo 1084620 4636561 := bstep (se 2 (by rfl) ⟨1738710, by rfl⟩ : syracuseStep 4636561 = 3477421) B3477421
theorem B8241101 : Blo 1084620 8241101 := bstep (se 3 (by rfl) ⟨1545206, by rfl⟩ : syracuseStep 8241101 = 3090413) B3090413
theorem B2441177 : Blo 1084620 2441177 := bstep (se 2 (by rfl) ⟨915441, by rfl⟩ : syracuseStep 2441177 = 1830883) B1830883
theorem B2441267 : Blo 1084620 2441267 := bstep (se 1 (by rfl) ⟨1830950, by rfl⟩ : syracuseStep 2441267 = 3661901) B3661901
theorem B2441303 : Blo 1084620 2441303 := bstep (se 1 (by rfl) ⟨1830977, by rfl⟩ : syracuseStep 2441303 = 3661955) B3661955
theorem B9289829 : Blo 1084620 9289829 := bstep (se 4 (by rfl) ⟨870921, by rfl⟩ : syracuseStep 9289829 = 1741843) B1741843
theorem B10436759 : Blo 1084620 10436759 := bstep (se 1 (by rfl) ⟨7827569, by rfl⟩ : syracuseStep 10436759 = 15655139) B15655139
theorem B2441483 : Blo 1084620 2441483 := bstep (se 1 (by rfl) ⟨1831112, by rfl⟩ : syracuseStep 2441483 = 3662225) B3662225
theorem B13582637 : Blo 1084620 13582637 := bstep (se 3 (by rfl) ⟨2546744, by rfl⟩ : syracuseStep 13582637 = 5093489) B5093489
theorem B3096883 : Blo 1084620 3096883 := bstep (se 1 (by rfl) ⟨2322662, by rfl⟩ : syracuseStep 3096883 = 4645325) B4645325
theorem B2441537 : Blo 1084620 2441537 := bstep (se 2 (by rfl) ⟨915576, by rfl⟩ : syracuseStep 2441537 = 1831153) B1831153
theorem B2474393 : Blo 1084620 2474393 := bstep (se 2 (by rfl) ⟨927897, by rfl⟩ : syracuseStep 2474393 = 1855795) B1855795
theorem B8241587 : Blo 1084620 8241587 := bstep (se 1 (by rfl) ⟨6181190, by rfl⟩ : syracuseStep 8241587 = 12362381) B12362381
theorem B3097111 : Blo 1084620 3097111 := bstep (se 1 (by rfl) ⟨2322833, by rfl⟩ : syracuseStep 3097111 = 4645667) B4645667
theorem B2441753 : Blo 1084620 2441753 := bstep (se 2 (by rfl) ⟨915657, by rfl⟩ : syracuseStep 2441753 = 1831315) B1831315
theorem B2441843 : Blo 1084620 2441843 := bstep (se 1 (by rfl) ⟨1831382, by rfl⟩ : syracuseStep 2441843 = 3662765) B3662765
theorem B2441879 : Blo 1084620 2441879 := bstep (se 1 (by rfl) ⟨1831409, by rfl⟩ : syracuseStep 2441879 = 3662819) B3662819
theorem B40682225 : Blo 1084620 40682225 := bstep (se 2 (by rfl) ⟨15255834, by rfl⟩ : syracuseStep 40682225 = 30511669) B30511669
theorem B2442059 : Blo 1084620 2442059 := bstep (se 1 (by rfl) ⟨1831544, by rfl⟩ : syracuseStep 2442059 = 3663089) B3663089
theorem B2442113 : Blo 1084620 2442113 := bstep (se 2 (by rfl) ⟨915792, by rfl⟩ : syracuseStep 2442113 = 1831585) B1831585
theorem B2442329 : Blo 1084620 2442329 := bstep (se 2 (by rfl) ⟨915873, by rfl⟩ : syracuseStep 2442329 = 1831747) B1831747
theorem B2442419 : Blo 1084620 2442419 := bstep (se 1 (by rfl) ⟨1831814, by rfl⟩ : syracuseStep 2442419 = 3663629) B3663629
theorem B2442455 : Blo 1084620 2442455 := bstep (se 1 (by rfl) ⟨1831841, by rfl⟩ : syracuseStep 2442455 = 3663683) B3663683
theorem B2442635 : Blo 1084620 2442635 := bstep (se 1 (by rfl) ⟨1831976, by rfl⟩ : syracuseStep 2442635 = 3663953) B3663953
theorem B2442689 : Blo 1084620 2442689 := bstep (se 2 (by rfl) ⟨916008, by rfl⟩ : syracuseStep 2442689 = 1832017) B1832017
theorem B6964811 : Blo 1084620 6964811 := bstep (se 1 (by rfl) ⟨5223608, by rfl⟩ : syracuseStep 6964811 = 10447217) B10447217
theorem B2442905 : Blo 1084620 2442905 := bstep (se 2 (by rfl) ⟨916089, by rfl⟩ : syracuseStep 2442905 = 1832179) B1832179
theorem B10045133 : Blo 1084620 10045133 := bstep (se 3 (by rfl) ⟨1883462, by rfl⟩ : syracuseStep 10045133 = 3766925) B3766925
theorem B9291469 : Blo 1084620 9291469 := bstep (se 3 (by rfl) ⟨1742150, by rfl⟩ : syracuseStep 9291469 = 3484301) B3484301
theorem B2442995 : Blo 1084620 2442995 := bstep (se 1 (by rfl) ⟨1832246, by rfl⟩ : syracuseStep 2442995 = 3664493) B3664493
theorem B2443031 : Blo 1084620 2443031 := bstep (se 1 (by rfl) ⟨1832273, by rfl⟩ : syracuseStep 2443031 = 3664547) B3664547
theorem B8243045 : Blo 1084620 8243045 := bstep (se 4 (by rfl) ⟨772785, by rfl⟩ : syracuseStep 8243045 = 1545571) B1545571
theorem B2443211 : Blo 1084620 2443211 := bstep (se 1 (by rfl) ⟨1832408, by rfl⟩ : syracuseStep 2443211 = 3664817) B3664817
theorem B2443265 : Blo 1084620 2443265 := bstep (se 2 (by rfl) ⟨916224, by rfl⟩ : syracuseStep 2443265 = 1832449) B1832449
theorem B2443481 : Blo 1084620 2443481 := bstep (se 2 (by rfl) ⟨916305, by rfl⟩ : syracuseStep 2443481 = 1832611) B1832611
theorem B5490989 : Blo 1084620 5490989 := bstep (se 3 (by rfl) ⟨1029560, by rfl⟩ : syracuseStep 5490989 = 2059121) B2059121
theorem B2443571 : Blo 1084620 2443571 := bstep (se 1 (by rfl) ⟨1832678, by rfl⟩ : syracuseStep 2443571 = 3665357) B3665357
theorem B8243531 : Blo 1084620 8243531 := bstep (se 1 (by rfl) ⟨6182648, by rfl⟩ : syracuseStep 8243531 = 12365297) B12365297
theorem B1395019 : Blo 1084620 1395019 := bstep (se 1 (by rfl) ⟨1046264, by rfl⟩ : syracuseStep 1395019 = 2092529) B2092529
theorem B2443607 : Blo 1084620 2443607 := bstep (se 1 (by rfl) ⟨1832705, by rfl⟩ : syracuseStep 2443607 = 3665411) B3665411
theorem B3098969 : Blo 1084620 3098969 := bstep (se 2 (by rfl) ⟨1162113, by rfl⟩ : syracuseStep 3098969 = 2324227) B2324227
theorem B6179165 : Blo 1084620 6179165 := bstep (se 3 (by rfl) ⟨1158593, by rfl⟩ : syracuseStep 6179165 = 2317187) B2317187
theorem B2443787 : Blo 1084620 2443787 := bstep (se 1 (by rfl) ⟨1832840, by rfl⟩ : syracuseStep 2443787 = 3665681) B3665681
theorem B5884433 : Blo 1084620 5884433 := bstep (se 2 (by rfl) ⟨2206662, by rfl⟩ : syracuseStep 5884433 = 4413325) B4413325
theorem B2443841 : Blo 1084620 2443841 := bstep (se 2 (by rfl) ⟨916440, by rfl⟩ : syracuseStep 2443841 = 1832881) B1832881
theorem B1100363 : Blo 1084620 1100363 := bstep (se 1 (by rfl) ⟨825272, by rfl⟩ : syracuseStep 1100363 = 1650545) B1650545
theorem B1886935 : Blo 1084620 1886935 := bstep (se 1 (by rfl) ⟨1415201, by rfl⟩ : syracuseStep 1886935 = 2830403) B2830403
theorem B2444057 : Blo 1084620 2444057 := bstep (se 2 (by rfl) ⟨916521, by rfl⟩ : syracuseStep 2444057 = 1833043) B1833043
theorem B2444147 : Blo 1084620 2444147 := bstep (se 1 (by rfl) ⟨1833110, by rfl⟩ : syracuseStep 2444147 = 3666221) B3666221
theorem B4639619 : Blo 1084620 4639619 := bstep (se 1 (by rfl) ⟨3479714, by rfl⟩ : syracuseStep 4639619 = 6959429) B6959429
theorem B2444183 : Blo 1084620 2444183 := bstep (se 1 (by rfl) ⟨1833137, by rfl⟩ : syracuseStep 2444183 = 3666275) B3666275
theorem B2608075 : Blo 1084620 2608075 := bstep (se 1 (by rfl) ⟨1956056, by rfl⟩ : syracuseStep 2608075 = 3912113) B3912113
theorem B9292805 : Blo 1084620 9292805 := bstep (se 4 (by rfl) ⟨871200, by rfl⟩ : syracuseStep 9292805 = 1742401) B1742401
theorem B6179915 : Blo 1084620 6179915 := bstep (se 1 (by rfl) ⟨4634936, by rfl⟩ : syracuseStep 6179915 = 9269873) B9269873
theorem B2444363 : Blo 1084620 2444363 := bstep (se 1 (by rfl) ⟨1833272, by rfl⟩ : syracuseStep 2444363 = 3666545) B3666545
theorem B1789015 : Blo 1084620 1789015 := bstep (se 1 (by rfl) ⟨1341761, by rfl⟩ : syracuseStep 1789015 = 2683523) B2683523
theorem B2935901 : Blo 1084620 2935901 := bstep (se 3 (by rfl) ⟨550481, by rfl⟩ : syracuseStep 2935901 = 1100963) B1100963
theorem B2444417 : Blo 1084620 2444417 := bstep (se 2 (by rfl) ⟨916656, by rfl⟩ : syracuseStep 2444417 = 1833313) B1833313
theorem B3099799 : Blo 1084620 3099799 := bstep (se 1 (by rfl) ⟨2324849, by rfl⟩ : syracuseStep 3099799 = 4649699) B4649699
theorem B7818457 : Blo 1084620 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B2444633 : Blo 1084620 2444633 := bstep (se 2 (by rfl) ⟨916737, by rfl⟩ : syracuseStep 2444633 = 1833475) B1833475
theorem B2444723 : Blo 1084620 2444723 := bstep (se 1 (by rfl) ⟨1833542, by rfl⟩ : syracuseStep 2444723 = 3667085) B3667085
theorem B2444759 : Blo 1084620 2444759 := bstep (se 1 (by rfl) ⟨1833569, by rfl⟩ : syracuseStep 2444759 = 3667139) B3667139
theorem B33476113 : Blo 1084620 33476113 := bstep (se 2 (by rfl) ⟨12553542, by rfl⟩ : syracuseStep 33476113 = 25107085) B25107085
theorem B2444939 : Blo 1084620 2444939 := bstep (se 1 (by rfl) ⟨1833704, by rfl⟩ : syracuseStep 2444939 = 3667409) B3667409
theorem B2444993 : Blo 1084620 2444993 := bstep (se 2 (by rfl) ⟨916872, by rfl⟩ : syracuseStep 2444993 = 1833745) B1833745
theorem B3919553 : Blo 1084620 3919553 := bstep (se 2 (by rfl) ⟨1469832, by rfl⟩ : syracuseStep 3919553 = 2939665) B2939665
theorem B1101547 : Blo 1084620 1101547 := bstep (se 1 (by rfl) ⟨826160, by rfl⟩ : syracuseStep 1101547 = 1652321) B1652321
theorem B5295889 : Blo 1084620 5295889 := bstep (se 2 (by rfl) ⟨1985958, by rfl⟩ : syracuseStep 5295889 = 3971917) B3971917
theorem B13946741 : Blo 1084620 13946741 := bstep (se 5 (by rfl) ⟨653753, by rfl⟩ : syracuseStep 13946741 = 1307507) B1307507
theorem B2445209 : Blo 1084620 2445209 := bstep (se 2 (by rfl) ⟨916953, by rfl⟩ : syracuseStep 2445209 = 1833907) B1833907
theorem B2445299 : Blo 1084620 2445299 := bstep (se 1 (by rfl) ⟨1833974, by rfl⟩ : syracuseStep 2445299 = 3667949) B3667949
theorem B2445335 : Blo 1084620 2445335 := bstep (se 1 (by rfl) ⟨1834001, by rfl⟩ : syracuseStep 2445335 = 3668003) B3668003
theorem B3133619 : Blo 1084620 3133619 := bstep (se 1 (by rfl) ⟨2350214, by rfl⟩ : syracuseStep 3133619 = 4700429) B4700429
theorem B2445515 : Blo 1084620 2445515 := bstep (se 1 (by rfl) ⟨1834136, by rfl⟩ : syracuseStep 2445515 = 3668273) B3668273
theorem B9392345 : Blo 1084620 9392345 := bstep (se 2 (by rfl) ⟨3522129, by rfl⟩ : syracuseStep 9392345 = 7044259) B7044259
theorem B2445569 : Blo 1084620 2445569 := bstep (se 2 (by rfl) ⟨917088, by rfl⟩ : syracuseStep 2445569 = 1834177) B1834177
theorem B2445785 : Blo 1084620 2445785 := bstep (se 2 (by rfl) ⟨917169, by rfl⟩ : syracuseStep 2445785 = 1834339) B1834339
theorem B2478593 : Blo 1084620 2478593 := bstep (se 2 (by rfl) ⟨929472, by rfl⟩ : syracuseStep 2478593 = 1858945) B1858945
theorem B2445875 : Blo 1084620 2445875 := bstep (se 1 (by rfl) ⟨1834406, by rfl⟩ : syracuseStep 2445875 = 3668813) B3668813
theorem B7819841 : Blo 1084620 7819841 := bstep (se 2 (by rfl) ⟨2932440, by rfl⟩ : syracuseStep 7819841 = 5864881) B5864881
theorem B2609729 : Blo 1084620 2609729 := bstep (se 2 (by rfl) ⟨978648, by rfl⟩ : syracuseStep 2609729 = 1957297) B1957297
theorem B2445911 : Blo 1084620 2445911 := bstep (se 1 (by rfl) ⟨1834433, by rfl⟩ : syracuseStep 2445911 = 3668867) B3668867
theorem B6181555 : Blo 1084620 6181555 := bstep (se 1 (by rfl) ⟨4636166, by rfl⟩ : syracuseStep 6181555 = 9272333) B9272333
theorem B2446091 : Blo 1084620 2446091 := bstep (se 1 (by rfl) ⟨1834568, by rfl⟩ : syracuseStep 2446091 = 3669137) B3669137
theorem B15651629 : Blo 1084620 15651629 := bstep (se 3 (by rfl) ⟨2934680, by rfl⟩ : syracuseStep 15651629 = 5869361) B5869361
theorem B2446145 : Blo 1084620 2446145 := bstep (se 2 (by rfl) ⟨917304, by rfl⟩ : syracuseStep 2446145 = 1834609) B1834609
theorem B2511703 : Blo 1084620 2511703 := bstep (se 1 (by rfl) ⟨1883777, by rfl⟩ : syracuseStep 2511703 = 3767555) B3767555
theorem B1627019 : Blo 1084620 1627019 := bstep (se 1 (by rfl) ⟨1220264, by rfl⟩ : syracuseStep 1627019 = 2440529) B2440529
theorem B1627031 : Blo 1084620 1627031 := bstep (se 1 (by rfl) ⟨1220273, by rfl⟩ : syracuseStep 1627031 = 2440547) B2440547
theorem B1627097 : Blo 1084620 1627097 := bstep (se 2 (by rfl) ⟨610161, by rfl⟩ : syracuseStep 1627097 = 1220323) B1220323
theorem B2446361 : Blo 1084620 2446361 := bstep (se 2 (by rfl) ⟨917385, by rfl⟩ : syracuseStep 2446361 = 1834771) B1834771
theorem B1987649 : Blo 1084620 1987649 := bstep (se 2 (by rfl) ⟨745368, by rfl⟩ : syracuseStep 1987649 = 1490737) B1490737
theorem B1627211 : Blo 1084620 1627211 := bstep (se 1 (by rfl) ⟨1220408, by rfl⟩ : syracuseStep 1627211 = 2440817) B2440817
theorem B1627223 : Blo 1084620 1627223 := bstep (se 1 (by rfl) ⟨1220417, by rfl⟩ : syracuseStep 1627223 = 2440835) B2440835
theorem B1954903 : Blo 1084620 1954903 := bstep (se 1 (by rfl) ⟨1466177, by rfl⟩ : syracuseStep 1954903 = 2932355) B2932355
theorem B2446451 : Blo 1084620 2446451 := bstep (se 1 (by rfl) ⟨1834838, by rfl⟩ : syracuseStep 2446451 = 3669677) B3669677
theorem B2446487 : Blo 1084620 2446487 := bstep (se 1 (by rfl) ⟨1834865, by rfl⟩ : syracuseStep 2446487 = 3669731) B3669731
theorem B1627289 : Blo 1084620 1627289 := bstep (se 2 (by rfl) ⟨610233, by rfl⟩ : syracuseStep 1627289 = 1220467) B1220467
theorem B1987787 : Blo 1084620 1987787 := bstep (se 1 (by rfl) ⟨1490840, by rfl⟩ : syracuseStep 1987787 = 2981681) B2981681
theorem B1627403 : Blo 1084620 1627403 := bstep (se 1 (by rfl) ⟨1220552, by rfl⟩ : syracuseStep 1627403 = 2441105) B2441105
theorem B1627415 : Blo 1084620 1627415 := bstep (se 1 (by rfl) ⟨1220561, by rfl⟩ : syracuseStep 1627415 = 2441123) B2441123
theorem B2446667 : Blo 1084620 2446667 := bstep (se 1 (by rfl) ⟨1835000, by rfl⟩ : syracuseStep 2446667 = 3670001) B3670001
theorem B1627481 : Blo 1084620 1627481 := bstep (se 2 (by rfl) ⟨610305, by rfl⟩ : syracuseStep 1627481 = 1220611) B1220611
theorem B2446721 : Blo 1084620 2446721 := bstep (se 2 (by rfl) ⟨917520, by rfl⟩ : syracuseStep 2446721 = 1835041) B1835041
theorem B1627595 : Blo 1084620 1627595 := bstep (se 1 (by rfl) ⟨1220696, by rfl⟩ : syracuseStep 1627595 = 2441393) B2441393
theorem B1627607 : Blo 1084620 1627607 := bstep (se 1 (by rfl) ⟨1220705, by rfl⟩ : syracuseStep 1627607 = 2441411) B2441411
theorem B1627673 : Blo 1084620 1627673 := bstep (se 2 (by rfl) ⟨610377, by rfl⟩ : syracuseStep 1627673 = 1220755) B1220755
theorem B2446937 : Blo 1084620 2446937 := bstep (se 2 (by rfl) ⟨917601, by rfl⟩ : syracuseStep 2446937 = 1835203) B1835203
theorem B1627787 : Blo 1084620 1627787 := bstep (se 1 (by rfl) ⟨1220840, by rfl⟩ : syracuseStep 1627787 = 2441681) B2441681
theorem B1627799 : Blo 1084620 1627799 := bstep (se 1 (by rfl) ⟨1220849, by rfl⟩ : syracuseStep 1627799 = 2441699) B2441699
theorem B2447027 : Blo 1084620 2447027 := bstep (se 1 (by rfl) ⟨1835270, by rfl⟩ : syracuseStep 2447027 = 3670541) B3670541
theorem B2447063 : Blo 1084620 2447063 := bstep (se 1 (by rfl) ⟨1835297, by rfl⟩ : syracuseStep 2447063 = 3670595) B3670595
theorem B1627865 : Blo 1084620 1627865 := bstep (se 2 (by rfl) ⟨610449, by rfl⟩ : syracuseStep 1627865 = 1220899) B1220899
theorem B1627979 : Blo 1084620 1627979 := bstep (se 1 (by rfl) ⟨1220984, by rfl⟩ : syracuseStep 1627979 = 2441969) B2441969
theorem B1627991 : Blo 1084620 1627991 := bstep (se 1 (by rfl) ⟨1220993, by rfl⟩ : syracuseStep 1627991 = 2441987) B2441987
theorem B2447243 : Blo 1084620 2447243 := bstep (se 1 (by rfl) ⟨1835432, by rfl⟩ : syracuseStep 2447243 = 3670865) B3670865
theorem B1628057 : Blo 1084620 1628057 := bstep (se 2 (by rfl) ⟨610521, by rfl⟩ : syracuseStep 1628057 = 1221043) B1221043
theorem B2447297 : Blo 1084620 2447297 := bstep (se 2 (by rfl) ⟨917736, by rfl⟩ : syracuseStep 2447297 = 1835473) B1835473
theorem B1628171 : Blo 1084620 1628171 := bstep (se 1 (by rfl) ⟨1221128, by rfl⟩ : syracuseStep 1628171 = 2442257) B2442257
theorem B1628183 : Blo 1084620 1628183 := bstep (se 1 (by rfl) ⟨1221137, by rfl⟩ : syracuseStep 1628183 = 2442275) B2442275
theorem B1628249 : Blo 1084620 1628249 := bstep (se 2 (by rfl) ⟨610593, by rfl⟩ : syracuseStep 1628249 = 1221187) B1221187
theorem B5494877 : Blo 1084620 5494877 := bstep (se 3 (by rfl) ⟨1030289, by rfl⟩ : syracuseStep 5494877 = 2060579) B2060579
theorem B6183013 : Blo 1084620 6183013 := bstep (se 4 (by rfl) ⟨579657, by rfl⟩ : syracuseStep 6183013 = 1159315) B1159315
theorem B2447513 : Blo 1084620 2447513 := bstep (se 2 (by rfl) ⟨917817, by rfl⟩ : syracuseStep 2447513 = 1835635) B1835635
theorem B1628363 : Blo 1084620 1628363 := bstep (se 1 (by rfl) ⟨1221272, by rfl⟩ : syracuseStep 1628363 = 2442545) B2442545
theorem B1628375 : Blo 1084620 1628375 := bstep (se 1 (by rfl) ⟨1221281, by rfl⟩ : syracuseStep 1628375 = 2442563) B2442563
theorem B2447603 : Blo 1084620 2447603 := bstep (se 1 (by rfl) ⟨1835702, by rfl⟩ : syracuseStep 2447603 = 3671405) B3671405
theorem B2447639 : Blo 1084620 2447639 := bstep (se 1 (by rfl) ⟨1835729, by rfl⟩ : syracuseStep 2447639 = 3671459) B3671459
theorem B1628441 : Blo 1084620 1628441 := bstep (se 2 (by rfl) ⟨610665, by rfl⟩ : syracuseStep 1628441 = 1221331) B1221331
theorem B2316683 : Blo 1084620 2316683 := bstep (se 1 (by rfl) ⟨1737512, by rfl⟩ : syracuseStep 2316683 = 3475025) B3475025
theorem B1628555 : Blo 1084620 1628555 := bstep (se 1 (by rfl) ⟨1221416, by rfl⟩ : syracuseStep 1628555 = 2442833) B2442833
theorem B1628567 : Blo 1084620 1628567 := bstep (se 1 (by rfl) ⟨1221425, by rfl⟩ : syracuseStep 1628567 = 2442851) B2442851
theorem B4118957 : Blo 1084620 4118957 := bstep (se 3 (by rfl) ⟨772304, by rfl⟩ : syracuseStep 4118957 = 1544609) B1544609
theorem B2447819 : Blo 1084620 2447819 := bstep (se 1 (by rfl) ⟨1835864, by rfl⟩ : syracuseStep 2447819 = 3671729) B3671729
theorem B1628633 : Blo 1084620 1628633 := bstep (se 2 (by rfl) ⟨610737, by rfl⟩ : syracuseStep 1628633 = 1221475) B1221475
theorem B2447873 : Blo 1084620 2447873 := bstep (se 2 (by rfl) ⟨917952, by rfl⟩ : syracuseStep 2447873 = 1835905) B1835905
theorem B19847693 : Blo 1084620 19847693 := bstep (se 3 (by rfl) ⟨3721442, by rfl⟩ : syracuseStep 19847693 = 7442885) B7442885
theorem B1956403 : Blo 1084620 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B1628747 : Blo 1084620 1628747 := bstep (se 1 (by rfl) ⟨1221560, by rfl⟩ : syracuseStep 1628747 = 2443121) B2443121
theorem B1628759 : Blo 1084620 1628759 := bstep (se 1 (by rfl) ⟨1221569, by rfl⟩ : syracuseStep 1628759 = 2443139) B2443139
theorem B1628825 : Blo 1084620 1628825 := bstep (se 2 (by rfl) ⟨610809, by rfl⟩ : syracuseStep 1628825 = 1221619) B1221619
theorem B2448089 : Blo 1084620 2448089 := bstep (se 2 (by rfl) ⟨918033, by rfl⟩ : syracuseStep 2448089 = 1836067) B1836067
theorem B1628939 : Blo 1084620 1628939 := bstep (se 1 (by rfl) ⟨1221704, by rfl⟩ : syracuseStep 1628939 = 2443409) B2443409
theorem B1628951 : Blo 1084620 1628951 := bstep (se 1 (by rfl) ⟨1221713, by rfl⟩ : syracuseStep 1628951 = 2443427) B2443427
theorem B2448179 : Blo 1084620 2448179 := bstep (se 1 (by rfl) ⟨1836134, by rfl⟩ : syracuseStep 2448179 = 3672269) B3672269
theorem B2448215 : Blo 1084620 2448215 := bstep (se 1 (by rfl) ⟨1836161, by rfl⟩ : syracuseStep 2448215 = 3672323) B3672323
theorem B1629017 : Blo 1084620 1629017 := bstep (se 2 (by rfl) ⟨610881, by rfl⟩ : syracuseStep 1629017 = 1221763) B1221763
theorem B2317195 : Blo 1084620 2317195 := bstep (se 1 (by rfl) ⟨1737896, by rfl⟩ : syracuseStep 2317195 = 3475793) B3475793
theorem B1629131 : Blo 1084620 1629131 := bstep (se 1 (by rfl) ⟨1221848, by rfl⟩ : syracuseStep 1629131 = 2443697) B2443697
theorem B1629143 : Blo 1084620 1629143 := bstep (se 1 (by rfl) ⟨1221857, by rfl⟩ : syracuseStep 1629143 = 2443715) B2443715
theorem B2448395 : Blo 1084620 2448395 := bstep (se 1 (by rfl) ⟨1836296, by rfl⟩ : syracuseStep 2448395 = 3672593) B3672593
theorem B1629209 : Blo 1084620 1629209 := bstep (se 2 (by rfl) ⟨610953, by rfl⟩ : syracuseStep 1629209 = 1221907) B1221907
theorem B4643891 : Blo 1084620 4643891 := bstep (se 1 (by rfl) ⟨3482918, by rfl⟩ : syracuseStep 4643891 = 6965837) B6965837
theorem B2448449 : Blo 1084620 2448449 := bstep (se 2 (by rfl) ⟨918168, by rfl⟩ : syracuseStep 2448449 = 1836337) B1836337
theorem B3660875 : Blo 1084620 3660875 := bstep (se 1 (by rfl) ⟨2745656, by rfl⟩ : syracuseStep 3660875 = 5491313) B5491313
theorem B1629323 : Blo 1084620 1629323 := bstep (se 1 (by rfl) ⟨1221992, by rfl⟩ : syracuseStep 1629323 = 2443985) B2443985
theorem B1629335 : Blo 1084620 1629335 := bstep (se 1 (by rfl) ⟨1222001, by rfl⟩ : syracuseStep 1629335 = 2444003) B2444003
theorem B1858711 : Blo 1084620 1858711 := bstep (se 1 (by rfl) ⟨1394033, by rfl⟩ : syracuseStep 1858711 = 2788067) B2788067
theorem B4119731 : Blo 1084620 4119731 := bstep (se 1 (by rfl) ⟨3089798, by rfl⟩ : syracuseStep 4119731 = 6179597) B6179597
theorem B1629401 : Blo 1084620 1629401 := bstep (se 2 (by rfl) ⟨611025, by rfl⟩ : syracuseStep 1629401 = 1222051) B1222051
theorem B2448665 : Blo 1084620 2448665 := bstep (se 2 (by rfl) ⟨918249, by rfl⟩ : syracuseStep 2448665 = 1836499) B1836499
theorem B1629515 : Blo 1084620 1629515 := bstep (se 1 (by rfl) ⟨1222136, by rfl⟩ : syracuseStep 1629515 = 2444273) B2444273
theorem B1629527 : Blo 1084620 1629527 := bstep (se 1 (by rfl) ⟨1222145, by rfl⟩ : syracuseStep 1629527 = 2444291) B2444291
theorem B3661145 : Blo 1084620 3661145 := bstep (se 2 (by rfl) ⟨1372929, by rfl⟩ : syracuseStep 3661145 = 2745859) B2745859
theorem B2448755 : Blo 1084620 2448755 := bstep (se 1 (by rfl) ⟨1836566, by rfl⟩ : syracuseStep 2448755 = 3673133) B3673133
theorem B2448791 : Blo 1084620 2448791 := bstep (se 1 (by rfl) ⟨1836593, by rfl⟩ : syracuseStep 2448791 = 3673187) B3673187
theorem B1629593 : Blo 1084620 1629593 := bstep (se 2 (by rfl) ⟨611097, by rfl⟩ : syracuseStep 1629593 = 1222195) B1222195
theorem B1629707 : Blo 1084620 1629707 := bstep (se 1 (by rfl) ⟨1222280, by rfl⟩ : syracuseStep 1629707 = 2444561) B2444561
theorem B1629719 : Blo 1084620 1629719 := bstep (se 1 (by rfl) ⟨1222289, by rfl⟩ : syracuseStep 1629719 = 2444579) B2444579
theorem B8248877 : Blo 1084620 8248877 := bstep (se 3 (by rfl) ⟨1546664, by rfl⟩ : syracuseStep 8248877 = 3093329) B3093329
theorem B1957441 : Blo 1084620 1957441 := bstep (se 2 (by rfl) ⟨734040, by rfl⟩ : syracuseStep 1957441 = 1468081) B1468081
theorem B2448971 : Blo 1084620 2448971 := bstep (se 1 (by rfl) ⟨1836728, by rfl⟩ : syracuseStep 2448971 = 3673457) B3673457
theorem B2317913 : Blo 1084620 2317913 := bstep (se 2 (by rfl) ⟨869217, by rfl⟩ : syracuseStep 2317913 = 1738435) B1738435
theorem B1629785 : Blo 1084620 1629785 := bstep (se 2 (by rfl) ⟨611169, by rfl⟩ : syracuseStep 1629785 = 1222339) B1222339
theorem B2449025 : Blo 1084620 2449025 := bstep (se 2 (by rfl) ⟨918384, by rfl⟩ : syracuseStep 2449025 = 1836769) B1836769
theorem B1629899 : Blo 1084620 1629899 := bstep (se 1 (by rfl) ⟨1222424, by rfl⟩ : syracuseStep 1629899 = 2444849) B2444849
theorem B1629911 : Blo 1084620 1629911 := bstep (se 1 (by rfl) ⟨1222433, by rfl⟩ : syracuseStep 1629911 = 2444867) B2444867
theorem B1629977 : Blo 1084620 1629977 := bstep (se 2 (by rfl) ⟨611241, by rfl⟩ : syracuseStep 1629977 = 1222483) B1222483
theorem B2449241 : Blo 1084620 2449241 := bstep (se 2 (by rfl) ⟨918465, by rfl⟩ : syracuseStep 2449241 = 1836931) B1836931
theorem B1630091 : Blo 1084620 1630091 := bstep (se 1 (by rfl) ⟨1222568, by rfl⟩ : syracuseStep 1630091 = 2445137) B2445137
theorem B1630103 : Blo 1084620 1630103 := bstep (se 1 (by rfl) ⟨1222577, by rfl⟩ : syracuseStep 1630103 = 2445155) B2445155
theorem B4186007 : Blo 1084620 4186007 := bstep (se 1 (by rfl) ⟨3139505, by rfl⟩ : syracuseStep 4186007 = 6279011) B6279011
theorem B2449331 : Blo 1084620 2449331 := bstep (se 1 (by rfl) ⟨1836998, by rfl⟩ : syracuseStep 2449331 = 3673997) B3673997
theorem B2940875 : Blo 1084620 2940875 := bstep (se 1 (by rfl) ⟨2205656, by rfl⟩ : syracuseStep 2940875 = 4411313) B4411313
theorem B2449367 : Blo 1084620 2449367 := bstep (se 1 (by rfl) ⟨1837025, by rfl⟩ : syracuseStep 2449367 = 3674051) B3674051
theorem B1630169 : Blo 1084620 1630169 := bstep (se 2 (by rfl) ⟨611313, by rfl⟩ : syracuseStep 1630169 = 1222627) B1222627
theorem B2318323 : Blo 1084620 2318323 := bstep (se 1 (by rfl) ⟨1738742, by rfl⟩ : syracuseStep 2318323 = 3477485) B3477485
theorem B3661847 : Blo 1084620 3661847 := bstep (se 1 (by rfl) ⟨2746385, by rfl⟩ : syracuseStep 3661847 = 5492771) B5492771
theorem B1630283 : Blo 1084620 1630283 := bstep (se 1 (by rfl) ⟨1222712, by rfl⟩ : syracuseStep 1630283 = 2445425) B2445425
theorem B2613323 : Blo 1084620 2613323 := bstep (se 1 (by rfl) ⟨1959992, by rfl⟩ : syracuseStep 2613323 = 3919985) B3919985
theorem B1630295 : Blo 1084620 1630295 := bstep (se 1 (by rfl) ⟨1222721, by rfl⟩ : syracuseStep 1630295 = 2445443) B2445443
theorem B5496983 : Blo 1084620 5496983 := bstep (se 1 (by rfl) ⟨4122737, by rfl⟩ : syracuseStep 5496983 = 8245475) B8245475
theorem B1630361 : Blo 1084620 1630361 := bstep (se 2 (by rfl) ⟨611385, by rfl⟩ : syracuseStep 1630361 = 1222771) B1222771
theorem B1630475 : Blo 1084620 1630475 := bstep (se 1 (by rfl) ⟨1222856, by rfl⟩ : syracuseStep 1630475 = 2445713) B2445713
theorem B62710037 : Blo 1084620 62710037 := bstep (se 6 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 62710037 = 2939533) B2939533
theorem B1630487 : Blo 1084620 1630487 := bstep (se 1 (by rfl) ⟨1222865, by rfl⟩ : syracuseStep 1630487 = 2445731) B2445731
theorem B1859915 : Blo 1084620 1859915 := bstep (se 1 (by rfl) ⟨1394936, by rfl⟩ : syracuseStep 1859915 = 2789873) B2789873
theorem B1630553 : Blo 1084620 1630553 := bstep (se 2 (by rfl) ⟨611457, by rfl⟩ : syracuseStep 1630553 = 1222915) B1222915
theorem B2351513 : Blo 1084620 2351513 := bstep (se 2 (by rfl) ⟨881817, by rfl⟩ : syracuseStep 2351513 = 1763635) B1763635
theorem B1630667 : Blo 1084620 1630667 := bstep (se 1 (by rfl) ⟨1223000, by rfl⟩ : syracuseStep 1630667 = 2446001) B2446001
theorem B1630679 : Blo 1084620 1630679 := bstep (se 1 (by rfl) ⟨1223009, by rfl⟩ : syracuseStep 1630679 = 2446019) B2446019
theorem B1630745 : Blo 1084620 1630745 := bstep (se 2 (by rfl) ⟨611529, by rfl⟩ : syracuseStep 1630745 = 1223059) B1223059
theorem B1860121 : Blo 1084620 1860121 := bstep (se 2 (by rfl) ⟨697545, by rfl⟩ : syracuseStep 1860121 = 1395091) B1395091
theorem B3662387 : Blo 1084620 3662387 := bstep (se 1 (by rfl) ⟨2746790, by rfl⟩ : syracuseStep 3662387 = 5493581) B5493581
theorem B4121219 : Blo 1084620 4121219 := bstep (se 1 (by rfl) ⟨3090914, by rfl⟩ : syracuseStep 4121219 = 6181829) B6181829
theorem B39608963 : Blo 1084620 39608963 := bstep (se 1 (by rfl) ⟨29706722, by rfl⟩ : syracuseStep 39608963 = 59413445) B59413445
theorem B1630859 : Blo 1084620 1630859 := bstep (se 1 (by rfl) ⟨1223144, by rfl⟩ : syracuseStep 1630859 = 2446289) B2446289
theorem B1630871 : Blo 1084620 1630871 := bstep (se 1 (by rfl) ⟨1223153, by rfl⟩ : syracuseStep 1630871 = 2446307) B2446307
theorem B1630937 : Blo 1084620 1630937 := bstep (se 2 (by rfl) ⟨611601, by rfl⟩ : syracuseStep 1630937 = 1223203) B1223203
theorem B1958681 : Blo 1084620 1958681 := bstep (se 2 (by rfl) ⟨734505, by rfl⟩ : syracuseStep 1958681 = 1469011) B1469011
theorem B3662657 : Blo 1084620 3662657 := bstep (se 2 (by rfl) ⟨1373496, by rfl⟩ : syracuseStep 3662657 = 2746993) B2746993
theorem B1631051 : Blo 1084620 1631051 := bstep (se 1 (by rfl) ⟨1223288, by rfl⟩ : syracuseStep 1631051 = 2446577) B2446577
theorem B1631063 : Blo 1084620 1631063 := bstep (se 1 (by rfl) ⟨1223297, by rfl⟩ : syracuseStep 1631063 = 2446595) B2446595
theorem B1631129 : Blo 1084620 1631129 := bstep (se 2 (by rfl) ⟨611673, by rfl⟩ : syracuseStep 1631129 = 1223347) B1223347
theorem B1631243 : Blo 1084620 1631243 := bstep (se 1 (by rfl) ⟨1223432, by rfl⟩ : syracuseStep 1631243 = 2446865) B2446865
theorem B1631255 : Blo 1084620 1631255 := bstep (se 1 (by rfl) ⟨1223441, by rfl⟩ : syracuseStep 1631255 = 2446883) B2446883
theorem B4121675 : Blo 1084620 4121675 := bstep (se 1 (by rfl) ⟨3091256, by rfl⟩ : syracuseStep 4121675 = 6182513) B6182513
theorem B4023371 : Blo 1084620 4023371 := bstep (se 1 (by rfl) ⟨3017528, by rfl⟩ : syracuseStep 4023371 = 6035057) B6035057
theorem B8479819 : Blo 1084620 8479819 := bstep (se 1 (by rfl) ⟨6359864, by rfl⟩ : syracuseStep 8479819 = 12719729) B12719729
theorem B1631321 : Blo 1084620 1631321 := bstep (se 2 (by rfl) ⟨611745, by rfl⟩ : syracuseStep 1631321 = 1223491) B1223491
theorem B4711517 : Blo 1084620 4711517 := bstep (se 3 (by rfl) ⟨883409, by rfl⟩ : syracuseStep 4711517 = 1766819) B1766819
theorem B2319511 : Blo 1084620 2319511 := bstep (se 1 (by rfl) ⟨1739633, by rfl⟩ : syracuseStep 2319511 = 3479267) B3479267
theorem B2319553 : Blo 1084620 2319553 := bstep (se 2 (by rfl) ⟨869832, by rfl⟩ : syracuseStep 2319553 = 1739665) B1739665
theorem B1631435 : Blo 1084620 1631435 := bstep (se 1 (by rfl) ⟨1223576, by rfl⟩ : syracuseStep 1631435 = 2447153) B2447153
theorem B1631447 : Blo 1084620 1631447 := bstep (se 1 (by rfl) ⟨1223585, by rfl⟩ : syracuseStep 1631447 = 2447171) B2447171
theorem B4121873 : Blo 1084620 4121873 := bstep (se 2 (by rfl) ⟨1545702, by rfl⟩ : syracuseStep 4121873 = 3091405) B3091405
theorem B1631513 : Blo 1084620 1631513 := bstep (se 2 (by rfl) ⟨611817, by rfl⟩ : syracuseStep 1631513 = 1223635) B1223635
theorem B3663197 : Blo 1084620 3663197 := bstep (se 3 (by rfl) ⟨686849, by rfl⟩ : syracuseStep 3663197 = 1373699) B1373699
theorem B1631627 : Blo 1084620 1631627 := bstep (se 1 (by rfl) ⟨1223720, by rfl⟩ : syracuseStep 1631627 = 2447441) B2447441
theorem B1631639 : Blo 1084620 1631639 := bstep (se 1 (by rfl) ⟨1223729, by rfl⟩ : syracuseStep 1631639 = 2447459) B2447459
theorem B1631705 : Blo 1084620 1631705 := bstep (se 2 (by rfl) ⟨611889, by rfl⟩ : syracuseStep 1631705 = 1223779) B1223779
theorem B3139037 : Blo 1084620 3139037 := bstep (se 3 (by rfl) ⟨588569, by rfl⟩ : syracuseStep 3139037 = 1177139) B1177139
theorem B1631819 : Blo 1084620 1631819 := bstep (se 1 (by rfl) ⟨1223864, by rfl⟩ : syracuseStep 1631819 = 2447729) B2447729
theorem B1631831 : Blo 1084620 1631831 := bstep (se 1 (by rfl) ⟨1223873, by rfl⟩ : syracuseStep 1631831 = 2447747) B2447747
theorem B1631897 : Blo 1084620 1631897 := bstep (se 2 (by rfl) ⟨611961, by rfl⟩ : syracuseStep 1631897 = 1223923) B1223923
theorem B1632011 : Blo 1084620 1632011 := bstep (se 1 (by rfl) ⟨1224008, by rfl⟩ : syracuseStep 1632011 = 2448017) B2448017
theorem B1632023 : Blo 1084620 1632023 := bstep (se 1 (by rfl) ⟨1224017, by rfl⟩ : syracuseStep 1632023 = 2448035) B2448035
theorem B2746163 : Blo 1084620 2746163 := bstep (se 1 (by rfl) ⟨2059622, by rfl⟩ : syracuseStep 2746163 = 4119245) B4119245
theorem B9398081 : Blo 1084620 9398081 := bstep (se 2 (by rfl) ⟨3524280, by rfl⟩ : syracuseStep 9398081 = 7048561) B7048561
theorem B1632089 : Blo 1084620 1632089 := bstep (se 2 (by rfl) ⟨612033, by rfl⟩ : syracuseStep 1632089 = 1224067) B1224067
theorem B1632203 : Blo 1084620 1632203 := bstep (se 1 (by rfl) ⟨1224152, by rfl⟩ : syracuseStep 1632203 = 2448305) B2448305
theorem B1632215 : Blo 1084620 1632215 := bstep (se 1 (by rfl) ⟨1224161, by rfl⟩ : syracuseStep 1632215 = 2448323) B2448323
theorem B4122647 : Blo 1084620 4122647 := bstep (se 1 (by rfl) ⟨3091985, by rfl⟩ : syracuseStep 4122647 = 6183971) B6183971
theorem B1632281 : Blo 1084620 1632281 := bstep (se 2 (by rfl) ⟨612105, by rfl⟩ : syracuseStep 1632281 = 1224211) B1224211
theorem B2746457 : Blo 1084620 2746457 := bstep (se 2 (by rfl) ⟨1029921, by rfl⟩ : syracuseStep 2746457 = 2059843) B2059843
theorem B1632395 : Blo 1084620 1632395 := bstep (se 1 (by rfl) ⟨1224296, by rfl⟩ : syracuseStep 1632395 = 2448593) B2448593
theorem B1632407 : Blo 1084620 1632407 := bstep (se 1 (by rfl) ⟨1224305, by rfl⟩ : syracuseStep 1632407 = 2448611) B2448611
theorem B2615447 : Blo 1084620 2615447 := bstep (se 1 (by rfl) ⟨1961585, by rfl⟩ : syracuseStep 2615447 = 3923171) B3923171
theorem B2091187 : Blo 1084620 2091187 := bstep (se 1 (by rfl) ⟨1568390, by rfl⟩ : syracuseStep 2091187 = 3136781) B3136781
theorem B1632473 : Blo 1084620 1632473 := bstep (se 2 (by rfl) ⟨612177, by rfl⟩ : syracuseStep 1632473 = 1224355) B1224355
theorem B4122845 : Blo 1084620 4122845 := bstep (se 3 (by rfl) ⟨773033, by rfl⟩ : syracuseStep 4122845 = 1546067) B1546067
theorem B1468697 : Blo 1084620 1468697 := bstep (se 2 (by rfl) ⟨550761, by rfl⟩ : syracuseStep 1468697 = 1101523) B1101523
theorem B1632587 : Blo 1084620 1632587 := bstep (se 1 (by rfl) ⟨1224440, by rfl⟩ : syracuseStep 1632587 = 2448881) B2448881
theorem B1632599 : Blo 1084620 1632599 := bstep (se 1 (by rfl) ⟨1224449, by rfl⟩ : syracuseStep 1632599 = 2448899) B2448899
theorem B38168981 : Blo 1084620 38168981 := bstep (se 6 (by rfl) ⟨894585, by rfl⟩ : syracuseStep 38168981 = 1789171) B1789171
theorem B1632665 : Blo 1084620 1632665 := bstep (se 2 (by rfl) ⟨612249, by rfl⟩ : syracuseStep 1632665 = 1224499) B1224499
theorem B3664331 : Blo 1084620 3664331 := bstep (se 1 (by rfl) ⟨2748248, by rfl⟩ : syracuseStep 3664331 = 5496497) B5496497
theorem B1632779 : Blo 1084620 1632779 := bstep (se 1 (by rfl) ⟨1224584, by rfl⟩ : syracuseStep 1632779 = 2449169) B2449169
theorem B1632791 : Blo 1084620 1632791 := bstep (se 1 (by rfl) ⟨1224593, by rfl⟩ : syracuseStep 1632791 = 2449187) B2449187
theorem B17885731 : Blo 1084620 17885731 := bstep (se 1 (by rfl) ⟨13414298, by rfl⟩ : syracuseStep 17885731 = 26828597) B26828597
theorem B1632857 : Blo 1084620 1632857 := bstep (se 2 (by rfl) ⟨612321, by rfl⟩ : syracuseStep 1632857 = 1224643) B1224643
theorem B15657623 : Blo 1084620 15657623 := bstep (se 1 (by rfl) ⟨11743217, by rfl⟩ : syracuseStep 15657623 = 23486435) B23486435
theorem B3664601 : Blo 1084620 3664601 := bstep (se 2 (by rfl) ⟨1374225, by rfl⟩ : syracuseStep 3664601 = 2748451) B2748451
theorem B2321227 : Blo 1084620 2321227 := bstep (se 1 (by rfl) ⟨1740920, by rfl⟩ : syracuseStep 2321227 = 3481841) B3481841
theorem B1174423 : Blo 1084620 1174423 := bstep (se 1 (by rfl) ⟨880817, by rfl⟩ : syracuseStep 1174423 = 1761635) B1761635
theorem B1469335 : Blo 1084620 1469335 := bstep (se 1 (by rfl) ⟨1102001, by rfl⟩ : syracuseStep 1469335 = 2204003) B2204003
theorem B12381335 : Blo 1084620 12381335 := bstep (se 1 (by rfl) ⟨9286001, by rfl⟩ : syracuseStep 12381335 = 18572003) B18572003
theorem B2321561 : Blo 1084620 2321561 := bstep (se 2 (by rfl) ⟨870585, by rfl⟩ : syracuseStep 2321561 = 1741171) B1741171
theorem B4648195 : Blo 1084620 4648195 := bstep (se 1 (by rfl) ⟨3486146, by rfl⟩ : syracuseStep 4648195 = 6972293) B6972293
theorem B2059607 : Blo 1084620 2059607 := bstep (se 1 (by rfl) ⟨1544705, by rfl⟩ : syracuseStep 2059607 = 3089411) B3089411
theorem B8252765 : Blo 1084620 8252765 := bstep (se 3 (by rfl) ⟨1547393, by rfl⟩ : syracuseStep 8252765 = 3094787) B3094787
theorem B22310261 : Blo 1084620 22310261 := bstep (se 5 (by rfl) ⟨1045793, by rfl⟩ : syracuseStep 22310261 = 2091587) B2091587
theorem B3665303 : Blo 1084620 3665303 := bstep (se 1 (by rfl) ⟨2748977, by rfl⟩ : syracuseStep 3665303 = 5497955) B5497955
theorem B1961419 : Blo 1084620 1961419 := bstep (se 1 (by rfl) ⟨1471064, by rfl⟩ : syracuseStep 1961419 = 2942129) B2942129
theorem B3763673 : Blo 1084620 3763673 := bstep (se 2 (by rfl) ⟨1411377, by rfl⟩ : syracuseStep 3763673 = 2822755) B2822755
theorem B5500547 : Blo 1084620 5500547 := bstep (se 1 (by rfl) ⟨4125410, by rfl⟩ : syracuseStep 5500547 = 8250821) B8250821
theorem B1830539 : Blo 1084620 1830539 := bstep (se 1 (by rfl) ⟨1372904, by rfl⟩ : syracuseStep 1830539 = 2745809) B2745809
theorem B1961651 : Blo 1084620 1961651 := bstep (se 1 (by rfl) ⟨1471238, by rfl⟩ : syracuseStep 1961651 = 2942477) B2942477
theorem B2748107 : Blo 1084620 2748107 := bstep (se 1 (by rfl) ⟨2061080, by rfl⟩ : syracuseStep 2748107 = 4122161) B4122161
theorem B1830667 : Blo 1084620 1830667 := bstep (se 1 (by rfl) ⟨1373000, by rfl⟩ : syracuseStep 1830667 = 2746001) B2746001
theorem B6188845 : Blo 1084620 6188845 := bstep (se 3 (by rfl) ⟨1160408, by rfl⟩ : syracuseStep 6188845 = 2320817) B2320817
theorem B2060147 : Blo 1084620 2060147 := bstep (se 1 (by rfl) ⟨1545110, by rfl⟩ : syracuseStep 2060147 = 3090221) B3090221
theorem B1830809 : Blo 1084620 1830809 := bstep (se 2 (by rfl) ⟨686553, by rfl⟩ : syracuseStep 1830809 = 1373107) B1373107
theorem B3665843 : Blo 1084620 3665843 := bstep (se 1 (by rfl) ⟨2749382, by rfl⟩ : syracuseStep 3665843 = 5498765) B5498765
theorem B1830937 : Blo 1084620 1830937 := bstep (se 2 (by rfl) ⟨686601, by rfl⟩ : syracuseStep 1830937 = 1373203) B1373203
theorem B4124803 : Blo 1084620 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B3666113 : Blo 1084620 3666113 := bstep (se 2 (by rfl) ⟨1374792, by rfl⟩ : syracuseStep 3666113 = 2749585) B2749585
theorem B1306955 : Blo 1084620 1306955 := bstep (se 1 (by rfl) ⟨980216, by rfl⟩ : syracuseStep 1306955 = 1960433) B1960433
theorem B2060633 : Blo 1084620 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B4125107 : Blo 1084620 4125107 := bstep (se 1 (by rfl) ⟨3093830, by rfl⟩ : syracuseStep 4125107 = 6187661) B6187661
theorem B1831511 : Blo 1084620 1831511 := bstep (se 1 (by rfl) ⟨1373633, by rfl⟩ : syracuseStep 1831511 = 2747267) B2747267
theorem B2323073 : Blo 1084620 2323073 := bstep (se 2 (by rfl) ⟨871152, by rfl⟩ : syracuseStep 2323073 = 1742305) B1742305
theorem B2749079 : Blo 1084620 2749079 := bstep (se 1 (by rfl) ⟨2061809, by rfl⟩ : syracuseStep 2749079 = 4123619) B4123619
theorem B1831639 : Blo 1084620 1831639 := bstep (se 1 (by rfl) ⟨1373729, by rfl⟩ : syracuseStep 1831639 = 2747459) B2747459
theorem B3666653 : Blo 1084620 3666653 := bstep (se 3 (by rfl) ⟨687497, by rfl⟩ : syracuseStep 3666653 = 1374995) B1374995
theorem B11760389 : Blo 1084620 11760389 := bstep (se 4 (by rfl) ⟨1102536, by rfl⟩ : syracuseStep 11760389 = 2205073) B2205073
theorem B4650007 : Blo 1084620 4650007 := bstep (se 1 (by rfl) ⟨3487505, by rfl⟩ : syracuseStep 4650007 = 6975011) B6975011
theorem B4125761 : Blo 1084620 4125761 := bstep (se 2 (by rfl) ⟨1547160, by rfl⟩ : syracuseStep 4125761 = 3094321) B3094321
theorem B2749747 : Blo 1084620 2749747 := bstep (se 1 (by rfl) ⟨2062310, by rfl⟩ : syracuseStep 2749747 = 4124621) B4124621
theorem B1832267 : Blo 1084620 1832267 := bstep (se 1 (by rfl) ⟨1374200, by rfl⟩ : syracuseStep 1832267 = 2748401) B2748401
theorem B1373527 : Blo 1084620 1373527 := bstep (se 1 (by rfl) ⟨1030145, by rfl⟩ : syracuseStep 1373527 = 2060291) B2060291
theorem B2749889 : Blo 1084620 2749889 := bstep (se 2 (by rfl) ⟨1031208, by rfl⟩ : syracuseStep 2749889 = 2062417) B2062417
theorem B1832395 : Blo 1084620 1832395 := bstep (se 1 (by rfl) ⟨1374296, by rfl⟩ : syracuseStep 1832395 = 2748593) B2748593
theorem B2323927 : Blo 1084620 2323927 := bstep (se 1 (by rfl) ⟨1742945, by rfl⟩ : syracuseStep 2323927 = 3485891) B3485891
theorem B1832537 : Blo 1084620 1832537 := bstep (se 2 (by rfl) ⟨687201, by rfl⟩ : syracuseStep 1832537 = 1374403) B1374403
theorem B9270935 : Blo 1084620 9270935 := bstep (se 1 (by rfl) ⟨6953201, by rfl⟩ : syracuseStep 9270935 = 13906403) B13906403
theorem B1832665 : Blo 1084620 1832665 := bstep (se 2 (by rfl) ⟨687249, by rfl⟩ : syracuseStep 1832665 = 1374499) B1374499
theorem B2062091 : Blo 1084620 2062091 := bstep (se 1 (by rfl) ⟨1546568, by rfl⟩ : syracuseStep 2062091 = 3093137) B3093137
theorem B3667787 : Blo 1084620 3667787 := bstep (se 1 (by rfl) ⟨2750840, by rfl⟩ : syracuseStep 3667787 = 5501681) B5501681
theorem B2062273 : Blo 1084620 2062273 := bstep (se 2 (by rfl) ⟨773352, by rfl⟩ : syracuseStep 2062273 = 1546705) B1546705
theorem B3668057 : Blo 1084620 3668057 := bstep (se 2 (by rfl) ⟨1375521, by rfl⟩ : syracuseStep 3668057 = 2751043) B2751043
theorem B1374347 : Blo 1084620 1374347 := bstep (se 1 (by rfl) ⟨1030760, by rfl⟩ : syracuseStep 1374347 = 2061521) B2061521
theorem B17627341 : Blo 1084620 17627341 := bstep (se 3 (by rfl) ⟨3305126, by rfl⟩ : syracuseStep 17627341 = 6610253) B6610253
theorem B2324747 : Blo 1084620 2324747 := bstep (se 1 (by rfl) ⟨1743560, by rfl⟩ : syracuseStep 2324747 = 3487121) B3487121
theorem B1833239 : Blo 1084620 1833239 := bstep (se 1 (by rfl) ⟨1374929, by rfl⟩ : syracuseStep 1833239 = 2749859) B2749859
theorem B4127021 : Blo 1084620 4127021 := bstep (se 3 (by rfl) ⟨773816, by rfl⟩ : syracuseStep 4127021 = 1547633) B1547633
theorem B4127051 : Blo 1084620 4127051 := bstep (se 1 (by rfl) ⟨3095288, by rfl⟩ : syracuseStep 4127051 = 6190577) B6190577
theorem B2062721 : Blo 1084620 2062721 := bstep (se 2 (by rfl) ⟨773520, by rfl⟩ : syracuseStep 2062721 = 1547041) B1547041
theorem B1833367 : Blo 1084620 1833367 := bstep (se 1 (by rfl) ⟨1375025, by rfl⟩ : syracuseStep 1833367 = 2750051) B2750051
theorem B5569175 : Blo 1084620 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B2751155 : Blo 1084620 2751155 := bstep (se 1 (by rfl) ⟨2063366, by rfl⟩ : syracuseStep 2751155 = 4126733) B4126733
theorem B2063063 : Blo 1084620 2063063 := bstep (se 1 (by rfl) ⟨1547297, by rfl⟩ : syracuseStep 2063063 = 3094595) B3094595
theorem B3668759 : Blo 1084620 3668759 := bstep (se 1 (by rfl) ⟨2751569, by rfl⟩ : syracuseStep 3668759 = 5503139) B5503139
theorem B5864237 : Blo 1084620 5864237 := bstep (se 3 (by rfl) ⟨1099544, by rfl⟩ : syracuseStep 5864237 = 2199089) B2199089
theorem B1375051 : Blo 1084620 1375051 := bstep (se 1 (by rfl) ⟨1031288, by rfl⟩ : syracuseStep 1375051 = 2062577) B2062577
theorem B4127705 : Blo 1084620 4127705 := bstep (se 2 (by rfl) ⟨1547889, by rfl⟩ : syracuseStep 4127705 = 3095779) B3095779
theorem B1833995 : Blo 1084620 1833995 := bstep (se 1 (by rfl) ⟨1375496, by rfl⟩ : syracuseStep 1833995 = 2750993) B2750993
theorem B1375319 : Blo 1084620 1375319 := bstep (se 1 (by rfl) ⟨1031489, by rfl⟩ : syracuseStep 1375319 = 2062979) B2062979
theorem B1834123 : Blo 1084620 1834123 := bstep (se 1 (by rfl) ⟨1375592, by rfl⟩ : syracuseStep 1834123 = 2751185) B2751185
theorem B2751691 : Blo 1084620 2751691 := bstep (se 1 (by rfl) ⟨2063768, by rfl⟩ : syracuseStep 2751691 = 4127537) B4127537
theorem B5504273 : Blo 1084620 5504273 := bstep (se 2 (by rfl) ⟨2064102, by rfl⟩ : syracuseStep 5504273 = 4128205) B4128205
theorem B4128023 : Blo 1084620 4128023 := bstep (se 1 (by rfl) ⟨3096017, by rfl⟩ : syracuseStep 4128023 = 6192035) B6192035
theorem B1834265 : Blo 1084620 1834265 := bstep (se 2 (by rfl) ⟨687849, by rfl⟩ : syracuseStep 1834265 = 1375699) B1375699
theorem B3669299 : Blo 1084620 3669299 := bstep (se 1 (by rfl) ⟨2751974, by rfl⟩ : syracuseStep 3669299 = 5503949) B5503949
theorem B2751833 : Blo 1084620 2751833 := bstep (se 2 (by rfl) ⟨1031937, by rfl⟩ : syracuseStep 2751833 = 2063875) B2063875
theorem B2063731 : Blo 1084620 2063731 := bstep (se 1 (by rfl) ⟨1547798, by rfl⟩ : syracuseStep 2063731 = 3095597) B3095597
theorem B1834393 : Blo 1084620 1834393 := bstep (se 2 (by rfl) ⟨687897, by rfl⟩ : syracuseStep 1834393 = 1375795) B1375795
theorem B5504435 : Blo 1084620 5504435 := bstep (se 1 (by rfl) ⟨4128326, by rfl⟩ : syracuseStep 5504435 = 8256653) B8256653
theorem B3964439 : Blo 1084620 3964439 := bstep (se 1 (by rfl) ⟨2973329, by rfl⟩ : syracuseStep 3964439 = 5946659) B5946659
theorem B3669569 : Blo 1084620 3669569 := bstep (se 2 (by rfl) ⟨1376088, by rfl⟩ : syracuseStep 3669569 = 2752177) B2752177
theorem B1376023 : Blo 1084620 1376023 := bstep (se 1 (by rfl) ⟨1032017, by rfl⟩ : syracuseStep 1376023 = 2064035) B2064035
theorem B2064179 : Blo 1084620 2064179 := bstep (se 1 (by rfl) ⟨1548134, by rfl⟩ : syracuseStep 2064179 = 3096269) B3096269
theorem B2064217 : Blo 1084620 2064217 := bstep (se 2 (by rfl) ⟨774081, by rfl⟩ : syracuseStep 2064217 = 1548163) B1548163
theorem B4128691 : Blo 1084620 4128691 := bstep (se 1 (by rfl) ⟨3096518, by rfl⟩ : syracuseStep 4128691 = 6193037) B6193037
theorem B1834967 : Blo 1084620 1834967 := bstep (se 1 (by rfl) ⟨1376225, by rfl⟩ : syracuseStep 1834967 = 2752451) B2752451
theorem B6193219 : Blo 1084620 6193219 := bstep (se 1 (by rfl) ⟨4644914, by rfl⟩ : syracuseStep 6193219 = 9289829) B9289829
theorem B1376443 : Blo 1084620 1376443 := bstep (se 1 (by rfl) ⟨1032332, by rfl⟩ : syracuseStep 1376443 = 2064665) B2064665
theorem B3670217 : Blo 1084620 3670217 := bstep (se 2 (by rfl) ⟨1376331, by rfl⟩ : syracuseStep 3670217 = 2752663) B2752663
theorem B1835399 : Blo 1084620 1835399 := bstep (se 1 (by rfl) ⟨1376549, by rfl⟩ : syracuseStep 1835399 = 2753099) B2753099
theorem B4129177 : Blo 1084620 4129177 := bstep (se 2 (by rfl) ⟨1548441, by rfl⟩ : syracuseStep 4129177 = 3096883) B3096883
theorem B1376939 : Blo 1084620 1376939 := bstep (se 1 (by rfl) ⟨1032704, by rfl⟩ : syracuseStep 1376939 = 2065409) B2065409
theorem B4129481 : Blo 1084620 4129481 := bstep (se 2 (by rfl) ⟨1548555, by rfl⟩ : syracuseStep 4129481 = 3097111) B3097111
theorem B2753291 : Blo 1084620 2753291 := bstep (se 1 (by rfl) ⟨2064968, by rfl⟩ : syracuseStep 2753291 = 4129937) B4129937
theorem B3670919 : Blo 1084620 3670919 := bstep (se 1 (by rfl) ⟨2753189, by rfl⟩ : syracuseStep 3670919 = 5506379) B5506379
theorem B1836047 : Blo 1084620 1836047 := bstep (se 1 (by rfl) ⟨1377035, by rfl⟩ : syracuseStep 1836047 = 2754071) B2754071
theorem B1377415 : Blo 1084620 1377415 := bstep (se 1 (by rfl) ⟨1033061, by rfl⟩ : syracuseStep 1377415 = 2066123) B2066123
theorem B3015937 : Blo 1084620 3015937 := bstep (se 2 (by rfl) ⟨1130976, by rfl⟩ : syracuseStep 3015937 = 2261953) B2261953
theorem B3671297 : Blo 1084620 3671297 := bstep (se 2 (by rfl) ⟨1376736, by rfl⟩ : syracuseStep 3671297 = 2753473) B2753473
theorem B2753939 : Blo 1084620 2753939 := bstep (se 1 (by rfl) ⟨2065454, by rfl⟩ : syracuseStep 2753939 = 4130909) B4130909
theorem B11306425 : Blo 1084620 11306425 := bstep (se 2 (by rfl) ⟨4239909, by rfl⟩ : syracuseStep 11306425 = 8479819) B8479819
theorem B1836587 : Blo 1084620 1836587 := bstep (se 1 (by rfl) ⟨1377440, by rfl⟩ : syracuseStep 1836587 = 2754881) B2754881
theorem B2065979 : Blo 1084620 2065979 := bstep (se 1 (by rfl) ⟨1549484, by rfl⟩ : syracuseStep 2065979 = 3098969) B3098969
theorem B4130423 : Blo 1084620 4130423 := bstep (se 1 (by rfl) ⟨3097817, by rfl⟩ : syracuseStep 4130423 = 6195635) B6195635
theorem B2754233 : Blo 1084620 2754233 := bstep (se 2 (by rfl) ⟨1032837, by rfl⟩ : syracuseStep 2754233 = 2065675) B2065675
theorem B11142947 : Blo 1084620 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B1836985 : Blo 1084620 1836985 := bstep (se 2 (by rfl) ⟨688869, by rfl⟩ : syracuseStep 1836985 = 1377739) B1377739
theorem B6195203 : Blo 1084620 6195203 := bstep (se 1 (by rfl) ⟨4646402, by rfl⟩ : syracuseStep 6195203 = 9292805) B9292805
theorem B2066465 : Blo 1084620 2066465 := bstep (se 2 (by rfl) ⟨774924, by rfl⟩ : syracuseStep 2066465 = 1549849) B1549849
theorem B3672107 : Blo 1084620 3672107 := bstep (se 1 (by rfl) ⟨2754080, by rfl⟩ : syracuseStep 3672107 = 5508161) B5508161
theorem B12388625 : Blo 1084620 12388625 := bstep (se 2 (by rfl) ⟨4645734, by rfl⟩ : syracuseStep 12388625 = 9291469) B9291469
theorem B2754931 : Blo 1084620 2754931 := bstep (se 1 (by rfl) ⟨2066198, by rfl⟩ : syracuseStep 2754931 = 4132397) B4132397
theorem B5507513 : Blo 1084620 5507513 := bstep (se 2 (by rfl) ⟨2065317, by rfl⟩ : syracuseStep 5507513 = 4130635) B4130635
theorem B2755073 : Blo 1084620 2755073 := bstep (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) B2066305
theorem B4131395 : Blo 1084620 4131395 := bstep (se 1 (by rfl) ⟨3098546, by rfl⟩ : syracuseStep 4131395 = 6197093) B6197093
theorem B6261563 : Blo 1084620 6261563 := bstep (se 1 (by rfl) ⟨4696172, by rfl⟩ : syracuseStep 6261563 = 9392345) B9392345
theorem B2755529 : Blo 1084620 2755529 := bstep (se 2 (by rfl) ⟨1033323, by rfl⟩ : syracuseStep 2755529 = 2066647) B2066647
theorem B1739819 : Blo 1084620 1739819 := bstep (se 1 (by rfl) ⟨1304864, by rfl⟩ : syracuseStep 1739819 = 2609729) B2609729
theorem B1084679 : Blo 1084620 1084679 := bstep (se 1 (by rfl) ⟨813509, by rfl⟩ : syracuseStep 1084679 = 1627019) B1627019
theorem B1084687 : Blo 1084620 1084687 := bstep (se 1 (by rfl) ⟨813515, by rfl⟩ : syracuseStep 1084687 = 1627031) B1627031
theorem B1084731 : Blo 1084620 1084731 := bstep (se 1 (by rfl) ⟨813548, by rfl⟩ : syracuseStep 1084731 = 1627097) B1627097
theorem B3673403 : Blo 1084620 3673403 := bstep (se 1 (by rfl) ⟨2755052, by rfl⟩ : syracuseStep 3673403 = 5510105) B5510105
theorem B1084807 : Blo 1084620 1084807 := bstep (se 1 (by rfl) ⟨813605, by rfl⟩ : syracuseStep 1084807 = 1627211) B1627211
theorem B1084815 : Blo 1084620 1084815 := bstep (se 1 (by rfl) ⟨813611, by rfl⟩ : syracuseStep 1084815 = 1627223) B1627223
theorem B1084859 : Blo 1084620 1084859 := bstep (se 1 (by rfl) ⟨813644, by rfl⟩ : syracuseStep 1084859 = 1627289) B1627289
theorem B1084935 : Blo 1084620 1084935 := bstep (se 1 (by rfl) ⟨813701, by rfl⟩ : syracuseStep 1084935 = 1627403) B1627403
theorem B1084943 : Blo 1084620 1084943 := bstep (se 1 (by rfl) ⟨813707, by rfl⟩ : syracuseStep 1084943 = 1627415) B1627415
theorem B1084987 : Blo 1084620 1084987 := bstep (se 1 (by rfl) ⟨813740, by rfl⟩ : syracuseStep 1084987 = 1627481) B1627481
theorem B1085063 : Blo 1084620 1085063 := bstep (se 1 (by rfl) ⟨813797, by rfl⟩ : syracuseStep 1085063 = 1627595) B1627595
theorem B1085071 : Blo 1084620 1085071 := bstep (se 1 (by rfl) ⟨813803, by rfl⟩ : syracuseStep 1085071 = 1627607) B1627607
theorem B1085115 : Blo 1084620 1085115 := bstep (se 1 (by rfl) ⟨813836, by rfl⟩ : syracuseStep 1085115 = 1627673) B1627673
theorem B5508809 : Blo 1084620 5508809 := bstep (se 2 (by rfl) ⟨2065803, by rfl⟩ : syracuseStep 5508809 = 4131607) B4131607
theorem B1085191 : Blo 1084620 1085191 := bstep (se 1 (by rfl) ⟨813893, by rfl⟩ : syracuseStep 1085191 = 1627787) B1627787
theorem B1085199 : Blo 1084620 1085199 := bstep (se 1 (by rfl) ⟨813899, by rfl⟩ : syracuseStep 1085199 = 1627799) B1627799
theorem B3673889 : Blo 1084620 3673889 := bstep (se 2 (by rfl) ⟨1377708, by rfl⟩ : syracuseStep 3673889 = 2755417) B2755417
theorem B1085243 : Blo 1084620 1085243 := bstep (se 1 (by rfl) ⟨813932, by rfl⟩ : syracuseStep 1085243 = 1627865) B1627865
theorem B1085319 : Blo 1084620 1085319 := bstep (se 1 (by rfl) ⟨813989, by rfl⟩ : syracuseStep 1085319 = 1627979) B1627979
theorem B1085327 : Blo 1084620 1085327 := bstep (se 1 (by rfl) ⟨813995, by rfl⟩ : syracuseStep 1085327 = 1627991) B1627991
theorem B3477433 : Blo 1084620 3477433 := bstep (se 2 (by rfl) ⟨1304037, by rfl⟩ : syracuseStep 3477433 = 2608075) B2608075
theorem B1085371 : Blo 1084620 1085371 := bstep (se 1 (by rfl) ⟨814028, by rfl⟩ : syracuseStep 1085371 = 1628057) B1628057
theorem B1085447 : Blo 1084620 1085447 := bstep (se 1 (by rfl) ⟨814085, by rfl⟩ : syracuseStep 1085447 = 1628171) B1628171
theorem B1085455 : Blo 1084620 1085455 := bstep (se 1 (by rfl) ⟨814091, by rfl⟩ : syracuseStep 1085455 = 1628183) B1628183
theorem B1085499 : Blo 1084620 1085499 := bstep (se 1 (by rfl) ⟨814124, by rfl⟩ : syracuseStep 1085499 = 1628249) B1628249
theorem B1085575 : Blo 1084620 1085575 := bstep (se 1 (by rfl) ⟨814181, by rfl⟩ : syracuseStep 1085575 = 1628363) B1628363
theorem B1085583 : Blo 1084620 1085583 := bstep (se 1 (by rfl) ⟨814187, by rfl⟩ : syracuseStep 1085583 = 1628375) B1628375
theorem B1085627 : Blo 1084620 1085627 := bstep (se 1 (by rfl) ⟨814220, by rfl⟩ : syracuseStep 1085627 = 1628441) B1628441
theorem B4133065 : Blo 1084620 4133065 := bstep (se 2 (by rfl) ⟨1549899, by rfl⟩ : syracuseStep 4133065 = 3099799) B3099799
theorem B1544455 : Blo 1084620 1544455 := bstep (se 1 (by rfl) ⟨1158341, by rfl⟩ : syracuseStep 1544455 = 2316683) B2316683
theorem B1085703 : Blo 1084620 1085703 := bstep (se 1 (by rfl) ⟨814277, by rfl⟩ : syracuseStep 1085703 = 1628555) B1628555
theorem B1085711 : Blo 1084620 1085711 := bstep (se 1 (by rfl) ⟨814283, by rfl⟩ : syracuseStep 1085711 = 1628567) B1628567
theorem B10424609 : Blo 1084620 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B1085755 : Blo 1084620 1085755 := bstep (se 1 (by rfl) ⟨814316, by rfl⟩ : syracuseStep 1085755 = 1628633) B1628633
theorem B6197593 : Blo 1084620 6197593 := bstep (se 2 (by rfl) ⟨2324097, by rfl⟩ : syracuseStep 6197593 = 4648195) B4648195
theorem B1085831 : Blo 1084620 1085831 := bstep (se 1 (by rfl) ⟨814373, by rfl⟩ : syracuseStep 1085831 = 1628747) B1628747
theorem B1085839 : Blo 1084620 1085839 := bstep (se 1 (by rfl) ⟨814379, by rfl⟩ : syracuseStep 1085839 = 1628759) B1628759
theorem B1085883 : Blo 1084620 1085883 := bstep (se 1 (by rfl) ⟨814412, by rfl⟩ : syracuseStep 1085883 = 1628825) B1628825
theorem B1085959 : Blo 1084620 1085959 := bstep (se 1 (by rfl) ⟨814469, by rfl⟩ : syracuseStep 1085959 = 1628939) B1628939
theorem B1085967 : Blo 1084620 1085967 := bstep (se 1 (by rfl) ⟨814475, by rfl⟩ : syracuseStep 1085967 = 1628951) B1628951
theorem B1086011 : Blo 1084620 1086011 := bstep (se 1 (by rfl) ⟨814508, by rfl⟩ : syracuseStep 1086011 = 1629017) B1629017
theorem B1086087 : Blo 1084620 1086087 := bstep (se 1 (by rfl) ⟨814565, by rfl⟩ : syracuseStep 1086087 = 1629131) B1629131
theorem B1086095 : Blo 1084620 1086095 := bstep (se 1 (by rfl) ⟨814571, by rfl⟩ : syracuseStep 1086095 = 1629143) B1629143
theorem B1086139 : Blo 1084620 1086139 := bstep (se 1 (by rfl) ⟨814604, by rfl⟩ : syracuseStep 1086139 = 1629209) B1629209
theorem B44634817 : Blo 1084620 44634817 := bstep (se 2 (by rfl) ⟨16738056, by rfl⟩ : syracuseStep 44634817 = 33476113) B33476113
theorem B1086215 : Blo 1084620 1086215 := bstep (se 1 (by rfl) ⟨814661, by rfl⟩ : syracuseStep 1086215 = 1629323) B1629323
theorem B1086223 : Blo 1084620 1086223 := bstep (se 1 (by rfl) ⟨814667, by rfl⟩ : syracuseStep 1086223 = 1629335) B1629335
theorem B1086267 : Blo 1084620 1086267 := bstep (se 1 (by rfl) ⟨814700, by rfl⟩ : syracuseStep 1086267 = 1629401) B1629401
theorem B1086343 : Blo 1084620 1086343 := bstep (se 1 (by rfl) ⟨814757, by rfl⟩ : syracuseStep 1086343 = 1629515) B1629515
theorem B1086351 : Blo 1084620 1086351 := bstep (se 1 (by rfl) ⟨814763, by rfl⟩ : syracuseStep 1086351 = 1629527) B1629527
theorem B1086395 : Blo 1084620 1086395 := bstep (se 1 (by rfl) ⟨814796, by rfl⟩ : syracuseStep 1086395 = 1629593) B1629593
theorem B1545161 : Blo 1084620 1545161 := bstep (se 2 (by rfl) ⟨579435, by rfl⟩ : syracuseStep 1545161 = 1158871) B1158871
theorem B1086471 : Blo 1084620 1086471 := bstep (se 1 (by rfl) ⟨814853, by rfl⟩ : syracuseStep 1086471 = 1629707) B1629707
theorem B1086479 : Blo 1084620 1086479 := bstep (se 1 (by rfl) ⟨814859, by rfl⟩ : syracuseStep 1086479 = 1629719) B1629719
theorem B1545275 : Blo 1084620 1545275 := bstep (se 1 (by rfl) ⟨1158956, by rfl⟩ : syracuseStep 1545275 = 2317913) B2317913
theorem B1086523 : Blo 1084620 1086523 := bstep (se 1 (by rfl) ⟨814892, by rfl⟩ : syracuseStep 1086523 = 1629785) B1629785
theorem B12391541 : Blo 1084620 12391541 := bstep (se 5 (by rfl) ⟨580853, by rfl⟩ : syracuseStep 12391541 = 1161707) B1161707
theorem B1086599 : Blo 1084620 1086599 := bstep (se 1 (by rfl) ⟨814949, by rfl⟩ : syracuseStep 1086599 = 1629899) B1629899
theorem B1086607 : Blo 1084620 1086607 := bstep (se 1 (by rfl) ⟨814955, by rfl⟩ : syracuseStep 1086607 = 1629911) B1629911
theorem B1086651 : Blo 1084620 1086651 := bstep (se 1 (by rfl) ⟨814988, by rfl⟩ : syracuseStep 1086651 = 1629977) B1629977
theorem B1086727 : Blo 1084620 1086727 := bstep (se 1 (by rfl) ⟨815045, by rfl⟩ : syracuseStep 1086727 = 1630091) B1630091
theorem B1086735 : Blo 1084620 1086735 := bstep (se 1 (by rfl) ⟨815051, by rfl⟩ : syracuseStep 1086735 = 1630103) B1630103
theorem B2790671 : Blo 1084620 2790671 := bstep (se 1 (by rfl) ⟨2093003, by rfl⟩ : syracuseStep 2790671 = 4186007) B4186007
theorem B1086779 : Blo 1084620 1086779 := bstep (se 1 (by rfl) ⟨815084, by rfl⟩ : syracuseStep 1086779 = 1630169) B1630169
theorem B8262971 : Blo 1084620 8262971 := bstep (se 1 (by rfl) ⟨6197228, by rfl⟩ : syracuseStep 8262971 = 12394457) B12394457
theorem B1086855 : Blo 1084620 1086855 := bstep (se 1 (by rfl) ⟨815141, by rfl⟩ : syracuseStep 1086855 = 1630283) B1630283
theorem B1086863 : Blo 1084620 1086863 := bstep (se 1 (by rfl) ⟨815147, by rfl⟩ : syracuseStep 1086863 = 1630295) B1630295
theorem B1086907 : Blo 1084620 1086907 := bstep (se 1 (by rfl) ⟨815180, by rfl⟩ : syracuseStep 1086907 = 1630361) B1630361
theorem B1086983 : Blo 1084620 1086983 := bstep (se 1 (by rfl) ⟨815237, by rfl⟩ : syracuseStep 1086983 = 1630475) B1630475
theorem B1086991 : Blo 1084620 1086991 := bstep (se 1 (by rfl) ⟨815243, by rfl⟩ : syracuseStep 1086991 = 1630487) B1630487
theorem B1087035 : Blo 1084620 1087035 := bstep (se 1 (by rfl) ⟨815276, by rfl⟩ : syracuseStep 1087035 = 1630553) B1630553
theorem B1087111 : Blo 1084620 1087111 := bstep (se 1 (by rfl) ⟨815333, by rfl⟩ : syracuseStep 1087111 = 1630667) B1630667
theorem B1087119 : Blo 1084620 1087119 := bstep (se 1 (by rfl) ⟨815339, by rfl⟩ : syracuseStep 1087119 = 1630679) B1630679
theorem B1545913 : Blo 1084620 1545913 := bstep (se 2 (by rfl) ⟨579717, by rfl⟩ : syracuseStep 1545913 = 1159435) B1159435
theorem B1087163 : Blo 1084620 1087163 := bstep (se 1 (by rfl) ⟨815372, by rfl⟩ : syracuseStep 1087163 = 1630745) B1630745
theorem B1087239 : Blo 1084620 1087239 := bstep (se 1 (by rfl) ⟨815429, by rfl⟩ : syracuseStep 1087239 = 1630859) B1630859
theorem B1087247 : Blo 1084620 1087247 := bstep (se 1 (by rfl) ⟨815435, by rfl⟩ : syracuseStep 1087247 = 1630871) B1630871
theorem B1087291 : Blo 1084620 1087291 := bstep (se 1 (by rfl) ⟨815468, by rfl⟩ : syracuseStep 1087291 = 1630937) B1630937
theorem B1087367 : Blo 1084620 1087367 := bstep (se 1 (by rfl) ⟨815525, by rfl⟩ : syracuseStep 1087367 = 1631051) B1631051
theorem B1087375 : Blo 1084620 1087375 := bstep (se 1 (by rfl) ⟨815531, by rfl⟩ : syracuseStep 1087375 = 1631063) B1631063
theorem B1087419 : Blo 1084620 1087419 := bstep (se 1 (by rfl) ⟨815564, by rfl⟩ : syracuseStep 1087419 = 1631129) B1631129
theorem B1087495 : Blo 1084620 1087495 := bstep (se 1 (by rfl) ⟨815621, by rfl⟩ : syracuseStep 1087495 = 1631243) B1631243
theorem B1087503 : Blo 1084620 1087503 := bstep (se 1 (by rfl) ⟨815627, by rfl⟩ : syracuseStep 1087503 = 1631255) B1631255
theorem B6199325 : Blo 1084620 6199325 := bstep (se 3 (by rfl) ⟨1162373, by rfl⟩ : syracuseStep 6199325 = 2324747) B2324747
theorem B1087547 : Blo 1084620 1087547 := bstep (se 1 (by rfl) ⟨815660, by rfl⟩ : syracuseStep 1087547 = 1631321) B1631321
theorem B1087623 : Blo 1084620 1087623 := bstep (se 1 (by rfl) ⟨815717, by rfl⟩ : syracuseStep 1087623 = 1631435) B1631435
theorem B1087631 : Blo 1084620 1087631 := bstep (se 1 (by rfl) ⟨815723, by rfl⟩ : syracuseStep 1087631 = 1631447) B1631447
theorem B1087675 : Blo 1084620 1087675 := bstep (se 1 (by rfl) ⟨815756, by rfl⟩ : syracuseStep 1087675 = 1631513) B1631513
theorem B1087751 : Blo 1084620 1087751 := bstep (se 1 (by rfl) ⟨815813, by rfl⟩ : syracuseStep 1087751 = 1631627) B1631627
theorem B1087759 : Blo 1084620 1087759 := bstep (se 1 (by rfl) ⟨815819, by rfl⟩ : syracuseStep 1087759 = 1631639) B1631639
theorem B1087803 : Blo 1084620 1087803 := bstep (se 1 (by rfl) ⟨815852, by rfl⟩ : syracuseStep 1087803 = 1631705) B1631705
theorem B1087879 : Blo 1084620 1087879 := bstep (se 1 (by rfl) ⟨815909, by rfl⟩ : syracuseStep 1087879 = 1631819) B1631819
theorem B1087887 : Blo 1084620 1087887 := bstep (se 1 (by rfl) ⟨815915, by rfl⟩ : syracuseStep 1087887 = 1631831) B1631831
theorem B3021209 : Blo 1084620 3021209 := bstep (se 2 (by rfl) ⟨1132953, by rfl⟩ : syracuseStep 3021209 = 2265907) B2265907
theorem B4954553 : Blo 1084620 4954553 := bstep (se 2 (by rfl) ⟨1857957, by rfl⟩ : syracuseStep 4954553 = 3715915) B3715915
theorem B1087931 : Blo 1084620 1087931 := bstep (se 1 (by rfl) ⟨815948, by rfl⟩ : syracuseStep 1087931 = 1631897) B1631897
theorem B3348937 : Blo 1084620 3348937 := bstep (se 2 (by rfl) ⟨1255851, by rfl⟩ : syracuseStep 3348937 = 2511703) B2511703
theorem B1088007 : Blo 1084620 1088007 := bstep (se 1 (by rfl) ⟨816005, by rfl⟩ : syracuseStep 1088007 = 1632011) B1632011
theorem B1088015 : Blo 1084620 1088015 := bstep (se 1 (by rfl) ⟨816011, by rfl⟩ : syracuseStep 1088015 = 1632023) B1632023
theorem B6265387 : Blo 1084620 6265387 := bstep (se 1 (by rfl) ⟨4699040, by rfl⟩ : syracuseStep 6265387 = 9398081) B9398081
theorem B1088059 : Blo 1084620 1088059 := bstep (se 1 (by rfl) ⟨816044, by rfl⟩ : syracuseStep 1088059 = 1632089) B1632089
theorem B1088135 : Blo 1084620 1088135 := bstep (se 1 (by rfl) ⟨816101, by rfl⟩ : syracuseStep 1088135 = 1632203) B1632203
theorem B1088143 : Blo 1084620 1088143 := bstep (se 1 (by rfl) ⟨816107, by rfl⟩ : syracuseStep 1088143 = 1632215) B1632215
theorem B5872301 : Blo 1084620 5872301 := bstep (se 3 (by rfl) ⟨1101056, by rfl⟩ : syracuseStep 5872301 = 2202113) B2202113
theorem B1088187 : Blo 1084620 1088187 := bstep (se 1 (by rfl) ⟨816140, by rfl⟩ : syracuseStep 1088187 = 1632281) B1632281
theorem B6200009 : Blo 1084620 6200009 := bstep (se 2 (by rfl) ⟨2325003, by rfl⟩ : syracuseStep 6200009 = 4650007) B4650007
theorem B1088263 : Blo 1084620 1088263 := bstep (se 1 (by rfl) ⟨816197, by rfl⟩ : syracuseStep 1088263 = 1632395) B1632395
theorem B1088271 : Blo 1084620 1088271 := bstep (se 1 (by rfl) ⟨816203, by rfl⟩ : syracuseStep 1088271 = 1632407) B1632407
theorem B1088315 : Blo 1084620 1088315 := bstep (se 1 (by rfl) ⟨816236, by rfl⟩ : syracuseStep 1088315 = 1632473) B1632473
theorem B1088391 : Blo 1084620 1088391 := bstep (se 1 (by rfl) ⟨816293, by rfl⟩ : syracuseStep 1088391 = 1632587) B1632587
theorem B1088399 : Blo 1084620 1088399 := bstep (se 1 (by rfl) ⟨816299, by rfl⟩ : syracuseStep 1088399 = 1632599) B1632599
theorem B1088443 : Blo 1084620 1088443 := bstep (se 1 (by rfl) ⟨816332, by rfl⟩ : syracuseStep 1088443 = 1632665) B1632665
theorem B1088519 : Blo 1084620 1088519 := bstep (se 1 (by rfl) ⟨816389, by rfl⟩ : syracuseStep 1088519 = 1632779) B1632779
theorem B1088527 : Blo 1084620 1088527 := bstep (se 1 (by rfl) ⟨816395, by rfl⟩ : syracuseStep 1088527 = 1632791) B1632791
theorem B1088571 : Blo 1084620 1088571 := bstep (se 1 (by rfl) ⟨816428, by rfl⟩ : syracuseStep 1088571 = 1632857) B1632857
theorem B14851133 : Blo 1084620 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B1220359 : Blo 1084620 1220359 := bstep (se 1 (by rfl) ⟨915269, by rfl⟩ : syracuseStep 1220359 = 1830539) B1830539
theorem B1220539 : Blo 1084620 1220539 := bstep (se 1 (by rfl) ⟨915404, by rfl⟩ : syracuseStep 1220539 = 1830809) B1830809
theorem B20848913 : Blo 1084620 20848913 := bstep (se 2 (by rfl) ⟨7818342, by rfl⟩ : syracuseStep 20848913 = 15636685) B15636685
theorem B23503121 : Blo 1084620 23503121 := bstep (se 2 (by rfl) ⟨8813670, by rfl⟩ : syracuseStep 23503121 = 17627341) B17627341
theorem B2203937 : Blo 1084620 2203937 := bstep (se 2 (by rfl) ⟨826476, by rfl⟩ : syracuseStep 2203937 = 1652953) B1652953
theorem B11739451 : Blo 1084620 11739451 := bstep (se 1 (by rfl) ⟨8804588, by rfl⟩ : syracuseStep 11739451 = 17609177) B17609177
theorem B1221007 : Blo 1084620 1221007 := bstep (se 1 (by rfl) ⟨915755, by rfl⟩ : syracuseStep 1221007 = 1831511) B1831511
theorem B1548715 : Blo 1084620 1548715 := bstep (se 1 (by rfl) ⟨1161536, by rfl⟩ : syracuseStep 1548715 = 2323073) B2323073
theorem B7840259 : Blo 1084620 7840259 := bstep (se 1 (by rfl) ⟨5880194, by rfl⟩ : syracuseStep 7840259 = 11760389) B11760389
theorem B3088955 : Blo 1084620 3088955 := bstep (se 1 (by rfl) ⟨2316716, by rfl⟩ : syracuseStep 3088955 = 4633433) B4633433
theorem B7840601 : Blo 1084620 7840601 := bstep (se 2 (by rfl) ⟨2940225, by rfl⟩ : syracuseStep 7840601 = 5880451) B5880451
theorem B1221511 : Blo 1084620 1221511 := bstep (se 1 (by rfl) ⟨916133, by rfl⟩ : syracuseStep 1221511 = 1832267) B1832267
theorem B5219225 : Blo 1084620 5219225 := bstep (se 2 (by rfl) ⟨1957209, by rfl⟩ : syracuseStep 5219225 = 3914419) B3914419
theorem B1221691 : Blo 1084620 1221691 := bstep (se 1 (by rfl) ⟨916268, by rfl⟩ : syracuseStep 1221691 = 1832537) B1832537
theorem B3089593 : Blo 1084620 3089593 := bstep (se 2 (by rfl) ⟨1158597, by rfl⟩ : syracuseStep 3089593 = 2317195) B2317195
theorem B3482995 : Blo 1084620 3482995 := bstep (se 1 (by rfl) ⟨2612246, by rfl⟩ : syracuseStep 3482995 = 5224493) B5224493
theorem B1222159 : Blo 1084620 1222159 := bstep (se 1 (by rfl) ⟨916619, by rfl⟩ : syracuseStep 1222159 = 1833239) B1833239
theorem B3089981 : Blo 1084620 3089981 := bstep (se 3 (by rfl) ⟨579371, by rfl⟩ : syracuseStep 3089981 = 1158743) B1158743
theorem B6367027 : Blo 1084620 6367027 := bstep (se 1 (by rfl) ⟨4775270, by rfl⟩ : syracuseStep 6367027 = 9550541) B9550541
theorem B3909491 : Blo 1084620 3909491 := bstep (se 1 (by rfl) ⟨2932118, by rfl⟩ : syracuseStep 3909491 = 5864237) B5864237
theorem B1222663 : Blo 1084620 1222663 := bstep (se 1 (by rfl) ⟨916997, by rfl⟩ : syracuseStep 1222663 = 1833995) B1833995
theorem B1222843 : Blo 1084620 1222843 := bstep (se 1 (by rfl) ⟨917132, by rfl⟩ : syracuseStep 1222843 = 1834265) B1834265
theorem B1223311 : Blo 1084620 1223311 := bstep (se 1 (by rfl) ⟨917483, by rfl⟩ : syracuseStep 1223311 = 1834967) B1834967
theorem B3091097 : Blo 1084620 3091097 := bstep (se 2 (by rfl) ⟨1159161, by rfl⟩ : syracuseStep 3091097 = 2318323) B2318323
theorem B6957839 : Blo 1084620 6957839 := bstep (se 1 (by rfl) ⟨5218379, by rfl⟩ : syracuseStep 6957839 = 10436759) B10436759
theorem B9055091 : Blo 1084620 9055091 := bstep (se 1 (by rfl) ⟨6791318, by rfl⟩ : syracuseStep 9055091 = 13582637) B13582637
theorem B13216715 : Blo 1084620 13216715 := bstep (se 1 (by rfl) ⟨9912536, by rfl⟩ : syracuseStep 13216715 = 19825073) B19825073
theorem B8825867 : Blo 1084620 8825867 := bstep (se 1 (by rfl) ⟨6619400, by rfl⟩ : syracuseStep 8825867 = 13238801) B13238801
theorem B7056407 : Blo 1084620 7056407 := bstep (se 1 (by rfl) ⟨5292305, by rfl⟩ : syracuseStep 7056407 = 10584611) B10584611
theorem B1223815 : Blo 1084620 1223815 := bstep (se 1 (by rfl) ⟨917861, by rfl⟩ : syracuseStep 1223815 = 1835723) B1835723
theorem B1223995 : Blo 1084620 1223995 := bstep (se 1 (by rfl) ⟨917996, by rfl⟩ : syracuseStep 1223995 = 1835993) B1835993
theorem B6598097 : Blo 1084620 6598097 := bstep (se 2 (by rfl) ⟨2474286, by rfl⟩ : syracuseStep 6598097 = 4948573) B4948573
theorem B27831761 : Blo 1084620 27831761 := bstep (se 2 (by rfl) ⟨10436910, by rfl⟩ : syracuseStep 27831761 = 20873821) B20873821
theorem B3485213 : Blo 1084620 3485213 := bstep (se 3 (by rfl) ⟨653477, by rfl⟩ : syracuseStep 3485213 = 1306955) B1306955
theorem B11152997 : Blo 1084620 11152997 := bstep (se 4 (by rfl) ⟨1045593, by rfl⟩ : syracuseStep 11152997 = 2091187) B2091187
theorem B6598381 : Blo 1084620 6598381 := bstep (se 3 (by rfl) ⟨1237196, by rfl⟩ : syracuseStep 6598381 = 2474393) B2474393
theorem B1224463 : Blo 1084620 1224463 := bstep (se 1 (by rfl) ⟨918347, by rfl⟩ : syracuseStep 1224463 = 1836695) B1836695
theorem B6696755 : Blo 1084620 6696755 := bstep (se 1 (by rfl) ⟨5022566, by rfl⟩ : syracuseStep 6696755 = 10045133) B10045133
theorem B3092509 : Blo 1084620 3092509 := bstep (se 3 (by rfl) ⟨579845, by rfl⟩ : syracuseStep 3092509 = 1159691) B1159691
theorem B20852909 : Blo 1084620 20852909 := bstep (se 3 (by rfl) ⟨3909920, by rfl⟩ : syracuseStep 20852909 = 7819841) B7819841
theorem B3092681 : Blo 1084620 3092681 := bstep (se 2 (by rfl) ⟨1159755, by rfl⟩ : syracuseStep 3092681 = 2319511) B2319511
theorem B3092737 : Blo 1084620 3092737 := bstep (se 2 (by rfl) ⟨1159776, by rfl⟩ : syracuseStep 3092737 = 2319553) B2319553
theorem B12890503 : Blo 1084620 12890503 := bstep (se 1 (by rfl) ⟨9667877, by rfl⟩ : syracuseStep 12890503 = 19335755) B19335755
theorem B1159687 : Blo 1084620 1159687 := bstep (se 1 (by rfl) ⟨869765, by rfl⟩ : syracuseStep 1159687 = 1739531) B1739531
theorem B3912259 : Blo 1084620 3912259 := bstep (se 1 (by rfl) ⟨2934194, by rfl⟩ : syracuseStep 3912259 = 5868389) B5868389
theorem B3093079 : Blo 1084620 3093079 := bstep (se 1 (by rfl) ⟨2319809, by rfl⟩ : syracuseStep 3093079 = 4639619) B4639619
theorem B5223149 : Blo 1084620 5223149 := bstep (se 3 (by rfl) ⟨979340, by rfl⟩ : syracuseStep 5223149 = 1958681) B1958681
theorem B12366755 : Blo 1084620 12366755 := bstep (se 1 (by rfl) ⟨9275066, by rfl⟩ : syracuseStep 12366755 = 18550133) B18550133
theorem B4175479 : Blo 1084620 4175479 := bstep (se 1 (by rfl) ⟨3131609, by rfl⟩ : syracuseStep 4175479 = 6263219) B6263219
theorem B1652395 : Blo 1084620 1652395 := bstep (se 1 (by rfl) ⟨1239296, by rfl⟩ : syracuseStep 1652395 = 2478593) B2478593
theorem B5879567 : Blo 1084620 5879567 := bstep (se 1 (by rfl) ⟨4409675, by rfl⟩ : syracuseStep 5879567 = 8819351) B8819351
theorem B10434419 : Blo 1084620 10434419 := bstep (se 1 (by rfl) ⟨7825814, by rfl⟩ : syracuseStep 10434419 = 15651629) B15651629
theorem B1325099 : Blo 1084620 1325099 := bstep (se 1 (by rfl) ⟨993824, by rfl⟩ : syracuseStep 1325099 = 1987649) B1987649
theorem B4176143 : Blo 1084620 4176143 := bstep (se 1 (by rfl) ⟨3132107, by rfl⟩ : syracuseStep 4176143 = 6264215) B6264215
theorem B2931913 : Blo 1084620 2931913 := bstep (se 2 (by rfl) ⟨1099467, by rfl⟩ : syracuseStep 2931913 = 2198935) B2198935
theorem B3095927 : Blo 1084620 3095927 := bstep (se 1 (by rfl) ⟨2321945, by rfl⟩ : syracuseStep 3095927 = 4643891) B4643891
theorem B2440583 : Blo 1084620 2440583 := bstep (se 1 (by rfl) ⟨1830437, by rfl⟩ : syracuseStep 2440583 = 3660875) B3660875
theorem B2440763 : Blo 1084620 2440763 := bstep (se 1 (by rfl) ⟨1830572, by rfl⟩ : syracuseStep 2440763 = 3661145) B3661145
theorem B2440889 : Blo 1084620 2440889 := bstep (se 2 (by rfl) ⟨915333, by rfl⟩ : syracuseStep 2440889 = 1830667) B1830667
theorem B7061185 : Blo 1084620 7061185 := bstep (se 2 (by rfl) ⟨2647944, by rfl⟩ : syracuseStep 7061185 = 5295889) B5295889
theorem B2441231 : Blo 1084620 2441231 := bstep (se 1 (by rfl) ⟨1830923, by rfl⟩ : syracuseStep 2441231 = 3661847) B3661847
theorem B2441249 : Blo 1084620 2441249 := bstep (se 2 (by rfl) ⟨915468, by rfl⟩ : syracuseStep 2441249 = 1830937) B1830937
theorem B3915863 : Blo 1084620 3915863 := bstep (se 1 (by rfl) ⟨2936897, by rfl⟩ : syracuseStep 3915863 = 5873795) B5873795
theorem B2441591 : Blo 1084620 2441591 := bstep (se 1 (by rfl) ⟨1831193, by rfl⟩ : syracuseStep 2441591 = 3662387) B3662387
theorem B2933177 : Blo 1084620 2933177 := bstep (se 2 (by rfl) ⟨1099941, by rfl⟩ : syracuseStep 2933177 = 2199883) B2199883
theorem B2933263 : Blo 1084620 2933263 := bstep (se 1 (by rfl) ⟨2199947, by rfl⟩ : syracuseStep 2933263 = 4399895) B4399895
theorem B2441771 : Blo 1084620 2441771 := bstep (se 1 (by rfl) ⟨1831328, by rfl⟩ : syracuseStep 2441771 = 3662657) B3662657
theorem B5227051 : Blo 1084620 5227051 := bstep (se 1 (by rfl) ⟨3920288, by rfl⟩ : syracuseStep 5227051 = 7840577) B7840577
theorem B3916525 : Blo 1084620 3916525 := bstep (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) B1468697
theorem B9061121 : Blo 1084620 9061121 := bstep (se 2 (by rfl) ⟨3397920, by rfl⟩ : syracuseStep 9061121 = 6795841) B6795841
theorem B2442131 : Blo 1084620 2442131 := bstep (se 1 (by rfl) ⟨1831598, by rfl⟩ : syracuseStep 2442131 = 3663197) B3663197
theorem B8242073 : Blo 1084620 8242073 := bstep (se 2 (by rfl) ⟨3090777, by rfl⟩ : syracuseStep 8242073 = 6181555) B6181555
theorem B2442185 : Blo 1084620 2442185 := bstep (se 2 (by rfl) ⟨915819, by rfl⟩ : syracuseStep 2442185 = 1831639) B1831639
theorem B95438197 : Blo 1084620 95438197 := bstep (se 5 (by rfl) ⟨4473665, by rfl⟩ : syracuseStep 95438197 = 8947331) B8947331
theorem B2606537 : Blo 1084620 2606537 := bstep (se 2 (by rfl) ⟨977451, by rfl⟩ : syracuseStep 2606537 = 1954903) B1954903
theorem B2934301 : Blo 1084620 2934301 := bstep (se 3 (by rfl) ⟨550181, by rfl⟩ : syracuseStep 2934301 = 1100363) B1100363
theorem B25445987 : Blo 1084620 25445987 := bstep (se 1 (by rfl) ⟨19084490, by rfl⟩ : syracuseStep 25445987 = 38168981) B38168981
theorem B2442887 : Blo 1084620 2442887 := bstep (se 1 (by rfl) ⟨1832165, by rfl⟩ : syracuseStep 2442887 = 3664331) B3664331
theorem B10438415 : Blo 1084620 10438415 := bstep (se 1 (by rfl) ⟨7828811, by rfl⟩ : syracuseStep 10438415 = 15657623) B15657623
theorem B2443067 : Blo 1084620 2443067 := bstep (se 1 (by rfl) ⟨1832300, by rfl⟩ : syracuseStep 2443067 = 3664601) B3664601
theorem B2934647 : Blo 1084620 2934647 := bstep (se 1 (by rfl) ⟨2200985, by rfl⟩ : syracuseStep 2934647 = 4401971) B4401971
theorem B2443193 : Blo 1084620 2443193 := bstep (se 2 (by rfl) ⟨916197, by rfl⟩ : syracuseStep 2443193 = 1832395) B1832395
theorem B1984441 : Blo 1084620 1984441 := bstep (se 2 (by rfl) ⟨744165, by rfl⟩ : syracuseStep 1984441 = 1488331) B1488331
theorem B3098569 : Blo 1084620 3098569 := bstep (se 2 (by rfl) ⟨1161963, by rfl⟩ : syracuseStep 3098569 = 2323927) B2323927
theorem B2443535 : Blo 1084620 2443535 := bstep (se 1 (by rfl) ⟨1832651, by rfl⟩ : syracuseStep 2443535 = 3665303) B3665303
theorem B2443553 : Blo 1084620 2443553 := bstep (se 2 (by rfl) ⟨916332, by rfl⟩ : syracuseStep 2443553 = 1832665) B1832665
theorem B2509115 : Blo 1084620 2509115 := bstep (se 1 (by rfl) ⟨1881836, by rfl⟩ : syracuseStep 2509115 = 3763673) B3763673
theorem B2443895 : Blo 1084620 2443895 := bstep (se 1 (by rfl) ⟨1832921, by rfl⟩ : syracuseStep 2443895 = 3665843) B3665843
theorem B2444075 : Blo 1084620 2444075 := bstep (se 1 (by rfl) ⟨1833056, by rfl⟩ : syracuseStep 2444075 = 3666113) B3666113
theorem B8244017 : Blo 1084620 8244017 := bstep (se 2 (by rfl) ⟨3091506, by rfl⟩ : syracuseStep 8244017 = 6183013) B6183013
theorem B5491799 : Blo 1084620 5491799 := bstep (se 1 (by rfl) ⟨4118849, by rfl⟩ : syracuseStep 5491799 = 8237699) B8237699
theorem B2444435 : Blo 1084620 2444435 := bstep (se 1 (by rfl) ⟨1833326, by rfl⟩ : syracuseStep 2444435 = 3666653) B3666653
theorem B2444489 : Blo 1084620 2444489 := bstep (se 2 (by rfl) ⟨916683, by rfl⟩ : syracuseStep 2444489 = 1833367) B1833367
theorem B6180097 : Blo 1084620 6180097 := bstep (se 2 (by rfl) ⟨2317536, by rfl⟩ : syracuseStep 6180097 = 4635073) B4635073
theorem B2608499 : Blo 1084620 2608499 := bstep (se 1 (by rfl) ⟨1956374, by rfl⟩ : syracuseStep 2608499 = 3912749) B3912749
theorem B2608537 : Blo 1084620 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B4640267 : Blo 1084620 4640267 := bstep (se 1 (by rfl) ⟨3480200, by rfl⟩ : syracuseStep 4640267 = 6960401) B6960401
theorem B5492285 : Blo 1084620 5492285 := bstep (se 3 (by rfl) ⟨1029803, by rfl⟩ : syracuseStep 5492285 = 2059607) B2059607
theorem B2608787 : Blo 1084620 2608787 := bstep (se 1 (by rfl) ⟨1956590, by rfl⟩ : syracuseStep 2608787 = 3913181) B3913181
theorem B6180623 : Blo 1084620 6180623 := bstep (se 1 (by rfl) ⟨4635467, by rfl⟩ : syracuseStep 6180623 = 9270935) B9270935
theorem B2445191 : Blo 1084620 2445191 := bstep (se 1 (by rfl) ⟨1833893, by rfl⟩ : syracuseStep 2445191 = 3667787) B3667787
theorem B8376331 : Blo 1084620 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B2445371 : Blo 1084620 2445371 := bstep (se 1 (by rfl) ⟨1834028, by rfl⟩ : syracuseStep 2445371 = 3668057) B3668057
theorem B2445497 : Blo 1084620 2445497 := bstep (se 2 (by rfl) ⟨917061, by rfl⟩ : syracuseStep 2445497 = 1834123) B1834123
theorem B2478281 : Blo 1084620 2478281 := bstep (se 2 (by rfl) ⟨929355, by rfl⟩ : syracuseStep 2478281 = 1858711) B1858711
theorem B3920243 : Blo 1084620 3920243 := bstep (se 1 (by rfl) ⟨2940182, by rfl⟩ : syracuseStep 3920243 = 5880365) B5880365
theorem B4641209 : Blo 1084620 4641209 := bstep (se 2 (by rfl) ⟨1740453, by rfl⟩ : syracuseStep 4641209 = 3480907) B3480907
theorem B2445839 : Blo 1084620 2445839 := bstep (se 1 (by rfl) ⟨1834379, by rfl⟩ : syracuseStep 2445839 = 3668759) B3668759
theorem B2445857 : Blo 1084620 2445857 := bstep (se 2 (by rfl) ⟨917196, by rfl⟩ : syracuseStep 2445857 = 1834393) B1834393
theorem B2609921 : Blo 1084620 2609921 := bstep (se 2 (by rfl) ⟨978720, by rfl⟩ : syracuseStep 2609921 = 1957441) B1957441
theorem B1626953 : Blo 1084620 1626953 := bstep (se 2 (by rfl) ⟨610107, by rfl⟩ : syracuseStep 1626953 = 1220215) B1220215
theorem B2446199 : Blo 1084620 2446199 := bstep (se 1 (by rfl) ⟨1834649, by rfl⟩ : syracuseStep 2446199 = 3669299) B3669299
theorem B1627067 : Blo 1084620 1627067 := bstep (se 1 (by rfl) ⟨1220300, by rfl⟩ : syracuseStep 1627067 = 2440601) B2440601
theorem B1627127 : Blo 1084620 1627127 := bstep (se 1 (by rfl) ⟨1220345, by rfl⟩ : syracuseStep 1627127 = 2440691) B2440691
theorem B1627151 : Blo 1084620 1627151 := bstep (se 1 (by rfl) ⟨1220363, by rfl⟩ : syracuseStep 1627151 = 2440727) B2440727
theorem B2642959 : Blo 1084620 2642959 := bstep (se 1 (by rfl) ⟨1982219, by rfl⟩ : syracuseStep 2642959 = 3964439) B3964439
theorem B2446379 : Blo 1084620 2446379 := bstep (se 1 (by rfl) ⟨1834784, by rfl⟩ : syracuseStep 2446379 = 3669569) B3669569
theorem B1627193 : Blo 1084620 1627193 := bstep (se 2 (by rfl) ⟨610197, by rfl⟩ : syracuseStep 1627193 = 1220395) B1220395
theorem B25416791 : Blo 1084620 25416791 := bstep (se 1 (by rfl) ⟨19062593, by rfl⟩ : syracuseStep 25416791 = 38125187) B38125187
theorem B1627271 : Blo 1084620 1627271 := bstep (se 1 (by rfl) ⟨1220453, by rfl⟩ : syracuseStep 1627271 = 2440907) B2440907
theorem B1627307 : Blo 1084620 1627307 := bstep (se 1 (by rfl) ⟨1220480, by rfl⟩ : syracuseStep 1627307 = 2440961) B2440961
theorem B6182081 : Blo 1084620 6182081 := bstep (se 2 (by rfl) ⟨2318280, by rfl⟩ : syracuseStep 6182081 = 4636561) B4636561
theorem B1627337 : Blo 1084620 1627337 := bstep (se 2 (by rfl) ⟨610251, by rfl⟩ : syracuseStep 1627337 = 1220503) B1220503
theorem B5494067 : Blo 1084620 5494067 := bstep (se 1 (by rfl) ⟨4120550, by rfl⟩ : syracuseStep 5494067 = 8241101) B8241101
theorem B1627451 : Blo 1084620 1627451 := bstep (se 1 (by rfl) ⟨1220588, by rfl⟩ : syracuseStep 1627451 = 2441177) B2441177
theorem B1627511 : Blo 1084620 1627511 := bstep (se 1 (by rfl) ⟨1220633, by rfl⟩ : syracuseStep 1627511 = 2441267) B2441267
theorem B1627535 : Blo 1084620 1627535 := bstep (se 1 (by rfl) ⟨1220651, by rfl⟩ : syracuseStep 1627535 = 2441303) B2441303
theorem B2446739 : Blo 1084620 2446739 := bstep (se 1 (by rfl) ⟨1835054, by rfl⟩ : syracuseStep 2446739 = 3670109) B3670109
theorem B1627577 : Blo 1084620 1627577 := bstep (se 2 (by rfl) ⟨610341, by rfl⟩ : syracuseStep 1627577 = 1220683) B1220683
theorem B2446793 : Blo 1084620 2446793 := bstep (se 2 (by rfl) ⟨917547, by rfl⟩ : syracuseStep 2446793 = 1835095) B1835095
theorem B1627655 : Blo 1084620 1627655 := bstep (se 1 (by rfl) ⟨1220741, by rfl⟩ : syracuseStep 1627655 = 2441483) B2441483
theorem B6968861 : Blo 1084620 6968861 := bstep (se 3 (by rfl) ⟨1306661, by rfl⟩ : syracuseStep 6968861 = 2613323) B2613323
theorem B1627691 : Blo 1084620 1627691 := bstep (se 1 (by rfl) ⟨1220768, by rfl⟩ : syracuseStep 1627691 = 2441537) B2441537
theorem B1627721 : Blo 1084620 1627721 := bstep (se 2 (by rfl) ⟨610395, by rfl⟩ : syracuseStep 1627721 = 1220791) B1220791
theorem B5494391 : Blo 1084620 5494391 := bstep (se 1 (by rfl) ⟨4120793, by rfl⟩ : syracuseStep 5494391 = 8241587) B8241587
theorem B1627835 : Blo 1084620 1627835 := bstep (se 1 (by rfl) ⟨1220876, by rfl⟩ : syracuseStep 1627835 = 2441753) B2441753
theorem B1627895 : Blo 1084620 1627895 := bstep (se 1 (by rfl) ⟨1220921, by rfl⟩ : syracuseStep 1627895 = 2441843) B2441843
theorem B4118273 : Blo 1084620 4118273 := bstep (se 2 (by rfl) ⟨1544352, by rfl⟩ : syracuseStep 4118273 = 3088705) B3088705
theorem B1627919 : Blo 1084620 1627919 := bstep (se 1 (by rfl) ⟨1220939, by rfl⟩ : syracuseStep 1627919 = 2441879) B2441879
theorem B12736291 : Blo 1084620 12736291 := bstep (se 1 (by rfl) ⟨9552218, by rfl⟩ : syracuseStep 12736291 = 19104437) B19104437
theorem B1627961 : Blo 1084620 1627961 := bstep (se 2 (by rfl) ⟨610485, by rfl⟩ : syracuseStep 1627961 = 1220971) B1220971
theorem B27121483 : Blo 1084620 27121483 := bstep (se 1 (by rfl) ⟨20341112, by rfl⟩ : syracuseStep 27121483 = 40682225) B40682225
theorem B1628039 : Blo 1084620 1628039 := bstep (se 1 (by rfl) ⟨1221029, by rfl⟩ : syracuseStep 1628039 = 2442059) B2442059
theorem B1628075 : Blo 1084620 1628075 := bstep (se 1 (by rfl) ⟨1221056, by rfl⟩ : syracuseStep 1628075 = 2442113) B2442113
theorem B1628105 : Blo 1084620 1628105 := bstep (se 2 (by rfl) ⟨610539, by rfl⟩ : syracuseStep 1628105 = 1221079) B1221079
theorem B2480161 : Blo 1084620 2480161 := bstep (se 2 (by rfl) ⟨930060, by rfl⟩ : syracuseStep 2480161 = 1860121) B1860121
theorem B1628219 : Blo 1084620 1628219 := bstep (se 1 (by rfl) ⟨1221164, by rfl⟩ : syracuseStep 1628219 = 2442329) B2442329
theorem B1628279 : Blo 1084620 1628279 := bstep (se 1 (by rfl) ⟨1221209, by rfl⟩ : syracuseStep 1628279 = 2442419) B2442419
theorem B2447495 : Blo 1084620 2447495 := bstep (se 1 (by rfl) ⟨1835621, by rfl⟩ : syracuseStep 2447495 = 3671243) B3671243
theorem B1628303 : Blo 1084620 1628303 := bstep (se 1 (by rfl) ⟨1221227, by rfl⟩ : syracuseStep 1628303 = 2442455) B2442455
theorem B27121837 : Blo 1084620 27121837 := bstep (se 3 (by rfl) ⟨5085344, by rfl⟩ : syracuseStep 27121837 = 10170689) B10170689
theorem B1628345 : Blo 1084620 1628345 := bstep (se 2 (by rfl) ⟨610629, by rfl⟩ : syracuseStep 1628345 = 1221259) B1221259
theorem B1628423 : Blo 1084620 1628423 := bstep (se 1 (by rfl) ⟨1221317, by rfl⟩ : syracuseStep 1628423 = 2442635) B2442635
theorem B1628459 : Blo 1084620 1628459 := bstep (se 1 (by rfl) ⟨1221344, by rfl⟩ : syracuseStep 1628459 = 2442689) B2442689
theorem B2447675 : Blo 1084620 2447675 := bstep (se 1 (by rfl) ⟨1835756, by rfl⟩ : syracuseStep 2447675 = 3671513) B3671513
theorem B1628489 : Blo 1084620 1628489 := bstep (se 2 (by rfl) ⟨610683, by rfl⟩ : syracuseStep 1628489 = 1221367) B1221367
theorem B4643207 : Blo 1084620 4643207 := bstep (se 1 (by rfl) ⟨3482405, by rfl⟩ : syracuseStep 4643207 = 6964811) B6964811
theorem B2447801 : Blo 1084620 2447801 := bstep (se 2 (by rfl) ⟨917925, by rfl⟩ : syracuseStep 2447801 = 1835851) B1835851
theorem B1628603 : Blo 1084620 1628603 := bstep (se 1 (by rfl) ⟨1221452, by rfl⟩ : syracuseStep 1628603 = 2442905) B2442905
theorem B1628663 : Blo 1084620 1628663 := bstep (se 1 (by rfl) ⟨1221497, by rfl⟩ : syracuseStep 1628663 = 2442995) B2442995
theorem B1628687 : Blo 1084620 1628687 := bstep (se 1 (by rfl) ⟨1221515, by rfl⟩ : syracuseStep 1628687 = 2443031) B2443031
theorem B1628729 : Blo 1084620 1628729 := bstep (se 2 (by rfl) ⟨610773, by rfl⟩ : syracuseStep 1628729 = 1221547) B1221547
theorem B3299899 : Blo 1084620 3299899 := bstep (se 1 (by rfl) ⟨2474924, by rfl⟩ : syracuseStep 3299899 = 4949849) B4949849
theorem B5495363 : Blo 1084620 5495363 := bstep (se 1 (by rfl) ⟨4121522, by rfl⟩ : syracuseStep 5495363 = 8243045) B8243045
theorem B1628807 : Blo 1084620 1628807 := bstep (se 1 (by rfl) ⟨1221605, by rfl⟩ : syracuseStep 1628807 = 2443211) B2443211
theorem B1628843 : Blo 1084620 1628843 := bstep (se 1 (by rfl) ⟨1221632, by rfl⟩ : syracuseStep 1628843 = 2443265) B2443265
theorem B1628873 : Blo 1084620 1628873 := bstep (se 2 (by rfl) ⟨610827, by rfl⟩ : syracuseStep 1628873 = 1221655) B1221655
theorem B2448143 : Blo 1084620 2448143 := bstep (se 1 (by rfl) ⟨1836107, by rfl⟩ : syracuseStep 2448143 = 3672215) B3672215
theorem B2448161 : Blo 1084620 2448161 := bstep (se 2 (by rfl) ⟨918060, by rfl⟩ : syracuseStep 2448161 = 1836121) B1836121
theorem B1628987 : Blo 1084620 1628987 := bstep (se 1 (by rfl) ⟨1221740, by rfl⟩ : syracuseStep 1628987 = 2443481) B2443481
theorem B3660659 : Blo 1084620 3660659 := bstep (se 1 (by rfl) ⟨2745494, by rfl⟩ : syracuseStep 3660659 = 5490989) B5490989
theorem B1629047 : Blo 1084620 1629047 := bstep (se 1 (by rfl) ⟨1221785, by rfl⟩ : syracuseStep 1629047 = 2443571) B2443571
theorem B5495687 : Blo 1084620 5495687 := bstep (se 1 (by rfl) ⟨4121765, by rfl⟩ : syracuseStep 5495687 = 8243531) B8243531
theorem B1629071 : Blo 1084620 1629071 := bstep (se 1 (by rfl) ⟨1221803, by rfl⟩ : syracuseStep 1629071 = 2443607) B2443607
theorem B4119443 : Blo 1084620 4119443 := bstep (se 1 (by rfl) ⟨3089582, by rfl⟩ : syracuseStep 4119443 = 6179165) B6179165
theorem B1629113 : Blo 1084620 1629113 := bstep (se 2 (by rfl) ⟨610917, by rfl⟩ : syracuseStep 1629113 = 1221835) B1221835
theorem B1629191 : Blo 1084620 1629191 := bstep (se 1 (by rfl) ⟨1221893, by rfl⟩ : syracuseStep 1629191 = 2443787) B2443787
theorem B3922955 : Blo 1084620 3922955 := bstep (se 1 (by rfl) ⟨2942216, by rfl⟩ : syracuseStep 3922955 = 5884433) B5884433
theorem B1629227 : Blo 1084620 1629227 := bstep (se 1 (by rfl) ⟨1221920, by rfl⟩ : syracuseStep 1629227 = 2443841) B2443841
theorem B1629257 : Blo 1084620 1629257 := bstep (se 2 (by rfl) ⟨610971, by rfl⟩ : syracuseStep 1629257 = 1221943) B1221943
theorem B2448503 : Blo 1084620 2448503 := bstep (se 1 (by rfl) ⟨1836377, by rfl⟩ : syracuseStep 2448503 = 3672755) B3672755
theorem B1629371 : Blo 1084620 1629371 := bstep (se 1 (by rfl) ⟨1222028, by rfl⟩ : syracuseStep 1629371 = 2444057) B2444057
theorem B1629431 : Blo 1084620 1629431 := bstep (se 1 (by rfl) ⟨1222073, by rfl⟩ : syracuseStep 1629431 = 2444147) B2444147
theorem B1629455 : Blo 1084620 1629455 := bstep (se 1 (by rfl) ⟨1222091, by rfl⟩ : syracuseStep 1629455 = 2444183) B2444183
theorem B2448683 : Blo 1084620 2448683 := bstep (se 1 (by rfl) ⟨1836512, by rfl⟩ : syracuseStep 2448683 = 3673025) B3673025
theorem B1629497 : Blo 1084620 1629497 := bstep (se 2 (by rfl) ⟨611061, by rfl⟩ : syracuseStep 1629497 = 1222123) B1222123
theorem B4119943 : Blo 1084620 4119943 := bstep (se 1 (by rfl) ⟨3089957, by rfl⟩ : syracuseStep 4119943 = 6179915) B6179915
theorem B1629575 : Blo 1084620 1629575 := bstep (se 1 (by rfl) ⟨1222181, by rfl⟩ : syracuseStep 1629575 = 2444363) B2444363
theorem B1957267 : Blo 1084620 1957267 := bstep (se 1 (by rfl) ⟨1467950, by rfl⟩ : syracuseStep 1957267 = 2935901) B2935901
theorem B1629611 : Blo 1084620 1629611 := bstep (se 1 (by rfl) ⟨1222208, by rfl⟩ : syracuseStep 1629611 = 2444417) B2444417
theorem B1629641 : Blo 1084620 1629641 := bstep (se 2 (by rfl) ⟨611115, by rfl⟩ : syracuseStep 1629641 = 1222231) B1222231
theorem B6184471 : Blo 1084620 6184471 := bstep (se 1 (by rfl) ⟨4638353, by rfl⟩ : syracuseStep 6184471 = 9276707) B9276707
theorem B1629755 : Blo 1084620 1629755 := bstep (se 1 (by rfl) ⟨1222316, by rfl⟩ : syracuseStep 1629755 = 2444633) B2444633
theorem B8805955 : Blo 1084620 8805955 := bstep (se 1 (by rfl) ⟨6604466, by rfl⟩ : syracuseStep 8805955 = 13208933) B13208933
theorem B1629815 : Blo 1084620 1629815 := bstep (se 1 (by rfl) ⟨1222361, by rfl⟩ : syracuseStep 1629815 = 2444723) B2444723
theorem B1629839 : Blo 1084620 1629839 := bstep (se 1 (by rfl) ⟨1222379, by rfl⟩ : syracuseStep 1629839 = 2444759) B2444759
theorem B2449043 : Blo 1084620 2449043 := bstep (se 1 (by rfl) ⟨1836782, by rfl⟩ : syracuseStep 2449043 = 3673565) B3673565
theorem B1629881 : Blo 1084620 1629881 := bstep (se 2 (by rfl) ⟨611205, by rfl⟩ : syracuseStep 1629881 = 1222411) B1222411
theorem B2449097 : Blo 1084620 2449097 := bstep (se 2 (by rfl) ⟨918411, by rfl⟩ : syracuseStep 2449097 = 1836823) B1836823
theorem B1629959 : Blo 1084620 1629959 := bstep (se 1 (by rfl) ⟨1222469, by rfl⟩ : syracuseStep 1629959 = 2444939) B2444939
theorem B4644641 : Blo 1084620 4644641 := bstep (se 2 (by rfl) ⟨1741740, by rfl⟩ : syracuseStep 4644641 = 3483481) B3483481
theorem B1629995 : Blo 1084620 1629995 := bstep (se 1 (by rfl) ⟨1222496, by rfl⟩ : syracuseStep 1629995 = 2444993) B2444993
theorem B2613035 : Blo 1084620 2613035 := bstep (se 1 (by rfl) ⟨1959776, by rfl⟩ : syracuseStep 2613035 = 3919553) B3919553
theorem B1630025 : Blo 1084620 1630025 := bstep (se 2 (by rfl) ⟨611259, by rfl⟩ : syracuseStep 1630025 = 1222519) B1222519
theorem B3301235 : Blo 1084620 3301235 := bstep (se 1 (by rfl) ⟨2475926, by rfl⟩ : syracuseStep 3301235 = 4951853) B4951853
theorem B9297827 : Blo 1084620 9297827 := bstep (se 1 (by rfl) ⟨6973370, by rfl⟩ : syracuseStep 9297827 = 13946741) B13946741
theorem B1630139 : Blo 1084620 1630139 := bstep (se 1 (by rfl) ⟨1222604, by rfl⟩ : syracuseStep 1630139 = 2445209) B2445209
theorem B1630199 : Blo 1084620 1630199 := bstep (se 1 (by rfl) ⟨1222649, by rfl⟩ : syracuseStep 1630199 = 2445299) B2445299
theorem B1630223 : Blo 1084620 1630223 := bstep (se 1 (by rfl) ⟨1222667, by rfl⟩ : syracuseStep 1630223 = 2445335) B2445335
theorem B1630265 : Blo 1084620 1630265 := bstep (se 2 (by rfl) ⟨611349, by rfl⟩ : syracuseStep 1630265 = 1222699) B1222699
theorem B2089079 : Blo 1084620 2089079 := bstep (se 1 (by rfl) ⟨1566809, by rfl⟩ : syracuseStep 2089079 = 3133619) B3133619
theorem B1630343 : Blo 1084620 1630343 := bstep (se 1 (by rfl) ⟨1222757, by rfl⟩ : syracuseStep 1630343 = 2445515) B2445515
theorem B1630379 : Blo 1084620 1630379 := bstep (se 1 (by rfl) ⟨1222784, by rfl⟩ : syracuseStep 1630379 = 2445569) B2445569
theorem B1630409 : Blo 1084620 1630409 := bstep (se 2 (by rfl) ⟨611403, by rfl⟩ : syracuseStep 1630409 = 1222807) B1222807
theorem B1630523 : Blo 1084620 1630523 := bstep (se 1 (by rfl) ⟨1222892, by rfl⟩ : syracuseStep 1630523 = 2445785) B2445785
theorem B1630583 : Blo 1084620 1630583 := bstep (se 1 (by rfl) ⟨1222937, by rfl⟩ : syracuseStep 1630583 = 2445875) B2445875
theorem B1630607 : Blo 1084620 1630607 := bstep (se 1 (by rfl) ⟨1222955, by rfl⟩ : syracuseStep 1630607 = 2445911) B2445911
theorem B1630649 : Blo 1084620 1630649 := bstep (se 2 (by rfl) ⟨611493, by rfl⟩ : syracuseStep 1630649 = 1222987) B1222987
theorem B1860025 : Blo 1084620 1860025 := bstep (se 2 (by rfl) ⟨697509, by rfl⟩ : syracuseStep 1860025 = 1395019) B1395019
theorem B1630727 : Blo 1084620 1630727 := bstep (se 1 (by rfl) ⟨1223045, by rfl⟩ : syracuseStep 1630727 = 2446091) B2446091
theorem B5300765 : Blo 1084620 5300765 := bstep (se 3 (by rfl) ⟨993893, by rfl⟩ : syracuseStep 5300765 = 1987787) B1987787
theorem B1630763 : Blo 1084620 1630763 := bstep (se 1 (by rfl) ⟨1223072, by rfl⟩ : syracuseStep 1630763 = 2446145) B2446145
theorem B1630793 : Blo 1084620 1630793 := bstep (se 2 (by rfl) ⟨611547, by rfl⟩ : syracuseStep 1630793 = 1223095) B1223095
theorem B1630907 : Blo 1084620 1630907 := bstep (se 1 (by rfl) ⟨1223180, by rfl⟩ : syracuseStep 1630907 = 2446361) B2446361
theorem B23847641 : Blo 1084620 23847641 := bstep (se 2 (by rfl) ⟨8942865, by rfl⟩ : syracuseStep 23847641 = 17885731) B17885731
theorem B1630967 : Blo 1084620 1630967 := bstep (se 1 (by rfl) ⟨1223225, by rfl⟩ : syracuseStep 1630967 = 2446451) B2446451
theorem B4645633 : Blo 1084620 4645633 := bstep (se 2 (by rfl) ⟨1742112, by rfl⟩ : syracuseStep 4645633 = 3484225) B3484225
theorem B2941697 : Blo 1084620 2941697 := bstep (se 2 (by rfl) ⟨1103136, by rfl⟩ : syracuseStep 2941697 = 2206273) B2206273
theorem B8807183 : Blo 1084620 8807183 := bstep (se 1 (by rfl) ⟨6605387, by rfl⟩ : syracuseStep 8807183 = 13210775) B13210775
theorem B1630991 : Blo 1084620 1630991 := bstep (se 1 (by rfl) ⟨1223243, by rfl⟩ : syracuseStep 1630991 = 2446487) B2446487
theorem B1631033 : Blo 1084620 1631033 := bstep (se 2 (by rfl) ⟨611637, by rfl⟩ : syracuseStep 1631033 = 1223275) B1223275
theorem B1631111 : Blo 1084620 1631111 := bstep (se 1 (by rfl) ⟨1223333, by rfl⟩ : syracuseStep 1631111 = 2446667) B2446667
theorem B1631147 : Blo 1084620 1631147 := bstep (se 1 (by rfl) ⟨1223360, by rfl⟩ : syracuseStep 1631147 = 2446721) B2446721
theorem B1631177 : Blo 1084620 1631177 := bstep (se 2 (by rfl) ⟨611691, by rfl⟩ : syracuseStep 1631177 = 1223383) B1223383
theorem B2515913 : Blo 1084620 2515913 := bstep (se 2 (by rfl) ⟨943467, by rfl⟩ : syracuseStep 2515913 = 1886935) B1886935
theorem B1631291 : Blo 1084620 1631291 := bstep (se 1 (by rfl) ⟨1223468, by rfl⟩ : syracuseStep 1631291 = 2446937) B2446937
theorem B1631351 : Blo 1084620 1631351 := bstep (se 1 (by rfl) ⟨1223513, by rfl⟩ : syracuseStep 1631351 = 2447027) B2447027
theorem B1631375 : Blo 1084620 1631375 := bstep (se 1 (by rfl) ⟨1223531, by rfl⟩ : syracuseStep 1631375 = 2447063) B2447063
theorem B1631417 : Blo 1084620 1631417 := bstep (se 2 (by rfl) ⟨611781, by rfl⟩ : syracuseStep 1631417 = 1223563) B1223563
theorem B1565897 : Blo 1084620 1565897 := bstep (se 2 (by rfl) ⟨587211, by rfl⟩ : syracuseStep 1565897 = 1174423) B1174423
theorem B1959113 : Blo 1084620 1959113 := bstep (se 2 (by rfl) ⟨734667, by rfl⟩ : syracuseStep 1959113 = 1469335) B1469335
theorem B1631495 : Blo 1084620 1631495 := bstep (se 1 (by rfl) ⟨1223621, by rfl⟩ : syracuseStep 1631495 = 2447243) B2447243
theorem B1631531 : Blo 1084620 1631531 := bstep (se 1 (by rfl) ⟨1223648, by rfl⟩ : syracuseStep 1631531 = 2447297) B2447297
theorem B1631561 : Blo 1084620 1631561 := bstep (se 2 (by rfl) ⟨611835, by rfl⟩ : syracuseStep 1631561 = 1223671) B1223671
theorem B3663251 : Blo 1084620 3663251 := bstep (se 1 (by rfl) ⟨2747438, by rfl⟩ : syracuseStep 3663251 = 5494877) B5494877
theorem B1631675 : Blo 1084620 1631675 := bstep (se 1 (by rfl) ⟨1223756, by rfl⟩ : syracuseStep 1631675 = 2447513) B2447513
theorem B2385353 : Blo 1084620 2385353 := bstep (se 2 (by rfl) ⟨894507, by rfl⟩ : syracuseStep 2385353 = 1789015) B1789015
theorem B1631735 : Blo 1084620 1631735 := bstep (se 1 (by rfl) ⟨1223801, by rfl⟩ : syracuseStep 1631735 = 2447603) B2447603
theorem B1467919 : Blo 1084620 1467919 := bstep (se 1 (by rfl) ⟨1100939, by rfl⟩ : syracuseStep 1467919 = 2201879) B2201879
theorem B1631759 : Blo 1084620 1631759 := bstep (se 1 (by rfl) ⟨1223819, by rfl⟩ : syracuseStep 1631759 = 2447639) B2447639
theorem B1631801 : Blo 1084620 1631801 := bstep (se 2 (by rfl) ⟨611925, by rfl⟩ : syracuseStep 1631801 = 1223851) B1223851
theorem B2745971 : Blo 1084620 2745971 := bstep (se 1 (by rfl) ⟨2059478, by rfl⟩ : syracuseStep 2745971 = 4118957) B4118957
theorem B1631879 : Blo 1084620 1631879 := bstep (se 1 (by rfl) ⟨1223909, by rfl⟩ : syracuseStep 1631879 = 2447819) B2447819
theorem B1631915 : Blo 1084620 1631915 := bstep (se 1 (by rfl) ⟨1223936, by rfl⟩ : syracuseStep 1631915 = 2447873) B2447873
theorem B13231795 : Blo 1084620 13231795 := bstep (se 1 (by rfl) ⟨9923846, by rfl⟩ : syracuseStep 13231795 = 19847693) B19847693
theorem B1631945 : Blo 1084620 1631945 := bstep (se 2 (by rfl) ⟨611979, by rfl⟩ : syracuseStep 1631945 = 1223959) B1223959
theorem B12379877 : Blo 1084620 12379877 := bstep (se 4 (by rfl) ⟨1160613, by rfl⟩ : syracuseStep 12379877 = 2321227) B2321227
theorem B1632059 : Blo 1084620 1632059 := bstep (se 1 (by rfl) ⟨1224044, by rfl⟩ : syracuseStep 1632059 = 2448089) B2448089
theorem B1632119 : Blo 1084620 1632119 := bstep (se 1 (by rfl) ⟨1224089, by rfl⟩ : syracuseStep 1632119 = 2448179) B2448179
theorem B6186887 : Blo 1084620 6186887 := bstep (se 1 (by rfl) ⟨4640165, by rfl⟩ : syracuseStep 6186887 = 9280331) B9280331
theorem B1632143 : Blo 1084620 1632143 := bstep (se 1 (by rfl) ⟨1224107, by rfl⟩ : syracuseStep 1632143 = 2448215) B2448215
theorem B1632185 : Blo 1084620 1632185 := bstep (se 2 (by rfl) ⟨612069, by rfl⟩ : syracuseStep 1632185 = 1224139) B1224139
theorem B2615225 : Blo 1084620 2615225 := bstep (se 2 (by rfl) ⟨980709, by rfl⟩ : syracuseStep 2615225 = 1961419) B1961419
theorem B1632263 : Blo 1084620 1632263 := bstep (se 1 (by rfl) ⟨1224197, by rfl⟩ : syracuseStep 1632263 = 2448395) B2448395
theorem B1632299 : Blo 1084620 1632299 := bstep (se 1 (by rfl) ⟨1224224, by rfl⟩ : syracuseStep 1632299 = 2448449) B2448449
theorem B1632329 : Blo 1084620 1632329 := bstep (se 2 (by rfl) ⟨612123, by rfl⟩ : syracuseStep 1632329 = 1224247) B1224247
theorem B2746487 : Blo 1084620 2746487 := bstep (se 1 (by rfl) ⟨2059865, by rfl⟩ : syracuseStep 2746487 = 4119731) B4119731
theorem B1632443 : Blo 1084620 1632443 := bstep (se 1 (by rfl) ⟨1224332, by rfl⟩ : syracuseStep 1632443 = 2448665) B2448665
theorem B1632503 : Blo 1084620 1632503 := bstep (se 1 (by rfl) ⟨1224377, by rfl⟩ : syracuseStep 1632503 = 2448755) B2448755
theorem B1468687 : Blo 1084620 1468687 := bstep (se 1 (by rfl) ⟨1101515, by rfl⟩ : syracuseStep 1468687 = 2203031) B2203031
theorem B1632527 : Blo 1084620 1632527 := bstep (se 1 (by rfl) ⟨1224395, by rfl⟩ : syracuseStep 1632527 = 2448791) B2448791
theorem B1468729 : Blo 1084620 1468729 := bstep (se 2 (by rfl) ⟨550773, by rfl⟩ : syracuseStep 1468729 = 1101547) B1101547
theorem B1632569 : Blo 1084620 1632569 := bstep (se 2 (by rfl) ⟨612213, by rfl⟩ : syracuseStep 1632569 = 1224427) B1224427
theorem B3303767 : Blo 1084620 3303767 := bstep (se 1 (by rfl) ⟨2477825, by rfl⟩ : syracuseStep 3303767 = 4955651) B4955651
theorem B5499251 : Blo 1084620 5499251 := bstep (se 1 (by rfl) ⟨4124438, by rfl⟩ : syracuseStep 5499251 = 8248877) B8248877
theorem B1632647 : Blo 1084620 1632647 := bstep (se 1 (by rfl) ⟨1224485, by rfl⟩ : syracuseStep 1632647 = 2448971) B2448971
theorem B8251793 : Blo 1084620 8251793 := bstep (se 2 (by rfl) ⟨3094422, by rfl⟩ : syracuseStep 8251793 = 6188845) B6188845
theorem B1632683 : Blo 1084620 1632683 := bstep (se 1 (by rfl) ⟨1224512, by rfl⟩ : syracuseStep 1632683 = 2449025) B2449025
theorem B1632713 : Blo 1084620 1632713 := bstep (se 2 (by rfl) ⟨612267, by rfl⟩ : syracuseStep 1632713 = 1224535) B1224535
theorem B1632827 : Blo 1084620 1632827 := bstep (se 1 (by rfl) ⟨1224620, by rfl⟩ : syracuseStep 1632827 = 2449241) B2449241
theorem B1632887 : Blo 1084620 1632887 := bstep (se 1 (by rfl) ⟨1224665, by rfl⟩ : syracuseStep 1632887 = 2449331) B2449331
theorem B1960583 : Blo 1084620 1960583 := bstep (se 1 (by rfl) ⟨1470437, by rfl⟩ : syracuseStep 1960583 = 2940875) B2940875
theorem B1632911 : Blo 1084620 1632911 := bstep (se 1 (by rfl) ⟨1224683, by rfl⟩ : syracuseStep 1632911 = 2449367) B2449367
theorem B3664655 : Blo 1084620 3664655 := bstep (se 1 (by rfl) ⟨2748491, by rfl⟩ : syracuseStep 3664655 = 5496983) B5496983
theorem B5499737 : Blo 1084620 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B41806691 : Blo 1084620 41806691 := bstep (se 1 (by rfl) ⟨31355018, by rfl⟩ : syracuseStep 41806691 = 62710037) B62710037
theorem B1239943 : Blo 1084620 1239943 := bstep (se 1 (by rfl) ⟨929957, by rfl⟩ : syracuseStep 1239943 = 1859915) B1859915
theorem B1567675 : Blo 1084620 1567675 := bstep (se 1 (by rfl) ⟨1175756, by rfl⟩ : syracuseStep 1567675 = 2351513) B2351513
theorem B3664925 : Blo 1084620 3664925 := bstep (se 3 (by rfl) ⟨687173, by rfl⟩ : syracuseStep 3664925 = 1374347) B1374347
theorem B6974525 : Blo 1084620 6974525 := bstep (se 3 (by rfl) ⟨1307723, by rfl⟩ : syracuseStep 6974525 = 2615447) B2615447
theorem B2747479 : Blo 1084620 2747479 := bstep (se 1 (by rfl) ⟨2060609, by rfl⟩ : syracuseStep 2747479 = 4121219) B4121219
theorem B26405975 : Blo 1084620 26405975 := bstep (se 1 (by rfl) ⟨19804481, by rfl⟩ : syracuseStep 26405975 = 39608963) B39608963
theorem B2321723 : Blo 1084620 2321723 := bstep (se 1 (by rfl) ⟨1741292, by rfl⟩ : syracuseStep 2321723 = 3482585) B3482585
theorem B2747783 : Blo 1084620 2747783 := bstep (se 1 (by rfl) ⟨2060837, by rfl⟩ : syracuseStep 2747783 = 4121675) B4121675
theorem B2682247 : Blo 1084620 2682247 := bstep (se 1 (by rfl) ⟨2011685, by rfl⟩ : syracuseStep 2682247 = 4023371) B4023371
theorem B3141011 : Blo 1084620 3141011 := bstep (se 1 (by rfl) ⟨2355758, by rfl⟩ : syracuseStep 3141011 = 4711517) B4711517
theorem B2747915 : Blo 1084620 2747915 := bstep (se 1 (by rfl) ⟨2060936, by rfl⟩ : syracuseStep 2747915 = 4121873) B4121873
theorem B6188663 : Blo 1084620 6188663 := bstep (se 1 (by rfl) ⟨4641497, by rfl⟩ : syracuseStep 6188663 = 9282995) B9282995
theorem B2092691 : Blo 1084620 2092691 := bstep (se 1 (by rfl) ⟨1569518, by rfl⟩ : syracuseStep 2092691 = 3139037) B3139037
theorem B1830775 : Blo 1084620 1830775 := bstep (se 1 (by rfl) ⟨1373081, by rfl⟩ : syracuseStep 1830775 = 2746163) B2746163
theorem B2748431 : Blo 1084620 2748431 := bstep (se 1 (by rfl) ⟨2061323, by rfl⟩ : syracuseStep 2748431 = 4122647) B4122647
theorem B1830971 : Blo 1084620 1830971 := bstep (se 1 (by rfl) ⟨1373228, by rfl⟩ : syracuseStep 1830971 = 2746457) B2746457
theorem B2748563 : Blo 1084620 2748563 := bstep (se 1 (by rfl) ⟨2061422, by rfl⟩ : syracuseStep 2748563 = 4122845) B4122845
theorem B2060473 : Blo 1084620 2060473 := bstep (se 2 (by rfl) ⟨772677, by rfl⟩ : syracuseStep 2060473 = 1545355) B1545355
theorem B2322731 : Blo 1084620 2322731 := bstep (se 1 (by rfl) ⟨1742048, by rfl⟩ : syracuseStep 2322731 = 3484097) B3484097
theorem B6189371 : Blo 1084620 6189371 := bstep (se 1 (by rfl) ⟨4642028, by rfl⟩ : syracuseStep 6189371 = 9284057) B9284057
theorem B3666329 : Blo 1084620 3666329 := bstep (se 2 (by rfl) ⟨1374873, by rfl⟩ : syracuseStep 3666329 = 2749747) B2749747
theorem B1831369 : Blo 1084620 1831369 := bstep (se 2 (by rfl) ⟨686763, by rfl⟩ : syracuseStep 1831369 = 1373527) B1373527
theorem B2060815 : Blo 1084620 2060815 := bstep (se 1 (by rfl) ⟨1545611, by rfl⟩ : syracuseStep 2060815 = 3091223) B3091223
theorem B8254223 : Blo 1084620 8254223 := bstep (se 1 (by rfl) ⟨6190667, by rfl⟩ : syracuseStep 8254223 = 12381335) B12381335
theorem B5501843 : Blo 1084620 5501843 := bstep (se 1 (by rfl) ⟨4126382, by rfl⟩ : syracuseStep 5501843 = 8252765) B8252765
theorem B4125593 : Blo 1084620 4125593 := bstep (se 2 (by rfl) ⟨1547097, by rfl⟩ : syracuseStep 4125593 = 3094195) B3094195
theorem B14873507 : Blo 1084620 14873507 := bstep (se 1 (by rfl) ⟨11155130, by rfl⟩ : syracuseStep 14873507 = 22310261) B22310261
theorem B3306539 : Blo 1084620 3306539 := bstep (se 1 (by rfl) ⟨2479904, by rfl⟩ : syracuseStep 3306539 = 4959809) B4959809
theorem B3667031 : Blo 1084620 3667031 := bstep (se 1 (by rfl) ⟨2750273, by rfl⟩ : syracuseStep 3667031 = 5500547) B5500547
theorem B1307767 : Blo 1084620 1307767 := bstep (se 1 (by rfl) ⟨980825, by rfl⟩ : syracuseStep 1307767 = 1961651) B1961651
theorem B1832071 : Blo 1084620 1832071 := bstep (se 1 (by rfl) ⟨1374053, by rfl⟩ : syracuseStep 1832071 = 2748107) B2748107
theorem B1373431 : Blo 1084620 1373431 := bstep (se 1 (by rfl) ⟨1030073, by rfl⟩ : syracuseStep 1373431 = 2060147) B2060147
theorem B2749697 : Blo 1084620 2749697 := bstep (se 2 (by rfl) ⟨1031136, by rfl⟩ : syracuseStep 2749697 = 2062273) B2062273
theorem B2061703 : Blo 1084620 2061703 := bstep (se 1 (by rfl) ⟨1546277, by rfl⟩ : syracuseStep 2061703 = 3092555) B3092555
theorem B1373755 : Blo 1084620 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B3667517 : Blo 1084620 3667517 := bstep (se 3 (by rfl) ⟨687659, by rfl⟩ : syracuseStep 3667517 = 1375319) B1375319
theorem B2750071 : Blo 1084620 2750071 := bstep (se 1 (by rfl) ⟨2062553, by rfl⟩ : syracuseStep 2750071 = 4125107) B4125107
theorem B6190829 : Blo 1084620 6190829 := bstep (se 3 (by rfl) ⟨1160780, by rfl⟩ : syracuseStep 6190829 = 2321561) B2321561
theorem B1832719 : Blo 1084620 1832719 := bstep (se 1 (by rfl) ⟨1374539, by rfl⟩ : syracuseStep 1832719 = 2749079) B2749079
theorem B2324371 : Blo 1084620 2324371 := bstep (se 1 (by rfl) ⟨1743278, by rfl⟩ : syracuseStep 2324371 = 3486557) B3486557
theorem B2750507 : Blo 1084620 2750507 := bstep (se 1 (by rfl) ⟨2062880, by rfl⟩ : syracuseStep 2750507 = 4125761) B4125761
theorem B3962947 : Blo 1084620 3962947 := bstep (se 1 (by rfl) ⟨2972210, by rfl⟩ : syracuseStep 3962947 = 5944421) B5944421
theorem B1833259 : Blo 1084620 1833259 := bstep (se 1 (by rfl) ⟨1374944, by rfl⟩ : syracuseStep 1833259 = 2749889) B2749889
theorem B1833401 : Blo 1084620 1833401 := bstep (se 2 (by rfl) ⟨687525, by rfl⟩ : syracuseStep 1833401 = 1375051) B1375051
theorem B1374727 : Blo 1084620 1374727 := bstep (se 1 (by rfl) ⟨1031045, by rfl⟩ : syracuseStep 1374727 = 2062091) B2062091
theorem B5863997 : Blo 1084620 5863997 := bstep (se 3 (by rfl) ⟨1099499, by rfl⟩ : syracuseStep 5863997 = 2198999) B2198999
theorem B27884249 : Blo 1084620 27884249 := bstep (se 2 (by rfl) ⟨10456593, by rfl⟩ : syracuseStep 27884249 = 20913187) B20913187
theorem B2751347 : Blo 1084620 2751347 := bstep (se 1 (by rfl) ⟨2063510, by rfl⟩ : syracuseStep 2751347 = 4127021) B4127021
theorem B2751367 : Blo 1084620 2751367 := bstep (se 1 (by rfl) ⟨2063525, by rfl⟩ : syracuseStep 2751367 = 4127051) B4127051
theorem B1375147 : Blo 1084620 1375147 := bstep (se 1 (by rfl) ⟨1031360, by rfl⟩ : syracuseStep 1375147 = 2062721) B2062721
theorem B3668921 : Blo 1084620 3668921 := bstep (se 2 (by rfl) ⟨1375845, by rfl⟩ : syracuseStep 3668921 = 2751691) B2751691
theorem B1834103 : Blo 1084620 1834103 := bstep (se 1 (by rfl) ⟨1375577, by rfl⟩ : syracuseStep 1834103 = 2751155) B2751155
theorem B2063495 : Blo 1084620 2063495 := bstep (se 1 (by rfl) ⟨1547621, by rfl⟩ : syracuseStep 2063495 = 3095243) B3095243
theorem B1375375 : Blo 1084620 1375375 := bstep (se 1 (by rfl) ⟨1031531, by rfl⟩ : syracuseStep 1375375 = 2063063) B2063063
theorem B2751641 : Blo 1084620 2751641 := bstep (se 2 (by rfl) ⟨1031865, by rfl⟩ : syracuseStep 2751641 = 2063731) B2063731
theorem B11762977 : Blo 1084620 11762977 := bstep (se 2 (by rfl) ⟨4411116, by rfl⟩ : syracuseStep 11762977 = 8822233) B8822233
theorem B2751803 : Blo 1084620 2751803 := bstep (se 1 (by rfl) ⟨2063852, by rfl⟩ : syracuseStep 2751803 = 4127705) B4127705
theorem B3669515 : Blo 1084620 3669515 := bstep (se 1 (by rfl) ⟨2752136, by rfl⟩ : syracuseStep 3669515 = 5504273) B5504273
theorem B2752015 : Blo 1084620 2752015 := bstep (se 1 (by rfl) ⟨2064011, by rfl⟩ : syracuseStep 2752015 = 4128023) B4128023
theorem B1834555 : Blo 1084620 1834555 := bstep (se 1 (by rfl) ⟨1375916, by rfl⟩ : syracuseStep 1834555 = 2751833) B2751833
theorem B3669623 : Blo 1084620 3669623 := bstep (se 1 (by rfl) ⟨2752217, by rfl⟩ : syracuseStep 3669623 = 5504435) B5504435
theorem B1834697 : Blo 1084620 1834697 := bstep (se 2 (by rfl) ⟨688011, by rfl⟩ : syracuseStep 1834697 = 1376023) B1376023
theorem B2752289 : Blo 1084620 2752289 := bstep (se 2 (by rfl) ⟨1032108, by rfl⟩ : syracuseStep 2752289 = 2064217) B2064217
theorem B67927853 : Blo 1084620 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B1376119 : Blo 1084620 1376119 := bstep (se 1 (by rfl) ⟨1032089, by rfl⟩ : syracuseStep 1376119 = 2064179) B2064179
theorem B5504921 : Blo 1084620 5504921 := bstep (se 2 (by rfl) ⟨2064345, by rfl⟩ : syracuseStep 5504921 = 4128691) B4128691
theorem B8257625 : Blo 1084620 8257625 := bstep (se 2 (by rfl) ⟨3096609, by rfl⟩ : syracuseStep 8257625 = 6193219) B6193219
theorem B1835257 : Blo 1084620 1835257 := bstep (se 2 (by rfl) ⟨688221, by rfl⟩ : syracuseStep 1835257 = 1376443) B1376443
theorem B2752987 : Blo 1084620 2752987 := bstep (se 1 (by rfl) ⟨2064740, by rfl⟩ : syracuseStep 2752987 = 4129481) B4129481
theorem B1835527 : Blo 1084620 1835527 := bstep (se 1 (by rfl) ⟨1376645, by rfl⟩ : syracuseStep 1835527 = 2753291) B2753291
theorem B5505569 : Blo 1084620 5505569 := bstep (se 2 (by rfl) ⟨2064588, by rfl⟩ : syracuseStep 5505569 = 4129177) B4129177
theorem B2064953 : Blo 1084620 2064953 := bstep (se 2 (by rfl) ⟨774357, by rfl⟩ : syracuseStep 2064953 = 1548715) B1548715
theorem B1835959 : Blo 1084620 1835959 := bstep (se 1 (by rfl) ⟨1376969, by rfl⟩ : syracuseStep 1835959 = 2753939) B2753939
theorem B10453981 : Blo 1084620 10453981 := bstep (se 3 (by rfl) ⟨1960121, by rfl⟩ : syracuseStep 10453981 = 3920243) B3920243
theorem B6194177 : Blo 1084620 6194177 := bstep (se 2 (by rfl) ⟨2322816, by rfl⟩ : syracuseStep 6194177 = 4645633) B4645633
theorem B1377319 : Blo 1084620 1377319 := bstep (se 1 (by rfl) ⟨1032989, by rfl⟩ : syracuseStep 1377319 = 2065979) B2065979
theorem B2753615 : Blo 1084620 2753615 := bstep (se 1 (by rfl) ⟨2065211, by rfl⟩ : syracuseStep 2753615 = 4130423) B4130423
theorem B1836155 : Blo 1084620 1836155 := bstep (se 1 (by rfl) ⟨1377116, by rfl⟩ : syracuseStep 1836155 = 2754233) B2754233
theorem B4130135 : Blo 1084620 4130135 := bstep (se 1 (by rfl) ⟨3097601, by rfl⟩ : syracuseStep 4130135 = 6195203) B6195203
theorem B1377643 : Blo 1084620 1377643 := bstep (se 1 (by rfl) ⟨1033232, by rfl⟩ : syracuseStep 1377643 = 2066465) B2066465
theorem B1836553 : Blo 1084620 1836553 := bstep (se 2 (by rfl) ⟨688707, by rfl⟩ : syracuseStep 1836553 = 1377415) B1377415
theorem B8259083 : Blo 1084620 8259083 := bstep (se 1 (by rfl) ⟨6194312, by rfl⟩ : syracuseStep 8259083 = 12388625) B12388625
theorem B3671675 : Blo 1084620 3671675 := bstep (se 1 (by rfl) ⟨2753756, by rfl⟩ : syracuseStep 3671675 = 5507513) B5507513
theorem B1836715 : Blo 1084620 1836715 := bstep (se 1 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 1836715 = 2755073) B2755073
theorem B2754263 : Blo 1084620 2754263 := bstep (se 1 (by rfl) ⟨2065697, by rfl⟩ : syracuseStep 2754263 = 4131395) B4131395
theorem B3671837 : Blo 1084620 3671837 := bstep (se 3 (by rfl) ⟨688469, by rfl⟩ : syracuseStep 3671837 = 1376939) B1376939
theorem B15075233 : Blo 1084620 15075233 := bstep (se 2 (by rfl) ⟨5653212, by rfl⟩ : syracuseStep 15075233 = 11306425) B11306425
theorem B1837019 : Blo 1084620 1837019 := bstep (se 1 (by rfl) ⟨1377764, by rfl⟩ : syracuseStep 1837019 = 2755529) B2755529
theorem B1738999 : Blo 1084620 1738999 := bstep (se 1 (by rfl) ⟨1304249, by rfl⟩ : syracuseStep 1738999 = 2608499) B2608499
theorem B8489369 : Blo 1084620 8489369 := bstep (se 2 (by rfl) ⟨3183513, by rfl⟩ : syracuseStep 8489369 = 6367027) B6367027
theorem B3672539 : Blo 1084620 3672539 := bstep (se 1 (by rfl) ⟨2754404, by rfl⟩ : syracuseStep 3672539 = 5508809) B5508809
theorem B4131425 : Blo 1084620 4131425 := bstep (se 2 (by rfl) ⟨1549284, by rfl⟩ : syracuseStep 4131425 = 3098569) B3098569
theorem B8817437 : Blo 1084620 8817437 := bstep (se 3 (by rfl) ⟨1653269, by rfl⟩ : syracuseStep 8817437 = 3306539) B3306539
theorem B6949739 : Blo 1084620 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B3673241 : Blo 1084620 3673241 := bstep (se 2 (by rfl) ⟨1377465, by rfl⟩ : syracuseStep 3673241 = 2754931) B2754931
theorem B1739947 : Blo 1084620 1739947 := bstep (se 1 (by rfl) ⟨1304960, by rfl⟩ : syracuseStep 1739947 = 2609921) B2609921
theorem B1084635 : Blo 1084620 1084635 := bstep (se 1 (by rfl) ⟨813476, by rfl⟩ : syracuseStep 1084635 = 1626953) B1626953
theorem B1084711 : Blo 1084620 1084711 := bstep (se 1 (by rfl) ⟨813533, by rfl⟩ : syracuseStep 1084711 = 1627067) B1627067
theorem B1084751 : Blo 1084620 1084751 := bstep (se 1 (by rfl) ⟨813563, by rfl⟩ : syracuseStep 1084751 = 1627127) B1627127
theorem B1084767 : Blo 1084620 1084767 := bstep (se 1 (by rfl) ⟨813575, by rfl⟩ : syracuseStep 1084767 = 1627151) B1627151
theorem B1084795 : Blo 1084620 1084795 := bstep (se 1 (by rfl) ⟨813596, by rfl⟩ : syracuseStep 1084795 = 1627193) B1627193
theorem B7441789 : Blo 1084620 7441789 := bstep (se 3 (by rfl) ⟨1395335, by rfl⟩ : syracuseStep 7441789 = 2790671) B2790671
theorem B16944527 : Blo 1084620 16944527 := bstep (se 1 (by rfl) ⟨12708395, by rfl⟩ : syracuseStep 16944527 = 25416791) B25416791
theorem B8261027 : Blo 1084620 8261027 := bstep (se 1 (by rfl) ⟨6195770, by rfl⟩ : syracuseStep 8261027 = 12391541) B12391541
theorem B1084847 : Blo 1084620 1084847 := bstep (se 1 (by rfl) ⟨813635, by rfl⟩ : syracuseStep 1084847 = 1627271) B1627271
theorem B1084871 : Blo 1084620 1084871 := bstep (se 1 (by rfl) ⟨813653, by rfl⟩ : syracuseStep 1084871 = 1627307) B1627307
theorem B1084891 : Blo 1084620 1084891 := bstep (se 1 (by rfl) ⟨813668, by rfl⟩ : syracuseStep 1084891 = 1627337) B1627337
theorem B1084967 : Blo 1084620 1084967 := bstep (se 1 (by rfl) ⟨813725, by rfl⟩ : syracuseStep 1084967 = 1627451) B1627451
theorem B5508647 : Blo 1084620 5508647 := bstep (se 1 (by rfl) ⟨4131485, by rfl⟩ : syracuseStep 5508647 = 8262971) B8262971
theorem B1085007 : Blo 1084620 1085007 := bstep (se 1 (by rfl) ⟨813755, by rfl⟩ : syracuseStep 1085007 = 1627511) B1627511
theorem B1085023 : Blo 1084620 1085023 := bstep (se 1 (by rfl) ⟨813767, by rfl⟩ : syracuseStep 1085023 = 1627535) B1627535
theorem B1085051 : Blo 1084620 1085051 := bstep (se 1 (by rfl) ⟨813788, by rfl⟩ : syracuseStep 1085051 = 1627577) B1627577
theorem B1085103 : Blo 1084620 1085103 := bstep (se 1 (by rfl) ⟨813827, by rfl⟩ : syracuseStep 1085103 = 1627655) B1627655
theorem B1085127 : Blo 1084620 1085127 := bstep (se 1 (by rfl) ⟨813845, by rfl⟩ : syracuseStep 1085127 = 1627691) B1627691
theorem B1085147 : Blo 1084620 1085147 := bstep (se 1 (by rfl) ⟨813860, by rfl⟩ : syracuseStep 1085147 = 1627721) B1627721
theorem B1085223 : Blo 1084620 1085223 := bstep (se 1 (by rfl) ⟨813917, by rfl⟩ : syracuseStep 1085223 = 1627835) B1627835
theorem B1085263 : Blo 1084620 1085263 := bstep (se 1 (by rfl) ⟨813947, by rfl⟩ : syracuseStep 1085263 = 1627895) B1627895
theorem B1085279 : Blo 1084620 1085279 := bstep (se 1 (by rfl) ⟨813959, by rfl⟩ : syracuseStep 1085279 = 1627919) B1627919
theorem B6950765 : Blo 1084620 6950765 := bstep (se 3 (by rfl) ⟨1303268, by rfl⟩ : syracuseStep 6950765 = 2606537) B2606537
theorem B6360941 : Blo 1084620 6360941 := bstep (se 3 (by rfl) ⟨1192676, by rfl⟩ : syracuseStep 6360941 = 2385353) B2385353
theorem B1085307 : Blo 1084620 1085307 := bstep (se 1 (by rfl) ⟨813980, by rfl⟩ : syracuseStep 1085307 = 1627961) B1627961
theorem B1085359 : Blo 1084620 1085359 := bstep (se 1 (by rfl) ⟨814019, by rfl⟩ : syracuseStep 1085359 = 1628039) B1628039
theorem B1085383 : Blo 1084620 1085383 := bstep (se 1 (by rfl) ⟨814037, by rfl⟩ : syracuseStep 1085383 = 1628075) B1628075
theorem B1085403 : Blo 1084620 1085403 := bstep (se 1 (by rfl) ⟨814052, by rfl⟩ : syracuseStep 1085403 = 1628105) B1628105
theorem B4132883 : Blo 1084620 4132883 := bstep (se 1 (by rfl) ⟨3099662, by rfl⟩ : syracuseStep 4132883 = 6199325) B6199325
theorem B1085479 : Blo 1084620 1085479 := bstep (se 1 (by rfl) ⟨814109, by rfl⟩ : syracuseStep 1085479 = 1628219) B1628219
theorem B1085519 : Blo 1084620 1085519 := bstep (se 1 (by rfl) ⟨814139, by rfl⟩ : syracuseStep 1085519 = 1628279) B1628279
theorem B1085535 : Blo 1084620 1085535 := bstep (se 1 (by rfl) ⟨814151, by rfl⟩ : syracuseStep 1085535 = 1628303) B1628303
theorem B1085563 : Blo 1084620 1085563 := bstep (se 1 (by rfl) ⟨814172, by rfl⟩ : syracuseStep 1085563 = 1628345) B1628345
theorem B1085615 : Blo 1084620 1085615 := bstep (se 1 (by rfl) ⟨814211, by rfl⟩ : syracuseStep 1085615 = 1628423) B1628423
theorem B1085639 : Blo 1084620 1085639 := bstep (se 1 (by rfl) ⟨814229, by rfl⟩ : syracuseStep 1085639 = 1628459) B1628459
theorem B1085659 : Blo 1084620 1085659 := bstep (se 1 (by rfl) ⟨814244, by rfl⟩ : syracuseStep 1085659 = 1628489) B1628489
theorem B1085735 : Blo 1084620 1085735 := bstep (se 1 (by rfl) ⟨814301, by rfl⟩ : syracuseStep 1085735 = 1628603) B1628603
theorem B1085775 : Blo 1084620 1085775 := bstep (se 1 (by rfl) ⟨814331, by rfl⟩ : syracuseStep 1085775 = 1628663) B1628663
theorem B1085791 : Blo 1084620 1085791 := bstep (se 1 (by rfl) ⟨814343, by rfl⟩ : syracuseStep 1085791 = 1628687) B1628687
theorem B1085819 : Blo 1084620 1085819 := bstep (se 1 (by rfl) ⟨814364, by rfl⟩ : syracuseStep 1085819 = 1628729) B1628729
theorem B1085871 : Blo 1084620 1085871 := bstep (se 1 (by rfl) ⟨814403, by rfl⟩ : syracuseStep 1085871 = 1628807) B1628807
theorem B1085895 : Blo 1084620 1085895 := bstep (se 1 (by rfl) ⟨814421, by rfl⟩ : syracuseStep 1085895 = 1628843) B1628843
theorem B1085915 : Blo 1084620 1085915 := bstep (se 1 (by rfl) ⟨814436, by rfl⟩ : syracuseStep 1085915 = 1628873) B1628873
theorem B4133339 : Blo 1084620 4133339 := bstep (se 1 (by rfl) ⟨3100004, by rfl⟩ : syracuseStep 4133339 = 6200009) B6200009
theorem B3576329 : Blo 1084620 3576329 := bstep (se 2 (by rfl) ⟨1341123, by rfl⟩ : syracuseStep 3576329 = 2682247) B2682247
theorem B3478049 : Blo 1084620 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B1085991 : Blo 1084620 1085991 := bstep (se 1 (by rfl) ⟨814493, by rfl⟩ : syracuseStep 1085991 = 1628987) B1628987
theorem B1086031 : Blo 1084620 1086031 := bstep (se 1 (by rfl) ⟨814523, by rfl⟩ : syracuseStep 1086031 = 1629047) B1629047
theorem B1086047 : Blo 1084620 1086047 := bstep (se 1 (by rfl) ⟨814535, by rfl⟩ : syracuseStep 1086047 = 1629071) B1629071
theorem B1086075 : Blo 1084620 1086075 := bstep (se 1 (by rfl) ⟨814556, by rfl⟩ : syracuseStep 1086075 = 1629113) B1629113
theorem B1086127 : Blo 1084620 1086127 := bstep (se 1 (by rfl) ⟨814595, by rfl⟩ : syracuseStep 1086127 = 1629191) B1629191
theorem B1086151 : Blo 1084620 1086151 := bstep (se 1 (by rfl) ⟨814613, by rfl⟩ : syracuseStep 1086151 = 1629227) B1629227
theorem B9900755 : Blo 1084620 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B1086171 : Blo 1084620 1086171 := bstep (se 1 (by rfl) ⟨814628, by rfl⟩ : syracuseStep 1086171 = 1629257) B1629257
theorem B1086247 : Blo 1084620 1086247 := bstep (se 1 (by rfl) ⟨814685, by rfl⟩ : syracuseStep 1086247 = 1629371) B1629371
theorem B1086287 : Blo 1084620 1086287 := bstep (se 1 (by rfl) ⟨814715, by rfl⟩ : syracuseStep 1086287 = 1629431) B1629431
theorem B1086303 : Blo 1084620 1086303 := bstep (se 1 (by rfl) ⟨814727, by rfl⟩ : syracuseStep 1086303 = 1629455) B1629455
theorem B1086331 : Blo 1084620 1086331 := bstep (se 1 (by rfl) ⟨814748, by rfl⟩ : syracuseStep 1086331 = 1629497) B1629497
theorem B1086383 : Blo 1084620 1086383 := bstep (se 1 (by rfl) ⟨814787, by rfl⟩ : syracuseStep 1086383 = 1629575) B1629575
theorem B1086407 : Blo 1084620 1086407 := bstep (se 1 (by rfl) ⟨814805, by rfl⟩ : syracuseStep 1086407 = 1629611) B1629611
theorem B1086427 : Blo 1084620 1086427 := bstep (se 1 (by rfl) ⟨814820, by rfl⟩ : syracuseStep 1086427 = 1629641) B1629641
theorem B1086503 : Blo 1084620 1086503 := bstep (se 1 (by rfl) ⟨814877, by rfl⟩ : syracuseStep 1086503 = 1629755) B1629755
theorem B1086543 : Blo 1084620 1086543 := bstep (se 1 (by rfl) ⟨814907, by rfl⟩ : syracuseStep 1086543 = 1629815) B1629815
theorem B1086559 : Blo 1084620 1086559 := bstep (se 1 (by rfl) ⟨814919, by rfl⟩ : syracuseStep 1086559 = 1629839) B1629839
theorem B1086587 : Blo 1084620 1086587 := bstep (se 1 (by rfl) ⟨814940, by rfl⟩ : syracuseStep 1086587 = 1629881) B1629881
theorem B1086639 : Blo 1084620 1086639 := bstep (se 1 (by rfl) ⟨814979, by rfl⟩ : syracuseStep 1086639 = 1629959) B1629959
theorem B1086663 : Blo 1084620 1086663 := bstep (se 1 (by rfl) ⟨814997, by rfl⟩ : syracuseStep 1086663 = 1629995) B1629995
theorem B1742023 : Blo 1084620 1742023 := bstep (se 1 (by rfl) ⟨1306517, by rfl⟩ : syracuseStep 1742023 = 2613035) B2613035
theorem B1086683 : Blo 1084620 1086683 := bstep (se 1 (by rfl) ⟨815012, by rfl⟩ : syracuseStep 1086683 = 1630025) B1630025
theorem B2200823 : Blo 1084620 2200823 := bstep (se 1 (by rfl) ⟨1650617, by rfl⟩ : syracuseStep 2200823 = 3301235) B3301235
theorem B6198551 : Blo 1084620 6198551 := bstep (se 1 (by rfl) ⟨4648913, by rfl⟩ : syracuseStep 6198551 = 9297827) B9297827
theorem B1086759 : Blo 1084620 1086759 := bstep (se 1 (by rfl) ⟨815069, by rfl⟩ : syracuseStep 1086759 = 1630139) B1630139
theorem B1086799 : Blo 1084620 1086799 := bstep (se 1 (by rfl) ⟨815099, by rfl⟩ : syracuseStep 1086799 = 1630199) B1630199
theorem B1086815 : Blo 1084620 1086815 := bstep (se 1 (by rfl) ⟨815111, by rfl⟩ : syracuseStep 1086815 = 1630223) B1630223
theorem B1086843 : Blo 1084620 1086843 := bstep (se 1 (by rfl) ⟨815132, by rfl⟩ : syracuseStep 1086843 = 1630265) B1630265
theorem B1086895 : Blo 1084620 1086895 := bstep (se 1 (by rfl) ⟨815171, by rfl⟩ : syracuseStep 1086895 = 1630343) B1630343
theorem B1086919 : Blo 1084620 1086919 := bstep (se 1 (by rfl) ⟨815189, by rfl⟩ : syracuseStep 1086919 = 1630379) B1630379
theorem B1086939 : Blo 1084620 1086939 := bstep (se 1 (by rfl) ⟨815204, by rfl⟩ : syracuseStep 1086939 = 1630409) B1630409
theorem B13899275 : Blo 1084620 13899275 := bstep (se 1 (by rfl) ⟨10424456, by rfl⟩ : syracuseStep 13899275 = 20848913) B20848913
theorem B15668747 : Blo 1084620 15668747 := bstep (se 1 (by rfl) ⟨11751560, by rfl⟩ : syracuseStep 15668747 = 23503121) B23503121
theorem B1087015 : Blo 1084620 1087015 := bstep (se 1 (by rfl) ⟨815261, by rfl⟩ : syracuseStep 1087015 = 1630523) B1630523
theorem B1087055 : Blo 1084620 1087055 := bstep (se 1 (by rfl) ⟨815291, by rfl⟩ : syracuseStep 1087055 = 1630583) B1630583
theorem B1087071 : Blo 1084620 1087071 := bstep (se 1 (by rfl) ⟨815303, by rfl⟩ : syracuseStep 1087071 = 1630607) B1630607
theorem B5510753 : Blo 1084620 5510753 := bstep (se 2 (by rfl) ⟨2066532, by rfl⟩ : syracuseStep 5510753 = 4133065) B4133065
theorem B1087099 : Blo 1084620 1087099 := bstep (se 1 (by rfl) ⟨815324, by rfl⟩ : syracuseStep 1087099 = 1630649) B1630649
theorem B1087151 : Blo 1084620 1087151 := bstep (se 1 (by rfl) ⟨815363, by rfl⟩ : syracuseStep 1087151 = 1630727) B1630727
theorem B1087175 : Blo 1084620 1087175 := bstep (se 1 (by rfl) ⟨815381, by rfl⟩ : syracuseStep 1087175 = 1630763) B1630763
theorem B1087195 : Blo 1084620 1087195 := bstep (se 1 (by rfl) ⟨815396, by rfl⟩ : syracuseStep 1087195 = 1630793) B1630793
theorem B8263457 : Blo 1084620 8263457 := bstep (se 2 (by rfl) ⟨3098796, by rfl⟩ : syracuseStep 8263457 = 6197593) B6197593
theorem B1087271 : Blo 1084620 1087271 := bstep (se 1 (by rfl) ⟨815453, by rfl⟩ : syracuseStep 1087271 = 1630907) B1630907
theorem B15898427 : Blo 1084620 15898427 := bstep (se 1 (by rfl) ⟨11923820, by rfl⟩ : syracuseStep 15898427 = 23847641) B23847641
theorem B1087311 : Blo 1084620 1087311 := bstep (se 1 (by rfl) ⟨815483, by rfl⟩ : syracuseStep 1087311 = 1630967) B1630967
theorem B5871455 : Blo 1084620 5871455 := bstep (se 1 (by rfl) ⟨4403591, by rfl⟩ : syracuseStep 5871455 = 8807183) B8807183
theorem B1087327 : Blo 1084620 1087327 := bstep (se 1 (by rfl) ⟨815495, by rfl⟩ : syracuseStep 1087327 = 1630991) B1630991
theorem B1087355 : Blo 1084620 1087355 := bstep (se 1 (by rfl) ⟨815516, by rfl⟩ : syracuseStep 1087355 = 1631033) B1631033
theorem B1087407 : Blo 1084620 1087407 := bstep (se 1 (by rfl) ⟨815555, by rfl⟩ : syracuseStep 1087407 = 1631111) B1631111
theorem B3479483 : Blo 1084620 3479483 := bstep (se 1 (by rfl) ⟨2609612, by rfl⟩ : syracuseStep 3479483 = 5219225) B5219225
theorem B1087431 : Blo 1084620 1087431 := bstep (se 1 (by rfl) ⟨815573, by rfl⟩ : syracuseStep 1087431 = 1631147) B1631147
theorem B1087451 : Blo 1084620 1087451 := bstep (se 1 (by rfl) ⟨815588, by rfl⟩ : syracuseStep 1087451 = 1631177) B1631177
theorem B1677275 : Blo 1084620 1677275 := bstep (se 1 (by rfl) ⟨1257956, by rfl⟩ : syracuseStep 1677275 = 2515913) B2515913
theorem B1087527 : Blo 1084620 1087527 := bstep (se 1 (by rfl) ⟨815645, by rfl⟩ : syracuseStep 1087527 = 1631291) B1631291
theorem B1087567 : Blo 1084620 1087567 := bstep (se 1 (by rfl) ⟨815675, by rfl⟩ : syracuseStep 1087567 = 1631351) B1631351
theorem B5216345 : Blo 1084620 5216345 := bstep (se 2 (by rfl) ⟨1956129, by rfl⟩ : syracuseStep 5216345 = 3912259) B3912259
theorem B1087583 : Blo 1084620 1087583 := bstep (se 1 (by rfl) ⟨815687, by rfl⟩ : syracuseStep 1087583 = 1631375) B1631375
theorem B1087611 : Blo 1084620 1087611 := bstep (se 1 (by rfl) ⟨815708, by rfl⟩ : syracuseStep 1087611 = 1631417) B1631417
theorem B6690973 : Blo 1084620 6690973 := bstep (se 3 (by rfl) ⟨1254557, by rfl⟩ : syracuseStep 6690973 = 2509115) B2509115
theorem B1087663 : Blo 1084620 1087663 := bstep (se 1 (by rfl) ⟨815747, by rfl⟩ : syracuseStep 1087663 = 1631495) B1631495
theorem B1087687 : Blo 1084620 1087687 := bstep (se 1 (by rfl) ⟨815765, by rfl⟩ : syracuseStep 1087687 = 1631531) B1631531
theorem B1087707 : Blo 1084620 1087707 := bstep (se 1 (by rfl) ⟨815780, by rfl⟩ : syracuseStep 1087707 = 1631561) B1631561
theorem B59513089 : Blo 1084620 59513089 := bstep (se 2 (by rfl) ⟨22317408, by rfl⟩ : syracuseStep 59513089 = 44634817) B44634817
theorem B1087783 : Blo 1084620 1087783 := bstep (se 1 (by rfl) ⟨815837, by rfl⟩ : syracuseStep 1087783 = 1631675) B1631675
theorem B1087823 : Blo 1084620 1087823 := bstep (se 1 (by rfl) ⟨815867, by rfl⟩ : syracuseStep 1087823 = 1631735) B1631735
theorem B1087839 : Blo 1084620 1087839 := bstep (se 1 (by rfl) ⟨815879, by rfl⟩ : syracuseStep 1087839 = 1631759) B1631759
theorem B1087867 : Blo 1084620 1087867 := bstep (se 1 (by rfl) ⟨815900, by rfl⟩ : syracuseStep 1087867 = 1631801) B1631801
theorem B1087919 : Blo 1084620 1087919 := bstep (se 1 (by rfl) ⟨815939, by rfl⟩ : syracuseStep 1087919 = 1631879) B1631879
theorem B1087943 : Blo 1084620 1087943 := bstep (se 1 (by rfl) ⟨815957, by rfl⟩ : syracuseStep 1087943 = 1631915) B1631915
theorem B1087963 : Blo 1084620 1087963 := bstep (se 1 (by rfl) ⟨815972, by rfl⟩ : syracuseStep 1087963 = 1631945) B1631945
theorem B1088039 : Blo 1084620 1088039 := bstep (se 1 (by rfl) ⟨816029, by rfl⟩ : syracuseStep 1088039 = 1632059) B1632059
theorem B1088079 : Blo 1084620 1088079 := bstep (se 1 (by rfl) ⟨816059, by rfl⟩ : syracuseStep 1088079 = 1632119) B1632119
theorem B1088095 : Blo 1084620 1088095 := bstep (se 1 (by rfl) ⟨816071, by rfl⟩ : syracuseStep 1088095 = 1632143) B1632143
theorem B1088123 : Blo 1084620 1088123 := bstep (se 1 (by rfl) ⟨816092, by rfl⟩ : syracuseStep 1088123 = 1632185) B1632185
theorem B1088175 : Blo 1084620 1088175 := bstep (se 1 (by rfl) ⟨816131, by rfl⟩ : syracuseStep 1088175 = 1632263) B1632263
theorem B1088199 : Blo 1084620 1088199 := bstep (se 1 (by rfl) ⟨816149, by rfl⟩ : syracuseStep 1088199 = 1632299) B1632299
theorem B1088219 : Blo 1084620 1088219 := bstep (se 1 (by rfl) ⟨816164, by rfl⟩ : syracuseStep 1088219 = 1632329) B1632329
theorem B1088295 : Blo 1084620 1088295 := bstep (se 1 (by rfl) ⟨816221, by rfl⟩ : syracuseStep 1088295 = 1632443) B1632443
theorem B1743689 : Blo 1084620 1743689 := bstep (se 2 (by rfl) ⟨653883, by rfl⟩ : syracuseStep 1743689 = 1307767) B1307767
theorem B1088335 : Blo 1084620 1088335 := bstep (se 1 (by rfl) ⟨816251, by rfl⟩ : syracuseStep 1088335 = 1632503) B1632503
theorem B1088351 : Blo 1084620 1088351 := bstep (se 1 (by rfl) ⟨816263, by rfl⟩ : syracuseStep 1088351 = 1632527) B1632527
theorem B1088379 : Blo 1084620 1088379 := bstep (se 1 (by rfl) ⟨816284, by rfl⟩ : syracuseStep 1088379 = 1632569) B1632569
theorem B2202511 : Blo 1084620 2202511 := bstep (se 1 (by rfl) ⟨1651883, by rfl⟩ : syracuseStep 2202511 = 3303767) B3303767
theorem B1088431 : Blo 1084620 1088431 := bstep (se 1 (by rfl) ⟨816323, by rfl⟩ : syracuseStep 1088431 = 1632647) B1632647
theorem B1088455 : Blo 1084620 1088455 := bstep (se 1 (by rfl) ⟨816341, by rfl⟩ : syracuseStep 1088455 = 1632683) B1632683
theorem B1088475 : Blo 1084620 1088475 := bstep (se 1 (by rfl) ⟨816356, by rfl⟩ : syracuseStep 1088475 = 1632713) B1632713
theorem B1088551 : Blo 1084620 1088551 := bstep (se 1 (by rfl) ⟨816413, by rfl⟩ : syracuseStep 1088551 = 1632827) B1632827
theorem B1088591 : Blo 1084620 1088591 := bstep (se 1 (by rfl) ⟨816443, by rfl⟩ : syracuseStep 1088591 = 1632887) B1632887
theorem B1088607 : Blo 1084620 1088607 := bstep (se 1 (by rfl) ⟨816455, by rfl⟩ : syracuseStep 1088607 = 1632911) B1632911
theorem B17603983 : Blo 1084620 17603983 := bstep (se 1 (by rfl) ⟨13202987, by rfl⟩ : syracuseStep 17603983 = 26405975) B26405975
theorem B2203193 : Blo 1084620 2203193 := bstep (se 2 (by rfl) ⟨826197, by rfl⟩ : syracuseStep 2203193 = 1652395) B1652395
theorem B4398731 : Blo 1084620 4398731 := bstep (se 1 (by rfl) ⟨3299048, by rfl⟩ : syracuseStep 4398731 = 6598097) B6598097
theorem B18554507 : Blo 1084620 18554507 := bstep (se 1 (by rfl) ⟨13915880, by rfl⟩ : syracuseStep 18554507 = 27831761) B27831761
theorem B16981721 : Blo 1084620 16981721 := bstep (se 2 (by rfl) ⟨6368145, by rfl⟩ : syracuseStep 16981721 = 12736291) B12736291
theorem B4464503 : Blo 1084620 4464503 := bstep (se 1 (by rfl) ⟨3348377, by rfl⟩ : syracuseStep 4464503 = 6696755) B6696755
theorem B1220647 : Blo 1084620 1220647 := bstep (se 1 (by rfl) ⟨915485, by rfl⟩ : syracuseStep 1220647 = 1830971) B1830971
theorem B18817085 : Blo 1084620 18817085 := bstep (se 3 (by rfl) ⟨3528203, by rfl⟩ : syracuseStep 18817085 = 7056407) B7056407
theorem B5283929 : Blo 1084620 5283929 := bstep (se 2 (by rfl) ⟨1981473, by rfl⟩ : syracuseStep 5283929 = 3962947) B3962947
theorem B13901939 : Blo 1084620 13901939 := bstep (se 1 (by rfl) ⟨10426454, by rfl⟩ : syracuseStep 13901939 = 20852909) B20852909
theorem B1548487 : Blo 1084620 1548487 := bstep (se 1 (by rfl) ⟨1161365, by rfl⟩ : syracuseStep 1548487 = 2322731) B2322731
theorem B3482099 : Blo 1084620 3482099 := bstep (se 1 (by rfl) ⟨2611574, by rfl⟩ : syracuseStep 3482099 = 5223149) B5223149
theorem B4465249 : Blo 1084620 4465249 := bstep (se 2 (by rfl) ⟨1674468, by rfl⟩ : syracuseStep 4465249 = 3348937) B3348937
theorem B4399865 : Blo 1084620 4399865 := bstep (se 2 (by rfl) ⟨1649949, by rfl⟩ : syracuseStep 4399865 = 3299899) B3299899
theorem B6956279 : Blo 1084620 6956279 := bstep (se 1 (by rfl) ⟨5217209, by rfl⟩ : syracuseStep 6956279 = 10434419) B10434419
theorem B3909217 : Blo 1084620 3909217 := bstep (se 2 (by rfl) ⟨1465956, by rfl⟩ : syracuseStep 3909217 = 2931913) B2931913
theorem B1222267 : Blo 1084620 1222267 := bstep (se 1 (by rfl) ⟨916700, by rfl⟩ : syracuseStep 1222267 = 1833401) B1833401
theorem B3909331 : Blo 1084620 3909331 := bstep (se 1 (by rfl) ⟨2931998, by rfl⟩ : syracuseStep 3909331 = 5863997) B5863997
theorem B6956765 : Blo 1084620 6956765 := bstep (se 3 (by rfl) ⟨1304393, by rfl⟩ : syracuseStep 6956765 = 2608787) B2608787
theorem B18589499 : Blo 1084620 18589499 := bstep (se 1 (by rfl) ⟨13942124, by rfl⟩ : syracuseStep 18589499 = 27884249) B27884249
theorem B1222735 : Blo 1084620 1222735 := bstep (se 1 (by rfl) ⟨917051, by rfl⟩ : syracuseStep 1222735 = 1834103) B1834103
theorem B11741273 : Blo 1084620 11741273 := bstep (se 2 (by rfl) ⟨4402977, by rfl⟩ : syracuseStep 11741273 = 8805955) B8805955
theorem B9414913 : Blo 1084620 9414913 := bstep (se 2 (by rfl) ⟨3530592, by rfl⟩ : syracuseStep 9414913 = 7061185) B7061185
theorem B1223131 : Blo 1084620 1223131 := bstep (se 1 (by rfl) ⟨917348, by rfl⟩ : syracuseStep 1223131 = 1834697) B1834697
theorem B1223599 : Blo 1084620 1223599 := bstep (se 1 (by rfl) ⟨917699, by rfl⟩ : syracuseStep 1223599 = 1835399) B1835399
theorem B6040747 : Blo 1084620 6040747 := bstep (se 1 (by rfl) ⟨4530560, by rfl⟩ : syracuseStep 6040747 = 9061121) B9061121
theorem B1224031 : Blo 1084620 1224031 := bstep (se 1 (by rfl) ⟨918023, by rfl⟩ : syracuseStep 1224031 = 1836047) B1836047
theorem B3911017 : Blo 1084620 3911017 := bstep (se 2 (by rfl) ⟨1466631, by rfl⟩ : syracuseStep 3911017 = 2933263) B2933263
theorem B5222033 : Blo 1084620 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B1224391 : Blo 1084620 1224391 := bstep (se 1 (by rfl) ⟨918293, by rfl⟩ : syracuseStep 1224391 = 1836587) B1836587
theorem B6958943 : Blo 1084620 6958943 := bstep (se 1 (by rfl) ⟨5219207, by rfl⟩ : syracuseStep 6958943 = 10438415) B10438415
theorem B8237213 : Blo 1084620 8237213 := bstep (se 3 (by rfl) ⟨1544477, by rfl⟩ : syracuseStep 8237213 = 3088955) B3088955
theorem B127250929 : Blo 1084620 127250929 := bstep (se 2 (by rfl) ⟨47719098, by rfl⟩ : syracuseStep 127250929 = 95438197) B95438197
theorem B4174375 : Blo 1084620 4174375 := bstep (se 1 (by rfl) ⟨3130781, by rfl⟩ : syracuseStep 4174375 = 6261563) B6261563
theorem B7844525 : Blo 1084620 7844525 := bstep (se 3 (by rfl) ⟨1470848, by rfl⟩ : syracuseStep 7844525 = 2941697) B2941697
theorem B3912401 : Blo 1084620 3912401 := bstep (se 2 (by rfl) ⟨1467150, by rfl⟩ : syracuseStep 3912401 = 2934301) B2934301
theorem B17642393 : Blo 1084620 17642393 := bstep (se 2 (by rfl) ⟨6615897, by rfl⟩ : syracuseStep 17642393 = 13231795) B13231795
theorem B3094139 : Blo 1084620 3094139 := bstep (se 1 (by rfl) ⟨2320604, by rfl⟩ : syracuseStep 3094139 = 4641209) B4641209
theorem B4175725 : Blo 1084620 4175725 := bstep (se 3 (by rfl) ⟨782948, by rfl⟩ : syracuseStep 4175725 = 1565897) B1565897
theorem B1653257 : Blo 1084620 1653257 := bstep (se 2 (by rfl) ⟨619971, by rfl⟩ : syracuseStep 1653257 = 1239943) B1239943
theorem B3095471 : Blo 1084620 3095471 := bstep (se 1 (by rfl) ⟨2321603, by rfl⟩ : syracuseStep 3095471 = 4643207) B4643207
theorem B2014139 : Blo 1084620 2014139 := bstep (se 1 (by rfl) ⟨1510604, by rfl⟩ : syracuseStep 2014139 = 3021209) B3021209
theorem B8240129 : Blo 1084620 8240129 := bstep (se 2 (by rfl) ⟨3090048, by rfl⟩ : syracuseStep 8240129 = 6180097) B6180097
theorem B3914867 : Blo 1084620 3914867 := bstep (se 1 (by rfl) ⟨2936150, by rfl⟩ : syracuseStep 3914867 = 5872301) B5872301
theorem B2440439 : Blo 1084620 2440439 := bstep (se 1 (by rfl) ⟨1830329, by rfl⟩ : syracuseStep 2440439 = 3660659) B3660659
theorem B15678845 : Blo 1084620 15678845 := bstep (se 3 (by rfl) ⟨2939783, by rfl⟩ : syracuseStep 15678845 = 5879567) B5879567
theorem B8797841 : Blo 1084620 8797841 := bstep (se 2 (by rfl) ⟨3299190, by rfl⟩ : syracuseStep 8797841 = 6598381) B6598381
theorem B2441033 : Blo 1084620 2441033 := bstep (se 2 (by rfl) ⟨915387, by rfl⟩ : syracuseStep 2441033 = 1830775) B1830775
theorem B4636577 : Blo 1084620 4636577 := bstep (se 2 (by rfl) ⟨1738716, by rfl⟩ : syracuseStep 4636577 = 3477433) B3477433
theorem B1392719 : Blo 1084620 1392719 := bstep (se 1 (by rfl) ⟨1044539, by rfl⟩ : syracuseStep 1392719 = 2089079) B2089079
theorem B5226839 : Blo 1084620 5226839 := bstep (se 1 (by rfl) ⟨3920129, by rfl⟩ : syracuseStep 5226839 = 7840259) B7840259
theorem B17187337 : Blo 1084620 17187337 := bstep (se 2 (by rfl) ⟨6445251, by rfl⟩ : syracuseStep 17187337 = 12890503) B12890503
theorem B5227067 : Blo 1084620 5227067 := bstep (se 1 (by rfl) ⟨3920300, by rfl⟩ : syracuseStep 5227067 = 7840601) B7840601
theorem B2441825 : Blo 1084620 2441825 := bstep (se 2 (by rfl) ⟨915684, by rfl⟩ : syracuseStep 2441825 = 1831369) B1831369
theorem B2442167 : Blo 1084620 2442167 := bstep (se 1 (by rfl) ⟨1831625, by rfl⟩ : syracuseStep 2442167 = 3663251) B3663251
theorem B2606327 : Blo 1084620 2606327 := bstep (se 1 (by rfl) ⟨1954745, by rfl⟩ : syracuseStep 2606327 = 3909491) B3909491
theorem B3523945 : Blo 1084620 3523945 := bstep (se 2 (by rfl) ⟨1321479, by rfl⟩ : syracuseStep 3523945 = 2642959) B2642959
theorem B2442761 : Blo 1084620 2442761 := bstep (se 2 (by rfl) ⟨916035, by rfl⟩ : syracuseStep 2442761 = 1832071) B1832071
theorem B5228221 : Blo 1084620 5228221 := bstep (se 3 (by rfl) ⟨980291, by rfl⟩ : syracuseStep 5228221 = 1960583) B1960583
theorem B2443103 : Blo 1084620 2443103 := bstep (se 1 (by rfl) ⟨1832327, by rfl⟩ : syracuseStep 2443103 = 3664655) B3664655
theorem B4638559 : Blo 1084620 4638559 := bstep (se 1 (by rfl) ⟨3478919, by rfl⟩ : syracuseStep 4638559 = 6957839) B6957839
theorem B27871127 : Blo 1084620 27871127 := bstep (se 1 (by rfl) ⟨20903345, by rfl⟩ : syracuseStep 27871127 = 41806691) B41806691
theorem B5883911 : Blo 1084620 5883911 := bstep (se 1 (by rfl) ⟨4412933, by rfl⟩ : syracuseStep 5883911 = 8825867) B8825867
theorem B2443283 : Blo 1084620 2443283 := bstep (se 1 (by rfl) ⟨1832462, by rfl⟩ : syracuseStep 2443283 = 3664925) B3664925
theorem B10438757 : Blo 1084620 10438757 := bstep (se 4 (by rfl) ⟨978633, by rfl⟩ : syracuseStep 10438757 = 1957267) B1957267
theorem B2443625 : Blo 1084620 2443625 := bstep (se 2 (by rfl) ⟨916359, by rfl⟩ : syracuseStep 2443625 = 1832719) B1832719
theorem B1395127 : Blo 1084620 1395127 := bstep (se 1 (by rfl) ⟨1046345, by rfl⟩ : syracuseStep 1395127 = 2092691) B2092691
theorem B36161977 : Blo 1084620 36161977 := bstep (se 2 (by rfl) ⟨13560741, by rfl⟩ : syracuseStep 36161977 = 27121483) B27121483
theorem B3099161 : Blo 1084620 3099161 := bstep (se 2 (by rfl) ⟨1162185, by rfl⟩ : syracuseStep 3099161 = 2324371) B2324371
theorem B4639517 : Blo 1084620 4639517 := bstep (se 3 (by rfl) ⟨869909, by rfl⟩ : syracuseStep 4639517 = 1739819) B1739819
theorem B36162449 : Blo 1084620 36162449 := bstep (se 2 (by rfl) ⟨13560918, by rfl⟩ : syracuseStep 36162449 = 27121837) B27121837
theorem B2444219 : Blo 1084620 2444219 := bstep (se 1 (by rfl) ⟨1833164, by rfl⟩ : syracuseStep 2444219 = 3666329) B3666329
theorem B2444345 : Blo 1084620 2444345 := bstep (se 2 (by rfl) ⟨916629, by rfl⟩ : syracuseStep 2444345 = 1833259) B1833259
theorem B8244503 : Blo 1084620 8244503 := bstep (se 1 (by rfl) ⟨6183377, by rfl⟩ : syracuseStep 8244503 = 12366755) B12366755
theorem B9915671 : Blo 1084620 9915671 := bstep (se 1 (by rfl) ⟨7436753, by rfl⟩ : syracuseStep 9915671 = 14873507) B14873507
theorem B2444687 : Blo 1084620 2444687 := bstep (se 1 (by rfl) ⟨1833515, by rfl⟩ : syracuseStep 2444687 = 3667031) B3667031
theorem B2445011 : Blo 1084620 2445011 := bstep (se 1 (by rfl) ⟨1833758, by rfl⟩ : syracuseStep 2445011 = 3667517) B3667517
theorem B12374045 : Blo 1084620 12374045 := bstep (se 3 (by rfl) ⟨2320133, by rfl⟩ : syracuseStep 12374045 = 4640267) B4640267
theorem B15683969 : Blo 1084620 15683969 := bstep (se 2 (by rfl) ⟨5881488, by rfl⟩ : syracuseStep 15683969 = 11762977) B11762977
theorem B5493257 : Blo 1084620 5493257 := bstep (se 2 (by rfl) ⟨2059971, by rfl⟩ : syracuseStep 5493257 = 4119943) B4119943
theorem B2445947 : Blo 1084620 2445947 := bstep (se 1 (by rfl) ⟨1834460, by rfl⟩ : syracuseStep 2445947 = 3668921) B3668921
theorem B8245961 : Blo 1084620 8245961 := bstep (se 2 (by rfl) ⟨3092235, by rfl⟩ : syracuseStep 8245961 = 6184471) B6184471
theorem B2446073 : Blo 1084620 2446073 := bstep (se 2 (by rfl) ⟨917277, by rfl⟩ : syracuseStep 2446073 = 1834555) B1834555
theorem B1627055 : Blo 1084620 1627055 := bstep (se 1 (by rfl) ⟨1220291, by rfl⟩ : syracuseStep 1627055 = 2440583) B2440583
theorem B2446343 : Blo 1084620 2446343 := bstep (se 1 (by rfl) ⟨1834757, by rfl⟩ : syracuseStep 2446343 = 3669515) B3669515
theorem B1627145 : Blo 1084620 1627145 := bstep (se 2 (by rfl) ⟨610179, by rfl⟩ : syracuseStep 1627145 = 1220359) B1220359
theorem B1627175 : Blo 1084620 1627175 := bstep (se 1 (by rfl) ⟨1220381, by rfl⟩ : syracuseStep 1627175 = 2440763) B2440763
theorem B2446415 : Blo 1084620 2446415 := bstep (se 1 (by rfl) ⟨1834811, by rfl⟩ : syracuseStep 2446415 = 3669623) B3669623
theorem B1627259 : Blo 1084620 1627259 := bstep (se 1 (by rfl) ⟨1220444, by rfl⟩ : syracuseStep 1627259 = 2440889) B2440889
theorem B1627385 : Blo 1084620 1627385 := bstep (se 2 (by rfl) ⟨610269, by rfl⟩ : syracuseStep 1627385 = 1220539) B1220539
theorem B1627487 : Blo 1084620 1627487 := bstep (se 1 (by rfl) ⟨1220615, by rfl⟩ : syracuseStep 1627487 = 2441231) B2441231
theorem B1627499 : Blo 1084620 1627499 := bstep (se 1 (by rfl) ⟨1220624, by rfl⟩ : syracuseStep 1627499 = 2441249) B2441249
theorem B2610575 : Blo 1084620 2610575 := bstep (se 1 (by rfl) ⟨1957931, by rfl⟩ : syracuseStep 2610575 = 3915863) B3915863
theorem B2446811 : Blo 1084620 2446811 := bstep (se 1 (by rfl) ⟨1835108, by rfl⟩ : syracuseStep 2446811 = 3670217) B3670217
theorem B1627727 : Blo 1084620 1627727 := bstep (se 1 (by rfl) ⟨1220795, by rfl⟩ : syracuseStep 1627727 = 2441591) B2441591
theorem B1627847 : Blo 1084620 1627847 := bstep (se 1 (by rfl) ⟨1220885, by rfl⟩ : syracuseStep 1627847 = 2441771) B2441771
theorem B15652601 : Blo 1084620 15652601 := bstep (se 2 (by rfl) ⟨5869725, by rfl⟩ : syracuseStep 15652601 = 11739451) B11739451
theorem B1628009 : Blo 1084620 1628009 := bstep (se 2 (by rfl) ⟨610503, by rfl⟩ : syracuseStep 1628009 = 1221007) B1221007
theorem B6608749 : Blo 1084620 6608749 := bstep (se 3 (by rfl) ⟨1239140, by rfl⟩ : syracuseStep 6608749 = 2478281) B2478281
theorem B2480033 : Blo 1084620 2480033 := bstep (se 2 (by rfl) ⟨930012, by rfl⟩ : syracuseStep 2480033 = 1860025) B1860025
theorem B2447279 : Blo 1084620 2447279 := bstep (se 1 (by rfl) ⟨1835459, by rfl⟩ : syracuseStep 2447279 = 3670919) B3670919
theorem B1628087 : Blo 1084620 1628087 := bstep (se 1 (by rfl) ⟨1221065, by rfl⟩ : syracuseStep 1628087 = 2442131) B2442131
theorem B5494715 : Blo 1084620 5494715 := bstep (se 1 (by rfl) ⟨4121036, by rfl⟩ : syracuseStep 5494715 = 8242073) B8242073
theorem B1628123 : Blo 1084620 1628123 := bstep (se 1 (by rfl) ⟨1221092, by rfl⟩ : syracuseStep 1628123 = 2442185) B2442185
theorem B6969401 : Blo 1084620 6969401 := bstep (se 2 (by rfl) ⟨2613525, by rfl⟩ : syracuseStep 6969401 = 5227051) B5227051
theorem B2447531 : Blo 1084620 2447531 := bstep (se 1 (by rfl) ⟨1835648, by rfl⟩ : syracuseStep 2447531 = 3671297) B3671297
theorem B16963991 : Blo 1084620 16963991 := bstep (se 1 (by rfl) ⟨12722993, by rfl⟩ : syracuseStep 16963991 = 25445987) B25445987
theorem B1628591 : Blo 1084620 1628591 := bstep (se 1 (by rfl) ⟨1221443, by rfl⟩ : syracuseStep 1628591 = 2442887) B2442887
theorem B7821805 : Blo 1084620 7821805 := bstep (se 3 (by rfl) ⟨1466588, by rfl⟩ : syracuseStep 7821805 = 2933177) B2933177
theorem B1628681 : Blo 1084620 1628681 := bstep (se 2 (by rfl) ⟨610755, by rfl⟩ : syracuseStep 1628681 = 1221511) B1221511
theorem B7428631 : Blo 1084620 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B1628711 : Blo 1084620 1628711 := bstep (se 1 (by rfl) ⟨1221533, by rfl⟩ : syracuseStep 1628711 = 2443067) B2443067
theorem B1956431 : Blo 1084620 1956431 := bstep (se 1 (by rfl) ⟨1467323, by rfl⟩ : syracuseStep 1956431 = 2934647) B2934647
theorem B1628795 : Blo 1084620 1628795 := bstep (se 1 (by rfl) ⟨1221596, by rfl⟩ : syracuseStep 1628795 = 2443193) B2443193
theorem B2448071 : Blo 1084620 2448071 := bstep (se 1 (by rfl) ⟨1836053, by rfl⟩ : syracuseStep 2448071 = 3672107) B3672107
theorem B1628921 : Blo 1084620 1628921 := bstep (se 2 (by rfl) ⟨610845, by rfl⟩ : syracuseStep 1628921 = 1221691) B1221691
theorem B1629023 : Blo 1084620 1629023 := bstep (se 1 (by rfl) ⟨1221767, by rfl⟩ : syracuseStep 1629023 = 2443535) B2443535
theorem B1629035 : Blo 1084620 1629035 := bstep (se 1 (by rfl) ⟨1221776, by rfl⟩ : syracuseStep 1629035 = 2443553) B2443553
theorem B4119457 : Blo 1084620 4119457 := bstep (se 2 (by rfl) ⟨1544796, by rfl⟩ : syracuseStep 4119457 = 3089593) B3089593
theorem B4021249 : Blo 1084620 4021249 := bstep (se 2 (by rfl) ⟨1507968, by rfl⟩ : syracuseStep 4021249 = 3015937) B3015937
theorem B1629263 : Blo 1084620 1629263 := bstep (se 1 (by rfl) ⟨1221947, by rfl⟩ : syracuseStep 1629263 = 2443895) B2443895
theorem B4643993 : Blo 1084620 4643993 := bstep (se 2 (by rfl) ⟨1741497, by rfl⟩ : syracuseStep 4643993 = 3482995) B3482995
theorem B1629383 : Blo 1084620 1629383 := bstep (se 1 (by rfl) ⟨1222037, by rfl⟩ : syracuseStep 1629383 = 2444075) B2444075
theorem B5496011 : Blo 1084620 5496011 := bstep (se 1 (by rfl) ⟨4122008, by rfl⟩ : syracuseStep 5496011 = 8244017) B8244017
theorem B1957225 : Blo 1084620 1957225 := bstep (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) B1467919
theorem B1629545 : Blo 1084620 1629545 := bstep (se 2 (by rfl) ⟨611079, by rfl⟩ : syracuseStep 1629545 = 1222159) B1222159
theorem B3661199 : Blo 1084620 3661199 := bstep (se 1 (by rfl) ⟨2745899, by rfl⟩ : syracuseStep 3661199 = 5491799) B5491799
theorem B1629623 : Blo 1084620 1629623 := bstep (se 1 (by rfl) ⟨1222217, by rfl⟩ : syracuseStep 1629623 = 2444435) B2444435
theorem B1629659 : Blo 1084620 1629659 := bstep (se 1 (by rfl) ⟨1222244, by rfl⟩ : syracuseStep 1629659 = 2444489) B2444489
theorem B2448935 : Blo 1084620 2448935 := bstep (se 1 (by rfl) ⟨1836701, by rfl⟩ : syracuseStep 2448935 = 3673403) B3673403
theorem B3661523 : Blo 1084620 3661523 := bstep (se 1 (by rfl) ⟨2746142, by rfl⟩ : syracuseStep 3661523 = 5492285) B5492285
theorem B4120415 : Blo 1084620 4120415 := bstep (se 1 (by rfl) ⟨3090311, by rfl⟩ : syracuseStep 4120415 = 6180623) B6180623
theorem B2449259 : Blo 1084620 2449259 := bstep (se 1 (by rfl) ⟨1836944, by rfl⟩ : syracuseStep 2449259 = 3673889) B3673889
theorem B4120429 : Blo 1084620 4120429 := bstep (se 3 (by rfl) ⟨772580, by rfl⟩ : syracuseStep 4120429 = 1545161) B1545161
theorem B2645921 : Blo 1084620 2645921 := bstep (se 2 (by rfl) ⟨992220, by rfl⟩ : syracuseStep 2645921 = 1984441) B1984441
theorem B2449313 : Blo 1084620 2449313 := bstep (se 2 (by rfl) ⟨918492, by rfl⟩ : syracuseStep 2449313 = 1836985) B1836985
theorem B1630127 : Blo 1084620 1630127 := bstep (se 1 (by rfl) ⟨1222595, by rfl⟩ : syracuseStep 1630127 = 2445191) B2445191
theorem B1630217 : Blo 1084620 1630217 := bstep (se 2 (by rfl) ⟨611331, by rfl⟩ : syracuseStep 1630217 = 1222663) B1222663
theorem B6184997 : Blo 1084620 6184997 := bstep (se 4 (by rfl) ⟨579843, by rfl⟩ : syracuseStep 6184997 = 1159687) B1159687
theorem B1630247 : Blo 1084620 1630247 := bstep (se 1 (by rfl) ⟨1222685, by rfl⟩ : syracuseStep 1630247 = 2445371) B2445371
theorem B1630331 : Blo 1084620 1630331 := bstep (se 1 (by rfl) ⟨1222748, by rfl⟩ : syracuseStep 1630331 = 2445497) B2445497
theorem B4120733 : Blo 1084620 4120733 := bstep (se 3 (by rfl) ⟨772637, by rfl⟩ : syracuseStep 4120733 = 1545275) B1545275
theorem B1630457 : Blo 1084620 1630457 := bstep (se 2 (by rfl) ⟨611421, by rfl⟩ : syracuseStep 1630457 = 1222843) B1222843
theorem B1630559 : Blo 1084620 1630559 := bstep (se 1 (by rfl) ⟨1222919, by rfl⟩ : syracuseStep 1630559 = 2445839) B2445839
theorem B1958249 : Blo 1084620 1958249 := bstep (se 2 (by rfl) ⟨734343, by rfl⟩ : syracuseStep 1958249 = 1468687) B1468687
theorem B1630571 : Blo 1084620 1630571 := bstep (se 1 (by rfl) ⟨1222928, by rfl⟩ : syracuseStep 1630571 = 2445857) B2445857
theorem B1958305 : Blo 1084620 1958305 := bstep (se 2 (by rfl) ⟨734364, by rfl⟩ : syracuseStep 1958305 = 1468729) B1468729
theorem B1630799 : Blo 1084620 1630799 := bstep (se 1 (by rfl) ⟨1223099, by rfl⟩ : syracuseStep 1630799 = 2446199) B2446199
theorem B1630919 : Blo 1084620 1630919 := bstep (se 1 (by rfl) ⟨1223189, by rfl⟩ : syracuseStep 1630919 = 2446379) B2446379
theorem B4121387 : Blo 1084620 4121387 := bstep (se 1 (by rfl) ⟨3091040, by rfl⟩ : syracuseStep 4121387 = 6182081) B6182081
theorem B1631081 : Blo 1084620 1631081 := bstep (se 2 (by rfl) ⟨611655, by rfl⟩ : syracuseStep 1631081 = 1223311) B1223311
theorem B3662711 : Blo 1084620 3662711 := bstep (se 1 (by rfl) ⟨2747033, by rfl⟩ : syracuseStep 3662711 = 5494067) B5494067
theorem B1631159 : Blo 1084620 1631159 := bstep (se 1 (by rfl) ⟨1223369, by rfl⟩ : syracuseStep 1631159 = 2446739) B2446739
theorem B1631195 : Blo 1084620 1631195 := bstep (se 1 (by rfl) ⟨1223396, by rfl⟩ : syracuseStep 1631195 = 2446793) B2446793
theorem B4645907 : Blo 1084620 4645907 := bstep (se 1 (by rfl) ⟨3484430, by rfl⟩ : syracuseStep 4645907 = 6968861) B6968861
theorem B3662927 : Blo 1084620 3662927 := bstep (se 1 (by rfl) ⟨2747195, by rfl⟩ : syracuseStep 3662927 = 5494391) B5494391
theorem B2745515 : Blo 1084620 2745515 := bstep (se 1 (by rfl) ⟨2059136, by rfl⟩ : syracuseStep 2745515 = 4118273) B4118273
theorem B2090233 : Blo 1084620 2090233 := bstep (se 2 (by rfl) ⟨783837, by rfl⟩ : syracuseStep 2090233 = 1567675) B1567675
theorem B1631663 : Blo 1084620 1631663 := bstep (se 1 (by rfl) ⟨1223747, by rfl⟩ : syracuseStep 1631663 = 2447495) B2447495
theorem B3663305 : Blo 1084620 3663305 := bstep (se 2 (by rfl) ⟨1373739, by rfl⟩ : syracuseStep 3663305 = 2747479) B2747479
theorem B1631753 : Blo 1084620 1631753 := bstep (se 2 (by rfl) ⟨611907, by rfl⟩ : syracuseStep 1631753 = 1223815) B1223815
theorem B1631783 : Blo 1084620 1631783 := bstep (se 1 (by rfl) ⟨1223837, by rfl⟩ : syracuseStep 1631783 = 2447675) B2447675
theorem B3303035 : Blo 1084620 3303035 := bstep (se 1 (by rfl) ⟨2477276, by rfl⟩ : syracuseStep 3303035 = 4954553) B4954553
theorem B1631867 : Blo 1084620 1631867 := bstep (se 1 (by rfl) ⟨1223900, by rfl⟩ : syracuseStep 1631867 = 2447801) B2447801
theorem B3663575 : Blo 1084620 3663575 := bstep (se 1 (by rfl) ⟨2747681, by rfl⟩ : syracuseStep 3663575 = 5495363) B5495363
theorem B1631993 : Blo 1084620 1631993 := bstep (se 2 (by rfl) ⟨611997, by rfl⟩ : syracuseStep 1631993 = 1223995) B1223995
theorem B1632095 : Blo 1084620 1632095 := bstep (se 1 (by rfl) ⟨1224071, by rfl⟩ : syracuseStep 1632095 = 2448143) B2448143
theorem B1632107 : Blo 1084620 1632107 := bstep (se 1 (by rfl) ⟨1224080, by rfl⟩ : syracuseStep 1632107 = 2448161) B2448161
theorem B3663791 : Blo 1084620 3663791 := bstep (se 1 (by rfl) ⟨2747843, by rfl⟩ : syracuseStep 3663791 = 5495687) B5495687
theorem B2746295 : Blo 1084620 2746295 := bstep (se 1 (by rfl) ⟨2059721, by rfl⟩ : syracuseStep 2746295 = 4119443) B4119443
theorem B2615303 : Blo 1084620 2615303 := bstep (se 1 (by rfl) ⟨1961477, by rfl⟩ : syracuseStep 2615303 = 3922955) B3922955
theorem B1632335 : Blo 1084620 1632335 := bstep (se 1 (by rfl) ⟨1224251, by rfl⟩ : syracuseStep 1632335 = 2448503) B2448503
theorem B1632455 : Blo 1084620 1632455 := bstep (se 1 (by rfl) ⟨1224341, by rfl⟩ : syracuseStep 1632455 = 2448683) B2448683
theorem B1632617 : Blo 1084620 1632617 := bstep (se 2 (by rfl) ⟨612231, by rfl⟩ : syracuseStep 1632617 = 1224463) B1224463
theorem B1632695 : Blo 1084620 1632695 := bstep (se 1 (by rfl) ⟨1224521, by rfl⟩ : syracuseStep 1632695 = 2449043) B2449043
theorem B1632731 : Blo 1084620 1632731 := bstep (se 1 (by rfl) ⟨1224548, by rfl⟩ : syracuseStep 1632731 = 2449097) B2449097
theorem B6973933 : Blo 1084620 6973933 := bstep (se 3 (by rfl) ⟨1307612, by rfl⟩ : syracuseStep 6973933 = 2615225) B2615225
theorem B11168441 : Blo 1084620 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B4123345 : Blo 1084620 4123345 := bstep (se 2 (by rfl) ⟨1546254, by rfl⟩ : syracuseStep 4123345 = 3092509) B3092509
theorem B3533597 : Blo 1084620 3533597 := bstep (se 3 (by rfl) ⟨662549, by rfl⟩ : syracuseStep 3533597 = 1325099) B1325099
theorem B1469291 : Blo 1084620 1469291 := bstep (se 1 (by rfl) ⟨1101968, by rfl⟩ : syracuseStep 1469291 = 2203937) B2203937
theorem B2747297 : Blo 1084620 2747297 := bstep (se 2 (by rfl) ⟨1030236, by rfl⟩ : syracuseStep 2747297 = 2060473) B2060473
theorem B4123649 : Blo 1084620 4123649 := bstep (se 2 (by rfl) ⟨1546368, by rfl⟩ : syracuseStep 4123649 = 3092737) B3092737
theorem B2059273 : Blo 1084620 2059273 := bstep (se 2 (by rfl) ⟨772227, by rfl⟩ : syracuseStep 2059273 = 1544455) B1544455
theorem B3533843 : Blo 1084620 3533843 := bstep (se 1 (by rfl) ⟨2650382, by rfl⟩ : syracuseStep 3533843 = 5300765) B5300765
theorem B2747753 : Blo 1084620 2747753 := bstep (se 2 (by rfl) ⟨1030407, by rfl⟩ : syracuseStep 2747753 = 2060815) B2060815
theorem B4124105 : Blo 1084620 4124105 := bstep (se 2 (by rfl) ⟨1546539, by rfl⟩ : syracuseStep 4124105 = 3093079) B3093079
theorem B1306075 : Blo 1084620 1306075 := bstep (se 1 (by rfl) ⟨979556, by rfl⟩ : syracuseStep 1306075 = 1959113) B1959113
theorem B2059987 : Blo 1084620 2059987 := bstep (se 1 (by rfl) ⟨1544990, by rfl⟩ : syracuseStep 2059987 = 3089981) B3089981
theorem B1830647 : Blo 1084620 1830647 := bstep (se 1 (by rfl) ⟨1372985, by rfl⟩ : syracuseStep 1830647 = 2745971) B2745971
theorem B8253251 : Blo 1084620 8253251 := bstep (se 1 (by rfl) ⟨6189938, by rfl⟩ : syracuseStep 8253251 = 12379877) B12379877
theorem B4124591 : Blo 1084620 4124591 := bstep (se 1 (by rfl) ⟨3093443, by rfl⟩ : syracuseStep 4124591 = 6186887) B6186887
theorem B1830991 : Blo 1084620 1830991 := bstep (se 1 (by rfl) ⟨1373243, by rfl⟩ : syracuseStep 1830991 = 2746487) B2746487
theorem B3666167 : Blo 1084620 3666167 := bstep (se 1 (by rfl) ⟨2749625, by rfl⟩ : syracuseStep 3666167 = 5499251) B5499251
theorem B5501195 : Blo 1084620 5501195 := bstep (se 1 (by rfl) ⟨4125896, by rfl⟩ : syracuseStep 5501195 = 8251793) B8251793
theorem B1831241 : Blo 1084620 1831241 := bstep (se 2 (by rfl) ⟨686715, by rfl⟩ : syracuseStep 1831241 = 1373431) B1373431
theorem B2060731 : Blo 1084620 2060731 := bstep (se 1 (by rfl) ⟨1545548, by rfl⟩ : syracuseStep 2060731 = 3091097) B3091097
theorem B2748937 : Blo 1084620 2748937 := bstep (se 2 (by rfl) ⟨1030851, by rfl⟩ : syracuseStep 2748937 = 2061703) B2061703
theorem B3666491 : Blo 1084620 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B8811143 : Blo 1084620 8811143 := bstep (se 1 (by rfl) ⟨6608357, by rfl⟩ : syracuseStep 8811143 = 13216715) B13216715
theorem B4649683 : Blo 1084620 4649683 := bstep (se 1 (by rfl) ⟨3487262, by rfl⟩ : syracuseStep 4649683 = 6974525) B6974525
theorem B1831673 : Blo 1084620 1831673 := bstep (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) B1373755
theorem B5567305 : Blo 1084620 5567305 := bstep (se 2 (by rfl) ⟨2087739, by rfl⟩ : syracuseStep 5567305 = 4175479) B4175479
theorem B3666761 : Blo 1084620 3666761 := bstep (se 2 (by rfl) ⟨1375035, by rfl⟩ : syracuseStep 3666761 = 2750071) B2750071
theorem B2061217 : Blo 1084620 2061217 := bstep (se 2 (by rfl) ⟨772956, by rfl⟩ : syracuseStep 2061217 = 1545913) B1545913
theorem B1831855 : Blo 1084620 1831855 := bstep (se 1 (by rfl) ⟨1373891, by rfl⟩ : syracuseStep 1831855 = 2747783) B2747783
theorem B2094007 : Blo 1084620 2094007 := bstep (se 1 (by rfl) ⟨1570505, by rfl⟩ : syracuseStep 2094007 = 3141011) B3141011
theorem B24146909 : Blo 1084620 24146909 := bstep (se 3 (by rfl) ⟨4527545, by rfl⟩ : syracuseStep 24146909 = 9055091) B9055091
theorem B1831943 : Blo 1084620 1831943 := bstep (se 1 (by rfl) ⟨1373957, by rfl⟩ : syracuseStep 1831943 = 2747915) B2747915
theorem B2323475 : Blo 1084620 2323475 := bstep (se 1 (by rfl) ⟨1742606, by rfl⟩ : syracuseStep 2323475 = 3485213) B3485213
theorem B7435331 : Blo 1084620 7435331 := bstep (se 1 (by rfl) ⟨5576498, by rfl⟩ : syracuseStep 7435331 = 11152997) B11152997
theorem B4125775 : Blo 1084620 4125775 := bstep (se 1 (by rfl) ⟨3094331, by rfl⟩ : syracuseStep 4125775 = 6188663) B6188663
theorem B1832287 : Blo 1084620 1832287 := bstep (se 1 (by rfl) ⟨1374215, by rfl⟩ : syracuseStep 1832287 = 2748431) B2748431
theorem B3306881 : Blo 1084620 3306881 := bstep (se 2 (by rfl) ⟨1240080, by rfl⟩ : syracuseStep 3306881 = 2480161) B2480161
theorem B1832375 : Blo 1084620 1832375 := bstep (se 1 (by rfl) ⟨1374281, by rfl⟩ : syracuseStep 1832375 = 2748563) B2748563
theorem B2061787 : Blo 1084620 2061787 := bstep (se 1 (by rfl) ⟨1546340, by rfl⟩ : syracuseStep 2061787 = 3092681) B3092681
theorem B4126247 : Blo 1084620 4126247 := bstep (se 1 (by rfl) ⟨3094685, by rfl⟩ : syracuseStep 4126247 = 6189371) B6189371
theorem B5502653 : Blo 1084620 5502653 := bstep (se 3 (by rfl) ⟨1031747, by rfl⟩ : syracuseStep 5502653 = 2063495) B2063495
theorem B5502815 : Blo 1084620 5502815 := bstep (se 1 (by rfl) ⟨4127111, by rfl⟩ : syracuseStep 5502815 = 8254223) B8254223
theorem B3667895 : Blo 1084620 3667895 := bstep (se 1 (by rfl) ⟨2750921, by rfl⟩ : syracuseStep 3667895 = 5501843) B5501843
theorem B2750395 : Blo 1084620 2750395 := bstep (se 1 (by rfl) ⟨2062796, by rfl⟩ : syracuseStep 2750395 = 4125593) B4125593
theorem B1832969 : Blo 1084620 1832969 := bstep (se 2 (by rfl) ⟨687363, by rfl⟩ : syracuseStep 1832969 = 1374727) B1374727
theorem B8353849 : Blo 1084620 8353849 := bstep (se 2 (by rfl) ⟨3132693, by rfl⟩ : syracuseStep 8353849 = 6265387) B6265387
theorem B6191261 : Blo 1084620 6191261 := bstep (se 3 (by rfl) ⟨1160861, by rfl⟩ : syracuseStep 6191261 = 2321723) B2321723
theorem B1833131 : Blo 1084620 1833131 := bstep (se 1 (by rfl) ⟨1374848, by rfl⟩ : syracuseStep 1833131 = 2749697) B2749697
theorem B4127219 : Blo 1084620 4127219 := bstep (se 1 (by rfl) ⟨3095414, by rfl⟩ : syracuseStep 4127219 = 6190829) B6190829
theorem B3668489 : Blo 1084620 3668489 := bstep (se 2 (by rfl) ⟨1375683, by rfl⟩ : syracuseStep 3668489 = 2751367) B2751367
theorem B1833529 : Blo 1084620 1833529 := bstep (se 2 (by rfl) ⟨687573, by rfl⟩ : syracuseStep 1833529 = 1375147) B1375147
theorem B1833671 : Blo 1084620 1833671 := bstep (se 1 (by rfl) ⟨1375253, by rfl⟩ : syracuseStep 1833671 = 2750507) B2750507
theorem B2784095 : Blo 1084620 2784095 := bstep (se 1 (by rfl) ⟨2088071, by rfl⟩ : syracuseStep 2784095 = 4176143) B4176143
theorem B1833833 : Blo 1084620 1833833 := bstep (se 2 (by rfl) ⟨687687, by rfl⟩ : syracuseStep 1833833 = 1375375) B1375375
theorem B1834231 : Blo 1084620 1834231 := bstep (se 1 (by rfl) ⟨1375673, by rfl⟩ : syracuseStep 1834231 = 2751347) B2751347
theorem B3669353 : Blo 1084620 3669353 := bstep (se 2 (by rfl) ⟨1376007, by rfl⟩ : syracuseStep 3669353 = 2752015) B2752015
theorem B12385709 : Blo 1084620 12385709 := bstep (se 3 (by rfl) ⟨2322320, by rfl⟩ : syracuseStep 12385709 = 4644641) B4644641
theorem B1834427 : Blo 1084620 1834427 := bstep (se 1 (by rfl) ⟨1375820, by rfl⟩ : syracuseStep 1834427 = 2751641) B2751641
theorem B181140941 : Blo 1084620 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B1834535 : Blo 1084620 1834535 := bstep (se 1 (by rfl) ⟨1375901, by rfl⟩ : syracuseStep 1834535 = 2751803) B2751803
theorem B2063951 : Blo 1084620 2063951 := bstep (se 1 (by rfl) ⟨1547963, by rfl⟩ : syracuseStep 2063951 = 3095927) B3095927
theorem B1834825 : Blo 1084620 1834825 := bstep (se 2 (by rfl) ⟨688059, by rfl⟩ : syracuseStep 1834825 = 1376119) B1376119
theorem B1834859 : Blo 1084620 1834859 := bstep (se 1 (by rfl) ⟨1376144, by rfl⟩ : syracuseStep 1834859 = 2752289) B2752289
theorem B3669947 : Blo 1084620 3669947 := bstep (se 1 (by rfl) ⟨2752460, by rfl⟩ : syracuseStep 3669947 = 5504921) B5504921
theorem B5505083 : Blo 1084620 5505083 := bstep (se 1 (by rfl) ⟨4128812, by rfl⟩ : syracuseStep 5505083 = 8257625) B8257625
theorem B3670379 : Blo 1084620 3670379 := bstep (se 1 (by rfl) ⟨2752784, by rfl⟩ : syracuseStep 3670379 = 5505569) B5505569
theorem B3670649 : Blo 1084620 3670649 := bstep (se 2 (by rfl) ⟨1376493, by rfl⟩ : syracuseStep 3670649 = 2752987) B2752987
theorem B4129451 : Blo 1084620 4129451 := bstep (se 1 (by rfl) ⟨3097088, by rfl⟩ : syracuseStep 4129451 = 6194177) B6194177
theorem B1835743 : Blo 1084620 1835743 := bstep (se 1 (by rfl) ⟨1376807, by rfl⟩ : syracuseStep 1835743 = 2753615) B2753615
theorem B1737551 : Blo 1084620 1737551 := bstep (se 1 (by rfl) ⟨1303163, by rfl⟩ : syracuseStep 1737551 = 2606327) B2606327
theorem B2753423 : Blo 1084620 2753423 := bstep (se 1 (by rfl) ⟨2065067, by rfl⟩ : syracuseStep 2753423 = 4130135) B4130135
theorem B5506055 : Blo 1084620 5506055 := bstep (se 1 (by rfl) ⟨4129541, by rfl⟩ : syracuseStep 5506055 = 8259083) B8259083
theorem B8258597 : Blo 1084620 8258597 := bstep (se 4 (by rfl) ⟨774243, by rfl⟩ : syracuseStep 8258597 = 1548487) B1548487
theorem B1836175 : Blo 1084620 1836175 := bstep (se 1 (by rfl) ⟨1377131, by rfl⟩ : syracuseStep 1836175 = 2754263) B2754263
theorem B18580751 : Blo 1084620 18580751 := bstep (se 1 (by rfl) ⟨13935563, by rfl⟩ : syracuseStep 18580751 = 27871127) B27871127
theorem B1836425 : Blo 1084620 1836425 := bstep (se 2 (by rfl) ⟨688659, by rfl⟩ : syracuseStep 1836425 = 1377319) B1377319
theorem B5506541 : Blo 1084620 5506541 := bstep (se 3 (by rfl) ⟨1032476, by rfl⟩ : syracuseStep 5506541 = 2064953) B2064953
theorem B2786977 : Blo 1084620 2786977 := bstep (se 2 (by rfl) ⟨1045116, by rfl⟩ : syracuseStep 2786977 = 2090233) B2090233
theorem B2754283 : Blo 1084620 2754283 := bstep (se 1 (by rfl) ⟨2065712, by rfl⟩ : syracuseStep 2754283 = 4131425) B4131425
theorem B1836857 : Blo 1084620 1836857 := bstep (se 2 (by rfl) ⟨688821, by rfl⟩ : syracuseStep 1836857 = 1377643) B1377643
theorem B5212289 : Blo 1084620 5212289 := bstep (se 2 (by rfl) ⟨1954608, by rfl⟩ : syracuseStep 5212289 = 3909217) B3909217
theorem B5507351 : Blo 1084620 5507351 := bstep (se 1 (by rfl) ⟨4130513, by rfl⟩ : syracuseStep 5507351 = 8261027) B8261027
theorem B5212441 : Blo 1084620 5212441 := bstep (se 2 (by rfl) ⟨1954665, by rfl⟩ : syracuseStep 5212441 = 3909331) B3909331
theorem B3672431 : Blo 1084620 3672431 := bstep (se 1 (by rfl) ⟨2754323, by rfl⟩ : syracuseStep 3672431 = 5508647) B5508647
theorem B2755255 : Blo 1084620 2755255 := bstep (se 1 (by rfl) ⟨2066441, by rfl⟩ : syracuseStep 2755255 = 4132883) B4132883
theorem B10455979 : Blo 1084620 10455979 := bstep (se 1 (by rfl) ⟨7841984, by rfl⟩ : syracuseStep 10455979 = 15683969) B15683969
theorem B2755559 : Blo 1084620 2755559 := bstep (se 1 (by rfl) ⟨2066669, by rfl⟩ : syracuseStep 2755559 = 4133339) B4133339
theorem B12553217 : Blo 1084620 12553217 := bstep (se 2 (by rfl) ⟨4707456, by rfl⟩ : syracuseStep 12553217 = 9414913) B9414913
theorem B1084703 : Blo 1084620 1084703 := bstep (se 1 (by rfl) ⟨813527, by rfl⟩ : syracuseStep 1084703 = 1627055) B1627055
theorem B1084763 : Blo 1084620 1084763 := bstep (se 1 (by rfl) ⟨813572, by rfl⟩ : syracuseStep 1084763 = 1627145) B1627145
theorem B1084783 : Blo 1084620 1084783 := bstep (se 1 (by rfl) ⟨813587, by rfl⟩ : syracuseStep 1084783 = 1627175) B1627175
theorem B1084839 : Blo 1084620 1084839 := bstep (se 1 (by rfl) ⟨813629, by rfl⟩ : syracuseStep 1084839 = 1627259) B1627259
theorem B1084923 : Blo 1084620 1084923 := bstep (se 1 (by rfl) ⟨813692, by rfl⟩ : syracuseStep 1084923 = 1627385) B1627385
theorem B4132367 : Blo 1084620 4132367 := bstep (se 1 (by rfl) ⟨3099275, by rfl⟩ : syracuseStep 4132367 = 6198551) B6198551
theorem B1084991 : Blo 1084620 1084991 := bstep (se 1 (by rfl) ⟨813743, by rfl⟩ : syracuseStep 1084991 = 1627487) B1627487
theorem B1084999 : Blo 1084620 1084999 := bstep (se 1 (by rfl) ⟨813749, by rfl⟩ : syracuseStep 1084999 = 1627499) B1627499
theorem B1740383 : Blo 1084620 1740383 := bstep (se 1 (by rfl) ⟨1305287, by rfl⟩ : syracuseStep 1740383 = 2610575) B2610575
theorem B1085151 : Blo 1084620 1085151 := bstep (se 1 (by rfl) ⟨813863, by rfl⟩ : syracuseStep 1085151 = 1627727) B1627727
theorem B3673835 : Blo 1084620 3673835 := bstep (se 1 (by rfl) ⟨2755376, by rfl⟩ : syracuseStep 3673835 = 5510753) B5510753
theorem B1085231 : Blo 1084620 1085231 := bstep (se 1 (by rfl) ⟨813923, by rfl⟩ : syracuseStep 1085231 = 1627847) B1627847
theorem B5508971 : Blo 1084620 5508971 := bstep (se 1 (by rfl) ⟨4131728, by rfl⟩ : syracuseStep 5508971 = 8263457) B8263457
theorem B1085339 : Blo 1084620 1085339 := bstep (se 1 (by rfl) ⟨814004, by rfl⟩ : syracuseStep 1085339 = 1628009) B1628009
theorem B1085391 : Blo 1084620 1085391 := bstep (se 1 (by rfl) ⟨814043, by rfl⟩ : syracuseStep 1085391 = 1628087) B1628087
theorem B1085415 : Blo 1084620 1085415 := bstep (se 1 (by rfl) ⟨814061, by rfl⟩ : syracuseStep 1085415 = 1628123) B1628123
theorem B1118183 : Blo 1084620 1118183 := bstep (se 1 (by rfl) ⟨838637, by rfl⟩ : syracuseStep 1118183 = 1677275) B1677275
theorem B3477563 : Blo 1084620 3477563 := bstep (se 1 (by rfl) ⟨2608172, by rfl⟩ : syracuseStep 3477563 = 5216345) B5216345
theorem B11309327 : Blo 1084620 11309327 := bstep (se 1 (by rfl) ⟨8481995, by rfl⟩ : syracuseStep 11309327 = 16963991) B16963991
theorem B1085727 : Blo 1084620 1085727 := bstep (se 1 (by rfl) ⟨814295, by rfl⟩ : syracuseStep 1085727 = 1628591) B1628591
theorem B1085787 : Blo 1084620 1085787 := bstep (se 1 (by rfl) ⟨814340, by rfl⟩ : syracuseStep 1085787 = 1628681) B1628681
theorem B1085807 : Blo 1084620 1085807 := bstep (se 1 (by rfl) ⟨814355, by rfl⟩ : syracuseStep 1085807 = 1628711) B1628711
theorem B1085863 : Blo 1084620 1085863 := bstep (se 1 (by rfl) ⟨814397, by rfl⟩ : syracuseStep 1085863 = 1628795) B1628795
theorem B5214689 : Blo 1084620 5214689 := bstep (se 2 (by rfl) ⟨1955508, by rfl⟩ : syracuseStep 5214689 = 3911017) B3911017
theorem B1085947 : Blo 1084620 1085947 := bstep (se 1 (by rfl) ⟨814460, by rfl⟩ : syracuseStep 1085947 = 1628921) B1628921
theorem B1086015 : Blo 1084620 1086015 := bstep (se 1 (by rfl) ⟨814511, by rfl⟩ : syracuseStep 1086015 = 1629023) B1629023
theorem B1086023 : Blo 1084620 1086023 := bstep (se 1 (by rfl) ⟨814517, by rfl⟩ : syracuseStep 1086023 = 1629035) B1629035
theorem B1741433 : Blo 1084620 1741433 := bstep (se 2 (by rfl) ⟨653037, by rfl⟩ : syracuseStep 1741433 = 1306075) B1306075
theorem B1086175 : Blo 1084620 1086175 := bstep (se 1 (by rfl) ⟨814631, by rfl⟩ : syracuseStep 1086175 = 1629263) B1629263
theorem B1086255 : Blo 1084620 1086255 := bstep (se 1 (by rfl) ⟨814691, by rfl⟩ : syracuseStep 1086255 = 1629383) B1629383
theorem B1086363 : Blo 1084620 1086363 := bstep (se 1 (by rfl) ⟨814772, by rfl⟩ : syracuseStep 1086363 = 1629545) B1629545
theorem B1086415 : Blo 1084620 1086415 := bstep (se 1 (by rfl) ⟨814811, by rfl⟩ : syracuseStep 1086415 = 1629623) B1629623
theorem B1086439 : Blo 1084620 1086439 := bstep (se 1 (by rfl) ⟨814829, by rfl⟩ : syracuseStep 1086439 = 1629659) B1629659
theorem B9278621 : Blo 1084620 9278621 := bstep (se 3 (by rfl) ⟨1739741, by rfl⟩ : syracuseStep 9278621 = 3479483) B3479483
theorem B1086751 : Blo 1084620 1086751 := bstep (se 1 (by rfl) ⟨815063, by rfl⟩ : syracuseStep 1086751 = 1630127) B1630127
theorem B1086811 : Blo 1084620 1086811 := bstep (se 1 (by rfl) ⟨815108, by rfl⟩ : syracuseStep 1086811 = 1630217) B1630217
theorem B1086831 : Blo 1084620 1086831 := bstep (se 1 (by rfl) ⟨815123, by rfl⟩ : syracuseStep 1086831 = 1630247) B1630247
theorem B1086887 : Blo 1084620 1086887 := bstep (se 1 (by rfl) ⟨815165, by rfl⟩ : syracuseStep 1086887 = 1630331) B1630331
theorem B1086971 : Blo 1084620 1086971 := bstep (se 1 (by rfl) ⟨815228, by rfl⟩ : syracuseStep 1086971 = 1630457) B1630457
theorem B1087039 : Blo 1084620 1087039 := bstep (se 1 (by rfl) ⟨815279, by rfl⟩ : syracuseStep 1087039 = 1630559) B1630559
theorem B1087047 : Blo 1084620 1087047 := bstep (se 1 (by rfl) ⟨815285, by rfl⟩ : syracuseStep 1087047 = 1630571) B1630571
theorem B1087199 : Blo 1084620 1087199 := bstep (se 1 (by rfl) ⟨815399, by rfl⟩ : syracuseStep 1087199 = 1630799) B1630799
theorem B1087279 : Blo 1084620 1087279 := bstep (se 1 (by rfl) ⟨815459, by rfl⟩ : syracuseStep 1087279 = 1630919) B1630919
theorem B1087387 : Blo 1084620 1087387 := bstep (se 1 (by rfl) ⟨815540, by rfl⟩ : syracuseStep 1087387 = 1631081) B1631081
theorem B1087439 : Blo 1084620 1087439 := bstep (se 1 (by rfl) ⟨815579, by rfl⟩ : syracuseStep 1087439 = 1631159) B1631159
theorem B1087463 : Blo 1084620 1087463 := bstep (se 1 (by rfl) ⟨815597, by rfl⟩ : syracuseStep 1087463 = 1631195) B1631195
theorem B6199577 : Blo 1084620 6199577 := bstep (se 2 (by rfl) ⟨2324841, by rfl⟩ : syracuseStep 6199577 = 4649683) B4649683
theorem B1087775 : Blo 1084620 1087775 := bstep (se 1 (by rfl) ⟨815831, by rfl⟩ : syracuseStep 1087775 = 1631663) B1631663
theorem B1087835 : Blo 1084620 1087835 := bstep (se 1 (by rfl) ⟨815876, by rfl⟩ : syracuseStep 1087835 = 1631753) B1631753
theorem B1087855 : Blo 1084620 1087855 := bstep (se 1 (by rfl) ⟨815891, by rfl⟩ : syracuseStep 1087855 = 1631783) B1631783
theorem B2202023 : Blo 1084620 2202023 := bstep (se 1 (by rfl) ⟨1651517, by rfl⟩ : syracuseStep 2202023 = 3303035) B3303035
theorem B1087911 : Blo 1084620 1087911 := bstep (se 1 (by rfl) ⟨815933, by rfl⟩ : syracuseStep 1087911 = 1631867) B1631867
theorem B1087995 : Blo 1084620 1087995 := bstep (se 1 (by rfl) ⟨815996, by rfl⟩ : syracuseStep 1087995 = 1631993) B1631993
theorem B12392999 : Blo 1084620 12392999 := bstep (se 1 (by rfl) ⟨9294749, by rfl⟩ : syracuseStep 12392999 = 18589499) B18589499
theorem B1088063 : Blo 1084620 1088063 := bstep (se 1 (by rfl) ⟨816047, by rfl⟩ : syracuseStep 1088063 = 1632095) B1632095
theorem B1088071 : Blo 1084620 1088071 := bstep (se 1 (by rfl) ⟨816053, by rfl⟩ : syracuseStep 1088071 = 1632107) B1632107
theorem B2792009 : Blo 1084620 2792009 := bstep (se 2 (by rfl) ⟨1047003, by rfl⟩ : syracuseStep 2792009 = 2094007) B2094007
theorem B1743535 : Blo 1084620 1743535 := bstep (se 1 (by rfl) ⟨1307651, by rfl⟩ : syracuseStep 1743535 = 2615303) B2615303
theorem B1088223 : Blo 1084620 1088223 := bstep (se 1 (by rfl) ⟨816167, by rfl⟩ : syracuseStep 1088223 = 1632335) B1632335
theorem B8264429 : Blo 1084620 8264429 := bstep (se 3 (by rfl) ⟨1549580, by rfl⟩ : syracuseStep 8264429 = 3099161) B3099161
theorem B1088303 : Blo 1084620 1088303 := bstep (se 1 (by rfl) ⟨816227, by rfl⟩ : syracuseStep 1088303 = 1632455) B1632455
theorem B5217149 : Blo 1084620 5217149 := bstep (se 3 (by rfl) ⟨978215, by rfl⟩ : syracuseStep 5217149 = 1956431) B1956431
theorem B1088411 : Blo 1084620 1088411 := bstep (se 1 (by rfl) ⟨816308, by rfl⟩ : syracuseStep 1088411 = 1632617) B1632617
theorem B1088463 : Blo 1084620 1088463 := bstep (se 1 (by rfl) ⟨816347, by rfl⟩ : syracuseStep 1088463 = 1632695) B1632695
theorem B1088487 : Blo 1084620 1088487 := bstep (se 1 (by rfl) ⟨816365, by rfl⟩ : syracuseStep 1088487 = 1632731) B1632731
theorem B7445627 : Blo 1084620 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B93887909 : Blo 1084620 93887909 := bstep (se 4 (by rfl) ⟨8801991, by rfl⟩ : syracuseStep 93887909 = 17603983) B17603983
theorem B3481355 : Blo 1084620 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B1220431 : Blo 1084620 1220431 := bstep (se 1 (by rfl) ⟨915323, by rfl⟩ : syracuseStep 1220431 = 1830647) B1830647
theorem B8921297 : Blo 1084620 8921297 := bstep (se 2 (by rfl) ⟨3345486, by rfl⟩ : syracuseStep 8921297 = 6690973) B6690973
theorem B1220827 : Blo 1084620 1220827 := bstep (se 1 (by rfl) ⟨915620, by rfl⟩ : syracuseStep 1220827 = 1831241) B1831241
theorem B5874095 : Blo 1084620 5874095 := bstep (se 1 (by rfl) ⟨4405571, by rfl⟩ : syracuseStep 5874095 = 8811143) B8811143
theorem B1221115 : Blo 1084620 1221115 := bstep (se 1 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 1221115 = 1831673) B1831673
theorem B10429073 : Blo 1084620 10429073 := bstep (se 2 (by rfl) ⟨3910902, by rfl⟩ : syracuseStep 10429073 = 7821805) B7821805
theorem B16097939 : Blo 1084620 16097939 := bstep (se 1 (by rfl) ⟨12073454, by rfl⟩ : syracuseStep 16097939 = 24146909) B24146909
theorem B1221295 : Blo 1084620 1221295 := bstep (se 1 (by rfl) ⟨915971, by rfl⟩ : syracuseStep 1221295 = 1831943) B1831943
theorem B1548983 : Blo 1084620 1548983 := bstep (se 1 (by rfl) ⟨1161737, by rfl⟩ : syracuseStep 1548983 = 2323475) B2323475
theorem B9904841 : Blo 1084620 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B4956887 : Blo 1084620 4956887 := bstep (se 1 (by rfl) ⟨3717665, by rfl⟩ : syracuseStep 4956887 = 7435331) B7435331
theorem B2204587 : Blo 1084620 2204587 := bstep (se 1 (by rfl) ⟨1653440, by rfl⟩ : syracuseStep 2204587 = 3306881) B3306881
theorem B1221583 : Blo 1084620 1221583 := bstep (se 1 (by rfl) ⟨916187, by rfl⟩ : syracuseStep 1221583 = 1832375) B1832375
theorem B15672437 : Blo 1084620 15672437 := bstep (se 5 (by rfl) ⟨734645, by rfl⟩ : syracuseStep 15672437 = 1469291) B1469291
theorem B1221979 : Blo 1084620 1221979 := bstep (se 1 (by rfl) ⟨916484, by rfl⟩ : syracuseStep 1221979 = 1832969) B1832969
theorem B1222087 : Blo 1084620 1222087 := bstep (se 1 (by rfl) ⟨916565, by rfl⟩ : syracuseStep 1222087 = 1833131) B1833131
theorem B1222447 : Blo 1084620 1222447 := bstep (se 1 (by rfl) ⟨916835, by rfl⟩ : syracuseStep 1222447 = 1833671) B1833671
theorem B1222555 : Blo 1084620 1222555 := bstep (se 1 (by rfl) ⟨916916, by rfl⟩ : syracuseStep 1222555 = 1833833) B1833833
theorem B1222951 : Blo 1084620 1222951 := bstep (se 1 (by rfl) ⟨917213, by rfl⟩ : syracuseStep 1222951 = 1834427) B1834427
theorem B120760627 : Blo 1084620 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B1223023 : Blo 1084620 1223023 := bstep (se 1 (by rfl) ⟨917267, by rfl⟩ : syracuseStep 1223023 = 1834535) B1834535
theorem B1223239 : Blo 1084620 1223239 := bstep (se 1 (by rfl) ⟨917429, by rfl⟩ : syracuseStep 1223239 = 1834859) B1834859
theorem B3091051 : Blo 1084620 3091051 := bstep (se 1 (by rfl) ⟨2318288, by rfl⟩ : syracuseStep 3091051 = 4636577) B4636577
theorem B3484559 : Blo 1084620 3484559 := bstep (se 1 (by rfl) ⟨2613419, by rfl⟩ : syracuseStep 3484559 = 5226839) B5226839
theorem B3484711 : Blo 1084620 3484711 := bstep (se 1 (by rfl) ⟨2613533, by rfl⟩ : syracuseStep 3484711 = 5227067) B5227067
theorem B22916449 : Blo 1084620 22916449 := bstep (se 2 (by rfl) ⟨8593668, by rfl⟩ : syracuseStep 22916449 = 17187337) B17187337
theorem B1224103 : Blo 1084620 1224103 := bstep (se 1 (by rfl) ⟨918077, by rfl⟩ : syracuseStep 1224103 = 1836155) B1836155
theorem B14855669 : Blo 1084620 14855669 := bstep (se 5 (by rfl) ⟨696359, by rfl⟩ : syracuseStep 14855669 = 1392719) B1392719
theorem B13938641 : Blo 1084620 13938641 := bstep (se 2 (by rfl) ⟨5226990, by rfl⟩ : syracuseStep 13938641 = 10453981) B10453981
theorem B1224679 : Blo 1084620 1224679 := bstep (se 1 (by rfl) ⟨918509, by rfl⟩ : syracuseStep 1224679 = 1837019) B1837019
theorem B6959171 : Blo 1084620 6959171 := bstep (se 1 (by rfl) ⟨5219378, by rfl⟩ : syracuseStep 6959171 = 10438757) B10438757
theorem B4698593 : Blo 1084620 4698593 := bstep (se 2 (by rfl) ⟨1761972, by rfl⟩ : syracuseStep 4698593 = 3523945) B3523945
theorem B3093011 : Blo 1084620 3093011 := bstep (se 1 (by rfl) ⟨2319758, by rfl⟩ : syracuseStep 3093011 = 4639517) B4639517
theorem B5878291 : Blo 1084620 5878291 := bstep (se 1 (by rfl) ⟨4408718, by rfl⟩ : syracuseStep 5878291 = 8817437) B8817437
theorem B10433069 : Blo 1084620 10433069 := bstep (se 3 (by rfl) ⟨1956200, by rfl⟩ : syracuseStep 10433069 = 3912401) B3912401
theorem B4633843 : Blo 1084620 4633843 := bstep (se 1 (by rfl) ⟨3475382, by rfl⟩ : syracuseStep 4633843 = 6950765) B6950765
theorem B6600503 : Blo 1084620 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B48215969 : Blo 1084620 48215969 := bstep (se 2 (by rfl) ⟨18080988, by rfl⟩ : syracuseStep 48215969 = 36161977) B36161977
theorem B10435067 : Blo 1084620 10435067 := bstep (se 1 (by rfl) ⟨7826300, by rfl⟩ : syracuseStep 10435067 = 15652601) B15652601
theorem B10598951 : Blo 1084620 10598951 := bstep (se 1 (by rfl) ⟨7949213, by rfl⟩ : syracuseStep 10598951 = 15898427) B15898427
theorem B3914303 : Blo 1084620 3914303 := bstep (se 1 (by rfl) ⟨2935727, by rfl⟩ : syracuseStep 3914303 = 5871455) B5871455
theorem B1653355 : Blo 1084620 1653355 := bstep (se 1 (by rfl) ⟨1240016, by rfl⟩ : syracuseStep 1653355 = 2480033) B2480033
theorem B1162459 : Blo 1084620 1162459 := bstep (se 1 (by rfl) ⟨871844, by rfl⟩ : syracuseStep 1162459 = 1743689) B1743689
theorem B3095995 : Blo 1084620 3095995 := bstep (se 1 (by rfl) ⟨2321996, by rfl⟩ : syracuseStep 3095995 = 4643993) B4643993
theorem B2440799 : Blo 1084620 2440799 := bstep (se 1 (by rfl) ⟨1830599, by rfl⟩ : syracuseStep 2440799 = 3661199) B3661199
theorem B2932487 : Blo 1084620 2932487 := bstep (se 1 (by rfl) ⟨2199365, by rfl⟩ : syracuseStep 2932487 = 4398731) B4398731
theorem B12369671 : Blo 1084620 12369671 := bstep (se 1 (by rfl) ⟨9277253, by rfl⟩ : syracuseStep 12369671 = 18554507) B18554507
theorem B2441015 : Blo 1084620 2441015 := bstep (se 1 (by rfl) ⟨1830761, by rfl⟩ : syracuseStep 2441015 = 3661523) B3661523
theorem B11321147 : Blo 1084620 11321147 := bstep (se 1 (by rfl) ⟨8490860, by rfl⟩ : syracuseStep 11321147 = 16981721) B16981721
theorem B3522619 : Blo 1084620 3522619 := bstep (se 1 (by rfl) ⟨2641964, by rfl⟩ : syracuseStep 3522619 = 5283929) B5283929
theorem B2441321 : Blo 1084620 2441321 := bstep (se 2 (by rfl) ⟨915495, by rfl⟩ : syracuseStep 2441321 = 1830991) B1830991
theorem B2933243 : Blo 1084620 2933243 := bstep (se 1 (by rfl) ⟨2199932, by rfl⟩ : syracuseStep 2933243 = 4399865) B4399865
theorem B2441807 : Blo 1084620 2441807 := bstep (se 1 (by rfl) ⟨1831355, by rfl⟩ : syracuseStep 2441807 = 3662711) B3662711
theorem B3097271 : Blo 1084620 3097271 := bstep (se 1 (by rfl) ⟨2322953, by rfl⟩ : syracuseStep 3097271 = 4645907) B4645907
theorem B2441951 : Blo 1084620 2441951 := bstep (se 1 (by rfl) ⟨1831463, by rfl⟩ : syracuseStep 2441951 = 3662927) B3662927
theorem B4637519 : Blo 1084620 4637519 := bstep (se 1 (by rfl) ⟨3478139, by rfl⟩ : syracuseStep 4637519 = 6956279) B6956279
theorem B2442203 : Blo 1084620 2442203 := bstep (se 1 (by rfl) ⟨1831652, by rfl⟩ : syracuseStep 2442203 = 3663305) B3663305
theorem B7423073 : Blo 1084620 7423073 := bstep (se 2 (by rfl) ⟨2783652, by rfl⟩ : syracuseStep 7423073 = 5567305) B5567305
theorem B2442383 : Blo 1084620 2442383 := bstep (se 1 (by rfl) ⟨1831787, by rfl⟩ : syracuseStep 2442383 = 3663575) B3663575
theorem B4637843 : Blo 1084620 4637843 := bstep (se 1 (by rfl) ⟨3478382, by rfl⟩ : syracuseStep 4637843 = 6956765) B6956765
theorem B2442473 : Blo 1084620 2442473 := bstep (se 2 (by rfl) ⟨915927, by rfl⟩ : syracuseStep 2442473 = 1831855) B1831855
theorem B2442527 : Blo 1084620 2442527 := bstep (se 1 (by rfl) ⟨1831895, by rfl⟩ : syracuseStep 2442527 = 3663791) B3663791
theorem B4408685 : Blo 1084620 4408685 := bstep (se 3 (by rfl) ⟨826628, by rfl⟩ : syracuseStep 4408685 = 1653257) B1653257
theorem B2443049 : Blo 1084620 2443049 := bstep (se 2 (by rfl) ⟨916143, by rfl⟩ : syracuseStep 2443049 = 1832287) B1832287
theorem B18532637 : Blo 1084620 18532637 := bstep (se 3 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 18532637 = 6949739) B6949739
theorem B4639295 : Blo 1084620 4639295 := bstep (se 1 (by rfl) ⟨3479471, by rfl⟩ : syracuseStep 4639295 = 6958943) B6958943
theorem B5491475 : Blo 1084620 5491475 := bstep (se 1 (by rfl) ⟨4118606, by rfl⟩ : syracuseStep 5491475 = 8237213) B8237213
theorem B2444111 : Blo 1084620 2444111 := bstep (se 1 (by rfl) ⟨1833083, by rfl⟩ : syracuseStep 2444111 = 3666167) B3666167
theorem B79350785 : Blo 1084620 79350785 := bstep (se 2 (by rfl) ⟨29756544, by rfl⟩ : syracuseStep 79350785 = 59513089) B59513089
theorem B2444327 : Blo 1084620 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B5229683 : Blo 1084620 5229683 := bstep (se 1 (by rfl) ⟨3922262, by rfl⟩ : syracuseStep 5229683 = 7844525) B7844525
theorem B2444507 : Blo 1084620 2444507 := bstep (se 1 (by rfl) ⟨1833380, by rfl⟩ : syracuseStep 2444507 = 3666761) B3666761
theorem B2444705 : Blo 1084620 2444705 := bstep (se 2 (by rfl) ⟨916764, by rfl⟩ : syracuseStep 2444705 = 1833529) B1833529
theorem B2936681 : Blo 1084620 2936681 := bstep (se 2 (by rfl) ⟨1101255, by rfl⟩ : syracuseStep 2936681 = 2202511) B2202511
theorem B5492609 : Blo 1084620 5492609 := bstep (se 2 (by rfl) ⟨2059728, by rfl⟩ : syracuseStep 5492609 = 4119457) B4119457
theorem B2445263 : Blo 1084620 2445263 := bstep (se 1 (by rfl) ⟨1833947, by rfl⟩ : syracuseStep 2445263 = 3667895) B3667895
theorem B5361665 : Blo 1084620 5361665 := bstep (se 2 (by rfl) ⟨2010624, by rfl⟩ : syracuseStep 5361665 = 4021249) B4021249
theorem B2445641 : Blo 1084620 2445641 := bstep (se 2 (by rfl) ⟨917115, by rfl⟩ : syracuseStep 2445641 = 1834231) B1834231
theorem B2445659 : Blo 1084620 2445659 := bstep (se 1 (by rfl) ⟨1834244, by rfl⟩ : syracuseStep 2445659 = 3668489) B3668489
theorem B2609633 : Blo 1084620 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B1856063 : Blo 1084620 1856063 := bstep (se 1 (by rfl) ⟨1392047, by rfl⟩ : syracuseStep 1856063 = 2784095) B2784095
theorem B5493419 : Blo 1084620 5493419 := bstep (se 1 (by rfl) ⟨4120064, by rfl⟩ : syracuseStep 5493419 = 8240129) B8240129
theorem B2609911 : Blo 1084620 2609911 := bstep (se 1 (by rfl) ⟨1957433, by rfl⟩ : syracuseStep 2609911 = 3914867) B3914867
theorem B1626959 : Blo 1084620 1626959 := bstep (se 1 (by rfl) ⟨1220219, by rfl⟩ : syracuseStep 1626959 = 2440439) B2440439
theorem B2446235 : Blo 1084620 2446235 := bstep (se 1 (by rfl) ⟨1834676, by rfl⟩ : syracuseStep 2446235 = 3669353) B3669353
theorem B16962509 : Blo 1084620 16962509 := bstep (se 3 (by rfl) ⟨3180470, by rfl⟩ : syracuseStep 16962509 = 6360941) B6360941
theorem B2446433 : Blo 1084620 2446433 := bstep (se 2 (by rfl) ⟨917412, by rfl⟩ : syracuseStep 2446433 = 1834825) B1834825
theorem B5493905 : Blo 1084620 5493905 := bstep (se 2 (by rfl) ⟨2060214, by rfl⟩ : syracuseStep 5493905 = 4120429) B4120429
theorem B1627355 : Blo 1084620 1627355 := bstep (se 1 (by rfl) ⟨1220516, by rfl⟩ : syracuseStep 1627355 = 2441033) B2441033
theorem B2446631 : Blo 1084620 2446631 := bstep (se 1 (by rfl) ⟨1834973, by rfl⟩ : syracuseStep 2446631 = 3669947) B3669947
theorem B1627529 : Blo 1084620 1627529 := bstep (se 2 (by rfl) ⟨610323, by rfl⟩ : syracuseStep 1627529 = 1220647) B1220647
theorem B2447009 : Blo 1084620 2447009 := bstep (se 2 (by rfl) ⟨917628, by rfl⟩ : syracuseStep 2447009 = 1835257) B1835257
theorem B1627883 : Blo 1084620 1627883 := bstep (se 1 (by rfl) ⟨1220912, by rfl⟩ : syracuseStep 1627883 = 2441825) B2441825
theorem B2611073 : Blo 1084620 2611073 := bstep (se 2 (by rfl) ⟨979152, by rfl⟩ : syracuseStep 2611073 = 1958305) B1958305
theorem B1628111 : Blo 1084620 1628111 := bstep (se 1 (by rfl) ⟨1221083, by rfl⟩ : syracuseStep 1628111 = 2442167) B2442167
theorem B2447369 : Blo 1084620 2447369 := bstep (se 2 (by rfl) ⟨917763, by rfl⟩ : syracuseStep 2447369 = 1835527) B1835527
theorem B1628507 : Blo 1084620 1628507 := bstep (se 1 (by rfl) ⟨1221380, by rfl⟩ : syracuseStep 1628507 = 2442761) B2442761
theorem B2447783 : Blo 1084620 2447783 := bstep (se 1 (by rfl) ⟨1835837, by rfl⟩ : syracuseStep 2447783 = 3671675) B3671675
theorem B2447891 : Blo 1084620 2447891 := bstep (se 1 (by rfl) ⟨1835918, by rfl⟩ : syracuseStep 2447891 = 3671837) B3671837
theorem B1628735 : Blo 1084620 1628735 := bstep (se 1 (by rfl) ⟨1221551, by rfl⟩ : syracuseStep 1628735 = 2443103) B2443103
theorem B2447945 : Blo 1084620 2447945 := bstep (se 2 (by rfl) ⟨917979, by rfl⟩ : syracuseStep 2447945 = 1835959) B1835959
theorem B10050155 : Blo 1084620 10050155 := bstep (se 1 (by rfl) ⟨7537616, by rfl⟩ : syracuseStep 10050155 = 15075233) B15075233
theorem B3922607 : Blo 1084620 3922607 := bstep (se 1 (by rfl) ⟨2941955, by rfl⟩ : syracuseStep 3922607 = 5883911) B5883911
theorem B1628855 : Blo 1084620 1628855 := bstep (se 1 (by rfl) ⟨1221641, by rfl⟩ : syracuseStep 1628855 = 2443283) B2443283
theorem B1629083 : Blo 1084620 1629083 := bstep (se 1 (by rfl) ⟨1221812, by rfl⟩ : syracuseStep 1629083 = 2443625) B2443625
theorem B5659579 : Blo 1084620 5659579 := bstep (se 1 (by rfl) ⟨4244684, by rfl⟩ : syracuseStep 5659579 = 8489369) B8489369
theorem B2448359 : Blo 1084620 2448359 := bstep (se 1 (by rfl) ⟨1836269, by rfl⟩ : syracuseStep 2448359 = 3672539) B3672539
theorem B24108299 : Blo 1084620 24108299 := bstep (se 1 (by rfl) ⟨18081224, by rfl⟩ : syracuseStep 24108299 = 36162449) B36162449
theorem B1629479 : Blo 1084620 1629479 := bstep (se 1 (by rfl) ⟨1222109, by rfl⟩ : syracuseStep 1629479 = 2444219) B2444219
theorem B2448737 : Blo 1084620 2448737 := bstep (se 2 (by rfl) ⟨918276, by rfl⟩ : syracuseStep 2448737 = 1836553) B1836553
theorem B1629563 : Blo 1084620 1629563 := bstep (se 1 (by rfl) ⟨1222172, by rfl⟩ : syracuseStep 1629563 = 2444345) B2444345
theorem B2448827 : Blo 1084620 2448827 := bstep (se 1 (by rfl) ⟨1836620, by rfl⟩ : syracuseStep 2448827 = 3673241) B3673241
theorem B1629689 : Blo 1084620 1629689 := bstep (se 2 (by rfl) ⟨611133, by rfl⟩ : syracuseStep 1629689 = 1222267) B1222267
theorem B5496335 : Blo 1084620 5496335 := bstep (se 1 (by rfl) ⟨4122251, by rfl⟩ : syracuseStep 5496335 = 8244503) B8244503
theorem B6610447 : Blo 1084620 6610447 := bstep (se 1 (by rfl) ⟨4957835, by rfl⟩ : syracuseStep 6610447 = 9915671) B9915671
theorem B2448953 : Blo 1084620 2448953 := bstep (se 2 (by rfl) ⟨918357, by rfl⟩ : syracuseStep 2448953 = 1836715) B1836715
theorem B6970961 : Blo 1084620 6970961 := bstep (se 2 (by rfl) ⟨2614110, by rfl⟩ : syracuseStep 6970961 = 5228221) B5228221
theorem B11296351 : Blo 1084620 11296351 := bstep (se 1 (by rfl) ⟨8472263, by rfl⟩ : syracuseStep 11296351 = 16944527) B16944527
theorem B1629791 : Blo 1084620 1629791 := bstep (se 1 (by rfl) ⟨1222343, by rfl⟩ : syracuseStep 1629791 = 2444687) B2444687
theorem B6184745 : Blo 1084620 6184745 := bstep (se 2 (by rfl) ⟨2319279, by rfl⟩ : syracuseStep 6184745 = 4638559) B4638559
theorem B1630007 : Blo 1084620 1630007 := bstep (se 1 (by rfl) ⟨1222505, by rfl⟩ : syracuseStep 1630007 = 2445011) B2445011
theorem B8249363 : Blo 1084620 8249363 := bstep (se 1 (by rfl) ⟨6187022, by rfl⟩ : syracuseStep 8249363 = 12374045) B12374045
theorem B1630313 : Blo 1084620 1630313 := bstep (se 2 (by rfl) ⟨611367, by rfl⟩ : syracuseStep 1630313 = 1222735) B1222735
theorem B2318665 : Blo 1084620 2318665 := bstep (se 2 (by rfl) ⟨869499, by rfl⟩ : syracuseStep 2318665 = 1738999) B1738999
theorem B3662171 : Blo 1084620 3662171 := bstep (se 1 (by rfl) ⟨2746628, by rfl⟩ : syracuseStep 3662171 = 5493257) B5493257
theorem B2384219 : Blo 1084620 2384219 := bstep (se 1 (by rfl) ⟨1788164, by rfl⟩ : syracuseStep 2384219 = 3576329) B3576329
theorem B2318699 : Blo 1084620 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B1630631 : Blo 1084620 1630631 := bstep (se 1 (by rfl) ⟨1222973, by rfl⟩ : syracuseStep 1630631 = 2445947) B2445947
theorem B5497307 : Blo 1084620 5497307 := bstep (se 1 (by rfl) ⟨4122980, by rfl⟩ : syracuseStep 5497307 = 8245961) B8245961
theorem B1630715 : Blo 1084620 1630715 := bstep (se 1 (by rfl) ⟨1223036, by rfl⟩ : syracuseStep 1630715 = 2446073) B2446073
theorem B23814661 : Blo 1084620 23814661 := bstep (se 4 (by rfl) ⟨2232624, by rfl⟩ : syracuseStep 23814661 = 4465249) B4465249
theorem B1860169 : Blo 1084620 1860169 := bstep (se 2 (by rfl) ⟨697563, by rfl⟩ : syracuseStep 1860169 = 1395127) B1395127
theorem B1630841 : Blo 1084620 1630841 := bstep (se 2 (by rfl) ⟨611565, by rfl⟩ : syracuseStep 1630841 = 1223131) B1223131
theorem B9298577 : Blo 1084620 9298577 := bstep (se 2 (by rfl) ⟨3486966, by rfl⟩ : syracuseStep 9298577 = 6973933) B6973933
theorem B1630895 : Blo 1084620 1630895 := bstep (se 1 (by rfl) ⟨1223171, by rfl⟩ : syracuseStep 1630895 = 2446343) B2446343
theorem B1630943 : Blo 1084620 1630943 := bstep (se 1 (by rfl) ⟨1223207, by rfl⟩ : syracuseStep 1630943 = 2446415) B2446415
theorem B1467215 : Blo 1084620 1467215 := bstep (se 1 (by rfl) ⟨1100411, by rfl⟩ : syracuseStep 1467215 = 2200823) B2200823
theorem B5497793 : Blo 1084620 5497793 := bstep (se 2 (by rfl) ⟨2061672, by rfl⟩ : syracuseStep 5497793 = 4123345) B4123345
theorem B1631207 : Blo 1084620 1631207 := bstep (se 1 (by rfl) ⟨1223405, by rfl⟩ : syracuseStep 1631207 = 2446811) B2446811
theorem B9266183 : Blo 1084620 9266183 := bstep (se 1 (by rfl) ⟨6949637, by rfl⟩ : syracuseStep 9266183 = 13899275) B13899275
theorem B10445831 : Blo 1084620 10445831 := bstep (se 1 (by rfl) ⟨7834373, by rfl⟩ : syracuseStep 10445831 = 15668747) B15668747
theorem B1631465 : Blo 1084620 1631465 := bstep (se 2 (by rfl) ⟨611799, by rfl⟩ : syracuseStep 1631465 = 1223599) B1223599
theorem B1631519 : Blo 1084620 1631519 := bstep (se 1 (by rfl) ⟨1223639, by rfl⟩ : syracuseStep 1631519 = 2447279) B2447279
theorem B3663143 : Blo 1084620 3663143 := bstep (se 1 (by rfl) ⟨2747357, by rfl⟩ : syracuseStep 3663143 = 5494715) B5494715
theorem B2745697 : Blo 1084620 2745697 := bstep (se 2 (by rfl) ⟨1029636, by rfl⟩ : syracuseStep 2745697 = 2059273) B2059273
theorem B4646267 : Blo 1084620 4646267 := bstep (se 1 (by rfl) ⟨3484700, by rfl⟩ : syracuseStep 4646267 = 6969401) B6969401
theorem B1631687 : Blo 1084620 1631687 := bstep (se 1 (by rfl) ⟨1223765, by rfl⟩ : syracuseStep 1631687 = 2447531) B2447531
theorem B2319929 : Blo 1084620 2319929 := bstep (se 2 (by rfl) ⟨869973, by rfl⟩ : syracuseStep 2319929 = 1739947) B1739947
theorem B8054329 : Blo 1084620 8054329 := bstep (se 2 (by rfl) ⟨3020373, by rfl⟩ : syracuseStep 8054329 = 6040747) B6040747
theorem B1632041 : Blo 1084620 1632041 := bstep (se 2 (by rfl) ⟨612015, by rfl⟩ : syracuseStep 1632041 = 1224031) B1224031
theorem B1632047 : Blo 1084620 1632047 := bstep (se 1 (by rfl) ⟨1224035, by rfl⟩ : syracuseStep 1632047 = 2448071) B2448071
theorem B9922385 : Blo 1084620 9922385 := bstep (se 2 (by rfl) ⟨3720894, by rfl⟩ : syracuseStep 9922385 = 7441789) B7441789
theorem B3664007 : Blo 1084620 3664007 := bstep (se 1 (by rfl) ⟨2748005, by rfl⟩ : syracuseStep 3664007 = 5496011) B5496011
theorem B1632521 : Blo 1084620 1632521 := bstep (se 2 (by rfl) ⟨612195, by rfl⟩ : syracuseStep 1632521 = 1224391) B1224391
theorem B2746649 : Blo 1084620 2746649 := bstep (se 2 (by rfl) ⟨1029993, by rfl⟩ : syracuseStep 2746649 = 2059987) B2059987
theorem B1632623 : Blo 1084620 1632623 := bstep (se 1 (by rfl) ⟨1224467, by rfl⟩ : syracuseStep 1632623 = 2448935) B2448935
theorem B1468795 : Blo 1084620 1468795 := bstep (se 1 (by rfl) ⟨1101596, by rfl⟩ : syracuseStep 1468795 = 2203193) B2203193
theorem B2746943 : Blo 1084620 2746943 := bstep (se 1 (by rfl) ⟨2060207, by rfl⟩ : syracuseStep 2746943 = 4120415) B4120415
theorem B1632839 : Blo 1084620 1632839 := bstep (se 1 (by rfl) ⟨1224629, by rfl⟩ : syracuseStep 1632839 = 2449259) B2449259
theorem B2976335 : Blo 1084620 2976335 := bstep (se 1 (by rfl) ⟨2232251, by rfl⟩ : syracuseStep 2976335 = 4464503) B4464503
theorem B1763947 : Blo 1084620 1763947 := bstep (se 1 (by rfl) ⟨1322960, by rfl⟩ : syracuseStep 1763947 = 2645921) B2645921
theorem B1632875 : Blo 1084620 1632875 := bstep (se 1 (by rfl) ⟨1224656, by rfl⟩ : syracuseStep 1632875 = 2449313) B2449313
theorem B4123331 : Blo 1084620 4123331 := bstep (se 1 (by rfl) ⟨3092498, by rfl⟩ : syracuseStep 4123331 = 6184997) B6184997
theorem B12544723 : Blo 1084620 12544723 := bstep (se 1 (by rfl) ⟨9408542, by rfl⟩ : syracuseStep 12544723 = 18817085) B18817085
theorem B9267959 : Blo 1084620 9267959 := bstep (se 1 (by rfl) ⟨6950969, by rfl⟩ : syracuseStep 9267959 = 13901939) B13901939
theorem B2747155 : Blo 1084620 2747155 := bstep (se 1 (by rfl) ⟨2060366, by rfl⟩ : syracuseStep 2747155 = 4120733) B4120733
theorem B1305499 : Blo 1084620 1305499 := bstep (se 1 (by rfl) ⟨979124, by rfl⟩ : syracuseStep 1305499 = 1958249) B1958249
theorem B2321399 : Blo 1084620 2321399 := bstep (se 1 (by rfl) ⟨1741049, by rfl⟩ : syracuseStep 2321399 = 3482099) B3482099
theorem B2747591 : Blo 1084620 2747591 := bstep (se 1 (by rfl) ⟨2060693, by rfl⟩ : syracuseStep 2747591 = 4121387) B4121387
theorem B2747641 : Blo 1084620 2747641 := bstep (se 2 (by rfl) ⟨1030365, by rfl⟩ : syracuseStep 2747641 = 2060731) B2060731
theorem B169667905 : Blo 1084620 169667905 := bstep (se 2 (by rfl) ⟨63625464, by rfl⟩ : syracuseStep 169667905 = 127250929) B127250929
theorem B3665249 : Blo 1084620 3665249 := bstep (se 2 (by rfl) ⟨1374468, by rfl⟩ : syracuseStep 3665249 = 2748937) B2748937
theorem B5565833 : Blo 1084620 5565833 := bstep (se 2 (by rfl) ⟨2087187, by rfl⟩ : syracuseStep 5565833 = 4174375) B4174375
theorem B1830343 : Blo 1084620 1830343 := bstep (se 1 (by rfl) ⟨1372757, by rfl⟩ : syracuseStep 1830343 = 2745515) B2745515
theorem B2748289 : Blo 1084620 2748289 := bstep (se 2 (by rfl) ⟨1030608, by rfl⟩ : syracuseStep 2748289 = 2061217) B2061217
theorem B1830863 : Blo 1084620 1830863 := bstep (se 1 (by rfl) ⟨1373147, by rfl⟩ : syracuseStep 1830863 = 2746295) B2746295
theorem B7827515 : Blo 1084620 7827515 := bstep (se 1 (by rfl) ⟨5870636, by rfl⟩ : syracuseStep 7827515 = 11741273) B11741273
theorem B5501033 : Blo 1084620 5501033 := bstep (se 2 (by rfl) ⟨2062887, by rfl⟩ : syracuseStep 5501033 = 4125775) B4125775
theorem B2322697 : Blo 1084620 2322697 := bstep (se 2 (by rfl) ⟨871011, by rfl⟩ : syracuseStep 2322697 = 1742023) B1742023
theorem B2355731 : Blo 1084620 2355731 := bstep (se 1 (by rfl) ⟨1766798, by rfl⟩ : syracuseStep 2355731 = 3533597) B3533597
theorem B1831531 : Blo 1084620 1831531 := bstep (se 1 (by rfl) ⟨1373648, by rfl⟩ : syracuseStep 1831531 = 2747297) B2747297
theorem B2749049 : Blo 1084620 2749049 := bstep (se 2 (by rfl) ⟨1030893, by rfl⟩ : syracuseStep 2749049 = 2061787) B2061787
theorem B2749099 : Blo 1084620 2749099 := bstep (se 1 (by rfl) ⟨2061824, by rfl⟩ : syracuseStep 2749099 = 4123649) B4123649
theorem B2355895 : Blo 1084620 2355895 := bstep (se 1 (by rfl) ⟨1766921, by rfl⟩ : syracuseStep 2355895 = 3533843) B3533843
theorem B1831835 : Blo 1084620 1831835 := bstep (se 1 (by rfl) ⟨1373876, by rfl⟩ : syracuseStep 1831835 = 2747753) B2747753
theorem B2749403 : Blo 1084620 2749403 := bstep (se 1 (by rfl) ⟨2062052, by rfl⟩ : syracuseStep 2749403 = 4124105) B4124105
theorem B5567633 : Blo 1084620 5567633 := bstep (se 2 (by rfl) ⟨2087862, by rfl⟩ : syracuseStep 5567633 = 4175725) B4175725
theorem B8811665 : Blo 1084620 8811665 := bstep (se 2 (by rfl) ⟨3304374, by rfl⟩ : syracuseStep 8811665 = 6608749) B6608749
theorem B5502167 : Blo 1084620 5502167 := bstep (se 1 (by rfl) ⟨4126625, by rfl⟩ : syracuseStep 5502167 = 8253251) B8253251
theorem B3667193 : Blo 1084620 3667193 := bstep (se 2 (by rfl) ⟨1375197, by rfl⟩ : syracuseStep 3667193 = 2750395) B2750395
theorem B2749727 : Blo 1084620 2749727 := bstep (se 1 (by rfl) ⟨2062295, by rfl⟩ : syracuseStep 2749727 = 4124591) B4124591
theorem B11138465 : Blo 1084620 11138465 := bstep (se 2 (by rfl) ⟨4176924, by rfl⟩ : syracuseStep 11138465 = 8353849) B8353849
theorem B3667463 : Blo 1084620 3667463 := bstep (se 1 (by rfl) ⟨2750597, by rfl⟩ : syracuseStep 3667463 = 5501195) B5501195
theorem B11761595 : Blo 1084620 11761595 := bstep (se 1 (by rfl) ⟨8821196, by rfl⟩ : syracuseStep 11761595 = 17642393) B17642393
theorem B2750831 : Blo 1084620 2750831 := bstep (se 1 (by rfl) ⟨2063123, by rfl⟩ : syracuseStep 2750831 = 4126247) B4126247
theorem B2062759 : Blo 1084620 2062759 := bstep (se 1 (by rfl) ⟨1547069, by rfl⟩ : syracuseStep 2062759 = 3094139) B3094139
theorem B3668435 : Blo 1084620 3668435 := bstep (se 1 (by rfl) ⟨2751326, by rfl⟩ : syracuseStep 3668435 = 5502653) B5502653
theorem B3668543 : Blo 1084620 3668543 := bstep (se 1 (by rfl) ⟨2751407, by rfl⟩ : syracuseStep 3668543 = 5502815) B5502815
theorem B4127507 : Blo 1084620 4127507 := bstep (se 1 (by rfl) ⟨3095630, by rfl⟩ : syracuseStep 4127507 = 6191261) B6191261
theorem B2751479 : Blo 1084620 2751479 := bstep (se 1 (by rfl) ⟨2063609, by rfl⟩ : syracuseStep 2751479 = 4127219) B4127219
theorem B2063647 : Blo 1084620 2063647 := bstep (se 1 (by rfl) ⟨1547735, by rfl⟩ : syracuseStep 2063647 = 3095471) B3095471
theorem B1342759 : Blo 1084620 1342759 := bstep (se 1 (by rfl) ⟨1007069, by rfl⟩ : syracuseStep 1342759 = 2014139) B2014139
theorem B10452563 : Blo 1084620 10452563 := bstep (se 1 (by rfl) ⟨7839422, by rfl⟩ : syracuseStep 10452563 = 15678845) B15678845
theorem B8257139 : Blo 1084620 8257139 := bstep (se 1 (by rfl) ⟨6192854, by rfl⟩ : syracuseStep 8257139 = 12385709) B12385709
theorem B1375967 : Blo 1084620 1375967 := bstep (se 1 (by rfl) ⟨1031975, by rfl⟩ : syracuseStep 1375967 = 2063951) B2063951
theorem B5865227 : Blo 1084620 5865227 := bstep (se 1 (by rfl) ⟨4398920, by rfl⟩ : syracuseStep 5865227 = 8797841) B8797841
theorem B3670055 : Blo 1084620 3670055 := bstep (se 1 (by rfl) ⟨2752541, by rfl⟩ : syracuseStep 3670055 = 5505083) B5505083
theorem B2752967 : Blo 1084620 2752967 := bstep (se 1 (by rfl) ⟨2064725, by rfl⟩ : syracuseStep 2752967 = 4129451) B4129451
theorem B2064847 : Blo 1084620 2064847 := bstep (se 1 (by rfl) ⟨1548635, by rfl⟩ : syracuseStep 2064847 = 3097271) B3097271
theorem B23790125 : Blo 1084620 23790125 := bstep (se 3 (by rfl) ⟨4460648, by rfl⟩ : syracuseStep 23790125 = 8921297) B8921297
theorem B1835615 : Blo 1084620 1835615 := bstep (se 1 (by rfl) ⟨1376711, by rfl⟩ : syracuseStep 1835615 = 2753423) B2753423
theorem B3670703 : Blo 1084620 3670703 := bstep (se 1 (by rfl) ⟨2753027, by rfl⟩ : syracuseStep 3670703 = 5506055) B5506055
theorem B31752881 : Blo 1084620 31752881 := bstep (se 2 (by rfl) ⟨11907330, by rfl⟩ : syracuseStep 31752881 = 23814661) B23814661
theorem B5505731 : Blo 1084620 5505731 := bstep (se 1 (by rfl) ⟨4129298, by rfl⟩ : syracuseStep 5505731 = 8258597) B8258597
theorem B4948715 : Blo 1084620 4948715 := bstep (se 1 (by rfl) ⟨3711536, by rfl⟩ : syracuseStep 4948715 = 7423073) B7423073
theorem B12387167 : Blo 1084620 12387167 := bstep (se 1 (by rfl) ⟨9290375, by rfl⟩ : syracuseStep 12387167 = 18580751) B18580751
theorem B6357917 : Blo 1084620 6357917 := bstep (se 3 (by rfl) ⟨1192109, by rfl⟩ : syracuseStep 6357917 = 2384219) B2384219
theorem B3671027 : Blo 1084620 3671027 := bstep (se 1 (by rfl) ⟨2753270, by rfl⟩ : syracuseStep 3671027 = 5506541) B5506541
theorem B3474859 : Blo 1084620 3474859 := bstep (se 1 (by rfl) ⟨2606144, by rfl⟩ : syracuseStep 3474859 = 5212289) B5212289
theorem B3671567 : Blo 1084620 3671567 := bstep (se 1 (by rfl) ⟨2753675, by rfl⟩ : syracuseStep 3671567 = 5507351) B5507351
theorem B12355091 : Blo 1084620 12355091 := bstep (se 1 (by rfl) ⟨9266318, by rfl⟩ : syracuseStep 12355091 = 18532637) B18532637
theorem B4130621 : Blo 1084620 4130621 := bstep (se 3 (by rfl) ⟨774491, by rfl⟩ : syracuseStep 4130621 = 1548983) B1548983
theorem B1837039 : Blo 1084620 1837039 := bstep (se 1 (by rfl) ⟨1377779, by rfl⟩ : syracuseStep 1837039 = 2755559) B2755559
theorem B3672377 : Blo 1084620 3672377 := bstep (se 2 (by rfl) ⟨1377141, by rfl⟩ : syracuseStep 3672377 = 2754283) B2754283
theorem B2754911 : Blo 1084620 2754911 := bstep (se 1 (by rfl) ⟨2066183, by rfl⟩ : syracuseStep 2754911 = 4132367) B4132367
theorem B3672647 : Blo 1084620 3672647 := bstep (se 1 (by rfl) ⟨2754485, by rfl⟩ : syracuseStep 3672647 = 5508971) B5508971
theorem B7539551 : Blo 1084620 7539551 := bstep (se 1 (by rfl) ⟨5654663, by rfl⟩ : syracuseStep 7539551 = 11309327) B11309327
theorem B3476459 : Blo 1084620 3476459 := bstep (se 1 (by rfl) ⟨2607344, by rfl⟩ : syracuseStep 3476459 = 5214689) B5214689
theorem B1739755 : Blo 1084620 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B6949921 : Blo 1084620 6949921 := bstep (se 2 (by rfl) ⟨2606220, by rfl⟩ : syracuseStep 6949921 = 5212441) B5212441
theorem B1084639 : Blo 1084620 1084639 := bstep (se 1 (by rfl) ⟨813479, by rfl⟩ : syracuseStep 1084639 = 1626959) B1626959
theorem B8817893 : Blo 1084620 8817893 := bstep (se 4 (by rfl) ⟨826677, by rfl⟩ : syracuseStep 8817893 = 1653355) B1653355
theorem B11308339 : Blo 1084620 11308339 := bstep (se 1 (by rfl) ⟨8481254, by rfl⟩ : syracuseStep 11308339 = 16962509) B16962509
theorem B1084903 : Blo 1084620 1084903 := bstep (se 1 (by rfl) ⟨813677, by rfl⟩ : syracuseStep 1084903 = 1627355) B1627355
theorem B3673673 : Blo 1084620 3673673 := bstep (se 2 (by rfl) ⟨1377627, by rfl⟩ : syracuseStep 3673673 = 2755255) B2755255
theorem B1085019 : Blo 1084620 1085019 := bstep (se 1 (by rfl) ⟨813764, by rfl⟩ : syracuseStep 1085019 = 1627529) B1627529
theorem B1085255 : Blo 1084620 1085255 := bstep (se 1 (by rfl) ⟨813941, by rfl⟩ : syracuseStep 1085255 = 1627883) B1627883
theorem B1740665 : Blo 1084620 1740665 := bstep (se 2 (by rfl) ⟨652749, by rfl⟩ : syracuseStep 1740665 = 1305499) B1305499
theorem B1085407 : Blo 1084620 1085407 := bstep (se 1 (by rfl) ⟨814055, by rfl⟩ : syracuseStep 1085407 = 1628111) B1628111
theorem B4133051 : Blo 1084620 4133051 := bstep (se 1 (by rfl) ⟨3099788, by rfl⟩ : syracuseStep 4133051 = 6199577) B6199577
theorem B1085671 : Blo 1084620 1085671 := bstep (se 1 (by rfl) ⟨814253, by rfl⟩ : syracuseStep 1085671 = 1628507) B1628507
theorem B8261999 : Blo 1084620 8261999 := bstep (se 1 (by rfl) ⟨6196499, by rfl⟩ : syracuseStep 8261999 = 12392999) B12392999
theorem B1085823 : Blo 1084620 1085823 := bstep (se 1 (by rfl) ⟨814367, by rfl⟩ : syracuseStep 1085823 = 1628735) B1628735
theorem B1085903 : Blo 1084620 1085903 := bstep (se 1 (by rfl) ⟨814427, by rfl⟩ : syracuseStep 1085903 = 1628855) B1628855
theorem B5509619 : Blo 1084620 5509619 := bstep (se 1 (by rfl) ⟨4132214, by rfl⟩ : syracuseStep 5509619 = 8264429) B8264429
theorem B1086055 : Blo 1084620 1086055 := bstep (se 1 (by rfl) ⟨814541, by rfl⟩ : syracuseStep 1086055 = 1629083) B1629083
theorem B1086319 : Blo 1084620 1086319 := bstep (se 1 (by rfl) ⟨814739, by rfl⟩ : syracuseStep 1086319 = 1629479) B1629479
theorem B1086375 : Blo 1084620 1086375 := bstep (se 1 (by rfl) ⟨814781, by rfl⟩ : syracuseStep 1086375 = 1629563) B1629563
theorem B62591939 : Blo 1084620 62591939 := bstep (se 1 (by rfl) ⟨46943954, by rfl⟩ : syracuseStep 62591939 = 93887909) B93887909
theorem B1086459 : Blo 1084620 1086459 := bstep (se 1 (by rfl) ⟨814844, by rfl⟩ : syracuseStep 1086459 = 1629689) B1629689
theorem B1086527 : Blo 1084620 1086527 := bstep (se 1 (by rfl) ⟨814895, by rfl⟩ : syracuseStep 1086527 = 1629791) B1629791
theorem B1086671 : Blo 1084620 1086671 := bstep (se 1 (by rfl) ⟨815003, by rfl⟩ : syracuseStep 1086671 = 1630007) B1630007
theorem B1086875 : Blo 1084620 1086875 := bstep (se 1 (by rfl) ⟨815156, by rfl⟩ : syracuseStep 1086875 = 1630313) B1630313
theorem B18585125 : Blo 1084620 18585125 := bstep (se 4 (by rfl) ⟨1742355, by rfl⟩ : syracuseStep 18585125 = 3484711) B3484711
theorem B1545799 : Blo 1084620 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B1087087 : Blo 1084620 1087087 := bstep (se 1 (by rfl) ⟨815315, by rfl⟩ : syracuseStep 1087087 = 1630631) B1630631
theorem B1087143 : Blo 1084620 1087143 := bstep (se 1 (by rfl) ⟨815357, by rfl⟩ : syracuseStep 1087143 = 1630715) B1630715
theorem B1087227 : Blo 1084620 1087227 := bstep (se 1 (by rfl) ⟨815420, by rfl⟩ : syracuseStep 1087227 = 1630841) B1630841
theorem B6952715 : Blo 1084620 6952715 := bstep (se 1 (by rfl) ⟨5214536, by rfl⟩ : syracuseStep 6952715 = 10429073) B10429073
theorem B6199051 : Blo 1084620 6199051 := bstep (se 1 (by rfl) ⟨4649288, by rfl⟩ : syracuseStep 6199051 = 9298577) B9298577
theorem B1087263 : Blo 1084620 1087263 := bstep (se 1 (by rfl) ⟨815447, by rfl⟩ : syracuseStep 1087263 = 1630895) B1630895
theorem B1087295 : Blo 1084620 1087295 := bstep (se 1 (by rfl) ⟨815471, by rfl⟩ : syracuseStep 1087295 = 1630943) B1630943
theorem B1087471 : Blo 1084620 1087471 := bstep (se 1 (by rfl) ⟨815603, by rfl⟩ : syracuseStep 1087471 = 1631207) B1631207
theorem B7837721 : Blo 1084620 7837721 := bstep (se 2 (by rfl) ⟨2939145, by rfl⟩ : syracuseStep 7837721 = 5878291) B5878291
theorem B1087643 : Blo 1084620 1087643 := bstep (se 1 (by rfl) ⟨815732, by rfl⟩ : syracuseStep 1087643 = 1631465) B1631465
theorem B1087679 : Blo 1084620 1087679 := bstep (se 1 (by rfl) ⟨815759, by rfl⟩ : syracuseStep 1087679 = 1631519) B1631519
theorem B1087791 : Blo 1084620 1087791 := bstep (se 1 (by rfl) ⟨815843, by rfl⟩ : syracuseStep 1087791 = 1631687) B1631687
theorem B1546619 : Blo 1084620 1546619 := bstep (se 1 (by rfl) ⟨1159964, by rfl⟩ : syracuseStep 1546619 = 2319929) B2319929
theorem B5872061 : Blo 1084620 5872061 := bstep (se 3 (by rfl) ⟨1101011, by rfl⟩ : syracuseStep 5872061 = 2202023) B2202023
theorem B1088027 : Blo 1084620 1088027 := bstep (se 1 (by rfl) ⟨816020, by rfl⟩ : syracuseStep 1088027 = 1632041) B1632041
theorem B1088031 : Blo 1084620 1088031 := bstep (se 1 (by rfl) ⟨816023, by rfl⟩ : syracuseStep 1088031 = 1632047) B1632047
theorem B1088347 : Blo 1084620 1088347 := bstep (se 1 (by rfl) ⟨816260, by rfl⟩ : syracuseStep 1088347 = 1632521) B1632521
theorem B1088415 : Blo 1084620 1088415 := bstep (se 1 (by rfl) ⟨816311, by rfl⟩ : syracuseStep 1088415 = 1632623) B1632623
theorem B1088559 : Blo 1084620 1088559 := bstep (se 1 (by rfl) ⟨816419, by rfl⟩ : syracuseStep 1088559 = 1632839) B1632839
theorem B1088583 : Blo 1084620 1088583 := bstep (se 1 (by rfl) ⟨816437, by rfl⟩ : syracuseStep 1088583 = 1632875) B1632875
theorem B10460285 : Blo 1084620 10460285 := bstep (se 3 (by rfl) ⟨1961303, by rfl⟩ : syracuseStep 10460285 = 3922607) B3922607
theorem B1547599 : Blo 1084620 1547599 := bstep (se 1 (by rfl) ⟨1160699, by rfl⟩ : syracuseStep 1547599 = 2321399) B2321399
theorem B3710555 : Blo 1084620 3710555 := bstep (se 1 (by rfl) ⟨2782916, by rfl⟩ : syracuseStep 3710555 = 5565833) B5565833
theorem B9903779 : Blo 1084620 9903779 := bstep (se 1 (by rfl) ⟨7427834, by rfl⟩ : syracuseStep 9903779 = 14855669) B14855669
theorem B1220575 : Blo 1084620 1220575 := bstep (se 1 (by rfl) ⟨915431, by rfl⟩ : syracuseStep 1220575 = 1830863) B1830863
theorem B5218343 : Blo 1084620 5218343 := bstep (se 1 (by rfl) ⟨3913757, by rfl⟩ : syracuseStep 5218343 = 7827515) B7827515
theorem B6955379 : Blo 1084620 6955379 := bstep (se 1 (by rfl) ⟨5216534, by rfl⟩ : syracuseStep 6955379 = 10433069) B10433069
theorem B1221223 : Blo 1084620 1221223 := bstep (se 1 (by rfl) ⟨915917, by rfl⟩ : syracuseStep 1221223 = 1831835) B1831835
theorem B3711755 : Blo 1084620 3711755 := bstep (se 1 (by rfl) ⟨2783816, by rfl⟩ : syracuseStep 3711755 = 5567633) B5567633
theorem B5874443 : Blo 1084620 5874443 := bstep (se 1 (by rfl) ⟨4405832, by rfl⟩ : syracuseStep 5874443 = 8811665) B8811665
theorem B4400335 : Blo 1084620 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B7546105 : Blo 1084620 7546105 := bstep (se 2 (by rfl) ⟨2829789, by rfl⟩ : syracuseStep 7546105 = 5659579) B5659579
theorem B7841063 : Blo 1084620 7841063 := bstep (se 1 (by rfl) ⟨5880797, by rfl⟩ : syracuseStep 7841063 = 11761595) B11761595
theorem B1549945 : Blo 1084620 1549945 := bstep (se 2 (by rfl) ⟨581229, by rfl⟩ : syracuseStep 1549945 = 1162459) B1162459
theorem B6956711 : Blo 1084620 6956711 := bstep (se 1 (by rfl) ⟨5217533, by rfl⟩ : syracuseStep 6956711 = 10435067) B10435067
theorem B30189725 : Blo 1084620 30189725 := bstep (se 3 (by rfl) ⟨5660573, by rfl⟩ : syracuseStep 30189725 = 11321147) B11321147
theorem B3910151 : Blo 1084620 3910151 := bstep (se 1 (by rfl) ⟨2932613, by rfl⟩ : syracuseStep 3910151 = 5865227) B5865227
theorem B57191093 : Blo 1084620 57191093 := bstep (se 5 (by rfl) ⟨2680832, by rfl⟩ : syracuseStep 57191093 = 5361665) B5361665
theorem B18787301 : Blo 1084620 18787301 := bstep (se 4 (by rfl) ⟨1761309, by rfl⟩ : syracuseStep 18787301 = 3522619) B3522619
theorem B3091553 : Blo 1084620 3091553 := bstep (se 2 (by rfl) ⟨1159332, by rfl⟩ : syracuseStep 3091553 = 2318665) B2318665
theorem B3091679 : Blo 1084620 3091679 := bstep (se 1 (by rfl) ⟨2318759, by rfl⟩ : syracuseStep 3091679 = 4637519) B4637519
theorem B3091895 : Blo 1084620 3091895 := bstep (se 1 (by rfl) ⟨2318921, by rfl⟩ : syracuseStep 3091895 = 4637843) B4637843
theorem B1224283 : Blo 1084620 1224283 := bstep (se 1 (by rfl) ⟨918212, by rfl⟩ : syracuseStep 1224283 = 1836425) B1836425
theorem B1224571 : Blo 1084620 1224571 := bstep (se 1 (by rfl) ⟨918428, by rfl⟩ : syracuseStep 1224571 = 1836857) B1836857
theorem B3092863 : Blo 1084620 3092863 := bstep (se 1 (by rfl) ⟨2319647, by rfl⟩ : syracuseStep 3092863 = 4639295) B4639295
theorem B13218365 : Blo 1084620 13218365 := bstep (se 3 (by rfl) ⟨2478443, by rfl⟩ : syracuseStep 13218365 = 4956887) B4956887
theorem B8368811 : Blo 1084620 8368811 := bstep (se 1 (by rfl) ⟨6276608, by rfl⟩ : syracuseStep 8368811 = 12553217) B12553217
theorem B52900523 : Blo 1084620 52900523 := bstep (se 1 (by rfl) ⟨39675392, by rfl⟩ : syracuseStep 52900523 = 79350785) B79350785
theorem B3486455 : Blo 1084620 3486455 := bstep (se 1 (by rfl) ⟨2614841, by rfl⟩ : syracuseStep 3486455 = 5229683) B5229683
theorem B4633469 : Blo 1084620 4633469 := bstep (se 3 (by rfl) ⟨868775, by rfl⟩ : syracuseStep 4633469 = 1737551) B1737551
theorem B3715969 : Blo 1084620 3715969 := bstep (se 2 (by rfl) ⟨1393488, by rfl⟩ : syracuseStep 3715969 = 2786977) B2786977
theorem B1160255 : Blo 1084620 1160255 := bstep (se 1 (by rfl) ⟨870191, by rfl⟩ : syracuseStep 1160255 = 1740383) B1740383
theorem B16726297 : Blo 1084620 16726297 := bstep (se 2 (by rfl) ⟨6272361, by rfl⟩ : syracuseStep 16726297 = 12544723) B12544723
theorem B13941305 : Blo 1084620 13941305 := bstep (se 2 (by rfl) ⟨5227989, by rfl⟩ : syracuseStep 13941305 = 10455979) B10455979
theorem B6700103 : Blo 1084620 6700103 := bstep (se 1 (by rfl) ⟨5025077, by rfl⟩ : syracuseStep 6700103 = 10050155) B10050155
theorem B30555265 : Blo 1084620 30555265 := bstep (se 2 (by rfl) ⟨11458224, by rfl⟩ : syracuseStep 30555265 = 22916449) B22916449
theorem B2440457 : Blo 1084620 2440457 := bstep (se 2 (by rfl) ⟨915171, by rfl⟩ : syracuseStep 2440457 = 1830343) B1830343
theorem B4963751 : Blo 1084620 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B16072199 : Blo 1084620 16072199 := bstep (se 1 (by rfl) ⟨12054149, by rfl⟩ : syracuseStep 16072199 = 24108299) B24108299
theorem B26459693 : Blo 1084620 26459693 := bstep (se 3 (by rfl) ⟨4961192, by rfl⟩ : syracuseStep 26459693 = 9922385) B9922385
theorem B6962861 : Blo 1084620 6962861 := bstep (se 3 (by rfl) ⟨1305536, by rfl⟩ : syracuseStep 6962861 = 2611073) B2611073
theorem B2441447 : Blo 1084620 2441447 := bstep (se 1 (by rfl) ⟨1831085, by rfl⟩ : syracuseStep 2441447 = 3662171) B3662171
theorem B3916063 : Blo 1084620 3916063 := bstep (se 1 (by rfl) ⟨2937047, by rfl⟩ : syracuseStep 3916063 = 5874095) B5874095
theorem B3096929 : Blo 1084620 3096929 := bstep (se 2 (by rfl) ⟨1161348, by rfl⟩ : syracuseStep 3096929 = 2322697) B2322697
theorem B10731959 : Blo 1084620 10731959 := bstep (se 1 (by rfl) ⟨8048969, by rfl⟩ : syracuseStep 10731959 = 16097939) B16097939
theorem B6603227 : Blo 1084620 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B6177455 : Blo 1084620 6177455 := bstep (se 1 (by rfl) ⟨4633091, by rfl⟩ : syracuseStep 6177455 = 9266183) B9266183
theorem B6963887 : Blo 1084620 6963887 := bstep (se 1 (by rfl) ⟨5222915, by rfl⟩ : syracuseStep 6963887 = 10445831) B10445831
theorem B2442041 : Blo 1084620 2442041 := bstep (se 2 (by rfl) ⟨915765, by rfl⟩ : syracuseStep 2442041 = 1831531) B1831531
theorem B2442095 : Blo 1084620 2442095 := bstep (se 1 (by rfl) ⟨1831571, by rfl⟩ : syracuseStep 2442095 = 3663143) B3663143
theorem B3097511 : Blo 1084620 3097511 := bstep (se 1 (by rfl) ⟨2323133, by rfl⟩ : syracuseStep 3097511 = 4646267) B4646267
theorem B2442671 : Blo 1084620 2442671 := bstep (se 1 (by rfl) ⟨1832003, by rfl⟩ : syracuseStep 2442671 = 3664007) B3664007
theorem B10438141 : Blo 1084620 10438141 := bstep (se 3 (by rfl) ⟨1957151, by rfl⟩ : syracuseStep 10438141 = 3914303) B3914303
theorem B6178457 : Blo 1084620 6178457 := bstep (se 2 (by rfl) ⟨2316921, by rfl⟩ : syracuseStep 6178457 = 4633843) B4633843
theorem B1984223 : Blo 1084620 1984223 := bstep (se 1 (by rfl) ⟨1488167, by rfl⟩ : syracuseStep 1984223 = 2976335) B2976335
theorem B6178639 : Blo 1084620 6178639 := bstep (se 1 (by rfl) ⟨4633979, by rfl⟩ : syracuseStep 6178639 = 9267959) B9267959
theorem B2443499 : Blo 1084620 2443499 := bstep (se 1 (by rfl) ⟨1832624, by rfl⟩ : syracuseStep 2443499 = 3665249) B3665249
theorem B13912397 : Blo 1084620 13912397 := bstep (se 3 (by rfl) ⟨2608574, by rfl⟩ : syracuseStep 13912397 = 5217149) B5217149
theorem B9292427 : Blo 1084620 9292427 := bstep (se 1 (by rfl) ⟨6969320, by rfl⟩ : syracuseStep 9292427 = 13938641) B13938641
theorem B4639447 : Blo 1084620 4639447 := bstep (se 1 (by rfl) ⟨3479585, by rfl⟩ : syracuseStep 4639447 = 6959171) B6959171
theorem B3132395 : Blo 1084620 3132395 := bstep (se 1 (by rfl) ⟨2349296, by rfl⟩ : syracuseStep 3132395 = 4698593) B4698593
theorem B15650293 : Blo 1084620 15650293 := bstep (se 5 (by rfl) ⟨733607, by rfl⟩ : syracuseStep 15650293 = 1467215) B1467215
theorem B2444795 : Blo 1084620 2444795 := bstep (se 1 (by rfl) ⟨1833596, by rfl⟩ : syracuseStep 2444795 = 3667193) B3667193
theorem B7425643 : Blo 1084620 7425643 := bstep (se 1 (by rfl) ⟨5569232, by rfl⟩ : syracuseStep 7425643 = 11138465) B11138465
theorem B2444975 : Blo 1084620 2444975 := bstep (se 1 (by rfl) ⟨1833731, by rfl⟩ : syracuseStep 2444975 = 3667463) B3667463
theorem B2445623 : Blo 1084620 2445623 := bstep (se 1 (by rfl) ⟨1834217, by rfl⟩ : syracuseStep 2445623 = 3668435) B3668435
theorem B7065967 : Blo 1084620 7065967 := bstep (se 1 (by rfl) ⟨5299475, by rfl⟩ : syracuseStep 7065967 = 10598951) B10598951
theorem B2445695 : Blo 1084620 2445695 := bstep (se 1 (by rfl) ⟨1834271, by rfl⟩ : syracuseStep 2445695 = 3668543) B3668543
theorem B1790345 : Blo 1084620 1790345 := bstep (se 2 (by rfl) ⟨671379, by rfl⟩ : syracuseStep 1790345 = 1342759) B1342759
theorem B15061801 : Blo 1084620 15061801 := bstep (se 2 (by rfl) ⟨5648175, by rfl⟩ : syracuseStep 15061801 = 11296351) B11296351
theorem B6968375 : Blo 1084620 6968375 := bstep (se 1 (by rfl) ⟨5226281, by rfl⟩ : syracuseStep 6968375 = 10452563) B10452563
theorem B1627199 : Blo 1084620 1627199 := bstep (se 1 (by rfl) ⟨1220399, by rfl⟩ : syracuseStep 1627199 = 2440799) B2440799
theorem B1627241 : Blo 1084620 1627241 := bstep (se 2 (by rfl) ⟨610215, by rfl⟩ : syracuseStep 1627241 = 1220431) B1220431
theorem B1954991 : Blo 1084620 1954991 := bstep (se 1 (by rfl) ⟨1466243, by rfl⟩ : syracuseStep 1954991 = 2932487) B2932487
theorem B8246447 : Blo 1084620 8246447 := bstep (se 1 (by rfl) ⟨6184835, by rfl⟩ : syracuseStep 8246447 = 12369671) B12369671
theorem B1627343 : Blo 1084620 1627343 := bstep (se 1 (by rfl) ⟨1220507, by rfl⟩ : syracuseStep 1627343 = 2441015) B2441015
theorem B1627547 : Blo 1084620 1627547 := bstep (se 1 (by rfl) ⟨1220660, by rfl⟩ : syracuseStep 1627547 = 2441321) B2441321
theorem B2446919 : Blo 1084620 2446919 := bstep (se 1 (by rfl) ⟨1835189, by rfl⟩ : syracuseStep 2446919 = 3670379) B3670379
theorem B1627769 : Blo 1084620 1627769 := bstep (se 2 (by rfl) ⟨610413, by rfl⟩ : syracuseStep 1627769 = 1220827) B1220827
theorem B1955495 : Blo 1084620 1955495 := bstep (se 1 (by rfl) ⟨1466621, by rfl⟩ : syracuseStep 1955495 = 2933243) B2933243
theorem B1627871 : Blo 1084620 1627871 := bstep (se 1 (by rfl) ⟨1220903, by rfl⟩ : syracuseStep 1627871 = 2441807) B2441807
theorem B2447099 : Blo 1084620 2447099 := bstep (se 1 (by rfl) ⟨1835324, by rfl⟩ : syracuseStep 2447099 = 3670649) B3670649
theorem B1627967 : Blo 1084620 1627967 := bstep (se 1 (by rfl) ⟨1220975, by rfl⟩ : syracuseStep 1627967 = 2441951) B2441951
theorem B1628135 : Blo 1084620 1628135 := bstep (se 1 (by rfl) ⟨1221101, by rfl⟩ : syracuseStep 1628135 = 2442203) B2442203
theorem B1628153 : Blo 1084620 1628153 := bstep (se 2 (by rfl) ⟨610557, by rfl⟩ : syracuseStep 1628153 = 1221115) B1221115
theorem B1628255 : Blo 1084620 1628255 := bstep (se 1 (by rfl) ⟨1221191, by rfl⟩ : syracuseStep 1628255 = 2442383) B2442383
theorem B2480225 : Blo 1084620 2480225 := bstep (se 2 (by rfl) ⟨930084, by rfl⟩ : syracuseStep 2480225 = 1860169) B1860169
theorem B1628315 : Blo 1084620 1628315 := bstep (se 1 (by rfl) ⟨1221236, by rfl⟩ : syracuseStep 1628315 = 2442473) B2442473
theorem B1628351 : Blo 1084620 1628351 := bstep (se 1 (by rfl) ⟨1221263, by rfl⟩ : syracuseStep 1628351 = 2442527) B2442527
theorem B1628393 : Blo 1084620 1628393 := bstep (se 2 (by rfl) ⟨610647, by rfl⟩ : syracuseStep 1628393 = 1221295) B1221295
theorem B2939123 : Blo 1084620 2939123 := bstep (se 1 (by rfl) ⟨2204342, by rfl⟩ : syracuseStep 2939123 = 4408685) B4408685
theorem B2447657 : Blo 1084620 2447657 := bstep (se 2 (by rfl) ⟨917871, by rfl⟩ : syracuseStep 2447657 = 1835743) B1835743
theorem B1628699 : Blo 1084620 1628699 := bstep (se 1 (by rfl) ⟨1221524, by rfl⟩ : syracuseStep 1628699 = 2443049) B2443049
theorem B2939449 : Blo 1084620 2939449 := bstep (se 2 (by rfl) ⟨1102293, by rfl⟩ : syracuseStep 2939449 = 2204587) B2204587
theorem B1628777 : Blo 1084620 1628777 := bstep (se 2 (by rfl) ⟨610791, by rfl⟩ : syracuseStep 1628777 = 1221583) B1221583
theorem B2448233 : Blo 1084620 2448233 := bstep (se 2 (by rfl) ⟨918087, by rfl⟩ : syracuseStep 2448233 = 1836175) B1836175
theorem B2448287 : Blo 1084620 2448287 := bstep (se 1 (by rfl) ⟨1836215, by rfl⟩ : syracuseStep 2448287 = 3672431) B3672431
theorem B4643821 : Blo 1084620 4643821 := bstep (se 3 (by rfl) ⟨870716, by rfl⟩ : syracuseStep 4643821 = 1741433) B1741433
theorem B1629305 : Blo 1084620 1629305 := bstep (se 2 (by rfl) ⟨610989, by rfl⟩ : syracuseStep 1629305 = 1221979) B1221979
theorem B3660929 : Blo 1084620 3660929 := bstep (se 2 (by rfl) ⟨1372848, by rfl⟩ : syracuseStep 3660929 = 2745697) B2745697
theorem B3660983 : Blo 1084620 3660983 := bstep (se 1 (by rfl) ⟨2745737, by rfl⟩ : syracuseStep 3660983 = 5491475) B5491475
theorem B1629407 : Blo 1084620 1629407 := bstep (se 1 (by rfl) ⟨1222055, by rfl⟩ : syracuseStep 1629407 = 2444111) B2444111
theorem B1629449 : Blo 1084620 1629449 := bstep (se 2 (by rfl) ⟨611043, by rfl⟩ : syracuseStep 1629449 = 1222087) B1222087
theorem B1629551 : Blo 1084620 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B10739105 : Blo 1084620 10739105 := bstep (se 2 (by rfl) ⟨4027164, by rfl⟩ : syracuseStep 10739105 = 8054329) B8054329
theorem B1629671 : Blo 1084620 1629671 := bstep (se 1 (by rfl) ⟨1222253, by rfl⟩ : syracuseStep 1629671 = 2444507) B2444507
theorem B1629803 : Blo 1084620 1629803 := bstep (se 1 (by rfl) ⟨1222352, by rfl⟩ : syracuseStep 1629803 = 2444705) B2444705
theorem B1629929 : Blo 1084620 1629929 := bstep (se 2 (by rfl) ⟨611223, by rfl⟩ : syracuseStep 1629929 = 1222447) B1222447
theorem B2449223 : Blo 1084620 2449223 := bstep (se 1 (by rfl) ⟨1836917, by rfl⟩ : syracuseStep 2449223 = 3673835) B3673835
theorem B1630073 : Blo 1084620 1630073 := bstep (se 2 (by rfl) ⟨611277, by rfl⟩ : syracuseStep 1630073 = 1222555) B1222555
theorem B1957787 : Blo 1084620 1957787 := bstep (se 1 (by rfl) ⟨1468340, by rfl⟩ : syracuseStep 1957787 = 2936681) B2936681
theorem B3661739 : Blo 1084620 3661739 := bstep (se 1 (by rfl) ⟨2746304, by rfl⟩ : syracuseStep 3661739 = 5492609) B5492609
theorem B1630175 : Blo 1084620 1630175 := bstep (se 1 (by rfl) ⟨1222631, by rfl⟩ : syracuseStep 1630175 = 2445263) B2445263
theorem B2318375 : Blo 1084620 2318375 := bstep (se 1 (by rfl) ⟨1738781, by rfl⟩ : syracuseStep 2318375 = 3477563) B3477563
theorem B1630427 : Blo 1084620 1630427 := bstep (se 1 (by rfl) ⟨1222820, by rfl⟩ : syracuseStep 1630427 = 2445641) B2445641
theorem B1630439 : Blo 1084620 1630439 := bstep (se 1 (by rfl) ⟨1222829, by rfl⟩ : syracuseStep 1630439 = 2445659) B2445659
theorem B1237375 : Blo 1084620 1237375 := bstep (se 1 (by rfl) ⟨928031, by rfl⟩ : syracuseStep 1237375 = 1856063) B1856063
theorem B1630601 : Blo 1084620 1630601 := bstep (se 2 (by rfl) ⟨611475, by rfl⟩ : syracuseStep 1630601 = 1222951) B1222951
theorem B161014169 : Blo 1084620 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B3662279 : Blo 1084620 3662279 := bstep (se 1 (by rfl) ⟨2746709, by rfl⟩ : syracuseStep 3662279 = 5493419) B5493419
theorem B1630697 : Blo 1084620 1630697 := bstep (se 2 (by rfl) ⟨611511, by rfl⟩ : syracuseStep 1630697 = 1223023) B1223023
theorem B1958393 : Blo 1084620 1958393 := bstep (se 2 (by rfl) ⟨734397, by rfl⟩ : syracuseStep 1958393 = 1468795) B1468795
theorem B1630823 : Blo 1084620 1630823 := bstep (se 1 (by rfl) ⟨1223117, by rfl⟩ : syracuseStep 1630823 = 2446235) B2446235
theorem B1630955 : Blo 1084620 1630955 := bstep (se 1 (by rfl) ⟨1223216, by rfl⟩ : syracuseStep 1630955 = 2446433) B2446433
theorem B1630985 : Blo 1084620 1630985 := bstep (se 2 (by rfl) ⟨611619, by rfl⟩ : syracuseStep 1630985 = 1223239) B1223239
theorem B3662603 : Blo 1084620 3662603 := bstep (se 1 (by rfl) ⟨2746952, by rfl⟩ : syracuseStep 3662603 = 5493905) B5493905
theorem B6185747 : Blo 1084620 6185747 := bstep (se 1 (by rfl) ⟨4639310, by rfl⟩ : syracuseStep 6185747 = 9278621) B9278621
theorem B4121401 : Blo 1084620 4121401 := bstep (se 2 (by rfl) ⟨1545525, by rfl⟩ : syracuseStep 4121401 = 3091051) B3091051
theorem B2351929 : Blo 1084620 2351929 := bstep (se 2 (by rfl) ⟨881973, by rfl⟩ : syracuseStep 2351929 = 1763947) B1763947
theorem B1631087 : Blo 1084620 1631087 := bstep (se 1 (by rfl) ⟨1223315, by rfl⟩ : syracuseStep 1631087 = 2446631) B2446631
theorem B3662873 : Blo 1084620 3662873 := bstep (se 2 (by rfl) ⟨1373577, by rfl⟩ : syracuseStep 3662873 = 2747155) B2747155
theorem B1631339 : Blo 1084620 1631339 := bstep (se 1 (by rfl) ⟨1223504, by rfl⟩ : syracuseStep 1631339 = 2447009) B2447009
theorem B13919525 : Blo 1084620 13919525 := bstep (se 4 (by rfl) ⟨1304955, by rfl⟩ : syracuseStep 13919525 = 2609911) B2609911
theorem B1631579 : Blo 1084620 1631579 := bstep (se 1 (by rfl) ⟨1223684, by rfl⟩ : syracuseStep 1631579 = 2447369) B2447369
theorem B1631855 : Blo 1084620 1631855 := bstep (se 1 (by rfl) ⟨1223891, by rfl⟩ : syracuseStep 1631855 = 2447783) B2447783
theorem B3663521 : Blo 1084620 3663521 := bstep (se 2 (by rfl) ⟨1373820, by rfl⟩ : syracuseStep 3663521 = 2747641) B2747641
theorem B1631927 : Blo 1084620 1631927 := bstep (se 1 (by rfl) ⟨1223945, by rfl⟩ : syracuseStep 1631927 = 2447891) B2447891
theorem B1631963 : Blo 1084620 1631963 := bstep (se 1 (by rfl) ⟨1223972, by rfl⟩ : syracuseStep 1631963 = 2447945) B2447945
theorem B1861339 : Blo 1084620 1861339 := bstep (se 1 (by rfl) ⟨1396004, by rfl⟩ : syracuseStep 1861339 = 2792009) B2792009
theorem B226223873 : Blo 1084620 226223873 := bstep (se 2 (by rfl) ⟨84833952, by rfl⟩ : syracuseStep 226223873 = 169667905) B169667905
theorem B1632137 : Blo 1084620 1632137 := bstep (se 2 (by rfl) ⟨612051, by rfl⟩ : syracuseStep 1632137 = 1224103) B1224103
theorem B1632239 : Blo 1084620 1632239 := bstep (se 1 (by rfl) ⟨1224179, by rfl⟩ : syracuseStep 1632239 = 2448359) B2448359
theorem B1632491 : Blo 1084620 1632491 := bstep (se 1 (by rfl) ⟨1224368, by rfl⟩ : syracuseStep 1632491 = 2448737) B2448737
theorem B1632551 : Blo 1084620 1632551 := bstep (se 1 (by rfl) ⟨1224413, by rfl⟩ : syracuseStep 1632551 = 2448827) B2448827
theorem B3664223 : Blo 1084620 3664223 := bstep (se 1 (by rfl) ⟨2748167, by rfl⟩ : syracuseStep 3664223 = 5496335) B5496335
theorem B1632635 : Blo 1084620 1632635 := bstep (se 1 (by rfl) ⟨1224476, by rfl⟩ : syracuseStep 1632635 = 2448953) B2448953
theorem B4647307 : Blo 1084620 4647307 := bstep (se 1 (by rfl) ⟨3485480, by rfl⟩ : syracuseStep 4647307 = 6970961) B6970961
theorem B3664385 : Blo 1084620 3664385 := bstep (se 2 (by rfl) ⟨1374144, by rfl⟩ : syracuseStep 3664385 = 2748289) B2748289
theorem B2320903 : Blo 1084620 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B4123163 : Blo 1084620 4123163 := bstep (se 1 (by rfl) ⟨3092372, by rfl⟩ : syracuseStep 4123163 = 6184745) B6184745
theorem B1632905 : Blo 1084620 1632905 := bstep (se 2 (by rfl) ⟨612339, by rfl⟩ : syracuseStep 1632905 = 1224679) B1224679
theorem B5499575 : Blo 1084620 5499575 := bstep (se 1 (by rfl) ⟨4124681, by rfl⟩ : syracuseStep 5499575 = 8249363) B8249363
theorem B3664871 : Blo 1084620 3664871 := bstep (se 1 (by rfl) ⟨2748653, by rfl⟩ : syracuseStep 3664871 = 5497307) B5497307
theorem B3665195 : Blo 1084620 3665195 := bstep (se 1 (by rfl) ⟨2748896, by rfl⟩ : syracuseStep 3665195 = 5497793) B5497793
theorem B10448291 : Blo 1084620 10448291 := bstep (se 1 (by rfl) ⟨7836218, by rfl⟩ : syracuseStep 10448291 = 15672437) B15672437
theorem B3665465 : Blo 1084620 3665465 := bstep (se 2 (by rfl) ⟨1374549, by rfl⟩ : syracuseStep 3665465 = 2749099) B2749099
theorem B3141193 : Blo 1084620 3141193 := bstep (se 2 (by rfl) ⟨1177947, by rfl⟩ : syracuseStep 3141193 = 2355895) B2355895
theorem B1831099 : Blo 1084620 1831099 := bstep (se 1 (by rfl) ⟨1373324, by rfl⟩ : syracuseStep 1831099 = 2746649) B2746649
theorem B1831295 : Blo 1084620 1831295 := bstep (se 1 (by rfl) ⟨1373471, by rfl⟩ : syracuseStep 1831295 = 2746943) B2746943
theorem B2748887 : Blo 1084620 2748887 := bstep (se 1 (by rfl) ⟨2061665, by rfl⟩ : syracuseStep 2748887 = 4123331) B4123331
theorem B2323039 : Blo 1084620 2323039 := bstep (se 1 (by rfl) ⟨1742279, by rfl⟩ : syracuseStep 2323039 = 3484559) B3484559
theorem B1831727 : Blo 1084620 1831727 := bstep (se 1 (by rfl) ⟨1373795, by rfl⟩ : syracuseStep 1831727 = 2747591) B2747591
theorem B3667355 : Blo 1084620 3667355 := bstep (se 1 (by rfl) ⟨2750516, by rfl⟩ : syracuseStep 3667355 = 5501033) B5501033
theorem B2062007 : Blo 1084620 2062007 := bstep (se 1 (by rfl) ⟨1546505, by rfl⟩ : syracuseStep 2062007 = 3093011) B3093011
theorem B1570487 : Blo 1084620 1570487 := bstep (se 1 (by rfl) ⟨1177865, by rfl⟩ : syracuseStep 1570487 = 2355731) B2355731
theorem B1832699 : Blo 1084620 1832699 := bstep (se 1 (by rfl) ⟨1374524, by rfl⟩ : syracuseStep 1832699 = 2749049) B2749049
theorem B2750345 : Blo 1084620 2750345 := bstep (se 2 (by rfl) ⟨1031379, by rfl⟩ : syracuseStep 2750345 = 2062759) B2062759
theorem B1832935 : Blo 1084620 1832935 := bstep (se 1 (by rfl) ⟨1374701, by rfl⟩ : syracuseStep 1832935 = 2749403) B2749403
theorem B3668111 : Blo 1084620 3668111 := bstep (se 1 (by rfl) ⟨2751083, by rfl⟩ : syracuseStep 3668111 = 5502167) B5502167
theorem B1833151 : Blo 1084620 1833151 := bstep (se 1 (by rfl) ⟨1374863, by rfl⟩ : syracuseStep 1833151 = 2749727) B2749727
theorem B2324713 : Blo 1084620 2324713 := bstep (se 2 (by rfl) ⟨871767, by rfl⟩ : syracuseStep 2324713 = 1743535) B1743535
theorem B32143979 : Blo 1084620 32143979 := bstep (se 1 (by rfl) ⟨24107984, by rfl⟩ : syracuseStep 32143979 = 48215969) B48215969
theorem B1833887 : Blo 1084620 1833887 := bstep (se 1 (by rfl) ⟨1375415, by rfl⟩ : syracuseStep 1833887 = 2750831) B2750831
theorem B2751529 : Blo 1084620 2751529 := bstep (se 2 (by rfl) ⟨1031823, by rfl⟩ : syracuseStep 2751529 = 2063647) B2063647
theorem B2751671 : Blo 1084620 2751671 := bstep (se 1 (by rfl) ⟨2063753, by rfl⟩ : syracuseStep 2751671 = 4127507) B4127507
theorem B4127993 : Blo 1084620 4127993 := bstep (se 2 (by rfl) ⟨1547997, by rfl⟩ : syracuseStep 4127993 = 3095995) B3095995
theorem B3669245 : Blo 1084620 3669245 := bstep (se 3 (by rfl) ⟨687983, by rfl⟩ : syracuseStep 3669245 = 1375967) B1375967
theorem B1834319 : Blo 1084620 1834319 := bstep (se 1 (by rfl) ⟨1375739, by rfl⟩ : syracuseStep 1834319 = 2751479) B2751479
theorem B8813929 : Blo 1084620 8813929 := bstep (se 2 (by rfl) ⟨3305223, by rfl⟩ : syracuseStep 8813929 = 6610447) B6610447
theorem B5504759 : Blo 1084620 5504759 := bstep (se 1 (by rfl) ⟨4128569, by rfl⟩ : syracuseStep 5504759 = 8257139) B8257139
theorem B2981821 : Blo 1084620 2981821 := bstep (se 3 (by rfl) ⟨559091, by rfl⟩ : syracuseStep 2981821 = 1118183) B1118183
theorem B2064619 : Blo 1084620 2064619 := bstep (se 1 (by rfl) ⟨1548464, by rfl⟩ : syracuseStep 2064619 = 3096929) B3096929
theorem B1835311 : Blo 1084620 1835311 := bstep (se 1 (by rfl) ⟨1376483, by rfl⟩ : syracuseStep 1835311 = 2752967) B2752967
theorem B15860083 : Blo 1084620 15860083 := bstep (se 1 (by rfl) ⟨11895062, by rfl⟩ : syracuseStep 15860083 = 23790125) B23790125
theorem B21168587 : Blo 1084620 21168587 := bstep (se 1 (by rfl) ⟨15876440, by rfl⟩ : syracuseStep 21168587 = 31752881) B31752881
theorem B3670487 : Blo 1084620 3670487 := bstep (se 1 (by rfl) ⟨2752865, by rfl⟩ : syracuseStep 3670487 = 5505731) B5505731
theorem B8258111 : Blo 1084620 8258111 := bstep (se 1 (by rfl) ⟨6193583, by rfl⟩ : syracuseStep 8258111 = 12387167) B12387167
theorem B2753129 : Blo 1084620 2753129 := bstep (se 2 (by rfl) ⟨1032423, by rfl⟩ : syracuseStep 2753129 = 2064847) B2064847
theorem B2065007 : Blo 1084620 2065007 := bstep (se 1 (by rfl) ⟨1548755, by rfl⟩ : syracuseStep 2065007 = 3097511) B3097511
theorem B2753747 : Blo 1084620 2753747 := bstep (se 1 (by rfl) ⟨2065310, by rfl⟩ : syracuseStep 2753747 = 4130621) B4130621
theorem B9274931 : Blo 1084620 9274931 := bstep (se 1 (by rfl) ⟨6956198, by rfl⟩ : syracuseStep 9274931 = 13912397) B13912397
theorem B1836607 : Blo 1084620 1836607 := bstep (se 1 (by rfl) ⟨1377455, by rfl⟩ : syracuseStep 1836607 = 2754911) B2754911
theorem B5867113 : Blo 1084620 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B6194951 : Blo 1084620 6194951 := bstep (se 1 (by rfl) ⟨4646213, by rfl⟩ : syracuseStep 6194951 = 9292427) B9292427
theorem B9898013 : Blo 1084620 9898013 := bstep (se 3 (by rfl) ⟨1855877, by rfl⟩ : syracuseStep 9898013 = 3711755) B3711755
theorem B2755367 : Blo 1084620 2755367 := bstep (se 1 (by rfl) ⟨2066525, by rfl⟩ : syracuseStep 2755367 = 4133051) B4133051
theorem B5507999 : Blo 1084620 5507999 := bstep (se 1 (by rfl) ⟨4130999, by rfl⟩ : syracuseStep 5507999 = 8261999) B8261999
theorem B3673079 : Blo 1084620 3673079 := bstep (se 1 (by rfl) ⟨2754809, by rfl⟩ : syracuseStep 3673079 = 5509619) B5509619
theorem B6196409 : Blo 1084620 6196409 := bstep (se 2 (by rfl) ⟨2323653, by rfl⟩ : syracuseStep 6196409 = 4647307) B4647307
theorem B1084799 : Blo 1084620 1084799 := bstep (se 1 (by rfl) ⟨813599, by rfl⟩ : syracuseStep 1084799 = 1627199) B1627199
theorem B1084827 : Blo 1084620 1084827 := bstep (se 1 (by rfl) ⟨813620, by rfl⟩ : syracuseStep 1084827 = 1627241) B1627241
theorem B1084895 : Blo 1084620 1084895 := bstep (se 1 (by rfl) ⟨813671, by rfl⟩ : syracuseStep 1084895 = 1627343) B1627343
theorem B1085031 : Blo 1084620 1085031 := bstep (se 1 (by rfl) ⟨813773, by rfl⟩ : syracuseStep 1085031 = 1627547) B1627547
theorem B12390083 : Blo 1084620 12390083 := bstep (se 1 (by rfl) ⟨9292562, by rfl⟩ : syracuseStep 12390083 = 18585125) B18585125
theorem B1085179 : Blo 1084620 1085179 := bstep (se 1 (by rfl) ⟨813884, by rfl⟩ : syracuseStep 1085179 = 1627769) B1627769
theorem B1085247 : Blo 1084620 1085247 := bstep (se 1 (by rfl) ⟨813935, by rfl⟩ : syracuseStep 1085247 = 1627871) B1627871
theorem B1085311 : Blo 1084620 1085311 := bstep (se 1 (by rfl) ⟨813983, by rfl⟩ : syracuseStep 1085311 = 1627967) B1627967
theorem B1085423 : Blo 1084620 1085423 := bstep (se 1 (by rfl) ⟨814067, by rfl⟩ : syracuseStep 1085423 = 1628135) B1628135
theorem B1085435 : Blo 1084620 1085435 := bstep (se 1 (by rfl) ⟨814076, by rfl⟩ : syracuseStep 1085435 = 1628153) B1628153
theorem B1085503 : Blo 1084620 1085503 := bstep (se 1 (by rfl) ⟨814127, by rfl⟩ : syracuseStep 1085503 = 1628255) B1628255
theorem B1085543 : Blo 1084620 1085543 := bstep (se 1 (by rfl) ⟨814157, by rfl⟩ : syracuseStep 1085543 = 1628315) B1628315
theorem B1085567 : Blo 1084620 1085567 := bstep (se 1 (by rfl) ⟨814175, by rfl⟩ : syracuseStep 1085567 = 1628351) B1628351
theorem B1085595 : Blo 1084620 1085595 := bstep (se 1 (by rfl) ⟨814196, by rfl⟩ : syracuseStep 1085595 = 1628393) B1628393
theorem B1085799 : Blo 1084620 1085799 := bstep (se 1 (by rfl) ⟨814349, by rfl⟩ : syracuseStep 1085799 = 1628699) B1628699
theorem B1085851 : Blo 1084620 1085851 := bstep (se 1 (by rfl) ⟨814388, by rfl⟩ : syracuseStep 1085851 = 1628777) B1628777
theorem B1086203 : Blo 1084620 1086203 := bstep (se 1 (by rfl) ⟨814652, by rfl⟩ : syracuseStep 1086203 = 1629305) B1629305
theorem B9900857 : Blo 1084620 9900857 := bstep (se 2 (by rfl) ⟨3712821, by rfl⟩ : syracuseStep 9900857 = 7425643) B7425643
theorem B1086271 : Blo 1084620 1086271 := bstep (se 1 (by rfl) ⟨814703, by rfl⟩ : syracuseStep 1086271 = 1629407) B1629407
theorem B1086299 : Blo 1084620 1086299 := bstep (se 1 (by rfl) ⟨814724, by rfl⟩ : syracuseStep 1086299 = 1629449) B1629449
theorem B1086367 : Blo 1084620 1086367 := bstep (se 1 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 1086367 = 1629551) B1629551
theorem B1086447 : Blo 1084620 1086447 := bstep (se 1 (by rfl) ⟨814835, by rfl⟩ : syracuseStep 1086447 = 1629671) B1629671
theorem B1086535 : Blo 1084620 1086535 := bstep (se 1 (by rfl) ⟨814901, by rfl⟩ : syracuseStep 1086535 = 1629803) B1629803
theorem B1086619 : Blo 1084620 1086619 := bstep (se 1 (by rfl) ⟨814964, by rfl⟩ : syracuseStep 1086619 = 1629929) B1629929
theorem B1086715 : Blo 1084620 1086715 := bstep (se 1 (by rfl) ⟨815036, by rfl⟩ : syracuseStep 1086715 = 1630073) B1630073
theorem B1086783 : Blo 1084620 1086783 := bstep (se 1 (by rfl) ⟨815087, by rfl⟩ : syracuseStep 1086783 = 1630175) B1630175
theorem B1545583 : Blo 1084620 1545583 := bstep (se 1 (by rfl) ⟨1159187, by rfl⟩ : syracuseStep 1545583 = 2318375) B2318375
theorem B3478895 : Blo 1084620 3478895 := bstep (se 1 (by rfl) ⟨2609171, by rfl⟩ : syracuseStep 3478895 = 5218343) B5218343
theorem B1086951 : Blo 1084620 1086951 := bstep (se 1 (by rfl) ⟨815213, by rfl⟩ : syracuseStep 1086951 = 1630427) B1630427
theorem B1086959 : Blo 1084620 1086959 := bstep (se 1 (by rfl) ⟨815219, by rfl⟩ : syracuseStep 1086959 = 1630439) B1630439
theorem B1087067 : Blo 1084620 1087067 := bstep (se 1 (by rfl) ⟨815300, by rfl⟩ : syracuseStep 1087067 = 1630601) B1630601
theorem B1087131 : Blo 1084620 1087131 := bstep (se 1 (by rfl) ⟨815348, by rfl⟩ : syracuseStep 1087131 = 1630697) B1630697
theorem B1087215 : Blo 1084620 1087215 := bstep (se 1 (by rfl) ⟨815411, by rfl⟩ : syracuseStep 1087215 = 1630823) B1630823
theorem B1087303 : Blo 1084620 1087303 := bstep (se 1 (by rfl) ⟨815477, by rfl⟩ : syracuseStep 1087303 = 1630955) B1630955
theorem B1087323 : Blo 1084620 1087323 := bstep (se 1 (by rfl) ⟨815492, by rfl⟩ : syracuseStep 1087323 = 1630985) B1630985
theorem B1087391 : Blo 1084620 1087391 := bstep (se 1 (by rfl) ⟨815543, by rfl⟩ : syracuseStep 1087391 = 1631087) B1631087
theorem B7837661 : Blo 1084620 7837661 := bstep (se 3 (by rfl) ⟨1469561, by rfl⟩ : syracuseStep 7837661 = 2939123) B2939123
theorem B1087559 : Blo 1084620 1087559 := bstep (se 1 (by rfl) ⟨815669, by rfl⟩ : syracuseStep 1087559 = 1631339) B1631339
theorem B9279683 : Blo 1084620 9279683 := bstep (se 1 (by rfl) ⟨6959762, by rfl⟩ : syracuseStep 9279683 = 13919525) B13919525
theorem B1087719 : Blo 1084620 1087719 := bstep (se 1 (by rfl) ⟨815789, by rfl⟩ : syracuseStep 1087719 = 1631579) B1631579
theorem B1087903 : Blo 1084620 1087903 := bstep (se 1 (by rfl) ⟨815927, by rfl⟩ : syracuseStep 1087903 = 1631855) B1631855
theorem B1087951 : Blo 1084620 1087951 := bstep (se 1 (by rfl) ⟨815963, by rfl⟩ : syracuseStep 1087951 = 1631927) B1631927
theorem B1087975 : Blo 1084620 1087975 := bstep (se 1 (by rfl) ⟨815981, by rfl⟩ : syracuseStep 1087975 = 1631963) B1631963
theorem B4954625 : Blo 1084620 4954625 := bstep (se 2 (by rfl) ⟨1857984, by rfl⟩ : syracuseStep 4954625 = 3715969) B3715969
theorem B1088091 : Blo 1084620 1088091 := bstep (se 1 (by rfl) ⟨816068, by rfl⟩ : syracuseStep 1088091 = 1632137) B1632137
theorem B40245893 : Blo 1084620 40245893 := bstep (se 4 (by rfl) ⟨3773052, by rfl⟩ : syracuseStep 40245893 = 7546105) B7546105
theorem B1088159 : Blo 1084620 1088159 := bstep (se 1 (by rfl) ⟨816119, by rfl⟩ : syracuseStep 1088159 = 1632239) B1632239
theorem B10427069 : Blo 1084620 10427069 := bstep (se 3 (by rfl) ⟨1955075, by rfl⟩ : syracuseStep 10427069 = 3910151) B3910151
theorem B20126483 : Blo 1084620 20126483 := bstep (se 1 (by rfl) ⟨15094862, by rfl⟩ : syracuseStep 20126483 = 30189725) B30189725
theorem B1088327 : Blo 1084620 1088327 := bstep (se 1 (by rfl) ⟨816245, by rfl⟩ : syracuseStep 1088327 = 1632491) B1632491
theorem B1088367 : Blo 1084620 1088367 := bstep (se 1 (by rfl) ⟨816275, by rfl⟩ : syracuseStep 1088367 = 1632551) B1632551
theorem B1088423 : Blo 1084620 1088423 := bstep (se 1 (by rfl) ⟨816317, by rfl⟩ : syracuseStep 1088423 = 1632635) B1632635
theorem B1088603 : Blo 1084620 1088603 := bstep (se 1 (by rfl) ⟨816452, by rfl⟩ : syracuseStep 1088603 = 1632905) B1632905
theorem B12524867 : Blo 1084620 12524867 := bstep (se 1 (by rfl) ⟨9393650, by rfl⟩ : syracuseStep 12524867 = 18787301) B18787301
theorem B8265401 : Blo 1084620 8265401 := bstep (se 2 (by rfl) ⟨3099525, by rfl⟩ : syracuseStep 8265401 = 6199051) B6199051
theorem B1220863 : Blo 1084620 1220863 := bstep (se 1 (by rfl) ⟨915647, by rfl⟩ : syracuseStep 1220863 = 1831295) B1831295
theorem B5579207 : Blo 1084620 5579207 := bstep (se 1 (by rfl) ⟨4184405, by rfl⟩ : syracuseStep 5579207 = 8368811) B8368811
theorem B35267015 : Blo 1084620 35267015 := bstep (se 1 (by rfl) ⟨26450261, by rfl⟩ : syracuseStep 35267015 = 52900523) B52900523
theorem B1221151 : Blo 1084620 1221151 := bstep (se 1 (by rfl) ⟨915863, by rfl⟩ : syracuseStep 1221151 = 1831727) B1831727
theorem B3088979 : Blo 1084620 3088979 := bstep (se 1 (by rfl) ⟨2316734, by rfl⟩ : syracuseStep 3088979 = 4633469) B4633469
theorem B8266373 : Blo 1084620 8266373 := bstep (se 4 (by rfl) ⟨774972, by rfl⟩ : syracuseStep 8266373 = 1549945) B1549945
theorem B1221799 : Blo 1084620 1221799 := bstep (se 1 (by rfl) ⟨916349, by rfl⟩ : syracuseStep 1221799 = 1832699) B1832699
theorem B40740353 : Blo 1084620 40740353 := bstep (se 2 (by rfl) ⟨15277632, by rfl⟩ : syracuseStep 40740353 = 30555265) B30555265
theorem B1222591 : Blo 1084620 1222591 := bstep (se 1 (by rfl) ⟨916943, by rfl⟩ : syracuseStep 1222591 = 1833887) B1833887
theorem B4466735 : Blo 1084620 4466735 := bstep (se 1 (by rfl) ⟨3350051, by rfl⟩ : syracuseStep 4466735 = 6700103) B6700103
theorem B1222879 : Blo 1084620 1222879 := bstep (se 1 (by rfl) ⟨917159, by rfl⟩ : syracuseStep 1222879 = 1834319) B1834319
theorem B17639795 : Blo 1084620 17639795 := bstep (se 1 (by rfl) ⟨13229846, by rfl⟩ : syracuseStep 17639795 = 26459693) B26459693
theorem B3975761 : Blo 1084620 3975761 := bstep (se 2 (by rfl) ⟨1490910, by rfl⟩ : syracuseStep 3975761 = 2981821) B2981821
theorem B7154639 : Blo 1084620 7154639 := bstep (se 1 (by rfl) ⟨5365979, by rfl⟩ : syracuseStep 7154639 = 10731959) B10731959
theorem B4402151 : Blo 1084620 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B5221417 : Blo 1084620 5221417 := bstep (se 2 (by rfl) ⟨1958031, by rfl⟩ : syracuseStep 5221417 = 3916063) B3916063
theorem B1223743 : Blo 1084620 1223743 := bstep (se 1 (by rfl) ⟨917807, by rfl⟩ : syracuseStep 1223743 = 1835615) B1835615
theorem B4238611 : Blo 1084620 4238611 := bstep (se 1 (by rfl) ⟨3178958, by rfl⟩ : syracuseStep 4238611 = 6357917) B6357917
theorem B8236727 : Blo 1084620 8236727 := bstep (se 1 (by rfl) ⟨6177545, by rfl⟩ : syracuseStep 8236727 = 12355091) B12355091
theorem B1322815 : Blo 1084620 1322815 := bstep (se 1 (by rfl) ⟨992111, by rfl⟩ : syracuseStep 1322815 = 1984223) B1984223
theorem B4633145 : Blo 1084620 4633145 := bstep (se 2 (by rfl) ⟨1737429, by rfl⟩ : syracuseStep 4633145 = 3474859) B3474859
theorem B5026367 : Blo 1084620 5026367 := bstep (se 1 (by rfl) ⟨3769775, by rfl⟩ : syracuseStep 5026367 = 7539551) B7539551
theorem B6599333 : Blo 1084620 6599333 := bstep (se 4 (by rfl) ⟨618687, by rfl⟩ : syracuseStep 6599333 = 1237375) B1237375
theorem B5878595 : Blo 1084620 5878595 := bstep (se 1 (by rfl) ⟨4408946, by rfl⟩ : syracuseStep 5878595 = 8817893) B8817893
theorem B8238185 : Blo 1084620 8238185 := bstep (se 2 (by rfl) ⟨3089319, by rfl⟩ : syracuseStep 8238185 = 6178639) B6178639
theorem B1160443 : Blo 1084620 1160443 := bstep (se 1 (by rfl) ⟨870332, by rfl⟩ : syracuseStep 1160443 = 1740665) B1740665
theorem B3094013 : Blo 1084620 3094013 := bstep (se 3 (by rfl) ⟨580127, by rfl⟩ : syracuseStep 3094013 = 1160255) B1160255
theorem B1193563 : Blo 1084620 1193563 := bstep (se 1 (by rfl) ⟨895172, by rfl⟩ : syracuseStep 1193563 = 1790345) B1790345
theorem B41727959 : Blo 1084620 41727959 := bstep (se 1 (by rfl) ⟨31295969, by rfl⟩ : syracuseStep 41727959 = 62591939) B62591939
theorem B3094537 : Blo 1084620 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B4635143 : Blo 1084620 4635143 := bstep (se 1 (by rfl) ⟨3476357, by rfl⟩ : syracuseStep 4635143 = 6952715) B6952715
theorem B5225147 : Blo 1084620 5225147 := bstep (se 1 (by rfl) ⟨3918860, by rfl⟩ : syracuseStep 5225147 = 7837721) B7837721
theorem B2440619 : Blo 1084620 2440619 := bstep (se 1 (by rfl) ⟨1830464, by rfl⟩ : syracuseStep 2440619 = 3660929) B3660929
theorem B2440655 : Blo 1084620 2440655 := bstep (se 1 (by rfl) ⟨1830491, by rfl⟩ : syracuseStep 2440655 = 3660983) B3660983
theorem B7159403 : Blo 1084620 7159403 := bstep (se 1 (by rfl) ⟨5369552, by rfl⟩ : syracuseStep 7159403 = 10739105) B10739105
theorem B2473703 : Blo 1084620 2473703 := bstep (se 1 (by rfl) ⟨1855277, by rfl⟩ : syracuseStep 2473703 = 3710555) B3710555
theorem B6602519 : Blo 1084620 6602519 := bstep (se 1 (by rfl) ⟨4951889, by rfl⟩ : syracuseStep 6602519 = 9903779) B9903779
theorem B2441159 : Blo 1084620 2441159 := bstep (se 1 (by rfl) ⟨1830869, by rfl⟩ : syracuseStep 2441159 = 3661739) B3661739
theorem B4636919 : Blo 1084620 4636919 := bstep (se 1 (by rfl) ⟨3477689, by rfl⟩ : syracuseStep 4636919 = 6955379) B6955379
theorem B2441465 : Blo 1084620 2441465 := bstep (se 2 (by rfl) ⟨915549, by rfl⟩ : syracuseStep 2441465 = 1831099) B1831099
theorem B2441519 : Blo 1084620 2441519 := bstep (se 1 (by rfl) ⟨1831139, by rfl⟩ : syracuseStep 2441519 = 3662279) B3662279
theorem B9421289 : Blo 1084620 9421289 := bstep (se 2 (by rfl) ⟨3532983, by rfl⟩ : syracuseStep 9421289 = 7065967) B7065967
theorem B2441735 : Blo 1084620 2441735 := bstep (se 1 (by rfl) ⟨1831301, by rfl⟩ : syracuseStep 2441735 = 3662603) B3662603
theorem B3916295 : Blo 1084620 3916295 := bstep (se 1 (by rfl) ⟨2937221, by rfl⟩ : syracuseStep 3916295 = 5874443) B5874443
theorem B2441915 : Blo 1084620 2441915 := bstep (se 1 (by rfl) ⟨1831436, by rfl⟩ : syracuseStep 2441915 = 3662873) B3662873
theorem B3097385 : Blo 1084620 3097385 := bstep (se 2 (by rfl) ⟨1161519, by rfl⟩ : syracuseStep 3097385 = 2323039) B2323039
theorem B5227375 : Blo 1084620 5227375 := bstep (se 1 (by rfl) ⟨3920531, by rfl⟩ : syracuseStep 5227375 = 7841063) B7841063
theorem B2442347 : Blo 1084620 2442347 := bstep (se 1 (by rfl) ⟨1831760, by rfl⟩ : syracuseStep 2442347 = 3663521) B3663521
theorem B4637807 : Blo 1084620 4637807 := bstep (se 1 (by rfl) ⟨3478355, by rfl⟩ : syracuseStep 4637807 = 6956711) B6956711
theorem B150815915 : Blo 1084620 150815915 := bstep (se 1 (by rfl) ⟨113111936, by rfl⟩ : syracuseStep 150815915 = 226223873) B226223873
theorem B2442815 : Blo 1084620 2442815 := bstep (se 1 (by rfl) ⟨1832111, by rfl⟩ : syracuseStep 2442815 = 3664223) B3664223
theorem B60311141 : Blo 1084620 60311141 := bstep (se 4 (by rfl) ⟨5654169, by rfl⟩ : syracuseStep 60311141 = 11308339) B11308339
theorem B2442923 : Blo 1084620 2442923 := bstep (se 1 (by rfl) ⟨1832192, by rfl⟩ : syracuseStep 2442923 = 3664385) B3664385
theorem B38127395 : Blo 1084620 38127395 := bstep (se 1 (by rfl) ⟨28595546, by rfl⟩ : syracuseStep 38127395 = 57191093) B57191093
theorem B2443247 : Blo 1084620 2443247 := bstep (se 1 (by rfl) ⟨1832435, by rfl⟩ : syracuseStep 2443247 = 3664871) B3664871
theorem B2443463 : Blo 1084620 2443463 := bstep (se 1 (by rfl) ⟨1832597, by rfl⟩ : syracuseStep 2443463 = 3665195) B3665195
theorem B6965527 : Blo 1084620 6965527 := bstep (se 1 (by rfl) ⟨5224145, by rfl⟩ : syracuseStep 6965527 = 10448291) B10448291
theorem B2443643 : Blo 1084620 2443643 := bstep (se 1 (by rfl) ⟨1832732, by rfl⟩ : syracuseStep 2443643 = 3665465) B3665465
theorem B2443913 : Blo 1084620 2443913 := bstep (se 2 (by rfl) ⟨916467, by rfl⟩ : syracuseStep 2443913 = 1832935) B1832935
theorem B2444201 : Blo 1084620 2444201 := bstep (se 2 (by rfl) ⟨916575, by rfl⟩ : syracuseStep 2444201 = 1833151) B1833151
theorem B3099617 : Blo 1084620 3099617 := bstep (se 2 (by rfl) ⟨1162356, by rfl⟩ : syracuseStep 3099617 = 2324713) B2324713
theorem B22301729 : Blo 1084620 22301729 := bstep (se 2 (by rfl) ⟨8363148, by rfl⟩ : syracuseStep 22301729 = 16726297) B16726297
theorem B3919265 : Blo 1084620 3919265 := bstep (se 2 (by rfl) ⟨1469724, by rfl⟩ : syracuseStep 3919265 = 2939449) B2939449
theorem B2444903 : Blo 1084620 2444903 := bstep (se 1 (by rfl) ⟨1833677, by rfl⟩ : syracuseStep 2444903 = 3667355) B3667355
theorem B2445407 : Blo 1084620 2445407 := bstep (se 1 (by rfl) ⟨1834055, by rfl⟩ : syracuseStep 2445407 = 3668111) B3668111
theorem B9294203 : Blo 1084620 9294203 := bstep (se 1 (by rfl) ⟨6970652, by rfl⟩ : syracuseStep 9294203 = 13941305) B13941305
theorem B18567629 : Blo 1084620 18567629 := bstep (se 3 (by rfl) ⟨3481430, by rfl⟩ : syracuseStep 18567629 = 6962861) B6962861
theorem B11751905 : Blo 1084620 11751905 := bstep (se 2 (by rfl) ⟨4406964, by rfl⟩ : syracuseStep 11751905 = 8813929) B8813929
theorem B2446163 : Blo 1084620 2446163 := bstep (se 1 (by rfl) ⟨1834622, by rfl⟩ : syracuseStep 2446163 = 3669245) B3669245
theorem B1626971 : Blo 1084620 1626971 := bstep (se 1 (by rfl) ⟨1220228, by rfl⟩ : syracuseStep 1626971 = 2440457) B2440457
theorem B1627433 : Blo 1084620 1627433 := bstep (se 2 (by rfl) ⟨610287, by rfl⟩ : syracuseStep 1627433 = 1220575) B1220575
theorem B2446703 : Blo 1084620 2446703 := bstep (se 1 (by rfl) ⟨1835027, by rfl⟩ : syracuseStep 2446703 = 3670055) B3670055
theorem B1627631 : Blo 1084620 1627631 := bstep (se 1 (by rfl) ⟨1220723, by rfl⟩ : syracuseStep 1627631 = 2441447) B2441447
theorem B4118303 : Blo 1084620 4118303 := bstep (se 1 (by rfl) ⟨3088727, by rfl⟩ : syracuseStep 4118303 = 6177455) B6177455
theorem B4642591 : Blo 1084620 4642591 := bstep (se 1 (by rfl) ⟨3481943, by rfl⟩ : syracuseStep 4642591 = 6963887) B6963887
theorem B2447135 : Blo 1084620 2447135 := bstep (se 1 (by rfl) ⟨1835351, by rfl⟩ : syracuseStep 2447135 = 3670703) B3670703
theorem B3299143 : Blo 1084620 3299143 := bstep (se 1 (by rfl) ⟨2474357, by rfl⟩ : syracuseStep 3299143 = 4948715) B4948715
theorem B1628027 : Blo 1084620 1628027 := bstep (se 1 (by rfl) ⟨1221020, by rfl⟩ : syracuseStep 1628027 = 2442041) B2442041
theorem B1628063 : Blo 1084620 1628063 := bstep (se 1 (by rfl) ⟨1221047, by rfl⟩ : syracuseStep 1628063 = 2442095) B2442095
theorem B2447351 : Blo 1084620 2447351 := bstep (se 1 (by rfl) ⟨1835513, by rfl⟩ : syracuseStep 2447351 = 3671027) B3671027
theorem B1628297 : Blo 1084620 1628297 := bstep (se 2 (by rfl) ⟨610611, by rfl⟩ : syracuseStep 1628297 = 1221223) B1221223
theorem B1628447 : Blo 1084620 1628447 := bstep (se 1 (by rfl) ⟨1221335, by rfl⟩ : syracuseStep 1628447 = 2442671) B2442671
theorem B2447711 : Blo 1084620 2447711 := bstep (se 1 (by rfl) ⟨1835783, by rfl⟩ : syracuseStep 2447711 = 3671567) B3671567
theorem B5495201 : Blo 1084620 5495201 := bstep (se 2 (by rfl) ⟨2060700, by rfl⟩ : syracuseStep 5495201 = 4121401) B4121401
theorem B3135905 : Blo 1084620 3135905 := bstep (se 2 (by rfl) ⟨1175964, by rfl⟩ : syracuseStep 3135905 = 2351929) B2351929
theorem B4118971 : Blo 1084620 4118971 := bstep (se 1 (by rfl) ⟨3089228, by rfl⟩ : syracuseStep 4118971 = 6178457) B6178457
theorem B1628999 : Blo 1084620 1628999 := bstep (se 1 (by rfl) ⟨1221749, by rfl⟩ : syracuseStep 1628999 = 2443499) B2443499
theorem B2448251 : Blo 1084620 2448251 := bstep (se 1 (by rfl) ⟨1836188, by rfl⟩ : syracuseStep 2448251 = 3672377) B3672377
theorem B2448431 : Blo 1084620 2448431 := bstep (se 1 (by rfl) ⟨1836323, by rfl⟩ : syracuseStep 2448431 = 3672647) B3672647
theorem B2088263 : Blo 1084620 2088263 := bstep (se 1 (by rfl) ⟨1566197, by rfl⟩ : syracuseStep 2088263 = 3132395) B3132395
theorem B13917521 : Blo 1084620 13917521 := bstep (se 2 (by rfl) ⟨5219070, by rfl⟩ : syracuseStep 13917521 = 10438141) B10438141
theorem B2481785 : Blo 1084620 2481785 := bstep (se 2 (by rfl) ⟨930669, by rfl⟩ : syracuseStep 2481785 = 1861339) B1861339
theorem B1629863 : Blo 1084620 1629863 := bstep (se 1 (by rfl) ⟨1222397, by rfl⟩ : syracuseStep 1629863 = 2444795) B2444795
theorem B2449115 : Blo 1084620 2449115 := bstep (se 1 (by rfl) ⟨1836836, by rfl⟩ : syracuseStep 2449115 = 3673673) B3673673
theorem B1629983 : Blo 1084620 1629983 := bstep (se 1 (by rfl) ⟨1222487, by rfl⟩ : syracuseStep 1629983 = 2444975) B2444975
theorem B2449385 : Blo 1084620 2449385 := bstep (se 2 (by rfl) ⟨918519, by rfl⟩ : syracuseStep 2449385 = 1837039) B1837039
theorem B1630415 : Blo 1084620 1630415 := bstep (se 1 (by rfl) ⟨1222811, by rfl⟩ : syracuseStep 1630415 = 2445623) B2445623
theorem B1630463 : Blo 1084620 1630463 := bstep (se 1 (by rfl) ⟨1222847, by rfl⟩ : syracuseStep 1630463 = 2445695) B2445695
theorem B4645583 : Blo 1084620 4645583 := bstep (se 1 (by rfl) ⟨3484187, by rfl⟩ : syracuseStep 4645583 = 6968375) B6968375
theorem B1303327 : Blo 1084620 1303327 := bstep (se 1 (by rfl) ⟨977495, by rfl⟩ : syracuseStep 1303327 = 1954991) B1954991
theorem B5497631 : Blo 1084620 5497631 := bstep (se 1 (by rfl) ⟨4123223, by rfl⟩ : syracuseStep 5497631 = 8246447) B8246447
theorem B6185929 : Blo 1084620 6185929 := bstep (se 2 (by rfl) ⟨2319723, by rfl⟩ : syracuseStep 6185929 = 4639447) B4639447
theorem B1631279 : Blo 1084620 1631279 := bstep (se 1 (by rfl) ⟨1223459, by rfl⟩ : syracuseStep 1631279 = 2446919) B2446919
theorem B1303663 : Blo 1084620 1303663 := bstep (se 1 (by rfl) ⟨977747, by rfl⟩ : syracuseStep 1303663 = 1955495) B1955495
theorem B1631399 : Blo 1084620 1631399 := bstep (se 1 (by rfl) ⟨1223549, by rfl⟩ : syracuseStep 1631399 = 2447099) B2447099
theorem B2319673 : Blo 1084620 2319673 := bstep (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) B1739755
theorem B9266561 : Blo 1084620 9266561 := bstep (se 2 (by rfl) ⟨3474960, by rfl⟩ : syracuseStep 9266561 = 6949921) B6949921
theorem B1631771 : Blo 1084620 1631771 := bstep (se 1 (by rfl) ⟨1223828, by rfl⟩ : syracuseStep 1631771 = 2447657) B2447657
theorem B4187965 : Blo 1084620 4187965 := bstep (se 3 (by rfl) ⟨785243, by rfl⟩ : syracuseStep 4187965 = 1570487) B1570487
theorem B1632155 : Blo 1084620 1632155 := bstep (se 1 (by rfl) ⟨1224116, by rfl⟩ : syracuseStep 1632155 = 2448233) B2448233
theorem B1632191 : Blo 1084620 1632191 := bstep (se 1 (by rfl) ⟨1224143, by rfl⟩ : syracuseStep 1632191 = 2448287) B2448287
theorem B20867057 : Blo 1084620 20867057 := bstep (se 2 (by rfl) ⟨7825146, by rfl⟩ : syracuseStep 20867057 = 15650293) B15650293
theorem B6973523 : Blo 1084620 6973523 := bstep (se 1 (by rfl) ⟨5230142, by rfl⟩ : syracuseStep 6973523 = 10460285) B10460285
theorem B4188257 : Blo 1084620 4188257 := bstep (se 2 (by rfl) ⟨1570596, by rfl⟩ : syracuseStep 4188257 = 3141193) B3141193
theorem B1632377 : Blo 1084620 1632377 := bstep (se 2 (by rfl) ⟨612141, by rfl⟩ : syracuseStep 1632377 = 1224283) B1224283
theorem B1632761 : Blo 1084620 1632761 := bstep (se 2 (by rfl) ⟨612285, by rfl⟩ : syracuseStep 1632761 = 1224571) B1224571
theorem B1632815 : Blo 1084620 1632815 := bstep (se 1 (by rfl) ⟨1224611, by rfl⟩ : syracuseStep 1632815 = 2449223) B2449223
theorem B1305191 : Blo 1084620 1305191 := bstep (se 1 (by rfl) ⟨978893, by rfl⟩ : syracuseStep 1305191 = 1957787) B1957787
theorem B6613933 : Blo 1084620 6613933 := bstep (se 3 (by rfl) ⟨1240112, by rfl⟩ : syracuseStep 6613933 = 2480225) B2480225
theorem B107342779 : Blo 1084620 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B1305595 : Blo 1084620 1305595 := bstep (se 1 (by rfl) ⟨979196, by rfl⟩ : syracuseStep 1305595 = 1958393) B1958393
theorem B4123817 : Blo 1084620 4123817 := bstep (se 2 (by rfl) ⟨1546431, by rfl⟩ : syracuseStep 4123817 = 3092863) B3092863
theorem B4123831 : Blo 1084620 4123831 := bstep (se 1 (by rfl) ⟨3092873, by rfl⟩ : syracuseStep 4123831 = 6185747) B6185747
theorem B4124317 : Blo 1084620 4124317 := bstep (se 3 (by rfl) ⟨773309, by rfl⟩ : syracuseStep 4124317 = 1546619) B1546619
theorem B20082401 : Blo 1084620 20082401 := bstep (se 2 (by rfl) ⟨7530900, by rfl⟩ : syracuseStep 20082401 = 15061801) B15061801
theorem B15658829 : Blo 1084620 15658829 := bstep (se 3 (by rfl) ⟨2936030, by rfl⟩ : syracuseStep 15658829 = 5872061) B5872061
theorem B2748775 : Blo 1084620 2748775 := bstep (se 1 (by rfl) ⟨2061581, by rfl⟩ : syracuseStep 2748775 = 4123163) B4123163
theorem B3666383 : Blo 1084620 3666383 := bstep (se 1 (by rfl) ⟨2749787, by rfl⟩ : syracuseStep 3666383 = 5499575) B5499575
theorem B2061035 : Blo 1084620 2061035 := bstep (se 1 (by rfl) ⟨1545776, by rfl⟩ : syracuseStep 2061035 = 3091553) B3091553
theorem B2061065 : Blo 1084620 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B2061119 : Blo 1084620 2061119 := bstep (se 1 (by rfl) ⟨1545839, by rfl⟩ : syracuseStep 2061119 = 3091679) B3091679
theorem B2061263 : Blo 1084620 2061263 := bstep (se 1 (by rfl) ⟨1545947, by rfl⟩ : syracuseStep 2061263 = 3091895) B3091895
theorem B9270557 : Blo 1084620 9270557 := bstep (se 3 (by rfl) ⟨1738229, by rfl⟩ : syracuseStep 9270557 = 3476459) B3476459
theorem B1832591 : Blo 1084620 1832591 := bstep (se 1 (by rfl) ⟨1374443, by rfl⟩ : syracuseStep 1832591 = 2748887) B2748887
theorem B8812243 : Blo 1084620 8812243 := bstep (se 1 (by rfl) ⟨6609182, by rfl⟩ : syracuseStep 8812243 = 13218365) B13218365
theorem B2324303 : Blo 1084620 2324303 := bstep (se 1 (by rfl) ⟨1743227, by rfl⟩ : syracuseStep 2324303 = 3486455) B3486455
theorem B1374671 : Blo 1084620 1374671 := bstep (se 1 (by rfl) ⟨1031003, by rfl⟩ : syracuseStep 1374671 = 2062007) B2062007
theorem B1833563 : Blo 1084620 1833563 := bstep (se 1 (by rfl) ⟨1375172, by rfl⟩ : syracuseStep 1833563 = 2750345) B2750345
theorem B6191761 : Blo 1084620 6191761 := bstep (se 2 (by rfl) ⟨2321910, by rfl⟩ : syracuseStep 6191761 = 4643821) B4643821
theorem B3668705 : Blo 1084620 3668705 := bstep (se 2 (by rfl) ⟨1375764, by rfl⟩ : syracuseStep 3668705 = 2751529) B2751529
theorem B21429319 : Blo 1084620 21429319 := bstep (se 1 (by rfl) ⟨16071989, by rfl⟩ : syracuseStep 21429319 = 32143979) B32143979
theorem B2063465 : Blo 1084620 2063465 := bstep (se 2 (by rfl) ⟨773799, by rfl⟩ : syracuseStep 2063465 = 1547599) B1547599
theorem B1834447 : Blo 1084620 1834447 := bstep (se 1 (by rfl) ⟨1375835, by rfl⟩ : syracuseStep 1834447 = 2751671) B2751671
theorem B2751995 : Blo 1084620 2751995 := bstep (se 1 (by rfl) ⟨2063996, by rfl⟩ : syracuseStep 2751995 = 4127993) B4127993
theorem B3309167 : Blo 1084620 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B10714799 : Blo 1084620 10714799 := bstep (se 1 (by rfl) ⟨8036099, by rfl⟩ : syracuseStep 10714799 = 16072199) B16072199
theorem B3669839 : Blo 1084620 3669839 := bstep (se 1 (by rfl) ⟨2752379, by rfl⟩ : syracuseStep 3669839 = 5504759) B5504759
theorem B2752825 : Blo 1084620 2752825 := bstep (se 2 (by rfl) ⟨1032309, by rfl⟩ : syracuseStep 2752825 = 2064619) B2064619
theorem B5505407 : Blo 1084620 5505407 := bstep (se 1 (by rfl) ⟨4129055, by rfl⟩ : syracuseStep 5505407 = 8258111) B8258111
theorem B1835419 : Blo 1084620 1835419 := bstep (se 1 (by rfl) ⟨1376564, by rfl⟩ : syracuseStep 1835419 = 2753129) B2753129
theorem B1376671 : Blo 1084620 1376671 := bstep (se 1 (by rfl) ⟨1032503, by rfl⟩ : syracuseStep 1376671 = 2065007) B2065007
theorem B2064923 : Blo 1084620 2064923 := bstep (se 1 (by rfl) ⟨1548692, by rfl⟩ : syracuseStep 2064923 = 3097385) B3097385
theorem B1835831 : Blo 1084620 1835831 := bstep (se 1 (by rfl) ⟨1376873, by rfl⟩ : syracuseStep 1835831 = 2753747) B2753747
theorem B1737769 : Blo 1084620 1737769 := bstep (se 2 (by rfl) ⟨651663, by rfl⟩ : syracuseStep 1737769 = 1303327) B1303327
theorem B40207427 : Blo 1084620 40207427 := bstep (se 1 (by rfl) ⟨30155570, by rfl⟩ : syracuseStep 40207427 = 60311141) B60311141
theorem B4129967 : Blo 1084620 4129967 := bstep (se 1 (by rfl) ⟨3097475, by rfl⟩ : syracuseStep 4129967 = 6194951) B6194951
theorem B1738217 : Blo 1084620 1738217 := bstep (se 2 (by rfl) ⟨651831, by rfl⟩ : syracuseStep 1738217 = 1303663) B1303663
theorem B17598221 : Blo 1084620 17598221 := bstep (se 3 (by rfl) ⟨3299666, by rfl⟩ : syracuseStep 17598221 = 6599333) B6599333
theorem B1836911 : Blo 1084620 1836911 := bstep (se 1 (by rfl) ⟨1377683, by rfl⟩ : syracuseStep 1836911 = 2755367) B2755367
theorem B3671999 : Blo 1084620 3671999 := bstep (se 1 (by rfl) ⟨2753999, by rfl⟩ : syracuseStep 3671999 = 5507999) B5507999
theorem B2066411 : Blo 1084620 2066411 := bstep (se 1 (by rfl) ⟨1549808, by rfl⟩ : syracuseStep 2066411 = 3099617) B3099617
theorem B4130939 : Blo 1084620 4130939 := bstep (se 1 (by rfl) ⟨3098204, by rfl⟩ : syracuseStep 4130939 = 6196409) B6196409
theorem B8260055 : Blo 1084620 8260055 := bstep (se 1 (by rfl) ⟨6195041, by rfl⟩ : syracuseStep 8260055 = 12390083) B12390083
theorem B6196135 : Blo 1084620 6196135 := bstep (se 1 (by rfl) ⟨4647101, by rfl⟩ : syracuseStep 6196135 = 9294203) B9294203
theorem B1084647 : Blo 1084620 1084647 := bstep (se 1 (by rfl) ⟨813485, by rfl⟩ : syracuseStep 1084647 = 1626971) B1626971
theorem B1084955 : Blo 1084620 1084955 := bstep (se 1 (by rfl) ⟨813716, by rfl⟩ : syracuseStep 1084955 = 1627433) B1627433
theorem B1085087 : Blo 1084620 1085087 := bstep (se 1 (by rfl) ⟨813815, by rfl⟩ : syracuseStep 1085087 = 1627631) B1627631
theorem B8818577 : Blo 1084620 8818577 := bstep (se 2 (by rfl) ⟨3306966, by rfl⟩ : syracuseStep 8818577 = 6613933) B6613933
theorem B1085351 : Blo 1084620 1085351 := bstep (se 1 (by rfl) ⟨814013, by rfl⟩ : syracuseStep 1085351 = 1628027) B1628027
theorem B1085375 : Blo 1084620 1085375 := bstep (se 1 (by rfl) ⟨814031, by rfl⟩ : syracuseStep 1085375 = 1628063) B1628063
theorem B1740793 : Blo 1084620 1740793 := bstep (se 2 (by rfl) ⟨652797, by rfl⟩ : syracuseStep 1740793 = 1305595) B1305595
theorem B1085531 : Blo 1084620 1085531 := bstep (se 1 (by rfl) ⟨814148, by rfl⟩ : syracuseStep 1085531 = 1628297) B1628297
theorem B1085631 : Blo 1084620 1085631 := bstep (se 1 (by rfl) ⟨814223, by rfl⟩ : syracuseStep 1085631 = 1628447) B1628447
theorem B1085999 : Blo 1084620 1085999 := bstep (se 1 (by rfl) ⟨814499, by rfl⟩ : syracuseStep 1085999 = 1628999) B1628999
theorem B9278347 : Blo 1084620 9278347 := bstep (se 1 (by rfl) ⟨6958760, by rfl⟩ : syracuseStep 9278347 = 13917521) B13917521
theorem B1086575 : Blo 1084620 1086575 := bstep (se 1 (by rfl) ⟨814931, by rfl⟩ : syracuseStep 1086575 = 1629863) B1629863
theorem B5510267 : Blo 1084620 5510267 := bstep (se 1 (by rfl) ⟨4132700, by rfl⟩ : syracuseStep 5510267 = 8265401) B8265401
theorem B1086655 : Blo 1084620 1086655 := bstep (se 1 (by rfl) ⟨814991, by rfl⟩ : syracuseStep 1086655 = 1629983) B1629983
theorem B1086943 : Blo 1084620 1086943 := bstep (se 1 (by rfl) ⟨815207, by rfl⟩ : syracuseStep 1086943 = 1630415) B1630415
theorem B1086975 : Blo 1084620 1086975 := bstep (se 1 (by rfl) ⟨815231, by rfl⟩ : syracuseStep 1086975 = 1630463) B1630463
theorem B5510915 : Blo 1084620 5510915 := bstep (se 1 (by rfl) ⟨4133186, by rfl⟩ : syracuseStep 5510915 = 8266373) B8266373
theorem B1087519 : Blo 1084620 1087519 := bstep (se 1 (by rfl) ⟨815639, by rfl⟩ : syracuseStep 1087519 = 1631279) B1631279
theorem B1087599 : Blo 1084620 1087599 := bstep (se 1 (by rfl) ⟨815699, by rfl⟩ : syracuseStep 1087599 = 1631399) B1631399
theorem B1087847 : Blo 1084620 1087847 := bstep (se 1 (by rfl) ⟨815885, by rfl⟩ : syracuseStep 1087847 = 1631771) B1631771
theorem B1088103 : Blo 1084620 1088103 := bstep (se 1 (by rfl) ⟨816077, by rfl⟩ : syracuseStep 1088103 = 1632155) B1632155
theorem B1088127 : Blo 1084620 1088127 := bstep (se 1 (by rfl) ⟨816095, by rfl⟩ : syracuseStep 1088127 = 1632191) B1632191
theorem B2792171 : Blo 1084620 2792171 := bstep (se 1 (by rfl) ⟨2094128, by rfl⟩ : syracuseStep 2792171 = 4188257) B4188257
theorem B1088251 : Blo 1084620 1088251 := bstep (se 1 (by rfl) ⟨816188, by rfl⟩ : syracuseStep 1088251 = 1632377) B1632377
theorem B3480509 : Blo 1084620 3480509 := bstep (se 3 (by rfl) ⟨652595, by rfl⟩ : syracuseStep 3480509 = 1305191) B1305191
theorem B1547257 : Blo 1084620 1547257 := bstep (se 2 (by rfl) ⟨580221, by rfl⟩ : syracuseStep 1547257 = 1160443) B1160443
theorem B1088507 : Blo 1084620 1088507 := bstep (se 1 (by rfl) ⟨816380, by rfl⟩ : syracuseStep 1088507 = 1632761) B1632761
theorem B1088543 : Blo 1084620 1088543 := bstep (se 1 (by rfl) ⟨816407, by rfl⟩ : syracuseStep 1088543 = 1632815) B1632815
theorem B4398857 : Blo 1084620 4398857 := bstep (se 2 (by rfl) ⟨1649571, by rfl⟩ : syracuseStep 4398857 = 3299143) B3299143
theorem B3088763 : Blo 1084620 3088763 := bstep (se 1 (by rfl) ⟨2316572, by rfl⟩ : syracuseStep 3088763 = 4633145) B4633145
theorem B3350911 : Blo 1084620 3350911 := bstep (se 1 (by rfl) ⟨2513183, by rfl⟩ : syracuseStep 3350911 = 5026367) B5026367
theorem B1221727 : Blo 1084620 1221727 := bstep (se 1 (by rfl) ⟨916295, by rfl⟩ : syracuseStep 1221727 = 1832591) B1832591
theorem B46998629 : Blo 1084620 46998629 := bstep (se 4 (by rfl) ⟨4406121, by rfl⟩ : syracuseStep 46998629 = 8812243) B8812243
theorem B1549535 : Blo 1084620 1549535 := bstep (se 1 (by rfl) ⟨1162151, by rfl⟩ : syracuseStep 1549535 = 2324303) B2324303
theorem B3090095 : Blo 1084620 3090095 := bstep (se 1 (by rfl) ⟨2317571, by rfl⟩ : syracuseStep 3090095 = 4635143) B4635143
theorem B1222375 : Blo 1084620 1222375 := bstep (se 1 (by rfl) ⟨916781, by rfl⟩ : syracuseStep 1222375 = 1833563) B1833563
theorem B3483431 : Blo 1084620 3483431 := bstep (se 1 (by rfl) ⟨2612573, by rfl⟩ : syracuseStep 3483431 = 5225147) B5225147
theorem B17606717 : Blo 1084620 17606717 := bstep (se 3 (by rfl) ⟨3301259, by rfl⟩ : syracuseStep 17606717 = 6602519) B6602519
theorem B2206111 : Blo 1084620 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B1649135 : Blo 1084620 1649135 := bstep (se 1 (by rfl) ⟨1236851, by rfl⟩ : syracuseStep 1649135 = 2473703) B2473703
theorem B3091279 : Blo 1084620 3091279 := bstep (se 1 (by rfl) ⟨2318459, by rfl⟩ : syracuseStep 3091279 = 4636919) B4636919
theorem B21146777 : Blo 1084620 21146777 := bstep (se 2 (by rfl) ⟨7930041, by rfl⟩ : syracuseStep 21146777 = 15860083) B15860083
theorem B3091871 : Blo 1084620 3091871 := bstep (se 1 (by rfl) ⟨2318903, by rfl⟩ : syracuseStep 3091871 = 4637807) B4637807
theorem B100543943 : Blo 1084620 100543943 := bstep (se 1 (by rfl) ⟨75407957, by rfl⟩ : syracuseStep 100543943 = 150815915) B150815915
theorem B31338413 : Blo 1084620 31338413 := bstep (se 3 (by rfl) ⟨5875952, by rfl⟩ : syracuseStep 31338413 = 11751905) B11751905
theorem B6598675 : Blo 1084620 6598675 := bstep (se 1 (by rfl) ⟨4949006, by rfl⟩ : syracuseStep 6598675 = 9898013) B9898013
theorem B3092897 : Blo 1084620 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B5583953 : Blo 1084620 5583953 := bstep (se 2 (by rfl) ⟨2093982, by rfl⟩ : syracuseStep 5583953 = 4187965) B4187965
theorem B9287369 : Blo 1084620 9287369 := bstep (se 2 (by rfl) ⟨3482763, by rfl⟩ : syracuseStep 9287369 = 6965527) B6965527
theorem B6600571 : Blo 1084620 6600571 := bstep (se 1 (by rfl) ⟨4950428, by rfl⟩ : syracuseStep 6600571 = 9900857) B9900857
theorem B6961889 : Blo 1084620 6961889 := bstep (se 2 (by rfl) ⟨2610708, by rfl⟩ : syracuseStep 6961889 = 5221417) B5221417
theorem B13417655 : Blo 1084620 13417655 := bstep (se 1 (by rfl) ⟨10063241, by rfl⟩ : syracuseStep 13417655 = 20126483) B20126483
theorem B1392175 : Blo 1084620 1392175 := bstep (se 1 (by rfl) ⟨1044131, by rfl⟩ : syracuseStep 1392175 = 2088263) B2088263
theorem B1654523 : Blo 1084620 1654523 := bstep (se 1 (by rfl) ⟨1240892, by rfl⟩ : syracuseStep 1654523 = 2481785) B2481785
theorem B3719471 : Blo 1084620 3719471 := bstep (se 1 (by rfl) ⟨2789603, by rfl⟩ : syracuseStep 3719471 = 5579207) B5579207
theorem B23511343 : Blo 1084620 23511343 := bstep (se 1 (by rfl) ⟨17633507, by rfl⟩ : syracuseStep 23511343 = 35267015) B35267015
theorem B3097055 : Blo 1084620 3097055 := bstep (se 1 (by rfl) ⟨2322791, by rfl⟩ : syracuseStep 3097055 = 4645583) B4645583
theorem B6177707 : Blo 1084620 6177707 := bstep (se 1 (by rfl) ⟨4633280, by rfl⟩ : syracuseStep 6177707 = 9266561) B9266561
theorem B47039453 : Blo 1084620 47039453 := bstep (se 3 (by rfl) ⟨8819897, by rfl⟩ : syracuseStep 47039453 = 17639795) B17639795
theorem B13911371 : Blo 1084620 13911371 := bstep (se 1 (by rfl) ⟨10433528, by rfl⟩ : syracuseStep 13911371 = 20867057) B20867057
theorem B10602029 : Blo 1084620 10602029 := bstep (se 3 (by rfl) ⟨1987880, by rfl⟩ : syracuseStep 10602029 = 3975761) B3975761
theorem B27805517 : Blo 1084620 27805517 := bstep (se 3 (by rfl) ⟨5213534, by rfl⟩ : syracuseStep 27805517 = 10427069) B10427069
theorem B4769759 : Blo 1084620 4769759 := bstep (se 1 (by rfl) ⟨3577319, by rfl⟩ : syracuseStep 4769759 = 7154639) B7154639
theorem B2934767 : Blo 1084620 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B1591417 : Blo 1084620 1591417 := bstep (se 2 (by rfl) ⟨596781, by rfl⟩ : syracuseStep 1591417 = 1193563) B1193563
theorem B5491151 : Blo 1084620 5491151 := bstep (se 1 (by rfl) ⟨4118363, by rfl⟩ : syracuseStep 5491151 = 8236727) B8236727
theorem B13388267 : Blo 1084620 13388267 := bstep (se 1 (by rfl) ⟨10041200, by rfl⟩ : syracuseStep 13388267 = 20082401) B20082401
theorem B10439219 : Blo 1084620 10439219 := bstep (se 1 (by rfl) ⟨7829414, by rfl⟩ : syracuseStep 10439219 = 15658829) B15658829
theorem B2444255 : Blo 1084620 2444255 := bstep (se 1 (by rfl) ⟨1833191, by rfl⟩ : syracuseStep 2444255 = 3666383) B3666383
theorem B3919063 : Blo 1084620 3919063 := bstep (se 1 (by rfl) ⟨2939297, by rfl⟩ : syracuseStep 3919063 = 5878595) B5878595
theorem B5491961 : Blo 1084620 5491961 := bstep (se 2 (by rfl) ⟨2059485, by rfl⟩ : syracuseStep 5491961 = 4118971) B4118971
theorem B5492123 : Blo 1084620 5492123 := bstep (se 1 (by rfl) ⟨4119092, by rfl⟩ : syracuseStep 5492123 = 8238185) B8238185
theorem B6180371 : Blo 1084620 6180371 := bstep (se 1 (by rfl) ⟨4635278, by rfl⟩ : syracuseStep 6180371 = 9270557) B9270557
theorem B2445803 : Blo 1084620 2445803 := bstep (se 1 (by rfl) ⟨1834352, by rfl⟩ : syracuseStep 2445803 = 3668705) B3668705
theorem B2445929 : Blo 1084620 2445929 := bstep (se 2 (by rfl) ⟨917223, by rfl⟩ : syracuseStep 2445929 = 1834447) B1834447
theorem B1627079 : Blo 1084620 1627079 := bstep (se 1 (by rfl) ⟨1220309, by rfl⟩ : syracuseStep 1627079 = 2440619) B2440619
theorem B1627103 : Blo 1084620 1627103 := bstep (se 1 (by rfl) ⟨1220327, by rfl⟩ : syracuseStep 1627103 = 2440655) B2440655
theorem B4772935 : Blo 1084620 4772935 := bstep (se 1 (by rfl) ⟨3579701, by rfl⟩ : syracuseStep 4772935 = 7159403) B7159403
theorem B2446559 : Blo 1084620 2446559 := bstep (se 1 (by rfl) ⟨1834919, by rfl⟩ : syracuseStep 2446559 = 3669839) B3669839
theorem B1627439 : Blo 1084620 1627439 := bstep (se 1 (by rfl) ⟨1220579, by rfl⟩ : syracuseStep 1627439 = 2441159) B2441159
theorem B1627643 : Blo 1084620 1627643 := bstep (se 1 (by rfl) ⟨1220732, by rfl⟩ : syracuseStep 1627643 = 2441465) B2441465
theorem B1627679 : Blo 1084620 1627679 := bstep (se 1 (by rfl) ⟨1220759, by rfl⟩ : syracuseStep 1627679 = 2441519) B2441519
theorem B14112391 : Blo 1084620 14112391 := bstep (se 1 (by rfl) ⟨10584293, by rfl⟩ : syracuseStep 14112391 = 21168587) B21168587
theorem B2446991 : Blo 1084620 2446991 := bstep (se 1 (by rfl) ⟨1835243, by rfl⟩ : syracuseStep 2446991 = 3670487) B3670487
theorem B6280859 : Blo 1084620 6280859 := bstep (se 1 (by rfl) ⟨4710644, by rfl⟩ : syracuseStep 6280859 = 9421289) B9421289
theorem B1627817 : Blo 1084620 1627817 := bstep (se 2 (by rfl) ⟨610431, by rfl⟩ : syracuseStep 1627817 = 1220863) B1220863
theorem B1627823 : Blo 1084620 1627823 := bstep (se 1 (by rfl) ⟨1220867, by rfl⟩ : syracuseStep 1627823 = 2441735) B2441735
theorem B2610863 : Blo 1084620 2610863 := bstep (se 1 (by rfl) ⟨1958147, by rfl⟩ : syracuseStep 2610863 = 3916295) B3916295
theorem B2447081 : Blo 1084620 2447081 := bstep (se 2 (by rfl) ⟨917655, by rfl⟩ : syracuseStep 2447081 = 1835311) B1835311
theorem B1627943 : Blo 1084620 1627943 := bstep (se 1 (by rfl) ⟨1220957, by rfl⟩ : syracuseStep 1627943 = 2441915) B2441915
theorem B1628201 : Blo 1084620 1628201 := bstep (se 2 (by rfl) ⟨610575, by rfl⟩ : syracuseStep 1628201 = 1221151) B1221151
theorem B1628231 : Blo 1084620 1628231 := bstep (se 1 (by rfl) ⟨1221173, by rfl⟩ : syracuseStep 1628231 = 2442347) B2442347
theorem B6183287 : Blo 1084620 6183287 := bstep (se 1 (by rfl) ⟨4637465, by rfl⟩ : syracuseStep 6183287 = 9274931) B9274931
theorem B1628543 : Blo 1084620 1628543 := bstep (se 1 (by rfl) ⟨1221407, by rfl⟩ : syracuseStep 1628543 = 2442815) B2442815
theorem B1628615 : Blo 1084620 1628615 := bstep (se 1 (by rfl) ⟨1221461, by rfl⟩ : syracuseStep 1628615 = 2442923) B2442923
theorem B6969833 : Blo 1084620 6969833 := bstep (se 2 (by rfl) ⟨2613687, by rfl⟩ : syracuseStep 6969833 = 5227375) B5227375
theorem B8247905 : Blo 1084620 8247905 := bstep (se 2 (by rfl) ⟨3092964, by rfl⟩ : syracuseStep 8247905 = 6185929) B6185929
theorem B1628831 : Blo 1084620 1628831 := bstep (se 1 (by rfl) ⟨1221623, by rfl⟩ : syracuseStep 1628831 = 2443247) B2443247
theorem B1628975 : Blo 1084620 1628975 := bstep (se 1 (by rfl) ⟨1221731, by rfl⟩ : syracuseStep 1628975 = 2443463) B2443463
theorem B1629065 : Blo 1084620 1629065 := bstep (se 2 (by rfl) ⟨610899, by rfl⟩ : syracuseStep 1629065 = 1221799) B1221799
theorem B1629095 : Blo 1084620 1629095 := bstep (se 1 (by rfl) ⟨1221821, by rfl⟩ : syracuseStep 1629095 = 2443643) B2443643
theorem B1629275 : Blo 1084620 1629275 := bstep (se 1 (by rfl) ⟨1221956, by rfl⟩ : syracuseStep 1629275 = 2443913) B2443913
theorem B1629467 : Blo 1084620 1629467 := bstep (se 1 (by rfl) ⟨1222100, by rfl⟩ : syracuseStep 1629467 = 2444201) B2444201
theorem B2448719 : Blo 1084620 2448719 := bstep (se 1 (by rfl) ⟨1836539, by rfl⟩ : syracuseStep 2448719 = 3673079) B3673079
theorem B14867819 : Blo 1084620 14867819 := bstep (se 1 (by rfl) ⟨11150864, by rfl⟩ : syracuseStep 14867819 = 22301729) B22301729
theorem B5496173 : Blo 1084620 5496173 := bstep (se 3 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 5496173 = 2061065) B2061065
theorem B2448809 : Blo 1084620 2448809 := bstep (se 2 (by rfl) ⟨918303, by rfl⟩ : syracuseStep 2448809 = 1836607) B1836607
theorem B7822817 : Blo 1084620 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B2612843 : Blo 1084620 2612843 := bstep (se 1 (by rfl) ⟨1959632, by rfl⟩ : syracuseStep 2612843 = 3919265) B3919265
theorem B1629935 : Blo 1084620 1629935 := bstep (se 1 (by rfl) ⟨1222451, by rfl⟩ : syracuseStep 1629935 = 2444903) B2444903
theorem B1630121 : Blo 1084620 1630121 := bstep (se 2 (by rfl) ⟨611295, by rfl⟩ : syracuseStep 1630121 = 1222591) B1222591
theorem B1630271 : Blo 1084620 1630271 := bstep (se 1 (by rfl) ⟨1222703, by rfl⟩ : syracuseStep 1630271 = 2445407) B2445407
theorem B1630505 : Blo 1084620 1630505 := bstep (se 2 (by rfl) ⟨611439, by rfl⟩ : syracuseStep 1630505 = 1222879) B1222879
theorem B12378419 : Blo 1084620 12378419 := bstep (se 1 (by rfl) ⟨9283814, by rfl⟩ : syracuseStep 12378419 = 18567629) B18567629
theorem B1630775 : Blo 1084620 1630775 := bstep (se 1 (by rfl) ⟨1223081, by rfl⟩ : syracuseStep 1630775 = 2446163) B2446163
theorem B2319263 : Blo 1084620 2319263 := bstep (se 1 (by rfl) ⟨1739447, by rfl⟩ : syracuseStep 2319263 = 3478895) B3478895
theorem B1631135 : Blo 1084620 1631135 := bstep (se 1 (by rfl) ⟨1223351, by rfl⟩ : syracuseStep 1631135 = 2446703) B2446703
theorem B2745535 : Blo 1084620 2745535 := bstep (se 1 (by rfl) ⟨2059151, by rfl⟩ : syracuseStep 2745535 = 4118303) B4118303
theorem B1631423 : Blo 1084620 1631423 := bstep (se 1 (by rfl) ⟨1223567, by rfl⟩ : syracuseStep 1631423 = 2447135) B2447135
theorem B143123705 : Blo 1084620 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B1631567 : Blo 1084620 1631567 := bstep (se 1 (by rfl) ⟨1223675, by rfl⟩ : syracuseStep 1631567 = 2447351) B2447351
theorem B1631657 : Blo 1084620 1631657 := bstep (se 2 (by rfl) ⟨611871, by rfl⟩ : syracuseStep 1631657 = 1223743) B1223743
theorem B6186455 : Blo 1084620 6186455 := bstep (se 1 (by rfl) ⟨4639841, by rfl⟩ : syracuseStep 6186455 = 9279683) B9279683
theorem B1631807 : Blo 1084620 1631807 := bstep (se 1 (by rfl) ⟨1223855, by rfl⟩ : syracuseStep 1631807 = 2447711) B2447711
theorem B5498441 : Blo 1084620 5498441 := bstep (se 2 (by rfl) ⟨2061915, by rfl⟩ : syracuseStep 5498441 = 4123831) B4123831
theorem B3663467 : Blo 1084620 3663467 := bstep (se 1 (by rfl) ⟨2747600, by rfl⟩ : syracuseStep 3663467 = 5495201) B5495201
theorem B2090603 : Blo 1084620 2090603 := bstep (se 1 (by rfl) ⟨1567952, by rfl⟩ : syracuseStep 2090603 = 3135905) B3135905
theorem B3303083 : Blo 1084620 3303083 := bstep (se 1 (by rfl) ⟨2477312, by rfl⟩ : syracuseStep 3303083 = 4954625) B4954625
theorem B26830595 : Blo 1084620 26830595 := bstep (se 1 (by rfl) ⟨20122946, by rfl⟩ : syracuseStep 26830595 = 40245893) B40245893
theorem B1632167 : Blo 1084620 1632167 := bstep (se 1 (by rfl) ⟨1224125, by rfl⟩ : syracuseStep 1632167 = 2448251) B2448251
theorem B1632287 : Blo 1084620 1632287 := bstep (se 1 (by rfl) ⟨1224215, by rfl⟩ : syracuseStep 1632287 = 2448431) B2448431
theorem B101673053 : Blo 1084620 101673053 := bstep (se 3 (by rfl) ⟨19063697, by rfl⟩ : syracuseStep 101673053 = 38127395) B38127395
theorem B5499089 : Blo 1084620 5499089 := bstep (se 2 (by rfl) ⟨2062158, by rfl⟩ : syracuseStep 5499089 = 4124317) B4124317
theorem B8349911 : Blo 1084620 8349911 := bstep (se 1 (by rfl) ⟨6262433, by rfl⟩ : syracuseStep 8349911 = 12524867) B12524867
theorem B1763753 : Blo 1084620 1763753 := bstep (se 2 (by rfl) ⟨661407, by rfl⟩ : syracuseStep 1763753 = 1322815) B1322815
theorem B1632743 : Blo 1084620 1632743 := bstep (se 1 (by rfl) ⟨1224557, by rfl⟩ : syracuseStep 1632743 = 2449115) B2449115
theorem B20900429 : Blo 1084620 20900429 := bstep (se 3 (by rfl) ⟨3918830, by rfl⟩ : syracuseStep 20900429 = 7837661) B7837661
theorem B1632923 : Blo 1084620 1632923 := bstep (se 1 (by rfl) ⟨1224692, by rfl⟩ : syracuseStep 1632923 = 2449385) B2449385
theorem B2059319 : Blo 1084620 2059319 := bstep (se 1 (by rfl) ⟨1544489, by rfl⟩ : syracuseStep 2059319 = 3088979) B3088979
theorem B3665033 : Blo 1084620 3665033 := bstep (se 2 (by rfl) ⟨1374387, by rfl⟩ : syracuseStep 3665033 = 2748775) B2748775
theorem B3665087 : Blo 1084620 3665087 := bstep (se 1 (by rfl) ⟨2748815, by rfl⟩ : syracuseStep 3665087 = 5497631) B5497631
theorem B27160235 : Blo 1084620 27160235 := bstep (se 1 (by rfl) ⟨20370176, by rfl⟩ : syracuseStep 27160235 = 40740353) B40740353
theorem B3665789 : Blo 1084620 3665789 := bstep (se 3 (by rfl) ⟨687335, by rfl⟩ : syracuseStep 3665789 = 1374671) B1374671
theorem B2977823 : Blo 1084620 2977823 := bstep (se 1 (by rfl) ⟨2233367, by rfl⟩ : syracuseStep 2977823 = 4466735) B4466735
theorem B4649015 : Blo 1084620 4649015 := bstep (se 1 (by rfl) ⟨3486761, by rfl⟩ : syracuseStep 4649015 = 6973523) B6973523
theorem B22605925 : Blo 1084620 22605925 := bstep (se 4 (by rfl) ⟨2119305, by rfl⟩ : syracuseStep 22605925 = 4238611) B4238611
theorem B2060777 : Blo 1084620 2060777 := bstep (se 2 (by rfl) ⟨772791, by rfl⟩ : syracuseStep 2060777 = 1545583) B1545583
theorem B2749211 : Blo 1084620 2749211 := bstep (se 1 (by rfl) ⟨2061908, by rfl⟩ : syracuseStep 2749211 = 4123817) B4123817
theorem B6190121 : Blo 1084620 6190121 := bstep (se 2 (by rfl) ⟨2321295, by rfl⟩ : syracuseStep 6190121 = 4642591) B4642591
theorem B4126049 : Blo 1084620 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B1374023 : Blo 1084620 1374023 := bstep (se 1 (by rfl) ⟨1030517, by rfl⟩ : syracuseStep 1374023 = 2061035) B2061035
theorem B1374079 : Blo 1084620 1374079 := bstep (se 1 (by rfl) ⟨1030559, by rfl⟩ : syracuseStep 1374079 = 2061119) B2061119
theorem B1374175 : Blo 1084620 1374175 := bstep (se 1 (by rfl) ⟨1030631, by rfl⟩ : syracuseStep 1374175 = 2061263) B2061263
theorem B8255681 : Blo 1084620 8255681 := bstep (se 2 (by rfl) ⟨3095880, by rfl⟩ : syracuseStep 8255681 = 6191761) B6191761
theorem B2062675 : Blo 1084620 2062675 := bstep (se 1 (by rfl) ⟨1547006, by rfl⟩ : syracuseStep 2062675 = 3094013) B3094013
theorem B27818639 : Blo 1084620 27818639 := bstep (se 1 (by rfl) ⟨20863979, by rfl⟩ : syracuseStep 27818639 = 41727959) B41727959
theorem B28572425 : Blo 1084620 28572425 := bstep (se 2 (by rfl) ⟨10714659, by rfl⟩ : syracuseStep 28572425 = 21429319) B21429319
theorem B28572797 : Blo 1084620 28572797 := bstep (se 3 (by rfl) ⟨5357399, by rfl⟩ : syracuseStep 28572797 = 10714799) B10714799
theorem B1375643 : Blo 1084620 1375643 := bstep (se 1 (by rfl) ⟨1031732, by rfl⟩ : syracuseStep 1375643 = 2063465) B2063465
theorem B1834663 : Blo 1084620 1834663 := bstep (se 1 (by rfl) ⟨1375997, by rfl⟩ : syracuseStep 1834663 = 2751995) B2751995
theorem B3670271 : Blo 1084620 3670271 := bstep (se 1 (by rfl) ⟨2752703, by rfl⟩ : syracuseStep 3670271 = 5505407) B5505407
theorem B2064703 : Blo 1084620 2064703 := bstep (se 1 (by rfl) ⟨1548527, by rfl⟩ : syracuseStep 2064703 = 3097055) B3097055
theorem B1376615 : Blo 1084620 1376615 := bstep (se 1 (by rfl) ⟨1032461, by rfl⟩ : syracuseStep 1376615 = 2064923) B2064923
theorem B3670433 : Blo 1084620 3670433 := bstep (se 2 (by rfl) ⟨1376412, by rfl⟩ : syracuseStep 3670433 = 2752825) B2752825
theorem B1835561 : Blo 1084620 1835561 := bstep (se 2 (by rfl) ⟨688335, by rfl⟩ : syracuseStep 1835561 = 1376671) B1376671
theorem B31359635 : Blo 1084620 31359635 := bstep (se 1 (by rfl) ⟨23519726, by rfl⟩ : syracuseStep 31359635 = 47039453) B47039453
theorem B26804951 : Blo 1084620 26804951 := bstep (se 1 (by rfl) ⟨20103713, by rfl⟩ : syracuseStep 26804951 = 40207427) B40207427
theorem B2753311 : Blo 1084620 2753311 := bstep (se 1 (by rfl) ⟨2064983, by rfl⟩ : syracuseStep 2753311 = 4129967) B4129967
theorem B9274247 : Blo 1084620 9274247 := bstep (se 1 (by rfl) ⟨6955685, by rfl⟩ : syracuseStep 9274247 = 13911371) B13911371
theorem B11732147 : Blo 1084620 11732147 := bstep (se 1 (by rfl) ⟨8799110, by rfl⟩ : syracuseStep 11732147 = 17598221) B17598221
theorem B3179839 : Blo 1084620 3179839 := bstep (se 1 (by rfl) ⟨2384879, by rfl⟩ : syracuseStep 3179839 = 4769759) B4769759
theorem B2753959 : Blo 1084620 2753959 := bstep (se 1 (by rfl) ⟨2065469, by rfl⟩ : syracuseStep 2753959 = 4130939) B4130939
theorem B5506703 : Blo 1084620 5506703 := bstep (se 1 (by rfl) ⟨4130027, by rfl⟩ : syracuseStep 5506703 = 8260055) B8260055
theorem B4132093 : Blo 1084620 4132093 := bstep (se 3 (by rfl) ⟨774767, by rfl⟩ : syracuseStep 4132093 = 1549535) B1549535
theorem B1084719 : Blo 1084620 1084719 := bstep (se 1 (by rfl) ⟨813539, by rfl⟩ : syracuseStep 1084719 = 1627079) B1627079
theorem B1084735 : Blo 1084620 1084735 := bstep (se 1 (by rfl) ⟨813551, by rfl⟩ : syracuseStep 1084735 = 1627103) B1627103
theorem B3673511 : Blo 1084620 3673511 := bstep (se 1 (by rfl) ⟨2755133, by rfl⟩ : syracuseStep 3673511 = 5510267) B5510267
theorem B1084959 : Blo 1084620 1084959 := bstep (se 1 (by rfl) ⟨813719, by rfl⟩ : syracuseStep 1084959 = 1627439) B1627439
theorem B1085095 : Blo 1084620 1085095 := bstep (se 1 (by rfl) ⟨813821, by rfl⟩ : syracuseStep 1085095 = 1627643) B1627643
theorem B1085119 : Blo 1084620 1085119 := bstep (se 1 (by rfl) ⟨813839, by rfl⟩ : syracuseStep 1085119 = 1627679) B1627679
theorem B1085211 : Blo 1084620 1085211 := bstep (se 1 (by rfl) ⟨813908, by rfl⟩ : syracuseStep 1085211 = 1627817) B1627817
theorem B1085215 : Blo 1084620 1085215 := bstep (se 1 (by rfl) ⟨813911, by rfl⟩ : syracuseStep 1085215 = 1627823) B1627823
theorem B1740575 : Blo 1084620 1740575 := bstep (se 1 (by rfl) ⟨1305431, by rfl⟩ : syracuseStep 1740575 = 2610863) B2610863
theorem B3673943 : Blo 1084620 3673943 := bstep (se 1 (by rfl) ⟨2755457, by rfl⟩ : syracuseStep 3673943 = 5510915) B5510915
theorem B1085295 : Blo 1084620 1085295 := bstep (se 1 (by rfl) ⟨813971, by rfl⟩ : syracuseStep 1085295 = 1627943) B1627943
theorem B8261513 : Blo 1084620 8261513 := bstep (se 2 (by rfl) ⟨3098067, by rfl⟩ : syracuseStep 8261513 = 6196135) B6196135
theorem B1085467 : Blo 1084620 1085467 := bstep (se 1 (by rfl) ⟨814100, by rfl⟩ : syracuseStep 1085467 = 1628201) B1628201
theorem B1085487 : Blo 1084620 1085487 := bstep (se 1 (by rfl) ⟨814115, by rfl⟩ : syracuseStep 1085487 = 1628231) B1628231
theorem B1085695 : Blo 1084620 1085695 := bstep (se 1 (by rfl) ⟨814271, by rfl⟩ : syracuseStep 1085695 = 1628543) B1628543
theorem B1085743 : Blo 1084620 1085743 := bstep (se 1 (by rfl) ⟨814307, by rfl⟩ : syracuseStep 1085743 = 1628615) B1628615
theorem B16748957 : Blo 1084620 16748957 := bstep (se 3 (by rfl) ⟨3140429, by rfl⟩ : syracuseStep 16748957 = 6280859) B6280859
theorem B1085887 : Blo 1084620 1085887 := bstep (se 1 (by rfl) ⟨814415, by rfl⟩ : syracuseStep 1085887 = 1628831) B1628831
theorem B1085983 : Blo 1084620 1085983 := bstep (se 1 (by rfl) ⟨814487, by rfl⟩ : syracuseStep 1085983 = 1628975) B1628975
theorem B1086043 : Blo 1084620 1086043 := bstep (se 1 (by rfl) ⟨814532, by rfl⟩ : syracuseStep 1086043 = 1629065) B1629065
theorem B1086063 : Blo 1084620 1086063 := bstep (se 1 (by rfl) ⟨814547, by rfl⟩ : syracuseStep 1086063 = 1629095) B1629095
theorem B1086183 : Blo 1084620 1086183 := bstep (se 1 (by rfl) ⟨814637, by rfl⟩ : syracuseStep 1086183 = 1629275) B1629275
theorem B1086311 : Blo 1084620 1086311 := bstep (se 1 (by rfl) ⟨814733, by rfl⟩ : syracuseStep 1086311 = 1629467) B1629467
theorem B5215211 : Blo 1084620 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B1741895 : Blo 1084620 1741895 := bstep (se 1 (by rfl) ⟨1306421, by rfl⟩ : syracuseStep 1741895 = 2612843) B2612843
theorem B1086623 : Blo 1084620 1086623 := bstep (se 1 (by rfl) ⟨814967, by rfl⟩ : syracuseStep 1086623 = 1629935) B1629935
theorem B1086747 : Blo 1084620 1086747 := bstep (se 1 (by rfl) ⟨815060, by rfl⟩ : syracuseStep 1086747 = 1630121) B1630121
theorem B5510429 : Blo 1084620 5510429 := bstep (se 3 (by rfl) ⟨1033205, by rfl⟩ : syracuseStep 5510429 = 2066411) B2066411
theorem B1086847 : Blo 1084620 1086847 := bstep (se 1 (by rfl) ⟨815135, by rfl⟩ : syracuseStep 1086847 = 1630271) B1630271
theorem B1087003 : Blo 1084620 1087003 := bstep (se 1 (by rfl) ⟨815252, by rfl⟩ : syracuseStep 1087003 = 1630505) B1630505
theorem B1087183 : Blo 1084620 1087183 := bstep (se 1 (by rfl) ⟨815387, by rfl⟩ : syracuseStep 1087183 = 1630775) B1630775
theorem B1546175 : Blo 1084620 1546175 := bstep (se 1 (by rfl) ⟨1159631, by rfl⟩ : syracuseStep 1546175 = 2319263) B2319263
theorem B1087423 : Blo 1084620 1087423 := bstep (se 1 (by rfl) ⟨815567, by rfl⟩ : syracuseStep 1087423 = 1631135) B1631135
theorem B31332419 : Blo 1084620 31332419 := bstep (se 1 (by rfl) ⟨23499314, by rfl⟩ : syracuseStep 31332419 = 46998629) B46998629
theorem B1087615 : Blo 1084620 1087615 := bstep (se 1 (by rfl) ⟨815711, by rfl⟩ : syracuseStep 1087615 = 1631423) B1631423
theorem B1087711 : Blo 1084620 1087711 := bstep (se 1 (by rfl) ⟨815783, by rfl⟩ : syracuseStep 1087711 = 1631567) B1631567
theorem B1087771 : Blo 1084620 1087771 := bstep (se 1 (by rfl) ⟨815828, by rfl⟩ : syracuseStep 1087771 = 1631657) B1631657
theorem B1087871 : Blo 1084620 1087871 := bstep (se 1 (by rfl) ⟨815903, by rfl⟩ : syracuseStep 1087871 = 1631807) B1631807
theorem B2202055 : Blo 1084620 2202055 := bstep (se 1 (by rfl) ⟨1651541, by rfl⟩ : syracuseStep 2202055 = 3303083) B3303083
theorem B1088111 : Blo 1084620 1088111 := bstep (se 1 (by rfl) ⟨816083, by rfl⟩ : syracuseStep 1088111 = 1632167) B1632167
theorem B1088191 : Blo 1084620 1088191 := bstep (se 1 (by rfl) ⟨816143, by rfl⟩ : syracuseStep 1088191 = 1632287) B1632287
theorem B11737811 : Blo 1084620 11737811 := bstep (se 1 (by rfl) ⟨8803358, by rfl⟩ : syracuseStep 11737811 = 17606717) B17606717
theorem B6363913 : Blo 1084620 6363913 := bstep (se 2 (by rfl) ⟨2386467, by rfl⟩ : syracuseStep 6363913 = 4772935) B4772935
theorem B1088495 : Blo 1084620 1088495 := bstep (se 1 (by rfl) ⟨816371, by rfl⟩ : syracuseStep 1088495 = 1632743) B1632743
theorem B13933619 : Blo 1084620 13933619 := bstep (se 1 (by rfl) ⟨10450214, by rfl⟩ : syracuseStep 13933619 = 20900429) B20900429
theorem B1088615 : Blo 1084620 1088615 := bstep (se 1 (by rfl) ⟨816461, by rfl⟩ : syracuseStep 1088615 = 1632923) B1632923
theorem B7445789 : Blo 1084620 7445789 := bstep (se 3 (by rfl) ⟨1396085, by rfl⟩ : syracuseStep 7445789 = 2792171) B2792171
theorem B14097851 : Blo 1084620 14097851 := bstep (se 1 (by rfl) ⟨10573388, by rfl⟩ : syracuseStep 14097851 = 21146777) B21146777
theorem B18816521 : Blo 1084620 18816521 := bstep (se 2 (by rfl) ⟨7056195, by rfl⟩ : syracuseStep 18816521 = 14112391) B14112391
theorem B19048283 : Blo 1084620 19048283 := bstep (se 1 (by rfl) ⟨14286212, by rfl⟩ : syracuseStep 19048283 = 28572425) B28572425
theorem B35203045 : Blo 1084620 35203045 := bstep (se 4 (by rfl) ⟨3300285, by rfl⟩ : syracuseStep 35203045 = 6600571) B6600571
theorem B19048531 : Blo 1084620 19048531 := bstep (se 1 (by rfl) ⟨14286398, by rfl⟩ : syracuseStep 19048531 = 28572797) B28572797
theorem B7940861 : Blo 1084620 7940861 := bstep (se 3 (by rfl) ⟨1488911, by rfl⟩ : syracuseStep 7940861 = 2977823) B2977823
theorem B12397373 : Blo 1084620 12397373 := bstep (se 3 (by rfl) ⟨2324507, by rfl⟩ : syracuseStep 12397373 = 4649015) B4649015
theorem B4467881 : Blo 1084620 4467881 := bstep (se 2 (by rfl) ⟨1675455, by rfl⟩ : syracuseStep 4467881 = 3350911) B3350911
theorem B1223887 : Blo 1084620 1223887 := bstep (se 1 (by rfl) ⟨917915, by rfl⟩ : syracuseStep 1223887 = 1835831) B1835831
theorem B1224607 : Blo 1084620 1224607 := bstep (se 1 (by rfl) ⟨918455, by rfl⟩ : syracuseStep 1224607 = 1836911) B1836911
theorem B6959479 : Blo 1084620 6959479 := bstep (se 1 (by rfl) ⟨5219609, by rfl⟩ : syracuseStep 6959479 = 10439219) B10439219
theorem B5879051 : Blo 1084620 5879051 := bstep (se 1 (by rfl) ⟨4409288, by rfl⟩ : syracuseStep 5879051 = 8818577) B8818577
theorem B4635245 : Blo 1084620 4635245 := bstep (se 3 (by rfl) ⟨869108, by rfl⟩ : syracuseStep 4635245 = 1738217) B1738217
theorem B5225417 : Blo 1084620 5225417 := bstep (se 2 (by rfl) ⟨1959531, by rfl⟩ : syracuseStep 5225417 = 3919063) B3919063
theorem B9911879 : Blo 1084620 9911879 := bstep (se 1 (by rfl) ⟨7433909, by rfl⟩ : syracuseStep 9911879 = 14867819) B14867819
theorem B2932571 : Blo 1084620 2932571 := bstep (se 1 (by rfl) ⟨2199428, by rfl⟩ : syracuseStep 2932571 = 4398857) B4398857
theorem B8798233 : Blo 1084620 8798233 := bstep (se 2 (by rfl) ⟨3299337, by rfl⟩ : syracuseStep 8798233 = 6598675) B6598675
theorem B2442311 : Blo 1084620 2442311 := bstep (se 1 (by rfl) ⟨1831733, by rfl⟩ : syracuseStep 2442311 = 3663467) B3663467
theorem B1393735 : Blo 1084620 1393735 := bstep (se 1 (by rfl) ⟨1045301, by rfl⟩ : syracuseStep 1393735 = 2090603) B2090603
theorem B4703341 : Blo 1084620 4703341 := bstep (se 3 (by rfl) ⟨881876, by rfl⟩ : syracuseStep 4703341 = 1763753) B1763753
theorem B12371129 : Blo 1084620 12371129 := bstep (se 2 (by rfl) ⟨4639173, by rfl⟩ : syracuseStep 12371129 = 9278347) B9278347
theorem B35702045 : Blo 1084620 35702045 := bstep (se 3 (by rfl) ⟨6694133, by rfl⟩ : syracuseStep 35702045 = 13388267) B13388267
theorem B67782035 : Blo 1084620 67782035 := bstep (se 1 (by rfl) ⟨50836526, by rfl⟩ : syracuseStep 67782035 = 101673053) B101673053
theorem B1099423 : Blo 1084620 1099423 := bstep (se 1 (by rfl) ⟨824567, by rfl⟩ : syracuseStep 1099423 = 1649135) B1649135
theorem B2443355 : Blo 1084620 2443355 := bstep (se 1 (by rfl) ⟨1832516, by rfl⟩ : syracuseStep 2443355 = 3665033) B3665033
theorem B2443391 : Blo 1084620 2443391 := bstep (se 1 (by rfl) ⟨1832543, by rfl⟩ : syracuseStep 2443391 = 3665087) B3665087
theorem B67029295 : Blo 1084620 67029295 := bstep (se 1 (by rfl) ⟨50271971, by rfl⟩ : syracuseStep 67029295 = 100543943) B100543943
theorem B18106823 : Blo 1084620 18106823 := bstep (se 1 (by rfl) ⟨13580117, by rfl⟩ : syracuseStep 18106823 = 27160235) B27160235
theorem B2443859 : Blo 1084620 2443859 := bstep (se 1 (by rfl) ⟨1832894, by rfl⟩ : syracuseStep 2443859 = 3665789) B3665789
theorem B20892275 : Blo 1084620 20892275 := bstep (se 1 (by rfl) ⟨15669206, by rfl⟩ : syracuseStep 20892275 = 31338413) B31338413
theorem B3722635 : Blo 1084620 3722635 := bstep (se 1 (by rfl) ⟨2791976, by rfl⟩ : syracuseStep 3722635 = 5583953) B5583953
theorem B8244989 : Blo 1084620 8244989 := bstep (se 3 (by rfl) ⟨1545935, by rfl⟩ : syracuseStep 8244989 = 3091871) B3091871
theorem B4641259 : Blo 1084620 4641259 := bstep (se 1 (by rfl) ⟨3480944, by rfl⟩ : syracuseStep 4641259 = 6961889) B6961889
theorem B1856233 : Blo 1084620 1856233 := bstep (se 2 (by rfl) ⟨696087, by rfl⟩ : syracuseStep 1856233 = 1392175) B1392175
theorem B2446217 : Blo 1084620 2446217 := bstep (se 2 (by rfl) ⟨917331, by rfl⟩ : syracuseStep 2446217 = 1834663) B1834663
theorem B1103015 : Blo 1084620 1103015 := bstep (se 1 (by rfl) ⟨827261, by rfl⟩ : syracuseStep 1103015 = 1654523) B1654523
theorem B31348457 : Blo 1084620 31348457 := bstep (se 2 (by rfl) ⟨11755671, by rfl⟩ : syracuseStep 31348457 = 23511343) B23511343
theorem B2447225 : Blo 1084620 2447225 := bstep (se 2 (by rfl) ⟨917709, by rfl⟩ : syracuseStep 2447225 = 1835419) B1835419
theorem B4118471 : Blo 1084620 4118471 := bstep (se 1 (by rfl) ⟨3088853, by rfl⟩ : syracuseStep 4118471 = 6177707) B6177707
theorem B18537011 : Blo 1084620 18537011 := bstep (se 1 (by rfl) ⟨13902758, by rfl⟩ : syracuseStep 18537011 = 27805517) B27805517
theorem B2447999 : Blo 1084620 2447999 := bstep (se 1 (by rfl) ⟨1835999, by rfl⟩ : syracuseStep 2447999 = 3671999) B3671999
theorem B1956511 : Blo 1084620 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B2317025 : Blo 1084620 2317025 := bstep (se 2 (by rfl) ⟨868884, by rfl⟩ : syracuseStep 2317025 = 1737769) B1737769
theorem B1628969 : Blo 1084620 1628969 := bstep (se 2 (by rfl) ⟨610863, by rfl⟩ : syracuseStep 1628969 = 1221727) B1221727
theorem B3660713 : Blo 1084620 3660713 := bstep (se 2 (by rfl) ⟨1372767, by rfl⟩ : syracuseStep 3660713 = 2745535) B2745535
theorem B3660767 : Blo 1084620 3660767 := bstep (se 1 (by rfl) ⟨2745575, by rfl⟩ : syracuseStep 3660767 = 5491151) B5491151
theorem B1629503 : Blo 1084620 1629503 := bstep (se 1 (by rfl) ⟨1222127, by rfl⟩ : syracuseStep 1629503 = 2444255) B2444255
theorem B3661307 : Blo 1084620 3661307 := bstep (se 1 (by rfl) ⟨2745980, by rfl⟩ : syracuseStep 3661307 = 5491961) B5491961
theorem B3661415 : Blo 1084620 3661415 := bstep (se 1 (by rfl) ⟨2746061, by rfl⟩ : syracuseStep 3661415 = 5492123) B5492123
theorem B1629833 : Blo 1084620 1629833 := bstep (se 2 (by rfl) ⟨611187, by rfl⟩ : syracuseStep 1629833 = 1222375) B1222375
theorem B4120247 : Blo 1084620 4120247 := bstep (se 1 (by rfl) ⟨3090185, by rfl⟩ : syracuseStep 4120247 = 6180371) B6180371
theorem B2121889 : Blo 1084620 2121889 := bstep (se 2 (by rfl) ⟨795708, by rfl⟩ : syracuseStep 2121889 = 1591417) B1591417
theorem B1630535 : Blo 1084620 1630535 := bstep (se 1 (by rfl) ⟨1222901, by rfl⟩ : syracuseStep 1630535 = 2445803) B2445803
theorem B1630619 : Blo 1084620 1630619 := bstep (se 1 (by rfl) ⟨1222964, by rfl⟩ : syracuseStep 1630619 = 2445929) B2445929
theorem B39674357 : Blo 1084620 39674357 := bstep (se 5 (by rfl) ⟨1859735, by rfl⟩ : syracuseStep 39674357 = 3719471) B3719471
theorem B2941481 : Blo 1084620 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B1631039 : Blo 1084620 1631039 := bstep (se 1 (by rfl) ⟨1223279, by rfl⟩ : syracuseStep 1631039 = 2446559) B2446559
theorem B1631327 : Blo 1084620 1631327 := bstep (se 1 (by rfl) ⟨1223495, by rfl⟩ : syracuseStep 1631327 = 2446991) B2446991
theorem B4121705 : Blo 1084620 4121705 := bstep (se 2 (by rfl) ⟨1545639, by rfl⟩ : syracuseStep 4121705 = 3091279) B3091279
theorem B1631387 : Blo 1084620 1631387 := bstep (se 1 (by rfl) ⟨1223540, by rfl⟩ : syracuseStep 1631387 = 2447081) B2447081
theorem B28272077 : Blo 1084620 28272077 := bstep (se 3 (by rfl) ⟨5301014, by rfl⟩ : syracuseStep 28272077 = 10602029) B10602029
theorem B4122191 : Blo 1084620 4122191 := bstep (se 1 (by rfl) ⟨3091643, by rfl⟩ : syracuseStep 4122191 = 6183287) B6183287
theorem B4646555 : Blo 1084620 4646555 := bstep (se 1 (by rfl) ⟨3484916, by rfl⟩ : syracuseStep 4646555 = 6969833) B6969833
theorem B5498603 : Blo 1084620 5498603 := bstep (se 1 (by rfl) ⟨4123952, by rfl⟩ : syracuseStep 5498603 = 8247905) B8247905
theorem B2320339 : Blo 1084620 2320339 := bstep (se 1 (by rfl) ⟨1740254, by rfl⟩ : syracuseStep 2320339 = 3480509) B3480509
theorem B3664061 : Blo 1084620 3664061 := bstep (se 3 (by rfl) ⟨687011, by rfl⟩ : syracuseStep 3664061 = 1374023) B1374023
theorem B1632479 : Blo 1084620 1632479 := bstep (se 1 (by rfl) ⟨1224359, by rfl⟩ : syracuseStep 1632479 = 2448719) B2448719
theorem B3664115 : Blo 1084620 3664115 := bstep (se 1 (by rfl) ⟨2748086, by rfl⟩ : syracuseStep 3664115 = 5496173) B5496173
theorem B1632539 : Blo 1084620 1632539 := bstep (se 1 (by rfl) ⟨1224404, by rfl⟩ : syracuseStep 1632539 = 2448809) B2448809
theorem B2321057 : Blo 1084620 2321057 := bstep (se 2 (by rfl) ⟨870396, by rfl⟩ : syracuseStep 2321057 = 1740793) B1740793
theorem B30141233 : Blo 1084620 30141233 := bstep (se 2 (by rfl) ⟨11302962, by rfl⟩ : syracuseStep 30141233 = 22605925) B22605925
theorem B8252279 : Blo 1084620 8252279 := bstep (se 1 (by rfl) ⟨6189209, by rfl⟩ : syracuseStep 8252279 = 12378419) B12378419
theorem B2059175 : Blo 1084620 2059175 := bstep (se 1 (by rfl) ⟨1544381, by rfl⟩ : syracuseStep 2059175 = 3088763) B3088763
theorem B95415803 : Blo 1084620 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B4124303 : Blo 1084620 4124303 := bstep (se 1 (by rfl) ⟨3093227, by rfl⟩ : syracuseStep 4124303 = 6186455) B6186455
theorem B3665627 : Blo 1084620 3665627 := bstep (se 1 (by rfl) ⟨2749220, by rfl⟩ : syracuseStep 3665627 = 5498441) B5498441
theorem B2060063 : Blo 1084620 2060063 := bstep (se 1 (by rfl) ⟨1545047, by rfl⟩ : syracuseStep 2060063 = 3090095) B3090095
theorem B17887063 : Blo 1084620 17887063 := bstep (se 1 (by rfl) ⟨13415297, by rfl⟩ : syracuseStep 17887063 = 26830595) B26830595
theorem B2322287 : Blo 1084620 2322287 := bstep (se 1 (by rfl) ⟨1741715, by rfl⟩ : syracuseStep 2322287 = 3483431) B3483431
theorem B3666059 : Blo 1084620 3666059 := bstep (se 1 (by rfl) ⟨2749544, by rfl⟩ : syracuseStep 3666059 = 5499089) B5499089
theorem B5566607 : Blo 1084620 5566607 := bstep (se 1 (by rfl) ⟨4174955, by rfl⟩ : syracuseStep 5566607 = 8349911) B8349911
theorem B1372879 : Blo 1084620 1372879 := bstep (se 1 (by rfl) ⟨1029659, by rfl⟩ : syracuseStep 1372879 = 2059319) B2059319
theorem B1832105 : Blo 1084620 1832105 := bstep (se 2 (by rfl) ⟨687039, by rfl⟩ : syracuseStep 1832105 = 1374079) B1374079
theorem B1832233 : Blo 1084620 1832233 := bstep (se 2 (by rfl) ⟨687087, by rfl⟩ : syracuseStep 1832233 = 1374175) B1374175
theorem B2061931 : Blo 1084620 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B1373851 : Blo 1084620 1373851 := bstep (se 1 (by rfl) ⟨1030388, by rfl⟩ : syracuseStep 1373851 = 2060777) B2060777
theorem B2750233 : Blo 1084620 2750233 := bstep (se 2 (by rfl) ⟨1031337, by rfl⟩ : syracuseStep 2750233 = 2062675) B2062675
theorem B35780413 : Blo 1084620 35780413 := bstep (se 3 (by rfl) ⟨6708827, by rfl⟩ : syracuseStep 35780413 = 13417655) B13417655
theorem B1832807 : Blo 1084620 1832807 := bstep (se 1 (by rfl) ⟨1374605, by rfl⟩ : syracuseStep 1832807 = 2749211) B2749211
theorem B4126747 : Blo 1084620 4126747 := bstep (se 1 (by rfl) ⟨3095060, by rfl⟩ : syracuseStep 4126747 = 6190121) B6190121
theorem B2750699 : Blo 1084620 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B3668381 : Blo 1084620 3668381 := bstep (se 3 (by rfl) ⟨687821, by rfl⟩ : syracuseStep 3668381 = 1375643) B1375643
theorem B6191579 : Blo 1084620 6191579 := bstep (se 1 (by rfl) ⟨4643684, by rfl⟩ : syracuseStep 6191579 = 9287369) B9287369
theorem B2063009 : Blo 1084620 2063009 := bstep (se 2 (by rfl) ⟨773628, by rfl⟩ : syracuseStep 2063009 = 1547257) B1547257
theorem B5503787 : Blo 1084620 5503787 := bstep (se 1 (by rfl) ⟨4127840, by rfl⟩ : syracuseStep 5503787 = 8255681) B8255681
theorem B18545759 : Blo 1084620 18545759 := bstep (se 1 (by rfl) ⟨13909319, by rfl⟩ : syracuseStep 18545759 = 27818639) B27818639
theorem B11730977 : Blo 1084620 11730977 := bstep (se 2 (by rfl) ⟨4399116, by rfl⟩ : syracuseStep 11730977 = 8798233) B8798233
theorem B2752937 : Blo 1084620 2752937 := bstep (se 2 (by rfl) ⟨1032351, by rfl⟩ : syracuseStep 2752937 = 2064703) B2064703
theorem B20906423 : Blo 1084620 20906423 := bstep (se 1 (by rfl) ⟨15679817, by rfl⟩ : syracuseStep 20906423 = 31359635) B31359635
theorem B45188023 : Blo 1084620 45188023 := bstep (se 1 (by rfl) ⟨33891017, by rfl⟩ : syracuseStep 45188023 = 67782035) B67782035
theorem B3670973 : Blo 1084620 3670973 := bstep (se 3 (by rfl) ⟨688307, by rfl⟩ : syracuseStep 3670973 = 1376615) B1376615
theorem B3671081 : Blo 1084620 3671081 := bstep (se 2 (by rfl) ⟨1376655, by rfl⟩ : syracuseStep 3671081 = 2753311) B2753311
theorem B44663885 : Blo 1084620 44663885 := bstep (se 3 (by rfl) ⟨8374478, by rfl⟩ : syracuseStep 44663885 = 16748957) B16748957
theorem B3671135 : Blo 1084620 3671135 := bstep (se 1 (by rfl) ⟨2753351, by rfl⟩ : syracuseStep 3671135 = 5506703) B5506703
theorem B13928183 : Blo 1084620 13928183 := bstep (se 1 (by rfl) ⟨10446137, by rfl⟩ : syracuseStep 13928183 = 20892275) B20892275
theorem B3671945 : Blo 1084620 3671945 := bstep (se 2 (by rfl) ⟨1376979, by rfl⟩ : syracuseStep 3671945 = 2753959) B2753959
theorem B5507675 : Blo 1084620 5507675 := bstep (se 1 (by rfl) ⟨4130756, by rfl⟩ : syracuseStep 5507675 = 8261513) B8261513
theorem B25398041 : Blo 1084620 25398041 := bstep (se 2 (by rfl) ⟨9524265, by rfl⟩ : syracuseStep 25398041 = 19048531) B19048531
theorem B3476807 : Blo 1084620 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B3673619 : Blo 1084620 3673619 := bstep (se 1 (by rfl) ⟨2755214, by rfl⟩ : syracuseStep 3673619 = 5510429) B5510429
theorem B5509457 : Blo 1084620 5509457 := bstep (se 2 (by rfl) ⟨2066046, by rfl⟩ : syracuseStep 5509457 = 4132093) B4132093
theorem B12358007 : Blo 1084620 12358007 := bstep (se 1 (by rfl) ⟨9268505, by rfl⟩ : syracuseStep 12358007 = 18537011) B18537011
theorem B1544683 : Blo 1084620 1544683 := bstep (se 1 (by rfl) ⟨1158512, by rfl⟩ : syracuseStep 1544683 = 2317025) B2317025
theorem B1085979 : Blo 1084620 1085979 := bstep (se 1 (by rfl) ⟨814484, by rfl⟩ : syracuseStep 1085979 = 1628969) B1628969
theorem B1086335 : Blo 1084620 1086335 := bstep (se 1 (by rfl) ⟨814751, by rfl⟩ : syracuseStep 1086335 = 1629503) B1629503
theorem B1086555 : Blo 1084620 1086555 := bstep (se 1 (by rfl) ⟨814916, by rfl⟩ : syracuseStep 1086555 = 1629833) B1629833
theorem B1087023 : Blo 1084620 1087023 := bstep (se 1 (by rfl) ⟨815267, by rfl⟩ : syracuseStep 1087023 = 1630535) B1630535
theorem B1087079 : Blo 1084620 1087079 := bstep (se 1 (by rfl) ⟨815309, by rfl⟩ : syracuseStep 1087079 = 1630619) B1630619
theorem B26449571 : Blo 1084620 26449571 := bstep (se 1 (by rfl) ⟨19837178, by rfl⟩ : syracuseStep 26449571 = 39674357) B39674357
theorem B9279305 : Blo 1084620 9279305 := bstep (se 2 (by rfl) ⟨3479739, by rfl⟩ : syracuseStep 9279305 = 6959479) B6959479
theorem B1087359 : Blo 1084620 1087359 := bstep (se 1 (by rfl) ⟨815519, by rfl⟩ : syracuseStep 1087359 = 1631039) B1631039
theorem B1087551 : Blo 1084620 1087551 := bstep (se 1 (by rfl) ⟨815663, by rfl⟩ : syracuseStep 1087551 = 1631327) B1631327
theorem B1087591 : Blo 1084620 1087591 := bstep (se 1 (by rfl) ⟨815693, by rfl⟩ : syracuseStep 1087591 = 1631387) B1631387
theorem B18848051 : Blo 1084620 18848051 := bstep (se 1 (by rfl) ⟨14136038, by rfl⟩ : syracuseStep 18848051 = 28272077) B28272077
theorem B1088319 : Blo 1084620 1088319 := bstep (se 1 (by rfl) ⟨816239, by rfl⟩ : syracuseStep 1088319 = 1632479) B1632479
theorem B1088359 : Blo 1084620 1088359 := bstep (se 1 (by rfl) ⟨816269, by rfl⟩ : syracuseStep 1088359 = 1632539) B1632539
theorem B1547371 : Blo 1084620 1547371 := bstep (se 1 (by rfl) ⟨1160528, by rfl⟩ : syracuseStep 1547371 = 2321057) B2321057
theorem B20094155 : Blo 1084620 20094155 := bstep (se 1 (by rfl) ⟨15070616, by rfl⟩ : syracuseStep 20094155 = 30141233) B30141233
theorem B8264915 : Blo 1084620 8264915 := bstep (se 1 (by rfl) ⟨6198686, by rfl⟩ : syracuseStep 8264915 = 12397373) B12397373
theorem B63610535 : Blo 1084620 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B1548191 : Blo 1084620 1548191 := bstep (se 1 (by rfl) ⟨1161143, by rfl⟩ : syracuseStep 1548191 = 2322287) B2322287
theorem B3711071 : Blo 1084620 3711071 := bstep (se 1 (by rfl) ⟨2783303, by rfl⟩ : syracuseStep 3711071 = 5566607) B5566607
theorem B1221403 : Blo 1084620 1221403 := bstep (se 1 (by rfl) ⟨916052, by rfl⟩ : syracuseStep 1221403 = 1832105) B1832105
theorem B1221871 : Blo 1084620 1221871 := bstep (se 1 (by rfl) ⟨916403, by rfl⟩ : syracuseStep 1221871 = 1832807) B1832807
theorem B50177389 : Blo 1084620 50177389 := bstep (se 3 (by rfl) ⟨9408260, by rfl⟩ : syracuseStep 50177389 = 18816521) B18816521
theorem B3090163 : Blo 1084620 3090163 := bstep (se 1 (by rfl) ⟨2317622, by rfl⟩ : syracuseStep 3090163 = 4635245) B4635245
theorem B3483611 : Blo 1084620 3483611 := bstep (se 1 (by rfl) ⟨2612708, by rfl⟩ : syracuseStep 3483611 = 5225417) B5225417
theorem B12363839 : Blo 1084620 12363839 := bstep (se 1 (by rfl) ⟨9272879, by rfl⟩ : syracuseStep 12363839 = 18545759) B18545759
theorem B2829185 : Blo 1084620 2829185 := bstep (se 2 (by rfl) ⟨1060944, by rfl⟩ : syracuseStep 2829185 = 2121889) B2121889
theorem B1223707 : Blo 1084620 1223707 := bstep (se 1 (by rfl) ⟨917780, by rfl⟩ : syracuseStep 1223707 = 1835561) B1835561
theorem B17869967 : Blo 1084620 17869967 := bstep (se 1 (by rfl) ⟨13402475, by rfl⟩ : syracuseStep 17869967 = 26804951) B26804951
theorem B23801363 : Blo 1084620 23801363 := bstep (se 1 (by rfl) ⟨17851022, by rfl⟩ : syracuseStep 23801363 = 35702045) B35702045
theorem B7843949 : Blo 1084620 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B6271121 : Blo 1084620 6271121 := bstep (se 2 (by rfl) ⟨2351670, by rfl⟩ : syracuseStep 6271121 = 4703341) B4703341
theorem B12071215 : Blo 1084620 12071215 := bstep (se 1 (by rfl) ⟨9053411, by rfl⟩ : syracuseStep 12071215 = 18106823) B18106823
theorem B4239785 : Blo 1084620 4239785 := bstep (se 2 (by rfl) ⟨1589919, by rfl⟩ : syracuseStep 4239785 = 3179839) B3179839
theorem B11744293 : Blo 1084620 11744293 := bstep (se 4 (by rfl) ⟨1101027, by rfl⟩ : syracuseStep 11744293 = 2202055) B2202055
theorem B3093785 : Blo 1084620 3093785 := bstep (se 2 (by rfl) ⟨1160169, by rfl⟩ : syracuseStep 3093785 = 2320339) B2320339
theorem B46937393 : Blo 1084620 46937393 := bstep (se 2 (by rfl) ⟨17601522, by rfl⟩ : syracuseStep 46937393 = 35203045) B35203045
theorem B89372393 : Blo 1084620 89372393 := bstep (se 2 (by rfl) ⟨33514647, by rfl⟩ : syracuseStep 89372393 = 67029295) B67029295
theorem B1161263 : Blo 1084620 1161263 := bstep (se 1 (by rfl) ⟨870947, by rfl⟩ : syracuseStep 1161263 = 1741895) B1741895
theorem B20888279 : Blo 1084620 20888279 := bstep (se 1 (by rfl) ⟨15666209, by rfl⟩ : syracuseStep 20888279 = 31332419) B31332419
theorem B4963513 : Blo 1084620 4963513 := bstep (se 2 (by rfl) ⟨1861317, by rfl⟩ : syracuseStep 4963513 = 3722635) B3722635
theorem B2440475 : Blo 1084620 2440475 := bstep (se 1 (by rfl) ⟨1830356, by rfl⟩ : syracuseStep 2440475 = 3660713) B3660713
theorem B2440511 : Blo 1084620 2440511 := bstep (se 1 (by rfl) ⟨1830383, by rfl⟩ : syracuseStep 2440511 = 3660767) B3660767
theorem B9289079 : Blo 1084620 9289079 := bstep (se 1 (by rfl) ⟨6966809, by rfl⟩ : syracuseStep 9289079 = 13933619) B13933619
theorem B4963859 : Blo 1084620 4963859 := bstep (se 1 (by rfl) ⟨3722894, by rfl⟩ : syracuseStep 4963859 = 7445789) B7445789
theorem B2440871 : Blo 1084620 2440871 := bstep (se 1 (by rfl) ⟨1830653, by rfl⟩ : syracuseStep 2440871 = 3661307) B3661307
theorem B2440943 : Blo 1084620 2440943 := bstep (se 1 (by rfl) ⟨1830707, by rfl⟩ : syracuseStep 2440943 = 3661415) B3661415
theorem B2474977 : Blo 1084620 2474977 := bstep (se 2 (by rfl) ⟨928116, by rfl⟩ : syracuseStep 2474977 = 1856233) B1856233
theorem B3097703 : Blo 1084620 3097703 := bstep (se 1 (by rfl) ⟨2323277, by rfl⟩ : syracuseStep 3097703 = 4646555) B4646555
theorem B12698855 : Blo 1084620 12698855 := bstep (se 1 (by rfl) ⟨9524141, by rfl⟩ : syracuseStep 12698855 = 19048283) B19048283
theorem B2442707 : Blo 1084620 2442707 := bstep (se 1 (by rfl) ⟨1832030, by rfl⟩ : syracuseStep 2442707 = 3664061) B3664061
theorem B2442743 : Blo 1084620 2442743 := bstep (se 1 (by rfl) ⟨1832057, by rfl⟩ : syracuseStep 2442743 = 3664115) B3664115
theorem B2442977 : Blo 1084620 2442977 := bstep (se 2 (by rfl) ⟨916116, by rfl⟩ : syracuseStep 2442977 = 1832233) B1832233
theorem B5293907 : Blo 1084620 5293907 := bstep (se 1 (by rfl) ⟨3970430, by rfl⟩ : syracuseStep 5293907 = 7940861) B7940861
theorem B2443751 : Blo 1084620 2443751 := bstep (se 1 (by rfl) ⟨1832813, by rfl⟩ : syracuseStep 2443751 = 3665627) B3665627
theorem B2444039 : Blo 1084620 2444039 := bstep (se 1 (by rfl) ⟨1833029, by rfl⟩ : syracuseStep 2444039 = 3666059) B3666059
theorem B3919367 : Blo 1084620 3919367 := bstep (se 1 (by rfl) ⟨2939525, by rfl⟩ : syracuseStep 3919367 = 5879051) B5879051
theorem B2608681 : Blo 1084620 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B2445587 : Blo 1084620 2445587 := bstep (se 1 (by rfl) ⟨1834190, by rfl⟩ : syracuseStep 2445587 = 3668381) B3668381
theorem B4641533 : Blo 1084620 4641533 := bstep (se 3 (by rfl) ⟨870287, by rfl⟩ : syracuseStep 4641533 = 1740575) B1740575
theorem B7820189 : Blo 1084620 7820189 := bstep (se 3 (by rfl) ⟨1466285, by rfl⟩ : syracuseStep 7820189 = 2932571) B2932571
theorem B6607919 : Blo 1084620 6607919 := bstep (se 1 (by rfl) ⟨4955939, by rfl⟩ : syracuseStep 6607919 = 9911879) B9911879
theorem B2446847 : Blo 1084620 2446847 := bstep (se 1 (by rfl) ⟨1835135, by rfl⟩ : syracuseStep 2446847 = 3670271) B3670271
theorem B2446955 : Blo 1084620 2446955 := bstep (se 1 (by rfl) ⟨1835216, by rfl⟩ : syracuseStep 2446955 = 3670433) B3670433
theorem B6182831 : Blo 1084620 6182831 := bstep (se 1 (by rfl) ⟨4637123, by rfl⟩ : syracuseStep 6182831 = 9274247) B9274247
theorem B1628207 : Blo 1084620 1628207 := bstep (se 1 (by rfl) ⟨1221155, by rfl⟩ : syracuseStep 1628207 = 2442311) B2442311
theorem B7821431 : Blo 1084620 7821431 := bstep (se 1 (by rfl) ⟨5866073, by rfl⟩ : syracuseStep 7821431 = 11732147) B11732147
theorem B8247419 : Blo 1084620 8247419 := bstep (se 1 (by rfl) ⟨6185564, by rfl⟩ : syracuseStep 8247419 = 12371129) B12371129
theorem B1628903 : Blo 1084620 1628903 := bstep (se 1 (by rfl) ⟨1221677, by rfl⟩ : syracuseStep 1628903 = 2443355) B2443355
theorem B1628927 : Blo 1084620 1628927 := bstep (se 1 (by rfl) ⟨1221695, by rfl⟩ : syracuseStep 1628927 = 2443391) B2443391
theorem B1858313 : Blo 1084620 1858313 := bstep (se 2 (by rfl) ⟨696867, by rfl⟩ : syracuseStep 1858313 = 1393735) B1393735
theorem B1629239 : Blo 1084620 1629239 := bstep (se 1 (by rfl) ⟨1221929, by rfl⟩ : syracuseStep 1629239 = 2443859) B2443859
theorem B2449007 : Blo 1084620 2449007 := bstep (se 1 (by rfl) ⟨1836755, by rfl⟩ : syracuseStep 2449007 = 3673511) B3673511
theorem B5496659 : Blo 1084620 5496659 := bstep (se 1 (by rfl) ⟨4122494, by rfl⟩ : syracuseStep 5496659 = 8244989) B8244989
theorem B2449295 : Blo 1084620 2449295 := bstep (se 1 (by rfl) ⟨1836971, by rfl⟩ : syracuseStep 2449295 = 3673943) B3673943
theorem B2941373 : Blo 1084620 2941373 := bstep (se 3 (by rfl) ⟨551507, by rfl⟩ : syracuseStep 2941373 = 1103015) B1103015
theorem B1630811 : Blo 1084620 1630811 := bstep (se 1 (by rfl) ⟨1223108, by rfl⟩ : syracuseStep 1630811 = 2446217) B2446217
theorem B20898971 : Blo 1084620 20898971 := bstep (se 1 (by rfl) ⟨15674228, by rfl⟩ : syracuseStep 20898971 = 31348457) B31348457
theorem B1631483 : Blo 1084620 1631483 := bstep (se 1 (by rfl) ⟨1223612, by rfl⟩ : syracuseStep 1631483 = 2447225) B2447225
theorem B2745647 : Blo 1084620 2745647 := bstep (se 1 (by rfl) ⟨2059235, by rfl⟩ : syracuseStep 2745647 = 4118471) B4118471
theorem B1631849 : Blo 1084620 1631849 := bstep (se 2 (by rfl) ⟨611943, by rfl⟩ : syracuseStep 1631849 = 1223887) B1223887
theorem B1631999 : Blo 1084620 1631999 := bstep (se 1 (by rfl) ⟨1223999, by rfl⟩ : syracuseStep 1631999 = 2447999) B2447999
theorem B7825207 : Blo 1084620 7825207 := bstep (se 1 (by rfl) ⟨5868905, by rfl⟩ : syracuseStep 7825207 = 11737811) B11737811
theorem B9398567 : Blo 1084620 9398567 := bstep (se 1 (by rfl) ⟨7048925, by rfl⟩ : syracuseStep 9398567 = 14097851) B14097851
theorem B23849417 : Blo 1084620 23849417 := bstep (se 2 (by rfl) ⟨8943531, by rfl⟩ : syracuseStep 23849417 = 17887063) B17887063
theorem B2746831 : Blo 1084620 2746831 := bstep (se 1 (by rfl) ⟨2060123, by rfl⟩ : syracuseStep 2746831 = 4120247) B4120247
theorem B4123133 : Blo 1084620 4123133 := bstep (se 3 (by rfl) ⟨773087, by rfl⟩ : syracuseStep 4123133 = 1546175) B1546175
theorem B1632809 : Blo 1084620 1632809 := bstep (se 2 (by rfl) ⟨612303, by rfl⟩ : syracuseStep 1632809 = 1224607) B1224607
theorem B6188345 : Blo 1084620 6188345 := bstep (se 2 (by rfl) ⟨2320629, by rfl⟩ : syracuseStep 6188345 = 4641259) B4641259
theorem B2747803 : Blo 1084620 2747803 := bstep (se 1 (by rfl) ⟨2060852, by rfl⟩ : syracuseStep 2747803 = 4121705) B4121705
theorem B1830505 : Blo 1084620 1830505 := bstep (se 2 (by rfl) ⟨686439, by rfl⟩ : syracuseStep 1830505 = 1372879) B1372879
theorem B2748127 : Blo 1084620 2748127 := bstep (se 1 (by rfl) ⟨2061095, by rfl⟩ : syracuseStep 2748127 = 4122191) B4122191
theorem B3665735 : Blo 1084620 3665735 := bstep (se 1 (by rfl) ⟨2749301, by rfl⟩ : syracuseStep 3665735 = 5498603) B5498603
theorem B5501357 : Blo 1084620 5501357 := bstep (se 3 (by rfl) ⟨1031504, by rfl⟩ : syracuseStep 5501357 = 2063009) B2063009
theorem B5501519 : Blo 1084620 5501519 := bstep (se 1 (by rfl) ⟨4126139, by rfl⟩ : syracuseStep 5501519 = 8252279) B8252279
theorem B1372783 : Blo 1084620 1372783 := bstep (se 1 (by rfl) ⟨1029587, by rfl⟩ : syracuseStep 1372783 = 2059175) B2059175
theorem B2978587 : Blo 1084620 2978587 := bstep (se 1 (by rfl) ⟨2233940, by rfl⟩ : syracuseStep 2978587 = 4467881) B4467881
theorem B2749241 : Blo 1084620 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B1831801 : Blo 1084620 1831801 := bstep (se 2 (by rfl) ⟨686925, by rfl⟩ : syracuseStep 1831801 = 1373851) B1373851
theorem B3666977 : Blo 1084620 3666977 := bstep (se 2 (by rfl) ⟨1375116, by rfl⟩ : syracuseStep 3666977 = 2750233) B2750233
theorem B47707217 : Blo 1084620 47707217 := bstep (se 2 (by rfl) ⟨17890206, by rfl⟩ : syracuseStep 47707217 = 35780413) B35780413
theorem B2749535 : Blo 1084620 2749535 := bstep (se 1 (by rfl) ⟨2062151, by rfl⟩ : syracuseStep 2749535 = 4124303) B4124303
theorem B1373375 : Blo 1084620 1373375 := bstep (se 1 (by rfl) ⟨1030031, by rfl⟩ : syracuseStep 1373375 = 2060063) B2060063
theorem B5502329 : Blo 1084620 5502329 := bstep (se 2 (by rfl) ⟨2063373, by rfl⟩ : syracuseStep 5502329 = 4126747) B4126747
theorem B5863589 : Blo 1084620 5863589 := bstep (se 4 (by rfl) ⟨549711, by rfl⟩ : syracuseStep 5863589 = 1099423) B1099423
theorem B8485217 : Blo 1084620 8485217 := bstep (se 2 (by rfl) ⟨3181956, by rfl⟩ : syracuseStep 8485217 = 6363913) B6363913
theorem B1833799 : Blo 1084620 1833799 := bstep (se 1 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 1833799 = 2750699) B2750699
theorem B4127719 : Blo 1084620 4127719 := bstep (se 1 (by rfl) ⟨3095789, by rfl⟩ : syracuseStep 4127719 = 6191579) B6191579
theorem B3669191 : Blo 1084620 3669191 := bstep (se 1 (by rfl) ⟨2751893, by rfl⟩ : syracuseStep 3669191 = 5503787) B5503787
theorem B1835291 : Blo 1084620 1835291 := bstep (se 1 (by rfl) ⟨1376468, by rfl⟩ : syracuseStep 1835291 = 2752937) B2752937
theorem B3671783 : Blo 1084620 3671783 := bstep (se 1 (by rfl) ⟨2753837, by rfl⟩ : syracuseStep 3671783 = 5507675) B5507675
theorem B3672971 : Blo 1084620 3672971 := bstep (se 1 (by rfl) ⟨2754728, by rfl⟩ : syracuseStep 3672971 = 5509457) B5509457
theorem B8260541 : Blo 1084620 8260541 := bstep (se 3 (by rfl) ⟨1548851, by rfl⟩ : syracuseStep 8260541 = 3097703) B3097703
theorem B5213459 : Blo 1084620 5213459 := bstep (se 1 (by rfl) ⟨3910094, by rfl⟩ : syracuseStep 5213459 = 7820189) B7820189
theorem B17633047 : Blo 1084620 17633047 := bstep (se 1 (by rfl) ⟨13224785, by rfl⟩ : syracuseStep 17633047 = 26449571) B26449571
theorem B1085471 : Blo 1084620 1085471 := bstep (se 1 (by rfl) ⟨814103, by rfl⟩ : syracuseStep 1085471 = 1628207) B1628207
theorem B5214287 : Blo 1084620 5214287 := bstep (se 1 (by rfl) ⟨3910715, by rfl⟩ : syracuseStep 5214287 = 7821431) B7821431
theorem B1085935 : Blo 1084620 1085935 := bstep (se 1 (by rfl) ⟨814451, by rfl⟩ : syracuseStep 1085935 = 1628903) B1628903
theorem B1085951 : Blo 1084620 1085951 := bstep (se 1 (by rfl) ⟨814463, by rfl⟩ : syracuseStep 1085951 = 1628927) B1628927
theorem B1086159 : Blo 1084620 1086159 := bstep (se 1 (by rfl) ⟨814619, by rfl⟩ : syracuseStep 1086159 = 1629239) B1629239
theorem B3478241 : Blo 1084620 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B5509943 : Blo 1084620 5509943 := bstep (se 1 (by rfl) ⟨4132457, by rfl⟩ : syracuseStep 5509943 = 8264915) B8264915
theorem B42407023 : Blo 1084620 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B1087207 : Blo 1084620 1087207 := bstep (se 1 (by rfl) ⟨815405, by rfl⟩ : syracuseStep 1087207 = 1630811) B1630811
theorem B16094953 : Blo 1084620 16094953 := bstep (se 2 (by rfl) ⟨6035607, by rfl⟩ : syracuseStep 16094953 = 12071215) B12071215
theorem B13932647 : Blo 1084620 13932647 := bstep (se 1 (by rfl) ⟨10449485, by rfl⟩ : syracuseStep 13932647 = 20898971) B20898971
theorem B1087655 : Blo 1084620 1087655 := bstep (se 1 (by rfl) ⟨815741, by rfl⟩ : syracuseStep 1087655 = 1631483) B1631483
theorem B3971449 : Blo 1084620 3971449 := bstep (se 2 (by rfl) ⟨1489293, by rfl⟩ : syracuseStep 3971449 = 2978587) B2978587
theorem B1087899 : Blo 1084620 1087899 := bstep (se 1 (by rfl) ⟨815924, by rfl⟩ : syracuseStep 1087899 = 1631849) B1631849
theorem B1087999 : Blo 1084620 1087999 := bstep (se 1 (by rfl) ⟨815999, by rfl⟩ : syracuseStep 1087999 = 1631999) B1631999
theorem B6265711 : Blo 1084620 6265711 := bstep (se 1 (by rfl) ⟨4699283, by rfl⟩ : syracuseStep 6265711 = 9398567) B9398567
theorem B15899611 : Blo 1084620 15899611 := bstep (se 1 (by rfl) ⟨11924708, by rfl⟩ : syracuseStep 15899611 = 23849417) B23849417
theorem B1088539 : Blo 1084620 1088539 := bstep (se 1 (by rfl) ⟨816404, by rfl⟩ : syracuseStep 1088539 = 1632809) B1632809
theorem B4955501 : Blo 1084620 4955501 := bstep (se 3 (by rfl) ⟨929156, by rfl⟩ : syracuseStep 4955501 = 1858313) B1858313
theorem B15867575 : Blo 1084620 15867575 := bstep (se 1 (by rfl) ⟨11900681, by rfl⟩ : syracuseStep 15867575 = 23801363) B23801363
theorem B2826523 : Blo 1084620 2826523 := bstep (se 1 (by rfl) ⟨2119892, by rfl⟩ : syracuseStep 2826523 = 4239785) B4239785
theorem B59581595 : Blo 1084620 59581595 := bstep (se 1 (by rfl) ⟨44686196, by rfl⟩ : syracuseStep 59581595 = 89372393) B89372393
theorem B3909059 : Blo 1084620 3909059 := bstep (se 1 (by rfl) ⟨2931794, by rfl⟩ : syracuseStep 3909059 = 5863589) B5863589
theorem B13937615 : Blo 1084620 13937615 := bstep (se 1 (by rfl) ⟨10453211, by rfl⟩ : syracuseStep 13937615 = 20906423) B20906423
theorem B8465903 : Blo 1084620 8465903 := bstep (se 1 (by rfl) ⟨6349427, by rfl⟩ : syracuseStep 8465903 = 12698855) B12698855
theorem B7843661 : Blo 1084620 7843661 := bstep (se 3 (by rfl) ⟨1470686, by rfl⟩ : syracuseStep 7843661 = 2941373) B2941373
theorem B9285455 : Blo 1084620 9285455 := bstep (se 1 (by rfl) ⟨6964091, by rfl⟩ : syracuseStep 9285455 = 13928183) B13928183
theorem B10433609 : Blo 1084620 10433609 := bstep (se 2 (by rfl) ⟨3912603, by rfl⟩ : syracuseStep 10433609 = 7825207) B7825207
theorem B8238671 : Blo 1084620 8238671 := bstep (se 1 (by rfl) ⟨6179003, by rfl⟩ : syracuseStep 8238671 = 12358007) B12358007
theorem B3094355 : Blo 1084620 3094355 := bstep (se 1 (by rfl) ⟨2320766, by rfl⟩ : syracuseStep 3094355 = 4641533) B4641533
theorem B4405279 : Blo 1084620 4405279 := bstep (se 1 (by rfl) ⟨3303959, by rfl⟩ : syracuseStep 4405279 = 6607919) B6607919
theorem B12565367 : Blo 1084620 12565367 := bstep (se 1 (by rfl) ⟨9424025, by rfl⟩ : syracuseStep 12565367 = 18848051) B18848051
theorem B2440673 : Blo 1084620 2440673 := bstep (se 2 (by rfl) ⟨915252, by rfl⟩ : syracuseStep 2440673 = 1830505) B1830505
theorem B2474047 : Blo 1084620 2474047 := bstep (se 1 (by rfl) ⟨1855535, by rfl⟩ : syracuseStep 2474047 = 3711071) B3711071
theorem B3096701 : Blo 1084620 3096701 := bstep (se 3 (by rfl) ⟨580631, by rfl⟩ : syracuseStep 3096701 = 1161263) B1161263
theorem B2442401 : Blo 1084620 2442401 := bstep (se 2 (by rfl) ⟨915900, by rfl⟩ : syracuseStep 2442401 = 1831801) B1831801
theorem B8242559 : Blo 1084620 8242559 := bstep (se 1 (by rfl) ⟨6181919, by rfl⟩ : syracuseStep 8242559 = 12363839) B12363839
theorem B1886123 : Blo 1084620 1886123 := bstep (se 1 (by rfl) ⟨1414592, by rfl⟩ : syracuseStep 1886123 = 2829185) B2829185
theorem B11913311 : Blo 1084620 11913311 := bstep (se 1 (by rfl) ⟨8934983, by rfl⟩ : syracuseStep 11913311 = 17869967) B17869967
theorem B2443823 : Blo 1084620 2443823 := bstep (se 1 (by rfl) ⟨1832867, by rfl⟩ : syracuseStep 2443823 = 3665735) B3665735
theorem B5229299 : Blo 1084620 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B4180747 : Blo 1084620 4180747 := bstep (se 1 (by rfl) ⟨3135560, by rfl⟩ : syracuseStep 4180747 = 6271121) B6271121
theorem B270912437 : Blo 1084620 270912437 := bstep (se 5 (by rfl) ⟨12699020, by rfl⟩ : syracuseStep 270912437 = 25398041) B25398041
theorem B2444651 : Blo 1084620 2444651 := bstep (se 1 (by rfl) ⟨1833488, by rfl⟩ : syracuseStep 2444651 = 3666977) B3666977
theorem B31804811 : Blo 1084620 31804811 := bstep (se 1 (by rfl) ⟨23853608, by rfl⟩ : syracuseStep 31804811 = 47707217) B47707217
theorem B2445065 : Blo 1084620 2445065 := bstep (se 2 (by rfl) ⟨916899, by rfl⟩ : syracuseStep 2445065 = 1833799) B1833799
theorem B5656811 : Blo 1084620 5656811 := bstep (se 1 (by rfl) ⟨4242608, by rfl⟩ : syracuseStep 5656811 = 8485217) B8485217
theorem B2446127 : Blo 1084620 2446127 := bstep (se 1 (by rfl) ⟨1834595, by rfl⟩ : syracuseStep 2446127 = 3669191) B3669191
theorem B1626983 : Blo 1084620 1626983 := bstep (se 1 (by rfl) ⟨1220237, by rfl⟩ : syracuseStep 1626983 = 2440475) B2440475
theorem B1627007 : Blo 1084620 1627007 := bstep (se 1 (by rfl) ⟨1220255, by rfl⟩ : syracuseStep 1627007 = 2440511) B2440511
theorem B1627247 : Blo 1084620 1627247 := bstep (se 1 (by rfl) ⟨1220435, by rfl⟩ : syracuseStep 1627247 = 2440871) B2440871
theorem B1627295 : Blo 1084620 1627295 := bstep (se 1 (by rfl) ⟨1220471, by rfl⟩ : syracuseStep 1627295 = 2440943) B2440943
theorem B7820651 : Blo 1084620 7820651 := bstep (se 1 (by rfl) ⟨5865488, by rfl⟩ : syracuseStep 7820651 = 11730977) B11730977
theorem B2447315 : Blo 1084620 2447315 := bstep (se 1 (by rfl) ⟨1835486, by rfl⟩ : syracuseStep 2447315 = 3670973) B3670973
theorem B2447387 : Blo 1084620 2447387 := bstep (se 1 (by rfl) ⟨1835540, by rfl⟩ : syracuseStep 2447387 = 3671081) B3671081
theorem B29775923 : Blo 1084620 29775923 := bstep (se 1 (by rfl) ⟨22331942, by rfl⟩ : syracuseStep 29775923 = 44663885) B44663885
theorem B2447423 : Blo 1084620 2447423 := bstep (se 1 (by rfl) ⟨1835567, by rfl⟩ : syracuseStep 2447423 = 3671135) B3671135
theorem B1628471 : Blo 1084620 1628471 := bstep (se 1 (by rfl) ⟨1221353, by rfl⟩ : syracuseStep 1628471 = 2442707) B2442707
theorem B1628495 : Blo 1084620 1628495 := bstep (se 1 (by rfl) ⟨1221371, by rfl⟩ : syracuseStep 1628495 = 2442743) B2442743
theorem B1628537 : Blo 1084620 1628537 := bstep (se 2 (by rfl) ⟨610701, by rfl⟩ : syracuseStep 1628537 = 1221403) B1221403
theorem B1628651 : Blo 1084620 1628651 := bstep (se 1 (by rfl) ⟨1221488, by rfl⟩ : syracuseStep 1628651 = 2442977) B2442977
theorem B3529271 : Blo 1084620 3529271 := bstep (se 1 (by rfl) ⟨2646953, by rfl⟩ : syracuseStep 3529271 = 5293907) B5293907
theorem B60250697 : Blo 1084620 60250697 := bstep (se 2 (by rfl) ⟨22594011, by rfl⟩ : syracuseStep 60250697 = 45188023) B45188023
theorem B2447963 : Blo 1084620 2447963 := bstep (se 1 (by rfl) ⟨1835972, by rfl⟩ : syracuseStep 2447963 = 3671945) B3671945
theorem B3299969 : Blo 1084620 3299969 := bstep (se 2 (by rfl) ⟨1237488, by rfl⟩ : syracuseStep 3299969 = 2474977) B2474977
theorem B1629161 : Blo 1084620 1629161 := bstep (se 2 (by rfl) ⟨610935, by rfl⟩ : syracuseStep 1629161 = 1221871) B1221871
theorem B1629167 : Blo 1084620 1629167 := bstep (se 1 (by rfl) ⟨1221875, by rfl⟩ : syracuseStep 1629167 = 2443751) B2443751
theorem B66903185 : Blo 1084620 66903185 := bstep (se 2 (by rfl) ⟨25088694, by rfl⟩ : syracuseStep 66903185 = 50177389) B50177389
theorem B1629359 : Blo 1084620 1629359 := bstep (se 1 (by rfl) ⟨1222019, by rfl⟩ : syracuseStep 1629359 = 2444039) B2444039
theorem B2317871 : Blo 1084620 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B4120217 : Blo 1084620 4120217 := bstep (se 2 (by rfl) ⟨1545081, by rfl⟩ : syracuseStep 4120217 = 3090163) B3090163
theorem B2612911 : Blo 1084620 2612911 := bstep (se 1 (by rfl) ⟨1959683, by rfl⟩ : syracuseStep 2612911 = 3919367) B3919367
theorem B2449079 : Blo 1084620 2449079 := bstep (se 1 (by rfl) ⟨1836809, by rfl⟩ : syracuseStep 2449079 = 3673619) B3673619
theorem B1630391 : Blo 1084620 1630391 := bstep (se 1 (by rfl) ⟨1222793, by rfl⟩ : syracuseStep 1630391 = 2445587) B2445587
theorem B3662333 : Blo 1084620 3662333 := bstep (se 3 (by rfl) ⟨686687, by rfl⟩ : syracuseStep 3662333 = 1373375) B1373375
theorem B3662441 : Blo 1084620 3662441 := bstep (se 2 (by rfl) ⟨1373415, by rfl⟩ : syracuseStep 3662441 = 2746831) B2746831
theorem B1631231 : Blo 1084620 1631231 := bstep (se 1 (by rfl) ⟨1223423, by rfl⟩ : syracuseStep 1631231 = 2446847) B2446847
theorem B1631303 : Blo 1084620 1631303 := bstep (se 1 (by rfl) ⟨1223477, by rfl⟩ : syracuseStep 1631303 = 2446955) B2446955
theorem B6186203 : Blo 1084620 6186203 := bstep (se 1 (by rfl) ⟨4639652, by rfl⟩ : syracuseStep 6186203 = 9279305) B9279305
theorem B4121887 : Blo 1084620 4121887 := bstep (se 1 (by rfl) ⟨3091415, by rfl⟩ : syracuseStep 4121887 = 6182831) B6182831
theorem B1631609 : Blo 1084620 1631609 := bstep (se 2 (by rfl) ⟨611853, by rfl⟩ : syracuseStep 1631609 = 1223707) B1223707
theorem B5498279 : Blo 1084620 5498279 := bstep (se 1 (by rfl) ⟨4123709, by rfl⟩ : syracuseStep 5498279 = 8247419) B8247419
theorem B3663737 : Blo 1084620 3663737 := bstep (se 2 (by rfl) ⟨1373901, by rfl⟩ : syracuseStep 3663737 = 2747803) B2747803
theorem B13396103 : Blo 1084620 13396103 := bstep (se 1 (by rfl) ⟨10047077, by rfl⟩ : syracuseStep 13396103 = 20094155) B20094155
theorem B3664169 : Blo 1084620 3664169 := bstep (se 2 (by rfl) ⟨1374063, by rfl⟩ : syracuseStep 3664169 = 2748127) B2748127
theorem B1632671 : Blo 1084620 1632671 := bstep (se 1 (by rfl) ⟨1224503, by rfl⟩ : syracuseStep 1632671 = 2449007) B2449007
theorem B3664439 : Blo 1084620 3664439 := bstep (se 1 (by rfl) ⟨2748329, by rfl⟩ : syracuseStep 3664439 = 5496659) B5496659
theorem B1632863 : Blo 1084620 1632863 := bstep (se 1 (by rfl) ⟨1224647, by rfl⟩ : syracuseStep 1632863 = 2449295) B2449295
theorem B2059577 : Blo 1084620 2059577 := bstep (se 2 (by rfl) ⟨772341, by rfl⟩ : syracuseStep 2059577 = 1544683) B1544683
theorem B1830377 : Blo 1084620 1830377 := bstep (se 2 (by rfl) ⟨686391, by rfl⟩ : syracuseStep 1830377 = 1372783) B1372783
theorem B1830431 : Blo 1084620 1830431 := bstep (se 1 (by rfl) ⟨1372823, by rfl⟩ : syracuseStep 1830431 = 2745647) B2745647
theorem B2322407 : Blo 1084620 2322407 := bstep (se 1 (by rfl) ⟨1741805, by rfl⟩ : syracuseStep 2322407 = 3483611) B3483611
theorem B15659057 : Blo 1084620 15659057 := bstep (se 2 (by rfl) ⟨5872146, by rfl⟩ : syracuseStep 15659057 = 11744293) B11744293
theorem B2748755 : Blo 1084620 2748755 := bstep (se 1 (by rfl) ⟨2061566, by rfl⟩ : syracuseStep 2748755 = 4123133) B4123133
theorem B4125563 : Blo 1084620 4125563 := bstep (se 1 (by rfl) ⟨3094172, by rfl⟩ : syracuseStep 4125563 = 6188345) B6188345
theorem B3667571 : Blo 1084620 3667571 := bstep (se 1 (by rfl) ⟨2750678, by rfl⟩ : syracuseStep 3667571 = 5501357) B5501357
theorem B3667679 : Blo 1084620 3667679 := bstep (se 1 (by rfl) ⟨2750759, by rfl⟩ : syracuseStep 3667679 = 5501519) B5501519
theorem B1832827 : Blo 1084620 1832827 := bstep (se 1 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 1832827 = 2749241) B2749241
theorem B1833023 : Blo 1084620 1833023 := bstep (se 1 (by rfl) ⟨1374767, by rfl⟩ : syracuseStep 1833023 = 2749535) B2749535
theorem B2062523 : Blo 1084620 2062523 := bstep (se 1 (by rfl) ⟨1546892, by rfl⟩ : syracuseStep 2062523 = 3093785) B3093785
theorem B31291595 : Blo 1084620 31291595 := bstep (se 1 (by rfl) ⟨23468696, by rfl⟩ : syracuseStep 31291595 = 46937393) B46937393
theorem B3668219 : Blo 1084620 3668219 := bstep (se 1 (by rfl) ⟨2751164, by rfl⟩ : syracuseStep 3668219 = 5502329) B5502329
theorem B5503625 : Blo 1084620 5503625 := bstep (se 2 (by rfl) ⟨2063859, by rfl⟩ : syracuseStep 5503625 = 4127719) B4127719
theorem B2063161 : Blo 1084620 2063161 := bstep (se 2 (by rfl) ⟨773685, by rfl⟩ : syracuseStep 2063161 = 1547371) B1547371
theorem B6618017 : Blo 1084620 6618017 := bstep (se 2 (by rfl) ⟨2481756, by rfl⟩ : syracuseStep 6618017 = 4963513) B4963513
theorem B13925519 : Blo 1084620 13925519 := bstep (se 1 (by rfl) ⟨10444139, by rfl⟩ : syracuseStep 13925519 = 20888279) B20888279
theorem B6192719 : Blo 1084620 6192719 := bstep (se 1 (by rfl) ⟨4644539, by rfl⟩ : syracuseStep 6192719 = 9289079) B9289079
theorem B3309239 : Blo 1084620 3309239 := bstep (se 1 (by rfl) ⟨2481929, by rfl⟩ : syracuseStep 3309239 = 4963859) B4963859
theorem B4128509 : Blo 1084620 4128509 := bstep (se 3 (by rfl) ⟨774095, by rfl⟩ : syracuseStep 4128509 = 1548191) B1548191
theorem B2064467 : Blo 1084620 2064467 := bstep (se 1 (by rfl) ⟨1548350, by rfl⟩ : syracuseStep 2064467 = 3096701) B3096701
theorem B3768697 : Blo 1084620 3768697 := bstep (se 2 (by rfl) ⟨1413261, by rfl⟩ : syracuseStep 3768697 = 2826523) B2826523
theorem B9275309 : Blo 1084620 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B5507027 : Blo 1084620 5507027 := bstep (se 1 (by rfl) ⟨4130270, by rfl⟩ : syracuseStep 5507027 = 8260541) B8260541
theorem B3475639 : Blo 1084620 3475639 := bstep (se 1 (by rfl) ⟨2606729, by rfl⟩ : syracuseStep 3475639 = 5213459) B5213459
theorem B21203207 : Blo 1084620 21203207 := bstep (se 1 (by rfl) ⟨15902405, by rfl⟩ : syracuseStep 21203207 = 31804811) B31804811
theorem B3476191 : Blo 1084620 3476191 := bstep (se 1 (by rfl) ⟨2607143, by rfl⟩ : syracuseStep 3476191 = 5214287) B5214287
theorem B3673295 : Blo 1084620 3673295 := bstep (se 1 (by rfl) ⟨2754971, by rfl⟩ : syracuseStep 3673295 = 5509943) B5509943
theorem B1084655 : Blo 1084620 1084655 := bstep (se 1 (by rfl) ⟨813491, by rfl⟩ : syracuseStep 1084655 = 1626983) B1626983
theorem B1084671 : Blo 1084620 1084671 := bstep (se 1 (by rfl) ⟨813503, by rfl⟩ : syracuseStep 1084671 = 1627007) B1627007
theorem B1084831 : Blo 1084620 1084831 := bstep (se 1 (by rfl) ⟨813623, by rfl⟩ : syracuseStep 1084831 = 1627247) B1627247
theorem B1084863 : Blo 1084620 1084863 := bstep (se 1 (by rfl) ⟨813647, by rfl⟩ : syracuseStep 1084863 = 1627295) B1627295
theorem B5213767 : Blo 1084620 5213767 := bstep (se 1 (by rfl) ⟨3910325, by rfl⟩ : syracuseStep 5213767 = 7820651) B7820651
theorem B5574329 : Blo 1084620 5574329 := bstep (se 2 (by rfl) ⟨2090373, by rfl⟩ : syracuseStep 5574329 = 4180747) B4180747
theorem B1085647 : Blo 1084620 1085647 := bstep (se 1 (by rfl) ⟨814235, by rfl⟩ : syracuseStep 1085647 = 1628471) B1628471
theorem B1085663 : Blo 1084620 1085663 := bstep (se 1 (by rfl) ⟨814247, by rfl⟩ : syracuseStep 1085663 = 1628495) B1628495
theorem B1085691 : Blo 1084620 1085691 := bstep (se 1 (by rfl) ⟨814268, by rfl⟩ : syracuseStep 1085691 = 1628537) B1628537
theorem B1085767 : Blo 1084620 1085767 := bstep (se 1 (by rfl) ⟨814325, by rfl⟩ : syracuseStep 1085767 = 1628651) B1628651
theorem B2199979 : Blo 1084620 2199979 := bstep (se 1 (by rfl) ⟨1649984, by rfl⟩ : syracuseStep 2199979 = 3299969) B3299969
theorem B1086107 : Blo 1084620 1086107 := bstep (se 1 (by rfl) ⟨814580, by rfl⟩ : syracuseStep 1086107 = 1629161) B1629161
theorem B1086111 : Blo 1084620 1086111 := bstep (se 1 (by rfl) ⟨814583, by rfl⟩ : syracuseStep 1086111 = 1629167) B1629167
theorem B44602123 : Blo 1084620 44602123 := bstep (se 1 (by rfl) ⟨33451592, by rfl⟩ : syracuseStep 44602123 = 66903185) B66903185
theorem B1086239 : Blo 1084620 1086239 := bstep (se 1 (by rfl) ⟨814679, by rfl⟩ : syracuseStep 1086239 = 1629359) B1629359
theorem B1545247 : Blo 1084620 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B1086927 : Blo 1084620 1086927 := bstep (se 1 (by rfl) ⟨815195, by rfl⟩ : syracuseStep 1086927 = 1630391) B1630391
theorem B1087487 : Blo 1084620 1087487 := bstep (se 1 (by rfl) ⟨815615, by rfl⟩ : syracuseStep 1087487 = 1631231) B1631231
theorem B1087535 : Blo 1084620 1087535 := bstep (se 1 (by rfl) ⟨815651, by rfl⟩ : syracuseStep 1087535 = 1631303) B1631303
theorem B1087739 : Blo 1084620 1087739 := bstep (se 1 (by rfl) ⟨815804, by rfl⟩ : syracuseStep 1087739 = 1631609) B1631609
theorem B9411389 : Blo 1084620 9411389 := bstep (se 3 (by rfl) ⟨1764635, by rfl⟩ : syracuseStep 9411389 = 3529271) B3529271
theorem B1088447 : Blo 1084620 1088447 := bstep (se 1 (by rfl) ⟨816335, by rfl⟩ : syracuseStep 1088447 = 1632671) B1632671
theorem B1088575 : Blo 1084620 1088575 := bstep (se 1 (by rfl) ⟨816431, by rfl⟩ : syracuseStep 1088575 = 1632863) B1632863
theorem B1220251 : Blo 1084620 1220251 := bstep (se 1 (by rfl) ⟨915188, by rfl⟩ : syracuseStep 1220251 = 1830377) B1830377
theorem B5643935 : Blo 1084620 5643935 := bstep (se 1 (by rfl) ⟨4232951, by rfl⟩ : syracuseStep 5643935 = 8465903) B8465903
theorem B1220287 : Blo 1084620 1220287 := bstep (se 1 (by rfl) ⟨915215, by rfl⟩ : syracuseStep 1220287 = 1830431) B1830431
theorem B1548271 : Blo 1084620 1548271 := bstep (se 1 (by rfl) ⟨1161203, by rfl⟩ : syracuseStep 1548271 = 2322407) B2322407
theorem B5873705 : Blo 1084620 5873705 := bstep (se 2 (by rfl) ⟨2202639, by rfl⟩ : syracuseStep 5873705 = 4405279) B4405279
theorem B6955739 : Blo 1084620 6955739 := bstep (se 1 (by rfl) ⟨5216804, by rfl⟩ : syracuseStep 6955739 = 10433609) B10433609
theorem B1222015 : Blo 1084620 1222015 := bstep (se 1 (by rfl) ⟨916511, by rfl⟩ : syracuseStep 1222015 = 1833023) B1833023
theorem B9283679 : Blo 1084620 9283679 := bstep (se 1 (by rfl) ⟨6962759, by rfl⟩ : syracuseStep 9283679 = 13925519) B13925519
theorem B3483881 : Blo 1084620 3483881 := bstep (se 2 (by rfl) ⟨1306455, by rfl⟩ : syracuseStep 3483881 = 2612911) B2612911
theorem B2206159 : Blo 1084620 2206159 := bstep (se 1 (by rfl) ⟨1654619, by rfl⟩ : syracuseStep 2206159 = 3309239) B3309239
theorem B1223527 : Blo 1084620 1223527 := bstep (se 1 (by rfl) ⟨917645, by rfl⟩ : syracuseStep 1223527 = 1835291) B1835291
theorem B15084829 : Blo 1084620 15084829 := bstep (se 3 (by rfl) ⟨2828405, by rfl⟩ : syracuseStep 15084829 = 5656811) B5656811
theorem B7942207 : Blo 1084620 7942207 := bstep (se 1 (by rfl) ⟨5956655, by rfl⟩ : syracuseStep 7942207 = 11913311) B11913311
theorem B3486199 : Blo 1084620 3486199 := bstep (se 1 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 3486199 = 5229299) B5229299
theorem B21181061 : Blo 1084620 21181061 := bstep (se 4 (by rfl) ⟨1985724, by rfl⟩ : syracuseStep 21181061 = 3971449) B3971449
theorem B9288431 : Blo 1084620 9288431 := bstep (se 1 (by rfl) ⟨6966323, by rfl⟩ : syracuseStep 9288431 = 13932647) B13932647
theorem B23510729 : Blo 1084620 23510729 := bstep (se 2 (by rfl) ⟨8816523, by rfl⟩ : syracuseStep 23510729 = 17633047) B17633047
theorem B5029661 : Blo 1084620 5029661 := bstep (se 3 (by rfl) ⟨943061, by rfl⟩ : syracuseStep 5029661 = 1886123) B1886123
theorem B2441555 : Blo 1084620 2441555 := bstep (se 1 (by rfl) ⟨1831166, by rfl⟩ : syracuseStep 2441555 = 3662333) B3662333
theorem B2441627 : Blo 1084620 2441627 := bstep (se 1 (by rfl) ⟨1831220, by rfl⟩ : syracuseStep 2441627 = 3662441) B3662441
theorem B2606039 : Blo 1084620 2606039 := bstep (se 1 (by rfl) ⟨1954529, by rfl⟩ : syracuseStep 2606039 = 3909059) B3909059
theorem B2442491 : Blo 1084620 2442491 := bstep (se 1 (by rfl) ⟨1831868, by rfl⟩ : syracuseStep 2442491 = 3663737) B3663737
theorem B8930735 : Blo 1084620 8930735 := bstep (se 1 (by rfl) ⟨6698051, by rfl⟩ : syracuseStep 8930735 = 13396103) B13396103
theorem B56542697 : Blo 1084620 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B2442779 : Blo 1084620 2442779 := bstep (se 1 (by rfl) ⟨1832084, by rfl⟩ : syracuseStep 2442779 = 3664169) B3664169
theorem B2442959 : Blo 1084620 2442959 := bstep (se 1 (by rfl) ⟨1832219, by rfl⟩ : syracuseStep 2442959 = 3664439) B3664439
theorem B9291743 : Blo 1084620 9291743 := bstep (se 1 (by rfl) ⟨6968807, by rfl⟩ : syracuseStep 9291743 = 13937615) B13937615
theorem B2443769 : Blo 1084620 2443769 := bstep (se 2 (by rfl) ⟨916413, by rfl⟩ : syracuseStep 2443769 = 1832827) B1832827
theorem B5229107 : Blo 1084620 5229107 := bstep (se 1 (by rfl) ⟨3921830, by rfl⟩ : syracuseStep 5229107 = 7843661) B7843661
theorem B10439371 : Blo 1084620 10439371 := bstep (se 1 (by rfl) ⟨7829528, by rfl⟩ : syracuseStep 10439371 = 15659057) B15659057
theorem B5492447 : Blo 1084620 5492447 := bstep (se 1 (by rfl) ⟨4119335, by rfl⟩ : syracuseStep 5492447 = 8238671) B8238671
theorem B2445047 : Blo 1084620 2445047 := bstep (se 1 (by rfl) ⟨1833785, by rfl⟩ : syracuseStep 2445047 = 3667571) B3667571
theorem B2445119 : Blo 1084620 2445119 := bstep (se 1 (by rfl) ⟨1833839, by rfl⟩ : syracuseStep 2445119 = 3667679) B3667679
theorem B20861063 : Blo 1084620 20861063 := bstep (se 1 (by rfl) ⟨15645797, by rfl⟩ : syracuseStep 20861063 = 31291595) B31291595
theorem B2445479 : Blo 1084620 2445479 := bstep (se 1 (by rfl) ⟨1834109, by rfl⟩ : syracuseStep 2445479 = 3668219) B3668219
theorem B8376911 : Blo 1084620 8376911 := bstep (se 1 (by rfl) ⟨6282683, by rfl⟩ : syracuseStep 8376911 = 12565367) B12565367
theorem B4412011 : Blo 1084620 4412011 := bstep (se 1 (by rfl) ⟨3309008, by rfl⟩ : syracuseStep 4412011 = 6618017) B6618017
theorem B1627115 : Blo 1084620 1627115 := bstep (se 1 (by rfl) ⟨1220336, by rfl⟩ : syracuseStep 1627115 = 2440673) B2440673
theorem B3298729 : Blo 1084620 3298729 := bstep (se 2 (by rfl) ⟨1237023, by rfl⟩ : syracuseStep 3298729 = 2474047) B2474047
theorem B1628267 : Blo 1084620 1628267 := bstep (se 1 (by rfl) ⟨1221200, by rfl⟩ : syracuseStep 1628267 = 2442401) B2442401
theorem B5495039 : Blo 1084620 5495039 := bstep (se 1 (by rfl) ⟨4121279, by rfl⟩ : syracuseStep 5495039 = 8242559) B8242559
theorem B2447855 : Blo 1084620 2447855 := bstep (se 1 (by rfl) ⟨1835891, by rfl⟩ : syracuseStep 2447855 = 3671783) B3671783
theorem B1629215 : Blo 1084620 1629215 := bstep (se 1 (by rfl) ⟨1221911, by rfl⟩ : syracuseStep 1629215 = 2443823) B2443823
theorem B5495849 : Blo 1084620 5495849 := bstep (se 2 (by rfl) ⟨2060943, by rfl⟩ : syracuseStep 5495849 = 4121887) B4121887
theorem B2448647 : Blo 1084620 2448647 := bstep (se 1 (by rfl) ⟨1836485, by rfl⟩ : syracuseStep 2448647 = 3672971) B3672971
theorem B180608291 : Blo 1084620 180608291 := bstep (se 1 (by rfl) ⟨135456218, by rfl⟩ : syracuseStep 180608291 = 270912437) B270912437
theorem B1629767 : Blo 1084620 1629767 := bstep (se 1 (by rfl) ⟨1222325, by rfl⟩ : syracuseStep 1629767 = 2444651) B2444651
theorem B1630043 : Blo 1084620 1630043 := bstep (se 1 (by rfl) ⟨1222532, by rfl⟩ : syracuseStep 1630043 = 2445065) B2445065
theorem B158884253 : Blo 1084620 158884253 := bstep (se 3 (by rfl) ⟨29790797, by rfl⟩ : syracuseStep 158884253 = 59581595) B59581595
theorem B1630751 : Blo 1084620 1630751 := bstep (se 1 (by rfl) ⟨1223063, by rfl⟩ : syracuseStep 1630751 = 2446127) B2446127
theorem B1631543 : Blo 1084620 1631543 := bstep (se 1 (by rfl) ⟨1223657, by rfl⟩ : syracuseStep 1631543 = 2447315) B2447315
theorem B1631591 : Blo 1084620 1631591 := bstep (se 1 (by rfl) ⟨1223693, by rfl⟩ : syracuseStep 1631591 = 2447387) B2447387
theorem B19850615 : Blo 1084620 19850615 := bstep (se 1 (by rfl) ⟨14887961, by rfl⟩ : syracuseStep 19850615 = 29775923) B29775923
theorem B1631615 : Blo 1084620 1631615 := bstep (se 1 (by rfl) ⟨1223711, by rfl⟩ : syracuseStep 1631615 = 2447423) B2447423
theorem B40167131 : Blo 1084620 40167131 := bstep (se 1 (by rfl) ⟨30125348, by rfl⟩ : syracuseStep 40167131 = 60250697) B60250697
theorem B1631975 : Blo 1084620 1631975 := bstep (se 1 (by rfl) ⟨1223981, by rfl⟩ : syracuseStep 1631975 = 2447963) B2447963
theorem B3303667 : Blo 1084620 3303667 := bstep (se 1 (by rfl) ⟨2477750, by rfl⟩ : syracuseStep 3303667 = 4955501) B4955501
theorem B2746811 : Blo 1084620 2746811 := bstep (se 1 (by rfl) ⟨2060108, by rfl⟩ : syracuseStep 2746811 = 4120217) B4120217
theorem B10578383 : Blo 1084620 10578383 := bstep (se 1 (by rfl) ⟨7933787, by rfl⟩ : syracuseStep 10578383 = 15867575) B15867575
theorem B1632719 : Blo 1084620 1632719 := bstep (se 1 (by rfl) ⟨1224539, by rfl⟩ : syracuseStep 1632719 = 2449079) B2449079
theorem B5500061 : Blo 1084620 5500061 := bstep (se 3 (by rfl) ⟨1031261, by rfl⟩ : syracuseStep 5500061 = 2062523) B2062523
theorem B4124135 : Blo 1084620 4124135 := bstep (se 1 (by rfl) ⟨3093101, by rfl⟩ : syracuseStep 4124135 = 6186203) B6186203
theorem B3665519 : Blo 1084620 3665519 := bstep (se 1 (by rfl) ⟨2749139, by rfl⟩ : syracuseStep 3665519 = 5498279) B5498279
theorem B1373051 : Blo 1084620 1373051 := bstep (se 1 (by rfl) ⟨1029788, by rfl⟩ : syracuseStep 1373051 = 2059577) B2059577
theorem B21459937 : Blo 1084620 21459937 := bstep (se 2 (by rfl) ⟨8047476, by rfl⟩ : syracuseStep 21459937 = 16094953) B16094953
theorem B6190303 : Blo 1084620 6190303 := bstep (se 1 (by rfl) ⟨4642727, by rfl⟩ : syracuseStep 6190303 = 9285455) B9285455
theorem B1832503 : Blo 1084620 1832503 := bstep (se 1 (by rfl) ⟨1374377, by rfl⟩ : syracuseStep 1832503 = 2748755) B2748755
theorem B2750375 : Blo 1084620 2750375 := bstep (se 1 (by rfl) ⟨2062781, by rfl⟩ : syracuseStep 2750375 = 4125563) B4125563
theorem B2750881 : Blo 1084620 2750881 := bstep (se 2 (by rfl) ⟨1031580, by rfl⟩ : syracuseStep 2750881 = 2063161) B2063161
theorem B8354281 : Blo 1084620 8354281 := bstep (se 2 (by rfl) ⟨3132855, by rfl⟩ : syracuseStep 8354281 = 6265711) B6265711
theorem B2062903 : Blo 1084620 2062903 := bstep (se 1 (by rfl) ⟨1547177, by rfl⟩ : syracuseStep 2062903 = 3094355) B3094355
theorem B21199481 : Blo 1084620 21199481 := bstep (se 2 (by rfl) ⟨7949805, by rfl⟩ : syracuseStep 21199481 = 15899611) B15899611
theorem B3669083 : Blo 1084620 3669083 := bstep (se 1 (by rfl) ⟨2751812, by rfl⟩ : syracuseStep 3669083 = 5503625) B5503625
theorem B4128479 : Blo 1084620 4128479 := bstep (se 1 (by rfl) ⟨3096359, by rfl⟩ : syracuseStep 4128479 = 6192719) B6192719
theorem B2752339 : Blo 1084620 2752339 := bstep (se 1 (by rfl) ⟨2064254, by rfl⟩ : syracuseStep 2752339 = 4128509) B4128509
theorem B5505245 : Blo 1084620 5505245 := bstep (se 3 (by rfl) ⟨1032233, by rfl⟩ : syracuseStep 5505245 = 2064467) B2064467
theorem B1737359 : Blo 1084620 1737359 := bstep (se 1 (by rfl) ⟨1303019, by rfl⟩ : syracuseStep 1737359 = 2606039) B2606039
theorem B3671351 : Blo 1084620 3671351 := bstep (se 1 (by rfl) ⟨2753513, by rfl⟩ : syracuseStep 3671351 = 5507027) B5507027
theorem B6194495 : Blo 1084620 6194495 := bstep (se 1 (by rfl) ⟨4645871, by rfl⟩ : syracuseStep 6194495 = 9291743) B9291743
theorem B11733221 : Blo 1084620 11733221 := bstep (se 4 (by rfl) ⟨1099989, by rfl⟩ : syracuseStep 11733221 = 2199979) B2199979
theorem B11766181 : Blo 1084620 11766181 := bstep (se 4 (by rfl) ⟨1103079, by rfl⟩ : syracuseStep 11766181 = 2206159) B2206159
theorem B1084743 : Blo 1084620 1084743 := bstep (se 1 (by rfl) ⟨813557, by rfl⟩ : syracuseStep 1084743 = 1627115) B1627115
theorem B1085511 : Blo 1084620 1085511 := bstep (se 1 (by rfl) ⟨814133, by rfl⟩ : syracuseStep 1085511 = 1628267) B1628267
theorem B1086143 : Blo 1084620 1086143 := bstep (se 1 (by rfl) ⟨814607, by rfl⟩ : syracuseStep 1086143 = 1629215) B1629215
theorem B6951689 : Blo 1084620 6951689 := bstep (se 2 (by rfl) ⟨2606883, by rfl⟩ : syracuseStep 6951689 = 5213767) B5213767
theorem B1086511 : Blo 1084620 1086511 := bstep (se 1 (by rfl) ⟨814883, by rfl⟩ : syracuseStep 1086511 = 1629767) B1629767
theorem B1086695 : Blo 1084620 1086695 := bstep (se 1 (by rfl) ⟨815021, by rfl⟩ : syracuseStep 1086695 = 1630043) B1630043
theorem B10589609 : Blo 1084620 10589609 := bstep (se 2 (by rfl) ⟨3971103, by rfl⟩ : syracuseStep 10589609 = 7942207) B7942207
theorem B1087167 : Blo 1084620 1087167 := bstep (se 1 (by rfl) ⟨815375, by rfl⟩ : syracuseStep 1087167 = 1630751) B1630751
theorem B1087695 : Blo 1084620 1087695 := bstep (se 1 (by rfl) ⟨815771, by rfl⟩ : syracuseStep 1087695 = 1631543) B1631543
theorem B1087727 : Blo 1084620 1087727 := bstep (se 1 (by rfl) ⟨815795, by rfl⟩ : syracuseStep 1087727 = 1631591) B1631591
theorem B1087743 : Blo 1084620 1087743 := bstep (se 1 (by rfl) ⟨815807, by rfl⟩ : syracuseStep 1087743 = 1631615) B1631615
theorem B1087983 : Blo 1084620 1087983 := bstep (se 1 (by rfl) ⟨815987, by rfl⟩ : syracuseStep 1087983 = 1631975) B1631975
theorem B28613249 : Blo 1084620 28613249 := bstep (se 2 (by rfl) ⟨10729968, by rfl⟩ : syracuseStep 28613249 = 21459937) B21459937
theorem B7052255 : Blo 1084620 7052255 := bstep (se 1 (by rfl) ⟨5289191, by rfl⟩ : syracuseStep 7052255 = 10578383) B10578383
theorem B1088479 : Blo 1084620 1088479 := bstep (se 1 (by rfl) ⟨816359, by rfl⟩ : syracuseStep 1088479 = 1632719) B1632719
theorem B4398305 : Blo 1084620 4398305 := bstep (se 2 (by rfl) ⟨1649364, by rfl⟩ : syracuseStep 4398305 = 3298729) B3298729
theorem B14132987 : Blo 1084620 14132987 := bstep (se 1 (by rfl) ⟨10599740, by rfl⟩ : syracuseStep 14132987 = 21199481) B21199481
theorem B15673819 : Blo 1084620 15673819 := bstep (se 1 (by rfl) ⟨11755364, by rfl⟩ : syracuseStep 15673819 = 23510729) B23510729
theorem B3353107 : Blo 1084620 3353107 := bstep (se 1 (by rfl) ⟨2514830, by rfl⟩ : syracuseStep 3353107 = 5029661) B5029661
theorem B5024929 : Blo 1084620 5024929 := bstep (se 2 (by rfl) ⟨1884348, by rfl⟩ : syracuseStep 5024929 = 3768697) B3768697
theorem B37695131 : Blo 1084620 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B14135471 : Blo 1084620 14135471 := bstep (se 1 (by rfl) ⟨10601603, by rfl⟩ : syracuseStep 14135471 = 21203207) B21203207
theorem B3486071 : Blo 1084620 3486071 := bstep (se 1 (by rfl) ⟨2614553, by rfl⟩ : syracuseStep 3486071 = 5229107) B5229107
theorem B3716219 : Blo 1084620 3716219 := bstep (se 1 (by rfl) ⟨2787164, by rfl⟩ : syracuseStep 3716219 = 5574329) B5574329
theorem B13907375 : Blo 1084620 13907375 := bstep (se 1 (by rfl) ⟨10430531, by rfl⟩ : syracuseStep 13907375 = 20861063) B20861063
theorem B4634185 : Blo 1084620 4634185 := bstep (se 2 (by rfl) ⟨1737819, by rfl⟩ : syracuseStep 4634185 = 3475639) B3475639
theorem B4404889 : Blo 1084620 4404889 := bstep (se 2 (by rfl) ⟨1651833, by rfl⟩ : syracuseStep 4404889 = 3303667) B3303667
theorem B5584607 : Blo 1084620 5584607 := bstep (se 1 (by rfl) ⟨4188455, by rfl⟩ : syracuseStep 5584607 = 8376911) B8376911
theorem B4634921 : Blo 1084620 4634921 := bstep (se 2 (by rfl) ⟨1738095, by rfl⟩ : syracuseStep 4634921 = 3476191) B3476191
theorem B6274259 : Blo 1084620 6274259 := bstep (se 1 (by rfl) ⟨4705694, by rfl⟩ : syracuseStep 6274259 = 9411389) B9411389
theorem B120405527 : Blo 1084620 120405527 := bstep (se 1 (by rfl) ⟨90304145, by rfl⟩ : syracuseStep 120405527 = 180608291) B180608291
theorem B3915803 : Blo 1084620 3915803 := bstep (se 1 (by rfl) ⟨2936852, by rfl⟩ : syracuseStep 3915803 = 5873705) B5873705
theorem B105922835 : Blo 1084620 105922835 := bstep (se 1 (by rfl) ⟨79442126, by rfl⟩ : syracuseStep 105922835 = 158884253) B158884253
theorem B4637159 : Blo 1084620 4637159 := bstep (se 1 (by rfl) ⟨3477869, by rfl⟩ : syracuseStep 4637159 = 6955739) B6955739
theorem B5882681 : Blo 1084620 5882681 := bstep (se 2 (by rfl) ⟨2206005, by rfl⟩ : syracuseStep 5882681 = 4412011) B4412011
theorem B2443337 : Blo 1084620 2443337 := bstep (se 2 (by rfl) ⟨916251, by rfl⟩ : syracuseStep 2443337 = 1832503) B1832503
theorem B2443679 : Blo 1084620 2443679 := bstep (se 1 (by rfl) ⟨1832759, by rfl⟩ : syracuseStep 2443679 = 3665519) B3665519
theorem B2446055 : Blo 1084620 2446055 := bstep (se 1 (by rfl) ⟨1834541, by rfl⟩ : syracuseStep 2446055 = 3669083) B3669083
theorem B1627001 : Blo 1084620 1627001 := bstep (se 2 (by rfl) ⟨610125, by rfl⟩ : syracuseStep 1627001 = 1220251) B1220251
theorem B1627049 : Blo 1084620 1627049 := bstep (se 2 (by rfl) ⟨610143, by rfl⟩ : syracuseStep 1627049 = 1220287) B1220287
theorem B1627703 : Blo 1084620 1627703 := bstep (se 1 (by rfl) ⟨1220777, by rfl⟩ : syracuseStep 1627703 = 2441555) B2441555
theorem B1627751 : Blo 1084620 1627751 := bstep (se 1 (by rfl) ⟨1220813, by rfl⟩ : syracuseStep 1627751 = 2441627) B2441627
theorem B1628327 : Blo 1084620 1628327 := bstep (se 1 (by rfl) ⟨1221245, by rfl⟩ : syracuseStep 1628327 = 2442491) B2442491
theorem B5953823 : Blo 1084620 5953823 := bstep (se 1 (by rfl) ⟨4465367, by rfl⟩ : syracuseStep 5953823 = 8930735) B8930735
theorem B1628519 : Blo 1084620 1628519 := bstep (se 1 (by rfl) ⟨1221389, by rfl⟩ : syracuseStep 1628519 = 2442779) B2442779
theorem B1628639 : Blo 1084620 1628639 := bstep (se 1 (by rfl) ⟨1221479, by rfl⟩ : syracuseStep 1628639 = 2442959) B2442959
theorem B6183539 : Blo 1084620 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B1629179 : Blo 1084620 1629179 := bstep (se 1 (by rfl) ⟨1221884, by rfl⟩ : syracuseStep 1629179 = 2443769) B2443769
theorem B56482829 : Blo 1084620 56482829 := bstep (se 3 (by rfl) ⟨10590530, by rfl⟩ : syracuseStep 56482829 = 21181061) B21181061
theorem B1629353 : Blo 1084620 1629353 := bstep (se 2 (by rfl) ⟨611007, by rfl⟩ : syracuseStep 1629353 = 1222015) B1222015
theorem B2448863 : Blo 1084620 2448863 := bstep (se 1 (by rfl) ⟨1836647, by rfl⟩ : syracuseStep 2448863 = 3673295) B3673295
theorem B3661469 : Blo 1084620 3661469 := bstep (se 3 (by rfl) ⟨686525, by rfl⟩ : syracuseStep 3661469 = 1373051) B1373051
theorem B3661631 : Blo 1084620 3661631 := bstep (se 1 (by rfl) ⟨2746223, by rfl⟩ : syracuseStep 3661631 = 5492447) B5492447
theorem B1630031 : Blo 1084620 1630031 := bstep (se 1 (by rfl) ⟨1222523, by rfl⟩ : syracuseStep 1630031 = 2445047) B2445047
theorem B1630079 : Blo 1084620 1630079 := bstep (se 1 (by rfl) ⟨1222559, by rfl⟩ : syracuseStep 1630079 = 2445119) B2445119
theorem B1630319 : Blo 1084620 1630319 := bstep (se 1 (by rfl) ⟨1222739, by rfl⟩ : syracuseStep 1630319 = 2445479) B2445479
theorem B13919161 : Blo 1084620 13919161 := bstep (se 2 (by rfl) ⟨5219685, by rfl⟩ : syracuseStep 13919161 = 10439371) B10439371
theorem B1631369 : Blo 1084620 1631369 := bstep (se 2 (by rfl) ⟨611763, by rfl⟩ : syracuseStep 1631369 = 1223527) B1223527
theorem B3663359 : Blo 1084620 3663359 := bstep (se 1 (by rfl) ⟨2747519, by rfl⟩ : syracuseStep 3663359 = 5495039) B5495039
theorem B1631903 : Blo 1084620 1631903 := bstep (se 1 (by rfl) ⟨1223927, by rfl⟩ : syracuseStep 1631903 = 2447855) B2447855
theorem B20113105 : Blo 1084620 20113105 := bstep (se 2 (by rfl) ⟨7542414, by rfl⟩ : syracuseStep 20113105 = 15084829) B15084829
theorem B107112349 : Blo 1084620 107112349 := bstep (se 3 (by rfl) ⟨20083565, by rfl⟩ : syracuseStep 107112349 = 40167131) B40167131
theorem B3663899 : Blo 1084620 3663899 := bstep (se 1 (by rfl) ⟨2747924, by rfl⟩ : syracuseStep 3663899 = 5495849) B5495849
theorem B1632431 : Blo 1084620 1632431 := bstep (se 1 (by rfl) ⟨1224323, by rfl⟩ : syracuseStep 1632431 = 2448647) B2448647
theorem B3762623 : Blo 1084620 3762623 := bstep (se 1 (by rfl) ⟨2821967, by rfl⟩ : syracuseStep 3762623 = 5643935) B5643935
theorem B4648265 : Blo 1084620 4648265 := bstep (se 2 (by rfl) ⟨1743099, by rfl⟩ : syracuseStep 4648265 = 3486199) B3486199
theorem B13233743 : Blo 1084620 13233743 := bstep (se 1 (by rfl) ⟨9925307, by rfl⟩ : syracuseStep 13233743 = 19850615) B19850615
theorem B59469497 : Blo 1084620 59469497 := bstep (se 2 (by rfl) ⟨22301061, by rfl⟩ : syracuseStep 59469497 = 44602123) B44602123
theorem B2060329 : Blo 1084620 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B6189119 : Blo 1084620 6189119 := bstep (se 1 (by rfl) ⟨4641839, by rfl⟩ : syracuseStep 6189119 = 9283679) B9283679
theorem B2322587 : Blo 1084620 2322587 := bstep (se 1 (by rfl) ⟨1741940, by rfl⟩ : syracuseStep 2322587 = 3483881) B3483881
theorem B1831207 : Blo 1084620 1831207 := bstep (se 1 (by rfl) ⟨1373405, by rfl⟩ : syracuseStep 1831207 = 2746811) B2746811
theorem B8253737 : Blo 1084620 8253737 := bstep (se 2 (by rfl) ⟨3095151, by rfl⟩ : syracuseStep 8253737 = 6190303) B6190303
theorem B3666707 : Blo 1084620 3666707 := bstep (se 1 (by rfl) ⟨2750030, by rfl⟩ : syracuseStep 3666707 = 5500061) B5500061
theorem B2749423 : Blo 1084620 2749423 := bstep (se 1 (by rfl) ⟨2062067, by rfl⟩ : syracuseStep 2749423 = 4124135) B4124135
theorem B3667841 : Blo 1084620 3667841 := bstep (se 2 (by rfl) ⟨1375440, by rfl⟩ : syracuseStep 3667841 = 2750881) B2750881
theorem B11139041 : Blo 1084620 11139041 := bstep (se 2 (by rfl) ⟨4177140, by rfl⟩ : syracuseStep 11139041 = 8354281) B8354281
theorem B2750537 : Blo 1084620 2750537 := bstep (se 2 (by rfl) ⟨1031451, by rfl⟩ : syracuseStep 2750537 = 2062903) B2062903
theorem B1833583 : Blo 1084620 1833583 := bstep (se 1 (by rfl) ⟨1375187, by rfl⟩ : syracuseStep 1833583 = 2750375) B2750375
theorem B6192287 : Blo 1084620 6192287 := bstep (se 1 (by rfl) ⟨4644215, by rfl⟩ : syracuseStep 6192287 = 9288431) B9288431
theorem B3669785 : Blo 1084620 3669785 := bstep (se 2 (by rfl) ⟨1376169, by rfl⟩ : syracuseStep 3669785 = 2752339) B2752339
theorem B2752319 : Blo 1084620 2752319 := bstep (se 1 (by rfl) ⟨2064239, by rfl⟩ : syracuseStep 2752319 = 4128479) B4128479
theorem B2064361 : Blo 1084620 2064361 := bstep (se 2 (by rfl) ⟨774135, by rfl⟩ : syracuseStep 2064361 = 1548271) B1548271
theorem B3670163 : Blo 1084620 3670163 := bstep (se 1 (by rfl) ⟨2752622, by rfl⟩ : syracuseStep 3670163 = 5505245) B5505245
theorem B70615223 : Blo 1084620 70615223 := bstep (se 1 (by rfl) ⟨52961417, by rfl⟩ : syracuseStep 70615223 = 105922835) B105922835
theorem B4129663 : Blo 1084620 4129663 := bstep (se 1 (by rfl) ⟨3097247, by rfl⟩ : syracuseStep 4129663 = 6194495) B6194495
theorem B1084667 : Blo 1084620 1084667 := bstep (se 1 (by rfl) ⟨813500, by rfl⟩ : syracuseStep 1084667 = 1627001) B1627001
theorem B1084699 : Blo 1084620 1084699 := bstep (se 1 (by rfl) ⟨813524, by rfl⟩ : syracuseStep 1084699 = 1627049) B1627049
theorem B1085135 : Blo 1084620 1085135 := bstep (se 1 (by rfl) ⟨813851, by rfl⟩ : syracuseStep 1085135 = 1627703) B1627703
theorem B1085167 : Blo 1084620 1085167 := bstep (se 1 (by rfl) ⟨813875, by rfl⟩ : syracuseStep 1085167 = 1627751) B1627751
theorem B1085551 : Blo 1084620 1085551 := bstep (se 1 (by rfl) ⟨814163, by rfl⟩ : syracuseStep 1085551 = 1628327) B1628327
theorem B3969215 : Blo 1084620 3969215 := bstep (se 1 (by rfl) ⟨2976911, by rfl⟩ : syracuseStep 3969215 = 5953823) B5953823
theorem B1085679 : Blo 1084620 1085679 := bstep (se 1 (by rfl) ⟨814259, by rfl⟩ : syracuseStep 1085679 = 1628519) B1628519
theorem B1085759 : Blo 1084620 1085759 := bstep (se 1 (by rfl) ⟨814319, by rfl⟩ : syracuseStep 1085759 = 1628639) B1628639
theorem B19075499 : Blo 1084620 19075499 := bstep (se 1 (by rfl) ⟨14306624, by rfl⟩ : syracuseStep 19075499 = 28613249) B28613249
theorem B1086119 : Blo 1084620 1086119 := bstep (se 1 (by rfl) ⟨814589, by rfl⟩ : syracuseStep 1086119 = 1629179) B1629179
theorem B37655219 : Blo 1084620 37655219 := bstep (se 1 (by rfl) ⟨28241414, by rfl⟩ : syracuseStep 37655219 = 56482829) B56482829
theorem B1086235 : Blo 1084620 1086235 := bstep (se 1 (by rfl) ⟨814676, by rfl⟩ : syracuseStep 1086235 = 1629353) B1629353
theorem B1086687 : Blo 1084620 1086687 := bstep (se 1 (by rfl) ⟨815015, by rfl⟩ : syracuseStep 1086687 = 1630031) B1630031
theorem B1086719 : Blo 1084620 1086719 := bstep (se 1 (by rfl) ⟨815039, by rfl⟩ : syracuseStep 1086719 = 1630079) B1630079
theorem B1086879 : Blo 1084620 1086879 := bstep (se 1 (by rfl) ⟨815159, by rfl⟩ : syracuseStep 1086879 = 1630319) B1630319
theorem B1087579 : Blo 1084620 1087579 := bstep (se 1 (by rfl) ⟨815684, by rfl⟩ : syracuseStep 1087579 = 1631369) B1631369
theorem B1087935 : Blo 1084620 1087935 := bstep (se 1 (by rfl) ⟨815951, by rfl⟩ : syracuseStep 1087935 = 1631903) B1631903
theorem B1088287 : Blo 1084620 1088287 := bstep (se 1 (by rfl) ⟨816215, by rfl⟩ : syracuseStep 1088287 = 1632431) B1632431
theorem B5873185 : Blo 1084620 5873185 := bstep (se 2 (by rfl) ⟨2202444, by rfl⟩ : syracuseStep 5873185 = 4404889) B4404889
theorem B8822495 : Blo 1084620 8822495 := bstep (se 1 (by rfl) ⟨6616871, by rfl⟩ : syracuseStep 8822495 = 13233743) B13233743
theorem B1548391 : Blo 1084620 1548391 := bstep (se 1 (by rfl) ⟨1161293, by rfl⟩ : syracuseStep 1548391 = 2322587) B2322587
theorem B3089947 : Blo 1084620 3089947 := bstep (se 1 (by rfl) ⟨2317460, by rfl⟩ : syracuseStep 3089947 = 4634921) B4634921
theorem B3091439 : Blo 1084620 3091439 := bstep (se 1 (by rfl) ⟨2318579, by rfl⟩ : syracuseStep 3091439 = 4637159) B4637159
theorem B1158239 : Blo 1084620 1158239 := bstep (se 1 (by rfl) ⟨868679, by rfl⟩ : syracuseStep 1158239 = 1737359) B1737359
theorem B18558881 : Blo 1084620 18558881 := bstep (se 2 (by rfl) ⟨6959580, by rfl⟩ : syracuseStep 18558881 = 13919161) B13919161
theorem B26817473 : Blo 1084620 26817473 := bstep (se 2 (by rfl) ⟨10056552, by rfl⟩ : syracuseStep 26817473 = 20113105) B20113105
theorem B142816465 : Blo 1084620 142816465 := bstep (se 2 (by rfl) ⟨53556174, by rfl⟩ : syracuseStep 142816465 = 107112349) B107112349
theorem B4634459 : Blo 1084620 4634459 := bstep (se 1 (by rfl) ⟨3475844, by rfl⟩ : syracuseStep 4634459 = 6951689) B6951689
theorem B4470809 : Blo 1084620 4470809 := bstep (se 2 (by rfl) ⟨1676553, by rfl⟩ : syracuseStep 4470809 = 3353107) B3353107
theorem B7059739 : Blo 1084620 7059739 := bstep (se 1 (by rfl) ⟨5294804, by rfl⟩ : syracuseStep 7059739 = 10589609) B10589609
theorem B6699905 : Blo 1084620 6699905 := bstep (se 2 (by rfl) ⟨2512464, by rfl⟩ : syracuseStep 6699905 = 5024929) B5024929
theorem B4701503 : Blo 1084620 4701503 := bstep (se 1 (by rfl) ⟨3526127, by rfl⟩ : syracuseStep 4701503 = 7052255) B7052255
theorem B2440979 : Blo 1084620 2440979 := bstep (se 1 (by rfl) ⟨1830734, by rfl⟩ : syracuseStep 2440979 = 3661469) B3661469
theorem B2441087 : Blo 1084620 2441087 := bstep (se 1 (by rfl) ⟨1830815, by rfl⟩ : syracuseStep 2441087 = 3661631) B3661631
theorem B2441609 : Blo 1084620 2441609 := bstep (se 2 (by rfl) ⟨915603, by rfl⟩ : syracuseStep 2441609 = 1831207) B1831207
theorem B2442239 : Blo 1084620 2442239 := bstep (se 1 (by rfl) ⟨1831679, by rfl⟩ : syracuseStep 2442239 = 3663359) B3663359
theorem B9421991 : Blo 1084620 9421991 := bstep (se 1 (by rfl) ⟨7066493, by rfl⟩ : syracuseStep 9421991 = 14132987) B14132987
theorem B2442599 : Blo 1084620 2442599 := bstep (se 1 (by rfl) ⟨1831949, by rfl⟩ : syracuseStep 2442599 = 3663899) B3663899
theorem B2508415 : Blo 1084620 2508415 := bstep (se 1 (by rfl) ⟨1881311, by rfl⟩ : syracuseStep 2508415 = 3762623) B3762623
theorem B6178913 : Blo 1084620 6178913 := bstep (se 2 (by rfl) ⟨2317092, by rfl⟩ : syracuseStep 6178913 = 4634185) B4634185
theorem B3098843 : Blo 1084620 3098843 := bstep (se 1 (by rfl) ⟨2324132, by rfl⟩ : syracuseStep 3098843 = 4648265) B4648265
theorem B9423647 : Blo 1084620 9423647 := bstep (se 1 (by rfl) ⟨7067735, by rfl⟩ : syracuseStep 9423647 = 14135471) B14135471
theorem B2444471 : Blo 1084620 2444471 := bstep (se 1 (by rfl) ⟨1833353, by rfl⟩ : syracuseStep 2444471 = 3666707) B3666707
theorem B2477479 : Blo 1084620 2477479 := bstep (se 1 (by rfl) ⟨1858109, by rfl⟩ : syracuseStep 2477479 = 3716219) B3716219
theorem B2444777 : Blo 1084620 2444777 := bstep (se 2 (by rfl) ⟨916791, by rfl⟩ : syracuseStep 2444777 = 1833583) B1833583
theorem B2445227 : Blo 1084620 2445227 := bstep (se 1 (by rfl) ⟨1833920, by rfl⟩ : syracuseStep 2445227 = 3667841) B3667841
theorem B7426027 : Blo 1084620 7426027 := bstep (se 1 (by rfl) ⟨5569520, by rfl⟩ : syracuseStep 7426027 = 11139041) B11139041
theorem B4182839 : Blo 1084620 4182839 := bstep (se 1 (by rfl) ⟨3137129, by rfl⟩ : syracuseStep 4182839 = 6274259) B6274259
theorem B80270351 : Blo 1084620 80270351 := bstep (se 1 (by rfl) ⟨60202763, by rfl⟩ : syracuseStep 80270351 = 120405527) B120405527
theorem B2446523 : Blo 1084620 2446523 := bstep (se 1 (by rfl) ⟨1834892, by rfl⟩ : syracuseStep 2446523 = 3669785) B3669785
theorem B10442141 : Blo 1084620 10442141 := bstep (se 3 (by rfl) ⟨1957901, by rfl⟩ : syracuseStep 10442141 = 3915803) B3915803
theorem B3921787 : Blo 1084620 3921787 := bstep (se 1 (by rfl) ⟨2941340, by rfl⟩ : syracuseStep 3921787 = 5882681) B5882681
theorem B2447567 : Blo 1084620 2447567 := bstep (se 1 (by rfl) ⟨1835675, by rfl⟩ : syracuseStep 2447567 = 3671351) B3671351
theorem B1628891 : Blo 1084620 1628891 := bstep (se 1 (by rfl) ⟨1221668, by rfl⟩ : syracuseStep 1628891 = 2443337) B2443337
theorem B1629119 : Blo 1084620 1629119 := bstep (se 1 (by rfl) ⟨1221839, by rfl⟩ : syracuseStep 1629119 = 2443679) B2443679
theorem B1630703 : Blo 1084620 1630703 := bstep (se 1 (by rfl) ⟨1223027, by rfl⟩ : syracuseStep 1630703 = 2446055) B2446055
theorem B15688241 : Blo 1084620 15688241 := bstep (se 2 (by rfl) ⟨5883090, by rfl⟩ : syracuseStep 15688241 = 11766181) B11766181
theorem B20898425 : Blo 1084620 20898425 := bstep (se 2 (by rfl) ⟨7836909, by rfl⟩ : syracuseStep 20898425 = 15673819) B15673819
theorem B4122359 : Blo 1084620 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B1632575 : Blo 1084620 1632575 := bstep (se 1 (by rfl) ⟨1224431, by rfl⟩ : syracuseStep 1632575 = 2448863) B2448863
theorem B2747105 : Blo 1084620 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B31288589 : Blo 1084620 31288589 := bstep (se 3 (by rfl) ⟨5866610, by rfl⟩ : syracuseStep 31288589 = 11733221) B11733221
theorem B3665897 : Blo 1084620 3665897 := bstep (se 2 (by rfl) ⟨1374711, by rfl⟩ : syracuseStep 3665897 = 2749423) B2749423
theorem B59569141 : Blo 1084620 59569141 := bstep (se 5 (by rfl) ⟨2792303, by rfl⟩ : syracuseStep 59569141 = 5584607) B5584607
theorem B25130087 : Blo 1084620 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B39646331 : Blo 1084620 39646331 := bstep (se 1 (by rfl) ⟨29734748, by rfl⟩ : syracuseStep 39646331 = 59469497) B59469497
theorem B4126079 : Blo 1084620 4126079 := bstep (se 1 (by rfl) ⟨3094559, by rfl⟩ : syracuseStep 4126079 = 6189119) B6189119
theorem B5502491 : Blo 1084620 5502491 := bstep (se 1 (by rfl) ⟨4126868, by rfl⟩ : syracuseStep 5502491 = 8253737) B8253737
theorem B2324047 : Blo 1084620 2324047 := bstep (se 1 (by rfl) ⟨1743035, by rfl⟩ : syracuseStep 2324047 = 3486071) B3486071
theorem B11728813 : Blo 1084620 11728813 := bstep (se 3 (by rfl) ⟨2199152, by rfl⟩ : syracuseStep 11728813 = 4398305) B4398305
theorem B9271583 : Blo 1084620 9271583 := bstep (se 1 (by rfl) ⟨6953687, by rfl⟩ : syracuseStep 9271583 = 13907375) B13907375
theorem B1833691 : Blo 1084620 1833691 := bstep (se 1 (by rfl) ⟨1375268, by rfl⟩ : syracuseStep 1833691 = 2750537) B2750537
theorem B4128191 : Blo 1084620 4128191 := bstep (se 1 (by rfl) ⟨3096143, by rfl⟩ : syracuseStep 4128191 = 6192287) B6192287
theorem B1834879 : Blo 1084620 1834879 := bstep (se 1 (by rfl) ⟨1376159, by rfl⟩ : syracuseStep 1834879 = 2752319) B2752319
theorem B2752481 : Blo 1084620 2752481 := bstep (se 2 (by rfl) ⟨1032180, by rfl⟩ : syracuseStep 2752481 = 2064361) B2064361
theorem B2064521 : Blo 1084620 2064521 := bstep (se 2 (by rfl) ⟨774195, by rfl⟩ : syracuseStep 2064521 = 1548391) B1548391
theorem B5506217 : Blo 1084620 5506217 := bstep (se 2 (by rfl) ⟨2064831, by rfl⟩ : syracuseStep 5506217 = 4129663) B4129663
theorem B2065895 : Blo 1084620 2065895 := bstep (se 1 (by rfl) ⟨1549421, by rfl⟩ : syracuseStep 2065895 = 3098843) B3098843
theorem B12716999 : Blo 1084620 12716999 := bstep (se 1 (by rfl) ⟨9537749, by rfl⟩ : syracuseStep 12716999 = 19075499) B19075499
theorem B25103479 : Blo 1084620 25103479 := bstep (se 1 (by rfl) ⟨18827609, by rfl⟩ : syracuseStep 25103479 = 37655219) B37655219
theorem B2788559 : Blo 1084620 2788559 := bstep (se 1 (by rfl) ⟨2091419, by rfl⟩ : syracuseStep 2788559 = 4182839) B4182839
theorem B53513567 : Blo 1084620 53513567 := bstep (se 1 (by rfl) ⟨40135175, by rfl⟩ : syracuseStep 53513567 = 80270351) B80270351
theorem B1085927 : Blo 1084620 1085927 := bstep (se 1 (by rfl) ⟨814445, by rfl⟩ : syracuseStep 1085927 = 1628891) B1628891
theorem B1086079 : Blo 1084620 1086079 := bstep (se 1 (by rfl) ⟨814559, by rfl⟩ : syracuseStep 1086079 = 1629119) B1629119
theorem B9901369 : Blo 1084620 9901369 := bstep (se 2 (by rfl) ⟨3713013, by rfl⟩ : syracuseStep 9901369 = 7426027) B7426027
theorem B1087135 : Blo 1084620 1087135 := bstep (se 1 (by rfl) ⟨815351, by rfl⟩ : syracuseStep 1087135 = 1630703) B1630703
theorem B10458827 : Blo 1084620 10458827 := bstep (se 1 (by rfl) ⟨7844120, by rfl⟩ : syracuseStep 10458827 = 15688241) B15688241
theorem B13932283 : Blo 1084620 13932283 := bstep (se 1 (by rfl) ⟨10449212, by rfl⟩ : syracuseStep 13932283 = 20898425) B20898425
theorem B1088383 : Blo 1084620 1088383 := bstep (se 1 (by rfl) ⟨816287, by rfl⟩ : syracuseStep 1088383 = 1632575) B1632575
theorem B15638417 : Blo 1084620 15638417 := bstep (se 2 (by rfl) ⟨5864406, by rfl⟩ : syracuseStep 15638417 = 11728813) B11728813
theorem B3088637 : Blo 1084620 3088637 := bstep (se 3 (by rfl) ⟨579119, by rfl⟩ : syracuseStep 3088637 = 1158239) B1158239
theorem B9412985 : Blo 1084620 9412985 := bstep (se 2 (by rfl) ⟨3529869, by rfl⟩ : syracuseStep 9412985 = 7059739) B7059739
theorem B13378213 : Blo 1084620 13378213 := bstep (se 4 (by rfl) ⟨1254207, by rfl⟩ : syracuseStep 13378213 = 2508415) B2508415
theorem B16753391 : Blo 1084620 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B3089639 : Blo 1084620 3089639 := bstep (se 1 (by rfl) ⟨2317229, by rfl⟩ : syracuseStep 3089639 = 4634459) B4634459
theorem B4466603 : Blo 1084620 4466603 := bstep (se 1 (by rfl) ⟨3349952, by rfl⟩ : syracuseStep 4466603 = 6699905) B6699905
theorem B6961427 : Blo 1084620 6961427 := bstep (se 1 (by rfl) ⟨5221070, by rfl⟩ : syracuseStep 6961427 = 10442141) B10442141
theorem B5881663 : Blo 1084620 5881663 := bstep (se 1 (by rfl) ⟨4411247, by rfl⟩ : syracuseStep 5881663 = 8822495) B8822495
theorem B3098729 : Blo 1084620 3098729 := bstep (se 2 (by rfl) ⟨1162023, by rfl⟩ : syracuseStep 3098729 = 2324047) B2324047
theorem B20859059 : Blo 1084620 20859059 := bstep (se 1 (by rfl) ⟨15644294, by rfl⟩ : syracuseStep 20859059 = 31288589) B31288589
theorem B5229049 : Blo 1084620 5229049 := bstep (se 2 (by rfl) ⟨1960893, by rfl⟩ : syracuseStep 5229049 = 3921787) B3921787
theorem B12372587 : Blo 1084620 12372587 := bstep (se 1 (by rfl) ⟨9279440, by rfl⟩ : syracuseStep 12372587 = 18558881) B18558881
theorem B2443931 : Blo 1084620 2443931 := bstep (se 1 (by rfl) ⟨1832948, by rfl⟩ : syracuseStep 2443931 = 3665897) B3665897
theorem B17878315 : Blo 1084620 17878315 := bstep (se 1 (by rfl) ⟨13408736, by rfl⟩ : syracuseStep 17878315 = 26817473) B26817473
theorem B26430887 : Blo 1084620 26430887 := bstep (se 1 (by rfl) ⟨19823165, by rfl⟩ : syracuseStep 26430887 = 39646331) B39646331
theorem B12537341 : Blo 1084620 12537341 := bstep (se 3 (by rfl) ⟨2350751, by rfl⟩ : syracuseStep 12537341 = 4701503) B4701503
theorem B2444921 : Blo 1084620 2444921 := bstep (se 2 (by rfl) ⟨916845, by rfl⟩ : syracuseStep 2444921 = 1833691) B1833691
theorem B6181055 : Blo 1084620 6181055 := bstep (se 1 (by rfl) ⟨4635791, by rfl⟩ : syracuseStep 6181055 = 9271583) B9271583
theorem B2446505 : Blo 1084620 2446505 := bstep (se 2 (by rfl) ⟨917439, by rfl⟩ : syracuseStep 2446505 = 1834879) B1834879
theorem B1627319 : Blo 1084620 1627319 := bstep (se 1 (by rfl) ⟨1220489, by rfl⟩ : syracuseStep 1627319 = 2440979) B2440979
theorem B1627391 : Blo 1084620 1627391 := bstep (se 1 (by rfl) ⟨1220543, by rfl⟩ : syracuseStep 1627391 = 2441087) B2441087
theorem B2446775 : Blo 1084620 2446775 := bstep (se 1 (by rfl) ⟨1835081, by rfl⟩ : syracuseStep 2446775 = 3670163) B3670163
theorem B47076815 : Blo 1084620 47076815 := bstep (se 1 (by rfl) ⟨35307611, by rfl⟩ : syracuseStep 47076815 = 70615223) B70615223
theorem B1627739 : Blo 1084620 1627739 := bstep (se 1 (by rfl) ⟨1220804, by rfl⟩ : syracuseStep 1627739 = 2441609) B2441609
theorem B1628159 : Blo 1084620 1628159 := bstep (se 1 (by rfl) ⟨1221119, by rfl⟩ : syracuseStep 1628159 = 2442239) B2442239
theorem B6281327 : Blo 1084620 6281327 := bstep (se 1 (by rfl) ⟨4710995, by rfl⟩ : syracuseStep 6281327 = 9421991) B9421991
theorem B1628399 : Blo 1084620 1628399 := bstep (se 1 (by rfl) ⟨1221299, by rfl⟩ : syracuseStep 1628399 = 2442599) B2442599
theorem B4119275 : Blo 1084620 4119275 := bstep (se 1 (by rfl) ⟨3089456, by rfl⟩ : syracuseStep 4119275 = 6178913) B6178913
theorem B6282431 : Blo 1084620 6282431 := bstep (se 1 (by rfl) ⟨4711823, by rfl⟩ : syracuseStep 6282431 = 9423647) B9423647
theorem B4119929 : Blo 1084620 4119929 := bstep (se 2 (by rfl) ⟨1544973, by rfl⟩ : syracuseStep 4119929 = 3089947) B3089947
theorem B1629647 : Blo 1084620 1629647 := bstep (se 1 (by rfl) ⟨1222235, by rfl⟩ : syracuseStep 1629647 = 2444471) B2444471
theorem B1629851 : Blo 1084620 1629851 := bstep (se 1 (by rfl) ⟨1222388, by rfl⟩ : syracuseStep 1629851 = 2444777) B2444777
theorem B1630151 : Blo 1084620 1630151 := bstep (se 1 (by rfl) ⟨1222613, by rfl⟩ : syracuseStep 1630151 = 2445227) B2445227
theorem B2646143 : Blo 1084620 2646143 := bstep (se 1 (by rfl) ⟨1984607, by rfl⟩ : syracuseStep 2646143 = 3969215) B3969215
theorem B1631015 : Blo 1084620 1631015 := bstep (se 1 (by rfl) ⟨1223261, by rfl⟩ : syracuseStep 1631015 = 2446523) B2446523
theorem B1631711 : Blo 1084620 1631711 := bstep (se 1 (by rfl) ⟨1223783, by rfl⟩ : syracuseStep 1631711 = 2447567) B2447567
theorem B3303305 : Blo 1084620 3303305 := bstep (se 2 (by rfl) ⟨1238739, by rfl⟩ : syracuseStep 3303305 = 2477479) B2477479
theorem B11922157 : Blo 1084620 11922157 := bstep (se 3 (by rfl) ⟨2235404, by rfl⟩ : syracuseStep 11922157 = 4470809) B4470809
theorem B761687813 : Blo 1084620 761687813 := bstep (se 4 (by rfl) ⟨71408232, by rfl⟩ : syracuseStep 761687813 = 142816465) B142816465
theorem B2748239 : Blo 1084620 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B79425521 : Blo 1084620 79425521 := bstep (se 2 (by rfl) ⟨29784570, by rfl⟩ : syracuseStep 79425521 = 59569141) B59569141
theorem B1831403 : Blo 1084620 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B2060959 : Blo 1084620 2060959 := bstep (se 1 (by rfl) ⟨1545719, by rfl⟩ : syracuseStep 2060959 = 3091439) B3091439
theorem B2750719 : Blo 1084620 2750719 := bstep (se 1 (by rfl) ⟨2063039, by rfl⟩ : syracuseStep 2750719 = 4126079) B4126079
theorem B3668327 : Blo 1084620 3668327 := bstep (se 1 (by rfl) ⟨2751245, by rfl⟩ : syracuseStep 3668327 = 5502491) B5502491
theorem B7830913 : Blo 1084620 7830913 := bstep (se 2 (by rfl) ⟨2936592, by rfl⟩ : syracuseStep 7830913 = 5873185) B5873185
theorem B2752127 : Blo 1084620 2752127 := bstep (se 1 (by rfl) ⟨2064095, by rfl⟩ : syracuseStep 2752127 = 4128191) B4128191
theorem B1834987 : Blo 1084620 1834987 := bstep (se 1 (by rfl) ⟨1376240, by rfl⟩ : syracuseStep 1834987 = 2752481) B2752481
theorem B1376347 : Blo 1084620 1376347 := bstep (se 1 (by rfl) ⟨1032260, by rfl⟩ : syracuseStep 1376347 = 2064521) B2064521
theorem B3670811 : Blo 1084620 3670811 := bstep (se 1 (by rfl) ⟨2753108, by rfl⟩ : syracuseStep 3670811 = 5506217) B5506217
theorem B1377263 : Blo 1084620 1377263 := bstep (se 1 (by rfl) ⟨1032947, by rfl⟩ : syracuseStep 1377263 = 2065895) B2065895
theorem B2065819 : Blo 1084620 2065819 := bstep (se 1 (by rfl) ⟨1549364, by rfl⟩ : syracuseStep 2065819 = 3098729) B3098729
theorem B8358227 : Blo 1084620 8358227 := bstep (se 1 (by rfl) ⟨6268670, by rfl⟩ : syracuseStep 8358227 = 12537341) B12537341
theorem B1084879 : Blo 1084620 1084879 := bstep (se 1 (by rfl) ⟨813659, by rfl⟩ : syracuseStep 1084879 = 1627319) B1627319
theorem B1084927 : Blo 1084620 1084927 := bstep (se 1 (by rfl) ⟨813695, by rfl⟩ : syracuseStep 1084927 = 1627391) B1627391
theorem B1085159 : Blo 1084620 1085159 := bstep (se 1 (by rfl) ⟨813869, by rfl⟩ : syracuseStep 1085159 = 1627739) B1627739
theorem B1085439 : Blo 1084620 1085439 := bstep (se 1 (by rfl) ⟨814079, by rfl⟩ : syracuseStep 1085439 = 1628159) B1628159
theorem B1085599 : Blo 1084620 1085599 := bstep (se 1 (by rfl) ⟨814199, by rfl⟩ : syracuseStep 1085599 = 1628399) B1628399
theorem B1086431 : Blo 1084620 1086431 := bstep (se 1 (by rfl) ⟨814823, by rfl⟩ : syracuseStep 1086431 = 1629647) B1629647
theorem B1086567 : Blo 1084620 1086567 := bstep (se 1 (by rfl) ⟨814925, by rfl⟩ : syracuseStep 1086567 = 1629851) B1629851
theorem B10425611 : Blo 1084620 10425611 := bstep (se 1 (by rfl) ⟨7819208, by rfl⟩ : syracuseStep 10425611 = 15638417) B15638417
theorem B1086767 : Blo 1084620 1086767 := bstep (se 1 (by rfl) ⟨815075, by rfl⟩ : syracuseStep 1086767 = 1630151) B1630151
theorem B1087343 : Blo 1084620 1087343 := bstep (se 1 (by rfl) ⟨815507, by rfl⟩ : syracuseStep 1087343 = 1631015) B1631015
theorem B1087807 : Blo 1084620 1087807 := bstep (se 1 (by rfl) ⟨815855, by rfl⟩ : syracuseStep 1087807 = 1631711) B1631711
theorem B2202203 : Blo 1084620 2202203 := bstep (se 1 (by rfl) ⟨1651652, by rfl⟩ : syracuseStep 2202203 = 3303305) B3303305
theorem B1220935 : Blo 1084620 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B7842217 : Blo 1084620 7842217 := bstep (se 2 (by rfl) ⟨2940831, by rfl⟩ : syracuseStep 7842217 = 5881663) B5881663
theorem B17837617 : Blo 1084620 17837617 := bstep (se 2 (by rfl) ⟨6689106, by rfl⟩ : syracuseStep 17837617 = 13378213) B13378213
theorem B28225525 : Blo 1084620 28225525 := bstep (se 5 (by rfl) ⟨1323071, by rfl⟩ : syracuseStep 28225525 = 2646143) B2646143
theorem B13906039 : Blo 1084620 13906039 := bstep (se 1 (by rfl) ⟨10429529, by rfl⟩ : syracuseStep 13906039 = 20859059) B20859059
theorem B63584837 : Blo 1084620 63584837 := bstep (se 4 (by rfl) ⟨5961078, by rfl⟩ : syracuseStep 63584837 = 11922157) B11922157
theorem B33471305 : Blo 1084620 33471305 := bstep (se 2 (by rfl) ⟨12551739, by rfl⟩ : syracuseStep 33471305 = 25103479) B25103479
theorem B23837753 : Blo 1084620 23837753 := bstep (se 2 (by rfl) ⟨8939157, by rfl⟩ : syracuseStep 23837753 = 17878315) B17878315
theorem B6275323 : Blo 1084620 6275323 := bstep (se 1 (by rfl) ⟨4706492, by rfl⟩ : syracuseStep 6275323 = 9412985) B9412985
theorem B507791875 : Blo 1084620 507791875 := bstep (se 1 (by rfl) ⟨380843906, by rfl⟩ : syracuseStep 507791875 = 761687813) B761687813
theorem B4640951 : Blo 1084620 4640951 := bstep (se 1 (by rfl) ⟨3480713, by rfl⟩ : syracuseStep 4640951 = 6961427) B6961427
theorem B2445551 : Blo 1084620 2445551 := bstep (se 1 (by rfl) ⟨1834163, by rfl⟩ : syracuseStep 2445551 = 3668327) B3668327
theorem B10441217 : Blo 1084620 10441217 := bstep (se 2 (by rfl) ⟨3915456, by rfl⟩ : syracuseStep 10441217 = 7830913) B7830913
theorem B2446649 : Blo 1084620 2446649 := bstep (se 2 (by rfl) ⟨917493, by rfl⟩ : syracuseStep 2446649 = 1834987) B1834987
theorem B8248391 : Blo 1084620 8248391 := bstep (se 1 (by rfl) ⟨6186293, by rfl⟩ : syracuseStep 8248391 = 12372587) B12372587
theorem B1629287 : Blo 1084620 1629287 := bstep (se 1 (by rfl) ⟨1221965, by rfl⟩ : syracuseStep 1629287 = 2443931) B2443931
theorem B8477999 : Blo 1084620 8477999 := bstep (se 1 (by rfl) ⟨6358499, by rfl⟩ : syracuseStep 8477999 = 12716999) B12716999
theorem B1859039 : Blo 1084620 1859039 := bstep (se 1 (by rfl) ⟨1394279, by rfl⟩ : syracuseStep 1859039 = 2788559) B2788559
theorem B35675711 : Blo 1084620 35675711 := bstep (se 1 (by rfl) ⟨26756783, by rfl⟩ : syracuseStep 35675711 = 53513567) B53513567
theorem B17620591 : Blo 1084620 17620591 := bstep (se 1 (by rfl) ⟨13215443, by rfl⟩ : syracuseStep 17620591 = 26430887) B26430887
theorem B1629947 : Blo 1084620 1629947 := bstep (se 1 (by rfl) ⟨1222460, by rfl⟩ : syracuseStep 1629947 = 2444921) B2444921
theorem B4120703 : Blo 1084620 4120703 := bstep (se 1 (by rfl) ⟨3090527, by rfl⟩ : syracuseStep 4120703 = 6181055) B6181055
theorem B6972065 : Blo 1084620 6972065 := bstep (se 2 (by rfl) ⟨2614524, by rfl⟩ : syracuseStep 6972065 = 5229049) B5229049
theorem B1631003 : Blo 1084620 1631003 := bstep (se 1 (by rfl) ⟨1223252, by rfl⟩ : syracuseStep 1631003 = 2446505) B2446505
theorem B1631183 : Blo 1084620 1631183 := bstep (se 1 (by rfl) ⟨1223387, by rfl⟩ : syracuseStep 1631183 = 2446775) B2446775
theorem B31384543 : Blo 1084620 31384543 := bstep (se 1 (by rfl) ⟨23538407, by rfl⟩ : syracuseStep 31384543 = 47076815) B47076815
theorem B6972551 : Blo 1084620 6972551 := bstep (se 1 (by rfl) ⟨5229413, by rfl⟩ : syracuseStep 6972551 = 10458827) B10458827
theorem B4187551 : Blo 1084620 4187551 := bstep (se 1 (by rfl) ⟨3140663, by rfl⟩ : syracuseStep 4187551 = 6281327) B6281327
theorem B2746183 : Blo 1084620 2746183 := bstep (se 1 (by rfl) ⟨2059637, by rfl⟩ : syracuseStep 2746183 = 4119275) B4119275
theorem B4188287 : Blo 1084620 4188287 := bstep (se 1 (by rfl) ⟨3141215, by rfl⟩ : syracuseStep 4188287 = 6282431) B6282431
theorem B2746619 : Blo 1084620 2746619 := bstep (se 1 (by rfl) ⟨2059964, by rfl⟩ : syracuseStep 2746619 = 4119929) B4119929
theorem B2059091 : Blo 1084620 2059091 := bstep (se 1 (by rfl) ⟨1544318, by rfl⟩ : syracuseStep 2059091 = 3088637) B3088637
theorem B11168927 : Blo 1084620 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B2059759 : Blo 1084620 2059759 := bstep (se 1 (by rfl) ⟨1544819, by rfl⟩ : syracuseStep 2059759 = 3089639) B3089639
theorem B2747945 : Blo 1084620 2747945 := bstep (se 2 (by rfl) ⟨1030479, by rfl⟩ : syracuseStep 2747945 = 2060959) B2060959
theorem B2977735 : Blo 1084620 2977735 := bstep (se 1 (by rfl) ⟨2233301, by rfl⟩ : syracuseStep 2977735 = 4466603) B4466603
theorem B13201825 : Blo 1084620 13201825 := bstep (se 2 (by rfl) ⟨4950684, by rfl⟩ : syracuseStep 13201825 = 9901369) B9901369
theorem B18576377 : Blo 1084620 18576377 := bstep (se 2 (by rfl) ⟨6966141, by rfl⟩ : syracuseStep 18576377 = 13932283) B13932283
theorem B1832159 : Blo 1084620 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B52950347 : Blo 1084620 52950347 := bstep (se 1 (by rfl) ⟨39712760, by rfl⟩ : syracuseStep 52950347 = 79425521) B79425521
theorem B3667625 : Blo 1084620 3667625 := bstep (se 2 (by rfl) ⟨1375359, by rfl⟩ : syracuseStep 3667625 = 2750719) B2750719
theorem B1834751 : Blo 1084620 1834751 := bstep (se 1 (by rfl) ⟨1376063, by rfl⟩ : syracuseStep 1834751 = 2752127) B2752127
theorem B1835129 : Blo 1084620 1835129 := bstep (se 2 (by rfl) ⟨688173, by rfl⟩ : syracuseStep 1835129 = 1376347) B1376347
theorem B41846057 : Blo 1084620 41846057 := bstep (se 2 (by rfl) ⟨15692271, by rfl⟩ : syracuseStep 41846057 = 31384543) B31384543
theorem B5572151 : Blo 1084620 5572151 := bstep (se 1 (by rfl) ⟨4179113, by rfl⟩ : syracuseStep 5572151 = 8358227) B8358227
theorem B2754425 : Blo 1084620 2754425 := bstep (se 2 (by rfl) ⟨1032909, by rfl⟩ : syracuseStep 2754425 = 2065819) B2065819
theorem B3672701 : Blo 1084620 3672701 := bstep (se 3 (by rfl) ⟨688631, by rfl⟩ : syracuseStep 3672701 = 1377263) B1377263
theorem B10456289 : Blo 1084620 10456289 := bstep (se 2 (by rfl) ⟨3921108, by rfl⟩ : syracuseStep 10456289 = 7842217) B7842217
theorem B677055833 : Blo 1084620 677055833 := bstep (se 2 (by rfl) ⟨253895937, by rfl⟩ : syracuseStep 677055833 = 507791875) B507791875
theorem B6950407 : Blo 1084620 6950407 := bstep (se 1 (by rfl) ⟨5212805, by rfl⟩ : syracuseStep 6950407 = 10425611) B10425611
theorem B1086191 : Blo 1084620 1086191 := bstep (se 1 (by rfl) ⟨814643, by rfl⟩ : syracuseStep 1086191 = 1629287) B1629287
theorem B1086631 : Blo 1084620 1086631 := bstep (se 1 (by rfl) ⟨814973, by rfl⟩ : syracuseStep 1086631 = 1629947) B1629947
theorem B3970313 : Blo 1084620 3970313 := bstep (se 2 (by rfl) ⟨1488867, by rfl⟩ : syracuseStep 3970313 = 2977735) B2977735
theorem B1087335 : Blo 1084620 1087335 := bstep (se 1 (by rfl) ⟨815501, by rfl⟩ : syracuseStep 1087335 = 1631003) B1631003
theorem B17602433 : Blo 1084620 17602433 := bstep (se 2 (by rfl) ⟨6600912, by rfl⟩ : syracuseStep 17602433 = 13201825) B13201825
theorem B1087455 : Blo 1084620 1087455 := bstep (se 1 (by rfl) ⟨815591, by rfl⟩ : syracuseStep 1087455 = 1631183) B1631183
theorem B7445951 : Blo 1084620 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B1221439 : Blo 1084620 1221439 := bstep (se 1 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 1221439 = 1832159) B1832159
theorem B35300231 : Blo 1084620 35300231 := bstep (se 1 (by rfl) ⟨26475173, by rfl⟩ : syracuseStep 35300231 = 52950347) B52950347
theorem B1223167 : Blo 1084620 1223167 := bstep (se 1 (by rfl) ⟨917375, by rfl⟩ : syracuseStep 1223167 = 1834751) B1834751
theorem B8367097 : Blo 1084620 8367097 := bstep (se 2 (by rfl) ⟨3137661, by rfl⟩ : syracuseStep 8367097 = 6275323) B6275323
theorem B5583401 : Blo 1084620 5583401 := bstep (se 2 (by rfl) ⟨2093775, by rfl⟩ : syracuseStep 5583401 = 4187551) B4187551
theorem B3093967 : Blo 1084620 3093967 := bstep (se 1 (by rfl) ⟨2320475, by rfl⟩ : syracuseStep 3093967 = 4640951) B4640951
theorem B6960811 : Blo 1084620 6960811 := bstep (se 1 (by rfl) ⟨5220608, by rfl⟩ : syracuseStep 6960811 = 10441217) B10441217
theorem B5651999 : Blo 1084620 5651999 := bstep (se 1 (by rfl) ⟨4238999, by rfl⟩ : syracuseStep 5651999 = 8477999) B8477999
theorem B37634033 : Blo 1084620 37634033 := bstep (se 2 (by rfl) ⟨14112762, by rfl⟩ : syracuseStep 37634033 = 28225525) B28225525
theorem B2445083 : Blo 1084620 2445083 := bstep (se 1 (by rfl) ⟨1833812, by rfl⟩ : syracuseStep 2445083 = 3667625) B3667625
theorem B42389891 : Blo 1084620 42389891 := bstep (se 1 (by rfl) ⟨31792418, by rfl⟩ : syracuseStep 42389891 = 63584837) B63584837
theorem B1627913 : Blo 1084620 1627913 := bstep (se 2 (by rfl) ⟨610467, by rfl⟩ : syracuseStep 1627913 = 1220935) B1220935
theorem B2447207 : Blo 1084620 2447207 := bstep (se 1 (by rfl) ⟨1835405, by rfl⟩ : syracuseStep 2447207 = 3670811) B3670811
theorem B3661577 : Blo 1084620 3661577 := bstep (se 2 (by rfl) ⟨1373091, by rfl⟩ : syracuseStep 3661577 = 2746183) B2746183
theorem B1630367 : Blo 1084620 1630367 := bstep (se 1 (by rfl) ⟨1222775, by rfl⟩ : syracuseStep 1630367 = 2445551) B2445551
theorem B1631099 : Blo 1084620 1631099 := bstep (se 1 (by rfl) ⟨1223324, by rfl⟩ : syracuseStep 1631099 = 2446649) B2446649
theorem B1468135 : Blo 1084620 1468135 := bstep (se 1 (by rfl) ⟨1101101, by rfl⟩ : syracuseStep 1468135 = 2202203) B2202203
theorem B2746345 : Blo 1084620 2746345 := bstep (se 2 (by rfl) ⟨1029879, by rfl⟩ : syracuseStep 2746345 = 2059759) B2059759
theorem B5498927 : Blo 1084620 5498927 := bstep (se 1 (by rfl) ⟨4124195, by rfl⟩ : syracuseStep 5498927 = 8248391) B8248391
theorem B23783489 : Blo 1084620 23783489 := bstep (se 2 (by rfl) ⟨8918808, by rfl⟩ : syracuseStep 23783489 = 17837617) B17837617
theorem B1239359 : Blo 1084620 1239359 := bstep (se 1 (by rfl) ⟨929519, by rfl⟩ : syracuseStep 1239359 = 1859039) B1859039
theorem B23783807 : Blo 1084620 23783807 := bstep (se 1 (by rfl) ⟨17837855, by rfl⟩ : syracuseStep 23783807 = 35675711) B35675711
theorem B2747135 : Blo 1084620 2747135 := bstep (se 1 (by rfl) ⟨2060351, by rfl⟩ : syracuseStep 2747135 = 4120703) B4120703
theorem B18541385 : Blo 1084620 18541385 := bstep (se 2 (by rfl) ⟨6953019, by rfl⟩ : syracuseStep 18541385 = 13906039) B13906039
theorem B11168765 : Blo 1084620 11168765 := bstep (se 3 (by rfl) ⟨2094143, by rfl⟩ : syracuseStep 11168765 = 4188287) B4188287
theorem B4648043 : Blo 1084620 4648043 := bstep (se 1 (by rfl) ⟨3486032, by rfl⟩ : syracuseStep 4648043 = 6972065) B6972065
theorem B4648367 : Blo 1084620 4648367 := bstep (se 1 (by rfl) ⟨3486275, by rfl⟩ : syracuseStep 4648367 = 6972551) B6972551
theorem B1831079 : Blo 1084620 1831079 := bstep (se 1 (by rfl) ⟨1373309, by rfl⟩ : syracuseStep 1831079 = 2746619) B2746619
theorem B1372727 : Blo 1084620 1372727 := bstep (se 1 (by rfl) ⟨1029545, by rfl⟩ : syracuseStep 1372727 = 2059091) B2059091
theorem B1831963 : Blo 1084620 1831963 := bstep (se 1 (by rfl) ⟨1373972, by rfl⟩ : syracuseStep 1831963 = 2747945) B2747945
theorem B12384251 : Blo 1084620 12384251 := bstep (se 1 (by rfl) ⟨9288188, by rfl⟩ : syracuseStep 12384251 = 18576377) B18576377
theorem B22314203 : Blo 1084620 22314203 := bstep (se 1 (by rfl) ⟨16735652, by rfl⟩ : syracuseStep 22314203 = 33471305) B33471305
theorem B15891835 : Blo 1084620 15891835 := bstep (se 1 (by rfl) ⟨11918876, by rfl⟩ : syracuseStep 15891835 = 23837753) B23837753
theorem B23494121 : Blo 1084620 23494121 := bstep (se 2 (by rfl) ⟨8810295, by rfl⟩ : syracuseStep 23494121 = 17620591) B17620591
theorem B1836283 : Blo 1084620 1836283 := bstep (se 1 (by rfl) ⟨1377212, by rfl⟩ : syracuseStep 1836283 = 2754425) B2754425
theorem B1085275 : Blo 1084620 1085275 := bstep (se 1 (by rfl) ⟨813956, by rfl⟩ : syracuseStep 1085275 = 1627913) B1627913
theorem B11734955 : Blo 1084620 11734955 := bstep (se 1 (by rfl) ⟨8801216, by rfl⟩ : syracuseStep 11734955 = 17602433) B17602433
theorem B1086911 : Blo 1084620 1086911 := bstep (se 1 (by rfl) ⟨815183, by rfl⟩ : syracuseStep 1086911 = 1630367) B1630367
theorem B1087399 : Blo 1084620 1087399 := bstep (se 1 (by rfl) ⟨815549, by rfl⟩ : syracuseStep 1087399 = 1631099) B1631099
theorem B23533487 : Blo 1084620 23533487 := bstep (se 1 (by rfl) ⟨17650115, by rfl⟩ : syracuseStep 23533487 = 35300231) B35300231
theorem B12360923 : Blo 1084620 12360923 := bstep (se 1 (by rfl) ⟨9270692, by rfl⟩ : syracuseStep 12360923 = 18541385) B18541385
theorem B7445843 : Blo 1084620 7445843 := bstep (se 1 (by rfl) ⟨5584382, by rfl⟩ : syracuseStep 7445843 = 11168765) B11168765
theorem B9281081 : Blo 1084620 9281081 := bstep (se 2 (by rfl) ⟨3480405, by rfl⟩ : syracuseStep 9281081 = 6960811) B6960811
theorem B1220719 : Blo 1084620 1220719 := bstep (se 1 (by rfl) ⟨915539, by rfl⟩ : syracuseStep 1220719 = 1831079) B1831079
theorem B1223419 : Blo 1084620 1223419 := bstep (se 1 (by rfl) ⟨917564, by rfl⟩ : syracuseStep 1223419 = 1835129) B1835129
theorem B27897371 : Blo 1084620 27897371 := bstep (se 1 (by rfl) ⟨20923028, by rfl⟩ : syracuseStep 27897371 = 41846057) B41846057
theorem B3714767 : Blo 1084620 3714767 := bstep (se 1 (by rfl) ⟨2786075, by rfl⟩ : syracuseStep 3714767 = 5572151) B5572151
theorem B28259927 : Blo 1084620 28259927 := bstep (se 1 (by rfl) ⟨21194945, by rfl⟩ : syracuseStep 28259927 = 42389891) B42389891
theorem B11156129 : Blo 1084620 11156129 := bstep (se 2 (by rfl) ⟨4183548, by rfl⟩ : syracuseStep 11156129 = 8367097) B8367097
theorem B4963967 : Blo 1084620 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B2441051 : Blo 1084620 2441051 := bstep (se 1 (by rfl) ⟨1830788, by rfl⟩ : syracuseStep 2441051 = 3661577) B3661577
theorem B2442617 : Blo 1084620 2442617 := bstep (se 2 (by rfl) ⟨915981, by rfl⟩ : syracuseStep 2442617 = 1831963) B1831963
theorem B3098695 : Blo 1084620 3098695 := bstep (se 1 (by rfl) ⟨2324021, by rfl⟩ : syracuseStep 3098695 = 4648043) B4648043
theorem B3098911 : Blo 1084620 3098911 := bstep (se 1 (by rfl) ⟨2324183, by rfl⟩ : syracuseStep 3098911 = 4648367) B4648367
theorem B3722267 : Blo 1084620 3722267 := bstep (se 1 (by rfl) ⟨2791700, by rfl⟩ : syracuseStep 3722267 = 5583401) B5583401
theorem B21189113 : Blo 1084620 21189113 := bstep (se 2 (by rfl) ⟨7945917, by rfl⟩ : syracuseStep 21189113 = 15891835) B15891835
theorem B25089355 : Blo 1084620 25089355 := bstep (se 1 (by rfl) ⟨18817016, by rfl⟩ : syracuseStep 25089355 = 37634033) B37634033
theorem B1628585 : Blo 1084620 1628585 := bstep (se 2 (by rfl) ⟨610719, by rfl⟩ : syracuseStep 1628585 = 1221439) B1221439
theorem B3660605 : Blo 1084620 3660605 := bstep (se 3 (by rfl) ⟨686363, by rfl⟩ : syracuseStep 3660605 = 1372727) B1372727
theorem B2448467 : Blo 1084620 2448467 := bstep (se 1 (by rfl) ⟨1836350, by rfl⟩ : syracuseStep 2448467 = 3672701) B3672701
theorem B6970859 : Blo 1084620 6970859 := bstep (se 1 (by rfl) ⟨5228144, by rfl⟩ : syracuseStep 6970859 = 10456289) B10456289
theorem B451370555 : Blo 1084620 451370555 := bstep (se 1 (by rfl) ⟨338527916, by rfl⟩ : syracuseStep 451370555 = 677055833) B677055833
theorem B1630055 : Blo 1084620 1630055 := bstep (se 1 (by rfl) ⟨1222541, by rfl⟩ : syracuseStep 1630055 = 2445083) B2445083
theorem B3661793 : Blo 1084620 3661793 := bstep (se 2 (by rfl) ⟨1373172, by rfl⟩ : syracuseStep 3661793 = 2746345) B2746345
theorem B1630889 : Blo 1084620 1630889 := bstep (se 2 (by rfl) ⟨611583, by rfl⟩ : syracuseStep 1630889 = 1223167) B1223167
theorem B2646875 : Blo 1084620 2646875 := bstep (se 1 (by rfl) ⟨1985156, by rfl⟩ : syracuseStep 2646875 = 3970313) B3970313
theorem B1631471 : Blo 1084620 1631471 := bstep (se 1 (by rfl) ⟨1223603, by rfl⟩ : syracuseStep 1631471 = 2447207) B2447207
theorem B9267209 : Blo 1084620 9267209 := bstep (se 2 (by rfl) ⟨3475203, by rfl⟩ : syracuseStep 9267209 = 6950407) B6950407
theorem B3304957 : Blo 1084620 3304957 := bstep (se 3 (by rfl) ⟨619679, by rfl⟩ : syracuseStep 3304957 = 1239359) B1239359
theorem B3665951 : Blo 1084620 3665951 := bstep (se 1 (by rfl) ⟨2749463, by rfl⟩ : syracuseStep 3665951 = 5498927) B5498927
theorem B15855659 : Blo 1084620 15855659 := bstep (se 1 (by rfl) ⟨11891744, by rfl⟩ : syracuseStep 15855659 = 23783489) B23783489
theorem B15855871 : Blo 1084620 15855871 := bstep (se 1 (by rfl) ⟨11891903, by rfl⟩ : syracuseStep 15855871 = 23783807) B23783807
theorem B1831423 : Blo 1084620 1831423 := bstep (se 1 (by rfl) ⟨1373567, by rfl⟩ : syracuseStep 1831423 = 2747135) B2747135
theorem B4125289 : Blo 1084620 4125289 := bstep (se 2 (by rfl) ⟨1546983, by rfl⟩ : syracuseStep 4125289 = 3093967) B3093967
theorem B7830053 : Blo 1084620 7830053 := bstep (se 4 (by rfl) ⟨734067, by rfl⟩ : syracuseStep 7830053 = 1468135) B1468135
theorem B8256167 : Blo 1084620 8256167 := bstep (se 1 (by rfl) ⟨6192125, by rfl⟩ : syracuseStep 8256167 = 12384251) B12384251
theorem B14876135 : Blo 1084620 14876135 := bstep (se 1 (by rfl) ⟨11157101, by rfl⟩ : syracuseStep 14876135 = 22314203) B22314203
theorem B15662747 : Blo 1084620 15662747 := bstep (se 1 (by rfl) ⟨11747060, by rfl⟩ : syracuseStep 15662747 = 23494121) B23494121
theorem B3767999 : Blo 1084620 3767999 := bstep (se 1 (by rfl) ⟨2825999, by rfl⟩ : syracuseStep 3767999 = 5651999) B5651999
theorem B4131593 : Blo 1084620 4131593 := bstep (se 2 (by rfl) ⟨1549347, by rfl⟩ : syracuseStep 4131593 = 3098695) B3098695
theorem B14126075 : Blo 1084620 14126075 := bstep (se 1 (by rfl) ⟨10594556, by rfl⟩ : syracuseStep 14126075 = 21189113) B21189113
theorem B4131881 : Blo 1084620 4131881 := bstep (se 2 (by rfl) ⟨1549455, by rfl⟩ : syracuseStep 4131881 = 3098911) B3098911
theorem B1085723 : Blo 1084620 1085723 := bstep (se 1 (by rfl) ⟨814292, by rfl⟩ : syracuseStep 1085723 = 1628585) B1628585
theorem B300913703 : Blo 1084620 300913703 := bstep (se 1 (by rfl) ⟨225685277, by rfl⟩ : syracuseStep 300913703 = 451370555) B451370555
theorem B1086703 : Blo 1084620 1086703 := bstep (se 1 (by rfl) ⟨815027, by rfl⟩ : syracuseStep 1086703 = 1630055) B1630055
theorem B21141161 : Blo 1084620 21141161 := bstep (se 2 (by rfl) ⟨7927935, by rfl⟩ : syracuseStep 21141161 = 15855871) B15855871
theorem B1087259 : Blo 1084620 1087259 := bstep (se 1 (by rfl) ⟨815444, by rfl⟩ : syracuseStep 1087259 = 1630889) B1630889
theorem B1087647 : Blo 1084620 1087647 := bstep (se 1 (by rfl) ⟨815735, by rfl⟩ : syracuseStep 1087647 = 1631471) B1631471
theorem B5220035 : Blo 1084620 5220035 := bstep (se 1 (by rfl) ⟨3915026, by rfl⟩ : syracuseStep 5220035 = 7830053) B7830053
theorem B7058333 : Blo 1084620 7058333 := bstep (se 3 (by rfl) ⟨1323437, by rfl⟩ : syracuseStep 7058333 = 2646875) B2646875
theorem B2440403 : Blo 1084620 2440403 := bstep (se 1 (by rfl) ⟨1830302, by rfl⟩ : syracuseStep 2440403 = 3660605) B3660605
theorem B4406609 : Blo 1084620 4406609 := bstep (se 2 (by rfl) ⟨1652478, by rfl⟩ : syracuseStep 4406609 = 3304957) B3304957
theorem B8240615 : Blo 1084620 8240615 := bstep (se 1 (by rfl) ⟨6180461, by rfl⟩ : syracuseStep 8240615 = 12360923) B12360923
theorem B4963895 : Blo 1084620 4963895 := bstep (se 1 (by rfl) ⟨3722921, by rfl⟩ : syracuseStep 4963895 = 7445843) B7445843
theorem B2441195 : Blo 1084620 2441195 := bstep (se 1 (by rfl) ⟨1830896, by rfl⟩ : syracuseStep 2441195 = 3661793) B3661793
theorem B2441897 : Blo 1084620 2441897 := bstep (se 2 (by rfl) ⟨915711, by rfl⟩ : syracuseStep 2441897 = 1831423) B1831423
theorem B6178139 : Blo 1084620 6178139 := bstep (se 1 (by rfl) ⟨4633604, by rfl⟩ : syracuseStep 6178139 = 9267209) B9267209
theorem B18598247 : Blo 1084620 18598247 := bstep (se 1 (by rfl) ⟨13948685, by rfl⟩ : syracuseStep 18598247 = 27897371) B27897371
theorem B2476511 : Blo 1084620 2476511 := bstep (se 1 (by rfl) ⟨1857383, by rfl⟩ : syracuseStep 2476511 = 3714767) B3714767
theorem B2443967 : Blo 1084620 2443967 := bstep (se 1 (by rfl) ⟨1832975, by rfl⟩ : syracuseStep 2443967 = 3665951) B3665951
theorem B10570439 : Blo 1084620 10570439 := bstep (se 1 (by rfl) ⟨7927829, by rfl⟩ : syracuseStep 10570439 = 15855659) B15855659
theorem B41767325 : Blo 1084620 41767325 := bstep (se 3 (by rfl) ⟨7831373, by rfl⟩ : syracuseStep 41767325 = 15662747) B15662747
theorem B10047997 : Blo 1084620 10047997 := bstep (se 3 (by rfl) ⟨1883999, by rfl⟩ : syracuseStep 10047997 = 3767999) B3767999
theorem B9917423 : Blo 1084620 9917423 := bstep (se 1 (by rfl) ⟨7438067, by rfl⟩ : syracuseStep 9917423 = 14876135) B14876135
theorem B1627367 : Blo 1084620 1627367 := bstep (se 1 (by rfl) ⟨1220525, by rfl⟩ : syracuseStep 1627367 = 2441051) B2441051
theorem B1627625 : Blo 1084620 1627625 := bstep (se 2 (by rfl) ⟨610359, by rfl⟩ : syracuseStep 1627625 = 1220719) B1220719
theorem B1628411 : Blo 1084620 1628411 := bstep (se 1 (by rfl) ⟨1221308, by rfl⟩ : syracuseStep 1628411 = 2442617) B2442617
theorem B2448377 : Blo 1084620 2448377 := bstep (se 2 (by rfl) ⟨918141, by rfl⟩ : syracuseStep 2448377 = 1836283) B1836283
theorem B2481511 : Blo 1084620 2481511 := bstep (se 1 (by rfl) ⟨1861133, by rfl⟩ : syracuseStep 2481511 = 3722267) B3722267
theorem B7823303 : Blo 1084620 7823303 := bstep (se 1 (by rfl) ⟨5867477, by rfl⟩ : syracuseStep 7823303 = 11734955) B11734955
theorem B1631225 : Blo 1084620 1631225 := bstep (se 2 (by rfl) ⟨611709, by rfl⟩ : syracuseStep 1631225 = 1223419) B1223419
theorem B15688991 : Blo 1084620 15688991 := bstep (se 1 (by rfl) ⟨11766743, by rfl⟩ : syracuseStep 15688991 = 23533487) B23533487
theorem B1632311 : Blo 1084620 1632311 := bstep (se 1 (by rfl) ⟨1224233, by rfl⟩ : syracuseStep 1632311 = 2448467) B2448467
theorem B4647239 : Blo 1084620 4647239 := bstep (se 1 (by rfl) ⟨3485429, by rfl⟩ : syracuseStep 4647239 = 6970859) B6970859
theorem B6187387 : Blo 1084620 6187387 := bstep (se 1 (by rfl) ⟨4640540, by rfl⟩ : syracuseStep 6187387 = 9281081) B9281081
theorem B5500385 : Blo 1084620 5500385 := bstep (se 2 (by rfl) ⟨2062644, by rfl⟩ : syracuseStep 5500385 = 4125289) B4125289
theorem B33452473 : Blo 1084620 33452473 := bstep (se 2 (by rfl) ⟨12544677, by rfl⟩ : syracuseStep 33452473 = 25089355) B25089355
theorem B18839951 : Blo 1084620 18839951 := bstep (se 1 (by rfl) ⟨14129963, by rfl⟩ : syracuseStep 18839951 = 28259927) B28259927
theorem B7437419 : Blo 1084620 7437419 := bstep (se 1 (by rfl) ⟨5578064, by rfl⟩ : syracuseStep 7437419 = 11156129) B11156129
theorem B5504111 : Blo 1084620 5504111 := bstep (se 1 (by rfl) ⟨4128083, by rfl⟩ : syracuseStep 5504111 = 8256167) B8256167
theorem B3309311 : Blo 1084620 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B7046959 : Blo 1084620 7046959 := bstep (se 1 (by rfl) ⟨5285219, by rfl⟩ : syracuseStep 7046959 = 10570439) B10570439
theorem B2754395 : Blo 1084620 2754395 := bstep (se 1 (by rfl) ⟨2065796, by rfl⟩ : syracuseStep 2754395 = 4131593) B4131593
theorem B2754587 : Blo 1084620 2754587 := bstep (se 1 (by rfl) ⟨2065940, by rfl⟩ : syracuseStep 2754587 = 4131881) B4131881
theorem B200609135 : Blo 1084620 200609135 := bstep (se 1 (by rfl) ⟨150456851, by rfl⟩ : syracuseStep 200609135 = 300913703) B300913703
theorem B1084911 : Blo 1084620 1084911 := bstep (se 1 (by rfl) ⟨813683, by rfl⟩ : syracuseStep 1084911 = 1627367) B1627367
theorem B1085083 : Blo 1084620 1085083 := bstep (se 1 (by rfl) ⟨813812, by rfl⟩ : syracuseStep 1085083 = 1627625) B1627625
theorem B14094107 : Blo 1084620 14094107 := bstep (se 1 (by rfl) ⟨10570580, by rfl⟩ : syracuseStep 14094107 = 21141161) B21141161
theorem B1085607 : Blo 1084620 1085607 := bstep (se 1 (by rfl) ⟨814205, by rfl⟩ : syracuseStep 1085607 = 1628411) B1628411
theorem B5215535 : Blo 1084620 5215535 := bstep (se 1 (by rfl) ⟨3911651, by rfl⟩ : syracuseStep 5215535 = 7823303) B7823303
theorem B44603297 : Blo 1084620 44603297 := bstep (se 2 (by rfl) ⟨16726236, by rfl⟩ : syracuseStep 44603297 = 33452473) B33452473
theorem B1087483 : Blo 1084620 1087483 := bstep (se 1 (by rfl) ⟨815612, by rfl⟩ : syracuseStep 1087483 = 1631225) B1631225
theorem B10459327 : Blo 1084620 10459327 := bstep (se 1 (by rfl) ⟨7844495, by rfl⟩ : syracuseStep 10459327 = 15688991) B15688991
theorem B3480023 : Blo 1084620 3480023 := bstep (se 1 (by rfl) ⟨2610017, by rfl⟩ : syracuseStep 3480023 = 5220035) B5220035
theorem B1088207 : Blo 1084620 1088207 := bstep (se 1 (by rfl) ⟨816155, by rfl⟩ : syracuseStep 1088207 = 1632311) B1632311
theorem B12559967 : Blo 1084620 12559967 := bstep (se 1 (by rfl) ⟨9419975, by rfl⟩ : syracuseStep 12559967 = 18839951) B18839951
theorem B4958279 : Blo 1084620 4958279 := bstep (se 1 (by rfl) ⟨3718709, by rfl⟩ : syracuseStep 4958279 = 7437419) B7437419
theorem B2206207 : Blo 1084620 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B12398831 : Blo 1084620 12398831 := bstep (se 1 (by rfl) ⟨9299123, by rfl⟩ : syracuseStep 12398831 = 18598247) B18598247
theorem B1651007 : Blo 1084620 1651007 := bstep (se 1 (by rfl) ⟨1238255, by rfl⟩ : syracuseStep 1651007 = 2476511) B2476511
theorem B9417383 : Blo 1084620 9417383 := bstep (se 1 (by rfl) ⟨7063037, by rfl⟩ : syracuseStep 9417383 = 14126075) B14126075
theorem B3098159 : Blo 1084620 3098159 := bstep (se 1 (by rfl) ⟨2323619, by rfl⟩ : syracuseStep 3098159 = 4647239) B4647239
theorem B4705555 : Blo 1084620 4705555 := bstep (se 1 (by rfl) ⟨3529166, by rfl⟩ : syracuseStep 4705555 = 7058333) B7058333
theorem B11750957 : Blo 1084620 11750957 := bstep (se 3 (by rfl) ⟨2203304, by rfl⟩ : syracuseStep 11750957 = 4406609) B4406609
theorem B1626935 : Blo 1084620 1626935 := bstep (se 1 (by rfl) ⟨1220201, by rfl⟩ : syracuseStep 1626935 = 2440403) B2440403
theorem B5493743 : Blo 1084620 5493743 := bstep (se 1 (by rfl) ⟨4120307, by rfl⟩ : syracuseStep 5493743 = 8240615) B8240615
theorem B1627463 : Blo 1084620 1627463 := bstep (se 1 (by rfl) ⟨1220597, by rfl⟩ : syracuseStep 1627463 = 2441195) B2441195
theorem B1627931 : Blo 1084620 1627931 := bstep (se 1 (by rfl) ⟨1220948, by rfl⟩ : syracuseStep 1627931 = 2441897) B2441897
theorem B4118759 : Blo 1084620 4118759 := bstep (se 1 (by rfl) ⟨3089069, by rfl⟩ : syracuseStep 4118759 = 6178139) B6178139
theorem B1629311 : Blo 1084620 1629311 := bstep (se 1 (by rfl) ⟨1221983, by rfl⟩ : syracuseStep 1629311 = 2443967) B2443967
theorem B27844883 : Blo 1084620 27844883 := bstep (se 1 (by rfl) ⟨20883662, by rfl⟩ : syracuseStep 27844883 = 41767325) B41767325
theorem B8249849 : Blo 1084620 8249849 := bstep (se 2 (by rfl) ⟨3093693, by rfl⟩ : syracuseStep 8249849 = 6187387) B6187387
theorem B6611615 : Blo 1084620 6611615 := bstep (se 1 (by rfl) ⟨4958711, by rfl⟩ : syracuseStep 6611615 = 9917423) B9917423
theorem B1632251 : Blo 1084620 1632251 := bstep (se 1 (by rfl) ⟨1224188, by rfl⟩ : syracuseStep 1632251 = 2448377) B2448377
theorem B13397329 : Blo 1084620 13397329 := bstep (se 2 (by rfl) ⟨5023998, by rfl⟩ : syracuseStep 13397329 = 10047997) B10047997
theorem B3666923 : Blo 1084620 3666923 := bstep (se 1 (by rfl) ⟨2750192, by rfl⟩ : syracuseStep 3666923 = 5500385) B5500385
theorem B3308681 : Blo 1084620 3308681 := bstep (se 2 (by rfl) ⟨1240755, by rfl⟩ : syracuseStep 3308681 = 2481511) B2481511
theorem B3669407 : Blo 1084620 3669407 := bstep (se 1 (by rfl) ⟨2752055, by rfl⟩ : syracuseStep 3669407 = 5504111) B5504111
theorem B3309263 : Blo 1084620 3309263 := bstep (se 1 (by rfl) ⟨2481947, by rfl⟩ : syracuseStep 3309263 = 4963895) B4963895
theorem B2065439 : Blo 1084620 2065439 := bstep (se 1 (by rfl) ⟨1549079, by rfl⟩ : syracuseStep 2065439 = 3098159) B3098159
theorem B1836263 : Blo 1084620 1836263 := bstep (se 1 (by rfl) ⟨1377197, by rfl⟩ : syracuseStep 1836263 = 2754395) B2754395
theorem B1836391 : Blo 1084620 1836391 := bstep (se 1 (by rfl) ⟨1377293, by rfl⟩ : syracuseStep 1836391 = 2754587) B2754587
theorem B7833971 : Blo 1084620 7833971 := bstep (se 1 (by rfl) ⟨5875478, by rfl⟩ : syracuseStep 7833971 = 11750957) B11750957
theorem B11766437 : Blo 1084620 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B1084623 : Blo 1084620 1084623 := bstep (se 1 (by rfl) ⟨813467, by rfl⟩ : syracuseStep 1084623 = 1626935) B1626935
theorem B3477023 : Blo 1084620 3477023 := bstep (se 1 (by rfl) ⟨2607767, by rfl⟩ : syracuseStep 3477023 = 5215535) B5215535
theorem B1084975 : Blo 1084620 1084975 := bstep (se 1 (by rfl) ⟨813731, by rfl⟩ : syracuseStep 1084975 = 1627463) B1627463
theorem B1085287 : Blo 1084620 1085287 := bstep (se 1 (by rfl) ⟨813965, by rfl⟩ : syracuseStep 1085287 = 1627931) B1627931
theorem B17863105 : Blo 1084620 17863105 := bstep (se 2 (by rfl) ⟨6698664, by rfl⟩ : syracuseStep 17863105 = 13397329) B13397329
theorem B1086207 : Blo 1084620 1086207 := bstep (se 1 (by rfl) ⟨814655, by rfl⟩ : syracuseStep 1086207 = 1629311) B1629311
theorem B1088167 : Blo 1084620 1088167 := bstep (se 1 (by rfl) ⟨816125, by rfl⟩ : syracuseStep 1088167 = 1632251) B1632251
theorem B8265887 : Blo 1084620 8265887 := bstep (se 1 (by rfl) ⟨6199415, by rfl⟩ : syracuseStep 8265887 = 12398831) B12398831
theorem B2205787 : Blo 1084620 2205787 := bstep (se 1 (by rfl) ⟨1654340, by rfl⟩ : syracuseStep 2205787 = 3308681) B3308681
theorem B2206175 : Blo 1084620 2206175 := bstep (se 1 (by rfl) ⟨1654631, by rfl⟩ : syracuseStep 2206175 = 3309263) B3309263
theorem B133739423 : Blo 1084620 133739423 := bstep (se 1 (by rfl) ⟨100304567, by rfl⟩ : syracuseStep 133739423 = 200609135) B200609135
theorem B29735531 : Blo 1084620 29735531 := bstep (se 1 (by rfl) ⟨22301648, by rfl⟩ : syracuseStep 29735531 = 44603297) B44603297
theorem B6274073 : Blo 1084620 6274073 := bstep (se 2 (by rfl) ⟨2352777, by rfl⟩ : syracuseStep 6274073 = 4705555) B4705555
theorem B18563255 : Blo 1084620 18563255 := bstep (se 1 (by rfl) ⟨13922441, by rfl⟩ : syracuseStep 18563255 = 27844883) B27844883
theorem B4407743 : Blo 1084620 4407743 := bstep (se 1 (by rfl) ⟨3305807, by rfl⟩ : syracuseStep 4407743 = 6611615) B6611615
theorem B8373311 : Blo 1084620 8373311 := bstep (se 1 (by rfl) ⟨6279983, by rfl⟩ : syracuseStep 8373311 = 12559967) B12559967
theorem B1100671 : Blo 1084620 1100671 := bstep (se 1 (by rfl) ⟨825503, by rfl⟩ : syracuseStep 1100671 = 1651007) B1651007
theorem B13945769 : Blo 1084620 13945769 := bstep (se 2 (by rfl) ⟨5229663, by rfl⟩ : syracuseStep 13945769 = 10459327) B10459327
theorem B6278255 : Blo 1084620 6278255 := bstep (se 1 (by rfl) ⟨4708691, by rfl⟩ : syracuseStep 6278255 = 9417383) B9417383
theorem B2444615 : Blo 1084620 2444615 := bstep (se 1 (by rfl) ⟨1833461, by rfl⟩ : syracuseStep 2444615 = 3666923) B3666923
theorem B2446271 : Blo 1084620 2446271 := bstep (se 1 (by rfl) ⟨1834703, by rfl⟩ : syracuseStep 2446271 = 3669407) B3669407
theorem B9395945 : Blo 1084620 9395945 := bstep (se 2 (by rfl) ⟨3523479, by rfl⟩ : syracuseStep 9395945 = 7046959) B7046959
theorem B9396071 : Blo 1084620 9396071 := bstep (se 1 (by rfl) ⟨7047053, by rfl⟩ : syracuseStep 9396071 = 14094107) B14094107
theorem B3662495 : Blo 1084620 3662495 := bstep (se 1 (by rfl) ⟨2746871, by rfl⟩ : syracuseStep 3662495 = 5493743) B5493743
theorem B2745839 : Blo 1084620 2745839 := bstep (se 1 (by rfl) ⟨2059379, by rfl⟩ : syracuseStep 2745839 = 4118759) B4118759
theorem B2320015 : Blo 1084620 2320015 := bstep (se 1 (by rfl) ⟨1740011, by rfl⟩ : syracuseStep 2320015 = 3480023) B3480023
theorem B5499899 : Blo 1084620 5499899 := bstep (se 1 (by rfl) ⟨4124924, by rfl⟩ : syracuseStep 5499899 = 8249849) B8249849
theorem B3305519 : Blo 1084620 3305519 := bstep (se 1 (by rfl) ⟨2479139, by rfl⟩ : syracuseStep 3305519 = 4958279) B4958279
theorem B5507837 : Blo 1084620 5507837 := bstep (se 3 (by rfl) ⟨1032719, by rfl⟩ : syracuseStep 5507837 = 2065439) B2065439
theorem B5870245 : Blo 1084620 5870245 := bstep (se 4 (by rfl) ⟨550335, by rfl⟩ : syracuseStep 5870245 = 1100671) B1100671
theorem B6263963 : Blo 1084620 6263963 := bstep (se 1 (by rfl) ⟨4697972, by rfl⟩ : syracuseStep 6263963 = 9395945) B9395945
theorem B6264047 : Blo 1084620 6264047 := bstep (se 1 (by rfl) ⟨4698035, by rfl⟩ : syracuseStep 6264047 = 9396071) B9396071
theorem B5510591 : Blo 1084620 5510591 := bstep (se 1 (by rfl) ⟨4132943, by rfl⟩ : syracuseStep 5510591 = 8265887) B8265887
theorem B2203679 : Blo 1084620 2203679 := bstep (se 1 (by rfl) ⟨1652759, by rfl⟩ : syracuseStep 2203679 = 3305519) B3305519
theorem B5582207 : Blo 1084620 5582207 := bstep (se 1 (by rfl) ⟨4186655, by rfl⟩ : syracuseStep 5582207 = 8373311) B8373311
theorem B1224175 : Blo 1084620 1224175 := bstep (se 1 (by rfl) ⟨918131, by rfl⟩ : syracuseStep 1224175 = 1836263) B1836263
theorem B5222647 : Blo 1084620 5222647 := bstep (se 1 (by rfl) ⟨3916985, by rfl⟩ : syracuseStep 5222647 = 7833971) B7833971
theorem B7844291 : Blo 1084620 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B3093353 : Blo 1084620 3093353 := bstep (se 2 (by rfl) ⟨1160007, by rfl⟩ : syracuseStep 3093353 = 2320015) B2320015
theorem B2441663 : Blo 1084620 2441663 := bstep (se 1 (by rfl) ⟨1831247, by rfl⟩ : syracuseStep 2441663 = 3662495) B3662495
theorem B5883133 : Blo 1084620 5883133 := bstep (se 3 (by rfl) ⟨1103087, by rfl⟩ : syracuseStep 5883133 = 2206175) B2206175
theorem B4182715 : Blo 1084620 4182715 := bstep (se 1 (by rfl) ⟨3137036, by rfl⟩ : syracuseStep 4182715 = 6274073) B6274073
theorem B12375503 : Blo 1084620 12375503 := bstep (se 1 (by rfl) ⟨9281627, by rfl⟩ : syracuseStep 12375503 = 18563255) B18563255
theorem B11753981 : Blo 1084620 11753981 := bstep (se 3 (by rfl) ⟨2203871, by rfl⟩ : syracuseStep 11753981 = 4407743) B4407743
theorem B2448521 : Blo 1084620 2448521 := bstep (se 2 (by rfl) ⟨918195, by rfl⟩ : syracuseStep 2448521 = 1836391) B1836391
theorem B9297179 : Blo 1084620 9297179 := bstep (se 1 (by rfl) ⟨6972884, by rfl⟩ : syracuseStep 9297179 = 13945769) B13945769
theorem B4185503 : Blo 1084620 4185503 := bstep (se 1 (by rfl) ⟨3139127, by rfl⟩ : syracuseStep 4185503 = 6278255) B6278255
theorem B1629743 : Blo 1084620 1629743 := bstep (se 1 (by rfl) ⟨1222307, by rfl⟩ : syracuseStep 1629743 = 2444615) B2444615
theorem B2318015 : Blo 1084620 2318015 := bstep (se 1 (by rfl) ⟨1738511, by rfl⟩ : syracuseStep 2318015 = 3477023) B3477023
theorem B2941049 : Blo 1084620 2941049 := bstep (se 2 (by rfl) ⟨1102893, by rfl⟩ : syracuseStep 2941049 = 2205787) B2205787
theorem B1630847 : Blo 1084620 1630847 := bstep (se 1 (by rfl) ⟨1223135, by rfl⟩ : syracuseStep 1630847 = 2446271) B2446271
theorem B23817473 : Blo 1084620 23817473 := bstep (se 2 (by rfl) ⟨8931552, by rfl⟩ : syracuseStep 23817473 = 17863105) B17863105
theorem B1830559 : Blo 1084620 1830559 := bstep (se 1 (by rfl) ⟨1372919, by rfl⟩ : syracuseStep 1830559 = 2745839) B2745839
theorem B3666599 : Blo 1084620 3666599 := bstep (se 1 (by rfl) ⟨2749949, by rfl⟩ : syracuseStep 3666599 = 5499899) B5499899
theorem B89159615 : Blo 1084620 89159615 := bstep (se 1 (by rfl) ⟨66869711, by rfl⟩ : syracuseStep 89159615 = 133739423) B133739423
theorem B19823687 : Blo 1084620 19823687 := bstep (se 1 (by rfl) ⟨14867765, by rfl⟩ : syracuseStep 19823687 = 29735531) B29735531
theorem B3671891 : Blo 1084620 3671891 := bstep (se 1 (by rfl) ⟨2753918, by rfl⟩ : syracuseStep 3671891 = 5507837) B5507837
theorem B3673727 : Blo 1084620 3673727 := bstep (se 1 (by rfl) ⟨2755295, by rfl⟩ : syracuseStep 3673727 = 5510591) B5510591
theorem B7835987 : Blo 1084620 7835987 := bstep (se 1 (by rfl) ⟨5876990, by rfl⟩ : syracuseStep 7835987 = 11753981) B11753981
theorem B6198119 : Blo 1084620 6198119 := bstep (se 1 (by rfl) ⟨4648589, by rfl⟩ : syracuseStep 6198119 = 9297179) B9297179
theorem B2790335 : Blo 1084620 2790335 := bstep (se 1 (by rfl) ⟨2092751, by rfl⟩ : syracuseStep 2790335 = 4185503) B4185503
theorem B1086495 : Blo 1084620 1086495 := bstep (se 1 (by rfl) ⟨814871, by rfl⟩ : syracuseStep 1086495 = 1629743) B1629743
theorem B1087231 : Blo 1084620 1087231 := bstep (se 1 (by rfl) ⟨815423, by rfl⟩ : syracuseStep 1087231 = 1630847) B1630847
theorem B5576953 : Blo 1084620 5576953 := bstep (se 2 (by rfl) ⟨2091357, by rfl⟩ : syracuseStep 5576953 = 4182715) B4182715
theorem B13215791 : Blo 1084620 13215791 := bstep (se 1 (by rfl) ⟨9911843, by rfl⟩ : syracuseStep 13215791 = 19823687) B19823687
theorem B7844177 : Blo 1084620 7844177 := bstep (se 2 (by rfl) ⟨2941566, by rfl⟩ : syracuseStep 7844177 = 5883133) B5883133
theorem B4175975 : Blo 1084620 4175975 := bstep (se 1 (by rfl) ⟨3131981, by rfl⟩ : syracuseStep 4175975 = 6263963) B6263963
theorem B4176031 : Blo 1084620 4176031 := bstep (se 1 (by rfl) ⟨3132023, by rfl⟩ : syracuseStep 4176031 = 6264047) B6264047
theorem B2440745 : Blo 1084620 2440745 := bstep (se 2 (by rfl) ⟨915279, by rfl⟩ : syracuseStep 2440745 = 1830559) B1830559
theorem B6963529 : Blo 1084620 6963529 := bstep (se 2 (by rfl) ⟨2611323, by rfl⟩ : syracuseStep 6963529 = 5222647) B5222647
theorem B15878315 : Blo 1084620 15878315 := bstep (se 1 (by rfl) ⟨11908736, by rfl⟩ : syracuseStep 15878315 = 23817473) B23817473
theorem B3721471 : Blo 1084620 3721471 := bstep (se 1 (by rfl) ⟨2791103, by rfl⟩ : syracuseStep 3721471 = 5582207) B5582207
theorem B5229527 : Blo 1084620 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B2444399 : Blo 1084620 2444399 := bstep (se 1 (by rfl) ⟨1833299, by rfl⟩ : syracuseStep 2444399 = 3666599) B3666599
theorem B6181373 : Blo 1084620 6181373 := bstep (se 3 (by rfl) ⟨1159007, by rfl⟩ : syracuseStep 6181373 = 2318015) B2318015
theorem B1627775 : Blo 1084620 1627775 := bstep (se 1 (by rfl) ⟨1220831, by rfl⟩ : syracuseStep 1627775 = 2441663) B2441663
theorem B8250335 : Blo 1084620 8250335 := bstep (se 1 (by rfl) ⟨6187751, by rfl⟩ : syracuseStep 8250335 = 12375503) B12375503
theorem B1632233 : Blo 1084620 1632233 := bstep (se 2 (by rfl) ⟨612087, by rfl⟩ : syracuseStep 1632233 = 1224175) B1224175
theorem B1632347 : Blo 1084620 1632347 := bstep (se 1 (by rfl) ⟨1224260, by rfl⟩ : syracuseStep 1632347 = 2448521) B2448521
theorem B1469119 : Blo 1084620 1469119 := bstep (se 1 (by rfl) ⟨1101839, by rfl⟩ : syracuseStep 1469119 = 2203679) B2203679
theorem B1960699 : Blo 1084620 1960699 := bstep (se 1 (by rfl) ⟨1470524, by rfl⟩ : syracuseStep 1960699 = 2941049) B2941049
theorem B7826993 : Blo 1084620 7826993 := bstep (se 2 (by rfl) ⟨2935122, by rfl⟩ : syracuseStep 7826993 = 5870245) B5870245
theorem B2062235 : Blo 1084620 2062235 := bstep (se 1 (by rfl) ⟨1546676, by rfl⟩ : syracuseStep 2062235 = 3093353) B3093353
theorem B59439743 : Blo 1084620 59439743 := bstep (se 1 (by rfl) ⟨44579807, by rfl⟩ : syracuseStep 59439743 = 89159615) B89159615
theorem B7440893 : Blo 1084620 7440893 := bstep (se 3 (by rfl) ⟨1395167, by rfl⟩ : syracuseStep 7440893 = 2790335) B2790335
theorem B4132079 : Blo 1084620 4132079 := bstep (se 1 (by rfl) ⟨3099059, by rfl⟩ : syracuseStep 4132079 = 6198119) B6198119
theorem B1085183 : Blo 1084620 1085183 := bstep (se 1 (by rfl) ⟨813887, by rfl⟩ : syracuseStep 1085183 = 1627775) B1627775
theorem B42342173 : Blo 1084620 42342173 := bstep (se 3 (by rfl) ⟨7939157, by rfl⟩ : syracuseStep 42342173 = 15878315) B15878315
theorem B1088155 : Blo 1084620 1088155 := bstep (se 1 (by rfl) ⟨816116, by rfl⟩ : syracuseStep 1088155 = 1632233) B1632233
theorem B1088231 : Blo 1084620 1088231 := bstep (se 1 (by rfl) ⟨816173, by rfl⟩ : syracuseStep 1088231 = 1632347) B1632347
theorem B5217995 : Blo 1084620 5217995 := bstep (se 1 (by rfl) ⟨3913496, by rfl⟩ : syracuseStep 5217995 = 7826993) B7826993
theorem B39626495 : Blo 1084620 39626495 := bstep (se 1 (by rfl) ⟨29719871, by rfl⟩ : syracuseStep 39626495 = 59439743) B59439743
theorem B9284705 : Blo 1084620 9284705 := bstep (se 2 (by rfl) ⟨3481764, by rfl⟩ : syracuseStep 9284705 = 6963529) B6963529
theorem B13945405 : Blo 1084620 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B5229451 : Blo 1084620 5229451 := bstep (se 1 (by rfl) ⟨3922088, by rfl⟩ : syracuseStep 5229451 = 7844177) B7844177
theorem B1627163 : Blo 1084620 1627163 := bstep (se 1 (by rfl) ⟨1220372, by rfl⟩ : syracuseStep 1627163 = 2440745) B2440745
theorem B20895965 : Blo 1084620 20895965 := bstep (se 3 (by rfl) ⟨3917993, by rfl⟩ : syracuseStep 20895965 = 7835987) B7835987
theorem B2447927 : Blo 1084620 2447927 := bstep (se 1 (by rfl) ⟨1835945, by rfl⟩ : syracuseStep 2447927 = 3671891) B3671891
theorem B19847845 : Blo 1084620 19847845 := bstep (se 4 (by rfl) ⟨1860735, by rfl⟩ : syracuseStep 19847845 = 3721471) B3721471
theorem B1629599 : Blo 1084620 1629599 := bstep (se 1 (by rfl) ⟨1222199, by rfl⟩ : syracuseStep 1629599 = 2444399) B2444399
theorem B2449151 : Blo 1084620 2449151 := bstep (se 1 (by rfl) ⟨1836863, by rfl⟩ : syracuseStep 2449151 = 3673727) B3673727
theorem B4120915 : Blo 1084620 4120915 := bstep (se 1 (by rfl) ⟨3090686, by rfl⟩ : syracuseStep 4120915 = 6181373) B6181373
theorem B1958825 : Blo 1084620 1958825 := bstep (se 2 (by rfl) ⟨734559, by rfl⟩ : syracuseStep 1958825 = 1469119) B1469119
theorem B2614265 : Blo 1084620 2614265 := bstep (se 2 (by rfl) ⟨980349, by rfl⟩ : syracuseStep 2614265 = 1960699) B1960699
theorem B5500223 : Blo 1084620 5500223 := bstep (se 1 (by rfl) ⟨4125167, by rfl⟩ : syracuseStep 5500223 = 8250335) B8250335
theorem B8810527 : Blo 1084620 8810527 := bstep (se 1 (by rfl) ⟨6607895, by rfl⟩ : syracuseStep 8810527 = 13215791) B13215791
theorem B5568041 : Blo 1084620 5568041 := bstep (se 2 (by rfl) ⟨2088015, by rfl⟩ : syracuseStep 5568041 = 4176031) B4176031
theorem B7435937 : Blo 1084620 7435937 := bstep (se 2 (by rfl) ⟨2788476, by rfl⟩ : syracuseStep 7435937 = 5576953) B5576953
theorem B1374823 : Blo 1084620 1374823 := bstep (se 1 (by rfl) ⟨1031117, by rfl⟩ : syracuseStep 1374823 = 2062235) B2062235
theorem B2783983 : Blo 1084620 2783983 := bstep (se 1 (by rfl) ⟨2087987, by rfl⟩ : syracuseStep 2783983 = 4175975) B4175975
theorem B2754719 : Blo 1084620 2754719 := bstep (se 1 (by rfl) ⟨2066039, by rfl⟩ : syracuseStep 2754719 = 4132079) B4132079
theorem B1084775 : Blo 1084620 1084775 := bstep (se 1 (by rfl) ⟨813581, by rfl⟩ : syracuseStep 1084775 = 1627163) B1627163
theorem B14848109 : Blo 1084620 14848109 := bstep (se 3 (by rfl) ⟨2784020, by rfl⟩ : syracuseStep 14848109 = 5568041) B5568041
theorem B13930643 : Blo 1084620 13930643 := bstep (se 1 (by rfl) ⟨10447982, by rfl⟩ : syracuseStep 13930643 = 20895965) B20895965
theorem B1086399 : Blo 1084620 1086399 := bstep (se 1 (by rfl) ⟨814799, by rfl⟩ : syracuseStep 1086399 = 1629599) B1629599
theorem B3478663 : Blo 1084620 3478663 := bstep (se 1 (by rfl) ⟨2608997, by rfl⟩ : syracuseStep 3478663 = 5217995) B5217995
theorem B1742843 : Blo 1084620 1742843 := bstep (se 1 (by rfl) ⟨1307132, by rfl⟩ : syracuseStep 1742843 = 2614265) B2614265
theorem B26417663 : Blo 1084620 26417663 := bstep (se 1 (by rfl) ⟨19813247, by rfl⟩ : syracuseStep 26417663 = 39626495) B39626495
theorem B3711977 : Blo 1084620 3711977 := bstep (se 2 (by rfl) ⟨1391991, by rfl⟩ : syracuseStep 3711977 = 2783983) B2783983
theorem B4957291 : Blo 1084620 4957291 := bstep (se 1 (by rfl) ⟨3717968, by rfl⟩ : syracuseStep 4957291 = 7435937) B7435937
theorem B4960595 : Blo 1084620 4960595 := bstep (se 1 (by rfl) ⟨3720446, by rfl⟩ : syracuseStep 4960595 = 7440893) B7440893
theorem B18593873 : Blo 1084620 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B28228115 : Blo 1084620 28228115 := bstep (se 1 (by rfl) ⟨21171086, by rfl⟩ : syracuseStep 28228115 = 42342173) B42342173
theorem B11747369 : Blo 1084620 11747369 := bstep (se 2 (by rfl) ⟨4405263, by rfl⟩ : syracuseStep 11747369 = 8810527) B8810527
theorem B26463793 : Blo 1084620 26463793 := bstep (se 2 (by rfl) ⟨9923922, by rfl⟩ : syracuseStep 26463793 = 19847845) B19847845
theorem B5494553 : Blo 1084620 5494553 := bstep (se 2 (by rfl) ⟨2060457, by rfl⟩ : syracuseStep 5494553 = 4120915) B4120915
theorem B6972601 : Blo 1084620 6972601 := bstep (se 2 (by rfl) ⟨2614725, by rfl⟩ : syracuseStep 6972601 = 5229451) B5229451
theorem B1631951 : Blo 1084620 1631951 := bstep (se 1 (by rfl) ⟨1223963, by rfl⟩ : syracuseStep 1631951 = 2447927) B2447927
theorem B1632767 : Blo 1084620 1632767 := bstep (se 1 (by rfl) ⟨1224575, by rfl⟩ : syracuseStep 1632767 = 2449151) B2449151
theorem B1305883 : Blo 1084620 1305883 := bstep (se 1 (by rfl) ⟨979412, by rfl⟩ : syracuseStep 1305883 = 1958825) B1958825
theorem B6189803 : Blo 1084620 6189803 := bstep (se 1 (by rfl) ⟨4642352, by rfl⟩ : syracuseStep 6189803 = 9284705) B9284705
theorem B3666815 : Blo 1084620 3666815 := bstep (se 1 (by rfl) ⟨2750111, by rfl⟩ : syracuseStep 3666815 = 5500223) B5500223
theorem B1833097 : Blo 1084620 1833097 := bstep (se 2 (by rfl) ⟨687411, by rfl⟩ : syracuseStep 1833097 = 1374823) B1374823
theorem B7831579 : Blo 1084620 7831579 := bstep (se 1 (by rfl) ⟨5873684, by rfl⟩ : syracuseStep 7831579 = 11747369) B11747369
theorem B1836479 : Blo 1084620 1836479 := bstep (se 1 (by rfl) ⟨1377359, by rfl⟩ : syracuseStep 1836479 = 2754719) B2754719
theorem B9898739 : Blo 1084620 9898739 := bstep (se 1 (by rfl) ⟨7424054, by rfl⟩ : syracuseStep 9898739 = 14848109) B14848109
theorem B1741177 : Blo 1084620 1741177 := bstep (se 2 (by rfl) ⟨652941, by rfl⟩ : syracuseStep 1741177 = 1305883) B1305883
theorem B1087967 : Blo 1084620 1087967 := bstep (se 1 (by rfl) ⟨815975, by rfl⟩ : syracuseStep 1087967 = 1631951) B1631951
theorem B1088511 : Blo 1084620 1088511 := bstep (se 1 (by rfl) ⟨816383, by rfl⟩ : syracuseStep 1088511 = 1632767) B1632767
theorem B12395915 : Blo 1084620 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B18818743 : Blo 1084620 18818743 := bstep (se 1 (by rfl) ⟨14114057, by rfl⟩ : syracuseStep 18818743 = 28228115) B28228115
theorem B9287095 : Blo 1084620 9287095 := bstep (se 1 (by rfl) ⟨6965321, by rfl⟩ : syracuseStep 9287095 = 13930643) B13930643
theorem B17611775 : Blo 1084620 17611775 := bstep (se 1 (by rfl) ⟨13208831, by rfl⟩ : syracuseStep 17611775 = 26417663) B26417663
theorem B2474651 : Blo 1084620 2474651 := bstep (se 1 (by rfl) ⟨1855988, by rfl⟩ : syracuseStep 2474651 = 3711977) B3711977
theorem B4638217 : Blo 1084620 4638217 := bstep (se 2 (by rfl) ⟨1739331, by rfl⟩ : syracuseStep 4638217 = 3478663) B3478663
theorem B2444129 : Blo 1084620 2444129 := bstep (se 2 (by rfl) ⟨916548, by rfl⟩ : syracuseStep 2444129 = 1833097) B1833097
theorem B2444543 : Blo 1084620 2444543 := bstep (se 1 (by rfl) ⟨1833407, by rfl⟩ : syracuseStep 2444543 = 3666815) B3666815
theorem B9296801 : Blo 1084620 9296801 := bstep (se 2 (by rfl) ⟨3486300, by rfl⟩ : syracuseStep 9296801 = 6972601) B6972601
theorem B3663035 : Blo 1084620 3663035 := bstep (se 1 (by rfl) ⟨2747276, by rfl⟩ : syracuseStep 3663035 = 5494553) B5494553
theorem B35285057 : Blo 1084620 35285057 := bstep (se 2 (by rfl) ⟨13231896, by rfl⟩ : syracuseStep 35285057 = 26463793) B26463793
theorem B4647581 : Blo 1084620 4647581 := bstep (se 3 (by rfl) ⟨871421, by rfl⟩ : syracuseStep 4647581 = 1742843) B1742843
theorem B26438885 : Blo 1084620 26438885 := bstep (se 4 (by rfl) ⟨2478645, by rfl⟩ : syracuseStep 26438885 = 4957291) B4957291
theorem B3307063 : Blo 1084620 3307063 := bstep (se 1 (by rfl) ⟨2480297, by rfl⟩ : syracuseStep 3307063 = 4960595) B4960595
theorem B4126535 : Blo 1084620 4126535 := bstep (se 1 (by rfl) ⟨3094901, by rfl⟩ : syracuseStep 4126535 = 6189803) B6189803
theorem B6197867 : Blo 1084620 6197867 := bstep (se 1 (by rfl) ⟨4648400, by rfl⟩ : syracuseStep 6197867 = 9296801) B9296801
theorem B8263943 : Blo 1084620 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B11741183 : Blo 1084620 11741183 := bstep (se 1 (by rfl) ⟨8805887, by rfl⟩ : syracuseStep 11741183 = 17611775) B17611775
theorem B1224319 : Blo 1084620 1224319 := bstep (se 1 (by rfl) ⟨918239, by rfl⟩ : syracuseStep 1224319 = 1836479) B1836479
theorem B6599069 : Blo 1084620 6599069 := bstep (se 3 (by rfl) ⟨1237325, by rfl⟩ : syracuseStep 6599069 = 2474651) B2474651
theorem B6599159 : Blo 1084620 6599159 := bstep (se 1 (by rfl) ⟨4949369, by rfl⟩ : syracuseStep 6599159 = 9898739) B9898739
theorem B2442023 : Blo 1084620 2442023 := bstep (se 1 (by rfl) ⟨1831517, by rfl⟩ : syracuseStep 2442023 = 3663035) B3663035
theorem B3098387 : Blo 1084620 3098387 := bstep (se 1 (by rfl) ⟨2323790, by rfl⟩ : syracuseStep 3098387 = 4647581) B4647581
theorem B4409417 : Blo 1084620 4409417 := bstep (se 2 (by rfl) ⟨1653531, by rfl⟩ : syracuseStep 4409417 = 3307063) B3307063
theorem B10442105 : Blo 1084620 10442105 := bstep (se 2 (by rfl) ⟨3915789, by rfl⟩ : syracuseStep 10442105 = 7831579) B7831579
theorem B1629419 : Blo 1084620 1629419 := bstep (se 1 (by rfl) ⟨1222064, by rfl⟩ : syracuseStep 1629419 = 2444129) B2444129
theorem B6184289 : Blo 1084620 6184289 := bstep (se 2 (by rfl) ⟨2319108, by rfl⟩ : syracuseStep 6184289 = 4638217) B4638217
theorem B1629695 : Blo 1084620 1629695 := bstep (se 1 (by rfl) ⟨1222271, by rfl⟩ : syracuseStep 1629695 = 2444543) B2444543
theorem B25091657 : Blo 1084620 25091657 := bstep (se 2 (by rfl) ⟨9409371, by rfl⟩ : syracuseStep 25091657 = 18818743) B18818743
theorem B2321569 : Blo 1084620 2321569 := bstep (se 2 (by rfl) ⟨870588, by rfl⟩ : syracuseStep 2321569 = 1741177) B1741177
theorem B23523371 : Blo 1084620 23523371 := bstep (se 1 (by rfl) ⟨17642528, by rfl⟩ : syracuseStep 23523371 = 35285057) B35285057
theorem B12382793 : Blo 1084620 12382793 := bstep (se 2 (by rfl) ⟨4643547, by rfl⟩ : syracuseStep 12382793 = 9287095) B9287095
theorem B17625923 : Blo 1084620 17625923 := bstep (se 1 (by rfl) ⟨13219442, by rfl⟩ : syracuseStep 17625923 = 26438885) B26438885
theorem B2751023 : Blo 1084620 2751023 := bstep (se 1 (by rfl) ⟨2063267, by rfl⟩ : syracuseStep 2751023 = 4126535) B4126535
theorem B2065591 : Blo 1084620 2065591 := bstep (se 1 (by rfl) ⟨1549193, by rfl⟩ : syracuseStep 2065591 = 3098387) B3098387
theorem B4131911 : Blo 1084620 4131911 := bstep (se 1 (by rfl) ⟨3098933, by rfl⟩ : syracuseStep 4131911 = 6197867) B6197867
theorem B5509295 : Blo 1084620 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B1086279 : Blo 1084620 1086279 := bstep (se 1 (by rfl) ⟨814709, by rfl⟩ : syracuseStep 1086279 = 1629419) B1629419
theorem B1086463 : Blo 1084620 1086463 := bstep (se 1 (by rfl) ⟨814847, by rfl⟩ : syracuseStep 1086463 = 1629695) B1629695
theorem B4399379 : Blo 1084620 4399379 := bstep (se 1 (by rfl) ⟨3299534, by rfl⟩ : syracuseStep 4399379 = 6599069) B6599069
theorem B4399439 : Blo 1084620 4399439 := bstep (se 1 (by rfl) ⟨3299579, by rfl⟩ : syracuseStep 4399439 = 6599159) B6599159
theorem B6961403 : Blo 1084620 6961403 := bstep (se 1 (by rfl) ⟨5221052, by rfl⟩ : syracuseStep 6961403 = 10442105) B10442105
theorem B3095425 : Blo 1084620 3095425 := bstep (se 2 (by rfl) ⟨1160784, by rfl⟩ : syracuseStep 3095425 = 2321569) B2321569
theorem B16727771 : Blo 1084620 16727771 := bstep (se 1 (by rfl) ⟨12545828, by rfl⟩ : syracuseStep 16727771 = 25091657) B25091657
theorem B15682247 : Blo 1084620 15682247 := bstep (se 1 (by rfl) ⟨11761685, by rfl⟩ : syracuseStep 15682247 = 23523371) B23523371
theorem B11750615 : Blo 1084620 11750615 := bstep (se 1 (by rfl) ⟨8812961, by rfl⟩ : syracuseStep 11750615 = 17625923) B17625923
theorem B1628015 : Blo 1084620 1628015 := bstep (se 1 (by rfl) ⟨1221011, by rfl⟩ : syracuseStep 1628015 = 2442023) B2442023
theorem B2939611 : Blo 1084620 2939611 := bstep (se 1 (by rfl) ⟨2204708, by rfl⟩ : syracuseStep 2939611 = 4409417) B4409417
theorem B1632425 : Blo 1084620 1632425 := bstep (se 2 (by rfl) ⟨612159, by rfl⟩ : syracuseStep 1632425 = 1224319) B1224319
theorem B4122859 : Blo 1084620 4122859 := bstep (se 1 (by rfl) ⟨3092144, by rfl⟩ : syracuseStep 4122859 = 6184289) B6184289
theorem B7827455 : Blo 1084620 7827455 := bstep (se 1 (by rfl) ⟨5870591, by rfl⟩ : syracuseStep 7827455 = 11741183) B11741183
theorem B8255195 : Blo 1084620 8255195 := bstep (se 1 (by rfl) ⟨6191396, by rfl⟩ : syracuseStep 8255195 = 12382793) B12382793
theorem B1834015 : Blo 1084620 1834015 := bstep (se 1 (by rfl) ⟨1375511, by rfl⟩ : syracuseStep 1834015 = 2751023) B2751023
theorem B2754121 : Blo 1084620 2754121 := bstep (se 2 (by rfl) ⟨1032795, by rfl⟩ : syracuseStep 2754121 = 2065591) B2065591
theorem B10454831 : Blo 1084620 10454831 := bstep (se 1 (by rfl) ⟨7841123, by rfl⟩ : syracuseStep 10454831 = 15682247) B15682247
theorem B2754607 : Blo 1084620 2754607 := bstep (se 1 (by rfl) ⟨2065955, by rfl⟩ : syracuseStep 2754607 = 4131911) B4131911
theorem B7833743 : Blo 1084620 7833743 := bstep (se 1 (by rfl) ⟨5875307, by rfl⟩ : syracuseStep 7833743 = 11750615) B11750615
theorem B3672863 : Blo 1084620 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B46927349 : Blo 1084620 46927349 := bstep (se 5 (by rfl) ⟨2199719, by rfl⟩ : syracuseStep 46927349 = 4399439) B4399439
theorem B1085343 : Blo 1084620 1085343 := bstep (se 1 (by rfl) ⟨814007, by rfl⟩ : syracuseStep 1085343 = 1628015) B1628015
theorem B1088283 : Blo 1084620 1088283 := bstep (se 1 (by rfl) ⟨816212, by rfl⟩ : syracuseStep 1088283 = 1632425) B1632425
theorem B5218303 : Blo 1084620 5218303 := bstep (se 1 (by rfl) ⟨3913727, by rfl⟩ : syracuseStep 5218303 = 7827455) B7827455
theorem B11151847 : Blo 1084620 11151847 := bstep (se 1 (by rfl) ⟨8363885, by rfl⟩ : syracuseStep 11151847 = 16727771) B16727771
theorem B2932919 : Blo 1084620 2932919 := bstep (se 1 (by rfl) ⟨2199689, by rfl⟩ : syracuseStep 2932919 = 4399379) B4399379
theorem B3919481 : Blo 1084620 3919481 := bstep (se 2 (by rfl) ⟨1469805, by rfl⟩ : syracuseStep 3919481 = 2939611) B2939611
theorem B2445353 : Blo 1084620 2445353 := bstep (se 2 (by rfl) ⟨917007, by rfl⟩ : syracuseStep 2445353 = 1834015) B1834015
theorem B4640935 : Blo 1084620 4640935 := bstep (se 1 (by rfl) ⟨3480701, by rfl⟩ : syracuseStep 4640935 = 6961403) B6961403
theorem B5497145 : Blo 1084620 5497145 := bstep (se 2 (by rfl) ⟨2061429, by rfl⟩ : syracuseStep 5497145 = 4122859) B4122859
theorem B5503463 : Blo 1084620 5503463 := bstep (se 1 (by rfl) ⟨4127597, by rfl⟩ : syracuseStep 5503463 = 8255195) B8255195
theorem B4127233 : Blo 1084620 4127233 := bstep (se 2 (by rfl) ⟨1547712, by rfl⟩ : syracuseStep 4127233 = 3095425) B3095425
theorem B3672161 : Blo 1084620 3672161 := bstep (se 2 (by rfl) ⟨1377060, by rfl⟩ : syracuseStep 3672161 = 2754121) B2754121
theorem B3672809 : Blo 1084620 3672809 := bstep (se 2 (by rfl) ⟨1377303, by rfl⟩ : syracuseStep 3672809 = 2754607) B2754607
theorem B6957737 : Blo 1084620 6957737 := bstep (se 2 (by rfl) ⟨2609151, by rfl⟩ : syracuseStep 6957737 = 5218303) B5218303
theorem B5222495 : Blo 1084620 5222495 := bstep (se 1 (by rfl) ⟨3916871, by rfl⟩ : syracuseStep 5222495 = 7833743) B7833743
theorem B1955279 : Blo 1084620 1955279 := bstep (se 1 (by rfl) ⟨1466459, by rfl⟩ : syracuseStep 1955279 = 2932919) B2932919
theorem B6969887 : Blo 1084620 6969887 := bstep (se 1 (by rfl) ⟨5227415, by rfl⟩ : syracuseStep 6969887 = 10454831) B10454831
theorem B2448575 : Blo 1084620 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B31284899 : Blo 1084620 31284899 := bstep (se 1 (by rfl) ⟨23463674, by rfl⟩ : syracuseStep 31284899 = 46927349) B46927349
theorem B2612987 : Blo 1084620 2612987 := bstep (se 1 (by rfl) ⟨1959740, by rfl⟩ : syracuseStep 2612987 = 3919481) B3919481
theorem B1630235 : Blo 1084620 1630235 := bstep (se 1 (by rfl) ⟨1222676, by rfl⟩ : syracuseStep 1630235 = 2445353) B2445353
theorem B14869129 : Blo 1084620 14869129 := bstep (se 2 (by rfl) ⟨5575923, by rfl⟩ : syracuseStep 14869129 = 11151847) B11151847
theorem B3664763 : Blo 1084620 3664763 := bstep (se 1 (by rfl) ⟨2748572, by rfl⟩ : syracuseStep 3664763 = 5497145) B5497145
theorem B6187913 : Blo 1084620 6187913 := bstep (se 2 (by rfl) ⟨2320467, by rfl⟩ : syracuseStep 6187913 = 4640935) B4640935
theorem B5502977 : Blo 1084620 5502977 := bstep (se 2 (by rfl) ⟨2063616, by rfl⟩ : syracuseStep 5502977 = 4127233) B4127233
theorem B3668975 : Blo 1084620 3668975 := bstep (se 1 (by rfl) ⟨2751731, by rfl⟩ : syracuseStep 3668975 = 5503463) B5503463
theorem B19825505 : Blo 1084620 19825505 := bstep (se 2 (by rfl) ⟨7434564, by rfl⟩ : syracuseStep 19825505 = 14869129) B14869129
theorem B1741991 : Blo 1084620 1741991 := bstep (se 1 (by rfl) ⟨1306493, by rfl⟩ : syracuseStep 1741991 = 2612987) B2612987
theorem B1086823 : Blo 1084620 1086823 := bstep (se 1 (by rfl) ⟨815117, by rfl⟩ : syracuseStep 1086823 = 1630235) B1630235
theorem B3481663 : Blo 1084620 3481663 := bstep (se 1 (by rfl) ⟨2611247, by rfl⟩ : syracuseStep 3481663 = 5222495) B5222495
theorem B20856599 : Blo 1084620 20856599 := bstep (se 1 (by rfl) ⟨15642449, by rfl⟩ : syracuseStep 20856599 = 31284899) B31284899
theorem B4638491 : Blo 1084620 4638491 := bstep (se 1 (by rfl) ⟨3478868, by rfl⟩ : syracuseStep 4638491 = 6957737) B6957737
theorem B2443175 : Blo 1084620 2443175 := bstep (se 1 (by rfl) ⟨1832381, by rfl⟩ : syracuseStep 2443175 = 3664763) B3664763
theorem B2445983 : Blo 1084620 2445983 := bstep (se 1 (by rfl) ⟨1834487, by rfl⟩ : syracuseStep 2445983 = 3668975) B3668975
theorem B2448107 : Blo 1084620 2448107 := bstep (se 1 (by rfl) ⟨1836080, by rfl⟩ : syracuseStep 2448107 = 3672161) B3672161
theorem B2448539 : Blo 1084620 2448539 := bstep (se 1 (by rfl) ⟨1836404, by rfl⟩ : syracuseStep 2448539 = 3672809) B3672809
theorem B1303519 : Blo 1084620 1303519 := bstep (se 1 (by rfl) ⟨977639, by rfl⟩ : syracuseStep 1303519 = 1955279) B1955279
theorem B4646591 : Blo 1084620 4646591 := bstep (se 1 (by rfl) ⟨3484943, by rfl⟩ : syracuseStep 4646591 = 6969887) B6969887
theorem B1632383 : Blo 1084620 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B4125275 : Blo 1084620 4125275 := bstep (se 1 (by rfl) ⟨3093956, by rfl⟩ : syracuseStep 4125275 = 6187913) B6187913
theorem B3668651 : Blo 1084620 3668651 := bstep (se 1 (by rfl) ⟨2751488, by rfl⟩ : syracuseStep 3668651 = 5502977) B5502977
theorem B1738025 : Blo 1084620 1738025 := bstep (se 2 (by rfl) ⟨651759, by rfl⟩ : syracuseStep 1738025 = 1303519) B1303519
theorem B1088255 : Blo 1084620 1088255 := bstep (se 1 (by rfl) ⟨816191, by rfl⟩ : syracuseStep 1088255 = 1632383) B1632383
theorem B13904399 : Blo 1084620 13904399 := bstep (se 1 (by rfl) ⟨10428299, by rfl⟩ : syracuseStep 13904399 = 20856599) B20856599
theorem B13217003 : Blo 1084620 13217003 := bstep (se 1 (by rfl) ⟨9912752, by rfl⟩ : syracuseStep 13217003 = 19825505) B19825505
theorem B3092327 : Blo 1084620 3092327 := bstep (se 1 (by rfl) ⟨2319245, by rfl⟩ : syracuseStep 3092327 = 4638491) B4638491
theorem B3097727 : Blo 1084620 3097727 := bstep (se 1 (by rfl) ⟨2323295, by rfl⟩ : syracuseStep 3097727 = 4646591) B4646591
theorem B2445767 : Blo 1084620 2445767 := bstep (se 1 (by rfl) ⟨1834325, by rfl⟩ : syracuseStep 2445767 = 3668651) B3668651
theorem B4642217 : Blo 1084620 4642217 := bstep (se 2 (by rfl) ⟨1740831, by rfl⟩ : syracuseStep 4642217 = 3481663) B3481663
theorem B1628783 : Blo 1084620 1628783 := bstep (se 1 (by rfl) ⟨1221587, by rfl⟩ : syracuseStep 1628783 = 2443175) B2443175
theorem B4645309 : Blo 1084620 4645309 := bstep (se 3 (by rfl) ⟨870995, by rfl⟩ : syracuseStep 4645309 = 1741991) B1741991
theorem B1630655 : Blo 1084620 1630655 := bstep (se 1 (by rfl) ⟨1222991, by rfl⟩ : syracuseStep 1630655 = 2445983) B2445983
theorem B1632071 : Blo 1084620 1632071 := bstep (se 1 (by rfl) ⟨1224053, by rfl⟩ : syracuseStep 1632071 = 2448107) B2448107
theorem B1632359 : Blo 1084620 1632359 := bstep (se 1 (by rfl) ⟨1224269, by rfl⟩ : syracuseStep 1632359 = 2448539) B2448539
theorem B2750183 : Blo 1084620 2750183 := bstep (se 1 (by rfl) ⟨2062637, by rfl⟩ : syracuseStep 2750183 = 4125275) B4125275
theorem B6193745 : Blo 1084620 6193745 := bstep (se 2 (by rfl) ⟨2322654, by rfl⟩ : syracuseStep 6193745 = 4645309) B4645309
theorem B2065151 : Blo 1084620 2065151 := bstep (se 1 (by rfl) ⟨1548863, by rfl⟩ : syracuseStep 2065151 = 3097727) B3097727
theorem B1085855 : Blo 1084620 1085855 := bstep (se 1 (by rfl) ⟨814391, by rfl⟩ : syracuseStep 1085855 = 1628783) B1628783
theorem B1087103 : Blo 1084620 1087103 := bstep (se 1 (by rfl) ⟨815327, by rfl⟩ : syracuseStep 1087103 = 1630655) B1630655
theorem B1088047 : Blo 1084620 1088047 := bstep (se 1 (by rfl) ⟨816035, by rfl⟩ : syracuseStep 1088047 = 1632071) B1632071
theorem B1088239 : Blo 1084620 1088239 := bstep (se 1 (by rfl) ⟨816179, by rfl⟩ : syracuseStep 1088239 = 1632359) B1632359
theorem B1158683 : Blo 1084620 1158683 := bstep (se 1 (by rfl) ⟨869012, by rfl⟩ : syracuseStep 1158683 = 1738025) B1738025
theorem B3094811 : Blo 1084620 3094811 := bstep (se 1 (by rfl) ⟨2321108, by rfl⟩ : syracuseStep 3094811 = 4642217) B4642217
theorem B1630511 : Blo 1084620 1630511 := bstep (se 1 (by rfl) ⟨1222883, by rfl⟩ : syracuseStep 1630511 = 2445767) B2445767
theorem B9269599 : Blo 1084620 9269599 := bstep (se 1 (by rfl) ⟨6952199, by rfl⟩ : syracuseStep 9269599 = 13904399) B13904399
theorem B8811335 : Blo 1084620 8811335 := bstep (se 1 (by rfl) ⟨6608501, by rfl⟩ : syracuseStep 8811335 = 13217003) B13217003
theorem B2061551 : Blo 1084620 2061551 := bstep (se 1 (by rfl) ⟨1546163, by rfl⟩ : syracuseStep 2061551 = 3092327) B3092327
theorem B1833455 : Blo 1084620 1833455 := bstep (se 1 (by rfl) ⟨1375091, by rfl⟩ : syracuseStep 1833455 = 2750183) B2750183
theorem B4129163 : Blo 1084620 4129163 := bstep (se 1 (by rfl) ⟨3096872, by rfl⟩ : syracuseStep 4129163 = 6193745) B6193745
theorem B1376767 : Blo 1084620 1376767 := bstep (se 1 (by rfl) ⟨1032575, by rfl⟩ : syracuseStep 1376767 = 2065151) B2065151
theorem B1087007 : Blo 1084620 1087007 := bstep (se 1 (by rfl) ⟨815255, by rfl⟩ : syracuseStep 1087007 = 1630511) B1630511
theorem B12359465 : Blo 1084620 12359465 := bstep (se 2 (by rfl) ⟨4634799, by rfl⟩ : syracuseStep 12359465 = 9269599) B9269599
theorem B5874223 : Blo 1084620 5874223 := bstep (se 1 (by rfl) ⟨4405667, by rfl⟩ : syracuseStep 5874223 = 8811335) B8811335
theorem B3089821 : Blo 1084620 3089821 := bstep (se 3 (by rfl) ⟨579341, by rfl⟩ : syracuseStep 3089821 = 1158683) B1158683
theorem B1222303 : Blo 1084620 1222303 := bstep (se 1 (by rfl) ⟨916727, by rfl⟩ : syracuseStep 1222303 = 1833455) B1833455
theorem B5497469 : Blo 1084620 5497469 := bstep (se 3 (by rfl) ⟨1030775, by rfl⟩ : syracuseStep 5497469 = 2061551) B2061551
theorem B2063207 : Blo 1084620 2063207 := bstep (se 1 (by rfl) ⟨1547405, by rfl⟩ : syracuseStep 2063207 = 3094811) B3094811
theorem B2752775 : Blo 1084620 2752775 := bstep (se 1 (by rfl) ⟨2064581, by rfl⟩ : syracuseStep 2752775 = 4129163) B4129163
theorem B1835689 : Blo 1084620 1835689 := bstep (se 2 (by rfl) ⟨688383, by rfl⟩ : syracuseStep 1835689 = 1376767) B1376767
theorem B7832297 : Blo 1084620 7832297 := bstep (se 2 (by rfl) ⟨2937111, by rfl⟩ : syracuseStep 7832297 = 5874223) B5874223
theorem B8239643 : Blo 1084620 8239643 := bstep (se 1 (by rfl) ⟨6179732, by rfl⟩ : syracuseStep 8239643 = 12359465) B12359465
theorem B4119761 : Blo 1084620 4119761 := bstep (se 2 (by rfl) ⟨1544910, by rfl⟩ : syracuseStep 4119761 = 3089821) B3089821
theorem B1629737 : Blo 1084620 1629737 := bstep (se 2 (by rfl) ⟨611151, by rfl⟩ : syracuseStep 1629737 = 1222303) B1222303
theorem B3664979 : Blo 1084620 3664979 := bstep (se 1 (by rfl) ⟨2748734, by rfl⟩ : syracuseStep 3664979 = 5497469) B5497469
theorem B1375471 : Blo 1084620 1375471 := bstep (se 1 (by rfl) ⟨1031603, by rfl⟩ : syracuseStep 1375471 = 2063207) B2063207
theorem B1835183 : Blo 1084620 1835183 := bstep (se 1 (by rfl) ⟨1376387, by rfl⟩ : syracuseStep 1835183 = 2752775) B2752775
theorem B1086491 : Blo 1084620 1086491 := bstep (se 1 (by rfl) ⟨814868, by rfl⟩ : syracuseStep 1086491 = 1629737) B1629737
theorem B5221531 : Blo 1084620 5221531 := bstep (se 1 (by rfl) ⟨3916148, by rfl⟩ : syracuseStep 5221531 = 7832297) B7832297
theorem B2443319 : Blo 1084620 2443319 := bstep (se 1 (by rfl) ⟨1832489, by rfl⟩ : syracuseStep 2443319 = 3664979) B3664979
theorem B5493095 : Blo 1084620 5493095 := bstep (se 1 (by rfl) ⟨4119821, by rfl⟩ : syracuseStep 5493095 = 8239643) B8239643
theorem B2447585 : Blo 1084620 2447585 := bstep (se 2 (by rfl) ⟨917844, by rfl⟩ : syracuseStep 2447585 = 1835689) B1835689
theorem B2746507 : Blo 1084620 2746507 := bstep (se 1 (by rfl) ⟨2059880, by rfl⟩ : syracuseStep 2746507 = 4119761) B4119761
theorem B1833961 : Blo 1084620 1833961 := bstep (se 2 (by rfl) ⟨687735, by rfl⟩ : syracuseStep 1833961 = 1375471) B1375471
theorem B1223455 : Blo 1084620 1223455 := bstep (se 1 (by rfl) ⟨917591, by rfl⟩ : syracuseStep 1223455 = 1835183) B1835183
theorem B6962041 : Blo 1084620 6962041 := bstep (se 2 (by rfl) ⟨2610765, by rfl⟩ : syracuseStep 6962041 = 5221531) B5221531
theorem B2445281 : Blo 1084620 2445281 := bstep (se 2 (by rfl) ⟨916980, by rfl⟩ : syracuseStep 2445281 = 1833961) B1833961
theorem B1628879 : Blo 1084620 1628879 := bstep (se 1 (by rfl) ⟨1221659, by rfl⟩ : syracuseStep 1628879 = 2443319) B2443319
theorem B3662009 : Blo 1084620 3662009 := bstep (se 2 (by rfl) ⟨1373253, by rfl⟩ : syracuseStep 3662009 = 2746507) B2746507
theorem B3662063 : Blo 1084620 3662063 := bstep (se 1 (by rfl) ⟨2746547, by rfl⟩ : syracuseStep 3662063 = 5493095) B5493095
theorem B1631723 : Blo 1084620 1631723 := bstep (se 1 (by rfl) ⟨1223792, by rfl⟩ : syracuseStep 1631723 = 2447585) B2447585
theorem B1085919 : Blo 1084620 1085919 := bstep (se 1 (by rfl) ⟨814439, by rfl⟩ : syracuseStep 1085919 = 1628879) B1628879
theorem B1087815 : Blo 1084620 1087815 := bstep (se 1 (by rfl) ⟨815861, by rfl⟩ : syracuseStep 1087815 = 1631723) B1631723
theorem B9282721 : Blo 1084620 9282721 := bstep (se 2 (by rfl) ⟨3481020, by rfl⟩ : syracuseStep 9282721 = 6962041) B6962041
theorem B2441339 : Blo 1084620 2441339 := bstep (se 1 (by rfl) ⟨1831004, by rfl⟩ : syracuseStep 2441339 = 3662009) B3662009
theorem B2441375 : Blo 1084620 2441375 := bstep (se 1 (by rfl) ⟨1831031, by rfl⟩ : syracuseStep 2441375 = 3662063) B3662063
theorem B1630187 : Blo 1084620 1630187 := bstep (se 1 (by rfl) ⟨1222640, by rfl⟩ : syracuseStep 1630187 = 2445281) B2445281
theorem B1631273 : Blo 1084620 1631273 := bstep (se 2 (by rfl) ⟨611727, by rfl⟩ : syracuseStep 1631273 = 1223455) B1223455
theorem B1086791 : Blo 1084620 1086791 := bstep (se 1 (by rfl) ⟨815093, by rfl⟩ : syracuseStep 1086791 = 1630187) B1630187
theorem B1087515 : Blo 1084620 1087515 := bstep (se 1 (by rfl) ⟨815636, by rfl⟩ : syracuseStep 1087515 = 1631273) B1631273
theorem B1627559 : Blo 1084620 1627559 := bstep (se 1 (by rfl) ⟨1220669, by rfl⟩ : syracuseStep 1627559 = 2441339) B2441339
theorem B1627583 : Blo 1084620 1627583 := bstep (se 1 (by rfl) ⟨1220687, by rfl⟩ : syracuseStep 1627583 = 2441375) B2441375
theorem B12376961 : Blo 1084620 12376961 := bstep (se 2 (by rfl) ⟨4641360, by rfl⟩ : syracuseStep 12376961 = 9282721) B9282721
theorem B1085039 : Blo 1084620 1085039 := bstep (se 1 (by rfl) ⟨813779, by rfl⟩ : syracuseStep 1085039 = 1627559) B1627559
theorem B1085055 : Blo 1084620 1085055 := bstep (se 1 (by rfl) ⟨813791, by rfl⟩ : syracuseStep 1085055 = 1627583) B1627583
theorem B8251307 : Blo 1084620 8251307 := bstep (se 1 (by rfl) ⟨6188480, by rfl⟩ : syracuseStep 8251307 = 12376961) B12376961
theorem B5500871 : Blo 1084620 5500871 := bstep (se 1 (by rfl) ⟨4125653, by rfl⟩ : syracuseStep 5500871 = 8251307) B8251307
theorem B3667247 : Blo 1084620 3667247 := bstep (se 1 (by rfl) ⟨2750435, by rfl⟩ : syracuseStep 3667247 = 5500871) B5500871
theorem B2444831 : Blo 1084620 2444831 := bstep (se 1 (by rfl) ⟨1833623, by rfl⟩ : syracuseStep 2444831 = 3667247) B3667247
theorem B1629887 : Blo 1084620 1629887 := bstep (se 1 (by rfl) ⟨1222415, by rfl⟩ : syracuseStep 1629887 = 2444831) B2444831
theorem B1086591 : Blo 1084620 1086591 := bstep (se 1 (by rfl) ⟨814943, by rfl⟩ : syracuseStep 1086591 = 1629887) B1629887

theorem C0 (j : ℕ) (h1 : 271155 ≤ j) (h2 : j ≤ 271854) : Blo 1084620 (4 * j + 3) := by
  interval_cases j
  · exact B1084623
  · exact B1084627
  · exact B1084631
  · exact B1084635
  · exact B1084639
  · exact B1084643
  · exact B1084647
  · exact B1084651
  · exact B1084655
  · exact B1084659
  · exact B1084663
  · exact B1084667
  · exact B1084671
  · exact B1084675
  · exact B1084679
  · exact B1084683
  · exact B1084687
  · exact B1084691
  · exact B1084695
  · exact B1084699
  · exact B1084703
  · exact B1084707
  · exact B1084711
  · exact B1084715
  · exact B1084719
  · exact B1084723
  · exact B1084727
  · exact B1084731
  · exact B1084735
  · exact B1084739
  · exact B1084743
  · exact B1084747
  · exact B1084751
  · exact B1084755
  · exact B1084759
  · exact B1084763
  · exact B1084767
  · exact B1084771
  · exact B1084775
  · exact B1084779
  · exact B1084783
  · exact B1084787
  · exact B1084791
  · exact B1084795
  · exact B1084799
  · exact B1084803
  · exact B1084807
  · exact B1084811
  · exact B1084815
  · exact B1084819
  · exact B1084823
  · exact B1084827
  · exact B1084831
  · exact B1084835
  · exact B1084839
  · exact B1084843
  · exact B1084847
  · exact B1084851
  · exact B1084855
  · exact B1084859
  · exact B1084863
  · exact B1084867
  · exact B1084871
  · exact B1084875
  · exact B1084879
  · exact B1084883
  · exact B1084887
  · exact B1084891
  · exact B1084895
  · exact B1084899
  · exact B1084903
  · exact B1084907
  · exact B1084911
  · exact B1084915
  · exact B1084919
  · exact B1084923
  · exact B1084927
  · exact B1084931
  · exact B1084935
  · exact B1084939
  · exact B1084943
  · exact B1084947
  · exact B1084951
  · exact B1084955
  · exact B1084959
  · exact B1084963
  · exact B1084967
  · exact B1084971
  · exact B1084975
  · exact B1084979
  · exact B1084983
  · exact B1084987
  · exact B1084991
  · exact B1084995
  · exact B1084999
  · exact B1085003
  · exact B1085007
  · exact B1085011
  · exact B1085015
  · exact B1085019
  · exact B1085023
  · exact B1085027
  · exact B1085031
  · exact B1085035
  · exact B1085039
  · exact B1085043
  · exact B1085047
  · exact B1085051
  · exact B1085055
  · exact B1085059
  · exact B1085063
  · exact B1085067
  · exact B1085071
  · exact B1085075
  · exact B1085079
  · exact B1085083
  · exact B1085087
  · exact B1085091
  · exact B1085095
  · exact B1085099
  · exact B1085103
  · exact B1085107
  · exact B1085111
  · exact B1085115
  · exact B1085119
  · exact B1085123
  · exact B1085127
  · exact B1085131
  · exact B1085135
  · exact B1085139
  · exact B1085143
  · exact B1085147
  · exact B1085151
  · exact B1085155
  · exact B1085159
  · exact B1085163
  · exact B1085167
  · exact B1085171
  · exact B1085175
  · exact B1085179
  · exact B1085183
  · exact B1085187
  · exact B1085191
  · exact B1085195
  · exact B1085199
  · exact B1085203
  · exact B1085207
  · exact B1085211
  · exact B1085215
  · exact B1085219
  · exact B1085223
  · exact B1085227
  · exact B1085231
  · exact B1085235
  · exact B1085239
  · exact B1085243
  · exact B1085247
  · exact B1085251
  · exact B1085255
  · exact B1085259
  · exact B1085263
  · exact B1085267
  · exact B1085271
  · exact B1085275
  · exact B1085279
  · exact B1085283
  · exact B1085287
  · exact B1085291
  · exact B1085295
  · exact B1085299
  · exact B1085303
  · exact B1085307
  · exact B1085311
  · exact B1085315
  · exact B1085319
  · exact B1085323
  · exact B1085327
  · exact B1085331
  · exact B1085335
  · exact B1085339
  · exact B1085343
  · exact B1085347
  · exact B1085351
  · exact B1085355
  · exact B1085359
  · exact B1085363
  · exact B1085367
  · exact B1085371
  · exact B1085375
  · exact B1085379
  · exact B1085383
  · exact B1085387
  · exact B1085391
  · exact B1085395
  · exact B1085399
  · exact B1085403
  · exact B1085407
  · exact B1085411
  · exact B1085415
  · exact B1085419
  · exact B1085423
  · exact B1085427
  · exact B1085431
  · exact B1085435
  · exact B1085439
  · exact B1085443
  · exact B1085447
  · exact B1085451
  · exact B1085455
  · exact B1085459
  · exact B1085463
  · exact B1085467
  · exact B1085471
  · exact B1085475
  · exact B1085479
  · exact B1085483
  · exact B1085487
  · exact B1085491
  · exact B1085495
  · exact B1085499
  · exact B1085503
  · exact B1085507
  · exact B1085511
  · exact B1085515
  · exact B1085519
  · exact B1085523
  · exact B1085527
  · exact B1085531
  · exact B1085535
  · exact B1085539
  · exact B1085543
  · exact B1085547
  · exact B1085551
  · exact B1085555
  · exact B1085559
  · exact B1085563
  · exact B1085567
  · exact B1085571
  · exact B1085575
  · exact B1085579
  · exact B1085583
  · exact B1085587
  · exact B1085591
  · exact B1085595
  · exact B1085599
  · exact B1085603
  · exact B1085607
  · exact B1085611
  · exact B1085615
  · exact B1085619
  · exact B1085623
  · exact B1085627
  · exact B1085631
  · exact B1085635
  · exact B1085639
  · exact B1085643
  · exact B1085647
  · exact B1085651
  · exact B1085655
  · exact B1085659
  · exact B1085663
  · exact B1085667
  · exact B1085671
  · exact B1085675
  · exact B1085679
  · exact B1085683
  · exact B1085687
  · exact B1085691
  · exact B1085695
  · exact B1085699
  · exact B1085703
  · exact B1085707
  · exact B1085711
  · exact B1085715
  · exact B1085719
  · exact B1085723
  · exact B1085727
  · exact B1085731
  · exact B1085735
  · exact B1085739
  · exact B1085743
  · exact B1085747
  · exact B1085751
  · exact B1085755
  · exact B1085759
  · exact B1085763
  · exact B1085767
  · exact B1085771
  · exact B1085775
  · exact B1085779
  · exact B1085783
  · exact B1085787
  · exact B1085791
  · exact B1085795
  · exact B1085799
  · exact B1085803
  · exact B1085807
  · exact B1085811
  · exact B1085815
  · exact B1085819
  · exact B1085823
  · exact B1085827
  · exact B1085831
  · exact B1085835
  · exact B1085839
  · exact B1085843
  · exact B1085847
  · exact B1085851
  · exact B1085855
  · exact B1085859
  · exact B1085863
  · exact B1085867
  · exact B1085871
  · exact B1085875
  · exact B1085879
  · exact B1085883
  · exact B1085887
  · exact B1085891
  · exact B1085895
  · exact B1085899
  · exact B1085903
  · exact B1085907
  · exact B1085911
  · exact B1085915
  · exact B1085919
  · exact B1085923
  · exact B1085927
  · exact B1085931
  · exact B1085935
  · exact B1085939
  · exact B1085943
  · exact B1085947
  · exact B1085951
  · exact B1085955
  · exact B1085959
  · exact B1085963
  · exact B1085967
  · exact B1085971
  · exact B1085975
  · exact B1085979
  · exact B1085983
  · exact B1085987
  · exact B1085991
  · exact B1085995
  · exact B1085999
  · exact B1086003
  · exact B1086007
  · exact B1086011
  · exact B1086015
  · exact B1086019
  · exact B1086023
  · exact B1086027
  · exact B1086031
  · exact B1086035
  · exact B1086039
  · exact B1086043
  · exact B1086047
  · exact B1086051
  · exact B1086055
  · exact B1086059
  · exact B1086063
  · exact B1086067
  · exact B1086071
  · exact B1086075
  · exact B1086079
  · exact B1086083
  · exact B1086087
  · exact B1086091
  · exact B1086095
  · exact B1086099
  · exact B1086103
  · exact B1086107
  · exact B1086111
  · exact B1086115
  · exact B1086119
  · exact B1086123
  · exact B1086127
  · exact B1086131
  · exact B1086135
  · exact B1086139
  · exact B1086143
  · exact B1086147
  · exact B1086151
  · exact B1086155
  · exact B1086159
  · exact B1086163
  · exact B1086167
  · exact B1086171
  · exact B1086175
  · exact B1086179
  · exact B1086183
  · exact B1086187
  · exact B1086191
  · exact B1086195
  · exact B1086199
  · exact B1086203
  · exact B1086207
  · exact B1086211
  · exact B1086215
  · exact B1086219
  · exact B1086223
  · exact B1086227
  · exact B1086231
  · exact B1086235
  · exact B1086239
  · exact B1086243
  · exact B1086247
  · exact B1086251
  · exact B1086255
  · exact B1086259
  · exact B1086263
  · exact B1086267
  · exact B1086271
  · exact B1086275
  · exact B1086279
  · exact B1086283
  · exact B1086287
  · exact B1086291
  · exact B1086295
  · exact B1086299
  · exact B1086303
  · exact B1086307
  · exact B1086311
  · exact B1086315
  · exact B1086319
  · exact B1086323
  · exact B1086327
  · exact B1086331
  · exact B1086335
  · exact B1086339
  · exact B1086343
  · exact B1086347
  · exact B1086351
  · exact B1086355
  · exact B1086359
  · exact B1086363
  · exact B1086367
  · exact B1086371
  · exact B1086375
  · exact B1086379
  · exact B1086383
  · exact B1086387
  · exact B1086391
  · exact B1086395
  · exact B1086399
  · exact B1086403
  · exact B1086407
  · exact B1086411
  · exact B1086415
  · exact B1086419
  · exact B1086423
  · exact B1086427
  · exact B1086431
  · exact B1086435
  · exact B1086439
  · exact B1086443
  · exact B1086447
  · exact B1086451
  · exact B1086455
  · exact B1086459
  · exact B1086463
  · exact B1086467
  · exact B1086471
  · exact B1086475
  · exact B1086479
  · exact B1086483
  · exact B1086487
  · exact B1086491
  · exact B1086495
  · exact B1086499
  · exact B1086503
  · exact B1086507
  · exact B1086511
  · exact B1086515
  · exact B1086519
  · exact B1086523
  · exact B1086527
  · exact B1086531
  · exact B1086535
  · exact B1086539
  · exact B1086543
  · exact B1086547
  · exact B1086551
  · exact B1086555
  · exact B1086559
  · exact B1086563
  · exact B1086567
  · exact B1086571
  · exact B1086575
  · exact B1086579
  · exact B1086583
  · exact B1086587
  · exact B1086591
  · exact B1086595
  · exact B1086599
  · exact B1086603
  · exact B1086607
  · exact B1086611
  · exact B1086615
  · exact B1086619
  · exact B1086623
  · exact B1086627
  · exact B1086631
  · exact B1086635
  · exact B1086639
  · exact B1086643
  · exact B1086647
  · exact B1086651
  · exact B1086655
  · exact B1086659
  · exact B1086663
  · exact B1086667
  · exact B1086671
  · exact B1086675
  · exact B1086679
  · exact B1086683
  · exact B1086687
  · exact B1086691
  · exact B1086695
  · exact B1086699
  · exact B1086703
  · exact B1086707
  · exact B1086711
  · exact B1086715
  · exact B1086719
  · exact B1086723
  · exact B1086727
  · exact B1086731
  · exact B1086735
  · exact B1086739
  · exact B1086743
  · exact B1086747
  · exact B1086751
  · exact B1086755
  · exact B1086759
  · exact B1086763
  · exact B1086767
  · exact B1086771
  · exact B1086775
  · exact B1086779
  · exact B1086783
  · exact B1086787
  · exact B1086791
  · exact B1086795
  · exact B1086799
  · exact B1086803
  · exact B1086807
  · exact B1086811
  · exact B1086815
  · exact B1086819
  · exact B1086823
  · exact B1086827
  · exact B1086831
  · exact B1086835
  · exact B1086839
  · exact B1086843
  · exact B1086847
  · exact B1086851
  · exact B1086855
  · exact B1086859
  · exact B1086863
  · exact B1086867
  · exact B1086871
  · exact B1086875
  · exact B1086879
  · exact B1086883
  · exact B1086887
  · exact B1086891
  · exact B1086895
  · exact B1086899
  · exact B1086903
  · exact B1086907
  · exact B1086911
  · exact B1086915
  · exact B1086919
  · exact B1086923
  · exact B1086927
  · exact B1086931
  · exact B1086935
  · exact B1086939
  · exact B1086943
  · exact B1086947
  · exact B1086951
  · exact B1086955
  · exact B1086959
  · exact B1086963
  · exact B1086967
  · exact B1086971
  · exact B1086975
  · exact B1086979
  · exact B1086983
  · exact B1086987
  · exact B1086991
  · exact B1086995
  · exact B1086999
  · exact B1087003
  · exact B1087007
  · exact B1087011
  · exact B1087015
  · exact B1087019
  · exact B1087023
  · exact B1087027
  · exact B1087031
  · exact B1087035
  · exact B1087039
  · exact B1087043
  · exact B1087047
  · exact B1087051
  · exact B1087055
  · exact B1087059
  · exact B1087063
  · exact B1087067
  · exact B1087071
  · exact B1087075
  · exact B1087079
  · exact B1087083
  · exact B1087087
  · exact B1087091
  · exact B1087095
  · exact B1087099
  · exact B1087103
  · exact B1087107
  · exact B1087111
  · exact B1087115
  · exact B1087119
  · exact B1087123
  · exact B1087127
  · exact B1087131
  · exact B1087135
  · exact B1087139
  · exact B1087143
  · exact B1087147
  · exact B1087151
  · exact B1087155
  · exact B1087159
  · exact B1087163
  · exact B1087167
  · exact B1087171
  · exact B1087175
  · exact B1087179
  · exact B1087183
  · exact B1087187
  · exact B1087191
  · exact B1087195
  · exact B1087199
  · exact B1087203
  · exact B1087207
  · exact B1087211
  · exact B1087215
  · exact B1087219
  · exact B1087223
  · exact B1087227
  · exact B1087231
  · exact B1087235
  · exact B1087239
  · exact B1087243
  · exact B1087247
  · exact B1087251
  · exact B1087255
  · exact B1087259
  · exact B1087263
  · exact B1087267
  · exact B1087271
  · exact B1087275
  · exact B1087279
  · exact B1087283
  · exact B1087287
  · exact B1087291
  · exact B1087295
  · exact B1087299
  · exact B1087303
  · exact B1087307
  · exact B1087311
  · exact B1087315
  · exact B1087319
  · exact B1087323
  · exact B1087327
  · exact B1087331
  · exact B1087335
  · exact B1087339
  · exact B1087343
  · exact B1087347
  · exact B1087351
  · exact B1087355
  · exact B1087359
  · exact B1087363
  · exact B1087367
  · exact B1087371
  · exact B1087375
  · exact B1087379
  · exact B1087383
  · exact B1087387
  · exact B1087391
  · exact B1087395
  · exact B1087399
  · exact B1087403
  · exact B1087407
  · exact B1087411
  · exact B1087415
  · exact B1087419

theorem C1 (j : ℕ) (h1 : 271855 ≤ j) (h2 : j ≤ 272154) : Blo 1084620 (4 * j + 3) := by
  interval_cases j
  · exact B1087423
  · exact B1087427
  · exact B1087431
  · exact B1087435
  · exact B1087439
  · exact B1087443
  · exact B1087447
  · exact B1087451
  · exact B1087455
  · exact B1087459
  · exact B1087463
  · exact B1087467
  · exact B1087471
  · exact B1087475
  · exact B1087479
  · exact B1087483
  · exact B1087487
  · exact B1087491
  · exact B1087495
  · exact B1087499
  · exact B1087503
  · exact B1087507
  · exact B1087511
  · exact B1087515
  · exact B1087519
  · exact B1087523
  · exact B1087527
  · exact B1087531
  · exact B1087535
  · exact B1087539
  · exact B1087543
  · exact B1087547
  · exact B1087551
  · exact B1087555
  · exact B1087559
  · exact B1087563
  · exact B1087567
  · exact B1087571
  · exact B1087575
  · exact B1087579
  · exact B1087583
  · exact B1087587
  · exact B1087591
  · exact B1087595
  · exact B1087599
  · exact B1087603
  · exact B1087607
  · exact B1087611
  · exact B1087615
  · exact B1087619
  · exact B1087623
  · exact B1087627
  · exact B1087631
  · exact B1087635
  · exact B1087639
  · exact B1087643
  · exact B1087647
  · exact B1087651
  · exact B1087655
  · exact B1087659
  · exact B1087663
  · exact B1087667
  · exact B1087671
  · exact B1087675
  · exact B1087679
  · exact B1087683
  · exact B1087687
  · exact B1087691
  · exact B1087695
  · exact B1087699
  · exact B1087703
  · exact B1087707
  · exact B1087711
  · exact B1087715
  · exact B1087719
  · exact B1087723
  · exact B1087727
  · exact B1087731
  · exact B1087735
  · exact B1087739
  · exact B1087743
  · exact B1087747
  · exact B1087751
  · exact B1087755
  · exact B1087759
  · exact B1087763
  · exact B1087767
  · exact B1087771
  · exact B1087775
  · exact B1087779
  · exact B1087783
  · exact B1087787
  · exact B1087791
  · exact B1087795
  · exact B1087799
  · exact B1087803
  · exact B1087807
  · exact B1087811
  · exact B1087815
  · exact B1087819
  · exact B1087823
  · exact B1087827
  · exact B1087831
  · exact B1087835
  · exact B1087839
  · exact B1087843
  · exact B1087847
  · exact B1087851
  · exact B1087855
  · exact B1087859
  · exact B1087863
  · exact B1087867
  · exact B1087871
  · exact B1087875
  · exact B1087879
  · exact B1087883
  · exact B1087887
  · exact B1087891
  · exact B1087895
  · exact B1087899
  · exact B1087903
  · exact B1087907
  · exact B1087911
  · exact B1087915
  · exact B1087919
  · exact B1087923
  · exact B1087927
  · exact B1087931
  · exact B1087935
  · exact B1087939
  · exact B1087943
  · exact B1087947
  · exact B1087951
  · exact B1087955
  · exact B1087959
  · exact B1087963
  · exact B1087967
  · exact B1087971
  · exact B1087975
  · exact B1087979
  · exact B1087983
  · exact B1087987
  · exact B1087991
  · exact B1087995
  · exact B1087999
  · exact B1088003
  · exact B1088007
  · exact B1088011
  · exact B1088015
  · exact B1088019
  · exact B1088023
  · exact B1088027
  · exact B1088031
  · exact B1088035
  · exact B1088039
  · exact B1088043
  · exact B1088047
  · exact B1088051
  · exact B1088055
  · exact B1088059
  · exact B1088063
  · exact B1088067
  · exact B1088071
  · exact B1088075
  · exact B1088079
  · exact B1088083
  · exact B1088087
  · exact B1088091
  · exact B1088095
  · exact B1088099
  · exact B1088103
  · exact B1088107
  · exact B1088111
  · exact B1088115
  · exact B1088119
  · exact B1088123
  · exact B1088127
  · exact B1088131
  · exact B1088135
  · exact B1088139
  · exact B1088143
  · exact B1088147
  · exact B1088151
  · exact B1088155
  · exact B1088159
  · exact B1088163
  · exact B1088167
  · exact B1088171
  · exact B1088175
  · exact B1088179
  · exact B1088183
  · exact B1088187
  · exact B1088191
  · exact B1088195
  · exact B1088199
  · exact B1088203
  · exact B1088207
  · exact B1088211
  · exact B1088215
  · exact B1088219
  · exact B1088223
  · exact B1088227
  · exact B1088231
  · exact B1088235
  · exact B1088239
  · exact B1088243
  · exact B1088247
  · exact B1088251
  · exact B1088255
  · exact B1088259
  · exact B1088263
  · exact B1088267
  · exact B1088271
  · exact B1088275
  · exact B1088279
  · exact B1088283
  · exact B1088287
  · exact B1088291
  · exact B1088295
  · exact B1088299
  · exact B1088303
  · exact B1088307
  · exact B1088311
  · exact B1088315
  · exact B1088319
  · exact B1088323
  · exact B1088327
  · exact B1088331
  · exact B1088335
  · exact B1088339
  · exact B1088343
  · exact B1088347
  · exact B1088351
  · exact B1088355
  · exact B1088359
  · exact B1088363
  · exact B1088367
  · exact B1088371
  · exact B1088375
  · exact B1088379
  · exact B1088383
  · exact B1088387
  · exact B1088391
  · exact B1088395
  · exact B1088399
  · exact B1088403
  · exact B1088407
  · exact B1088411
  · exact B1088415
  · exact B1088419
  · exact B1088423
  · exact B1088427
  · exact B1088431
  · exact B1088435
  · exact B1088439
  · exact B1088443
  · exact B1088447
  · exact B1088451
  · exact B1088455
  · exact B1088459
  · exact B1088463
  · exact B1088467
  · exact B1088471
  · exact B1088475
  · exact B1088479
  · exact B1088483
  · exact B1088487
  · exact B1088491
  · exact B1088495
  · exact B1088499
  · exact B1088503
  · exact B1088507
  · exact B1088511
  · exact B1088515
  · exact B1088519
  · exact B1088523
  · exact B1088527
  · exact B1088531
  · exact B1088535
  · exact B1088539
  · exact B1088543
  · exact B1088547
  · exact B1088551
  · exact B1088555
  · exact B1088559
  · exact B1088563
  · exact B1088567
  · exact B1088571
  · exact B1088575
  · exact B1088579
  · exact B1088583
  · exact B1088587
  · exact B1088591
  · exact B1088595
  · exact B1088599
  · exact B1088603
  · exact B1088607
  · exact B1088611
  · exact B1088615
  · exact B1088619

theorem solution (m : ℕ) (hlo : 1084620 ≤ m) (hhi : m ≤ 1088620) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 271155 ≤ j := by omega
    have hj2 : j ≤ 272154 := by omega
    have hb : Blo 1084620 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 271855 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
