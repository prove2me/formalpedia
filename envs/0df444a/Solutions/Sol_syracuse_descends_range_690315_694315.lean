-- Prove2me | solution 1 for syracuse_descends_range_690315_694315
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:04:57.213334+00:00
-- url     : https://prove2.me/submissions/9728415b-ca37-4f0c-8fa3-be536ca5598b

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


theorem B4423733 : Blo 690315 4423733 := bbase (se 5 (by rfl) ⟨207362, by rfl⟩ : syracuseStep 4423733 = 414725) (by norm_num)
theorem B983125 : Blo 690315 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B4259957 : Blo 690315 4259957 := bbase (se 5 (by rfl) ⟨199685, by rfl⟩ : syracuseStep 4259957 = 399371) (by norm_num)
theorem B2621605 : Blo 690315 2621605 := bbase (se 4 (by rfl) ⟨245775, by rfl⟩ : syracuseStep 2621605 = 491551) (by norm_num)
theorem B1310917 : Blo 690315 1310917 := bbase (se 4 (by rfl) ⟨122898, by rfl⟩ : syracuseStep 1310917 = 245797) (by norm_num)
theorem B5898581 : Blo 690315 5898581 := bbase (se 10 (by rfl) ⟨8640, by rfl⟩ : syracuseStep 5898581 = 17281) (by norm_num)
theorem B1311061 : Blo 690315 1311061 := bbase (se 10 (by rfl) ⟨1920, by rfl⟩ : syracuseStep 1311061 = 3841) (by norm_num)
theorem B2621909 : Blo 690315 2621909 := bbase (se 7 (by rfl) ⟨30725, by rfl⟩ : syracuseStep 2621909 = 61451) (by norm_num)
theorem B1311221 : Blo 690315 1311221 := bbase (se 5 (by rfl) ⟨61463, by rfl⟩ : syracuseStep 1311221 = 122927) (by norm_num)
theorem B7111253 : Blo 690315 7111253 := bbase (se 8 (by rfl) ⟨41667, by rfl⟩ : syracuseStep 7111253 = 83335) (by norm_num)
theorem B1311365 : Blo 690315 1311365 := bbase (se 4 (by rfl) ⟨122940, by rfl⟩ : syracuseStep 1311365 = 245881) (by norm_num)
theorem B1245869 : Blo 690315 1245869 := bbase (se 3 (by rfl) ⟨233600, by rfl⟩ : syracuseStep 1245869 = 467201) (by norm_num)
theorem B1966933 : Blo 690315 1966933 := bbase (se 9 (by rfl) ⟨5762, by rfl⟩ : syracuseStep 1966933 = 11525) (by norm_num)
theorem B983917 : Blo 690315 983917 := bbase (se 3 (by rfl) ⟨184484, by rfl⟩ : syracuseStep 983917 = 368969) (by norm_num)
theorem B1311653 : Blo 690315 1311653 := bbase (se 4 (by rfl) ⟨122967, by rfl⟩ : syracuseStep 1311653 = 245935) (by norm_num)
theorem B1049645 : Blo 690315 1049645 := bbase (se 3 (by rfl) ⟨196808, by rfl⟩ : syracuseStep 1049645 = 393617) (by norm_num)
theorem B1311805 : Blo 690315 1311805 := bbase (se 3 (by rfl) ⟨245963, by rfl⟩ : syracuseStep 1311805 = 491927) (by norm_num)
theorem B984253 : Blo 690315 984253 := bbase (se 3 (by rfl) ⟨184547, by rfl⟩ : syracuseStep 984253 = 369095) (by norm_num)
theorem B885997 : Blo 690315 885997 := bbase (se 3 (by rfl) ⟨166124, by rfl⟩ : syracuseStep 885997 = 332249) (by norm_num)
theorem B3507461 : Blo 690315 3507461 := bbase (se 4 (by rfl) ⟨328824, by rfl⟩ : syracuseStep 3507461 = 657649) (by norm_num)
theorem B2950469 : Blo 690315 2950469 := bbase (se 4 (by rfl) ⟨276606, by rfl⟩ : syracuseStep 2950469 = 553213) (by norm_num)
theorem B1901909 : Blo 690315 1901909 := bbase (se 12 (by rfl) ⟨696, by rfl⟩ : syracuseStep 1901909 = 1393) (by norm_num)
theorem B1312109 : Blo 690315 1312109 := bbase (se 3 (by rfl) ⟨246020, by rfl⟩ : syracuseStep 1312109 = 492041) (by norm_num)
theorem B984469 : Blo 690315 984469 := bbase (se 6 (by rfl) ⟨23073, by rfl⟩ : syracuseStep 984469 = 46147) (by norm_num)
theorem B1476157 : Blo 690315 1476157 := bbase (se 3 (by rfl) ⟨276779, by rfl⟩ : syracuseStep 1476157 = 553559) (by norm_num)
theorem B3933845 : Blo 690315 3933845 := bbase (se 6 (by rfl) ⟨92199, by rfl⟩ : syracuseStep 3933845 = 184399) (by norm_num)
theorem B984845 : Blo 690315 984845 := bbase (se 3 (by rfl) ⟨184658, by rfl⟩ : syracuseStep 984845 = 369317) (by norm_num)
theorem B1869605 : Blo 690315 1869605 := bbase (se 4 (by rfl) ⟨175275, by rfl⟩ : syracuseStep 1869605 = 350551) (by norm_num)
theorem B1312861 : Blo 690315 1312861 := bbase (se 3 (by rfl) ⟨246161, by rfl⟩ : syracuseStep 1312861 = 492323) (by norm_num)
theorem B1870037 : Blo 690315 1870037 := bbase (se 7 (by rfl) ⟨21914, by rfl⟩ : syracuseStep 1870037 = 43829) (by norm_num)
theorem B1313005 : Blo 690315 1313005 := bbase (se 3 (by rfl) ⟨246188, by rfl⟩ : syracuseStep 1313005 = 492377) (by norm_num)
theorem B1968437 : Blo 690315 1968437 := bbase (se 5 (by rfl) ⟨92270, by rfl⟩ : syracuseStep 1968437 = 184541) (by norm_num)
theorem B1050989 : Blo 690315 1050989 := bbase (se 3 (by rfl) ⟨197060, by rfl⟩ : syracuseStep 1050989 = 394121) (by norm_num)
theorem B1313165 : Blo 690315 1313165 := bbase (se 3 (by rfl) ⟨246218, by rfl⟩ : syracuseStep 1313165 = 492437) (by norm_num)
theorem B1477045 : Blo 690315 1477045 := bbase (se 5 (by rfl) ⟨69236, by rfl⟩ : syracuseStep 1477045 = 138473) (by norm_num)
theorem B5245397 : Blo 690315 5245397 := bbase (se 7 (by rfl) ⟨61469, by rfl⟩ : syracuseStep 5245397 = 122939) (by norm_num)
theorem B2624021 : Blo 690315 2624021 := bbase (se 6 (by rfl) ⟨61500, by rfl⟩ : syracuseStep 2624021 = 123001) (by norm_num)
theorem B3508757 : Blo 690315 3508757 := bbase (se 6 (by rfl) ⟨82236, by rfl⟩ : syracuseStep 3508757 = 164473) (by norm_num)
theorem B1313309 : Blo 690315 1313309 := bbase (se 3 (by rfl) ⟨246245, by rfl⟩ : syracuseStep 1313309 = 492491) (by norm_num)
theorem B789085 : Blo 690315 789085 := bbase (se 3 (by rfl) ⟨147953, by rfl⟩ : syracuseStep 789085 = 295907) (by norm_num)
theorem B2624309 : Blo 690315 2624309 := bbase (se 5 (by rfl) ⟨123014, by rfl⟩ : syracuseStep 2624309 = 246029) (by norm_num)
theorem B4000565 : Blo 690315 4000565 := bbase (se 5 (by rfl) ⟨187526, by rfl⟩ : syracuseStep 4000565 = 375053) (by norm_num)
theorem B1313597 : Blo 690315 1313597 := bbase (se 3 (by rfl) ⟨246299, by rfl⟩ : syracuseStep 1313597 = 492599) (by norm_num)
theorem B1182533 : Blo 690315 1182533 := bbase (se 4 (by rfl) ⟨110862, by rfl⟩ : syracuseStep 1182533 = 221725) (by norm_num)
theorem B1477541 : Blo 690315 1477541 := bbase (se 4 (by rfl) ⟨138519, by rfl⟩ : syracuseStep 1477541 = 277039) (by norm_num)
theorem B1313749 : Blo 690315 1313749 := bbase (se 7 (by rfl) ⟨15395, by rfl⟩ : syracuseStep 1313749 = 30791) (by norm_num)
theorem B789569 : Blo 690315 789569 := bbase (se 2 (by rfl) ⟨296088, by rfl⟩ : syracuseStep 789569 = 592177) (by norm_num)
theorem B1576093 : Blo 690315 1576093 := bbase (se 3 (by rfl) ⟨295517, by rfl⟩ : syracuseStep 1576093 = 591035) (by norm_num)
theorem B986269 : Blo 690315 986269 := bbase (se 3 (by rfl) ⟨184925, by rfl⟩ : syracuseStep 986269 = 369851) (by norm_num)
theorem B4426933 : Blo 690315 4426933 := bbase (se 5 (by rfl) ⟨207512, by rfl⟩ : syracuseStep 4426933 = 415025) (by norm_num)
theorem B2329829 : Blo 690315 2329829 := bbase (se 4 (by rfl) ⟨218421, by rfl⟩ : syracuseStep 2329829 = 436843) (by norm_num)
theorem B888049 : Blo 690315 888049 := bbase (se 2 (by rfl) ⟨333018, by rfl⟩ : syracuseStep 888049 = 666037) (by norm_num)
theorem B1314053 : Blo 690315 1314053 := bbase (se 4 (by rfl) ⟨123192, by rfl⟩ : syracuseStep 1314053 = 246385) (by norm_num)
theorem B1248637 : Blo 690315 1248637 := bbase (se 3 (by rfl) ⟨234119, by rfl⟩ : syracuseStep 1248637 = 468239) (by norm_num)
theorem B1248709 : Blo 690315 1248709 := bbase (se 4 (by rfl) ⟨117066, by rfl⟩ : syracuseStep 1248709 = 234133) (by norm_num)
theorem B789961 : Blo 690315 789961 := bbase (se 2 (by rfl) ⟨296235, by rfl⟩ : syracuseStep 789961 = 592471) (by norm_num)
theorem B2100725 : Blo 690315 2100725 := bbase (se 5 (by rfl) ⟨98471, by rfl⟩ : syracuseStep 2100725 = 196943) (by norm_num)
theorem B1576493 : Blo 690315 1576493 := bbase (se 3 (by rfl) ⟨295592, by rfl⟩ : syracuseStep 1576493 = 591185) (by norm_num)
theorem B1248853 : Blo 690315 1248853 := bbase (se 8 (by rfl) ⟨7317, by rfl⟩ : syracuseStep 1248853 = 14635) (by norm_num)
theorem B2330261 : Blo 690315 2330261 := bbase (se 6 (by rfl) ⟨54615, by rfl⟩ : syracuseStep 2330261 = 109231) (by norm_num)
theorem B1052357 : Blo 690315 1052357 := bbase (se 4 (by rfl) ⟨98658, by rfl⟩ : syracuseStep 1052357 = 197317) (by norm_num)
theorem B986861 : Blo 690315 986861 := bbase (se 3 (by rfl) ⟨185036, by rfl⟩ : syracuseStep 986861 = 370073) (by norm_num)
theorem B1478405 : Blo 690315 1478405 := bbase (se 4 (by rfl) ⟨138600, by rfl⟩ : syracuseStep 1478405 = 277201) (by norm_num)
theorem B3510053 : Blo 690315 3510053 := bbase (se 4 (by rfl) ⟨329067, by rfl⟩ : syracuseStep 3510053 = 658135) (by norm_num)
theorem B3936053 : Blo 690315 3936053 := bbase (se 5 (by rfl) ⟨184502, by rfl⟩ : syracuseStep 3936053 = 369005) (by norm_num)
theorem B986941 : Blo 690315 986941 := bbase (se 3 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 986941 = 370103) (by norm_num)
theorem B1970021 : Blo 690315 1970021 := bbase (se 4 (by rfl) ⟨184689, by rfl⟩ : syracuseStep 1970021 = 369379) (by norm_num)
theorem B1183589 : Blo 690315 1183589 := bbase (se 4 (by rfl) ⟨110961, by rfl⟩ : syracuseStep 1183589 = 221923) (by norm_num)
theorem B757621 : Blo 690315 757621 := bbase (se 5 (by rfl) ⟨35513, by rfl⟩ : syracuseStep 757621 = 71027) (by norm_num)
theorem B1478549 : Blo 690315 1478549 := bbase (se 6 (by rfl) ⟨34653, by rfl⟩ : syracuseStep 1478549 = 69307) (by norm_num)
theorem B1871765 : Blo 690315 1871765 := bbase (se 6 (by rfl) ⟨43869, by rfl⟩ : syracuseStep 1871765 = 87739) (by norm_num)
theorem B987061 : Blo 690315 987061 := bbase (se 5 (by rfl) ⟨46268, by rfl⟩ : syracuseStep 987061 = 92537) (by norm_num)
theorem B2625493 : Blo 690315 2625493 := bbase (se 7 (by rfl) ⟨30767, by rfl⟩ : syracuseStep 2625493 = 61535) (by norm_num)
theorem B1314805 : Blo 690315 1314805 := bbase (se 5 (by rfl) ⟨61631, by rfl⟩ : syracuseStep 1314805 = 123263) (by norm_num)
theorem B2363413 : Blo 690315 2363413 := bbase (se 6 (by rfl) ⟨55392, by rfl⟩ : syracuseStep 2363413 = 110785) (by norm_num)
theorem B987157 : Blo 690315 987157 := bbase (se 6 (by rfl) ⟨23136, by rfl⟩ : syracuseStep 987157 = 46273) (by norm_num)
theorem B2330693 : Blo 690315 2330693 := bbase (se 4 (by rfl) ⟨218502, by rfl⟩ : syracuseStep 2330693 = 437005) (by norm_num)
theorem B888953 : Blo 690315 888953 := bbase (se 2 (by rfl) ⟨333357, by rfl⟩ : syracuseStep 888953 = 666715) (by norm_num)
theorem B1314949 : Blo 690315 1314949 := bbase (se 4 (by rfl) ⟨123276, by rfl⟩ : syracuseStep 1314949 = 246553) (by norm_num)
theorem B2625797 : Blo 690315 2625797 := bbase (se 4 (by rfl) ⟨246168, by rfl⟩ : syracuseStep 2625797 = 492337) (by norm_num)
theorem B1315109 : Blo 690315 1315109 := bbase (se 4 (by rfl) ⟨123291, by rfl⟩ : syracuseStep 1315109 = 246583) (by norm_num)
theorem B1249661 : Blo 690315 1249661 := bbase (se 3 (by rfl) ⟨234311, by rfl⟩ : syracuseStep 1249661 = 468623) (by norm_num)
theorem B1773965 : Blo 690315 1773965 := bbase (se 3 (by rfl) ⟨332618, by rfl⟩ : syracuseStep 1773965 = 665237) (by norm_num)
theorem B1315253 : Blo 690315 1315253 := bbase (se 5 (by rfl) ⟨61652, by rfl⟩ : syracuseStep 1315253 = 123305) (by norm_num)
theorem B1249717 : Blo 690315 1249717 := bbase (se 5 (by rfl) ⟨58580, by rfl⟩ : syracuseStep 1249717 = 117161) (by norm_num)
theorem B2331125 : Blo 690315 2331125 := bbase (se 5 (by rfl) ⟨109271, by rfl⟩ : syracuseStep 2331125 = 218543) (by norm_num)
theorem B1970693 : Blo 690315 1970693 := bbase (se 4 (by rfl) ⟨184752, by rfl⟩ : syracuseStep 1970693 = 369505) (by norm_num)
theorem B987653 : Blo 690315 987653 := bbase (se 4 (by rfl) ⟨92592, by rfl⟩ : syracuseStep 987653 = 185185) (by norm_num)
theorem B1249805 : Blo 690315 1249805 := bbase (se 3 (by rfl) ⟨234338, by rfl⟩ : syracuseStep 1249805 = 468677) (by norm_num)
theorem B1479293 : Blo 690315 1479293 := bbase (se 3 (by rfl) ⟨277367, by rfl⟩ : syracuseStep 1479293 = 554735) (by norm_num)
theorem B1315541 : Blo 690315 1315541 := bbase (se 7 (by rfl) ⟨15416, by rfl⟩ : syracuseStep 1315541 = 30833) (by norm_num)
theorem B1250093 : Blo 690315 1250093 := bbase (se 3 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 1250093 = 468785) (by norm_num)
theorem B1315693 : Blo 690315 1315693 := bbase (se 3 (by rfl) ⟨246692, by rfl⟩ : syracuseStep 1315693 = 493385) (by norm_num)
theorem B2331557 : Blo 690315 2331557 := bbase (se 4 (by rfl) ⟨218583, by rfl⟩ : syracuseStep 2331557 = 437167) (by norm_num)
theorem B1971125 : Blo 690315 1971125 := bbase (se 5 (by rfl) ⟨92396, by rfl⟩ : syracuseStep 1971125 = 184793) (by norm_num)
theorem B1250237 : Blo 690315 1250237 := bbase (se 3 (by rfl) ⟨234419, by rfl⟩ : syracuseStep 1250237 = 468839) (by norm_num)
theorem B1774541 : Blo 690315 1774541 := bbase (se 3 (by rfl) ⟨332726, by rfl⟩ : syracuseStep 1774541 = 665453) (by norm_num)
theorem B988205 : Blo 690315 988205 := bbase (se 3 (by rfl) ⟨185288, by rfl⟩ : syracuseStep 988205 = 370577) (by norm_num)
theorem B3511349 : Blo 690315 3511349 := bbase (se 5 (by rfl) ⟨164594, by rfl⟩ : syracuseStep 3511349 = 329189) (by norm_num)
theorem B2495573 : Blo 690315 2495573 := bbase (se 8 (by rfl) ⟨14622, by rfl⟩ : syracuseStep 2495573 = 29245) (by norm_num)
theorem B791677 : Blo 690315 791677 := bbase (se 3 (by rfl) ⟨148439, by rfl⟩ : syracuseStep 791677 = 296879) (by norm_num)
theorem B1315997 : Blo 690315 1315997 := bbase (se 3 (by rfl) ⟨246749, by rfl⟩ : syracuseStep 1315997 = 493499) (by norm_num)
theorem B1250525 : Blo 690315 1250525 := bbase (se 3 (by rfl) ⟨234473, by rfl⟩ : syracuseStep 1250525 = 468947) (by norm_num)
theorem B2954501 : Blo 690315 2954501 := bbase (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) (by norm_num)
theorem B1250597 : Blo 690315 1250597 := bbase (se 4 (by rfl) ⟨117243, by rfl⟩ : syracuseStep 1250597 = 234487) (by norm_num)
theorem B1774909 : Blo 690315 1774909 := bbase (se 3 (by rfl) ⟨332795, by rfl⟩ : syracuseStep 1774909 = 665591) (by norm_num)
theorem B890185 : Blo 690315 890185 := bbase (se 2 (by rfl) ⟨333819, by rfl⟩ : syracuseStep 890185 = 667639) (by norm_num)
theorem B2331989 : Blo 690315 2331989 := bbase (se 14 (by rfl) ⟨213, by rfl⟩ : syracuseStep 2331989 = 427) (by norm_num)
theorem B1480045 : Blo 690315 1480045 := bbase (se 3 (by rfl) ⟨277508, by rfl⟩ : syracuseStep 1480045 = 555017) (by norm_num)
theorem B5051765 : Blo 690315 5051765 := bbase (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) (by norm_num)
theorem B1054109 : Blo 690315 1054109 := bbase (se 3 (by rfl) ⟨197645, by rfl⟩ : syracuseStep 1054109 = 395291) (by norm_num)
theorem B1480189 : Blo 690315 1480189 := bbase (se 3 (by rfl) ⟨277535, by rfl⟩ : syracuseStep 1480189 = 555071) (by norm_num)
theorem B2496005 : Blo 690315 2496005 := bbase (se 4 (by rfl) ⟨234000, by rfl⟩ : syracuseStep 2496005 = 468001) (by norm_num)
theorem B2365013 : Blo 690315 2365013 := bbase (se 8 (by rfl) ⟨13857, by rfl⟩ : syracuseStep 2365013 = 27715) (by norm_num)
theorem B1971877 : Blo 690315 1971877 := bbase (se 4 (by rfl) ⟨184863, by rfl⟩ : syracuseStep 1971877 = 369727) (by norm_num)
theorem B2332421 : Blo 690315 2332421 := bbase (se 4 (by rfl) ⟨218664, by rfl⟩ : syracuseStep 2332421 = 437329) (by norm_num)
theorem B890677 : Blo 690315 890677 := bbase (se 5 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 890677 = 83501) (by norm_num)
theorem B1480565 : Blo 690315 1480565 := bbase (se 5 (by rfl) ⟨69401, by rfl⟩ : syracuseStep 1480565 = 138803) (by norm_num)
theorem B1316749 : Blo 690315 1316749 := bbase (se 3 (by rfl) ⟨246890, by rfl⟩ : syracuseStep 1316749 = 493781) (by norm_num)
theorem B1316893 : Blo 690315 1316893 := bbase (se 3 (by rfl) ⟨246917, by rfl⟩ : syracuseStep 1316893 = 493835) (by norm_num)
theorem B2136181 : Blo 690315 2136181 := bbase (se 5 (by rfl) ⟨100133, by rfl⟩ : syracuseStep 2136181 = 200267) (by norm_num)
theorem B2332853 : Blo 690315 2332853 := bbase (se 5 (by rfl) ⟨109352, by rfl⟩ : syracuseStep 2332853 = 218705) (by norm_num)
theorem B1317053 : Blo 690315 1317053 := bbase (se 3 (by rfl) ⟨246947, by rfl⟩ : syracuseStep 1317053 = 493895) (by norm_num)
theorem B1480933 : Blo 690315 1480933 := bbase (se 4 (by rfl) ⟨138837, by rfl⟩ : syracuseStep 1480933 = 277675) (by norm_num)
theorem B2627909 : Blo 690315 2627909 := bbase (se 4 (by rfl) ⟨246366, by rfl⟩ : syracuseStep 2627909 = 492733) (by norm_num)
theorem B3512645 : Blo 690315 3512645 := bbase (se 4 (by rfl) ⟨329310, by rfl⟩ : syracuseStep 3512645 = 658621) (by norm_num)
theorem B1317197 : Blo 690315 1317197 := bbase (se 3 (by rfl) ⟨246974, by rfl⟩ : syracuseStep 1317197 = 493949) (by norm_num)
theorem B2365861 : Blo 690315 2365861 := bbase (se 4 (by rfl) ⟨221799, by rfl⟩ : syracuseStep 2365861 = 443599) (by norm_num)
theorem B2333285 : Blo 690315 2333285 := bbase (se 4 (by rfl) ⟨218745, by rfl⟩ : syracuseStep 2333285 = 437491) (by norm_num)
theorem B2628197 : Blo 690315 2628197 := bbase (se 4 (by rfl) ⟨246393, by rfl⟩ : syracuseStep 2628197 = 492787) (by norm_num)
theorem B1317485 : Blo 690315 1317485 := bbase (se 3 (by rfl) ⟨247028, by rfl⟩ : syracuseStep 1317485 = 494057) (by norm_num)
theorem B1317637 : Blo 690315 1317637 := bbase (se 4 (by rfl) ⟨123528, by rfl⟩ : syracuseStep 1317637 = 247057) (by norm_num)
theorem B3152837 : Blo 690315 3152837 := bbase (se 4 (by rfl) ⟨295578, by rfl⟩ : syracuseStep 3152837 = 591157) (by norm_num)
theorem B2956277 : Blo 690315 2956277 := bbase (se 5 (by rfl) ⟨138575, by rfl⟩ : syracuseStep 2956277 = 277151) (by norm_num)
theorem B2333717 : Blo 690315 2333717 := bbase (se 6 (by rfl) ⟨54696, by rfl⟩ : syracuseStep 2333717 = 109393) (by norm_num)
theorem B1317941 : Blo 690315 1317941 := bbase (se 5 (by rfl) ⟨61778, by rfl⟩ : syracuseStep 1317941 = 123557) (by norm_num)
theorem B2137205 : Blo 690315 2137205 := bbase (se 5 (by rfl) ⟨100181, by rfl⟩ : syracuseStep 2137205 = 200363) (by norm_num)
theorem B2334149 : Blo 690315 2334149 := bbase (se 4 (by rfl) ⟨218826, by rfl⟩ : syracuseStep 2334149 = 437653) (by norm_num)
theorem B3513941 : Blo 690315 3513941 := bbase (se 8 (by rfl) ⟨20589, by rfl⟩ : syracuseStep 3513941 = 41179) (by norm_num)
theorem B1482437 : Blo 690315 1482437 := bbase (se 4 (by rfl) ⟨138978, by rfl⟩ : syracuseStep 1482437 = 277957) (by norm_num)
theorem B1777373 : Blo 690315 1777373 := bbase (se 3 (by rfl) ⟨333257, by rfl⟩ : syracuseStep 1777373 = 666515) (by norm_num)
theorem B2629381 : Blo 690315 2629381 := bbase (se 4 (by rfl) ⟨246504, by rfl⟩ : syracuseStep 2629381 = 493009) (by norm_num)
theorem B1482581 : Blo 690315 1482581 := bbase (se 9 (by rfl) ⟨4343, by rfl⟩ : syracuseStep 1482581 = 8687) (by norm_num)
theorem B2334581 : Blo 690315 2334581 := bbase (se 5 (by rfl) ⟨109433, by rfl⟩ : syracuseStep 2334581 = 218867) (by norm_num)
theorem B2957269 : Blo 690315 2957269 := bbase (se 7 (by rfl) ⟨34655, by rfl⟩ : syracuseStep 2957269 = 69311) (by norm_num)
theorem B2629685 : Blo 690315 2629685 := bbase (se 5 (by rfl) ⟨123266, by rfl⟩ : syracuseStep 2629685 = 246533) (by norm_num)
theorem B2335013 : Blo 690315 2335013 := bbase (se 4 (by rfl) ⟨218907, by rfl⟩ : syracuseStep 2335013 = 437815) (by norm_num)
theorem B1778069 : Blo 690315 1778069 := bbase (se 6 (by rfl) ⟨41673, by rfl⟩ : syracuseStep 1778069 = 83347) (by norm_num)
theorem B1974725 : Blo 690315 1974725 := bbase (se 4 (by rfl) ⟨185130, by rfl⟩ : syracuseStep 1974725 = 370261) (by norm_num)
theorem B1581637 : Blo 690315 1581637 := bbase (se 4 (by rfl) ⟨148278, by rfl⟩ : syracuseStep 1581637 = 296557) (by norm_num)
theorem B1352341 : Blo 690315 1352341 := bbase (se 6 (by rfl) ⟨31695, by rfl⟩ : syracuseStep 1352341 = 63391) (by norm_num)
theorem B2335445 : Blo 690315 2335445 := bbase (se 7 (by rfl) ⟨27368, by rfl⟩ : syracuseStep 2335445 = 54737) (by norm_num)
theorem B2499349 : Blo 690315 2499349 := bbase (se 6 (by rfl) ⟨58578, by rfl⟩ : syracuseStep 2499349 = 117157) (by norm_num)
theorem B4432981 : Blo 690315 4432981 := bbase (se 8 (by rfl) ⟨25974, by rfl⟩ : syracuseStep 4432981 = 51949) (by norm_num)
theorem B6661237 : Blo 690315 6661237 := bbase (se 5 (by rfl) ⟨312245, by rfl⟩ : syracuseStep 6661237 = 624491) (by norm_num)
theorem B2335877 : Blo 690315 2335877 := bbase (se 4 (by rfl) ⟨218988, by rfl⟩ : syracuseStep 2335877 = 437977) (by norm_num)
theorem B10003733 : Blo 690315 10003733 := bbase (se 6 (by rfl) ⟨234462, by rfl⟩ : syracuseStep 10003733 = 468925) (by norm_num)
theorem B2368901 : Blo 690315 2368901 := bbase (se 4 (by rfl) ⟨222084, by rfl⟩ : syracuseStep 2368901 = 444169) (by norm_num)
theorem B2368997 : Blo 690315 2368997 := bbase (se 4 (by rfl) ⟨222093, by rfl⟩ : syracuseStep 2368997 = 444187) (by norm_num)
theorem B2336309 : Blo 690315 2336309 := bbase (se 5 (by rfl) ⟨109514, by rfl⟩ : syracuseStep 2336309 = 219029) (by norm_num)
theorem B1975909 : Blo 690315 1975909 := bbase (se 4 (by rfl) ⟨185241, by rfl⟩ : syracuseStep 1975909 = 370483) (by norm_num)
theorem B1976069 : Blo 690315 1976069 := bbase (se 4 (by rfl) ⟨185256, by rfl⟩ : syracuseStep 1976069 = 370513) (by norm_num)
theorem B829397 : Blo 690315 829397 := bbase (se 7 (by rfl) ⟨9719, by rfl⟩ : syracuseStep 829397 = 19439) (by norm_num)
theorem B2336741 : Blo 690315 2336741 := bbase (se 4 (by rfl) ⟨219069, by rfl⟩ : syracuseStep 2336741 = 438139) (by norm_num)
theorem B1976309 : Blo 690315 1976309 := bbase (se 5 (by rfl) ⟨92639, by rfl⟩ : syracuseStep 1976309 = 185279) (by norm_num)
theorem B5253173 : Blo 690315 5253173 := bbase (se 5 (by rfl) ⟨246242, by rfl⟩ : syracuseStep 5253173 = 492485) (by norm_num)
theorem B2631797 : Blo 690315 2631797 := bbase (se 5 (by rfl) ⟨123365, by rfl⟩ : syracuseStep 2631797 = 246731) (by norm_num)
theorem B1976501 : Blo 690315 1976501 := bbase (se 5 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 1976501 = 185297) (by norm_num)
theorem B829705 : Blo 690315 829705 := bbase (se 2 (by rfl) ⟨311139, by rfl⟩ : syracuseStep 829705 = 622279) (by norm_num)
theorem B2337173 : Blo 690315 2337173 := bbase (se 6 (by rfl) ⟨54777, by rfl⟩ : syracuseStep 2337173 = 109555) (by norm_num)
theorem B2632085 : Blo 690315 2632085 := bbase (se 6 (by rfl) ⟨61689, by rfl⟩ : syracuseStep 2632085 = 123379) (by norm_num)
theorem B829873 : Blo 690315 829873 := bbase (se 2 (by rfl) ⟨311202, by rfl⟩ : syracuseStep 829873 = 622405) (by norm_num)
theorem B3320261 : Blo 690315 3320261 := bbase (se 4 (by rfl) ⟨311274, by rfl⟩ : syracuseStep 3320261 = 622549) (by norm_num)
theorem B1747453 : Blo 690315 1747453 := bbase (se 3 (by rfl) ⟨327647, by rfl⟩ : syracuseStep 1747453 = 655295) (by norm_num)
theorem B2107925 : Blo 690315 2107925 := bbase (se 6 (by rfl) ⟨49404, by rfl⟩ : syracuseStep 2107925 = 98809) (by norm_num)
theorem B1780309 : Blo 690315 1780309 := bbase (se 8 (by rfl) ⟨10431, by rfl⟩ : syracuseStep 1780309 = 20863) (by norm_num)
theorem B1747565 : Blo 690315 1747565 := bbase (se 3 (by rfl) ⟨327668, by rfl⟩ : syracuseStep 1747565 = 655337) (by norm_num)
theorem B830069 : Blo 690315 830069 := bbase (se 5 (by rfl) ⟨38909, by rfl⟩ : syracuseStep 830069 = 77819) (by norm_num)
theorem B1747757 : Blo 690315 1747757 := bbase (se 3 (by rfl) ⟨327704, by rfl⟩ : syracuseStep 1747757 = 655409) (by norm_num)
theorem B2337605 : Blo 690315 2337605 := bbase (se 4 (by rfl) ⟨219150, by rfl⟩ : syracuseStep 2337605 = 438301) (by norm_num)
theorem B3550229 : Blo 690315 3550229 := bbase (se 6 (by rfl) ⟨83208, by rfl⟩ : syracuseStep 3550229 = 166417) (by norm_num)
theorem B1748101 : Blo 690315 1748101 := bbase (se 4 (by rfl) ⟨163884, by rfl⟩ : syracuseStep 1748101 = 327769) (by norm_num)
theorem B5680277 : Blo 690315 5680277 := bbase (se 6 (by rfl) ⟨133131, by rfl⟩ : syracuseStep 5680277 = 266263) (by norm_num)
theorem B3550373 : Blo 690315 3550373 := bbase (se 4 (by rfl) ⟨332847, by rfl⟩ : syracuseStep 3550373 = 665695) (by norm_num)
theorem B1748213 : Blo 690315 1748213 := bbase (se 5 (by rfl) ⟨81947, by rfl⟩ : syracuseStep 1748213 = 163895) (by norm_num)
theorem B2338037 : Blo 690315 2338037 := bbase (se 5 (by rfl) ⟨109595, by rfl⟩ : syracuseStep 2338037 = 219191) (by norm_num)
theorem B5680469 : Blo 690315 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B1748405 : Blo 690315 1748405 := bbase (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) (by norm_num)
theorem B2633269 : Blo 690315 2633269 := bbase (se 5 (by rfl) ⟨123434, by rfl⟩ : syracuseStep 2633269 = 246869) (by norm_num)
theorem B798373 : Blo 690315 798373 := bbase (se 4 (by rfl) ⟨74847, by rfl⟩ : syracuseStep 798373 = 149695) (by norm_num)
theorem B2338469 : Blo 690315 2338469 := bbase (se 4 (by rfl) ⟨219231, by rfl⟩ : syracuseStep 2338469 = 438463) (by norm_num)
theorem B1748749 : Blo 690315 1748749 := bbase (se 3 (by rfl) ⟨327890, by rfl⟩ : syracuseStep 1748749 = 655781) (by norm_num)
theorem B2633573 : Blo 690315 2633573 := bbase (se 4 (by rfl) ⟨246897, by rfl⟩ : syracuseStep 2633573 = 493795) (by norm_num)
theorem B4435829 : Blo 690315 4435829 := bbase (se 5 (by rfl) ⟨207929, by rfl⟩ : syracuseStep 4435829 = 415859) (by norm_num)
theorem B1748861 : Blo 690315 1748861 := bbase (se 3 (by rfl) ⟨327911, by rfl⟩ : syracuseStep 1748861 = 655823) (by norm_num)
theorem B3158021 : Blo 690315 3158021 := bbase (se 4 (by rfl) ⟨296064, by rfl⟩ : syracuseStep 3158021 = 592129) (by norm_num)
theorem B700445 : Blo 690315 700445 := bbase (se 3 (by rfl) ⟨131333, by rfl⟩ : syracuseStep 700445 = 262667) (by norm_num)
theorem B1749053 : Blo 690315 1749053 := bbase (se 3 (by rfl) ⟨327947, by rfl⟩ : syracuseStep 1749053 = 655895) (by norm_num)
theorem B2338901 : Blo 690315 2338901 := bbase (se 8 (by rfl) ⟨13704, by rfl⟩ : syracuseStep 2338901 = 27409) (by norm_num)
theorem B2535509 : Blo 690315 2535509 := bbase (se 8 (by rfl) ⟨14856, by rfl⟩ : syracuseStep 2535509 = 29713) (by norm_num)
theorem B831641 : Blo 690315 831641 := bbase (se 2 (by rfl) ⟨311865, by rfl⟩ : syracuseStep 831641 = 623731) (by norm_num)
theorem B831665 : Blo 690315 831665 := bbase (se 2 (by rfl) ⟨311874, by rfl⟩ : syracuseStep 831665 = 623749) (by norm_num)
theorem B1749397 : Blo 690315 1749397 := bbase (se 6 (by rfl) ⟨41001, by rfl⟩ : syracuseStep 1749397 = 82003) (by norm_num)
theorem B831973 : Blo 690315 831973 := bbase (se 4 (by rfl) ⟨77997, by rfl⟩ : syracuseStep 831973 = 155995) (by norm_num)
theorem B2994677 : Blo 690315 2994677 := bbase (se 5 (by rfl) ⟨140375, by rfl⟩ : syracuseStep 2994677 = 280751) (by norm_num)
theorem B1749509 : Blo 690315 1749509 := bbase (se 4 (by rfl) ⟨164016, by rfl⟩ : syracuseStep 1749509 = 328033) (by norm_num)
theorem B2339333 : Blo 690315 2339333 := bbase (se 4 (by rfl) ⟨219312, by rfl⟩ : syracuseStep 2339333 = 438625) (by norm_num)
theorem B799345 : Blo 690315 799345 := bbase (se 2 (by rfl) ⟨299754, by rfl⟩ : syracuseStep 799345 = 599509) (by norm_num)
theorem B832145 : Blo 690315 832145 := bbase (se 2 (by rfl) ⟨312054, by rfl⟩ : syracuseStep 832145 = 624109) (by norm_num)
theorem B1749701 : Blo 690315 1749701 := bbase (se 4 (by rfl) ⟨164034, by rfl⟩ : syracuseStep 1749701 = 328069) (by norm_num)
theorem B832261 : Blo 690315 832261 := bbase (se 4 (by rfl) ⟨78024, by rfl⟩ : syracuseStep 832261 = 156049) (by norm_num)
theorem B1553237 : Blo 690315 1553237 := bbase (se 9 (by rfl) ⟨4550, by rfl⟩ : syracuseStep 1553237 = 9101) (by norm_num)
theorem B1422173 : Blo 690315 1422173 := bbase (se 3 (by rfl) ⟨266657, by rfl⟩ : syracuseStep 1422173 = 533315) (by norm_num)
theorem B832357 : Blo 690315 832357 := bbase (se 4 (by rfl) ⟨78033, by rfl⟩ : syracuseStep 832357 = 156067) (by norm_num)
theorem B2962277 : Blo 690315 2962277 := bbase (se 4 (by rfl) ⟨277713, by rfl⟩ : syracuseStep 2962277 = 555427) (by norm_num)
theorem B1553309 : Blo 690315 1553309 := bbase (se 3 (by rfl) ⟨291245, by rfl⟩ : syracuseStep 1553309 = 582491) (by norm_num)
theorem B2339765 : Blo 690315 2339765 := bbase (se 5 (by rfl) ⟨109676, by rfl⟩ : syracuseStep 2339765 = 219353) (by norm_num)
theorem B701393 : Blo 690315 701393 := bbase (se 2 (by rfl) ⟨263022, by rfl⟩ : syracuseStep 701393 = 526045) (by norm_num)
theorem B1553381 : Blo 690315 1553381 := bbase (se 4 (by rfl) ⟨145629, by rfl⟩ : syracuseStep 1553381 = 291259) (by norm_num)
theorem B832501 : Blo 690315 832501 := bbase (se 5 (by rfl) ⟨39023, by rfl⟩ : syracuseStep 832501 = 78047) (by norm_num)
theorem B1750045 : Blo 690315 1750045 := bbase (se 3 (by rfl) ⟨328133, by rfl⟩ : syracuseStep 1750045 = 656267) (by norm_num)
theorem B1553453 : Blo 690315 1553453 := bbase (se 3 (by rfl) ⟨291272, by rfl⟩ : syracuseStep 1553453 = 582545) (by norm_num)
theorem B1553525 : Blo 690315 1553525 := bbase (se 5 (by rfl) ⟨72821, by rfl⟩ : syracuseStep 1553525 = 145643) (by norm_num)
theorem B2962565 : Blo 690315 2962565 := bbase (se 4 (by rfl) ⟨277740, by rfl⟩ : syracuseStep 2962565 = 555481) (by norm_num)
theorem B1750157 : Blo 690315 1750157 := bbase (se 3 (by rfl) ⟨328154, by rfl⟩ : syracuseStep 1750157 = 656309) (by norm_num)
theorem B3323045 : Blo 690315 3323045 := bbase (se 4 (by rfl) ⟨311535, by rfl⟩ : syracuseStep 3323045 = 623071) (by norm_num)
theorem B1553597 : Blo 690315 1553597 := bbase (se 3 (by rfl) ⟨291299, by rfl⟩ : syracuseStep 1553597 = 582599) (by norm_num)
theorem B6665429 : Blo 690315 6665429 := bbase (se 7 (by rfl) ⟨78110, by rfl⟩ : syracuseStep 6665429 = 156221) (by norm_num)
theorem B1553669 : Blo 690315 1553669 := bbase (se 4 (by rfl) ⟨145656, by rfl⟩ : syracuseStep 1553669 = 291313) (by norm_num)
theorem B1553741 : Blo 690315 1553741 := bbase (se 3 (by rfl) ⟨291326, by rfl⟩ : syracuseStep 1553741 = 582653) (by norm_num)
theorem B1750349 : Blo 690315 1750349 := bbase (se 3 (by rfl) ⟨328190, by rfl⟩ : syracuseStep 1750349 = 656381) (by norm_num)
theorem B2340197 : Blo 690315 2340197 := bbase (se 4 (by rfl) ⟨219393, by rfl⟩ : syracuseStep 2340197 = 438787) (by norm_num)
theorem B1553813 : Blo 690315 1553813 := bbase (se 6 (by rfl) ⟨36417, by rfl⟩ : syracuseStep 1553813 = 72835) (by norm_num)
theorem B3945941 : Blo 690315 3945941 := bbase (se 7 (by rfl) ⟨46241, by rfl⟩ : syracuseStep 3945941 = 92483) (by norm_num)
theorem B1553885 : Blo 690315 1553885 := bbase (se 3 (by rfl) ⟨291353, by rfl⟩ : syracuseStep 1553885 = 582707) (by norm_num)
theorem B701957 : Blo 690315 701957 := bbase (se 4 (by rfl) ⟨65808, by rfl⟩ : syracuseStep 701957 = 131617) (by norm_num)
theorem B1553957 : Blo 690315 1553957 := bbase (se 4 (by rfl) ⟨145683, by rfl⟩ : syracuseStep 1553957 = 291367) (by norm_num)
theorem B40416853 : Blo 690315 40416853 := bbase (se 8 (by rfl) ⟨236817, by rfl⟩ : syracuseStep 40416853 = 473635) (by norm_num)
theorem B1554029 : Blo 690315 1554029 := bbase (se 3 (by rfl) ⟨291380, by rfl⟩ : syracuseStep 1554029 = 582761) (by norm_num)
theorem B1750693 : Blo 690315 1750693 := bbase (se 4 (by rfl) ⟨164127, by rfl⟩ : syracuseStep 1750693 = 328255) (by norm_num)
theorem B1554101 : Blo 690315 1554101 := bbase (se 5 (by rfl) ⟨72848, by rfl⟩ : syracuseStep 1554101 = 145697) (by norm_num)
theorem B1554173 : Blo 690315 1554173 := bbase (se 3 (by rfl) ⟨291407, by rfl⟩ : syracuseStep 1554173 = 582815) (by norm_num)
theorem B702217 : Blo 690315 702217 := bbase (se 2 (by rfl) ⟨263331, by rfl⟩ : syracuseStep 702217 = 526663) (by norm_num)
theorem B1750805 : Blo 690315 1750805 := bbase (se 6 (by rfl) ⟨41034, by rfl⟩ : syracuseStep 1750805 = 82069) (by norm_num)
theorem B2340629 : Blo 690315 2340629 := bbase (se 6 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 2340629 = 109717) (by norm_num)
theorem B1554245 : Blo 690315 1554245 := bbase (se 4 (by rfl) ⟨145710, by rfl⟩ : syracuseStep 1554245 = 291421) (by norm_num)
theorem B2963317 : Blo 690315 2963317 := bbase (se 5 (by rfl) ⟨138905, by rfl⟩ : syracuseStep 2963317 = 277811) (by norm_num)
theorem B1554317 : Blo 690315 1554317 := bbase (se 3 (by rfl) ⟨291434, by rfl⟩ : syracuseStep 1554317 = 582869) (by norm_num)
theorem B2635685 : Blo 690315 2635685 := bbase (se 4 (by rfl) ⟨247095, by rfl⟩ : syracuseStep 2635685 = 494191) (by norm_num)
theorem B1554389 : Blo 690315 1554389 := bbase (se 7 (by rfl) ⟨18215, by rfl⟩ : syracuseStep 1554389 = 36431) (by norm_num)
theorem B1750997 : Blo 690315 1750997 := bbase (se 7 (by rfl) ⟨20519, by rfl⟩ : syracuseStep 1750997 = 41039) (by norm_num)
theorem B1554461 : Blo 690315 1554461 := bbase (se 3 (by rfl) ⟨291461, by rfl⟩ : syracuseStep 1554461 = 582923) (by norm_num)
theorem B1554533 : Blo 690315 1554533 := bbase (se 4 (by rfl) ⟨145737, by rfl⟩ : syracuseStep 1554533 = 291475) (by norm_num)
theorem B702577 : Blo 690315 702577 := bbase (se 2 (by rfl) ⟨263466, by rfl⟩ : syracuseStep 702577 = 526933) (by norm_num)
theorem B1554605 : Blo 690315 1554605 := bbase (se 3 (by rfl) ⟨291488, by rfl⟩ : syracuseStep 1554605 = 582977) (by norm_num)
theorem B2341061 : Blo 690315 2341061 := bbase (se 4 (by rfl) ⟨219474, by rfl⟩ : syracuseStep 2341061 = 438949) (by norm_num)
theorem B2635973 : Blo 690315 2635973 := bbase (se 4 (by rfl) ⟨247122, by rfl⟩ : syracuseStep 2635973 = 494245) (by norm_num)
theorem B1554677 : Blo 690315 1554677 := bbase (se 5 (by rfl) ⟨72875, by rfl⟩ : syracuseStep 1554677 = 145751) (by norm_num)
theorem B1751341 : Blo 690315 1751341 := bbase (se 3 (by rfl) ⟨328376, by rfl⟩ : syracuseStep 1751341 = 656753) (by norm_num)
theorem B1554749 : Blo 690315 1554749 := bbase (se 3 (by rfl) ⟨291515, by rfl⟩ : syracuseStep 1554749 = 583031) (by norm_num)
theorem B1554821 : Blo 690315 1554821 := bbase (se 4 (by rfl) ⟨145764, by rfl⟩ : syracuseStep 1554821 = 291529) (by norm_num)
theorem B1751453 : Blo 690315 1751453 := bbase (se 3 (by rfl) ⟨328397, by rfl⟩ : syracuseStep 1751453 = 656795) (by norm_num)
theorem B1554893 : Blo 690315 1554893 := bbase (se 3 (by rfl) ⟨291542, by rfl⟩ : syracuseStep 1554893 = 583085) (by norm_num)
theorem B1554965 : Blo 690315 1554965 := bbase (se 6 (by rfl) ⟨36444, by rfl⟩ : syracuseStep 1554965 = 72889) (by norm_num)
theorem B2964053 : Blo 690315 2964053 := bbase (se 8 (by rfl) ⟨17367, by rfl⟩ : syracuseStep 2964053 = 34735) (by norm_num)
theorem B1555037 : Blo 690315 1555037 := bbase (se 3 (by rfl) ⟨291569, by rfl⟩ : syracuseStep 1555037 = 583139) (by norm_num)
theorem B1751645 : Blo 690315 1751645 := bbase (se 3 (by rfl) ⟨328433, by rfl⟩ : syracuseStep 1751645 = 656867) (by norm_num)
theorem B4995701 : Blo 690315 4995701 := bbase (se 5 (by rfl) ⟨234173, by rfl⟩ : syracuseStep 4995701 = 468347) (by norm_num)
theorem B2341493 : Blo 690315 2341493 := bbase (se 5 (by rfl) ⟨109757, by rfl⟩ : syracuseStep 2341493 = 219515) (by norm_num)
theorem B2374261 : Blo 690315 2374261 := bbase (se 5 (by rfl) ⟨111293, by rfl⟩ : syracuseStep 2374261 = 222587) (by norm_num)
theorem B1555109 : Blo 690315 1555109 := bbase (se 4 (by rfl) ⟨145791, by rfl⟩ : syracuseStep 1555109 = 291583) (by norm_num)
theorem B1555181 : Blo 690315 1555181 := bbase (se 3 (by rfl) ⟨291596, by rfl⟩ : syracuseStep 1555181 = 583193) (by norm_num)
theorem B1555253 : Blo 690315 1555253 := bbase (se 5 (by rfl) ⟨72902, by rfl⟩ : syracuseStep 1555253 = 145805) (by norm_num)
theorem B1555325 : Blo 690315 1555325 := bbase (se 3 (by rfl) ⟨291623, by rfl⟩ : syracuseStep 1555325 = 583247) (by norm_num)
theorem B1751989 : Blo 690315 1751989 := bbase (se 5 (by rfl) ⟨82124, by rfl⟩ : syracuseStep 1751989 = 164249) (by norm_num)
theorem B1555397 : Blo 690315 1555397 := bbase (se 4 (by rfl) ⟨145818, by rfl⟩ : syracuseStep 1555397 = 291637) (by norm_num)
theorem B1555469 : Blo 690315 1555469 := bbase (se 3 (by rfl) ⟨291650, by rfl⟩ : syracuseStep 1555469 = 583301) (by norm_num)
theorem B1752101 : Blo 690315 1752101 := bbase (se 4 (by rfl) ⟨164259, by rfl⟩ : syracuseStep 1752101 = 328519) (by norm_num)
theorem B2341925 : Blo 690315 2341925 := bbase (se 4 (by rfl) ⟨219555, by rfl⟩ : syracuseStep 2341925 = 439111) (by norm_num)
theorem B1555541 : Blo 690315 1555541 := bbase (se 8 (by rfl) ⟨9114, by rfl⟩ : syracuseStep 1555541 = 18229) (by norm_num)
theorem B1555613 : Blo 690315 1555613 := bbase (se 3 (by rfl) ⟨291677, by rfl⟩ : syracuseStep 1555613 = 583355) (by norm_num)
theorem B1555685 : Blo 690315 1555685 := bbase (se 4 (by rfl) ⟨145845, by rfl⟩ : syracuseStep 1555685 = 291691) (by norm_num)
theorem B1752293 : Blo 690315 1752293 := bbase (se 4 (by rfl) ⟨164277, by rfl⟩ : syracuseStep 1752293 = 328555) (by norm_num)
theorem B1555757 : Blo 690315 1555757 := bbase (se 3 (by rfl) ⟨291704, by rfl⟩ : syracuseStep 1555757 = 583409) (by norm_num)
theorem B1555829 : Blo 690315 1555829 := bbase (se 5 (by rfl) ⟨72929, by rfl⟩ : syracuseStep 1555829 = 145859) (by norm_num)
theorem B933277 : Blo 690315 933277 := bbase (se 3 (by rfl) ⟨174989, by rfl⟩ : syracuseStep 933277 = 349979) (by norm_num)
theorem B998821 : Blo 690315 998821 := bbase (se 4 (by rfl) ⟨93639, by rfl⟩ : syracuseStep 998821 = 187279) (by norm_num)
theorem B1555901 : Blo 690315 1555901 := bbase (se 3 (by rfl) ⟨291731, by rfl⟩ : syracuseStep 1555901 = 583463) (by norm_num)
theorem B2342357 : Blo 690315 2342357 := bbase (se 7 (by rfl) ⟨27449, by rfl⟩ : syracuseStep 2342357 = 54899) (by norm_num)
theorem B1555973 : Blo 690315 1555973 := bbase (se 4 (by rfl) ⟨145872, by rfl⟩ : syracuseStep 1555973 = 291745) (by norm_num)
theorem B4439573 : Blo 690315 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B1752637 : Blo 690315 1752637 := bbase (se 3 (by rfl) ⟨328619, by rfl⟩ : syracuseStep 1752637 = 657239) (by norm_num)
theorem B2375237 : Blo 690315 2375237 := bbase (se 4 (by rfl) ⟨222678, by rfl⟩ : syracuseStep 2375237 = 445357) (by norm_num)
theorem B1556045 : Blo 690315 1556045 := bbase (se 3 (by rfl) ⟨291758, by rfl⟩ : syracuseStep 1556045 = 583517) (by norm_num)
theorem B1523333 : Blo 690315 1523333 := bbase (se 4 (by rfl) ⟨142812, by rfl⟩ : syracuseStep 1523333 = 285625) (by norm_num)
theorem B1556117 : Blo 690315 1556117 := bbase (se 6 (by rfl) ⟨36471, by rfl⟩ : syracuseStep 1556117 = 72943) (by norm_num)
theorem B1752749 : Blo 690315 1752749 := bbase (se 3 (by rfl) ⟨328640, by rfl⟩ : syracuseStep 1752749 = 657281) (by norm_num)
theorem B1556189 : Blo 690315 1556189 := bbase (se 3 (by rfl) ⟨291785, by rfl⟩ : syracuseStep 1556189 = 583571) (by norm_num)
theorem B4275989 : Blo 690315 4275989 := bbase (se 6 (by rfl) ⟨100218, by rfl⟩ : syracuseStep 4275989 = 200437) (by norm_num)
theorem B1556261 : Blo 690315 1556261 := bbase (se 4 (by rfl) ⟨145899, by rfl⟩ : syracuseStep 1556261 = 291799) (by norm_num)
theorem B1556333 : Blo 690315 1556333 := bbase (se 3 (by rfl) ⟨291812, by rfl⟩ : syracuseStep 1556333 = 583625) (by norm_num)
theorem B1752941 : Blo 690315 1752941 := bbase (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) (by norm_num)
theorem B2342789 : Blo 690315 2342789 := bbase (se 4 (by rfl) ⟨219636, by rfl⟩ : syracuseStep 2342789 = 439273) (by norm_num)
theorem B1556405 : Blo 690315 1556405 := bbase (se 5 (by rfl) ⟨72956, by rfl⟩ : syracuseStep 1556405 = 145913) (by norm_num)
theorem B3162037 : Blo 690315 3162037 := bbase (se 5 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 3162037 = 296441) (by norm_num)
theorem B1556477 : Blo 690315 1556477 := bbase (se 3 (by rfl) ⟨291839, by rfl⟩ : syracuseStep 1556477 = 583679) (by norm_num)
theorem B2211877 : Blo 690315 2211877 := bbase (se 4 (by rfl) ⟨207363, by rfl⟩ : syracuseStep 2211877 = 414727) (by norm_num)
theorem B1556549 : Blo 690315 1556549 := bbase (se 4 (by rfl) ⟨145926, by rfl⟩ : syracuseStep 1556549 = 291853) (by norm_num)
theorem B5914741 : Blo 690315 5914741 := bbase (se 5 (by rfl) ⟨277253, by rfl⟩ : syracuseStep 5914741 = 554507) (by norm_num)
theorem B1556621 : Blo 690315 1556621 := bbase (se 3 (by rfl) ⟨291866, by rfl⟩ : syracuseStep 1556621 = 583733) (by norm_num)
theorem B737429 : Blo 690315 737429 := bbase (se 6 (by rfl) ⟨17283, by rfl⟩ : syracuseStep 737429 = 34567) (by norm_num)
theorem B1753285 : Blo 690315 1753285 := bbase (se 4 (by rfl) ⟨164370, by rfl⟩ : syracuseStep 1753285 = 328741) (by norm_num)
theorem B1851589 : Blo 690315 1851589 := bbase (se 4 (by rfl) ⟨173586, by rfl⟩ : syracuseStep 1851589 = 347173) (by norm_num)
theorem B1556693 : Blo 690315 1556693 := bbase (se 7 (by rfl) ⟨18242, by rfl⟩ : syracuseStep 1556693 = 36485) (by norm_num)
theorem B1556765 : Blo 690315 1556765 := bbase (se 3 (by rfl) ⟨291893, by rfl⟩ : syracuseStep 1556765 = 583787) (by norm_num)
theorem B1753397 : Blo 690315 1753397 := bbase (se 5 (by rfl) ⟨82190, by rfl⟩ : syracuseStep 1753397 = 164381) (by norm_num)
theorem B2343221 : Blo 690315 2343221 := bbase (se 5 (by rfl) ⟨109838, by rfl⟩ : syracuseStep 2343221 = 219677) (by norm_num)
theorem B999749 : Blo 690315 999749 := bbase (se 4 (by rfl) ⟨93726, by rfl⟩ : syracuseStep 999749 = 187453) (by norm_num)
theorem B1556837 : Blo 690315 1556837 := bbase (se 4 (by rfl) ⟨145953, by rfl⟩ : syracuseStep 1556837 = 291907) (by norm_num)
theorem B737677 : Blo 690315 737677 := bbase (se 3 (by rfl) ⟨138314, by rfl⟩ : syracuseStep 737677 = 276629) (by norm_num)
theorem B1556909 : Blo 690315 1556909 := bbase (se 3 (by rfl) ⟨291920, by rfl⟩ : syracuseStep 1556909 = 583841) (by norm_num)
theorem B1556981 : Blo 690315 1556981 := bbase (se 5 (by rfl) ⟨72983, by rfl⟩ : syracuseStep 1556981 = 145967) (by norm_num)
theorem B1753589 : Blo 690315 1753589 := bbase (se 5 (by rfl) ⟨82199, by rfl⟩ : syracuseStep 1753589 = 164399) (by norm_num)
theorem B1557053 : Blo 690315 1557053 := bbase (se 3 (by rfl) ⟨291947, by rfl⟩ : syracuseStep 1557053 = 583895) (by norm_num)
theorem B1557125 : Blo 690315 1557125 := bbase (se 4 (by rfl) ⟨145980, by rfl⟩ : syracuseStep 1557125 = 291961) (by norm_num)
theorem B1557197 : Blo 690315 1557197 := bbase (se 3 (by rfl) ⟨291974, by rfl⟩ : syracuseStep 1557197 = 583949) (by norm_num)
theorem B1557269 : Blo 690315 1557269 := bbase (se 6 (by rfl) ⟨36498, by rfl⟩ : syracuseStep 1557269 = 72997) (by norm_num)
theorem B738109 : Blo 690315 738109 := bbase (se 3 (by rfl) ⟨138395, by rfl⟩ : syracuseStep 738109 = 276791) (by norm_num)
theorem B1753933 : Blo 690315 1753933 := bbase (se 3 (by rfl) ⟨328862, by rfl⟩ : syracuseStep 1753933 = 657725) (by norm_num)
theorem B1557341 : Blo 690315 1557341 := bbase (se 3 (by rfl) ⟨292001, by rfl⟩ : syracuseStep 1557341 = 584003) (by norm_num)
theorem B738181 : Blo 690315 738181 := bbase (se 4 (by rfl) ⟨69204, by rfl⟩ : syracuseStep 738181 = 138409) (by norm_num)
theorem B1557413 : Blo 690315 1557413 := bbase (se 4 (by rfl) ⟨146007, by rfl⟩ : syracuseStep 1557413 = 292015) (by norm_num)
theorem B1754045 : Blo 690315 1754045 := bbase (se 3 (by rfl) ⟨328883, by rfl⟩ : syracuseStep 1754045 = 657767) (by norm_num)
theorem B1557485 : Blo 690315 1557485 := bbase (se 3 (by rfl) ⟨292028, by rfl⟩ : syracuseStep 1557485 = 584057) (by norm_num)
theorem B1557557 : Blo 690315 1557557 := bbase (se 5 (by rfl) ⟨73010, by rfl⟩ : syracuseStep 1557557 = 146021) (by norm_num)
theorem B1557629 : Blo 690315 1557629 := bbase (se 3 (by rfl) ⟨292055, by rfl⟩ : syracuseStep 1557629 = 584111) (by norm_num)
theorem B1754237 : Blo 690315 1754237 := bbase (se 3 (by rfl) ⟨328919, by rfl⟩ : syracuseStep 1754237 = 657839) (by norm_num)
theorem B1557701 : Blo 690315 1557701 := bbase (se 4 (by rfl) ⟨146034, by rfl⟩ : syracuseStep 1557701 = 292069) (by norm_num)
theorem B27280597 : Blo 690315 27280597 := bbase (se 7 (by rfl) ⟨319694, by rfl⟩ : syracuseStep 27280597 = 639389) (by norm_num)
theorem B1000669 : Blo 690315 1000669 := bbase (se 3 (by rfl) ⟨187625, by rfl⟩ : syracuseStep 1000669 = 375251) (by norm_num)
theorem B4211957 : Blo 690315 4211957 := bbase (se 5 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 4211957 = 394871) (by norm_num)
theorem B738553 : Blo 690315 738553 := bbase (se 2 (by rfl) ⟨276957, by rfl⟩ : syracuseStep 738553 = 553915) (by norm_num)
theorem B1557773 : Blo 690315 1557773 := bbase (se 3 (by rfl) ⟨292082, by rfl⟩ : syracuseStep 1557773 = 584165) (by norm_num)
theorem B1557845 : Blo 690315 1557845 := bbase (se 12 (by rfl) ⟨570, by rfl⟩ : syracuseStep 1557845 = 1141) (by norm_num)
theorem B2213237 : Blo 690315 2213237 := bbase (se 5 (by rfl) ⟨103745, by rfl⟩ : syracuseStep 2213237 = 207491) (by norm_num)
theorem B1557917 : Blo 690315 1557917 := bbase (se 3 (by rfl) ⟨292109, by rfl⟩ : syracuseStep 1557917 = 584219) (by norm_num)
theorem B2803157 : Blo 690315 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B1754581 : Blo 690315 1754581 := bbase (se 7 (by rfl) ⟨20561, by rfl⟩ : syracuseStep 1754581 = 41123) (by norm_num)
theorem B1557989 : Blo 690315 1557989 := bbase (se 4 (by rfl) ⟨146061, by rfl⟩ : syracuseStep 1557989 = 292123) (by norm_num)
theorem B2213365 : Blo 690315 2213365 := bbase (se 5 (by rfl) ⟨103751, by rfl⟩ : syracuseStep 2213365 = 207503) (by norm_num)
theorem B1558061 : Blo 690315 1558061 := bbase (se 3 (by rfl) ⟨292136, by rfl⟩ : syracuseStep 1558061 = 584273) (by norm_num)
theorem B2246213 : Blo 690315 2246213 := bbase (se 4 (by rfl) ⟨210582, by rfl⟩ : syracuseStep 2246213 = 421165) (by norm_num)
theorem B1754693 : Blo 690315 1754693 := bbase (se 4 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 1754693 = 329005) (by norm_num)
theorem B738929 : Blo 690315 738929 := bbase (se 2 (by rfl) ⟨277098, by rfl⟩ : syracuseStep 738929 = 554197) (by norm_num)
theorem B1558133 : Blo 690315 1558133 := bbase (se 5 (by rfl) ⟨73037, by rfl⟩ : syracuseStep 1558133 = 146075) (by norm_num)
theorem B1328765 : Blo 690315 1328765 := bbase (se 3 (by rfl) ⟨249143, by rfl⟩ : syracuseStep 1328765 = 498287) (by norm_num)
theorem B5260949 : Blo 690315 5260949 := bbase (se 6 (by rfl) ⟨123303, by rfl⟩ : syracuseStep 5260949 = 246607) (by norm_num)
theorem B739001 : Blo 690315 739001 := bbase (se 2 (by rfl) ⟨277125, by rfl⟩ : syracuseStep 739001 = 554251) (by norm_num)
theorem B1164989 : Blo 690315 1164989 := bbase (se 3 (by rfl) ⟨218435, by rfl⟩ : syracuseStep 1164989 = 436871) (by norm_num)
theorem B1558205 : Blo 690315 1558205 := bbase (se 3 (by rfl) ⟨292163, by rfl⟩ : syracuseStep 1558205 = 584327) (by norm_num)
theorem B2213621 : Blo 690315 2213621 := bbase (se 5 (by rfl) ⟨103763, by rfl⟩ : syracuseStep 2213621 = 207527) (by norm_num)
theorem B1558277 : Blo 690315 1558277 := bbase (se 4 (by rfl) ⟨146088, by rfl⟩ : syracuseStep 1558277 = 292177) (by norm_num)
theorem B1754885 : Blo 690315 1754885 := bbase (se 4 (by rfl) ⟨164520, by rfl⟩ : syracuseStep 1754885 = 329041) (by norm_num)
theorem B1165117 : Blo 690315 1165117 := bbase (se 3 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 1165117 = 436919) (by norm_num)
theorem B1558349 : Blo 690315 1558349 := bbase (se 3 (by rfl) ⟨292190, by rfl⟩ : syracuseStep 1558349 = 584381) (by norm_num)
theorem B739189 : Blo 690315 739189 := bbase (se 5 (by rfl) ⟨34649, by rfl⟩ : syracuseStep 739189 = 69299) (by norm_num)
theorem B1165205 : Blo 690315 1165205 := bbase (se 6 (by rfl) ⟨27309, by rfl⟩ : syracuseStep 1165205 = 54619) (by norm_num)
theorem B1558421 : Blo 690315 1558421 := bbase (se 6 (by rfl) ⟨36525, by rfl⟩ : syracuseStep 1558421 = 73051) (by norm_num)
theorem B1558493 : Blo 690315 1558493 := bbase (se 3 (by rfl) ⟨292217, by rfl⟩ : syracuseStep 1558493 = 584435) (by norm_num)
theorem B1165333 : Blo 690315 1165333 := bbase (se 6 (by rfl) ⟨27312, by rfl⟩ : syracuseStep 1165333 = 54625) (by norm_num)
theorem B1558565 : Blo 690315 1558565 := bbase (se 4 (by rfl) ⟨146115, by rfl⟩ : syracuseStep 1558565 = 292231) (by norm_num)
theorem B739373 : Blo 690315 739373 := bbase (se 3 (by rfl) ⟨138632, by rfl⟩ : syracuseStep 739373 = 277265) (by norm_num)
theorem B5916725 : Blo 690315 5916725 := bbase (se 5 (by rfl) ⟨277346, by rfl⟩ : syracuseStep 5916725 = 554693) (by norm_num)
theorem B1755229 : Blo 690315 1755229 := bbase (se 3 (by rfl) ⟨329105, by rfl⟩ : syracuseStep 1755229 = 658211) (by norm_num)
theorem B1165421 : Blo 690315 1165421 := bbase (se 3 (by rfl) ⟨218516, by rfl⟩ : syracuseStep 1165421 = 437033) (by norm_num)
theorem B1558637 : Blo 690315 1558637 := bbase (se 3 (by rfl) ⟨292244, by rfl⟩ : syracuseStep 1558637 = 584489) (by norm_num)
theorem B1558709 : Blo 690315 1558709 := bbase (se 5 (by rfl) ⟨73064, by rfl⟩ : syracuseStep 1558709 = 146129) (by norm_num)
theorem B1755341 : Blo 690315 1755341 := bbase (se 3 (by rfl) ⟨329126, by rfl⟩ : syracuseStep 1755341 = 658253) (by norm_num)
theorem B1165549 : Blo 690315 1165549 := bbase (se 3 (by rfl) ⟨218540, by rfl⟩ : syracuseStep 1165549 = 437081) (by norm_num)
theorem B1558781 : Blo 690315 1558781 := bbase (se 3 (by rfl) ⟨292271, by rfl⟩ : syracuseStep 1558781 = 584543) (by norm_num)
theorem B1165637 : Blo 690315 1165637 := bbase (se 4 (by rfl) ⟨109278, by rfl⟩ : syracuseStep 1165637 = 218557) (by norm_num)
theorem B1558853 : Blo 690315 1558853 := bbase (se 4 (by rfl) ⟨146142, by rfl⟩ : syracuseStep 1558853 = 292285) (by norm_num)
theorem B1558925 : Blo 690315 1558925 := bbase (se 3 (by rfl) ⟨292298, by rfl⟩ : syracuseStep 1558925 = 584597) (by norm_num)
theorem B1755533 : Blo 690315 1755533 := bbase (se 3 (by rfl) ⟨329162, by rfl⟩ : syracuseStep 1755533 = 658325) (by norm_num)
theorem B1165765 : Blo 690315 1165765 := bbase (se 4 (by rfl) ⟨109290, by rfl⟩ : syracuseStep 1165765 = 218581) (by norm_num)
theorem B1558997 : Blo 690315 1558997 := bbase (se 7 (by rfl) ⟨18269, by rfl⟩ : syracuseStep 1558997 = 36539) (by norm_num)
theorem B1165853 : Blo 690315 1165853 := bbase (se 3 (by rfl) ⟨218597, by rfl⟩ : syracuseStep 1165853 = 437195) (by norm_num)
theorem B1559069 : Blo 690315 1559069 := bbase (se 3 (by rfl) ⟨292325, by rfl⟩ : syracuseStep 1559069 = 584651) (by norm_num)
theorem B1559141 : Blo 690315 1559141 := bbase (se 4 (by rfl) ⟨146169, by rfl⟩ : syracuseStep 1559141 = 292339) (by norm_num)
theorem B1165981 : Blo 690315 1165981 := bbase (se 3 (by rfl) ⟨218621, by rfl⟩ : syracuseStep 1165981 = 437243) (by norm_num)
theorem B1559213 : Blo 690315 1559213 := bbase (se 3 (by rfl) ⟨292352, by rfl⟩ : syracuseStep 1559213 = 584705) (by norm_num)
theorem B1755877 : Blo 690315 1755877 := bbase (se 4 (by rfl) ⟨164613, by rfl⟩ : syracuseStep 1755877 = 329227) (by norm_num)
theorem B1166069 : Blo 690315 1166069 := bbase (se 5 (by rfl) ⟨54659, by rfl⟩ : syracuseStep 1166069 = 109319) (by norm_num)
theorem B1559285 : Blo 690315 1559285 := bbase (se 5 (by rfl) ⟨73091, by rfl⟩ : syracuseStep 1559285 = 146183) (by norm_num)
theorem B740125 : Blo 690315 740125 := bbase (se 3 (by rfl) ⟨138773, by rfl⟩ : syracuseStep 740125 = 277547) (by norm_num)
theorem B1559357 : Blo 690315 1559357 := bbase (se 3 (by rfl) ⟨292379, by rfl⟩ : syracuseStep 1559357 = 584759) (by norm_num)
theorem B1755989 : Blo 690315 1755989 := bbase (se 9 (by rfl) ⟨5144, by rfl⟩ : syracuseStep 1755989 = 10289) (by norm_num)
theorem B740197 : Blo 690315 740197 := bbase (se 4 (by rfl) ⟨69393, by rfl⟩ : syracuseStep 740197 = 138787) (by norm_num)
theorem B1166197 : Blo 690315 1166197 := bbase (se 5 (by rfl) ⟨54665, by rfl⟩ : syracuseStep 1166197 = 109331) (by norm_num)
theorem B1559429 : Blo 690315 1559429 := bbase (se 4 (by rfl) ⟨146196, by rfl⟩ : syracuseStep 1559429 = 292393) (by norm_num)
theorem B1264565 : Blo 690315 1264565 := bbase (se 5 (by rfl) ⟨59276, by rfl⟩ : syracuseStep 1264565 = 118553) (by norm_num)
theorem B1166285 : Blo 690315 1166285 := bbase (se 3 (by rfl) ⟨218678, by rfl⟩ : syracuseStep 1166285 = 437357) (by norm_num)
theorem B1559501 : Blo 690315 1559501 := bbase (se 3 (by rfl) ⟨292406, by rfl⟩ : syracuseStep 1559501 = 584813) (by norm_num)
theorem B1559573 : Blo 690315 1559573 := bbase (se 6 (by rfl) ⟨36552, by rfl⟩ : syracuseStep 1559573 = 73105) (by norm_num)
theorem B1756181 : Blo 690315 1756181 := bbase (se 6 (by rfl) ⟨41160, by rfl⟩ : syracuseStep 1756181 = 82321) (by norm_num)
theorem B740377 : Blo 690315 740377 := bbase (se 2 (by rfl) ⟨277641, by rfl⟩ : syracuseStep 740377 = 555283) (by norm_num)
theorem B1166413 : Blo 690315 1166413 := bbase (se 3 (by rfl) ⟨218702, by rfl⟩ : syracuseStep 1166413 = 437405) (by norm_num)
theorem B1559645 : Blo 690315 1559645 := bbase (se 3 (by rfl) ⟨292433, by rfl⟩ : syracuseStep 1559645 = 584867) (by norm_num)
theorem B1166501 : Blo 690315 1166501 := bbase (se 4 (by rfl) ⟨109359, by rfl⟩ : syracuseStep 1166501 = 218719) (by norm_num)
theorem B1559717 : Blo 690315 1559717 := bbase (se 4 (by rfl) ⟨146223, by rfl⟩ : syracuseStep 1559717 = 292447) (by norm_num)
theorem B1035485 : Blo 690315 1035485 := bbase (se 3 (by rfl) ⟨194153, by rfl⟩ : syracuseStep 1035485 = 388307) (by norm_num)
theorem B1559789 : Blo 690315 1559789 := bbase (se 3 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 1559789 = 584921) (by norm_num)
theorem B1035509 : Blo 690315 1035509 := bbase (se 5 (by rfl) ⟨48539, by rfl⟩ : syracuseStep 1035509 = 97079) (by norm_num)
theorem B1035533 : Blo 690315 1035533 := bbase (se 3 (by rfl) ⟨194162, by rfl⟩ : syracuseStep 1035533 = 388325) (by norm_num)
theorem B1035557 : Blo 690315 1035557 := bbase (se 4 (by rfl) ⟨97083, by rfl⟩ : syracuseStep 1035557 = 194167) (by norm_num)
theorem B1166629 : Blo 690315 1166629 := bbase (se 4 (by rfl) ⟨109371, by rfl⟩ : syracuseStep 1166629 = 218743) (by norm_num)
theorem B3329333 : Blo 690315 3329333 := bbase (se 5 (by rfl) ⟨156062, by rfl⟩ : syracuseStep 3329333 = 312125) (by norm_num)
theorem B1559861 : Blo 690315 1559861 := bbase (se 5 (by rfl) ⟨73118, by rfl⟩ : syracuseStep 1559861 = 146237) (by norm_num)
theorem B1035581 : Blo 690315 1035581 := bbase (se 3 (by rfl) ⟨194171, by rfl⟩ : syracuseStep 1035581 = 388343) (by norm_num)
theorem B1035605 : Blo 690315 1035605 := bbase (se 11 (by rfl) ⟨758, by rfl⟩ : syracuseStep 1035605 = 1517) (by norm_num)
theorem B1035629 : Blo 690315 1035629 := bbase (se 3 (by rfl) ⟨194180, by rfl⟩ : syracuseStep 1035629 = 388361) (by norm_num)
theorem B1756525 : Blo 690315 1756525 := bbase (se 3 (by rfl) ⟨329348, by rfl⟩ : syracuseStep 1756525 = 658697) (by norm_num)
theorem B1166717 : Blo 690315 1166717 := bbase (se 3 (by rfl) ⟨218759, by rfl⟩ : syracuseStep 1166717 = 437519) (by norm_num)
theorem B1559933 : Blo 690315 1559933 := bbase (se 3 (by rfl) ⟨292487, by rfl⟩ : syracuseStep 1559933 = 584975) (by norm_num)
theorem B1035653 : Blo 690315 1035653 := bbase (se 4 (by rfl) ⟨97092, by rfl⟩ : syracuseStep 1035653 = 194185) (by norm_num)
theorem B1035677 : Blo 690315 1035677 := bbase (se 3 (by rfl) ⟨194189, by rfl⟩ : syracuseStep 1035677 = 388379) (by norm_num)
theorem B1035701 : Blo 690315 1035701 := bbase (se 5 (by rfl) ⟨48548, by rfl⟩ : syracuseStep 1035701 = 97097) (by norm_num)
theorem B1560005 : Blo 690315 1560005 := bbase (se 4 (by rfl) ⟨146250, by rfl⟩ : syracuseStep 1560005 = 292501) (by norm_num)
theorem B1068485 : Blo 690315 1068485 := bbase (se 4 (by rfl) ⟨100170, by rfl⟩ : syracuseStep 1068485 = 200341) (by norm_num)
theorem B1035725 : Blo 690315 1035725 := bbase (se 3 (by rfl) ⟨194198, by rfl⟩ : syracuseStep 1035725 = 388397) (by norm_num)
theorem B740821 : Blo 690315 740821 := bbase (se 7 (by rfl) ⟨8681, by rfl⟩ : syracuseStep 740821 = 17363) (by norm_num)
theorem B1756637 : Blo 690315 1756637 := bbase (se 3 (by rfl) ⟨329369, by rfl⟩ : syracuseStep 1756637 = 658739) (by norm_num)
theorem B1035749 : Blo 690315 1035749 := bbase (se 4 (by rfl) ⟨97101, by rfl⟩ : syracuseStep 1035749 = 194203) (by norm_num)
theorem B1035773 : Blo 690315 1035773 := bbase (se 3 (by rfl) ⟨194207, by rfl⟩ : syracuseStep 1035773 = 388415) (by norm_num)
theorem B1166845 : Blo 690315 1166845 := bbase (se 3 (by rfl) ⟨218783, by rfl⟩ : syracuseStep 1166845 = 437567) (by norm_num)
theorem B1560077 : Blo 690315 1560077 := bbase (se 3 (by rfl) ⟨292514, by rfl⟩ : syracuseStep 1560077 = 585029) (by norm_num)
theorem B1035797 : Blo 690315 1035797 := bbase (se 6 (by rfl) ⟨24276, by rfl⟩ : syracuseStep 1035797 = 48553) (by norm_num)
theorem B1035821 : Blo 690315 1035821 := bbase (se 3 (by rfl) ⟨194216, by rfl⟩ : syracuseStep 1035821 = 388433) (by norm_num)
theorem B1035845 : Blo 690315 1035845 := bbase (se 4 (by rfl) ⟨97110, by rfl⟩ : syracuseStep 1035845 = 194221) (by norm_num)
theorem B740945 : Blo 690315 740945 := bbase (se 2 (by rfl) ⟨277854, by rfl⟩ : syracuseStep 740945 = 555709) (by norm_num)
theorem B1166933 : Blo 690315 1166933 := bbase (se 8 (by rfl) ⟨6837, by rfl⟩ : syracuseStep 1166933 = 13675) (by norm_num)
theorem B1560149 : Blo 690315 1560149 := bbase (se 8 (by rfl) ⟨9141, by rfl⟩ : syracuseStep 1560149 = 18283) (by norm_num)
theorem B17780309 : Blo 690315 17780309 := bbase (se 8 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 17780309 = 208363) (by norm_num)
theorem B1035869 : Blo 690315 1035869 := bbase (se 3 (by rfl) ⟨194225, by rfl⟩ : syracuseStep 1035869 = 388451) (by norm_num)
theorem B1035893 : Blo 690315 1035893 := bbase (se 5 (by rfl) ⟨48557, by rfl⟩ : syracuseStep 1035893 = 97115) (by norm_num)
theorem B1035917 : Blo 690315 1035917 := bbase (se 3 (by rfl) ⟨194234, by rfl⟩ : syracuseStep 1035917 = 388469) (by norm_num)
theorem B9981589 : Blo 690315 9981589 := bbase (se 6 (by rfl) ⟨233943, by rfl⟩ : syracuseStep 9981589 = 467887) (by norm_num)
theorem B1068701 : Blo 690315 1068701 := bbase (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) (by norm_num)
theorem B1560221 : Blo 690315 1560221 := bbase (se 3 (by rfl) ⟨292541, by rfl⟩ : syracuseStep 1560221 = 585083) (by norm_num)
theorem B1756829 : Blo 690315 1756829 := bbase (se 3 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 1756829 = 658811) (by norm_num)
theorem B1035941 : Blo 690315 1035941 := bbase (se 4 (by rfl) ⟨97119, by rfl⟩ : syracuseStep 1035941 = 194239) (by norm_num)
theorem B1035965 : Blo 690315 1035965 := bbase (se 3 (by rfl) ⟨194243, by rfl⟩ : syracuseStep 1035965 = 388487) (by norm_num)
theorem B1035989 : Blo 690315 1035989 := bbase (se 7 (by rfl) ⟨12140, by rfl⟩ : syracuseStep 1035989 = 24281) (by norm_num)
theorem B1167061 : Blo 690315 1167061 := bbase (se 7 (by rfl) ⟨13676, by rfl⟩ : syracuseStep 1167061 = 27353) (by norm_num)
theorem B1560293 : Blo 690315 1560293 := bbase (se 4 (by rfl) ⟨146277, by rfl⟩ : syracuseStep 1560293 = 292555) (by norm_num)
theorem B1036013 : Blo 690315 1036013 := bbase (se 3 (by rfl) ⟨194252, by rfl⟩ : syracuseStep 1036013 = 388505) (by norm_num)
theorem B1036037 : Blo 690315 1036037 := bbase (se 4 (by rfl) ⟨97128, by rfl⟩ : syracuseStep 1036037 = 194257) (by norm_num)
theorem B1036061 : Blo 690315 1036061 := bbase (se 3 (by rfl) ⟨194261, by rfl⟩ : syracuseStep 1036061 = 388523) (by norm_num)
theorem B1167149 : Blo 690315 1167149 := bbase (se 3 (by rfl) ⟨218840, by rfl⟩ : syracuseStep 1167149 = 437681) (by norm_num)
theorem B1560365 : Blo 690315 1560365 := bbase (se 3 (by rfl) ⟨292568, by rfl⟩ : syracuseStep 1560365 = 585137) (by norm_num)
theorem B1036085 : Blo 690315 1036085 := bbase (se 5 (by rfl) ⟨48566, by rfl⟩ : syracuseStep 1036085 = 97133) (by norm_num)
theorem B1036109 : Blo 690315 1036109 := bbase (se 3 (by rfl) ⟨194270, by rfl⟩ : syracuseStep 1036109 = 388541) (by norm_num)
theorem B741197 : Blo 690315 741197 := bbase (se 3 (by rfl) ⟨138974, by rfl⟩ : syracuseStep 741197 = 277949) (by norm_num)
theorem B1036133 : Blo 690315 1036133 := bbase (se 4 (by rfl) ⟨97137, by rfl⟩ : syracuseStep 1036133 = 194275) (by norm_num)
theorem B1560437 : Blo 690315 1560437 := bbase (se 5 (by rfl) ⟨73145, by rfl⟩ : syracuseStep 1560437 = 146291) (by norm_num)
theorem B1036157 : Blo 690315 1036157 := bbase (se 3 (by rfl) ⟨194279, by rfl⟩ : syracuseStep 1036157 = 388559) (by norm_num)
theorem B1036181 : Blo 690315 1036181 := bbase (se 6 (by rfl) ⟨24285, by rfl⟩ : syracuseStep 1036181 = 48571) (by norm_num)
theorem B1036205 : Blo 690315 1036205 := bbase (se 3 (by rfl) ⟨194288, by rfl⟩ : syracuseStep 1036205 = 388577) (by norm_num)
theorem B1167277 : Blo 690315 1167277 := bbase (se 3 (by rfl) ⟨218864, by rfl⟩ : syracuseStep 1167277 = 437729) (by norm_num)
theorem B1560509 : Blo 690315 1560509 := bbase (se 3 (by rfl) ⟨292595, by rfl⟩ : syracuseStep 1560509 = 585191) (by norm_num)
theorem B1036229 : Blo 690315 1036229 := bbase (se 4 (by rfl) ⟨97146, by rfl⟩ : syracuseStep 1036229 = 194293) (by norm_num)
theorem B1036253 : Blo 690315 1036253 := bbase (se 3 (by rfl) ⟨194297, by rfl⟩ : syracuseStep 1036253 = 388595) (by norm_num)
theorem B1036277 : Blo 690315 1036277 := bbase (se 5 (by rfl) ⟨48575, by rfl⟩ : syracuseStep 1036277 = 97151) (by norm_num)
theorem B1757173 : Blo 690315 1757173 := bbase (se 5 (by rfl) ⟨82367, by rfl⟩ : syracuseStep 1757173 = 164735) (by norm_num)
theorem B1167365 : Blo 690315 1167365 := bbase (se 4 (by rfl) ⟨109440, by rfl⟩ : syracuseStep 1167365 = 218881) (by norm_num)
theorem B1560581 : Blo 690315 1560581 := bbase (se 4 (by rfl) ⟨146304, by rfl⟩ : syracuseStep 1560581 = 292609) (by norm_num)
theorem B1036301 : Blo 690315 1036301 := bbase (se 3 (by rfl) ⟨194306, by rfl⟩ : syracuseStep 1036301 = 388613) (by norm_num)
theorem B1036325 : Blo 690315 1036325 := bbase (se 4 (by rfl) ⟨97155, by rfl⟩ : syracuseStep 1036325 = 194311) (by norm_num)
theorem B1036349 : Blo 690315 1036349 := bbase (se 3 (by rfl) ⟨194315, by rfl⟩ : syracuseStep 1036349 = 388631) (by norm_num)
theorem B1560653 : Blo 690315 1560653 := bbase (se 3 (by rfl) ⟨292622, by rfl⟩ : syracuseStep 1560653 = 585245) (by norm_num)
theorem B1036373 : Blo 690315 1036373 := bbase (se 8 (by rfl) ⟨6072, by rfl⟩ : syracuseStep 1036373 = 12145) (by norm_num)
theorem B1757285 : Blo 690315 1757285 := bbase (se 4 (by rfl) ⟨164745, by rfl⟩ : syracuseStep 1757285 = 329491) (by norm_num)
theorem B1036397 : Blo 690315 1036397 := bbase (se 3 (by rfl) ⟨194324, by rfl⟩ : syracuseStep 1036397 = 388649) (by norm_num)
theorem B1036421 : Blo 690315 1036421 := bbase (se 4 (by rfl) ⟨97164, by rfl⟩ : syracuseStep 1036421 = 194329) (by norm_num)
theorem B2216069 : Blo 690315 2216069 := bbase (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) (by norm_num)
theorem B1167493 : Blo 690315 1167493 := bbase (se 4 (by rfl) ⟨109452, by rfl⟩ : syracuseStep 1167493 = 218905) (by norm_num)
theorem B1560725 : Blo 690315 1560725 := bbase (se 6 (by rfl) ⟨36579, by rfl⟩ : syracuseStep 1560725 = 73159) (by norm_num)
theorem B1036445 : Blo 690315 1036445 := bbase (se 3 (by rfl) ⟨194333, by rfl⟩ : syracuseStep 1036445 = 388667) (by norm_num)
theorem B1036469 : Blo 690315 1036469 := bbase (se 5 (by rfl) ⟨48584, by rfl⟩ : syracuseStep 1036469 = 97169) (by norm_num)
theorem B1036493 : Blo 690315 1036493 := bbase (se 3 (by rfl) ⟨194342, by rfl⟩ : syracuseStep 1036493 = 388685) (by norm_num)
theorem B1167581 : Blo 690315 1167581 := bbase (se 3 (by rfl) ⟨218921, by rfl⟩ : syracuseStep 1167581 = 437843) (by norm_num)
theorem B1560797 : Blo 690315 1560797 := bbase (se 3 (by rfl) ⟨292649, by rfl⟩ : syracuseStep 1560797 = 585299) (by norm_num)
theorem B1036517 : Blo 690315 1036517 := bbase (se 4 (by rfl) ⟨97173, by rfl⟩ : syracuseStep 1036517 = 194347) (by norm_num)
theorem B1036541 : Blo 690315 1036541 := bbase (se 3 (by rfl) ⟨194351, by rfl⟩ : syracuseStep 1036541 = 388703) (by norm_num)
theorem B1036565 : Blo 690315 1036565 := bbase (se 6 (by rfl) ⟨24294, by rfl⟩ : syracuseStep 1036565 = 48589) (by norm_num)
theorem B1560869 : Blo 690315 1560869 := bbase (se 4 (by rfl) ⟨146331, by rfl⟩ : syracuseStep 1560869 = 292663) (by norm_num)
theorem B1757477 : Blo 690315 1757477 := bbase (se 4 (by rfl) ⟨164763, by rfl⟩ : syracuseStep 1757477 = 329527) (by norm_num)
theorem B1036589 : Blo 690315 1036589 := bbase (se 3 (by rfl) ⟨194360, by rfl⟩ : syracuseStep 1036589 = 388721) (by norm_num)
theorem B1036613 : Blo 690315 1036613 := bbase (se 4 (by rfl) ⟨97182, by rfl⟩ : syracuseStep 1036613 = 194365) (by norm_num)
theorem B1036637 : Blo 690315 1036637 := bbase (se 3 (by rfl) ⟨194369, by rfl⟩ : syracuseStep 1036637 = 388739) (by norm_num)
theorem B1167709 : Blo 690315 1167709 := bbase (se 3 (by rfl) ⟨218945, by rfl⟩ : syracuseStep 1167709 = 437891) (by norm_num)
theorem B1560941 : Blo 690315 1560941 := bbase (se 3 (by rfl) ⟨292676, by rfl⟩ : syracuseStep 1560941 = 585353) (by norm_num)
theorem B1036661 : Blo 690315 1036661 := bbase (se 5 (by rfl) ⟨48593, by rfl⟩ : syracuseStep 1036661 = 97187) (by norm_num)
theorem B1036685 : Blo 690315 1036685 := bbase (se 3 (by rfl) ⟨194378, by rfl⟩ : syracuseStep 1036685 = 388757) (by norm_num)
theorem B1659293 : Blo 690315 1659293 := bbase (se 3 (by rfl) ⟨311117, by rfl⟩ : syracuseStep 1659293 = 622235) (by norm_num)
theorem B1036709 : Blo 690315 1036709 := bbase (se 4 (by rfl) ⟨97191, by rfl⟩ : syracuseStep 1036709 = 194383) (by norm_num)
theorem B1167797 : Blo 690315 1167797 := bbase (se 5 (by rfl) ⟨54740, by rfl⟩ : syracuseStep 1167797 = 109481) (by norm_num)
theorem B1561013 : Blo 690315 1561013 := bbase (se 5 (by rfl) ⟨73172, by rfl⟩ : syracuseStep 1561013 = 146345) (by norm_num)
theorem B1036733 : Blo 690315 1036733 := bbase (se 3 (by rfl) ⟨194387, by rfl⟩ : syracuseStep 1036733 = 388775) (by norm_num)
theorem B1036757 : Blo 690315 1036757 := bbase (se 7 (by rfl) ⟨12149, by rfl⟩ : syracuseStep 1036757 = 24299) (by norm_num)
theorem B1036781 : Blo 690315 1036781 := bbase (se 3 (by rfl) ⟨194396, by rfl⟩ : syracuseStep 1036781 = 388793) (by norm_num)
theorem B1561085 : Blo 690315 1561085 := bbase (se 3 (by rfl) ⟨292703, by rfl⟩ : syracuseStep 1561085 = 585407) (by norm_num)
theorem B1036805 : Blo 690315 1036805 := bbase (se 4 (by rfl) ⟨97200, by rfl⟩ : syracuseStep 1036805 = 194401) (by norm_num)
theorem B1036829 : Blo 690315 1036829 := bbase (se 3 (by rfl) ⟨194405, by rfl⟩ : syracuseStep 1036829 = 388811) (by norm_num)
theorem B1036853 : Blo 690315 1036853 := bbase (se 5 (by rfl) ⟨48602, by rfl⟩ : syracuseStep 1036853 = 97205) (by norm_num)
theorem B1167925 : Blo 690315 1167925 := bbase (se 5 (by rfl) ⟨54746, by rfl⟩ : syracuseStep 1167925 = 109493) (by norm_num)
theorem B1561157 : Blo 690315 1561157 := bbase (se 4 (by rfl) ⟨146358, by rfl⟩ : syracuseStep 1561157 = 292717) (by norm_num)
theorem B1036877 : Blo 690315 1036877 := bbase (se 3 (by rfl) ⟨194414, by rfl⟩ : syracuseStep 1036877 = 388829) (by norm_num)
theorem B1659485 : Blo 690315 1659485 := bbase (se 3 (by rfl) ⟨311153, by rfl⟩ : syracuseStep 1659485 = 622307) (by norm_num)
theorem B1036901 : Blo 690315 1036901 := bbase (se 4 (by rfl) ⟨97209, by rfl⟩ : syracuseStep 1036901 = 194419) (by norm_num)
theorem B1036925 : Blo 690315 1036925 := bbase (se 3 (by rfl) ⟨194423, by rfl⟩ : syracuseStep 1036925 = 388847) (by norm_num)
theorem B1168013 : Blo 690315 1168013 := bbase (se 3 (by rfl) ⟨219002, by rfl⟩ : syracuseStep 1168013 = 438005) (by norm_num)
theorem B1561229 : Blo 690315 1561229 := bbase (se 3 (by rfl) ⟨292730, by rfl⟩ : syracuseStep 1561229 = 585461) (by norm_num)
theorem B1036949 : Blo 690315 1036949 := bbase (se 6 (by rfl) ⟨24303, by rfl⟩ : syracuseStep 1036949 = 48607) (by norm_num)
theorem B1036973 : Blo 690315 1036973 := bbase (se 3 (by rfl) ⟨194432, by rfl⟩ : syracuseStep 1036973 = 388865) (by norm_num)
theorem B1036997 : Blo 690315 1036997 := bbase (se 4 (by rfl) ⟨97218, by rfl⟩ : syracuseStep 1036997 = 194437) (by norm_num)
theorem B1561301 : Blo 690315 1561301 := bbase (se 7 (by rfl) ⟨18296, by rfl⟩ : syracuseStep 1561301 = 36593) (by norm_num)
theorem B1037021 : Blo 690315 1037021 := bbase (se 3 (by rfl) ⟨194441, by rfl⟩ : syracuseStep 1037021 = 388883) (by norm_num)
theorem B1037045 : Blo 690315 1037045 := bbase (se 5 (by rfl) ⟨48611, by rfl⟩ : syracuseStep 1037045 = 97223) (by norm_num)
theorem B1037069 : Blo 690315 1037069 := bbase (se 3 (by rfl) ⟨194450, by rfl⟩ : syracuseStep 1037069 = 388901) (by norm_num)
theorem B1168141 : Blo 690315 1168141 := bbase (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) (by norm_num)
theorem B1561373 : Blo 690315 1561373 := bbase (se 3 (by rfl) ⟨292757, by rfl⟩ : syracuseStep 1561373 = 585515) (by norm_num)
theorem B1037093 : Blo 690315 1037093 := bbase (se 4 (by rfl) ⟨97227, by rfl⟩ : syracuseStep 1037093 = 194455) (by norm_num)
theorem B1037117 : Blo 690315 1037117 := bbase (se 3 (by rfl) ⟨194459, by rfl⟩ : syracuseStep 1037117 = 388919) (by norm_num)
theorem B1037141 : Blo 690315 1037141 := bbase (se 9 (by rfl) ⟨3038, by rfl⟩ : syracuseStep 1037141 = 6077) (by norm_num)
theorem B1168229 : Blo 690315 1168229 := bbase (se 4 (by rfl) ⟨109521, by rfl⟩ : syracuseStep 1168229 = 219043) (by norm_num)
theorem B1561445 : Blo 690315 1561445 := bbase (se 4 (by rfl) ⟨146385, by rfl⟩ : syracuseStep 1561445 = 292771) (by norm_num)
theorem B1037165 : Blo 690315 1037165 := bbase (se 3 (by rfl) ⟨194468, by rfl⟩ : syracuseStep 1037165 = 388937) (by norm_num)
theorem B1037189 : Blo 690315 1037189 := bbase (se 4 (by rfl) ⟨97236, by rfl⟩ : syracuseStep 1037189 = 194473) (by norm_num)
theorem B1037213 : Blo 690315 1037213 := bbase (se 3 (by rfl) ⟨194477, by rfl⟩ : syracuseStep 1037213 = 388955) (by norm_num)
theorem B1561517 : Blo 690315 1561517 := bbase (se 3 (by rfl) ⟨292784, by rfl⟩ : syracuseStep 1561517 = 585569) (by norm_num)
theorem B1037237 : Blo 690315 1037237 := bbase (se 5 (by rfl) ⟨48620, by rfl⟩ : syracuseStep 1037237 = 97241) (by norm_num)
theorem B1037261 : Blo 690315 1037261 := bbase (se 3 (by rfl) ⟨194486, by rfl⟩ : syracuseStep 1037261 = 388973) (by norm_num)
theorem B1037285 : Blo 690315 1037285 := bbase (se 4 (by rfl) ⟨97245, by rfl⟩ : syracuseStep 1037285 = 194491) (by norm_num)
theorem B1168357 : Blo 690315 1168357 := bbase (se 4 (by rfl) ⟨109533, by rfl⟩ : syracuseStep 1168357 = 219067) (by norm_num)
theorem B1561589 : Blo 690315 1561589 := bbase (se 5 (by rfl) ⟨73199, by rfl⟩ : syracuseStep 1561589 = 146399) (by norm_num)
theorem B1037309 : Blo 690315 1037309 := bbase (se 3 (by rfl) ⟨194495, by rfl⟩ : syracuseStep 1037309 = 388991) (by norm_num)
theorem B1037333 : Blo 690315 1037333 := bbase (se 6 (by rfl) ⟨24312, by rfl⟩ : syracuseStep 1037333 = 48625) (by norm_num)
theorem B2806805 : Blo 690315 2806805 := bbase (se 6 (by rfl) ⟨65784, by rfl⟩ : syracuseStep 2806805 = 131569) (by norm_num)
theorem B1037357 : Blo 690315 1037357 := bbase (se 3 (by rfl) ⟨194504, by rfl⟩ : syracuseStep 1037357 = 389009) (by norm_num)
theorem B1168445 : Blo 690315 1168445 := bbase (se 3 (by rfl) ⟨219083, by rfl⟩ : syracuseStep 1168445 = 438167) (by norm_num)
theorem B1561661 : Blo 690315 1561661 := bbase (se 3 (by rfl) ⟨292811, by rfl⟩ : syracuseStep 1561661 = 585623) (by norm_num)
theorem B1037381 : Blo 690315 1037381 := bbase (se 4 (by rfl) ⟨97254, by rfl⟩ : syracuseStep 1037381 = 194509) (by norm_num)
theorem B1037405 : Blo 690315 1037405 := bbase (se 3 (by rfl) ⟨194513, by rfl⟩ : syracuseStep 1037405 = 389027) (by norm_num)
theorem B1037429 : Blo 690315 1037429 := bbase (se 5 (by rfl) ⟨48629, by rfl⟩ : syracuseStep 1037429 = 97259) (by norm_num)
theorem B1561733 : Blo 690315 1561733 := bbase (se 4 (by rfl) ⟨146412, by rfl⟩ : syracuseStep 1561733 = 292825) (by norm_num)
theorem B1037453 : Blo 690315 1037453 := bbase (se 3 (by rfl) ⟨194522, by rfl⟩ : syracuseStep 1037453 = 389045) (by norm_num)
theorem B1037477 : Blo 690315 1037477 := bbase (se 4 (by rfl) ⟨97263, by rfl⟩ : syracuseStep 1037477 = 194527) (by norm_num)
theorem B1037501 : Blo 690315 1037501 := bbase (se 3 (by rfl) ⟨194531, by rfl⟩ : syracuseStep 1037501 = 389063) (by norm_num)
theorem B1168573 : Blo 690315 1168573 := bbase (se 3 (by rfl) ⟨219107, by rfl⟩ : syracuseStep 1168573 = 438215) (by norm_num)
theorem B1561805 : Blo 690315 1561805 := bbase (se 3 (by rfl) ⟨292838, by rfl⟩ : syracuseStep 1561805 = 585677) (by norm_num)
theorem B1037525 : Blo 690315 1037525 := bbase (se 7 (by rfl) ⟨12158, by rfl⟩ : syracuseStep 1037525 = 24317) (by norm_num)
theorem B1037549 : Blo 690315 1037549 := bbase (se 3 (by rfl) ⟨194540, by rfl⟩ : syracuseStep 1037549 = 389081) (by norm_num)
theorem B1037573 : Blo 690315 1037573 := bbase (se 4 (by rfl) ⟨97272, by rfl⟩ : syracuseStep 1037573 = 194545) (by norm_num)
theorem B1168661 : Blo 690315 1168661 := bbase (se 6 (by rfl) ⟨27390, by rfl⟩ : syracuseStep 1168661 = 54781) (by norm_num)
theorem B1561877 : Blo 690315 1561877 := bbase (se 6 (by rfl) ⟨36606, by rfl⟩ : syracuseStep 1561877 = 73213) (by norm_num)
theorem B873757 : Blo 690315 873757 := bbase (se 3 (by rfl) ⟨163829, by rfl⟩ : syracuseStep 873757 = 327659) (by norm_num)
theorem B1037597 : Blo 690315 1037597 := bbase (se 3 (by rfl) ⟨194549, by rfl⟩ : syracuseStep 1037597 = 389099) (by norm_num)
theorem B1037621 : Blo 690315 1037621 := bbase (se 5 (by rfl) ⟨48638, by rfl⟩ : syracuseStep 1037621 = 97277) (by norm_num)
theorem B1037645 : Blo 690315 1037645 := bbase (se 3 (by rfl) ⟨194558, by rfl⟩ : syracuseStep 1037645 = 389117) (by norm_num)
theorem B3954005 : Blo 690315 3954005 := bbase (se 16 (by rfl) ⟨90, by rfl⟩ : syracuseStep 3954005 = 181) (by norm_num)
theorem B1561949 : Blo 690315 1561949 := bbase (se 3 (by rfl) ⟨292865, by rfl⟩ : syracuseStep 1561949 = 585731) (by norm_num)
theorem B1037669 : Blo 690315 1037669 := bbase (se 4 (by rfl) ⟨97281, by rfl⟩ : syracuseStep 1037669 = 194563) (by norm_num)
theorem B1037693 : Blo 690315 1037693 := bbase (se 3 (by rfl) ⟨194567, by rfl⟩ : syracuseStep 1037693 = 389135) (by norm_num)
theorem B1037717 : Blo 690315 1037717 := bbase (se 6 (by rfl) ⟨24321, by rfl⟩ : syracuseStep 1037717 = 48643) (by norm_num)
theorem B1168789 : Blo 690315 1168789 := bbase (se 6 (by rfl) ⟨27393, by rfl⟩ : syracuseStep 1168789 = 54787) (by norm_num)
theorem B1562021 : Blo 690315 1562021 := bbase (se 4 (by rfl) ⟨146439, by rfl⟩ : syracuseStep 1562021 = 292879) (by norm_num)
theorem B1037741 : Blo 690315 1037741 := bbase (se 3 (by rfl) ⟨194576, by rfl⟩ : syracuseStep 1037741 = 389153) (by norm_num)
theorem B1037765 : Blo 690315 1037765 := bbase (se 4 (by rfl) ⟨97290, by rfl⟩ : syracuseStep 1037765 = 194581) (by norm_num)
theorem B2217413 : Blo 690315 2217413 := bbase (se 4 (by rfl) ⟨207882, by rfl⟩ : syracuseStep 2217413 = 415765) (by norm_num)
theorem B873929 : Blo 690315 873929 := bbase (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) (by norm_num)
theorem B1037789 : Blo 690315 1037789 := bbase (se 3 (by rfl) ⟨194585, by rfl⟩ : syracuseStep 1037789 = 389171) (by norm_num)
theorem B1168877 : Blo 690315 1168877 := bbase (se 3 (by rfl) ⟨219164, by rfl⟩ : syracuseStep 1168877 = 438329) (by norm_num)
theorem B1562093 : Blo 690315 1562093 := bbase (se 3 (by rfl) ⟨292892, by rfl⟩ : syracuseStep 1562093 = 585785) (by norm_num)
theorem B1037813 : Blo 690315 1037813 := bbase (se 5 (by rfl) ⟨48647, by rfl⟩ : syracuseStep 1037813 = 97295) (by norm_num)
theorem B873985 : Blo 690315 873985 := bbase (se 2 (by rfl) ⟨327744, by rfl⟩ : syracuseStep 873985 = 655489) (by norm_num)
theorem B1037837 : Blo 690315 1037837 := bbase (se 3 (by rfl) ⟨194594, by rfl⟩ : syracuseStep 1037837 = 389189) (by norm_num)
theorem B1037861 : Blo 690315 1037861 := bbase (se 4 (by rfl) ⟨97299, by rfl⟩ : syracuseStep 1037861 = 194599) (by norm_num)
theorem B1562165 : Blo 690315 1562165 := bbase (se 5 (by rfl) ⟨73226, by rfl⟩ : syracuseStep 1562165 = 146453) (by norm_num)
theorem B1037885 : Blo 690315 1037885 := bbase (se 3 (by rfl) ⟨194603, by rfl⟩ : syracuseStep 1037885 = 389207) (by norm_num)
theorem B1037909 : Blo 690315 1037909 := bbase (se 8 (by rfl) ⟨6081, by rfl⟩ : syracuseStep 1037909 = 12163) (by norm_num)
theorem B874081 : Blo 690315 874081 := bbase (se 2 (by rfl) ⟨327780, by rfl⟩ : syracuseStep 874081 = 655561) (by norm_num)
theorem B1037933 : Blo 690315 1037933 := bbase (se 3 (by rfl) ⟨194612, by rfl⟩ : syracuseStep 1037933 = 389225) (by norm_num)
theorem B1169005 : Blo 690315 1169005 := bbase (se 3 (by rfl) ⟨219188, by rfl⟩ : syracuseStep 1169005 = 438377) (by norm_num)
theorem B1037957 : Blo 690315 1037957 := bbase (se 4 (by rfl) ⟨97308, by rfl⟩ : syracuseStep 1037957 = 194617) (by norm_num)
theorem B1037981 : Blo 690315 1037981 := bbase (se 3 (by rfl) ⟨194621, by rfl⟩ : syracuseStep 1037981 = 389243) (by norm_num)
theorem B1038005 : Blo 690315 1038005 := bbase (se 5 (by rfl) ⟨48656, by rfl⟩ : syracuseStep 1038005 = 97313) (by norm_num)
theorem B1169093 : Blo 690315 1169093 := bbase (se 4 (by rfl) ⟨109602, by rfl⟩ : syracuseStep 1169093 = 219205) (by norm_num)
theorem B1038029 : Blo 690315 1038029 := bbase (se 3 (by rfl) ⟨194630, by rfl⟩ : syracuseStep 1038029 = 389261) (by norm_num)
theorem B1038053 : Blo 690315 1038053 := bbase (se 4 (by rfl) ⟨97317, by rfl⟩ : syracuseStep 1038053 = 194635) (by norm_num)
theorem B1038077 : Blo 690315 1038077 := bbase (se 3 (by rfl) ⟨194639, by rfl⟩ : syracuseStep 1038077 = 389279) (by norm_num)
theorem B874253 : Blo 690315 874253 := bbase (se 3 (by rfl) ⟨163922, by rfl⟩ : syracuseStep 874253 = 327845) (by norm_num)
theorem B1038101 : Blo 690315 1038101 := bbase (se 6 (by rfl) ⟨24330, by rfl⟩ : syracuseStep 1038101 = 48661) (by norm_num)
theorem B1038125 : Blo 690315 1038125 := bbase (se 3 (by rfl) ⟨194648, by rfl⟩ : syracuseStep 1038125 = 389297) (by norm_num)
theorem B874309 : Blo 690315 874309 := bbase (se 4 (by rfl) ⟨81966, by rfl⟩ : syracuseStep 874309 = 163933) (by norm_num)
theorem B1038149 : Blo 690315 1038149 := bbase (se 4 (by rfl) ⟨97326, by rfl⟩ : syracuseStep 1038149 = 194653) (by norm_num)
theorem B1169221 : Blo 690315 1169221 := bbase (se 4 (by rfl) ⟨109614, by rfl⟩ : syracuseStep 1169221 = 219229) (by norm_num)
theorem B1038173 : Blo 690315 1038173 := bbase (se 3 (by rfl) ⟨194657, by rfl⟩ : syracuseStep 1038173 = 389315) (by norm_num)
theorem B3495797 : Blo 690315 3495797 := bbase (se 5 (by rfl) ⟨163865, by rfl⟩ : syracuseStep 3495797 = 327731) (by norm_num)
theorem B1038197 : Blo 690315 1038197 := bbase (se 5 (by rfl) ⟨48665, by rfl⟩ : syracuseStep 1038197 = 97331) (by norm_num)
theorem B1038221 : Blo 690315 1038221 := bbase (se 3 (by rfl) ⟨194666, by rfl⟩ : syracuseStep 1038221 = 389333) (by norm_num)
theorem B1169309 : Blo 690315 1169309 := bbase (se 3 (by rfl) ⟨219245, by rfl⟩ : syracuseStep 1169309 = 438491) (by norm_num)
theorem B874405 : Blo 690315 874405 := bbase (se 4 (by rfl) ⟨81975, by rfl⟩ : syracuseStep 874405 = 163951) (by norm_num)
theorem B1038245 : Blo 690315 1038245 := bbase (se 4 (by rfl) ⟨97335, by rfl⟩ : syracuseStep 1038245 = 194671) (by norm_num)
theorem B1038269 : Blo 690315 1038269 := bbase (se 3 (by rfl) ⟨194675, by rfl⟩ : syracuseStep 1038269 = 389351) (by norm_num)
theorem B1038293 : Blo 690315 1038293 := bbase (se 7 (by rfl) ⟨12167, by rfl⟩ : syracuseStep 1038293 = 24335) (by norm_num)
theorem B1038317 : Blo 690315 1038317 := bbase (se 3 (by rfl) ⟨194684, by rfl⟩ : syracuseStep 1038317 = 389369) (by norm_num)
theorem B1038341 : Blo 690315 1038341 := bbase (se 4 (by rfl) ⟨97344, by rfl⟩ : syracuseStep 1038341 = 194689) (by norm_num)
theorem B3332117 : Blo 690315 3332117 := bbase (se 6 (by rfl) ⟨78096, by rfl⟩ : syracuseStep 3332117 = 156193) (by norm_num)
theorem B1038365 : Blo 690315 1038365 := bbase (se 3 (by rfl) ⟨194693, by rfl⟩ : syracuseStep 1038365 = 389387) (by norm_num)
theorem B1169437 : Blo 690315 1169437 := bbase (se 3 (by rfl) ⟨219269, by rfl⟩ : syracuseStep 1169437 = 438539) (by norm_num)
theorem B1038389 : Blo 690315 1038389 := bbase (se 5 (by rfl) ⟨48674, by rfl⟩ : syracuseStep 1038389 = 97349) (by norm_num)
theorem B1038413 : Blo 690315 1038413 := bbase (se 3 (by rfl) ⟨194702, by rfl⟩ : syracuseStep 1038413 = 389405) (by norm_num)
theorem B874577 : Blo 690315 874577 := bbase (se 2 (by rfl) ⟨327966, by rfl⟩ : syracuseStep 874577 = 655933) (by norm_num)
theorem B1038437 : Blo 690315 1038437 := bbase (se 4 (by rfl) ⟨97353, by rfl⟩ : syracuseStep 1038437 = 194707) (by norm_num)
theorem B1169525 : Blo 690315 1169525 := bbase (se 5 (by rfl) ⟨54821, by rfl⟩ : syracuseStep 1169525 = 109643) (by norm_num)
theorem B1038461 : Blo 690315 1038461 := bbase (se 3 (by rfl) ⟨194711, by rfl⟩ : syracuseStep 1038461 = 389423) (by norm_num)
theorem B874633 : Blo 690315 874633 := bbase (se 2 (by rfl) ⟨327987, by rfl⟩ : syracuseStep 874633 = 655975) (by norm_num)
theorem B1038485 : Blo 690315 1038485 := bbase (se 6 (by rfl) ⟨24339, by rfl⟩ : syracuseStep 1038485 = 48679) (by norm_num)
theorem B841901 : Blo 690315 841901 := bbase (se 3 (by rfl) ⟨157856, by rfl⟩ : syracuseStep 841901 = 315713) (by norm_num)
theorem B1038509 : Blo 690315 1038509 := bbase (se 3 (by rfl) ⟨194720, by rfl⟩ : syracuseStep 1038509 = 389441) (by norm_num)
theorem B1038533 : Blo 690315 1038533 := bbase (se 4 (by rfl) ⟨97362, by rfl⟩ : syracuseStep 1038533 = 194725) (by norm_num)
theorem B1038557 : Blo 690315 1038557 := bbase (se 3 (by rfl) ⟨194729, by rfl⟩ : syracuseStep 1038557 = 389459) (by norm_num)
theorem B874729 : Blo 690315 874729 := bbase (se 2 (by rfl) ⟨328023, by rfl⟩ : syracuseStep 874729 = 656047) (by norm_num)
theorem B1038581 : Blo 690315 1038581 := bbase (se 5 (by rfl) ⟨48683, by rfl⟩ : syracuseStep 1038581 = 97367) (by norm_num)
theorem B1169653 : Blo 690315 1169653 := bbase (se 5 (by rfl) ⟨54827, by rfl⟩ : syracuseStep 1169653 = 109655) (by norm_num)
theorem B1038605 : Blo 690315 1038605 := bbase (se 3 (by rfl) ⟨194738, by rfl⟩ : syracuseStep 1038605 = 389477) (by norm_num)
theorem B1038629 : Blo 690315 1038629 := bbase (se 4 (by rfl) ⟨97371, by rfl⟩ : syracuseStep 1038629 = 194743) (by norm_num)
theorem B1038653 : Blo 690315 1038653 := bbase (se 3 (by rfl) ⟨194747, by rfl⟩ : syracuseStep 1038653 = 389495) (by norm_num)
theorem B1169741 : Blo 690315 1169741 := bbase (se 3 (by rfl) ⟨219326, by rfl⟩ : syracuseStep 1169741 = 438653) (by norm_num)
theorem B1038677 : Blo 690315 1038677 := bbase (se 10 (by rfl) ⟨1521, by rfl⟩ : syracuseStep 1038677 = 3043) (by norm_num)
theorem B1038701 : Blo 690315 1038701 := bbase (se 3 (by rfl) ⟨194756, by rfl⟩ : syracuseStep 1038701 = 389513) (by norm_num)
theorem B1038725 : Blo 690315 1038725 := bbase (se 4 (by rfl) ⟨97380, by rfl⟩ : syracuseStep 1038725 = 194761) (by norm_num)
theorem B874901 : Blo 690315 874901 := bbase (se 6 (by rfl) ⟨20505, by rfl⟩ : syracuseStep 874901 = 41011) (by norm_num)
theorem B776605 : Blo 690315 776605 := bbase (se 3 (by rfl) ⟨145613, by rfl⟩ : syracuseStep 776605 = 291227) (by norm_num)
theorem B1038749 : Blo 690315 1038749 := bbase (se 3 (by rfl) ⟨194765, by rfl⟩ : syracuseStep 1038749 = 389531) (by norm_num)
theorem B1038773 : Blo 690315 1038773 := bbase (se 5 (by rfl) ⟨48692, by rfl⟩ : syracuseStep 1038773 = 97385) (by norm_num)
theorem B776641 : Blo 690315 776641 := bbase (se 2 (by rfl) ⟨291240, by rfl⟩ : syracuseStep 776641 = 582481) (by norm_num)
theorem B874957 : Blo 690315 874957 := bbase (se 3 (by rfl) ⟨164054, by rfl⟩ : syracuseStep 874957 = 328109) (by norm_num)
theorem B1038797 : Blo 690315 1038797 := bbase (se 3 (by rfl) ⟨194774, by rfl⟩ : syracuseStep 1038797 = 389549) (by norm_num)
theorem B1169869 : Blo 690315 1169869 := bbase (se 3 (by rfl) ⟨219350, by rfl⟩ : syracuseStep 1169869 = 438701) (by norm_num)
theorem B776677 : Blo 690315 776677 := bbase (se 4 (by rfl) ⟨72813, by rfl⟩ : syracuseStep 776677 = 145627) (by norm_num)
theorem B1038821 : Blo 690315 1038821 := bbase (se 4 (by rfl) ⟨97389, by rfl⟩ : syracuseStep 1038821 = 194779) (by norm_num)
theorem B1038845 : Blo 690315 1038845 := bbase (se 3 (by rfl) ⟨194783, by rfl⟩ : syracuseStep 1038845 = 389567) (by norm_num)
theorem B776713 : Blo 690315 776713 := bbase (se 2 (by rfl) ⟨291267, by rfl⟩ : syracuseStep 776713 = 582535) (by norm_num)
theorem B1038869 : Blo 690315 1038869 := bbase (se 6 (by rfl) ⟨24348, by rfl⟩ : syracuseStep 1038869 = 48697) (by norm_num)
theorem B1169957 : Blo 690315 1169957 := bbase (se 4 (by rfl) ⟨109683, by rfl⟩ : syracuseStep 1169957 = 219367) (by norm_num)
theorem B776749 : Blo 690315 776749 := bbase (se 3 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 776749 = 291281) (by norm_num)
theorem B875053 : Blo 690315 875053 := bbase (se 3 (by rfl) ⟨164072, by rfl⟩ : syracuseStep 875053 = 328145) (by norm_num)
theorem B1661485 : Blo 690315 1661485 := bbase (se 3 (by rfl) ⟨311528, by rfl⟩ : syracuseStep 1661485 = 623057) (by norm_num)
theorem B1038893 : Blo 690315 1038893 := bbase (se 3 (by rfl) ⟨194792, by rfl⟩ : syracuseStep 1038893 = 389585) (by norm_num)
theorem B1038917 : Blo 690315 1038917 := bbase (se 4 (by rfl) ⟨97398, by rfl⟩ : syracuseStep 1038917 = 194797) (by norm_num)
theorem B776785 : Blo 690315 776785 := bbase (se 2 (by rfl) ⟨291294, by rfl⟩ : syracuseStep 776785 = 582589) (by norm_num)
theorem B1038941 : Blo 690315 1038941 := bbase (se 3 (by rfl) ⟨194801, by rfl⟩ : syracuseStep 1038941 = 389603) (by norm_num)
theorem B776821 : Blo 690315 776821 := bbase (se 5 (by rfl) ⟨36413, by rfl⟩ : syracuseStep 776821 = 72827) (by norm_num)
theorem B1038965 : Blo 690315 1038965 := bbase (se 5 (by rfl) ⟨48701, by rfl⟩ : syracuseStep 1038965 = 97403) (by norm_num)
theorem B1038989 : Blo 690315 1038989 := bbase (se 3 (by rfl) ⟨194810, by rfl⟩ : syracuseStep 1038989 = 389621) (by norm_num)
theorem B776857 : Blo 690315 776857 := bbase (se 2 (by rfl) ⟨291321, by rfl⟩ : syracuseStep 776857 = 582643) (by norm_num)
theorem B1039013 : Blo 690315 1039013 := bbase (se 4 (by rfl) ⟨97407, by rfl⟩ : syracuseStep 1039013 = 194815) (by norm_num)
theorem B1170085 : Blo 690315 1170085 := bbase (se 4 (by rfl) ⟨109695, by rfl⟩ : syracuseStep 1170085 = 219391) (by norm_num)
theorem B776893 : Blo 690315 776893 := bbase (se 3 (by rfl) ⟨145667, by rfl⟩ : syracuseStep 776893 = 291335) (by norm_num)
theorem B1039037 : Blo 690315 1039037 := bbase (se 3 (by rfl) ⟨194819, by rfl⟩ : syracuseStep 1039037 = 389639) (by norm_num)
theorem B1039061 : Blo 690315 1039061 := bbase (se 7 (by rfl) ⟨12176, by rfl⟩ : syracuseStep 1039061 = 24353) (by norm_num)
theorem B875225 : Blo 690315 875225 := bbase (se 2 (by rfl) ⟨328209, by rfl⟩ : syracuseStep 875225 = 656419) (by norm_num)
theorem B776929 : Blo 690315 776929 := bbase (se 2 (by rfl) ⟨291348, by rfl⟩ : syracuseStep 776929 = 582697) (by norm_num)
theorem B1039085 : Blo 690315 1039085 := bbase (se 3 (by rfl) ⟨194828, by rfl⟩ : syracuseStep 1039085 = 389657) (by norm_num)
theorem B1170173 : Blo 690315 1170173 := bbase (se 3 (by rfl) ⟨219407, by rfl⟩ : syracuseStep 1170173 = 438815) (by norm_num)
theorem B776965 : Blo 690315 776965 := bbase (se 4 (by rfl) ⟨72840, by rfl⟩ : syracuseStep 776965 = 145681) (by norm_num)
theorem B1039109 : Blo 690315 1039109 := bbase (se 4 (by rfl) ⟨97416, by rfl⟩ : syracuseStep 1039109 = 194833) (by norm_num)
theorem B875281 : Blo 690315 875281 := bbase (se 2 (by rfl) ⟨328230, by rfl⟩ : syracuseStep 875281 = 656461) (by norm_num)
theorem B1039133 : Blo 690315 1039133 := bbase (se 3 (by rfl) ⟨194837, by rfl⟩ : syracuseStep 1039133 = 389675) (by norm_num)
theorem B1334045 : Blo 690315 1334045 := bbase (se 3 (by rfl) ⟨250133, by rfl⟩ : syracuseStep 1334045 = 500267) (by norm_num)
theorem B777001 : Blo 690315 777001 := bbase (se 2 (by rfl) ⟨291375, by rfl⟩ : syracuseStep 777001 = 582751) (by norm_num)
theorem B1039157 : Blo 690315 1039157 := bbase (se 5 (by rfl) ⟨48710, by rfl⟩ : syracuseStep 1039157 = 97421) (by norm_num)
theorem B777037 : Blo 690315 777037 := bbase (se 3 (by rfl) ⟨145694, by rfl⟩ : syracuseStep 777037 = 291389) (by norm_num)
theorem B1039181 : Blo 690315 1039181 := bbase (se 3 (by rfl) ⟨194846, by rfl⟩ : syracuseStep 1039181 = 389693) (by norm_num)
theorem B1039205 : Blo 690315 1039205 := bbase (se 4 (by rfl) ⟨97425, by rfl⟩ : syracuseStep 1039205 = 194851) (by norm_num)
theorem B777073 : Blo 690315 777073 := bbase (se 2 (by rfl) ⟨291402, by rfl⟩ : syracuseStep 777073 = 582805) (by norm_num)
theorem B875377 : Blo 690315 875377 := bbase (se 2 (by rfl) ⟨328266, by rfl⟩ : syracuseStep 875377 = 656533) (by norm_num)
theorem B1039229 : Blo 690315 1039229 := bbase (se 3 (by rfl) ⟨194855, by rfl⟩ : syracuseStep 1039229 = 389711) (by norm_num)
theorem B1170301 : Blo 690315 1170301 := bbase (se 3 (by rfl) ⟨219431, by rfl⟩ : syracuseStep 1170301 = 438863) (by norm_num)
theorem B777109 : Blo 690315 777109 := bbase (se 6 (by rfl) ⟨18213, by rfl⟩ : syracuseStep 777109 = 36427) (by norm_num)
theorem B1039253 : Blo 690315 1039253 := bbase (se 6 (by rfl) ⟨24357, by rfl⟩ : syracuseStep 1039253 = 48715) (by norm_num)
theorem B1039277 : Blo 690315 1039277 := bbase (se 3 (by rfl) ⟨194864, by rfl⟩ : syracuseStep 1039277 = 389729) (by norm_num)
theorem B777145 : Blo 690315 777145 := bbase (se 2 (by rfl) ⟨291429, by rfl⟩ : syracuseStep 777145 = 582859) (by norm_num)
theorem B1039301 : Blo 690315 1039301 := bbase (se 4 (by rfl) ⟨97434, by rfl⟩ : syracuseStep 1039301 = 194869) (by norm_num)
theorem B1170389 : Blo 690315 1170389 := bbase (se 7 (by rfl) ⟨13715, by rfl⟩ : syracuseStep 1170389 = 27431) (by norm_num)
theorem B777181 : Blo 690315 777181 := bbase (se 3 (by rfl) ⟨145721, by rfl⟩ : syracuseStep 777181 = 291443) (by norm_num)
theorem B1039325 : Blo 690315 1039325 := bbase (se 3 (by rfl) ⟨194873, by rfl⟩ : syracuseStep 1039325 = 389747) (by norm_num)
theorem B1039349 : Blo 690315 1039349 := bbase (se 5 (by rfl) ⟨48719, by rfl⟩ : syracuseStep 1039349 = 97439) (by norm_num)
theorem B777217 : Blo 690315 777217 := bbase (se 2 (by rfl) ⟨291456, by rfl⟩ : syracuseStep 777217 = 582913) (by norm_num)
theorem B1039373 : Blo 690315 1039373 := bbase (se 3 (by rfl) ⟨194882, by rfl⟩ : syracuseStep 1039373 = 389765) (by norm_num)
theorem B875549 : Blo 690315 875549 := bbase (se 3 (by rfl) ⟨164165, by rfl⟩ : syracuseStep 875549 = 328331) (by norm_num)
theorem B777253 : Blo 690315 777253 := bbase (se 4 (by rfl) ⟨72867, by rfl⟩ : syracuseStep 777253 = 145735) (by norm_num)
theorem B1039397 : Blo 690315 1039397 := bbase (se 4 (by rfl) ⟨97443, by rfl⟩ : syracuseStep 1039397 = 194887) (by norm_num)
theorem B1039421 : Blo 690315 1039421 := bbase (se 3 (by rfl) ⟨194891, by rfl⟩ : syracuseStep 1039421 = 389783) (by norm_num)
theorem B777289 : Blo 690315 777289 := bbase (se 2 (by rfl) ⟨291483, by rfl⟩ : syracuseStep 777289 = 582967) (by norm_num)
theorem B875605 : Blo 690315 875605 := bbase (se 8 (by rfl) ⟨5130, by rfl⟩ : syracuseStep 875605 = 10261) (by norm_num)
theorem B1039445 : Blo 690315 1039445 := bbase (se 8 (by rfl) ⟨6090, by rfl⟩ : syracuseStep 1039445 = 12181) (by norm_num)
theorem B1170517 : Blo 690315 1170517 := bbase (se 8 (by rfl) ⟨6858, by rfl⟩ : syracuseStep 1170517 = 13717) (by norm_num)
theorem B777325 : Blo 690315 777325 := bbase (se 3 (by rfl) ⟨145748, by rfl⟩ : syracuseStep 777325 = 291497) (by norm_num)
theorem B1662061 : Blo 690315 1662061 := bbase (se 3 (by rfl) ⟨311636, by rfl⟩ : syracuseStep 1662061 = 623273) (by norm_num)
theorem B1039469 : Blo 690315 1039469 := bbase (se 3 (by rfl) ⟨194900, by rfl⟩ : syracuseStep 1039469 = 389801) (by norm_num)
theorem B3497093 : Blo 690315 3497093 := bbase (se 4 (by rfl) ⟨327852, by rfl⟩ : syracuseStep 3497093 = 655705) (by norm_num)
theorem B1039493 : Blo 690315 1039493 := bbase (se 4 (by rfl) ⟨97452, by rfl⟩ : syracuseStep 1039493 = 194905) (by norm_num)
theorem B777361 : Blo 690315 777361 := bbase (se 2 (by rfl) ⟨291510, by rfl⟩ : syracuseStep 777361 = 583021) (by norm_num)
theorem B2841749 : Blo 690315 2841749 := bbase (se 6 (by rfl) ⟨66603, by rfl⟩ : syracuseStep 2841749 = 133207) (by norm_num)
theorem B1039517 : Blo 690315 1039517 := bbase (se 3 (by rfl) ⟨194909, by rfl⟩ : syracuseStep 1039517 = 389819) (by norm_num)
theorem B1170605 : Blo 690315 1170605 := bbase (se 3 (by rfl) ⟨219488, by rfl⟩ : syracuseStep 1170605 = 438977) (by norm_num)
theorem B777397 : Blo 690315 777397 := bbase (se 5 (by rfl) ⟨36440, by rfl⟩ : syracuseStep 777397 = 72881) (by norm_num)
theorem B875701 : Blo 690315 875701 := bbase (se 5 (by rfl) ⟨41048, by rfl⟩ : syracuseStep 875701 = 82097) (by norm_num)
theorem B1039541 : Blo 690315 1039541 := bbase (se 5 (by rfl) ⟨48728, by rfl⟩ : syracuseStep 1039541 = 97457) (by norm_num)
theorem B1039565 : Blo 690315 1039565 := bbase (se 3 (by rfl) ⟨194918, by rfl⟩ : syracuseStep 1039565 = 389837) (by norm_num)
theorem B777433 : Blo 690315 777433 := bbase (se 2 (by rfl) ⟨291537, by rfl⟩ : syracuseStep 777433 = 583075) (by norm_num)
theorem B1039589 : Blo 690315 1039589 := bbase (se 4 (by rfl) ⟨97461, by rfl⟩ : syracuseStep 1039589 = 194923) (by norm_num)
theorem B777469 : Blo 690315 777469 := bbase (se 3 (by rfl) ⟨145775, by rfl⟩ : syracuseStep 777469 = 291551) (by norm_num)
theorem B1039613 : Blo 690315 1039613 := bbase (se 3 (by rfl) ⟨194927, by rfl⟩ : syracuseStep 1039613 = 389855) (by norm_num)
theorem B1039637 : Blo 690315 1039637 := bbase (se 6 (by rfl) ⟨24366, by rfl⟩ : syracuseStep 1039637 = 48733) (by norm_num)
theorem B777505 : Blo 690315 777505 := bbase (se 2 (by rfl) ⟨291564, by rfl⟩ : syracuseStep 777505 = 583129) (by norm_num)
theorem B1039661 : Blo 690315 1039661 := bbase (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) (by norm_num)
theorem B1170733 : Blo 690315 1170733 := bbase (se 3 (by rfl) ⟨219512, by rfl⟩ : syracuseStep 1170733 = 439025) (by norm_num)
theorem B777541 : Blo 690315 777541 := bbase (se 4 (by rfl) ⟨72894, by rfl⟩ : syracuseStep 777541 = 145789) (by norm_num)
theorem B1039685 : Blo 690315 1039685 := bbase (se 4 (by rfl) ⟨97470, by rfl⟩ : syracuseStep 1039685 = 194941) (by norm_num)
theorem B1039709 : Blo 690315 1039709 := bbase (se 3 (by rfl) ⟨194945, by rfl⟩ : syracuseStep 1039709 = 389891) (by norm_num)
theorem B875873 : Blo 690315 875873 := bbase (se 2 (by rfl) ⟨328452, by rfl⟩ : syracuseStep 875873 = 656905) (by norm_num)
theorem B777577 : Blo 690315 777577 := bbase (se 2 (by rfl) ⟨291591, by rfl⟩ : syracuseStep 777577 = 583183) (by norm_num)
theorem B1039733 : Blo 690315 1039733 := bbase (se 5 (by rfl) ⟨48737, by rfl⟩ : syracuseStep 1039733 = 97475) (by norm_num)
theorem B1170821 : Blo 690315 1170821 := bbase (se 4 (by rfl) ⟨109764, by rfl⟩ : syracuseStep 1170821 = 219529) (by norm_num)
theorem B777613 : Blo 690315 777613 := bbase (se 3 (by rfl) ⟨145802, by rfl⟩ : syracuseStep 777613 = 291605) (by norm_num)
theorem B1039757 : Blo 690315 1039757 := bbase (se 3 (by rfl) ⟨194954, by rfl⟩ : syracuseStep 1039757 = 389909) (by norm_num)
theorem B2219413 : Blo 690315 2219413 := bbase (se 6 (by rfl) ⟨52017, by rfl⟩ : syracuseStep 2219413 = 104035) (by norm_num)
theorem B875929 : Blo 690315 875929 := bbase (se 2 (by rfl) ⟨328473, by rfl⟩ : syracuseStep 875929 = 656947) (by norm_num)
theorem B1039781 : Blo 690315 1039781 := bbase (se 4 (by rfl) ⟨97479, by rfl⟩ : syracuseStep 1039781 = 194959) (by norm_num)
theorem B777649 : Blo 690315 777649 := bbase (se 2 (by rfl) ⟨291618, by rfl⟩ : syracuseStep 777649 = 583237) (by norm_num)
theorem B1662389 : Blo 690315 1662389 := bbase (se 5 (by rfl) ⟨77924, by rfl⟩ : syracuseStep 1662389 = 155849) (by norm_num)
theorem B1039805 : Blo 690315 1039805 := bbase (se 3 (by rfl) ⟨194963, by rfl⟩ : syracuseStep 1039805 = 389927) (by norm_num)
theorem B777685 : Blo 690315 777685 := bbase (se 7 (by rfl) ⟨9113, by rfl⟩ : syracuseStep 777685 = 18227) (by norm_num)
theorem B1039829 : Blo 690315 1039829 := bbase (se 7 (by rfl) ⟨12185, by rfl⟩ : syracuseStep 1039829 = 24371) (by norm_num)
theorem B1662445 : Blo 690315 1662445 := bbase (se 3 (by rfl) ⟨311708, by rfl⟩ : syracuseStep 1662445 = 623417) (by norm_num)
theorem B1039853 : Blo 690315 1039853 := bbase (se 3 (by rfl) ⟨194972, by rfl⟩ : syracuseStep 1039853 = 389945) (by norm_num)
theorem B777721 : Blo 690315 777721 := bbase (se 2 (by rfl) ⟨291645, by rfl⟩ : syracuseStep 777721 = 583291) (by norm_num)
theorem B876025 : Blo 690315 876025 := bbase (se 2 (by rfl) ⟨328509, by rfl⟩ : syracuseStep 876025 = 657019) (by norm_num)
theorem B1039877 : Blo 690315 1039877 := bbase (se 4 (by rfl) ⟨97488, by rfl⟩ : syracuseStep 1039877 = 194977) (by norm_num)
theorem B1170949 : Blo 690315 1170949 := bbase (se 4 (by rfl) ⟨109776, by rfl⟩ : syracuseStep 1170949 = 219553) (by norm_num)
theorem B777757 : Blo 690315 777757 := bbase (se 3 (by rfl) ⟨145829, by rfl⟩ : syracuseStep 777757 = 291659) (by norm_num)
theorem B1039901 : Blo 690315 1039901 := bbase (se 3 (by rfl) ⟨194981, by rfl⟩ : syracuseStep 1039901 = 389963) (by norm_num)
theorem B1039925 : Blo 690315 1039925 := bbase (se 5 (by rfl) ⟨48746, by rfl⟩ : syracuseStep 1039925 = 97493) (by norm_num)
theorem B1334845 : Blo 690315 1334845 := bbase (se 3 (by rfl) ⟨250283, by rfl⟩ : syracuseStep 1334845 = 500567) (by norm_num)
theorem B777793 : Blo 690315 777793 := bbase (se 2 (by rfl) ⟨291672, by rfl⟩ : syracuseStep 777793 = 583345) (by norm_num)
theorem B1039949 : Blo 690315 1039949 := bbase (se 3 (by rfl) ⟨194990, by rfl⟩ : syracuseStep 1039949 = 389981) (by norm_num)
theorem B1171037 : Blo 690315 1171037 := bbase (se 3 (by rfl) ⟨219569, by rfl⟩ : syracuseStep 1171037 = 439139) (by norm_num)
theorem B3595877 : Blo 690315 3595877 := bbase (se 4 (by rfl) ⟨337113, by rfl⟩ : syracuseStep 3595877 = 674227) (by norm_num)
theorem B777829 : Blo 690315 777829 := bbase (se 4 (by rfl) ⟨72921, by rfl⟩ : syracuseStep 777829 = 145843) (by norm_num)
theorem B1039973 : Blo 690315 1039973 := bbase (se 4 (by rfl) ⟨97497, by rfl⟩ : syracuseStep 1039973 = 194995) (by norm_num)
theorem B1039997 : Blo 690315 1039997 := bbase (se 3 (by rfl) ⟨194999, by rfl⟩ : syracuseStep 1039997 = 389999) (by norm_num)
theorem B777865 : Blo 690315 777865 := bbase (se 2 (by rfl) ⟨291699, by rfl⟩ : syracuseStep 777865 = 583399) (by norm_num)
theorem B1040021 : Blo 690315 1040021 := bbase (se 6 (by rfl) ⟨24375, by rfl⟩ : syracuseStep 1040021 = 48751) (by norm_num)
theorem B876197 : Blo 690315 876197 := bbase (se 4 (by rfl) ⟨82143, by rfl⟩ : syracuseStep 876197 = 164287) (by norm_num)
theorem B777901 : Blo 690315 777901 := bbase (se 3 (by rfl) ⟨145856, by rfl⟩ : syracuseStep 777901 = 291713) (by norm_num)
theorem B1040045 : Blo 690315 1040045 := bbase (se 3 (by rfl) ⟨195008, by rfl⟩ : syracuseStep 1040045 = 390017) (by norm_num)
theorem B1040069 : Blo 690315 1040069 := bbase (se 4 (by rfl) ⟨97506, by rfl⟩ : syracuseStep 1040069 = 195013) (by norm_num)
theorem B777937 : Blo 690315 777937 := bbase (se 2 (by rfl) ⟨291726, by rfl⟩ : syracuseStep 777937 = 583453) (by norm_num)
theorem B1662677 : Blo 690315 1662677 := bbase (se 7 (by rfl) ⟨19484, by rfl⟩ : syracuseStep 1662677 = 38969) (by norm_num)
theorem B876253 : Blo 690315 876253 := bbase (se 3 (by rfl) ⟨164297, by rfl⟩ : syracuseStep 876253 = 328595) (by norm_num)
theorem B1040093 : Blo 690315 1040093 := bbase (se 3 (by rfl) ⟨195017, by rfl⟩ : syracuseStep 1040093 = 390035) (by norm_num)
theorem B1171165 : Blo 690315 1171165 := bbase (se 3 (by rfl) ⟨219593, by rfl⟩ : syracuseStep 1171165 = 439187) (by norm_num)
theorem B777973 : Blo 690315 777973 := bbase (se 5 (by rfl) ⟨36467, by rfl⟩ : syracuseStep 777973 = 72935) (by norm_num)
theorem B1040117 : Blo 690315 1040117 := bbase (se 5 (by rfl) ⟨48755, by rfl⟩ : syracuseStep 1040117 = 97511) (by norm_num)
theorem B1040141 : Blo 690315 1040141 := bbase (se 3 (by rfl) ⟨195026, by rfl⟩ : syracuseStep 1040141 = 390053) (by norm_num)
theorem B778009 : Blo 690315 778009 := bbase (se 2 (by rfl) ⟨291753, by rfl⟩ : syracuseStep 778009 = 583507) (by norm_num)
theorem B1040165 : Blo 690315 1040165 := bbase (se 4 (by rfl) ⟨97515, by rfl⟩ : syracuseStep 1040165 = 195031) (by norm_num)
theorem B1171253 : Blo 690315 1171253 := bbase (se 5 (by rfl) ⟨54902, by rfl⟩ : syracuseStep 1171253 = 109805) (by norm_num)
theorem B778045 : Blo 690315 778045 := bbase (se 3 (by rfl) ⟨145883, by rfl⟩ : syracuseStep 778045 = 291767) (by norm_num)
theorem B876349 : Blo 690315 876349 := bbase (se 3 (by rfl) ⟨164315, by rfl⟩ : syracuseStep 876349 = 328631) (by norm_num)
theorem B1040189 : Blo 690315 1040189 := bbase (se 3 (by rfl) ⟨195035, by rfl⟩ : syracuseStep 1040189 = 390071) (by norm_num)
theorem B1892165 : Blo 690315 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B1040213 : Blo 690315 1040213 := bbase (se 9 (by rfl) ⟨3047, by rfl⟩ : syracuseStep 1040213 = 6095) (by norm_num)
theorem B778081 : Blo 690315 778081 := bbase (se 2 (by rfl) ⟨291780, by rfl⟩ : syracuseStep 778081 = 583561) (by norm_num)
theorem B1040237 : Blo 690315 1040237 := bbase (se 3 (by rfl) ⟨195044, by rfl⟩ : syracuseStep 1040237 = 390089) (by norm_num)
theorem B778117 : Blo 690315 778117 := bbase (se 4 (by rfl) ⟨72948, by rfl⟩ : syracuseStep 778117 = 145897) (by norm_num)
theorem B1040261 : Blo 690315 1040261 := bbase (se 4 (by rfl) ⟨97524, by rfl⟩ : syracuseStep 1040261 = 195049) (by norm_num)
theorem B1662869 : Blo 690315 1662869 := bbase (se 6 (by rfl) ⟨38973, by rfl⟩ : syracuseStep 1662869 = 77947) (by norm_num)
theorem B1040285 : Blo 690315 1040285 := bbase (se 3 (by rfl) ⟨195053, by rfl⟩ : syracuseStep 1040285 = 390107) (by norm_num)
theorem B778153 : Blo 690315 778153 := bbase (se 2 (by rfl) ⟨291807, by rfl⟩ : syracuseStep 778153 = 583615) (by norm_num)
theorem B1040309 : Blo 690315 1040309 := bbase (se 5 (by rfl) ⟨48764, by rfl⟩ : syracuseStep 1040309 = 97529) (by norm_num)
theorem B1171381 : Blo 690315 1171381 := bbase (se 5 (by rfl) ⟨54908, by rfl⟩ : syracuseStep 1171381 = 109817) (by norm_num)
theorem B778189 : Blo 690315 778189 := bbase (se 3 (by rfl) ⟨145910, by rfl⟩ : syracuseStep 778189 = 291821) (by norm_num)
theorem B1040333 : Blo 690315 1040333 := bbase (se 3 (by rfl) ⟨195062, by rfl⟩ : syracuseStep 1040333 = 390125) (by norm_num)
theorem B843733 : Blo 690315 843733 := bbase (se 7 (by rfl) ⟨9887, by rfl⟩ : syracuseStep 843733 = 19775) (by norm_num)
theorem B1040357 : Blo 690315 1040357 := bbase (se 4 (by rfl) ⟨97533, by rfl⟩ : syracuseStep 1040357 = 195067) (by norm_num)
theorem B876521 : Blo 690315 876521 := bbase (se 2 (by rfl) ⟨328695, by rfl⟩ : syracuseStep 876521 = 657391) (by norm_num)
theorem B1105901 : Blo 690315 1105901 := bbase (se 3 (by rfl) ⟨207356, by rfl⟩ : syracuseStep 1105901 = 414713) (by norm_num)
theorem B778225 : Blo 690315 778225 := bbase (se 2 (by rfl) ⟨291834, by rfl⟩ : syracuseStep 778225 = 583669) (by norm_num)
theorem B1040381 : Blo 690315 1040381 := bbase (se 3 (by rfl) ⟨195071, by rfl⟩ : syracuseStep 1040381 = 390143) (by norm_num)
theorem B1171469 : Blo 690315 1171469 := bbase (se 3 (by rfl) ⟨219650, by rfl⟩ : syracuseStep 1171469 = 439301) (by norm_num)
theorem B778261 : Blo 690315 778261 := bbase (se 6 (by rfl) ⟨18240, by rfl⟩ : syracuseStep 778261 = 36481) (by norm_num)
theorem B1040405 : Blo 690315 1040405 := bbase (se 6 (by rfl) ⟨24384, by rfl⟩ : syracuseStep 1040405 = 48769) (by norm_num)
theorem B876577 : Blo 690315 876577 := bbase (se 2 (by rfl) ⟨328716, by rfl⟩ : syracuseStep 876577 = 657433) (by norm_num)
theorem B1040429 : Blo 690315 1040429 := bbase (se 3 (by rfl) ⟨195080, by rfl⟩ : syracuseStep 1040429 = 390161) (by norm_num)
theorem B778297 : Blo 690315 778297 := bbase (se 2 (by rfl) ⟨291861, by rfl⟩ : syracuseStep 778297 = 583723) (by norm_num)
theorem B1040453 : Blo 690315 1040453 := bbase (se 4 (by rfl) ⟨97542, by rfl⟩ : syracuseStep 1040453 = 195085) (by norm_num)
theorem B778333 : Blo 690315 778333 := bbase (se 3 (by rfl) ⟨145937, by rfl⟩ : syracuseStep 778333 = 291875) (by norm_num)
theorem B1040477 : Blo 690315 1040477 := bbase (se 3 (by rfl) ⟨195089, by rfl⟩ : syracuseStep 1040477 = 390179) (by norm_num)
theorem B1040501 : Blo 690315 1040501 := bbase (se 5 (by rfl) ⟨48773, by rfl⟩ : syracuseStep 1040501 = 97547) (by norm_num)
theorem B778369 : Blo 690315 778369 := bbase (se 2 (by rfl) ⟨291888, by rfl⟩ : syracuseStep 778369 = 583777) (by norm_num)
theorem B876673 : Blo 690315 876673 := bbase (se 2 (by rfl) ⟨328752, by rfl⟩ : syracuseStep 876673 = 657505) (by norm_num)
theorem B1040525 : Blo 690315 1040525 := bbase (se 3 (by rfl) ⟨195098, by rfl⟩ : syracuseStep 1040525 = 390197) (by norm_num)
theorem B1171597 : Blo 690315 1171597 := bbase (se 3 (by rfl) ⟨219674, by rfl⟩ : syracuseStep 1171597 = 439349) (by norm_num)
theorem B778405 : Blo 690315 778405 := bbase (se 4 (by rfl) ⟨72975, by rfl⟩ : syracuseStep 778405 = 145951) (by norm_num)
theorem B1040549 : Blo 690315 1040549 := bbase (se 4 (by rfl) ⟨97551, by rfl⟩ : syracuseStep 1040549 = 195103) (by norm_num)
theorem B1040573 : Blo 690315 1040573 := bbase (se 3 (by rfl) ⟨195107, by rfl⟩ : syracuseStep 1040573 = 390215) (by norm_num)
theorem B778441 : Blo 690315 778441 := bbase (se 2 (by rfl) ⟨291915, by rfl⟩ : syracuseStep 778441 = 583831) (by norm_num)
theorem B1040597 : Blo 690315 1040597 := bbase (se 7 (by rfl) ⟨12194, by rfl⟩ : syracuseStep 1040597 = 24389) (by norm_num)
theorem B778477 : Blo 690315 778477 := bbase (se 3 (by rfl) ⟨145964, by rfl⟩ : syracuseStep 778477 = 291929) (by norm_num)
theorem B1040621 : Blo 690315 1040621 := bbase (se 3 (by rfl) ⟨195116, by rfl⟩ : syracuseStep 1040621 = 390233) (by norm_num)
theorem B1040645 : Blo 690315 1040645 := bbase (se 4 (by rfl) ⟨97560, by rfl⟩ : syracuseStep 1040645 = 195121) (by norm_num)
theorem B778513 : Blo 690315 778513 := bbase (se 2 (by rfl) ⟨291942, by rfl⟩ : syracuseStep 778513 = 583885) (by norm_num)
theorem B1040669 : Blo 690315 1040669 := bbase (se 3 (by rfl) ⟨195125, by rfl⟩ : syracuseStep 1040669 = 390251) (by norm_num)
theorem B876845 : Blo 690315 876845 := bbase (se 3 (by rfl) ⟨164408, by rfl⟩ : syracuseStep 876845 = 328817) (by norm_num)
theorem B778549 : Blo 690315 778549 := bbase (se 5 (by rfl) ⟨36494, by rfl⟩ : syracuseStep 778549 = 72989) (by norm_num)
theorem B1040693 : Blo 690315 1040693 := bbase (se 5 (by rfl) ⟨48782, by rfl⟩ : syracuseStep 1040693 = 97565) (by norm_num)
theorem B1040717 : Blo 690315 1040717 := bbase (se 3 (by rfl) ⟨195134, by rfl⟩ : syracuseStep 1040717 = 390269) (by norm_num)
theorem B1597781 : Blo 690315 1597781 := bbase (se 10 (by rfl) ⟨2340, by rfl⟩ : syracuseStep 1597781 = 4681) (by norm_num)
theorem B7889237 : Blo 690315 7889237 := bbase (se 10 (by rfl) ⟨11556, by rfl⟩ : syracuseStep 7889237 = 23113) (by norm_num)
theorem B778585 : Blo 690315 778585 := bbase (se 2 (by rfl) ⟨291969, by rfl⟩ : syracuseStep 778585 = 583939) (by norm_num)
theorem B876901 : Blo 690315 876901 := bbase (se 4 (by rfl) ⟨82209, by rfl⟩ : syracuseStep 876901 = 164419) (by norm_num)
theorem B1040741 : Blo 690315 1040741 := bbase (se 4 (by rfl) ⟨97569, by rfl⟩ : syracuseStep 1040741 = 195139) (by norm_num)
theorem B778621 : Blo 690315 778621 := bbase (se 3 (by rfl) ⟨145991, by rfl⟩ : syracuseStep 778621 = 291983) (by norm_num)
theorem B1040765 : Blo 690315 1040765 := bbase (se 3 (by rfl) ⟨195143, by rfl⟩ : syracuseStep 1040765 = 390287) (by norm_num)
theorem B1401229 : Blo 690315 1401229 := bbase (se 3 (by rfl) ⟨262730, by rfl⟩ : syracuseStep 1401229 = 525461) (by norm_num)
theorem B3498389 : Blo 690315 3498389 := bbase (se 6 (by rfl) ⟨81993, by rfl⟩ : syracuseStep 3498389 = 163987) (by norm_num)
theorem B1040789 : Blo 690315 1040789 := bbase (se 6 (by rfl) ⟨24393, by rfl⟩ : syracuseStep 1040789 = 48787) (by norm_num)
theorem B778657 : Blo 690315 778657 := bbase (se 2 (by rfl) ⟨291996, by rfl⟩ : syracuseStep 778657 = 583993) (by norm_num)
theorem B1040813 : Blo 690315 1040813 := bbase (se 3 (by rfl) ⟨195152, by rfl⟩ : syracuseStep 1040813 = 390305) (by norm_num)
theorem B778693 : Blo 690315 778693 := bbase (se 4 (by rfl) ⟨73002, by rfl⟩ : syracuseStep 778693 = 146005) (by norm_num)
theorem B876997 : Blo 690315 876997 := bbase (se 4 (by rfl) ⟨82218, by rfl⟩ : syracuseStep 876997 = 164437) (by norm_num)
theorem B1040837 : Blo 690315 1040837 := bbase (se 4 (by rfl) ⟨97578, by rfl⟩ : syracuseStep 1040837 = 195157) (by norm_num)
theorem B1040861 : Blo 690315 1040861 := bbase (se 3 (by rfl) ⟨195161, by rfl⟩ : syracuseStep 1040861 = 390323) (by norm_num)
theorem B778729 : Blo 690315 778729 := bbase (se 2 (by rfl) ⟨292023, by rfl⟩ : syracuseStep 778729 = 584047) (by norm_num)
theorem B1040885 : Blo 690315 1040885 := bbase (se 5 (by rfl) ⟨48791, by rfl⟩ : syracuseStep 1040885 = 97583) (by norm_num)
theorem B778765 : Blo 690315 778765 := bbase (se 3 (by rfl) ⟨146018, by rfl⟩ : syracuseStep 778765 = 292037) (by norm_num)
theorem B1040909 : Blo 690315 1040909 := bbase (se 3 (by rfl) ⟨195170, by rfl⟩ : syracuseStep 1040909 = 390341) (by norm_num)
theorem B1040933 : Blo 690315 1040933 := bbase (se 4 (by rfl) ⟨97587, by rfl⟩ : syracuseStep 1040933 = 195175) (by norm_num)
theorem B778801 : Blo 690315 778801 := bbase (se 2 (by rfl) ⟨292050, by rfl⟩ : syracuseStep 778801 = 584101) (by norm_num)
theorem B1040957 : Blo 690315 1040957 := bbase (se 3 (by rfl) ⟨195179, by rfl⟩ : syracuseStep 1040957 = 390359) (by norm_num)
theorem B844357 : Blo 690315 844357 := bbase (se 4 (by rfl) ⟨79158, by rfl⟩ : syracuseStep 844357 = 158317) (by norm_num)
theorem B778837 : Blo 690315 778837 := bbase (se 8 (by rfl) ⟨4563, by rfl⟩ : syracuseStep 778837 = 9127) (by norm_num)
theorem B1040981 : Blo 690315 1040981 := bbase (se 8 (by rfl) ⟨6099, by rfl⟩ : syracuseStep 1040981 = 12199) (by norm_num)
theorem B1892965 : Blo 690315 1892965 := bbase (se 4 (by rfl) ⟨177465, by rfl⟩ : syracuseStep 1892965 = 354931) (by norm_num)
theorem B1041005 : Blo 690315 1041005 := bbase (se 3 (by rfl) ⟨195188, by rfl⟩ : syracuseStep 1041005 = 390377) (by norm_num)
theorem B877169 : Blo 690315 877169 := bbase (se 2 (by rfl) ⟨328938, by rfl⟩ : syracuseStep 877169 = 657877) (by norm_num)
theorem B778873 : Blo 690315 778873 := bbase (se 2 (by rfl) ⟨292077, by rfl⟩ : syracuseStep 778873 = 584155) (by norm_num)
theorem B1041029 : Blo 690315 1041029 := bbase (se 4 (by rfl) ⟨97596, by rfl⟩ : syracuseStep 1041029 = 195193) (by norm_num)
theorem B778909 : Blo 690315 778909 := bbase (se 3 (by rfl) ⟨146045, by rfl⟩ : syracuseStep 778909 = 292091) (by norm_num)
theorem B1041053 : Blo 690315 1041053 := bbase (se 3 (by rfl) ⟨195197, by rfl⟩ : syracuseStep 1041053 = 390395) (by norm_num)
theorem B877225 : Blo 690315 877225 := bbase (se 2 (by rfl) ⟨328959, by rfl⟩ : syracuseStep 877225 = 657919) (by norm_num)
theorem B1106605 : Blo 690315 1106605 := bbase (se 3 (by rfl) ⟨207488, by rfl⟩ : syracuseStep 1106605 = 414977) (by norm_num)
theorem B1041077 : Blo 690315 1041077 := bbase (se 5 (by rfl) ⟨48800, by rfl⟩ : syracuseStep 1041077 = 97601) (by norm_num)
theorem B778945 : Blo 690315 778945 := bbase (se 2 (by rfl) ⟨292104, by rfl⟩ : syracuseStep 778945 = 584209) (by norm_num)
theorem B1041101 : Blo 690315 1041101 := bbase (se 3 (by rfl) ⟨195206, by rfl⟩ : syracuseStep 1041101 = 390413) (by norm_num)
theorem B778981 : Blo 690315 778981 := bbase (se 4 (by rfl) ⟨73029, by rfl⟩ : syracuseStep 778981 = 146059) (by norm_num)
theorem B1041125 : Blo 690315 1041125 := bbase (se 4 (by rfl) ⟨97605, by rfl⟩ : syracuseStep 1041125 = 195211) (by norm_num)
theorem B1041149 : Blo 690315 1041149 := bbase (se 3 (by rfl) ⟨195215, by rfl⟩ : syracuseStep 1041149 = 390431) (by norm_num)
theorem B779017 : Blo 690315 779017 := bbase (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) (by norm_num)
theorem B877321 : Blo 690315 877321 := bbase (se 2 (by rfl) ⟨328995, by rfl⟩ : syracuseStep 877321 = 657991) (by norm_num)
theorem B1041173 : Blo 690315 1041173 := bbase (se 6 (by rfl) ⟨24402, by rfl⟩ : syracuseStep 1041173 = 48805) (by norm_num)
theorem B779053 : Blo 690315 779053 := bbase (se 3 (by rfl) ⟨146072, by rfl⟩ : syracuseStep 779053 = 292145) (by norm_num)
theorem B1041197 : Blo 690315 1041197 := bbase (se 3 (by rfl) ⟨195224, by rfl⟩ : syracuseStep 1041197 = 390449) (by norm_num)
theorem B1041221 : Blo 690315 1041221 := bbase (se 4 (by rfl) ⟨97614, by rfl⟩ : syracuseStep 1041221 = 195229) (by norm_num)
theorem B779089 : Blo 690315 779089 := bbase (se 2 (by rfl) ⟨292158, by rfl⟩ : syracuseStep 779089 = 584317) (by norm_num)
theorem B1663829 : Blo 690315 1663829 := bbase (se 9 (by rfl) ⟨4874, by rfl⟩ : syracuseStep 1663829 = 9749) (by norm_num)
theorem B1041245 : Blo 690315 1041245 := bbase (se 3 (by rfl) ⟨195233, by rfl⟩ : syracuseStep 1041245 = 390467) (by norm_num)
theorem B779125 : Blo 690315 779125 := bbase (se 5 (by rfl) ⟨36521, by rfl⟩ : syracuseStep 779125 = 73043) (by norm_num)
theorem B1041269 : Blo 690315 1041269 := bbase (se 5 (by rfl) ⟨48809, by rfl⟩ : syracuseStep 1041269 = 97619) (by norm_num)
theorem B1041293 : Blo 690315 1041293 := bbase (se 3 (by rfl) ⟨195242, by rfl⟩ : syracuseStep 1041293 = 390485) (by norm_num)
theorem B779161 : Blo 690315 779161 := bbase (se 2 (by rfl) ⟨292185, by rfl⟩ : syracuseStep 779161 = 584371) (by norm_num)
theorem B1041317 : Blo 690315 1041317 := bbase (se 4 (by rfl) ⟨97623, by rfl⟩ : syracuseStep 1041317 = 195247) (by norm_num)
theorem B877493 : Blo 690315 877493 := bbase (se 5 (by rfl) ⟨41132, by rfl⟩ : syracuseStep 877493 = 82265) (by norm_num)
theorem B779197 : Blo 690315 779197 := bbase (se 3 (by rfl) ⟨146099, by rfl⟩ : syracuseStep 779197 = 292199) (by norm_num)
theorem B1041341 : Blo 690315 1041341 := bbase (se 3 (by rfl) ⟨195251, by rfl⟩ : syracuseStep 1041341 = 390503) (by norm_num)
theorem B1041365 : Blo 690315 1041365 := bbase (se 7 (by rfl) ⟨12203, by rfl⟩ : syracuseStep 1041365 = 24407) (by norm_num)
theorem B779233 : Blo 690315 779233 := bbase (se 2 (by rfl) ⟨292212, by rfl⟩ : syracuseStep 779233 = 584425) (by norm_num)
theorem B877549 : Blo 690315 877549 := bbase (se 3 (by rfl) ⟨164540, by rfl⟩ : syracuseStep 877549 = 329081) (by norm_num)
theorem B1041389 : Blo 690315 1041389 := bbase (se 3 (by rfl) ⟨195260, by rfl⟩ : syracuseStep 1041389 = 390521) (by norm_num)
theorem B779269 : Blo 690315 779269 := bbase (se 4 (by rfl) ⟨73056, by rfl⟩ : syracuseStep 779269 = 146113) (by norm_num)
theorem B1041413 : Blo 690315 1041413 := bbase (se 4 (by rfl) ⟨97632, by rfl⟩ : syracuseStep 1041413 = 195265) (by norm_num)
theorem B1041437 : Blo 690315 1041437 := bbase (se 3 (by rfl) ⟨195269, by rfl⟩ : syracuseStep 1041437 = 390539) (by norm_num)
theorem B779305 : Blo 690315 779305 := bbase (se 2 (by rfl) ⟨292239, by rfl⟩ : syracuseStep 779305 = 584479) (by norm_num)
theorem B1041461 : Blo 690315 1041461 := bbase (se 5 (by rfl) ⟨48818, by rfl⟩ : syracuseStep 1041461 = 97637) (by norm_num)
theorem B779341 : Blo 690315 779341 := bbase (se 3 (by rfl) ⟨146126, by rfl⟩ : syracuseStep 779341 = 292253) (by norm_num)
theorem B877645 : Blo 690315 877645 := bbase (se 3 (by rfl) ⟨164558, by rfl⟩ : syracuseStep 877645 = 329117) (by norm_num)
theorem B1107029 : Blo 690315 1107029 := bbase (se 8 (by rfl) ⟨6486, by rfl⟩ : syracuseStep 1107029 = 12973) (by norm_num)
theorem B779377 : Blo 690315 779377 := bbase (se 2 (by rfl) ⟨292266, by rfl⟩ : syracuseStep 779377 = 584533) (by norm_num)
theorem B779413 : Blo 690315 779413 := bbase (se 6 (by rfl) ⟨18267, by rfl⟩ : syracuseStep 779413 = 36535) (by norm_num)
theorem B779449 : Blo 690315 779449 := bbase (se 2 (by rfl) ⟨292293, by rfl⟩ : syracuseStep 779449 = 584587) (by norm_num)
theorem B779485 : Blo 690315 779485 := bbase (se 3 (by rfl) ⟨146153, by rfl⟩ : syracuseStep 779485 = 292307) (by norm_num)
theorem B5268725 : Blo 690315 5268725 := bbase (se 5 (by rfl) ⟨246971, by rfl⟩ : syracuseStep 5268725 = 493943) (by norm_num)
theorem B877817 : Blo 690315 877817 := bbase (se 2 (by rfl) ⟨329181, by rfl⟩ : syracuseStep 877817 = 658363) (by norm_num)
theorem B779521 : Blo 690315 779521 := bbase (se 2 (by rfl) ⟨292320, by rfl⟩ : syracuseStep 779521 = 584641) (by norm_num)
theorem B3368213 : Blo 690315 3368213 := bbase (se 6 (by rfl) ⟨78942, by rfl⟩ : syracuseStep 3368213 = 157885) (by norm_num)
theorem B779557 : Blo 690315 779557 := bbase (se 4 (by rfl) ⟨73083, by rfl⟩ : syracuseStep 779557 = 146167) (by norm_num)
theorem B877873 : Blo 690315 877873 := bbase (se 2 (by rfl) ⟨329202, by rfl⟩ : syracuseStep 877873 = 658405) (by norm_num)
theorem B779593 : Blo 690315 779593 := bbase (se 2 (by rfl) ⟨292347, by rfl⟩ : syracuseStep 779593 = 584695) (by norm_num)
theorem B1795421 : Blo 690315 1795421 := bbase (se 3 (by rfl) ⟨336641, by rfl⟩ : syracuseStep 1795421 = 673283) (by norm_num)
theorem B779629 : Blo 690315 779629 := bbase (se 3 (by rfl) ⟨146180, by rfl⟩ : syracuseStep 779629 = 292361) (by norm_num)
theorem B1107317 : Blo 690315 1107317 := bbase (se 5 (by rfl) ⟨51905, by rfl⟩ : syracuseStep 1107317 = 103811) (by norm_num)
theorem B779665 : Blo 690315 779665 := bbase (se 2 (by rfl) ⟨292374, by rfl⟩ : syracuseStep 779665 = 584749) (by norm_num)
theorem B877969 : Blo 690315 877969 := bbase (se 2 (by rfl) ⟨329238, by rfl⟩ : syracuseStep 877969 = 658477) (by norm_num)
theorem B779701 : Blo 690315 779701 := bbase (se 5 (by rfl) ⟨36548, by rfl⟩ : syracuseStep 779701 = 73097) (by norm_num)
theorem B779737 : Blo 690315 779737 := bbase (se 2 (by rfl) ⟨292401, by rfl⟩ : syracuseStep 779737 = 584803) (by norm_num)
theorem B845273 : Blo 690315 845273 := bbase (se 2 (by rfl) ⟨316977, by rfl⟩ : syracuseStep 845273 = 633955) (by norm_num)
theorem B779773 : Blo 690315 779773 := bbase (se 3 (by rfl) ⟨146207, by rfl⟩ : syracuseStep 779773 = 292415) (by norm_num)
theorem B779809 : Blo 690315 779809 := bbase (se 2 (by rfl) ⟨292428, by rfl⟩ : syracuseStep 779809 = 584857) (by norm_num)
theorem B878141 : Blo 690315 878141 := bbase (se 3 (by rfl) ⟨164651, by rfl⟩ : syracuseStep 878141 = 329303) (by norm_num)
theorem B779845 : Blo 690315 779845 := bbase (se 4 (by rfl) ⟨73110, by rfl⟩ : syracuseStep 779845 = 146221) (by norm_num)
theorem B1107541 : Blo 690315 1107541 := bbase (se 8 (by rfl) ⟨6489, by rfl⟩ : syracuseStep 1107541 = 12979) (by norm_num)
theorem B779881 : Blo 690315 779881 := bbase (se 2 (by rfl) ⟨292455, by rfl⟩ : syracuseStep 779881 = 584911) (by norm_num)
theorem B878197 : Blo 690315 878197 := bbase (se 5 (by rfl) ⟨41165, by rfl⟩ : syracuseStep 878197 = 82331) (by norm_num)
theorem B779917 : Blo 690315 779917 := bbase (se 3 (by rfl) ⟨146234, by rfl⟩ : syracuseStep 779917 = 292469) (by norm_num)
theorem B3499685 : Blo 690315 3499685 := bbase (se 4 (by rfl) ⟨328095, by rfl⟩ : syracuseStep 3499685 = 656191) (by norm_num)
theorem B779953 : Blo 690315 779953 := bbase (se 2 (by rfl) ⟨292482, by rfl⟩ : syracuseStep 779953 = 584965) (by norm_num)
theorem B779989 : Blo 690315 779989 := bbase (se 7 (by rfl) ⟨9140, by rfl⟩ : syracuseStep 779989 = 18281) (by norm_num)
theorem B878293 : Blo 690315 878293 := bbase (se 7 (by rfl) ⟨10292, by rfl⟩ : syracuseStep 878293 = 20585) (by norm_num)
theorem B780025 : Blo 690315 780025 := bbase (se 2 (by rfl) ⟨292509, by rfl⟩ : syracuseStep 780025 = 585019) (by norm_num)
theorem B780061 : Blo 690315 780061 := bbase (se 3 (by rfl) ⟨146261, by rfl⟩ : syracuseStep 780061 = 292523) (by norm_num)
theorem B780097 : Blo 690315 780097 := bbase (se 2 (by rfl) ⟨292536, by rfl⟩ : syracuseStep 780097 = 585073) (by norm_num)
theorem B780133 : Blo 690315 780133 := bbase (se 4 (by rfl) ⟨73137, by rfl⟩ : syracuseStep 780133 = 146275) (by norm_num)
theorem B878465 : Blo 690315 878465 := bbase (se 2 (by rfl) ⟨329424, by rfl⟩ : syracuseStep 878465 = 658849) (by norm_num)
theorem B780169 : Blo 690315 780169 := bbase (se 2 (by rfl) ⟨292563, by rfl⟩ : syracuseStep 780169 = 585127) (by norm_num)
theorem B780205 : Blo 690315 780205 := bbase (se 3 (by rfl) ⟨146288, by rfl⟩ : syracuseStep 780205 = 292577) (by norm_num)
theorem B878521 : Blo 690315 878521 := bbase (se 2 (by rfl) ⟨329445, by rfl⟩ : syracuseStep 878521 = 658891) (by norm_num)
theorem B780241 : Blo 690315 780241 := bbase (se 2 (by rfl) ⟨292590, by rfl⟩ : syracuseStep 780241 = 585181) (by norm_num)
theorem B780277 : Blo 690315 780277 := bbase (se 5 (by rfl) ⟨36575, by rfl⟩ : syracuseStep 780277 = 73151) (by norm_num)
theorem B780313 : Blo 690315 780313 := bbase (se 2 (by rfl) ⟨292617, by rfl⟩ : syracuseStep 780313 = 585235) (by norm_num)
theorem B878617 : Blo 690315 878617 := bbase (se 2 (by rfl) ⟨329481, by rfl⟩ : syracuseStep 878617 = 658963) (by norm_num)
theorem B780349 : Blo 690315 780349 := bbase (se 3 (by rfl) ⟨146315, by rfl⟩ : syracuseStep 780349 = 292631) (by norm_num)
theorem B780385 : Blo 690315 780385 := bbase (se 2 (by rfl) ⟨292644, by rfl⟩ : syracuseStep 780385 = 585289) (by norm_num)
theorem B780421 : Blo 690315 780421 := bbase (se 4 (by rfl) ⟨73164, by rfl⟩ : syracuseStep 780421 = 146329) (by norm_num)
theorem B780457 : Blo 690315 780457 := bbase (se 2 (by rfl) ⟨292671, by rfl⟩ : syracuseStep 780457 = 585343) (by norm_num)
theorem B780493 : Blo 690315 780493 := bbase (se 3 (by rfl) ⟨146342, by rfl⟩ : syracuseStep 780493 = 292685) (by norm_num)
theorem B23914709 : Blo 690315 23914709 := bbase (se 7 (by rfl) ⟨280250, by rfl⟩ : syracuseStep 23914709 = 560501) (by norm_num)
theorem B780529 : Blo 690315 780529 := bbase (se 2 (by rfl) ⟨292698, by rfl⟩ : syracuseStep 780529 = 585397) (by norm_num)
theorem B780565 : Blo 690315 780565 := bbase (se 6 (by rfl) ⟨18294, by rfl⟩ : syracuseStep 780565 = 36589) (by norm_num)
theorem B780601 : Blo 690315 780601 := bbase (se 2 (by rfl) ⟨292725, by rfl⟩ : syracuseStep 780601 = 585451) (by norm_num)
theorem B4811093 : Blo 690315 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B780637 : Blo 690315 780637 := bbase (se 3 (by rfl) ⟨146369, by rfl⟩ : syracuseStep 780637 = 292739) (by norm_num)
theorem B2222437 : Blo 690315 2222437 := bbase (se 4 (by rfl) ⟨208353, by rfl⟩ : syracuseStep 2222437 = 416707) (by norm_num)
theorem B780673 : Blo 690315 780673 := bbase (se 2 (by rfl) ⟨292752, by rfl⟩ : syracuseStep 780673 = 585505) (by norm_num)
theorem B747937 : Blo 690315 747937 := bbase (se 2 (by rfl) ⟨280476, by rfl⟩ : syracuseStep 747937 = 560953) (by norm_num)
theorem B780709 : Blo 690315 780709 := bbase (se 4 (by rfl) ⟨73191, by rfl⟩ : syracuseStep 780709 = 146383) (by norm_num)
theorem B780745 : Blo 690315 780745 := bbase (se 2 (by rfl) ⟨292779, by rfl⟩ : syracuseStep 780745 = 585559) (by norm_num)
theorem B780781 : Blo 690315 780781 := bbase (se 3 (by rfl) ⟨146396, by rfl⟩ : syracuseStep 780781 = 292793) (by norm_num)
theorem B780817 : Blo 690315 780817 := bbase (se 2 (by rfl) ⟨292806, by rfl⟩ : syracuseStep 780817 = 585613) (by norm_num)
theorem B780853 : Blo 690315 780853 := bbase (se 5 (by rfl) ⟨36602, by rfl⟩ : syracuseStep 780853 = 73205) (by norm_num)
theorem B780889 : Blo 690315 780889 := bbase (se 2 (by rfl) ⟨292833, by rfl⟩ : syracuseStep 780889 = 585667) (by norm_num)
theorem B780925 : Blo 690315 780925 := bbase (se 3 (by rfl) ⟨146423, by rfl⟩ : syracuseStep 780925 = 292847) (by norm_num)
theorem B780961 : Blo 690315 780961 := bbase (se 2 (by rfl) ⟨292860, by rfl⟩ : syracuseStep 780961 = 585721) (by norm_num)
theorem B1108669 : Blo 690315 1108669 := bbase (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) (by norm_num)
theorem B780997 : Blo 690315 780997 := bbase (se 4 (by rfl) ⟨73218, by rfl⟩ : syracuseStep 780997 = 146437) (by norm_num)
theorem B781033 : Blo 690315 781033 := bbase (se 2 (by rfl) ⟨292887, by rfl⟩ : syracuseStep 781033 = 585775) (by norm_num)
theorem B781069 : Blo 690315 781069 := bbase (se 3 (by rfl) ⟨146450, by rfl⟩ : syracuseStep 781069 = 292901) (by norm_num)
theorem B781105 : Blo 690315 781105 := bbase (se 2 (by rfl) ⟨292914, by rfl⟩ : syracuseStep 781105 = 585829) (by norm_num)
theorem B3500981 : Blo 690315 3500981 := bbase (se 5 (by rfl) ⟨164108, by rfl⟩ : syracuseStep 3500981 = 328217) (by norm_num)
theorem B1109117 : Blo 690315 1109117 := bbase (se 3 (by rfl) ⟨207959, by rfl⟩ : syracuseStep 1109117 = 415919) (by norm_num)
theorem B748721 : Blo 690315 748721 := bbase (se 2 (by rfl) ⟨280770, by rfl⟩ : syracuseStep 748721 = 561541) (by norm_num)
theorem B1666597 : Blo 690315 1666597 := bbase (se 4 (by rfl) ⟨156243, by rfl⟩ : syracuseStep 1666597 = 312487) (by norm_num)
theorem B1666973 : Blo 690315 1666973 := bbase (se 3 (by rfl) ⟨312557, by rfl⟩ : syracuseStep 1666973 = 625115) (by norm_num)
theorem B3502277 : Blo 690315 3502277 := bbase (se 4 (by rfl) ⟨328338, by rfl⟩ : syracuseStep 3502277 = 656677) (by norm_num)
theorem B749821 : Blo 690315 749821 := bbase (se 3 (by rfl) ⟨140591, by rfl⟩ : syracuseStep 749821 = 281183) (by norm_num)
theorem B1667405 : Blo 690315 1667405 := bbase (se 3 (by rfl) ⟨312638, by rfl⟩ : syracuseStep 1667405 = 625277) (by norm_num)
theorem B1110629 : Blo 690315 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B1110757 : Blo 690315 1110757 := bbase (se 4 (by rfl) ⟨104133, by rfl⟩ : syracuseStep 1110757 = 208267) (by norm_num)
theorem B5206837 : Blo 690315 5206837 := bbase (se 5 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 5206837 = 488141) (by norm_num)
theorem B1667981 : Blo 690315 1667981 := bbase (se 3 (by rfl) ⟨312746, by rfl⟩ : syracuseStep 1667981 = 625493) (by norm_num)
theorem B3503573 : Blo 690315 3503573 := bbase (se 7 (by rfl) ⟨41057, by rfl⟩ : syracuseStep 3503573 = 82115) (by norm_num)
theorem B13301333 : Blo 690315 13301333 := bbase (se 8 (by rfl) ⟨77937, by rfl⟩ : syracuseStep 13301333 = 155875) (by norm_num)
theorem B1406549 : Blo 690315 1406549 := bbase (se 8 (by rfl) ⟨8241, by rfl⟩ : syracuseStep 1406549 = 16483) (by norm_num)
theorem B5928821 : Blo 690315 5928821 := bbase (se 5 (by rfl) ⟨277913, by rfl⟩ : syracuseStep 5928821 = 555827) (by norm_num)
theorem B1112141 : Blo 690315 1112141 := bbase (se 3 (by rfl) ⟨208526, by rfl⟩ : syracuseStep 1112141 = 417053) (by norm_num)
theorem B1407181 : Blo 690315 1407181 := bbase (se 3 (by rfl) ⟨263846, by rfl⟩ : syracuseStep 1407181 = 527693) (by norm_num)
theorem B12024085 : Blo 690315 12024085 := bbase (se 6 (by rfl) ⟨281814, by rfl⟩ : syracuseStep 12024085 = 563629) (by norm_num)
theorem B1997237 : Blo 690315 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B948893 : Blo 690315 948893 := bbase (se 3 (by rfl) ⟨177917, by rfl⟩ : syracuseStep 948893 = 355835) (by norm_num)
theorem B3504869 : Blo 690315 3504869 := bbase (se 4 (by rfl) ⟨328581, by rfl⟩ : syracuseStep 3504869 = 657163) (by norm_num)
theorem B1866901 : Blo 690315 1866901 := bbase (se 6 (by rfl) ⟨43755, by rfl⟩ : syracuseStep 1866901 = 87511) (by norm_num)
theorem B1244845 : Blo 690315 1244845 := bbase (se 3 (by rfl) ⟨233408, by rfl⟩ : syracuseStep 1244845 = 466817) (by norm_num)
theorem B3931861 : Blo 690315 3931861 := bbase (se 7 (by rfl) ⟨46076, by rfl⟩ : syracuseStep 3931861 = 92153) (by norm_num)
theorem B1965829 : Blo 690315 1965829 := bbase (se 4 (by rfl) ⟨184296, by rfl⟩ : syracuseStep 1965829 = 368593) (by norm_num)
theorem B1245061 : Blo 690315 1245061 := bbase (se 4 (by rfl) ⟨116724, by rfl⟩ : syracuseStep 1245061 = 233449) (by norm_num)
theorem B1474517 : Blo 690315 1474517 := bbase (se 7 (by rfl) ⟨17279, by rfl⟩ : syracuseStep 1474517 = 34559) (by norm_num)
theorem B3506165 : Blo 690315 3506165 := bbase (se 5 (by rfl) ⟨164351, by rfl⟩ : syracuseStep 3506165 = 328703) (by norm_num)
theorem B2949155 : Blo 690315 2949155 := bstep (se 1 (by rfl) ⟨2211866, by rfl⟩ : syracuseStep 2949155 = 4423733) B4423733
theorem B1867853 : Blo 690315 1867853 := bstep (se 3 (by rfl) ⟨350222, by rfl⟩ : syracuseStep 1867853 = 700445) B700445
theorem B1310833 : Blo 690315 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B11796677 : Blo 690315 11796677 := bstep (se 4 (by rfl) ⟨1105938, by rfl⟩ : syracuseStep 11796677 = 2211877) B2211877
theorem B3932387 : Blo 690315 3932387 := bstep (se 1 (by rfl) ⟨2949290, by rfl⟩ : syracuseStep 3932387 = 5898581) B5898581
theorem B8422069 : Blo 690315 8422069 := bstep (se 5 (by rfl) ⟨394784, by rfl⟩ : syracuseStep 8422069 = 789569) B789569
theorem B2523953 : Blo 690315 2523953 := bstep (se 2 (by rfl) ⟨946482, by rfl⟩ : syracuseStep 2523953 = 1892965) B1892965
theorem B1966979 : Blo 690315 1966979 := bstep (se 1 (by rfl) ⟨1475234, by rfl⟩ : syracuseStep 1966979 = 2950469) B2950469
theorem B1475491 : Blo 690315 1475491 := bstep (se 1 (by rfl) ⟨1106618, by rfl⟩ : syracuseStep 1475491 = 2213237) B2213237
theorem B1868771 : Blo 690315 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B984145 : Blo 690315 984145 := bstep (se 2 (by rfl) ⟨369054, by rfl⟩ : syracuseStep 984145 = 738109) B738109
theorem B2622563 : Blo 690315 2622563 := bstep (se 1 (by rfl) ⟨1966922, by rfl⟩ : syracuseStep 2622563 = 3933845) B3933845
theorem B3507299 : Blo 690315 3507299 := bstep (se 1 (by rfl) ⟨2630474, by rfl⟩ : syracuseStep 3507299 = 5260949) B5260949
theorem B2622577 : Blo 690315 2622577 := bstep (se 2 (by rfl) ⟨983466, by rfl⟩ : syracuseStep 2622577 = 1966933) B1966933
theorem B1311889 : Blo 690315 1311889 := bstep (se 2 (by rfl) ⟨491958, by rfl⟩ : syracuseStep 1311889 = 983917) B983917
theorem B1475747 : Blo 690315 1475747 := bstep (se 1 (by rfl) ⟨1106810, by rfl⟩ : syracuseStep 1475747 = 2213621) B2213621
theorem B984241 : Blo 690315 984241 := bstep (se 2 (by rfl) ⟨369090, by rfl⟩ : syracuseStep 984241 = 738181) B738181
theorem B1246403 : Blo 690315 1246403 := bstep (se 1 (by rfl) ⟨934802, by rfl⟩ : syracuseStep 1246403 = 1869605) B1869605
theorem B1246691 : Blo 690315 1246691 := bstep (se 1 (by rfl) ⟨935018, by rfl⟩ : syracuseStep 1246691 = 1870037) B1870037
theorem B8881649 : Blo 690315 8881649 := bstep (se 2 (by rfl) ⟨3330618, by rfl⟩ : syracuseStep 8881649 = 6661237) B6661237
theorem B1312291 : Blo 690315 1312291 := bstep (se 1 (by rfl) ⟨984218, by rfl⟩ : syracuseStep 1312291 = 1968437) B1968437
theorem B7865909 : Blo 690315 7865909 := bstep (se 5 (by rfl) ⟨368714, by rfl⟩ : syracuseStep 7865909 = 737429) B737429
theorem B4425293 : Blo 690315 4425293 := bstep (se 3 (by rfl) ⟨829742, by rfl⟩ : syracuseStep 4425293 = 1659485) B1659485
theorem B1312337 : Blo 690315 1312337 := bstep (se 2 (by rfl) ⟨492126, by rfl⟩ : syracuseStep 1312337 = 984253) B984253
theorem B36374129 : Blo 690315 36374129 := bstep (se 2 (by rfl) ⟨13640298, by rfl⟩ : syracuseStep 36374129 = 27280597) B27280597
theorem B984737 : Blo 690315 984737 := bstep (se 2 (by rfl) ⟨369276, by rfl⟩ : syracuseStep 984737 = 738553) B738553
theorem B1312625 : Blo 690315 1312625 := bstep (se 2 (by rfl) ⟨492234, by rfl⟩ : syracuseStep 1312625 = 984469) B984469
theorem B3508109 : Blo 690315 3508109 := bstep (se 3 (by rfl) ⟨657770, by rfl⟩ : syracuseStep 3508109 = 1315541) B1315541
theorem B2951153 : Blo 690315 2951153 := bstep (se 2 (by rfl) ⟨1106682, by rfl⟩ : syracuseStep 2951153 = 2213365) B2213365
theorem B3934277 : Blo 690315 3934277 := bstep (se 4 (by rfl) ⟨368838, by rfl⟩ : syracuseStep 3934277 = 737677) B737677
theorem B7473221 : Blo 690315 7473221 := bstep (se 4 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 7473221 = 1401229) B1401229
theorem B1968209 : Blo 690315 1968209 := bstep (se 2 (by rfl) ⟨738078, by rfl⟩ : syracuseStep 1968209 = 1476157) B1476157
theorem B1476721 : Blo 690315 1476721 := bstep (se 2 (by rfl) ⟨553770, by rfl⟩ : syracuseStep 1476721 = 1107541) B1107541
theorem B690323 : Blo 690315 690323 := bstep (se 1 (by rfl) ⟨517742, by rfl⟩ : syracuseStep 690323 = 1035485) B1035485
theorem B690339 : Blo 690315 690339 := bstep (se 1 (by rfl) ⟨517754, by rfl⟩ : syracuseStep 690339 = 1035509) B1035509
theorem B690355 : Blo 690315 690355 := bstep (se 1 (by rfl) ⟨517766, by rfl⟩ : syracuseStep 690355 = 1035533) B1035533
theorem B690371 : Blo 690315 690371 := bstep (se 1 (by rfl) ⟨517778, by rfl⟩ : syracuseStep 690371 = 1035557) B1035557
theorem B690387 : Blo 690315 690387 := bstep (se 1 (by rfl) ⟨517790, by rfl⟩ : syracuseStep 690387 = 1035581) B1035581
theorem B690403 : Blo 690315 690403 := bstep (se 1 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 690403 = 1035605) B1035605
theorem B690419 : Blo 690315 690419 := bstep (se 1 (by rfl) ⟨517814, by rfl⟩ : syracuseStep 690419 = 1035629) B1035629
theorem B690435 : Blo 690315 690435 := bstep (se 1 (by rfl) ⟨517826, by rfl⟩ : syracuseStep 690435 = 1035653) B1035653
theorem B690451 : Blo 690315 690451 := bstep (se 1 (by rfl) ⟨517838, by rfl⟩ : syracuseStep 690451 = 1035677) B1035677
theorem B690467 : Blo 690315 690467 := bstep (se 1 (by rfl) ⟨517850, by rfl⟩ : syracuseStep 690467 = 1035701) B1035701
theorem B690483 : Blo 690315 690483 := bstep (se 1 (by rfl) ⟨517862, by rfl⟩ : syracuseStep 690483 = 1035725) B1035725
theorem B690499 : Blo 690315 690499 := bstep (se 1 (by rfl) ⟨517874, by rfl⟩ : syracuseStep 690499 = 1035749) B1035749
theorem B690515 : Blo 690315 690515 := bstep (se 1 (by rfl) ⟨517886, by rfl⟩ : syracuseStep 690515 = 1035773) B1035773
theorem B690531 : Blo 690315 690531 := bstep (se 1 (by rfl) ⟨517898, by rfl⟩ : syracuseStep 690531 = 1035797) B1035797
theorem B690547 : Blo 690315 690547 := bstep (se 1 (by rfl) ⟨517910, by rfl⟩ : syracuseStep 690547 = 1035821) B1035821
theorem B1050995 : Blo 690315 1050995 := bstep (se 1 (by rfl) ⟨788246, by rfl⟩ : syracuseStep 1050995 = 1576493) B1576493
theorem B690563 : Blo 690315 690563 := bstep (se 1 (by rfl) ⟨517922, by rfl⟩ : syracuseStep 690563 = 1035845) B1035845
theorem B690579 : Blo 690315 690579 := bstep (se 1 (by rfl) ⟨517934, by rfl⟩ : syracuseStep 690579 = 1035869) B1035869
theorem B690595 : Blo 690315 690595 := bstep (se 1 (by rfl) ⟨517946, by rfl⟩ : syracuseStep 690595 = 1035893) B1035893
theorem B690611 : Blo 690315 690611 := bstep (se 1 (by rfl) ⟨517958, by rfl⟩ : syracuseStep 690611 = 1035917) B1035917
theorem B690627 : Blo 690315 690627 := bstep (se 1 (by rfl) ⟨517970, by rfl⟩ : syracuseStep 690627 = 1035941) B1035941
theorem B690643 : Blo 690315 690643 := bstep (se 1 (by rfl) ⟨517982, by rfl⟩ : syracuseStep 690643 = 1035965) B1035965
theorem B690659 : Blo 690315 690659 := bstep (se 1 (by rfl) ⟨517994, by rfl⟩ : syracuseStep 690659 = 1035989) B1035989
theorem B690675 : Blo 690315 690675 := bstep (se 1 (by rfl) ⟨518006, by rfl⟩ : syracuseStep 690675 = 1036013) B1036013
theorem B690691 : Blo 690315 690691 := bstep (se 1 (by rfl) ⟨518018, by rfl⟩ : syracuseStep 690691 = 1036037) B1036037
theorem B985603 : Blo 690315 985603 := bstep (se 1 (by rfl) ⟨739202, by rfl⟩ : syracuseStep 985603 = 1478405) B1478405
theorem B690707 : Blo 690315 690707 := bstep (se 1 (by rfl) ⟨518030, by rfl⟩ : syracuseStep 690707 = 1036061) B1036061
theorem B690723 : Blo 690315 690723 := bstep (se 1 (by rfl) ⟨518042, by rfl⟩ : syracuseStep 690723 = 1036085) B1036085
theorem B2624035 : Blo 690315 2624035 := bstep (se 1 (by rfl) ⟨1968026, by rfl⟩ : syracuseStep 2624035 = 3936053) B3936053
theorem B1870381 : Blo 690315 1870381 := bstep (se 3 (by rfl) ⟨350696, by rfl⟩ : syracuseStep 1870381 = 701393) B701393
theorem B690739 : Blo 690315 690739 := bstep (se 1 (by rfl) ⟨518054, by rfl⟩ : syracuseStep 690739 = 1036109) B1036109
theorem B690755 : Blo 690315 690755 := bstep (se 1 (by rfl) ⟨518066, by rfl⟩ : syracuseStep 690755 = 1036133) B1036133
theorem B1313347 : Blo 690315 1313347 := bstep (se 1 (by rfl) ⟨985010, by rfl⟩ : syracuseStep 1313347 = 1970021) B1970021
theorem B789059 : Blo 690315 789059 := bstep (se 1 (by rfl) ⟨591794, by rfl⟩ : syracuseStep 789059 = 1183589) B1183589
theorem B690771 : Blo 690315 690771 := bstep (se 1 (by rfl) ⟨518078, by rfl⟩ : syracuseStep 690771 = 1036157) B1036157
theorem B690787 : Blo 690315 690787 := bstep (se 1 (by rfl) ⟨518090, by rfl⟩ : syracuseStep 690787 = 1036181) B1036181
theorem B985699 : Blo 690315 985699 := bstep (se 1 (by rfl) ⟨739274, by rfl⟩ : syracuseStep 985699 = 1478549) B1478549
theorem B1247843 : Blo 690315 1247843 := bstep (se 1 (by rfl) ⟨935882, by rfl⟩ : syracuseStep 1247843 = 1871765) B1871765
theorem B690803 : Blo 690315 690803 := bstep (se 1 (by rfl) ⟨518102, by rfl⟩ : syracuseStep 690803 = 1036205) B1036205
theorem B690819 : Blo 690315 690819 := bstep (se 1 (by rfl) ⟨518114, by rfl⟩ : syracuseStep 690819 = 1036229) B1036229
theorem B690835 : Blo 690315 690835 := bstep (se 1 (by rfl) ⟨518126, by rfl⟩ : syracuseStep 690835 = 1036253) B1036253
theorem B690851 : Blo 690315 690851 := bstep (se 1 (by rfl) ⟨518138, by rfl⟩ : syracuseStep 690851 = 1036277) B1036277
theorem B690867 : Blo 690315 690867 := bstep (se 1 (by rfl) ⟨518150, by rfl⟩ : syracuseStep 690867 = 1036301) B1036301
theorem B690883 : Blo 690315 690883 := bstep (se 1 (by rfl) ⟨518162, by rfl⟩ : syracuseStep 690883 = 1036325) B1036325
theorem B690899 : Blo 690315 690899 := bstep (se 1 (by rfl) ⟨518174, by rfl⟩ : syracuseStep 690899 = 1036349) B1036349
theorem B690915 : Blo 690315 690915 := bstep (se 1 (by rfl) ⟨518186, by rfl⟩ : syracuseStep 690915 = 1036373) B1036373
theorem B690931 : Blo 690315 690931 := bstep (se 1 (by rfl) ⟨518198, by rfl⟩ : syracuseStep 690931 = 1036397) B1036397
theorem B690947 : Blo 690315 690947 := bstep (se 1 (by rfl) ⟨518210, by rfl⟩ : syracuseStep 690947 = 1036421) B1036421
theorem B1477379 : Blo 690315 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B690963 : Blo 690315 690963 := bstep (se 1 (by rfl) ⟨518222, by rfl⟩ : syracuseStep 690963 = 1036445) B1036445
theorem B690979 : Blo 690315 690979 := bstep (se 1 (by rfl) ⟨518234, by rfl⟩ : syracuseStep 690979 = 1036469) B1036469
theorem B690995 : Blo 690315 690995 := bstep (se 1 (by rfl) ⟨518246, by rfl⟩ : syracuseStep 690995 = 1036493) B1036493
theorem B691011 : Blo 690315 691011 := bstep (se 1 (by rfl) ⟨518258, by rfl⟩ : syracuseStep 691011 = 1036517) B1036517
theorem B691027 : Blo 690315 691027 := bstep (se 1 (by rfl) ⟨518270, by rfl⟩ : syracuseStep 691027 = 1036541) B1036541
theorem B691043 : Blo 690315 691043 := bstep (se 1 (by rfl) ⟨518282, by rfl⟩ : syracuseStep 691043 = 1036565) B1036565
theorem B691059 : Blo 690315 691059 := bstep (se 1 (by rfl) ⟨518294, by rfl⟩ : syracuseStep 691059 = 1036589) B1036589
theorem B691075 : Blo 690315 691075 := bstep (se 1 (by rfl) ⟨518306, by rfl⟩ : syracuseStep 691075 = 1036613) B1036613
theorem B691091 : Blo 690315 691091 := bstep (se 1 (by rfl) ⟨518318, by rfl⟩ : syracuseStep 691091 = 1036637) B1036637
theorem B691107 : Blo 690315 691107 := bstep (se 1 (by rfl) ⟨518330, by rfl⟩ : syracuseStep 691107 = 1036661) B1036661
theorem B691123 : Blo 690315 691123 := bstep (se 1 (by rfl) ⟨518342, by rfl⟩ : syracuseStep 691123 = 1036685) B1036685
theorem B1182643 : Blo 690315 1182643 := bstep (se 1 (by rfl) ⟨886982, by rfl⟩ : syracuseStep 1182643 = 1773965) B1773965
theorem B691139 : Blo 690315 691139 := bstep (se 1 (by rfl) ⟨518354, by rfl⟩ : syracuseStep 691139 = 1036709) B1036709
theorem B691155 : Blo 690315 691155 := bstep (se 1 (by rfl) ⟨518366, by rfl⟩ : syracuseStep 691155 = 1036733) B1036733
theorem B691171 : Blo 690315 691171 := bstep (se 1 (by rfl) ⟨518378, by rfl⟩ : syracuseStep 691171 = 1036757) B1036757
theorem B691187 : Blo 690315 691187 := bstep (se 1 (by rfl) ⟨518390, by rfl⟩ : syracuseStep 691187 = 1036781) B1036781
theorem B691203 : Blo 690315 691203 := bstep (se 1 (by rfl) ⟨518402, by rfl⟩ : syracuseStep 691203 = 1036805) B1036805
theorem B1313795 : Blo 690315 1313795 := bstep (se 1 (by rfl) ⟨985346, by rfl⟩ : syracuseStep 1313795 = 1970693) B1970693
theorem B691219 : Blo 690315 691219 := bstep (se 1 (by rfl) ⟨518414, by rfl⟩ : syracuseStep 691219 = 1036829) B1036829
theorem B691235 : Blo 690315 691235 := bstep (se 1 (by rfl) ⟨518426, by rfl⟩ : syracuseStep 691235 = 1036853) B1036853
theorem B691251 : Blo 690315 691251 := bstep (se 1 (by rfl) ⟨518438, by rfl⟩ : syracuseStep 691251 = 1036877) B1036877
theorem B691267 : Blo 690315 691267 := bstep (se 1 (by rfl) ⟨518450, by rfl⟩ : syracuseStep 691267 = 1036901) B1036901
theorem B691283 : Blo 690315 691283 := bstep (se 1 (by rfl) ⟨518462, by rfl⟩ : syracuseStep 691283 = 1036925) B1036925
theorem B986195 : Blo 690315 986195 := bstep (se 1 (by rfl) ⟨739646, by rfl⟩ : syracuseStep 986195 = 1479293) B1479293
theorem B691299 : Blo 690315 691299 := bstep (se 1 (by rfl) ⟨518474, by rfl⟩ : syracuseStep 691299 = 1036949) B1036949
theorem B691315 : Blo 690315 691315 := bstep (se 1 (by rfl) ⟨518486, by rfl⟩ : syracuseStep 691315 = 1036973) B1036973
theorem B691331 : Blo 690315 691331 := bstep (se 1 (by rfl) ⟨518498, by rfl⟩ : syracuseStep 691331 = 1036997) B1036997
theorem B691347 : Blo 690315 691347 := bstep (se 1 (by rfl) ⟨518510, by rfl⟩ : syracuseStep 691347 = 1037021) B1037021
theorem B691363 : Blo 690315 691363 := bstep (se 1 (by rfl) ⟨518522, by rfl⟩ : syracuseStep 691363 = 1037045) B1037045
theorem B691379 : Blo 690315 691379 := bstep (se 1 (by rfl) ⟨518534, by rfl⟩ : syracuseStep 691379 = 1037069) B1037069
theorem B691395 : Blo 690315 691395 := bstep (se 1 (by rfl) ⟨518546, by rfl⟩ : syracuseStep 691395 = 1037093) B1037093
theorem B691411 : Blo 690315 691411 := bstep (se 1 (by rfl) ⟨518558, by rfl⟩ : syracuseStep 691411 = 1037117) B1037117
theorem B691427 : Blo 690315 691427 := bstep (se 1 (by rfl) ⟨518570, by rfl⟩ : syracuseStep 691427 = 1037141) B1037141
theorem B691443 : Blo 690315 691443 := bstep (se 1 (by rfl) ⟨518582, by rfl⟩ : syracuseStep 691443 = 1037165) B1037165
theorem B691459 : Blo 690315 691459 := bstep (se 1 (by rfl) ⟨518594, by rfl⟩ : syracuseStep 691459 = 1037189) B1037189
theorem B691475 : Blo 690315 691475 := bstep (se 1 (by rfl) ⟨518606, by rfl⟩ : syracuseStep 691475 = 1037213) B1037213
theorem B691491 : Blo 690315 691491 := bstep (se 1 (by rfl) ⟨518618, by rfl⟩ : syracuseStep 691491 = 1037237) B1037237
theorem B1314083 : Blo 690315 1314083 := bstep (se 1 (by rfl) ⟨985562, by rfl⟩ : syracuseStep 1314083 = 1971125) B1971125
theorem B691507 : Blo 690315 691507 := bstep (se 1 (by rfl) ⟨518630, by rfl⟩ : syracuseStep 691507 = 1037261) B1037261
theorem B1183027 : Blo 690315 1183027 := bstep (se 1 (by rfl) ⟨887270, by rfl⟩ : syracuseStep 1183027 = 1774541) B1774541
theorem B691523 : Blo 690315 691523 := bstep (se 1 (by rfl) ⟨518642, by rfl⟩ : syracuseStep 691523 = 1037285) B1037285
theorem B2329937 : Blo 690315 2329937 := bstep (se 2 (by rfl) ⟨873726, by rfl⟩ : syracuseStep 2329937 = 1747453) B1747453
theorem B691539 : Blo 690315 691539 := bstep (se 1 (by rfl) ⟨518654, by rfl⟩ : syracuseStep 691539 = 1037309) B1037309
theorem B691555 : Blo 690315 691555 := bstep (se 1 (by rfl) ⟨518666, by rfl⟩ : syracuseStep 691555 = 1037333) B1037333
theorem B1871203 : Blo 690315 1871203 := bstep (se 1 (by rfl) ⟨1403402, by rfl⟩ : syracuseStep 1871203 = 2806805) B2806805
theorem B691571 : Blo 690315 691571 := bstep (se 1 (by rfl) ⟨518678, by rfl⟩ : syracuseStep 691571 = 1037357) B1037357
theorem B691587 : Blo 690315 691587 := bstep (se 1 (by rfl) ⟨518690, by rfl⟩ : syracuseStep 691587 = 1037381) B1037381
theorem B691603 : Blo 690315 691603 := bstep (se 1 (by rfl) ⟨518702, by rfl⟩ : syracuseStep 691603 = 1037405) B1037405
theorem B691619 : Blo 690315 691619 := bstep (se 1 (by rfl) ⟨518714, by rfl⟩ : syracuseStep 691619 = 1037429) B1037429
theorem B691635 : Blo 690315 691635 := bstep (se 1 (by rfl) ⟨518726, by rfl⟩ : syracuseStep 691635 = 1037453) B1037453
theorem B691651 : Blo 690315 691651 := bstep (se 1 (by rfl) ⟨518738, by rfl⟩ : syracuseStep 691651 = 1037477) B1037477
theorem B7212485 : Blo 690315 7212485 := bstep (se 4 (by rfl) ⟨676170, by rfl⟩ : syracuseStep 7212485 = 1352341) B1352341
theorem B691667 : Blo 690315 691667 := bstep (se 1 (by rfl) ⟨518750, by rfl⟩ : syracuseStep 691667 = 1037501) B1037501
theorem B691683 : Blo 690315 691683 := bstep (se 1 (by rfl) ⟨518762, by rfl⟩ : syracuseStep 691683 = 1037525) B1037525
theorem B691699 : Blo 690315 691699 := bstep (se 1 (by rfl) ⟨518774, by rfl⟩ : syracuseStep 691699 = 1037549) B1037549
theorem B1969667 : Blo 690315 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B691715 : Blo 690315 691715 := bstep (se 1 (by rfl) ⟨518786, by rfl⟩ : syracuseStep 691715 = 1037573) B1037573
theorem B691731 : Blo 690315 691731 := bstep (se 1 (by rfl) ⟨518798, by rfl⟩ : syracuseStep 691731 = 1037597) B1037597
theorem B691747 : Blo 690315 691747 := bstep (se 1 (by rfl) ⟨518810, by rfl⟩ : syracuseStep 691747 = 1037621) B1037621
theorem B691763 : Blo 690315 691763 := bstep (se 1 (by rfl) ⟨518822, by rfl⟩ : syracuseStep 691763 = 1037645) B1037645
theorem B691779 : Blo 690315 691779 := bstep (se 1 (by rfl) ⟨518834, by rfl⟩ : syracuseStep 691779 = 1037669) B1037669
theorem B5901893 : Blo 690315 5901893 := bstep (se 4 (by rfl) ⟨553302, by rfl⟩ : syracuseStep 5901893 = 1106605) B1106605
theorem B1478225 : Blo 690315 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B691795 : Blo 690315 691795 := bstep (se 1 (by rfl) ⟨518846, by rfl⟩ : syracuseStep 691795 = 1037693) B1037693
theorem B691811 : Blo 690315 691811 := bstep (se 1 (by rfl) ⟨518858, by rfl⟩ : syracuseStep 691811 = 1037717) B1037717
theorem B691827 : Blo 690315 691827 := bstep (se 1 (by rfl) ⟨518870, by rfl⟩ : syracuseStep 691827 = 1037741) B1037741
theorem B691843 : Blo 690315 691843 := bstep (se 1 (by rfl) ⟨518882, by rfl⟩ : syracuseStep 691843 = 1037765) B1037765
theorem B2952845 : Blo 690315 2952845 := bstep (se 3 (by rfl) ⟨553658, by rfl⟩ : syracuseStep 2952845 = 1107317) B1107317
theorem B13471373 : Blo 690315 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B691859 : Blo 690315 691859 := bstep (se 1 (by rfl) ⟨518894, by rfl⟩ : syracuseStep 691859 = 1037789) B1037789
theorem B691875 : Blo 690315 691875 := bstep (se 1 (by rfl) ⟨518906, by rfl⟩ : syracuseStep 691875 = 1037813) B1037813
theorem B691891 : Blo 690315 691891 := bstep (se 1 (by rfl) ⟨518918, by rfl⟩ : syracuseStep 691891 = 1037837) B1037837
theorem B691907 : Blo 690315 691907 := bstep (se 1 (by rfl) ⟨518930, by rfl⟩ : syracuseStep 691907 = 1037861) B1037861
theorem B986833 : Blo 690315 986833 := bstep (se 2 (by rfl) ⟨370062, by rfl⟩ : syracuseStep 986833 = 740125) B740125
theorem B691923 : Blo 690315 691923 := bstep (se 1 (by rfl) ⟨518942, by rfl⟩ : syracuseStep 691923 = 1037885) B1037885
theorem B1576675 : Blo 690315 1576675 := bstep (se 1 (by rfl) ⟨1182506, by rfl⟩ : syracuseStep 1576675 = 2365013) B2365013
theorem B691939 : Blo 690315 691939 := bstep (se 1 (by rfl) ⟨518954, by rfl⟩ : syracuseStep 691939 = 1037909) B1037909
theorem B691955 : Blo 690315 691955 := bstep (se 1 (by rfl) ⟨518966, by rfl⟩ : syracuseStep 691955 = 1037933) B1037933
theorem B691971 : Blo 690315 691971 := bstep (se 1 (by rfl) ⟨518978, by rfl⟩ : syracuseStep 691971 = 1037957) B1037957
theorem B691987 : Blo 690315 691987 := bstep (se 1 (by rfl) ⟨518990, by rfl⟩ : syracuseStep 691987 = 1037981) B1037981
theorem B692003 : Blo 690315 692003 := bstep (se 1 (by rfl) ⟨519002, by rfl⟩ : syracuseStep 692003 = 1038005) B1038005
theorem B692019 : Blo 690315 692019 := bstep (se 1 (by rfl) ⟨519014, by rfl⟩ : syracuseStep 692019 = 1038029) B1038029
theorem B692035 : Blo 690315 692035 := bstep (se 1 (by rfl) ⟨519026, by rfl⟩ : syracuseStep 692035 = 1038053) B1038053
theorem B692051 : Blo 690315 692051 := bstep (se 1 (by rfl) ⟨519038, by rfl⟩ : syracuseStep 692051 = 1038077) B1038077
theorem B692067 : Blo 690315 692067 := bstep (se 1 (by rfl) ⟨519050, by rfl⟩ : syracuseStep 692067 = 1038101) B1038101
theorem B2330477 : Blo 690315 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B692083 : Blo 690315 692083 := bstep (se 1 (by rfl) ⟨519062, by rfl⟩ : syracuseStep 692083 = 1038125) B1038125
theorem B692099 : Blo 690315 692099 := bstep (se 1 (by rfl) ⟨519074, by rfl⟩ : syracuseStep 692099 = 1038149) B1038149
theorem B692115 : Blo 690315 692115 := bstep (se 1 (by rfl) ⟨519086, by rfl⟩ : syracuseStep 692115 = 1038173) B1038173
theorem B2330531 : Blo 690315 2330531 := bstep (se 1 (by rfl) ⟨1747898, by rfl⟩ : syracuseStep 2330531 = 3495797) B3495797
theorem B692131 : Blo 690315 692131 := bstep (se 1 (by rfl) ⟨519098, by rfl⟩ : syracuseStep 692131 = 1038197) B1038197
theorem B692147 : Blo 690315 692147 := bstep (se 1 (by rfl) ⟨519110, by rfl⟩ : syracuseStep 692147 = 1038221) B1038221
theorem B692163 : Blo 690315 692163 := bstep (se 1 (by rfl) ⟨519122, by rfl⟩ : syracuseStep 692163 = 1038245) B1038245
theorem B692179 : Blo 690315 692179 := bstep (se 1 (by rfl) ⟨519134, by rfl⟩ : syracuseStep 692179 = 1038269) B1038269
theorem B692195 : Blo 690315 692195 := bstep (se 1 (by rfl) ⟨519146, by rfl⟩ : syracuseStep 692195 = 1038293) B1038293
theorem B692211 : Blo 690315 692211 := bstep (se 1 (by rfl) ⟨519158, by rfl⟩ : syracuseStep 692211 = 1038317) B1038317
theorem B692227 : Blo 690315 692227 := bstep (se 1 (by rfl) ⟨519170, by rfl⟩ : syracuseStep 692227 = 1038341) B1038341
theorem B1871885 : Blo 690315 1871885 := bstep (se 3 (by rfl) ⟨350978, by rfl⟩ : syracuseStep 1871885 = 701957) B701957
theorem B692243 : Blo 690315 692243 := bstep (se 1 (by rfl) ⟨519182, by rfl⟩ : syracuseStep 692243 = 1038365) B1038365
theorem B987169 : Blo 690315 987169 := bstep (se 2 (by rfl) ⟨370188, by rfl⟩ : syracuseStep 987169 = 740377) B740377
theorem B692259 : Blo 690315 692259 := bstep (se 1 (by rfl) ⟨519194, by rfl⟩ : syracuseStep 692259 = 1038389) B1038389
theorem B692275 : Blo 690315 692275 := bstep (se 1 (by rfl) ⟨519206, by rfl⟩ : syracuseStep 692275 = 1038413) B1038413
theorem B692291 : Blo 690315 692291 := bstep (se 1 (by rfl) ⟨519218, by rfl⟩ : syracuseStep 692291 = 1038437) B1038437
theorem B692307 : Blo 690315 692307 := bstep (se 1 (by rfl) ⟨519230, by rfl⟩ : syracuseStep 692307 = 1038461) B1038461
theorem B692323 : Blo 690315 692323 := bstep (se 1 (by rfl) ⟨519242, by rfl⟩ : syracuseStep 692323 = 1038485) B1038485
theorem B692339 : Blo 690315 692339 := bstep (se 1 (by rfl) ⟨519254, by rfl⟩ : syracuseStep 692339 = 1038509) B1038509
theorem B692355 : Blo 690315 692355 := bstep (se 1 (by rfl) ⟨519266, by rfl⟩ : syracuseStep 692355 = 1038533) B1038533
theorem B692371 : Blo 690315 692371 := bstep (se 1 (by rfl) ⟨519278, by rfl⟩ : syracuseStep 692371 = 1038557) B1038557
theorem B692387 : Blo 690315 692387 := bstep (se 1 (by rfl) ⟨519290, by rfl⟩ : syracuseStep 692387 = 1038581) B1038581
theorem B2330801 : Blo 690315 2330801 := bstep (se 2 (by rfl) ⟨874050, by rfl⟩ : syracuseStep 2330801 = 1748101) B1748101
theorem B692403 : Blo 690315 692403 := bstep (se 1 (by rfl) ⟨519302, by rfl⟩ : syracuseStep 692403 = 1038605) B1038605
theorem B692419 : Blo 690315 692419 := bstep (se 1 (by rfl) ⟨519314, by rfl⟩ : syracuseStep 692419 = 1038629) B1038629
theorem B2101457 : Blo 690315 2101457 := bstep (se 2 (by rfl) ⟨788046, by rfl⟩ : syracuseStep 2101457 = 1576093) B1576093
theorem B1315025 : Blo 690315 1315025 := bstep (se 2 (by rfl) ⟨493134, by rfl⟩ : syracuseStep 1315025 = 986269) B986269
theorem B692435 : Blo 690315 692435 := bstep (se 1 (by rfl) ⟨519326, by rfl⟩ : syracuseStep 692435 = 1038653) B1038653
theorem B692451 : Blo 690315 692451 := bstep (se 1 (by rfl) ⟨519338, by rfl⟩ : syracuseStep 692451 = 1038677) B1038677
theorem B5902577 : Blo 690315 5902577 := bstep (se 2 (by rfl) ⟨2213466, by rfl⟩ : syracuseStep 5902577 = 4426933) B4426933
theorem B692467 : Blo 690315 692467 := bstep (se 1 (by rfl) ⟨519350, by rfl⟩ : syracuseStep 692467 = 1038701) B1038701
theorem B692483 : Blo 690315 692483 := bstep (se 1 (by rfl) ⟨519362, by rfl⟩ : syracuseStep 692483 = 1038725) B1038725
theorem B692499 : Blo 690315 692499 := bstep (se 1 (by rfl) ⟨519374, by rfl⟩ : syracuseStep 692499 = 1038749) B1038749
theorem B692515 : Blo 690315 692515 := bstep (se 1 (by rfl) ⟨519386, by rfl⟩ : syracuseStep 692515 = 1038773) B1038773
theorem B1970477 : Blo 690315 1970477 := bstep (se 3 (by rfl) ⟨369464, by rfl⟩ : syracuseStep 1970477 = 738929) B738929
theorem B692531 : Blo 690315 692531 := bstep (se 1 (by rfl) ⟨519398, by rfl⟩ : syracuseStep 692531 = 1038797) B1038797
theorem B692547 : Blo 690315 692547 := bstep (se 1 (by rfl) ⟨519410, by rfl⟩ : syracuseStep 692547 = 1038821) B1038821
theorem B3543373 : Blo 690315 3543373 := bstep (se 3 (by rfl) ⟨664382, by rfl⟩ : syracuseStep 3543373 = 1328765) B1328765
theorem B692563 : Blo 690315 692563 := bstep (se 1 (by rfl) ⟨519422, by rfl⟩ : syracuseStep 692563 = 1038845) B1038845
theorem B692579 : Blo 690315 692579 := bstep (se 1 (by rfl) ⟨519434, by rfl⟩ : syracuseStep 692579 = 1038869) B1038869
theorem B692595 : Blo 690315 692595 := bstep (se 1 (by rfl) ⟨519446, by rfl⟩ : syracuseStep 692595 = 1038893) B1038893
theorem B692611 : Blo 690315 692611 := bstep (se 1 (by rfl) ⟨519458, by rfl⟩ : syracuseStep 692611 = 1038917) B1038917
theorem B692627 : Blo 690315 692627 := bstep (se 1 (by rfl) ⟨519470, by rfl⟩ : syracuseStep 692627 = 1038941) B1038941
theorem B692643 : Blo 690315 692643 := bstep (se 1 (by rfl) ⟨519482, by rfl⟩ : syracuseStep 692643 = 1038965) B1038965
theorem B692659 : Blo 690315 692659 := bstep (se 1 (by rfl) ⟨519494, by rfl⟩ : syracuseStep 692659 = 1038989) B1038989
theorem B692675 : Blo 690315 692675 := bstep (se 1 (by rfl) ⟨519506, by rfl⟩ : syracuseStep 692675 = 1039013) B1039013
theorem B692691 : Blo 690315 692691 := bstep (se 1 (by rfl) ⟨519518, by rfl⟩ : syracuseStep 692691 = 1039037) B1039037
theorem B692707 : Blo 690315 692707 := bstep (se 1 (by rfl) ⟨519530, by rfl⟩ : syracuseStep 692707 = 1039061) B1039061
theorem B1970669 : Blo 690315 1970669 := bstep (se 3 (by rfl) ⟨369500, by rfl⟩ : syracuseStep 1970669 = 739001) B739001
theorem B692723 : Blo 690315 692723 := bstep (se 1 (by rfl) ⟨519542, by rfl⟩ : syracuseStep 692723 = 1039085) B1039085
theorem B692739 : Blo 690315 692739 := bstep (se 1 (by rfl) ⟨519554, by rfl⟩ : syracuseStep 692739 = 1039109) B1039109
theorem B692755 : Blo 690315 692755 := bstep (se 1 (by rfl) ⟨519566, by rfl⟩ : syracuseStep 692755 = 1039133) B1039133
theorem B889363 : Blo 690315 889363 := bstep (se 1 (by rfl) ⟨667022, by rfl⟩ : syracuseStep 889363 = 1334045) B1334045
theorem B692771 : Blo 690315 692771 := bstep (se 1 (by rfl) ⟨519578, by rfl⟩ : syracuseStep 692771 = 1039157) B1039157
theorem B692787 : Blo 690315 692787 := bstep (se 1 (by rfl) ⟨519590, by rfl⟩ : syracuseStep 692787 = 1039181) B1039181
theorem B692803 : Blo 690315 692803 := bstep (se 1 (by rfl) ⟨519602, by rfl⟩ : syracuseStep 692803 = 1039205) B1039205
theorem B692819 : Blo 690315 692819 := bstep (se 1 (by rfl) ⟨519614, by rfl⟩ : syracuseStep 692819 = 1039229) B1039229
theorem B1053281 : Blo 690315 1053281 := bstep (se 2 (by rfl) ⟨394980, by rfl⟩ : syracuseStep 1053281 = 789961) B789961
theorem B692835 : Blo 690315 692835 := bstep (se 1 (by rfl) ⟨519626, by rfl⟩ : syracuseStep 692835 = 1039253) B1039253
theorem B987761 : Blo 690315 987761 := bstep (se 2 (by rfl) ⟨370410, by rfl⟩ : syracuseStep 987761 = 740821) B740821
theorem B692851 : Blo 690315 692851 := bstep (se 1 (by rfl) ⟨519638, by rfl⟩ : syracuseStep 692851 = 1039277) B1039277
theorem B2101891 : Blo 690315 2101891 := bstep (se 1 (by rfl) ⟨1576418, by rfl⟩ : syracuseStep 2101891 = 3152837) B3152837
theorem B692867 : Blo 690315 692867 := bstep (se 1 (by rfl) ⟨519650, by rfl⟩ : syracuseStep 692867 = 1039301) B1039301
theorem B692883 : Blo 690315 692883 := bstep (se 1 (by rfl) ⟨519662, by rfl⟩ : syracuseStep 692883 = 1039325) B1039325
theorem B692899 : Blo 690315 692899 := bstep (se 1 (by rfl) ⟨519674, by rfl⟩ : syracuseStep 692899 = 1039349) B1039349
theorem B692915 : Blo 690315 692915 := bstep (se 1 (by rfl) ⟨519686, by rfl⟩ : syracuseStep 692915 = 1039373) B1039373
theorem B692931 : Blo 690315 692931 := bstep (se 1 (by rfl) ⟨519698, by rfl⟩ : syracuseStep 692931 = 1039397) B1039397
theorem B2331341 : Blo 690315 2331341 := bstep (se 3 (by rfl) ⟨437126, by rfl⟩ : syracuseStep 2331341 = 874253) B874253
theorem B2626253 : Blo 690315 2626253 := bstep (se 3 (by rfl) ⟨492422, by rfl⟩ : syracuseStep 2626253 = 984845) B984845
theorem B692947 : Blo 690315 692947 := bstep (se 1 (by rfl) ⟨519710, by rfl⟩ : syracuseStep 692947 = 1039421) B1039421
theorem B692963 : Blo 690315 692963 := bstep (se 1 (by rfl) ⟨519722, by rfl⟩ : syracuseStep 692963 = 1039445) B1039445
theorem B3511025 : Blo 690315 3511025 := bstep (se 2 (by rfl) ⟨1316634, by rfl⟩ : syracuseStep 3511025 = 2633269) B2633269
theorem B692979 : Blo 690315 692979 := bstep (se 1 (by rfl) ⟨519734, by rfl⟩ : syracuseStep 692979 = 1039469) B1039469
theorem B2331395 : Blo 690315 2331395 := bstep (se 1 (by rfl) ⟨1748546, by rfl⟩ : syracuseStep 2331395 = 3497093) B3497093
theorem B692995 : Blo 690315 692995 := bstep (se 1 (by rfl) ⟨519746, by rfl⟩ : syracuseStep 692995 = 1039493) B1039493
theorem B693011 : Blo 690315 693011 := bstep (se 1 (by rfl) ⟨519758, by rfl⟩ : syracuseStep 693011 = 1039517) B1039517
theorem B693027 : Blo 690315 693027 := bstep (se 1 (by rfl) ⟨519770, by rfl⟩ : syracuseStep 693027 = 1039541) B1039541
theorem B693043 : Blo 690315 693043 := bstep (se 1 (by rfl) ⟨519782, by rfl⟩ : syracuseStep 693043 = 1039565) B1039565
theorem B693059 : Blo 690315 693059 := bstep (se 1 (by rfl) ⟨519794, by rfl⟩ : syracuseStep 693059 = 1039589) B1039589
theorem B693075 : Blo 690315 693075 := bstep (se 1 (by rfl) ⟨519806, by rfl⟩ : syracuseStep 693075 = 1039613) B1039613
theorem B693091 : Blo 690315 693091 := bstep (se 1 (by rfl) ⟨519818, by rfl⟩ : syracuseStep 693091 = 1039637) B1039637
theorem B13308785 : Blo 690315 13308785 := bstep (se 2 (by rfl) ⟨4990794, by rfl⟩ : syracuseStep 13308785 = 9981589) B9981589
theorem B693107 : Blo 690315 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B693123 : Blo 690315 693123 := bstep (se 1 (by rfl) ⟨519842, by rfl⟩ : syracuseStep 693123 = 1039685) B1039685
theorem B693139 : Blo 690315 693139 := bstep (se 1 (by rfl) ⟨519854, by rfl⟩ : syracuseStep 693139 = 1039709) B1039709
theorem B693155 : Blo 690315 693155 := bstep (se 1 (by rfl) ⟨519866, by rfl⟩ : syracuseStep 693155 = 1039733) B1039733
theorem B693171 : Blo 690315 693171 := bstep (se 1 (by rfl) ⟨519878, by rfl⟩ : syracuseStep 693171 = 1039757) B1039757
theorem B693187 : Blo 690315 693187 := bstep (se 1 (by rfl) ⟨519890, by rfl⟩ : syracuseStep 693187 = 1039781) B1039781
theorem B693203 : Blo 690315 693203 := bstep (se 1 (by rfl) ⟨519902, by rfl⟩ : syracuseStep 693203 = 1039805) B1039805
theorem B693219 : Blo 690315 693219 := bstep (se 1 (by rfl) ⟨519914, by rfl⟩ : syracuseStep 693219 = 1039829) B1039829
theorem B693235 : Blo 690315 693235 := bstep (se 1 (by rfl) ⟨519926, by rfl⟩ : syracuseStep 693235 = 1039853) B1039853
theorem B693251 : Blo 690315 693251 := bstep (se 1 (by rfl) ⟨519938, by rfl⟩ : syracuseStep 693251 = 1039877) B1039877
theorem B2331665 : Blo 690315 2331665 := bstep (se 2 (by rfl) ⟨874374, by rfl⟩ : syracuseStep 2331665 = 1748749) B1748749
theorem B693267 : Blo 690315 693267 := bstep (se 1 (by rfl) ⟨519950, by rfl⟩ : syracuseStep 693267 = 1039901) B1039901
theorem B693283 : Blo 690315 693283 := bstep (se 1 (by rfl) ⟨519962, by rfl⟩ : syracuseStep 693283 = 1039925) B1039925
theorem B693299 : Blo 690315 693299 := bstep (se 1 (by rfl) ⟨519974, by rfl⟩ : syracuseStep 693299 = 1039949) B1039949
theorem B2397251 : Blo 690315 2397251 := bstep (se 1 (by rfl) ⟨1797938, by rfl⟩ : syracuseStep 2397251 = 3595877) B3595877
theorem B693315 : Blo 690315 693315 := bstep (se 1 (by rfl) ⟨519986, by rfl⟩ : syracuseStep 693315 = 1039973) B1039973
theorem B1315921 : Blo 690315 1315921 := bstep (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) B986941
theorem B693331 : Blo 690315 693331 := bstep (se 1 (by rfl) ⟨519998, by rfl⟩ : syracuseStep 693331 = 1039997) B1039997
theorem B693347 : Blo 690315 693347 := bstep (se 1 (by rfl) ⟨520010, by rfl⟩ : syracuseStep 693347 = 1040021) B1040021
theorem B693363 : Blo 690315 693363 := bstep (se 1 (by rfl) ⟨520022, by rfl⟩ : syracuseStep 693363 = 1040045) B1040045
theorem B693379 : Blo 690315 693379 := bstep (se 1 (by rfl) ⟨520034, by rfl⟩ : syracuseStep 693379 = 1040069) B1040069
theorem B988291 : Blo 690315 988291 := bstep (se 1 (by rfl) ⟨741218, by rfl⟩ : syracuseStep 988291 = 1482437) B1482437
theorem B1184915 : Blo 690315 1184915 := bstep (se 1 (by rfl) ⟨888686, by rfl⟩ : syracuseStep 1184915 = 1777373) B1777373
theorem B693395 : Blo 690315 693395 := bstep (se 1 (by rfl) ⟨520046, by rfl⟩ : syracuseStep 693395 = 1040093) B1040093
theorem B693411 : Blo 690315 693411 := bstep (se 1 (by rfl) ⟨520058, by rfl⟩ : syracuseStep 693411 = 1040117) B1040117
theorem B693427 : Blo 690315 693427 := bstep (se 1 (by rfl) ⟨520070, by rfl⟩ : syracuseStep 693427 = 1040141) B1040141
theorem B693443 : Blo 690315 693443 := bstep (se 1 (by rfl) ⟨520082, by rfl⟩ : syracuseStep 693443 = 1040165) B1040165
theorem B693459 : Blo 690315 693459 := bstep (se 1 (by rfl) ⟨520094, by rfl⟩ : syracuseStep 693459 = 1040189) B1040189
theorem B693475 : Blo 690315 693475 := bstep (se 1 (by rfl) ⟨520106, by rfl⟩ : syracuseStep 693475 = 1040213) B1040213
theorem B1316081 : Blo 690315 1316081 := bstep (se 2 (by rfl) ⟨493530, by rfl⟩ : syracuseStep 1316081 = 987061) B987061
theorem B693491 : Blo 690315 693491 := bstep (se 1 (by rfl) ⟨520118, by rfl⟩ : syracuseStep 693491 = 1040237) B1040237
theorem B693507 : Blo 690315 693507 := bstep (se 1 (by rfl) ⟨520130, by rfl⟩ : syracuseStep 693507 = 1040261) B1040261
theorem B693523 : Blo 690315 693523 := bstep (se 1 (by rfl) ⟨520142, by rfl⟩ : syracuseStep 693523 = 1040285) B1040285
theorem B693539 : Blo 690315 693539 := bstep (se 1 (by rfl) ⟨520154, by rfl⟩ : syracuseStep 693539 = 1040309) B1040309
theorem B693555 : Blo 690315 693555 := bstep (se 1 (by rfl) ⟨520166, by rfl⟩ : syracuseStep 693555 = 1040333) B1040333
theorem B693571 : Blo 690315 693571 := bstep (se 1 (by rfl) ⟨520178, by rfl⟩ : syracuseStep 693571 = 1040357) B1040357
theorem B693587 : Blo 690315 693587 := bstep (se 1 (by rfl) ⟨520190, by rfl⟩ : syracuseStep 693587 = 1040381) B1040381
theorem B693603 : Blo 690315 693603 := bstep (se 1 (by rfl) ⟨520202, by rfl⟩ : syracuseStep 693603 = 1040405) B1040405
theorem B3151217 : Blo 690315 3151217 := bstep (se 2 (by rfl) ⟨1181706, by rfl⟩ : syracuseStep 3151217 = 2363413) B2363413
theorem B693619 : Blo 690315 693619 := bstep (se 1 (by rfl) ⟨520214, by rfl⟩ : syracuseStep 693619 = 1040429) B1040429
theorem B693635 : Blo 690315 693635 := bstep (se 1 (by rfl) ⟨520226, by rfl⟩ : syracuseStep 693635 = 1040453) B1040453
theorem B8885645 : Blo 690315 8885645 := bstep (se 3 (by rfl) ⟨1666058, by rfl⟩ : syracuseStep 8885645 = 3332117) B3332117
theorem B693651 : Blo 690315 693651 := bstep (se 1 (by rfl) ⟨520238, by rfl⟩ : syracuseStep 693651 = 1040477) B1040477
theorem B693667 : Blo 690315 693667 := bstep (se 1 (by rfl) ⟨520250, by rfl⟩ : syracuseStep 693667 = 1040501) B1040501
theorem B693683 : Blo 690315 693683 := bstep (se 1 (by rfl) ⟨520262, by rfl⟩ : syracuseStep 693683 = 1040525) B1040525
theorem B693699 : Blo 690315 693699 := bstep (se 1 (by rfl) ⟨520274, by rfl⟩ : syracuseStep 693699 = 1040549) B1040549
theorem B1971661 : Blo 690315 1971661 := bstep (se 3 (by rfl) ⟨369686, by rfl⟩ : syracuseStep 1971661 = 739373) B739373
theorem B693715 : Blo 690315 693715 := bstep (se 1 (by rfl) ⟨520286, by rfl⟩ : syracuseStep 693715 = 1040573) B1040573
theorem B693731 : Blo 690315 693731 := bstep (se 1 (by rfl) ⟨520298, by rfl⟩ : syracuseStep 693731 = 1040597) B1040597
theorem B693747 : Blo 690315 693747 := bstep (se 1 (by rfl) ⟨520310, by rfl⟩ : syracuseStep 693747 = 1040621) B1040621
theorem B693763 : Blo 690315 693763 := bstep (se 1 (by rfl) ⟨520322, by rfl⟩ : syracuseStep 693763 = 1040645) B1040645
theorem B693779 : Blo 690315 693779 := bstep (se 1 (by rfl) ⟨520334, by rfl⟩ : syracuseStep 693779 = 1040669) B1040669
theorem B693795 : Blo 690315 693795 := bstep (se 1 (by rfl) ⟨520346, by rfl⟩ : syracuseStep 693795 = 1040693) B1040693
theorem B2332205 : Blo 690315 2332205 := bstep (se 3 (by rfl) ⟨437288, by rfl⟩ : syracuseStep 2332205 = 874577) B874577
theorem B693811 : Blo 690315 693811 := bstep (se 1 (by rfl) ⟨520358, by rfl⟩ : syracuseStep 693811 = 1040717) B1040717
theorem B693827 : Blo 690315 693827 := bstep (se 1 (by rfl) ⟨520370, by rfl⟩ : syracuseStep 693827 = 1040741) B1040741
theorem B693843 : Blo 690315 693843 := bstep (se 1 (by rfl) ⟨520382, by rfl⟩ : syracuseStep 693843 = 1040765) B1040765
theorem B2332259 : Blo 690315 2332259 := bstep (se 1 (by rfl) ⟨1749194, by rfl⟩ : syracuseStep 2332259 = 3498389) B3498389
theorem B693859 : Blo 690315 693859 := bstep (se 1 (by rfl) ⟨520394, by rfl⟩ : syracuseStep 693859 = 1040789) B1040789
theorem B693875 : Blo 690315 693875 := bstep (se 1 (by rfl) ⟨520406, by rfl⟩ : syracuseStep 693875 = 1040813) B1040813
theorem B1316483 : Blo 690315 1316483 := bstep (se 1 (by rfl) ⟨987362, by rfl⟩ : syracuseStep 1316483 = 1974725) B1974725
theorem B693891 : Blo 690315 693891 := bstep (se 1 (by rfl) ⟨520418, by rfl⟩ : syracuseStep 693891 = 1040837) B1040837
theorem B693907 : Blo 690315 693907 := bstep (se 1 (by rfl) ⟨520430, by rfl⟩ : syracuseStep 693907 = 1040861) B1040861
theorem B693923 : Blo 690315 693923 := bstep (se 1 (by rfl) ⟨520442, by rfl⟩ : syracuseStep 693923 = 1040885) B1040885
theorem B693939 : Blo 690315 693939 := bstep (se 1 (by rfl) ⟨520454, by rfl⟩ : syracuseStep 693939 = 1040909) B1040909
theorem B693955 : Blo 690315 693955 := bstep (se 1 (by rfl) ⟨520466, by rfl⟩ : syracuseStep 693955 = 1040933) B1040933
theorem B693971 : Blo 690315 693971 := bstep (se 1 (by rfl) ⟨520478, by rfl⟩ : syracuseStep 693971 = 1040957) B1040957
theorem B693987 : Blo 690315 693987 := bstep (se 1 (by rfl) ⟨520490, by rfl⟩ : syracuseStep 693987 = 1040981) B1040981
theorem B694003 : Blo 690315 694003 := bstep (se 1 (by rfl) ⟨520502, by rfl⟩ : syracuseStep 694003 = 1041005) B1041005
theorem B694019 : Blo 690315 694019 := bstep (se 1 (by rfl) ⟨520514, by rfl⟩ : syracuseStep 694019 = 1041029) B1041029
theorem B694035 : Blo 690315 694035 := bstep (se 1 (by rfl) ⟨520526, by rfl⟩ : syracuseStep 694035 = 1041053) B1041053
theorem B694051 : Blo 690315 694051 := bstep (se 1 (by rfl) ⟨520538, by rfl⟩ : syracuseStep 694051 = 1041077) B1041077
theorem B694067 : Blo 690315 694067 := bstep (se 1 (by rfl) ⟨520550, by rfl⟩ : syracuseStep 694067 = 1041101) B1041101
theorem B694083 : Blo 690315 694083 := bstep (se 1 (by rfl) ⟨520562, by rfl⟩ : syracuseStep 694083 = 1041125) B1041125
theorem B694099 : Blo 690315 694099 := bstep (se 1 (by rfl) ⟨520574, by rfl⟩ : syracuseStep 694099 = 1041149) B1041149
theorem B694115 : Blo 690315 694115 := bstep (se 1 (by rfl) ⟨520586, by rfl⟩ : syracuseStep 694115 = 1041173) B1041173
theorem B2332529 : Blo 690315 2332529 := bstep (se 2 (by rfl) ⟨874698, by rfl⟩ : syracuseStep 2332529 = 1749397) B1749397
theorem B694131 : Blo 690315 694131 := bstep (se 1 (by rfl) ⟨520598, by rfl⟩ : syracuseStep 694131 = 1041197) B1041197
theorem B694147 : Blo 690315 694147 := bstep (se 1 (by rfl) ⟨520610, by rfl⟩ : syracuseStep 694147 = 1041221) B1041221
theorem B694163 : Blo 690315 694163 := bstep (se 1 (by rfl) ⟨520622, by rfl⟩ : syracuseStep 694163 = 1041245) B1041245
theorem B694179 : Blo 690315 694179 := bstep (se 1 (by rfl) ⟨520634, by rfl⟩ : syracuseStep 694179 = 1041269) B1041269
theorem B694195 : Blo 690315 694195 := bstep (se 1 (by rfl) ⟨520646, by rfl⟩ : syracuseStep 694195 = 1041293) B1041293
theorem B694211 : Blo 690315 694211 := bstep (se 1 (by rfl) ⟨520658, by rfl⟩ : syracuseStep 694211 = 1041317) B1041317
theorem B694227 : Blo 690315 694227 := bstep (se 1 (by rfl) ⟨520670, by rfl⟩ : syracuseStep 694227 = 1041341) B1041341
theorem B694243 : Blo 690315 694243 := bstep (se 1 (by rfl) ⟨520682, by rfl⟩ : syracuseStep 694243 = 1041365) B1041365
theorem B694259 : Blo 690315 694259 := bstep (se 1 (by rfl) ⟨520694, by rfl⟩ : syracuseStep 694259 = 1041389) B1041389
theorem B694275 : Blo 690315 694275 := bstep (se 1 (by rfl) ⟨520706, by rfl⟩ : syracuseStep 694275 = 1041413) B1041413
theorem B694291 : Blo 690315 694291 := bstep (se 1 (by rfl) ⟨520718, by rfl⟩ : syracuseStep 694291 = 1041437) B1041437
theorem B694307 : Blo 690315 694307 := bstep (se 1 (by rfl) ⟨520730, by rfl⟩ : syracuseStep 694307 = 1041461) B1041461
theorem B3512483 : Blo 690315 3512483 := bstep (se 1 (by rfl) ⟨2634362, by rfl⟩ : syracuseStep 3512483 = 5268725) B5268725
theorem B1579267 : Blo 690315 1579267 := bstep (se 1 (by rfl) ⟨1184450, by rfl⟩ : syracuseStep 1579267 = 2368901) B2368901
theorem B1481009 : Blo 690315 1481009 := bstep (se 2 (by rfl) ⟨555378, by rfl⟩ : syracuseStep 1481009 = 1110757) B1110757
theorem B1579331 : Blo 690315 1579331 := bstep (se 1 (by rfl) ⟨1184498, by rfl⟩ : syracuseStep 1579331 = 2368997) B2368997
theorem B2333069 : Blo 690315 2333069 := bstep (se 3 (by rfl) ⟨437450, by rfl⟩ : syracuseStep 2333069 = 874901) B874901
theorem B2333123 : Blo 690315 2333123 := bstep (se 1 (by rfl) ⟨1749842, by rfl⟩ : syracuseStep 2333123 = 3499685) B3499685
theorem B1317379 : Blo 690315 1317379 := bstep (se 1 (by rfl) ⟨988034, by rfl⟩ : syracuseStep 1317379 = 1976069) B1976069
theorem B8854069 : Blo 690315 8854069 := bstep (se 5 (by rfl) ⟨415034, by rfl⟩ : syracuseStep 8854069 = 830069) B830069
theorem B4725317 : Blo 690315 4725317 := bstep (se 4 (by rfl) ⟨442998, by rfl⟩ : syracuseStep 4725317 = 885997) B885997
theorem B1317539 : Blo 690315 1317539 := bstep (se 1 (by rfl) ⟨988154, by rfl⟩ : syracuseStep 1317539 = 1976309) B1976309
theorem B2333393 : Blo 690315 2333393 := bstep (se 2 (by rfl) ⟨875022, by rfl⟩ : syracuseStep 2333393 = 1750045) B1750045
theorem B3513293 : Blo 690315 3513293 := bstep (se 3 (by rfl) ⟨658742, by rfl⟩ : syracuseStep 3513293 = 1317485) B1317485
theorem B2530381 : Blo 690315 2530381 := bstep (se 3 (by rfl) ⟨474446, by rfl⟩ : syracuseStep 2530381 = 948893) B948893
theorem B2366545 : Blo 690315 2366545 := bstep (se 2 (by rfl) ⟨887454, by rfl⟩ : syracuseStep 2366545 = 1774909) B1774909
theorem B1186913 : Blo 690315 1186913 := bstep (se 2 (by rfl) ⟨445092, by rfl⟩ : syracuseStep 1186913 = 890185) B890185
theorem B1973393 : Blo 690315 1973393 := bstep (se 2 (by rfl) ⟨740022, by rfl⟩ : syracuseStep 1973393 = 1480045) B1480045
theorem B2333933 : Blo 690315 2333933 := bstep (se 3 (by rfl) ⟨437612, by rfl⟩ : syracuseStep 2333933 = 875225) B875225
theorem B2333987 : Blo 690315 2333987 := bstep (se 1 (by rfl) ⟨1750490, by rfl⟩ : syracuseStep 2333987 = 3500981) B3500981
theorem B1973585 : Blo 690315 1973585 := bstep (se 2 (by rfl) ⟨740094, by rfl⟩ : syracuseStep 1973585 = 1480189) B1480189
theorem B2366819 : Blo 690315 2366819 := bstep (se 1 (by rfl) ⟨1775114, by rfl⟩ : syracuseStep 2366819 = 3550229) B3550229
theorem B2366915 : Blo 690315 2366915 := bstep (se 1 (by rfl) ⟨1775186, by rfl⟩ : syracuseStep 2366915 = 3550373) B3550373
theorem B3153421 : Blo 690315 3153421 := bstep (se 3 (by rfl) ⟨591266, by rfl⟩ : syracuseStep 3153421 = 1182533) B1182533
theorem B2334257 : Blo 690315 2334257 := bstep (se 2 (by rfl) ⟨875346, by rfl⟩ : syracuseStep 2334257 = 1750693) B1750693
theorem B2629169 : Blo 690315 2629169 := bstep (se 2 (by rfl) ⟨985938, by rfl⟩ : syracuseStep 2629169 = 1971877) B1971877
theorem B1187569 : Blo 690315 1187569 := bstep (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) B890677
theorem B3940109 : Blo 690315 3940109 := bstep (se 3 (by rfl) ⟨738770, by rfl⟩ : syracuseStep 3940109 = 1477541) B1477541
theorem B2957219 : Blo 690315 2957219 := bstep (se 1 (by rfl) ⟨2217914, by rfl⟩ : syracuseStep 2957219 = 4435829) B4435829
theorem B2105347 : Blo 690315 2105347 := bstep (se 1 (by rfl) ⟨1579010, by rfl⟩ : syracuseStep 2105347 = 3158021) B3158021
theorem B2334797 : Blo 690315 2334797 := bstep (se 3 (by rfl) ⟨437774, by rfl⟩ : syracuseStep 2334797 = 875549) B875549
theorem B2334851 : Blo 690315 2334851 := bstep (se 1 (by rfl) ⟨1751138, by rfl⟩ : syracuseStep 2334851 = 3502277) B3502277
theorem B1876241 : Blo 690315 1876241 := bstep (se 2 (by rfl) ⟨703590, by rfl⟩ : syracuseStep 1876241 = 1407181) B1407181
theorem B1974577 : Blo 690315 1974577 := bstep (se 2 (by rfl) ⟨740466, by rfl⟩ : syracuseStep 1974577 = 1480933) B1480933
theorem B7119173 : Blo 690315 7119173 := bstep (se 4 (by rfl) ⟨667422, by rfl⟩ : syracuseStep 7119173 = 1334845) B1334845
theorem B16032113 : Blo 690315 16032113 := bstep (se 2 (by rfl) ⟨6012042, by rfl⟩ : syracuseStep 16032113 = 12024085) B12024085
theorem B2335121 : Blo 690315 2335121 := bstep (se 2 (by rfl) ⟨875670, by rfl⟩ : syracuseStep 2335121 = 1751341) B1751341
theorem B3154481 : Blo 690315 3154481 := bstep (se 2 (by rfl) ⟨1182930, by rfl⟩ : syracuseStep 3154481 = 2365861) B2365861
theorem B1974851 : Blo 690315 1974851 := bstep (se 1 (by rfl) ⟨1481138, by rfl⟩ : syracuseStep 1974851 = 2962277) B2962277
theorem B1975043 : Blo 690315 1975043 := bstep (se 1 (by rfl) ⟨1481282, by rfl⟩ : syracuseStep 1975043 = 2962565) B2962565
theorem B2335661 : Blo 690315 2335661 := bstep (se 3 (by rfl) ⟨437936, by rfl⟩ : syracuseStep 2335661 = 875873) B875873
theorem B2335715 : Blo 690315 2335715 := bstep (se 1 (by rfl) ⟨1751786, by rfl⟩ : syracuseStep 2335715 = 3503573) B3503573
theorem B2630627 : Blo 690315 2630627 := bstep (se 1 (by rfl) ⟨1972970, by rfl⟩ : syracuseStep 2630627 = 3945941) B3945941
theorem B2335985 : Blo 690315 2335985 := bstep (se 2 (by rfl) ⟨875994, by rfl⟩ : syracuseStep 2335985 = 1751989) B1751989
theorem B1975853 : Blo 690315 1975853 := bstep (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) B740945
theorem B1976035 : Blo 690315 1976035 := bstep (se 1 (by rfl) ⟨1482026, by rfl⟩ : syracuseStep 1976035 = 2964053) B2964053
theorem B2336525 : Blo 690315 2336525 := bstep (se 3 (by rfl) ⟨438098, by rfl⟩ : syracuseStep 2336525 = 876197) B876197
theorem B2336579 : Blo 690315 2336579 := bstep (se 1 (by rfl) ⟨1752434, by rfl⟩ : syracuseStep 2336579 = 3504869) B3504869
theorem B2959217 : Blo 690315 2959217 := bstep (se 2 (by rfl) ⟨1109706, by rfl⟩ : syracuseStep 2959217 = 2219413) B2219413
theorem B3942341 : Blo 690315 3942341 := bstep (se 4 (by rfl) ⟨369594, by rfl⟩ : syracuseStep 3942341 = 739189) B739189
theorem B2631629 : Blo 690315 2631629 := bstep (se 3 (by rfl) ⟨493430, by rfl⟩ : syracuseStep 2631629 = 986861) B986861
theorem B2336849 : Blo 690315 2336849 := bstep (se 2 (by rfl) ⟨876318, by rfl⟩ : syracuseStep 2336849 = 1752637) B1752637
theorem B1976525 : Blo 690315 1976525 := bstep (se 3 (by rfl) ⟨370598, by rfl⟩ : syracuseStep 1976525 = 741197) B741197
theorem B2959715 : Blo 690315 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B1583491 : Blo 690315 1583491 := bstep (se 1 (by rfl) ⟨1187618, by rfl⟩ : syracuseStep 1583491 = 2375237) B2375237
theorem B2337389 : Blo 690315 2337389 := bstep (se 3 (by rfl) ⟨438260, by rfl⟩ : syracuseStep 2337389 = 876521) B876521
theorem B3943025 : Blo 690315 3943025 := bstep (se 2 (by rfl) ⟨1478634, by rfl⟩ : syracuseStep 3943025 = 2957269) B2957269
theorem B1124977 : Blo 690315 1124977 := bstep (se 2 (by rfl) ⟨421866, by rfl⟩ : syracuseStep 1124977 = 843733) B843733
theorem B2337443 : Blo 690315 2337443 := bstep (se 1 (by rfl) ⟨1753082, by rfl⟩ : syracuseStep 2337443 = 3506165) B3506165
theorem B6761357 : Blo 690315 6761357 := bstep (se 3 (by rfl) ⟨1267754, by rfl⟩ : syracuseStep 6761357 = 2535509) B2535509
theorem B1747889 : Blo 690315 1747889 := bstep (se 2 (by rfl) ⟨655458, by rfl⟩ : syracuseStep 1747889 = 1310917) B1310917
theorem B2337713 : Blo 690315 2337713 := bstep (se 2 (by rfl) ⟨876642, by rfl⟩ : syracuseStep 2337713 = 1753285) B1753285
theorem B1747939 : Blo 690315 1747939 := bstep (se 1 (by rfl) ⟨1310954, by rfl⟩ : syracuseStep 1747939 = 2621909) B2621909
theorem B2370541 : Blo 690315 2370541 := bstep (se 3 (by rfl) ⟨444476, by rfl⟩ : syracuseStep 2370541 = 888953) B888953
theorem B1748081 : Blo 690315 1748081 := bstep (se 2 (by rfl) ⟨655530, by rfl⟩ : syracuseStep 1748081 = 1311061) B1311061
theorem B830579 : Blo 690315 830579 := bstep (se 1 (by rfl) ⟨622934, by rfl⟩ : syracuseStep 830579 = 1245869) B1245869
theorem B2108849 : Blo 690315 2108849 := bstep (se 2 (by rfl) ⟨790818, by rfl⟩ : syracuseStep 2108849 = 1581637) B1581637
theorem B1125809 : Blo 690315 1125809 := bstep (se 2 (by rfl) ⟨422178, by rfl⟩ : syracuseStep 1125809 = 844357) B844357
theorem B2338253 : Blo 690315 2338253 := bstep (se 3 (by rfl) ⟨438422, by rfl⟩ : syracuseStep 2338253 = 876845) B876845
theorem B2338307 : Blo 690315 2338307 := bstep (se 1 (by rfl) ⟨1753730, by rfl⟩ : syracuseStep 2338307 = 3507461) B3507461
theorem B2665997 : Blo 690315 2665997 := bstep (se 3 (by rfl) ⟨499874, by rfl⟩ : syracuseStep 2665997 = 999749) B999749
theorem B9875141 : Blo 690315 9875141 := bstep (se 4 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 9875141 = 1851589) B1851589
theorem B2338577 : Blo 690315 2338577 := bstep (se 2 (by rfl) ⟨876966, by rfl⟩ : syracuseStep 2338577 = 1753933) B1753933
theorem B2633741 : Blo 690315 2633741 := bstep (se 3 (by rfl) ⟨493826, by rfl⟩ : syracuseStep 2633741 = 987653) B987653
theorem B3944483 : Blo 690315 3944483 := bstep (se 1 (by rfl) ⟨2958362, by rfl⟩ : syracuseStep 3944483 = 5916725) B5916725
theorem B1749073 : Blo 690315 1749073 := bstep (se 2 (by rfl) ⟨655902, by rfl⟩ : syracuseStep 1749073 = 1311805) B1311805
theorem B5910641 : Blo 690315 5910641 := bstep (se 2 (by rfl) ⟨2216490, by rfl⟩ : syracuseStep 5910641 = 4432981) B4432981
theorem B2961677 : Blo 690315 2961677 := bstep (se 3 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 2961677 = 1110629) B1110629
theorem B2339117 : Blo 690315 2339117 := bstep (se 3 (by rfl) ⟨438584, by rfl⟩ : syracuseStep 2339117 = 877169) B877169
theorem B1749347 : Blo 690315 1749347 := bstep (se 1 (by rfl) ⟨1312010, by rfl⟩ : syracuseStep 1749347 = 2624021) B2624021
theorem B2339171 : Blo 690315 2339171 := bstep (se 1 (by rfl) ⟨1754378, by rfl⟩ : syracuseStep 2339171 = 3508757) B3508757
theorem B1749539 : Blo 690315 1749539 := bstep (se 1 (by rfl) ⟨1312154, by rfl⟩ : syracuseStep 1749539 = 2624309) B2624309
theorem B2667043 : Blo 690315 2667043 := bstep (se 1 (by rfl) ⟨2000282, by rfl⟩ : syracuseStep 2667043 = 4000565) B4000565
theorem B2339441 : Blo 690315 2339441 := bstep (se 2 (by rfl) ⟨877290, by rfl⟩ : syracuseStep 2339441 = 1754581) B1754581
theorem B2634545 : Blo 690315 2634545 := bstep (se 2 (by rfl) ⟨987954, by rfl⟩ : syracuseStep 2634545 = 1975909) B1975909
theorem B1553219 : Blo 690315 1553219 := bstep (se 1 (by rfl) ⟨1164914, by rfl⟩ : syracuseStep 1553219 = 2329829) B2329829
theorem B7877573 : Blo 690315 7877573 := bstep (se 4 (by rfl) ⟨738522, by rfl⟩ : syracuseStep 7877573 = 1477045) B1477045
theorem B1553489 : Blo 690315 1553489 := bstep (se 2 (by rfl) ⟨582558, by rfl⟩ : syracuseStep 1553489 = 1165117) B1165117
theorem B1553507 : Blo 690315 1553507 := bstep (se 1 (by rfl) ⟨1165130, by rfl⟩ : syracuseStep 1553507 = 2330261) B2330261
theorem B2339981 : Blo 690315 2339981 := bstep (se 3 (by rfl) ⟨438746, by rfl⟩ : syracuseStep 2339981 = 877493) B877493
theorem B2340035 : Blo 690315 2340035 := bstep (se 1 (by rfl) ⟨1755026, by rfl⟩ : syracuseStep 2340035 = 3510053) B3510053
theorem B1553777 : Blo 690315 1553777 := bstep (se 2 (by rfl) ⟨582666, by rfl⟩ : syracuseStep 1553777 = 1165333) B1165333
theorem B1553795 : Blo 690315 1553795 := bstep (se 1 (by rfl) ⟨1165346, by rfl⟩ : syracuseStep 1553795 = 2330693) B2330693
theorem B2799053 : Blo 690315 2799053 := bstep (se 3 (by rfl) ⟨524822, by rfl⟩ : syracuseStep 2799053 = 1049645) B1049645
theorem B2635213 : Blo 690315 2635213 := bstep (se 3 (by rfl) ⟨494102, by rfl⟩ : syracuseStep 2635213 = 988205) B988205
theorem B1750481 : Blo 690315 1750481 := bstep (se 2 (by rfl) ⟨656430, by rfl⟩ : syracuseStep 1750481 = 1312861) B1312861
theorem B2340305 : Blo 690315 2340305 := bstep (se 2 (by rfl) ⟨877614, by rfl⟩ : syracuseStep 2340305 = 1755229) B1755229
theorem B1750531 : Blo 690315 1750531 := bstep (se 1 (by rfl) ⟨1312898, by rfl⟩ : syracuseStep 1750531 = 2625797) B2625797
theorem B833107 : Blo 690315 833107 := bstep (se 1 (by rfl) ⟨624830, by rfl⟩ : syracuseStep 833107 = 1249661) B1249661
theorem B1554065 : Blo 690315 1554065 := bstep (se 2 (by rfl) ⟨582774, by rfl⟩ : syracuseStep 1554065 = 1165549) B1165549
theorem B1750673 : Blo 690315 1750673 := bstep (se 2 (by rfl) ⟨656502, by rfl⟩ : syracuseStep 1750673 = 1313005) B1313005
theorem B1554083 : Blo 690315 1554083 := bstep (se 1 (by rfl) ⟨1165562, by rfl⟩ : syracuseStep 1554083 = 2331125) B2331125
theorem B833203 : Blo 690315 833203 := bstep (se 1 (by rfl) ⟨624902, by rfl⟩ : syracuseStep 833203 = 1249805) B1249805
theorem B2963249 : Blo 690315 2963249 := bstep (se 2 (by rfl) ⟨1111218, by rfl⟩ : syracuseStep 2963249 = 2222437) B2222437
theorem B4208453 : Blo 690315 4208453 := bstep (se 4 (by rfl) ⟨394542, by rfl⟩ : syracuseStep 4208453 = 789085) B789085
theorem B1554353 : Blo 690315 1554353 := bstep (se 2 (by rfl) ⟨582882, by rfl⟩ : syracuseStep 1554353 = 1165765) B1165765
theorem B1554371 : Blo 690315 1554371 := bstep (se 1 (by rfl) ⟨1165778, by rfl⟩ : syracuseStep 1554371 = 2331557) B2331557
theorem B12662725 : Blo 690315 12662725 := bstep (se 4 (by rfl) ⟨1187130, by rfl⟩ : syracuseStep 12662725 = 2374261) B2374261
theorem B833491 : Blo 690315 833491 := bstep (se 1 (by rfl) ⟨625118, by rfl⟩ : syracuseStep 833491 = 1250237) B1250237
theorem B2340845 : Blo 690315 2340845 := bstep (se 3 (by rfl) ⟨438908, by rfl⟩ : syracuseStep 2340845 = 877817) B877817
theorem B2340899 : Blo 690315 2340899 := bstep (se 1 (by rfl) ⟨1755674, by rfl⟩ : syracuseStep 2340899 = 3511349) B3511349
theorem B2373745 : Blo 690315 2373745 := bstep (se 2 (by rfl) ⟨890154, by rfl⟩ : syracuseStep 2373745 = 1780309) B1780309
theorem B833683 : Blo 690315 833683 := bstep (se 1 (by rfl) ⟨625262, by rfl⟩ : syracuseStep 833683 = 1250525) B1250525
theorem B1554641 : Blo 690315 1554641 := bstep (se 2 (by rfl) ⟨582990, by rfl⟩ : syracuseStep 1554641 = 1165981) B1165981
theorem B1554659 : Blo 690315 1554659 := bstep (se 1 (by rfl) ⟨1165994, by rfl⟩ : syracuseStep 1554659 = 2331989) B2331989
theorem B2636003 : Blo 690315 2636003 := bstep (se 1 (by rfl) ⟨1977002, by rfl⟩ : syracuseStep 2636003 = 3954005) B3954005
theorem B702739 : Blo 690315 702739 := bstep (se 1 (by rfl) ⟨527054, by rfl⟩ : syracuseStep 702739 = 1054109) B1054109
theorem B2341169 : Blo 690315 2341169 := bstep (se 2 (by rfl) ⟨877938, by rfl⟩ : syracuseStep 2341169 = 1755877) B1755877
theorem B1554929 : Blo 690315 1554929 := bstep (se 2 (by rfl) ⟨583098, by rfl⟩ : syracuseStep 1554929 = 1166197) B1166197
theorem B1554947 : Blo 690315 1554947 := bstep (se 1 (by rfl) ⟨1166210, by rfl⟩ : syracuseStep 1554947 = 2332421) B2332421
theorem B5913101 : Blo 690315 5913101 := bstep (se 3 (by rfl) ⟨1108706, by rfl⟩ : syracuseStep 5913101 = 2217413) B2217413
theorem B1751665 : Blo 690315 1751665 := bstep (se 2 (by rfl) ⟨656874, by rfl⟩ : syracuseStep 1751665 = 1313749) B1313749
theorem B1555217 : Blo 690315 1555217 := bstep (se 2 (by rfl) ⟨583206, by rfl⟩ : syracuseStep 1555217 = 1166413) B1166413
theorem B1555235 : Blo 690315 1555235 := bstep (se 1 (by rfl) ⟨1166426, by rfl⟩ : syracuseStep 1555235 = 2332853) B2332853
theorem B2341709 : Blo 690315 2341709 := bstep (se 3 (by rfl) ⟨439070, by rfl⟩ : syracuseStep 2341709 = 878141) B878141
theorem B1751939 : Blo 690315 1751939 := bstep (se 1 (by rfl) ⟨1313954, by rfl⟩ : syracuseStep 1751939 = 2627909) B2627909
theorem B2341763 : Blo 690315 2341763 := bstep (se 1 (by rfl) ⟨1756322, by rfl⟩ : syracuseStep 2341763 = 3512645) B3512645
theorem B1555505 : Blo 690315 1555505 := bstep (se 2 (by rfl) ⟨583314, by rfl⟩ : syracuseStep 1555505 = 1166629) B1166629
theorem B1555523 : Blo 690315 1555523 := bstep (se 1 (by rfl) ⟨1166642, by rfl⟩ : syracuseStep 1555523 = 2333285) B2333285
theorem B1752131 : Blo 690315 1752131 := bstep (se 1 (by rfl) ⟨1314098, by rfl⟩ : syracuseStep 1752131 = 2628197) B2628197
theorem B2342033 : Blo 690315 2342033 := bstep (se 2 (by rfl) ⟨878262, by rfl⟩ : syracuseStep 2342033 = 1756525) B1756525
theorem B3947717 : Blo 690315 3947717 := bstep (se 4 (by rfl) ⟨370098, by rfl⟩ : syracuseStep 3947717 = 740197) B740197
theorem B1555793 : Blo 690315 1555793 := bstep (se 2 (by rfl) ⟨583422, by rfl⟩ : syracuseStep 1555793 = 1166845) B1166845
theorem B1555811 : Blo 690315 1555811 := bstep (se 1 (by rfl) ⟨1166858, by rfl⟩ : syracuseStep 1555811 = 2333717) B2333717
theorem B1424803 : Blo 690315 1424803 := bstep (se 1 (by rfl) ⟨1068602, by rfl⟩ : syracuseStep 1424803 = 2137205) B2137205
theorem B1064497 : Blo 690315 1064497 := bstep (se 2 (by rfl) ⟨399186, by rfl⟩ : syracuseStep 1064497 = 798373) B798373
theorem B1556081 : Blo 690315 1556081 := bstep (se 2 (by rfl) ⟨583530, by rfl⟩ : syracuseStep 1556081 = 1167061) B1167061
theorem B1556099 : Blo 690315 1556099 := bstep (se 1 (by rfl) ⟨1167074, by rfl⟩ : syracuseStep 1556099 = 2334149) B2334149
theorem B3948173 : Blo 690315 3948173 := bstep (se 3 (by rfl) ⟨740282, by rfl⟩ : syracuseStep 3948173 = 1480565) B1480565
theorem B2342573 : Blo 690315 2342573 := bstep (se 3 (by rfl) ⟨439232, by rfl⟩ : syracuseStep 2342573 = 878465) B878465
theorem B2342627 : Blo 690315 2342627 := bstep (se 1 (by rfl) ⟨1756970, by rfl⟩ : syracuseStep 2342627 = 3513941) B3513941
theorem B2211725 : Blo 690315 2211725 := bstep (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) B829397
theorem B1556369 : Blo 690315 1556369 := bstep (se 2 (by rfl) ⟨583638, by rfl⟩ : syracuseStep 1556369 = 1167277) B1167277
theorem B1556387 : Blo 690315 1556387 := bstep (se 1 (by rfl) ⟨1167290, by rfl⟩ : syracuseStep 1556387 = 2334581) B2334581
theorem B4440005 : Blo 690315 4440005 := bstep (se 4 (by rfl) ⟨416250, by rfl⟩ : syracuseStep 4440005 = 832501) B832501
theorem B1753073 : Blo 690315 1753073 := bstep (se 2 (by rfl) ⟨657402, by rfl⟩ : syracuseStep 1753073 = 1314805) B1314805
theorem B2342897 : Blo 690315 2342897 := bstep (se 2 (by rfl) ⟨878586, by rfl⟩ : syracuseStep 2342897 = 1757173) B1757173
theorem B737267 : Blo 690315 737267 := bstep (se 1 (by rfl) ⟨552950, by rfl⟩ : syracuseStep 737267 = 1105901) B1105901
theorem B1753123 : Blo 690315 1753123 := bstep (se 1 (by rfl) ⟨1314842, by rfl⟩ : syracuseStep 1753123 = 2629685) B2629685
theorem B1556657 : Blo 690315 1556657 := bstep (se 2 (by rfl) ⟨583746, by rfl⟩ : syracuseStep 1556657 = 1167493) B1167493
theorem B1753265 : Blo 690315 1753265 := bstep (se 2 (by rfl) ⟨657474, by rfl⟩ : syracuseStep 1753265 = 1314949) B1314949
theorem B1556675 : Blo 690315 1556675 := bstep (se 1 (by rfl) ⟨1167506, by rfl⟩ : syracuseStep 1556675 = 2335013) B2335013
theorem B2965709 : Blo 690315 2965709 := bstep (se 3 (by rfl) ⟨556070, by rfl⟩ : syracuseStep 2965709 = 1112141) B1112141
theorem B1065187 : Blo 690315 1065187 := bstep (se 1 (by rfl) ⟨798890, by rfl⟩ : syracuseStep 1065187 = 1597781) B1597781
theorem B5259491 : Blo 690315 5259491 := bstep (se 1 (by rfl) ⟨3944618, by rfl⟩ : syracuseStep 5259491 = 7889237) B7889237
theorem B999761 : Blo 690315 999761 := bstep (se 2 (by rfl) ⟨374910, by rfl⟩ : syracuseStep 999761 = 749821) B749821
theorem B2245069 : Blo 690315 2245069 := bstep (se 3 (by rfl) ⟨420950, by rfl⟩ : syracuseStep 2245069 = 841901) B841901
theorem B1556945 : Blo 690315 1556945 := bstep (se 2 (by rfl) ⟨583854, by rfl⟩ : syracuseStep 1556945 = 1167709) B1167709
theorem B1556963 : Blo 690315 1556963 := bstep (se 1 (by rfl) ⟨1167722, by rfl⟩ : syracuseStep 1556963 = 2335445) B2335445
theorem B738019 : Blo 690315 738019 := bstep (se 1 (by rfl) ⟨553514, by rfl⟩ : syracuseStep 738019 = 1107029) B1107029
theorem B1557233 : Blo 690315 1557233 := bstep (se 2 (by rfl) ⟨583962, by rfl⟩ : syracuseStep 1557233 = 1167925) B1167925
theorem B1557251 : Blo 690315 1557251 := bstep (se 1 (by rfl) ⟨1167938, by rfl⟩ : syracuseStep 1557251 = 2335877) B2335877
theorem B1065793 : Blo 690315 1065793 := bstep (se 2 (by rfl) ⟨399672, by rfl⟩ : syracuseStep 1065793 = 799345) B799345
theorem B2245475 : Blo 690315 2245475 := bstep (se 1 (by rfl) ⟨1684106, by rfl⟩ : syracuseStep 2245475 = 3368213) B3368213
theorem B6669155 : Blo 690315 6669155 := bstep (se 1 (by rfl) ⟨5001866, by rfl⟩ : syracuseStep 6669155 = 10003733) B10003733
theorem B1196947 : Blo 690315 1196947 := bstep (se 1 (by rfl) ⟨897710, by rfl⟩ : syracuseStep 1196947 = 1795421) B1795421
theorem B2802637 : Blo 690315 2802637 := bstep (se 3 (by rfl) ⟨525494, by rfl⟩ : syracuseStep 2802637 = 1050989) B1050989
theorem B1557521 : Blo 690315 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B1557539 : Blo 690315 1557539 := bstep (se 1 (by rfl) ⟨1168154, by rfl⟩ : syracuseStep 1557539 = 2336309) B2336309
theorem B1754257 : Blo 690315 1754257 := bstep (se 2 (by rfl) ⟨657846, by rfl⟩ : syracuseStep 1754257 = 1315693) B1315693
theorem B4736261 : Blo 690315 4736261 := bstep (se 4 (by rfl) ⟨444024, by rfl⟩ : syracuseStep 4736261 = 888049) B888049
theorem B1557809 : Blo 690315 1557809 := bstep (se 2 (by rfl) ⟨584178, by rfl⟩ : syracuseStep 1557809 = 1168357) B1168357
theorem B1557827 : Blo 690315 1557827 := bstep (se 1 (by rfl) ⟨1168370, by rfl⟩ : syracuseStep 1557827 = 2336741) B2336741
theorem B1754531 : Blo 690315 1754531 := bstep (se 1 (by rfl) ⟨1315898, by rfl⟩ : syracuseStep 1754531 = 2631797) B2631797
theorem B15943139 : Blo 690315 15943139 := bstep (se 1 (by rfl) ⟨11957354, by rfl⟩ : syracuseStep 15943139 = 23914709) B23914709
theorem B1558097 : Blo 690315 1558097 := bstep (se 2 (by rfl) ⟨584286, by rfl⟩ : syracuseStep 1558097 = 1168573) B1168573
theorem B1558115 : Blo 690315 1558115 := bstep (se 1 (by rfl) ⟨1168586, by rfl⟩ : syracuseStep 1558115 = 2337173) B2337173
theorem B1754723 : Blo 690315 1754723 := bstep (se 1 (by rfl) ⟨1316042, by rfl⟩ : syracuseStep 1754723 = 2632085) B2632085
theorem B2213507 : Blo 690315 2213507 := bstep (se 1 (by rfl) ⟨1660130, by rfl⟩ : syracuseStep 2213507 = 3320261) B3320261
theorem B1165009 : Blo 690315 1165009 := bstep (se 2 (by rfl) ⟨436878, by rfl⟩ : syracuseStep 1165009 = 873757) B873757
theorem B1165043 : Blo 690315 1165043 := bstep (se 1 (by rfl) ⟨873782, by rfl⟩ : syracuseStep 1165043 = 1747565) B1747565
theorem B1558385 : Blo 690315 1558385 := bstep (se 2 (by rfl) ⟨584394, by rfl⟩ : syracuseStep 1558385 = 1168789) B1168789
theorem B1165171 : Blo 690315 1165171 := bstep (se 1 (by rfl) ⟨873878, by rfl⟩ : syracuseStep 1165171 = 1747757) B1747757
theorem B1558403 : Blo 690315 1558403 := bstep (se 1 (by rfl) ⟨1168802, by rfl⟩ : syracuseStep 1558403 = 2337605) B2337605
theorem B1165313 : Blo 690315 1165313 := bstep (se 2 (by rfl) ⟨436992, by rfl⟩ : syracuseStep 1165313 = 873985) B873985
theorem B11225141 : Blo 690315 11225141 := bstep (se 5 (by rfl) ⟨526178, by rfl⟩ : syracuseStep 11225141 = 1052357) B1052357
theorem B739411 : Blo 690315 739411 := bstep (se 1 (by rfl) ⟨554558, by rfl⟩ : syracuseStep 739411 = 1109117) B1109117
theorem B3786851 : Blo 690315 3786851 := bstep (se 1 (by rfl) ⟨2840138, by rfl⟩ : syracuseStep 3786851 = 5680277) B5680277
theorem B53889137 : Blo 690315 53889137 := bstep (se 2 (by rfl) ⟨20208426, by rfl⟩ : syracuseStep 53889137 = 40416853) B40416853
theorem B1165441 : Blo 690315 1165441 := bstep (se 2 (by rfl) ⟨437040, by rfl⟩ : syracuseStep 1165441 = 874081) B874081
theorem B1558673 : Blo 690315 1558673 := bstep (se 2 (by rfl) ⟨584502, by rfl⟩ : syracuseStep 1558673 = 1169005) B1169005
theorem B1165475 : Blo 690315 1165475 := bstep (se 1 (by rfl) ⟨874106, by rfl⟩ : syracuseStep 1165475 = 1748213) B1748213
theorem B1558691 : Blo 690315 1558691 := bstep (se 1 (by rfl) ⟨1169018, by rfl⟩ : syracuseStep 1558691 = 2338037) B2338037
theorem B5327045 : Blo 690315 5327045 := bstep (se 4 (by rfl) ⟨499410, by rfl⟩ : syracuseStep 5327045 = 998821) B998821
theorem B3786979 : Blo 690315 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B1165603 : Blo 690315 1165603 := bstep (se 1 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 1165603 = 1748405) B1748405
theorem B936289 : Blo 690315 936289 := bstep (se 2 (by rfl) ⟨351108, by rfl⟩ : syracuseStep 936289 = 702217) B702217
theorem B1165745 : Blo 690315 1165745 := bstep (se 2 (by rfl) ⟨437154, by rfl⟩ : syracuseStep 1165745 = 874309) B874309
theorem B1558961 : Blo 690315 1558961 := bstep (se 2 (by rfl) ⟨584610, by rfl⟩ : syracuseStep 1558961 = 1169221) B1169221
theorem B1558979 : Blo 690315 1558979 := bstep (se 1 (by rfl) ⟨1169234, by rfl⟩ : syracuseStep 1558979 = 2338469) B2338469
theorem B3951089 : Blo 690315 3951089 := bstep (se 2 (by rfl) ⟨1481658, by rfl⟩ : syracuseStep 3951089 = 2963317) B2963317
theorem B1755665 : Blo 690315 1755665 := bstep (se 2 (by rfl) ⟨658374, by rfl⟩ : syracuseStep 1755665 = 1316749) B1316749
theorem B1165873 : Blo 690315 1165873 := bstep (se 2 (by rfl) ⟨437202, by rfl⟩ : syracuseStep 1165873 = 874405) B874405
theorem B1755715 : Blo 690315 1755715 := bstep (se 1 (by rfl) ⟨1316786, by rfl⟩ : syracuseStep 1755715 = 2633573) B2633573
theorem B1165907 : Blo 690315 1165907 := bstep (se 1 (by rfl) ⟨874430, by rfl⟩ : syracuseStep 1165907 = 1748861) B1748861
theorem B7883405 : Blo 690315 7883405 := bstep (se 3 (by rfl) ⟨1478138, by rfl⟩ : syracuseStep 7883405 = 2956277) B2956277
theorem B1559249 : Blo 690315 1559249 := bstep (se 2 (by rfl) ⟨584718, by rfl⟩ : syracuseStep 1559249 = 1169437) B1169437
theorem B1755857 : Blo 690315 1755857 := bstep (se 2 (by rfl) ⟨658446, by rfl⟩ : syracuseStep 1755857 = 1316893) B1316893
theorem B1166035 : Blo 690315 1166035 := bstep (se 1 (by rfl) ⟨874526, by rfl⟩ : syracuseStep 1166035 = 1749053) B1749053
theorem B1559267 : Blo 690315 1559267 := bstep (se 1 (by rfl) ⟨1169450, by rfl⟩ : syracuseStep 1559267 = 2338901) B2338901
theorem B936769 : Blo 690315 936769 := bstep (se 2 (by rfl) ⟨351288, by rfl⟩ : syracuseStep 936769 = 702577) B702577
theorem B1166177 : Blo 690315 1166177 := bstep (se 2 (by rfl) ⟨437316, by rfl⟩ : syracuseStep 1166177 = 874633) B874633
theorem B1166305 : Blo 690315 1166305 := bstep (se 2 (by rfl) ⟨437364, by rfl⟩ : syracuseStep 1166305 = 874729) B874729
theorem B1559537 : Blo 690315 1559537 := bstep (se 2 (by rfl) ⟨584826, by rfl⟩ : syracuseStep 1559537 = 1169653) B1169653
theorem B1166339 : Blo 690315 1166339 := bstep (se 1 (by rfl) ⟨874754, by rfl⟩ : syracuseStep 1166339 = 1749509) B1749509
theorem B1559555 : Blo 690315 1559555 := bstep (se 1 (by rfl) ⟨1169666, by rfl⟩ : syracuseStep 1559555 = 2339333) B2339333
theorem B1166467 : Blo 690315 1166467 := bstep (se 1 (by rfl) ⟨874850, by rfl⟩ : syracuseStep 1166467 = 1749701) B1749701
theorem B1035473 : Blo 690315 1035473 := bstep (se 2 (by rfl) ⟨388302, by rfl⟩ : syracuseStep 1035473 = 776605) B776605
theorem B1035491 : Blo 690315 1035491 := bstep (se 1 (by rfl) ⟨776618, by rfl⟩ : syracuseStep 1035491 = 1553237) B1553237
theorem B1035521 : Blo 690315 1035521 := bstep (se 2 (by rfl) ⟨388320, by rfl⟩ : syracuseStep 1035521 = 776641) B776641
theorem B1166609 : Blo 690315 1166609 := bstep (se 2 (by rfl) ⟨437478, by rfl⟩ : syracuseStep 1166609 = 874957) B874957
theorem B1559825 : Blo 690315 1559825 := bstep (se 2 (by rfl) ⟨584934, by rfl⟩ : syracuseStep 1559825 = 1169869) B1169869
theorem B1035539 : Blo 690315 1035539 := bstep (se 1 (by rfl) ⟨776654, by rfl⟩ : syracuseStep 1035539 = 1553309) B1553309
theorem B1559843 : Blo 690315 1559843 := bstep (se 1 (by rfl) ⟨1169882, by rfl⟩ : syracuseStep 1559843 = 2339765) B2339765
theorem B1035569 : Blo 690315 1035569 := bstep (se 2 (by rfl) ⟨388338, by rfl⟩ : syracuseStep 1035569 = 776677) B776677
theorem B1035587 : Blo 690315 1035587 := bstep (se 1 (by rfl) ⟨776690, by rfl⟩ : syracuseStep 1035587 = 1553381) B1553381
theorem B1035617 : Blo 690315 1035617 := bstep (se 2 (by rfl) ⟨388356, by rfl⟩ : syracuseStep 1035617 = 776713) B776713
theorem B1035635 : Blo 690315 1035635 := bstep (se 1 (by rfl) ⟨776726, by rfl⟩ : syracuseStep 1035635 = 1553453) B1553453
theorem B1035665 : Blo 690315 1035665 := bstep (se 2 (by rfl) ⟨388374, by rfl⟩ : syracuseStep 1035665 = 776749) B776749
theorem B1166737 : Blo 690315 1166737 := bstep (se 2 (by rfl) ⟨437526, by rfl⟩ : syracuseStep 1166737 = 875053) B875053
theorem B2215313 : Blo 690315 2215313 := bstep (se 2 (by rfl) ⟨830742, by rfl⟩ : syracuseStep 2215313 = 1661485) B1661485
theorem B1035683 : Blo 690315 1035683 := bstep (se 1 (by rfl) ⟨776762, by rfl⟩ : syracuseStep 1035683 = 1553525) B1553525
theorem B1166771 : Blo 690315 1166771 := bstep (se 1 (by rfl) ⟨875078, by rfl⟩ : syracuseStep 1166771 = 1750157) B1750157
theorem B1035713 : Blo 690315 1035713 := bstep (se 2 (by rfl) ⟨388392, by rfl⟩ : syracuseStep 1035713 = 776785) B776785
theorem B2215363 : Blo 690315 2215363 := bstep (se 1 (by rfl) ⟨1661522, by rfl⟩ : syracuseStep 2215363 = 3323045) B3323045
theorem B1035731 : Blo 690315 1035731 := bstep (se 1 (by rfl) ⟨776798, by rfl⟩ : syracuseStep 1035731 = 1553597) B1553597
theorem B4443619 : Blo 690315 4443619 := bstep (se 1 (by rfl) ⟨3332714, by rfl⟩ : syracuseStep 4443619 = 6665429) B6665429
theorem B1035761 : Blo 690315 1035761 := bstep (se 2 (by rfl) ⟨388410, by rfl⟩ : syracuseStep 1035761 = 776821) B776821
theorem B1035779 : Blo 690315 1035779 := bstep (se 1 (by rfl) ⟨776834, by rfl⟩ : syracuseStep 1035779 = 1553669) B1553669
theorem B1035809 : Blo 690315 1035809 := bstep (se 2 (by rfl) ⟨388428, by rfl⟩ : syracuseStep 1035809 = 776857) B776857
theorem B1560113 : Blo 690315 1560113 := bstep (se 2 (by rfl) ⟨585042, by rfl⟩ : syracuseStep 1560113 = 1170085) B1170085
theorem B1035827 : Blo 690315 1035827 := bstep (se 1 (by rfl) ⟨776870, by rfl⟩ : syracuseStep 1035827 = 1553741) B1553741
theorem B1166899 : Blo 690315 1166899 := bstep (se 1 (by rfl) ⟨875174, by rfl⟩ : syracuseStep 1166899 = 1750349) B1750349
theorem B1560131 : Blo 690315 1560131 := bstep (se 1 (by rfl) ⟨1170098, by rfl⟩ : syracuseStep 1560131 = 2340197) B2340197
theorem B1035857 : Blo 690315 1035857 := bstep (se 2 (by rfl) ⟨388446, by rfl⟩ : syracuseStep 1035857 = 776893) B776893
theorem B1035875 : Blo 690315 1035875 := bstep (se 1 (by rfl) ⟨776906, by rfl⟩ : syracuseStep 1035875 = 1553813) B1553813
theorem B1035905 : Blo 690315 1035905 := bstep (se 2 (by rfl) ⟨388464, by rfl⟩ : syracuseStep 1035905 = 776929) B776929
theorem B1035923 : Blo 690315 1035923 := bstep (se 1 (by rfl) ⟨776942, by rfl⟩ : syracuseStep 1035923 = 1553885) B1553885
theorem B1035953 : Blo 690315 1035953 := bstep (se 2 (by rfl) ⟨388482, by rfl⟩ : syracuseStep 1035953 = 776965) B776965
theorem B1756849 : Blo 690315 1756849 := bstep (se 2 (by rfl) ⟨658818, by rfl⟩ : syracuseStep 1756849 = 1317637) B1317637
theorem B1167041 : Blo 690315 1167041 := bstep (se 2 (by rfl) ⟨437640, by rfl⟩ : syracuseStep 1167041 = 875281) B875281
theorem B1035971 : Blo 690315 1035971 := bstep (se 1 (by rfl) ⟨776978, by rfl⟩ : syracuseStep 1035971 = 1553957) B1553957
theorem B1036001 : Blo 690315 1036001 := bstep (se 2 (by rfl) ⟨388500, by rfl⟩ : syracuseStep 1036001 = 777001) B777001
theorem B8867555 : Blo 690315 8867555 := bstep (se 1 (by rfl) ⟨6650666, by rfl⟩ : syracuseStep 8867555 = 13301333) B13301333
theorem B937699 : Blo 690315 937699 := bstep (se 1 (by rfl) ⟨703274, by rfl⟩ : syracuseStep 937699 = 1406549) B1406549
theorem B1036019 : Blo 690315 1036019 := bstep (se 1 (by rfl) ⟨777014, by rfl⟩ : syracuseStep 1036019 = 1554029) B1554029
theorem B1036049 : Blo 690315 1036049 := bstep (se 2 (by rfl) ⟨388518, by rfl⟩ : syracuseStep 1036049 = 777037) B777037
theorem B1036067 : Blo 690315 1036067 := bstep (se 1 (by rfl) ⟨777050, by rfl⟩ : syracuseStep 1036067 = 1554101) B1554101
theorem B1036097 : Blo 690315 1036097 := bstep (se 2 (by rfl) ⟨388536, by rfl⟩ : syracuseStep 1036097 = 777073) B777073
theorem B1167169 : Blo 690315 1167169 := bstep (se 2 (by rfl) ⟨437688, by rfl⟩ : syracuseStep 1167169 = 875377) B875377
theorem B1560401 : Blo 690315 1560401 := bstep (se 2 (by rfl) ⟨585150, by rfl⟩ : syracuseStep 1560401 = 1170301) B1170301
theorem B1036115 : Blo 690315 1036115 := bstep (se 1 (by rfl) ⟨777086, by rfl⟩ : syracuseStep 1036115 = 1554173) B1554173
theorem B1560419 : Blo 690315 1560419 := bstep (se 1 (by rfl) ⟨1170314, by rfl⟩ : syracuseStep 1560419 = 2340629) B2340629
theorem B1167203 : Blo 690315 1167203 := bstep (se 1 (by rfl) ⟨875402, by rfl⟩ : syracuseStep 1167203 = 1750805) B1750805
theorem B1036145 : Blo 690315 1036145 := bstep (se 2 (by rfl) ⟨388554, by rfl⟩ : syracuseStep 1036145 = 777109) B777109
theorem B1036163 : Blo 690315 1036163 := bstep (se 1 (by rfl) ⟨777122, by rfl⟩ : syracuseStep 1036163 = 1554245) B1554245
theorem B1036193 : Blo 690315 1036193 := bstep (se 2 (by rfl) ⟨388572, by rfl⟩ : syracuseStep 1036193 = 777145) B777145
theorem B3952547 : Blo 690315 3952547 := bstep (se 1 (by rfl) ⟨2964410, by rfl⟩ : syracuseStep 3952547 = 5928821) B5928821
theorem B1036211 : Blo 690315 1036211 := bstep (se 1 (by rfl) ⟨777158, by rfl⟩ : syracuseStep 1036211 = 1554317) B1554317
theorem B1757123 : Blo 690315 1757123 := bstep (se 1 (by rfl) ⟨1317842, by rfl⟩ : syracuseStep 1757123 = 2635685) B2635685
theorem B1036241 : Blo 690315 1036241 := bstep (se 2 (by rfl) ⟨388590, by rfl⟩ : syracuseStep 1036241 = 777181) B777181
theorem B1036259 : Blo 690315 1036259 := bstep (se 1 (by rfl) ⟨777194, by rfl⟩ : syracuseStep 1036259 = 1554389) B1554389
theorem B1167331 : Blo 690315 1167331 := bstep (se 1 (by rfl) ⟨875498, by rfl⟩ : syracuseStep 1167331 = 1750997) B1750997
theorem B1036289 : Blo 690315 1036289 := bstep (se 2 (by rfl) ⟨388608, by rfl⟩ : syracuseStep 1036289 = 777217) B777217
theorem B1036307 : Blo 690315 1036307 := bstep (se 1 (by rfl) ⟨777230, by rfl⟩ : syracuseStep 1036307 = 1554461) B1554461
theorem B1036337 : Blo 690315 1036337 := bstep (se 2 (by rfl) ⟨388626, by rfl⟩ : syracuseStep 1036337 = 777253) B777253
theorem B1036355 : Blo 690315 1036355 := bstep (se 1 (by rfl) ⟨777266, by rfl⟩ : syracuseStep 1036355 = 1554533) B1554533
theorem B1036385 : Blo 690315 1036385 := bstep (se 2 (by rfl) ⟨388644, by rfl⟩ : syracuseStep 1036385 = 777289) B777289
theorem B1167473 : Blo 690315 1167473 := bstep (se 2 (by rfl) ⟨437802, by rfl⟩ : syracuseStep 1167473 = 875605) B875605
theorem B1560689 : Blo 690315 1560689 := bstep (se 2 (by rfl) ⟨585258, by rfl⟩ : syracuseStep 1560689 = 1170517) B1170517
theorem B1036403 : Blo 690315 1036403 := bstep (se 1 (by rfl) ⟨777302, by rfl⟩ : syracuseStep 1036403 = 1554605) B1554605
theorem B1560707 : Blo 690315 1560707 := bstep (se 1 (by rfl) ⟨1170530, by rfl⟩ : syracuseStep 1560707 = 2341061) B2341061
theorem B1757315 : Blo 690315 1757315 := bstep (se 1 (by rfl) ⟨1317986, by rfl⟩ : syracuseStep 1757315 = 2635973) B2635973
theorem B1036433 : Blo 690315 1036433 := bstep (se 2 (by rfl) ⟨388662, by rfl⟩ : syracuseStep 1036433 = 777325) B777325
theorem B2216081 : Blo 690315 2216081 := bstep (se 2 (by rfl) ⟨831030, by rfl⟩ : syracuseStep 2216081 = 1662061) B1662061
theorem B1036451 : Blo 690315 1036451 := bstep (se 1 (by rfl) ⟨777338, by rfl⟩ : syracuseStep 1036451 = 1554677) B1554677
theorem B1036481 : Blo 690315 1036481 := bstep (se 2 (by rfl) ⟨388680, by rfl⟩ : syracuseStep 1036481 = 777361) B777361
theorem B1036499 : Blo 690315 1036499 := bstep (se 1 (by rfl) ⟨777374, by rfl⟩ : syracuseStep 1036499 = 1554749) B1554749
theorem B1036529 : Blo 690315 1036529 := bstep (se 2 (by rfl) ⟨388698, by rfl⟩ : syracuseStep 1036529 = 777397) B777397
theorem B1167601 : Blo 690315 1167601 := bstep (se 2 (by rfl) ⟨437850, by rfl⟩ : syracuseStep 1167601 = 875701) B875701
theorem B1036547 : Blo 690315 1036547 := bstep (se 1 (by rfl) ⟨777410, by rfl⟩ : syracuseStep 1036547 = 1554821) B1554821
theorem B1167635 : Blo 690315 1167635 := bstep (se 1 (by rfl) ⟨875726, by rfl⟩ : syracuseStep 1167635 = 1751453) B1751453
theorem B1036577 : Blo 690315 1036577 := bstep (se 2 (by rfl) ⟨388716, by rfl⟩ : syracuseStep 1036577 = 777433) B777433
theorem B1331491 : Blo 690315 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B1036595 : Blo 690315 1036595 := bstep (se 1 (by rfl) ⟨777446, by rfl⟩ : syracuseStep 1036595 = 1554893) B1554893
theorem B1036625 : Blo 690315 1036625 := bstep (se 2 (by rfl) ⟨388734, by rfl⟩ : syracuseStep 1036625 = 777469) B777469
theorem B1036643 : Blo 690315 1036643 := bstep (se 1 (by rfl) ⟨777482, by rfl⟩ : syracuseStep 1036643 = 1554965) B1554965
theorem B1036673 : Blo 690315 1036673 := bstep (se 2 (by rfl) ⟨388752, by rfl⟩ : syracuseStep 1036673 = 777505) B777505
theorem B1560977 : Blo 690315 1560977 := bstep (se 2 (by rfl) ⟨585366, by rfl⟩ : syracuseStep 1560977 = 1170733) B1170733
theorem B1036691 : Blo 690315 1036691 := bstep (se 1 (by rfl) ⟨777518, by rfl⟩ : syracuseStep 1036691 = 1555037) B1555037
theorem B1167763 : Blo 690315 1167763 := bstep (se 1 (by rfl) ⟨875822, by rfl⟩ : syracuseStep 1167763 = 1751645) B1751645
theorem B3330467 : Blo 690315 3330467 := bstep (se 1 (by rfl) ⟨2497850, by rfl⟩ : syracuseStep 3330467 = 4995701) B4995701
theorem B1560995 : Blo 690315 1560995 := bstep (se 1 (by rfl) ⟨1170746, by rfl⟩ : syracuseStep 1560995 = 2341493) B2341493
theorem B1036721 : Blo 690315 1036721 := bstep (se 2 (by rfl) ⟨388770, by rfl⟩ : syracuseStep 1036721 = 777541) B777541
theorem B1036739 : Blo 690315 1036739 := bstep (se 1 (by rfl) ⟨777554, by rfl⟩ : syracuseStep 1036739 = 1555109) B1555109
theorem B1036769 : Blo 690315 1036769 := bstep (se 2 (by rfl) ⟨388788, by rfl⟩ : syracuseStep 1036769 = 777577) B777577
theorem B1036787 : Blo 690315 1036787 := bstep (se 1 (by rfl) ⟨777590, by rfl⟩ : syracuseStep 1036787 = 1555181) B1555181
theorem B1036817 : Blo 690315 1036817 := bstep (se 2 (by rfl) ⟨388806, by rfl⟩ : syracuseStep 1036817 = 777613) B777613
theorem B1167905 : Blo 690315 1167905 := bstep (se 2 (by rfl) ⟨437964, by rfl⟩ : syracuseStep 1167905 = 875929) B875929
theorem B1036835 : Blo 690315 1036835 := bstep (se 1 (by rfl) ⟨777626, by rfl⟩ : syracuseStep 1036835 = 1555253) B1555253
theorem B1036865 : Blo 690315 1036865 := bstep (se 2 (by rfl) ⟨388824, by rfl⟩ : syracuseStep 1036865 = 777649) B777649
theorem B1036883 : Blo 690315 1036883 := bstep (se 1 (by rfl) ⟨777662, by rfl⟩ : syracuseStep 1036883 = 1555325) B1555325
theorem B1036913 : Blo 690315 1036913 := bstep (se 2 (by rfl) ⟨388842, by rfl⟩ : syracuseStep 1036913 = 777685) B777685
theorem B1036931 : Blo 690315 1036931 := bstep (se 1 (by rfl) ⟨777698, by rfl⟩ : syracuseStep 1036931 = 1555397) B1555397
theorem B2216593 : Blo 690315 2216593 := bstep (se 2 (by rfl) ⟨831222, by rfl⟩ : syracuseStep 2216593 = 1662445) B1662445
theorem B1036961 : Blo 690315 1036961 := bstep (se 2 (by rfl) ⟨388860, by rfl⟩ : syracuseStep 1036961 = 777721) B777721
theorem B1168033 : Blo 690315 1168033 := bstep (se 2 (by rfl) ⟨438012, by rfl⟩ : syracuseStep 1168033 = 876025) B876025
theorem B1561265 : Blo 690315 1561265 := bstep (se 2 (by rfl) ⟨585474, by rfl⟩ : syracuseStep 1561265 = 1170949) B1170949
theorem B1036979 : Blo 690315 1036979 := bstep (se 1 (by rfl) ⟨777734, by rfl⟩ : syracuseStep 1036979 = 1555469) B1555469
theorem B1168067 : Blo 690315 1168067 := bstep (se 1 (by rfl) ⟨876050, by rfl⟩ : syracuseStep 1168067 = 1752101) B1752101
theorem B1561283 : Blo 690315 1561283 := bstep (se 1 (by rfl) ⟨1170962, by rfl⟩ : syracuseStep 1561283 = 2341925) B2341925
theorem B6640325 : Blo 690315 6640325 := bstep (se 4 (by rfl) ⟨622530, by rfl⟩ : syracuseStep 6640325 = 1245061) B1245061
theorem B1037009 : Blo 690315 1037009 := bstep (se 2 (by rfl) ⟨388878, by rfl⟩ : syracuseStep 1037009 = 777757) B777757
theorem B1037027 : Blo 690315 1037027 := bstep (se 1 (by rfl) ⟨777770, by rfl⟩ : syracuseStep 1037027 = 1555541) B1555541
theorem B1037057 : Blo 690315 1037057 := bstep (se 2 (by rfl) ⟨388896, by rfl⟩ : syracuseStep 1037057 = 777793) B777793
theorem B1037075 : Blo 690315 1037075 := bstep (se 1 (by rfl) ⟨777806, by rfl⟩ : syracuseStep 1037075 = 1555613) B1555613
theorem B1037105 : Blo 690315 1037105 := bstep (se 2 (by rfl) ⟨388914, by rfl⟩ : syracuseStep 1037105 = 777829) B777829
theorem B1037123 : Blo 690315 1037123 := bstep (se 1 (by rfl) ⟨777842, by rfl⟩ : syracuseStep 1037123 = 1555685) B1555685
theorem B1168195 : Blo 690315 1168195 := bstep (se 1 (by rfl) ⟨876146, by rfl⟩ : syracuseStep 1168195 = 1752293) B1752293
theorem B1037153 : Blo 690315 1037153 := bstep (se 2 (by rfl) ⟨388932, by rfl⟩ : syracuseStep 1037153 = 777865) B777865
theorem B1037171 : Blo 690315 1037171 := bstep (se 1 (by rfl) ⟨777878, by rfl⟩ : syracuseStep 1037171 = 1555757) B1555757
theorem B3953549 : Blo 690315 3953549 := bstep (se 3 (by rfl) ⟨741290, by rfl⟩ : syracuseStep 3953549 = 1482581) B1482581
theorem B1659793 : Blo 690315 1659793 := bstep (se 2 (by rfl) ⟨622422, by rfl⟩ : syracuseStep 1659793 = 1244845) B1244845
theorem B1037201 : Blo 690315 1037201 := bstep (se 2 (by rfl) ⟨388950, by rfl⟩ : syracuseStep 1037201 = 777901) B777901
theorem B1037219 : Blo 690315 1037219 := bstep (se 1 (by rfl) ⟨777914, by rfl⟩ : syracuseStep 1037219 = 1555829) B1555829
theorem B1037249 : Blo 690315 1037249 := bstep (se 2 (by rfl) ⟨388968, by rfl⟩ : syracuseStep 1037249 = 777937) B777937
theorem B1168337 : Blo 690315 1168337 := bstep (se 2 (by rfl) ⟨438126, by rfl⟩ : syracuseStep 1168337 = 876253) B876253
theorem B1561553 : Blo 690315 1561553 := bstep (se 2 (by rfl) ⟨585582, by rfl⟩ : syracuseStep 1561553 = 1171165) B1171165
theorem B1037267 : Blo 690315 1037267 := bstep (se 1 (by rfl) ⟨777950, by rfl⟩ : syracuseStep 1037267 = 1555901) B1555901
theorem B1561571 : Blo 690315 1561571 := bstep (se 1 (by rfl) ⟨1171178, by rfl⟩ : syracuseStep 1561571 = 2342357) B2342357
theorem B1037297 : Blo 690315 1037297 := bstep (se 2 (by rfl) ⟨388986, by rfl⟩ : syracuseStep 1037297 = 777973) B777973
theorem B1037315 : Blo 690315 1037315 := bstep (se 1 (by rfl) ⟨777986, by rfl⟩ : syracuseStep 1037315 = 1555973) B1555973
theorem B1037345 : Blo 690315 1037345 := bstep (se 2 (by rfl) ⟨389004, by rfl⟩ : syracuseStep 1037345 = 778009) B778009
theorem B1037363 : Blo 690315 1037363 := bstep (se 1 (by rfl) ⟨778022, by rfl⟩ : syracuseStep 1037363 = 1556045) B1556045
theorem B1037393 : Blo 690315 1037393 := bstep (se 2 (by rfl) ⟨389022, by rfl⟩ : syracuseStep 1037393 = 778045) B778045
theorem B1168465 : Blo 690315 1168465 := bstep (se 2 (by rfl) ⟨438174, by rfl⟩ : syracuseStep 1168465 = 876349) B876349
theorem B1037411 : Blo 690315 1037411 := bstep (se 1 (by rfl) ⟨778058, by rfl⟩ : syracuseStep 1037411 = 1556117) B1556117
theorem B1168499 : Blo 690315 1168499 := bstep (se 1 (by rfl) ⟨876374, by rfl⟩ : syracuseStep 1168499 = 1752749) B1752749
theorem B1037441 : Blo 690315 1037441 := bstep (se 2 (by rfl) ⟨389040, by rfl⟩ : syracuseStep 1037441 = 778081) B778081
theorem B1037459 : Blo 690315 1037459 := bstep (se 1 (by rfl) ⟨778094, by rfl⟩ : syracuseStep 1037459 = 1556189) B1556189
theorem B1037489 : Blo 690315 1037489 := bstep (se 2 (by rfl) ⟨389058, by rfl⟩ : syracuseStep 1037489 = 778117) B778117
theorem B1037507 : Blo 690315 1037507 := bstep (se 1 (by rfl) ⟨778130, by rfl⟩ : syracuseStep 1037507 = 1556261) B1556261
theorem B1037537 : Blo 690315 1037537 := bstep (se 2 (by rfl) ⟨389076, by rfl⟩ : syracuseStep 1037537 = 778153) B778153
theorem B4216049 : Blo 690315 4216049 := bstep (se 2 (by rfl) ⟨1581018, by rfl⟩ : syracuseStep 4216049 = 3162037) B3162037
theorem B1561841 : Blo 690315 1561841 := bstep (se 2 (by rfl) ⟨585690, by rfl⟩ : syracuseStep 1561841 = 1171381) B1171381
theorem B1037555 : Blo 690315 1037555 := bstep (se 1 (by rfl) ⟨778166, by rfl⟩ : syracuseStep 1037555 = 1556333) B1556333
theorem B1168627 : Blo 690315 1168627 := bstep (se 1 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 1168627 = 1752941) B1752941
theorem B1561859 : Blo 690315 1561859 := bstep (se 1 (by rfl) ⟨1171394, by rfl⟩ : syracuseStep 1561859 = 2342789) B2342789
theorem B1037585 : Blo 690315 1037585 := bstep (se 2 (by rfl) ⟨389094, by rfl⟩ : syracuseStep 1037585 = 778189) B778189
theorem B1037603 : Blo 690315 1037603 := bstep (se 1 (by rfl) ⟨778202, by rfl⟩ : syracuseStep 1037603 = 1556405) B1556405
theorem B1037633 : Blo 690315 1037633 := bstep (se 2 (by rfl) ⟨389112, by rfl⟩ : syracuseStep 1037633 = 778225) B778225
theorem B1037651 : Blo 690315 1037651 := bstep (se 1 (by rfl) ⟨778238, by rfl⟩ : syracuseStep 1037651 = 1556477) B1556477
theorem B1037681 : Blo 690315 1037681 := bstep (se 2 (by rfl) ⟨389130, by rfl⟩ : syracuseStep 1037681 = 778261) B778261
theorem B1168769 : Blo 690315 1168769 := bstep (se 2 (by rfl) ⟨438288, by rfl⟩ : syracuseStep 1168769 = 876577) B876577
theorem B1037699 : Blo 690315 1037699 := bstep (se 1 (by rfl) ⟨778274, by rfl⟩ : syracuseStep 1037699 = 1556549) B1556549
theorem B1037729 : Blo 690315 1037729 := bstep (se 2 (by rfl) ⟨389148, by rfl⟩ : syracuseStep 1037729 = 778297) B778297
theorem B1037747 : Blo 690315 1037747 := bstep (se 1 (by rfl) ⟨778310, by rfl⟩ : syracuseStep 1037747 = 1556621) B1556621
theorem B5264837 : Blo 690315 5264837 := bstep (se 4 (by rfl) ⟨493578, by rfl⟩ : syracuseStep 5264837 = 987157) B987157
theorem B1037777 : Blo 690315 1037777 := bstep (se 2 (by rfl) ⟨389166, by rfl⟩ : syracuseStep 1037777 = 778333) B778333
theorem B1037795 : Blo 690315 1037795 := bstep (se 1 (by rfl) ⟨778346, by rfl⟩ : syracuseStep 1037795 = 1556693) B1556693
theorem B7886321 : Blo 690315 7886321 := bstep (se 2 (by rfl) ⟨2957370, by rfl⟩ : syracuseStep 7886321 = 5914741) B5914741
theorem B1037825 : Blo 690315 1037825 := bstep (se 2 (by rfl) ⟨389184, by rfl⟩ : syracuseStep 1037825 = 778369) B778369
theorem B1168897 : Blo 690315 1168897 := bstep (se 2 (by rfl) ⟨438336, by rfl⟩ : syracuseStep 1168897 = 876673) B876673
theorem B1562129 : Blo 690315 1562129 := bstep (se 2 (by rfl) ⟨585798, by rfl⟩ : syracuseStep 1562129 = 1171597) B1171597
theorem B1037843 : Blo 690315 1037843 := bstep (se 1 (by rfl) ⟨778382, by rfl⟩ : syracuseStep 1037843 = 1556765) B1556765
theorem B1168931 : Blo 690315 1168931 := bstep (se 1 (by rfl) ⟨876698, by rfl⟩ : syracuseStep 1168931 = 1753397) B1753397
theorem B1562147 : Blo 690315 1562147 := bstep (se 1 (by rfl) ⟨1171610, by rfl⟩ : syracuseStep 1562147 = 2343221) B2343221
theorem B3495473 : Blo 690315 3495473 := bstep (se 2 (by rfl) ⟨1310802, by rfl⟩ : syracuseStep 3495473 = 2621605) B2621605
theorem B1037873 : Blo 690315 1037873 := bstep (se 2 (by rfl) ⟨389202, by rfl⟩ : syracuseStep 1037873 = 778405) B778405
theorem B1037891 : Blo 690315 1037891 := bstep (se 1 (by rfl) ⟨778418, by rfl⟩ : syracuseStep 1037891 = 1556837) B1556837
theorem B1037921 : Blo 690315 1037921 := bstep (se 2 (by rfl) ⟨389220, by rfl⟩ : syracuseStep 1037921 = 778441) B778441
theorem B1037939 : Blo 690315 1037939 := bstep (se 1 (by rfl) ⟨778454, by rfl⟩ : syracuseStep 1037939 = 1556909) B1556909
theorem B1037969 : Blo 690315 1037969 := bstep (se 2 (by rfl) ⟨389238, by rfl⟩ : syracuseStep 1037969 = 778477) B778477
theorem B874147 : Blo 690315 874147 := bstep (se 1 (by rfl) ⟨655610, by rfl⟩ : syracuseStep 874147 = 1311221) B1311221
theorem B1037987 : Blo 690315 1037987 := bstep (se 1 (by rfl) ⟨778490, by rfl⟩ : syracuseStep 1037987 = 1556981) B1556981
theorem B1169059 : Blo 690315 1169059 := bstep (se 1 (by rfl) ⟨876794, by rfl⟩ : syracuseStep 1169059 = 1753589) B1753589
theorem B1038017 : Blo 690315 1038017 := bstep (se 2 (by rfl) ⟨389256, by rfl⟩ : syracuseStep 1038017 = 778513) B778513
theorem B1038035 : Blo 690315 1038035 := bstep (se 1 (by rfl) ⟨778526, by rfl⟩ : syracuseStep 1038035 = 1557053) B1557053
theorem B2217709 : Blo 690315 2217709 := bstep (se 3 (by rfl) ⟨415820, by rfl⟩ : syracuseStep 2217709 = 831641) B831641
theorem B1038065 : Blo 690315 1038065 := bstep (se 2 (by rfl) ⟨389274, by rfl⟩ : syracuseStep 1038065 = 778549) B778549
theorem B874243 : Blo 690315 874243 := bstep (se 1 (by rfl) ⟨655682, by rfl⟩ : syracuseStep 874243 = 1311365) B1311365
theorem B1038083 : Blo 690315 1038083 := bstep (se 1 (by rfl) ⟨778562, by rfl⟩ : syracuseStep 1038083 = 1557125) B1557125
theorem B1038113 : Blo 690315 1038113 := bstep (se 2 (by rfl) ⟨389292, by rfl⟩ : syracuseStep 1038113 = 778585) B778585
theorem B2217773 : Blo 690315 2217773 := bstep (se 3 (by rfl) ⟨415832, by rfl⟩ : syracuseStep 2217773 = 831665) B831665
theorem B1169201 : Blo 690315 1169201 := bstep (se 2 (by rfl) ⟨438450, by rfl⟩ : syracuseStep 1169201 = 876901) B876901
theorem B1038131 : Blo 690315 1038131 := bstep (se 1 (by rfl) ⟨778598, by rfl⟩ : syracuseStep 1038131 = 1557197) B1557197
theorem B1038161 : Blo 690315 1038161 := bstep (se 2 (by rfl) ⟨389310, by rfl⟩ : syracuseStep 1038161 = 778621) B778621
theorem B1038179 : Blo 690315 1038179 := bstep (se 1 (by rfl) ⟨778634, by rfl⟩ : syracuseStep 1038179 = 1557269) B1557269
theorem B1038209 : Blo 690315 1038209 := bstep (se 2 (by rfl) ⟨389328, by rfl⟩ : syracuseStep 1038209 = 778657) B778657
theorem B1038227 : Blo 690315 1038227 := bstep (se 1 (by rfl) ⟨778670, by rfl⟩ : syracuseStep 1038227 = 1557341) B1557341
theorem B1038257 : Blo 690315 1038257 := bstep (se 2 (by rfl) ⟨389346, by rfl⟩ : syracuseStep 1038257 = 778693) B778693
theorem B1169329 : Blo 690315 1169329 := bstep (se 2 (by rfl) ⟨438498, by rfl⟩ : syracuseStep 1169329 = 876997) B876997
theorem B1038275 : Blo 690315 1038275 := bstep (se 1 (by rfl) ⟨778706, by rfl⟩ : syracuseStep 1038275 = 1557413) B1557413
theorem B1169363 : Blo 690315 1169363 := bstep (se 1 (by rfl) ⟨877022, by rfl⟩ : syracuseStep 1169363 = 1754045) B1754045
theorem B1038305 : Blo 690315 1038305 := bstep (se 2 (by rfl) ⟨389364, by rfl⟩ : syracuseStep 1038305 = 778729) B778729
theorem B1038323 : Blo 690315 1038323 := bstep (se 1 (by rfl) ⟨778742, by rfl⟩ : syracuseStep 1038323 = 1557485) B1557485
theorem B1038353 : Blo 690315 1038353 := bstep (se 2 (by rfl) ⟨389382, by rfl⟩ : syracuseStep 1038353 = 778765) B778765
theorem B1038371 : Blo 690315 1038371 := bstep (se 1 (by rfl) ⟨778778, by rfl⟩ : syracuseStep 1038371 = 1557557) B1557557
theorem B1038401 : Blo 690315 1038401 := bstep (se 2 (by rfl) ⟨389400, by rfl⟩ : syracuseStep 1038401 = 778801) B778801
theorem B1038419 : Blo 690315 1038419 := bstep (se 1 (by rfl) ⟨778814, by rfl⟩ : syracuseStep 1038419 = 1557629) B1557629
theorem B1169491 : Blo 690315 1169491 := bstep (se 1 (by rfl) ⟨877118, by rfl⟩ : syracuseStep 1169491 = 1754237) B1754237
theorem B1038449 : Blo 690315 1038449 := bstep (se 2 (by rfl) ⟨389418, by rfl⟩ : syracuseStep 1038449 = 778837) B778837
theorem B1038467 : Blo 690315 1038467 := bstep (se 1 (by rfl) ⟨778850, by rfl⟩ : syracuseStep 1038467 = 1557701) B1557701
theorem B1038497 : Blo 690315 1038497 := bstep (se 2 (by rfl) ⟨389436, by rfl⟩ : syracuseStep 1038497 = 778873) B778873
theorem B1038515 : Blo 690315 1038515 := bstep (se 1 (by rfl) ⟨778886, by rfl⟩ : syracuseStep 1038515 = 1557773) B1557773
theorem B4446413 : Blo 690315 4446413 := bstep (se 3 (by rfl) ⟨833702, by rfl⟩ : syracuseStep 4446413 = 1667405) B1667405
theorem B1038545 : Blo 690315 1038545 := bstep (se 2 (by rfl) ⟨389454, by rfl⟩ : syracuseStep 1038545 = 778909) B778909
theorem B1169633 : Blo 690315 1169633 := bstep (se 2 (by rfl) ⟨438612, by rfl⟩ : syracuseStep 1169633 = 877225) B877225
theorem B1038563 : Blo 690315 1038563 := bstep (se 1 (by rfl) ⟨778922, by rfl⟩ : syracuseStep 1038563 = 1557845) B1557845
theorem B1267939 : Blo 690315 1267939 := bstep (se 1 (by rfl) ⟨950954, by rfl⟩ : syracuseStep 1267939 = 1901909) B1901909
theorem B874739 : Blo 690315 874739 := bstep (se 1 (by rfl) ⟨656054, by rfl⟩ : syracuseStep 874739 = 1312109) B1312109
theorem B1038593 : Blo 690315 1038593 := bstep (se 2 (by rfl) ⟨389472, by rfl⟩ : syracuseStep 1038593 = 778945) B778945
theorem B1038611 : Blo 690315 1038611 := bstep (se 1 (by rfl) ⟨778958, by rfl⟩ : syracuseStep 1038611 = 1557917) B1557917
theorem B1038641 : Blo 690315 1038641 := bstep (se 2 (by rfl) ⟨389490, by rfl⟩ : syracuseStep 1038641 = 778981) B778981
theorem B1038659 : Blo 690315 1038659 := bstep (se 1 (by rfl) ⟨778994, by rfl⟩ : syracuseStep 1038659 = 1557989) B1557989
theorem B1038689 : Blo 690315 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B1169761 : Blo 690315 1169761 := bstep (se 2 (by rfl) ⟨438660, by rfl⟩ : syracuseStep 1169761 = 877321) B877321
theorem B3332465 : Blo 690315 3332465 := bstep (se 2 (by rfl) ⟨1249674, by rfl⟩ : syracuseStep 3332465 = 2499349) B2499349
theorem B1038707 : Blo 690315 1038707 := bstep (se 1 (by rfl) ⟨779030, by rfl⟩ : syracuseStep 1038707 = 1558061) B1558061
theorem B1497475 : Blo 690315 1497475 := bstep (se 1 (by rfl) ⟨1123106, by rfl⟩ : syracuseStep 1497475 = 2246213) B2246213
theorem B1169795 : Blo 690315 1169795 := bstep (se 1 (by rfl) ⟨877346, by rfl⟩ : syracuseStep 1169795 = 1754693) B1754693
theorem B4741517 : Blo 690315 4741517 := bstep (se 3 (by rfl) ⟨889034, by rfl⟩ : syracuseStep 4741517 = 1778069) B1778069
theorem B1038737 : Blo 690315 1038737 := bstep (se 2 (by rfl) ⟨389526, by rfl⟩ : syracuseStep 1038737 = 779053) B779053
theorem B1038755 : Blo 690315 1038755 := bstep (se 1 (by rfl) ⟨779066, by rfl⟩ : syracuseStep 1038755 = 1558133) B1558133
theorem B1038785 : Blo 690315 1038785 := bstep (se 2 (by rfl) ⟨389544, by rfl⟩ : syracuseStep 1038785 = 779089) B779089
theorem B776659 : Blo 690315 776659 := bstep (se 1 (by rfl) ⟨582494, by rfl⟩ : syracuseStep 776659 = 1164989) B1164989
theorem B1038803 : Blo 690315 1038803 := bstep (se 1 (by rfl) ⟨779102, by rfl⟩ : syracuseStep 1038803 = 1558205) B1558205
theorem B1038833 : Blo 690315 1038833 := bstep (se 2 (by rfl) ⟨389562, by rfl⟩ : syracuseStep 1038833 = 779125) B779125
theorem B1038851 : Blo 690315 1038851 := bstep (se 1 (by rfl) ⟨779138, by rfl⟩ : syracuseStep 1038851 = 1558277) B1558277
theorem B1169923 : Blo 690315 1169923 := bstep (se 1 (by rfl) ⟨877442, by rfl⟩ : syracuseStep 1169923 = 1754885) B1754885
theorem B1038881 : Blo 690315 1038881 := bstep (se 2 (by rfl) ⟨389580, by rfl⟩ : syracuseStep 1038881 = 779161) B779161
theorem B1038899 : Blo 690315 1038899 := bstep (se 1 (by rfl) ⟨779174, by rfl⟩ : syracuseStep 1038899 = 1558349) B1558349
theorem B45439541 : Blo 690315 45439541 := bstep (se 5 (by rfl) ⟨2129978, by rfl⟩ : syracuseStep 45439541 = 4259957) B4259957
theorem B1038929 : Blo 690315 1038929 := bstep (se 2 (by rfl) ⟨389598, by rfl⟩ : syracuseStep 1038929 = 779197) B779197
theorem B776803 : Blo 690315 776803 := bstep (se 1 (by rfl) ⟨582602, by rfl⟩ : syracuseStep 776803 = 1165205) B1165205
theorem B1038947 : Blo 690315 1038947 := bstep (se 1 (by rfl) ⟨779210, by rfl⟩ : syracuseStep 1038947 = 1558421) B1558421
theorem B1038977 : Blo 690315 1038977 := bstep (se 2 (by rfl) ⟨389616, by rfl⟩ : syracuseStep 1038977 = 779233) B779233
theorem B1170065 : Blo 690315 1170065 := bstep (se 2 (by rfl) ⟨438774, by rfl⟩ : syracuseStep 1170065 = 877549) B877549
theorem B1038995 : Blo 690315 1038995 := bstep (se 1 (by rfl) ⟨779246, by rfl⟩ : syracuseStep 1038995 = 1558493) B1558493
theorem B1039025 : Blo 690315 1039025 := bstep (se 2 (by rfl) ⟨389634, by rfl⟩ : syracuseStep 1039025 = 779269) B779269
theorem B1039043 : Blo 690315 1039043 := bstep (se 1 (by rfl) ⟨779282, by rfl⟩ : syracuseStep 1039043 = 1558565) B1558565
theorem B1039073 : Blo 690315 1039073 := bstep (se 2 (by rfl) ⟨389652, by rfl⟩ : syracuseStep 1039073 = 779305) B779305
theorem B776947 : Blo 690315 776947 := bstep (se 1 (by rfl) ⟨582710, by rfl⟩ : syracuseStep 776947 = 1165421) B1165421
theorem B1039091 : Blo 690315 1039091 := bstep (se 1 (by rfl) ⟨779318, by rfl⟩ : syracuseStep 1039091 = 1558637) B1558637
theorem B1039121 : Blo 690315 1039121 := bstep (se 2 (by rfl) ⟨389670, by rfl⟩ : syracuseStep 1039121 = 779341) B779341
theorem B1170193 : Blo 690315 1170193 := bstep (se 2 (by rfl) ⟨438822, by rfl⟩ : syracuseStep 1170193 = 877645) B877645
theorem B1039139 : Blo 690315 1039139 := bstep (se 1 (by rfl) ⟨779354, by rfl⟩ : syracuseStep 1039139 = 1558709) B1558709
theorem B1170227 : Blo 690315 1170227 := bstep (se 1 (by rfl) ⟨877670, by rfl⟩ : syracuseStep 1170227 = 1755341) B1755341
theorem B1039169 : Blo 690315 1039169 := bstep (se 2 (by rfl) ⟨389688, by rfl⟩ : syracuseStep 1039169 = 779377) B779377
theorem B1039187 : Blo 690315 1039187 := bstep (se 1 (by rfl) ⟨779390, by rfl⟩ : syracuseStep 1039187 = 1558781) B1558781
theorem B1039217 : Blo 690315 1039217 := bstep (se 2 (by rfl) ⟨389706, by rfl⟩ : syracuseStep 1039217 = 779413) B779413
theorem B777091 : Blo 690315 777091 := bstep (se 1 (by rfl) ⟨582818, by rfl⟩ : syracuseStep 777091 = 1165637) B1165637
theorem B1039235 : Blo 690315 1039235 := bstep (se 1 (by rfl) ⟨779426, by rfl⟩ : syracuseStep 1039235 = 1558853) B1558853
theorem B18963341 : Blo 690315 18963341 := bstep (se 3 (by rfl) ⟨3555626, by rfl⟩ : syracuseStep 18963341 = 7111253) B7111253
theorem B1039265 : Blo 690315 1039265 := bstep (se 2 (by rfl) ⟨389724, by rfl⟩ : syracuseStep 1039265 = 779449) B779449
theorem B875443 : Blo 690315 875443 := bstep (se 1 (by rfl) ⟨656582, by rfl⟩ : syracuseStep 875443 = 1313165) B1313165
theorem B1039283 : Blo 690315 1039283 := bstep (se 1 (by rfl) ⟨779462, by rfl⟩ : syracuseStep 1039283 = 1558925) B1558925
theorem B1170355 : Blo 690315 1170355 := bstep (se 1 (by rfl) ⟨877766, by rfl⟩ : syracuseStep 1170355 = 1755533) B1755533
theorem B1039313 : Blo 690315 1039313 := bstep (se 2 (by rfl) ⟨389742, by rfl⟩ : syracuseStep 1039313 = 779485) B779485
theorem B1334225 : Blo 690315 1334225 := bstep (se 2 (by rfl) ⟨500334, by rfl⟩ : syracuseStep 1334225 = 1000669) B1000669
theorem B3496931 : Blo 690315 3496931 := bstep (se 1 (by rfl) ⟨2622698, by rfl⟩ : syracuseStep 3496931 = 5245397) B5245397
theorem B1039331 : Blo 690315 1039331 := bstep (se 1 (by rfl) ⟨779498, by rfl⟩ : syracuseStep 1039331 = 1558997) B1558997
theorem B1039361 : Blo 690315 1039361 := bstep (se 2 (by rfl) ⟨389760, by rfl⟩ : syracuseStep 1039361 = 779521) B779521
theorem B777235 : Blo 690315 777235 := bstep (se 1 (by rfl) ⟨582926, by rfl⟩ : syracuseStep 777235 = 1165853) B1165853
theorem B875539 : Blo 690315 875539 := bstep (se 1 (by rfl) ⟨656654, by rfl⟩ : syracuseStep 875539 = 1313309) B1313309
theorem B1039379 : Blo 690315 1039379 := bstep (se 1 (by rfl) ⟨779534, by rfl⟩ : syracuseStep 1039379 = 1559069) B1559069
theorem B1039409 : Blo 690315 1039409 := bstep (se 2 (by rfl) ⟨389778, by rfl⟩ : syracuseStep 1039409 = 779557) B779557
theorem B1170497 : Blo 690315 1170497 := bstep (se 2 (by rfl) ⟨438936, by rfl⟩ : syracuseStep 1170497 = 877873) B877873
theorem B1039427 : Blo 690315 1039427 := bstep (se 1 (by rfl) ⟨779570, by rfl⟩ : syracuseStep 1039427 = 1559141) B1559141
theorem B1039457 : Blo 690315 1039457 := bstep (se 2 (by rfl) ⟨389796, by rfl⟩ : syracuseStep 1039457 = 779593) B779593
theorem B1039475 : Blo 690315 1039475 := bstep (se 1 (by rfl) ⟨779606, by rfl⟩ : syracuseStep 1039475 = 1559213) B1559213
theorem B1039505 : Blo 690315 1039505 := bstep (se 2 (by rfl) ⟨389814, by rfl⟩ : syracuseStep 1039505 = 779629) B779629
theorem B777379 : Blo 690315 777379 := bstep (se 1 (by rfl) ⟨583034, by rfl⟩ : syracuseStep 777379 = 1166069) B1166069
theorem B1039523 : Blo 690315 1039523 := bstep (se 1 (by rfl) ⟨779642, by rfl⟩ : syracuseStep 1039523 = 1559285) B1559285
theorem B1039553 : Blo 690315 1039553 := bstep (se 2 (by rfl) ⟨389832, by rfl⟩ : syracuseStep 1039553 = 779665) B779665
theorem B1170625 : Blo 690315 1170625 := bstep (se 2 (by rfl) ⟨438984, by rfl⟩ : syracuseStep 1170625 = 877969) B877969
theorem B1039571 : Blo 690315 1039571 := bstep (se 1 (by rfl) ⟨779678, by rfl⟩ : syracuseStep 1039571 = 1559357) B1559357
theorem B1170659 : Blo 690315 1170659 := bstep (se 1 (by rfl) ⟨877994, by rfl⟩ : syracuseStep 1170659 = 1755989) B1755989
theorem B1039601 : Blo 690315 1039601 := bstep (se 2 (by rfl) ⟨389850, by rfl⟩ : syracuseStep 1039601 = 779701) B779701
theorem B1039619 : Blo 690315 1039619 := bstep (se 1 (by rfl) ⟨779714, by rfl⟩ : syracuseStep 1039619 = 1559429) B1559429
theorem B1039649 : Blo 690315 1039649 := bstep (se 2 (by rfl) ⟨389868, by rfl⟩ : syracuseStep 1039649 = 779737) B779737
theorem B843043 : Blo 690315 843043 := bstep (se 1 (by rfl) ⟨632282, by rfl⟩ : syracuseStep 843043 = 1264565) B1264565
theorem B777523 : Blo 690315 777523 := bstep (se 1 (by rfl) ⟨583142, by rfl⟩ : syracuseStep 777523 = 1166285) B1166285
theorem B1039667 : Blo 690315 1039667 := bstep (se 1 (by rfl) ⟨779750, by rfl⟩ : syracuseStep 1039667 = 1559501) B1559501
theorem B1039697 : Blo 690315 1039697 := bstep (se 2 (by rfl) ⟨389886, by rfl⟩ : syracuseStep 1039697 = 779773) B779773
theorem B1039715 : Blo 690315 1039715 := bstep (se 1 (by rfl) ⟨779786, by rfl⟩ : syracuseStep 1039715 = 1559573) B1559573
theorem B1170787 : Blo 690315 1170787 := bstep (se 1 (by rfl) ⟨878090, by rfl⟩ : syracuseStep 1170787 = 1756181) B1756181
theorem B1039745 : Blo 690315 1039745 := bstep (se 2 (by rfl) ⟨389904, by rfl⟩ : syracuseStep 1039745 = 779809) B779809
theorem B1039763 : Blo 690315 1039763 := bstep (se 1 (by rfl) ⟨779822, by rfl⟩ : syracuseStep 1039763 = 1559645) B1559645
theorem B1039793 : Blo 690315 1039793 := bstep (se 2 (by rfl) ⟨389922, by rfl⟩ : syracuseStep 1039793 = 779845) B779845
theorem B777667 : Blo 690315 777667 := bstep (se 1 (by rfl) ⟨583250, by rfl⟩ : syracuseStep 777667 = 1166501) B1166501
theorem B1039811 : Blo 690315 1039811 := bstep (se 1 (by rfl) ⟨779858, by rfl⟩ : syracuseStep 1039811 = 1559717) B1559717
theorem B3333581 : Blo 690315 3333581 := bstep (se 3 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 3333581 = 1250093) B1250093
theorem B1039841 : Blo 690315 1039841 := bstep (se 2 (by rfl) ⟨389940, by rfl⟩ : syracuseStep 1039841 = 779881) B779881
theorem B1170929 : Blo 690315 1170929 := bstep (se 2 (by rfl) ⟨439098, by rfl⟩ : syracuseStep 1170929 = 878197) B878197
theorem B1039859 : Blo 690315 1039859 := bstep (se 1 (by rfl) ⟨779894, by rfl⟩ : syracuseStep 1039859 = 1559789) B1559789
theorem B876035 : Blo 690315 876035 := bstep (se 1 (by rfl) ⟨657026, by rfl⟩ : syracuseStep 876035 = 1314053) B1314053
theorem B3988997 : Blo 690315 3988997 := bstep (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) B747937
theorem B1039889 : Blo 690315 1039889 := bstep (se 2 (by rfl) ⟨389958, by rfl⟩ : syracuseStep 1039889 = 779917) B779917
theorem B2219555 : Blo 690315 2219555 := bstep (se 1 (by rfl) ⟨1664666, by rfl⟩ : syracuseStep 2219555 = 3329333) B3329333
theorem B1039907 : Blo 690315 1039907 := bstep (se 1 (by rfl) ⟨779930, by rfl⟩ : syracuseStep 1039907 = 1559861) B1559861
theorem B1039937 : Blo 690315 1039937 := bstep (se 2 (by rfl) ⟨389976, by rfl⟩ : syracuseStep 1039937 = 779953) B779953
theorem B777811 : Blo 690315 777811 := bstep (se 1 (by rfl) ⟨583358, by rfl⟩ : syracuseStep 777811 = 1166717) B1166717
theorem B1039955 : Blo 690315 1039955 := bstep (se 1 (by rfl) ⟨779966, by rfl⟩ : syracuseStep 1039955 = 1559933) B1559933
theorem B1039985 : Blo 690315 1039985 := bstep (se 2 (by rfl) ⟨389994, by rfl⟩ : syracuseStep 1039985 = 779989) B779989
theorem B1171057 : Blo 690315 1171057 := bstep (se 2 (by rfl) ⟨439146, by rfl⟩ : syracuseStep 1171057 = 878293) B878293
theorem B1040003 : Blo 690315 1040003 := bstep (se 1 (by rfl) ⟨780002, by rfl⟩ : syracuseStep 1040003 = 1560005) B1560005
theorem B1171091 : Blo 690315 1171091 := bstep (se 1 (by rfl) ⟨878318, by rfl⟩ : syracuseStep 1171091 = 1756637) B1756637
theorem B1040033 : Blo 690315 1040033 := bstep (se 2 (by rfl) ⟨390012, by rfl⟩ : syracuseStep 1040033 = 780025) B780025
theorem B1400483 : Blo 690315 1400483 := bstep (se 1 (by rfl) ⟨1050362, by rfl⟩ : syracuseStep 1400483 = 2100725) B2100725
theorem B1040051 : Blo 690315 1040051 := bstep (se 1 (by rfl) ⟨780038, by rfl⟩ : syracuseStep 1040051 = 1560077) B1560077
theorem B1040081 : Blo 690315 1040081 := bstep (se 2 (by rfl) ⟨390030, by rfl⟩ : syracuseStep 1040081 = 780061) B780061
theorem B777955 : Blo 690315 777955 := bstep (se 1 (by rfl) ⟨583466, by rfl⟩ : syracuseStep 777955 = 1166933) B1166933
theorem B1040099 : Blo 690315 1040099 := bstep (se 1 (by rfl) ⟨780074, by rfl⟩ : syracuseStep 1040099 = 1560149) B1560149
theorem B11853539 : Blo 690315 11853539 := bstep (se 1 (by rfl) ⟨8890154, by rfl⟩ : syracuseStep 11853539 = 17780309) B17780309
theorem B1040129 : Blo 690315 1040129 := bstep (se 2 (by rfl) ⟨390048, by rfl⟩ : syracuseStep 1040129 = 780097) B780097
theorem B3497741 : Blo 690315 3497741 := bstep (se 3 (by rfl) ⟨655826, by rfl⟩ : syracuseStep 3497741 = 1311653) B1311653
theorem B1040147 : Blo 690315 1040147 := bstep (se 1 (by rfl) ⟨780110, by rfl⟩ : syracuseStep 1040147 = 1560221) B1560221
theorem B1171219 : Blo 690315 1171219 := bstep (se 1 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 1171219 = 1756829) B1756829
theorem B1040177 : Blo 690315 1040177 := bstep (se 2 (by rfl) ⟨390066, by rfl⟩ : syracuseStep 1040177 = 780133) B780133
theorem B1040195 : Blo 690315 1040195 := bstep (se 1 (by rfl) ⟨780146, by rfl⟩ : syracuseStep 1040195 = 1560293) B1560293
theorem B1040225 : Blo 690315 1040225 := bstep (se 2 (by rfl) ⟨390084, by rfl⟩ : syracuseStep 1040225 = 780169) B780169
theorem B778099 : Blo 690315 778099 := bstep (se 1 (by rfl) ⟨583574, by rfl⟩ : syracuseStep 778099 = 1167149) B1167149
theorem B1040243 : Blo 690315 1040243 := bstep (se 1 (by rfl) ⟨780182, by rfl⟩ : syracuseStep 1040243 = 1560365) B1560365
theorem B1040273 : Blo 690315 1040273 := bstep (se 2 (by rfl) ⟨390102, by rfl⟩ : syracuseStep 1040273 = 780205) B780205
theorem B1171361 : Blo 690315 1171361 := bstep (se 2 (by rfl) ⟨439260, by rfl⟩ : syracuseStep 1171361 = 878521) B878521
theorem B1040291 : Blo 690315 1040291 := bstep (se 1 (by rfl) ⟨780218, by rfl⟩ : syracuseStep 1040291 = 1560437) B1560437
theorem B1040321 : Blo 690315 1040321 := bstep (se 2 (by rfl) ⟨390120, by rfl⟩ : syracuseStep 1040321 = 780241) B780241
theorem B1040339 : Blo 690315 1040339 := bstep (se 1 (by rfl) ⟨780254, by rfl⟩ : syracuseStep 1040339 = 1560509) B1560509
theorem B1040369 : Blo 690315 1040369 := bstep (se 2 (by rfl) ⟨390138, by rfl⟩ : syracuseStep 1040369 = 780277) B780277
theorem B778243 : Blo 690315 778243 := bstep (se 1 (by rfl) ⟨583682, by rfl⟩ : syracuseStep 778243 = 1167365) B1167365
theorem B1040387 : Blo 690315 1040387 := bstep (se 1 (by rfl) ⟨780290, by rfl⟩ : syracuseStep 1040387 = 1560581) B1560581
theorem B1040417 : Blo 690315 1040417 := bstep (se 2 (by rfl) ⟨390156, by rfl⟩ : syracuseStep 1040417 = 780313) B780313
theorem B1171489 : Blo 690315 1171489 := bstep (se 2 (by rfl) ⟨439308, by rfl⟩ : syracuseStep 1171489 = 878617) B878617
theorem B1040435 : Blo 690315 1040435 := bstep (se 1 (by rfl) ⟨780326, by rfl⟩ : syracuseStep 1040435 = 1560653) B1560653
theorem B1171523 : Blo 690315 1171523 := bstep (se 1 (by rfl) ⟨878642, by rfl⟩ : syracuseStep 1171523 = 1757285) B1757285
theorem B1040465 : Blo 690315 1040465 := bstep (se 2 (by rfl) ⟨390174, by rfl⟩ : syracuseStep 1040465 = 780349) B780349
theorem B1040483 : Blo 690315 1040483 := bstep (se 1 (by rfl) ⟨780362, by rfl⟩ : syracuseStep 1040483 = 1560725) B1560725
theorem B1040513 : Blo 690315 1040513 := bstep (se 2 (by rfl) ⟨390192, by rfl⟩ : syracuseStep 1040513 = 780385) B780385
theorem B778387 : Blo 690315 778387 := bstep (se 1 (by rfl) ⟨583790, by rfl⟩ : syracuseStep 778387 = 1167581) B1167581
theorem B1040531 : Blo 690315 1040531 := bstep (se 1 (by rfl) ⟨780398, by rfl⟩ : syracuseStep 1040531 = 1560797) B1560797
theorem B1040561 : Blo 690315 1040561 := bstep (se 2 (by rfl) ⟨390210, by rfl⟩ : syracuseStep 1040561 = 780421) B780421
theorem B876739 : Blo 690315 876739 := bstep (se 1 (by rfl) ⟨657554, by rfl⟩ : syracuseStep 876739 = 1315109) B1315109
theorem B1040579 : Blo 690315 1040579 := bstep (se 1 (by rfl) ⟨780434, by rfl⟩ : syracuseStep 1040579 = 1560869) B1560869
theorem B1171651 : Blo 690315 1171651 := bstep (se 1 (by rfl) ⟨878738, by rfl⟩ : syracuseStep 1171651 = 1757477) B1757477
theorem B1040609 : Blo 690315 1040609 := bstep (se 2 (by rfl) ⟨390228, by rfl⟩ : syracuseStep 1040609 = 780457) B780457
theorem B1040627 : Blo 690315 1040627 := bstep (se 1 (by rfl) ⟨780470, by rfl⟩ : syracuseStep 1040627 = 1560941) B1560941
theorem B1040657 : Blo 690315 1040657 := bstep (se 2 (by rfl) ⟨390246, by rfl⟩ : syracuseStep 1040657 = 780493) B780493
theorem B1106195 : Blo 690315 1106195 := bstep (se 1 (by rfl) ⟨829646, by rfl⟩ : syracuseStep 1106195 = 1659293) B1659293
theorem B778531 : Blo 690315 778531 := bstep (se 1 (by rfl) ⟨583898, by rfl⟩ : syracuseStep 778531 = 1167797) B1167797
theorem B876835 : Blo 690315 876835 := bstep (se 1 (by rfl) ⟨657626, by rfl⟩ : syracuseStep 876835 = 1315253) B1315253
theorem B1040675 : Blo 690315 1040675 := bstep (se 1 (by rfl) ⟨780506, by rfl⟩ : syracuseStep 1040675 = 1561013) B1561013
theorem B1040705 : Blo 690315 1040705 := bstep (se 2 (by rfl) ⟨390264, by rfl⟩ : syracuseStep 1040705 = 780529) B780529
theorem B1040723 : Blo 690315 1040723 := bstep (se 1 (by rfl) ⟨780542, by rfl⟩ : syracuseStep 1040723 = 1561085) B1561085
theorem B1106273 : Blo 690315 1106273 := bstep (se 2 (by rfl) ⟨414852, by rfl⟩ : syracuseStep 1106273 = 829705) B829705
theorem B1040753 : Blo 690315 1040753 := bstep (se 2 (by rfl) ⟨390282, by rfl⟩ : syracuseStep 1040753 = 780565) B780565
theorem B1040771 : Blo 690315 1040771 := bstep (se 1 (by rfl) ⟨780578, by rfl⟩ : syracuseStep 1040771 = 1561157) B1561157
theorem B1040801 : Blo 690315 1040801 := bstep (se 2 (by rfl) ⟨390300, by rfl⟩ : syracuseStep 1040801 = 780601) B780601
theorem B778675 : Blo 690315 778675 := bstep (se 1 (by rfl) ⟨584006, by rfl⟩ : syracuseStep 778675 = 1168013) B1168013
theorem B1040819 : Blo 690315 1040819 := bstep (se 1 (by rfl) ⟨780614, by rfl⟩ : syracuseStep 1040819 = 1561229) B1561229
theorem B1040849 : Blo 690315 1040849 := bstep (se 2 (by rfl) ⟨390318, by rfl⟩ : syracuseStep 1040849 = 780637) B780637
theorem B1040867 : Blo 690315 1040867 := bstep (se 1 (by rfl) ⟨780650, by rfl⟩ : syracuseStep 1040867 = 1561301) B1561301
theorem B1040897 : Blo 690315 1040897 := bstep (se 2 (by rfl) ⟨390336, by rfl⟩ : syracuseStep 1040897 = 780673) B780673
theorem B1040915 : Blo 690315 1040915 := bstep (se 1 (by rfl) ⟨780686, by rfl⟩ : syracuseStep 1040915 = 1561373) B1561373
theorem B1040945 : Blo 690315 1040945 := bstep (se 2 (by rfl) ⟨390354, by rfl⟩ : syracuseStep 1040945 = 780709) B780709
theorem B1106497 : Blo 690315 1106497 := bstep (se 2 (by rfl) ⟨414936, by rfl⟩ : syracuseStep 1106497 = 829873) B829873
theorem B778819 : Blo 690315 778819 := bstep (se 1 (by rfl) ⟨584114, by rfl⟩ : syracuseStep 778819 = 1168229) B1168229
theorem B1040963 : Blo 690315 1040963 := bstep (se 1 (by rfl) ⟨780722, by rfl⟩ : syracuseStep 1040963 = 1561445) B1561445
theorem B1040993 : Blo 690315 1040993 := bstep (se 2 (by rfl) ⟨390372, by rfl⟩ : syracuseStep 1040993 = 780745) B780745
theorem B1041011 : Blo 690315 1041011 := bstep (se 1 (by rfl) ⟨780758, by rfl⟩ : syracuseStep 1041011 = 1561517) B1561517
theorem B11231885 : Blo 690315 11231885 := bstep (se 3 (by rfl) ⟨2105978, by rfl⟩ : syracuseStep 11231885 = 4211957) B4211957
theorem B1041041 : Blo 690315 1041041 := bstep (se 2 (by rfl) ⟨390390, by rfl⟩ : syracuseStep 1041041 = 780781) B780781
theorem B1041059 : Blo 690315 1041059 := bstep (se 1 (by rfl) ⟨780794, by rfl⟩ : syracuseStep 1041059 = 1561589) B1561589
theorem B1041089 : Blo 690315 1041089 := bstep (se 2 (by rfl) ⟨390408, by rfl⟩ : syracuseStep 1041089 = 780817) B780817
theorem B778963 : Blo 690315 778963 := bstep (se 1 (by rfl) ⟨584222, by rfl⟩ : syracuseStep 778963 = 1168445) B1168445
theorem B1041107 : Blo 690315 1041107 := bstep (se 1 (by rfl) ⟨780830, by rfl⟩ : syracuseStep 1041107 = 1561661) B1561661
theorem B1663715 : Blo 690315 1663715 := bstep (se 1 (by rfl) ⟨1247786, by rfl⟩ : syracuseStep 1663715 = 2495573) B2495573
theorem B1041137 : Blo 690315 1041137 := bstep (se 2 (by rfl) ⟨390426, by rfl⟩ : syracuseStep 1041137 = 780853) B780853
theorem B1041155 : Blo 690315 1041155 := bstep (se 1 (by rfl) ⟨780866, by rfl⟩ : syracuseStep 1041155 = 1561733) B1561733
theorem B3334925 : Blo 690315 3334925 := bstep (se 3 (by rfl) ⟨625298, by rfl⟩ : syracuseStep 3334925 = 1250597) B1250597
theorem B877331 : Blo 690315 877331 := bstep (se 1 (by rfl) ⟨657998, by rfl⟩ : syracuseStep 877331 = 1315997) B1315997
theorem B1041185 : Blo 690315 1041185 := bstep (se 2 (by rfl) ⟨390444, by rfl⟩ : syracuseStep 1041185 = 780889) B780889
theorem B1041203 : Blo 690315 1041203 := bstep (se 1 (by rfl) ⟨780902, by rfl⟩ : syracuseStep 1041203 = 1561805) B1561805
theorem B1041233 : Blo 690315 1041233 := bstep (se 2 (by rfl) ⟨390462, by rfl⟩ : syracuseStep 1041233 = 780925) B780925
theorem B779107 : Blo 690315 779107 := bstep (se 1 (by rfl) ⟨584330, by rfl⟩ : syracuseStep 779107 = 1168661) B1168661
theorem B1041251 : Blo 690315 1041251 := bstep (se 1 (by rfl) ⟨780938, by rfl⟩ : syracuseStep 1041251 = 1561877) B1561877
theorem B1041281 : Blo 690315 1041281 := bstep (se 2 (by rfl) ⟨390480, by rfl⟩ : syracuseStep 1041281 = 780961) B780961
theorem B1041299 : Blo 690315 1041299 := bstep (se 1 (by rfl) ⟨780974, by rfl⟩ : syracuseStep 1041299 = 1561949) B1561949
theorem B1041329 : Blo 690315 1041329 := bstep (se 2 (by rfl) ⟨390498, by rfl⟩ : syracuseStep 1041329 = 780997) B780997
theorem B1041347 : Blo 690315 1041347 := bstep (se 1 (by rfl) ⟨781010, by rfl⟩ : syracuseStep 1041347 = 1562021) B1562021
theorem B1041377 : Blo 690315 1041377 := bstep (se 2 (by rfl) ⟨390516, by rfl⟩ : syracuseStep 1041377 = 781033) B781033
theorem B779251 : Blo 690315 779251 := bstep (se 1 (by rfl) ⟨584438, by rfl⟩ : syracuseStep 779251 = 1168877) B1168877
theorem B1041395 : Blo 690315 1041395 := bstep (se 1 (by rfl) ⟨781046, by rfl⟩ : syracuseStep 1041395 = 1562093) B1562093
theorem B1664003 : Blo 690315 1664003 := bstep (se 1 (by rfl) ⟨1248002, by rfl⟩ : syracuseStep 1664003 = 2496005) B2496005
theorem B1041425 : Blo 690315 1041425 := bstep (se 2 (by rfl) ⟨390534, by rfl⟩ : syracuseStep 1041425 = 781069) B781069
theorem B1041443 : Blo 690315 1041443 := bstep (se 1 (by rfl) ⟨781082, by rfl⟩ : syracuseStep 1041443 = 1562165) B1562165
theorem B1041473 : Blo 690315 1041473 := bstep (se 2 (by rfl) ⟨390552, by rfl⟩ : syracuseStep 1041473 = 781105) B781105
theorem B779395 : Blo 690315 779395 := bstep (se 1 (by rfl) ⟨584546, by rfl⟩ : syracuseStep 779395 = 1169093) B1169093
theorem B2254061 : Blo 690315 2254061 := bstep (se 3 (by rfl) ⟨422636, by rfl⟩ : syracuseStep 2254061 = 845273) B845273
theorem B779539 : Blo 690315 779539 := bstep (se 1 (by rfl) ⟨584654, by rfl⟩ : syracuseStep 779539 = 1169309) B1169309
theorem B779683 : Blo 690315 779683 := bstep (se 1 (by rfl) ⟨584762, by rfl⟩ : syracuseStep 779683 = 1169525) B1169525
theorem B878035 : Blo 690315 878035 := bstep (se 1 (by rfl) ⟨658526, by rfl⟩ : syracuseStep 878035 = 1317053) B1317053
theorem B779827 : Blo 690315 779827 := bstep (se 1 (by rfl) ⟨584870, by rfl⟩ : syracuseStep 779827 = 1169741) B1169741
theorem B878131 : Blo 690315 878131 := bstep (se 1 (by rfl) ⟨658598, by rfl⟩ : syracuseStep 878131 = 1317197) B1317197
theorem B779971 : Blo 690315 779971 := bstep (se 1 (by rfl) ⟨584978, by rfl⟩ : syracuseStep 779971 = 1169957) B1169957
theorem B1664849 : Blo 690315 1664849 := bstep (se 2 (by rfl) ⟨624318, by rfl⟩ : syracuseStep 1664849 = 1248637) B1248637
theorem B780115 : Blo 690315 780115 := bstep (se 1 (by rfl) ⟨585086, by rfl⟩ : syracuseStep 780115 = 1170173) B1170173
theorem B1664945 : Blo 690315 1664945 := bstep (se 2 (by rfl) ⟨624354, by rfl⟩ : syracuseStep 1664945 = 1248709) B1248709
theorem B780259 : Blo 690315 780259 := bstep (se 1 (by rfl) ⟨585194, by rfl⟩ : syracuseStep 780259 = 1170389) B1170389
theorem B878627 : Blo 690315 878627 := bstep (se 1 (by rfl) ⟨658970, by rfl⟩ : syracuseStep 878627 = 1317941) B1317941
theorem B2222129 : Blo 690315 2222129 := bstep (se 2 (by rfl) ⟨833298, by rfl⟩ : syracuseStep 2222129 = 1666597) B1666597
theorem B1894499 : Blo 690315 1894499 := bstep (se 1 (by rfl) ⟨1420874, by rfl⟩ : syracuseStep 1894499 = 2841749) B2841749
theorem B1665137 : Blo 690315 1665137 := bstep (se 2 (by rfl) ⟨624426, by rfl⟩ : syracuseStep 1665137 = 1248853) B1248853
theorem B780403 : Blo 690315 780403 := bstep (se 1 (by rfl) ⟨585302, by rfl⟩ : syracuseStep 780403 = 1170605) B1170605
theorem B780547 : Blo 690315 780547 := bstep (se 1 (by rfl) ⟨585410, by rfl⟩ : syracuseStep 780547 = 1170821) B1170821
theorem B1108259 : Blo 690315 1108259 := bstep (se 1 (by rfl) ⟨831194, by rfl⟩ : syracuseStep 1108259 = 1662389) B1662389
theorem B780691 : Blo 690315 780691 := bstep (se 1 (by rfl) ⟨585518, by rfl⟩ : syracuseStep 780691 = 1171037) B1171037
theorem B1108451 : Blo 690315 1108451 := bstep (se 1 (by rfl) ⟨831338, by rfl⟩ : syracuseStep 1108451 = 1662677) B1662677
theorem B1010161 : Blo 690315 1010161 := bstep (se 2 (by rfl) ⟨378810, by rfl⟩ : syracuseStep 1010161 = 757621) B757621
theorem B780835 : Blo 690315 780835 := bstep (se 1 (by rfl) ⟨585626, by rfl⟩ : syracuseStep 780835 = 1171253) B1171253
theorem B1108579 : Blo 690315 1108579 := bstep (se 1 (by rfl) ⟨831434, by rfl⟩ : syracuseStep 1108579 = 1662869) B1662869
theorem B3500657 : Blo 690315 3500657 := bstep (se 2 (by rfl) ⟨1312746, by rfl⟩ : syracuseStep 3500657 = 2625493) B2625493
theorem B780979 : Blo 690315 780979 := bstep (se 1 (by rfl) ⟨585734, by rfl⟩ : syracuseStep 780979 = 1171469) B1171469
theorem B5270669 : Blo 690315 5270669 := bstep (se 3 (by rfl) ⟨988250, by rfl⟩ : syracuseStep 5270669 = 1976501) B1976501
theorem B1109219 : Blo 690315 1109219 := bstep (se 1 (by rfl) ⟨831914, by rfl⟩ : syracuseStep 1109219 = 1663829) B1663829
theorem B1666289 : Blo 690315 1666289 := bstep (se 2 (by rfl) ⟨624858, by rfl⟩ : syracuseStep 1666289 = 1249717) B1249717
theorem B1109297 : Blo 690315 1109297 := bstep (se 2 (by rfl) ⟨415986, by rfl⟩ : syracuseStep 1109297 = 831973) B831973
theorem B4222277 : Blo 690315 4222277 := bstep (se 4 (by rfl) ⟨395838, by rfl⟩ : syracuseStep 4222277 = 791677) B791677
theorem B1109681 : Blo 690315 1109681 := bstep (se 2 (by rfl) ⟨416130, by rfl⟩ : syracuseStep 1109681 = 832261) B832261
theorem B6942449 : Blo 690315 6942449 := bstep (se 2 (by rfl) ⟨2603418, by rfl⟩ : syracuseStep 6942449 = 5206837) B5206837
theorem B1109809 : Blo 690315 1109809 := bstep (se 2 (by rfl) ⟨416178, by rfl⟩ : syracuseStep 1109809 = 832357) B832357
theorem B3502115 : Blo 690315 3502115 := bstep (se 1 (by rfl) ⟨2626586, by rfl⟩ : syracuseStep 3502115 = 5253173) B5253173
theorem B8876213 : Blo 690315 8876213 := bstep (se 5 (by rfl) ⟨416072, by rfl⟩ : syracuseStep 8876213 = 832145) B832145
theorem B3207395 : Blo 690315 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B1405283 : Blo 690315 1405283 := bstep (se 1 (by rfl) ⟨1053962, by rfl⟩ : syracuseStep 1405283 = 2107925) B2107925
theorem B3502925 : Blo 690315 3502925 := bstep (se 3 (by rfl) ⟨656798, by rfl⟩ : syracuseStep 3502925 = 1313597) B1313597
theorem B1111315 : Blo 690315 1111315 := bstep (se 1 (by rfl) ⟨833486, by rfl⟩ : syracuseStep 1111315 = 1666973) B1666973
theorem B2848241 : Blo 690315 2848241 := bstep (se 2 (by rfl) ⟨1068090, by rfl⟩ : syracuseStep 2848241 = 2136181) B2136181
theorem B1996451 : Blo 690315 1996451 := bstep (se 1 (by rfl) ⟨1497338, by rfl⟩ : syracuseStep 1996451 = 2994677) B2994677
theorem B1996589 : Blo 690315 1996589 := bstep (se 3 (by rfl) ⟨374360, by rfl⟩ : syracuseStep 1996589 = 748721) B748721
theorem B948115 : Blo 690315 948115 := bstep (se 1 (by rfl) ⟨711086, by rfl⟩ : syracuseStep 948115 = 1422173) B1422173
theorem B1111987 : Blo 690315 1111987 := bstep (se 1 (by rfl) ⟨833990, by rfl⟩ : syracuseStep 1111987 = 1667981) B1667981
theorem B20183093 : Blo 690315 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B2849293 : Blo 690315 2849293 := bstep (se 3 (by rfl) ⟨534242, by rfl⟩ : syracuseStep 2849293 = 1068485) B1068485
theorem B2489201 : Blo 690315 2489201 := bstep (se 2 (by rfl) ⟨933450, by rfl⟩ : syracuseStep 2489201 = 1866901) B1866901
theorem B4062221 : Blo 690315 4062221 := bstep (se 3 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 4062221 = 1523333) B1523333
theorem B2849869 : Blo 690315 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B1244369 : Blo 690315 1244369 := bstep (se 2 (by rfl) ⟨466638, by rfl⟩ : syracuseStep 1244369 = 933277) B933277
theorem B5242481 : Blo 690315 5242481 := bstep (se 2 (by rfl) ⟨1965930, by rfl⟩ : syracuseStep 5242481 = 3931861) B3931861
theorem B2621105 : Blo 690315 2621105 := bstep (se 2 (by rfl) ⟨982914, by rfl⟩ : syracuseStep 2621105 = 1965829) B1965829
theorem B3505841 : Blo 690315 3505841 := bstep (se 2 (by rfl) ⟨1314690, by rfl⟩ : syracuseStep 3505841 = 2629381) B2629381
theorem B2850659 : Blo 690315 2850659 := bstep (se 1 (by rfl) ⟨2137994, by rfl⟩ : syracuseStep 2850659 = 4275989) B4275989
theorem B983011 : Blo 690315 983011 := bstep (se 1 (by rfl) ⟨737258, by rfl⟩ : syracuseStep 983011 = 1474517) B1474517
theorem B1966103 : Blo 690315 1966103 := bstep (se 1 (by rfl) ⟨1474577, by rfl⟩ : syracuseStep 1966103 = 2949155) B2949155
theorem B1245235 : Blo 690315 1245235 := bstep (se 1 (by rfl) ⟨933926, by rfl⟩ : syracuseStep 1245235 = 1867853) B1867853
theorem B7864451 : Blo 690315 7864451 := bstep (se 1 (by rfl) ⟨5898338, by rfl⟩ : syracuseStep 7864451 = 11796677) B11796677
theorem B2621591 : Blo 690315 2621591 := bstep (se 1 (by rfl) ⟨1966193, by rfl⟩ : syracuseStep 2621591 = 3932387) B3932387
theorem B3506327 : Blo 690315 3506327 := bstep (se 1 (by rfl) ⟨2629745, by rfl⟩ : syracuseStep 3506327 = 5259491) B5259491
theorem B1311319 : Blo 690315 1311319 := bstep (se 1 (by rfl) ⟨983489, by rfl⟩ : syracuseStep 1311319 = 1966979) B1966979
theorem B8553053 : Blo 690315 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B2949853 : Blo 690315 2949853 := bstep (se 3 (by rfl) ⟨553097, by rfl⟩ : syracuseStep 2949853 = 1106195) B1106195
theorem B1475329 : Blo 690315 1475329 := bstep (se 2 (by rfl) ⟨553248, by rfl⟩ : syracuseStep 1475329 = 1106497) B1106497
theorem B983831 : Blo 690315 983831 := bstep (se 1 (by rfl) ⟨737873, by rfl⟩ : syracuseStep 983831 = 1475747) B1475747
theorem B984025 : Blo 690315 984025 := bstep (se 2 (by rfl) ⟨369009, by rfl⟩ : syracuseStep 984025 = 738019) B738019
theorem B5243939 : Blo 690315 5243939 := bstep (se 1 (by rfl) ⟨3932954, by rfl⟩ : syracuseStep 5243939 = 7865909) B7865909
theorem B2950195 : Blo 690315 2950195 := bstep (se 1 (by rfl) ⟨2212646, by rfl⟩ : syracuseStep 2950195 = 4425293) B4425293
theorem B24249419 : Blo 690315 24249419 := bstep (se 1 (by rfl) ⟨18187064, by rfl⟩ : syracuseStep 24249419 = 36374129) B36374129
theorem B1475671 : Blo 690315 1475671 := bstep (se 1 (by rfl) ⟨1106753, by rfl⟩ : syracuseStep 1475671 = 2213507) B2213507
theorem B1967321 : Blo 690315 1967321 := bstep (se 2 (by rfl) ⟨737745, by rfl⟩ : syracuseStep 1967321 = 1475491) B1475491
theorem B3736849 : Blo 690315 3736849 := bstep (se 2 (by rfl) ⟨1401318, by rfl⟩ : syracuseStep 3736849 = 2802637) B2802637
theorem B1967435 : Blo 690315 1967435 := bstep (se 1 (by rfl) ⟨1475576, by rfl⟩ : syracuseStep 1967435 = 2951153) B2951153
theorem B2622851 : Blo 690315 2622851 := bstep (se 1 (by rfl) ⟨1967138, by rfl⟩ : syracuseStep 2622851 = 3934277) B3934277
theorem B4982147 : Blo 690315 4982147 := bstep (se 1 (by rfl) ⟨3736610, by rfl⟩ : syracuseStep 4982147 = 7473221) B7473221
theorem B1312139 : Blo 690315 1312139 := bstep (se 1 (by rfl) ⟨984104, by rfl⟩ : syracuseStep 1312139 = 1968209) B1968209
theorem B1312193 : Blo 690315 1312193 := bstep (se 2 (by rfl) ⟨492072, by rfl⟩ : syracuseStep 1312193 = 984145) B984145
theorem B690315 : Blo 690315 690315 := bstep (se 1 (by rfl) ⟨517736, by rfl⟩ : syracuseStep 690315 = 1035473) B1035473
theorem B690327 : Blo 690315 690327 := bstep (se 1 (by rfl) ⟨517745, by rfl⟩ : syracuseStep 690327 = 1035491) B1035491
theorem B690347 : Blo 690315 690347 := bstep (se 1 (by rfl) ⟨517760, by rfl⟩ : syracuseStep 690347 = 1035521) B1035521
theorem B690359 : Blo 690315 690359 := bstep (se 1 (by rfl) ⟨517769, by rfl⟩ : syracuseStep 690359 = 1035539) B1035539
theorem B690379 : Blo 690315 690379 := bstep (se 1 (by rfl) ⟨517784, by rfl⟩ : syracuseStep 690379 = 1035569) B1035569
theorem B690391 : Blo 690315 690391 := bstep (se 1 (by rfl) ⟨517793, by rfl⟩ : syracuseStep 690391 = 1035587) B1035587
theorem B690411 : Blo 690315 690411 := bstep (se 1 (by rfl) ⟨517808, by rfl⟩ : syracuseStep 690411 = 1035617) B1035617
theorem B690423 : Blo 690315 690423 := bstep (se 1 (by rfl) ⟨517817, by rfl⟩ : syracuseStep 690423 = 1035635) B1035635
theorem B690443 : Blo 690315 690443 := bstep (se 1 (by rfl) ⟨517832, by rfl⟩ : syracuseStep 690443 = 1035665) B1035665
theorem B1476875 : Blo 690315 1476875 := bstep (se 1 (by rfl) ⟨1107656, by rfl⟩ : syracuseStep 1476875 = 2215313) B2215313
theorem B690455 : Blo 690315 690455 := bstep (se 1 (by rfl) ⟨517841, by rfl⟩ : syracuseStep 690455 = 1035683) B1035683
theorem B690475 : Blo 690315 690475 := bstep (se 1 (by rfl) ⟨517856, by rfl⟩ : syracuseStep 690475 = 1035713) B1035713
theorem B690487 : Blo 690315 690487 := bstep (se 1 (by rfl) ⟨517865, by rfl⟩ : syracuseStep 690487 = 1035731) B1035731
theorem B690507 : Blo 690315 690507 := bstep (se 1 (by rfl) ⟨517880, by rfl⟩ : syracuseStep 690507 = 1035761) B1035761
theorem B690519 : Blo 690315 690519 := bstep (se 1 (by rfl) ⟨517889, by rfl⟩ : syracuseStep 690519 = 1035779) B1035779
theorem B1313111 : Blo 690315 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B690539 : Blo 690315 690539 := bstep (se 1 (by rfl) ⟨517904, by rfl⟩ : syracuseStep 690539 = 1035809) B1035809
theorem B11831669 : Blo 690315 11831669 := bstep (se 5 (by rfl) ⟨554609, by rfl⟩ : syracuseStep 11831669 = 1109219) B1109219
theorem B690551 : Blo 690315 690551 := bstep (se 1 (by rfl) ⟨517913, by rfl⟩ : syracuseStep 690551 = 1035827) B1035827
theorem B3934595 : Blo 690315 3934595 := bstep (se 1 (by rfl) ⟨2950946, by rfl⟩ : syracuseStep 3934595 = 5901893) B5901893
theorem B690571 : Blo 690315 690571 := bstep (se 1 (by rfl) ⟨517928, by rfl⟩ : syracuseStep 690571 = 1035857) B1035857
theorem B985483 : Blo 690315 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B690583 : Blo 690315 690583 := bstep (se 1 (by rfl) ⟨517937, by rfl⟩ : syracuseStep 690583 = 1035875) B1035875
theorem B690603 : Blo 690315 690603 := bstep (se 1 (by rfl) ⟨517952, by rfl⟩ : syracuseStep 690603 = 1035905) B1035905
theorem B1968563 : Blo 690315 1968563 := bstep (se 1 (by rfl) ⟨1476422, by rfl⟩ : syracuseStep 1968563 = 2952845) B2952845
theorem B690615 : Blo 690315 690615 := bstep (se 1 (by rfl) ⟨517961, by rfl⟩ : syracuseStep 690615 = 1035923) B1035923
theorem B690635 : Blo 690315 690635 := bstep (se 1 (by rfl) ⟨517976, by rfl⟩ : syracuseStep 690635 = 1035953) B1035953
theorem B690647 : Blo 690315 690647 := bstep (se 1 (by rfl) ⟨517985, by rfl⟩ : syracuseStep 690647 = 1035971) B1035971
theorem B690667 : Blo 690315 690667 := bstep (se 1 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 690667 = 1036001) B1036001
theorem B690679 : Blo 690315 690679 := bstep (se 1 (by rfl) ⟨518009, by rfl⟩ : syracuseStep 690679 = 1036019) B1036019
theorem B690699 : Blo 690315 690699 := bstep (se 1 (by rfl) ⟨518024, by rfl⟩ : syracuseStep 690699 = 1036049) B1036049
theorem B690711 : Blo 690315 690711 := bstep (se 1 (by rfl) ⟨518033, by rfl⟩ : syracuseStep 690711 = 1036067) B1036067
theorem B690731 : Blo 690315 690731 := bstep (se 1 (by rfl) ⟨518048, by rfl⟩ : syracuseStep 690731 = 1036097) B1036097
theorem B690743 : Blo 690315 690743 := bstep (se 1 (by rfl) ⟨518057, by rfl⟩ : syracuseStep 690743 = 1036115) B1036115
theorem B690763 : Blo 690315 690763 := bstep (se 1 (by rfl) ⟨518072, by rfl⟩ : syracuseStep 690763 = 1036145) B1036145
theorem B690775 : Blo 690315 690775 := bstep (se 1 (by rfl) ⟨518081, by rfl⟩ : syracuseStep 690775 = 1036163) B1036163
theorem B4983389 : Blo 690315 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B690795 : Blo 690315 690795 := bstep (se 1 (by rfl) ⟨518096, by rfl⟩ : syracuseStep 690795 = 1036193) B1036193
theorem B690807 : Blo 690315 690807 := bstep (se 1 (by rfl) ⟨518105, by rfl⟩ : syracuseStep 690807 = 1036211) B1036211
theorem B690827 : Blo 690315 690827 := bstep (se 1 (by rfl) ⟨518120, by rfl⟩ : syracuseStep 690827 = 1036241) B1036241
theorem B690839 : Blo 690315 690839 := bstep (se 1 (by rfl) ⟨518129, by rfl⟩ : syracuseStep 690839 = 1036259) B1036259
theorem B690859 : Blo 690315 690859 := bstep (se 1 (by rfl) ⟨518144, by rfl⟩ : syracuseStep 690859 = 1036289) B1036289
theorem B1247923 : Blo 690315 1247923 := bstep (se 1 (by rfl) ⟨935942, by rfl⟩ : syracuseStep 1247923 = 1871885) B1871885
theorem B690871 : Blo 690315 690871 := bstep (se 1 (by rfl) ⟨518153, by rfl⟩ : syracuseStep 690871 = 1036307) B1036307
theorem B690891 : Blo 690315 690891 := bstep (se 1 (by rfl) ⟨518168, by rfl⟩ : syracuseStep 690891 = 1036337) B1036337
theorem B690903 : Blo 690315 690903 := bstep (se 1 (by rfl) ⟨518177, by rfl⟩ : syracuseStep 690903 = 1036355) B1036355
theorem B690923 : Blo 690315 690923 := bstep (se 1 (by rfl) ⟨518192, by rfl⟩ : syracuseStep 690923 = 1036385) B1036385
theorem B690935 : Blo 690315 690935 := bstep (se 1 (by rfl) ⟨518201, by rfl⟩ : syracuseStep 690935 = 1036403) B1036403
theorem B690955 : Blo 690315 690955 := bstep (se 1 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 690955 = 1036433) B1036433
theorem B1477387 : Blo 690315 1477387 := bstep (se 1 (by rfl) ⟨1108040, by rfl⟩ : syracuseStep 1477387 = 2216081) B2216081
theorem B690967 : Blo 690315 690967 := bstep (se 1 (by rfl) ⟨518225, by rfl⟩ : syracuseStep 690967 = 1036451) B1036451
theorem B690987 : Blo 690315 690987 := bstep (se 1 (by rfl) ⟨518240, by rfl⟩ : syracuseStep 690987 = 1036481) B1036481
theorem B690999 : Blo 690315 690999 := bstep (se 1 (by rfl) ⟨518249, by rfl⟩ : syracuseStep 690999 = 1036499) B1036499
theorem B1968961 : Blo 690315 1968961 := bstep (se 2 (by rfl) ⟨738360, by rfl⟩ : syracuseStep 1968961 = 1476721) B1476721
theorem B3935051 : Blo 690315 3935051 := bstep (se 1 (by rfl) ⟨2951288, by rfl⟩ : syracuseStep 3935051 = 5902577) B5902577
theorem B691019 : Blo 690315 691019 := bstep (se 1 (by rfl) ⟨518264, by rfl⟩ : syracuseStep 691019 = 1036529) B1036529
theorem B691031 : Blo 690315 691031 := bstep (se 1 (by rfl) ⟨518273, by rfl⟩ : syracuseStep 691031 = 1036547) B1036547
theorem B691051 : Blo 690315 691051 := bstep (se 1 (by rfl) ⟨518288, by rfl⟩ : syracuseStep 691051 = 1036577) B1036577
theorem B1313651 : Blo 690315 1313651 := bstep (se 1 (by rfl) ⟨985238, by rfl⟩ : syracuseStep 1313651 = 1970477) B1970477
theorem B691063 : Blo 690315 691063 := bstep (se 1 (by rfl) ⟨518297, by rfl⟩ : syracuseStep 691063 = 1036595) B1036595
theorem B691083 : Blo 690315 691083 := bstep (se 1 (by rfl) ⟨518312, by rfl⟩ : syracuseStep 691083 = 1036625) B1036625
theorem B691095 : Blo 690315 691095 := bstep (se 1 (by rfl) ⟨518321, by rfl⟩ : syracuseStep 691095 = 1036643) B1036643
theorem B691115 : Blo 690315 691115 := bstep (se 1 (by rfl) ⟨518336, by rfl⟩ : syracuseStep 691115 = 1036673) B1036673
theorem B691127 : Blo 690315 691127 := bstep (se 1 (by rfl) ⟨518345, by rfl⟩ : syracuseStep 691127 = 1036691) B1036691
theorem B691147 : Blo 690315 691147 := bstep (se 1 (by rfl) ⟨518360, by rfl⟩ : syracuseStep 691147 = 1036721) B1036721
theorem B691159 : Blo 690315 691159 := bstep (se 1 (by rfl) ⟨518369, by rfl⟩ : syracuseStep 691159 = 1036739) B1036739
theorem B5049305 : Blo 690315 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B691179 : Blo 690315 691179 := bstep (se 1 (by rfl) ⟨518384, by rfl⟩ : syracuseStep 691179 = 1036769) B1036769
theorem B691191 : Blo 690315 691191 := bstep (se 1 (by rfl) ⟨518393, by rfl⟩ : syracuseStep 691191 = 1036787) B1036787
theorem B691211 : Blo 690315 691211 := bstep (se 1 (by rfl) ⟨518408, by rfl⟩ : syracuseStep 691211 = 1036817) B1036817
theorem B691223 : Blo 690315 691223 := bstep (se 1 (by rfl) ⟨518417, by rfl⟩ : syracuseStep 691223 = 1036835) B1036835
theorem B691243 : Blo 690315 691243 := bstep (se 1 (by rfl) ⟨518432, by rfl⟩ : syracuseStep 691243 = 1036865) B1036865
theorem B691255 : Blo 690315 691255 := bstep (se 1 (by rfl) ⟨518441, by rfl⟩ : syracuseStep 691255 = 1036883) B1036883
theorem B691275 : Blo 690315 691275 := bstep (se 1 (by rfl) ⟨518456, by rfl⟩ : syracuseStep 691275 = 1036913) B1036913
theorem B691287 : Blo 690315 691287 := bstep (se 1 (by rfl) ⟨518465, by rfl⟩ : syracuseStep 691287 = 1036931) B1036931
theorem B691307 : Blo 690315 691307 := bstep (se 1 (by rfl) ⟨518480, by rfl⟩ : syracuseStep 691307 = 1036961) B1036961
theorem B691319 : Blo 690315 691319 := bstep (se 1 (by rfl) ⟨518489, by rfl⟩ : syracuseStep 691319 = 1036979) B1036979
theorem B1248385 : Blo 690315 1248385 := bstep (se 2 (by rfl) ⟨468144, by rfl⟩ : syracuseStep 1248385 = 936289) B936289
theorem B4426883 : Blo 690315 4426883 := bstep (se 1 (by rfl) ⟨3320162, by rfl⟩ : syracuseStep 4426883 = 6640325) B6640325
theorem B691339 : Blo 690315 691339 := bstep (se 1 (by rfl) ⟨518504, by rfl⟩ : syracuseStep 691339 = 1037009) B1037009
theorem B691351 : Blo 690315 691351 := bstep (se 1 (by rfl) ⟨518513, by rfl⟩ : syracuseStep 691351 = 1037027) B1037027
theorem B691371 : Blo 690315 691371 := bstep (se 1 (by rfl) ⟨518528, by rfl⟩ : syracuseStep 691371 = 1037057) B1037057
theorem B691383 : Blo 690315 691383 := bstep (se 1 (by rfl) ⟨518537, by rfl⟩ : syracuseStep 691383 = 1037075) B1037075
theorem B691403 : Blo 690315 691403 := bstep (se 1 (by rfl) ⟨518552, by rfl⟩ : syracuseStep 691403 = 1037105) B1037105
theorem B691415 : Blo 690315 691415 := bstep (se 1 (by rfl) ⟨518561, by rfl⟩ : syracuseStep 691415 = 1037123) B1037123
theorem B691435 : Blo 690315 691435 := bstep (se 1 (by rfl) ⟨518576, by rfl⟩ : syracuseStep 691435 = 1037153) B1037153
theorem B691447 : Blo 690315 691447 := bstep (se 1 (by rfl) ⟨518585, by rfl⟩ : syracuseStep 691447 = 1037171) B1037171
theorem B691467 : Blo 690315 691467 := bstep (se 1 (by rfl) ⟨518600, by rfl⟩ : syracuseStep 691467 = 1037201) B1037201
theorem B691479 : Blo 690315 691479 := bstep (se 1 (by rfl) ⟨518609, by rfl⟩ : syracuseStep 691479 = 1037219) B1037219
theorem B691499 : Blo 690315 691499 := bstep (se 1 (by rfl) ⟨518624, by rfl⟩ : syracuseStep 691499 = 1037249) B1037249
theorem B691511 : Blo 690315 691511 := bstep (se 1 (by rfl) ⟨518633, by rfl⟩ : syracuseStep 691511 = 1037267) B1037267
theorem B1346881 : Blo 690315 1346881 := bstep (se 2 (by rfl) ⟨505080, by rfl⟩ : syracuseStep 1346881 = 1010161) B1010161
theorem B691531 : Blo 690315 691531 := bstep (se 1 (by rfl) ⟨518648, by rfl⟩ : syracuseStep 691531 = 1037297) B1037297
theorem B691543 : Blo 690315 691543 := bstep (se 1 (by rfl) ⟨518657, by rfl⟩ : syracuseStep 691543 = 1037315) B1037315
theorem B1314137 : Blo 690315 1314137 := bstep (se 2 (by rfl) ⟨492801, by rfl⟩ : syracuseStep 1314137 = 985603) B985603
theorem B691563 : Blo 690315 691563 := bstep (se 1 (by rfl) ⟨518672, by rfl⟩ : syracuseStep 691563 = 1037345) B1037345
theorem B691575 : Blo 690315 691575 := bstep (se 1 (by rfl) ⟨518681, by rfl⟩ : syracuseStep 691575 = 1037363) B1037363
theorem B691595 : Blo 690315 691595 := bstep (se 1 (by rfl) ⟨518696, by rfl⟩ : syracuseStep 691595 = 1037393) B1037393
theorem B2493841 : Blo 690315 2493841 := bstep (se 2 (by rfl) ⟨935190, by rfl⟩ : syracuseStep 2493841 = 1870381) B1870381
theorem B691607 : Blo 690315 691607 := bstep (se 1 (by rfl) ⟨518705, by rfl⟩ : syracuseStep 691607 = 1037411) B1037411
theorem B691627 : Blo 690315 691627 := bstep (se 1 (by rfl) ⟨518720, by rfl⟩ : syracuseStep 691627 = 1037441) B1037441
theorem B691639 : Blo 690315 691639 := bstep (se 1 (by rfl) ⟨518729, by rfl⟩ : syracuseStep 691639 = 1037459) B1037459
theorem B789943 : Blo 690315 789943 := bstep (se 1 (by rfl) ⟨592457, by rfl⟩ : syracuseStep 789943 = 1184915) B1184915
theorem B691659 : Blo 690315 691659 := bstep (se 1 (by rfl) ⟨518744, by rfl⟩ : syracuseStep 691659 = 1037489) B1037489
theorem B691671 : Blo 690315 691671 := bstep (se 1 (by rfl) ⟨518753, by rfl⟩ : syracuseStep 691671 = 1037507) B1037507
theorem B1478105 : Blo 690315 1478105 := bstep (se 2 (by rfl) ⟨554289, by rfl⟩ : syracuseStep 1478105 = 1108579) B1108579
theorem B691691 : Blo 690315 691691 := bstep (se 1 (by rfl) ⟨518768, by rfl⟩ : syracuseStep 691691 = 1037537) B1037537
theorem B691703 : Blo 690315 691703 := bstep (se 1 (by rfl) ⟨518777, by rfl⟩ : syracuseStep 691703 = 1037555) B1037555
theorem B691723 : Blo 690315 691723 := bstep (se 1 (by rfl) ⟨518792, by rfl⟩ : syracuseStep 691723 = 1037585) B1037585
theorem B691735 : Blo 690315 691735 := bstep (se 1 (by rfl) ⟨518801, by rfl⟩ : syracuseStep 691735 = 1037603) B1037603
theorem B691755 : Blo 690315 691755 := bstep (se 1 (by rfl) ⟨518816, by rfl⟩ : syracuseStep 691755 = 1037633) B1037633
theorem B691767 : Blo 690315 691767 := bstep (se 1 (by rfl) ⟨518825, by rfl⟩ : syracuseStep 691767 = 1037651) B1037651
theorem B2100811 : Blo 690315 2100811 := bstep (se 1 (by rfl) ⟨1575608, by rfl⟩ : syracuseStep 2100811 = 3151217) B3151217
theorem B691787 : Blo 690315 691787 := bstep (se 1 (by rfl) ⟨518840, by rfl⟩ : syracuseStep 691787 = 1037681) B1037681
theorem B691799 : Blo 690315 691799 := bstep (se 1 (by rfl) ⟨518849, by rfl⟩ : syracuseStep 691799 = 1037699) B1037699
theorem B691819 : Blo 690315 691819 := bstep (se 1 (by rfl) ⟨518864, by rfl⟩ : syracuseStep 691819 = 1037729) B1037729
theorem B691831 : Blo 690315 691831 := bstep (se 1 (by rfl) ⟨518873, by rfl⟩ : syracuseStep 691831 = 1037747) B1037747
theorem B3509891 : Blo 690315 3509891 := bstep (se 1 (by rfl) ⟨2632418, by rfl⟩ : syracuseStep 3509891 = 5264837) B5264837
theorem B691851 : Blo 690315 691851 := bstep (se 1 (by rfl) ⟨518888, by rfl⟩ : syracuseStep 691851 = 1037777) B1037777
theorem B691863 : Blo 690315 691863 := bstep (se 1 (by rfl) ⟨518897, by rfl⟩ : syracuseStep 691863 = 1037795) B1037795
theorem B691883 : Blo 690315 691883 := bstep (se 1 (by rfl) ⟨518912, by rfl⟩ : syracuseStep 691883 = 1037825) B1037825
theorem B691895 : Blo 690315 691895 := bstep (se 1 (by rfl) ⟨518921, by rfl⟩ : syracuseStep 691895 = 1037843) B1037843
theorem B2330315 : Blo 690315 2330315 := bstep (se 1 (by rfl) ⟨1747736, by rfl⟩ : syracuseStep 2330315 = 3495473) B3495473
theorem B691915 : Blo 690315 691915 := bstep (se 1 (by rfl) ⟨518936, by rfl⟩ : syracuseStep 691915 = 1037873) B1037873
theorem B691927 : Blo 690315 691927 := bstep (se 1 (by rfl) ⟨518945, by rfl⟩ : syracuseStep 691927 = 1037891) B1037891
theorem B691947 : Blo 690315 691947 := bstep (se 1 (by rfl) ⟨518960, by rfl⟩ : syracuseStep 691947 = 1037921) B1037921
theorem B691959 : Blo 690315 691959 := bstep (se 1 (by rfl) ⟨518969, by rfl⟩ : syracuseStep 691959 = 1037939) B1037939
theorem B1249025 : Blo 690315 1249025 := bstep (se 2 (by rfl) ⟨468384, by rfl⟩ : syracuseStep 1249025 = 936769) B936769
theorem B691979 : Blo 690315 691979 := bstep (se 1 (by rfl) ⟨518984, by rfl⟩ : syracuseStep 691979 = 1037969) B1037969
theorem B691991 : Blo 690315 691991 := bstep (se 1 (by rfl) ⟨518993, by rfl⟩ : syracuseStep 691991 = 1037987) B1037987
theorem B692011 : Blo 690315 692011 := bstep (se 1 (by rfl) ⟨519008, by rfl⟩ : syracuseStep 692011 = 1038017) B1038017
theorem B692023 : Blo 690315 692023 := bstep (se 1 (by rfl) ⟨519017, by rfl⟩ : syracuseStep 692023 = 1038035) B1038035
theorem B692043 : Blo 690315 692043 := bstep (se 1 (by rfl) ⟨519032, by rfl⟩ : syracuseStep 692043 = 1038065) B1038065
theorem B692055 : Blo 690315 692055 := bstep (se 1 (by rfl) ⟨519041, by rfl⟩ : syracuseStep 692055 = 1038083) B1038083
theorem B692075 : Blo 690315 692075 := bstep (se 1 (by rfl) ⟨519056, by rfl⟩ : syracuseStep 692075 = 1038113) B1038113
theorem B1478515 : Blo 690315 1478515 := bstep (se 1 (by rfl) ⟨1108886, by rfl⟩ : syracuseStep 1478515 = 2217773) B2217773
theorem B692087 : Blo 690315 692087 := bstep (se 1 (by rfl) ⟨519065, by rfl⟩ : syracuseStep 692087 = 1038131) B1038131
theorem B692107 : Blo 690315 692107 := bstep (se 1 (by rfl) ⟨519080, by rfl⟩ : syracuseStep 692107 = 1038161) B1038161
theorem B692119 : Blo 690315 692119 := bstep (se 1 (by rfl) ⟨519089, by rfl⟩ : syracuseStep 692119 = 1038179) B1038179
theorem B692139 : Blo 690315 692139 := bstep (se 1 (by rfl) ⟨519104, by rfl⟩ : syracuseStep 692139 = 1038209) B1038209
theorem B692151 : Blo 690315 692151 := bstep (se 1 (by rfl) ⟨519113, by rfl⟩ : syracuseStep 692151 = 1038227) B1038227
theorem B692171 : Blo 690315 692171 := bstep (se 1 (by rfl) ⟨519128, by rfl⟩ : syracuseStep 692171 = 1038257) B1038257
theorem B692183 : Blo 690315 692183 := bstep (se 1 (by rfl) ⟨519137, by rfl⟩ : syracuseStep 692183 = 1038275) B1038275
theorem B2330585 : Blo 690315 2330585 := bstep (se 2 (by rfl) ⟨873969, by rfl⟩ : syracuseStep 2330585 = 1747939) B1747939
theorem B692203 : Blo 690315 692203 := bstep (se 1 (by rfl) ⟨519152, by rfl⟩ : syracuseStep 692203 = 1038305) B1038305
theorem B692215 : Blo 690315 692215 := bstep (se 1 (by rfl) ⟨519161, by rfl⟩ : syracuseStep 692215 = 1038323) B1038323
theorem B692235 : Blo 690315 692235 := bstep (se 1 (by rfl) ⟨519176, by rfl⟩ : syracuseStep 692235 = 1038353) B1038353
theorem B692247 : Blo 690315 692247 := bstep (se 1 (by rfl) ⟨519185, by rfl⟩ : syracuseStep 692247 = 1038371) B1038371
theorem B692267 : Blo 690315 692267 := bstep (se 1 (by rfl) ⟨519200, by rfl⟩ : syracuseStep 692267 = 1038401) B1038401
theorem B692279 : Blo 690315 692279 := bstep (se 1 (by rfl) ⟨519209, by rfl⟩ : syracuseStep 692279 = 1038419) B1038419
theorem B692299 : Blo 690315 692299 := bstep (se 1 (by rfl) ⟨519224, by rfl⟩ : syracuseStep 692299 = 1038449) B1038449
theorem B692311 : Blo 690315 692311 := bstep (se 1 (by rfl) ⟨519233, by rfl⟩ : syracuseStep 692311 = 1038467) B1038467
theorem B692331 : Blo 690315 692331 := bstep (se 1 (by rfl) ⟨519248, by rfl⟩ : syracuseStep 692331 = 1038497) B1038497
theorem B692343 : Blo 690315 692343 := bstep (se 1 (by rfl) ⟨519257, by rfl⟩ : syracuseStep 692343 = 1038515) B1038515
theorem B692363 : Blo 690315 692363 := bstep (se 1 (by rfl) ⟨519272, by rfl⟩ : syracuseStep 692363 = 1038545) B1038545
theorem B692375 : Blo 690315 692375 := bstep (se 1 (by rfl) ⟨519281, by rfl⟩ : syracuseStep 692375 = 1038563) B1038563
theorem B692395 : Blo 690315 692395 := bstep (se 1 (by rfl) ⟨519296, by rfl⟩ : syracuseStep 692395 = 1038593) B1038593
theorem B692407 : Blo 690315 692407 := bstep (se 1 (by rfl) ⟨519305, by rfl⟩ : syracuseStep 692407 = 1038611) B1038611
theorem B692427 : Blo 690315 692427 := bstep (se 1 (by rfl) ⟨519320, by rfl⟩ : syracuseStep 692427 = 1038641) B1038641
theorem B692439 : Blo 690315 692439 := bstep (se 1 (by rfl) ⟨519329, by rfl⟩ : syracuseStep 692439 = 1038659) B1038659
theorem B1052887 : Blo 690315 1052887 := bstep (se 1 (by rfl) ⟨789665, by rfl⟩ : syracuseStep 1052887 = 1579331) B1579331
theorem B692459 : Blo 690315 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B692471 : Blo 690315 692471 := bstep (se 1 (by rfl) ⟨519353, by rfl⟩ : syracuseStep 692471 = 1038707) B1038707
theorem B692491 : Blo 690315 692491 := bstep (se 1 (by rfl) ⟨519368, by rfl⟩ : syracuseStep 692491 = 1038737) B1038737
theorem B692503 : Blo 690315 692503 := bstep (se 1 (by rfl) ⟨519377, by rfl⟩ : syracuseStep 692503 = 1038755) B1038755
theorem B692523 : Blo 690315 692523 := bstep (se 1 (by rfl) ⟨519392, by rfl⟩ : syracuseStep 692523 = 1038785) B1038785
theorem B692535 : Blo 690315 692535 := bstep (se 1 (by rfl) ⟨519401, by rfl⟩ : syracuseStep 692535 = 1038803) B1038803
theorem B692555 : Blo 690315 692555 := bstep (se 1 (by rfl) ⟨519416, by rfl⟩ : syracuseStep 692555 = 1038833) B1038833
theorem B692567 : Blo 690315 692567 := bstep (se 1 (by rfl) ⟨519425, by rfl⟩ : syracuseStep 692567 = 1038851) B1038851
theorem B692587 : Blo 690315 692587 := bstep (se 1 (by rfl) ⟨519440, by rfl⟩ : syracuseStep 692587 = 1038881) B1038881
theorem B692599 : Blo 690315 692599 := bstep (se 1 (by rfl) ⟨519449, by rfl⟩ : syracuseStep 692599 = 1038899) B1038899
theorem B3150211 : Blo 690315 3150211 := bstep (se 1 (by rfl) ⟨2362658, by rfl⟩ : syracuseStep 3150211 = 4725317) B4725317
theorem B692619 : Blo 690315 692619 := bstep (se 1 (by rfl) ⟨519464, by rfl⟩ : syracuseStep 692619 = 1038929) B1038929
theorem B692631 : Blo 690315 692631 := bstep (se 1 (by rfl) ⟨519473, by rfl⟩ : syracuseStep 692631 = 1038947) B1038947
theorem B1577369 : Blo 690315 1577369 := bstep (se 2 (by rfl) ⟨591513, by rfl⟩ : syracuseStep 1577369 = 1183027) B1183027
theorem B692651 : Blo 690315 692651 := bstep (se 1 (by rfl) ⟨519488, by rfl⟩ : syracuseStep 692651 = 1038977) B1038977
theorem B2625965 : Blo 690315 2625965 := bstep (se 3 (by rfl) ⟨492368, by rfl⟩ : syracuseStep 2625965 = 984737) B984737
theorem B692663 : Blo 690315 692663 := bstep (se 1 (by rfl) ⟨519497, by rfl⟩ : syracuseStep 692663 = 1038995) B1038995
theorem B692683 : Blo 690315 692683 := bstep (se 1 (by rfl) ⟨519512, by rfl⟩ : syracuseStep 692683 = 1039025) B1039025
theorem B692695 : Blo 690315 692695 := bstep (se 1 (by rfl) ⟨519521, by rfl⟩ : syracuseStep 692695 = 1039043) B1039043
theorem B2494937 : Blo 690315 2494937 := bstep (se 2 (by rfl) ⟨935601, by rfl⟩ : syracuseStep 2494937 = 1871203) B1871203
theorem B692715 : Blo 690315 692715 := bstep (se 1 (by rfl) ⟨519536, by rfl⟩ : syracuseStep 692715 = 1039073) B1039073
theorem B692727 : Blo 690315 692727 := bstep (se 1 (by rfl) ⟨519545, by rfl⟩ : syracuseStep 692727 = 1039091) B1039091
theorem B692747 : Blo 690315 692747 := bstep (se 1 (by rfl) ⟨519560, by rfl⟩ : syracuseStep 692747 = 1039121) B1039121
theorem B692759 : Blo 690315 692759 := bstep (se 1 (by rfl) ⟨519569, by rfl⟩ : syracuseStep 692759 = 1039139) B1039139
theorem B692779 : Blo 690315 692779 := bstep (se 1 (by rfl) ⟨519584, by rfl⟩ : syracuseStep 692779 = 1039169) B1039169
theorem B692791 : Blo 690315 692791 := bstep (se 1 (by rfl) ⟨519593, by rfl⟩ : syracuseStep 692791 = 1039187) B1039187
theorem B692811 : Blo 690315 692811 := bstep (se 1 (by rfl) ⟨519608, by rfl⟩ : syracuseStep 692811 = 1039217) B1039217
theorem B692823 : Blo 690315 692823 := bstep (se 1 (by rfl) ⟨519617, by rfl⟩ : syracuseStep 692823 = 1039235) B1039235
theorem B2953817 : Blo 690315 2953817 := bstep (se 2 (by rfl) ⟨1107681, by rfl⟩ : syracuseStep 2953817 = 2215363) B2215363
theorem B692843 : Blo 690315 692843 := bstep (se 1 (by rfl) ⟨519632, by rfl⟩ : syracuseStep 692843 = 1039265) B1039265
theorem B692855 : Blo 690315 692855 := bstep (se 1 (by rfl) ⟨519641, by rfl⟩ : syracuseStep 692855 = 1039283) B1039283
theorem B692875 : Blo 690315 692875 := bstep (se 1 (by rfl) ⟨519656, by rfl⟩ : syracuseStep 692875 = 1039313) B1039313
theorem B889483 : Blo 690315 889483 := bstep (se 1 (by rfl) ⟨667112, by rfl⟩ : syracuseStep 889483 = 1334225) B1334225
theorem B2331287 : Blo 690315 2331287 := bstep (se 1 (by rfl) ⟨1748465, by rfl⟩ : syracuseStep 2331287 = 3496931) B3496931
theorem B692887 : Blo 690315 692887 := bstep (se 1 (by rfl) ⟨519665, by rfl⟩ : syracuseStep 692887 = 1039331) B1039331
theorem B692907 : Blo 690315 692907 := bstep (se 1 (by rfl) ⟨519680, by rfl⟩ : syracuseStep 692907 = 1039361) B1039361
theorem B692919 : Blo 690315 692919 := bstep (se 1 (by rfl) ⟨519689, by rfl⟩ : syracuseStep 692919 = 1039379) B1039379
theorem B692939 : Blo 690315 692939 := bstep (se 1 (by rfl) ⟨519704, by rfl⟩ : syracuseStep 692939 = 1039409) B1039409
theorem B692951 : Blo 690315 692951 := bstep (se 1 (by rfl) ⟨519713, by rfl⟩ : syracuseStep 692951 = 1039427) B1039427
theorem B692971 : Blo 690315 692971 := bstep (se 1 (by rfl) ⟨519728, by rfl⟩ : syracuseStep 692971 = 1039457) B1039457
theorem B791275 : Blo 690315 791275 := bstep (se 1 (by rfl) ⟨593456, by rfl⟩ : syracuseStep 791275 = 1186913) B1186913
theorem B692983 : Blo 690315 692983 := bstep (se 1 (by rfl) ⟨519737, by rfl⟩ : syracuseStep 692983 = 1039475) B1039475
theorem B1315595 : Blo 690315 1315595 := bstep (se 1 (by rfl) ⟨986696, by rfl⟩ : syracuseStep 1315595 = 1973393) B1973393
theorem B693003 : Blo 690315 693003 := bstep (se 1 (by rfl) ⟨519752, by rfl⟩ : syracuseStep 693003 = 1039505) B1039505
theorem B693015 : Blo 690315 693015 := bstep (se 1 (by rfl) ⟨519761, by rfl⟩ : syracuseStep 693015 = 1039523) B1039523
theorem B693035 : Blo 690315 693035 := bstep (se 1 (by rfl) ⟨519776, by rfl⟩ : syracuseStep 693035 = 1039553) B1039553
theorem B693047 : Blo 690315 693047 := bstep (se 1 (by rfl) ⟨519785, by rfl⟩ : syracuseStep 693047 = 1039571) B1039571
theorem B693067 : Blo 690315 693067 := bstep (se 1 (by rfl) ⟨519800, by rfl⟩ : syracuseStep 693067 = 1039601) B1039601
theorem B693079 : Blo 690315 693079 := bstep (se 1 (by rfl) ⟨519809, by rfl⟩ : syracuseStep 693079 = 1039619) B1039619
theorem B693099 : Blo 690315 693099 := bstep (se 1 (by rfl) ⟨519824, by rfl⟩ : syracuseStep 693099 = 1039649) B1039649
theorem B693111 : Blo 690315 693111 := bstep (se 1 (by rfl) ⟨519833, by rfl⟩ : syracuseStep 693111 = 1039667) B1039667
theorem B693131 : Blo 690315 693131 := bstep (se 1 (by rfl) ⟨519848, by rfl⟩ : syracuseStep 693131 = 1039697) B1039697
theorem B1577879 : Blo 690315 1577879 := bstep (se 1 (by rfl) ⟨1183409, by rfl⟩ : syracuseStep 1577879 = 2366819) B2366819
theorem B693143 : Blo 690315 693143 := bstep (se 1 (by rfl) ⟨519857, by rfl⟩ : syracuseStep 693143 = 1039715) B1039715
theorem B693163 : Blo 690315 693163 := bstep (se 1 (by rfl) ⟨519872, by rfl⟩ : syracuseStep 693163 = 1039745) B1039745
theorem B693175 : Blo 690315 693175 := bstep (se 1 (by rfl) ⟨519881, by rfl⟩ : syracuseStep 693175 = 1039763) B1039763
theorem B1315777 : Blo 690315 1315777 := bstep (se 2 (by rfl) ⟨493416, by rfl⟩ : syracuseStep 1315777 = 986833) B986833
theorem B693195 : Blo 690315 693195 := bstep (se 1 (by rfl) ⟨519896, by rfl⟩ : syracuseStep 693195 = 1039793) B1039793
theorem B693207 : Blo 690315 693207 := bstep (se 1 (by rfl) ⟨519905, by rfl⟩ : syracuseStep 693207 = 1039811) B1039811
theorem B693227 : Blo 690315 693227 := bstep (se 1 (by rfl) ⟨519920, by rfl⟩ : syracuseStep 693227 = 1039841) B1039841
theorem B693239 : Blo 690315 693239 := bstep (se 1 (by rfl) ⟨519929, by rfl⟩ : syracuseStep 693239 = 1039859) B1039859
theorem B2659331 : Blo 690315 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B693259 : Blo 690315 693259 := bstep (se 1 (by rfl) ⟨519944, by rfl⟩ : syracuseStep 693259 = 1039889) B1039889
theorem B1479703 : Blo 690315 1479703 := bstep (se 1 (by rfl) ⟨1109777, by rfl⟩ : syracuseStep 1479703 = 2219555) B2219555
theorem B693271 : Blo 690315 693271 := bstep (se 1 (by rfl) ⟨519953, by rfl⟩ : syracuseStep 693271 = 1039907) B1039907
theorem B693291 : Blo 690315 693291 := bstep (se 1 (by rfl) ⟨519968, by rfl⟩ : syracuseStep 693291 = 1039937) B1039937
theorem B693303 : Blo 690315 693303 := bstep (se 1 (by rfl) ⟨519977, by rfl⟩ : syracuseStep 693303 = 1039955) B1039955
theorem B1479745 : Blo 690315 1479745 := bstep (se 2 (by rfl) ⟨554904, by rfl⟩ : syracuseStep 1479745 = 1109809) B1109809
theorem B693323 : Blo 690315 693323 := bstep (se 1 (by rfl) ⟨519992, by rfl⟩ : syracuseStep 693323 = 1039985) B1039985
theorem B693335 : Blo 690315 693335 := bstep (se 1 (by rfl) ⟨520001, by rfl⟩ : syracuseStep 693335 = 1040003) B1040003
theorem B693355 : Blo 690315 693355 := bstep (se 1 (by rfl) ⟨520016, by rfl⟩ : syracuseStep 693355 = 1040033) B1040033
theorem B693367 : Blo 690315 693367 := bstep (se 1 (by rfl) ⟨520025, by rfl⟩ : syracuseStep 693367 = 1040051) B1040051
theorem B693387 : Blo 690315 693387 := bstep (se 1 (by rfl) ⟨520040, by rfl⟩ : syracuseStep 693387 = 1040081) B1040081
theorem B693399 : Blo 690315 693399 := bstep (se 1 (by rfl) ⟨520049, by rfl⟩ : syracuseStep 693399 = 1040099) B1040099
theorem B7902359 : Blo 690315 7902359 := bstep (se 1 (by rfl) ⟨5926769, by rfl⟩ : syracuseStep 7902359 = 11853539) B11853539
theorem B693419 : Blo 690315 693419 := bstep (se 1 (by rfl) ⟨520064, by rfl⟩ : syracuseStep 693419 = 1040129) B1040129
theorem B2331827 : Blo 690315 2331827 := bstep (se 1 (by rfl) ⟨1748870, by rfl⟩ : syracuseStep 2331827 = 3497741) B3497741
theorem B2626739 : Blo 690315 2626739 := bstep (se 1 (by rfl) ⟨1970054, by rfl⟩ : syracuseStep 2626739 = 3940109) B3940109
theorem B693431 : Blo 690315 693431 := bstep (se 1 (by rfl) ⟨520073, by rfl⟩ : syracuseStep 693431 = 1040147) B1040147
theorem B693451 : Blo 690315 693451 := bstep (se 1 (by rfl) ⟨520088, by rfl⟩ : syracuseStep 693451 = 1040177) B1040177
theorem B693463 : Blo 690315 693463 := bstep (se 1 (by rfl) ⟨520097, by rfl⟩ : syracuseStep 693463 = 1040195) B1040195
theorem B693483 : Blo 690315 693483 := bstep (se 1 (by rfl) ⟨520112, by rfl⟩ : syracuseStep 693483 = 1040225) B1040225
theorem B693495 : Blo 690315 693495 := bstep (se 1 (by rfl) ⟨520121, by rfl⟩ : syracuseStep 693495 = 1040243) B1040243
theorem B693515 : Blo 690315 693515 := bstep (se 1 (by rfl) ⟨520136, by rfl⟩ : syracuseStep 693515 = 1040273) B1040273
theorem B1971479 : Blo 690315 1971479 := bstep (se 1 (by rfl) ⟨1478609, by rfl⟩ : syracuseStep 1971479 = 2957219) B2957219
theorem B693527 : Blo 690315 693527 := bstep (se 1 (by rfl) ⟨520145, by rfl⟩ : syracuseStep 693527 = 1040291) B1040291
theorem B693547 : Blo 690315 693547 := bstep (se 1 (by rfl) ⟨520160, by rfl⟩ : syracuseStep 693547 = 1040321) B1040321
theorem B693559 : Blo 690315 693559 := bstep (se 1 (by rfl) ⟨520169, by rfl⟩ : syracuseStep 693559 = 1040339) B1040339
theorem B693579 : Blo 690315 693579 := bstep (se 1 (by rfl) ⟨520184, by rfl⟩ : syracuseStep 693579 = 1040369) B1040369
theorem B693591 : Blo 690315 693591 := bstep (se 1 (by rfl) ⟨520193, by rfl⟩ : syracuseStep 693591 = 1040387) B1040387
theorem B693611 : Blo 690315 693611 := bstep (se 1 (by rfl) ⟨520208, by rfl⟩ : syracuseStep 693611 = 1040417) B1040417
theorem B693623 : Blo 690315 693623 := bstep (se 1 (by rfl) ⟨520217, by rfl⟩ : syracuseStep 693623 = 1040435) B1040435
theorem B1316225 : Blo 690315 1316225 := bstep (se 2 (by rfl) ⟨493584, by rfl⟩ : syracuseStep 1316225 = 987169) B987169
theorem B693643 : Blo 690315 693643 := bstep (se 1 (by rfl) ⟨520232, by rfl⟩ : syracuseStep 693643 = 1040465) B1040465
theorem B693655 : Blo 690315 693655 := bstep (se 1 (by rfl) ⟨520241, by rfl⟩ : syracuseStep 693655 = 1040483) B1040483
theorem B693675 : Blo 690315 693675 := bstep (se 1 (by rfl) ⟨520256, by rfl⟩ : syracuseStep 693675 = 1040513) B1040513
theorem B693687 : Blo 690315 693687 := bstep (se 1 (by rfl) ⟨520265, by rfl⟩ : syracuseStep 693687 = 1040531) B1040531
theorem B2332097 : Blo 690315 2332097 := bstep (se 2 (by rfl) ⟨874536, by rfl⟩ : syracuseStep 2332097 = 1749073) B1749073
theorem B693707 : Blo 690315 693707 := bstep (se 1 (by rfl) ⟨520280, by rfl⟩ : syracuseStep 693707 = 1040561) B1040561
theorem B693719 : Blo 690315 693719 := bstep (se 1 (by rfl) ⟨520289, by rfl⟩ : syracuseStep 693719 = 1040579) B1040579
theorem B693739 : Blo 690315 693739 := bstep (se 1 (by rfl) ⟨520304, by rfl⟩ : syracuseStep 693739 = 1040609) B1040609
theorem B693751 : Blo 690315 693751 := bstep (se 1 (by rfl) ⟨520313, by rfl⟩ : syracuseStep 693751 = 1040627) B1040627
theorem B693771 : Blo 690315 693771 := bstep (se 1 (by rfl) ⟨520328, by rfl⟩ : syracuseStep 693771 = 1040657) B1040657
theorem B693783 : Blo 690315 693783 := bstep (se 1 (by rfl) ⟨520337, by rfl⟩ : syracuseStep 693783 = 1040675) B1040675
theorem B693803 : Blo 690315 693803 := bstep (se 1 (by rfl) ⟨520352, by rfl⟩ : syracuseStep 693803 = 1040705) B1040705
theorem B693815 : Blo 690315 693815 := bstep (se 1 (by rfl) ⟨520361, by rfl⟩ : syracuseStep 693815 = 1040723) B1040723
theorem B693835 : Blo 690315 693835 := bstep (se 1 (by rfl) ⟨520376, by rfl⟩ : syracuseStep 693835 = 1040753) B1040753
theorem B10688075 : Blo 690315 10688075 := bstep (se 1 (by rfl) ⟨8016056, by rfl⟩ : syracuseStep 10688075 = 16032113) B16032113
theorem B693847 : Blo 690315 693847 := bstep (se 1 (by rfl) ⟨520385, by rfl⟩ : syracuseStep 693847 = 1040771) B1040771
theorem B10098269 : Blo 690315 10098269 := bstep (se 3 (by rfl) ⟨1893425, by rfl⟩ : syracuseStep 10098269 = 3786851) B3786851
theorem B693867 : Blo 690315 693867 := bstep (se 1 (by rfl) ⟨520400, by rfl⟩ : syracuseStep 693867 = 1040801) B1040801
theorem B693879 : Blo 690315 693879 := bstep (se 1 (by rfl) ⟨520409, by rfl⟩ : syracuseStep 693879 = 1040819) B1040819
theorem B693899 : Blo 690315 693899 := bstep (se 1 (by rfl) ⟨520424, by rfl⟩ : syracuseStep 693899 = 1040849) B1040849
theorem B693911 : Blo 690315 693911 := bstep (se 1 (by rfl) ⟨520433, by rfl⟩ : syracuseStep 693911 = 1040867) B1040867
theorem B693931 : Blo 690315 693931 := bstep (se 1 (by rfl) ⟨520448, by rfl⟩ : syracuseStep 693931 = 1040897) B1040897
theorem B693943 : Blo 690315 693943 := bstep (se 1 (by rfl) ⟨520457, by rfl⟩ : syracuseStep 693943 = 1040915) B1040915
theorem B2102987 : Blo 690315 2102987 := bstep (se 1 (by rfl) ⟨1577240, by rfl⟩ : syracuseStep 2102987 = 3154481) B3154481
theorem B693963 : Blo 690315 693963 := bstep (se 1 (by rfl) ⟨520472, by rfl⟩ : syracuseStep 693963 = 1040945) B1040945
theorem B1316567 : Blo 690315 1316567 := bstep (se 1 (by rfl) ⟨987425, by rfl⟩ : syracuseStep 1316567 = 1974851) B1974851
theorem B693975 : Blo 690315 693975 := bstep (se 1 (by rfl) ⟨520481, by rfl⟩ : syracuseStep 693975 = 1040963) B1040963
theorem B1775321 : Blo 690315 1775321 := bstep (se 2 (by rfl) ⟨665745, by rfl⟩ : syracuseStep 1775321 = 1331491) B1331491
theorem B693995 : Blo 690315 693995 := bstep (se 1 (by rfl) ⟨520496, by rfl⟩ : syracuseStep 693995 = 1040993) B1040993
theorem B694007 : Blo 690315 694007 := bstep (se 1 (by rfl) ⟨520505, by rfl⟩ : syracuseStep 694007 = 1041011) B1041011
theorem B694027 : Blo 690315 694027 := bstep (se 1 (by rfl) ⟨520520, by rfl⟩ : syracuseStep 694027 = 1041041) B1041041
theorem B4724497 : Blo 690315 4724497 := bstep (se 2 (by rfl) ⟨1771686, by rfl⟩ : syracuseStep 4724497 = 3543373) B3543373
theorem B694039 : Blo 690315 694039 := bstep (se 1 (by rfl) ⟨520529, by rfl⟩ : syracuseStep 694039 = 1041059) B1041059
theorem B694059 : Blo 690315 694059 := bstep (se 1 (by rfl) ⟨520544, by rfl⟩ : syracuseStep 694059 = 1041089) B1041089
theorem B694071 : Blo 690315 694071 := bstep (se 1 (by rfl) ⟨520553, by rfl⟩ : syracuseStep 694071 = 1041107) B1041107
theorem B694091 : Blo 690315 694091 := bstep (se 1 (by rfl) ⟨520568, by rfl⟩ : syracuseStep 694091 = 1041137) B1041137
theorem B694103 : Blo 690315 694103 := bstep (se 1 (by rfl) ⟨520577, by rfl⟩ : syracuseStep 694103 = 1041155) B1041155
theorem B694123 : Blo 690315 694123 := bstep (se 1 (by rfl) ⟨520592, by rfl⟩ : syracuseStep 694123 = 1041185) B1041185
theorem B694135 : Blo 690315 694135 := bstep (se 1 (by rfl) ⟨520601, by rfl⟩ : syracuseStep 694135 = 1041203) B1041203
theorem B694155 : Blo 690315 694155 := bstep (se 1 (by rfl) ⟨520616, by rfl⟩ : syracuseStep 694155 = 1041233) B1041233
theorem B694167 : Blo 690315 694167 := bstep (se 1 (by rfl) ⟨520625, by rfl⟩ : syracuseStep 694167 = 1041251) B1041251
theorem B694187 : Blo 690315 694187 := bstep (se 1 (by rfl) ⟨520640, by rfl⟩ : syracuseStep 694187 = 1041281) B1041281
theorem B694199 : Blo 690315 694199 := bstep (se 1 (by rfl) ⟨520649, by rfl⟩ : syracuseStep 694199 = 1041299) B1041299
theorem B694219 : Blo 690315 694219 := bstep (se 1 (by rfl) ⟨520664, by rfl⟩ : syracuseStep 694219 = 1041329) B1041329
theorem B694231 : Blo 690315 694231 := bstep (se 1 (by rfl) ⟨520673, by rfl⟩ : syracuseStep 694231 = 1041347) B1041347
theorem B2332637 : Blo 690315 2332637 := bstep (se 3 (by rfl) ⟨437369, by rfl⟩ : syracuseStep 2332637 = 874739) B874739
theorem B694251 : Blo 690315 694251 := bstep (se 1 (by rfl) ⟨520688, by rfl⟩ : syracuseStep 694251 = 1041377) B1041377
theorem B694263 : Blo 690315 694263 := bstep (se 1 (by rfl) ⟨520697, by rfl⟩ : syracuseStep 694263 = 1041395) B1041395
theorem B694283 : Blo 690315 694283 := bstep (se 1 (by rfl) ⟨520712, by rfl⟩ : syracuseStep 694283 = 1041425) B1041425
theorem B694295 : Blo 690315 694295 := bstep (se 1 (by rfl) ⟨520721, by rfl⟩ : syracuseStep 694295 = 1041443) B1041443
theorem B1185817 : Blo 690315 1185817 := bstep (se 2 (by rfl) ⟨444681, by rfl⟩ : syracuseStep 1185817 = 889363) B889363
theorem B694315 : Blo 690315 694315 := bstep (se 1 (by rfl) ⟨520736, by rfl⟩ : syracuseStep 694315 = 1041473) B1041473
theorem B2955457 : Blo 690315 2955457 := bstep (se 2 (by rfl) ⟨1108296, by rfl⟩ : syracuseStep 2955457 = 2216593) B2216593
theorem B5249285 : Blo 690315 5249285 := bstep (se 4 (by rfl) ⟨492120, by rfl⟩ : syracuseStep 5249285 = 984241) B984241
theorem B1317235 : Blo 690315 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B1972811 : Blo 690315 1972811 := bstep (se 1 (by rfl) ⟨1479608, by rfl⟩ : syracuseStep 1972811 = 2959217) B2959217
theorem B2628227 : Blo 690315 2628227 := bstep (se 1 (by rfl) ⟨1971170, by rfl⟩ : syracuseStep 2628227 = 3942341) B3942341
theorem B1481419 : Blo 690315 1481419 := bstep (se 1 (by rfl) ⟨1111064, by rfl⟩ : syracuseStep 1481419 = 2222129) B2222129
theorem B1317683 : Blo 690315 1317683 := bstep (se 1 (by rfl) ⟨988262, by rfl⟩ : syracuseStep 1317683 = 1976525) B1976525
theorem B1317721 : Blo 690315 1317721 := bstep (se 2 (by rfl) ⟨494145, by rfl⟩ : syracuseStep 1317721 = 988291) B988291
theorem B2104157 : Blo 690315 2104157 := bstep (se 3 (by rfl) ⟨394529, by rfl⟩ : syracuseStep 2104157 = 789059) B789059
theorem B1973143 : Blo 690315 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B1481753 : Blo 690315 1481753 := bstep (se 2 (by rfl) ⟨555657, by rfl⟩ : syracuseStep 1481753 = 1111315) B1111315
theorem B2333771 : Blo 690315 2333771 := bstep (se 1 (by rfl) ⟨1750328, by rfl⟩ : syracuseStep 2333771 = 3500657) B3500657
theorem B2628683 : Blo 690315 2628683 := bstep (se 1 (by rfl) ⟨1971512, by rfl⟩ : syracuseStep 2628683 = 3943025) B3943025
theorem B2628881 : Blo 690315 2628881 := bstep (se 2 (by rfl) ⟨985830, by rfl⟩ : syracuseStep 2628881 = 1971661) B1971661
theorem B3513617 : Blo 690315 3513617 := bstep (se 2 (by rfl) ⟨1317606, by rfl⟩ : syracuseStep 3513617 = 2635213) B2635213
theorem B2334041 : Blo 690315 2334041 := bstep (se 2 (by rfl) ⟨875265, by rfl⟩ : syracuseStep 2334041 = 1750531) B1750531
theorem B3939677 : Blo 690315 3939677 := bstep (se 3 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 3939677 = 1477379) B1477379
theorem B3513779 : Blo 690315 3513779 := bstep (se 1 (by rfl) ⟨2635334, by rfl⟩ : syracuseStep 3513779 = 5270669) B5270669
theorem B2956945 : Blo 690315 2956945 := bstep (se 2 (by rfl) ⟨1108854, by rfl⟩ : syracuseStep 2956945 = 2217709) B2217709
theorem B1777331 : Blo 690315 1777331 := bstep (se 1 (by rfl) ⟨1332998, by rfl⟩ : syracuseStep 1777331 = 2665997) B2665997
theorem B16883633 : Blo 690315 16883633 := bstep (se 2 (by rfl) ⟨6331362, by rfl⟩ : syracuseStep 16883633 = 12662725) B12662725
theorem B2334743 : Blo 690315 2334743 := bstep (se 1 (by rfl) ⟨1751057, by rfl⟩ : syracuseStep 2334743 = 3502115) B3502115
theorem B2629655 : Blo 690315 2629655 := bstep (se 1 (by rfl) ⟨1972241, by rfl⟩ : syracuseStep 2629655 = 3944483) B3944483
theorem B3940427 : Blo 690315 3940427 := bstep (se 1 (by rfl) ⟨2955320, by rfl⟩ : syracuseStep 3940427 = 5910641) B5910641
theorem B1974451 : Blo 690315 1974451 := bstep (se 1 (by rfl) ⟨1480838, by rfl⟩ : syracuseStep 1974451 = 2961677) B2961677
theorem B2629853 : Blo 690315 2629853 := bstep (se 3 (by rfl) ⟨493097, by rfl⟩ : syracuseStep 2629853 = 986195) B986195
theorem B2105689 : Blo 690315 2105689 := bstep (se 2 (by rfl) ⟨789633, by rfl⟩ : syracuseStep 2105689 = 1579267) B1579267
theorem B3318317 : Blo 690315 3318317 := bstep (se 3 (by rfl) ⟨622184, by rfl⟩ : syracuseStep 3318317 = 1244369) B1244369
theorem B2335283 : Blo 690315 2335283 := bstep (se 1 (by rfl) ⟨1751462, by rfl⟩ : syracuseStep 2335283 = 3502925) B3502925
theorem B5251715 : Blo 690315 5251715 := bstep (se 1 (by rfl) ⟨3938786, by rfl⟩ : syracuseStep 5251715 = 7877573) B7877573
theorem B11805425 : Blo 690315 11805425 := bstep (se 2 (by rfl) ⟨4427034, by rfl⟩ : syracuseStep 11805425 = 8854069) B8854069
theorem B2335553 : Blo 690315 2335553 := bstep (se 2 (by rfl) ⟨875832, by rfl⟩ : syracuseStep 2335553 = 1751665) B1751665
theorem B1975499 : Blo 690315 1975499 := bstep (se 1 (by rfl) ⟨1481624, by rfl⟩ : syracuseStep 1975499 = 2963249) B2963249
theorem B2336093 : Blo 690315 2336093 := bstep (se 3 (by rfl) ⟨438017, by rfl⟩ : syracuseStep 2336093 = 876035) B876035
theorem B3155393 : Blo 690315 3155393 := bstep (se 2 (by rfl) ⟨1183272, by rfl⟩ : syracuseStep 3155393 = 2366545) B2366545
theorem B3942067 : Blo 690315 3942067 := bstep (se 1 (by rfl) ⟨2956550, by rfl⟩ : syracuseStep 3942067 = 5913101) B5913101
theorem B35923661 : Blo 690315 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B1124057 : Blo 690315 1124057 := bstep (se 2 (by rfl) ⟨421521, by rfl⟩ : syracuseStep 1124057 = 843043) B843043
theorem B4204561 : Blo 690315 4204561 := bstep (se 2 (by rfl) ⟨1576710, by rfl⟩ : syracuseStep 4204561 = 3153421) B3153421
theorem B1419329 : Blo 690315 1419329 := bstep (se 2 (by rfl) ⟨532248, by rfl⟩ : syracuseStep 1419329 = 1064497) B1064497
theorem B2631811 : Blo 690315 2631811 := bstep (se 1 (by rfl) ⟨1973858, by rfl⟩ : syracuseStep 2631811 = 3947717) B3947717
theorem B1583425 : Blo 690315 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B2632115 : Blo 690315 2632115 := bstep (se 1 (by rfl) ⟨1974086, by rfl⟩ : syracuseStep 2632115 = 3948173) B3948173
theorem B1747403 : Blo 690315 1747403 := bstep (se 1 (by rfl) ⟨1310552, by rfl⟩ : syracuseStep 1747403 = 2621105) B2621105
theorem B2337227 : Blo 690315 2337227 := bstep (se 1 (by rfl) ⟨1752920, by rfl⟩ : syracuseStep 2337227 = 3505841) B3505841
theorem B2960003 : Blo 690315 2960003 := bstep (se 1 (by rfl) ⟨2220002, by rfl⟩ : syracuseStep 2960003 = 4440005) B4440005
theorem B2337497 : Blo 690315 2337497 := bstep (se 2 (by rfl) ⟨876561, by rfl⟩ : syracuseStep 2337497 = 1753123) B1753123
theorem B1977139 : Blo 690315 1977139 := bstep (se 1 (by rfl) ⟨1482854, by rfl⟩ : syracuseStep 1977139 = 2965709) B2965709
theorem B1747777 : Blo 690315 1747777 := bstep (se 2 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 1747777 = 1310833) B1310833
theorem B1420249 : Blo 690315 1420249 := bstep (se 2 (by rfl) ⟨532593, by rfl⟩ : syracuseStep 1420249 = 1065187) B1065187
theorem B2632769 : Blo 690315 2632769 := bstep (se 2 (by rfl) ⟨987288, by rfl⟩ : syracuseStep 2632769 = 1974577) B1974577
theorem B3943525 : Blo 690315 3943525 := bstep (se 4 (by rfl) ⟨369705, by rfl⟩ : syracuseStep 3943525 = 739411) B739411
theorem B1682635 : Blo 690315 1682635 := bstep (se 1 (by rfl) ⟨1261976, by rfl⟩ : syracuseStep 1682635 = 2523953) B2523953
theorem B2993425 : Blo 690315 2993425 := bstep (se 2 (by rfl) ⟨1122534, by rfl⟩ : syracuseStep 2993425 = 2245069) B2245069
theorem B1748375 : Blo 690315 1748375 := bstep (se 1 (by rfl) ⟨1311281, by rfl⟩ : syracuseStep 1748375 = 2622563) B2622563
theorem B2338199 : Blo 690315 2338199 := bstep (se 1 (by rfl) ⟨1753649, by rfl⟩ : syracuseStep 2338199 = 3507299) B3507299
theorem B830935 : Blo 690315 830935 := bstep (se 1 (by rfl) ⟨623201, by rfl⟩ : syracuseStep 830935 = 1246403) B1246403
theorem B3157507 : Blo 690315 3157507 := bstep (se 1 (by rfl) ⟨2368130, by rfl⟩ : syracuseStep 3157507 = 4736261) B4736261
theorem B2666029 : Blo 690315 2666029 := bstep (se 3 (by rfl) ⟨499880, by rfl⟩ : syracuseStep 2666029 = 999761) B999761
theorem B3747421 : Blo 690315 3747421 := bstep (se 3 (by rfl) ⟨702641, by rfl⟩ : syracuseStep 3747421 = 1405283) B1405283
theorem B10628759 : Blo 690315 10628759 := bstep (se 1 (by rfl) ⟨7971569, by rfl⟩ : syracuseStep 10628759 = 15943139) B15943139
theorem B831127 : Blo 690315 831127 := bstep (se 1 (by rfl) ⟨623345, by rfl⟩ : syracuseStep 831127 = 1246691) B1246691
theorem B1421057 : Blo 690315 1421057 := bstep (se 2 (by rfl) ⟨532896, by rfl⟩ : syracuseStep 1421057 = 1065793) B1065793
theorem B6762341 : Blo 690315 6762341 := bstep (se 4 (by rfl) ⟨633969, by rfl⟩ : syracuseStep 6762341 = 1267939) B1267939
theorem B2338739 : Blo 690315 2338739 := bstep (se 1 (by rfl) ⟨1754054, by rfl⟩ : syracuseStep 2338739 = 3508109) B3508109
theorem B5255117 : Blo 690315 5255117 := bstep (se 3 (by rfl) ⟨985334, by rfl⟩ : syracuseStep 5255117 = 1970669) B1970669
theorem B7483427 : Blo 690315 7483427 := bstep (se 1 (by rfl) ⟨5612570, by rfl⟩ : syracuseStep 7483427 = 11225141) B11225141
theorem B35926091 : Blo 690315 35926091 := bstep (se 1 (by rfl) ⟨26944568, by rfl⟩ : syracuseStep 35926091 = 53889137) B53889137
theorem B3747941 : Blo 690315 3747941 := bstep (se 4 (by rfl) ⟨351369, by rfl⟩ : syracuseStep 3747941 = 702739) B702739
theorem B3551363 : Blo 690315 3551363 := bstep (se 1 (by rfl) ⟨2663522, by rfl⟩ : syracuseStep 3551363 = 5327045) B5327045
theorem B1749185 : Blo 690315 1749185 := bstep (se 2 (by rfl) ⟨655944, by rfl⟩ : syracuseStep 1749185 = 1311889) B1311889
theorem B2339009 : Blo 690315 2339009 := bstep (se 2 (by rfl) ⟨877128, by rfl⟩ : syracuseStep 2339009 = 1754257) B1754257
theorem B2634029 : Blo 690315 2634029 := bstep (se 3 (by rfl) ⟨493880, by rfl⟩ : syracuseStep 2634029 = 987761) B987761
theorem B2634059 : Blo 690315 2634059 := bstep (se 1 (by rfl) ⟨1975544, by rfl⟩ : syracuseStep 2634059 = 3951089) B3951089
theorem B5255603 : Blo 690315 5255603 := bstep (se 1 (by rfl) ⟨3941702, by rfl⟩ : syracuseStep 5255603 = 7883405) B7883405
theorem B1749721 : Blo 690315 1749721 := bstep (se 2 (by rfl) ⟨656145, by rfl⟩ : syracuseStep 1749721 = 1312291) B1312291
theorem B2339549 : Blo 690315 2339549 := bstep (se 3 (by rfl) ⟨438665, by rfl⟩ : syracuseStep 2339549 = 877331) B877331
theorem B1553291 : Blo 690315 1553291 := bstep (se 1 (by rfl) ⟨1164968, by rfl⟩ : syracuseStep 1553291 = 2329937) B2329937
theorem B1553345 : Blo 690315 1553345 := bstep (se 2 (by rfl) ⟨582504, by rfl⟩ : syracuseStep 1553345 = 1165009) B1165009
theorem B2634713 : Blo 690315 2634713 := bstep (se 2 (by rfl) ⟨988017, by rfl⟩ : syracuseStep 2634713 = 1976035) B1976035
theorem B5911703 : Blo 690315 5911703 := bstep (se 1 (by rfl) ⟨4433777, by rfl⟩ : syracuseStep 5911703 = 8867555) B8867555
theorem B1553561 : Blo 690315 1553561 := bstep (se 2 (by rfl) ⟨582585, by rfl⟩ : syracuseStep 1553561 = 1165171) B1165171
theorem B1553651 : Blo 690315 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B1553687 : Blo 690315 1553687 := bstep (se 1 (by rfl) ⟨1165265, by rfl⟩ : syracuseStep 1553687 = 2330531) B2330531
theorem B2635031 : Blo 690315 2635031 := bstep (se 1 (by rfl) ⟨1976273, by rfl⟩ : syracuseStep 2635031 = 3952547) B3952547
theorem B4437341 : Blo 690315 4437341 := bstep (se 3 (by rfl) ⟨832001, by rfl⟩ : syracuseStep 4437341 = 1664003) B1664003
theorem B1553867 : Blo 690315 1553867 := bstep (se 1 (by rfl) ⟨1165400, by rfl⟩ : syracuseStep 1553867 = 2330801) B2330801
theorem B102282709 : Blo 690315 102282709 := bstep (se 7 (by rfl) ⟨1198625, by rfl⟩ : syracuseStep 102282709 = 2397251) B2397251
theorem B1553921 : Blo 690315 1553921 := bstep (se 2 (by rfl) ⟨582720, by rfl⟩ : syracuseStep 1553921 = 1165441) B1165441
theorem B1554137 : Blo 690315 1554137 := bstep (se 2 (by rfl) ⟨582801, by rfl⟩ : syracuseStep 1554137 = 1165603) B1165603
theorem B1554227 : Blo 690315 1554227 := bstep (se 1 (by rfl) ⟨1165670, by rfl⟩ : syracuseStep 1554227 = 2331341) B2331341
theorem B1750835 : Blo 690315 1750835 := bstep (se 1 (by rfl) ⟨1313126, by rfl⟩ : syracuseStep 1750835 = 2626253) B2626253
theorem B2340683 : Blo 690315 2340683 := bstep (se 1 (by rfl) ⟨1755512, by rfl⟩ : syracuseStep 2340683 = 3511025) B3511025
theorem B1554263 : Blo 690315 1554263 := bstep (se 1 (by rfl) ⟨1165697, by rfl⟩ : syracuseStep 1554263 = 2331395) B2331395
theorem B2111321 : Blo 690315 2111321 := bstep (se 2 (by rfl) ⟨791745, by rfl⟩ : syracuseStep 2111321 = 1583491) B1583491
theorem B5257061 : Blo 690315 5257061 := bstep (se 4 (by rfl) ⟨492849, by rfl⟩ : syracuseStep 5257061 = 985699) B985699
theorem B2635699 : Blo 690315 2635699 := bstep (se 1 (by rfl) ⟨1976774, by rfl⟩ : syracuseStep 2635699 = 3953549) B3953549
theorem B1554443 : Blo 690315 1554443 := bstep (se 1 (by rfl) ⟨1165832, by rfl⟩ : syracuseStep 1554443 = 2331665) B2331665
theorem B1554497 : Blo 690315 1554497 := bstep (se 2 (by rfl) ⟨582936, by rfl⟩ : syracuseStep 1554497 = 1165873) B1165873
theorem B1751129 : Blo 690315 1751129 := bstep (se 2 (by rfl) ⟨656673, by rfl⟩ : syracuseStep 1751129 = 1313347) B1313347
theorem B2340953 : Blo 690315 2340953 := bstep (se 2 (by rfl) ⟨877857, by rfl⟩ : syracuseStep 2340953 = 1755715) B1755715
theorem B1554713 : Blo 690315 1554713 := bstep (se 2 (by rfl) ⟨583017, by rfl⟩ : syracuseStep 1554713 = 1166035) B1166035
theorem B5257547 : Blo 690315 5257547 := bstep (se 1 (by rfl) ⟨3943160, by rfl⟩ : syracuseStep 5257547 = 7886321) B7886321
theorem B1554803 : Blo 690315 1554803 := bstep (se 1 (by rfl) ⟨1166102, by rfl⟩ : syracuseStep 1554803 = 2332205) B2332205
theorem B1554839 : Blo 690315 1554839 := bstep (se 1 (by rfl) ⟨1166129, by rfl⟩ : syracuseStep 1554839 = 2332259) B2332259
theorem B1555019 : Blo 690315 1555019 := bstep (se 1 (by rfl) ⟨1166264, by rfl⟩ : syracuseStep 1555019 = 2332529) B2332529
theorem B1555073 : Blo 690315 1555073 := bstep (se 2 (by rfl) ⟨583152, by rfl⟩ : syracuseStep 1555073 = 1166305) B1166305
theorem B3160721 : Blo 690315 3160721 := bstep (se 2 (by rfl) ⟨1185270, by rfl⟩ : syracuseStep 3160721 = 2370541) B2370541
theorem B2341655 : Blo 690315 2341655 := bstep (se 1 (by rfl) ⟨1756241, by rfl⟩ : syracuseStep 2341655 = 3512483) B3512483
theorem B2964275 : Blo 690315 2964275 := bstep (se 1 (by rfl) ⟨2223206, by rfl⟩ : syracuseStep 2964275 = 4446413) B4446413
theorem B1555289 : Blo 690315 1555289 := bstep (se 2 (by rfl) ⟨583233, by rfl⟩ : syracuseStep 1555289 = 1166467) B1166467
theorem B1555379 : Blo 690315 1555379 := bstep (se 1 (by rfl) ⟨1166534, by rfl⟩ : syracuseStep 1555379 = 2333069) B2333069
theorem B3161011 : Blo 690315 3161011 := bstep (se 1 (by rfl) ⟨2370758, by rfl⟩ : syracuseStep 3161011 = 4741517) B4741517
theorem B1555415 : Blo 690315 1555415 := bstep (se 1 (by rfl) ⟨1166561, by rfl⟩ : syracuseStep 1555415 = 2333123) B2333123
theorem B30293027 : Blo 690315 30293027 := bstep (se 1 (by rfl) ⟨22719770, by rfl⟩ : syracuseStep 30293027 = 45439541) B45439541
theorem B1555595 : Blo 690315 1555595 := bstep (se 1 (by rfl) ⟨1166696, by rfl⟩ : syracuseStep 1555595 = 2333393) B2333393
theorem B1555649 : Blo 690315 1555649 := bstep (se 2 (by rfl) ⟨583368, by rfl⟩ : syracuseStep 1555649 = 1166737) B1166737
theorem B2342195 : Blo 690315 2342195 := bstep (se 1 (by rfl) ⟨1756646, by rfl⟩ : syracuseStep 2342195 = 3513293) B3513293
theorem B1555865 : Blo 690315 1555865 := bstep (se 2 (by rfl) ⟨583449, by rfl⟩ : syracuseStep 1555865 = 1166899) B1166899
theorem B5324237 : Blo 690315 5324237 := bstep (se 3 (by rfl) ⟨998294, by rfl⟩ : syracuseStep 5324237 = 1996589) B1996589
theorem B1555955 : Blo 690315 1555955 := bstep (se 1 (by rfl) ⟨1166966, by rfl⟩ : syracuseStep 1555955 = 2333933) B2333933
theorem B1555991 : Blo 690315 1555991 := bstep (se 1 (by rfl) ⟨1166993, by rfl⟩ : syracuseStep 1555991 = 2333987) B2333987
theorem B2342465 : Blo 690315 2342465 := bstep (se 2 (by rfl) ⟨878424, by rfl⟩ : syracuseStep 2342465 = 1756849) B1756849
theorem B6307429 : Blo 690315 6307429 := bstep (se 4 (by rfl) ⟨591321, by rfl⟩ : syracuseStep 6307429 = 1182643) B1182643
theorem B1556171 : Blo 690315 1556171 := bstep (se 1 (by rfl) ⟨1167128, by rfl⟩ : syracuseStep 1556171 = 2334257) B2334257
theorem B1752779 : Blo 690315 1752779 := bstep (se 1 (by rfl) ⟨1314584, by rfl⟩ : syracuseStep 1752779 = 2629169) B2629169
theorem B1556225 : Blo 690315 1556225 := bstep (se 2 (by rfl) ⟨583584, by rfl⟩ : syracuseStep 1556225 = 1167169) B1167169
theorem B933655 : Blo 690315 933655 := bstep (se 1 (by rfl) ⟨700241, by rfl⟩ : syracuseStep 933655 = 1400483) B1400483
theorem B1556441 : Blo 690315 1556441 := bstep (se 2 (by rfl) ⟨583665, by rfl⟩ : syracuseStep 1556441 = 1167331) B1167331
theorem B1556531 : Blo 690315 1556531 := bstep (se 1 (by rfl) ⟨1167398, by rfl⟩ : syracuseStep 1556531 = 2334797) B2334797
theorem B1556567 : Blo 690315 1556567 := bstep (se 1 (by rfl) ⟨1167425, by rfl⟩ : syracuseStep 1556567 = 2334851) B2334851
theorem B2343005 : Blo 690315 2343005 := bstep (se 3 (by rfl) ⟨439313, by rfl⟩ : syracuseStep 2343005 = 878627) B878627
theorem B737515 : Blo 690315 737515 := bstep (se 1 (by rfl) ⟨553136, by rfl⟩ : syracuseStep 737515 = 1106273) B1106273
theorem B1556747 : Blo 690315 1556747 := bstep (se 1 (by rfl) ⟨1167560, by rfl⟩ : syracuseStep 1556747 = 2335121) B2335121
theorem B1556801 : Blo 690315 1556801 := bstep (se 2 (by rfl) ⟨583800, by rfl⟩ : syracuseStep 1556801 = 1167601) B1167601
theorem B7487923 : Blo 690315 7487923 := bstep (se 1 (by rfl) ⟨5615942, by rfl⟩ : syracuseStep 7487923 = 11231885) B11231885
theorem B1557017 : Blo 690315 1557017 := bstep (se 2 (by rfl) ⟨583881, by rfl⟩ : syracuseStep 1557017 = 1167763) B1167763
theorem B1557107 : Blo 690315 1557107 := bstep (se 1 (by rfl) ⟨1167830, by rfl⟩ : syracuseStep 1557107 = 2335661) B2335661
theorem B1557143 : Blo 690315 1557143 := bstep (se 1 (by rfl) ⟨1167857, by rfl⟩ : syracuseStep 1557143 = 2335715) B2335715
theorem B1753751 : Blo 690315 1753751 := bstep (se 1 (by rfl) ⟨1315313, by rfl⟩ : syracuseStep 1753751 = 2630627) B2630627
theorem B3556057 : Blo 690315 3556057 := bstep (se 2 (by rfl) ⟨1333521, by rfl⟩ : syracuseStep 3556057 = 2667043) B2667043
theorem B3949357 : Blo 690315 3949357 := bstep (se 3 (by rfl) ⟨740504, by rfl⟩ : syracuseStep 3949357 = 1481009) B1481009
theorem B1557323 : Blo 690315 1557323 := bstep (se 1 (by rfl) ⟨1167992, by rfl⟩ : syracuseStep 1557323 = 2335985) B2335985
theorem B2802521 : Blo 690315 2802521 := bstep (se 2 (by rfl) ⟨1050945, by rfl⟩ : syracuseStep 2802521 = 2101891) B2101891
theorem B1557377 : Blo 690315 1557377 := bstep (se 2 (by rfl) ⟨584016, by rfl⟩ : syracuseStep 1557377 = 1168033) B1168033
theorem B2802653 : Blo 690315 2802653 := bstep (se 3 (by rfl) ⟨525497, by rfl⟩ : syracuseStep 2802653 = 1050995) B1050995
theorem B1557593 : Blo 690315 1557593 := bstep (se 2 (by rfl) ⟨584097, by rfl⟩ : syracuseStep 1557593 = 1168195) B1168195
theorem B1557683 : Blo 690315 1557683 := bstep (se 1 (by rfl) ⟨1168262, by rfl⟩ : syracuseStep 1557683 = 2336525) B2336525
theorem B2213057 : Blo 690315 2213057 := bstep (se 2 (by rfl) ⟨829896, by rfl⟩ : syracuseStep 2213057 = 1659793) B1659793
theorem B1557719 : Blo 690315 1557719 := bstep (se 1 (by rfl) ⟨1168289, by rfl⟩ : syracuseStep 1557719 = 2336579) B2336579
theorem B1754419 : Blo 690315 1754419 := bstep (se 1 (by rfl) ⟨1315814, by rfl⟩ : syracuseStep 1754419 = 2631629) B2631629
theorem B1557899 : Blo 690315 1557899 := bstep (se 1 (by rfl) ⟨1168424, by rfl⟩ : syracuseStep 1557899 = 2336849) B2336849
theorem B1262999 : Blo 690315 1262999 := bstep (se 1 (by rfl) ⟨947249, by rfl⟩ : syracuseStep 1262999 = 1894499) B1894499
theorem B1557953 : Blo 690315 1557953 := bstep (se 2 (by rfl) ⟨584232, by rfl⟩ : syracuseStep 1557953 = 1168465) B1168465
theorem B1754561 : Blo 690315 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B738839 : Blo 690315 738839 := bstep (se 1 (by rfl) ⟨554129, by rfl⟩ : syracuseStep 738839 = 1108259) B1108259
theorem B3327581 : Blo 690315 3327581 := bstep (se 3 (by rfl) ⟨623921, by rfl⟩ : syracuseStep 3327581 = 1247843) B1247843
theorem B738967 : Blo 690315 738967 := bstep (se 1 (by rfl) ⟨554225, by rfl⟩ : syracuseStep 738967 = 1108451) B1108451
theorem B1558169 : Blo 690315 1558169 := bstep (se 2 (by rfl) ⟨584313, by rfl⟩ : syracuseStep 1558169 = 1168627) B1168627
theorem B1558259 : Blo 690315 1558259 := bstep (se 1 (by rfl) ⟨1168694, by rfl⟩ : syracuseStep 1558259 = 2337389) B2337389
theorem B1558295 : Blo 690315 1558295 := bstep (se 1 (by rfl) ⟨1168721, by rfl⟩ : syracuseStep 1558295 = 2337443) B2337443
theorem B4507571 : Blo 690315 4507571 := bstep (se 1 (by rfl) ⟨3380678, by rfl⟩ : syracuseStep 4507571 = 6761357) B6761357
theorem B1165259 : Blo 690315 1165259 := bstep (se 1 (by rfl) ⟨873944, by rfl⟩ : syracuseStep 1165259 = 1747889) B1747889
theorem B1558475 : Blo 690315 1558475 := bstep (se 1 (by rfl) ⟨1168856, by rfl⟩ : syracuseStep 1558475 = 2337713) B2337713
theorem B1558529 : Blo 690315 1558529 := bstep (se 2 (by rfl) ⟨584448, by rfl⟩ : syracuseStep 1558529 = 1168897) B1168897
theorem B1165387 : Blo 690315 1165387 := bstep (se 1 (by rfl) ⟨874040, by rfl⟩ : syracuseStep 1165387 = 1748081) B1748081
theorem B739531 : Blo 690315 739531 := bstep (se 1 (by rfl) ⟨554648, by rfl⟩ : syracuseStep 739531 = 1109297) B1109297
theorem B1165529 : Blo 690315 1165529 := bstep (se 2 (by rfl) ⟨437073, by rfl⟩ : syracuseStep 1165529 = 874147) B874147
theorem B1558745 : Blo 690315 1558745 := bstep (se 2 (by rfl) ⟨584529, by rfl⟩ : syracuseStep 1558745 = 1169059) B1169059
theorem B1558835 : Blo 690315 1558835 := bstep (se 1 (by rfl) ⟨1169126, by rfl⟩ : syracuseStep 1558835 = 2338253) B2338253
theorem B1558871 : Blo 690315 1558871 := bstep (se 1 (by rfl) ⟨1169153, by rfl⟩ : syracuseStep 1558871 = 2338307) B2338307
theorem B1165657 : Blo 690315 1165657 := bstep (se 2 (by rfl) ⟨437121, by rfl⟩ : syracuseStep 1165657 = 874243) B874243
theorem B739787 : Blo 690315 739787 := bstep (se 1 (by rfl) ⟨554840, by rfl⟩ : syracuseStep 739787 = 1109681) B1109681
theorem B1559051 : Blo 690315 1559051 := bstep (se 1 (by rfl) ⟨1169288, by rfl⟩ : syracuseStep 1559051 = 2338577) B2338577
theorem B1264153 : Blo 690315 1264153 := bstep (se 2 (by rfl) ⟨474057, by rfl⟩ : syracuseStep 1264153 = 948115) B948115
theorem B1559105 : Blo 690315 1559105 := bstep (se 2 (by rfl) ⟨584664, by rfl⟩ : syracuseStep 1559105 = 1169329) B1169329
theorem B1755827 : Blo 690315 1755827 := bstep (se 1 (by rfl) ⟨1316870, by rfl⟩ : syracuseStep 1755827 = 2633741) B2633741
theorem B1559321 : Blo 690315 1559321 := bstep (se 2 (by rfl) ⟨584745, by rfl⟩ : syracuseStep 1559321 = 1169491) B1169491
theorem B5917475 : Blo 690315 5917475 := bstep (se 1 (by rfl) ⟨4438106, by rfl⟩ : syracuseStep 5917475 = 8876213) B8876213
theorem B3164993 : Blo 690315 3164993 := bstep (se 2 (by rfl) ⟨1186872, by rfl⟩ : syracuseStep 3164993 = 2373745) B2373745
theorem B1559411 : Blo 690315 1559411 := bstep (se 1 (by rfl) ⟨1169558, by rfl⟩ : syracuseStep 1559411 = 2339117) B2339117
theorem B1166231 : Blo 690315 1166231 := bstep (se 1 (by rfl) ⟨874673, by rfl⟩ : syracuseStep 1166231 = 1749347) B1749347
theorem B1559447 : Blo 690315 1559447 := bstep (se 1 (by rfl) ⟨1169585, by rfl⟩ : syracuseStep 1559447 = 2339171) B2339171
theorem B2214877 : Blo 690315 2214877 := bstep (se 3 (by rfl) ⟨415289, by rfl⟩ : syracuseStep 2214877 = 830579) B830579
theorem B1166359 : Blo 690315 1166359 := bstep (se 1 (by rfl) ⟨874769, by rfl⟩ : syracuseStep 1166359 = 1749539) B1749539
theorem B1559627 : Blo 690315 1559627 := bstep (se 1 (by rfl) ⟨1169720, by rfl⟩ : syracuseStep 1559627 = 2339441) B2339441
theorem B1559681 : Blo 690315 1559681 := bstep (se 2 (by rfl) ⟨584880, by rfl⟩ : syracuseStep 1559681 = 1169761) B1169761
theorem B1756363 : Blo 690315 1756363 := bstep (se 1 (by rfl) ⟨1317272, by rfl⟩ : syracuseStep 1756363 = 2634545) B2634545
theorem B1035479 : Blo 690315 1035479 := bstep (se 1 (by rfl) ⟨776609, by rfl⟩ : syracuseStep 1035479 = 1553219) B1553219
theorem B1035545 : Blo 690315 1035545 := bstep (se 2 (by rfl) ⟨388329, by rfl⟩ : syracuseStep 1035545 = 776659) B776659
theorem B4443437 : Blo 690315 4443437 := bstep (se 3 (by rfl) ⟨833144, by rfl⟩ : syracuseStep 4443437 = 1666289) B1666289
theorem B1559897 : Blo 690315 1559897 := bstep (se 2 (by rfl) ⟨584961, by rfl⟩ : syracuseStep 1559897 = 1169923) B1169923
theorem B1756505 : Blo 690315 1756505 := bstep (se 2 (by rfl) ⟨658689, by rfl⟩ : syracuseStep 1756505 = 1317379) B1317379
theorem B1035659 : Blo 690315 1035659 := bstep (se 1 (by rfl) ⟨776744, by rfl⟩ : syracuseStep 1035659 = 1553489) B1553489
theorem B1035671 : Blo 690315 1035671 := bstep (se 1 (by rfl) ⟨776753, by rfl⟩ : syracuseStep 1035671 = 1553507) B1553507
theorem B1559987 : Blo 690315 1559987 := bstep (se 1 (by rfl) ⟨1169990, by rfl⟩ : syracuseStep 1559987 = 2339981) B2339981
theorem B1560023 : Blo 690315 1560023 := bstep (se 1 (by rfl) ⟨1170017, by rfl⟩ : syracuseStep 1560023 = 2340035) B2340035
theorem B1035737 : Blo 690315 1035737 := bstep (se 2 (by rfl) ⟨388401, by rfl⟩ : syracuseStep 1035737 = 776803) B776803
theorem B5262893 : Blo 690315 5262893 := bstep (se 3 (by rfl) ⟨986792, by rfl⟩ : syracuseStep 5262893 = 1973585) B1973585
theorem B1035851 : Blo 690315 1035851 := bstep (se 1 (by rfl) ⟨776888, by rfl⟩ : syracuseStep 1035851 = 1553777) B1553777
theorem B1035863 : Blo 690315 1035863 := bstep (se 1 (by rfl) ⟨776897, by rfl⟩ : syracuseStep 1035863 = 1553795) B1553795
theorem B1166987 : Blo 690315 1166987 := bstep (se 1 (by rfl) ⟨875240, by rfl⟩ : syracuseStep 1166987 = 1750481) B1750481
theorem B1560203 : Blo 690315 1560203 := bstep (se 1 (by rfl) ⟨1170152, by rfl⟩ : syracuseStep 1560203 = 2340305) B2340305
theorem B1035929 : Blo 690315 1035929 := bstep (se 2 (by rfl) ⟨388473, by rfl⟩ : syracuseStep 1035929 = 776947) B776947
theorem B1560257 : Blo 690315 1560257 := bstep (se 2 (by rfl) ⟨585096, by rfl⟩ : syracuseStep 1560257 = 1170193) B1170193
theorem B1036043 : Blo 690315 1036043 := bstep (se 1 (by rfl) ⟨777032, by rfl⟩ : syracuseStep 1036043 = 1554065) B1554065
theorem B1167115 : Blo 690315 1167115 := bstep (se 1 (by rfl) ⟨875336, by rfl⟩ : syracuseStep 1167115 = 1750673) B1750673
theorem B1036055 : Blo 690315 1036055 := bstep (se 1 (by rfl) ⟨777041, by rfl⟩ : syracuseStep 1036055 = 1554083) B1554083
theorem B1330967 : Blo 690315 1330967 := bstep (se 1 (by rfl) ⟨998225, by rfl⟩ : syracuseStep 1330967 = 1996451) B1996451
theorem B5623597 : Blo 690315 5623597 := bstep (se 3 (by rfl) ⟨1054424, by rfl⟩ : syracuseStep 5623597 = 2108849) B2108849
theorem B1036121 : Blo 690315 1036121 := bstep (se 2 (by rfl) ⟨388545, by rfl⟩ : syracuseStep 1036121 = 777091) B777091
theorem B6311773 : Blo 690315 6311773 := bstep (se 3 (by rfl) ⟨1183457, by rfl⟩ : syracuseStep 6311773 = 2366915) B2366915
theorem B8408933 : Blo 690315 8408933 := bstep (se 4 (by rfl) ⟨788337, by rfl⟩ : syracuseStep 8408933 = 1576675) B1576675
theorem B5001061 : Blo 690315 5001061 := bstep (se 4 (by rfl) ⟨468849, by rfl⟩ : syracuseStep 5001061 = 937699) B937699
theorem B2805635 : Blo 690315 2805635 := bstep (se 1 (by rfl) ⟨2104226, by rfl⟩ : syracuseStep 2805635 = 4208453) B4208453
theorem B1560473 : Blo 690315 1560473 := bstep (se 2 (by rfl) ⟨585177, by rfl⟩ : syracuseStep 1560473 = 1170355) B1170355
theorem B1167257 : Blo 690315 1167257 := bstep (se 2 (by rfl) ⟨437721, by rfl⟩ : syracuseStep 1167257 = 875443) B875443
theorem B1036235 : Blo 690315 1036235 := bstep (se 1 (by rfl) ⟨777176, by rfl⟩ : syracuseStep 1036235 = 1554353) B1554353
theorem B1036247 : Blo 690315 1036247 := bstep (se 1 (by rfl) ⟨777185, by rfl⟩ : syracuseStep 1036247 = 1554371) B1554371
theorem B1560563 : Blo 690315 1560563 := bstep (se 1 (by rfl) ⟨1170422, by rfl⟩ : syracuseStep 1560563 = 2340845) B2340845
theorem B1560599 : Blo 690315 1560599 := bstep (se 1 (by rfl) ⟨1170449, by rfl⟩ : syracuseStep 1560599 = 2340899) B2340899
theorem B1036313 : Blo 690315 1036313 := bstep (se 2 (by rfl) ⟨388617, by rfl⟩ : syracuseStep 1036313 = 777235) B777235
theorem B1167385 : Blo 690315 1167385 := bstep (se 2 (by rfl) ⟨437769, by rfl⟩ : syracuseStep 1167385 = 875539) B875539
theorem B13455395 : Blo 690315 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B1036427 : Blo 690315 1036427 := bstep (se 1 (by rfl) ⟨777320, by rfl⟩ : syracuseStep 1036427 = 1554641) B1554641
theorem B1036439 : Blo 690315 1036439 := bstep (se 1 (by rfl) ⟨777329, by rfl⟩ : syracuseStep 1036439 = 1554659) B1554659
theorem B1757335 : Blo 690315 1757335 := bstep (se 1 (by rfl) ⟨1318001, by rfl⟩ : syracuseStep 1757335 = 2636003) B2636003
theorem B1560779 : Blo 690315 1560779 := bstep (se 1 (by rfl) ⟨1170584, by rfl⟩ : syracuseStep 1560779 = 2341169) B2341169
theorem B1036505 : Blo 690315 1036505 := bstep (se 2 (by rfl) ⟨388689, by rfl⟩ : syracuseStep 1036505 = 777379) B777379
theorem B1560833 : Blo 690315 1560833 := bstep (se 2 (by rfl) ⟨585312, by rfl⟩ : syracuseStep 1560833 = 1170625) B1170625
theorem B1036619 : Blo 690315 1036619 := bstep (se 1 (by rfl) ⟨777464, by rfl⟩ : syracuseStep 1036619 = 1554929) B1554929
theorem B1036631 : Blo 690315 1036631 := bstep (se 1 (by rfl) ⟨777473, by rfl⟩ : syracuseStep 1036631 = 1554947) B1554947
theorem B1036697 : Blo 690315 1036697 := bstep (se 2 (by rfl) ⟨388761, by rfl⟩ : syracuseStep 1036697 = 777523) B777523
theorem B1561049 : Blo 690315 1561049 := bstep (se 2 (by rfl) ⟨585393, by rfl⟩ : syracuseStep 1561049 = 1170787) B1170787
theorem B1036811 : Blo 690315 1036811 := bstep (se 1 (by rfl) ⟨777608, by rfl⟩ : syracuseStep 1036811 = 1555217) B1555217
theorem B1036823 : Blo 690315 1036823 := bstep (se 1 (by rfl) ⟨777617, by rfl⟩ : syracuseStep 1036823 = 1555235) B1555235
theorem B1561139 : Blo 690315 1561139 := bstep (se 1 (by rfl) ⟨1170854, by rfl⟩ : syracuseStep 1561139 = 2341709) B2341709
theorem B1659467 : Blo 690315 1659467 := bstep (se 1 (by rfl) ⟨1244600, by rfl⟩ : syracuseStep 1659467 = 2489201) B2489201
theorem B1167959 : Blo 690315 1167959 := bstep (se 1 (by rfl) ⟨875969, by rfl⟩ : syracuseStep 1167959 = 1751939) B1751939
theorem B1561175 : Blo 690315 1561175 := bstep (se 1 (by rfl) ⟨1170881, by rfl⟩ : syracuseStep 1561175 = 2341763) B2341763
theorem B1036889 : Blo 690315 1036889 := bstep (se 2 (by rfl) ⟨388833, by rfl⟩ : syracuseStep 1036889 = 777667) B777667
theorem B2708147 : Blo 690315 2708147 := bstep (se 1 (by rfl) ⟨2031110, by rfl⟩ : syracuseStep 2708147 = 4062221) B4062221
theorem B1037003 : Blo 690315 1037003 := bstep (se 1 (by rfl) ⟨777752, by rfl⟩ : syracuseStep 1037003 = 1555505) B1555505
theorem B1037015 : Blo 690315 1037015 := bstep (se 1 (by rfl) ⟨777761, by rfl⟩ : syracuseStep 1037015 = 1555523) B1555523
theorem B1168087 : Blo 690315 1168087 := bstep (se 1 (by rfl) ⟨876065, by rfl⟩ : syracuseStep 1168087 = 1752131) B1752131
theorem B1561355 : Blo 690315 1561355 := bstep (se 1 (by rfl) ⟨1171016, by rfl⟩ : syracuseStep 1561355 = 2342033) B2342033
theorem B1037081 : Blo 690315 1037081 := bstep (se 2 (by rfl) ⟨388905, by rfl⟩ : syracuseStep 1037081 = 777811) B777811
theorem B1561409 : Blo 690315 1561409 := bstep (se 2 (by rfl) ⟨585528, by rfl⟩ : syracuseStep 1561409 = 1171057) B1171057
theorem B1037195 : Blo 690315 1037195 := bstep (se 1 (by rfl) ⟨777896, by rfl⟩ : syracuseStep 1037195 = 1555793) B1555793
theorem B1037207 : Blo 690315 1037207 := bstep (se 1 (by rfl) ⟨777905, by rfl⟩ : syracuseStep 1037207 = 1555811) B1555811
theorem B1037273 : Blo 690315 1037273 := bstep (se 2 (by rfl) ⟨388977, by rfl⟩ : syracuseStep 1037273 = 777955) B777955
theorem B1561625 : Blo 690315 1561625 := bstep (se 2 (by rfl) ⟨585609, by rfl⟩ : syracuseStep 1561625 = 1171219) B1171219
theorem B3494987 : Blo 690315 3494987 := bstep (se 1 (by rfl) ⟨2621240, by rfl⟩ : syracuseStep 3494987 = 5242481) B5242481
theorem B1037387 : Blo 690315 1037387 := bstep (se 1 (by rfl) ⟨778040, by rfl⟩ : syracuseStep 1037387 = 1556081) B1556081
theorem B1037399 : Blo 690315 1037399 := bstep (se 1 (by rfl) ⟨778049, by rfl⟩ : syracuseStep 1037399 = 1556099) B1556099
theorem B1561715 : Blo 690315 1561715 := bstep (se 1 (by rfl) ⟨1171286, by rfl⟩ : syracuseStep 1561715 = 2342573) B2342573
theorem B1561751 : Blo 690315 1561751 := bstep (se 1 (by rfl) ⟨1171313, by rfl⟩ : syracuseStep 1561751 = 2342627) B2342627
theorem B1037465 : Blo 690315 1037465 := bstep (se 2 (by rfl) ⟨389049, by rfl⟩ : syracuseStep 1037465 = 778099) B778099
theorem B1037579 : Blo 690315 1037579 := bstep (se 1 (by rfl) ⟨778184, by rfl⟩ : syracuseStep 1037579 = 1556369) B1556369
theorem B1037591 : Blo 690315 1037591 := bstep (se 1 (by rfl) ⟨778193, by rfl⟩ : syracuseStep 1037591 = 1556387) B1556387
theorem B1168715 : Blo 690315 1168715 := bstep (se 1 (by rfl) ⟨876536, by rfl⟩ : syracuseStep 1168715 = 1753073) B1753073
theorem B1561931 : Blo 690315 1561931 := bstep (se 1 (by rfl) ⟨1171448, by rfl⟩ : syracuseStep 1561931 = 2342897) B2342897
theorem B1037657 : Blo 690315 1037657 := bstep (se 2 (by rfl) ⟨389121, by rfl⟩ : syracuseStep 1037657 = 778243) B778243
theorem B2807129 : Blo 690315 2807129 := bstep (se 2 (by rfl) ⟨1052673, by rfl⟩ : syracuseStep 2807129 = 2105347) B2105347
theorem B1561985 : Blo 690315 1561985 := bstep (se 2 (by rfl) ⟨585744, by rfl⟩ : syracuseStep 1561985 = 1171489) B1171489
theorem B1037771 : Blo 690315 1037771 := bstep (se 1 (by rfl) ⟨778328, by rfl⟩ : syracuseStep 1037771 = 1556657) B1556657
theorem B1168843 : Blo 690315 1168843 := bstep (se 1 (by rfl) ⟨876632, by rfl⟩ : syracuseStep 1168843 = 1753265) B1753265
theorem B1037783 : Blo 690315 1037783 := bstep (se 1 (by rfl) ⟨778337, by rfl⟩ : syracuseStep 1037783 = 1556675) B1556675
theorem B1037849 : Blo 690315 1037849 := bstep (se 2 (by rfl) ⟨389193, by rfl⟩ : syracuseStep 1037849 = 778387) B778387
theorem B1168985 : Blo 690315 1168985 := bstep (se 2 (by rfl) ⟨438369, by rfl⟩ : syracuseStep 1168985 = 876739) B876739
theorem B1562201 : Blo 690315 1562201 := bstep (se 2 (by rfl) ⟨585825, by rfl⟩ : syracuseStep 1562201 = 1171651) B1171651
theorem B1037963 : Blo 690315 1037963 := bstep (se 1 (by rfl) ⟨778472, by rfl⟩ : syracuseStep 1037963 = 1556945) B1556945
theorem B1037975 : Blo 690315 1037975 := bstep (se 1 (by rfl) ⟨778481, by rfl⟩ : syracuseStep 1037975 = 1556963) B1556963
theorem B1038041 : Blo 690315 1038041 := bstep (se 2 (by rfl) ⟨389265, by rfl⟩ : syracuseStep 1038041 = 778531) B778531
theorem B1169113 : Blo 690315 1169113 := bstep (se 2 (by rfl) ⟨438417, by rfl⟩ : syracuseStep 1169113 = 876835) B876835
theorem B1038155 : Blo 690315 1038155 := bstep (se 1 (by rfl) ⟨778616, by rfl⟩ : syracuseStep 1038155 = 1557233) B1557233
theorem B1038167 : Blo 690315 1038167 := bstep (se 1 (by rfl) ⟨778625, by rfl⟩ : syracuseStep 1038167 = 1557251) B1557251
theorem B1496983 : Blo 690315 1496983 := bstep (se 1 (by rfl) ⟨1122737, by rfl⟩ : syracuseStep 1496983 = 2245475) B2245475
theorem B4446103 : Blo 690315 4446103 := bstep (se 1 (by rfl) ⟨3334577, by rfl⟩ : syracuseStep 4446103 = 6669155) B6669155
theorem B1038233 : Blo 690315 1038233 := bstep (se 2 (by rfl) ⟨389337, by rfl⟩ : syracuseStep 1038233 = 778675) B778675
theorem B1038347 : Blo 690315 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B1038359 : Blo 690315 1038359 := bstep (se 1 (by rfl) ⟨778769, by rfl⟩ : syracuseStep 1038359 = 1557539) B1557539
theorem B5003309 : Blo 690315 5003309 := bstep (se 3 (by rfl) ⟨938120, by rfl⟩ : syracuseStep 5003309 = 1876241) B1876241
theorem B1038425 : Blo 690315 1038425 := bstep (se 2 (by rfl) ⟨389409, by rfl⟩ : syracuseStep 1038425 = 778819) B778819
theorem B1038539 : Blo 690315 1038539 := bstep (se 1 (by rfl) ⟨778904, by rfl⟩ : syracuseStep 1038539 = 1557809) B1557809
theorem B1038551 : Blo 690315 1038551 := bstep (se 1 (by rfl) ⟨778913, by rfl⟩ : syracuseStep 1038551 = 1557827) B1557827
theorem B11229425 : Blo 690315 11229425 := bstep (se 2 (by rfl) ⟨4211034, by rfl⟩ : syracuseStep 11229425 = 8422069) B8422069
theorem B1169687 : Blo 690315 1169687 := bstep (se 1 (by rfl) ⟨877265, by rfl⟩ : syracuseStep 1169687 = 1754531) B1754531
theorem B1038617 : Blo 690315 1038617 := bstep (se 2 (by rfl) ⟨389481, by rfl⟩ : syracuseStep 1038617 = 778963) B778963
theorem B5921099 : Blo 690315 5921099 := bstep (se 1 (by rfl) ⟨4440824, by rfl⟩ : syracuseStep 5921099 = 8881649) B8881649
theorem B874891 : Blo 690315 874891 := bstep (se 1 (by rfl) ⟨656168, by rfl⟩ : syracuseStep 874891 = 1312337) B1312337
theorem B1038731 : Blo 690315 1038731 := bstep (se 1 (by rfl) ⟨779048, by rfl⟩ : syracuseStep 1038731 = 1558097) B1558097
theorem B1038743 : Blo 690315 1038743 := bstep (se 1 (by rfl) ⟨779057, by rfl⟩ : syracuseStep 1038743 = 1558115) B1558115
theorem B1169815 : Blo 690315 1169815 := bstep (se 1 (by rfl) ⟨877361, by rfl⟩ : syracuseStep 1169815 = 1754723) B1754723
theorem B1038809 : Blo 690315 1038809 := bstep (se 2 (by rfl) ⟨389553, by rfl⟩ : syracuseStep 1038809 = 779107) B779107
theorem B776695 : Blo 690315 776695 := bstep (se 1 (by rfl) ⟨582521, by rfl⟩ : syracuseStep 776695 = 1165043) B1165043
theorem B1038923 : Blo 690315 1038923 := bstep (se 1 (by rfl) ⟨779192, by rfl⟩ : syracuseStep 1038923 = 1558385) B1558385
theorem B1038935 : Blo 690315 1038935 := bstep (se 1 (by rfl) ⟨779201, by rfl⟩ : syracuseStep 1038935 = 1558403) B1558403
theorem B1039001 : Blo 690315 1039001 := bstep (se 2 (by rfl) ⟨389625, by rfl⟩ : syracuseStep 1039001 = 779251) B779251
theorem B776875 : Blo 690315 776875 := bstep (se 1 (by rfl) ⟨582656, by rfl⟩ : syracuseStep 776875 = 1165313) B1165313
theorem B1039115 : Blo 690315 1039115 := bstep (se 1 (by rfl) ⟨779336, by rfl⟩ : syracuseStep 1039115 = 1558673) B1558673
theorem B776983 : Blo 690315 776983 := bstep (se 1 (by rfl) ⟨582737, by rfl⟩ : syracuseStep 776983 = 1165475) B1165475
theorem B1039127 : Blo 690315 1039127 := bstep (se 1 (by rfl) ⟨779345, by rfl⟩ : syracuseStep 1039127 = 1558691) B1558691
theorem B3496769 : Blo 690315 3496769 := bstep (se 2 (by rfl) ⟨1311288, by rfl⟩ : syracuseStep 3496769 = 2622577) B2622577
theorem B1039193 : Blo 690315 1039193 := bstep (se 2 (by rfl) ⟨389697, by rfl⟩ : syracuseStep 1039193 = 779395) B779395
theorem B2808749 : Blo 690315 2808749 := bstep (se 3 (by rfl) ⟨526640, by rfl⟩ : syracuseStep 2808749 = 1053281) B1053281
theorem B777163 : Blo 690315 777163 := bstep (se 1 (by rfl) ⟨582872, by rfl⟩ : syracuseStep 777163 = 1165745) B1165745
theorem B1039307 : Blo 690315 1039307 := bstep (se 1 (by rfl) ⟨779480, by rfl⟩ : syracuseStep 1039307 = 1558961) B1558961
theorem B1039319 : Blo 690315 1039319 := bstep (se 1 (by rfl) ⟨779489, by rfl⟩ : syracuseStep 1039319 = 1558979) B1558979
theorem B1170443 : Blo 690315 1170443 := bstep (se 1 (by rfl) ⟨877832, by rfl⟩ : syracuseStep 1170443 = 1755665) B1755665
theorem B1039385 : Blo 690315 1039385 := bstep (se 2 (by rfl) ⟨389769, by rfl⟩ : syracuseStep 1039385 = 779539) B779539
theorem B777271 : Blo 690315 777271 := bstep (se 1 (by rfl) ⟨582953, by rfl⟩ : syracuseStep 777271 = 1165907) B1165907
theorem B1039499 : Blo 690315 1039499 := bstep (se 1 (by rfl) ⟨779624, by rfl⟩ : syracuseStep 1039499 = 1559249) B1559249
theorem B1170571 : Blo 690315 1170571 := bstep (se 1 (by rfl) ⟨877928, by rfl⟩ : syracuseStep 1170571 = 1755857) B1755857
theorem B1039511 : Blo 690315 1039511 := bstep (se 1 (by rfl) ⟨779633, by rfl⟩ : syracuseStep 1039511 = 1559267) B1559267
theorem B1039577 : Blo 690315 1039577 := bstep (se 2 (by rfl) ⟨389841, by rfl⟩ : syracuseStep 1039577 = 779683) B779683
theorem B777451 : Blo 690315 777451 := bstep (se 1 (by rfl) ⟨583088, by rfl⟩ : syracuseStep 777451 = 1166177) B1166177
theorem B1170713 : Blo 690315 1170713 := bstep (se 2 (by rfl) ⟨439017, by rfl⟩ : syracuseStep 1170713 = 878035) B878035
theorem B1039691 : Blo 690315 1039691 := bstep (se 1 (by rfl) ⟨779768, by rfl⟩ : syracuseStep 1039691 = 1559537) B1559537
theorem B777559 : Blo 690315 777559 := bstep (se 1 (by rfl) ⟨583169, by rfl⟩ : syracuseStep 777559 = 1166339) B1166339
theorem B875863 : Blo 690315 875863 := bstep (se 1 (by rfl) ⟨656897, by rfl⟩ : syracuseStep 875863 = 1313795) B1313795
theorem B1039703 : Blo 690315 1039703 := bstep (se 1 (by rfl) ⟨779777, by rfl⟩ : syracuseStep 1039703 = 1559555) B1559555
theorem B5266781 : Blo 690315 5266781 := bstep (se 3 (by rfl) ⟨987521, by rfl⟩ : syracuseStep 5266781 = 1975043) B1975043
theorem B1039769 : Blo 690315 1039769 := bstep (se 2 (by rfl) ⟨389913, by rfl⟩ : syracuseStep 1039769 = 779827) B779827
theorem B1170841 : Blo 690315 1170841 := bstep (se 2 (by rfl) ⟨439065, by rfl⟩ : syracuseStep 1170841 = 878131) B878131
theorem B777739 : Blo 690315 777739 := bstep (se 1 (by rfl) ⟨583304, by rfl⟩ : syracuseStep 777739 = 1166609) B1166609
theorem B1039883 : Blo 690315 1039883 := bstep (se 1 (by rfl) ⟨779912, by rfl⟩ : syracuseStep 1039883 = 1559825) B1559825
theorem B1039895 : Blo 690315 1039895 := bstep (se 1 (by rfl) ⟨779921, by rfl⟩ : syracuseStep 1039895 = 1559843) B1559843
theorem B1039961 : Blo 690315 1039961 := bstep (se 2 (by rfl) ⟨389985, by rfl⟩ : syracuseStep 1039961 = 779971) B779971
theorem B777847 : Blo 690315 777847 := bstep (se 1 (by rfl) ⟨583385, by rfl⟩ : syracuseStep 777847 = 1166771) B1166771
theorem B4808323 : Blo 690315 4808323 := bstep (se 1 (by rfl) ⟨3606242, by rfl⟩ : syracuseStep 4808323 = 7212485) B7212485
theorem B1040075 : Blo 690315 1040075 := bstep (se 1 (by rfl) ⟨780056, by rfl⟩ : syracuseStep 1040075 = 1560113) B1560113
theorem B1040087 : Blo 690315 1040087 := bstep (se 1 (by rfl) ⟨780065, by rfl⟩ : syracuseStep 1040087 = 1560131) B1560131
theorem B1040153 : Blo 690315 1040153 := bstep (se 2 (by rfl) ⟨390057, by rfl⟩ : syracuseStep 1040153 = 780115) B780115
theorem B778027 : Blo 690315 778027 := bstep (se 1 (by rfl) ⟨583520, by rfl⟩ : syracuseStep 778027 = 1167041) B1167041
theorem B1040267 : Blo 690315 1040267 := bstep (se 1 (by rfl) ⟨780200, by rfl⟩ : syracuseStep 1040267 = 1560401) B1560401
theorem B778135 : Blo 690315 778135 := bstep (se 1 (by rfl) ⟨583601, by rfl⟩ : syracuseStep 778135 = 1167203) B1167203
theorem B1040279 : Blo 690315 1040279 := bstep (se 1 (by rfl) ⟨780209, by rfl⟩ : syracuseStep 1040279 = 1560419) B1560419
theorem B1171415 : Blo 690315 1171415 := bstep (se 1 (by rfl) ⟨878561, by rfl⟩ : syracuseStep 1171415 = 1757123) B1757123
theorem B1040345 : Blo 690315 1040345 := bstep (se 2 (by rfl) ⟨390129, by rfl⟩ : syracuseStep 1040345 = 780259) B780259
theorem B778315 : Blo 690315 778315 := bstep (se 1 (by rfl) ⟨583736, by rfl⟩ : syracuseStep 778315 = 1167473) B1167473
theorem B1040459 : Blo 690315 1040459 := bstep (se 1 (by rfl) ⟨780344, by rfl⟩ : syracuseStep 1040459 = 1560689) B1560689
theorem B1040471 : Blo 690315 1040471 := bstep (se 1 (by rfl) ⟨780353, by rfl⟩ : syracuseStep 1040471 = 1560707) B1560707
theorem B1171543 : Blo 690315 1171543 := bstep (se 1 (by rfl) ⟨878657, by rfl⟩ : syracuseStep 1171543 = 1757315) B1757315
theorem B1400971 : Blo 690315 1400971 := bstep (se 1 (by rfl) ⟨1050728, by rfl⟩ : syracuseStep 1400971 = 2101457) B2101457
theorem B876683 : Blo 690315 876683 := bstep (se 1 (by rfl) ⟨657512, by rfl⟩ : syracuseStep 876683 = 1315025) B1315025
theorem B1040537 : Blo 690315 1040537 := bstep (se 2 (by rfl) ⟨390201, by rfl⟩ : syracuseStep 1040537 = 780403) B780403
theorem B778423 : Blo 690315 778423 := bstep (se 1 (by rfl) ⟨583817, by rfl⟩ : syracuseStep 778423 = 1167635) B1167635
theorem B1040651 : Blo 690315 1040651 := bstep (se 1 (by rfl) ⟨780488, by rfl⟩ : syracuseStep 1040651 = 1560977) B1560977
theorem B2220311 : Blo 690315 2220311 := bstep (se 1 (by rfl) ⟨1665233, by rfl⟩ : syracuseStep 2220311 = 3330467) B3330467
theorem B1040663 : Blo 690315 1040663 := bstep (se 1 (by rfl) ⟨780497, by rfl⟩ : syracuseStep 1040663 = 1560995) B1560995
theorem B1040729 : Blo 690315 1040729 := bstep (se 2 (by rfl) ⟨390273, by rfl⟩ : syracuseStep 1040729 = 780547) B780547
theorem B778603 : Blo 690315 778603 := bstep (se 1 (by rfl) ⟨583952, by rfl⟩ : syracuseStep 778603 = 1167905) B1167905
theorem B1040843 : Blo 690315 1040843 := bstep (se 1 (by rfl) ⟨780632, by rfl⟩ : syracuseStep 1040843 = 1561265) B1561265
theorem B778711 : Blo 690315 778711 := bstep (se 1 (by rfl) ⟨584033, by rfl⟩ : syracuseStep 778711 = 1168067) B1168067
theorem B1040855 : Blo 690315 1040855 := bstep (se 1 (by rfl) ⟨780641, by rfl⟩ : syracuseStep 1040855 = 1561283) B1561283
theorem B1040921 : Blo 690315 1040921 := bstep (se 2 (by rfl) ⟨390345, by rfl⟩ : syracuseStep 1040921 = 780691) B780691
theorem B8872523 : Blo 690315 8872523 := bstep (se 1 (by rfl) ⟨6654392, by rfl⟩ : syracuseStep 8872523 = 13308785) B13308785
theorem B778891 : Blo 690315 778891 := bstep (se 1 (by rfl) ⟨584168, by rfl⟩ : syracuseStep 778891 = 1168337) B1168337
theorem B1041035 : Blo 690315 1041035 := bstep (se 1 (by rfl) ⟨780776, by rfl⟩ : syracuseStep 1041035 = 1561553) B1561553
theorem B1041047 : Blo 690315 1041047 := bstep (se 1 (by rfl) ⟨780785, by rfl⟩ : syracuseStep 1041047 = 1561571) B1561571
theorem B3498713 : Blo 690315 3498713 := bstep (se 2 (by rfl) ⟨1312017, by rfl⟩ : syracuseStep 3498713 = 2624035) B2624035
theorem B1041113 : Blo 690315 1041113 := bstep (se 2 (by rfl) ⟨390417, by rfl⟩ : syracuseStep 1041113 = 780835) B780835
theorem B778999 : Blo 690315 778999 := bstep (se 1 (by rfl) ⟨584249, by rfl⟩ : syracuseStep 778999 = 1168499) B1168499
theorem B1499969 : Blo 690315 1499969 := bstep (se 2 (by rfl) ⟨562488, by rfl⟩ : syracuseStep 1499969 = 1124977) B1124977
theorem B2810699 : Blo 690315 2810699 := bstep (se 1 (by rfl) ⟨2108024, by rfl⟩ : syracuseStep 2810699 = 4216049) B4216049
theorem B877387 : Blo 690315 877387 := bstep (se 1 (by rfl) ⟨658040, by rfl⟩ : syracuseStep 877387 = 1316081) B1316081
theorem B1041227 : Blo 690315 1041227 := bstep (se 1 (by rfl) ⟨780920, by rfl⟩ : syracuseStep 1041227 = 1561841) B1561841
theorem B1041239 : Blo 690315 1041239 := bstep (se 1 (by rfl) ⟨780929, by rfl⟩ : syracuseStep 1041239 = 1561859) B1561859
theorem B1041305 : Blo 690315 1041305 := bstep (se 2 (by rfl) ⟨390489, by rfl⟩ : syracuseStep 1041305 = 780979) B780979
theorem B779179 : Blo 690315 779179 := bstep (se 1 (by rfl) ⟨584384, by rfl⟩ : syracuseStep 779179 = 1168769) B1168769
theorem B5923763 : Blo 690315 5923763 := bstep (se 1 (by rfl) ⟨4442822, by rfl⟩ : syracuseStep 5923763 = 8885645) B8885645
theorem B1041419 : Blo 690315 1041419 := bstep (se 1 (by rfl) ⟨781064, by rfl⟩ : syracuseStep 1041419 = 1562129) B1562129
theorem B779287 : Blo 690315 779287 := bstep (se 1 (by rfl) ⟨584465, by rfl⟩ : syracuseStep 779287 = 1168931) B1168931
theorem B1041431 : Blo 690315 1041431 := bstep (se 1 (by rfl) ⟨781073, by rfl⟩ : syracuseStep 1041431 = 1562147) B1562147
theorem B877655 : Blo 690315 877655 := bstep (se 1 (by rfl) ⟨658241, by rfl⟩ : syracuseStep 877655 = 1316483) B1316483
theorem B779467 : Blo 690315 779467 := bstep (se 1 (by rfl) ⟨584600, by rfl⟩ : syracuseStep 779467 = 1169201) B1169201
theorem B7595309 : Blo 690315 7595309 := bstep (se 3 (by rfl) ⟨1424120, by rfl⟩ : syracuseStep 7595309 = 2848241) B2848241
theorem B779575 : Blo 690315 779575 := bstep (se 1 (by rfl) ⟨584681, by rfl⟩ : syracuseStep 779575 = 1169363) B1169363
theorem B779755 : Blo 690315 779755 := bstep (se 1 (by rfl) ⟨584816, by rfl⟩ : syracuseStep 779755 = 1169633) B1169633
theorem B2221643 : Blo 690315 2221643 := bstep (se 1 (by rfl) ⟨1666232, by rfl⟩ : syracuseStep 2221643 = 3332465) B3332465
theorem B779863 : Blo 690315 779863 := bstep (se 1 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 779863 = 1169795) B1169795
theorem B780043 : Blo 690315 780043 := bstep (se 1 (by rfl) ⟨585032, by rfl⟩ : syracuseStep 780043 = 1170065) B1170065
theorem B878359 : Blo 690315 878359 := bstep (se 1 (by rfl) ⟨658769, by rfl⟩ : syracuseStep 878359 = 1317539) B1317539
theorem B780151 : Blo 690315 780151 := bstep (se 1 (by rfl) ⟨585113, by rfl⟩ : syracuseStep 780151 = 1170227) B1170227
theorem B12642227 : Blo 690315 12642227 := bstep (se 1 (by rfl) ⟨9481670, by rfl⟩ : syracuseStep 12642227 = 18963341) B18963341
theorem B5924825 : Blo 690315 5924825 := bstep (se 2 (by rfl) ⟨2221809, by rfl⟩ : syracuseStep 5924825 = 4443619) B4443619
theorem B780331 : Blo 690315 780331 := bstep (se 1 (by rfl) ⟨585248, by rfl⟩ : syracuseStep 780331 = 1170497) B1170497
theorem B6383717 : Blo 690315 6383717 := bstep (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) B1196947
theorem B780439 : Blo 690315 780439 := bstep (se 1 (by rfl) ⟨585329, by rfl⟩ : syracuseStep 780439 = 1170659) B1170659
theorem B3500333 : Blo 690315 3500333 := bstep (se 3 (by rfl) ⟨656312, by rfl⟩ : syracuseStep 3500333 = 1312625) B1312625
theorem B2222387 : Blo 690315 2222387 := bstep (se 1 (by rfl) ⟨1666790, by rfl⟩ : syracuseStep 2222387 = 3333581) B3333581
theorem B780619 : Blo 690315 780619 := bstep (se 1 (by rfl) ⟨585464, by rfl⟩ : syracuseStep 780619 = 1170929) B1170929
theorem B780727 : Blo 690315 780727 := bstep (se 1 (by rfl) ⟨585545, by rfl⟩ : syracuseStep 780727 = 1171091) B1171091
theorem B780907 : Blo 690315 780907 := bstep (se 1 (by rfl) ⟨585680, by rfl⟩ : syracuseStep 780907 = 1171361) B1171361
theorem B781015 : Blo 690315 781015 := bstep (se 1 (by rfl) ⟨585761, by rfl⟩ : syracuseStep 781015 = 1171523) B1171523
theorem B4746115 : Blo 690315 4746115 := bstep (se 1 (by rfl) ⟨3559586, by rfl⟩ : syracuseStep 4746115 = 7119173) B7119173
theorem B15199301 : Blo 690315 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B1109143 : Blo 690315 1109143 := bstep (se 1 (by rfl) ⟨831857, by rfl⟩ : syracuseStep 1109143 = 1663715) B1663715
theorem B2223283 : Blo 690315 2223283 := bstep (se 1 (by rfl) ⟨1667462, by rfl⟩ : syracuseStep 2223283 = 3334925) B3334925
theorem B1502707 : Blo 690315 1502707 := bstep (se 1 (by rfl) ⟨1127030, by rfl⟩ : syracuseStep 1502707 = 2254061) B2254061
theorem B1109899 : Blo 690315 1109899 := bstep (se 1 (by rfl) ⟨832424, by rfl⟩ : syracuseStep 1109899 = 1664849) B1664849
theorem B1109963 : Blo 690315 1109963 := bstep (se 1 (by rfl) ⟨832472, by rfl⟩ : syracuseStep 1109963 = 1664945) B1664945
theorem B1110091 : Blo 690315 1110091 := bstep (se 1 (by rfl) ⟨832568, by rfl⟩ : syracuseStep 1110091 = 1665137) B1665137
theorem B1110809 : Blo 690315 1110809 := bstep (se 2 (by rfl) ⟨416553, by rfl⟩ : syracuseStep 1110809 = 833107) B833107
theorem B2814851 : Blo 690315 2814851 := bstep (se 1 (by rfl) ⟨2111138, by rfl⟩ : syracuseStep 2814851 = 4222277) B4222277
theorem B1110937 : Blo 690315 1110937 := bstep (se 2 (by rfl) ⟨416601, by rfl⟩ : syracuseStep 1110937 = 833203) B833203
theorem B750539 : Blo 690315 750539 := bstep (se 1 (by rfl) ⟨562904, by rfl⟩ : syracuseStep 750539 = 1125809) B1125809
theorem B6583427 : Blo 690315 6583427 := bstep (se 1 (by rfl) ⟨4937570, by rfl⟩ : syracuseStep 6583427 = 9875141) B9875141
theorem B1111321 : Blo 690315 1111321 := bstep (se 2 (by rfl) ⟨416745, by rfl⟩ : syracuseStep 1111321 = 833491) B833491
theorem B1111577 : Blo 690315 1111577 := bstep (se 2 (by rfl) ⟨416841, by rfl⟩ : syracuseStep 1111577 = 833683) B833683
theorem B1996633 : Blo 690315 1996633 := bstep (se 2 (by rfl) ⟨748737, by rfl⟩ : syracuseStep 1996633 = 1497475) B1497475
theorem B3799057 : Blo 690315 3799057 := bstep (se 2 (by rfl) ⟨1424646, by rfl⟩ : syracuseStep 3799057 = 2849293) B2849293
theorem B3504221 : Blo 690315 3504221 := bstep (se 3 (by rfl) ⟨657041, by rfl⟩ : syracuseStep 3504221 = 1314083) B1314083
theorem B1866035 : Blo 690315 1866035 := bstep (se 1 (by rfl) ⟨1399526, by rfl⟩ : syracuseStep 1866035 = 2799053) B2799053
theorem B3373841 : Blo 690315 3373841 := bstep (se 2 (by rfl) ⟨1265190, by rfl⟩ : syracuseStep 3373841 = 2530381) B2530381
theorem B1899737 : Blo 690315 1899737 := bstep (se 2 (by rfl) ⟨712401, by rfl⟩ : syracuseStep 1899737 = 1424803) B1424803
theorem B18513197 : Blo 690315 18513197 := bstep (se 3 (by rfl) ⟨3471224, by rfl⟩ : syracuseStep 18513197 = 6942449) B6942449
theorem B5930597 : Blo 690315 5930597 := bstep (se 4 (by rfl) ⟨555993, by rfl⟩ : syracuseStep 5930597 = 1111987) B1111987
theorem B1900439 : Blo 690315 1900439 := bstep (se 1 (by rfl) ⟨1425329, by rfl⟩ : syracuseStep 1900439 = 2850659) B2850659
theorem B1474483 : Blo 690315 1474483 := bstep (se 1 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 1474483 = 2211725) B2211725
theorem B1310681 : Blo 690315 1310681 := bstep (se 2 (by rfl) ⟨491505, by rfl⟩ : syracuseStep 1310681 = 983011) B983011
theorem B1966045 : Blo 690315 1966045 := bstep (se 3 (by rfl) ⟨368633, by rfl⟩ : syracuseStep 1966045 = 737267) B737267
theorem B1310735 : Blo 690315 1310735 := bstep (se 1 (by rfl) ⟨983051, by rfl⟩ : syracuseStep 1310735 = 1966103) B1966103
theorem B5242967 : Blo 690315 5242967 := bstep (se 1 (by rfl) ⟨3932225, by rfl⟩ : syracuseStep 5242967 = 7864451) B7864451
theorem B1867961 : Blo 690315 1867961 := bstep (se 2 (by rfl) ⟨700485, by rfl⟩ : syracuseStep 1867961 = 1400971) B1400971
theorem B983353 : Blo 690315 983353 := bstep (se 2 (by rfl) ⟨368757, by rfl⟩ : syracuseStep 983353 = 737515) B737515
theorem B1868435 : Blo 690315 1868435 := bstep (se 1 (by rfl) ⟨1401326, by rfl⟩ : syracuseStep 1868435 = 2802653) B2802653
theorem B1475371 : Blo 690315 1475371 := bstep (se 1 (by rfl) ⟨1106528, by rfl⟩ : syracuseStep 1475371 = 2213057) B2213057
theorem B1311547 : Blo 690315 1311547 := bstep (se 1 (by rfl) ⟨983660, by rfl⟩ : syracuseStep 1311547 = 1967321) B1967321
theorem B1311623 : Blo 690315 1311623 := bstep (se 1 (by rfl) ⟨983717, by rfl⟩ : syracuseStep 1311623 = 1967435) B1967435
theorem B3933137 : Blo 690315 3933137 := bstep (se 2 (by rfl) ⟨1474926, by rfl⟩ : syracuseStep 3933137 = 2949853) B2949853
theorem B1967105 : Blo 690315 1967105 := bstep (se 2 (by rfl) ⟨737664, by rfl⟩ : syracuseStep 1967105 = 1475329) B1475329
theorem B1312033 : Blo 690315 1312033 := bstep (se 2 (by rfl) ⟨492012, by rfl⟩ : syracuseStep 1312033 = 984025) B984025
theorem B3933593 : Blo 690315 3933593 := bstep (se 2 (by rfl) ⟨1475097, by rfl⟩ : syracuseStep 3933593 = 2950195) B2950195
theorem B1967561 : Blo 690315 1967561 := bstep (se 2 (by rfl) ⟨737835, by rfl⟩ : syracuseStep 1967561 = 1475671) B1475671
theorem B984583 : Blo 690315 984583 := bstep (se 1 (by rfl) ⟨738437, by rfl⟩ : syracuseStep 984583 = 1476875) B1476875
theorem B22808141 : Blo 690315 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B2623063 : Blo 690315 2623063 := bstep (se 1 (by rfl) ⟨1967297, by rfl⟩ : syracuseStep 2623063 = 3934595) B3934595
theorem B1312375 : Blo 690315 1312375 := bstep (se 1 (by rfl) ⟨984281, by rfl⟩ : syracuseStep 1312375 = 1968563) B1968563
theorem B4982465 : Blo 690315 4982465 := bstep (se 2 (by rfl) ⟨1868424, by rfl⟩ : syracuseStep 4982465 = 3736849) B3736849
theorem B2623367 : Blo 690315 2623367 := bstep (se 1 (by rfl) ⟨1967525, by rfl⟩ : syracuseStep 2623367 = 3935051) B3935051
theorem B2623549 : Blo 690315 2623549 := bstep (se 3 (by rfl) ⟨491915, by rfl⟩ : syracuseStep 2623549 = 983831) B983831
theorem B2951255 : Blo 690315 2951255 := bstep (se 1 (by rfl) ⟨2213441, by rfl⟩ : syracuseStep 2951255 = 4426883) B4426883
theorem B690319 : Blo 690315 690319 := bstep (se 1 (by rfl) ⟨517739, by rfl⟩ : syracuseStep 690319 = 1035479) B1035479
theorem B3999917 : Blo 690315 3999917 := bstep (se 3 (by rfl) ⟨749984, by rfl⟩ : syracuseStep 3999917 = 1499969) B1499969
theorem B690363 : Blo 690315 690363 := bstep (se 1 (by rfl) ⟨517772, by rfl⟩ : syracuseStep 690363 = 1035545) B1035545
theorem B985289 : Blo 690315 985289 := bstep (se 2 (by rfl) ⟨369483, by rfl⟩ : syracuseStep 985289 = 738967) B738967
theorem B7473389 : Blo 690315 7473389 := bstep (se 3 (by rfl) ⟨1401260, by rfl⟩ : syracuseStep 7473389 = 2802521) B2802521
theorem B690439 : Blo 690315 690439 := bstep (se 1 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 690439 = 1035659) B1035659
theorem B690447 : Blo 690315 690447 := bstep (se 1 (by rfl) ⟨517835, by rfl⟩ : syracuseStep 690447 = 1035671) B1035671
theorem B690491 : Blo 690315 690491 := bstep (se 1 (by rfl) ⟨517868, by rfl⟩ : syracuseStep 690491 = 1035737) B1035737
theorem B985403 : Blo 690315 985403 := bstep (se 1 (by rfl) ⟨739052, by rfl⟩ : syracuseStep 985403 = 1478105) B1478105
theorem B3508595 : Blo 690315 3508595 := bstep (se 1 (by rfl) ⟨2631446, by rfl⟩ : syracuseStep 3508595 = 5262893) B5262893
theorem B690567 : Blo 690315 690567 := bstep (se 1 (by rfl) ⟨517925, by rfl⟩ : syracuseStep 690567 = 1035851) B1035851
theorem B690575 : Blo 690315 690575 := bstep (se 1 (by rfl) ⟨517931, by rfl⟩ : syracuseStep 690575 = 1035863) B1035863
theorem B690619 : Blo 690315 690619 := bstep (se 1 (by rfl) ⟨517964, by rfl⟩ : syracuseStep 690619 = 1035929) B1035929
theorem B690695 : Blo 690315 690695 := bstep (se 1 (by rfl) ⟨518021, by rfl⟩ : syracuseStep 690695 = 1036043) B1036043
theorem B690703 : Blo 690315 690703 := bstep (se 1 (by rfl) ⟨518027, by rfl⟩ : syracuseStep 690703 = 1036055) B1036055
theorem B887311 : Blo 690315 887311 := bstep (se 1 (by rfl) ⟨665483, by rfl⟩ : syracuseStep 887311 = 1330967) B1330967
theorem B2001437 : Blo 690315 2001437 := bstep (se 3 (by rfl) ⟨375269, by rfl⟩ : syracuseStep 2001437 = 750539) B750539
theorem B690747 : Blo 690315 690747 := bstep (se 1 (by rfl) ⟨518060, by rfl⟩ : syracuseStep 690747 = 1036121) B1036121
theorem B5605955 : Blo 690315 5605955 := bstep (se 1 (by rfl) ⟨4204466, by rfl⟩ : syracuseStep 5605955 = 8408933) B8408933
theorem B690823 : Blo 690315 690823 := bstep (se 1 (by rfl) ⟨518117, by rfl⟩ : syracuseStep 690823 = 1036235) B1036235
theorem B690831 : Blo 690315 690831 := bstep (se 1 (by rfl) ⟨518123, by rfl⟩ : syracuseStep 690831 = 1036247) B1036247
theorem B690875 : Blo 690315 690875 := bstep (se 1 (by rfl) ⟨518156, by rfl⟩ : syracuseStep 690875 = 1036313) B1036313
theorem B5606081 : Blo 690315 5606081 := bstep (se 2 (by rfl) ⟨2102280, by rfl⟩ : syracuseStep 5606081 = 4204561) B4204561
theorem B690951 : Blo 690315 690951 := bstep (se 1 (by rfl) ⟨518213, by rfl⟩ : syracuseStep 690951 = 1036427) B1036427
theorem B690959 : Blo 690315 690959 := bstep (se 1 (by rfl) ⟨518219, by rfl⟩ : syracuseStep 690959 = 1036439) B1036439
theorem B691003 : Blo 690315 691003 := bstep (se 1 (by rfl) ⟨518252, by rfl⟩ : syracuseStep 691003 = 1036505) B1036505
theorem B3509081 : Blo 690315 3509081 := bstep (se 2 (by rfl) ⟨1315905, by rfl⟩ : syracuseStep 3509081 = 2631811) B2631811
theorem B691079 : Blo 690315 691079 := bstep (se 1 (by rfl) ⟨518309, by rfl⟩ : syracuseStep 691079 = 1036619) B1036619
theorem B691087 : Blo 690315 691087 := bstep (se 1 (by rfl) ⟨518315, by rfl⟩ : syracuseStep 691087 = 1036631) B1036631
theorem B986041 : Blo 690315 986041 := bstep (se 2 (by rfl) ⟨369765, by rfl⟩ : syracuseStep 986041 = 739531) B739531
theorem B691131 : Blo 690315 691131 := bstep (se 1 (by rfl) ⟨518348, by rfl⟩ : syracuseStep 691131 = 1036697) B1036697
theorem B1051579 : Blo 690315 1051579 := bstep (se 1 (by rfl) ⟨788684, by rfl⟩ : syracuseStep 1051579 = 1577369) B1577369
theorem B691207 : Blo 690315 691207 := bstep (se 1 (by rfl) ⟨518405, by rfl⟩ : syracuseStep 691207 = 1036811) B1036811
theorem B691215 : Blo 690315 691215 := bstep (se 1 (by rfl) ⟨518411, by rfl⟩ : syracuseStep 691215 = 1036823) B1036823
theorem B691259 : Blo 690315 691259 := bstep (se 1 (by rfl) ⟨518444, by rfl⟩ : syracuseStep 691259 = 1036889) B1036889
theorem B1969211 : Blo 690315 1969211 := bstep (se 1 (by rfl) ⟨1476908, by rfl⟩ : syracuseStep 1969211 = 2953817) B2953817
theorem B1805431 : Blo 690315 1805431 := bstep (se 1 (by rfl) ⟨1354073, by rfl⟩ : syracuseStep 1805431 = 2708147) B2708147
theorem B691335 : Blo 690315 691335 := bstep (se 1 (by rfl) ⟨518501, by rfl⟩ : syracuseStep 691335 = 1037003) B1037003
theorem B691343 : Blo 690315 691343 := bstep (se 1 (by rfl) ⟨518507, by rfl⟩ : syracuseStep 691343 = 1037015) B1037015
theorem B1313977 : Blo 690315 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B691387 : Blo 690315 691387 := bstep (se 1 (by rfl) ⟨518540, by rfl⟩ : syracuseStep 691387 = 1037081) B1037081
theorem B691463 : Blo 690315 691463 := bstep (se 1 (by rfl) ⟨518597, by rfl⟩ : syracuseStep 691463 = 1037195) B1037195
theorem B691471 : Blo 690315 691471 := bstep (se 1 (by rfl) ⟨518603, by rfl⟩ : syracuseStep 691471 = 1037207) B1037207
theorem B1051919 : Blo 690315 1051919 := bstep (se 1 (by rfl) ⟨788939, by rfl⟩ : syracuseStep 1051919 = 1577879) B1577879
theorem B691515 : Blo 690315 691515 := bstep (se 1 (by rfl) ⟨518636, by rfl⟩ : syracuseStep 691515 = 1037273) B1037273
theorem B2329991 : Blo 690315 2329991 := bstep (se 1 (by rfl) ⟨1747493, by rfl⟩ : syracuseStep 2329991 = 3494987) B3494987
theorem B691591 : Blo 690315 691591 := bstep (se 1 (by rfl) ⟨518693, by rfl⟩ : syracuseStep 691591 = 1037387) B1037387
theorem B691599 : Blo 690315 691599 := bstep (se 1 (by rfl) ⟨518699, by rfl⟩ : syracuseStep 691599 = 1037399) B1037399
theorem B691643 : Blo 690315 691643 := bstep (se 1 (by rfl) ⟨518732, by rfl⟩ : syracuseStep 691643 = 1037465) B1037465
theorem B20254157 : Blo 690315 20254157 := bstep (se 3 (by rfl) ⟨3797654, by rfl⟩ : syracuseStep 20254157 = 7595309) B7595309
theorem B691719 : Blo 690315 691719 := bstep (se 1 (by rfl) ⟨518789, by rfl⟩ : syracuseStep 691719 = 1037579) B1037579
theorem B691727 : Blo 690315 691727 := bstep (se 1 (by rfl) ⟨518795, by rfl⟩ : syracuseStep 691727 = 1037591) B1037591
theorem B1314319 : Blo 690315 1314319 := bstep (se 1 (by rfl) ⟨985739, by rfl⟩ : syracuseStep 1314319 = 1971479) B1971479
theorem B691771 : Blo 690315 691771 := bstep (se 1 (by rfl) ⟨518828, by rfl⟩ : syracuseStep 691771 = 1037657) B1037657
theorem B1871419 : Blo 690315 1871419 := bstep (se 1 (by rfl) ⟨1403564, by rfl⟩ : syracuseStep 1871419 = 2807129) B2807129
theorem B691847 : Blo 690315 691847 := bstep (se 1 (by rfl) ⟨518885, by rfl⟩ : syracuseStep 691847 = 1037771) B1037771
theorem B691855 : Blo 690315 691855 := bstep (se 1 (by rfl) ⟨518891, by rfl⟩ : syracuseStep 691855 = 1037783) B1037783
theorem B1969849 : Blo 690315 1969849 := bstep (se 2 (by rfl) ⟨738693, by rfl⟩ : syracuseStep 1969849 = 1477387) B1477387
theorem B691899 : Blo 690315 691899 := bstep (se 1 (by rfl) ⟨518924, by rfl⟩ : syracuseStep 691899 = 1037849) B1037849
theorem B7900901 : Blo 690315 7900901 := bstep (se 4 (by rfl) ⟨740709, by rfl⟩ : syracuseStep 7900901 = 1481419) B1481419
theorem B2330369 : Blo 690315 2330369 := bstep (se 2 (by rfl) ⟨873888, by rfl⟩ : syracuseStep 2330369 = 1747777) B1747777
theorem B2625281 : Blo 690315 2625281 := bstep (se 2 (by rfl) ⟨984480, by rfl⟩ : syracuseStep 2625281 = 1968961) B1968961
theorem B691975 : Blo 690315 691975 := bstep (se 1 (by rfl) ⟨518981, by rfl⟩ : syracuseStep 691975 = 1037963) B1037963
theorem B691983 : Blo 690315 691983 := bstep (se 1 (by rfl) ⟨518987, by rfl⟩ : syracuseStep 691983 = 1037975) B1037975
theorem B1183547 : Blo 690315 1183547 := bstep (se 1 (by rfl) ⟨887660, by rfl⟩ : syracuseStep 1183547 = 1775321) B1775321
theorem B692027 : Blo 690315 692027 := bstep (se 1 (by rfl) ⟨519020, by rfl⟩ : syracuseStep 692027 = 1038041) B1038041
theorem B6328153 : Blo 690315 6328153 := bstep (se 2 (by rfl) ⟨2373057, by rfl⟩ : syracuseStep 6328153 = 4746115) B4746115
theorem B692103 : Blo 690315 692103 := bstep (se 1 (by rfl) ⟨519077, by rfl⟩ : syracuseStep 692103 = 1038155) B1038155
theorem B692111 : Blo 690315 692111 := bstep (se 1 (by rfl) ⟨519083, by rfl⟩ : syracuseStep 692111 = 1038167) B1038167
theorem B692155 : Blo 690315 692155 := bstep (se 1 (by rfl) ⟨519116, by rfl⟩ : syracuseStep 692155 = 1038233) B1038233
theorem B2953169 : Blo 690315 2953169 := bstep (se 2 (by rfl) ⟨1107438, by rfl⟩ : syracuseStep 2953169 = 2214877) B2214877
theorem B692231 : Blo 690315 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B692239 : Blo 690315 692239 := bstep (se 1 (by rfl) ⟨519179, by rfl⟩ : syracuseStep 692239 = 1038359) B1038359
theorem B692283 : Blo 690315 692283 := bstep (se 1 (by rfl) ⟨519212, by rfl⟩ : syracuseStep 692283 = 1038425) B1038425
theorem B1970237 : Blo 690315 1970237 := bstep (se 3 (by rfl) ⟨369419, by rfl⟩ : syracuseStep 1970237 = 738839) B738839
theorem B692359 : Blo 690315 692359 := bstep (se 1 (by rfl) ⟨519269, by rfl⟩ : syracuseStep 692359 = 1038539) B1038539
theorem B692367 : Blo 690315 692367 := bstep (se 1 (by rfl) ⟨519275, by rfl⟩ : syracuseStep 692367 = 1038551) B1038551
theorem B692411 : Blo 690315 692411 := bstep (se 1 (by rfl) ⟨519308, by rfl⟩ : syracuseStep 692411 = 1038617) B1038617
theorem B1478857 : Blo 690315 1478857 := bstep (se 2 (by rfl) ⟨554571, by rfl⟩ : syracuseStep 1478857 = 1109143) B1109143
theorem B692487 : Blo 690315 692487 := bstep (se 1 (by rfl) ⟨519365, by rfl⟩ : syracuseStep 692487 = 1038731) B1038731
theorem B692495 : Blo 690315 692495 := bstep (se 1 (by rfl) ⟨519371, by rfl⟩ : syracuseStep 692495 = 1038743) B1038743
theorem B692539 : Blo 690315 692539 := bstep (se 1 (by rfl) ⟨519404, by rfl⟩ : syracuseStep 692539 = 1038809) B1038809
theorem B692615 : Blo 690315 692615 := bstep (se 1 (by rfl) ⟨519461, by rfl⟩ : syracuseStep 692615 = 1038923) B1038923
theorem B1315207 : Blo 690315 1315207 := bstep (se 1 (by rfl) ⟨986405, by rfl⟩ : syracuseStep 1315207 = 1972811) B1972811
theorem B692623 : Blo 690315 692623 := bstep (se 1 (by rfl) ⟨519467, by rfl⟩ : syracuseStep 692623 = 1038935) B1038935
theorem B692667 : Blo 690315 692667 := bstep (se 1 (by rfl) ⟨519500, by rfl⟩ : syracuseStep 692667 = 1039001) B1039001
theorem B692743 : Blo 690315 692743 := bstep (se 1 (by rfl) ⟨519557, by rfl⟩ : syracuseStep 692743 = 1039115) B1039115
theorem B692751 : Blo 690315 692751 := bstep (se 1 (by rfl) ⟨519563, by rfl⟩ : syracuseStep 692751 = 1039127) B1039127
theorem B2331179 : Blo 690315 2331179 := bstep (se 1 (by rfl) ⟨1748384, by rfl⟩ : syracuseStep 2331179 = 3496769) B3496769
theorem B692795 : Blo 690315 692795 := bstep (se 1 (by rfl) ⟨519596, by rfl⟩ : syracuseStep 692795 = 1039193) B1039193
theorem B1053257 : Blo 690315 1053257 := bstep (se 2 (by rfl) ⟨394971, by rfl⟩ : syracuseStep 1053257 = 789943) B789943
theorem B692871 : Blo 690315 692871 := bstep (se 1 (by rfl) ⟨519653, by rfl⟩ : syracuseStep 692871 = 1039307) B1039307
theorem B692879 : Blo 690315 692879 := bstep (se 1 (by rfl) ⟨519659, by rfl⟩ : syracuseStep 692879 = 1039319) B1039319
theorem B2003609 : Blo 690315 2003609 := bstep (se 2 (by rfl) ⟨751353, by rfl⟩ : syracuseStep 2003609 = 1502707) B1502707
theorem B692923 : Blo 690315 692923 := bstep (se 1 (by rfl) ⟨519692, by rfl⟩ : syracuseStep 692923 = 1039385) B1039385
theorem B692999 : Blo 690315 692999 := bstep (se 1 (by rfl) ⟨519749, by rfl⟩ : syracuseStep 692999 = 1039499) B1039499
theorem B693007 : Blo 690315 693007 := bstep (se 1 (by rfl) ⟨519755, by rfl⟩ : syracuseStep 693007 = 1039511) B1039511
theorem B10523429 : Blo 690315 10523429 := bstep (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) B1973143
theorem B693051 : Blo 690315 693051 := bstep (se 1 (by rfl) ⟨519788, by rfl⟩ : syracuseStep 693051 = 1039577) B1039577
theorem B693127 : Blo 690315 693127 := bstep (se 1 (by rfl) ⟨519845, by rfl⟩ : syracuseStep 693127 = 1039691) B1039691
theorem B693135 : Blo 690315 693135 := bstep (se 1 (by rfl) ⟨519851, by rfl⟩ : syracuseStep 693135 = 1039703) B1039703
theorem B2626451 : Blo 690315 2626451 := bstep (se 1 (by rfl) ⟨1969838, by rfl⟩ : syracuseStep 2626451 = 3939677) B3939677
theorem B3511187 : Blo 690315 3511187 := bstep (se 1 (by rfl) ⟨2633390, by rfl⟩ : syracuseStep 3511187 = 5266781) B5266781
theorem B693179 : Blo 690315 693179 := bstep (se 1 (by rfl) ⟨519884, by rfl⟩ : syracuseStep 693179 = 1039769) B1039769
theorem B693255 : Blo 690315 693255 := bstep (se 1 (by rfl) ⟨519941, by rfl⟩ : syracuseStep 693255 = 1039883) B1039883
theorem B693263 : Blo 690315 693263 := bstep (se 1 (by rfl) ⟨519947, by rfl⟩ : syracuseStep 693263 = 1039895) B1039895
theorem B693307 : Blo 690315 693307 := bstep (se 1 (by rfl) ⟨519980, by rfl⟩ : syracuseStep 693307 = 1039961) B1039961
theorem B1184887 : Blo 690315 1184887 := bstep (se 1 (by rfl) ⟨888665, by rfl⟩ : syracuseStep 1184887 = 1777331) B1777331
theorem B693383 : Blo 690315 693383 := bstep (se 1 (by rfl) ⟨520037, by rfl⟩ : syracuseStep 693383 = 1040075) B1040075
theorem B693391 : Blo 690315 693391 := bstep (se 1 (by rfl) ⟨520043, by rfl⟩ : syracuseStep 693391 = 1040087) B1040087
theorem B1971353 : Blo 690315 1971353 := bstep (se 2 (by rfl) ⟨739257, by rfl⟩ : syracuseStep 1971353 = 1478515) B1478515
theorem B1479865 : Blo 690315 1479865 := bstep (se 2 (by rfl) ⟨554949, by rfl⟩ : syracuseStep 1479865 = 1109899) B1109899
theorem B693435 : Blo 690315 693435 := bstep (se 1 (by rfl) ⟨520076, by rfl⟩ : syracuseStep 693435 = 1040153) B1040153
theorem B693511 : Blo 690315 693511 := bstep (se 1 (by rfl) ⟨520133, by rfl⟩ : syracuseStep 693511 = 1040267) B1040267
theorem B693519 : Blo 690315 693519 := bstep (se 1 (by rfl) ⟨520139, by rfl⟩ : syracuseStep 693519 = 1040279) B1040279
theorem B693563 : Blo 690315 693563 := bstep (se 1 (by rfl) ⟨520172, by rfl⟩ : syracuseStep 693563 = 1040345) B1040345
theorem B2626951 : Blo 690315 2626951 := bstep (se 1 (by rfl) ⟨1970213, by rfl⟩ : syracuseStep 2626951 = 3940427) B3940427
theorem B693639 : Blo 690315 693639 := bstep (se 1 (by rfl) ⟨520229, by rfl⟩ : syracuseStep 693639 = 1040459) B1040459
theorem B693647 : Blo 690315 693647 := bstep (se 1 (by rfl) ⟨520235, by rfl⟩ : syracuseStep 693647 = 1040471) B1040471
theorem B1480121 : Blo 690315 1480121 := bstep (se 2 (by rfl) ⟨555045, by rfl⟩ : syracuseStep 1480121 = 1110091) B1110091
theorem B693691 : Blo 690315 693691 := bstep (se 1 (by rfl) ⟨520268, by rfl⟩ : syracuseStep 693691 = 1040537) B1040537
theorem B13342157 : Blo 690315 13342157 := bstep (se 3 (by rfl) ⟨2501654, by rfl⟩ : syracuseStep 13342157 = 5003309) B5003309
theorem B693767 : Blo 690315 693767 := bstep (se 1 (by rfl) ⟨520325, by rfl⟩ : syracuseStep 693767 = 1040651) B1040651
theorem B1480207 : Blo 690315 1480207 := bstep (se 1 (by rfl) ⟨1110155, by rfl⟩ : syracuseStep 1480207 = 2220311) B2220311
theorem B693775 : Blo 690315 693775 := bstep (se 1 (by rfl) ⟨520331, by rfl⟩ : syracuseStep 693775 = 1040663) B1040663
theorem B693819 : Blo 690315 693819 := bstep (se 1 (by rfl) ⟨520364, by rfl⟩ : syracuseStep 693819 = 1040729) B1040729
theorem B693895 : Blo 690315 693895 := bstep (se 1 (by rfl) ⟨520421, by rfl⟩ : syracuseStep 693895 = 1040843) B1040843
theorem B693903 : Blo 690315 693903 := bstep (se 1 (by rfl) ⟨520427, by rfl⟩ : syracuseStep 693903 = 1040855) B1040855
theorem B693947 : Blo 690315 693947 := bstep (se 1 (by rfl) ⟨520460, by rfl⟩ : syracuseStep 693947 = 1040921) B1040921
theorem B694023 : Blo 690315 694023 := bstep (se 1 (by rfl) ⟨520517, by rfl⟩ : syracuseStep 694023 = 1041035) B1041035
theorem B694031 : Blo 690315 694031 := bstep (se 1 (by rfl) ⟨520523, by rfl⟩ : syracuseStep 694031 = 1041047) B1041047
theorem B2332475 : Blo 690315 2332475 := bstep (se 1 (by rfl) ⟨1749356, by rfl⟩ : syracuseStep 2332475 = 3498713) B3498713
theorem B694075 : Blo 690315 694075 := bstep (se 1 (by rfl) ⟨520556, by rfl⟩ : syracuseStep 694075 = 1041113) B1041113
theorem B7870283 : Blo 690315 7870283 := bstep (se 1 (by rfl) ⟨5902712, by rfl⟩ : syracuseStep 7870283 = 11805425) B11805425
theorem B4200281 : Blo 690315 4200281 := bstep (se 2 (by rfl) ⟨1575105, by rfl⟩ : syracuseStep 4200281 = 3150211) B3150211
theorem B1873799 : Blo 690315 1873799 := bstep (se 1 (by rfl) ⟨1405349, by rfl⟩ : syracuseStep 1873799 = 2810699) B2810699
theorem B694151 : Blo 690315 694151 := bstep (se 1 (by rfl) ⟨520613, by rfl⟩ : syracuseStep 694151 = 1041227) B1041227
theorem B694159 : Blo 690315 694159 := bstep (se 1 (by rfl) ⟨520619, by rfl⟩ : syracuseStep 694159 = 1041239) B1041239
theorem B694203 : Blo 690315 694203 := bstep (se 1 (by rfl) ⟨520652, by rfl⟩ : syracuseStep 694203 = 1041305) B1041305
theorem B694279 : Blo 690315 694279 := bstep (se 1 (by rfl) ⟨520709, by rfl⟩ : syracuseStep 694279 = 1041419) B1041419
theorem B694287 : Blo 690315 694287 := bstep (se 1 (by rfl) ⟨520715, by rfl⟩ : syracuseStep 694287 = 1041431) B1041431
theorem B1316999 : Blo 690315 1316999 := bstep (se 1 (by rfl) ⟨987749, by rfl⟩ : syracuseStep 1316999 = 1975499) B1975499
theorem B1185977 : Blo 690315 1185977 := bstep (se 2 (by rfl) ⟨444741, by rfl⟩ : syracuseStep 1185977 = 889483) B889483
theorem B2332961 : Blo 690315 2332961 := bstep (se 2 (by rfl) ⟨874860, by rfl⟩ : syracuseStep 2332961 = 1749721) B1749721
theorem B1055033 : Blo 690315 1055033 := bstep (se 2 (by rfl) ⟨395637, by rfl⟩ : syracuseStep 1055033 = 791275) B791275
theorem B1481095 : Blo 690315 1481095 := bstep (se 1 (by rfl) ⟨1110821, by rfl⟩ : syracuseStep 1481095 = 2221643) B2221643
theorem B1972765 : Blo 690315 1972765 := bstep (se 3 (by rfl) ⟨369893, by rfl⟩ : syracuseStep 1972765 = 739787) B739787
theorem B1481249 : Blo 690315 1481249 := bstep (se 2 (by rfl) ⟨555468, by rfl⟩ : syracuseStep 1481249 = 1110937) B1110937
theorem B8428151 : Blo 690315 8428151 := bstep (se 1 (by rfl) ⟨6321113, by rfl⟩ : syracuseStep 8428151 = 12642227) B12642227
theorem B1972937 : Blo 690315 1972937 := bstep (se 2 (by rfl) ⟨739851, by rfl⟩ : syracuseStep 1972937 = 1479703) B1479703
theorem B1972993 : Blo 690315 1972993 := bstep (se 2 (by rfl) ⟨739872, by rfl⟩ : syracuseStep 1972993 = 1479745) B1479745
theorem B15964933 : Blo 690315 15964933 := bstep (se 4 (by rfl) ⟨1496712, by rfl⟩ : syracuseStep 15964933 = 2993425) B2993425
theorem B2333555 : Blo 690315 2333555 := bstep (se 1 (by rfl) ⟨1750166, by rfl⟩ : syracuseStep 2333555 = 3500333) B3500333
theorem B1481591 : Blo 690315 1481591 := bstep (se 1 (by rfl) ⟨1111193, by rfl⟩ : syracuseStep 1481591 = 2222387) B2222387
theorem B1481761 : Blo 690315 1481761 := bstep (se 2 (by rfl) ⟨555660, by rfl⟩ : syracuseStep 1481761 = 1111321) B1111321
theorem B1973335 : Blo 690315 1973335 := bstep (se 1 (by rfl) ⟨1480001, by rfl⟩ : syracuseStep 1973335 = 2960003) B2960003
theorem B10132867 : Blo 690315 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B7085839 : Blo 690315 7085839 := bstep (se 1 (by rfl) ⟨5314379, by rfl⟩ : syracuseStep 7085839 = 10628759) B10628759
theorem B3514265 : Blo 690315 3514265 := bstep (se 2 (by rfl) ⟨1317849, by rfl⟩ : syracuseStep 3514265 = 2635699) B2635699
theorem B4988951 : Blo 690315 4988951 := bstep (se 1 (by rfl) ⟨3741713, by rfl⟩ : syracuseStep 4988951 = 7483427) B7483427
theorem B1581089 : Blo 690315 1581089 := bstep (se 2 (by rfl) ⟨592908, by rfl⟩ : syracuseStep 1581089 = 1185817) B1185817
theorem B2498627 : Blo 690315 2498627 := bstep (se 1 (by rfl) ⟨1873970, by rfl⟩ : syracuseStep 2498627 = 3747941) B3747941
theorem B2367575 : Blo 690315 2367575 := bstep (se 1 (by rfl) ⟨1775681, by rfl⟩ : syracuseStep 2367575 = 3551363) B3551363
theorem B3940609 : Blo 690315 3940609 := bstep (se 2 (by rfl) ⟨1477728, by rfl⟩ : syracuseStep 3940609 = 2955457) B2955457
theorem B1876567 : Blo 690315 1876567 := bstep (se 1 (by rfl) ⟨1407425, by rfl⟩ : syracuseStep 1876567 = 2814851) B2814851
theorem B3941135 : Blo 690315 3941135 := bstep (se 1 (by rfl) ⟨2955851, by rfl⟩ : syracuseStep 3941135 = 5911703) B5911703
theorem B2958227 : Blo 690315 2958227 := bstep (se 1 (by rfl) ⟨2218670, by rfl⟩ : syracuseStep 2958227 = 4437341) B4437341
theorem B2336147 : Blo 690315 2336147 := bstep (se 1 (by rfl) ⟨1752110, by rfl⟩ : syracuseStep 2336147 = 3504221) B3504221
theorem B29992517 : Blo 690315 29992517 := bstep (se 4 (by rfl) ⟨2811798, by rfl⟩ : syracuseStep 29992517 = 5623597) B5623597
theorem B2107147 : Blo 690315 2107147 := bstep (se 1 (by rfl) ⟨1580360, by rfl⟩ : syracuseStep 2107147 = 3160721) B3160721
theorem B1976183 : Blo 690315 1976183 := bstep (se 1 (by rfl) ⟨1482137, by rfl⟩ : syracuseStep 1976183 = 2964275) B2964275
theorem B20195351 : Blo 690315 20195351 := bstep (se 1 (by rfl) ⟨15146513, by rfl⟩ : syracuseStep 20195351 = 30293027) B30293027
theorem B3942593 : Blo 690315 3942593 := bstep (se 2 (by rfl) ⟨1478472, by rfl⟩ : syracuseStep 3942593 = 2956945) B2956945
theorem B3549491 : Blo 690315 3549491 := bstep (se 1 (by rfl) ⟨2662118, by rfl⟩ : syracuseStep 3549491 = 5324237) B5324237
theorem B7481693 : Blo 690315 7481693 := bstep (se 3 (by rfl) ⟨1402817, by rfl⟩ : syracuseStep 7481693 = 2805635) B2805635
theorem B2959901 : Blo 690315 2959901 := bstep (se 3 (by rfl) ⟨554981, by rfl⟩ : syracuseStep 2959901 = 1109963) B1109963
theorem B1747727 : Blo 690315 1747727 := bstep (se 1 (by rfl) ⟨1310795, by rfl⟩ : syracuseStep 1747727 = 2621591) B2621591
theorem B2337551 : Blo 690315 2337551 := bstep (se 1 (by rfl) ⟨1753163, by rfl⟩ : syracuseStep 2337551 = 3506327) B3506327
theorem B2632601 : Blo 690315 2632601 := bstep (se 2 (by rfl) ⟨987225, by rfl⟩ : syracuseStep 2632601 = 1974451) B1974451
theorem B2337821 : Blo 690315 2337821 := bstep (se 3 (by rfl) ⟨438341, by rfl⟩ : syracuseStep 2337821 = 876683) B876683
theorem B16166279 : Blo 690315 16166279 := bstep (se 1 (by rfl) ⟨12124709, by rfl⟩ : syracuseStep 16166279 = 24249419) B24249419
theorem B1748425 : Blo 690315 1748425 := bstep (se 2 (by rfl) ⟨655659, by rfl⟩ : syracuseStep 1748425 = 1311319) B1311319
theorem B1748567 : Blo 690315 1748567 := bstep (se 1 (by rfl) ⟨1311425, by rfl⟩ : syracuseStep 1748567 = 2622851) B2622851
theorem B3321431 : Blo 690315 3321431 := bstep (se 1 (by rfl) ⟨2491073, by rfl⟩ : syracuseStep 3321431 = 4982147) B4982147
theorem B3322259 : Blo 690315 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B2339225 : Blo 690315 2339225 := bstep (se 2 (by rfl) ⟨877209, by rfl⟩ : syracuseStep 2339225 = 1754419) B1754419
theorem B3944983 : Blo 690315 3944983 := bstep (se 1 (by rfl) ⟨2958737, by rfl⟩ : syracuseStep 3944983 = 5917475) B5917475
theorem B2109995 : Blo 690315 2109995 := bstep (se 1 (by rfl) ⟨1582496, by rfl⟩ : syracuseStep 2109995 = 3164993) B3164993
theorem B5256089 : Blo 690315 5256089 := bstep (se 2 (by rfl) ⟨1971033, by rfl⟩ : syracuseStep 5256089 = 3942067) B3942067
theorem B2339927 : Blo 690315 2339927 := bstep (se 1 (by rfl) ⟨1754945, by rfl⟩ : syracuseStep 2339927 = 3509891) B3509891
theorem B1553543 : Blo 690315 1553543 := bstep (se 1 (by rfl) ⟨1165157, by rfl⟩ : syracuseStep 1553543 = 2330315) B2330315
theorem B1553723 : Blo 690315 1553723 := bstep (se 1 (by rfl) ⟨1165292, by rfl⟩ : syracuseStep 1553723 = 2330585) B2330585
theorem B7091549 : Blo 690315 7091549 := bstep (se 3 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 7091549 = 2659331) B2659331
theorem B1553849 : Blo 690315 1553849 := bstep (se 2 (by rfl) ⟨582693, by rfl⟩ : syracuseStep 1553849 = 1165387) B1165387
theorem B2340413 : Blo 690315 2340413 := bstep (se 3 (by rfl) ⟨438827, by rfl⟩ : syracuseStep 2340413 = 877655) B877655
theorem B1750643 : Blo 690315 1750643 := bstep (se 1 (by rfl) ⟨1312982, by rfl⟩ : syracuseStep 1750643 = 2625965) B2625965
theorem B2111233 : Blo 690315 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B1554191 : Blo 690315 1554191 := bstep (se 1 (by rfl) ⟨1165643, by rfl⟩ : syracuseStep 1554191 = 2331287) B2331287
theorem B1554209 : Blo 690315 1554209 := bstep (se 2 (by rfl) ⟨582828, by rfl⟩ : syracuseStep 1554209 = 1165657) B1165657
theorem B1685537 : Blo 690315 1685537 := bstep (se 2 (by rfl) ⟨632076, by rfl⟩ : syracuseStep 1685537 = 1264153) B1264153
theorem B1554551 : Blo 690315 1554551 := bstep (se 1 (by rfl) ⟨1165913, by rfl⟩ : syracuseStep 1554551 = 2331827) B2331827
theorem B1751159 : Blo 690315 1751159 := bstep (se 1 (by rfl) ⟨1313369, by rfl⟩ : syracuseStep 1751159 = 2626739) B2626739
theorem B1554731 : Blo 690315 1554731 := bstep (se 1 (by rfl) ⟨1166048, by rfl⟩ : syracuseStep 1554731 = 2332097) B2332097
theorem B7125383 : Blo 690315 7125383 := bstep (se 1 (by rfl) ⟨5344037, by rfl⟩ : syracuseStep 7125383 = 10688075) B10688075
theorem B6732179 : Blo 690315 6732179 := bstep (se 1 (by rfl) ⟨5049134, by rfl⟩ : syracuseStep 6732179 = 10098269) B10098269
theorem B2636185 : Blo 690315 2636185 := bstep (se 2 (by rfl) ⟨988569, by rfl⟩ : syracuseStep 2636185 = 1977139) B1977139
theorem B1555091 : Blo 690315 1555091 := bstep (se 1 (by rfl) ⟨1166318, by rfl⟩ : syracuseStep 1555091 = 2332637) B2332637
theorem B1555145 : Blo 690315 1555145 := bstep (se 2 (by rfl) ⟨583179, by rfl⟩ : syracuseStep 1555145 = 1166359) B1166359
theorem B2964205 : Blo 690315 2964205 := bstep (se 3 (by rfl) ⟨555788, by rfl⟩ : syracuseStep 2964205 = 1111577) B1111577
theorem B5258033 : Blo 690315 5258033 := bstep (se 2 (by rfl) ⟨1971762, by rfl⟩ : syracuseStep 5258033 = 3943525) B3943525
theorem B7486283 : Blo 690315 7486283 := bstep (se 1 (by rfl) ⟨5614712, by rfl⟩ : syracuseStep 7486283 = 11229425) B11229425
theorem B3947399 : Blo 690315 3947399 := bstep (se 1 (by rfl) ⟨2960549, by rfl⟩ : syracuseStep 3947399 = 5921099) B5921099
theorem B2964377 : Blo 690315 2964377 := bstep (se 2 (by rfl) ⟨1111641, by rfl⟩ : syracuseStep 2964377 = 2223283) B2223283
theorem B2243513 : Blo 690315 2243513 := bstep (se 2 (by rfl) ⟨841317, by rfl⟩ : syracuseStep 2243513 = 1682635) B1682635
theorem B2341817 : Blo 690315 2341817 := bstep (se 2 (by rfl) ⟨878181, by rfl⟩ : syracuseStep 2341817 = 1756363) B1756363
theorem B1752151 : Blo 690315 1752151 := bstep (se 1 (by rfl) ⟨1314113, by rfl⟩ : syracuseStep 1752151 = 2628227) B2628227
theorem B3325121 : Blo 690315 3325121 := bstep (se 2 (by rfl) ⟨1246920, by rfl⟩ : syracuseStep 3325121 = 2493841) B2493841
theorem B2997485 : Blo 690315 2997485 := bstep (se 3 (by rfl) ⟨562028, by rfl⟩ : syracuseStep 2997485 = 1124057) B1124057
theorem B1555847 : Blo 690315 1555847 := bstep (se 1 (by rfl) ⟨1166885, by rfl⟩ : syracuseStep 1555847 = 2333771) B2333771
theorem B1752455 : Blo 690315 1752455 := bstep (se 1 (by rfl) ⟨1314341, by rfl⟩ : syracuseStep 1752455 = 2628683) B2628683
theorem B3554705 : Blo 690315 3554705 := bstep (se 2 (by rfl) ⟨1333014, by rfl⟩ : syracuseStep 3554705 = 2666029) B2666029
theorem B2801081 : Blo 690315 2801081 := bstep (se 2 (by rfl) ⟨1050405, by rfl⟩ : syracuseStep 2801081 = 2100811) B2100811
theorem B4996561 : Blo 690315 4996561 := bstep (se 2 (by rfl) ⟨1873710, by rfl⟩ : syracuseStep 4996561 = 3747421) B3747421
theorem B1752587 : Blo 690315 1752587 := bstep (se 1 (by rfl) ⟨1314440, by rfl⟩ : syracuseStep 1752587 = 2628881) B2628881
theorem B2342411 : Blo 690315 2342411 := bstep (se 1 (by rfl) ⟨1756808, by rfl⟩ : syracuseStep 2342411 = 3513617) B3513617
theorem B1556027 : Blo 690315 1556027 := bstep (se 1 (by rfl) ⟨1167020, by rfl⟩ : syracuseStep 1556027 = 2334041) B2334041
theorem B2342519 : Blo 690315 2342519 := bstep (se 1 (by rfl) ⟨1756889, by rfl⟩ : syracuseStep 2342519 = 3513779) B3513779
theorem B1556153 : Blo 690315 1556153 := bstep (se 2 (by rfl) ⟨583557, by rfl⟩ : syracuseStep 1556153 = 1167115) B1167115
theorem B6668081 : Blo 690315 6668081 := bstep (se 2 (by rfl) ⟨2500530, by rfl⟩ : syracuseStep 6668081 = 5001061) B5001061
theorem B11255755 : Blo 690315 11255755 := bstep (se 1 (by rfl) ⟨8441816, by rfl⟩ : syracuseStep 11255755 = 16883633) B16883633
theorem B1556495 : Blo 690315 1556495 := bstep (se 1 (by rfl) ⟨1167371, by rfl⟩ : syracuseStep 1556495 = 2334743) B2334743
theorem B1753103 : Blo 690315 1753103 := bstep (se 1 (by rfl) ⟨1314827, by rfl⟩ : syracuseStep 1753103 = 2629655) B2629655
theorem B1556513 : Blo 690315 1556513 := bstep (se 2 (by rfl) ⟨583692, by rfl⟩ : syracuseStep 1556513 = 1167385) B1167385
theorem B1753235 : Blo 690315 1753235 := bstep (se 1 (by rfl) ⟨1314926, by rfl⟩ : syracuseStep 1753235 = 2629853) B2629853
theorem B3784877 : Blo 690315 3784877 := bstep (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) B1419329
theorem B2343113 : Blo 690315 2343113 := bstep (se 2 (by rfl) ⟨878667, by rfl⟩ : syracuseStep 2343113 = 1757335) B1757335
theorem B2212211 : Blo 690315 2212211 := bstep (se 1 (by rfl) ⟨1659158, by rfl⟩ : syracuseStep 2212211 = 3318317) B3318317
theorem B1556855 : Blo 690315 1556855 := bstep (se 1 (by rfl) ⟨1167641, by rfl⟩ : syracuseStep 1556855 = 2335283) B2335283
theorem B5915015 : Blo 690315 5915015 := bstep (se 1 (by rfl) ⟨4436261, by rfl⟩ : syracuseStep 5915015 = 8872523) B8872523
theorem B1557035 : Blo 690315 1557035 := bstep (se 1 (by rfl) ⟨1167776, by rfl⟩ : syracuseStep 1557035 = 2335553) B2335553
theorem B3949175 : Blo 690315 3949175 := bstep (se 1 (by rfl) ⟨2961881, by rfl⟩ : syracuseStep 3949175 = 5923763) B5923763
theorem B1557395 : Blo 690315 1557395 := bstep (se 1 (by rfl) ⟨1168046, by rfl⟩ : syracuseStep 1557395 = 2336093) B2336093
theorem B1557449 : Blo 690315 1557449 := bstep (se 2 (by rfl) ⟨584043, by rfl⟩ : syracuseStep 1557449 = 1168087) B1168087
theorem B1754369 : Blo 690315 1754369 := bstep (se 2 (by rfl) ⟨657888, by rfl⟩ : syracuseStep 1754369 = 1315777) B1315777
theorem B3949883 : Blo 690315 3949883 := bstep (se 1 (by rfl) ⟨2962412, by rfl⟩ : syracuseStep 3949883 = 5924825) B5924825
theorem B1754743 : Blo 690315 1754743 := bstep (se 1 (by rfl) ⟨1316057, by rfl⟩ : syracuseStep 1754743 = 2632115) B2632115
theorem B1164935 : Blo 690315 1164935 := bstep (se 1 (by rfl) ⟨873701, by rfl⟩ : syracuseStep 1164935 = 1747403) B1747403
theorem B1558151 : Blo 690315 1558151 := bstep (se 1 (by rfl) ⟨1168613, by rfl⟩ : syracuseStep 1558151 = 2337227) B2337227
theorem B1558331 : Blo 690315 1558331 := bstep (se 1 (by rfl) ⟨1168748, by rfl⟩ : syracuseStep 1558331 = 2337497) B2337497
theorem B1558457 : Blo 690315 1558457 := bstep (se 2 (by rfl) ⟨584421, by rfl⟩ : syracuseStep 1558457 = 1168843) B1168843
theorem B1755179 : Blo 690315 1755179 := bstep (se 1 (by rfl) ⟨1316384, by rfl⟩ : syracuseStep 1755179 = 2632769) B2632769
theorem B1165583 : Blo 690315 1165583 := bstep (se 1 (by rfl) ⟨874187, by rfl⟩ : syracuseStep 1165583 = 1748375) B1748375
theorem B1558799 : Blo 690315 1558799 := bstep (se 1 (by rfl) ⟨1169099, by rfl⟩ : syracuseStep 1558799 = 2338199) B2338199
theorem B1558817 : Blo 690315 1558817 := bstep (se 2 (by rfl) ⟨584556, by rfl⟩ : syracuseStep 1558817 = 1169113) B1169113
theorem B7489997 : Blo 690315 7489997 := bstep (se 3 (by rfl) ⟨1404374, by rfl⟩ : syracuseStep 7489997 = 2808749) B2808749
theorem B4508227 : Blo 690315 4508227 := bstep (se 1 (by rfl) ⟨3381170, by rfl⟩ : syracuseStep 4508227 = 6762341) B6762341
theorem B1559159 : Blo 690315 1559159 := bstep (se 1 (by rfl) ⟨1169369, by rfl⟩ : syracuseStep 1559159 = 2338739) B2338739
theorem B5065409 : Blo 690315 5065409 := bstep (se 2 (by rfl) ⟨1899528, by rfl⟩ : syracuseStep 5065409 = 3799057) B3799057
theorem B3951341 : Blo 690315 3951341 := bstep (se 3 (by rfl) ⟨740876, by rfl⟩ : syracuseStep 3951341 = 1481753) B1481753
theorem B1166123 : Blo 690315 1166123 := bstep (se 1 (by rfl) ⟨874592, by rfl⟩ : syracuseStep 1166123 = 1749185) B1749185
theorem B1559339 : Blo 690315 1559339 := bstep (se 1 (by rfl) ⟨1169504, by rfl⟩ : syracuseStep 1559339 = 2339009) B2339009
theorem B1756019 : Blo 690315 1756019 := bstep (se 1 (by rfl) ⟨1317014, by rfl⟩ : syracuseStep 1756019 = 2634029) B2634029
theorem B1756039 : Blo 690315 1756039 := bstep (se 1 (by rfl) ⟨1317029, by rfl⟩ : syracuseStep 1756039 = 2634059) B2634059
theorem B1559699 : Blo 690315 1559699 := bstep (se 1 (by rfl) ⟨1169774, by rfl⟩ : syracuseStep 1559699 = 2339549) B2339549
theorem B1756313 : Blo 690315 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B1166521 : Blo 690315 1166521 := bstep (se 2 (by rfl) ⟨437445, by rfl⟩ : syracuseStep 1166521 = 874891) B874891
theorem B740539 : Blo 690315 740539 := bstep (se 1 (by rfl) ⟨555404, by rfl⟩ : syracuseStep 740539 = 1110809) B1110809
theorem B1559753 : Blo 690315 1559753 := bstep (se 2 (by rfl) ⟨584907, by rfl⟩ : syracuseStep 1559753 = 1169815) B1169815
theorem B1035527 : Blo 690315 1035527 := bstep (se 1 (by rfl) ⟨776645, by rfl⟩ : syracuseStep 1035527 = 1553291) B1553291
theorem B1035563 : Blo 690315 1035563 := bstep (se 1 (by rfl) ⟨776672, by rfl⟩ : syracuseStep 1035563 = 1553345) B1553345
theorem B1756475 : Blo 690315 1756475 := bstep (se 1 (by rfl) ⟨1317356, by rfl⟩ : syracuseStep 1756475 = 2634713) B2634713
theorem B1035593 : Blo 690315 1035593 := bstep (se 2 (by rfl) ⟨388347, by rfl⟩ : syracuseStep 1035593 = 776695) B776695
theorem B1035707 : Blo 690315 1035707 := bstep (se 1 (by rfl) ⟨776780, by rfl⟩ : syracuseStep 1035707 = 1553561) B1553561
theorem B11849165 : Blo 690315 11849165 := bstep (se 3 (by rfl) ⟨2221718, by rfl⟩ : syracuseStep 11849165 = 4443437) B4443437
theorem B1035767 : Blo 690315 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B1035791 : Blo 690315 1035791 := bstep (se 1 (by rfl) ⟨776843, by rfl⟩ : syracuseStep 1035791 = 1553687) B1553687
theorem B1756687 : Blo 690315 1756687 := bstep (se 1 (by rfl) ⟨1317515, by rfl⟩ : syracuseStep 1756687 = 2635031) B2635031
theorem B1035833 : Blo 690315 1035833 := bstep (se 2 (by rfl) ⟨388437, by rfl⟩ : syracuseStep 1035833 = 776875) B776875
theorem B1035911 : Blo 690315 1035911 := bstep (se 1 (by rfl) ⟨776933, by rfl⟩ : syracuseStep 1035911 = 1553867) B1553867
theorem B1035947 : Blo 690315 1035947 := bstep (se 1 (by rfl) ⟨776960, by rfl⟩ : syracuseStep 1035947 = 1553921) B1553921
theorem B1035977 : Blo 690315 1035977 := bstep (se 2 (by rfl) ⟨388491, by rfl⟩ : syracuseStep 1035977 = 776983) B776983
theorem B1756961 : Blo 690315 1756961 := bstep (se 2 (by rfl) ⟨658860, by rfl⟩ : syracuseStep 1756961 = 1317721) B1317721
theorem B1036091 : Blo 690315 1036091 := bstep (se 1 (by rfl) ⟨777068, by rfl⟩ : syracuseStep 1036091 = 1554137) B1554137
theorem B1036151 : Blo 690315 1036151 := bstep (se 1 (by rfl) ⟨777113, by rfl⟩ : syracuseStep 1036151 = 1554227) B1554227
theorem B1167223 : Blo 690315 1167223 := bstep (se 1 (by rfl) ⟨875417, by rfl⟩ : syracuseStep 1167223 = 1750835) B1750835
theorem B1560455 : Blo 690315 1560455 := bstep (se 1 (by rfl) ⟨1170341, by rfl⟩ : syracuseStep 1560455 = 2340683) B2340683
theorem B1036175 : Blo 690315 1036175 := bstep (se 1 (by rfl) ⟨777131, by rfl⟩ : syracuseStep 1036175 = 1554263) B1554263
theorem B4214681 : Blo 690315 4214681 := bstep (se 2 (by rfl) ⟨1580505, by rfl⟩ : syracuseStep 4214681 = 3161011) B3161011
theorem B1036217 : Blo 690315 1036217 := bstep (se 2 (by rfl) ⟨388581, by rfl⟩ : syracuseStep 1036217 = 777163) B777163
theorem B1036295 : Blo 690315 1036295 := bstep (se 1 (by rfl) ⟨777221, by rfl⟩ : syracuseStep 1036295 = 1554443) B1554443
theorem B1036331 : Blo 690315 1036331 := bstep (se 1 (by rfl) ⟨777248, by rfl⟩ : syracuseStep 1036331 = 1554497) B1554497
theorem B1167419 : Blo 690315 1167419 := bstep (se 1 (by rfl) ⟨875564, by rfl⟩ : syracuseStep 1167419 = 1751129) B1751129
theorem B1560635 : Blo 690315 1560635 := bstep (se 1 (by rfl) ⟨1170476, by rfl⟩ : syracuseStep 1560635 = 2340953) B2340953
theorem B1036361 : Blo 690315 1036361 := bstep (se 2 (by rfl) ⟨388635, by rfl⟩ : syracuseStep 1036361 = 777271) B777271
theorem B1560761 : Blo 690315 1560761 := bstep (se 2 (by rfl) ⟨585285, by rfl⟩ : syracuseStep 1560761 = 1170571) B1170571
theorem B1036475 : Blo 690315 1036475 := bstep (se 1 (by rfl) ⟨777356, by rfl⟩ : syracuseStep 1036475 = 1554713) B1554713
theorem B1036535 : Blo 690315 1036535 := bstep (se 1 (by rfl) ⟨777401, by rfl⟩ : syracuseStep 1036535 = 1554803) B1554803
theorem B1036559 : Blo 690315 1036559 := bstep (se 1 (by rfl) ⟨777419, by rfl⟩ : syracuseStep 1036559 = 1554839) B1554839
theorem B1036601 : Blo 690315 1036601 := bstep (se 2 (by rfl) ⟨388725, by rfl⟩ : syracuseStep 1036601 = 777451) B777451
theorem B1036679 : Blo 690315 1036679 := bstep (se 1 (by rfl) ⟨777509, by rfl⟩ : syracuseStep 1036679 = 1555019) B1555019
theorem B1036715 : Blo 690315 1036715 := bstep (se 1 (by rfl) ⟨777536, by rfl⟩ : syracuseStep 1036715 = 1555073) B1555073
theorem B1036745 : Blo 690315 1036745 := bstep (se 2 (by rfl) ⟨388779, by rfl⟩ : syracuseStep 1036745 = 777559) B777559
theorem B1167817 : Blo 690315 1167817 := bstep (se 2 (by rfl) ⟨437931, by rfl⟩ : syracuseStep 1167817 = 875863) B875863
theorem B2249227 : Blo 690315 2249227 := bstep (se 1 (by rfl) ⟨1686920, by rfl⟩ : syracuseStep 2249227 = 3373841) B3373841
theorem B1561103 : Blo 690315 1561103 := bstep (se 1 (by rfl) ⟨1170827, by rfl⟩ : syracuseStep 1561103 = 2341655) B2341655
theorem B1561121 : Blo 690315 1561121 := bstep (se 2 (by rfl) ⟨585420, by rfl⟩ : syracuseStep 1561121 = 1170841) B1170841
theorem B1036859 : Blo 690315 1036859 := bstep (se 1 (by rfl) ⟨777644, by rfl⟩ : syracuseStep 1036859 = 1555289) B1555289
theorem B1036919 : Blo 690315 1036919 := bstep (se 1 (by rfl) ⟨777689, by rfl⟩ : syracuseStep 1036919 = 1555379) B1555379
theorem B1036943 : Blo 690315 1036943 := bstep (se 1 (by rfl) ⟨777707, by rfl⟩ : syracuseStep 1036943 = 1555415) B1555415
theorem B3330733 : Blo 690315 3330733 := bstep (se 3 (by rfl) ⟨624512, by rfl⟩ : syracuseStep 3330733 = 1249025) B1249025
theorem B1036985 : Blo 690315 1036985 := bstep (se 2 (by rfl) ⟨388869, by rfl⟩ : syracuseStep 1036985 = 777739) B777739
theorem B1037063 : Blo 690315 1037063 := bstep (se 1 (by rfl) ⟨777797, by rfl⟩ : syracuseStep 1037063 = 1555595) B1555595
theorem B1037099 : Blo 690315 1037099 := bstep (se 1 (by rfl) ⟨777824, by rfl⟩ : syracuseStep 1037099 = 1555649) B1555649
theorem B8409905 : Blo 690315 8409905 := bstep (se 2 (by rfl) ⟨3153714, by rfl⟩ : syracuseStep 8409905 = 6307429) B6307429
theorem B1266491 : Blo 690315 1266491 := bstep (se 1 (by rfl) ⟨949868, by rfl⟩ : syracuseStep 1266491 = 1899737) B1899737
theorem B1037129 : Blo 690315 1037129 := bstep (se 2 (by rfl) ⟨388923, by rfl⟩ : syracuseStep 1037129 = 777847) B777847
theorem B6411097 : Blo 690315 6411097 := bstep (se 2 (by rfl) ⟨2404161, by rfl⟩ : syracuseStep 6411097 = 4808323) B4808323
theorem B12342131 : Blo 690315 12342131 := bstep (se 1 (by rfl) ⟨9256598, by rfl⟩ : syracuseStep 12342131 = 18513197) B18513197
theorem B1561463 : Blo 690315 1561463 := bstep (se 1 (by rfl) ⟨1171097, by rfl⟩ : syracuseStep 1561463 = 2342195) B2342195
theorem B1037243 : Blo 690315 1037243 := bstep (se 1 (by rfl) ⟨777932, by rfl⟩ : syracuseStep 1037243 = 1555865) B1555865
theorem B1037303 : Blo 690315 1037303 := bstep (se 1 (by rfl) ⟨777977, by rfl⟩ : syracuseStep 1037303 = 1555955) B1555955
theorem B1037327 : Blo 690315 1037327 := bstep (se 1 (by rfl) ⟨777995, by rfl⟩ : syracuseStep 1037327 = 1555991) B1555991
theorem B1561643 : Blo 690315 1561643 := bstep (se 1 (by rfl) ⟨1171232, by rfl⟩ : syracuseStep 1561643 = 2342465) B2342465
theorem B1037369 : Blo 690315 1037369 := bstep (se 2 (by rfl) ⟨389013, by rfl⟩ : syracuseStep 1037369 = 778027) B778027
theorem B3953731 : Blo 690315 3953731 := bstep (se 1 (by rfl) ⟨2965298, by rfl⟩ : syracuseStep 3953731 = 5930597) B5930597
theorem B1037447 : Blo 690315 1037447 := bstep (se 1 (by rfl) ⟨778085, by rfl⟩ : syracuseStep 1037447 = 1556171) B1556171
theorem B1168519 : Blo 690315 1168519 := bstep (se 1 (by rfl) ⟨876389, by rfl⟩ : syracuseStep 1168519 = 1752779) B1752779
theorem B1037483 : Blo 690315 1037483 := bstep (se 1 (by rfl) ⟨778112, by rfl⟩ : syracuseStep 1037483 = 1556225) B1556225
theorem B1037513 : Blo 690315 1037513 := bstep (se 2 (by rfl) ⟨389067, by rfl⟩ : syracuseStep 1037513 = 778135) B778135
theorem B3495149 : Blo 690315 3495149 := bstep (se 3 (by rfl) ⟨655340, by rfl⟩ : syracuseStep 3495149 = 1310681) B1310681
theorem B1266959 : Blo 690315 1266959 := bstep (se 1 (by rfl) ⟨950219, by rfl⟩ : syracuseStep 1266959 = 1900439) B1900439
theorem B1037627 : Blo 690315 1037627 := bstep (se 1 (by rfl) ⟨778220, by rfl⟩ : syracuseStep 1037627 = 1556441) B1556441
theorem B1037687 : Blo 690315 1037687 := bstep (se 1 (by rfl) ⟨778265, by rfl⟩ : syracuseStep 1037687 = 1556531) B1556531
theorem B1037711 : Blo 690315 1037711 := bstep (se 1 (by rfl) ⟨778283, by rfl⟩ : syracuseStep 1037711 = 1556567) B1556567
theorem B1562003 : Blo 690315 1562003 := bstep (se 1 (by rfl) ⟨1171502, by rfl⟩ : syracuseStep 1562003 = 2343005) B2343005
theorem B1660313 : Blo 690315 1660313 := bstep (se 2 (by rfl) ⟨622617, by rfl⟩ : syracuseStep 1660313 = 1245235) B1245235
theorem B1037753 : Blo 690315 1037753 := bstep (se 2 (by rfl) ⟨389157, by rfl⟩ : syracuseStep 1037753 = 778315) B778315
theorem B1562057 : Blo 690315 1562057 := bstep (se 2 (by rfl) ⟨585771, by rfl⟩ : syracuseStep 1562057 = 1171543) B1171543
theorem B1037831 : Blo 690315 1037831 := bstep (se 1 (by rfl) ⟨778373, by rfl⟩ : syracuseStep 1037831 = 1556747) B1556747
theorem B1037867 : Blo 690315 1037867 := bstep (se 1 (by rfl) ⟨778400, by rfl⟩ : syracuseStep 1037867 = 1556801) B1556801
theorem B1037897 : Blo 690315 1037897 := bstep (se 2 (by rfl) ⟨389211, by rfl⟩ : syracuseStep 1037897 = 778423) B778423
theorem B1038011 : Blo 690315 1038011 := bstep (se 1 (by rfl) ⟨778508, by rfl⟩ : syracuseStep 1038011 = 1557017) B1557017
theorem B1038071 : Blo 690315 1038071 := bstep (se 1 (by rfl) ⟨778553, by rfl⟩ : syracuseStep 1038071 = 1557107) B1557107
theorem B1038095 : Blo 690315 1038095 := bstep (se 1 (by rfl) ⟨778571, by rfl⟩ : syracuseStep 1038095 = 1557143) B1557143
theorem B1169167 : Blo 690315 1169167 := bstep (se 1 (by rfl) ⟨876875, by rfl⟩ : syracuseStep 1169167 = 1753751) B1753751
theorem B2807585 : Blo 690315 2807585 := bstep (se 2 (by rfl) ⟨1052844, by rfl⟩ : syracuseStep 2807585 = 2105689) B2105689
theorem B1038137 : Blo 690315 1038137 := bstep (se 2 (by rfl) ⟨389301, by rfl⟩ : syracuseStep 1038137 = 778603) B778603
theorem B1038215 : Blo 690315 1038215 := bstep (se 1 (by rfl) ⟨778661, by rfl⟩ : syracuseStep 1038215 = 1557323) B1557323
theorem B9983897 : Blo 690315 9983897 := bstep (se 2 (by rfl) ⟨3743961, by rfl⟩ : syracuseStep 9983897 = 7487923) B7487923
theorem B1038251 : Blo 690315 1038251 := bstep (se 1 (by rfl) ⟨778688, by rfl⟩ : syracuseStep 1038251 = 1557377) B1557377
theorem B1038281 : Blo 690315 1038281 := bstep (se 2 (by rfl) ⟨389355, by rfl⟩ : syracuseStep 1038281 = 778711) B778711
theorem B3495959 : Blo 690315 3495959 := bstep (se 1 (by rfl) ⟨2621969, by rfl⟩ : syracuseStep 3495959 = 5243939) B5243939
theorem B1038395 : Blo 690315 1038395 := bstep (se 1 (by rfl) ⟨778796, by rfl⟩ : syracuseStep 1038395 = 1557593) B1557593
theorem B1038455 : Blo 690315 1038455 := bstep (se 1 (by rfl) ⟨778841, by rfl⟩ : syracuseStep 1038455 = 1557683) B1557683
theorem B1038479 : Blo 690315 1038479 := bstep (se 1 (by rfl) ⟨778859, by rfl⟩ : syracuseStep 1038479 = 1557719) B1557719
theorem B1038521 : Blo 690315 1038521 := bstep (se 2 (by rfl) ⟨389445, by rfl⟩ : syracuseStep 1038521 = 778891) B778891
theorem B1038599 : Blo 690315 1038599 := bstep (se 1 (by rfl) ⟨778949, by rfl⟩ : syracuseStep 1038599 = 1557899) B1557899
theorem B841999 : Blo 690315 841999 := bstep (se 1 (by rfl) ⟨631499, by rfl⟩ : syracuseStep 841999 = 1262999) B1262999
theorem B4741409 : Blo 690315 4741409 := bstep (se 2 (by rfl) ⟨1778028, by rfl⟩ : syracuseStep 4741409 = 3556057) B3556057
theorem B874795 : Blo 690315 874795 := bstep (se 1 (by rfl) ⟨656096, by rfl⟩ : syracuseStep 874795 = 1312193) B1312193
theorem B1038635 : Blo 690315 1038635 := bstep (se 1 (by rfl) ⟨778976, by rfl⟩ : syracuseStep 1038635 = 1557953) B1557953
theorem B1169707 : Blo 690315 1169707 := bstep (se 1 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 1169707 = 1754561) B1754561
theorem B1038665 : Blo 690315 1038665 := bstep (se 2 (by rfl) ⟨389499, by rfl⟩ : syracuseStep 1038665 = 778999) B778999
theorem B5265809 : Blo 690315 5265809 := bstep (se 2 (by rfl) ⟨1974678, by rfl⟩ : syracuseStep 5265809 = 3949357) B3949357
theorem B1169849 : Blo 690315 1169849 := bstep (se 2 (by rfl) ⟨438693, by rfl⟩ : syracuseStep 1169849 = 877387) B877387
theorem B1038779 : Blo 690315 1038779 := bstep (se 1 (by rfl) ⟨779084, by rfl⟩ : syracuseStep 1038779 = 1558169) B1558169
theorem B1038839 : Blo 690315 1038839 := bstep (se 1 (by rfl) ⟨779129, by rfl⟩ : syracuseStep 1038839 = 1558259) B1558259
theorem B1038863 : Blo 690315 1038863 := bstep (se 1 (by rfl) ⟨779147, by rfl⟩ : syracuseStep 1038863 = 1558295) B1558295
theorem B1038905 : Blo 690315 1038905 := bstep (se 2 (by rfl) ⟨389589, by rfl⟩ : syracuseStep 1038905 = 779179) B779179
theorem B3005047 : Blo 690315 3005047 := bstep (se 1 (by rfl) ⟨2253785, by rfl⟩ : syracuseStep 3005047 = 4507571) B4507571
theorem B776839 : Blo 690315 776839 := bstep (se 1 (by rfl) ⟨582629, by rfl⟩ : syracuseStep 776839 = 1165259) B1165259
theorem B1038983 : Blo 690315 1038983 := bstep (se 1 (by rfl) ⟨779237, by rfl⟩ : syracuseStep 1038983 = 1558475) B1558475
theorem B1039019 : Blo 690315 1039019 := bstep (se 1 (by rfl) ⟨779264, by rfl⟩ : syracuseStep 1039019 = 1558529) B1558529
theorem B1039049 : Blo 690315 1039049 := bstep (se 2 (by rfl) ⟨389643, by rfl⟩ : syracuseStep 1039049 = 779287) B779287
theorem B777019 : Blo 690315 777019 := bstep (se 1 (by rfl) ⟨582764, by rfl⟩ : syracuseStep 777019 = 1165529) B1165529
theorem B1039163 : Blo 690315 1039163 := bstep (se 1 (by rfl) ⟨779372, by rfl⟩ : syracuseStep 1039163 = 1558745) B1558745
theorem B1039223 : Blo 690315 1039223 := bstep (se 1 (by rfl) ⟨779417, by rfl⟩ : syracuseStep 1039223 = 1558835) B1558835
theorem B1039247 : Blo 690315 1039247 := bstep (se 1 (by rfl) ⟨779435, by rfl⟩ : syracuseStep 1039247 = 1558871) B1558871
theorem B7887779 : Blo 690315 7887779 := bstep (se 1 (by rfl) ⟨5915834, by rfl⟩ : syracuseStep 7887779 = 11831669) B11831669
theorem B1039289 : Blo 690315 1039289 := bstep (se 2 (by rfl) ⟨389733, by rfl⟩ : syracuseStep 1039289 = 779467) B779467
theorem B1039367 : Blo 690315 1039367 := bstep (se 1 (by rfl) ⟨779525, by rfl⟩ : syracuseStep 1039367 = 1559051) B1559051
theorem B1039403 : Blo 690315 1039403 := bstep (se 1 (by rfl) ⟨779552, by rfl⟩ : syracuseStep 1039403 = 1559105) B1559105
theorem B1039433 : Blo 690315 1039433 := bstep (se 2 (by rfl) ⟨389787, by rfl⟩ : syracuseStep 1039433 = 779575) B779575
theorem B1170551 : Blo 690315 1170551 := bstep (se 1 (by rfl) ⟨877913, by rfl⟩ : syracuseStep 1170551 = 1755827) B1755827
theorem B1039547 : Blo 690315 1039547 := bstep (se 1 (by rfl) ⟨779660, by rfl⟩ : syracuseStep 1039547 = 1559321) B1559321
theorem B875767 : Blo 690315 875767 := bstep (se 1 (by rfl) ⟨656825, by rfl⟩ : syracuseStep 875767 = 1313651) B1313651
theorem B1039607 : Blo 690315 1039607 := bstep (se 1 (by rfl) ⟨779705, by rfl⟩ : syracuseStep 1039607 = 1559411) B1559411
theorem B777487 : Blo 690315 777487 := bstep (se 1 (by rfl) ⟨583115, by rfl⟩ : syracuseStep 777487 = 1166231) B1166231
theorem B1039631 : Blo 690315 1039631 := bstep (se 1 (by rfl) ⟨779723, by rfl⟩ : syracuseStep 1039631 = 1559447) B1559447
theorem B1039673 : Blo 690315 1039673 := bstep (se 2 (by rfl) ⟨389877, by rfl⟩ : syracuseStep 1039673 = 779755) B779755
theorem B3366203 : Blo 690315 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B1039751 : Blo 690315 1039751 := bstep (se 1 (by rfl) ⟨779813, by rfl⟩ : syracuseStep 1039751 = 1559627) B1559627
theorem B1039787 : Blo 690315 1039787 := bstep (se 1 (by rfl) ⟨779840, by rfl⟩ : syracuseStep 1039787 = 1559681) B1559681
theorem B1039817 : Blo 690315 1039817 := bstep (se 2 (by rfl) ⟨389931, by rfl⟩ : syracuseStep 1039817 = 779863) B779863
theorem B876091 : Blo 690315 876091 := bstep (se 1 (by rfl) ⟨657068, by rfl⟩ : syracuseStep 876091 = 1314137) B1314137
theorem B1039931 : Blo 690315 1039931 := bstep (se 1 (by rfl) ⟨779948, by rfl⟩ : syracuseStep 1039931 = 1559897) B1559897
theorem B1171003 : Blo 690315 1171003 := bstep (se 1 (by rfl) ⟨878252, by rfl⟩ : syracuseStep 1171003 = 1756505) B1756505
theorem B1039991 : Blo 690315 1039991 := bstep (se 1 (by rfl) ⟨779993, by rfl⟩ : syracuseStep 1039991 = 1559987) B1559987
theorem B1040015 : Blo 690315 1040015 := bstep (se 1 (by rfl) ⟨780011, by rfl⟩ : syracuseStep 1040015 = 1560023) B1560023
theorem B1040057 : Blo 690315 1040057 := bstep (se 2 (by rfl) ⟨390021, by rfl⟩ : syracuseStep 1040057 = 780043) B780043
theorem B1171145 : Blo 690315 1171145 := bstep (se 2 (by rfl) ⟨439179, by rfl⟩ : syracuseStep 1171145 = 878359) B878359
theorem B777991 : Blo 690315 777991 := bstep (se 1 (by rfl) ⟨583493, by rfl⟩ : syracuseStep 777991 = 1166987) B1166987
theorem B1040135 : Blo 690315 1040135 := bstep (se 1 (by rfl) ⟨780101, by rfl⟩ : syracuseStep 1040135 = 1560203) B1560203
theorem B1040171 : Blo 690315 1040171 := bstep (se 1 (by rfl) ⟨780128, by rfl⟩ : syracuseStep 1040171 = 1560257) B1560257
theorem B1040201 : Blo 690315 1040201 := bstep (se 2 (by rfl) ⟨390075, by rfl⟩ : syracuseStep 1040201 = 780151) B780151
theorem B778171 : Blo 690315 778171 := bstep (se 1 (by rfl) ⟨583628, by rfl⟩ : syracuseStep 778171 = 1167257) B1167257
theorem B1040315 : Blo 690315 1040315 := bstep (se 1 (by rfl) ⟨780236, by rfl⟩ : syracuseStep 1040315 = 1560473) B1560473
theorem B1040375 : Blo 690315 1040375 := bstep (se 1 (by rfl) ⟨780281, by rfl⟩ : syracuseStep 1040375 = 1560563) B1560563
theorem B1040399 : Blo 690315 1040399 := bstep (se 1 (by rfl) ⟨780299, by rfl⟩ : syracuseStep 1040399 = 1560599) B1560599
theorem B8970263 : Blo 690315 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B1040441 : Blo 690315 1040441 := bstep (se 2 (by rfl) ⟨390165, by rfl⟩ : syracuseStep 1040441 = 780331) B780331
theorem B1040519 : Blo 690315 1040519 := bstep (se 1 (by rfl) ⟨780389, by rfl⟩ : syracuseStep 1040519 = 1560779) B1560779
theorem B1040555 : Blo 690315 1040555 := bstep (se 1 (by rfl) ⟨780416, by rfl⟩ : syracuseStep 1040555 = 1560833) B1560833
theorem B1040585 : Blo 690315 1040585 := bstep (se 2 (by rfl) ⟨390219, by rfl⟩ : syracuseStep 1040585 = 780439) B780439
theorem B1663291 : Blo 690315 1663291 := bstep (se 1 (by rfl) ⟨1247468, by rfl⟩ : syracuseStep 1663291 = 2494937) B2494937
theorem B1040699 : Blo 690315 1040699 := bstep (se 1 (by rfl) ⟨780524, by rfl⟩ : syracuseStep 1040699 = 1561049) B1561049
theorem B1040759 : Blo 690315 1040759 := bstep (se 1 (by rfl) ⟨780569, by rfl⟩ : syracuseStep 1040759 = 1561139) B1561139
theorem B1106311 : Blo 690315 1106311 := bstep (se 1 (by rfl) ⟨829733, by rfl⟩ : syracuseStep 1106311 = 1659467) B1659467
theorem B778639 : Blo 690315 778639 := bstep (se 1 (by rfl) ⟨583979, by rfl⟩ : syracuseStep 778639 = 1167959) B1167959
theorem B1040783 : Blo 690315 1040783 := bstep (se 1 (by rfl) ⟨780587, by rfl⟩ : syracuseStep 1040783 = 1561175) B1561175
theorem B1040825 : Blo 690315 1040825 := bstep (se 2 (by rfl) ⟨390309, by rfl⟩ : syracuseStep 1040825 = 780619) B780619
theorem B877063 : Blo 690315 877063 := bstep (se 1 (by rfl) ⟨657797, by rfl⟩ : syracuseStep 877063 = 1315595) B1315595
theorem B1040903 : Blo 690315 1040903 := bstep (se 1 (by rfl) ⟨780677, by rfl⟩ : syracuseStep 1040903 = 1561355) B1561355
theorem B1040939 : Blo 690315 1040939 := bstep (se 1 (by rfl) ⟨780704, by rfl⟩ : syracuseStep 1040939 = 1561409) B1561409
theorem B1040969 : Blo 690315 1040969 := bstep (se 2 (by rfl) ⟨390363, by rfl⟩ : syracuseStep 1040969 = 780727) B780727
theorem B1041083 : Blo 690315 1041083 := bstep (se 1 (by rfl) ⟨780812, by rfl⟩ : syracuseStep 1041083 = 1561625) B1561625
theorem B1041143 : Blo 690315 1041143 := bstep (se 1 (by rfl) ⟨780857, by rfl⟩ : syracuseStep 1041143 = 1561715) B1561715
theorem B5268239 : Blo 690315 5268239 := bstep (se 1 (by rfl) ⟨3951179, by rfl⟩ : syracuseStep 5268239 = 7902359) B7902359
theorem B1041167 : Blo 690315 1041167 := bstep (se 1 (by rfl) ⟨780875, by rfl⟩ : syracuseStep 1041167 = 1561751) B1561751
theorem B1041209 : Blo 690315 1041209 := bstep (se 2 (by rfl) ⟨390453, by rfl⟩ : syracuseStep 1041209 = 780907) B780907
theorem B779143 : Blo 690315 779143 := bstep (se 1 (by rfl) ⟨584357, by rfl⟩ : syracuseStep 779143 = 1168715) B1168715
theorem B1041287 : Blo 690315 1041287 := bstep (se 1 (by rfl) ⟨780965, by rfl⟩ : syracuseStep 1041287 = 1561931) B1561931
theorem B1663897 : Blo 690315 1663897 := bstep (se 2 (by rfl) ⟨623961, by rfl⟩ : syracuseStep 1663897 = 1247923) B1247923
theorem B877483 : Blo 690315 877483 := bstep (se 1 (by rfl) ⟨658112, by rfl⟩ : syracuseStep 877483 = 1316225) B1316225
theorem B1041323 : Blo 690315 1041323 := bstep (se 1 (by rfl) ⟨780992, by rfl⟩ : syracuseStep 1041323 = 1561985) B1561985
theorem B1041353 : Blo 690315 1041353 := bstep (se 2 (by rfl) ⟨390507, by rfl⟩ : syracuseStep 1041353 = 781015) B781015
theorem B3499037 : Blo 690315 3499037 := bstep (se 3 (by rfl) ⟨656069, by rfl⟩ : syracuseStep 3499037 = 1312139) B1312139
theorem B779323 : Blo 690315 779323 := bstep (se 1 (by rfl) ⟨584492, by rfl⟩ : syracuseStep 779323 = 1168985) B1168985
theorem B1041467 : Blo 690315 1041467 := bstep (se 1 (by rfl) ⟨781100, by rfl⟩ : syracuseStep 1041467 = 1562201) B1562201
theorem B1401991 : Blo 690315 1401991 := bstep (se 1 (by rfl) ⟨1051493, by rfl⟩ : syracuseStep 1401991 = 2102987) B2102987
theorem B877711 : Blo 690315 877711 := bstep (se 1 (by rfl) ⟨658283, by rfl⟩ : syracuseStep 877711 = 1316567) B1316567
theorem B8414381 : Blo 690315 8414381 := bstep (se 3 (by rfl) ⟨1577696, by rfl⟩ : syracuseStep 8414381 = 3155393) B3155393
theorem B1893665 : Blo 690315 1893665 := bstep (se 2 (by rfl) ⟨710124, by rfl⟩ : syracuseStep 1893665 = 1420249) B1420249
theorem B1664513 : Blo 690315 1664513 := bstep (se 2 (by rfl) ⟨624192, by rfl⟩ : syracuseStep 1664513 = 1248385) B1248385
theorem B3499523 : Blo 690315 3499523 := bstep (se 1 (by rfl) ⟨2624642, by rfl⟩ : syracuseStep 3499523 = 5249285) B5249285
theorem B779791 : Blo 690315 779791 := bstep (se 1 (by rfl) ⟨584843, by rfl⟩ : syracuseStep 779791 = 1169687) B1169687
theorem B8873549 : Blo 690315 8873549 := bstep (se 3 (by rfl) ⟨1663790, by rfl⟩ : syracuseStep 8873549 = 3327581) B3327581
theorem B1795841 : Blo 690315 1795841 := bstep (se 2 (by rfl) ⟨673440, by rfl⟩ : syracuseStep 1795841 = 1346881) B1346881
theorem B878455 : Blo 690315 878455 := bstep (se 1 (by rfl) ⟨658841, by rfl⟩ : syracuseStep 878455 = 1317683) B1317683
theorem B1402771 : Blo 690315 1402771 := bstep (se 1 (by rfl) ⟨1052078, by rfl⟩ : syracuseStep 1402771 = 2104157) B2104157
theorem B1107913 : Blo 690315 1107913 := bstep (se 2 (by rfl) ⟨415467, by rfl⟩ : syracuseStep 1107913 = 830935) B830935
theorem B780295 : Blo 690315 780295 := bstep (se 1 (by rfl) ⟨585221, by rfl⟩ : syracuseStep 780295 = 1170443) B1170443
theorem B780475 : Blo 690315 780475 := bstep (se 1 (by rfl) ⟨585356, by rfl⟩ : syracuseStep 780475 = 1170713) B1170713
theorem B1108169 : Blo 690315 1108169 := bstep (se 2 (by rfl) ⟨415563, by rfl⟩ : syracuseStep 1108169 = 831127) B831127
theorem B8415697 : Blo 690315 8415697 := bstep (se 2 (by rfl) ⟨3155886, by rfl⟩ : syracuseStep 8415697 = 6311773) B6311773
theorem B780943 : Blo 690315 780943 := bstep (se 1 (by rfl) ⟨585707, by rfl⟩ : syracuseStep 780943 = 1171415) B1171415
theorem B1403849 : Blo 690315 1403849 := bstep (se 2 (by rfl) ⟨526443, by rfl⟩ : syracuseStep 1403849 = 1052887) B1052887
theorem B3501143 : Blo 690315 3501143 := bstep (se 1 (by rfl) ⟨2625857, by rfl⟩ : syracuseStep 3501143 = 5251715) B5251715
theorem B4976093 : Blo 690315 4976093 := bstep (se 3 (by rfl) ⟨933017, by rfl⟩ : syracuseStep 4976093 = 1866035) B1866035
theorem B3501629 : Blo 690315 3501629 := bstep (se 3 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 3501629 = 1313111) B1313111
theorem B23949107 : Blo 690315 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B4255811 : Blo 690315 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B136376945 : Blo 690315 136376945 := bstep (se 2 (by rfl) ⟨51141354, by rfl⟩ : syracuseStep 136376945 = 102282709) B102282709
theorem B947371 : Blo 690315 947371 := bstep (se 1 (by rfl) ⟨710528, by rfl⟩ : syracuseStep 947371 = 1421057) B1421057
theorem B1995977 : Blo 690315 1995977 := bstep (se 2 (by rfl) ⟨748491, by rfl⟩ : syracuseStep 1995977 = 1496983) B1496983
theorem B5928137 : Blo 690315 5928137 := bstep (se 2 (by rfl) ⟨2223051, by rfl⟩ : syracuseStep 5928137 = 4446103) B4446103
theorem B3503411 : Blo 690315 3503411 := bstep (se 1 (by rfl) ⟨2627558, by rfl⟩ : syracuseStep 3503411 = 5255117) B5255117
theorem B16840037 : Blo 690315 16840037 := bstep (se 4 (by rfl) ⟨1578753, by rfl⟩ : syracuseStep 16840037 = 3157507) B3157507
theorem B23950727 : Blo 690315 23950727 := bstep (se 1 (by rfl) ⟨17963045, by rfl⟩ : syracuseStep 23950727 = 35926091) B35926091
theorem B3503735 : Blo 690315 3503735 := bstep (se 1 (by rfl) ⟨2627801, by rfl⟩ : syracuseStep 3503735 = 5255603) B5255603
theorem B4388951 : Blo 690315 4388951 := bstep (se 1 (by rfl) ⟨3291713, by rfl⟩ : syracuseStep 4388951 = 6583427) B6583427
theorem B1407547 : Blo 690315 1407547 := bstep (se 1 (by rfl) ⟨1055660, by rfl⟩ : syracuseStep 1407547 = 2111321) B2111321
theorem B3504707 : Blo 690315 3504707 := bstep (se 1 (by rfl) ⟨2628530, by rfl⟩ : syracuseStep 3504707 = 5257061) B5257061
theorem B25197317 : Blo 690315 25197317 := bstep (se 4 (by rfl) ⟨2362248, by rfl⟩ : syracuseStep 25197317 = 4724497) B4724497
theorem B3505031 : Blo 690315 3505031 := bstep (se 1 (by rfl) ⟨2628773, by rfl⟩ : syracuseStep 3505031 = 5257547) B5257547
theorem B10648709 : Blo 690315 10648709 := bstep (se 4 (by rfl) ⟨998316, by rfl⟩ : syracuseStep 10648709 = 1996633) B1996633
theorem B1244873 : Blo 690315 1244873 := bstep (se 2 (by rfl) ⟨466827, by rfl⟩ : syracuseStep 1244873 = 933655) B933655
theorem B1965977 : Blo 690315 1965977 := bstep (se 2 (by rfl) ⟨737241, by rfl⟩ : syracuseStep 1965977 = 1474483) B1474483
theorem B2621393 : Blo 690315 2621393 := bstep (se 2 (by rfl) ⟨983022, by rfl⟩ : syracuseStep 2621393 = 1966045) B1966045
theorem B2523251 : Blo 690315 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B1245307 : Blo 690315 1245307 := bstep (se 1 (by rfl) ⟨933980, by rfl⟩ : syracuseStep 1245307 = 1867961) B1867961
theorem B1311137 : Blo 690315 1311137 := bstep (se 2 (by rfl) ⟨491676, by rfl⟩ : syracuseStep 1311137 = 983353) B983353
theorem B1245623 : Blo 690315 1245623 := bstep (se 1 (by rfl) ⟨934217, by rfl⟩ : syracuseStep 1245623 = 1868435) B1868435
theorem B1475081 : Blo 690315 1475081 := bstep (se 2 (by rfl) ⟨553155, by rfl⟩ : syracuseStep 1475081 = 1106311) B1106311
theorem B2622091 : Blo 690315 2622091 := bstep (se 1 (by rfl) ⟨1966568, by rfl⟩ : syracuseStep 2622091 = 3933137) B3933137
theorem B1311403 : Blo 690315 1311403 := bstep (se 1 (by rfl) ⟨983552, by rfl⟩ : syracuseStep 1311403 = 1967105) B1967105
theorem B2622395 : Blo 690315 2622395 := bstep (se 1 (by rfl) ⟨1966796, by rfl⟩ : syracuseStep 2622395 = 3933593) B3933593
theorem B1311707 : Blo 690315 1311707 := bstep (se 1 (by rfl) ⟨983780, by rfl⟩ : syracuseStep 1311707 = 1967561) B1967561
theorem B5899229 : Blo 690315 5899229 := bstep (se 3 (by rfl) ⟨1106105, by rfl⟩ : syracuseStep 5899229 = 2212211) B2212211
theorem B15205427 : Blo 690315 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B1967161 : Blo 690315 1967161 := bstep (se 2 (by rfl) ⟨737685, by rfl⟩ : syracuseStep 1967161 = 1475371) B1475371
theorem B1967503 : Blo 690315 1967503 := bstep (se 1 (by rfl) ⟨1475627, by rfl⟩ : syracuseStep 1967503 = 2951255) B2951255
theorem B3737303 : Blo 690315 3737303 := bstep (se 1 (by rfl) ⟨2802977, by rfl⟩ : syracuseStep 3737303 = 5605955) B5605955
theorem B3737387 : Blo 690315 3737387 := bstep (se 1 (by rfl) ⟨2803040, by rfl⟩ : syracuseStep 3737387 = 5606081) B5606081
theorem B3376939 : Blo 690315 3376939 := bstep (se 1 (by rfl) ⟨2532704, by rfl⟩ : syracuseStep 3376939 = 5065409) B5065409
theorem B1312777 : Blo 690315 1312777 := bstep (se 2 (by rfl) ⟨492291, by rfl⟩ : syracuseStep 1312777 = 984583) B984583
theorem B3377309 : Blo 690315 3377309 := bstep (se 3 (by rfl) ⟨633245, by rfl⟩ : syracuseStep 3377309 = 1266491) B1266491
theorem B690351 : Blo 690315 690351 := bstep (se 1 (by rfl) ⟨517763, by rfl⟩ : syracuseStep 690351 = 1035527) B1035527
theorem B690375 : Blo 690315 690375 := bstep (se 1 (by rfl) ⟨517781, by rfl⟩ : syracuseStep 690375 = 1035563) B1035563
theorem B690395 : Blo 690315 690395 := bstep (se 1 (by rfl) ⟨517796, by rfl⟩ : syracuseStep 690395 = 1035593) B1035593
theorem B690471 : Blo 690315 690471 := bstep (se 1 (by rfl) ⟨517853, by rfl⟩ : syracuseStep 690471 = 1035707) B1035707
theorem B13502771 : Blo 690315 13502771 := bstep (se 1 (by rfl) ⟨10127078, by rfl⟩ : syracuseStep 13502771 = 20254157) B20254157
theorem B7899443 : Blo 690315 7899443 := bstep (se 1 (by rfl) ⟨5924582, by rfl⟩ : syracuseStep 7899443 = 11849165) B11849165
theorem B690511 : Blo 690315 690511 := bstep (se 1 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 690511 = 1035767) B1035767
theorem B690527 : Blo 690315 690527 := bstep (se 1 (by rfl) ⟨517895, by rfl⟩ : syracuseStep 690527 = 1035791) B1035791
theorem B690555 : Blo 690315 690555 := bstep (se 1 (by rfl) ⟨517916, by rfl⟩ : syracuseStep 690555 = 1035833) B1035833
theorem B690607 : Blo 690315 690607 := bstep (se 1 (by rfl) ⟨517955, by rfl⟩ : syracuseStep 690607 = 1035911) B1035911
theorem B690631 : Blo 690315 690631 := bstep (se 1 (by rfl) ⟨517973, by rfl⟩ : syracuseStep 690631 = 1035947) B1035947
theorem B690651 : Blo 690315 690651 := bstep (se 1 (by rfl) ⟨517988, by rfl⟩ : syracuseStep 690651 = 1035977) B1035977
theorem B1870361 : Blo 690315 1870361 := bstep (se 2 (by rfl) ⟨701385, by rfl⟩ : syracuseStep 1870361 = 1402771) B1402771
theorem B690727 : Blo 690315 690727 := bstep (se 1 (by rfl) ⟨518045, by rfl⟩ : syracuseStep 690727 = 1036091) B1036091
theorem B789031 : Blo 690315 789031 := bstep (se 1 (by rfl) ⟨591773, by rfl⟩ : syracuseStep 789031 = 1183547) B1183547
theorem B690767 : Blo 690315 690767 := bstep (se 1 (by rfl) ⟨518075, by rfl⟩ : syracuseStep 690767 = 1036151) B1036151
theorem B690783 : Blo 690315 690783 := bstep (se 1 (by rfl) ⟨518087, by rfl⟩ : syracuseStep 690783 = 1036175) B1036175
theorem B1477217 : Blo 690315 1477217 := bstep (se 2 (by rfl) ⟨553956, by rfl⟩ : syracuseStep 1477217 = 1107913) B1107913
theorem B690811 : Blo 690315 690811 := bstep (se 1 (by rfl) ⟨518108, by rfl⟩ : syracuseStep 690811 = 1036217) B1036217
theorem B1968779 : Blo 690315 1968779 := bstep (se 1 (by rfl) ⟨1476584, by rfl⟩ : syracuseStep 1968779 = 2953169) B2953169
theorem B690863 : Blo 690315 690863 := bstep (se 1 (by rfl) ⟨518147, by rfl⟩ : syracuseStep 690863 = 1036295) B1036295
theorem B690887 : Blo 690315 690887 := bstep (se 1 (by rfl) ⟨518165, by rfl⟩ : syracuseStep 690887 = 1036331) B1036331
theorem B1313491 : Blo 690315 1313491 := bstep (se 1 (by rfl) ⟨985118, by rfl⟩ : syracuseStep 1313491 = 1970237) B1970237
theorem B690907 : Blo 690315 690907 := bstep (se 1 (by rfl) ⟨518180, by rfl⟩ : syracuseStep 690907 = 1036361) B1036361
theorem B11995877 : Blo 690315 11995877 := bstep (se 4 (by rfl) ⟨1124613, by rfl⟩ : syracuseStep 11995877 = 2249227) B2249227
theorem B690983 : Blo 690315 690983 := bstep (se 1 (by rfl) ⟨518237, by rfl⟩ : syracuseStep 690983 = 1036475) B1036475
theorem B691023 : Blo 690315 691023 := bstep (se 1 (by rfl) ⟨518267, by rfl⟩ : syracuseStep 691023 = 1036535) B1036535
theorem B691039 : Blo 690315 691039 := bstep (se 1 (by rfl) ⟨518279, by rfl⟩ : syracuseStep 691039 = 1036559) B1036559
theorem B691067 : Blo 690315 691067 := bstep (se 1 (by rfl) ⟨518300, by rfl⟩ : syracuseStep 691067 = 1036601) B1036601
theorem B691119 : Blo 690315 691119 := bstep (se 1 (by rfl) ⟨518339, by rfl⟩ : syracuseStep 691119 = 1036679) B1036679
theorem B691143 : Blo 690315 691143 := bstep (se 1 (by rfl) ⟨518357, by rfl⟩ : syracuseStep 691143 = 1036715) B1036715
theorem B691163 : Blo 690315 691163 := bstep (se 1 (by rfl) ⟨518372, by rfl⟩ : syracuseStep 691163 = 1036745) B1036745
theorem B691239 : Blo 690315 691239 := bstep (se 1 (by rfl) ⟨518429, by rfl⟩ : syracuseStep 691239 = 1036859) B1036859
theorem B691279 : Blo 690315 691279 := bstep (se 1 (by rfl) ⟨518459, by rfl⟩ : syracuseStep 691279 = 1036919) B1036919
theorem B691295 : Blo 690315 691295 := bstep (se 1 (by rfl) ⟨518471, by rfl⟩ : syracuseStep 691295 = 1036943) B1036943
theorem B691323 : Blo 690315 691323 := bstep (se 1 (by rfl) ⟨518492, by rfl⟩ : syracuseStep 691323 = 1036985) B1036985
theorem B691375 : Blo 690315 691375 := bstep (se 1 (by rfl) ⟨518531, by rfl⟩ : syracuseStep 691375 = 1037063) B1037063
theorem B7015619 : Blo 690315 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B691399 : Blo 690315 691399 := bstep (se 1 (by rfl) ⟨518549, by rfl⟩ : syracuseStep 691399 = 1037099) B1037099
theorem B5606603 : Blo 690315 5606603 := bstep (se 1 (by rfl) ⟨4204952, by rfl⟩ : syracuseStep 5606603 = 8409905) B8409905
theorem B691419 : Blo 690315 691419 := bstep (se 1 (by rfl) ⟨518564, by rfl⟩ : syracuseStep 691419 = 1037129) B1037129
theorem B8228087 : Blo 690315 8228087 := bstep (se 1 (by rfl) ⟨6171065, by rfl⟩ : syracuseStep 8228087 = 12342131) B12342131
theorem B16026917 : Blo 690315 16026917 := bstep (se 4 (by rfl) ⟨1502523, by rfl⟩ : syracuseStep 16026917 = 3005047) B3005047
theorem B691495 : Blo 690315 691495 := bstep (se 1 (by rfl) ⟨518621, by rfl⟩ : syracuseStep 691495 = 1037243) B1037243
theorem B691535 : Blo 690315 691535 := bstep (se 1 (by rfl) ⟨518651, by rfl⟩ : syracuseStep 691535 = 1037303) B1037303
theorem B691551 : Blo 690315 691551 := bstep (se 1 (by rfl) ⟨518663, by rfl⟩ : syracuseStep 691551 = 1037327) B1037327
theorem B1183081 : Blo 690315 1183081 := bstep (se 2 (by rfl) ⟨443655, by rfl⟩ : syracuseStep 1183081 = 887311) B887311
theorem B691579 : Blo 690315 691579 := bstep (se 1 (by rfl) ⟨518684, by rfl⟩ : syracuseStep 691579 = 1037369) B1037369
theorem B3378557 : Blo 690315 3378557 := bstep (se 3 (by rfl) ⟨633479, by rfl⟩ : syracuseStep 3378557 = 1266959) B1266959
theorem B5049773 : Blo 690315 5049773 := bstep (se 3 (by rfl) ⟨946832, by rfl⟩ : syracuseStep 5049773 = 1893665) B1893665
theorem B691631 : Blo 690315 691631 := bstep (se 1 (by rfl) ⟨518723, by rfl⟩ : syracuseStep 691631 = 1037447) B1037447
theorem B1314235 : Blo 690315 1314235 := bstep (se 1 (by rfl) ⟨985676, by rfl⟩ : syracuseStep 1314235 = 1971353) B1971353
theorem B691655 : Blo 690315 691655 := bstep (se 1 (by rfl) ⟨518741, by rfl⟩ : syracuseStep 691655 = 1037483) B1037483
theorem B691675 : Blo 690315 691675 := bstep (se 1 (by rfl) ⟨518756, by rfl⟩ : syracuseStep 691675 = 1037513) B1037513
theorem B2330099 : Blo 690315 2330099 := bstep (se 1 (by rfl) ⟨1747574, by rfl⟩ : syracuseStep 2330099 = 3495149) B3495149
theorem B691751 : Blo 690315 691751 := bstep (se 1 (by rfl) ⟨518813, by rfl⟩ : syracuseStep 691751 = 1037627) B1037627
theorem B691791 : Blo 690315 691791 := bstep (se 1 (by rfl) ⟨518843, by rfl⟩ : syracuseStep 691791 = 1037687) B1037687
theorem B691807 : Blo 690315 691807 := bstep (se 1 (by rfl) ⟨518855, by rfl⟩ : syracuseStep 691807 = 1037711) B1037711
theorem B691835 : Blo 690315 691835 := bstep (se 1 (by rfl) ⟨518876, by rfl⟩ : syracuseStep 691835 = 1037753) B1037753
theorem B986747 : Blo 690315 986747 := bstep (se 1 (by rfl) ⟨740060, by rfl⟩ : syracuseStep 986747 = 1480121) B1480121
theorem B691887 : Blo 690315 691887 := bstep (se 1 (by rfl) ⟨518915, by rfl⟩ : syracuseStep 691887 = 1037831) B1037831
theorem B691911 : Blo 690315 691911 := bstep (se 1 (by rfl) ⟨518933, by rfl⟩ : syracuseStep 691911 = 1037867) B1037867
theorem B691931 : Blo 690315 691931 := bstep (se 1 (by rfl) ⟨518948, by rfl⟩ : syracuseStep 691931 = 1037897) B1037897
theorem B692007 : Blo 690315 692007 := bstep (se 1 (by rfl) ⟨519005, by rfl⟩ : syracuseStep 692007 = 1038011) B1038011
theorem B692047 : Blo 690315 692047 := bstep (se 1 (by rfl) ⟨519035, by rfl⟩ : syracuseStep 692047 = 1038071) B1038071
theorem B692063 : Blo 690315 692063 := bstep (se 1 (by rfl) ⟨519047, by rfl⟩ : syracuseStep 692063 = 1038095) B1038095
theorem B1871723 : Blo 690315 1871723 := bstep (se 1 (by rfl) ⟨1403792, by rfl⟩ : syracuseStep 1871723 = 2807585) B2807585
theorem B692091 : Blo 690315 692091 := bstep (se 1 (by rfl) ⟨519068, by rfl⟩ : syracuseStep 692091 = 1038137) B1038137
theorem B5246855 : Blo 690315 5246855 := bstep (se 1 (by rfl) ⟨3935141, by rfl⟩ : syracuseStep 5246855 = 7870283) B7870283
theorem B1314721 : Blo 690315 1314721 := bstep (se 2 (by rfl) ⟨493020, by rfl⟩ : syracuseStep 1314721 = 986041) B986041
theorem B692143 : Blo 690315 692143 := bstep (se 1 (by rfl) ⟨519107, by rfl⟩ : syracuseStep 692143 = 1038215) B1038215
theorem B1249199 : Blo 690315 1249199 := bstep (se 1 (by rfl) ⟨936899, by rfl⟩ : syracuseStep 1249199 = 1873799) B1873799
theorem B6655931 : Blo 690315 6655931 := bstep (se 1 (by rfl) ⟨4991948, by rfl⟩ : syracuseStep 6655931 = 9983897) B9983897
theorem B692167 : Blo 690315 692167 := bstep (se 1 (by rfl) ⟨519125, by rfl⟩ : syracuseStep 692167 = 1038251) B1038251
theorem B692187 : Blo 690315 692187 := bstep (se 1 (by rfl) ⟨519140, by rfl⟩ : syracuseStep 692187 = 1038281) B1038281
theorem B2330639 : Blo 690315 2330639 := bstep (se 1 (by rfl) ⟨1747979, by rfl⟩ : syracuseStep 2330639 = 3495959) B3495959
theorem B692263 : Blo 690315 692263 := bstep (se 1 (by rfl) ⟨519197, by rfl⟩ : syracuseStep 692263 = 1038395) B1038395
theorem B692303 : Blo 690315 692303 := bstep (se 1 (by rfl) ⟨519227, by rfl⟩ : syracuseStep 692303 = 1038455) B1038455
theorem B692319 : Blo 690315 692319 := bstep (se 1 (by rfl) ⟨519239, by rfl⟩ : syracuseStep 692319 = 1038479) B1038479
theorem B692347 : Blo 690315 692347 := bstep (se 1 (by rfl) ⟨519260, by rfl⟩ : syracuseStep 692347 = 1038521) B1038521
theorem B790651 : Blo 690315 790651 := bstep (se 1 (by rfl) ⟨592988, by rfl⟩ : syracuseStep 790651 = 1185977) B1185977
theorem B692399 : Blo 690315 692399 := bstep (se 1 (by rfl) ⟨519299, by rfl⟩ : syracuseStep 692399 = 1038599) B1038599
theorem B692423 : Blo 690315 692423 := bstep (se 1 (by rfl) ⟨519317, by rfl⟩ : syracuseStep 692423 = 1038635) B1038635
theorem B692443 : Blo 690315 692443 := bstep (se 1 (by rfl) ⟨519332, by rfl⟩ : syracuseStep 692443 = 1038665) B1038665
theorem B987385 : Blo 690315 987385 := bstep (se 2 (by rfl) ⟨370269, by rfl⟩ : syracuseStep 987385 = 740539) B740539
theorem B3510539 : Blo 690315 3510539 := bstep (se 1 (by rfl) ⟨2632904, by rfl⟩ : syracuseStep 3510539 = 5265809) B5265809
theorem B692519 : Blo 690315 692519 := bstep (se 1 (by rfl) ⟨519389, by rfl⟩ : syracuseStep 692519 = 1038779) B1038779
theorem B692559 : Blo 690315 692559 := bstep (se 1 (by rfl) ⟨519419, by rfl⟩ : syracuseStep 692559 = 1038839) B1038839
theorem B692575 : Blo 690315 692575 := bstep (se 1 (by rfl) ⟨519431, by rfl⟩ : syracuseStep 692575 = 1038863) B1038863
theorem B987499 : Blo 690315 987499 := bstep (se 1 (by rfl) ⟨740624, by rfl⟩ : syracuseStep 987499 = 1481249) B1481249
theorem B692603 : Blo 690315 692603 := bstep (se 1 (by rfl) ⟨519452, by rfl⟩ : syracuseStep 692603 = 1038905) B1038905
theorem B692655 : Blo 690315 692655 := bstep (se 1 (by rfl) ⟨519491, by rfl⟩ : syracuseStep 692655 = 1038983) B1038983
theorem B692679 : Blo 690315 692679 := bstep (se 1 (by rfl) ⟨519509, by rfl⟩ : syracuseStep 692679 = 1039019) B1039019
theorem B692699 : Blo 690315 692699 := bstep (se 1 (by rfl) ⟨519524, by rfl⟩ : syracuseStep 692699 = 1039049) B1039049
theorem B1315291 : Blo 690315 1315291 := bstep (se 1 (by rfl) ⟨986468, by rfl⟩ : syracuseStep 1315291 = 1972937) B1972937
theorem B692775 : Blo 690315 692775 := bstep (se 1 (by rfl) ⟨519581, by rfl⟩ : syracuseStep 692775 = 1039163) B1039163
theorem B692815 : Blo 690315 692815 := bstep (se 1 (by rfl) ⟨519611, by rfl⟩ : syracuseStep 692815 = 1039223) B1039223
theorem B987727 : Blo 690315 987727 := bstep (se 1 (by rfl) ⟨740795, by rfl⟩ : syracuseStep 987727 = 1481591) B1481591
theorem B692831 : Blo 690315 692831 := bstep (se 1 (by rfl) ⟨519623, by rfl⟩ : syracuseStep 692831 = 1039247) B1039247
theorem B2331233 : Blo 690315 2331233 := bstep (se 2 (by rfl) ⟨874212, by rfl⟩ : syracuseStep 2331233 = 1748425) B1748425
theorem B692859 : Blo 690315 692859 := bstep (se 1 (by rfl) ⟨519644, by rfl⟩ : syracuseStep 692859 = 1039289) B1039289
theorem B692911 : Blo 690315 692911 := bstep (se 1 (by rfl) ⟨519683, by rfl⟩ : syracuseStep 692911 = 1039367) B1039367
theorem B692935 : Blo 690315 692935 := bstep (se 1 (by rfl) ⟨519701, by rfl⟩ : syracuseStep 692935 = 1039403) B1039403
theorem B692955 : Blo 690315 692955 := bstep (se 1 (by rfl) ⟨519716, by rfl⟩ : syracuseStep 692955 = 1039433) B1039433
theorem B2495225 : Blo 690315 2495225 := bstep (se 2 (by rfl) ⟨935709, by rfl⟩ : syracuseStep 2495225 = 1871419) B1871419
theorem B693031 : Blo 690315 693031 := bstep (se 1 (by rfl) ⟨519773, by rfl⟩ : syracuseStep 693031 = 1039547) B1039547
theorem B693071 : Blo 690315 693071 := bstep (se 1 (by rfl) ⟨519803, by rfl⟩ : syracuseStep 693071 = 1039607) B1039607
theorem B693087 : Blo 690315 693087 := bstep (se 1 (by rfl) ⟨519815, by rfl⟩ : syracuseStep 693087 = 1039631) B1039631
theorem B693115 : Blo 690315 693115 := bstep (se 1 (by rfl) ⟨519836, by rfl⟩ : syracuseStep 693115 = 1039673) B1039673
theorem B2626465 : Blo 690315 2626465 := bstep (se 2 (by rfl) ⟨984924, by rfl⟩ : syracuseStep 2626465 = 1969849) B1969849
theorem B693167 : Blo 690315 693167 := bstep (se 1 (by rfl) ⟨519875, by rfl⟩ : syracuseStep 693167 = 1039751) B1039751
theorem B693191 : Blo 690315 693191 := bstep (se 1 (by rfl) ⟨519893, by rfl⟩ : syracuseStep 693191 = 1039787) B1039787
theorem B693211 : Blo 690315 693211 := bstep (se 1 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 693211 = 1039817) B1039817
theorem B693287 : Blo 690315 693287 := bstep (se 1 (by rfl) ⟨519965, by rfl⟩ : syracuseStep 693287 = 1039931) B1039931
theorem B693327 : Blo 690315 693327 := bstep (se 1 (by rfl) ⟨519995, by rfl⟩ : syracuseStep 693327 = 1039991) B1039991
theorem B693343 : Blo 690315 693343 := bstep (se 1 (by rfl) ⟨520007, by rfl⟩ : syracuseStep 693343 = 1040015) B1040015
theorem B693371 : Blo 690315 693371 := bstep (se 1 (by rfl) ⟨520028, by rfl⟩ : syracuseStep 693371 = 1040057) B1040057
theorem B693423 : Blo 690315 693423 := bstep (se 1 (by rfl) ⟨520067, by rfl⟩ : syracuseStep 693423 = 1040135) B1040135
theorem B693447 : Blo 690315 693447 := bstep (se 1 (by rfl) ⟨520085, by rfl⟩ : syracuseStep 693447 = 1040171) B1040171
theorem B693467 : Blo 690315 693467 := bstep (se 1 (by rfl) ⟨520100, by rfl⟩ : syracuseStep 693467 = 1040201) B1040201
theorem B693543 : Blo 690315 693543 := bstep (se 1 (by rfl) ⟨520157, by rfl⟩ : syracuseStep 693543 = 1040315) B1040315
theorem B693583 : Blo 690315 693583 := bstep (se 1 (by rfl) ⟨520187, by rfl⟩ : syracuseStep 693583 = 1040375) B1040375
theorem B693599 : Blo 690315 693599 := bstep (se 1 (by rfl) ⟨520199, by rfl⟩ : syracuseStep 693599 = 1040399) B1040399
theorem B693627 : Blo 690315 693627 := bstep (se 1 (by rfl) ⟨520220, by rfl⟩ : syracuseStep 693627 = 1040441) B1040441
theorem B1578383 : Blo 690315 1578383 := bstep (se 1 (by rfl) ⟨1183787, by rfl⟩ : syracuseStep 1578383 = 2367575) B2367575
theorem B693679 : Blo 690315 693679 := bstep (se 1 (by rfl) ⟨520259, by rfl⟩ : syracuseStep 693679 = 1040519) B1040519
theorem B693703 : Blo 690315 693703 := bstep (se 1 (by rfl) ⟨520277, by rfl⟩ : syracuseStep 693703 = 1040555) B1040555
theorem B693723 : Blo 690315 693723 := bstep (se 1 (by rfl) ⟨520292, by rfl⟩ : syracuseStep 693723 = 1040585) B1040585
theorem B693799 : Blo 690315 693799 := bstep (se 1 (by rfl) ⟨520349, by rfl⟩ : syracuseStep 693799 = 1040699) B1040699
theorem B693839 : Blo 690315 693839 := bstep (se 1 (by rfl) ⟨520379, by rfl⟩ : syracuseStep 693839 = 1040759) B1040759
theorem B693855 : Blo 690315 693855 := bstep (se 1 (by rfl) ⟨520391, by rfl⟩ : syracuseStep 693855 = 1040783) B1040783
theorem B1971809 : Blo 690315 1971809 := bstep (se 2 (by rfl) ⟨739428, by rfl⟩ : syracuseStep 1971809 = 1478857) B1478857
theorem B693883 : Blo 690315 693883 := bstep (se 1 (by rfl) ⟨520412, by rfl⟩ : syracuseStep 693883 = 1040825) B1040825
theorem B693935 : Blo 690315 693935 := bstep (se 1 (by rfl) ⟨520451, by rfl⟩ : syracuseStep 693935 = 1040903) B1040903
theorem B3511997 : Blo 690315 3511997 := bstep (se 3 (by rfl) ⟨658499, by rfl⟩ : syracuseStep 3511997 = 1316999) B1316999
theorem B693959 : Blo 690315 693959 := bstep (se 1 (by rfl) ⟨520469, by rfl⟩ : syracuseStep 693959 = 1040939) B1040939
theorem B693979 : Blo 690315 693979 := bstep (se 1 (by rfl) ⟨520484, by rfl⟩ : syracuseStep 693979 = 1040969) B1040969
theorem B694055 : Blo 690315 694055 := bstep (se 1 (by rfl) ⟨520541, by rfl⟩ : syracuseStep 694055 = 1041083) B1041083
theorem B694095 : Blo 690315 694095 := bstep (se 1 (by rfl) ⟨520571, by rfl⟩ : syracuseStep 694095 = 1041143) B1041143
theorem B2627423 : Blo 690315 2627423 := bstep (se 1 (by rfl) ⟨1970567, by rfl⟩ : syracuseStep 2627423 = 3941135) B3941135
theorem B3512159 : Blo 690315 3512159 := bstep (se 1 (by rfl) ⟨2634119, by rfl⟩ : syracuseStep 3512159 = 5268239) B5268239
theorem B694111 : Blo 690315 694111 := bstep (se 1 (by rfl) ⟨520583, by rfl⟩ : syracuseStep 694111 = 1041167) B1041167
theorem B2627437 : Blo 690315 2627437 := bstep (se 3 (by rfl) ⟨492644, by rfl⟩ : syracuseStep 2627437 = 985289) B985289
theorem B694139 : Blo 690315 694139 := bstep (se 1 (by rfl) ⟨520604, by rfl⟩ : syracuseStep 694139 = 1041209) B1041209
theorem B694191 : Blo 690315 694191 := bstep (se 1 (by rfl) ⟨520643, by rfl⟩ : syracuseStep 694191 = 1041287) B1041287
theorem B1972151 : Blo 690315 1972151 := bstep (se 1 (by rfl) ⟨1479113, by rfl⟩ : syracuseStep 1972151 = 2958227) B2958227
theorem B694215 : Blo 690315 694215 := bstep (se 1 (by rfl) ⟨520661, by rfl⟩ : syracuseStep 694215 = 1041323) B1041323
theorem B19929037 : Blo 690315 19929037 := bstep (se 3 (by rfl) ⟨3736694, by rfl⟩ : syracuseStep 19929037 = 7473389) B7473389
theorem B694235 : Blo 690315 694235 := bstep (se 1 (by rfl) ⟨520676, by rfl⟩ : syracuseStep 694235 = 1041353) B1041353
theorem B2332691 : Blo 690315 2332691 := bstep (se 1 (by rfl) ⟨1749518, by rfl⟩ : syracuseStep 2332691 = 3499037) B3499037
theorem B7477285 : Blo 690315 7477285 := bstep (se 4 (by rfl) ⟨700995, by rfl⟩ : syracuseStep 7477285 = 1401991) B1401991
theorem B694311 : Blo 690315 694311 := bstep (se 1 (by rfl) ⟨520733, by rfl⟩ : syracuseStep 694311 = 1041467) B1041467
theorem B5609587 : Blo 690315 5609587 := bstep (se 1 (by rfl) ⟨4207190, by rfl⟩ : syracuseStep 5609587 = 8414381) B8414381
theorem B2627741 : Blo 690315 2627741 := bstep (se 3 (by rfl) ⟨492701, by rfl⟩ : syracuseStep 2627741 = 985403) B985403
theorem B2333015 : Blo 690315 2333015 := bstep (se 1 (by rfl) ⟨1749761, by rfl⟩ : syracuseStep 2333015 = 3499523) B3499523
theorem B19995011 : Blo 690315 19995011 := bstep (se 1 (by rfl) ⟨14996258, by rfl⟩ : syracuseStep 19995011 = 29992517) B29992517
theorem B1317455 : Blo 690315 1317455 := bstep (se 1 (by rfl) ⟨988091, by rfl⟩ : syracuseStep 1317455 = 1976183) B1976183
theorem B2628395 : Blo 690315 2628395 := bstep (se 1 (by rfl) ⟨1971296, by rfl⟩ : syracuseStep 2628395 = 3942593) B3942593
theorem B2366327 : Blo 690315 2366327 := bstep (se 1 (by rfl) ⟨1774745, by rfl⟩ : syracuseStep 2366327 = 3549491) B3549491
theorem B1973153 : Blo 690315 1973153 := bstep (se 2 (by rfl) ⟨739932, by rfl⟩ : syracuseStep 1973153 = 1479865) B1479865
theorem B1973267 : Blo 690315 1973267 := bstep (se 1 (by rfl) ⟨1479950, by rfl⟩ : syracuseStep 1973267 = 2959901) B2959901
theorem B1973609 : Blo 690315 1973609 := bstep (se 2 (by rfl) ⟨740103, by rfl⟩ : syracuseStep 1973609 = 1480207) B1480207
theorem B2334095 : Blo 690315 2334095 := bstep (se 1 (by rfl) ⟨1750571, by rfl⟩ : syracuseStep 2334095 = 3501143) B3501143
theorem B3317395 : Blo 690315 3317395 := bstep (se 1 (by rfl) ⟨2488046, by rfl⟩ : syracuseStep 3317395 = 4976093) B4976093
theorem B2334419 : Blo 690315 2334419 := bstep (se 1 (by rfl) ⟨1750814, by rfl⟩ : syracuseStep 2334419 = 3501629) B3501629
theorem B3743597 : Blo 690315 3743597 := bstep (se 3 (by rfl) ⟨701924, by rfl⟩ : syracuseStep 3743597 = 1403849) B1403849
theorem B15966071 : Blo 690315 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B5251229 : Blo 690315 5251229 := bstep (se 3 (by rfl) ⟨984605, by rfl⟩ : syracuseStep 5251229 = 1969211) B1969211
theorem B1122665 : Blo 690315 1122665 := bstep (se 2 (by rfl) ⟨420999, by rfl⟩ : syracuseStep 1122665 = 841999) B841999
theorem B1974793 : Blo 690315 1974793 := bstep (se 2 (by rfl) ⟨740547, by rfl⟩ : syracuseStep 1974793 = 1481095) B1481095
theorem B3514913 : Blo 690315 3514913 := bstep (se 2 (by rfl) ⟨1318092, by rfl⟩ : syracuseStep 3514913 = 2636185) B2636185
theorem B2630353 : Blo 690315 2630353 := bstep (se 2 (by rfl) ⟨986382, by rfl⟩ : syracuseStep 2630353 = 1972765) B1972765
theorem B1876729 : Blo 690315 1876729 := bstep (se 2 (by rfl) ⟨703773, by rfl⟩ : syracuseStep 1876729 = 1407547) B1407547
theorem B2335607 : Blo 690315 2335607 := bstep (se 1 (by rfl) ⟨1751705, by rfl⟩ : syracuseStep 2335607 = 3503411) B3503411
theorem B4727699 : Blo 690315 4727699 := bstep (se 1 (by rfl) ⟨3545774, by rfl⟩ : syracuseStep 4727699 = 7091549) B7091549
theorem B15967151 : Blo 690315 15967151 := bstep (se 1 (by rfl) ⟨11975363, by rfl⟩ : syracuseStep 15967151 = 23950727) B23950727
theorem B2630657 : Blo 690315 2630657 := bstep (se 2 (by rfl) ⟨986496, by rfl⟩ : syracuseStep 2630657 = 1972993) B1972993
theorem B2335823 : Blo 690315 2335823 := bstep (se 1 (by rfl) ⟨1751867, by rfl⟩ : syracuseStep 2335823 = 3503735) B3503735
theorem B1123691 : Blo 690315 1123691 := bstep (se 1 (by rfl) ⟨842768, by rfl⟩ : syracuseStep 1123691 = 1685537) B1685537
theorem B1975681 : Blo 690315 1975681 := bstep (se 2 (by rfl) ⟨740880, by rfl⟩ : syracuseStep 1975681 = 1481761) B1481761
theorem B2925967 : Blo 690315 2925967 := bstep (se 1 (by rfl) ⟨2194475, by rfl⟩ : syracuseStep 2925967 = 4388951) B4388951
theorem B2336201 : Blo 690315 2336201 := bstep (se 2 (by rfl) ⟨876075, by rfl⟩ : syracuseStep 2336201 = 1752151) B1752151
theorem B2631113 : Blo 690315 2631113 := bstep (se 2 (by rfl) ⟨986667, by rfl⟩ : syracuseStep 2631113 = 1973335) B1973335
theorem B2336471 : Blo 690315 2336471 := bstep (se 1 (by rfl) ⟨1752353, by rfl⟩ : syracuseStep 2336471 = 3504707) B3504707
theorem B13510489 : Blo 690315 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B3319661 : Blo 690315 3319661 := bstep (se 3 (by rfl) ⟨622436, by rfl⟩ : syracuseStep 3319661 = 1244873) B1244873
theorem B4990855 : Blo 690315 4990855 := bstep (se 1 (by rfl) ⟨3743141, by rfl⟩ : syracuseStep 4990855 = 7486283) B7486283
theorem B2336687 : Blo 690315 2336687 := bstep (se 1 (by rfl) ⟨1752515, by rfl⟩ : syracuseStep 2336687 = 3505031) B3505031
theorem B2631599 : Blo 690315 2631599 := bstep (se 1 (by rfl) ⟨1973699, by rfl⟩ : syracuseStep 2631599 = 3947399) B3947399
theorem B1976251 : Blo 690315 1976251 := bstep (se 1 (by rfl) ⟨1482188, by rfl⟩ : syracuseStep 1976251 = 2964377) B2964377
theorem B6662081 : Blo 690315 6662081 := bstep (se 2 (by rfl) ⟨2498280, by rfl⟩ : syracuseStep 6662081 = 4996561) B4996561
theorem B2369803 : Blo 690315 2369803 := bstep (se 1 (by rfl) ⟨1777352, by rfl⟩ : syracuseStep 2369803 = 3554705) B3554705
theorem B9447785 : Blo 690315 9447785 := bstep (se 2 (by rfl) ⟨3542919, by rfl⟩ : syracuseStep 9447785 = 7085839) B7085839
theorem B1747595 : Blo 690315 1747595 := bstep (se 1 (by rfl) ⟨1310696, by rfl⟩ : syracuseStep 1747595 = 2621393) B2621393
theorem B6663005 : Blo 690315 6663005 := bstep (se 3 (by rfl) ⟨1249313, by rfl⟩ : syracuseStep 6663005 = 2498627) B2498627
theorem B3943343 : Blo 690315 3943343 := bstep (se 1 (by rfl) ⟨2957507, by rfl⟩ : syracuseStep 3943343 = 5915015) B5915015
theorem B5254145 : Blo 690315 5254145 := bstep (se 2 (by rfl) ⟨1970304, by rfl⟩ : syracuseStep 5254145 = 3940609) B3940609
theorem B2632783 : Blo 690315 2632783 := bstep (se 1 (by rfl) ⟨1974587, by rfl⟩ : syracuseStep 2632783 = 3949175) B3949175
theorem B2502089 : Blo 690315 2502089 := bstep (se 2 (by rfl) ⟨938283, by rfl⟩ : syracuseStep 2502089 = 1876567) B1876567
theorem B2633255 : Blo 690315 2633255 := bstep (se 1 (by rfl) ⟨1974941, by rfl⟩ : syracuseStep 2633255 = 3949883) B3949883
theorem B1748729 : Blo 690315 1748729 := bstep (se 2 (by rfl) ⟨655773, by rfl⟩ : syracuseStep 1748729 = 1311547) B1311547
theorem B3321643 : Blo 690315 3321643 := bstep (se 1 (by rfl) ⟨2491232, by rfl⟩ : syracuseStep 3321643 = 4982465) B4982465
theorem B1748911 : Blo 690315 1748911 := bstep (se 1 (by rfl) ⟨1311683, by rfl⟩ : syracuseStep 1748911 = 2623367) B2623367
theorem B2666611 : Blo 690315 2666611 := bstep (se 1 (by rfl) ⟨1999958, by rfl⟩ : syracuseStep 2666611 = 3999917) B3999917
theorem B2339063 : Blo 690315 2339063 := bstep (se 1 (by rfl) ⟨1754297, by rfl⟩ : syracuseStep 2339063 = 3508595) B3508595
theorem B4993331 : Blo 690315 4993331 := bstep (se 1 (by rfl) ⟨3744998, by rfl⟩ : syracuseStep 4993331 = 7489997) B7489997
theorem B1749377 : Blo 690315 1749377 := bstep (se 2 (by rfl) ⟨656016, by rfl⟩ : syracuseStep 1749377 = 1312033) B1312033
theorem B2634227 : Blo 690315 2634227 := bstep (se 1 (by rfl) ⟨1975670, by rfl⟩ : syracuseStep 2634227 = 3951341) B3951341
theorem B2339387 : Blo 690315 2339387 := bstep (se 1 (by rfl) ⟨1754540, by rfl⟩ : syracuseStep 2339387 = 3509081) B3509081
theorem B1749833 : Blo 690315 1749833 := bstep (se 2 (by rfl) ⟨656187, by rfl⟩ : syracuseStep 1749833 = 1312375) B1312375
theorem B2339657 : Blo 690315 2339657 := bstep (se 2 (by rfl) ⟨877371, by rfl⟩ : syracuseStep 2339657 = 1754743) B1754743
theorem B701279 : Blo 690315 701279 := bstep (se 1 (by rfl) ⟨525959, by rfl⟩ : syracuseStep 701279 = 1051919) B1051919
theorem B1553327 : Blo 690315 1553327 := bstep (se 1 (by rfl) ⟨1164995, by rfl⟩ : syracuseStep 1553327 = 2329991) B2329991
theorem B1553579 : Blo 690315 1553579 := bstep (se 1 (by rfl) ⟨1165184, by rfl⟩ : syracuseStep 1553579 = 2330369) B2330369
theorem B1750187 : Blo 690315 1750187 := bstep (se 1 (by rfl) ⟨1312640, by rfl⟩ : syracuseStep 1750187 = 2625281) B2625281
theorem B1554119 : Blo 690315 1554119 := bstep (se 1 (by rfl) ⟨1165589, by rfl⟩ : syracuseStep 1554119 = 2331179) B2331179
theorem B1750967 : Blo 690315 1750967 := bstep (se 1 (by rfl) ⟨1313225, by rfl⟩ : syracuseStep 1750967 = 2626451) B2626451
theorem B2340791 : Blo 690315 2340791 := bstep (se 1 (by rfl) ⟨1755593, by rfl⟩ : syracuseStep 2340791 = 3511187) B3511187
theorem B11220929 : Blo 690315 11220929 := bstep (se 2 (by rfl) ⟨4207848, by rfl⟩ : syracuseStep 11220929 = 8415697) B8415697
theorem B6010969 : Blo 690315 6010969 := bstep (se 2 (by rfl) ⟨2254113, by rfl⟩ : syracuseStep 6010969 = 4508227) B4508227
theorem B8894771 : Blo 690315 8894771 := bstep (se 1 (by rfl) ⟨6671078, by rfl⟩ : syracuseStep 8894771 = 13342157) B13342157
theorem B2341385 : Blo 690315 2341385 := bstep (se 2 (by rfl) ⟨878019, by rfl⟩ : syracuseStep 2341385 = 1756039) B1756039
theorem B1554983 : Blo 690315 1554983 := bstep (se 1 (by rfl) ⟨1166237, by rfl⟩ : syracuseStep 1554983 = 2332475) B2332475
theorem B2800187 : Blo 690315 2800187 := bstep (se 1 (by rfl) ⟨2100140, by rfl⟩ : syracuseStep 2800187 = 4200281) B4200281
theorem B2407241 : Blo 690315 2407241 := bstep (se 2 (by rfl) ⟨902715, by rfl⟩ : syracuseStep 2407241 = 1805431) B1805431
theorem B1555307 : Blo 690315 1555307 := bstep (se 1 (by rfl) ⟨1166480, by rfl⟩ : syracuseStep 1555307 = 2332961) B2332961
theorem B3160939 : Blo 690315 3160939 := bstep (se 1 (by rfl) ⟨2370704, by rfl⟩ : syracuseStep 3160939 = 4741409) B4741409
theorem B703355 : Blo 690315 703355 := bstep (se 1 (by rfl) ⟨527516, by rfl⟩ : syracuseStep 703355 = 1055033) B1055033
theorem B1555361 : Blo 690315 1555361 := bstep (se 2 (by rfl) ⟨583260, by rfl⟩ : syracuseStep 1555361 = 1166521) B1166521
theorem B1751969 : Blo 690315 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B1555703 : Blo 690315 1555703 := bstep (se 1 (by rfl) ⟨1166777, by rfl⟩ : syracuseStep 1555703 = 2333555) B2333555
theorem B5258519 : Blo 690315 5258519 := bstep (se 1 (by rfl) ⟨3943889, by rfl⟩ : syracuseStep 5258519 = 7887779) B7887779
theorem B1752425 : Blo 690315 1752425 := bstep (se 2 (by rfl) ⟨657159, by rfl⟩ : syracuseStep 1752425 = 1314319) B1314319
theorem B2342249 : Blo 690315 2342249 := bstep (se 2 (by rfl) ⟨878343, by rfl⟩ : syracuseStep 2342249 = 1756687) B1756687
theorem B8437537 : Blo 690315 8437537 := bstep (se 2 (by rfl) ⟨3164076, by rfl⟩ : syracuseStep 8437537 = 6328153) B6328153
theorem B1556297 : Blo 690315 1556297 := bstep (se 2 (by rfl) ⟨583611, by rfl⟩ : syracuseStep 1556297 = 1167223) B1167223
theorem B2342843 : Blo 690315 2342843 := bstep (se 1 (by rfl) ⟨1757132, by rfl⟩ : syracuseStep 2342843 = 3514265) B3514265
theorem B5980175 : Blo 690315 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B3325967 : Blo 690315 3325967 := bstep (se 1 (by rfl) ⟨2494475, by rfl⟩ : syracuseStep 3325967 = 4988951) B4988951
theorem B1753609 : Blo 690315 1753609 := bstep (se 2 (by rfl) ⟨657603, by rfl⟩ : syracuseStep 1753609 = 1315207) B1315207
theorem B1557089 : Blo 690315 1557089 := bstep (se 2 (by rfl) ⟨583908, by rfl⟩ : syracuseStep 1557089 = 1167817) B1167817
theorem B5259977 : Blo 690315 5259977 := bstep (se 2 (by rfl) ⟨1972491, by rfl⟩ : syracuseStep 5259977 = 3944983) B3944983
theorem B4440977 : Blo 690315 4440977 := bstep (se 2 (by rfl) ⟨1665366, by rfl⟩ : syracuseStep 4440977 = 3330733) B3330733
theorem B1557431 : Blo 690315 1557431 := bstep (se 1 (by rfl) ⟨1168073, by rfl⟩ : syracuseStep 1557431 = 2336147) B2336147
theorem B5915699 : Blo 690315 5915699 := bstep (se 1 (by rfl) ⟨4436774, by rfl⟩ : syracuseStep 5915699 = 8873549) B8873549
theorem B1197227 : Blo 690315 1197227 := bstep (se 1 (by rfl) ⟨897920, by rfl⟩ : syracuseStep 1197227 = 1795841) B1795841
theorem B738779 : Blo 690315 738779 := bstep (se 1 (by rfl) ⟨554084, by rfl⟩ : syracuseStep 738779 = 1108169) B1108169
theorem B1558025 : Blo 690315 1558025 := bstep (se 2 (by rfl) ⟨584259, by rfl⟩ : syracuseStep 1558025 = 1168519) B1168519
theorem B1263161 : Blo 690315 1263161 := bstep (se 2 (by rfl) ⟨473685, by rfl⟩ : syracuseStep 1263161 = 947371) B947371
theorem B1165151 : Blo 690315 1165151 := bstep (se 1 (by rfl) ⟨873863, by rfl⟩ : syracuseStep 1165151 = 1747727) B1747727
theorem B1558367 : Blo 690315 1558367 := bstep (se 1 (by rfl) ⟨1168775, by rfl⟩ : syracuseStep 1558367 = 2337551) B2337551
theorem B1755067 : Blo 690315 1755067 := bstep (se 1 (by rfl) ⟨1316300, by rfl⟩ : syracuseStep 1755067 = 2632601) B2632601
theorem B1558547 : Blo 690315 1558547 := bstep (se 1 (by rfl) ⟨1168910, by rfl⟩ : syracuseStep 1558547 = 2337821) B2337821
theorem B1558889 : Blo 690315 1558889 := bstep (se 2 (by rfl) ⟨584583, by rfl⟩ : syracuseStep 1558889 = 1169167) B1169167
theorem B1165711 : Blo 690315 1165711 := bstep (se 1 (by rfl) ⟨874283, by rfl⟩ : syracuseStep 1165711 = 1748567) B1748567
theorem B2214287 : Blo 690315 2214287 := bstep (se 1 (by rfl) ⟨1660715, by rfl⟩ : syracuseStep 2214287 = 3321431) B3321431
theorem B2837207 : Blo 690315 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B2214839 : Blo 690315 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B1559483 : Blo 690315 1559483 := bstep (se 1 (by rfl) ⟨1169612, by rfl⟩ : syracuseStep 1559483 = 2339225) B2339225
theorem B1166393 : Blo 690315 1166393 := bstep (se 2 (by rfl) ⟨437397, by rfl⟩ : syracuseStep 1166393 = 874795) B874795
theorem B1559609 : Blo 690315 1559609 := bstep (se 2 (by rfl) ⟨584853, by rfl⟩ : syracuseStep 1559609 = 1169707) B1169707
theorem B90917963 : Blo 690315 90917963 := bstep (se 1 (by rfl) ⟨68188472, by rfl⟩ : syracuseStep 90917963 = 136376945) B136376945
theorem B1559951 : Blo 690315 1559951 := bstep (se 1 (by rfl) ⟨1169963, by rfl⟩ : syracuseStep 1559951 = 2339927) B2339927
theorem B1035695 : Blo 690315 1035695 := bstep (se 1 (by rfl) ⟨776771, by rfl⟩ : syracuseStep 1035695 = 1553543) B1553543
theorem B1330651 : Blo 690315 1330651 := bstep (se 1 (by rfl) ⟨997988, by rfl⟩ : syracuseStep 1330651 = 1995977) B1995977
theorem B3952091 : Blo 690315 3952091 := bstep (se 1 (by rfl) ⟨2964068, by rfl⟩ : syracuseStep 3952091 = 5928137) B5928137
theorem B1035785 : Blo 690315 1035785 := bstep (se 2 (by rfl) ⟨388419, by rfl⟩ : syracuseStep 1035785 = 776839) B776839
theorem B1035815 : Blo 690315 1035815 := bstep (se 1 (by rfl) ⟨776861, by rfl⟩ : syracuseStep 1035815 = 1553723) B1553723
theorem B11226691 : Blo 690315 11226691 := bstep (se 1 (by rfl) ⟨8420018, by rfl⟩ : syracuseStep 11226691 = 16840037) B16840037
theorem B1035899 : Blo 690315 1035899 := bstep (se 1 (by rfl) ⟨776924, by rfl⟩ : syracuseStep 1035899 = 1553849) B1553849
theorem B3952273 : Blo 690315 3952273 := bstep (se 2 (by rfl) ⟨1482102, by rfl⟩ : syracuseStep 3952273 = 2964205) B2964205
theorem B21286577 : Blo 690315 21286577 := bstep (se 2 (by rfl) ⟨7982466, by rfl⟩ : syracuseStep 21286577 = 15964933) B15964933
theorem B1560275 : Blo 690315 1560275 := bstep (se 1 (by rfl) ⟨1170206, by rfl⟩ : syracuseStep 1560275 = 2340413) B2340413
theorem B1167095 : Blo 690315 1167095 := bstep (se 1 (by rfl) ⟨875321, by rfl⟩ : syracuseStep 1167095 = 1750643) B1750643
theorem B1036025 : Blo 690315 1036025 := bstep (se 2 (by rfl) ⟨388509, by rfl⟩ : syracuseStep 1036025 = 777019) B777019
theorem B1036127 : Blo 690315 1036127 := bstep (se 1 (by rfl) ⟨777095, by rfl⟩ : syracuseStep 1036127 = 1554191) B1554191
theorem B1036139 : Blo 690315 1036139 := bstep (se 1 (by rfl) ⟨777104, by rfl⟩ : syracuseStep 1036139 = 1554209) B1554209
theorem B1036367 : Blo 690315 1036367 := bstep (se 1 (by rfl) ⟨777275, by rfl⟩ : syracuseStep 1036367 = 1554551) B1554551
theorem B1167439 : Blo 690315 1167439 := bstep (se 1 (by rfl) ⟨875579, by rfl⟩ : syracuseStep 1167439 = 1751159) B1751159
theorem B1036487 : Blo 690315 1036487 := bstep (se 1 (by rfl) ⟨777365, by rfl⟩ : syracuseStep 1036487 = 1554731) B1554731
theorem B1167689 : Blo 690315 1167689 := bstep (se 2 (by rfl) ⟨437883, by rfl⟩ : syracuseStep 1167689 = 875767) B875767
theorem B1036649 : Blo 690315 1036649 := bstep (se 2 (by rfl) ⟨388743, by rfl⟩ : syracuseStep 1036649 = 777487) B777487
theorem B1036727 : Blo 690315 1036727 := bstep (se 1 (by rfl) ⟨777545, by rfl⟩ : syracuseStep 1036727 = 1555091) B1555091
theorem B1036763 : Blo 690315 1036763 := bstep (se 1 (by rfl) ⟨777572, by rfl⟩ : syracuseStep 1036763 = 1555145) B1555145
theorem B16798211 : Blo 690315 16798211 := bstep (se 1 (by rfl) ⟨12598658, by rfl⟩ : syracuseStep 16798211 = 25197317) B25197317
theorem B1495675 : Blo 690315 1495675 := bstep (se 1 (by rfl) ⟨1121756, by rfl⟩ : syracuseStep 1495675 = 2243513) B2243513
theorem B1561211 : Blo 690315 1561211 := bstep (se 1 (by rfl) ⟨1170908, by rfl⟩ : syracuseStep 1561211 = 2341817) B2341817
theorem B1168121 : Blo 690315 1168121 := bstep (se 2 (by rfl) ⟨438045, by rfl⟩ : syracuseStep 1168121 = 876091) B876091
theorem B1561337 : Blo 690315 1561337 := bstep (se 2 (by rfl) ⟨585501, by rfl⟩ : syracuseStep 1561337 = 1171003) B1171003
theorem B7099139 : Blo 690315 7099139 := bstep (se 1 (by rfl) ⟨5324354, by rfl⟩ : syracuseStep 7099139 = 10648709) B10648709
theorem B2216747 : Blo 690315 2216747 := bstep (se 1 (by rfl) ⟨1662560, by rfl⟩ : syracuseStep 2216747 = 3325121) B3325121
theorem B1037231 : Blo 690315 1037231 := bstep (se 1 (by rfl) ⟨777923, by rfl⟩ : syracuseStep 1037231 = 1555847) B1555847
theorem B1168303 : Blo 690315 1168303 := bstep (se 1 (by rfl) ⟨876227, by rfl⟩ : syracuseStep 1168303 = 1752455) B1752455
theorem B1168391 : Blo 690315 1168391 := bstep (se 1 (by rfl) ⟨876293, by rfl⟩ : syracuseStep 1168391 = 1752587) B1752587
theorem B1561607 : Blo 690315 1561607 := bstep (se 1 (by rfl) ⟨1171205, by rfl⟩ : syracuseStep 1561607 = 2342411) B2342411
theorem B1037321 : Blo 690315 1037321 := bstep (se 2 (by rfl) ⟨388995, by rfl⟩ : syracuseStep 1037321 = 777991) B777991
theorem B1037351 : Blo 690315 1037351 := bstep (se 1 (by rfl) ⟨778013, by rfl⟩ : syracuseStep 1037351 = 1556027) B1556027
theorem B1561679 : Blo 690315 1561679 := bstep (se 1 (by rfl) ⟨1171259, by rfl⟩ : syracuseStep 1561679 = 2342519) B2342519
theorem B1037435 : Blo 690315 1037435 := bstep (se 1 (by rfl) ⟨778076, by rfl⟩ : syracuseStep 1037435 = 1556153) B1556153
theorem B4445387 : Blo 690315 4445387 := bstep (se 1 (by rfl) ⟨3334040, by rfl⟩ : syracuseStep 4445387 = 6668081) B6668081
theorem B1037561 : Blo 690315 1037561 := bstep (se 2 (by rfl) ⟨389085, by rfl⟩ : syracuseStep 1037561 = 778171) B778171
theorem B873823 : Blo 690315 873823 := bstep (se 1 (by rfl) ⟨655367, by rfl⟩ : syracuseStep 873823 = 1310735) B1310735
theorem B1037663 : Blo 690315 1037663 := bstep (se 1 (by rfl) ⟨778247, by rfl⟩ : syracuseStep 1037663 = 1556495) B1556495
theorem B1168735 : Blo 690315 1168735 := bstep (se 1 (by rfl) ⟨876551, by rfl⟩ : syracuseStep 1168735 = 1753103) B1753103
theorem B1037675 : Blo 690315 1037675 := bstep (se 1 (by rfl) ⟨778256, by rfl⟩ : syracuseStep 1037675 = 1556513) B1556513
theorem B3495311 : Blo 690315 3495311 := bstep (se 1 (by rfl) ⟨2621483, by rfl⟩ : syracuseStep 3495311 = 5242967) B5242967
theorem B1168823 : Blo 690315 1168823 := bstep (se 1 (by rfl) ⟨876617, by rfl⟩ : syracuseStep 1168823 = 1753235) B1753235
theorem B1562075 : Blo 690315 1562075 := bstep (se 1 (by rfl) ⟨1171556, by rfl⟩ : syracuseStep 1562075 = 2343113) B2343113
theorem B1037903 : Blo 690315 1037903 := bstep (se 1 (by rfl) ⟨778427, by rfl⟩ : syracuseStep 1037903 = 1556855) B1556855
theorem B16864949 : Blo 690315 16864949 := bstep (se 5 (by rfl) ⟨790544, by rfl⟩ : syracuseStep 16864949 = 1581089) B1581089
theorem B1038023 : Blo 690315 1038023 := bstep (se 1 (by rfl) ⟨778517, by rfl⟩ : syracuseStep 1038023 = 1557035) B1557035
theorem B2217721 : Blo 690315 2217721 := bstep (se 2 (by rfl) ⟨831645, by rfl⟩ : syracuseStep 2217721 = 1663291) B1663291
theorem B1038185 : Blo 690315 1038185 := bstep (se 2 (by rfl) ⟨389319, by rfl⟩ : syracuseStep 1038185 = 778639) B778639
theorem B874415 : Blo 690315 874415 := bstep (se 1 (by rfl) ⟨655811, by rfl⟩ : syracuseStep 874415 = 1311623) B1311623
theorem B1038263 : Blo 690315 1038263 := bstep (se 1 (by rfl) ⟨778697, by rfl⟩ : syracuseStep 1038263 = 1557395) B1557395
theorem B1038299 : Blo 690315 1038299 := bstep (se 1 (by rfl) ⟨778724, by rfl⟩ : syracuseStep 1038299 = 1557449) B1557449
theorem B1169417 : Blo 690315 1169417 := bstep (se 2 (by rfl) ⟨438531, by rfl⟩ : syracuseStep 1169417 = 877063) B877063
theorem B1169579 : Blo 690315 1169579 := bstep (se 1 (by rfl) ⟨877184, by rfl⟩ : syracuseStep 1169579 = 1754369) B1754369
theorem B776623 : Blo 690315 776623 := bstep (se 1 (by rfl) ⟨582467, by rfl⟩ : syracuseStep 776623 = 1164935) B1164935
theorem B1038767 : Blo 690315 1038767 := bstep (se 1 (by rfl) ⟨779075, by rfl⟩ : syracuseStep 1038767 = 1558151) B1558151
theorem B1038857 : Blo 690315 1038857 := bstep (se 2 (by rfl) ⟨389571, by rfl⟩ : syracuseStep 1038857 = 779143) B779143
theorem B2218529 : Blo 690315 2218529 := bstep (se 2 (by rfl) ⟨831948, by rfl⟩ : syracuseStep 2218529 = 1663897) B1663897
theorem B1038887 : Blo 690315 1038887 := bstep (se 1 (by rfl) ⟨779165, by rfl⟩ : syracuseStep 1038887 = 1558331) B1558331
theorem B1169977 : Blo 690315 1169977 := bstep (se 2 (by rfl) ⟨438741, by rfl⟩ : syracuseStep 1169977 = 877483) B877483
theorem B1038971 : Blo 690315 1038971 := bstep (se 1 (by rfl) ⟨779228, by rfl⟩ : syracuseStep 1038971 = 1558457) B1558457
theorem B1170119 : Blo 690315 1170119 := bstep (se 1 (by rfl) ⟨877589, by rfl⟩ : syracuseStep 1170119 = 1755179) B1755179
theorem B1039097 : Blo 690315 1039097 := bstep (se 2 (by rfl) ⟨389661, by rfl⟩ : syracuseStep 1039097 = 779323) B779323
theorem B777055 : Blo 690315 777055 := bstep (se 1 (by rfl) ⟨582791, by rfl⟩ : syracuseStep 777055 = 1165583) B1165583
theorem B1039199 : Blo 690315 1039199 := bstep (se 1 (by rfl) ⟨779399, by rfl⟩ : syracuseStep 1039199 = 1558799) B1558799
theorem B1170281 : Blo 690315 1170281 := bstep (se 2 (by rfl) ⟨438855, by rfl⟩ : syracuseStep 1170281 = 877711) B877711
theorem B1039211 : Blo 690315 1039211 := bstep (se 1 (by rfl) ⟨779408, by rfl⟩ : syracuseStep 1039211 = 1558817) B1558817
theorem B2808685 : Blo 690315 2808685 := bstep (se 3 (by rfl) ⟨526628, by rfl⟩ : syracuseStep 2808685 = 1053257) B1053257
theorem B1334291 : Blo 690315 1334291 := bstep (se 1 (by rfl) ⟨1000718, by rfl⟩ : syracuseStep 1334291 = 2001437) B2001437
theorem B1039439 : Blo 690315 1039439 := bstep (se 1 (by rfl) ⟨779579, by rfl⟩ : syracuseStep 1039439 = 1559159) B1559159
theorem B777415 : Blo 690315 777415 := bstep (se 1 (by rfl) ⟨583061, by rfl⟩ : syracuseStep 777415 = 1166123) B1166123
theorem B1039559 : Blo 690315 1039559 := bstep (se 1 (by rfl) ⟨779669, by rfl⟩ : syracuseStep 1039559 = 1559339) B1559339
theorem B1170679 : Blo 690315 1170679 := bstep (se 1 (by rfl) ⟨878009, by rfl⟩ : syracuseStep 1170679 = 1756019) B1756019
theorem B1039721 : Blo 690315 1039721 := bstep (se 2 (by rfl) ⟨389895, by rfl⟩ : syracuseStep 1039721 = 779791) B779791
theorem B1039799 : Blo 690315 1039799 := bstep (se 1 (by rfl) ⟨779849, by rfl⟩ : syracuseStep 1039799 = 1559699) B1559699
theorem B1170875 : Blo 690315 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B3497417 : Blo 690315 3497417 := bstep (se 2 (by rfl) ⟨1311531, by rfl⟩ : syracuseStep 3497417 = 2623063) B2623063
theorem B1039835 : Blo 690315 1039835 := bstep (se 1 (by rfl) ⟨779876, by rfl⟩ : syracuseStep 1039835 = 1559753) B1559753
theorem B1170983 : Blo 690315 1170983 := bstep (se 1 (by rfl) ⟨878237, by rfl⟩ : syracuseStep 1170983 = 1756475) B1756475
theorem B2809529 : Blo 690315 2809529 := bstep (se 2 (by rfl) ⟨1053573, by rfl⟩ : syracuseStep 2809529 = 2107147) B2107147
theorem B5267267 : Blo 690315 5267267 := bstep (se 1 (by rfl) ⟨3950450, by rfl⟩ : syracuseStep 5267267 = 7900901) B7900901
theorem B1171273 : Blo 690315 1171273 := bstep (se 2 (by rfl) ⟨439227, by rfl⟩ : syracuseStep 1171273 = 878455) B878455
theorem B1171307 : Blo 690315 1171307 := bstep (se 1 (by rfl) ⟨878480, by rfl⟩ : syracuseStep 1171307 = 1756961) B1756961
theorem B1040303 : Blo 690315 1040303 := bstep (se 1 (by rfl) ⟨780227, by rfl⟩ : syracuseStep 1040303 = 1560455) B1560455
theorem B2809787 : Blo 690315 2809787 := bstep (se 1 (by rfl) ⟨2107340, by rfl⟩ : syracuseStep 2809787 = 4214681) B4214681
theorem B1040393 : Blo 690315 1040393 := bstep (se 2 (by rfl) ⟨390147, by rfl⟩ : syracuseStep 1040393 = 780295) B780295
theorem B778279 : Blo 690315 778279 := bstep (se 1 (by rfl) ⟨583709, by rfl⟩ : syracuseStep 778279 = 1167419) B1167419
theorem B1040423 : Blo 690315 1040423 := bstep (se 1 (by rfl) ⟨780317, by rfl⟩ : syracuseStep 1040423 = 1560635) B1560635
theorem B3498065 : Blo 690315 3498065 := bstep (se 2 (by rfl) ⟨1311774, by rfl⟩ : syracuseStep 3498065 = 2623549) B2623549
theorem B1040507 : Blo 690315 1040507 := bstep (se 1 (by rfl) ⟨780380, by rfl⟩ : syracuseStep 1040507 = 1560761) B1560761
theorem B1040633 : Blo 690315 1040633 := bstep (se 2 (by rfl) ⟨390237, by rfl⟩ : syracuseStep 1040633 = 780475) B780475
theorem B1040735 : Blo 690315 1040735 := bstep (se 1 (by rfl) ⟨780551, by rfl⟩ : syracuseStep 1040735 = 1561103) B1561103
theorem B1040747 : Blo 690315 1040747 := bstep (se 1 (by rfl) ⟨780560, by rfl⟩ : syracuseStep 1040747 = 1561121) B1561121
theorem B1335739 : Blo 690315 1335739 := bstep (se 1 (by rfl) ⟨1001804, by rfl⟩ : syracuseStep 1335739 = 2003609) B2003609
theorem B1040975 : Blo 690315 1040975 := bstep (se 1 (by rfl) ⟨780731, by rfl⟩ : syracuseStep 1040975 = 1561463) B1561463
theorem B1041095 : Blo 690315 1041095 := bstep (se 1 (by rfl) ⟨780821, by rfl⟩ : syracuseStep 1041095 = 1561643) B1561643
theorem B1041257 : Blo 690315 1041257 := bstep (se 2 (by rfl) ⟨390471, by rfl⟩ : syracuseStep 1041257 = 780943) B780943
theorem B1041335 : Blo 690315 1041335 := bstep (se 1 (by rfl) ⟨781001, by rfl⟩ : syracuseStep 1041335 = 1562003) B1562003
theorem B1106875 : Blo 690315 1106875 := bstep (se 1 (by rfl) ⟨830156, by rfl⟩ : syracuseStep 1106875 = 1660313) B1660313
theorem B1041371 : Blo 690315 1041371 := bstep (se 1 (by rfl) ⟨781028, by rfl⟩ : syracuseStep 1041371 = 1562057) B1562057
theorem B1402105 : Blo 690315 1402105 := bstep (se 2 (by rfl) ⟨525789, by rfl⟩ : syracuseStep 1402105 = 1051579) B1051579
theorem B779899 : Blo 690315 779899 := bstep (se 1 (by rfl) ⟨584924, by rfl⟩ : syracuseStep 779899 = 1169849) B1169849
theorem B780367 : Blo 690315 780367 := bstep (se 1 (by rfl) ⟨585275, by rfl⟩ : syracuseStep 780367 = 1170551) B1170551
theorem B780763 : Blo 690315 780763 := bstep (se 1 (by rfl) ⟨585572, by rfl⟩ : syracuseStep 780763 = 1171145) B1171145
theorem B6319397 : Blo 690315 6319397 := bstep (se 4 (by rfl) ⟨592443, by rfl⟩ : syracuseStep 6319397 = 1184887) B1184887
theorem B19951181 : Blo 690315 19951181 := bstep (se 3 (by rfl) ⟨3740846, by rfl⟩ : syracuseStep 19951181 = 7481693) B7481693
theorem B1109675 : Blo 690315 1109675 := bstep (se 1 (by rfl) ⟨832256, by rfl⟩ : syracuseStep 1109675 = 1664513) B1664513
theorem B8548129 : Blo 690315 8548129 := bstep (se 2 (by rfl) ⟨3205548, by rfl⟩ : syracuseStep 8548129 = 6411097) B6411097
theorem B13463567 : Blo 690315 13463567 := bstep (se 1 (by rfl) ⟨10097675, by rfl⟩ : syracuseStep 13463567 = 20195351) B20195351
theorem B5271641 : Blo 690315 5271641 := bstep (se 2 (by rfl) ⟨1976865, by rfl⟩ : syracuseStep 5271641 = 3953731) B3953731
theorem B22475069 : Blo 690315 22475069 := bstep (se 3 (by rfl) ⟨4214075, by rfl⟩ : syracuseStep 22475069 = 8428151) B8428151
theorem B3502601 : Blo 690315 3502601 := bstep (se 2 (by rfl) ⟨1313475, by rfl⟩ : syracuseStep 3502601 = 2626951) B2626951
theorem B10777519 : Blo 690315 10777519 := bstep (se 1 (by rfl) ⟨8083139, by rfl⟩ : syracuseStep 10777519 = 16166279) B16166279
theorem B2814977 : Blo 690315 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B1406663 : Blo 690315 1406663 := bstep (se 1 (by rfl) ⟨1054997, by rfl⟩ : syracuseStep 1406663 = 2109995) B2109995
theorem B3504059 : Blo 690315 3504059 := bstep (se 1 (by rfl) ⟨2628044, by rfl⟩ : syracuseStep 3504059 = 5256089) B5256089
theorem B8976541 : Blo 690315 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B4750255 : Blo 690315 4750255 := bstep (se 1 (by rfl) ⟨3562691, by rfl⟩ : syracuseStep 4750255 = 7125383) B7125383
theorem B4488119 : Blo 690315 4488119 := bstep (se 1 (by rfl) ⟨3366089, by rfl⟩ : syracuseStep 4488119 = 6732179) B6732179
theorem B3505355 : Blo 690315 3505355 := bstep (se 1 (by rfl) ⟨2629016, by rfl⟩ : syracuseStep 3505355 = 5258033) B5258033
theorem B1998323 : Blo 690315 1998323 := bstep (se 1 (by rfl) ⟨1498742, by rfl⟩ : syracuseStep 1998323 = 2997485) B2997485
theorem B1867387 : Blo 690315 1867387 := bstep (se 1 (by rfl) ⟨1400540, by rfl⟩ : syracuseStep 1867387 = 2801081) B2801081
theorem B15007673 : Blo 690315 15007673 := bstep (se 2 (by rfl) ⟨5627877, by rfl⟩ : syracuseStep 15007673 = 11255755) B11255755
theorem B1310651 : Blo 690315 1310651 := bstep (se 1 (by rfl) ⟨982988, by rfl⟩ : syracuseStep 1310651 = 1965977) B1965977
theorem B983387 : Blo 690315 983387 := bstep (se 1 (by rfl) ⟨737540, by rfl⟩ : syracuseStep 983387 = 1475081) B1475081
theorem B3506651 : Blo 690315 3506651 := bstep (se 1 (by rfl) ⟨2629988, by rfl⟩ : syracuseStep 3506651 = 5259977) B5259977
theorem B14221925 : Blo 690315 14221925 := bstep (se 4 (by rfl) ⟨1333305, by rfl⟩ : syracuseStep 14221925 = 2666611) B2666611
theorem B3932819 : Blo 690315 3932819 := bstep (se 1 (by rfl) ⟨2949614, by rfl⟩ : syracuseStep 3932819 = 5899229) B5899229
theorem B3507137 : Blo 690315 3507137 := bstep (se 2 (by rfl) ⟨1315176, by rfl⟩ : syracuseStep 3507137 = 2630353) B2630353
theorem B2491535 : Blo 690315 2491535 := bstep (se 1 (by rfl) ⟨1868651, by rfl⟩ : syracuseStep 2491535 = 3737303) B3737303
theorem B1475833 : Blo 690315 1475833 := bstep (se 2 (by rfl) ⟨553437, by rfl⟩ : syracuseStep 1475833 = 1106875) B1106875
theorem B2622881 : Blo 690315 2622881 := bstep (se 2 (by rfl) ⟨983580, by rfl⟩ : syracuseStep 2622881 = 1967161) B1967161
theorem B1476191 : Blo 690315 1476191 := bstep (se 1 (by rfl) ⟨1107143, by rfl⟩ : syracuseStep 1476191 = 2214287) B2214287
theorem B1869473 : Blo 690315 1869473 := bstep (se 2 (by rfl) ⟨701052, by rfl⟩ : syracuseStep 1869473 = 1402105) B1402105
theorem B1246907 : Blo 690315 1246907 := bstep (se 1 (by rfl) ⟨935180, by rfl⟩ : syracuseStep 1246907 = 1870361) B1870361
theorem B984811 : Blo 690315 984811 := bstep (se 1 (by rfl) ⟨738608, by rfl⟩ : syracuseStep 984811 = 1477217) B1477217
theorem B1312519 : Blo 690315 1312519 := bstep (se 1 (by rfl) ⟨984389, by rfl⟩ : syracuseStep 1312519 = 1968779) B1968779
theorem B7997251 : Blo 690315 7997251 := bstep (se 1 (by rfl) ⟨5997938, by rfl⟩ : syracuseStep 7997251 = 11995877) B11995877
theorem B2623337 : Blo 690315 2623337 := bstep (se 2 (by rfl) ⟨983751, by rfl⟩ : syracuseStep 2623337 = 1967503) B1967503
theorem B3901289 : Blo 690315 3901289 := bstep (se 2 (by rfl) ⟨1462983, by rfl⟩ : syracuseStep 3901289 = 2925967) B2925967
theorem B1476559 : Blo 690315 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B6653933 : Blo 690315 6653933 := bstep (se 3 (by rfl) ⟨1247612, by rfl⟩ : syracuseStep 6653933 = 2495225) B2495225
theorem B3737735 : Blo 690315 3737735 := bstep (se 1 (by rfl) ⟨2803301, by rfl⟩ : syracuseStep 3737735 = 5606603) B5606603
theorem B690463 : Blo 690315 690463 := bstep (se 1 (by rfl) ⟨517847, by rfl⟩ : syracuseStep 690463 = 1035695) B1035695
theorem B690523 : Blo 690315 690523 := bstep (se 1 (by rfl) ⟨517892, by rfl⟩ : syracuseStep 690523 = 1035785) B1035785
theorem B690543 : Blo 690315 690543 := bstep (se 1 (by rfl) ⟨517907, by rfl⟩ : syracuseStep 690543 = 1035815) B1035815
theorem B690599 : Blo 690315 690599 := bstep (se 1 (by rfl) ⟨517949, by rfl⟩ : syracuseStep 690599 = 1035899) B1035899
theorem B14191051 : Blo 690315 14191051 := bstep (se 1 (by rfl) ⟨10643288, by rfl⟩ : syracuseStep 14191051 = 21286577) B21286577
theorem B690683 : Blo 690315 690683 := bstep (se 1 (by rfl) ⟨518012, by rfl⟩ : syracuseStep 690683 = 1036025) B1036025
theorem B6654473 : Blo 690315 6654473 := bstep (se 2 (by rfl) ⟨2495427, by rfl⟩ : syracuseStep 6654473 = 4990855) B4990855
theorem B690751 : Blo 690315 690751 := bstep (se 1 (by rfl) ⟨518063, by rfl⟩ : syracuseStep 690751 = 1036127) B1036127
theorem B690759 : Blo 690315 690759 := bstep (se 1 (by rfl) ⟨518069, by rfl⟩ : syracuseStep 690759 = 1036139) B1036139
theorem B1247815 : Blo 690315 1247815 := bstep (se 1 (by rfl) ⟨935861, by rfl⟩ : syracuseStep 1247815 = 1871723) B1871723
theorem B690911 : Blo 690315 690911 := bstep (se 1 (by rfl) ⟨518183, by rfl⟩ : syracuseStep 690911 = 1036367) B1036367
theorem B690991 : Blo 690315 690991 := bstep (se 1 (by rfl) ⟨518243, by rfl⟩ : syracuseStep 690991 = 1036487) B1036487
theorem B691099 : Blo 690315 691099 := bstep (se 1 (by rfl) ⟨518324, by rfl⟩ : syracuseStep 691099 = 1036649) B1036649
theorem B691151 : Blo 690315 691151 := bstep (se 1 (by rfl) ⟨518363, by rfl⟩ : syracuseStep 691151 = 1036727) B1036727
theorem B691175 : Blo 690315 691175 := bstep (se 1 (by rfl) ⟨518381, by rfl⟩ : syracuseStep 691175 = 1036763) B1036763
theorem B691487 : Blo 690315 691487 := bstep (se 1 (by rfl) ⟨518615, by rfl⟩ : syracuseStep 691487 = 1037231) B1037231
theorem B691547 : Blo 690315 691547 := bstep (se 1 (by rfl) ⟨518660, by rfl⟩ : syracuseStep 691547 = 1037321) B1037321
theorem B691567 : Blo 690315 691567 := bstep (se 1 (by rfl) ⟨518675, by rfl⟩ : syracuseStep 691567 = 1037351) B1037351
theorem B691623 : Blo 690315 691623 := bstep (se 1 (by rfl) ⟨518717, by rfl⟩ : syracuseStep 691623 = 1037435) B1037435
theorem B691707 : Blo 690315 691707 := bstep (se 1 (by rfl) ⟨518780, by rfl⟩ : syracuseStep 691707 = 1037561) B1037561
theorem B691775 : Blo 690315 691775 := bstep (se 1 (by rfl) ⟨518831, by rfl⟩ : syracuseStep 691775 = 1037663) B1037663
theorem B691783 : Blo 690315 691783 := bstep (se 1 (by rfl) ⟨518837, by rfl⟩ : syracuseStep 691783 = 1037675) B1037675
theorem B2330207 : Blo 690315 2330207 := bstep (se 1 (by rfl) ⟨1747655, by rfl⟩ : syracuseStep 2330207 = 3495311) B3495311
theorem B1052255 : Blo 690315 1052255 := bstep (se 1 (by rfl) ⟨789191, by rfl⟩ : syracuseStep 1052255 = 1578383) B1578383
theorem B691935 : Blo 690315 691935 := bstep (se 1 (by rfl) ⟨518951, by rfl⟩ : syracuseStep 691935 = 1037903) B1037903
theorem B1314539 : Blo 690315 1314539 := bstep (se 1 (by rfl) ⟨985904, by rfl⟩ : syracuseStep 1314539 = 1971809) B1971809
theorem B11243299 : Blo 690315 11243299 := bstep (se 1 (by rfl) ⟨8432474, by rfl⟩ : syracuseStep 11243299 = 16864949) B16864949
theorem B692015 : Blo 690315 692015 := bstep (se 1 (by rfl) ⟨519011, by rfl⟩ : syracuseStep 692015 = 1038023) B1038023
theorem B692123 : Blo 690315 692123 := bstep (se 1 (by rfl) ⟨519092, by rfl⟩ : syracuseStep 692123 = 1038185) B1038185
theorem B1970077 : Blo 690315 1970077 := bstep (se 3 (by rfl) ⟨369389, by rfl⟩ : syracuseStep 1970077 = 738779) B738779
theorem B1314767 : Blo 690315 1314767 := bstep (se 1 (by rfl) ⟨986075, by rfl⟩ : syracuseStep 1314767 = 1972151) B1972151
theorem B692175 : Blo 690315 692175 := bstep (se 1 (by rfl) ⟨519131, by rfl⟩ : syracuseStep 692175 = 1038263) B1038263
theorem B29921237 : Blo 690315 29921237 := bstep (se 7 (by rfl) ⟨350639, by rfl⟩ : syracuseStep 29921237 = 701279) B701279
theorem B692199 : Blo 690315 692199 := bstep (se 1 (by rfl) ⟨519149, by rfl⟩ : syracuseStep 692199 = 1038299) B1038299
theorem B3510377 : Blo 690315 3510377 := bstep (se 2 (by rfl) ⟨1316391, by rfl⟩ : syracuseStep 3510377 = 2632783) B2632783
theorem B692511 : Blo 690315 692511 := bstep (se 1 (by rfl) ⟨519383, by rfl⟩ : syracuseStep 692511 = 1038767) B1038767
theorem B692571 : Blo 690315 692571 := bstep (se 1 (by rfl) ⟨519428, by rfl⟩ : syracuseStep 692571 = 1038857) B1038857
theorem B692591 : Blo 690315 692591 := bstep (se 1 (by rfl) ⟨519443, by rfl⟩ : syracuseStep 692591 = 1038887) B1038887
theorem B692647 : Blo 690315 692647 := bstep (se 1 (by rfl) ⟨519485, by rfl⟩ : syracuseStep 692647 = 1038971) B1038971
theorem B1577441 : Blo 690315 1577441 := bstep (se 2 (by rfl) ⟨591540, by rfl⟩ : syracuseStep 1577441 = 1183081) B1183081
theorem B692731 : Blo 690315 692731 := bstep (se 1 (by rfl) ⟨519548, by rfl⟩ : syracuseStep 692731 = 1039097) B1039097
theorem B692799 : Blo 690315 692799 := bstep (se 1 (by rfl) ⟨519599, by rfl⟩ : syracuseStep 692799 = 1039199) B1039199
theorem B14979653 : Blo 690315 14979653 := bstep (se 4 (by rfl) ⟨1404342, by rfl⟩ : syracuseStep 14979653 = 2808685) B2808685
theorem B692807 : Blo 690315 692807 := bstep (se 1 (by rfl) ⟨519605, by rfl⟩ : syracuseStep 692807 = 1039211) B1039211
theorem B1577551 : Blo 690315 1577551 := bstep (se 1 (by rfl) ⟨1183163, by rfl⟩ : syracuseStep 1577551 = 2366327) B2366327
theorem B1315435 : Blo 690315 1315435 := bstep (se 1 (by rfl) ⟨986576, by rfl⟩ : syracuseStep 1315435 = 1973153) B1973153
theorem B1315511 : Blo 690315 1315511 := bstep (se 1 (by rfl) ⟨986633, by rfl⟩ : syracuseStep 1315511 = 1973267) B1973267
theorem B692959 : Blo 690315 692959 := bstep (se 1 (by rfl) ⟨519719, by rfl⟩ : syracuseStep 692959 = 1039439) B1039439
theorem B9966365 : Blo 690315 9966365 := bstep (se 3 (by rfl) ⟨1868693, by rfl⟩ : syracuseStep 9966365 = 3737387) B3737387
theorem B693039 : Blo 690315 693039 := bstep (se 1 (by rfl) ⟨519779, by rfl⟩ : syracuseStep 693039 = 1039559) B1039559
theorem B1315739 : Blo 690315 1315739 := bstep (se 1 (by rfl) ⟨986804, by rfl⟩ : syracuseStep 1315739 = 1973609) B1973609
theorem B693147 : Blo 690315 693147 := bstep (se 1 (by rfl) ⟨519860, by rfl⟩ : syracuseStep 693147 = 1039721) B1039721
theorem B57480101 : Blo 690315 57480101 := bstep (se 4 (by rfl) ⟨5388759, by rfl⟩ : syracuseStep 57480101 = 10777519) B10777519
theorem B8852429 : Blo 690315 8852429 := bstep (se 3 (by rfl) ⟨1659830, by rfl⟩ : syracuseStep 8852429 = 3319661) B3319661
theorem B693199 : Blo 690315 693199 := bstep (se 1 (by rfl) ⟨519899, by rfl⟩ : syracuseStep 693199 = 1039799) B1039799
theorem B2331611 : Blo 690315 2331611 := bstep (se 1 (by rfl) ⟨1748708, by rfl⟩ : syracuseStep 2331611 = 3497417) B3497417
theorem B693223 : Blo 690315 693223 := bstep (se 1 (by rfl) ⟨519917, by rfl⟩ : syracuseStep 693223 = 1039835) B1039835
theorem B4428857 : Blo 690315 4428857 := bstep (se 2 (by rfl) ⟨1660821, by rfl⟩ : syracuseStep 4428857 = 3321643) B3321643
theorem B1873019 : Blo 690315 1873019 := bstep (se 1 (by rfl) ⟨1404764, by rfl⟩ : syracuseStep 1873019 = 2809529) B2809529
theorem B2331773 : Blo 690315 2331773 := bstep (se 3 (by rfl) ⟨437207, by rfl⟩ : syracuseStep 2331773 = 874415) B874415
theorem B3511511 : Blo 690315 3511511 := bstep (se 1 (by rfl) ⟨2633633, by rfl⟩ : syracuseStep 3511511 = 5267267) B5267267
theorem B2331881 : Blo 690315 2331881 := bstep (se 2 (by rfl) ⟨874455, by rfl⟩ : syracuseStep 2331881 = 1748911) B1748911
theorem B693535 : Blo 690315 693535 := bstep (se 1 (by rfl) ⟨520151, by rfl⟩ : syracuseStep 693535 = 1040303) B1040303
theorem B693595 : Blo 690315 693595 := bstep (se 1 (by rfl) ⟨520196, by rfl⟩ : syracuseStep 693595 = 1040393) B1040393
theorem B693615 : Blo 690315 693615 := bstep (se 1 (by rfl) ⟨520211, by rfl⟩ : syracuseStep 693615 = 1040423) B1040423
theorem B2332043 : Blo 690315 2332043 := bstep (se 1 (by rfl) ⟨1749032, by rfl⟩ : syracuseStep 2332043 = 3498065) B3498065
theorem B693671 : Blo 690315 693671 := bstep (se 1 (by rfl) ⟨520253, by rfl⟩ : syracuseStep 693671 = 1040507) B1040507
theorem B1054201 : Blo 690315 1054201 := bstep (se 2 (by rfl) ⟨395325, by rfl⟩ : syracuseStep 1054201 = 790651) B790651
theorem B693755 : Blo 690315 693755 := bstep (se 1 (by rfl) ⟨520316, by rfl⟩ : syracuseStep 693755 = 1040633) B1040633
theorem B693823 : Blo 690315 693823 := bstep (se 1 (by rfl) ⟨520367, by rfl⟩ : syracuseStep 693823 = 1040735) B1040735
theorem B693831 : Blo 690315 693831 := bstep (se 1 (by rfl) ⟨520373, by rfl⟩ : syracuseStep 693831 = 1040747) B1040747
theorem B1316513 : Blo 690315 1316513 := bstep (se 2 (by rfl) ⟨493692, by rfl⟩ : syracuseStep 1316513 = 987385) B987385
theorem B693983 : Blo 690315 693983 := bstep (se 1 (by rfl) ⟨520487, by rfl⟩ : syracuseStep 693983 = 1040975) B1040975
theorem B694063 : Blo 690315 694063 := bstep (se 1 (by rfl) ⟨520547, by rfl⟩ : syracuseStep 694063 = 1041095) B1041095
theorem B1316665 : Blo 690315 1316665 := bstep (se 2 (by rfl) ⟨493749, by rfl⟩ : syracuseStep 1316665 = 987499) B987499
theorem B694171 : Blo 690315 694171 := bstep (se 1 (by rfl) ⟨520628, by rfl⟩ : syracuseStep 694171 = 1041257) B1041257
theorem B3151799 : Blo 690315 3151799 := bstep (se 1 (by rfl) ⟨2363849, by rfl⟩ : syracuseStep 3151799 = 4727699) B4727699
theorem B694223 : Blo 690315 694223 := bstep (se 1 (by rfl) ⟨520667, by rfl⟩ : syracuseStep 694223 = 1041335) B1041335
theorem B694247 : Blo 690315 694247 := bstep (se 1 (by rfl) ⟨520685, by rfl⟩ : syracuseStep 694247 = 1041371) B1041371
theorem B1316969 : Blo 690315 1316969 := bstep (se 2 (by rfl) ⟨493863, by rfl⟩ : syracuseStep 1316969 = 987727) B987727
theorem B6298523 : Blo 690315 6298523 := bstep (se 1 (by rfl) ⟨4723892, by rfl⟩ : syracuseStep 6298523 = 9447785) B9447785
theorem B2628895 : Blo 690315 2628895 := bstep (se 1 (by rfl) ⟨1971671, by rfl⟩ : syracuseStep 2628895 = 3943343) B3943343
theorem B2956961 : Blo 690315 2956961 := bstep (se 2 (by rfl) ⟨1108860, by rfl⟩ : syracuseStep 2956961 = 2217721) B2217721
theorem B9969713 : Blo 690315 9969713 := bstep (se 2 (by rfl) ⟨3738642, by rfl⟩ : syracuseStep 9969713 = 7477285) B7477285
theorem B3514427 : Blo 690315 3514427 := bstep (se 1 (by rfl) ⟨2635820, by rfl⟩ : syracuseStep 3514427 = 5271641) B5271641
theorem B7479449 : Blo 690315 7479449 := bstep (se 2 (by rfl) ⟨2804793, by rfl⟩ : syracuseStep 7479449 = 5609587) B5609587
theorem B11968721 : Blo 690315 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B14983379 : Blo 690315 14983379 := bstep (se 1 (by rfl) ⟨11237534, by rfl⟩ : syracuseStep 14983379 = 22475069) B22475069
theorem B2335067 : Blo 690315 2335067 := bstep (se 1 (by rfl) ⟨1751300, by rfl⟩ : syracuseStep 2335067 = 3502601) B3502601
theorem B59875685 : Blo 690315 59875685 := bstep (se 4 (by rfl) ⟨5613345, by rfl⟩ : syracuseStep 59875685 = 11226691) B11226691
theorem B1876651 : Blo 690315 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B16851725 : Blo 690315 16851725 := bstep (se 3 (by rfl) ⟨3159698, by rfl⟩ : syracuseStep 16851725 = 6319397) B6319397
theorem B42738445 : Blo 690315 42738445 := bstep (se 3 (by rfl) ⟨8013458, by rfl⟩ : syracuseStep 42738445 = 16026917) B16026917
theorem B6333673 : Blo 690315 6333673 := bstep (se 2 (by rfl) ⟨2375127, by rfl⟩ : syracuseStep 6333673 = 4750255) B4750255
theorem B2336039 : Blo 690315 2336039 := bstep (se 1 (by rfl) ⟨1752029, by rfl⟩ : syracuseStep 2336039 = 3504059) B3504059
theorem B7480619 : Blo 690315 7480619 := bstep (se 1 (by rfl) ⟨5610464, by rfl⟩ : syracuseStep 7480619 = 11220929) B11220929
theorem B2631325 : Blo 690315 2631325 := bstep (se 3 (by rfl) ⟨493373, by rfl⟩ : syracuseStep 2631325 = 986747) B986747
theorem B2992079 : Blo 690315 2992079 := bstep (se 1 (by rfl) ⟨2244059, by rfl⟩ : syracuseStep 2992079 = 4488119) B4488119
theorem B2336903 : Blo 690315 2336903 := bstep (se 1 (by rfl) ⟨1752677, by rfl⟩ : syracuseStep 2336903 = 3505355) B3505355
theorem B11250049 : Blo 690315 11250049 := bstep (se 2 (by rfl) ⟨4218768, by rfl⟩ : syracuseStep 11250049 = 8437537) B8437537
theorem B10005115 : Blo 690315 10005115 := bstep (se 1 (by rfl) ⟨7503836, by rfl⟩ : syracuseStep 10005115 = 15007673) B15007673
theorem B6728669 : Blo 690315 6728669 := bstep (se 3 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 6728669 = 2523251) B2523251
theorem B1780985 : Blo 690315 1780985 := bstep (se 2 (by rfl) ⟨667869, by rfl⟩ : syracuseStep 1780985 = 1335739) B1335739
theorem B2960651 : Blo 690315 2960651 := bstep (se 1 (by rfl) ⟨2220488, by rfl⟩ : syracuseStep 2960651 = 4440977) B4440977
theorem B1748263 : Blo 690315 1748263 := bstep (se 1 (by rfl) ⟨1311197, by rfl⟩ : syracuseStep 1748263 = 2622395) B2622395
theorem B2338145 : Blo 690315 2338145 := bstep (se 2 (by rfl) ⟨876804, by rfl⟩ : syracuseStep 2338145 = 1753609) B1753609
theorem B2633057 : Blo 690315 2633057 := bstep (se 2 (by rfl) ⟨987396, by rfl⟩ : syracuseStep 2633057 = 1974793) B1974793
theorem B3943799 : Blo 690315 3943799 := bstep (se 1 (by rfl) ⟨2957849, by rfl⟩ : syracuseStep 3943799 = 5915699) B5915699
theorem B10136951 : Blo 690315 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B13315549 : Blo 690315 13315549 := bstep (se 3 (by rfl) ⟨2496665, by rfl⟩ : syracuseStep 13315549 = 4993331) B4993331
theorem B1748537 : Blo 690315 1748537 := bstep (se 2 (by rfl) ⟨655701, by rfl⟩ : syracuseStep 1748537 = 1311403) B1311403
theorem B2993773 : Blo 690315 2993773 := bstep (se 3 (by rfl) ⟨561332, by rfl⟩ : syracuseStep 2993773 = 1122665) B1122665
theorem B2502305 : Blo 690315 2502305 := bstep (se 2 (by rfl) ⟨938364, by rfl⟩ : syracuseStep 2502305 = 1876729) B1876729
theorem B3321661 : Blo 690315 3321661 := bstep (se 3 (by rfl) ⟨622811, by rfl⟩ : syracuseStep 3321661 = 1245623) B1245623
theorem B2634241 : Blo 690315 2634241 := bstep (se 2 (by rfl) ⟨987840, by rfl⟩ : syracuseStep 2634241 = 1975681) B1975681
theorem B5911325 : Blo 690315 5911325 := bstep (se 3 (by rfl) ⟨1108373, by rfl⟩ : syracuseStep 5911325 = 2216747) B2216747
theorem B5485391 : Blo 690315 5485391 := bstep (se 1 (by rfl) ⟨4114043, by rfl⟩ : syracuseStep 5485391 = 8228087) B8228087
theorem B2634727 : Blo 690315 2634727 := bstep (se 1 (by rfl) ⟨1976045, by rfl⟩ : syracuseStep 2634727 = 3952091) B3952091
theorem B1553399 : Blo 690315 1553399 := bstep (se 1 (by rfl) ⟨1165049, by rfl⟩ : syracuseStep 1553399 = 2330099) B2330099
theorem B4502585 : Blo 690315 4502585 := bstep (se 2 (by rfl) ⟨1688469, by rfl⟩ : syracuseStep 4502585 = 3376939) B3376939
theorem B2340089 : Blo 690315 2340089 := bstep (se 2 (by rfl) ⟨877533, by rfl⟩ : syracuseStep 2340089 = 1755067) B1755067
theorem B2635001 : Blo 690315 2635001 := bstep (se 2 (by rfl) ⟨988125, by rfl⟩ : syracuseStep 2635001 = 1976251) B1976251
theorem B832799 : Blo 690315 832799 := bstep (se 1 (by rfl) ⟨624599, by rfl⟩ : syracuseStep 832799 = 1249199) B1249199
theorem B4437287 : Blo 690315 4437287 := bstep (se 1 (by rfl) ⟨3327965, by rfl⟩ : syracuseStep 4437287 = 6655931) B6655931
theorem B1553759 : Blo 690315 1553759 := bstep (se 1 (by rfl) ⟨1165319, by rfl⟩ : syracuseStep 1553759 = 2330639) B2330639
theorem B1750369 : Blo 690315 1750369 := bstep (se 2 (by rfl) ⟨656388, by rfl⟩ : syracuseStep 1750369 = 1312777) B1312777
theorem B2340359 : Blo 690315 2340359 := bstep (se 1 (by rfl) ⟨1755269, by rfl⟩ : syracuseStep 2340359 = 3510539) B3510539
theorem B4208165 : Blo 690315 4208165 := bstep (se 4 (by rfl) ⟨394515, by rfl⟩ : syracuseStep 4208165 = 789031) B789031
theorem B3159737 : Blo 690315 3159737 := bstep (se 2 (by rfl) ⟨1184901, by rfl⟩ : syracuseStep 3159737 = 2369803) B2369803
theorem B1554155 : Blo 690315 1554155 := bstep (se 1 (by rfl) ⟨1165616, by rfl⟩ : syracuseStep 1554155 = 2331233) B2331233
theorem B3192605 : Blo 690315 3192605 := bstep (se 3 (by rfl) ⟨598613, by rfl⟩ : syracuseStep 3192605 = 1197227) B1197227
theorem B4732759 : Blo 690315 4732759 := bstep (se 1 (by rfl) ⟨3549569, by rfl⟩ : syracuseStep 4732759 = 7099139) B7099139
theorem B1554281 : Blo 690315 1554281 := bstep (se 2 (by rfl) ⟨582855, by rfl⟩ : syracuseStep 1554281 = 1165711) B1165711
theorem B2963591 : Blo 690315 2963591 := bstep (se 1 (by rfl) ⟨2222693, by rfl⟩ : syracuseStep 2963591 = 4445387) B4445387
theorem B1751321 : Blo 690315 1751321 := bstep (se 2 (by rfl) ⟨656745, by rfl⟩ : syracuseStep 1751321 = 1313491) B1313491
theorem B2996509 : Blo 690315 2996509 := bstep (se 3 (by rfl) ⟨561845, by rfl⟩ : syracuseStep 2996509 = 1123691) B1123691
theorem B2341331 : Blo 690315 2341331 := bstep (se 1 (by rfl) ⟨1755998, by rfl⟩ : syracuseStep 2341331 = 3511997) B3511997
theorem B1751615 : Blo 690315 1751615 := bstep (se 1 (by rfl) ⟨1313711, by rfl⟩ : syracuseStep 1751615 = 2627423) B2627423
theorem B2341439 : Blo 690315 2341439 := bstep (se 1 (by rfl) ⟨1756079, by rfl⟩ : syracuseStep 2341439 = 3512159) B3512159
theorem B1555127 : Blo 690315 1555127 := bstep (se 1 (by rfl) ⟨1166345, by rfl⟩ : syracuseStep 1555127 = 2332691) B2332691
theorem B1751827 : Blo 690315 1751827 := bstep (se 1 (by rfl) ⟨1313870, by rfl⟩ : syracuseStep 1751827 = 2627741) B2627741
theorem B1555343 : Blo 690315 1555343 := bstep (se 1 (by rfl) ⟨1166507, by rfl⟩ : syracuseStep 1555343 = 2333015) B2333015
theorem B1752263 : Blo 690315 1752263 := bstep (se 1 (by rfl) ⟨1314197, by rfl⟩ : syracuseStep 1752263 = 2628395) B2628395
theorem B1752313 : Blo 690315 1752313 := bstep (se 2 (by rfl) ⟨657117, by rfl⟩ : syracuseStep 1752313 = 1314235) B1314235
theorem B1556063 : Blo 690315 1556063 := bstep (se 1 (by rfl) ⟨1167047, by rfl⟩ : syracuseStep 1556063 = 2334095) B2334095
theorem B1556279 : Blo 690315 1556279 := bstep (se 1 (by rfl) ⟨1167209, by rfl⟩ : syracuseStep 1556279 = 2334419) B2334419
theorem B1752961 : Blo 690315 1752961 := bstep (se 2 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 1752961 = 1314721) B1314721
theorem B1556585 : Blo 690315 1556585 := bstep (se 2 (by rfl) ⟨583719, by rfl⟩ : syracuseStep 1556585 = 1167439) B1167439
theorem B2343275 : Blo 690315 2343275 := bstep (se 1 (by rfl) ⟨1757456, by rfl⟩ : syracuseStep 2343275 = 3514913) B3514913
theorem B1557071 : Blo 690315 1557071 := bstep (se 1 (by rfl) ⟨1167803, by rfl⟩ : syracuseStep 1557071 = 2335607) B2335607
theorem B1753721 : Blo 690315 1753721 := bstep (se 2 (by rfl) ⟨657645, by rfl⟩ : syracuseStep 1753721 = 1315291) B1315291
theorem B1753771 : Blo 690315 1753771 := bstep (se 1 (by rfl) ⟨1315328, by rfl⟩ : syracuseStep 1753771 = 2630657) B2630657
theorem B1557215 : Blo 690315 1557215 := bstep (se 1 (by rfl) ⟨1167911, by rfl⟩ : syracuseStep 1557215 = 2335823) B2335823
theorem B1557467 : Blo 690315 1557467 := bstep (se 1 (by rfl) ⟨1168100, by rfl⟩ : syracuseStep 1557467 = 2336201) B2336201
theorem B1754075 : Blo 690315 1754075 := bstep (se 1 (by rfl) ⟨1315556, by rfl⟩ : syracuseStep 1754075 = 2631113) B2631113
theorem B1557647 : Blo 690315 1557647 := bstep (se 1 (by rfl) ⟨1168235, by rfl⟩ : syracuseStep 1557647 = 2336471) B2336471
theorem B1557737 : Blo 690315 1557737 := bstep (se 2 (by rfl) ⟨584151, by rfl⟩ : syracuseStep 1557737 = 1168303) B1168303
theorem B1557791 : Blo 690315 1557791 := bstep (se 1 (by rfl) ⟨1168343, by rfl⟩ : syracuseStep 1557791 = 2336687) B2336687
theorem B1754399 : Blo 690315 1754399 := bstep (se 1 (by rfl) ⟨1315799, by rfl⟩ : syracuseStep 1754399 = 2631599) B2631599
theorem B4441387 : Blo 690315 4441387 := bstep (se 1 (by rfl) ⟨3331040, by rfl⟩ : syracuseStep 4441387 = 6662081) B6662081
theorem B5916077 : Blo 690315 5916077 := bstep (se 3 (by rfl) ⟨1109264, by rfl⟩ : syracuseStep 5916077 = 2218529) B2218529
theorem B1165063 : Blo 690315 1165063 := bstep (se 1 (by rfl) ⟨873797, by rfl⟩ : syracuseStep 1165063 = 1747595) B1747595
theorem B1165097 : Blo 690315 1165097 := bstep (se 2 (by rfl) ⟨436911, by rfl⟩ : syracuseStep 1165097 = 873823) B873823
theorem B1558313 : Blo 690315 1558313 := bstep (se 2 (by rfl) ⟨584367, by rfl⟩ : syracuseStep 1558313 = 1168735) B1168735
theorem B4442003 : Blo 690315 4442003 := bstep (se 1 (by rfl) ⟨3331502, by rfl⟩ : syracuseStep 4442003 = 6663005) B6663005
theorem B1755503 : Blo 690315 1755503 := bstep (se 1 (by rfl) ⟨1316627, by rfl⟩ : syracuseStep 1755503 = 2633255) B2633255
theorem B739783 : Blo 690315 739783 := bstep (se 1 (by rfl) ⟨554837, by rfl⟩ : syracuseStep 739783 = 1109675) B1109675
theorem B7096805 : Blo 690315 7096805 := bstep (se 4 (by rfl) ⟨665325, by rfl⟩ : syracuseStep 7096805 = 1330651) B1330651
theorem B1165819 : Blo 690315 1165819 := bstep (se 1 (by rfl) ⟨874364, by rfl⟩ : syracuseStep 1165819 = 1748729) B1748729
theorem B3558109 : Blo 690315 3558109 := bstep (se 3 (by rfl) ⟨667145, by rfl⟩ : syracuseStep 3558109 = 1334291) B1334291
theorem B8014625 : Blo 690315 8014625 := bstep (se 2 (by rfl) ⟨3005484, by rfl⟩ : syracuseStep 8014625 = 6010969) B6010969
theorem B1559375 : Blo 690315 1559375 := bstep (se 1 (by rfl) ⟨1169531, by rfl⟩ : syracuseStep 1559375 = 2339063) B2339063
theorem B1166251 : Blo 690315 1166251 := bstep (se 1 (by rfl) ⟨874688, by rfl⟩ : syracuseStep 1166251 = 1749377) B1749377
theorem B1756151 : Blo 690315 1756151 := bstep (se 1 (by rfl) ⟨1317113, by rfl⟩ : syracuseStep 1756151 = 2634227) B2634227
theorem B1559591 : Blo 690315 1559591 := bstep (se 1 (by rfl) ⟨1169693, by rfl⟩ : syracuseStep 1559591 = 2339387) B2339387
theorem B1166555 : Blo 690315 1166555 := bstep (se 1 (by rfl) ⟨874916, by rfl⟩ : syracuseStep 1166555 = 1749833) B1749833
theorem B1559771 : Blo 690315 1559771 := bstep (se 1 (by rfl) ⟨1169828, by rfl⟩ : syracuseStep 1559771 = 2339657) B2339657
theorem B1035497 : Blo 690315 1035497 := bstep (se 2 (by rfl) ⟨388311, by rfl⟩ : syracuseStep 1035497 = 776623) B776623
theorem B1035551 : Blo 690315 1035551 := bstep (se 1 (by rfl) ⟨776663, by rfl⟩ : syracuseStep 1035551 = 1553327) B1553327
theorem B1559969 : Blo 690315 1559969 := bstep (se 2 (by rfl) ⟨584988, by rfl⟩ : syracuseStep 1559969 = 1169977) B1169977
theorem B1035719 : Blo 690315 1035719 := bstep (se 1 (by rfl) ⟨776789, by rfl⟩ : syracuseStep 1035719 = 1553579) B1553579
theorem B1166791 : Blo 690315 1166791 := bstep (se 1 (by rfl) ⟨875093, by rfl⟩ : syracuseStep 1166791 = 1750187) B1750187
theorem B1036073 : Blo 690315 1036073 := bstep (se 2 (by rfl) ⟨388527, by rfl⟩ : syracuseStep 1036073 = 777055) B777055
theorem B1036079 : Blo 690315 1036079 := bstep (se 1 (by rfl) ⟨777059, by rfl⟩ : syracuseStep 1036079 = 1554119) B1554119
theorem B937775 : Blo 690315 937775 := bstep (se 1 (by rfl) ⟨703331, by rfl⟩ : syracuseStep 937775 = 1406663) B1406663
theorem B4214585 : Blo 690315 4214585 := bstep (se 2 (by rfl) ⟨1580469, by rfl⟩ : syracuseStep 4214585 = 3160939) B3160939
theorem B1560527 : Blo 690315 1560527 := bstep (se 1 (by rfl) ⟨1170395, by rfl⟩ : syracuseStep 1560527 = 2340791) B2340791
theorem B1167311 : Blo 690315 1167311 := bstep (se 1 (by rfl) ⟨875483, by rfl⟩ : syracuseStep 1167311 = 1750967) B1750967
theorem B1036553 : Blo 690315 1036553 := bstep (se 2 (by rfl) ⟨388707, by rfl⟩ : syracuseStep 1036553 = 777415) B777415
theorem B1560905 : Blo 690315 1560905 := bstep (se 2 (by rfl) ⟨585339, by rfl⟩ : syracuseStep 1560905 = 1170679) B1170679
theorem B1560923 : Blo 690315 1560923 := bstep (se 1 (by rfl) ⟨1170692, by rfl⟩ : syracuseStep 1560923 = 2341385) B2341385
theorem B1036655 : Blo 690315 1036655 := bstep (se 1 (by rfl) ⟨777491, by rfl⟩ : syracuseStep 1036655 = 1554983) B1554983
theorem B1036871 : Blo 690315 1036871 := bstep (se 1 (by rfl) ⟨777653, by rfl⟩ : syracuseStep 1036871 = 1555307) B1555307
theorem B1036907 : Blo 690315 1036907 := bstep (se 1 (by rfl) ⟨777680, by rfl⟩ : syracuseStep 1036907 = 1555361) B1555361
theorem B1167979 : Blo 690315 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B1037135 : Blo 690315 1037135 := bstep (se 1 (by rfl) ⟨777851, by rfl⟩ : syracuseStep 1037135 = 1555703) B1555703
theorem B1168283 : Blo 690315 1168283 := bstep (se 1 (by rfl) ⟨876212, by rfl⟩ : syracuseStep 1168283 = 1752425) B1752425
theorem B1561499 : Blo 690315 1561499 := bstep (se 1 (by rfl) ⟨1171124, by rfl⟩ : syracuseStep 1561499 = 2342249) B2342249
theorem B9982925 : Blo 690315 9982925 := bstep (se 3 (by rfl) ⟨1871798, by rfl⟩ : syracuseStep 9982925 = 3743597) B3743597
theorem B1332215 : Blo 690315 1332215 := bstep (se 1 (by rfl) ⟨999161, by rfl⟩ : syracuseStep 1332215 = 1998323) B1998323
theorem B1561697 : Blo 690315 1561697 := bstep (se 2 (by rfl) ⟨585636, by rfl⟩ : syracuseStep 1561697 = 1171273) B1171273
theorem B7492765 : Blo 690315 7492765 := bstep (se 3 (by rfl) ⟨1404893, by rfl⟩ : syracuseStep 7492765 = 2809787) B2809787
theorem B1037531 : Blo 690315 1037531 := bstep (se 1 (by rfl) ⟨778148, by rfl⟩ : syracuseStep 1037531 = 1556297) B1556297
theorem B873767 : Blo 690315 873767 := bstep (se 1 (by rfl) ⟨655325, by rfl⟩ : syracuseStep 873767 = 1310651) B1310651
theorem B1561895 : Blo 690315 1561895 := bstep (se 1 (by rfl) ⟨1171421, by rfl⟩ : syracuseStep 1561895 = 2342843) B2342843
theorem B3986783 : Blo 690315 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B2217311 : Blo 690315 2217311 := bstep (se 1 (by rfl) ⟨1662983, by rfl⟩ : syracuseStep 2217311 = 3325967) B3325967
theorem B1037705 : Blo 690315 1037705 := bstep (se 2 (by rfl) ⟨389139, by rfl⟩ : syracuseStep 1037705 = 778279) B778279
theorem B1660409 : Blo 690315 1660409 := bstep (se 2 (by rfl) ⟨622653, by rfl⟩ : syracuseStep 1660409 = 1245307) B1245307
theorem B874091 : Blo 690315 874091 := bstep (se 1 (by rfl) ⟨655568, by rfl⟩ : syracuseStep 874091 = 1311137) B1311137
theorem B1038059 : Blo 690315 1038059 := bstep (se 1 (by rfl) ⟨778544, by rfl⟩ : syracuseStep 1038059 = 1557089) B1557089
theorem B1038287 : Blo 690315 1038287 := bstep (se 1 (by rfl) ⟨778715, by rfl⟩ : syracuseStep 1038287 = 1557431) B1557431
theorem B874471 : Blo 690315 874471 := bstep (se 1 (by rfl) ⟨655853, by rfl⟩ : syracuseStep 874471 = 1311707) B1311707
theorem B3496121 : Blo 690315 3496121 := bstep (se 2 (by rfl) ⟨1311045, by rfl⟩ : syracuseStep 3496121 = 2622091) B2622091
theorem B1038683 : Blo 690315 1038683 := bstep (se 1 (by rfl) ⟨779012, by rfl⟩ : syracuseStep 1038683 = 1558025) B1558025
theorem B776767 : Blo 690315 776767 := bstep (se 1 (by rfl) ⟨582575, by rfl⟩ : syracuseStep 776767 = 1165151) B1165151
theorem B1038911 : Blo 690315 1038911 := bstep (se 1 (by rfl) ⟨779183, by rfl⟩ : syracuseStep 1038911 = 1558367) B1558367
theorem B1039031 : Blo 690315 1039031 := bstep (se 1 (by rfl) ⟨779273, by rfl⟩ : syracuseStep 1039031 = 1558547) B1558547
theorem B9001847 : Blo 690315 9001847 := bstep (se 1 (by rfl) ⟨6751385, by rfl⟩ : syracuseStep 9001847 = 13502771) B13502771
theorem B5266295 : Blo 690315 5266295 := bstep (se 1 (by rfl) ⟨3949721, by rfl⟩ : syracuseStep 5266295 = 7899443) B7899443
theorem B1039259 : Blo 690315 1039259 := bstep (se 1 (by rfl) ⟨779444, by rfl⟩ : syracuseStep 1039259 = 1558889) B1558889
theorem B1039655 : Blo 690315 1039655 := bstep (se 1 (by rfl) ⟨779741, by rfl⟩ : syracuseStep 1039655 = 1559483) B1559483
theorem B777595 : Blo 690315 777595 := bstep (se 1 (by rfl) ⟨583196, by rfl⟩ : syracuseStep 777595 = 1166393) B1166393
theorem B1039739 : Blo 690315 1039739 := bstep (se 1 (by rfl) ⟨779804, by rfl⟩ : syracuseStep 1039739 = 1559609) B1559609
theorem B60611975 : Blo 690315 60611975 := bstep (se 1 (by rfl) ⟨45458981, by rfl⟩ : syracuseStep 60611975 = 90917963) B90917963
theorem B1039865 : Blo 690315 1039865 := bstep (se 2 (by rfl) ⟨389949, by rfl⟩ : syracuseStep 1039865 = 779899) B779899
theorem B2252371 : Blo 690315 2252371 := bstep (se 1 (by rfl) ⟨1689278, by rfl⟩ : syracuseStep 2252371 = 3378557) B3378557
theorem B1039967 : Blo 690315 1039967 := bstep (se 1 (by rfl) ⟨779975, by rfl⟩ : syracuseStep 1039967 = 1559951) B1559951
theorem B3366515 : Blo 690315 3366515 := bstep (se 1 (by rfl) ⟨2524886, by rfl⟩ : syracuseStep 3366515 = 5049773) B5049773
theorem B18013985 : Blo 690315 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B1040183 : Blo 690315 1040183 := bstep (se 1 (by rfl) ⟨780137, by rfl⟩ : syracuseStep 1040183 = 1560275) B1560275
theorem B778063 : Blo 690315 778063 := bstep (se 1 (by rfl) ⟨583547, by rfl⟩ : syracuseStep 778063 = 1167095) B1167095
theorem B3497903 : Blo 690315 3497903 := bstep (se 1 (by rfl) ⟨2623427, by rfl⟩ : syracuseStep 3497903 = 5246855) B5246855
theorem B1040489 : Blo 690315 1040489 := bstep (se 2 (by rfl) ⟨390183, by rfl⟩ : syracuseStep 1040489 = 780367) B780367
theorem B778459 : Blo 690315 778459 := bstep (se 1 (by rfl) ⟨583844, by rfl⟩ : syracuseStep 778459 = 1167689) B1167689
theorem B11198807 : Blo 690315 11198807 := bstep (se 1 (by rfl) ⟨8399105, by rfl⟩ : syracuseStep 11198807 = 16798211) B16798211
theorem B1040807 : Blo 690315 1040807 := bstep (se 1 (by rfl) ⟨780605, by rfl⟩ : syracuseStep 1040807 = 1561211) B1561211
theorem B778747 : Blo 690315 778747 := bstep (se 1 (by rfl) ⟨584060, by rfl⟩ : syracuseStep 778747 = 1168121) B1168121
theorem B1040891 : Blo 690315 1040891 := bstep (se 1 (by rfl) ⟨780668, by rfl⟩ : syracuseStep 1040891 = 1561337) B1561337
theorem B1041017 : Blo 690315 1041017 := bstep (se 2 (by rfl) ⟨390381, by rfl⟩ : syracuseStep 1041017 = 780763) B780763
theorem B778927 : Blo 690315 778927 := bstep (se 1 (by rfl) ⟨584195, by rfl⟩ : syracuseStep 778927 = 1168391) B1168391
theorem B1041071 : Blo 690315 1041071 := bstep (se 1 (by rfl) ⟨780803, by rfl⟩ : syracuseStep 1041071 = 1561607) B1561607
theorem B1041119 : Blo 690315 1041119 := bstep (se 1 (by rfl) ⟨780839, by rfl⟩ : syracuseStep 1041119 = 1561679) B1561679
theorem B779215 : Blo 690315 779215 := bstep (se 1 (by rfl) ⟨584411, by rfl⟩ : syracuseStep 779215 = 1168823) B1168823
theorem B1041383 : Blo 690315 1041383 := bstep (se 1 (by rfl) ⟨781037, by rfl⟩ : syracuseStep 1041383 = 1562075) B1562075
theorem B779611 : Blo 690315 779611 := bstep (se 1 (by rfl) ⟨584708, by rfl⟩ : syracuseStep 779611 = 1169417) B1169417
theorem B779719 : Blo 690315 779719 := bstep (se 1 (by rfl) ⟨584789, by rfl⟩ : syracuseStep 779719 = 1169579) B1169579
theorem B3368429 : Blo 690315 3368429 := bstep (se 3 (by rfl) ⟨631580, by rfl⟩ : syracuseStep 3368429 = 1263161) B1263161
theorem B13330007 : Blo 690315 13330007 := bstep (se 1 (by rfl) ⟨9997505, by rfl⟩ : syracuseStep 13330007 = 19995011) B19995011
theorem B878303 : Blo 690315 878303 := bstep (se 1 (by rfl) ⟨658727, by rfl⟩ : syracuseStep 878303 = 1317455) B1317455
theorem B780079 : Blo 690315 780079 := bstep (se 1 (by rfl) ⟨585059, by rfl⟩ : syracuseStep 780079 = 1170119) B1170119
theorem B780187 : Blo 690315 780187 := bstep (se 1 (by rfl) ⟨585140, by rfl⟩ : syracuseStep 780187 = 1170281) B1170281
theorem B5269697 : Blo 690315 5269697 := bstep (se 2 (by rfl) ⟨1976136, by rfl⟩ : syracuseStep 5269697 = 3952273) B3952273
theorem B780583 : Blo 690315 780583 := bstep (se 1 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 780583 = 1170875) B1170875
theorem B780655 : Blo 690315 780655 := bstep (se 1 (by rfl) ⟨585491, by rfl⟩ : syracuseStep 780655 = 1170983) B1170983
theorem B11397505 : Blo 690315 11397505 := bstep (se 2 (by rfl) ⟨4274064, by rfl⟩ : syracuseStep 11397505 = 8548129) B8548129
theorem B780871 : Blo 690315 780871 := bstep (se 1 (by rfl) ⟨585653, by rfl⟩ : syracuseStep 780871 = 1171307) B1171307
theorem B10644047 : Blo 690315 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B3500819 : Blo 690315 3500819 := bstep (se 1 (by rfl) ⟨2625614, by rfl⟩ : syracuseStep 3500819 = 5251229) B5251229
theorem B9006157 : Blo 690315 9006157 := bstep (se 3 (by rfl) ⟨1688654, by rfl⟩ : syracuseStep 9006157 = 3377309) B3377309
theorem B10644767 : Blo 690315 10644767 := bstep (se 1 (by rfl) ⟨7983575, by rfl⟩ : syracuseStep 10644767 = 15967151) B15967151
theorem B1994233 : Blo 690315 1994233 := bstep (se 2 (by rfl) ⟨747837, by rfl⟩ : syracuseStep 1994233 = 1495675) B1495675
theorem B3501953 : Blo 690315 3501953 := bstep (se 2 (by rfl) ⟨1313232, by rfl⟩ : syracuseStep 3501953 = 2626465) B2626465
theorem B7565885 : Blo 690315 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B3502763 : Blo 690315 3502763 := bstep (se 1 (by rfl) ⟨2627072, by rfl⟩ : syracuseStep 3502763 = 5254145) B5254145
theorem B1668059 : Blo 690315 1668059 := bstep (se 1 (by rfl) ⟨1251044, by rfl⟩ : syracuseStep 1668059 = 2502089) B2502089
theorem B13300787 : Blo 690315 13300787 := bstep (se 1 (by rfl) ⟨9975590, by rfl⟩ : syracuseStep 13300787 = 19951181) B19951181
theorem B3503249 : Blo 690315 3503249 := bstep (se 2 (by rfl) ⟨1313718, by rfl⟩ : syracuseStep 3503249 = 2627437) B2627437
theorem B26572049 : Blo 690315 26572049 := bstep (se 2 (by rfl) ⟨9964518, by rfl⟩ : syracuseStep 26572049 = 19929037) B19929037
theorem B8975711 : Blo 690315 8975711 := bstep (se 1 (by rfl) ⟨6731783, by rfl⟩ : syracuseStep 8975711 = 13463567) B13463567
theorem B18708317 : Blo 690315 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B7502453 : Blo 690315 7502453 := bstep (se 5 (by rfl) ⟨351677, by rfl⟩ : syracuseStep 7502453 = 703355) B703355
theorem B5929847 : Blo 690315 5929847 := bstep (se 1 (by rfl) ⟨4447385, by rfl⟩ : syracuseStep 5929847 = 8894771) B8894771
theorem B1866791 : Blo 690315 1866791 := bstep (se 1 (by rfl) ⟨1400093, by rfl⟩ : syracuseStep 1866791 = 2800187) B2800187
theorem B1604827 : Blo 690315 1604827 := bstep (se 1 (by rfl) ⟨1203620, by rfl⟩ : syracuseStep 1604827 = 2407241) B2407241
theorem B2489849 : Blo 690315 2489849 := bstep (se 2 (by rfl) ⟨933693, by rfl⟩ : syracuseStep 2489849 = 1867387) B1867387
theorem B3505679 : Blo 690315 3505679 := bstep (se 1 (by rfl) ⟨2629259, by rfl⟩ : syracuseStep 3505679 = 5258519) B5258519
theorem B4423193 : Blo 690315 4423193 := bstep (se 2 (by rfl) ⟨1658697, by rfl⟩ : syracuseStep 4423193 = 3317395) B3317395
theorem B2621879 : Blo 690315 2621879 := bstep (se 1 (by rfl) ⟨1966409, by rfl⟩ : syracuseStep 2621879 = 3932819) B3932819
theorem B2622365 : Blo 690315 2622365 := bstep (se 3 (by rfl) ⟨491693, by rfl⟩ : syracuseStep 2622365 = 983387) B983387
theorem B56984593 : Blo 690315 56984593 := bstep (se 2 (by rfl) ⟨21369222, by rfl⟩ : syracuseStep 56984593 = 42738445) B42738445
theorem B1246315 : Blo 690315 1246315 := bstep (se 1 (by rfl) ⟨934736, by rfl⟩ : syracuseStep 1246315 = 1869473) B1869473
theorem B2491823 : Blo 690315 2491823 := bstep (se 1 (by rfl) ⟨1868867, by rfl⟩ : syracuseStep 2491823 = 3737735) B3737735
theorem B1967777 : Blo 690315 1967777 := bstep (se 2 (by rfl) ⟨737916, by rfl⟩ : syracuseStep 1967777 = 1475833) B1475833
theorem B5343083 : Blo 690315 5343083 := bstep (se 1 (by rfl) ⟨4007312, by rfl⟩ : syracuseStep 5343083 = 8014625) B8014625
theorem B690331 : Blo 690315 690331 := bstep (se 1 (by rfl) ⟨517748, by rfl⟩ : syracuseStep 690331 = 1035497) B1035497
theorem B690367 : Blo 690315 690367 := bstep (se 1 (by rfl) ⟨517775, by rfl⟩ : syracuseStep 690367 = 1035551) B1035551
theorem B3508433 : Blo 690315 3508433 := bstep (se 2 (by rfl) ⟨1315662, by rfl⟩ : syracuseStep 3508433 = 2631325) B2631325
theorem B690479 : Blo 690315 690479 := bstep (se 1 (by rfl) ⟨517859, by rfl⟩ : syracuseStep 690479 = 1035719) B1035719
theorem B1313081 : Blo 690315 1313081 := bstep (se 2 (by rfl) ⟨492405, by rfl⟩ : syracuseStep 1313081 = 984811) B984811
theorem B690715 : Blo 690315 690715 := bstep (se 1 (by rfl) ⟨518036, by rfl⟩ : syracuseStep 690715 = 1036073) B1036073
theorem B690719 : Blo 690315 690719 := bstep (se 1 (by rfl) ⟨518039, by rfl⟩ : syracuseStep 690719 = 1036079) B1036079
theorem B1968745 : Blo 690315 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B691035 : Blo 690315 691035 := bstep (se 1 (by rfl) ⟨518276, by rfl⟩ : syracuseStep 691035 = 1036553) B1036553
theorem B691103 : Blo 690315 691103 := bstep (se 1 (by rfl) ⟨518327, by rfl⟩ : syracuseStep 691103 = 1036655) B1036655
theorem B1051627 : Blo 690315 1051627 := bstep (se 1 (by rfl) ⟨788720, by rfl⟩ : syracuseStep 1051627 = 1577441) B1577441
theorem B691247 : Blo 690315 691247 := bstep (se 1 (by rfl) ⟨518435, by rfl⟩ : syracuseStep 691247 = 1036871) B1036871
theorem B691271 : Blo 690315 691271 := bstep (se 1 (by rfl) ⟨518453, by rfl⟩ : syracuseStep 691271 = 1036907) B1036907
theorem B691423 : Blo 690315 691423 := bstep (se 1 (by rfl) ⟨518567, by rfl⟩ : syracuseStep 691423 = 1037135) B1037135
theorem B5901619 : Blo 690315 5901619 := bstep (se 1 (by rfl) ⟨4426214, by rfl⟩ : syracuseStep 5901619 = 8852429) B8852429
theorem B6655283 : Blo 690315 6655283 := bstep (se 1 (by rfl) ⟨4991462, by rfl⟩ : syracuseStep 6655283 = 9982925) B9982925
theorem B888143 : Blo 690315 888143 := bstep (se 1 (by rfl) ⟨666107, by rfl⟩ : syracuseStep 888143 = 1332215) B1332215
theorem B2952571 : Blo 690315 2952571 := bstep (se 1 (by rfl) ⟨2214428, by rfl⟩ : syracuseStep 2952571 = 4428857) B4428857
theorem B1248679 : Blo 690315 1248679 := bstep (se 1 (by rfl) ⟨936509, by rfl⟩ : syracuseStep 1248679 = 1873019) B1873019
theorem B2330045 : Blo 690315 2330045 := bstep (se 3 (by rfl) ⟨436883, by rfl⟩ : syracuseStep 2330045 = 873767) B873767
theorem B691687 : Blo 690315 691687 := bstep (se 1 (by rfl) ⟨518765, by rfl⟩ : syracuseStep 691687 = 1037531) B1037531
theorem B13340153 : Blo 690315 13340153 := bstep (se 2 (by rfl) ⟨5002557, by rfl⟩ : syracuseStep 13340153 = 10005115) B10005115
theorem B2657855 : Blo 690315 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B1478207 : Blo 690315 1478207 := bstep (se 1 (by rfl) ⟨1108655, by rfl⟩ : syracuseStep 1478207 = 2217311) B2217311
theorem B691803 : Blo 690315 691803 := bstep (se 1 (by rfl) ⟨518852, by rfl⟩ : syracuseStep 691803 = 1037705) B1037705
theorem B692039 : Blo 690315 692039 := bstep (se 1 (by rfl) ⟨519029, by rfl⟩ : syracuseStep 692039 = 1038059) B1038059
theorem B2101199 : Blo 690315 2101199 := bstep (se 1 (by rfl) ⟨1575899, by rfl⟩ : syracuseStep 2101199 = 3151799) B3151799
theorem B692191 : Blo 690315 692191 := bstep (se 1 (by rfl) ⟨519143, by rfl⟩ : syracuseStep 692191 = 1038287) B1038287
theorem B2330747 : Blo 690315 2330747 := bstep (se 1 (by rfl) ⟨1748060, by rfl⟩ : syracuseStep 2330747 = 3496121) B3496121
theorem B692455 : Blo 690315 692455 := bstep (se 1 (by rfl) ⟨519341, by rfl⟩ : syracuseStep 692455 = 1038683) B1038683
theorem B3936509 : Blo 690315 3936509 := bstep (se 3 (by rfl) ⟨738095, by rfl⟩ : syracuseStep 3936509 = 1476191) B1476191
theorem B2330909 : Blo 690315 2330909 := bstep (se 3 (by rfl) ⟨437045, by rfl⟩ : syracuseStep 2330909 = 874091) B874091
theorem B692607 : Blo 690315 692607 := bstep (se 1 (by rfl) ⟨519455, by rfl⟩ : syracuseStep 692607 = 1038911) B1038911
theorem B2331017 : Blo 690315 2331017 := bstep (se 2 (by rfl) ⟨874131, by rfl⟩ : syracuseStep 2331017 = 1748263) B1748263
theorem B3510701 : Blo 690315 3510701 := bstep (se 3 (by rfl) ⟨658256, by rfl⟩ : syracuseStep 3510701 = 1316513) B1316513
theorem B692687 : Blo 690315 692687 := bstep (se 1 (by rfl) ⟨519515, by rfl⟩ : syracuseStep 692687 = 1039031) B1039031
theorem B6001231 : Blo 690315 6001231 := bstep (se 1 (by rfl) ⟨4500923, by rfl⟩ : syracuseStep 6001231 = 9001847) B9001847
theorem B3510863 : Blo 690315 3510863 := bstep (se 1 (by rfl) ⟨2633147, by rfl⟩ : syracuseStep 3510863 = 5266295) B5266295
theorem B4199015 : Blo 690315 4199015 := bstep (se 1 (by rfl) ⟨3149261, by rfl⟩ : syracuseStep 4199015 = 6298523) B6298523
theorem B692839 : Blo 690315 692839 := bstep (se 1 (by rfl) ⟨519629, by rfl⟩ : syracuseStep 692839 = 1039259) B1039259
theorem B2658977 : Blo 690315 2658977 := bstep (se 2 (by rfl) ⟨997116, by rfl⟩ : syracuseStep 2658977 = 1994233) B1994233
theorem B693103 : Blo 690315 693103 := bstep (se 1 (by rfl) ⟨519827, by rfl⟩ : syracuseStep 693103 = 1039655) B1039655
theorem B693159 : Blo 690315 693159 := bstep (se 1 (by rfl) ⟨519869, by rfl⟩ : syracuseStep 693159 = 1039739) B1039739
theorem B40407983 : Blo 690315 40407983 := bstep (se 1 (by rfl) ⟨30305987, by rfl⟩ : syracuseStep 40407983 = 60611975) B60611975
theorem B693243 : Blo 690315 693243 := bstep (se 1 (by rfl) ⟨519932, by rfl⟩ : syracuseStep 693243 = 1039865) B1039865
theorem B693311 : Blo 690315 693311 := bstep (se 1 (by rfl) ⟨519983, by rfl⟩ : syracuseStep 693311 = 1039967) B1039967
theorem B4428881 : Blo 690315 4428881 := bstep (se 2 (by rfl) ⟨1660830, by rfl⟩ : syracuseStep 4428881 = 3321661) B3321661
theorem B1971307 : Blo 690315 1971307 := bstep (se 1 (by rfl) ⟨1478480, by rfl⟩ : syracuseStep 1971307 = 2956961) B2956961
theorem B693455 : Blo 690315 693455 := bstep (se 1 (by rfl) ⟨520091, by rfl⟩ : syracuseStep 693455 = 1040183) B1040183
theorem B2626769 : Blo 690315 2626769 := bstep (se 2 (by rfl) ⟨985038, by rfl⟩ : syracuseStep 2626769 = 1970077) B1970077
theorem B2331935 : Blo 690315 2331935 := bstep (se 1 (by rfl) ⟨1748951, by rfl⟩ : syracuseStep 2331935 = 3497903) B3497903
theorem B693659 : Blo 690315 693659 := bstep (se 1 (by rfl) ⟨520244, by rfl⟩ : syracuseStep 693659 = 1040489) B1040489
theorem B4986299 : Blo 690315 4986299 := bstep (se 1 (by rfl) ⟨3739724, by rfl⟩ : syracuseStep 4986299 = 7479449) B7479449
theorem B39917123 : Blo 690315 39917123 := bstep (se 1 (by rfl) ⟨29937842, by rfl⟩ : syracuseStep 39917123 = 59875685) B59875685
theorem B693871 : Blo 690315 693871 := bstep (se 1 (by rfl) ⟨520403, by rfl⟩ : syracuseStep 693871 = 1040807) B1040807
theorem B693927 : Blo 690315 693927 := bstep (se 1 (by rfl) ⟨520445, by rfl⟩ : syracuseStep 693927 = 1040891) B1040891
theorem B694011 : Blo 690315 694011 := bstep (se 1 (by rfl) ⟨520508, by rfl⟩ : syracuseStep 694011 = 1041017) B1041017
theorem B694047 : Blo 690315 694047 := bstep (se 1 (by rfl) ⟨520535, by rfl⟩ : syracuseStep 694047 = 1041071) B1041071
theorem B694079 : Blo 690315 694079 := bstep (se 1 (by rfl) ⟨520559, by rfl⟩ : syracuseStep 694079 = 1041119) B1041119
theorem B694255 : Blo 690315 694255 := bstep (se 1 (by rfl) ⟨520691, by rfl⟩ : syracuseStep 694255 = 1041383) B1041383
theorem B3512321 : Blo 690315 3512321 := bstep (se 2 (by rfl) ⟨1317120, by rfl⟩ : syracuseStep 3512321 = 2634241) B2634241
theorem B2103401 : Blo 690315 2103401 := bstep (se 2 (by rfl) ⟨788775, by rfl⟩ : syracuseStep 2103401 = 1577551) B1577551
theorem B4987079 : Blo 690315 4987079 := bstep (se 1 (by rfl) ⟨3740309, by rfl⟩ : syracuseStep 4987079 = 7480619) B7480619
theorem B8886671 : Blo 690315 8886671 := bstep (se 1 (by rfl) ⟨6665003, by rfl⟩ : syracuseStep 8886671 = 13330007) B13330007
theorem B3512969 : Blo 690315 3512969 := bstep (se 2 (by rfl) ⟨1317363, by rfl⟩ : syracuseStep 3512969 = 2634727) B2634727
theorem B3513131 : Blo 690315 3513131 := bstep (se 1 (by rfl) ⟨2634848, by rfl⟩ : syracuseStep 3513131 = 5269697) B5269697
theorem B2333825 : Blo 690315 2333825 := bstep (se 2 (by rfl) ⟨875184, by rfl⟩ : syracuseStep 2333825 = 1750369) B1750369
theorem B2333879 : Blo 690315 2333879 := bstep (se 1 (by rfl) ⟨1750409, by rfl⟩ : syracuseStep 2333879 = 3500819) B3500819
theorem B2629199 : Blo 690315 2629199 := bstep (se 1 (by rfl) ⟨1971899, by rfl⟩ : syracuseStep 2629199 = 3943799) B3943799
theorem B6757967 : Blo 690315 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B2334635 : Blo 690315 2334635 := bstep (se 1 (by rfl) ⟨1750976, by rfl⟩ : syracuseStep 2334635 = 3501953) B3501953
theorem B2335175 : Blo 690315 2335175 := bstep (se 1 (by rfl) ⟨1751381, by rfl⟩ : syracuseStep 2335175 = 3502763) B3502763
theorem B3940883 : Blo 690315 3940883 := bstep (se 1 (by rfl) ⟨2955662, by rfl⟩ : syracuseStep 3940883 = 5911325) B5911325
theorem B2335499 : Blo 690315 2335499 := bstep (se 1 (by rfl) ⟨1751624, by rfl⟩ : syracuseStep 2335499 = 3503249) B3503249
theorem B2958191 : Blo 690315 2958191 := bstep (se 1 (by rfl) ⟨2218643, by rfl⟩ : syracuseStep 2958191 = 4437287) B4437287
theorem B2335769 : Blo 690315 2335769 := bstep (se 2 (by rfl) ⟨875913, by rfl⟩ : syracuseStep 2335769 = 1751827) B1751827
theorem B2106491 : Blo 690315 2106491 := bstep (se 1 (by rfl) ⟨1579868, by rfl⟩ : syracuseStep 2106491 = 3159737) B3159737
theorem B1975727 : Blo 690315 1975727 := bstep (se 1 (by rfl) ⟨1481795, by rfl⟩ : syracuseStep 1975727 = 2963591) B2963591
theorem B2139769 : Blo 690315 2139769 := bstep (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) B1604827
theorem B2336417 : Blo 690315 2336417 := bstep (se 2 (by rfl) ⟨876156, by rfl⟩ : syracuseStep 2336417 = 1752313) B1752313
theorem B2500733 : Blo 690315 2500733 := bstep (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) B937775
theorem B2337119 : Blo 690315 2337119 := bstep (se 1 (by rfl) ⟨1752839, by rfl⟩ : syracuseStep 2337119 = 3505679) B3505679
theorem B2337281 : Blo 690315 2337281 := bstep (se 2 (by rfl) ⟨876480, by rfl⟩ : syracuseStep 2337281 = 1752961) B1752961
theorem B2337767 : Blo 690315 2337767 := bstep (se 1 (by rfl) ⟨1753325, by rfl⟩ : syracuseStep 2337767 = 3506651) B3506651
theorem B9481283 : Blo 690315 9481283 := bstep (se 1 (by rfl) ⟨7110962, by rfl⟩ : syracuseStep 9481283 = 14221925) B14221925
theorem B2338091 : Blo 690315 2338091 := bstep (se 1 (by rfl) ⟨1753568, by rfl⟩ : syracuseStep 2338091 = 3507137) B3507137
theorem B2338361 : Blo 690315 2338361 := bstep (se 2 (by rfl) ⟨876885, by rfl⟩ : syracuseStep 2338361 = 1753771) B1753771
theorem B1748587 : Blo 690315 1748587 := bstep (se 1 (by rfl) ⟨1311440, by rfl⟩ : syracuseStep 1748587 = 2622881) B2622881
theorem B3944051 : Blo 690315 3944051 := bstep (se 1 (by rfl) ⟨2958038, by rfl⟩ : syracuseStep 3944051 = 5916077) B5916077
theorem B831271 : Blo 690315 831271 := bstep (se 1 (by rfl) ⟨623453, by rfl⟩ : syracuseStep 831271 = 1246907) B1246907
theorem B1748891 : Blo 690315 1748891 := bstep (se 1 (by rfl) ⟨1311668, by rfl⟩ : syracuseStep 1748891 = 2623337) B2623337
theorem B2961335 : Blo 690315 2961335 := bstep (se 1 (by rfl) ⟨2221001, by rfl⟩ : syracuseStep 2961335 = 4442003) B4442003
theorem B4435955 : Blo 690315 4435955 := bstep (se 1 (by rfl) ⟨3326966, by rfl⟩ : syracuseStep 4435955 = 6653933) B6653933
theorem B4731203 : Blo 690315 4731203 := bstep (se 1 (by rfl) ⟨3548402, by rfl⟩ : syracuseStep 4731203 = 7096805) B7096805
theorem B4436315 : Blo 690315 4436315 := bstep (se 1 (by rfl) ⟨3327236, by rfl⟩ : syracuseStep 4436315 = 6654473) B6654473
theorem B1553417 : Blo 690315 1553417 := bstep (se 2 (by rfl) ⟨582531, by rfl⟩ : syracuseStep 1553417 = 1165063) B1165063
theorem B1750025 : Blo 690315 1750025 := bstep (se 2 (by rfl) ⟨656259, by rfl⟩ : syracuseStep 1750025 = 1312519) B1312519
theorem B3945509 : Blo 690315 3945509 := bstep (se 4 (by rfl) ⟨369891, by rfl⟩ : syracuseStep 3945509 = 739783) B739783
theorem B1553471 : Blo 690315 1553471 := bstep (se 1 (by rfl) ⟨1165103, by rfl⟩ : syracuseStep 1553471 = 2330207) B2330207
theorem B701503 : Blo 690315 701503 := bstep (se 1 (by rfl) ⟨526127, by rfl⟩ : syracuseStep 701503 = 1052255) B1052255
theorem B10663001 : Blo 690315 10663001 := bstep (se 2 (by rfl) ⟨3998625, by rfl⟩ : syracuseStep 10663001 = 7997251) B7997251
theorem B2340251 : Blo 690315 2340251 := bstep (se 1 (by rfl) ⟨1755188, by rfl⟩ : syracuseStep 2340251 = 3510377) B3510377
theorem B12006893 : Blo 690315 12006893 := bstep (se 3 (by rfl) ⟨2251292, by rfl⟩ : syracuseStep 12006893 = 4502585) B4502585
theorem B18921401 : Blo 690315 18921401 := bstep (se 2 (by rfl) ⟨7095525, by rfl⟩ : syracuseStep 18921401 = 14191051) B14191051
theorem B38320067 : Blo 690315 38320067 := bstep (se 1 (by rfl) ⟨28740050, by rfl⟩ : syracuseStep 38320067 = 57480101) B57480101
theorem B1554407 : Blo 690315 1554407 := bstep (se 1 (by rfl) ⟨1165805, by rfl⟩ : syracuseStep 1554407 = 2331611) B2331611
theorem B1554425 : Blo 690315 1554425 := bstep (se 2 (by rfl) ⟨582909, by rfl⟩ : syracuseStep 1554425 = 1165819) B1165819
theorem B1554515 : Blo 690315 1554515 := bstep (se 1 (by rfl) ⟨1165886, by rfl⟩ : syracuseStep 1554515 = 2331773) B2331773
theorem B2341007 : Blo 690315 2341007 := bstep (se 1 (by rfl) ⟨1755755, by rfl⟩ : syracuseStep 2341007 = 3511511) B3511511
theorem B1554587 : Blo 690315 1554587 := bstep (se 1 (by rfl) ⟨1165940, by rfl⟩ : syracuseStep 1554587 = 2331881) B2331881
theorem B1554695 : Blo 690315 1554695 := bstep (se 1 (by rfl) ⟨1166021, by rfl⟩ : syracuseStep 1554695 = 2332043) B2332043
theorem B1555001 : Blo 690315 1555001 := bstep (se 2 (by rfl) ⟨583125, by rfl⟩ : syracuseStep 1555001 = 1166251) B1166251
theorem B12008209 : Blo 690315 12008209 := bstep (se 2 (by rfl) ⟨4503078, by rfl⟩ : syracuseStep 12008209 = 9006157) B9006157
theorem B2342141 : Blo 690315 2342141 := bstep (se 3 (by rfl) ⟨439151, by rfl⟩ : syracuseStep 2342141 = 878303) B878303
theorem B1555721 : Blo 690315 1555721 := bstep (se 2 (by rfl) ⟨583395, by rfl⟩ : syracuseStep 1555721 = 1166791) B1166791
theorem B14991065 : Blo 690315 14991065 := bstep (se 2 (by rfl) ⟨5621649, by rfl⟩ : syracuseStep 14991065 = 11243299) B11243299
theorem B2244343 : Blo 690315 2244343 := bstep (se 1 (by rfl) ⟨1683257, by rfl⟩ : syracuseStep 2244343 = 3366515) B3366515
theorem B12009323 : Blo 690315 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B2342951 : Blo 690315 2342951 := bstep (se 1 (by rfl) ⟨1757213, by rfl⟩ : syracuseStep 2342951 = 3514427) B3514427
theorem B7979147 : Blo 690315 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B1556711 : Blo 690315 1556711 := bstep (se 1 (by rfl) ⟨1167533, by rfl⟩ : syracuseStep 1556711 = 2335067) B2335067
theorem B1557305 : Blo 690315 1557305 := bstep (se 2 (by rfl) ⟨583989, by rfl⟩ : syracuseStep 1557305 = 1167979) B1167979
theorem B1753913 : Blo 690315 1753913 := bstep (se 2 (by rfl) ⟨657717, by rfl⟩ : syracuseStep 1753913 = 1315435) B1315435
theorem B1557359 : Blo 690315 1557359 := bstep (se 1 (by rfl) ⟨1168019, by rfl⟩ : syracuseStep 1557359 = 2336039) B2336039
theorem B2245619 : Blo 690315 2245619 := bstep (se 1 (by rfl) ⟨1684214, by rfl⟩ : syracuseStep 2245619 = 3368429) B3368429
theorem B1557935 : Blo 690315 1557935 := bstep (se 1 (by rfl) ⟨1168451, by rfl⟩ : syracuseStep 1557935 = 2336903) B2336903
theorem B7096031 : Blo 690315 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B7096511 : Blo 690315 7096511 := bstep (se 1 (by rfl) ⟨5322383, by rfl⟩ : syracuseStep 7096511 = 10644767) B10644767
theorem B1558763 : Blo 690315 1558763 := bstep (se 1 (by rfl) ⟨1169072, by rfl⟩ : syracuseStep 1558763 = 2338145) B2338145
theorem B1755371 : Blo 690315 1755371 := bstep (se 1 (by rfl) ⟨1316528, by rfl⟩ : syracuseStep 1755371 = 2633057) B2633057
theorem B1165691 : Blo 690315 1165691 := bstep (se 1 (by rfl) ⟨874268, by rfl⟩ : syracuseStep 1165691 = 1748537) B1748537
theorem B1755553 : Blo 690315 1755553 := bstep (se 2 (by rfl) ⟨658332, by rfl⟩ : syracuseStep 1755553 = 1316665) B1316665
theorem B6310345 : Blo 690315 6310345 := bstep (se 2 (by rfl) ⟨2366379, by rfl⟩ : syracuseStep 6310345 = 4732759) B4732759
theorem B1165961 : Blo 690315 1165961 := bstep (se 2 (by rfl) ⟨437235, by rfl⟩ : syracuseStep 1165961 = 874471) B874471
theorem B3656927 : Blo 690315 3656927 := bstep (se 1 (by rfl) ⟨2742695, by rfl⟩ : syracuseStep 3656927 = 5485391) B5485391
theorem B1035599 : Blo 690315 1035599 := bstep (se 1 (by rfl) ⟨776699, by rfl⟩ : syracuseStep 1035599 = 1553399) B1553399
theorem B8867191 : Blo 690315 8867191 := bstep (se 1 (by rfl) ⟨6650393, by rfl⟩ : syracuseStep 8867191 = 13300787) B13300787
theorem B1035689 : Blo 690315 1035689 := bstep (se 2 (by rfl) ⟨388383, by rfl⟩ : syracuseStep 1035689 = 776767) B776767
theorem B1560059 : Blo 690315 1560059 := bstep (se 1 (by rfl) ⟨1170044, by rfl⟩ : syracuseStep 1560059 = 2340089) B2340089
theorem B1756667 : Blo 690315 1756667 := bstep (se 1 (by rfl) ⟨1317500, by rfl⟩ : syracuseStep 1756667 = 2635001) B2635001
theorem B17714699 : Blo 690315 17714699 := bstep (se 1 (by rfl) ⟨13286024, by rfl⟩ : syracuseStep 17714699 = 26572049) B26572049
theorem B1035839 : Blo 690315 1035839 := bstep (se 1 (by rfl) ⟨776879, by rfl⟩ : syracuseStep 1035839 = 1553759) B1553759
theorem B5983807 : Blo 690315 5983807 := bstep (se 1 (by rfl) ⟨4487855, by rfl⟩ : syracuseStep 5983807 = 8975711) B8975711
theorem B1560239 : Blo 690315 1560239 := bstep (se 1 (by rfl) ⟨1170179, by rfl⟩ : syracuseStep 1560239 = 2340359) B2340359
theorem B2805443 : Blo 690315 2805443 := bstep (se 1 (by rfl) ⟨2104082, by rfl⟩ : syracuseStep 2805443 = 4208165) B4208165
theorem B1036103 : Blo 690315 1036103 := bstep (se 1 (by rfl) ⟨777077, by rfl⟩ : syracuseStep 1036103 = 1554155) B1554155
theorem B12472211 : Blo 690315 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B1036187 : Blo 690315 1036187 := bstep (se 1 (by rfl) ⟨777140, by rfl⟩ : syracuseStep 1036187 = 1554281) B1554281
theorem B1167547 : Blo 690315 1167547 := bstep (se 1 (by rfl) ⟨875660, by rfl⟩ : syracuseStep 1167547 = 1751321) B1751321
theorem B1560887 : Blo 690315 1560887 := bstep (se 1 (by rfl) ⟨1170665, by rfl⟩ : syracuseStep 1560887 = 2341331) B2341331
theorem B1167743 : Blo 690315 1167743 := bstep (se 1 (by rfl) ⟨875807, by rfl⟩ : syracuseStep 1167743 = 1751615) B1751615
theorem B1560959 : Blo 690315 1560959 := bstep (se 1 (by rfl) ⟨1170719, by rfl⟩ : syracuseStep 1560959 = 2341439) B2341439
theorem B5001635 : Blo 690315 5001635 := bstep (se 1 (by rfl) ⟨3751226, by rfl⟩ : syracuseStep 5001635 = 7502453) B7502453
theorem B1036751 : Blo 690315 1036751 := bstep (se 1 (by rfl) ⟨777563, by rfl⟩ : syracuseStep 1036751 = 1555127) B1555127
theorem B1036793 : Blo 690315 1036793 := bstep (se 2 (by rfl) ⟨388797, by rfl⟩ : syracuseStep 1036793 = 777595) B777595
theorem B3953231 : Blo 690315 3953231 := bstep (se 1 (by rfl) ⟨2964923, by rfl⟩ : syracuseStep 3953231 = 5929847) B5929847
theorem B1036895 : Blo 690315 1036895 := bstep (se 1 (by rfl) ⟨777671, by rfl⟩ : syracuseStep 1036895 = 1555343) B1555343
theorem B3003161 : Blo 690315 3003161 := bstep (se 2 (by rfl) ⟨1126185, by rfl⟩ : syracuseStep 3003161 = 2252371) B2252371
theorem B1168175 : Blo 690315 1168175 := bstep (se 1 (by rfl) ⟨876131, by rfl⟩ : syracuseStep 1168175 = 1752263) B1752263
theorem B1659899 : Blo 690315 1659899 := bstep (se 1 (by rfl) ⟨1244924, by rfl⟩ : syracuseStep 1659899 = 2489849) B2489849
theorem B1037375 : Blo 690315 1037375 := bstep (se 1 (by rfl) ⟨778031, by rfl⟩ : syracuseStep 1037375 = 1556063) B1556063
theorem B1037417 : Blo 690315 1037417 := bstep (se 2 (by rfl) ⟨389031, by rfl⟩ : syracuseStep 1037417 = 778063) B778063
theorem B1037519 : Blo 690315 1037519 := bstep (se 1 (by rfl) ⟨778139, by rfl⟩ : syracuseStep 1037519 = 1556279) B1556279
theorem B1037723 : Blo 690315 1037723 := bstep (se 1 (by rfl) ⟨778292, by rfl⟩ : syracuseStep 1037723 = 1556585) B1556585
theorem B1562183 : Blo 690315 1562183 := bstep (se 1 (by rfl) ⟨1171637, by rfl⟩ : syracuseStep 1562183 = 2343275) B2343275
theorem B1037945 : Blo 690315 1037945 := bstep (se 2 (by rfl) ⟨389229, by rfl⟩ : syracuseStep 1037945 = 778459) B778459
theorem B1038047 : Blo 690315 1038047 := bstep (se 1 (by rfl) ⟨778535, by rfl⟩ : syracuseStep 1038047 = 1557071) B1557071
theorem B1169147 : Blo 690315 1169147 := bstep (se 1 (by rfl) ⟨876860, by rfl⟩ : syracuseStep 1169147 = 1753721) B1753721
theorem B1038143 : Blo 690315 1038143 := bstep (se 1 (by rfl) ⟨778607, by rfl⟩ : syracuseStep 1038143 = 1557215) B1557215
theorem B1038311 : Blo 690315 1038311 := bstep (se 1 (by rfl) ⟨778733, by rfl⟩ : syracuseStep 1038311 = 1557467) B1557467
theorem B1169383 : Blo 690315 1169383 := bstep (se 1 (by rfl) ⟨877037, by rfl⟩ : syracuseStep 1169383 = 1754075) B1754075
theorem B1038329 : Blo 690315 1038329 := bstep (se 2 (by rfl) ⟨389373, by rfl⟩ : syracuseStep 1038329 = 778747) B778747
theorem B1661023 : Blo 690315 1661023 := bstep (se 1 (by rfl) ⟨1245767, by rfl⟩ : syracuseStep 1661023 = 2491535) B2491535
theorem B1038431 : Blo 690315 1038431 := bstep (se 1 (by rfl) ⟨778823, by rfl⟩ : syracuseStep 1038431 = 1557647) B1557647
theorem B1038491 : Blo 690315 1038491 := bstep (se 1 (by rfl) ⟨778868, by rfl⟩ : syracuseStep 1038491 = 1557737) B1557737
theorem B1038527 : Blo 690315 1038527 := bstep (se 1 (by rfl) ⟨778895, by rfl⟩ : syracuseStep 1038527 = 1557791) B1557791
theorem B1169599 : Blo 690315 1169599 := bstep (se 1 (by rfl) ⟨877199, by rfl⟩ : syracuseStep 1169599 = 1754399) B1754399
theorem B1038569 : Blo 690315 1038569 := bstep (se 2 (by rfl) ⟨389463, by rfl⟩ : syracuseStep 1038569 = 778927) B778927
theorem B776731 : Blo 690315 776731 := bstep (se 1 (by rfl) ⟨582548, by rfl⟩ : syracuseStep 776731 = 1165097) B1165097
theorem B1038875 : Blo 690315 1038875 := bstep (se 1 (by rfl) ⟨779156, by rfl⟩ : syracuseStep 1038875 = 1558313) B1558313
theorem B1038953 : Blo 690315 1038953 := bstep (se 2 (by rfl) ⟨389607, by rfl⟩ : syracuseStep 1038953 = 779215) B779215
theorem B1170335 : Blo 690315 1170335 := bstep (se 1 (by rfl) ⟨877751, by rfl⟩ : syracuseStep 1170335 = 1755503) B1755503
theorem B8444897 : Blo 690315 8444897 := bstep (se 2 (by rfl) ⟨3166836, by rfl⟩ : syracuseStep 8444897 = 6333673) B6333673
theorem B5921849 : Blo 690315 5921849 := bstep (se 2 (by rfl) ⟨2220693, by rfl⟩ : syracuseStep 5921849 = 4441387) B4441387
theorem B1039481 : Blo 690315 1039481 := bstep (se 2 (by rfl) ⟨389805, by rfl⟩ : syracuseStep 1039481 = 779611) B779611
theorem B1039583 : Blo 690315 1039583 := bstep (se 1 (by rfl) ⟨779687, by rfl⟩ : syracuseStep 1039583 = 1559375) B1559375
theorem B1039625 : Blo 690315 1039625 := bstep (se 2 (by rfl) ⟨389859, by rfl⟩ : syracuseStep 1039625 = 779719) B779719
theorem B1170767 : Blo 690315 1170767 := bstep (se 1 (by rfl) ⟨878075, by rfl⟩ : syracuseStep 1170767 = 1756151) B1756151
theorem B1039727 : Blo 690315 1039727 := bstep (se 1 (by rfl) ⟨779795, by rfl⟩ : syracuseStep 1039727 = 1559591) B1559591
theorem B777703 : Blo 690315 777703 := bstep (se 1 (by rfl) ⟨583277, by rfl⟩ : syracuseStep 777703 = 1166555) B1166555
theorem B1039847 : Blo 690315 1039847 := bstep (se 1 (by rfl) ⟨779885, by rfl⟩ : syracuseStep 1039847 = 1559771) B1559771
theorem B1039979 : Blo 690315 1039979 := bstep (se 1 (by rfl) ⟨779984, by rfl⟩ : syracuseStep 1039979 = 1559969) B1559969
theorem B1040105 : Blo 690315 1040105 := bstep (se 2 (by rfl) ⟨390039, by rfl⟩ : syracuseStep 1040105 = 780079) B780079
theorem B876359 : Blo 690315 876359 := bstep (se 1 (by rfl) ⟨657269, by rfl⟩ : syracuseStep 876359 = 1314539) B1314539
theorem B1040249 : Blo 690315 1040249 := bstep (se 2 (by rfl) ⟨390093, by rfl⟩ : syracuseStep 1040249 = 780187) B780187
theorem B2809723 : Blo 690315 2809723 := bstep (se 1 (by rfl) ⟨2107292, by rfl⟩ : syracuseStep 2809723 = 4214585) B4214585
theorem B778207 : Blo 690315 778207 := bstep (se 1 (by rfl) ⟨583655, by rfl⟩ : syracuseStep 778207 = 1167311) B1167311
theorem B876511 : Blo 690315 876511 := bstep (se 1 (by rfl) ⟨657383, by rfl⟩ : syracuseStep 876511 = 1314767) B1314767
theorem B1040351 : Blo 690315 1040351 := bstep (se 1 (by rfl) ⟨780263, by rfl⟩ : syracuseStep 1040351 = 1560527) B1560527
theorem B19947491 : Blo 690315 19947491 := bstep (se 1 (by rfl) ⟨14960618, by rfl⟩ : syracuseStep 19947491 = 29921237) B29921237
theorem B1040603 : Blo 690315 1040603 := bstep (se 1 (by rfl) ⟨780452, by rfl⟩ : syracuseStep 1040603 = 1560905) B1560905
theorem B1040615 : Blo 690315 1040615 := bstep (se 1 (by rfl) ⟨780461, by rfl⟩ : syracuseStep 1040615 = 1560923) B1560923
theorem B9986435 : Blo 690315 9986435 := bstep (se 1 (by rfl) ⟨7489826, by rfl⟩ : syracuseStep 9986435 = 14979653) B14979653
theorem B1040777 : Blo 690315 1040777 := bstep (se 2 (by rfl) ⟨390291, by rfl⟩ : syracuseStep 1040777 = 780583) B780583
theorem B877007 : Blo 690315 877007 := bstep (se 1 (by rfl) ⟨657755, by rfl⟩ : syracuseStep 877007 = 1315511) B1315511
theorem B1040873 : Blo 690315 1040873 := bstep (se 2 (by rfl) ⟨390327, by rfl⟩ : syracuseStep 1040873 = 780655) B780655
theorem B15196673 : Blo 690315 15196673 := bstep (se 2 (by rfl) ⟨5698752, by rfl⟩ : syracuseStep 15196673 = 11397505) B11397505
theorem B15000065 : Blo 690315 15000065 := bstep (se 2 (by rfl) ⟨5625024, by rfl⟩ : syracuseStep 15000065 = 11250049) B11250049
theorem B6644243 : Blo 690315 6644243 := bstep (se 1 (by rfl) ⟨4983182, by rfl⟩ : syracuseStep 6644243 = 9966365) B9966365
theorem B778855 : Blo 690315 778855 := bstep (se 1 (by rfl) ⟨584141, by rfl⟩ : syracuseStep 778855 = 1168283) B1168283
theorem B877159 : Blo 690315 877159 := bstep (se 1 (by rfl) ⟨657869, by rfl⟩ : syracuseStep 877159 = 1315739) B1315739
theorem B1040999 : Blo 690315 1040999 := bstep (se 1 (by rfl) ⟨780749, by rfl⟩ : syracuseStep 1040999 = 1561499) B1561499
theorem B1041131 : Blo 690315 1041131 := bstep (se 1 (by rfl) ⟨780848, by rfl⟩ : syracuseStep 1041131 = 1561697) B1561697
theorem B2220797 : Blo 690315 2220797 := bstep (se 3 (by rfl) ⟨416399, by rfl⟩ : syracuseStep 2220797 = 832799) B832799
theorem B1663753 : Blo 690315 1663753 := bstep (se 2 (by rfl) ⟨623907, by rfl⟩ : syracuseStep 1663753 = 1247815) B1247815
theorem B1041161 : Blo 690315 1041161 := bstep (se 2 (by rfl) ⟨390435, by rfl⟩ : syracuseStep 1041161 = 780871) B780871
theorem B1041263 : Blo 690315 1041263 := bstep (se 1 (by rfl) ⟨780947, by rfl⟩ : syracuseStep 1041263 = 1561895) B1561895
theorem B40035221 : Blo 690315 40035221 := bstep (se 6 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 40035221 = 1876651) B1876651
theorem B4744145 : Blo 690315 4744145 := bstep (se 2 (by rfl) ⟨1779054, by rfl⟩ : syracuseStep 4744145 = 3558109) B3558109
theorem B1106939 : Blo 690315 1106939 := bstep (se 1 (by rfl) ⟨830204, by rfl⟩ : syracuseStep 1106939 = 1660409) B1660409
theorem B877979 : Blo 690315 877979 := bstep (se 1 (by rfl) ⟨658484, by rfl⟩ : syracuseStep 877979 = 1316969) B1316969
theorem B17754065 : Blo 690315 17754065 := bstep (se 2 (by rfl) ⟨6657774, by rfl⟩ : syracuseStep 17754065 = 13315549) B13315549
theorem B3991697 : Blo 690315 3991697 := bstep (se 2 (by rfl) ⟨1496886, by rfl⟩ : syracuseStep 3991697 = 2993773) B2993773
theorem B6646475 : Blo 690315 6646475 := bstep (se 1 (by rfl) ⟨4984856, by rfl⟩ : syracuseStep 6646475 = 9969713) B9969713
theorem B9988919 : Blo 690315 9988919 := bstep (se 1 (by rfl) ⟨7491689, by rfl⟩ : syracuseStep 9988919 = 14983379) B14983379
theorem B7465871 : Blo 690315 7465871 := bstep (se 1 (by rfl) ⟨5599403, by rfl⟩ : syracuseStep 7465871 = 11198807) B11198807
theorem B11234483 : Blo 690315 11234483 := bstep (se 1 (by rfl) ⟨8425862, by rfl⟩ : syracuseStep 11234483 = 16851725) B16851725
theorem B1994719 : Blo 690315 1994719 := bstep (se 1 (by rfl) ⟨1496039, by rfl⟩ : syracuseStep 1994719 = 2992079) B2992079
theorem B9990353 : Blo 690315 9990353 := bstep (se 2 (by rfl) ⟨3746382, by rfl⟩ : syracuseStep 9990353 = 7492765) B7492765
theorem B4485779 : Blo 690315 4485779 := bstep (se 1 (by rfl) ⟨3364334, by rfl⟩ : syracuseStep 4485779 = 6728669) B6728669
theorem B1405601 : Blo 690315 1405601 := bstep (se 2 (by rfl) ⟨527100, by rfl⟩ : syracuseStep 1405601 = 1054201) B1054201
theorem B1668203 : Blo 690315 1668203 := bstep (se 1 (by rfl) ⟨1251152, by rfl⟩ : syracuseStep 1668203 = 2502305) B2502305
theorem B3995345 : Blo 690315 3995345 := bstep (se 2 (by rfl) ⟨1498254, by rfl⟩ : syracuseStep 3995345 = 2996509) B2996509
theorem B5043923 : Blo 690315 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B1112039 : Blo 690315 1112039 := bstep (se 1 (by rfl) ⟨834029, by rfl⟩ : syracuseStep 1112039 = 1668059) B1668059
theorem B4749293 : Blo 690315 4749293 := bstep (se 3 (by rfl) ⟨890492, by rfl⟩ : syracuseStep 4749293 = 1780985) B1780985
theorem B7895069 : Blo 690315 7895069 := bstep (se 3 (by rfl) ⟨1480325, by rfl⟩ : syracuseStep 7895069 = 2960651) B2960651
theorem B41613749 : Blo 690315 41613749 := bstep (se 5 (by rfl) ⟨1950644, by rfl⟩ : syracuseStep 41613749 = 3901289) B3901289
theorem B2128403 : Blo 690315 2128403 := bstep (se 1 (by rfl) ⟨1596302, by rfl⟩ : syracuseStep 2128403 = 3192605) B3192605
theorem B3505193 : Blo 690315 3505193 := bstep (se 2 (by rfl) ⟨1314447, by rfl⟩ : syracuseStep 3505193 = 2628895) B2628895
theorem B1244527 : Blo 690315 1244527 := bstep (se 1 (by rfl) ⟨933395, by rfl⟩ : syracuseStep 1244527 = 1866791) B1866791
theorem B2948795 : Blo 690315 2948795 := bstep (se 1 (by rfl) ⟨2211596, by rfl⟩ : syracuseStep 2948795 = 4423193) B4423193
theorem B13337693 : Blo 690315 13337693 := bstep (se 3 (by rfl) ⟨2500817, by rfl⟩ : syracuseStep 13337693 = 5001635) B5001635
theorem B1311851 : Blo 690315 1311851 := bstep (se 1 (by rfl) ⟨983888, by rfl⟩ : syracuseStep 1311851 = 1967777) B1967777
theorem B2853025 : Blo 690315 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B690399 : Blo 690315 690399 := bstep (se 1 (by rfl) ⟨517799, by rfl⟩ : syracuseStep 690399 = 1035599) B1035599
theorem B690459 : Blo 690315 690459 := bstep (se 1 (by rfl) ⟨517844, by rfl⟩ : syracuseStep 690459 = 1035689) B1035689
theorem B690559 : Blo 690315 690559 := bstep (se 1 (by rfl) ⟨517919, by rfl⟩ : syracuseStep 690559 = 1035839) B1035839
theorem B1771903 : Blo 690315 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B1870295 : Blo 690315 1870295 := bstep (se 1 (by rfl) ⟨1402721, by rfl⟩ : syracuseStep 1870295 = 2805443) B2805443
theorem B690735 : Blo 690315 690735 := bstep (se 1 (by rfl) ⟨518051, by rfl⟩ : syracuseStep 690735 = 1036103) B1036103
theorem B690791 : Blo 690315 690791 := bstep (se 1 (by rfl) ⟨518093, by rfl⟩ : syracuseStep 690791 = 1036187) B1036187
theorem B4426397 : Blo 690315 4426397 := bstep (se 3 (by rfl) ⟨829949, by rfl⟩ : syracuseStep 4426397 = 1659899) B1659899
theorem B2624339 : Blo 690315 2624339 := bstep (se 1 (by rfl) ⟨1968254, by rfl⟩ : syracuseStep 2624339 = 3936509) B3936509
theorem B691167 : Blo 690315 691167 := bstep (se 1 (by rfl) ⟨518375, by rfl⟩ : syracuseStep 691167 = 1036751) B1036751
theorem B691195 : Blo 690315 691195 := bstep (se 1 (by rfl) ⟨518396, by rfl⟩ : syracuseStep 691195 = 1036793) B1036793
theorem B691263 : Blo 690315 691263 := bstep (se 1 (by rfl) ⟨518447, by rfl⟩ : syracuseStep 691263 = 1036895) B1036895
theorem B1772651 : Blo 690315 1772651 := bstep (se 1 (by rfl) ⟨1329488, by rfl⟩ : syracuseStep 1772651 = 2658977) B2658977
theorem B26938655 : Blo 690315 26938655 := bstep (se 1 (by rfl) ⟨20203991, by rfl⟩ : syracuseStep 26938655 = 40407983) B40407983
theorem B691583 : Blo 690315 691583 := bstep (se 1 (by rfl) ⟨518687, by rfl⟩ : syracuseStep 691583 = 1037375) B1037375
theorem B2952587 : Blo 690315 2952587 := bstep (se 1 (by rfl) ⟨2214440, by rfl⟩ : syracuseStep 2952587 = 4428881) B4428881
theorem B691611 : Blo 690315 691611 := bstep (se 1 (by rfl) ⟨518708, by rfl⟩ : syracuseStep 691611 = 1037417) B1037417
theorem B691679 : Blo 690315 691679 := bstep (se 1 (by rfl) ⟨518759, by rfl⟩ : syracuseStep 691679 = 1037519) B1037519
theorem B2624993 : Blo 690315 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B691815 : Blo 690315 691815 := bstep (se 1 (by rfl) ⟨518861, by rfl⟩ : syracuseStep 691815 = 1037723) B1037723
theorem B26611415 : Blo 690315 26611415 := bstep (se 1 (by rfl) ⟨19958561, by rfl⟩ : syracuseStep 26611415 = 39917123) B39917123
theorem B691963 : Blo 690315 691963 := bstep (se 1 (by rfl) ⟨518972, by rfl⟩ : syracuseStep 691963 = 1037945) B1037945
theorem B692031 : Blo 690315 692031 := bstep (se 1 (by rfl) ⟨519023, by rfl⟩ : syracuseStep 692031 = 1038047) B1038047
theorem B692095 : Blo 690315 692095 := bstep (se 1 (by rfl) ⟨519071, by rfl⟩ : syracuseStep 692095 = 1038143) B1038143
theorem B692207 : Blo 690315 692207 := bstep (se 1 (by rfl) ⟨519155, by rfl⟩ : syracuseStep 692207 = 1038311) B1038311
theorem B692219 : Blo 690315 692219 := bstep (se 1 (by rfl) ⟨519164, by rfl⟩ : syracuseStep 692219 = 1038329) B1038329
theorem B692287 : Blo 690315 692287 := bstep (se 1 (by rfl) ⟨519215, by rfl⟩ : syracuseStep 692287 = 1038431) B1038431
theorem B692327 : Blo 690315 692327 := bstep (se 1 (by rfl) ⟨519245, by rfl⟩ : syracuseStep 692327 = 1038491) B1038491
theorem B692351 : Blo 690315 692351 := bstep (se 1 (by rfl) ⟨519263, by rfl⟩ : syracuseStep 692351 = 1038527) B1038527
theorem B692379 : Blo 690315 692379 := bstep (se 1 (by rfl) ⟨519284, by rfl⟩ : syracuseStep 692379 = 1038569) B1038569
theorem B692583 : Blo 690315 692583 := bstep (se 1 (by rfl) ⟨519437, by rfl⟩ : syracuseStep 692583 = 1038875) B1038875
theorem B7868825 : Blo 690315 7868825 := bstep (se 2 (by rfl) ⟨2950809, by rfl⟩ : syracuseStep 7868825 = 5901619) B5901619
theorem B692635 : Blo 690315 692635 := bstep (se 1 (by rfl) ⟨519476, by rfl⟩ : syracuseStep 692635 = 1038953) B1038953
theorem B3936761 : Blo 690315 3936761 := bstep (se 2 (by rfl) ⟨1476285, by rfl⟩ : syracuseStep 3936761 = 2952571) B2952571
theorem B10654253 : Blo 690315 10654253 := bstep (se 3 (by rfl) ⟨1997672, by rfl⟩ : syracuseStep 10654253 = 3995345) B3995345
theorem B692987 : Blo 690315 692987 := bstep (se 1 (by rfl) ⟨519740, by rfl⟩ : syracuseStep 692987 = 1039481) B1039481
theorem B2331449 : Blo 690315 2331449 := bstep (se 2 (by rfl) ⟨874293, by rfl⟩ : syracuseStep 2331449 = 1748587) B1748587
theorem B693055 : Blo 690315 693055 := bstep (se 1 (by rfl) ⟨519791, by rfl⟩ : syracuseStep 693055 = 1039583) B1039583
theorem B693083 : Blo 690315 693083 := bstep (se 1 (by rfl) ⟨519812, by rfl⟩ : syracuseStep 693083 = 1039625) B1039625
theorem B693151 : Blo 690315 693151 := bstep (se 1 (by rfl) ⟨519863, by rfl⟩ : syracuseStep 693151 = 1039727) B1039727
theorem B693231 : Blo 690315 693231 := bstep (se 1 (by rfl) ⟨519923, by rfl⟩ : syracuseStep 693231 = 1039847) B1039847
theorem B693319 : Blo 690315 693319 := bstep (se 1 (by rfl) ⟨519989, by rfl⟩ : syracuseStep 693319 = 1039979) B1039979
theorem B693403 : Blo 690315 693403 := bstep (se 1 (by rfl) ⟨520052, by rfl⟩ : syracuseStep 693403 = 1040105) B1040105
theorem B693499 : Blo 690315 693499 := bstep (se 1 (by rfl) ⟨520124, by rfl⟩ : syracuseStep 693499 = 1040249) B1040249
theorem B2659625 : Blo 690315 2659625 := bstep (se 2 (by rfl) ⟨997359, by rfl⟩ : syracuseStep 2659625 = 1994719) B1994719
theorem B693567 : Blo 690315 693567 := bstep (se 1 (by rfl) ⟨520175, by rfl⟩ : syracuseStep 693567 = 1040351) B1040351
theorem B693735 : Blo 690315 693735 := bstep (se 1 (by rfl) ⟨520301, by rfl⟩ : syracuseStep 693735 = 1040603) B1040603
theorem B693743 : Blo 690315 693743 := bstep (se 1 (by rfl) ⟨520307, by rfl⟩ : syracuseStep 693743 = 1040615) B1040615
theorem B6657623 : Blo 690315 6657623 := bstep (se 1 (by rfl) ⟨4993217, by rfl⟩ : syracuseStep 6657623 = 9986435) B9986435
theorem B693851 : Blo 690315 693851 := bstep (se 1 (by rfl) ⟨520388, by rfl⟩ : syracuseStep 693851 = 1040777) B1040777
theorem B693915 : Blo 690315 693915 := bstep (se 1 (by rfl) ⟨520436, by rfl⟩ : syracuseStep 693915 = 1040873) B1040873
theorem B3741349 : Blo 690315 3741349 := bstep (se 4 (by rfl) ⟨350751, by rfl⟩ : syracuseStep 3741349 = 701503) B701503
theorem B10131115 : Blo 690315 10131115 := bstep (se 1 (by rfl) ⟨7598336, by rfl⟩ : syracuseStep 10131115 = 15196673) B15196673
theorem B10000043 : Blo 690315 10000043 := bstep (se 1 (by rfl) ⟨7500032, by rfl⟩ : syracuseStep 10000043 = 15000065) B15000065
theorem B4429495 : Blo 690315 4429495 := bstep (se 1 (by rfl) ⟨3322121, by rfl⟩ : syracuseStep 4429495 = 6644243) B6644243
theorem B2627255 : Blo 690315 2627255 := bstep (se 1 (by rfl) ⟨1970441, by rfl⟩ : syracuseStep 2627255 = 3940883) B3940883
theorem B693999 : Blo 690315 693999 := bstep (se 1 (by rfl) ⟨520499, by rfl⟩ : syracuseStep 693999 = 1040999) B1040999
theorem B694087 : Blo 690315 694087 := bstep (se 1 (by rfl) ⟨520565, by rfl⟩ : syracuseStep 694087 = 1041131) B1041131
theorem B1480531 : Blo 690315 1480531 := bstep (se 1 (by rfl) ⟨1110398, by rfl⟩ : syracuseStep 1480531 = 2220797) B2220797
theorem B694107 : Blo 690315 694107 := bstep (se 1 (by rfl) ⟨520580, by rfl⟩ : syracuseStep 694107 = 1041161) B1041161
theorem B1972127 : Blo 690315 1972127 := bstep (se 1 (by rfl) ⟨1479095, by rfl⟩ : syracuseStep 1972127 = 2958191) B2958191
theorem B694175 : Blo 690315 694175 := bstep (se 1 (by rfl) ⟨520631, by rfl⟩ : syracuseStep 694175 = 1041263) B1041263
theorem B8001641 : Blo 690315 8001641 := bstep (se 2 (by rfl) ⟨3000615, by rfl⟩ : syracuseStep 8001641 = 6001231) B6001231
theorem B1317151 : Blo 690315 1317151 := bstep (se 1 (by rfl) ⟨987863, by rfl⟩ : syracuseStep 1317151 = 1975727) B1975727
theorem B11836043 : Blo 690315 11836043 := bstep (se 1 (by rfl) ⟨8877032, by rfl⟩ : syracuseStep 11836043 = 17754065) B17754065
theorem B5675741 : Blo 690315 5675741 := bstep (se 3 (by rfl) ⟨1064201, by rfl⟩ : syracuseStep 5675741 = 2128403) B2128403
theorem B2661131 : Blo 690315 2661131 := bstep (se 1 (by rfl) ⟨1995848, by rfl⟩ : syracuseStep 2661131 = 3991697) B3991697
theorem B2628409 : Blo 690315 2628409 := bstep (se 2 (by rfl) ⟨985653, by rfl⟩ : syracuseStep 2628409 = 1971307) B1971307
theorem B4430983 : Blo 690315 4430983 := bstep (se 1 (by rfl) ⟨3323237, by rfl⟩ : syracuseStep 4430983 = 6646475) B6646475
theorem B6659279 : Blo 690315 6659279 := bstep (se 1 (by rfl) ⟨4994459, by rfl⟩ : syracuseStep 6659279 = 9988919) B9988919
theorem B6659621 : Blo 690315 6659621 := bstep (se 4 (by rfl) ⟨624339, by rfl⟩ : syracuseStep 6659621 = 1248679) B1248679
theorem B2629367 : Blo 690315 2629367 := bstep (se 1 (by rfl) ⟨1972025, by rfl⟩ : syracuseStep 2629367 = 3944051) B3944051
theorem B1974223 : Blo 690315 1974223 := bstep (se 1 (by rfl) ⟨1480667, by rfl⟩ : syracuseStep 1974223 = 2961335) B2961335
theorem B2957303 : Blo 690315 2957303 := bstep (se 1 (by rfl) ⟨2217977, by rfl⟩ : syracuseStep 2957303 = 4435955) B4435955
theorem B6660235 : Blo 690315 6660235 := bstep (se 1 (by rfl) ⟨4995176, by rfl⟩ : syracuseStep 6660235 = 9990353) B9990353
theorem B3154135 : Blo 690315 3154135 := bstep (se 1 (by rfl) ⟨2365601, by rfl⟩ : syracuseStep 3154135 = 4731203) B4731203
theorem B2957543 : Blo 690315 2957543 := bstep (se 1 (by rfl) ⟨2218157, by rfl⟩ : syracuseStep 2957543 = 4436315) B4436315
theorem B2990519 : Blo 690315 2990519 := bstep (se 1 (by rfl) ⟨2242889, by rfl⟩ : syracuseStep 2990519 = 4485779) B4485779
theorem B2630339 : Blo 690315 2630339 := bstep (se 1 (by rfl) ⟨1972754, by rfl⟩ : syracuseStep 2630339 = 3945509) B3945509
theorem B2368381 : Blo 690315 2368381 := bstep (se 3 (by rfl) ⟨444071, by rfl⟩ : syracuseStep 2368381 = 888143) B888143
theorem B8004595 : Blo 690315 8004595 := bstep (se 1 (by rfl) ⟨6003446, by rfl⟩ : syracuseStep 8004595 = 12006893) B12006893
theorem B3941885 : Blo 690315 3941885 := bstep (se 3 (by rfl) ⟨739103, by rfl⟩ : syracuseStep 3941885 = 1478207) B1478207
theorem B2336795 : Blo 690315 2336795 := bstep (se 1 (by rfl) ⟨1752596, by rfl⟩ : syracuseStep 2336795 = 3505193) B3505193
theorem B2336957 : Blo 690315 2336957 := bstep (se 3 (by rfl) ⟨438179, by rfl⟩ : syracuseStep 2336957 = 876359) B876359
theorem B2992457 : Blo 690315 2992457 := bstep (se 2 (by rfl) ⟨1122171, by rfl⟩ : syracuseStep 2992457 = 2244343) B2244343
theorem B3746297 : Blo 690315 3746297 := bstep (se 2 (by rfl) ⟨1404861, by rfl⟩ : syracuseStep 3746297 = 2809723) B2809723
theorem B8006215 : Blo 690315 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B5319431 : Blo 690315 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B1747919 : Blo 690315 1747919 := bstep (se 1 (by rfl) ⟨1310939, by rfl⟩ : syracuseStep 1747919 = 2621879) B2621879
theorem B1748243 : Blo 690315 1748243 := bstep (se 1 (by rfl) ⟨1311182, by rfl⟩ : syracuseStep 1748243 = 2622365) B2622365
theorem B4730687 : Blo 690315 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B2338685 : Blo 690315 2338685 := bstep (se 3 (by rfl) ⟨438503, by rfl⟩ : syracuseStep 2338685 = 877007) B877007
theorem B2338955 : Blo 690315 2338955 := bstep (se 1 (by rfl) ⟨1754216, by rfl⟩ : syracuseStep 2338955 = 3508433) B3508433
theorem B8008429 : Blo 690315 8008429 := bstep (se 3 (by rfl) ⟨1501580, by rfl⟩ : syracuseStep 8008429 = 3003161) B3003161
theorem B2437951 : Blo 690315 2437951 := bstep (se 1 (by rfl) ⟨1828463, by rfl⟩ : syracuseStep 2437951 = 3656927) B3656927
theorem B4436855 : Blo 690315 4436855 := bstep (se 1 (by rfl) ⟨3327641, by rfl⟩ : syracuseStep 4436855 = 6655283) B6655283
theorem B1553363 : Blo 690315 1553363 := bstep (se 1 (by rfl) ⟨1165022, by rfl⟩ : syracuseStep 1553363 = 2330045) B2330045
theorem B8893435 : Blo 690315 8893435 := bstep (se 1 (by rfl) ⟨6670076, by rfl⟩ : syracuseStep 8893435 = 13340153) B13340153
theorem B11809799 : Blo 690315 11809799 := bstep (se 1 (by rfl) ⟨8857349, by rfl⟩ : syracuseStep 11809799 = 17714699) B17714699
theorem B1553831 : Blo 690315 1553831 := bstep (se 1 (by rfl) ⟨1165373, by rfl⟩ : syracuseStep 1553831 = 2330747) B2330747
theorem B1553939 : Blo 690315 1553939 := bstep (se 1 (by rfl) ⟨1165454, by rfl⟩ : syracuseStep 1553939 = 2330909) B2330909
theorem B1554011 : Blo 690315 1554011 := bstep (se 1 (by rfl) ⟨1165508, by rfl⟩ : syracuseStep 1554011 = 2331017) B2331017
theorem B2340467 : Blo 690315 2340467 := bstep (se 1 (by rfl) ⟨1755350, by rfl⟩ : syracuseStep 2340467 = 3510701) B3510701
theorem B5617309 : Blo 690315 5617309 := bstep (se 3 (by rfl) ⟨1053245, by rfl⟩ : syracuseStep 5617309 = 2106491) B2106491
theorem B2340575 : Blo 690315 2340575 := bstep (se 1 (by rfl) ⟨1755431, by rfl⟩ : syracuseStep 2340575 = 3510863) B3510863
theorem B2635487 : Blo 690315 2635487 := bstep (se 1 (by rfl) ⟨1976615, by rfl⟩ : syracuseStep 2635487 = 3953231) B3953231
theorem B2799343 : Blo 690315 2799343 := bstep (se 1 (by rfl) ⟨2099507, by rfl⟩ : syracuseStep 2799343 = 4199015) B4199015
theorem B2340737 : Blo 690315 2340737 := bstep (se 2 (by rfl) ⟨877776, by rfl⟩ : syracuseStep 2340737 = 1755553) B1755553
theorem B1751179 : Blo 690315 1751179 := bstep (se 1 (by rfl) ⟨1313384, by rfl⟩ : syracuseStep 1751179 = 2626769) B2626769
theorem B1554623 : Blo 690315 1554623 := bstep (se 1 (by rfl) ⟨1165967, by rfl⟩ : syracuseStep 1554623 = 2331935) B2331935
theorem B3324199 : Blo 690315 3324199 := bstep (se 1 (by rfl) ⟨2493149, by rfl⟩ : syracuseStep 3324199 = 4986299) B4986299
theorem B2341277 : Blo 690315 2341277 := bstep (se 3 (by rfl) ⟨438989, by rfl⟩ : syracuseStep 2341277 = 877979) B877979
theorem B2341547 : Blo 690315 2341547 := bstep (se 1 (by rfl) ⟨1756160, by rfl⟩ : syracuseStep 2341547 = 3512321) B3512321
theorem B3324719 : Blo 690315 3324719 := bstep (se 1 (by rfl) ⟨2493539, by rfl⟩ : syracuseStep 3324719 = 4987079) B4987079
theorem B2341979 : Blo 690315 2341979 := bstep (se 1 (by rfl) ⟨1756484, by rfl⟩ : syracuseStep 2341979 = 3512969) B3512969
theorem B2342087 : Blo 690315 2342087 := bstep (se 1 (by rfl) ⟨1756565, by rfl⟩ : syracuseStep 2342087 = 3513131) B3513131
theorem B3947899 : Blo 690315 3947899 := bstep (se 1 (by rfl) ⟨2960924, by rfl⟩ : syracuseStep 3947899 = 5921849) B5921849
theorem B7978409 : Blo 690315 7978409 := bstep (se 2 (by rfl) ⟨2991903, by rfl⟩ : syracuseStep 7978409 = 5983807) B5983807
theorem B1555883 : Blo 690315 1555883 := bstep (se 1 (by rfl) ⟨1166912, by rfl⟩ : syracuseStep 1555883 = 2333825) B2333825
theorem B1555919 : Blo 690315 1555919 := bstep (se 1 (by rfl) ⟨1166939, by rfl⟩ : syracuseStep 1555919 = 2333879) B2333879
theorem B1752799 : Blo 690315 1752799 := bstep (se 1 (by rfl) ⟨1314599, by rfl⟩ : syracuseStep 1752799 = 2629199) B2629199
theorem B4505311 : Blo 690315 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B1556423 : Blo 690315 1556423 := bstep (se 1 (by rfl) ⟨1167317, by rfl⟩ : syracuseStep 1556423 = 2334635) B2334635
theorem B12664781 : Blo 690315 12664781 := bstep (se 3 (by rfl) ⟨2374646, by rfl⟩ : syracuseStep 12664781 = 4749293) B4749293
theorem B1556729 : Blo 690315 1556729 := bstep (se 2 (by rfl) ⟨583773, by rfl⟩ : syracuseStep 1556729 = 1167547) B1167547
theorem B1556783 : Blo 690315 1556783 := bstep (se 1 (by rfl) ⟨1167587, by rfl⟩ : syracuseStep 1556783 = 2335175) B2335175
theorem B18924029 : Blo 690315 18924029 := bstep (se 3 (by rfl) ⟨3548255, by rfl⟩ : syracuseStep 18924029 = 7096511) B7096511
theorem B1556999 : Blo 690315 1556999 := bstep (se 1 (by rfl) ⟨1167749, by rfl⟩ : syracuseStep 1556999 = 2335499) B2335499
theorem B26690147 : Blo 690315 26690147 := bstep (se 1 (by rfl) ⟨20017610, by rfl⟩ : syracuseStep 26690147 = 40035221) B40035221
theorem B3162763 : Blo 690315 3162763 := bstep (se 1 (by rfl) ⟨2372072, by rfl⟩ : syracuseStep 3162763 = 4744145) B4744145
theorem B737959 : Blo 690315 737959 := bstep (se 1 (by rfl) ⟨553469, by rfl⟩ : syracuseStep 737959 = 1106939) B1106939
theorem B1557179 : Blo 690315 1557179 := bstep (se 1 (by rfl) ⟨1167884, by rfl⟩ : syracuseStep 1557179 = 2335769) B2335769
theorem B1557611 : Blo 690315 1557611 := bstep (se 1 (by rfl) ⟨1168208, by rfl⟩ : syracuseStep 1557611 = 2336417) B2336417
theorem B1558079 : Blo 690315 1558079 := bstep (se 1 (by rfl) ⟨1168559, by rfl⟩ : syracuseStep 1558079 = 2337119) B2337119
theorem B1558187 : Blo 690315 1558187 := bstep (se 1 (by rfl) ⟨1168640, by rfl⟩ : syracuseStep 1558187 = 2337281) B2337281
theorem B6637477 : Blo 690315 6637477 := bstep (se 4 (by rfl) ⟨622263, by rfl⟩ : syracuseStep 6637477 = 1244527) B1244527
theorem B1558511 : Blo 690315 1558511 := bstep (se 1 (by rfl) ⟨1168883, by rfl⟩ : syracuseStep 1558511 = 2337767) B2337767
theorem B7489655 : Blo 690315 7489655 := bstep (se 1 (by rfl) ⟨5617241, by rfl⟩ : syracuseStep 7489655 = 11234483) B11234483
theorem B1558727 : Blo 690315 1558727 := bstep (se 1 (by rfl) ⟨1169045, by rfl⟩ : syracuseStep 1558727 = 2338091) B2338091
theorem B1558907 : Blo 690315 1558907 := bstep (se 1 (by rfl) ⟨1169180, by rfl⟩ : syracuseStep 1558907 = 2338361) B2338361
theorem B1165927 : Blo 690315 1165927 := bstep (se 1 (by rfl) ⟨874445, by rfl⟩ : syracuseStep 1165927 = 1748891) B1748891
theorem B1559177 : Blo 690315 1559177 := bstep (se 2 (by rfl) ⟨584691, by rfl⟩ : syracuseStep 1559177 = 1169383) B1169383
theorem B2214697 : Blo 690315 2214697 := bstep (se 2 (by rfl) ⟨830511, by rfl⟩ : syracuseStep 2214697 = 1661023) B1661023
theorem B1559465 : Blo 690315 1559465 := bstep (se 2 (by rfl) ⟨584799, by rfl⟩ : syracuseStep 1559465 = 1169599) B1169599
theorem B937067 : Blo 690315 937067 := bstep (se 1 (by rfl) ⟨702800, by rfl⟩ : syracuseStep 937067 = 1405601) B1405601
theorem B1035611 : Blo 690315 1035611 := bstep (se 1 (by rfl) ⟨776708, by rfl⟩ : syracuseStep 1035611 = 1553417) B1553417
theorem B1166683 : Blo 690315 1166683 := bstep (se 1 (by rfl) ⟨875012, by rfl⟩ : syracuseStep 1166683 = 1750025) B1750025
theorem B1035641 : Blo 690315 1035641 := bstep (se 2 (by rfl) ⟨388365, by rfl⟩ : syracuseStep 1035641 = 776731) B776731
theorem B1035647 : Blo 690315 1035647 := bstep (se 1 (by rfl) ⟨776735, by rfl⟩ : syracuseStep 1035647 = 1553471) B1553471
theorem B1560167 : Blo 690315 1560167 := bstep (se 1 (by rfl) ⟨1170125, by rfl⟩ : syracuseStep 1560167 = 2340251) B2340251
theorem B16010945 : Blo 690315 16010945 := bstep (se 2 (by rfl) ⟨6004104, by rfl⟩ : syracuseStep 16010945 = 12008209) B12008209
theorem B3362615 : Blo 690315 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B25546711 : Blo 690315 25546711 := bstep (se 1 (by rfl) ⟨19160033, by rfl⟩ : syracuseStep 25546711 = 38320067) B38320067
theorem B1036271 : Blo 690315 1036271 := bstep (se 1 (by rfl) ⟨777203, by rfl⟩ : syracuseStep 1036271 = 1554407) B1554407
theorem B741359 : Blo 690315 741359 := bstep (se 1 (by rfl) ⟨556019, by rfl⟩ : syracuseStep 741359 = 1112039) B1112039
theorem B1036283 : Blo 690315 1036283 := bstep (se 1 (by rfl) ⟨777212, by rfl⟩ : syracuseStep 1036283 = 1554425) B1554425
theorem B5263379 : Blo 690315 5263379 := bstep (se 1 (by rfl) ⟨3947534, by rfl⟩ : syracuseStep 5263379 = 7895069) B7895069
theorem B1036343 : Blo 690315 1036343 := bstep (se 1 (by rfl) ⟨777257, by rfl⟩ : syracuseStep 1036343 = 1554515) B1554515
theorem B1560671 : Blo 690315 1560671 := bstep (se 1 (by rfl) ⟨1170503, by rfl⟩ : syracuseStep 1560671 = 2341007) B2341007
theorem B1036391 : Blo 690315 1036391 := bstep (se 1 (by rfl) ⟨777293, by rfl⟩ : syracuseStep 1036391 = 1554587) B1554587
theorem B1036463 : Blo 690315 1036463 := bstep (se 1 (by rfl) ⟨777347, by rfl⟩ : syracuseStep 1036463 = 1554695) B1554695
theorem B27742499 : Blo 690315 27742499 := bstep (se 1 (by rfl) ⟨20806874, by rfl⟩ : syracuseStep 27742499 = 41613749) B41613749
theorem B1036667 : Blo 690315 1036667 := bstep (se 1 (by rfl) ⟨777500, by rfl⟩ : syracuseStep 1036667 = 1555001) B1555001
theorem B1036937 : Blo 690315 1036937 := bstep (se 2 (by rfl) ⟨388851, by rfl⟩ : syracuseStep 1036937 = 777703) B777703
theorem B1561427 : Blo 690315 1561427 := bstep (se 1 (by rfl) ⟨1171070, by rfl⟩ : syracuseStep 1561427 = 2342141) B2342141
theorem B1037147 : Blo 690315 1037147 := bstep (se 1 (by rfl) ⟨777860, by rfl⟩ : syracuseStep 1037147 = 1555721) B1555721
theorem B1037609 : Blo 690315 1037609 := bstep (se 2 (by rfl) ⟨389103, by rfl⟩ : syracuseStep 1037609 = 778207) B778207
theorem B1168681 : Blo 690315 1168681 := bstep (se 2 (by rfl) ⟨438255, by rfl⟩ : syracuseStep 1168681 = 876511) B876511
theorem B1561967 : Blo 690315 1561967 := bstep (se 1 (by rfl) ⟨1171475, by rfl⟩ : syracuseStep 1561967 = 2342951) B2342951
theorem B1037807 : Blo 690315 1037807 := bstep (se 1 (by rfl) ⟨778355, by rfl⟩ : syracuseStep 1037807 = 1556711) B1556711
theorem B1038203 : Blo 690315 1038203 := bstep (se 1 (by rfl) ⟨778652, by rfl⟩ : syracuseStep 1038203 = 1557305) B1557305
theorem B1169275 : Blo 690315 1169275 := bstep (se 1 (by rfl) ⟨876956, by rfl⟩ : syracuseStep 1169275 = 1753913) B1753913
theorem B1038239 : Blo 690315 1038239 := bstep (se 1 (by rfl) ⟨778679, by rfl⟩ : syracuseStep 1038239 = 1557359) B1557359
theorem B1497079 : Blo 690315 1497079 := bstep (se 1 (by rfl) ⟨1122809, by rfl⟩ : syracuseStep 1497079 = 2245619) B2245619
theorem B1038473 : Blo 690315 1038473 := bstep (se 2 (by rfl) ⟨389427, by rfl⟩ : syracuseStep 1038473 = 778855) B778855
theorem B1169545 : Blo 690315 1169545 := bstep (se 2 (by rfl) ⟨438579, by rfl⟩ : syracuseStep 1169545 = 877159) B877159
theorem B1661215 : Blo 690315 1661215 := bstep (se 1 (by rfl) ⟨1245911, by rfl⟩ : syracuseStep 1661215 = 2491823) B2491823
theorem B1038623 : Blo 690315 1038623 := bstep (se 1 (by rfl) ⟨778967, by rfl⟩ : syracuseStep 1038623 = 1557935) B1557935
theorem B2218337 : Blo 690315 2218337 := bstep (se 2 (by rfl) ⟨831876, by rfl⟩ : syracuseStep 2218337 = 1663753) B1663753
theorem B3562055 : Blo 690315 3562055 := bstep (se 1 (by rfl) ⟨2671541, by rfl⟩ : syracuseStep 3562055 = 5343083) B5343083
theorem B75979457 : Blo 690315 75979457 := bstep (se 2 (by rfl) ⟨28492296, by rfl⟩ : syracuseStep 75979457 = 56984593) B56984593
theorem B1661753 : Blo 690315 1661753 := bstep (se 2 (by rfl) ⟨623157, by rfl⟩ : syracuseStep 1661753 = 1246315) B1246315
theorem B1039175 : Blo 690315 1039175 := bstep (se 1 (by rfl) ⟨779381, by rfl⟩ : syracuseStep 1039175 = 1558763) B1558763
theorem B1170247 : Blo 690315 1170247 := bstep (se 1 (by rfl) ⟨877685, by rfl⟩ : syracuseStep 1170247 = 1755371) B1755371
theorem B875387 : Blo 690315 875387 := bstep (se 1 (by rfl) ⟨656540, by rfl⟩ : syracuseStep 875387 = 1313081) B1313081
theorem B777127 : Blo 690315 777127 := bstep (se 1 (by rfl) ⟨582845, by rfl⟩ : syracuseStep 777127 = 1165691) B1165691
theorem B777307 : Blo 690315 777307 := bstep (se 1 (by rfl) ⟨582980, by rfl⟩ : syracuseStep 777307 = 1165961) B1165961
theorem B1040039 : Blo 690315 1040039 := bstep (se 1 (by rfl) ⟨780029, by rfl⟩ : syracuseStep 1040039 = 1560059) B1560059
theorem B1171111 : Blo 690315 1171111 := bstep (se 1 (by rfl) ⟨878333, by rfl⟩ : syracuseStep 1171111 = 1756667) B1756667
theorem B1040159 : Blo 690315 1040159 := bstep (se 1 (by rfl) ⟨780119, by rfl⟩ : syracuseStep 1040159 = 1560239) B1560239
theorem B8314807 : Blo 690315 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B1040591 : Blo 690315 1040591 := bstep (se 1 (by rfl) ⟨780443, by rfl⟩ : syracuseStep 1040591 = 1560887) B1560887
theorem B778495 : Blo 690315 778495 := bstep (se 1 (by rfl) ⟨583871, by rfl⟩ : syracuseStep 778495 = 1167743) B1167743
theorem B1040639 : Blo 690315 1040639 := bstep (se 1 (by rfl) ⟨780479, by rfl⟩ : syracuseStep 1040639 = 1560959) B1560959
theorem B778783 : Blo 690315 778783 := bstep (se 1 (by rfl) ⟨584087, by rfl⟩ : syracuseStep 778783 = 1168175) B1168175
theorem B8413793 : Blo 690315 8413793 := bstep (se 2 (by rfl) ⟨3155172, by rfl⟩ : syracuseStep 8413793 = 6310345) B6310345
theorem B1041455 : Blo 690315 1041455 := bstep (se 1 (by rfl) ⟨781091, by rfl⟩ : syracuseStep 1041455 = 1562183) B1562183
theorem B779431 : Blo 690315 779431 := bstep (se 1 (by rfl) ⟨584573, by rfl⟩ : syracuseStep 779431 = 1169147) B1169147
theorem B1402169 : Blo 690315 1402169 := bstep (se 2 (by rfl) ⟨525813, by rfl⟩ : syracuseStep 1402169 = 1051627) B1051627
theorem B1402267 : Blo 690315 1402267 := bstep (se 1 (by rfl) ⟨1051700, by rfl⟩ : syracuseStep 1402267 = 2103401) B2103401
theorem B5924447 : Blo 690315 5924447 := bstep (se 1 (by rfl) ⟨4443335, by rfl⟩ : syracuseStep 5924447 = 8886671) B8886671
theorem B11822921 : Blo 690315 11822921 := bstep (se 2 (by rfl) ⟨4433595, by rfl⟩ : syracuseStep 11822921 = 8867191) B8867191
theorem B780223 : Blo 690315 780223 := bstep (se 1 (by rfl) ⟨585167, by rfl⟩ : syracuseStep 780223 = 1170335) B1170335
theorem B5629931 : Blo 690315 5629931 := bstep (se 1 (by rfl) ⟨4222448, by rfl⟩ : syracuseStep 5629931 = 8444897) B8444897
theorem B780511 : Blo 690315 780511 := bstep (se 1 (by rfl) ⟨585383, by rfl⟩ : syracuseStep 780511 = 1170767) B1170767
theorem B1108361 : Blo 690315 1108361 := bstep (se 2 (by rfl) ⟨415635, by rfl⟩ : syracuseStep 1108361 = 831271) B831271
theorem B13298327 : Blo 690315 13298327 := bstep (se 1 (by rfl) ⟨9973745, by rfl⟩ : syracuseStep 13298327 = 19947491) B19947491
theorem B1667155 : Blo 690315 1667155 := bstep (se 1 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 1667155 = 2500733) B2500733
theorem B4977247 : Blo 690315 4977247 := bstep (se 1 (by rfl) ⟨3732935, by rfl⟩ : syracuseStep 4977247 = 7465871) B7465871
theorem B6320855 : Blo 690315 6320855 := bstep (se 1 (by rfl) ⟨4740641, by rfl⟩ : syracuseStep 6320855 = 9481283) B9481283
theorem B7108667 : Blo 690315 7108667 := bstep (se 1 (by rfl) ⟨5331500, by rfl⟩ : syracuseStep 7108667 = 10663001) B10663001
theorem B1112135 : Blo 690315 1112135 := bstep (se 1 (by rfl) ⟨834101, by rfl⟩ : syracuseStep 1112135 = 1668203) B1668203
theorem B12614267 : Blo 690315 12614267 := bstep (se 1 (by rfl) ⟨9460700, by rfl⟩ : syracuseStep 12614267 = 18921401) B18921401
theorem B1965863 : Blo 690315 1965863 := bstep (se 1 (by rfl) ⟨1474397, by rfl⟩ : syracuseStep 1965863 = 2948795) B2948795
theorem B9994043 : Blo 690315 9994043 := bstep (se 1 (by rfl) ⟨7495532, by rfl⟩ : syracuseStep 9994043 = 14991065) B14991065
theorem B5603197 : Blo 690315 5603197 := bstep (se 3 (by rfl) ⟨1050599, by rfl⟩ : syracuseStep 5603197 = 2101199) B2101199
theorem B8880313 : Blo 690315 8880313 := bstep (se 2 (by rfl) ⟨3330117, by rfl⟩ : syracuseStep 8880313 = 6660235) B6660235
theorem B12616019 : Blo 690315 12616019 := bstep (se 1 (by rfl) ⟨9462014, by rfl⟩ : syracuseStep 12616019 = 18924029) B18924029
theorem B17793431 : Blo 690315 17793431 := bstep (se 1 (by rfl) ⟨13345073, by rfl⟩ : syracuseStep 17793431 = 26690147) B26690147
theorem B983945 : Blo 690315 983945 := bstep (se 2 (by rfl) ⟨368979, by rfl⟩ : syracuseStep 983945 = 737959) B737959
theorem B2950931 : Blo 690315 2950931 := bstep (se 1 (by rfl) ⟨2213198, by rfl⟩ : syracuseStep 2950931 = 4426397) B4426397
theorem B1869689 : Blo 690315 1869689 := bstep (se 2 (by rfl) ⟨701133, by rfl⟩ : syracuseStep 1869689 = 1402267) B1402267
theorem B17959103 : Blo 690315 17959103 := bstep (se 1 (by rfl) ⟨13469327, by rfl⟩ : syracuseStep 17959103 = 26938655) B26938655
theorem B690407 : Blo 690315 690407 := bstep (se 1 (by rfl) ⟨517805, by rfl⟩ : syracuseStep 690407 = 1035611) B1035611
theorem B690427 : Blo 690315 690427 := bstep (se 1 (by rfl) ⟨517820, by rfl⟩ : syracuseStep 690427 = 1035641) B1035641
theorem B690431 : Blo 690315 690431 := bstep (se 1 (by rfl) ⟨517823, by rfl⟩ : syracuseStep 690431 = 1035647) B1035647
theorem B1968391 : Blo 690315 1968391 := bstep (se 1 (by rfl) ⟨1476293, by rfl⟩ : syracuseStep 1968391 = 2952587) B2952587
theorem B8849969 : Blo 690315 8849969 := bstep (se 2 (by rfl) ⟨3318738, by rfl⟩ : syracuseStep 8849969 = 6637477) B6637477
theorem B690847 : Blo 690315 690847 := bstep (se 1 (by rfl) ⟨518135, by rfl⟩ : syracuseStep 690847 = 1036271) B1036271
theorem B690855 : Blo 690315 690855 := bstep (se 1 (by rfl) ⟨518141, by rfl⟩ : syracuseStep 690855 = 1036283) B1036283
theorem B3508919 : Blo 690315 3508919 := bstep (se 1 (by rfl) ⟨2631689, by rfl⟩ : syracuseStep 3508919 = 5263379) B5263379
theorem B690895 : Blo 690315 690895 := bstep (se 1 (by rfl) ⟨518171, by rfl⟩ : syracuseStep 690895 = 1036343) B1036343
theorem B690927 : Blo 690315 690927 := bstep (se 1 (by rfl) ⟨518195, by rfl⟩ : syracuseStep 690927 = 1036391) B1036391
theorem B690975 : Blo 690315 690975 := bstep (se 1 (by rfl) ⟨518231, by rfl⟩ : syracuseStep 690975 = 1036463) B1036463
theorem B691111 : Blo 690315 691111 := bstep (se 1 (by rfl) ⟨518333, by rfl⟩ : syracuseStep 691111 = 1036667) B1036667
theorem B5245883 : Blo 690315 5245883 := bstep (se 1 (by rfl) ⟨3934412, by rfl⟩ : syracuseStep 5245883 = 7868825) B7868825
theorem B2624507 : Blo 690315 2624507 := bstep (se 1 (by rfl) ⟨1968380, by rfl⟩ : syracuseStep 2624507 = 3936761) B3936761
theorem B691291 : Blo 690315 691291 := bstep (se 1 (by rfl) ⟨518468, by rfl⟩ : syracuseStep 691291 = 1036937) B1036937
theorem B2362537 : Blo 690315 2362537 := bstep (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) B1771903
theorem B691431 : Blo 690315 691431 := bstep (se 1 (by rfl) ⟨518573, by rfl⟩ : syracuseStep 691431 = 1037147) B1037147
theorem B3739117 : Blo 690315 3739117 := bstep (se 3 (by rfl) ⟨701084, by rfl⟩ : syracuseStep 3739117 = 1402169) B1402169
theorem B1773083 : Blo 690315 1773083 := bstep (se 1 (by rfl) ⟨1329812, by rfl⟩ : syracuseStep 1773083 = 2659625) B2659625
theorem B691739 : Blo 690315 691739 := bstep (se 1 (by rfl) ⟨518804, by rfl⟩ : syracuseStep 691739 = 1037609) B1037609
theorem B691871 : Blo 690315 691871 := bstep (se 1 (by rfl) ⟨518903, by rfl⟩ : syracuseStep 691871 = 1037807) B1037807
theorem B2952929 : Blo 690315 2952929 := bstep (se 2 (by rfl) ⟨1107348, by rfl⟩ : syracuseStep 2952929 = 2214697) B2214697
theorem B692135 : Blo 690315 692135 := bstep (se 1 (by rfl) ⟨519101, by rfl⟩ : syracuseStep 692135 = 1038203) B1038203
theorem B692159 : Blo 690315 692159 := bstep (se 1 (by rfl) ⟨519119, by rfl⟩ : syracuseStep 692159 = 1038239) B1038239
theorem B692315 : Blo 690315 692315 := bstep (se 1 (by rfl) ⟨519236, by rfl⟩ : syracuseStep 692315 = 1038473) B1038473
theorem B692415 : Blo 690315 692415 := bstep (se 1 (by rfl) ⟨519311, by rfl⟩ : syracuseStep 692415 = 1038623) B1038623
theorem B1478891 : Blo 690315 1478891 := bstep (se 1 (by rfl) ⟨1109168, by rfl⟩ : syracuseStep 1478891 = 2218337) B2218337
theorem B692783 : Blo 690315 692783 := bstep (se 1 (by rfl) ⟨519587, by rfl⟩ : syracuseStep 692783 = 1039175) B1039175
theorem B693359 : Blo 690315 693359 := bstep (se 1 (by rfl) ⟨520019, by rfl⟩ : syracuseStep 693359 = 1040039) B1040039
theorem B693439 : Blo 690315 693439 := bstep (se 1 (by rfl) ⟨520079, by rfl⟩ : syracuseStep 693439 = 1040159) B1040159
theorem B1971535 : Blo 690315 1971535 := bstep (se 1 (by rfl) ⟨1478651, by rfl⟩ : syracuseStep 1971535 = 2957303) B2957303
theorem B693727 : Blo 690315 693727 := bstep (se 1 (by rfl) ⟨520295, by rfl⟩ : syracuseStep 693727 = 1040591) B1040591
theorem B1971695 : Blo 690315 1971695 := bstep (se 1 (by rfl) ⟨1478771, by rfl⟩ : syracuseStep 1971695 = 2957543) B2957543
theorem B693759 : Blo 690315 693759 := bstep (se 1 (by rfl) ⟨520319, by rfl⟩ : syracuseStep 693759 = 1040639) B1040639
theorem B5609195 : Blo 690315 5609195 := bstep (se 1 (by rfl) ⟨4206896, by rfl⟩ : syracuseStep 5609195 = 8413793) B8413793
theorem B694303 : Blo 690315 694303 := bstep (se 1 (by rfl) ⟨520727, by rfl⟩ : syracuseStep 694303 = 1041455) B1041455
theorem B2627923 : Blo 690315 2627923 := bstep (se 1 (by rfl) ⟨1970942, by rfl⟩ : syracuseStep 2627923 = 3941885) B3941885
theorem B2955629 : Blo 690315 2955629 := bstep (se 3 (by rfl) ⟨554180, by rfl⟩ : syracuseStep 2955629 = 1108361) B1108361
theorem B3250601 : Blo 690315 3250601 := bstep (se 2 (by rfl) ⟨1218975, by rfl⟩ : syracuseStep 3250601 = 2437951) B2437951
theorem B4987453 : Blo 690315 4987453 := bstep (se 3 (by rfl) ⟨935147, by rfl⟩ : syracuseStep 4987453 = 1870295) B1870295
theorem B3546287 : Blo 690315 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B4431341 : Blo 690315 4431341 := bstep (se 3 (by rfl) ⟨830876, by rfl⟩ : syracuseStep 4431341 = 1661753) B1661753
theorem B4988465 : Blo 690315 4988465 := bstep (se 2 (by rfl) ⟨1870674, by rfl⟩ : syracuseStep 4988465 = 3741349) B3741349
theorem B13508153 : Blo 690315 13508153 := bstep (se 2 (by rfl) ⟨5065557, by rfl⟩ : syracuseStep 13508153 = 10131115) B10131115
theorem B5905993 : Blo 690315 5905993 := bstep (se 2 (by rfl) ⟨2214747, by rfl⟩ : syracuseStep 5905993 = 4429495) B4429495
theorem B2334365 : Blo 690315 2334365 := bstep (se 3 (by rfl) ⟨437693, by rfl⟩ : syracuseStep 2334365 = 875387) B875387
theorem B1974041 : Blo 690315 1974041 := bstep (se 2 (by rfl) ⟨740265, by rfl⟩ : syracuseStep 1974041 = 1480531) B1480531
theorem B3153791 : Blo 690315 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B2334905 : Blo 690315 2334905 := bstep (se 2 (by rfl) ⟨875589, by rfl⟩ : syracuseStep 2334905 = 1751179) B1751179
theorem B4727069 : Blo 690315 4727069 := bstep (se 3 (by rfl) ⟨886325, by rfl⟩ : syracuseStep 4727069 = 1772651) B1772651
theorem B2498845 : Blo 690315 2498845 := bstep (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) B937067
theorem B4432265 : Blo 690315 4432265 := bstep (se 2 (by rfl) ⟨1662099, by rfl⟩ : syracuseStep 4432265 = 3324199) B3324199
theorem B2957903 : Blo 690315 2957903 := bstep (se 1 (by rfl) ⟨2218427, by rfl⟩ : syracuseStep 2957903 = 4436855) B4436855
theorem B7873199 : Blo 690315 7873199 := bstep (se 1 (by rfl) ⟨5904899, by rfl⟩ : syracuseStep 7873199 = 11809799) B11809799
theorem B5907977 : Blo 690315 5907977 := bstep (se 2 (by rfl) ⟨2215491, by rfl⟩ : syracuseStep 5907977 = 4430983) B4430983
theorem B26650781 : Blo 690315 26650781 := bstep (se 3 (by rfl) ⟨4997021, by rfl⟩ : syracuseStep 26650781 = 9994043) B9994043
theorem B5318939 : Blo 690315 5318939 := bstep (se 1 (by rfl) ⟨3989204, by rfl⟩ : syracuseStep 5318939 = 7978409) B7978409
theorem B2337065 : Blo 690315 2337065 := bstep (se 2 (by rfl) ⟨876399, by rfl⟩ : syracuseStep 2337065 = 1752799) B1752799
theorem B6007081 : Blo 690315 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B11086409 : Blo 690315 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B2632297 : Blo 690315 2632297 := bstep (se 2 (by rfl) ⟨987111, by rfl⟩ : syracuseStep 2632297 = 1974223) B1974223
theorem B1976957 : Blo 690315 1976957 := bstep (se 3 (by rfl) ⟨370679, by rfl⟩ : syracuseStep 1976957 = 741359) B741359
theorem B4205513 : Blo 690315 4205513 := bstep (se 2 (by rfl) ⟨1577067, by rfl⟩ : syracuseStep 4205513 = 3154135) B3154135
theorem B8891795 : Blo 690315 8891795 := bstep (se 1 (by rfl) ⟨6668846, by rfl⟩ : syracuseStep 8891795 = 13337693) B13337693
theorem B15216133 : Blo 690315 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B3157841 : Blo 690315 3157841 := bstep (se 2 (by rfl) ⟨1184190, by rfl⟩ : syracuseStep 3157841 = 2368381) B2368381
theorem B4993103 : Blo 690315 4993103 := bstep (se 1 (by rfl) ⟨3744827, by rfl⟩ : syracuseStep 4993103 = 7489655) B7489655
theorem B1749559 : Blo 690315 1749559 := bstep (se 1 (by rfl) ⟨1312169, by rfl⟩ : syracuseStep 1749559 = 2624339) B2624339
theorem B143471573 : Blo 690315 143471573 := bstep (se 7 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 143471573 = 3362615) B3362615
theorem B1749995 : Blo 690315 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B17740943 : Blo 690315 17740943 := bstep (se 1 (by rfl) ⟨13305707, by rfl⟩ : syracuseStep 17740943 = 26611415) B26611415
theorem B18494999 : Blo 690315 18494999 := bstep (se 1 (by rfl) ⟨13871249, by rfl⟩ : syracuseStep 18494999 = 27742499) B27742499
theorem B1554299 : Blo 690315 1554299 := bstep (se 1 (by rfl) ⟨1165724, by rfl⟩ : syracuseStep 1554299 = 2331449) B2331449
theorem B1554569 : Blo 690315 1554569 := bstep (se 2 (by rfl) ⟨582963, by rfl⟩ : syracuseStep 1554569 = 1165927) B1165927
theorem B4438415 : Blo 690315 4438415 := bstep (se 1 (by rfl) ⟨3328811, by rfl⟩ : syracuseStep 4438415 = 6657623) B6657623
theorem B6666695 : Blo 690315 6666695 := bstep (se 1 (by rfl) ⟨5000021, by rfl⟩ : syracuseStep 6666695 = 10000043) B10000043
theorem B1751503 : Blo 690315 1751503 := bstep (se 1 (by rfl) ⟨1313627, by rfl⟩ : syracuseStep 1751503 = 2627255) B2627255
theorem B2374703 : Blo 690315 2374703 := bstep (se 1 (by rfl) ⟨1781027, by rfl⟩ : syracuseStep 2374703 = 3562055) B3562055
theorem B1555577 : Blo 690315 1555577 := bstep (se 2 (by rfl) ⟨583341, by rfl⟩ : syracuseStep 1555577 = 1166683) B1166683
theorem B3783827 : Blo 690315 3783827 := bstep (se 1 (by rfl) ⟨2837870, by rfl⟩ : syracuseStep 3783827 = 5675741) B5675741
theorem B4439519 : Blo 690315 4439519 := bstep (se 1 (by rfl) ⟨3329639, by rfl⟩ : syracuseStep 4439519 = 6659279) B6659279
theorem B4439747 : Blo 690315 4439747 := bstep (se 1 (by rfl) ⟨3329810, by rfl⟩ : syracuseStep 4439747 = 6659621) B6659621
theorem B5259005 : Blo 690315 5259005 := bstep (se 3 (by rfl) ⟨986063, by rfl⟩ : syracuseStep 5259005 = 1972127) B1972127
theorem B1752911 : Blo 690315 1752911 := bstep (se 1 (by rfl) ⟨1314683, by rfl⟩ : syracuseStep 1752911 = 2629367) B2629367
theorem B34062281 : Blo 690315 34062281 := bstep (se 2 (by rfl) ⟨12773355, by rfl⟩ : syracuseStep 34062281 = 25546711) B25546711
theorem B2965693 : Blo 690315 2965693 := bstep (se 3 (by rfl) ⟨556067, by rfl⟩ : syracuseStep 2965693 = 1112135) B1112135
theorem B1753559 : Blo 690315 1753559 := bstep (se 1 (by rfl) ⟨1315169, by rfl⟩ : syracuseStep 1753559 = 2630339) B2630339
theorem B6636329 : Blo 690315 6636329 := bstep (se 2 (by rfl) ⟨2488623, by rfl⟩ : syracuseStep 6636329 = 4977247) B4977247
theorem B3949631 : Blo 690315 3949631 := bstep (se 1 (by rfl) ⟨2962223, by rfl⟩ : syracuseStep 3949631 = 5924447) B5924447
theorem B7881947 : Blo 690315 7881947 := bstep (se 1 (by rfl) ⟨5911460, by rfl⟩ : syracuseStep 7881947 = 11822921) B11822921
theorem B3753287 : Blo 690315 3753287 := bstep (se 1 (by rfl) ⟨2814965, by rfl⟩ : syracuseStep 3753287 = 5629931) B5629931
theorem B1557863 : Blo 690315 1557863 := bstep (se 1 (by rfl) ⟨1168397, by rfl⟩ : syracuseStep 1557863 = 2336795) B2336795
theorem B1557971 : Blo 690315 1557971 := bstep (se 1 (by rfl) ⟨1168478, by rfl⟩ : syracuseStep 1557971 = 2336957) B2336957
theorem B1558241 : Blo 690315 1558241 := bstep (se 2 (by rfl) ⟨584340, by rfl⟩ : syracuseStep 1558241 = 1168681) B1168681
theorem B8865551 : Blo 690315 8865551 := bstep (se 1 (by rfl) ⟨6649163, by rfl⟩ : syracuseStep 8865551 = 13298327) B13298327
theorem B1165279 : Blo 690315 1165279 := bstep (se 1 (by rfl) ⟨873959, by rfl⟩ : syracuseStep 1165279 = 1747919) B1747919
theorem B7096349 : Blo 690315 7096349 := bstep (se 3 (by rfl) ⟨1330565, by rfl⟩ : syracuseStep 7096349 = 2661131) B2661131
theorem B1165495 : Blo 690315 1165495 := bstep (se 1 (by rfl) ⟨874121, by rfl⟩ : syracuseStep 1165495 = 1748243) B1748243
theorem B7489745 : Blo 690315 7489745 := bstep (se 2 (by rfl) ⟨2808654, by rfl⟩ : syracuseStep 7489745 = 5617309) B5617309
theorem B1559033 : Blo 690315 1559033 := bstep (se 2 (by rfl) ⟨584637, by rfl⟩ : syracuseStep 1559033 = 1169275) B1169275
theorem B1559123 : Blo 690315 1559123 := bstep (se 1 (by rfl) ⟨1169342, by rfl⟩ : syracuseStep 1559123 = 2338685) B2338685
theorem B1559303 : Blo 690315 1559303 := bstep (se 1 (by rfl) ⟨1169477, by rfl⟩ : syracuseStep 1559303 = 2338955) B2338955
theorem B1559393 : Blo 690315 1559393 := bstep (se 2 (by rfl) ⟨584772, by rfl⟩ : syracuseStep 1559393 = 1169545) B1169545
theorem B2214953 : Blo 690315 2214953 := bstep (se 2 (by rfl) ⟨830607, by rfl⟩ : syracuseStep 2214953 = 1661215) B1661215
theorem B1756201 : Blo 690315 1756201 := bstep (se 2 (by rfl) ⟨658575, by rfl⟩ : syracuseStep 1756201 = 1317151) B1317151
theorem B4213903 : Blo 690315 4213903 := bstep (se 1 (by rfl) ⟨3160427, by rfl⟩ : syracuseStep 4213903 = 6320855) B6320855
theorem B1035575 : Blo 690315 1035575 := bstep (se 1 (by rfl) ⟨776681, by rfl⟩ : syracuseStep 1035575 = 1553363) B1553363
theorem B1035887 : Blo 690315 1035887 := bstep (se 1 (by rfl) ⟨776915, by rfl⟩ : syracuseStep 1035887 = 1553831) B1553831
theorem B1035959 : Blo 690315 1035959 := bstep (se 1 (by rfl) ⟨776969, by rfl⟩ : syracuseStep 1035959 = 1553939) B1553939
theorem B1036007 : Blo 690315 1036007 := bstep (se 1 (by rfl) ⟨777005, by rfl⟩ : syracuseStep 1036007 = 1554011) B1554011
theorem B1560311 : Blo 690315 1560311 := bstep (se 1 (by rfl) ⟨1170233, by rfl⟩ : syracuseStep 1560311 = 2340467) B2340467
theorem B1560329 : Blo 690315 1560329 := bstep (se 2 (by rfl) ⟨585123, by rfl⟩ : syracuseStep 1560329 = 1170247) B1170247
theorem B1560383 : Blo 690315 1560383 := bstep (se 1 (by rfl) ⟨1170287, by rfl⟩ : syracuseStep 1560383 = 2340575) B2340575
theorem B1756991 : Blo 690315 1756991 := bstep (se 1 (by rfl) ⟨1317743, by rfl⟩ : syracuseStep 1756991 = 2635487) B2635487
theorem B1036169 : Blo 690315 1036169 := bstep (se 2 (by rfl) ⟨388563, by rfl⟩ : syracuseStep 1036169 = 777127) B777127
theorem B14929829 : Blo 690315 14929829 := bstep (se 4 (by rfl) ⟨1399671, by rfl⟩ : syracuseStep 14929829 = 2799343) B2799343
theorem B1560491 : Blo 690315 1560491 := bstep (se 1 (by rfl) ⟨1170368, by rfl⟩ : syracuseStep 1560491 = 2340737) B2340737
theorem B4739111 : Blo 690315 4739111 := bstep (se 1 (by rfl) ⟨3554333, by rfl⟩ : syracuseStep 4739111 = 7108667) B7108667
theorem B1036409 : Blo 690315 1036409 := bstep (se 2 (by rfl) ⟨388653, by rfl⟩ : syracuseStep 1036409 = 777307) B777307
theorem B1036415 : Blo 690315 1036415 := bstep (se 1 (by rfl) ⟨777311, by rfl⟩ : syracuseStep 1036415 = 1554623) B1554623
theorem B1560851 : Blo 690315 1560851 := bstep (se 1 (by rfl) ⟨1170638, by rfl⟩ : syracuseStep 1560851 = 2341277) B2341277
theorem B8409511 : Blo 690315 8409511 := bstep (se 1 (by rfl) ⟨6307133, by rfl⟩ : syracuseStep 8409511 = 12614267) B12614267
theorem B1561031 : Blo 690315 1561031 := bstep (se 1 (by rfl) ⟨1170773, by rfl⟩ : syracuseStep 1561031 = 2341547) B2341547
theorem B5263865 : Blo 690315 5263865 := bstep (se 2 (by rfl) ⟨1973949, by rfl⟩ : syracuseStep 5263865 = 3947899) B3947899
theorem B2216479 : Blo 690315 2216479 := bstep (se 1 (by rfl) ⟨1662359, by rfl⟩ : syracuseStep 2216479 = 3324719) B3324719
theorem B1561319 : Blo 690315 1561319 := bstep (se 1 (by rfl) ⟨1170989, by rfl⟩ : syracuseStep 1561319 = 2341979) B2341979
theorem B1561391 : Blo 690315 1561391 := bstep (se 1 (by rfl) ⟨1171043, by rfl⟩ : syracuseStep 1561391 = 2342087) B2342087
theorem B1561481 : Blo 690315 1561481 := bstep (se 2 (by rfl) ⟨585555, by rfl⟩ : syracuseStep 1561481 = 1171111) B1171111
theorem B1037255 : Blo 690315 1037255 := bstep (se 1 (by rfl) ⟨777941, by rfl⟩ : syracuseStep 1037255 = 1555883) B1555883
theorem B1037279 : Blo 690315 1037279 := bstep (se 1 (by rfl) ⟨777959, by rfl⟩ : syracuseStep 1037279 = 1555919) B1555919
theorem B1037615 : Blo 690315 1037615 := bstep (se 1 (by rfl) ⟨778211, by rfl⟩ : syracuseStep 1037615 = 1556423) B1556423
theorem B8443187 : Blo 690315 8443187 := bstep (se 1 (by rfl) ⟨6332390, by rfl⟩ : syracuseStep 8443187 = 12664781) B12664781
theorem B1037819 : Blo 690315 1037819 := bstep (se 1 (by rfl) ⟨778364, by rfl⟩ : syracuseStep 1037819 = 1556729) B1556729
theorem B1037855 : Blo 690315 1037855 := bstep (se 1 (by rfl) ⟨778391, by rfl⟩ : syracuseStep 1037855 = 1556783) B1556783
theorem B1037993 : Blo 690315 1037993 := bstep (se 2 (by rfl) ⟨389247, by rfl⟩ : syracuseStep 1037993 = 778495) B778495
theorem B1037999 : Blo 690315 1037999 := bstep (se 1 (by rfl) ⟨778499, by rfl⟩ : syracuseStep 1037999 = 1556999) B1556999
theorem B1038119 : Blo 690315 1038119 := bstep (se 1 (by rfl) ⟨778589, by rfl⟩ : syracuseStep 1038119 = 1557179) B1557179
theorem B1038377 : Blo 690315 1038377 := bstep (se 2 (by rfl) ⟨389391, by rfl⟩ : syracuseStep 1038377 = 778783) B778783
theorem B874567 : Blo 690315 874567 := bstep (se 1 (by rfl) ⟨655925, by rfl⟩ : syracuseStep 874567 = 1311851) B1311851
theorem B1038407 : Blo 690315 1038407 := bstep (se 1 (by rfl) ⟨778805, by rfl⟩ : syracuseStep 1038407 = 1557611) B1557611
theorem B4217017 : Blo 690315 4217017 := bstep (se 2 (by rfl) ⟨1581381, by rfl⟩ : syracuseStep 4217017 = 3162763) B3162763
theorem B1038719 : Blo 690315 1038719 := bstep (se 1 (by rfl) ⟨779039, by rfl⟩ : syracuseStep 1038719 = 1558079) B1558079
theorem B1038791 : Blo 690315 1038791 := bstep (se 1 (by rfl) ⟨779093, by rfl⟩ : syracuseStep 1038791 = 1558187) B1558187
theorem B10672793 : Blo 690315 10672793 := bstep (se 2 (by rfl) ⟨4002297, by rfl⟩ : syracuseStep 10672793 = 8004595) B8004595
theorem B1039007 : Blo 690315 1039007 := bstep (se 1 (by rfl) ⟨779255, by rfl⟩ : syracuseStep 1039007 = 1558511) B1558511
theorem B1039151 : Blo 690315 1039151 := bstep (se 1 (by rfl) ⟨779363, by rfl⟩ : syracuseStep 1039151 = 1558727) B1558727
theorem B1039241 : Blo 690315 1039241 := bstep (se 2 (by rfl) ⟨389715, by rfl⟩ : syracuseStep 1039241 = 779431) B779431
theorem B1039271 : Blo 690315 1039271 := bstep (se 1 (by rfl) ⟨779453, by rfl⟩ : syracuseStep 1039271 = 1558907) B1558907
theorem B1039451 : Blo 690315 1039451 := bstep (se 1 (by rfl) ⟨779588, by rfl⟩ : syracuseStep 1039451 = 1559177) B1559177
theorem B1039643 : Blo 690315 1039643 := bstep (se 1 (by rfl) ⟨779732, by rfl⟩ : syracuseStep 1039643 = 1559465) B1559465
theorem B1040111 : Blo 690315 1040111 := bstep (se 1 (by rfl) ⟨780083, by rfl⟩ : syracuseStep 1040111 = 1560167) B1560167
theorem B10673963 : Blo 690315 10673963 := bstep (se 1 (by rfl) ⟨8005472, by rfl⟩ : syracuseStep 10673963 = 16010945) B16010945
theorem B1040297 : Blo 690315 1040297 := bstep (se 2 (by rfl) ⟨390111, by rfl⟩ : syracuseStep 1040297 = 780223) B780223
theorem B1040447 : Blo 690315 1040447 := bstep (se 1 (by rfl) ⟨780335, by rfl⟩ : syracuseStep 1040447 = 1560671) B1560671
theorem B1040681 : Blo 690315 1040681 := bstep (se 2 (by rfl) ⟨390255, by rfl⟩ : syracuseStep 1040681 = 780511) B780511
theorem B7102835 : Blo 690315 7102835 := bstep (se 1 (by rfl) ⟨5327126, by rfl⟩ : syracuseStep 7102835 = 10654253) B10654253
theorem B1040951 : Blo 690315 1040951 := bstep (se 1 (by rfl) ⟨780713, by rfl⟩ : syracuseStep 1040951 = 1561427) B1561427
theorem B10674953 : Blo 690315 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B1041311 : Blo 690315 1041311 := bstep (se 1 (by rfl) ⟨780983, by rfl⟩ : syracuseStep 1041311 = 1561967) B1561967
theorem B5334427 : Blo 690315 5334427 := bstep (se 1 (by rfl) ⟨4000820, by rfl⟩ : syracuseStep 5334427 = 8001641) B8001641
theorem B7890695 : Blo 690315 7890695 := bstep (se 1 (by rfl) ⟨5918021, by rfl⟩ : syracuseStep 7890695 = 11836043) B11836043
theorem B50652971 : Blo 690315 50652971 := bstep (se 1 (by rfl) ⟨37989728, by rfl⟩ : syracuseStep 50652971 = 75979457) B75979457
theorem B2222873 : Blo 690315 2222873 := bstep (se 2 (by rfl) ⟨833577, by rfl⟩ : syracuseStep 2222873 = 1667155) B1667155
theorem B1993679 : Blo 690315 1993679 := bstep (se 1 (by rfl) ⟨1495259, by rfl⟩ : syracuseStep 1993679 = 2990519) B2990519
theorem B10677905 : Blo 690315 10677905 := bstep (se 2 (by rfl) ⟨4004214, by rfl⟩ : syracuseStep 10677905 = 8008429) B8008429
theorem B9990125 : Blo 690315 9990125 := bstep (se 3 (by rfl) ⟨1873148, by rfl⟩ : syracuseStep 9990125 = 3746297) B3746297
theorem B11857913 : Blo 690315 11857913 := bstep (se 2 (by rfl) ⟨4446717, by rfl⟩ : syracuseStep 11857913 = 8893435) B8893435
theorem B1994971 : Blo 690315 1994971 := bstep (se 1 (by rfl) ⟨1496228, by rfl⟩ : syracuseStep 1994971 = 2992457) B2992457
theorem B1996105 : Blo 690315 1996105 := bstep (se 2 (by rfl) ⟨748539, by rfl⟩ : syracuseStep 1996105 = 1497079) B1497079
theorem B3504545 : Blo 690315 3504545 := bstep (se 2 (by rfl) ⟨1314204, by rfl⟩ : syracuseStep 3504545 = 2628409) B2628409
theorem B7470929 : Blo 690315 7470929 := bstep (se 2 (by rfl) ⟨2801598, by rfl⟩ : syracuseStep 7470929 = 5603197) B5603197
theorem B1310575 : Blo 690315 1310575 := bstep (se 1 (by rfl) ⟨982931, by rfl⟩ : syracuseStep 1310575 = 1965863) B1965863
theorem B11862287 : Blo 690315 11862287 := bstep (se 1 (by rfl) ⟨8896715, by rfl⟩ : syracuseStep 11862287 = 17793431) B17793431
theorem B4424219 : Blo 690315 4424219 := bstep (se 1 (by rfl) ⟨3318164, by rfl⟩ : syracuseStep 4424219 = 6636329) B6636329
theorem B1967287 : Blo 690315 1967287 := bstep (se 1 (by rfl) ⟨1475465, by rfl⟩ : syracuseStep 1967287 = 2950931) B2950931
theorem B5899979 : Blo 690315 5899979 := bstep (se 1 (by rfl) ⟨4424984, by rfl⟩ : syracuseStep 5899979 = 8849969) B8849969
theorem B7112569 : Blo 690315 7112569 := bstep (se 2 (by rfl) ⟨2667213, by rfl⟩ : syracuseStep 7112569 = 5334427) B5334427
theorem B1476635 : Blo 690315 1476635 := bstep (se 1 (by rfl) ⟨1107476, by rfl⟩ : syracuseStep 1476635 = 2214953) B2214953
theorem B690383 : Blo 690315 690383 := bstep (se 1 (by rfl) ⟨517787, by rfl⟩ : syracuseStep 690383 = 1035575) B1035575
theorem B1182055 : Blo 690315 1182055 := bstep (se 1 (by rfl) ⟨886541, by rfl⟩ : syracuseStep 1182055 = 1773083) B1773083
theorem B2623853 : Blo 690315 2623853 := bstep (se 3 (by rfl) ⟨491972, by rfl⟩ : syracuseStep 2623853 = 983945) B983945
theorem B690591 : Blo 690315 690591 := bstep (se 1 (by rfl) ⟨517943, by rfl⟩ : syracuseStep 690591 = 1035887) B1035887
theorem B690639 : Blo 690315 690639 := bstep (se 1 (by rfl) ⟨517979, by rfl⟩ : syracuseStep 690639 = 1035959) B1035959
theorem B1968619 : Blo 690315 1968619 := bstep (se 1 (by rfl) ⟨1476464, by rfl⟩ : syracuseStep 1968619 = 2952929) B2952929
theorem B690671 : Blo 690315 690671 := bstep (se 1 (by rfl) ⟨518003, by rfl⟩ : syracuseStep 690671 = 1036007) B1036007
theorem B690779 : Blo 690315 690779 := bstep (se 1 (by rfl) ⟨518084, by rfl⟩ : syracuseStep 690779 = 1036169) B1036169
theorem B690939 : Blo 690315 690939 := bstep (se 1 (by rfl) ⟨518204, by rfl⟩ : syracuseStep 690939 = 1036409) B1036409
theorem B690943 : Blo 690315 690943 := bstep (se 1 (by rfl) ⟨518207, by rfl⟩ : syracuseStep 690943 = 1036415) B1036415
theorem B985927 : Blo 690315 985927 := bstep (se 1 (by rfl) ⟨739445, by rfl⟩ : syracuseStep 985927 = 1478891) B1478891
theorem B3509243 : Blo 690315 3509243 := bstep (se 1 (by rfl) ⟨2631932, by rfl⟩ : syracuseStep 3509243 = 5263865) B5263865
theorem B2624521 : Blo 690315 2624521 := bstep (se 2 (by rfl) ⟨984195, by rfl⟩ : syracuseStep 2624521 = 1968391) B1968391
theorem B691503 : Blo 690315 691503 := bstep (se 1 (by rfl) ⟨518627, by rfl⟩ : syracuseStep 691503 = 1037255) B1037255
theorem B691519 : Blo 690315 691519 := bstep (se 1 (by rfl) ⟨518639, by rfl⟩ : syracuseStep 691519 = 1037279) B1037279
theorem B3509729 : Blo 690315 3509729 := bstep (se 2 (by rfl) ⟨1316148, by rfl⟩ : syracuseStep 3509729 = 2632297) B2632297
theorem B691743 : Blo 690315 691743 := bstep (se 1 (by rfl) ⟨518807, by rfl⟩ : syracuseStep 691743 = 1037615) B1037615
theorem B1314463 : Blo 690315 1314463 := bstep (se 1 (by rfl) ⟨985847, by rfl⟩ : syracuseStep 1314463 = 1971695) B1971695
theorem B691879 : Blo 690315 691879 := bstep (se 1 (by rfl) ⟨518909, by rfl⟩ : syracuseStep 691879 = 1037819) B1037819
theorem B691903 : Blo 690315 691903 := bstep (se 1 (by rfl) ⟨518927, by rfl⟩ : syracuseStep 691903 = 1037855) B1037855
theorem B691995 : Blo 690315 691995 := bstep (se 1 (by rfl) ⟨518996, by rfl⟩ : syracuseStep 691995 = 1037993) B1037993
theorem B691999 : Blo 690315 691999 := bstep (se 1 (by rfl) ⟨518999, by rfl⟩ : syracuseStep 691999 = 1037999) B1037999
theorem B3739463 : Blo 690315 3739463 := bstep (se 1 (by rfl) ⟨2804597, by rfl⟩ : syracuseStep 3739463 = 5609195) B5609195
theorem B692079 : Blo 690315 692079 := bstep (se 1 (by rfl) ⟨519059, by rfl⟩ : syracuseStep 692079 = 1038119) B1038119
theorem B692251 : Blo 690315 692251 := bstep (se 1 (by rfl) ⟨519188, by rfl⟩ : syracuseStep 692251 = 1038377) B1038377
theorem B692271 : Blo 690315 692271 := bstep (se 1 (by rfl) ⟨519203, by rfl⟩ : syracuseStep 692271 = 1038407) B1038407
theorem B1970419 : Blo 690315 1970419 := bstep (se 1 (by rfl) ⟨1477814, by rfl⟩ : syracuseStep 1970419 = 2955629) B2955629
theorem B692479 : Blo 690315 692479 := bstep (se 1 (by rfl) ⟨519359, by rfl⟩ : syracuseStep 692479 = 1038719) B1038719
theorem B2167067 : Blo 690315 2167067 := bstep (se 1 (by rfl) ⟨1625300, by rfl⟩ : syracuseStep 2167067 = 3250601) B3250601
theorem B692527 : Blo 690315 692527 := bstep (se 1 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 692527 = 1038791) B1038791
theorem B7115195 : Blo 690315 7115195 := bstep (se 1 (by rfl) ⟨5336396, by rfl⟩ : syracuseStep 7115195 = 10672793) B10672793
theorem B692671 : Blo 690315 692671 := bstep (se 1 (by rfl) ⟨519503, by rfl⟩ : syracuseStep 692671 = 1039007) B1039007
theorem B692767 : Blo 690315 692767 := bstep (se 1 (by rfl) ⟨519575, by rfl⟩ : syracuseStep 692767 = 1039151) B1039151
theorem B692827 : Blo 690315 692827 := bstep (se 1 (by rfl) ⟨519620, by rfl⟩ : syracuseStep 692827 = 1039241) B1039241
theorem B692847 : Blo 690315 692847 := bstep (se 1 (by rfl) ⟨519635, by rfl⟩ : syracuseStep 692847 = 1039271) B1039271
theorem B4985489 : Blo 690315 4985489 := bstep (se 2 (by rfl) ⟨1869558, by rfl⟩ : syracuseStep 4985489 = 3739117) B3739117
theorem B20288177 : Blo 690315 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B692967 : Blo 690315 692967 := bstep (se 1 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 692967 = 1039451) B1039451
theorem B2364191 : Blo 690315 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B693095 : Blo 690315 693095 := bstep (se 1 (by rfl) ⟨519821, by rfl⟩ : syracuseStep 693095 = 1039643) B1039643
theorem B4985837 : Blo 690315 4985837 := bstep (se 3 (by rfl) ⟨934844, by rfl⟩ : syracuseStep 4985837 = 1869689) B1869689
theorem B2954227 : Blo 690315 2954227 := bstep (se 1 (by rfl) ⟨2215670, by rfl⟩ : syracuseStep 2954227 = 4431341) B4431341
theorem B693407 : Blo 690315 693407 := bstep (se 1 (by rfl) ⟨520055, by rfl⟩ : syracuseStep 693407 = 1040111) B1040111
theorem B1316027 : Blo 690315 1316027 := bstep (se 1 (by rfl) ⟨987020, by rfl⟩ : syracuseStep 1316027 = 1974041) B1974041
theorem B7115975 : Blo 690315 7115975 := bstep (se 1 (by rfl) ⟨5336981, by rfl⟩ : syracuseStep 7115975 = 10673963) B10673963
theorem B2102527 : Blo 690315 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B693531 : Blo 690315 693531 := bstep (se 1 (by rfl) ⟨520148, by rfl⟩ : syracuseStep 693531 = 1040297) B1040297
theorem B693631 : Blo 690315 693631 := bstep (se 1 (by rfl) ⟨520223, by rfl⟩ : syracuseStep 693631 = 1040447) B1040447
theorem B3151379 : Blo 690315 3151379 := bstep (se 1 (by rfl) ⟨2363534, by rfl⟩ : syracuseStep 3151379 = 4727069) B4727069
theorem B693787 : Blo 690315 693787 := bstep (se 1 (by rfl) ⟨520340, by rfl⟩ : syracuseStep 693787 = 1040681) B1040681
theorem B2954843 : Blo 690315 2954843 := bstep (se 1 (by rfl) ⟨2216132, by rfl⟩ : syracuseStep 2954843 = 4432265) B4432265
theorem B2659961 : Blo 690315 2659961 := bstep (se 2 (by rfl) ⟨997485, by rfl⟩ : syracuseStep 2659961 = 1994971) B1994971
theorem B693967 : Blo 690315 693967 := bstep (se 1 (by rfl) ⟨520475, by rfl⟩ : syracuseStep 693967 = 1040951) B1040951
theorem B1971935 : Blo 690315 1971935 := bstep (se 1 (by rfl) ⟨1478951, by rfl⟩ : syracuseStep 1971935 = 2957903) B2957903
theorem B5248799 : Blo 690315 5248799 := bstep (se 1 (by rfl) ⟨3936599, by rfl⟩ : syracuseStep 5248799 = 7873199) B7873199
theorem B7116635 : Blo 690315 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B11212681 : Blo 690315 11212681 := bstep (se 2 (by rfl) ⟨4204755, by rfl⟩ : syracuseStep 11212681 = 8409511) B8409511
theorem B694207 : Blo 690315 694207 := bstep (se 1 (by rfl) ⟨520655, by rfl⟩ : syracuseStep 694207 = 1041311) B1041311
theorem B2955305 : Blo 690315 2955305 := bstep (se 2 (by rfl) ⟨1108239, by rfl⟩ : syracuseStep 2955305 = 2216479) B2216479
theorem B2332745 : Blo 690315 2332745 := bstep (se 2 (by rfl) ⟨874779, by rfl⟩ : syracuseStep 2332745 = 1749559) B1749559
theorem B3938651 : Blo 690315 3938651 := bstep (se 1 (by rfl) ⟨2953988, by rfl⟩ : syracuseStep 3938651 = 5907977) B5907977
theorem B17767187 : Blo 690315 17767187 := bstep (se 1 (by rfl) ⟨13325390, by rfl⟩ : syracuseStep 17767187 = 26650781) B26650781
theorem B3545959 : Blo 690315 3545959 := bstep (se 1 (by rfl) ⟨2659469, by rfl⟩ : syracuseStep 3545959 = 5318939) B5318939
theorem B1317971 : Blo 690315 1317971 := bstep (se 1 (by rfl) ⟨988478, by rfl⟩ : syracuseStep 1317971 = 1976957) B1976957
theorem B2661473 : Blo 690315 2661473 := bstep (se 2 (by rfl) ⟨998052, by rfl⟩ : syracuseStep 2661473 = 1996105) B1996105
theorem B2628713 : Blo 690315 2628713 := bstep (se 2 (by rfl) ⟨985767, by rfl⟩ : syracuseStep 2628713 = 1971535) B1971535
theorem B1481915 : Blo 690315 1481915 := bstep (se 1 (by rfl) ⟨1111436, by rfl⟩ : syracuseStep 1481915 = 2222873) B2222873
theorem B7118603 : Blo 690315 7118603 := bstep (se 1 (by rfl) ⟨5338952, by rfl⟩ : syracuseStep 7118603 = 10677905) B10677905
theorem B2105227 : Blo 690315 2105227 := bstep (se 1 (by rfl) ⟨1578920, by rfl⟩ : syracuseStep 2105227 = 3157841) B3157841
theorem B6660083 : Blo 690315 6660083 := bstep (se 1 (by rfl) ⟨4995062, by rfl⟩ : syracuseStep 6660083 = 9990125) B9990125
theorem B7905275 : Blo 690315 7905275 := bstep (se 1 (by rfl) ⟨5928956, by rfl⟩ : syracuseStep 7905275 = 11857913) B11857913
theorem B2335337 : Blo 690315 2335337 := bstep (se 2 (by rfl) ⟨875751, by rfl⟩ : syracuseStep 2335337 = 1751503) B1751503
theorem B12329999 : Blo 690315 12329999 := bstep (se 1 (by rfl) ⟨9247499, by rfl⟩ : syracuseStep 12329999 = 18494999) B18494999
theorem B2958943 : Blo 690315 2958943 := bstep (se 1 (by rfl) ⟨2219207, by rfl⟩ : syracuseStep 2958943 = 4438415) B4438415
theorem B2336363 : Blo 690315 2336363 := bstep (se 1 (by rfl) ⟨1752272, by rfl⟩ : syracuseStep 2336363 = 3504545) B3504545
theorem B1583135 : Blo 690315 1583135 := bstep (se 1 (by rfl) ⟨1187351, by rfl⟩ : syracuseStep 1583135 = 2374703) B2374703
theorem B7874657 : Blo 690315 7874657 := bstep (se 2 (by rfl) ⟨2952996, by rfl⟩ : syracuseStep 7874657 = 5905993) B5905993
theorem B2959679 : Blo 690315 2959679 := bstep (se 1 (by rfl) ⟨2219759, by rfl⟩ : syracuseStep 2959679 = 4439519) B4439519
theorem B2959831 : Blo 690315 2959831 := bstep (se 1 (by rfl) ⟨2219873, by rfl⟩ : syracuseStep 2959831 = 4439747) B4439747
theorem B1747433 : Blo 690315 1747433 := bstep (se 2 (by rfl) ⟨655287, by rfl⟩ : syracuseStep 1747433 = 1310575) B1310575
theorem B11840417 : Blo 690315 11840417 := bstep (se 2 (by rfl) ⟨4440156, by rfl⟩ : syracuseStep 11840417 = 8880313) B8880313
theorem B2633087 : Blo 690315 2633087 := bstep (se 1 (by rfl) ⟨1974815, by rfl⟩ : syracuseStep 2633087 = 3949631) B3949631
theorem B5254631 : Blo 690315 5254631 := bstep (se 1 (by rfl) ⟨3940973, by rfl⟩ : syracuseStep 5254631 = 7881947) B7881947
theorem B2502191 : Blo 690315 2502191 := bstep (se 1 (by rfl) ⟨1876643, by rfl⟩ : syracuseStep 2502191 = 3753287) B3753287
theorem B5910367 : Blo 690315 5910367 := bstep (se 1 (by rfl) ⟨4432775, by rfl⟩ : syracuseStep 5910367 = 8865551) B8865551
theorem B4730899 : Blo 690315 4730899 := bstep (se 1 (by rfl) ⟨3548174, by rfl⟩ : syracuseStep 4730899 = 7096349) B7096349
theorem B11972735 : Blo 690315 11972735 := bstep (se 1 (by rfl) ⟨8979551, by rfl⟩ : syracuseStep 11972735 = 17959103) B17959103
theorem B4993163 : Blo 690315 4993163 := bstep (se 1 (by rfl) ⟨3744872, by rfl⟩ : syracuseStep 4993163 = 7489745) B7489745
theorem B2339279 : Blo 690315 2339279 := bstep (se 1 (by rfl) ⟨1754459, by rfl⟩ : syracuseStep 2339279 = 3508919) B3508919
theorem B1749671 : Blo 690315 1749671 := bstep (se 1 (by rfl) ⟨1312253, by rfl⟩ : syracuseStep 1749671 = 2624507) B2624507
theorem B1553705 : Blo 690315 1553705 := bstep (se 2 (by rfl) ⟨582639, by rfl⟩ : syracuseStep 1553705 = 1165279) B1165279
theorem B3159407 : Blo 690315 3159407 := bstep (se 1 (by rfl) ⟨2369555, by rfl⟩ : syracuseStep 3159407 = 4739111) B4739111
theorem B1553993 : Blo 690315 1553993 := bstep (se 2 (by rfl) ⟨582747, by rfl⟩ : syracuseStep 1553993 = 1165495) B1165495
theorem B8009441 : Blo 690315 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B2341601 : Blo 690315 2341601 := bstep (se 2 (by rfl) ⟨878100, by rfl⟩ : syracuseStep 2341601 = 1756201) B1756201
theorem B5618537 : Blo 690315 5618537 := bstep (se 2 (by rfl) ⟨2106951, by rfl⟩ : syracuseStep 5618537 = 4213903) B4213903
theorem B3325643 : Blo 690315 3325643 := bstep (se 1 (by rfl) ⟨2494232, by rfl⟩ : syracuseStep 3325643 = 4988465) B4988465
theorem B1556243 : Blo 690315 1556243 := bstep (se 1 (by rfl) ⟨1167182, by rfl⟩ : syracuseStep 1556243 = 2334365) B2334365
theorem B1556603 : Blo 690315 1556603 := bstep (se 1 (by rfl) ⟨1167452, by rfl⟩ : syracuseStep 1556603 = 2334905) B2334905
theorem B4735223 : Blo 690315 4735223 := bstep (se 1 (by rfl) ⟨3551417, by rfl⟩ : syracuseStep 4735223 = 7102835) B7102835
theorem B12600197 : Blo 690315 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B5260463 : Blo 690315 5260463 := bstep (se 1 (by rfl) ⟨3945347, by rfl⟩ : syracuseStep 5260463 = 7890695) B7890695
theorem B33768647 : Blo 690315 33768647 := bstep (se 1 (by rfl) ⟨25326485, by rfl⟩ : syracuseStep 33768647 = 50652971) B50652971
theorem B1558043 : Blo 690315 1558043 := bstep (se 1 (by rfl) ⟨1168532, by rfl⟩ : syracuseStep 1558043 = 2337065) B2337065
theorem B7390939 : Blo 690315 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B2803675 : Blo 690315 2803675 := bstep (se 1 (by rfl) ⟨2102756, by rfl⟩ : syracuseStep 2803675 = 4205513) B4205513
theorem B1329119 : Blo 690315 1329119 := bstep (se 1 (by rfl) ⟨996839, by rfl⟩ : syracuseStep 1329119 = 1993679) B1993679
theorem B3328735 : Blo 690315 3328735 := bstep (se 1 (by rfl) ⟨2496551, by rfl⟩ : syracuseStep 3328735 = 4993103) B4993103
theorem B1166089 : Blo 690315 1166089 := bstep (se 2 (by rfl) ⟨437283, by rfl⟩ : syracuseStep 1166089 = 874567) B874567
theorem B5622689 : Blo 690315 5622689 := bstep (se 2 (by rfl) ⟨2108508, by rfl⟩ : syracuseStep 5622689 = 4217017) B4217017
theorem B1166663 : Blo 690315 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B1036199 : Blo 690315 1036199 := bstep (se 1 (by rfl) ⟨777149, by rfl⟩ : syracuseStep 1036199 = 1554299) B1554299
theorem B1036379 : Blo 690315 1036379 := bstep (se 1 (by rfl) ⟨777284, by rfl⟩ : syracuseStep 1036379 = 1554569) B1554569
theorem B4444463 : Blo 690315 4444463 := bstep (se 1 (by rfl) ⟨3333347, by rfl⟩ : syracuseStep 4444463 = 6666695) B6666695
theorem B1037051 : Blo 690315 1037051 := bstep (se 1 (by rfl) ⟨777788, by rfl⟩ : syracuseStep 1037051 = 1555577) B1555577
theorem B1168607 : Blo 690315 1168607 := bstep (se 1 (by rfl) ⟨876455, by rfl⟩ : syracuseStep 1168607 = 1752911) B1752911
theorem B8410679 : Blo 690315 8410679 := bstep (se 1 (by rfl) ⟨6308009, by rfl⟩ : syracuseStep 8410679 = 12616019) B12616019
theorem B3954257 : Blo 690315 3954257 := bstep (se 2 (by rfl) ⟨1482846, by rfl⟩ : syracuseStep 3954257 = 2965693) B2965693
theorem B1169039 : Blo 690315 1169039 := bstep (se 1 (by rfl) ⟨876779, by rfl⟩ : syracuseStep 1169039 = 1753559) B1753559
theorem B3331793 : Blo 690315 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B1038575 : Blo 690315 1038575 := bstep (se 1 (by rfl) ⟨778931, by rfl⟩ : syracuseStep 1038575 = 1557863) B1557863
theorem B1038647 : Blo 690315 1038647 := bstep (se 1 (by rfl) ⟨778985, by rfl⟩ : syracuseStep 1038647 = 1557971) B1557971
theorem B1038827 : Blo 690315 1038827 := bstep (se 1 (by rfl) ⟨779120, by rfl⟩ : syracuseStep 1038827 = 1558241) B1558241
theorem B1039355 : Blo 690315 1039355 := bstep (se 1 (by rfl) ⟨779516, by rfl⟩ : syracuseStep 1039355 = 1559033) B1559033
theorem B1039415 : Blo 690315 1039415 := bstep (se 1 (by rfl) ⟨779561, by rfl⟩ : syracuseStep 1039415 = 1559123) B1559123
theorem B1039535 : Blo 690315 1039535 := bstep (se 1 (by rfl) ⟨779651, by rfl⟩ : syracuseStep 1039535 = 1559303) B1559303
theorem B1039595 : Blo 690315 1039595 := bstep (se 1 (by rfl) ⟨779696, by rfl⟩ : syracuseStep 1039595 = 1559393) B1559393
theorem B3497255 : Blo 690315 3497255 := bstep (se 1 (by rfl) ⟨2622941, by rfl⟩ : syracuseStep 3497255 = 5245883) B5245883
theorem B1040207 : Blo 690315 1040207 := bstep (se 1 (by rfl) ⟨780155, by rfl⟩ : syracuseStep 1040207 = 1560311) B1560311
theorem B1040219 : Blo 690315 1040219 := bstep (se 1 (by rfl) ⟨780164, by rfl⟩ : syracuseStep 1040219 = 1560329) B1560329
theorem B1040255 : Blo 690315 1040255 := bstep (se 1 (by rfl) ⟨780191, by rfl⟩ : syracuseStep 1040255 = 1560383) B1560383
theorem B1171327 : Blo 690315 1171327 := bstep (se 1 (by rfl) ⟨878495, by rfl⟩ : syracuseStep 1171327 = 1756991) B1756991
theorem B9953219 : Blo 690315 9953219 := bstep (se 1 (by rfl) ⟨7464914, by rfl⟩ : syracuseStep 9953219 = 14929829) B14929829
theorem B1040327 : Blo 690315 1040327 := bstep (se 1 (by rfl) ⟨780245, by rfl⟩ : syracuseStep 1040327 = 1560491) B1560491
theorem B1040567 : Blo 690315 1040567 := bstep (se 1 (by rfl) ⟨780425, by rfl⟩ : syracuseStep 1040567 = 1560851) B1560851
theorem B1040687 : Blo 690315 1040687 := bstep (se 1 (by rfl) ⟨780515, by rfl⟩ : syracuseStep 1040687 = 1561031) B1561031
theorem B1040879 : Blo 690315 1040879 := bstep (se 1 (by rfl) ⟨780659, by rfl⟩ : syracuseStep 1040879 = 1561319) B1561319
theorem B1040927 : Blo 690315 1040927 := bstep (se 1 (by rfl) ⟨780695, by rfl⟩ : syracuseStep 1040927 = 1561391) B1561391
theorem B1040987 : Blo 690315 1040987 := bstep (se 1 (by rfl) ⟨780740, by rfl⟩ : syracuseStep 1040987 = 1561481) B1561481
theorem B5628791 : Blo 690315 5628791 := bstep (se 1 (by rfl) ⟨4221593, by rfl⟩ : syracuseStep 5628791 = 8443187) B8443187
theorem B9005435 : Blo 690315 9005435 := bstep (se 1 (by rfl) ⟨6754076, by rfl⟩ : syracuseStep 9005435 = 13508153) B13508153
theorem B5927863 : Blo 690315 5927863 := bstep (se 1 (by rfl) ⟨4445897, by rfl⟩ : syracuseStep 5927863 = 8891795) B8891795
theorem B3503897 : Blo 690315 3503897 := bstep (se 2 (by rfl) ⟨1313961, by rfl⟩ : syracuseStep 3503897 = 2627923) B2627923
theorem B95647715 : Blo 690315 95647715 := bstep (se 1 (by rfl) ⟨71735786, by rfl⟩ : syracuseStep 95647715 = 143471573) B143471573
theorem B6649937 : Blo 690315 6649937 := bstep (se 2 (by rfl) ⟨2493726, by rfl⟩ : syracuseStep 6649937 = 4987453) B4987453
theorem B11827295 : Blo 690315 11827295 := bstep (se 1 (by rfl) ⟨8870471, by rfl⟩ : syracuseStep 11827295 = 17740943) B17740943
theorem B2522551 : Blo 690315 2522551 := bstep (se 1 (by rfl) ⟨1891913, by rfl⟩ : syracuseStep 2522551 = 3783827) B3783827
theorem B3506003 : Blo 690315 3506003 := bstep (se 1 (by rfl) ⟨2629502, by rfl⟩ : syracuseStep 3506003 = 5259005) B5259005
theorem B4980619 : Blo 690315 4980619 := bstep (se 1 (by rfl) ⟨3735464, by rfl⟩ : syracuseStep 4980619 = 7470929) B7470929
theorem B22708187 : Blo 690315 22708187 := bstep (se 1 (by rfl) ⟨17031140, by rfl⟩ : syracuseStep 22708187 = 34062281) B34062281
theorem B2949479 : Blo 690315 2949479 := bstep (se 1 (by rfl) ⟨2212109, by rfl⟩ : syracuseStep 2949479 = 4424219) B4424219
theorem B3506975 : Blo 690315 3506975 := bstep (se 1 (by rfl) ⟨2630231, by rfl⟩ : syracuseStep 3506975 = 5260463) B5260463
theorem B22512431 : Blo 690315 22512431 := bstep (se 1 (by rfl) ⟨16884323, by rfl⟩ : syracuseStep 22512431 = 33768647) B33768647
theorem B3933319 : Blo 690315 3933319 := bstep (se 1 (by rfl) ⟨2949989, by rfl⟩ : syracuseStep 3933319 = 5899979) B5899979
theorem B886079 : Blo 690315 886079 := bstep (se 1 (by rfl) ⟨664559, by rfl⟩ : syracuseStep 886079 = 1329119) B1329119
theorem B2623049 : Blo 690315 2623049 := bstep (se 2 (by rfl) ⟨983643, by rfl⟩ : syracuseStep 2623049 = 1967287) B1967287
theorem B2492975 : Blo 690315 2492975 := bstep (se 1 (by rfl) ⟨1869731, by rfl⟩ : syracuseStep 2492975 = 3739463) B3739463
theorem B690799 : Blo 690315 690799 := bstep (se 1 (by rfl) ⟨518099, by rfl⟩ : syracuseStep 690799 = 1036199) B1036199
theorem B3738233 : Blo 690315 3738233 := bstep (se 2 (by rfl) ⟨1401837, by rfl⟩ : syracuseStep 3738233 = 2803675) B2803675
theorem B690919 : Blo 690315 690919 := bstep (se 1 (by rfl) ⟨518189, by rfl⟩ : syracuseStep 690919 = 1036379) B1036379
theorem B1444711 : Blo 690315 1444711 := bstep (se 1 (by rfl) ⟨1083533, by rfl⟩ : syracuseStep 1444711 = 2167067) B2167067
theorem B1576073 : Blo 690315 1576073 := bstep (se 2 (by rfl) ⟨591027, by rfl⟩ : syracuseStep 1576073 = 1182055) B1182055
theorem B3509405 : Blo 690315 3509405 := bstep (se 3 (by rfl) ⟨658013, by rfl⟩ : syracuseStep 3509405 = 1316027) B1316027
theorem B691367 : Blo 690315 691367 := bstep (se 1 (by rfl) ⟨518525, by rfl⟩ : syracuseStep 691367 = 1037051) B1037051
theorem B1576127 : Blo 690315 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B2624825 : Blo 690315 2624825 := bstep (se 2 (by rfl) ⟨984309, by rfl⟩ : syracuseStep 2624825 = 1968619) B1968619
theorem B2100919 : Blo 690315 2100919 := bstep (se 1 (by rfl) ⟨1575689, by rfl⟩ : syracuseStep 2100919 = 3151379) B3151379
theorem B5607119 : Blo 690315 5607119 := bstep (se 1 (by rfl) ⟨4205339, by rfl⟩ : syracuseStep 5607119 = 8410679) B8410679
theorem B1969895 : Blo 690315 1969895 := bstep (se 1 (by rfl) ⟨1477421, by rfl⟩ : syracuseStep 1969895 = 2954843) B2954843
theorem B1773307 : Blo 690315 1773307 := bstep (se 1 (by rfl) ⟨1329980, by rfl⟩ : syracuseStep 1773307 = 2659961) B2659961
theorem B1314569 : Blo 690315 1314569 := bstep (se 2 (by rfl) ⟨492963, by rfl⟩ : syracuseStep 1314569 = 985927) B985927
theorem B1314623 : Blo 690315 1314623 := bstep (se 1 (by rfl) ⟨985967, by rfl⟩ : syracuseStep 1314623 = 1971935) B1971935
theorem B1970203 : Blo 690315 1970203 := bstep (se 1 (by rfl) ⟨1477652, by rfl⟩ : syracuseStep 1970203 = 2955305) B2955305
theorem B692383 : Blo 690315 692383 := bstep (se 1 (by rfl) ⟨519287, by rfl⟩ : syracuseStep 692383 = 1038575) B1038575
theorem B692431 : Blo 690315 692431 := bstep (se 1 (by rfl) ⟨519323, by rfl⟩ : syracuseStep 692431 = 1038647) B1038647
theorem B2625767 : Blo 690315 2625767 := bstep (se 1 (by rfl) ⟨1969325, by rfl⟩ : syracuseStep 2625767 = 3938651) B3938651
theorem B692551 : Blo 690315 692551 := bstep (se 1 (by rfl) ⟨519413, by rfl⟩ : syracuseStep 692551 = 1038827) B1038827
theorem B692903 : Blo 690315 692903 := bstep (se 1 (by rfl) ⟨519677, by rfl⟩ : syracuseStep 692903 = 1039355) B1039355
theorem B692943 : Blo 690315 692943 := bstep (se 1 (by rfl) ⟨519707, by rfl⟩ : syracuseStep 692943 = 1039415) B1039415
theorem B1774315 : Blo 690315 1774315 := bstep (se 1 (by rfl) ⟨1330736, by rfl⟩ : syracuseStep 1774315 = 2661473) B2661473
theorem B693023 : Blo 690315 693023 := bstep (se 1 (by rfl) ⟨519767, by rfl⟩ : syracuseStep 693023 = 1039535) B1039535
theorem B693063 : Blo 690315 693063 := bstep (se 1 (by rfl) ⟨519797, by rfl⟩ : syracuseStep 693063 = 1039595) B1039595
theorem B2331503 : Blo 690315 2331503 := bstep (se 1 (by rfl) ⟨1748627, by rfl⟩ : syracuseStep 2331503 = 3497255) B3497255
theorem B693471 : Blo 690315 693471 := bstep (se 1 (by rfl) ⟨520103, by rfl⟩ : syracuseStep 693471 = 1040207) B1040207
theorem B693479 : Blo 690315 693479 := bstep (se 1 (by rfl) ⟨520109, by rfl⟩ : syracuseStep 693479 = 1040219) B1040219
theorem B693503 : Blo 690315 693503 := bstep (se 1 (by rfl) ⟨520127, by rfl⟩ : syracuseStep 693503 = 1040255) B1040255
theorem B693551 : Blo 690315 693551 := bstep (se 1 (by rfl) ⟨520163, by rfl⟩ : syracuseStep 693551 = 1040327) B1040327
theorem B3937693 : Blo 690315 3937693 := bstep (se 3 (by rfl) ⟨738317, by rfl⟩ : syracuseStep 3937693 = 1476635) B1476635
theorem B693711 : Blo 690315 693711 := bstep (se 1 (by rfl) ⟨520283, by rfl⟩ : syracuseStep 693711 = 1040567) B1040567
theorem B693791 : Blo 690315 693791 := bstep (se 1 (by rfl) ⟨520343, by rfl⟩ : syracuseStep 693791 = 1040687) B1040687
theorem B2627225 : Blo 690315 2627225 := bstep (se 2 (by rfl) ⟨985209, by rfl⟩ : syracuseStep 2627225 = 1970419) B1970419
theorem B693919 : Blo 690315 693919 := bstep (se 1 (by rfl) ⟨520439, by rfl⟩ : syracuseStep 693919 = 1040879) B1040879
theorem B693951 : Blo 690315 693951 := bstep (se 1 (by rfl) ⟨520463, by rfl⟩ : syracuseStep 693951 = 1040927) B1040927
theorem B693991 : Blo 690315 693991 := bstep (se 1 (by rfl) ⟨520493, by rfl⟩ : syracuseStep 693991 = 1040987) B1040987
theorem B7903817 : Blo 690315 7903817 := bstep (se 2 (by rfl) ⟨2963931, by rfl⟩ : syracuseStep 7903817 = 5927863) B5927863
theorem B3938969 : Blo 690315 3938969 := bstep (se 2 (by rfl) ⟨1477113, by rfl⟩ : syracuseStep 3938969 = 2954227) B2954227
theorem B1055423 : Blo 690315 1055423 := bstep (se 1 (by rfl) ⟨791567, by rfl⟩ : syracuseStep 1055423 = 1583135) B1583135
theorem B5249771 : Blo 690315 5249771 := bstep (se 1 (by rfl) ⟨3937328, by rfl⟩ : syracuseStep 5249771 = 7874657) B7874657
theorem B1973119 : Blo 690315 1973119 := bstep (se 1 (by rfl) ⟨1479839, by rfl⟩ : syracuseStep 1973119 = 2959679) B2959679
theorem B6003623 : Blo 690315 6003623 := bstep (se 1 (by rfl) ⟨4502717, by rfl⟩ : syracuseStep 6003623 = 9005435) B9005435
theorem B14950241 : Blo 690315 14950241 := bstep (se 2 (by rfl) ⟨5606340, by rfl⟩ : syracuseStep 14950241 = 11212681) B11212681
theorem B3514589 : Blo 690315 3514589 := bstep (se 3 (by rfl) ⟨658985, by rfl⟩ : syracuseStep 3514589 = 1317971) B1317971
theorem B2106271 : Blo 690315 2106271 := bstep (se 1 (by rfl) ⟨1579703, by rfl⟩ : syracuseStep 2106271 = 3159407) B3159407
theorem B4727945 : Blo 690315 4727945 := bstep (se 2 (by rfl) ⟨1772979, by rfl⟩ : syracuseStep 4727945 = 3545959) B3545959
theorem B2335931 : Blo 690315 2335931 := bstep (se 1 (by rfl) ⟨1751948, by rfl⟩ : syracuseStep 2335931 = 3503897) B3503897
theorem B4433291 : Blo 690315 4433291 := bstep (se 1 (by rfl) ⟨3324968, by rfl⟩ : syracuseStep 4433291 = 6649937) B6649937
theorem B3745691 : Blo 690315 3745691 := bstep (se 1 (by rfl) ⟨2809268, by rfl⟩ : syracuseStep 3745691 = 5618537) B5618537
theorem B2337335 : Blo 690315 2337335 := bstep (se 1 (by rfl) ⟨1753001, by rfl⟩ : syracuseStep 2337335 = 3506003) B3506003
theorem B3156815 : Blo 690315 3156815 := bstep (se 1 (by rfl) ⟨2367611, by rfl⟩ : syracuseStep 3156815 = 4735223) B4735223
theorem B7908191 : Blo 690315 7908191 := bstep (se 1 (by rfl) ⟨5931143, by rfl⟩ : syracuseStep 7908191 = 11862287) B11862287
theorem B8400131 : Blo 690315 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B1749235 : Blo 690315 1749235 := bstep (se 1 (by rfl) ⟨1311926, by rfl⟩ : syracuseStep 1749235 = 2623853) B2623853
theorem B3748459 : Blo 690315 3748459 := bstep (se 1 (by rfl) ⟨2811344, by rfl⟩ : syracuseStep 3748459 = 5622689) B5622689
theorem B2339495 : Blo 690315 2339495 := bstep (se 1 (by rfl) ⟨1754621, by rfl⟩ : syracuseStep 2339495 = 3509243) B3509243
theorem B3945257 : Blo 690315 3945257 := bstep (se 2 (by rfl) ⟨1479471, by rfl⟩ : syracuseStep 3945257 = 2958943) B2958943
theorem B2339819 : Blo 690315 2339819 := bstep (se 1 (by rfl) ⟨1754864, by rfl⟩ : syracuseStep 2339819 = 3509729) B3509729
theorem B9483425 : Blo 690315 9483425 := bstep (se 2 (by rfl) ⟨3556284, by rfl⟩ : syracuseStep 9483425 = 7112569) B7112569
theorem B2962975 : Blo 690315 2962975 := bstep (se 1 (by rfl) ⟨2222231, by rfl⟩ : syracuseStep 2962975 = 4444463) B4444463
theorem B3946441 : Blo 690315 3946441 := bstep (se 2 (by rfl) ⟨1479915, by rfl⟩ : syracuseStep 3946441 = 2959831) B2959831
theorem B3323891 : Blo 690315 3323891 := bstep (se 1 (by rfl) ⟨2492918, by rfl⟩ : syracuseStep 3323891 = 4985837) B4985837
theorem B4438313 : Blo 690315 4438313 := bstep (se 2 (by rfl) ⟨1664367, by rfl⟩ : syracuseStep 4438313 = 3328735) B3328735
theorem B1554785 : Blo 690315 1554785 := bstep (se 2 (by rfl) ⟨583044, by rfl⟩ : syracuseStep 1554785 = 1166089) B1166089
theorem B2636171 : Blo 690315 2636171 := bstep (se 1 (by rfl) ⟨1977128, by rfl⟩ : syracuseStep 2636171 = 3954257) B3954257
theorem B1555163 : Blo 690315 1555163 := bstep (se 1 (by rfl) ⟨1166372, by rfl⟩ : syracuseStep 1555163 = 2332745) B2332745
theorem B11844791 : Blo 690315 11844791 := bstep (se 1 (by rfl) ⟨8883593, by rfl⟩ : syracuseStep 11844791 = 17767187) B17767187
theorem B1752475 : Blo 690315 1752475 := bstep (se 1 (by rfl) ⟨1314356, by rfl⟩ : syracuseStep 1752475 = 2628713) B2628713
theorem B1752617 : Blo 690315 1752617 := bstep (se 2 (by rfl) ⟨657231, by rfl⟩ : syracuseStep 1752617 = 1314463) B1314463
theorem B7880489 : Blo 690315 7880489 := bstep (se 2 (by rfl) ⟨2955183, by rfl⟩ : syracuseStep 7880489 = 5910367) B5910367
theorem B6635479 : Blo 690315 6635479 := bstep (se 1 (by rfl) ⟨4976609, by rfl⟩ : syracuseStep 6635479 = 9953219) B9953219
theorem B4440055 : Blo 690315 4440055 := bstep (se 1 (by rfl) ⟨3330041, by rfl⟩ : syracuseStep 4440055 = 6660083) B6660083
theorem B6307865 : Blo 690315 6307865 := bstep (se 2 (by rfl) ⟨2365449, by rfl⟩ : syracuseStep 6307865 = 4730899) B4730899
theorem B1556891 : Blo 690315 1556891 := bstep (se 1 (by rfl) ⟨1167668, by rfl⟩ : syracuseStep 1556891 = 2335337) B2335337
theorem B3752527 : Blo 690315 3752527 := bstep (se 1 (by rfl) ⟨2814395, by rfl⟩ : syracuseStep 3752527 = 5628791) B5628791
theorem B1557575 : Blo 690315 1557575 := bstep (se 1 (by rfl) ⟨1168181, by rfl⟩ : syracuseStep 1557575 = 2336363) B2336363
theorem B1164955 : Blo 690315 1164955 := bstep (se 1 (by rfl) ⟨873716, by rfl⟩ : syracuseStep 1164955 = 1747433) B1747433
theorem B2803369 : Blo 690315 2803369 := bstep (se 2 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 2803369 = 2102527) B2102527
theorem B1755391 : Blo 690315 1755391 := bstep (se 1 (by rfl) ⟨1316543, by rfl⟩ : syracuseStep 1755391 = 2633087) B2633087
theorem B7981823 : Blo 690315 7981823 := bstep (se 1 (by rfl) ⟨5986367, by rfl⟩ : syracuseStep 7981823 = 11972735) B11972735
theorem B3328775 : Blo 690315 3328775 := bstep (se 1 (by rfl) ⟨2496581, by rfl⟩ : syracuseStep 3328775 = 4993163) B4993163
theorem B1559519 : Blo 690315 1559519 := bstep (se 1 (by rfl) ⟨1169639, by rfl⟩ : syracuseStep 1559519 = 2339279) B2339279
theorem B1166447 : Blo 690315 1166447 := bstep (se 1 (by rfl) ⟨874835, by rfl⟩ : syracuseStep 1166447 = 1749671) B1749671
theorem B3951773 : Blo 690315 3951773 := bstep (se 3 (by rfl) ⟨740957, by rfl⟩ : syracuseStep 3951773 = 1481915) B1481915
theorem B1035803 : Blo 690315 1035803 := bstep (se 1 (by rfl) ⟨776852, by rfl⟩ : syracuseStep 1035803 = 1553705) B1553705
theorem B1035995 : Blo 690315 1035995 := bstep (se 1 (by rfl) ⟨776996, by rfl⟩ : syracuseStep 1035995 = 1553993) B1553993
theorem B7884863 : Blo 690315 7884863 := bstep (se 1 (by rfl) ⟨5913647, by rfl⟩ : syracuseStep 7884863 = 11827295) B11827295
theorem B1561067 : Blo 690315 1561067 := bstep (se 1 (by rfl) ⟨1170800, by rfl⟩ : syracuseStep 1561067 = 2341601) B2341601
theorem B3363401 : Blo 690315 3363401 := bstep (se 2 (by rfl) ⟨1261275, by rfl⟩ : syracuseStep 3363401 = 2522551) B2522551
theorem B2217095 : Blo 690315 2217095 := bstep (se 1 (by rfl) ⟨1662821, by rfl⟩ : syracuseStep 2217095 = 3325643) B3325643
theorem B1561769 : Blo 690315 1561769 := bstep (se 2 (by rfl) ⟨585663, by rfl⟩ : syracuseStep 1561769 = 1171327) B1171327
theorem B1037495 : Blo 690315 1037495 := bstep (se 1 (by rfl) ⟨778121, by rfl⟩ : syracuseStep 1037495 = 1556243) B1556243
theorem B6640825 : Blo 690315 6640825 := bstep (se 2 (by rfl) ⟨2490309, by rfl⟩ : syracuseStep 6640825 = 4980619) B4980619
theorem B2806969 : Blo 690315 2806969 := bstep (se 2 (by rfl) ⟨1052613, by rfl⟩ : syracuseStep 2806969 = 2105227) B2105227
theorem B1037735 : Blo 690315 1037735 := bstep (se 1 (by rfl) ⟨778301, by rfl⟩ : syracuseStep 1037735 = 1556603) B1556603
theorem B1038695 : Blo 690315 1038695 := bstep (se 1 (by rfl) ⟨779021, by rfl⟩ : syracuseStep 1038695 = 1558043) B1558043
theorem B13294637 : Blo 690315 13294637 := bstep (se 3 (by rfl) ⟨2492744, by rfl⟩ : syracuseStep 13294637 = 4985489) B4985489
theorem B777775 : Blo 690315 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B9854585 : Blo 690315 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B4743463 : Blo 690315 4743463 := bstep (se 1 (by rfl) ⟨3557597, by rfl⟩ : syracuseStep 4743463 = 7115195) B7115195
theorem B13525451 : Blo 690315 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B4743983 : Blo 690315 4743983 := bstep (se 1 (by rfl) ⟨3557987, by rfl⟩ : syracuseStep 4743983 = 7115975) B7115975
theorem B779071 : Blo 690315 779071 := bstep (se 1 (by rfl) ⟨584303, by rfl⟩ : syracuseStep 779071 = 1168607) B1168607
theorem B779359 : Blo 690315 779359 := bstep (se 1 (by rfl) ⟨584519, by rfl⟩ : syracuseStep 779359 = 1169039) B1169039
theorem B2221195 : Blo 690315 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B3499199 : Blo 690315 3499199 := bstep (se 1 (by rfl) ⟨2624399, by rfl⟩ : syracuseStep 3499199 = 5248799) B5248799
theorem B4744423 : Blo 690315 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B3499361 : Blo 690315 3499361 := bstep (se 2 (by rfl) ⟨1312260, by rfl⟩ : syracuseStep 3499361 = 2624521) B2624521
theorem B4745735 : Blo 690315 4745735 := bstep (se 1 (by rfl) ⟨3559301, by rfl⟩ : syracuseStep 4745735 = 7118603) B7118603
theorem B5270183 : Blo 690315 5270183 := bstep (se 1 (by rfl) ⟨3952637, by rfl⟩ : syracuseStep 5270183 = 7905275) B7905275
theorem B8219999 : Blo 690315 8219999 := bstep (se 1 (by rfl) ⟨6164999, by rfl⟩ : syracuseStep 8219999 = 12329999) B12329999
theorem B7893611 : Blo 690315 7893611 := bstep (se 1 (by rfl) ⟨5920208, by rfl⟩ : syracuseStep 7893611 = 11840417) B11840417
theorem B3503087 : Blo 690315 3503087 := bstep (se 1 (by rfl) ⟨2627315, by rfl⟩ : syracuseStep 3503087 = 5254631) B5254631
theorem B1668127 : Blo 690315 1668127 := bstep (se 1 (by rfl) ⟨1251095, by rfl⟩ : syracuseStep 1668127 = 2502191) B2502191
theorem B5339627 : Blo 690315 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B63765143 : Blo 690315 63765143 := bstep (se 1 (by rfl) ⟨47823857, by rfl⟩ : syracuseStep 63765143 = 95647715) B95647715
theorem B15138791 : Blo 690315 15138791 := bstep (se 1 (by rfl) ⟨11354093, by rfl⟩ : syracuseStep 15138791 = 22708187) B22708187
theorem B1966319 : Blo 690315 1966319 := bstep (se 1 (by rfl) ⟨1474739, by rfl⟩ : syracuseStep 1966319 = 2949479) B2949479
theorem B6324617 : Blo 690315 6324617 := bstep (se 2 (by rfl) ⟨2371731, by rfl⟩ : syracuseStep 6324617 = 4743463) B4743463
theorem B15008287 : Blo 690315 15008287 := bstep (se 1 (by rfl) ⟨11256215, by rfl⟩ : syracuseStep 15008287 = 22512431) B22512431
theorem B5244425 : Blo 690315 5244425 := bstep (se 2 (by rfl) ⟨1966659, by rfl⟩ : syracuseStep 5244425 = 3933319) B3933319
theorem B6325897 : Blo 690315 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B2492155 : Blo 690315 2492155 := bstep (se 1 (by rfl) ⟨1869116, by rfl⟩ : syracuseStep 2492155 = 3738233) B3738233
theorem B1050715 : Blo 690315 1050715 := bstep (se 1 (by rfl) ⟨788036, by rfl⟩ : syracuseStep 1050715 = 1576073) B1576073
theorem B1050751 : Blo 690315 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B3737825 : Blo 690315 3737825 := bstep (se 2 (by rfl) ⟨1401684, by rfl⟩ : syracuseStep 3737825 = 2803369) B2803369
theorem B690535 : Blo 690315 690535 := bstep (se 1 (by rfl) ⟨517901, by rfl⟩ : syracuseStep 690535 = 1035803) B1035803
theorem B3738079 : Blo 690315 3738079 := bstep (se 1 (by rfl) ⟨2803559, by rfl⟩ : syracuseStep 3738079 = 5607119) B5607119
theorem B690663 : Blo 690315 690663 := bstep (se 1 (by rfl) ⟨517997, by rfl⟩ : syracuseStep 690663 = 1035995) B1035995
theorem B1313263 : Blo 690315 1313263 := bstep (se 1 (by rfl) ⟨984947, by rfl⟩ : syracuseStep 1313263 = 1969895) B1969895
theorem B1478063 : Blo 690315 1478063 := bstep (se 1 (by rfl) ⟨1108547, by rfl⟩ : syracuseStep 1478063 = 2217095) B2217095
theorem B691663 : Blo 690315 691663 := bstep (se 1 (by rfl) ⟨518747, by rfl⟩ : syracuseStep 691663 = 1037495) B1037495
theorem B2362877 : Blo 690315 2362877 := bstep (se 3 (by rfl) ⟨443039, by rfl⟩ : syracuseStep 2362877 = 886079) B886079
theorem B691823 : Blo 690315 691823 := bstep (se 1 (by rfl) ⟨518867, by rfl⟩ : syracuseStep 691823 = 1037735) B1037735
theorem B692463 : Blo 690315 692463 := bstep (se 1 (by rfl) ⟨519347, by rfl⟩ : syracuseStep 692463 = 1038695) B1038695
theorem B2625979 : Blo 690315 2625979 := bstep (se 1 (by rfl) ⟨1969484, by rfl⟩ : syracuseStep 2625979 = 3938969) B3938969
theorem B4002415 : Blo 690315 4002415 := bstep (se 1 (by rfl) ⟨3001811, by rfl⟩ : syracuseStep 4002415 = 6003623) B6003623
theorem B2364409 : Blo 690315 2364409 := bstep (se 2 (by rfl) ⟨886653, by rfl⟩ : syracuseStep 2364409 = 1773307) B1773307
theorem B9966827 : Blo 690315 9966827 := bstep (se 1 (by rfl) ⟨7475120, by rfl⟩ : syracuseStep 9966827 = 14950241) B14950241
theorem B2626937 : Blo 690315 2626937 := bstep (se 2 (by rfl) ⟨985101, by rfl⟩ : syracuseStep 2626937 = 1970203) B1970203
theorem B9016967 : Blo 690315 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B2332313 : Blo 690315 2332313 := bstep (se 2 (by rfl) ⟨874617, by rfl⟩ : syracuseStep 2332313 = 1749235) B1749235
theorem B3151963 : Blo 690315 3151963 := bstep (se 1 (by rfl) ⟨2363972, by rfl⟩ : syracuseStep 3151963 = 4727945) B4727945
theorem B2332799 : Blo 690315 2332799 := bstep (se 1 (by rfl) ⟨1749599, by rfl⟩ : syracuseStep 2332799 = 3499199) B3499199
theorem B2332907 : Blo 690315 2332907 := bstep (se 1 (by rfl) ⟨1749680, by rfl⟩ : syracuseStep 2332907 = 3499361) B3499361
theorem B2955527 : Blo 690315 2955527 := bstep (se 1 (by rfl) ⟨2216645, by rfl⟩ : syracuseStep 2955527 = 4433291) B4433291
theorem B2497127 : Blo 690315 2497127 := bstep (se 1 (by rfl) ⟨1872845, by rfl⟩ : syracuseStep 2497127 = 3745691) B3745691
theorem B8854433 : Blo 690315 8854433 := bstep (se 2 (by rfl) ⟨3320412, by rfl⟩ : syracuseStep 8854433 = 6640825) B6640825
theorem B3742625 : Blo 690315 3742625 := bstep (se 2 (by rfl) ⟨1403484, by rfl⟩ : syracuseStep 3742625 = 2806969) B2806969
theorem B3513455 : Blo 690315 3513455 := bstep (se 1 (by rfl) ⟨2635091, by rfl⟩ : syracuseStep 3513455 = 5270183) B5270183
theorem B5250257 : Blo 690315 5250257 := bstep (se 2 (by rfl) ⟨1968846, by rfl⟩ : syracuseStep 5250257 = 3937693) B3937693
theorem B2630171 : Blo 690315 2630171 := bstep (se 1 (by rfl) ⟨1972628, by rfl⟩ : syracuseStep 2630171 = 3945257) B3945257
theorem B2335391 : Blo 690315 2335391 := bstep (se 1 (by rfl) ⟨1751543, by rfl⟩ : syracuseStep 2335391 = 3503087) B3503087
theorem B2630825 : Blo 690315 2630825 := bstep (se 2 (by rfl) ⟨986559, by rfl⟩ : syracuseStep 2630825 = 1973119) B1973119
theorem B2958875 : Blo 690315 2958875 := bstep (se 1 (by rfl) ⟨2219156, by rfl⟩ : syracuseStep 2958875 = 4438313) B4438313
theorem B42510095 : Blo 690315 42510095 := bstep (se 1 (by rfl) ⟨31882571, by rfl⟩ : syracuseStep 42510095 = 63765143) B63765143
theorem B2336633 : Blo 690315 2336633 := bstep (se 2 (by rfl) ⟨876237, by rfl⟩ : syracuseStep 2336633 = 1752475) B1752475
theorem B5253659 : Blo 690315 5253659 := bstep (se 1 (by rfl) ⟨3940244, by rfl⟩ : syracuseStep 5253659 = 7880489) B7880489
theorem B4205243 : Blo 690315 4205243 := bstep (se 1 (by rfl) ⟨3153932, by rfl⟩ : syracuseStep 4205243 = 6307865) B6307865
theorem B2337983 : Blo 690315 2337983 := bstep (se 1 (by rfl) ⟨1753487, by rfl⟩ : syracuseStep 2337983 = 3506975) B3506975
theorem B1748699 : Blo 690315 1748699 := bstep (se 1 (by rfl) ⟨1311524, by rfl⟩ : syracuseStep 1748699 = 2623049) B2623049
theorem B2961593 : Blo 690315 2961593 := bstep (se 2 (by rfl) ⟨1110597, by rfl⟩ : syracuseStep 2961593 = 2221195) B2221195
theorem B5321215 : Blo 690315 5321215 := bstep (se 1 (by rfl) ⟨3990911, by rfl⟩ : syracuseStep 5321215 = 7981823) B7981823
theorem B2339603 : Blo 690315 2339603 := bstep (se 1 (by rfl) ⟨1754702, by rfl⟩ : syracuseStep 2339603 = 3509405) B3509405
theorem B2634515 : Blo 690315 2634515 := bstep (se 1 (by rfl) ⟨1975886, by rfl⟩ : syracuseStep 2634515 = 3951773) B3951773
theorem B1553273 : Blo 690315 1553273 := bstep (se 2 (by rfl) ⟨582477, by rfl⟩ : syracuseStep 1553273 = 1164955) B1164955
theorem B1749883 : Blo 690315 1749883 := bstep (se 1 (by rfl) ⟨1312412, by rfl⟩ : syracuseStep 1749883 = 2624825) B2624825
theorem B5256575 : Blo 690315 5256575 := bstep (se 1 (by rfl) ⟨3942431, by rfl⟩ : syracuseStep 5256575 = 7884863) B7884863
theorem B1750511 : Blo 690315 1750511 := bstep (se 1 (by rfl) ⟨1312883, by rfl⟩ : syracuseStep 1750511 = 2625767) B2625767
theorem B2340521 : Blo 690315 2340521 := bstep (se 2 (by rfl) ⟨877695, by rfl⟩ : syracuseStep 2340521 = 1755391) B1755391
theorem B1554335 : Blo 690315 1554335 := bstep (se 1 (by rfl) ⟨1165751, by rfl⟩ : syracuseStep 1554335 = 2331503) B2331503
theorem B1751483 : Blo 690315 1751483 := bstep (se 1 (by rfl) ⟨1313612, by rfl⟩ : syracuseStep 1751483 = 2627225) B2627225
theorem B703615 : Blo 690315 703615 := bstep (se 1 (by rfl) ⟨527711, by rfl⟩ : syracuseStep 703615 = 1055423) B1055423
theorem B8863091 : Blo 690315 8863091 := bstep (se 1 (by rfl) ⟨6647318, by rfl⟩ : syracuseStep 8863091 = 13294637) B13294637
theorem B2801225 : Blo 690315 2801225 := bstep (se 2 (by rfl) ⟨1050459, by rfl⟩ : syracuseStep 2801225 = 2100919) B2100919
theorem B6569723 : Blo 690315 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B2343059 : Blo 690315 2343059 := bstep (se 1 (by rfl) ⟨1757294, by rfl⟩ : syracuseStep 2343059 = 3514589) B3514589
theorem B3162655 : Blo 690315 3162655 := bstep (se 1 (by rfl) ⟨2371991, by rfl⟩ : syracuseStep 3162655 = 4743983) B4743983
theorem B1557287 : Blo 690315 1557287 := bstep (se 1 (by rfl) ⟨1167965, by rfl⟩ : syracuseStep 1557287 = 2335931) B2335931
theorem B4997945 : Blo 690315 4997945 := bstep (se 2 (by rfl) ⟨1874229, by rfl⟩ : syracuseStep 4997945 = 3748459) B3748459
theorem B3163823 : Blo 690315 3163823 := bstep (se 1 (by rfl) ⟨2372867, by rfl⟩ : syracuseStep 3163823 = 4745735) B4745735
theorem B1558223 : Blo 690315 1558223 := bstep (se 1 (by rfl) ⟨1168667, by rfl⟩ : syracuseStep 1558223 = 2337335) B2337335
theorem B3950633 : Blo 690315 3950633 := bstep (se 2 (by rfl) ⟨1481487, by rfl⟩ : syracuseStep 3950633 = 2962975) B2962975
theorem B5261921 : Blo 690315 5261921 := bstep (se 2 (by rfl) ⟨1973220, by rfl⟩ : syracuseStep 5261921 = 3946441) B3946441
theorem B5262407 : Blo 690315 5262407 := bstep (se 1 (by rfl) ⟨3946805, by rfl⟩ : syracuseStep 5262407 = 7893611) B7893611
theorem B1559663 : Blo 690315 1559663 := bstep (se 1 (by rfl) ⟨1169747, by rfl⟩ : syracuseStep 1559663 = 2339495) B2339495
theorem B1559879 : Blo 690315 1559879 := bstep (se 1 (by rfl) ⟨1169909, by rfl⟩ : syracuseStep 1559879 = 2339819) B2339819
theorem B2215927 : Blo 690315 2215927 := bstep (se 1 (by rfl) ⟨1661945, by rfl⟩ : syracuseStep 2215927 = 3323891) B3323891
theorem B1036523 : Blo 690315 1036523 := bstep (se 1 (by rfl) ⟨777392, by rfl⟩ : syracuseStep 1036523 = 1554785) B1554785
theorem B1757447 : Blo 690315 1757447 := bstep (se 1 (by rfl) ⟨1318085, by rfl⟩ : syracuseStep 1757447 = 2636171) B2636171
theorem B3559751 : Blo 690315 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B1036775 : Blo 690315 1036775 := bstep (se 1 (by rfl) ⟨777581, by rfl⟩ : syracuseStep 1036775 = 1555163) B1555163
theorem B1037033 : Blo 690315 1037033 := bstep (se 2 (by rfl) ⟨388887, by rfl⟩ : syracuseStep 1037033 = 777775) B777775
theorem B1168411 : Blo 690315 1168411 := bstep (se 1 (by rfl) ⟨876308, by rfl⟩ : syracuseStep 1168411 = 1752617) B1752617
theorem B5920073 : Blo 690315 5920073 := bstep (se 2 (by rfl) ⟨2220027, by rfl⟩ : syracuseStep 5920073 = 4440055) B4440055
theorem B1037927 : Blo 690315 1037927 := bstep (se 1 (by rfl) ⟨778445, by rfl⟩ : syracuseStep 1037927 = 1556891) B1556891
theorem B1038383 : Blo 690315 1038383 := bstep (se 1 (by rfl) ⟨778787, by rfl⟩ : syracuseStep 1038383 = 1557575) B1557575
theorem B5003369 : Blo 690315 5003369 := bstep (se 2 (by rfl) ⟨1876263, by rfl⟩ : syracuseStep 5003369 = 3752527) B3752527
theorem B1038761 : Blo 690315 1038761 := bstep (se 2 (by rfl) ⟨389535, by rfl⟩ : syracuseStep 1038761 = 779071) B779071
theorem B2808361 : Blo 690315 2808361 := bstep (se 2 (by rfl) ⟨1053135, by rfl⟩ : syracuseStep 2808361 = 2106271) B2106271
theorem B1039145 : Blo 690315 1039145 := bstep (se 2 (by rfl) ⟨389679, by rfl⟩ : syracuseStep 1039145 = 779359) B779359
theorem B8969069 : Blo 690315 8969069 := bstep (se 3 (by rfl) ⟨1681700, by rfl⟩ : syracuseStep 8969069 = 3363401) B3363401
theorem B2219183 : Blo 690315 2219183 := bstep (se 1 (by rfl) ⟨1664387, by rfl⟩ : syracuseStep 2219183 = 3328775) B3328775
theorem B1039679 : Blo 690315 1039679 := bstep (se 1 (by rfl) ⟨779759, by rfl⟩ : syracuseStep 1039679 = 1559519) B1559519
theorem B777631 : Blo 690315 777631 := bstep (se 1 (by rfl) ⟨583223, by rfl⟩ : syracuseStep 777631 = 1166447) B1166447
theorem B876415 : Blo 690315 876415 := bstep (se 1 (by rfl) ⟨657311, by rfl⟩ : syracuseStep 876415 = 1314623) B1314623
theorem B1040711 : Blo 690315 1040711 := bstep (se 1 (by rfl) ⟨780533, by rfl⟩ : syracuseStep 1040711 = 1561067) B1561067
theorem B1041179 : Blo 690315 1041179 := bstep (se 1 (by rfl) ⟨780884, by rfl⟩ : syracuseStep 1041179 = 1561769) B1561769
theorem B1926281 : Blo 690315 1926281 := bstep (se 2 (by rfl) ⟨722355, by rfl⟩ : syracuseStep 1926281 = 1444711) B1444711
theorem B9463013 : Blo 690315 9463013 := bstep (se 4 (by rfl) ⟨887157, by rfl⟩ : syracuseStep 9463013 = 1774315) B1774315
theorem B5269211 : Blo 690315 5269211 := bstep (se 1 (by rfl) ⟨3951908, by rfl⟩ : syracuseStep 5269211 = 7903817) B7903817
theorem B3499847 : Blo 690315 3499847 := bstep (se 1 (by rfl) ⟨2624885, by rfl⟩ : syracuseStep 3499847 = 5249771) B5249771
theorem B2224169 : Blo 690315 2224169 := bstep (se 2 (by rfl) ⟨834063, by rfl⟩ : syracuseStep 2224169 = 1668127) B1668127
theorem B6647933 : Blo 690315 6647933 := bstep (se 3 (by rfl) ⟨1246487, by rfl⟩ : syracuseStep 6647933 = 2492975) B2492975
theorem B5272127 : Blo 690315 5272127 := bstep (se 1 (by rfl) ⟨3954095, by rfl⟩ : syracuseStep 5272127 = 7908191) B7908191
theorem B5600087 : Blo 690315 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B8418173 : Blo 690315 8418173 := bstep (se 3 (by rfl) ⟨1578407, by rfl⟩ : syracuseStep 8418173 = 3156815) B3156815
theorem B6322283 : Blo 690315 6322283 := bstep (se 1 (by rfl) ⟨4741712, by rfl⟩ : syracuseStep 6322283 = 9483425) B9483425
theorem B21919997 : Blo 690315 21919997 := bstep (se 3 (by rfl) ⟨4109999, by rfl⟩ : syracuseStep 21919997 = 8219999) B8219999
theorem B3505517 : Blo 690315 3505517 := bstep (se 3 (by rfl) ⟨657284, by rfl⟩ : syracuseStep 3505517 = 1314569) B1314569
theorem B7896527 : Blo 690315 7896527 := bstep (se 1 (by rfl) ⟨5922395, by rfl⟩ : syracuseStep 7896527 = 11844791) B11844791
theorem B8847305 : Blo 690315 8847305 := bstep (se 2 (by rfl) ⟨3317739, by rfl⟩ : syracuseStep 8847305 = 6635479) B6635479
theorem B10092527 : Blo 690315 10092527 := bstep (se 1 (by rfl) ⟨7569395, by rfl⟩ : syracuseStep 10092527 = 15138791) B15138791
theorem B1310879 : Blo 690315 1310879 := bstep (se 1 (by rfl) ⟨983159, by rfl⟩ : syracuseStep 1310879 = 1966319) B1966319
theorem B17727821 : Blo 690315 17727821 := bstep (se 3 (by rfl) ⟨3323966, by rfl⟩ : syracuseStep 17727821 = 6647933) B6647933
theorem B5603813 : Blo 690315 5603813 := bstep (se 4 (by rfl) ⟨525357, by rfl⟩ : syracuseStep 5603813 = 1050715) B1050715
theorem B5604005 : Blo 690315 5604005 := bstep (se 4 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 5604005 = 1050751) B1050751
theorem B2491883 : Blo 690315 2491883 := bstep (se 1 (by rfl) ⟨1868912, by rfl⟩ : syracuseStep 2491883 = 3737825) B3737825
theorem B3507947 : Blo 690315 3507947 := bstep (se 1 (by rfl) ⟨2630960, by rfl⟩ : syracuseStep 3507947 = 5261921) B5261921
theorem B3508271 : Blo 690315 3508271 := bstep (se 1 (by rfl) ⟨2631203, by rfl⟩ : syracuseStep 3508271 = 5262407) B5262407
theorem B985375 : Blo 690315 985375 := bstep (se 1 (by rfl) ⟨739031, by rfl⟩ : syracuseStep 985375 = 1478063) B1478063
theorem B22448461 : Blo 690315 22448461 := bstep (se 3 (by rfl) ⟨4209086, by rfl⟩ : syracuseStep 22448461 = 8418173) B8418173
theorem B1575251 : Blo 690315 1575251 := bstep (se 1 (by rfl) ⟨1181438, by rfl⟩ : syracuseStep 1575251 = 2362877) B2362877
theorem B691015 : Blo 690315 691015 := bstep (se 1 (by rfl) ⟨518261, by rfl⟩ : syracuseStep 691015 = 1036523) B1036523
theorem B691183 : Blo 690315 691183 := bstep (se 1 (by rfl) ⟨518387, by rfl⟩ : syracuseStep 691183 = 1036775) B1036775
theorem B691355 : Blo 690315 691355 := bstep (se 1 (by rfl) ⟨518516, by rfl⟩ : syracuseStep 691355 = 1037033) B1037033
theorem B4984105 : Blo 690315 4984105 := bstep (se 2 (by rfl) ⟨1869039, by rfl⟩ : syracuseStep 4984105 = 3738079) B3738079
theorem B691951 : Blo 690315 691951 := bstep (se 1 (by rfl) ⟨518963, by rfl⟩ : syracuseStep 691951 = 1037927) B1037927
theorem B692255 : Blo 690315 692255 := bstep (se 1 (by rfl) ⟨519191, by rfl⟩ : syracuseStep 692255 = 1038383) B1038383
theorem B1970351 : Blo 690315 1970351 := bstep (se 1 (by rfl) ⟨1477763, by rfl⟩ : syracuseStep 1970351 = 2955527) B2955527
theorem B692507 : Blo 690315 692507 := bstep (se 1 (by rfl) ⟨519380, by rfl⟩ : syracuseStep 692507 = 1038761) B1038761
theorem B692763 : Blo 690315 692763 := bstep (se 1 (by rfl) ⟨519572, by rfl⟩ : syracuseStep 692763 = 1039145) B1039145
theorem B5902955 : Blo 690315 5902955 := bstep (se 1 (by rfl) ⟨4427216, by rfl⟩ : syracuseStep 5902955 = 8854433) B8854433
theorem B2495083 : Blo 690315 2495083 := bstep (se 1 (by rfl) ⟨1871312, by rfl⟩ : syracuseStep 2495083 = 3742625) B3742625
theorem B1479455 : Blo 690315 1479455 := bstep (se 1 (by rfl) ⟨1109591, by rfl⟩ : syracuseStep 1479455 = 2219183) B2219183
theorem B693119 : Blo 690315 693119 := bstep (se 1 (by rfl) ⟨519839, by rfl⟩ : syracuseStep 693119 = 1039679) B1039679
theorem B2954569 : Blo 690315 2954569 := bstep (se 2 (by rfl) ⟨1107963, by rfl⟩ : syracuseStep 2954569 = 2215927) B2215927
theorem B693807 : Blo 690315 693807 := bstep (se 1 (by rfl) ⟨520355, by rfl⟩ : syracuseStep 693807 = 1040711) B1040711
theorem B694119 : Blo 690315 694119 := bstep (se 1 (by rfl) ⟨520589, by rfl⟩ : syracuseStep 694119 = 1041179) B1041179
theorem B1284187 : Blo 690315 1284187 := bstep (se 1 (by rfl) ⟨963140, by rfl⟩ : syracuseStep 1284187 = 1926281) B1926281
theorem B1972583 : Blo 690315 1972583 := bstep (se 1 (by rfl) ⟨1479437, by rfl⟩ : syracuseStep 1972583 = 2958875) B2958875
theorem B3512807 : Blo 690315 3512807 := bstep (se 1 (by rfl) ⟨2634605, by rfl⟩ : syracuseStep 3512807 = 5269211) B5269211
theorem B2333177 : Blo 690315 2333177 := bstep (se 2 (by rfl) ⟨874941, by rfl⟩ : syracuseStep 2333177 = 1749883) B1749883
theorem B2333231 : Blo 690315 2333231 := bstep (se 1 (by rfl) ⟨1749923, by rfl⟩ : syracuseStep 2333231 = 3499847) B3499847
theorem B6659005 : Blo 690315 6659005 := bstep (se 3 (by rfl) ⟨1248563, by rfl⟩ : syracuseStep 6659005 = 2497127) B2497127
theorem B1482779 : Blo 690315 1482779 := bstep (se 1 (by rfl) ⟨1112084, by rfl⟩ : syracuseStep 1482779 = 2224169) B2224169
theorem B4202617 : Blo 690315 4202617 := bstep (se 2 (by rfl) ⟨1575981, by rfl⟩ : syracuseStep 4202617 = 3151963) B3151963
theorem B1974395 : Blo 690315 1974395 := bstep (se 1 (by rfl) ⟨1480796, by rfl⟩ : syracuseStep 1974395 = 2961593) B2961593
theorem B3514751 : Blo 690315 3514751 := bstep (se 1 (by rfl) ⟨2636063, by rfl⟩ : syracuseStep 3514751 = 5272127) B5272127
theorem B3744481 : Blo 690315 3744481 := bstep (se 2 (by rfl) ⟨1404180, by rfl⟩ : syracuseStep 3744481 = 2808361) B2808361
theorem B2337011 : Blo 690315 2337011 := bstep (se 1 (by rfl) ⟨1752758, by rfl⟩ : syracuseStep 2337011 = 3505517) B3505517
theorem B5908727 : Blo 690315 5908727 := bstep (se 1 (by rfl) ⟨4431545, by rfl⟩ : syracuseStep 5908727 = 8863091) B8863091
theorem B6728351 : Blo 690315 6728351 := bstep (se 1 (by rfl) ⟨5046263, by rfl⟩ : syracuseStep 6728351 = 10092527) B10092527
theorem B2109215 : Blo 690315 2109215 := bstep (se 1 (by rfl) ⟨1581911, by rfl⟩ : syracuseStep 2109215 = 3163823) B3163823
theorem B2633755 : Blo 690315 2633755 := bstep (se 1 (by rfl) ⟨1975316, by rfl⟩ : syracuseStep 2633755 = 3950633) B3950633
theorem B8434529 : Blo 690315 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B3322873 : Blo 690315 3322873 := bstep (se 2 (by rfl) ⟨1246077, by rfl⟩ : syracuseStep 3322873 = 2492155) B2492155
theorem B2373167 : Blo 690315 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B21346213 : Blo 690315 21346213 := bstep (se 4 (by rfl) ⟨2001207, by rfl⟩ : syracuseStep 21346213 = 4002415) B4002415
theorem B1751017 : Blo 690315 1751017 := bstep (se 2 (by rfl) ⟨656631, by rfl⟩ : syracuseStep 1751017 = 1313263) B1313263
theorem B3946715 : Blo 690315 3946715 := bstep (se 1 (by rfl) ⟨2960036, by rfl⟩ : syracuseStep 3946715 = 5920073) B5920073
theorem B1751291 : Blo 690315 1751291 := bstep (se 1 (by rfl) ⟨1313468, by rfl⟩ : syracuseStep 1751291 = 2626937) B2626937
theorem B1554875 : Blo 690315 1554875 := bstep (se 1 (by rfl) ⟨1166156, by rfl⟩ : syracuseStep 1554875 = 2332313) B2332313
theorem B1555199 : Blo 690315 1555199 := bstep (se 1 (by rfl) ⟨1166399, by rfl⟩ : syracuseStep 1555199 = 2332799) B2332799
theorem B1555271 : Blo 690315 1555271 := bstep (se 1 (by rfl) ⟨1166453, by rfl⟩ : syracuseStep 1555271 = 2332907) B2332907
theorem B5979379 : Blo 690315 5979379 := bstep (se 1 (by rfl) ⟨4484534, by rfl⟩ : syracuseStep 5979379 = 8969069) B8969069
theorem B2342303 : Blo 690315 2342303 := bstep (se 1 (by rfl) ⟨1756727, by rfl⟩ : syracuseStep 2342303 = 3513455) B3513455
theorem B1753447 : Blo 690315 1753447 := bstep (se 1 (by rfl) ⟨1315085, by rfl⟩ : syracuseStep 1753447 = 2630171) B2630171
theorem B1556927 : Blo 690315 1556927 := bstep (se 1 (by rfl) ⟨1167695, by rfl⟩ : syracuseStep 1556927 = 2335391) B2335391
theorem B7094953 : Blo 690315 7094953 := bstep (se 2 (by rfl) ⟨2660607, by rfl⟩ : syracuseStep 7094953 = 5321215) B5321215
theorem B1753883 : Blo 690315 1753883 := bstep (se 1 (by rfl) ⟨1315412, by rfl⟩ : syracuseStep 1753883 = 2630825) B2630825
theorem B6308675 : Blo 690315 6308675 := bstep (se 1 (by rfl) ⟨4731506, by rfl⟩ : syracuseStep 6308675 = 9463013) B9463013
theorem B1557755 : Blo 690315 1557755 := bstep (se 1 (by rfl) ⟨1168316, by rfl⟩ : syracuseStep 1557755 = 2336633) B2336633
theorem B1557881 : Blo 690315 1557881 := bstep (se 2 (by rfl) ⟨584205, by rfl⟩ : syracuseStep 1557881 = 1168411) B1168411
theorem B2803495 : Blo 690315 2803495 := bstep (se 1 (by rfl) ⟨2102621, by rfl⟩ : syracuseStep 2803495 = 4205243) B4205243
theorem B1558655 : Blo 690315 1558655 := bstep (se 1 (by rfl) ⟨1168991, by rfl⟩ : syracuseStep 1558655 = 2337983) B2337983
theorem B1165799 : Blo 690315 1165799 := bstep (se 1 (by rfl) ⟨874349, by rfl⟩ : syracuseStep 1165799 = 1748699) B1748699
theorem B1559735 : Blo 690315 1559735 := bstep (se 1 (by rfl) ⟨1169801, by rfl⟩ : syracuseStep 1559735 = 2339603) B2339603
theorem B1756343 : Blo 690315 1756343 := bstep (se 1 (by rfl) ⟨1317257, by rfl⟩ : syracuseStep 1756343 = 2634515) B2634515
theorem B1035515 : Blo 690315 1035515 := bstep (se 1 (by rfl) ⟨776636, by rfl⟩ : syracuseStep 1035515 = 1553273) B1553273
theorem B1167007 : Blo 690315 1167007 := bstep (se 1 (by rfl) ⟨875255, by rfl⟩ : syracuseStep 1167007 = 1750511) B1750511
theorem B1560347 : Blo 690315 1560347 := bstep (se 1 (by rfl) ⟨1170260, by rfl⟩ : syracuseStep 1560347 = 2340521) B2340521
theorem B1036223 : Blo 690315 1036223 := bstep (se 1 (by rfl) ⟨777167, by rfl⟩ : syracuseStep 1036223 = 1554335) B1554335
theorem B4214855 : Blo 690315 4214855 := bstep (se 1 (by rfl) ⟨3161141, by rfl⟩ : syracuseStep 4214855 = 6322283) B6322283
theorem B938153 : Blo 690315 938153 := bstep (se 2 (by rfl) ⟨351807, by rfl⟩ : syracuseStep 938153 = 703615) B703615
theorem B1167655 : Blo 690315 1167655 := bstep (se 1 (by rfl) ⟨875741, by rfl⟩ : syracuseStep 1167655 = 1751483) B1751483
theorem B1036841 : Blo 690315 1036841 := bstep (se 2 (by rfl) ⟨388815, by rfl⟩ : syracuseStep 1036841 = 777631) B777631
theorem B5264351 : Blo 690315 5264351 := bstep (se 1 (by rfl) ⟨3948263, by rfl⟩ : syracuseStep 5264351 = 7896527) B7896527
theorem B4379815 : Blo 690315 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B1168553 : Blo 690315 1168553 := bstep (se 2 (by rfl) ⟨438207, by rfl⟩ : syracuseStep 1168553 = 876415) B876415
theorem B1562039 : Blo 690315 1562039 := bstep (se 1 (by rfl) ⟨1171529, by rfl⟩ : syracuseStep 1562039 = 2343059) B2343059
theorem B4216411 : Blo 690315 4216411 := bstep (se 1 (by rfl) ⟨3162308, by rfl⟩ : syracuseStep 4216411 = 6324617) B6324617
theorem B1038191 : Blo 690315 1038191 := bstep (se 1 (by rfl) ⟨778643, by rfl⟩ : syracuseStep 1038191 = 1557287) B1557287
theorem B3331963 : Blo 690315 3331963 := bstep (se 1 (by rfl) ⟨2498972, by rfl⟩ : syracuseStep 3331963 = 4997945) B4997945
theorem B4216873 : Blo 690315 4216873 := bstep (se 2 (by rfl) ⟨1581327, by rfl⟩ : syracuseStep 4216873 = 3162655) B3162655
theorem B20011049 : Blo 690315 20011049 := bstep (se 2 (by rfl) ⟨7504143, by rfl⟩ : syracuseStep 20011049 = 15008287) B15008287
theorem B3496283 : Blo 690315 3496283 := bstep (se 1 (by rfl) ⟨2622212, by rfl⟩ : syracuseStep 3496283 = 5244425) B5244425
theorem B1038815 : Blo 690315 1038815 := bstep (se 1 (by rfl) ⟨779111, by rfl⟩ : syracuseStep 1038815 = 1558223) B1558223
theorem B1039775 : Blo 690315 1039775 := bstep (se 1 (by rfl) ⟨779831, by rfl⟩ : syracuseStep 1039775 = 1559663) B1559663
theorem B1039919 : Blo 690315 1039919 := bstep (se 1 (by rfl) ⟨779939, by rfl⟩ : syracuseStep 1039919 = 1559879) B1559879
theorem B1171631 : Blo 690315 1171631 := bstep (se 1 (by rfl) ⟨878723, by rfl⟩ : syracuseStep 1171631 = 1757447) B1757447
theorem B6644551 : Blo 690315 6644551 := bstep (se 1 (by rfl) ⟨4983413, by rfl⟩ : syracuseStep 6644551 = 9966827) B9966827
theorem B3335579 : Blo 690315 3335579 := bstep (se 1 (by rfl) ⟨2501684, by rfl⟩ : syracuseStep 3335579 = 5003369) B5003369
theorem B24045245 : Blo 690315 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B3500171 : Blo 690315 3500171 := bstep (se 1 (by rfl) ⟨2625128, by rfl⟩ : syracuseStep 3500171 = 5250257) B5250257
theorem B12610181 : Blo 690315 12610181 := bstep (se 4 (by rfl) ⟨1182204, by rfl⟩ : syracuseStep 12610181 = 2364409) B2364409
theorem B3501305 : Blo 690315 3501305 := bstep (se 2 (by rfl) ⟨1312989, by rfl⟩ : syracuseStep 3501305 = 2625979) B2625979
theorem B58453325 : Blo 690315 58453325 := bstep (se 3 (by rfl) ⟨10959998, by rfl⟩ : syracuseStep 58453325 = 21919997) B21919997
theorem B28340063 : Blo 690315 28340063 := bstep (se 1 (by rfl) ⟨21255047, by rfl⟩ : syracuseStep 28340063 = 42510095) B42510095
theorem B3502439 : Blo 690315 3502439 := bstep (se 1 (by rfl) ⟨2626829, by rfl⟩ : syracuseStep 3502439 = 5253659) B5253659
theorem B3733391 : Blo 690315 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B3504383 : Blo 690315 3504383 := bstep (se 1 (by rfl) ⟨2628287, by rfl⟩ : syracuseStep 3504383 = 5256575) B5256575
theorem B1867483 : Blo 690315 1867483 := bstep (se 1 (by rfl) ⟨1400612, by rfl⟩ : syracuseStep 1867483 = 2801225) B2801225
theorem B5898203 : Blo 690315 5898203 := bstep (se 1 (by rfl) ⟨4423652, by rfl⟩ : syracuseStep 5898203 = 8847305) B8847305
theorem B5603489 : Blo 690315 5603489 := bstep (se 2 (by rfl) ⟨2101308, by rfl⟩ : syracuseStep 5603489 = 4202617) B4202617
theorem B3735875 : Blo 690315 3735875 := bstep (se 1 (by rfl) ⟨2801906, by rfl⟩ : syracuseStep 3735875 = 5603813) B5603813
theorem B1050167 : Blo 690315 1050167 := bstep (se 1 (by rfl) ⟨787625, by rfl⟩ : syracuseStep 1050167 = 1575251) B1575251
theorem B14944013 : Blo 690315 14944013 := bstep (se 3 (by rfl) ⟨2802002, by rfl⟩ : syracuseStep 14944013 = 5604005) B5604005
theorem B690343 : Blo 690315 690343 := bstep (se 1 (by rfl) ⟨517757, by rfl⟩ : syracuseStep 690343 = 1035515) B1035515
theorem B3737993 : Blo 690315 3737993 := bstep (se 2 (by rfl) ⟨1401747, by rfl⟩ : syracuseStep 3737993 = 2803495) B2803495
theorem B690815 : Blo 690315 690815 := bstep (se 1 (by rfl) ⟨518111, by rfl⟩ : syracuseStep 690815 = 1036223) B1036223
theorem B1313567 : Blo 690315 1313567 := bstep (se 1 (by rfl) ⟨985175, by rfl⟩ : syracuseStep 1313567 = 1970351) B1970351
theorem B691227 : Blo 690315 691227 := bstep (se 1 (by rfl) ⟨518420, by rfl⟩ : syracuseStep 691227 = 1036841) B1036841
theorem B1313833 : Blo 690315 1313833 := bstep (se 2 (by rfl) ⟨492687, by rfl⟩ : syracuseStep 1313833 = 985375) B985375
theorem B3935303 : Blo 690315 3935303 := bstep (se 1 (by rfl) ⟨2951477, by rfl⟩ : syracuseStep 3935303 = 5902955) B5902955
theorem B986303 : Blo 690315 986303 := bstep (se 1 (by rfl) ⟨739727, by rfl⟩ : syracuseStep 986303 = 1479455) B1479455
theorem B3509567 : Blo 690315 3509567 := bstep (se 1 (by rfl) ⟨2632175, by rfl⟩ : syracuseStep 3509567 = 5264351) B5264351
theorem B692127 : Blo 690315 692127 := bstep (se 1 (by rfl) ⟨519095, by rfl⟩ : syracuseStep 692127 = 1038191) B1038191
theorem B13340699 : Blo 690315 13340699 := bstep (se 1 (by rfl) ⟨10005524, by rfl⟩ : syracuseStep 13340699 = 20011049) B20011049
theorem B2330855 : Blo 690315 2330855 := bstep (se 1 (by rfl) ⟨1748141, by rfl⟩ : syracuseStep 2330855 = 3496283) B3496283
theorem B1315055 : Blo 690315 1315055 := bstep (se 1 (by rfl) ⟨986291, by rfl⟩ : syracuseStep 1315055 = 1972583) B1972583
theorem B692543 : Blo 690315 692543 := bstep (se 1 (by rfl) ⟨519407, by rfl⟩ : syracuseStep 692543 = 1038815) B1038815
theorem B693183 : Blo 690315 693183 := bstep (se 1 (by rfl) ⟨519887, by rfl⟩ : syracuseStep 693183 = 1039775) B1039775
theorem B693279 : Blo 690315 693279 := bstep (se 1 (by rfl) ⟨519959, by rfl⟩ : syracuseStep 693279 = 1039919) B1039919
theorem B988519 : Blo 690315 988519 := bstep (se 1 (by rfl) ⟨741389, by rfl⟩ : syracuseStep 988519 = 1482779) B1482779
theorem B3511673 : Blo 690315 3511673 := bstep (se 2 (by rfl) ⟨1316877, by rfl⟩ : syracuseStep 3511673 = 2633755) B2633755
theorem B1316263 : Blo 690315 1316263 := bstep (se 1 (by rfl) ⟨987197, by rfl⟩ : syracuseStep 1316263 = 1974395) B1974395
theorem B16030163 : Blo 690315 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B4430497 : Blo 690315 4430497 := bstep (se 2 (by rfl) ⟨1661436, by rfl⟩ : syracuseStep 4430497 = 3322873) B3322873
theorem B2333447 : Blo 690315 2333447 := bstep (se 1 (by rfl) ⟨1750085, by rfl⟩ : syracuseStep 2333447 = 3500171) B3500171
theorem B3939151 : Blo 690315 3939151 := bstep (se 1 (by rfl) ⟨2954363, by rfl⟩ : syracuseStep 3939151 = 5908727) B5908727
theorem B3939425 : Blo 690315 3939425 := bstep (se 2 (by rfl) ⟨1477284, by rfl⟩ : syracuseStep 3939425 = 2954569) B2954569
theorem B2334203 : Blo 690315 2334203 := bstep (se 1 (by rfl) ⟨1750652, by rfl⟩ : syracuseStep 2334203 = 3501305) B3501305
theorem B38968883 : Blo 690315 38968883 := bstep (se 1 (by rfl) ⟨29226662, by rfl⟩ : syracuseStep 38968883 = 58453325) B58453325
theorem B2334689 : Blo 690315 2334689 := bstep (se 2 (by rfl) ⟨875508, by rfl⟩ : syracuseStep 2334689 = 1751017) B1751017
theorem B1712249 : Blo 690315 1712249 := bstep (se 2 (by rfl) ⟨642093, by rfl⟩ : syracuseStep 1712249 = 1284187) B1284187
theorem B2334959 : Blo 690315 2334959 := bstep (se 1 (by rfl) ⟨1751219, by rfl⟩ : syracuseStep 2334959 = 3502439) B3502439
theorem B1582111 : Blo 690315 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B2631143 : Blo 690315 2631143 := bstep (se 1 (by rfl) ⟨1973357, by rfl⟩ : syracuseStep 2631143 = 3946715) B3946715
theorem B2336255 : Blo 690315 2336255 := bstep (se 1 (by rfl) ⟨1752191, by rfl⟩ : syracuseStep 2336255 = 3504383) B3504383
theorem B7972505 : Blo 690315 7972505 := bstep (se 2 (by rfl) ⟨2989689, by rfl⟩ : syracuseStep 7972505 = 5979379) B5979379
theorem B2501741 : Blo 690315 2501741 := bstep (se 3 (by rfl) ⟨469076, by rfl⟩ : syracuseStep 2501741 = 938153) B938153
theorem B2337929 : Blo 690315 2337929 := bstep (se 2 (by rfl) ⟨876723, by rfl⟩ : syracuseStep 2337929 = 1753447) B1753447
theorem B4205783 : Blo 690315 4205783 := bstep (se 1 (by rfl) ⟨3154337, by rfl⟩ : syracuseStep 4205783 = 6308675) B6308675
theorem B4992641 : Blo 690315 4992641 := bstep (se 2 (by rfl) ⟨1872240, by rfl⟩ : syracuseStep 4992641 = 3744481) B3744481
theorem B8859401 : Blo 690315 8859401 := bstep (se 2 (by rfl) ⟨3322275, by rfl⟩ : syracuseStep 8859401 = 6644551) B6644551
theorem B2338631 : Blo 690315 2338631 := bstep (se 1 (by rfl) ⟨1753973, by rfl⟩ : syracuseStep 2338631 = 3507947) B3507947
theorem B2338847 : Blo 690315 2338847 := bstep (se 1 (by rfl) ⟨1754135, by rfl⟩ : syracuseStep 2338847 = 3508271) B3508271
theorem B29931281 : Blo 690315 29931281 := bstep (se 2 (by rfl) ⟨11224230, by rfl⟩ : syracuseStep 29931281 = 22448461) B22448461
theorem B2341871 : Blo 690315 2341871 := bstep (se 1 (by rfl) ⟨1756403, by rfl⟩ : syracuseStep 2341871 = 3512807) B3512807
theorem B1555451 : Blo 690315 1555451 := bstep (se 1 (by rfl) ⟨1166588, by rfl⟩ : syracuseStep 1555451 = 2333177) B2333177
theorem B1555487 : Blo 690315 1555487 := bstep (se 1 (by rfl) ⟨1166615, by rfl⟩ : syracuseStep 1555487 = 2333231) B2333231
theorem B1556009 : Blo 690315 1556009 := bstep (se 2 (by rfl) ⟨583503, by rfl⟩ : syracuseStep 1556009 = 1167007) B1167007
theorem B2343167 : Blo 690315 2343167 := bstep (se 1 (by rfl) ⟨1757375, by rfl⟩ : syracuseStep 2343167 = 3514751) B3514751
theorem B1556873 : Blo 690315 1556873 := bstep (se 2 (by rfl) ⟨583827, by rfl⟩ : syracuseStep 1556873 = 1167655) B1167655
theorem B3326777 : Blo 690315 3326777 := bstep (se 2 (by rfl) ⟨1247541, by rfl⟩ : syracuseStep 3326777 = 2495083) B2495083
theorem B1558007 : Blo 690315 1558007 := bstep (se 1 (by rfl) ⟨1168505, by rfl⟩ : syracuseStep 1558007 = 2337011) B2337011
theorem B17942269 : Blo 690315 17942269 := bstep (se 3 (by rfl) ⟨3364175, by rfl⟩ : syracuseStep 17942269 = 6728351) B6728351
theorem B8406787 : Blo 690315 8406787 := bstep (se 1 (by rfl) ⟨6305090, by rfl⟩ : syracuseStep 8406787 = 12610181) B12610181
theorem B5621881 : Blo 690315 5621881 := bstep (se 2 (by rfl) ⟨2108205, by rfl⟩ : syracuseStep 5621881 = 4216411) B4216411
theorem B4442617 : Blo 690315 4442617 := bstep (se 2 (by rfl) ⟨1665981, by rfl⟩ : syracuseStep 4442617 = 3331963) B3331963
theorem B28461617 : Blo 690315 28461617 := bstep (se 2 (by rfl) ⟨10673106, by rfl⟩ : syracuseStep 28461617 = 21346213) B21346213
theorem B18893375 : Blo 690315 18893375 := bstep (se 1 (by rfl) ⟨14170031, by rfl⟩ : syracuseStep 18893375 = 28340063) B28340063
theorem B5622497 : Blo 690315 5622497 := bstep (se 2 (by rfl) ⟨2108436, by rfl⟩ : syracuseStep 5622497 = 4216873) B4216873
theorem B5623019 : Blo 690315 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B1167527 : Blo 690315 1167527 := bstep (se 1 (by rfl) ⟨875645, by rfl⟩ : syracuseStep 1167527 = 1751291) B1751291
theorem B1036583 : Blo 690315 1036583 := bstep (se 1 (by rfl) ⟨777437, by rfl⟩ : syracuseStep 1036583 = 1554875) B1554875
theorem B1036799 : Blo 690315 1036799 := bstep (se 1 (by rfl) ⟨777599, by rfl⟩ : syracuseStep 1036799 = 1555199) B1555199
theorem B1036847 : Blo 690315 1036847 := bstep (se 1 (by rfl) ⟨777635, by rfl⟩ : syracuseStep 1036847 = 1555271) B1555271
theorem B1561535 : Blo 690315 1561535 := bstep (se 1 (by rfl) ⟨1171151, by rfl⟩ : syracuseStep 1561535 = 2342303) B2342303
theorem B873919 : Blo 690315 873919 := bstep (se 1 (by rfl) ⟨655439, by rfl⟩ : syracuseStep 873919 = 1310879) B1310879
theorem B11818547 : Blo 690315 11818547 := bstep (se 1 (by rfl) ⟨8863910, by rfl⟩ : syracuseStep 11818547 = 17727821) B17727821
theorem B1037951 : Blo 690315 1037951 := bstep (se 1 (by rfl) ⟨778463, by rfl⟩ : syracuseStep 1037951 = 1556927) B1556927
theorem B1169255 : Blo 690315 1169255 := bstep (se 1 (by rfl) ⟨876941, by rfl⟩ : syracuseStep 1169255 = 1753883) B1753883
theorem B1038503 : Blo 690315 1038503 := bstep (se 1 (by rfl) ⟨778877, by rfl⟩ : syracuseStep 1038503 = 1557755) B1557755
theorem B9459937 : Blo 690315 9459937 := bstep (se 2 (by rfl) ⟨3547476, by rfl⟩ : syracuseStep 9459937 = 7094953) B7094953
theorem B1038587 : Blo 690315 1038587 := bstep (se 1 (by rfl) ⟨778940, by rfl⟩ : syracuseStep 1038587 = 1557881) B1557881
theorem B1661255 : Blo 690315 1661255 := bstep (se 1 (by rfl) ⟨1245941, by rfl⟩ : syracuseStep 1661255 = 2491883) B2491883
theorem B1039103 : Blo 690315 1039103 := bstep (se 1 (by rfl) ⟨779327, by rfl⟩ : syracuseStep 1039103 = 1558655) B1558655
theorem B777199 : Blo 690315 777199 := bstep (se 1 (by rfl) ⟨582899, by rfl⟩ : syracuseStep 777199 = 1165799) B1165799
theorem B1039823 : Blo 690315 1039823 := bstep (se 1 (by rfl) ⟨779867, by rfl⟩ : syracuseStep 1039823 = 1559735) B1559735
theorem B1170895 : Blo 690315 1170895 := bstep (se 1 (by rfl) ⟨878171, by rfl⟩ : syracuseStep 1170895 = 1756343) B1756343
theorem B1040231 : Blo 690315 1040231 := bstep (se 1 (by rfl) ⟨780173, by rfl⟩ : syracuseStep 1040231 = 1560347) B1560347
theorem B2809903 : Blo 690315 2809903 := bstep (se 1 (by rfl) ⟨2107427, by rfl⟩ : syracuseStep 2809903 = 4214855) B4214855
theorem B779035 : Blo 690315 779035 := bstep (se 1 (by rfl) ⟨584276, by rfl⟩ : syracuseStep 779035 = 1168553) B1168553
theorem B1041359 : Blo 690315 1041359 := bstep (se 1 (by rfl) ⟨781019, by rfl⟩ : syracuseStep 1041359 = 1562039) B1562039
theorem B6645473 : Blo 690315 6645473 := bstep (se 2 (by rfl) ⟨2492052, by rfl⟩ : syracuseStep 6645473 = 4984105) B4984105
theorem B781087 : Blo 690315 781087 := bstep (se 1 (by rfl) ⟨585815, by rfl⟩ : syracuseStep 781087 = 1171631) B1171631
theorem B23359013 : Blo 690315 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B2223719 : Blo 690315 2223719 := bstep (se 1 (by rfl) ⟨1667789, by rfl⟩ : syracuseStep 2223719 = 3335579) B3335579
theorem B1406143 : Blo 690315 1406143 := bstep (se 1 (by rfl) ⟨1054607, by rfl⟩ : syracuseStep 1406143 = 2109215) B2109215
theorem B8878673 : Blo 690315 8878673 := bstep (se 2 (by rfl) ⟨3329502, by rfl⟩ : syracuseStep 8878673 = 6659005) B6659005
theorem B2488927 : Blo 690315 2488927 := bstep (se 1 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 2488927 = 3733391) B3733391
theorem B2489977 : Blo 690315 2489977 := bstep (se 2 (by rfl) ⟨933741, by rfl⟩ : syracuseStep 2489977 = 1867483) B1867483
theorem B3932135 : Blo 690315 3932135 := bstep (se 1 (by rfl) ⟨2949101, by rfl⟩ : syracuseStep 3932135 = 5898203) B5898203
theorem B3735659 : Blo 690315 3735659 := bstep (se 1 (by rfl) ⟨2801744, by rfl⟩ : syracuseStep 3735659 = 5603489) B5603489
theorem B2490583 : Blo 690315 2490583 := bstep (se 1 (by rfl) ⟨1867937, by rfl⟩ : syracuseStep 2490583 = 3735875) B3735875
theorem B3506813 : Blo 690315 3506813 := bstep (se 3 (by rfl) ⟨657527, by rfl⟩ : syracuseStep 3506813 = 1315055) B1315055
theorem B9962675 : Blo 690315 9962675 := bstep (se 1 (by rfl) ⟨7472006, by rfl⟩ : syracuseStep 9962675 = 14944013) B14944013
theorem B18974411 : Blo 690315 18974411 := bstep (se 1 (by rfl) ⟨14230808, by rfl⟩ : syracuseStep 18974411 = 28461617) B28461617
theorem B2623535 : Blo 690315 2623535 := bstep (se 1 (by rfl) ⟨1967651, by rfl⟩ : syracuseStep 2623535 = 3935303) B3935303
theorem B23923025 : Blo 690315 23923025 := bstep (se 2 (by rfl) ⟨8971134, by rfl⟩ : syracuseStep 23923025 = 17942269) B17942269
theorem B11209049 : Blo 690315 11209049 := bstep (se 2 (by rfl) ⟨4203393, by rfl⟩ : syracuseStep 11209049 = 8406787) B8406787
theorem B691055 : Blo 690315 691055 := bstep (se 1 (by rfl) ⟨518291, by rfl⟩ : syracuseStep 691055 = 1036583) B1036583
theorem B691199 : Blo 690315 691199 := bstep (se 1 (by rfl) ⟨518399, by rfl⟩ : syracuseStep 691199 = 1036799) B1036799
theorem B691231 : Blo 690315 691231 := bstep (se 1 (by rfl) ⟨518423, by rfl⟩ : syracuseStep 691231 = 1036847) B1036847
theorem B691967 : Blo 690315 691967 := bstep (se 1 (by rfl) ⟨518975, by rfl⟩ : syracuseStep 691967 = 1037951) B1037951
theorem B692335 : Blo 690315 692335 := bstep (se 1 (by rfl) ⟨519251, by rfl⟩ : syracuseStep 692335 = 1038503) B1038503
theorem B692391 : Blo 690315 692391 := bstep (se 1 (by rfl) ⟨519293, by rfl⟩ : syracuseStep 692391 = 1038587) B1038587
theorem B692735 : Blo 690315 692735 := bstep (se 1 (by rfl) ⟨519551, by rfl⟩ : syracuseStep 692735 = 1039103) B1039103
theorem B2626283 : Blo 690315 2626283 := bstep (se 1 (by rfl) ⟨1969712, by rfl⟩ : syracuseStep 2626283 = 3939425) B3939425
theorem B693215 : Blo 690315 693215 := bstep (se 1 (by rfl) ⟨519911, by rfl⟩ : syracuseStep 693215 = 1039823) B1039823
theorem B693487 : Blo 690315 693487 := bstep (se 1 (by rfl) ⟨520115, by rfl⟩ : syracuseStep 693487 = 1040231) B1040231
theorem B694239 : Blo 690315 694239 := bstep (se 1 (by rfl) ⟨520679, by rfl⟩ : syracuseStep 694239 = 1041359) B1041359
theorem B9967981 : Blo 690315 9967981 := bstep (se 3 (by rfl) ⟨1868996, by rfl⟩ : syracuseStep 9967981 = 3737993) B3737993
theorem B5315003 : Blo 690315 5315003 := bstep (se 1 (by rfl) ⟨3986252, by rfl⟩ : syracuseStep 5315003 = 7972505) B7972505
theorem B4430315 : Blo 690315 4430315 := bstep (se 1 (by rfl) ⟨3322736, by rfl⟩ : syracuseStep 4430315 = 6645473) B6645473
theorem B1318025 : Blo 690315 1318025 := bstep (se 2 (by rfl) ⟨494259, by rfl⟩ : syracuseStep 1318025 = 988519) B988519
theorem B15572675 : Blo 690315 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B1482479 : Blo 690315 1482479 := bstep (se 1 (by rfl) ⟨1111859, by rfl⟩ : syracuseStep 1482479 = 2223719) B2223719
theorem B5906267 : Blo 690315 5906267 := bstep (se 1 (by rfl) ⟨4429700, by rfl⟩ : syracuseStep 5906267 = 8859401) B8859401
theorem B2630141 : Blo 690315 2630141 := bstep (se 3 (by rfl) ⟨493151, by rfl⟩ : syracuseStep 2630141 = 986303) B986303
theorem B3318569 : Blo 690315 3318569 := bstep (se 2 (by rfl) ⟨1244463, by rfl⟩ : syracuseStep 3318569 = 2488927) B2488927
theorem B5907329 : Blo 690315 5907329 := bstep (se 2 (by rfl) ⟨2215248, by rfl⟩ : syracuseStep 5907329 = 4430497) B4430497
theorem B5252201 : Blo 690315 5252201 := bstep (se 2 (by rfl) ⟨1969575, by rfl⟩ : syracuseStep 5252201 = 3939151) B3939151
theorem B3319969 : Blo 690315 3319969 := bstep (se 2 (by rfl) ⟨1244988, by rfl⟩ : syracuseStep 3319969 = 2489977) B2489977
theorem B3746537 : Blo 690315 3746537 := bstep (se 2 (by rfl) ⟨1404951, by rfl⟩ : syracuseStep 3746537 = 2809903) B2809903
theorem B12595583 : Blo 690315 12595583 := bstep (se 1 (by rfl) ⟨9446687, by rfl⟩ : syracuseStep 12595583 = 18893375) B18893375
theorem B3748331 : Blo 690315 3748331 := bstep (se 1 (by rfl) ⟨2811248, by rfl⟩ : syracuseStep 3748331 = 5622497) B5622497
theorem B3748679 : Blo 690315 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B2339711 : Blo 690315 2339711 := bstep (se 1 (by rfl) ⟨1754783, by rfl⟩ : syracuseStep 2339711 = 3509567) B3509567
theorem B8893799 : Blo 690315 8893799 := bstep (se 1 (by rfl) ⟨6670349, by rfl⟩ : syracuseStep 8893799 = 13340699) B13340699
theorem B1553903 : Blo 690315 1553903 := bstep (se 1 (by rfl) ⟨1165427, by rfl⟩ : syracuseStep 1553903 = 2330855) B2330855
theorem B2341115 : Blo 690315 2341115 := bstep (se 1 (by rfl) ⟨1755836, by rfl⟩ : syracuseStep 2341115 = 3511673) B3511673
theorem B7879031 : Blo 690315 7879031 := bstep (se 1 (by rfl) ⟨5909273, by rfl⟩ : syracuseStep 7879031 = 11818547) B11818547
theorem B1751777 : Blo 690315 1751777 := bstep (se 2 (by rfl) ⟨656916, by rfl⟩ : syracuseStep 1751777 = 1313833) B1313833
theorem B2800445 : Blo 690315 2800445 := bstep (se 3 (by rfl) ⟨525083, by rfl⟩ : syracuseStep 2800445 = 1050167) B1050167
theorem B1555631 : Blo 690315 1555631 := bstep (se 1 (by rfl) ⟨1166723, by rfl⟩ : syracuseStep 1555631 = 2333447) B2333447
theorem B1556135 : Blo 690315 1556135 := bstep (se 1 (by rfl) ⟨1167101, by rfl⟩ : syracuseStep 1556135 = 2334203) B2334203
theorem B1556459 : Blo 690315 1556459 := bstep (se 1 (by rfl) ⟨1167344, by rfl⟩ : syracuseStep 1556459 = 2334689) B2334689
theorem B1556639 : Blo 690315 1556639 := bstep (se 1 (by rfl) ⟨1167479, by rfl⟩ : syracuseStep 1556639 = 2334959) B2334959
theorem B8437925 : Blo 690315 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B1754095 : Blo 690315 1754095 := bstep (se 1 (by rfl) ⟨1315571, by rfl⟩ : syracuseStep 1754095 = 2631143) B2631143
theorem B1557503 : Blo 690315 1557503 := bstep (se 1 (by rfl) ⟨1168127, by rfl⟩ : syracuseStep 1557503 = 2336255) B2336255
theorem B42747101 : Blo 690315 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B1755017 : Blo 690315 1755017 := bstep (se 2 (by rfl) ⟨658131, by rfl⟩ : syracuseStep 1755017 = 1316263) B1316263
theorem B1165225 : Blo 690315 1165225 := bstep (se 2 (by rfl) ⟨436959, by rfl⟩ : syracuseStep 1165225 = 873919) B873919
theorem B1558619 : Blo 690315 1558619 := bstep (se 1 (by rfl) ⟨1168964, by rfl⟩ : syracuseStep 1558619 = 2337929) B2337929
theorem B2803855 : Blo 690315 2803855 := bstep (se 1 (by rfl) ⟨2102891, by rfl⟩ : syracuseStep 2803855 = 4205783) B4205783
theorem B3328427 : Blo 690315 3328427 := bstep (se 1 (by rfl) ⟨2496320, by rfl⟩ : syracuseStep 3328427 = 4992641) B4992641
theorem B1559087 : Blo 690315 1559087 := bstep (se 1 (by rfl) ⟨1169315, by rfl⟩ : syracuseStep 1559087 = 2338631) B2338631
theorem B1559231 : Blo 690315 1559231 := bstep (se 1 (by rfl) ⟨1169423, by rfl⟩ : syracuseStep 1559231 = 2338847) B2338847
theorem B1036265 : Blo 690315 1036265 := bstep (se 2 (by rfl) ⟨388599, by rfl⟩ : syracuseStep 1036265 = 777199) B777199
theorem B5919115 : Blo 690315 5919115 := bstep (se 1 (by rfl) ⟨4439336, by rfl⟩ : syracuseStep 5919115 = 8878673) B8878673
theorem B1561193 : Blo 690315 1561193 := bstep (se 2 (by rfl) ⟨585447, by rfl⟩ : syracuseStep 1561193 = 1170895) B1170895
theorem B1561247 : Blo 690315 1561247 := bstep (se 1 (by rfl) ⟨1170935, by rfl⟩ : syracuseStep 1561247 = 2341871) B2341871
theorem B1036967 : Blo 690315 1036967 := bstep (se 1 (by rfl) ⟨777725, by rfl⟩ : syracuseStep 1036967 = 1555451) B1555451
theorem B1036991 : Blo 690315 1036991 := bstep (se 1 (by rfl) ⟨777743, by rfl⟩ : syracuseStep 1036991 = 1555487) B1555487
theorem B1037339 : Blo 690315 1037339 := bstep (se 1 (by rfl) ⟨778004, by rfl⟩ : syracuseStep 1037339 = 1556009) B1556009
theorem B1562111 : Blo 690315 1562111 := bstep (se 1 (by rfl) ⟨1171583, by rfl⟩ : syracuseStep 1562111 = 2343167) B2343167
theorem B1037915 : Blo 690315 1037915 := bstep (se 1 (by rfl) ⟨778436, by rfl⟩ : syracuseStep 1037915 = 1556873) B1556873
theorem B2217851 : Blo 690315 2217851 := bstep (se 1 (by rfl) ⟨1663388, by rfl⟩ : syracuseStep 2217851 = 3326777) B3326777
theorem B1038671 : Blo 690315 1038671 := bstep (se 1 (by rfl) ⟨779003, by rfl⟩ : syracuseStep 1038671 = 1558007) B1558007
theorem B1038713 : Blo 690315 1038713 := bstep (se 2 (by rfl) ⟨389517, by rfl⟩ : syracuseStep 1038713 = 779035) B779035
theorem B875711 : Blo 690315 875711 := bstep (se 1 (by rfl) ⟨656783, by rfl⟩ : syracuseStep 875711 = 1313567) B1313567
theorem B778351 : Blo 690315 778351 := bstep (se 1 (by rfl) ⟨583763, by rfl⟩ : syracuseStep 778351 = 1167527) B1167527
theorem B7495841 : Blo 690315 7495841 := bstep (se 2 (by rfl) ⟨2810940, by rfl⟩ : syracuseStep 7495841 = 5621881) B5621881
theorem B1041023 : Blo 690315 1041023 := bstep (se 1 (by rfl) ⟨780767, by rfl⟩ : syracuseStep 1041023 = 1561535) B1561535
theorem B5923489 : Blo 690315 5923489 := bstep (se 2 (by rfl) ⟨2221308, by rfl⟩ : syracuseStep 5923489 = 4442617) B4442617
theorem B1041449 : Blo 690315 1041449 := bstep (se 2 (by rfl) ⟨390543, by rfl⟩ : syracuseStep 1041449 = 781087) B781087
theorem B779503 : Blo 690315 779503 := bstep (se 1 (by rfl) ⟨584627, by rfl⟩ : syracuseStep 779503 = 1169255) B1169255
theorem B1107503 : Blo 690315 1107503 := bstep (se 1 (by rfl) ⟨830627, by rfl⟩ : syracuseStep 1107503 = 1661255) B1661255
theorem B25979255 : Blo 690315 25979255 := bstep (se 1 (by rfl) ⟨19484441, by rfl⟩ : syracuseStep 25979255 = 38968883) B38968883
theorem B1141499 : Blo 690315 1141499 := bstep (se 1 (by rfl) ⟨856124, by rfl⟩ : syracuseStep 1141499 = 1712249) B1712249
theorem B7499429 : Blo 690315 7499429 := bstep (se 4 (by rfl) ⟨703071, by rfl⟩ : syracuseStep 7499429 = 1406143) B1406143
theorem B1667827 : Blo 690315 1667827 := bstep (se 1 (by rfl) ⟨1250870, by rfl⟩ : syracuseStep 1667827 = 2501741) B2501741
theorem B12613249 : Blo 690315 12613249 := bstep (se 2 (by rfl) ⟨4729968, by rfl⟩ : syracuseStep 12613249 = 9459937) B9459937
theorem B19954187 : Blo 690315 19954187 := bstep (se 1 (by rfl) ⟨14965640, by rfl⟩ : syracuseStep 19954187 = 29931281) B29931281
theorem B2621423 : Blo 690315 2621423 := bstep (se 1 (by rfl) ⟨1966067, by rfl⟩ : syracuseStep 2621423 = 3932135) B3932135
theorem B2490439 : Blo 690315 2490439 := bstep (se 1 (by rfl) ⟨1867829, by rfl⟩ : syracuseStep 2490439 = 3735659) B3735659
theorem B7897985 : Blo 690315 7897985 := bstep (se 2 (by rfl) ⟨2961744, by rfl⟩ : syracuseStep 7897985 = 5923489) B5923489
theorem B12649607 : Blo 690315 12649607 := bstep (se 1 (by rfl) ⟨9487205, by rfl⟩ : syracuseStep 12649607 = 18974411) B18974411
theorem B7472699 : Blo 690315 7472699 := bstep (se 1 (by rfl) ⟨5604524, by rfl⟩ : syracuseStep 7472699 = 11209049) B11209049
theorem B690843 : Blo 690315 690843 := bstep (se 1 (by rfl) ⟨518132, by rfl⟩ : syracuseStep 690843 = 1036265) B1036265
theorem B3738473 : Blo 690315 3738473 := bstep (se 2 (by rfl) ⟨1401927, by rfl⟩ : syracuseStep 3738473 = 2803855) B2803855
theorem B4426625 : Blo 690315 4426625 := bstep (se 2 (by rfl) ⟨1659984, by rfl⟩ : syracuseStep 4426625 = 3319969) B3319969
theorem B691311 : Blo 690315 691311 := bstep (se 1 (by rfl) ⟨518483, by rfl⟩ : syracuseStep 691311 = 1036967) B1036967
theorem B691327 : Blo 690315 691327 := bstep (se 1 (by rfl) ⟨518495, by rfl⟩ : syracuseStep 691327 = 1036991) B1036991
theorem B691559 : Blo 690315 691559 := bstep (se 1 (by rfl) ⟨518669, by rfl⟩ : syracuseStep 691559 = 1037339) B1037339
theorem B691943 : Blo 690315 691943 := bstep (se 1 (by rfl) ⟨518957, by rfl⟩ : syracuseStep 691943 = 1037915) B1037915
theorem B1478567 : Blo 690315 1478567 := bstep (se 1 (by rfl) ⟨1108925, by rfl⟩ : syracuseStep 1478567 = 2217851) B2217851
theorem B692447 : Blo 690315 692447 := bstep (se 1 (by rfl) ⟨519335, by rfl⟩ : syracuseStep 692447 = 1038671) B1038671
theorem B692475 : Blo 690315 692475 := bstep (se 1 (by rfl) ⟨519356, by rfl⟩ : syracuseStep 692475 = 1038713) B1038713
theorem B3543335 : Blo 690315 3543335 := bstep (se 1 (by rfl) ⟨2657501, by rfl⟩ : syracuseStep 3543335 = 5315003) B5315003
theorem B988319 : Blo 690315 988319 := bstep (se 1 (by rfl) ⟨741239, by rfl⟩ : syracuseStep 988319 = 1482479) B1482479
theorem B3937511 : Blo 690315 3937511 := bstep (se 1 (by rfl) ⟨2953133, by rfl⟩ : syracuseStep 3937511 = 5906267) B5906267
theorem B694015 : Blo 690315 694015 := bstep (se 1 (by rfl) ⟨520511, by rfl⟩ : syracuseStep 694015 = 1041023) B1041023
theorem B3938219 : Blo 690315 3938219 := bstep (se 1 (by rfl) ⟨2953664, by rfl⟩ : syracuseStep 3938219 = 5907329) B5907329
theorem B694299 : Blo 690315 694299 := bstep (se 1 (by rfl) ⟨520724, by rfl⟩ : syracuseStep 694299 = 1041449) B1041449
theorem B2497691 : Blo 690315 2497691 := bstep (se 1 (by rfl) ⟨1873268, by rfl⟩ : syracuseStep 2497691 = 3746537) B3746537
theorem B16817665 : Blo 690315 16817665 := bstep (se 2 (by rfl) ⟨6306624, by rfl⟩ : syracuseStep 16817665 = 12613249) B12613249
theorem B8397055 : Blo 690315 8397055 := bstep (se 1 (by rfl) ⟨6297791, by rfl⟩ : syracuseStep 8397055 = 12595583) B12595583
theorem B2498887 : Blo 690315 2498887 := bstep (se 1 (by rfl) ⟨1874165, by rfl⟩ : syracuseStep 2498887 = 3748331) B3748331
theorem B2335229 : Blo 690315 2335229 := bstep (se 3 (by rfl) ⟨437855, by rfl⟩ : syracuseStep 2335229 = 875711) B875711
theorem B2499119 : Blo 690315 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B5252687 : Blo 690315 5252687 := bstep (se 1 (by rfl) ⟨3939515, by rfl⟩ : syracuseStep 5252687 = 7879031) B7879031
theorem B41527133 : Blo 690315 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B1747615 : Blo 690315 1747615 := bstep (se 1 (by rfl) ⟨1310711, by rfl⟩ : syracuseStep 1747615 = 2621423) B2621423
theorem B3320777 : Blo 690315 3320777 := bstep (se 2 (by rfl) ⟨1245291, by rfl⟩ : syracuseStep 3320777 = 2490583) B2490583
theorem B2337875 : Blo 690315 2337875 := bstep (se 1 (by rfl) ⟨1753406, by rfl⟩ : syracuseStep 2337875 = 3506813) B3506813
theorem B2338793 : Blo 690315 2338793 := bstep (se 2 (by rfl) ⟨877047, by rfl⟩ : syracuseStep 2338793 = 1754095) B1754095
theorem B1749023 : Blo 690315 1749023 := bstep (se 1 (by rfl) ⟨1311767, by rfl⟩ : syracuseStep 1749023 = 2623535) B2623535
theorem B1553633 : Blo 690315 1553633 := bstep (se 2 (by rfl) ⟨582612, by rfl⟩ : syracuseStep 1553633 = 1165225) B1165225
theorem B1750855 : Blo 690315 1750855 := bstep (se 1 (by rfl) ⟨1313141, by rfl⟩ : syracuseStep 1750855 = 2626283) B2626283
theorem B4997227 : Blo 690315 4997227 := bstep (se 1 (by rfl) ⟨3747920, by rfl⟩ : syracuseStep 4997227 = 7495841) B7495841
theorem B1753427 : Blo 690315 1753427 := bstep (se 1 (by rfl) ⟨1315070, by rfl⟩ : syracuseStep 1753427 = 2630141) B2630141
theorem B2212379 : Blo 690315 2212379 := bstep (se 1 (by rfl) ⟨1659284, by rfl⟩ : syracuseStep 2212379 = 3318569) B3318569
theorem B738335 : Blo 690315 738335 := bstep (se 1 (by rfl) ⟨553751, by rfl⟩ : syracuseStep 738335 = 1107503) B1107503
theorem B11814173 : Blo 690315 11814173 := bstep (se 3 (by rfl) ⟨2215157, by rfl⟩ : syracuseStep 11814173 = 4430315) B4430315
theorem B17319503 : Blo 690315 17319503 := bstep (se 1 (by rfl) ⟨12989627, by rfl⟩ : syracuseStep 17319503 = 25979255) B25979255
theorem B4999619 : Blo 690315 4999619 := bstep (se 1 (by rfl) ⟨3749714, by rfl⟩ : syracuseStep 4999619 = 7499429) B7499429
theorem B13290641 : Blo 690315 13290641 := bstep (se 2 (by rfl) ⟨4983990, by rfl⟩ : syracuseStep 13290641 = 9967981) B9967981
theorem B1559807 : Blo 690315 1559807 := bstep (se 1 (by rfl) ⟨1169855, by rfl⟩ : syracuseStep 1559807 = 2339711) B2339711
theorem B29871413 : Blo 690315 29871413 := bstep (se 5 (by rfl) ⟨1400222, by rfl⟩ : syracuseStep 29871413 = 2800445) B2800445
theorem B1035935 : Blo 690315 1035935 := bstep (se 1 (by rfl) ⟨776951, by rfl⟩ : syracuseStep 1035935 = 1553903) B1553903
theorem B1560743 : Blo 690315 1560743 := bstep (se 1 (by rfl) ⟨1170557, by rfl⟩ : syracuseStep 1560743 = 2341115) B2341115
theorem B1167851 : Blo 690315 1167851 := bstep (se 1 (by rfl) ⟨875888, by rfl⟩ : syracuseStep 1167851 = 1751777) B1751777
theorem B1037087 : Blo 690315 1037087 := bstep (se 1 (by rfl) ⟨777815, by rfl⟩ : syracuseStep 1037087 = 1555631) B1555631
theorem B1037423 : Blo 690315 1037423 := bstep (se 1 (by rfl) ⟨778067, by rfl⟩ : syracuseStep 1037423 = 1556135) B1556135
theorem B1037639 : Blo 690315 1037639 := bstep (se 1 (by rfl) ⟨778229, by rfl⟩ : syracuseStep 1037639 = 1556459) B1556459
theorem B1037759 : Blo 690315 1037759 := bstep (se 1 (by rfl) ⟨778319, by rfl⟩ : syracuseStep 1037759 = 1556639) B1556639
theorem B5625283 : Blo 690315 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B1037801 : Blo 690315 1037801 := bstep (se 2 (by rfl) ⟨389175, by rfl⟩ : syracuseStep 1037801 = 778351) B778351
theorem B1038335 : Blo 690315 1038335 := bstep (se 1 (by rfl) ⟨778751, by rfl⟩ : syracuseStep 1038335 = 1557503) B1557503
theorem B6641783 : Blo 690315 6641783 := bstep (se 1 (by rfl) ⟨4981337, by rfl⟩ : syracuseStep 6641783 = 9962675) B9962675
theorem B28498067 : Blo 690315 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B1170011 : Blo 690315 1170011 := bstep (se 1 (by rfl) ⟨877508, by rfl⟩ : syracuseStep 1170011 = 1755017) B1755017
theorem B1039079 : Blo 690315 1039079 := bstep (se 1 (by rfl) ⟨779309, by rfl⟩ : syracuseStep 1039079 = 1558619) B1558619
theorem B15948683 : Blo 690315 15948683 := bstep (se 1 (by rfl) ⟨11961512, by rfl⟩ : syracuseStep 15948683 = 23923025) B23923025
theorem B2218951 : Blo 690315 2218951 := bstep (se 1 (by rfl) ⟨1664213, by rfl⟩ : syracuseStep 2218951 = 3328427) B3328427
theorem B1039337 : Blo 690315 1039337 := bstep (se 2 (by rfl) ⟨389751, by rfl⟩ : syracuseStep 1039337 = 779503) B779503
theorem B1039391 : Blo 690315 1039391 := bstep (se 1 (by rfl) ⟨779543, by rfl⟩ : syracuseStep 1039391 = 1559087) B1559087
theorem B1039487 : Blo 690315 1039487 := bstep (se 1 (by rfl) ⟨779615, by rfl⟩ : syracuseStep 1039487 = 1559231) B1559231
theorem B1040795 : Blo 690315 1040795 := bstep (se 1 (by rfl) ⟨780596, by rfl⟩ : syracuseStep 1040795 = 1561193) B1561193
theorem B1040831 : Blo 690315 1040831 := bstep (se 1 (by rfl) ⟨780623, by rfl⟩ : syracuseStep 1040831 = 1561247) B1561247
theorem B1041407 : Blo 690315 1041407 := bstep (se 1 (by rfl) ⟨781055, by rfl⟩ : syracuseStep 1041407 = 1562111) B1562111
theorem B878683 : Blo 690315 878683 := bstep (se 1 (by rfl) ⟨659012, by rfl⟩ : syracuseStep 878683 = 1318025) B1318025
theorem B7892153 : Blo 690315 7892153 := bstep (se 2 (by rfl) ⟨2959557, by rfl⟩ : syracuseStep 7892153 = 5919115) B5919115
theorem B3501467 : Blo 690315 3501467 := bstep (se 1 (by rfl) ⟨2626100, by rfl⟩ : syracuseStep 3501467 = 5252201) B5252201
theorem B2223769 : Blo 690315 2223769 := bstep (se 2 (by rfl) ⟨833913, by rfl⟩ : syracuseStep 2223769 = 1667827) B1667827
theorem B3043997 : Blo 690315 3043997 := bstep (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) B1141499
theorem B5929199 : Blo 690315 5929199 := bstep (se 1 (by rfl) ⟨4446899, by rfl⟩ : syracuseStep 5929199 = 8893799) B8893799
theorem B13302791 : Blo 690315 13302791 := bstep (se 1 (by rfl) ⟨9977093, by rfl⟩ : syracuseStep 13302791 = 19954187) B19954187
theorem B1474919 : Blo 690315 1474919 := bstep (se 1 (by rfl) ⟨1106189, by rfl⟩ : syracuseStep 1474919 = 2212379) B2212379
theorem B4981799 : Blo 690315 4981799 := bstep (se 1 (by rfl) ⟨3736349, by rfl⟩ : syracuseStep 4981799 = 7472699) B7472699
theorem B2492315 : Blo 690315 2492315 := bstep (se 1 (by rfl) ⟨1869236, by rfl⟩ : syracuseStep 2492315 = 3738473) B3738473
theorem B2951083 : Blo 690315 2951083 := bstep (se 1 (by rfl) ⟨2213312, by rfl⟩ : syracuseStep 2951083 = 4426625) B4426625
theorem B690623 : Blo 690315 690623 := bstep (se 1 (by rfl) ⟨517967, by rfl⟩ : syracuseStep 690623 = 1035935) B1035935
theorem B985711 : Blo 690315 985711 := bstep (se 1 (by rfl) ⟨739283, by rfl⟩ : syracuseStep 985711 = 1478567) B1478567
theorem B1968893 : Blo 690315 1968893 := bstep (se 3 (by rfl) ⟨369167, by rfl⟩ : syracuseStep 1968893 = 738335) B738335
theorem B2362223 : Blo 690315 2362223 := bstep (se 1 (by rfl) ⟨1771667, by rfl⟩ : syracuseStep 2362223 = 3543335) B3543335
theorem B691391 : Blo 690315 691391 := bstep (se 1 (by rfl) ⟨518543, by rfl⟩ : syracuseStep 691391 = 1037087) B1037087
theorem B691615 : Blo 690315 691615 := bstep (se 1 (by rfl) ⟨518711, by rfl⟩ : syracuseStep 691615 = 1037423) B1037423
theorem B2625007 : Blo 690315 2625007 := bstep (se 1 (by rfl) ⟨1968755, by rfl⟩ : syracuseStep 2625007 = 3937511) B3937511
theorem B2330153 : Blo 690315 2330153 := bstep (se 2 (by rfl) ⟨873807, by rfl⟩ : syracuseStep 2330153 = 1747615) B1747615
theorem B691759 : Blo 690315 691759 := bstep (se 1 (by rfl) ⟨518819, by rfl⟩ : syracuseStep 691759 = 1037639) B1037639
theorem B691839 : Blo 690315 691839 := bstep (se 1 (by rfl) ⟨518879, by rfl⟩ : syracuseStep 691839 = 1037759) B1037759
theorem B691867 : Blo 690315 691867 := bstep (se 1 (by rfl) ⟨518900, by rfl⟩ : syracuseStep 691867 = 1037801) B1037801
theorem B2625479 : Blo 690315 2625479 := bstep (se 1 (by rfl) ⟨1969109, by rfl⟩ : syracuseStep 2625479 = 3938219) B3938219
theorem B692223 : Blo 690315 692223 := bstep (se 1 (by rfl) ⟨519167, by rfl⟩ : syracuseStep 692223 = 1038335) B1038335
theorem B4427855 : Blo 690315 4427855 := bstep (se 1 (by rfl) ⟨3320891, by rfl⟩ : syracuseStep 4427855 = 6641783) B6641783
theorem B692719 : Blo 690315 692719 := bstep (se 1 (by rfl) ⟨519539, by rfl⟩ : syracuseStep 692719 = 1039079) B1039079
theorem B692891 : Blo 690315 692891 := bstep (se 1 (by rfl) ⟨519668, by rfl⟩ : syracuseStep 692891 = 1039337) B1039337
theorem B692927 : Blo 690315 692927 := bstep (se 1 (by rfl) ⟨519695, by rfl⟩ : syracuseStep 692927 = 1039391) B1039391
theorem B692991 : Blo 690315 692991 := bstep (se 1 (by rfl) ⟨519743, by rfl⟩ : syracuseStep 692991 = 1039487) B1039487
theorem B693863 : Blo 690315 693863 := bstep (se 1 (by rfl) ⟨520397, by rfl⟩ : syracuseStep 693863 = 1040795) B1040795
theorem B693887 : Blo 690315 693887 := bstep (se 1 (by rfl) ⟨520415, by rfl⟩ : syracuseStep 693887 = 1040831) B1040831
theorem B694271 : Blo 690315 694271 := bstep (se 1 (by rfl) ⟨520703, by rfl⟩ : syracuseStep 694271 = 1041407) B1041407
theorem B2334311 : Blo 690315 2334311 := bstep (se 1 (by rfl) ⟨1750733, by rfl⟩ : syracuseStep 2334311 = 3501467) B3501467
theorem B2334473 : Blo 690315 2334473 := bstep (se 2 (by rfl) ⟨875427, by rfl⟩ : syracuseStep 2334473 = 1750855) B1750855
theorem B8855405 : Blo 690315 8855405 := bstep (se 3 (by rfl) ⟨1660388, by rfl⟩ : syracuseStep 8855405 = 3320777) B3320777
theorem B2958601 : Blo 690315 2958601 := bstep (se 2 (by rfl) ⟨1109475, by rfl⟩ : syracuseStep 2958601 = 2218951) B2218951
theorem B22423553 : Blo 690315 22423553 := bstep (se 2 (by rfl) ⟨8408832, by rfl⟩ : syracuseStep 22423553 = 16817665) B16817665
theorem B3320585 : Blo 690315 3320585 := bstep (se 2 (by rfl) ⟨1245219, by rfl⟩ : syracuseStep 3320585 = 2490439) B2490439
theorem B6662969 : Blo 690315 6662969 := bstep (se 2 (by rfl) ⟨2498613, by rfl⟩ : syracuseStep 6662969 = 4997227) B4997227
theorem B8433071 : Blo 690315 8433071 := bstep (se 1 (by rfl) ⟨6324803, by rfl⟩ : syracuseStep 8433071 = 12649607) B12649607
theorem B7876115 : Blo 690315 7876115 := bstep (se 1 (by rfl) ⟨5907086, by rfl⟩ : syracuseStep 7876115 = 11814173) B11814173
theorem B11546335 : Blo 690315 11546335 := bstep (se 1 (by rfl) ⟨8659751, by rfl⟩ : syracuseStep 11546335 = 17319503) B17319503
theorem B8860427 : Blo 690315 8860427 := bstep (se 1 (by rfl) ⟨6645320, by rfl⟩ : syracuseStep 8860427 = 13290641) B13290641
theorem B2635517 : Blo 690315 2635517 := bstep (se 3 (by rfl) ⟨494159, by rfl⟩ : syracuseStep 2635517 = 988319) B988319
theorem B10632455 : Blo 690315 10632455 := bstep (se 1 (by rfl) ⟨7974341, by rfl⟩ : syracuseStep 10632455 = 15948683) B15948683
theorem B2965025 : Blo 690315 2965025 := bstep (se 2 (by rfl) ⟨1111884, by rfl⟩ : syracuseStep 2965025 = 2223769) B2223769
theorem B1556819 : Blo 690315 1556819 := bstep (se 1 (by rfl) ⟨1167614, by rfl⟩ : syracuseStep 1556819 = 2335229) B2335229
theorem B1558583 : Blo 690315 1558583 := bstep (se 1 (by rfl) ⟨1168937, by rfl⟩ : syracuseStep 1558583 = 2337875) B2337875
theorem B5261435 : Blo 690315 5261435 := bstep (se 1 (by rfl) ⟨3946076, by rfl⟩ : syracuseStep 5261435 = 7892153) B7892153
theorem B1559195 : Blo 690315 1559195 := bstep (se 1 (by rfl) ⟨1169396, by rfl⟩ : syracuseStep 1559195 = 2338793) B2338793
theorem B1166015 : Blo 690315 1166015 := bstep (se 1 (by rfl) ⟨874511, by rfl⟩ : syracuseStep 1166015 = 1749023) B1749023
theorem B1035755 : Blo 690315 1035755 := bstep (se 1 (by rfl) ⟨776816, by rfl⟩ : syracuseStep 1035755 = 1553633) B1553633
theorem B3952799 : Blo 690315 3952799 := bstep (se 1 (by rfl) ⟨2964599, by rfl⟩ : syracuseStep 3952799 = 5929199) B5929199
theorem B8868527 : Blo 690315 8868527 := bstep (se 1 (by rfl) ⟨6651395, by rfl⟩ : syracuseStep 8868527 = 13302791) B13302791
theorem B1168951 : Blo 690315 1168951 := bstep (se 1 (by rfl) ⟨876713, by rfl⟩ : syracuseStep 1168951 = 1753427) B1753427
theorem B11196073 : Blo 690315 11196073 := bstep (se 2 (by rfl) ⟨4198527, by rfl⟩ : syracuseStep 11196073 = 8397055) B8397055
theorem B3331849 : Blo 690315 3331849 := bstep (se 2 (by rfl) ⟨1249443, by rfl⟩ : syracuseStep 3331849 = 2498887) B2498887
theorem B5265323 : Blo 690315 5265323 := bstep (se 1 (by rfl) ⟨3948992, by rfl⟩ : syracuseStep 5265323 = 7897985) B7897985
theorem B3333079 : Blo 690315 3333079 := bstep (se 1 (by rfl) ⟨2499809, by rfl⟩ : syracuseStep 3333079 = 4999619) B4999619
theorem B1039871 : Blo 690315 1039871 := bstep (se 1 (by rfl) ⟨779903, by rfl⟩ : syracuseStep 1039871 = 1559807) B1559807
theorem B19914275 : Blo 690315 19914275 := bstep (se 1 (by rfl) ⟨14935706, by rfl⟩ : syracuseStep 19914275 = 29871413) B29871413
theorem B1040495 : Blo 690315 1040495 := bstep (se 1 (by rfl) ⟨780371, by rfl⟩ : syracuseStep 1040495 = 1560743) B1560743
theorem B1171577 : Blo 690315 1171577 := bstep (se 2 (by rfl) ⟨439341, by rfl⟩ : syracuseStep 1171577 = 878683) B878683
theorem B778567 : Blo 690315 778567 := bstep (se 1 (by rfl) ⟨583925, by rfl⟩ : syracuseStep 778567 = 1167851) B1167851
theorem B18998711 : Blo 690315 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B780007 : Blo 690315 780007 := bstep (se 1 (by rfl) ⟨585005, by rfl⟩ : syracuseStep 780007 = 1170011) B1170011
theorem B1665127 : Blo 690315 1665127 := bstep (se 1 (by rfl) ⟨1248845, by rfl⟩ : syracuseStep 1665127 = 2497691) B2497691
theorem B1666079 : Blo 690315 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B3501791 : Blo 690315 3501791 := bstep (se 1 (by rfl) ⟨2626343, by rfl⟩ : syracuseStep 3501791 = 5252687) B5252687
theorem B27684755 : Blo 690315 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B7500377 : Blo 690315 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B2029331 : Blo 690315 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B983279 : Blo 690315 983279 := bstep (se 1 (by rfl) ⟨737459, by rfl⟩ : syracuseStep 983279 = 1474919) B1474919
theorem B8880677 : Blo 690315 8880677 := bstep (se 4 (by rfl) ⟨832563, by rfl⟩ : syracuseStep 8880677 = 1665127) B1665127
theorem B3507623 : Blo 690315 3507623 := bstep (se 1 (by rfl) ⟨2630717, by rfl⟩ : syracuseStep 3507623 = 5261435) B5261435
theorem B1312595 : Blo 690315 1312595 := bstep (se 1 (by rfl) ⟨984446, by rfl⟩ : syracuseStep 1312595 = 1968893) B1968893
theorem B1574815 : Blo 690315 1574815 := bstep (se 1 (by rfl) ⟨1181111, by rfl⟩ : syracuseStep 1574815 = 2362223) B2362223
theorem B690503 : Blo 690315 690503 := bstep (se 1 (by rfl) ⟨517877, by rfl⟩ : syracuseStep 690503 = 1035755) B1035755
theorem B3934777 : Blo 690315 3934777 := bstep (se 2 (by rfl) ⟨1475541, by rfl⟩ : syracuseStep 3934777 = 2951083) B2951083
theorem B2951903 : Blo 690315 2951903 := bstep (se 1 (by rfl) ⟨2213927, by rfl⟩ : syracuseStep 2951903 = 4427855) B4427855
theorem B1314281 : Blo 690315 1314281 := bstep (se 2 (by rfl) ⟨492855, by rfl⟩ : syracuseStep 1314281 = 985711) B985711
theorem B3510215 : Blo 690315 3510215 := bstep (se 1 (by rfl) ⟨2632661, by rfl⟩ : syracuseStep 3510215 = 5265323) B5265323
theorem B5411549 : Blo 690315 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B693247 : Blo 690315 693247 := bstep (se 1 (by rfl) ⟨519935, by rfl⟩ : syracuseStep 693247 = 1039871) B1039871
theorem B13276183 : Blo 690315 13276183 := bstep (se 1 (by rfl) ⟨9957137, by rfl⟩ : syracuseStep 13276183 = 19914275) B19914275
theorem B5903603 : Blo 690315 5903603 := bstep (se 1 (by rfl) ⟨4427702, by rfl⟩ : syracuseStep 5903603 = 8855405) B8855405
theorem B693663 : Blo 690315 693663 := bstep (se 1 (by rfl) ⟨520247, by rfl⟩ : syracuseStep 693663 = 1040495) B1040495
theorem B14949035 : Blo 690315 14949035 := bstep (se 1 (by rfl) ⟨11211776, by rfl⟩ : syracuseStep 14949035 = 22423553) B22423553
theorem B5250743 : Blo 690315 5250743 := bstep (se 1 (by rfl) ⟨3938057, by rfl⟩ : syracuseStep 5250743 = 7876115) B7876115
theorem B2334527 : Blo 690315 2334527 := bstep (se 1 (by rfl) ⟨1750895, by rfl⟩ : syracuseStep 2334527 = 3501791) B3501791
theorem B18456503 : Blo 690315 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B5906951 : Blo 690315 5906951 := bstep (se 1 (by rfl) ⟨4430213, by rfl⟩ : syracuseStep 5906951 = 8860427) B8860427
theorem B7906733 : Blo 690315 7906733 := bstep (se 3 (by rfl) ⟨1482512, by rfl⟩ : syracuseStep 7906733 = 2965025) B2965025
theorem B7088303 : Blo 690315 7088303 := bstep (se 1 (by rfl) ⟨5316227, by rfl⟩ : syracuseStep 7088303 = 10632455) B10632455
theorem B3321199 : Blo 690315 3321199 := bstep (se 1 (by rfl) ⟨2490899, by rfl⟩ : syracuseStep 3321199 = 4981799) B4981799
theorem B20001005 : Blo 690315 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B3944801 : Blo 690315 3944801 := bstep (se 2 (by rfl) ⟨1479300, by rfl⟩ : syracuseStep 3944801 = 2958601) B2958601
theorem B1553435 : Blo 690315 1553435 := bstep (se 1 (by rfl) ⟨1165076, by rfl⟩ : syracuseStep 1553435 = 2330153) B2330153
theorem B1750319 : Blo 690315 1750319 := bstep (se 1 (by rfl) ⟨1312739, by rfl⟩ : syracuseStep 1750319 = 2625479) B2625479
theorem B2635199 : Blo 690315 2635199 := bstep (se 1 (by rfl) ⟨1976399, by rfl⟩ : syracuseStep 2635199 = 3952799) B3952799
theorem B5912351 : Blo 690315 5912351 := bstep (se 1 (by rfl) ⟨4434263, by rfl⟩ : syracuseStep 5912351 = 8868527) B8868527
theorem B1556207 : Blo 690315 1556207 := bstep (se 1 (by rfl) ⟨1167155, by rfl⟩ : syracuseStep 1556207 = 2334311) B2334311
theorem B1556315 : Blo 690315 1556315 := bstep (se 1 (by rfl) ⟨1167236, by rfl⟩ : syracuseStep 1556315 = 2334473) B2334473
theorem B12665807 : Blo 690315 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B2213723 : Blo 690315 2213723 := bstep (se 1 (by rfl) ⟨1660292, by rfl⟩ : syracuseStep 2213723 = 3320585) B3320585
theorem B4441979 : Blo 690315 4441979 := bstep (se 1 (by rfl) ⟨3331484, by rfl⟩ : syracuseStep 4441979 = 6662969) B6662969
theorem B1558601 : Blo 690315 1558601 := bstep (se 2 (by rfl) ⟨584475, by rfl⟩ : syracuseStep 1558601 = 1168951) B1168951
theorem B14928097 : Blo 690315 14928097 := bstep (se 2 (by rfl) ⟨5598036, by rfl⟩ : syracuseStep 14928097 = 11196073) B11196073
theorem B5622047 : Blo 690315 5622047 := bstep (se 1 (by rfl) ⟨4216535, by rfl⟩ : syracuseStep 5622047 = 8433071) B8433071
theorem B4442465 : Blo 690315 4442465 := bstep (se 2 (by rfl) ⟨1665924, by rfl⟩ : syracuseStep 4442465 = 3331849) B3331849
theorem B1757011 : Blo 690315 1757011 := bstep (se 1 (by rfl) ⟨1317758, by rfl⟩ : syracuseStep 1757011 = 2635517) B2635517
theorem B4444105 : Blo 690315 4444105 := bstep (se 2 (by rfl) ⟨1666539, by rfl⟩ : syracuseStep 4444105 = 3333079) B3333079
theorem B1037879 : Blo 690315 1037879 := bstep (se 1 (by rfl) ⟨778409, by rfl⟩ : syracuseStep 1037879 = 1556819) B1556819
theorem B1038089 : Blo 690315 1038089 := bstep (se 2 (by rfl) ⟨389283, by rfl⟩ : syracuseStep 1038089 = 778567) B778567
theorem B1661543 : Blo 690315 1661543 := bstep (se 1 (by rfl) ⟨1246157, by rfl⟩ : syracuseStep 1661543 = 2492315) B2492315
theorem B1039055 : Blo 690315 1039055 := bstep (se 1 (by rfl) ⟨779291, by rfl⟩ : syracuseStep 1039055 = 1558583) B1558583
theorem B1039463 : Blo 690315 1039463 := bstep (se 1 (by rfl) ⟨779597, by rfl⟩ : syracuseStep 1039463 = 1559195) B1559195
theorem B777343 : Blo 690315 777343 := bstep (se 1 (by rfl) ⟨583007, by rfl⟩ : syracuseStep 777343 = 1166015) B1166015
theorem B1040009 : Blo 690315 1040009 := bstep (se 2 (by rfl) ⟨390003, by rfl⟩ : syracuseStep 1040009 = 780007) B780007
theorem B3500009 : Blo 690315 3500009 := bstep (se 2 (by rfl) ⟨1312503, by rfl⟩ : syracuseStep 3500009 = 2625007) B2625007
theorem B15395113 : Blo 690315 15395113 := bstep (se 2 (by rfl) ⟨5773167, by rfl⟩ : syracuseStep 15395113 = 11546335) B11546335
theorem B781051 : Blo 690315 781051 := bstep (se 1 (by rfl) ⟨585788, by rfl⟩ : syracuseStep 781051 = 1171577) B1171577
theorem B1110719 : Blo 690315 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B2622077 : Blo 690315 2622077 := bstep (se 3 (by rfl) ⟨491639, by rfl⟩ : syracuseStep 2622077 = 983279) B983279
theorem B1475815 : Blo 690315 1475815 := bstep (se 1 (by rfl) ⟨1106861, by rfl⟩ : syracuseStep 1475815 = 2213723) B2213723
theorem B2099753 : Blo 690315 2099753 := bstep (se 2 (by rfl) ⟨787407, by rfl⟩ : syracuseStep 2099753 = 1574815) B1574815
theorem B5246369 : Blo 690315 5246369 := bstep (se 2 (by rfl) ⟨1967388, by rfl⟩ : syracuseStep 5246369 = 3934777) B3934777
theorem B3935735 : Blo 690315 3935735 := bstep (se 1 (by rfl) ⟨2951801, by rfl⟩ : syracuseStep 3935735 = 5903603) B5903603
theorem B691919 : Blo 690315 691919 := bstep (se 1 (by rfl) ⟨518939, by rfl⟩ : syracuseStep 691919 = 1037879) B1037879
theorem B692059 : Blo 690315 692059 := bstep (se 1 (by rfl) ⟨519044, by rfl⟩ : syracuseStep 692059 = 1038089) B1038089
theorem B9966023 : Blo 690315 9966023 := bstep (se 1 (by rfl) ⟨7474517, by rfl⟩ : syracuseStep 9966023 = 14949035) B14949035
theorem B692703 : Blo 690315 692703 := bstep (se 1 (by rfl) ⟨519527, by rfl⟩ : syracuseStep 692703 = 1039055) B1039055
theorem B4428265 : Blo 690315 4428265 := bstep (se 2 (by rfl) ⟨1660599, by rfl⟩ : syracuseStep 4428265 = 3321199) B3321199
theorem B692975 : Blo 690315 692975 := bstep (se 1 (by rfl) ⟨519731, by rfl⟩ : syracuseStep 692975 = 1039463) B1039463
theorem B693339 : Blo 690315 693339 := bstep (se 1 (by rfl) ⟨520004, by rfl⟩ : syracuseStep 693339 = 1040009) B1040009
theorem B3937967 : Blo 690315 3937967 := bstep (se 1 (by rfl) ⟨2953475, by rfl⟩ : syracuseStep 3937967 = 5906951) B5906951
theorem B2333339 : Blo 690315 2333339 := bstep (se 1 (by rfl) ⟨1750004, by rfl⟩ : syracuseStep 2333339 = 3500009) B3500009
theorem B17701577 : Blo 690315 17701577 := bstep (se 2 (by rfl) ⟨6638091, by rfl⟩ : syracuseStep 17701577 = 13276183) B13276183
theorem B4725535 : Blo 690315 4725535 := bstep (se 1 (by rfl) ⟨3544151, by rfl⟩ : syracuseStep 4725535 = 7088303) B7088303
theorem B7871741 : Blo 690315 7871741 := bstep (se 3 (by rfl) ⟨1475951, by rfl⟩ : syracuseStep 7871741 = 2951903) B2951903
theorem B2629867 : Blo 690315 2629867 := bstep (se 1 (by rfl) ⟨1972400, by rfl⟩ : syracuseStep 2629867 = 3944801) B3944801
theorem B3941567 : Blo 690315 3941567 := bstep (se 1 (by rfl) ⟨2956175, by rfl⟩ : syracuseStep 3941567 = 5912351) B5912351
theorem B2338415 : Blo 690315 2338415 := bstep (se 1 (by rfl) ⟨1753811, by rfl⟩ : syracuseStep 2338415 = 3507623) B3507623
theorem B2961319 : Blo 690315 2961319 := bstep (se 1 (by rfl) ⟨2220989, by rfl⟩ : syracuseStep 2961319 = 4441979) B4441979
theorem B3748031 : Blo 690315 3748031 := bstep (se 1 (by rfl) ⟨2811023, by rfl⟩ : syracuseStep 3748031 = 5622047) B5622047
theorem B2961643 : Blo 690315 2961643 := bstep (se 1 (by rfl) ⟨2221232, by rfl⟩ : syracuseStep 2961643 = 4442465) B4442465
theorem B2961917 : Blo 690315 2961917 := bstep (se 3 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 2961917 = 1110719) B1110719
theorem B14430797 : Blo 690315 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B2340143 : Blo 690315 2340143 := bstep (se 1 (by rfl) ⟨1755107, by rfl⟩ : syracuseStep 2340143 = 3510215) B3510215
theorem B19904129 : Blo 690315 19904129 := bstep (se 2 (by rfl) ⟨7464048, by rfl⟩ : syracuseStep 19904129 = 14928097) B14928097
theorem B20526817 : Blo 690315 20526817 := bstep (se 2 (by rfl) ⟨7697556, by rfl⟩ : syracuseStep 20526817 = 15395113) B15395113
theorem B2342681 : Blo 690315 2342681 := bstep (se 2 (by rfl) ⟨878505, by rfl⟩ : syracuseStep 2342681 = 1757011) B1757011
theorem B1556351 : Blo 690315 1556351 := bstep (se 1 (by rfl) ⟨1167263, by rfl⟩ : syracuseStep 1556351 = 2334527) B2334527
theorem B1035623 : Blo 690315 1035623 := bstep (se 1 (by rfl) ⟨776717, by rfl⟩ : syracuseStep 1035623 = 1553435) B1553435
theorem B1166879 : Blo 690315 1166879 := bstep (se 1 (by rfl) ⟨875159, by rfl⟩ : syracuseStep 1166879 = 1750319) B1750319
theorem B1756799 : Blo 690315 1756799 := bstep (se 1 (by rfl) ⟨1317599, by rfl⟩ : syracuseStep 1756799 = 2635199) B2635199
theorem B1036457 : Blo 690315 1036457 := bstep (se 2 (by rfl) ⟨388671, by rfl⟩ : syracuseStep 1036457 = 777343) B777343
theorem B1037471 : Blo 690315 1037471 := bstep (se 1 (by rfl) ⟨778103, by rfl⟩ : syracuseStep 1037471 = 1556207) B1556207
theorem B1037543 : Blo 690315 1037543 := bstep (se 1 (by rfl) ⟨778157, by rfl⟩ : syracuseStep 1037543 = 1556315) B1556315
theorem B5920451 : Blo 690315 5920451 := bstep (se 1 (by rfl) ⟨4440338, by rfl⟩ : syracuseStep 5920451 = 8880677) B8880677
theorem B8443871 : Blo 690315 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B875063 : Blo 690315 875063 := bstep (se 1 (by rfl) ⟨656297, by rfl⟩ : syracuseStep 875063 = 1312595) B1312595
theorem B1039067 : Blo 690315 1039067 := bstep (se 1 (by rfl) ⟨779300, by rfl⟩ : syracuseStep 1039067 = 1558601) B1558601
theorem B876187 : Blo 690315 876187 := bstep (se 1 (by rfl) ⟨657140, by rfl⟩ : syracuseStep 876187 = 1314281) B1314281
theorem B1041401 : Blo 690315 1041401 := bstep (se 2 (by rfl) ⟨390525, by rfl⟩ : syracuseStep 1041401 = 781051) B781051
theorem B1107695 : Blo 690315 1107695 := bstep (se 1 (by rfl) ⟨830771, by rfl⟩ : syracuseStep 1107695 = 1661543) B1661543
theorem B3500495 : Blo 690315 3500495 := bstep (se 1 (by rfl) ⟨2625371, by rfl⟩ : syracuseStep 3500495 = 5250743) B5250743
theorem B5925473 : Blo 690315 5925473 := bstep (se 2 (by rfl) ⟨2222052, by rfl⟩ : syracuseStep 5925473 = 4444105) B4444105
theorem B5271155 : Blo 690315 5271155 := bstep (se 1 (by rfl) ⟨3953366, by rfl⟩ : syracuseStep 5271155 = 7906733) B7906733
theorem B13334003 : Blo 690315 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B49217341 : Blo 690315 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B3506489 : Blo 690315 3506489 := bstep (se 2 (by rfl) ⟨1314933, by rfl⟩ : syracuseStep 3506489 = 2629867) B2629867
theorem B1967753 : Blo 690315 1967753 := bstep (se 2 (by rfl) ⟨737907, by rfl⟩ : syracuseStep 1967753 = 1475815) B1475815
theorem B690415 : Blo 690315 690415 := bstep (se 1 (by rfl) ⟨517811, by rfl⟩ : syracuseStep 690415 = 1035623) B1035623
theorem B2623823 : Blo 690315 2623823 := bstep (se 1 (by rfl) ⟨1967867, by rfl⟩ : syracuseStep 2623823 = 3935735) B3935735
theorem B690971 : Blo 690315 690971 := bstep (se 1 (by rfl) ⟨518228, by rfl⟩ : syracuseStep 690971 = 1036457) B1036457
theorem B691647 : Blo 690315 691647 := bstep (se 1 (by rfl) ⟨518735, by rfl⟩ : syracuseStep 691647 = 1037471) B1037471
theorem B691695 : Blo 690315 691695 := bstep (se 1 (by rfl) ⟨518771, by rfl⟩ : syracuseStep 691695 = 1037543) B1037543
theorem B2625311 : Blo 690315 2625311 := bstep (se 1 (by rfl) ⟨1968983, by rfl⟩ : syracuseStep 2625311 = 3937967) B3937967
theorem B11801051 : Blo 690315 11801051 := bstep (se 1 (by rfl) ⟨8850788, by rfl⟩ : syracuseStep 11801051 = 17701577) B17701577
theorem B692711 : Blo 690315 692711 := bstep (se 1 (by rfl) ⟨519533, by rfl⟩ : syracuseStep 692711 = 1039067) B1039067
theorem B2953853 : Blo 690315 2953853 := bstep (se 3 (by rfl) ⟨553847, by rfl⟩ : syracuseStep 2953853 = 1107695) B1107695
theorem B5247827 : Blo 690315 5247827 := bstep (se 1 (by rfl) ⟨3935870, by rfl⟩ : syracuseStep 5247827 = 7871741) B7871741
theorem B5904353 : Blo 690315 5904353 := bstep (se 2 (by rfl) ⟨2214132, by rfl⟩ : syracuseStep 5904353 = 4428265) B4428265
theorem B694267 : Blo 690315 694267 := bstep (se 1 (by rfl) ⟨520700, by rfl⟩ : syracuseStep 694267 = 1041401) B1041401
theorem B2627711 : Blo 690315 2627711 := bstep (se 1 (by rfl) ⟨1970783, by rfl⟩ : syracuseStep 2627711 = 3941567) B3941567
theorem B2333501 : Blo 690315 2333501 := bstep (se 3 (by rfl) ⟨437531, by rfl⟩ : syracuseStep 2333501 = 875063) B875063
theorem B2333663 : Blo 690315 2333663 := bstep (se 1 (by rfl) ⟨1750247, by rfl⟩ : syracuseStep 2333663 = 3500495) B3500495
theorem B27369089 : Blo 690315 27369089 := bstep (se 2 (by rfl) ⟨10263408, by rfl⟩ : syracuseStep 27369089 = 20526817) B20526817
theorem B3514103 : Blo 690315 3514103 := bstep (se 1 (by rfl) ⟨2635577, by rfl⟩ : syracuseStep 3514103 = 5271155) B5271155
theorem B2498687 : Blo 690315 2498687 := bstep (se 1 (by rfl) ⟨1874015, by rfl⟩ : syracuseStep 2498687 = 3748031) B3748031
theorem B1974611 : Blo 690315 1974611 := bstep (se 1 (by rfl) ⟨1480958, by rfl⟩ : syracuseStep 1974611 = 2961917) B2961917
theorem B8889335 : Blo 690315 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B6300713 : Blo 690315 6300713 := bstep (se 2 (by rfl) ⟨2362767, by rfl⟩ : syracuseStep 6300713 = 4725535) B4725535
theorem B1748051 : Blo 690315 1748051 := bstep (se 1 (by rfl) ⟨1311038, by rfl⟩ : syracuseStep 1748051 = 2622077) B2622077
theorem B3946967 : Blo 690315 3946967 := bstep (se 1 (by rfl) ⟨2960225, by rfl⟩ : syracuseStep 3946967 = 5920451) B5920451
theorem B1555559 : Blo 690315 1555559 := bstep (se 1 (by rfl) ⟨1166669, by rfl⟩ : syracuseStep 1555559 = 2333339) B2333339
theorem B3948425 : Blo 690315 3948425 := bstep (se 2 (by rfl) ⟨1480659, by rfl⟩ : syracuseStep 3948425 = 2961319) B2961319
theorem B3948857 : Blo 690315 3948857 := bstep (se 2 (by rfl) ⟨1480821, by rfl⟩ : syracuseStep 3948857 = 2961643) B2961643
theorem B3950315 : Blo 690315 3950315 := bstep (se 1 (by rfl) ⟨2962736, by rfl⟩ : syracuseStep 3950315 = 5925473) B5925473
theorem B1558943 : Blo 690315 1558943 := bstep (se 1 (by rfl) ⟨1169207, by rfl⟩ : syracuseStep 1558943 = 2338415) B2338415
theorem B9620531 : Blo 690315 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B1560095 : Blo 690315 1560095 := bstep (se 1 (by rfl) ⟨1170071, by rfl⟩ : syracuseStep 1560095 = 2340143) B2340143
theorem B1168249 : Blo 690315 1168249 := bstep (se 2 (by rfl) ⟨438093, by rfl⟩ : syracuseStep 1168249 = 876187) B876187
theorem B65623121 : Blo 690315 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B1561787 : Blo 690315 1561787 := bstep (se 1 (by rfl) ⟨1171340, by rfl⟩ : syracuseStep 1561787 = 2342681) B2342681
theorem B1037567 : Blo 690315 1037567 := bstep (se 1 (by rfl) ⟨778175, by rfl⟩ : syracuseStep 1037567 = 1556351) B1556351
theorem B1399835 : Blo 690315 1399835 := bstep (se 1 (by rfl) ⟨1049876, by rfl⟩ : syracuseStep 1399835 = 2099753) B2099753
theorem B3497579 : Blo 690315 3497579 := bstep (se 1 (by rfl) ⟨2623184, by rfl⟩ : syracuseStep 3497579 = 5246369) B5246369
theorem B777919 : Blo 690315 777919 := bstep (se 1 (by rfl) ⟨583439, by rfl⟩ : syracuseStep 777919 = 1166879) B1166879
theorem B1171199 : Blo 690315 1171199 := bstep (se 1 (by rfl) ⟨878399, by rfl⟩ : syracuseStep 1171199 = 1756799) B1756799
theorem B6644015 : Blo 690315 6644015 := bstep (se 1 (by rfl) ⟨4983011, by rfl⟩ : syracuseStep 6644015 = 9966023) B9966023
theorem B5629247 : Blo 690315 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B13269419 : Blo 690315 13269419 := bstep (se 1 (by rfl) ⟨9952064, by rfl⟩ : syracuseStep 13269419 = 19904129) B19904129
theorem B7867367 : Blo 690315 7867367 := bstep (se 1 (by rfl) ⟨5900525, by rfl⟩ : syracuseStep 7867367 = 11801051) B11801051
theorem B1969235 : Blo 690315 1969235 := bstep (se 1 (by rfl) ⟨1476926, by rfl⟩ : syracuseStep 1969235 = 2953853) B2953853
theorem B43748747 : Blo 690315 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B691711 : Blo 690315 691711 := bstep (se 1 (by rfl) ⟨518783, by rfl⟩ : syracuseStep 691711 = 1037567) B1037567
theorem B3936235 : Blo 690315 3936235 := bstep (se 1 (by rfl) ⟨2952176, by rfl⟩ : syracuseStep 3936235 = 5904353) B5904353
theorem B5247341 : Blo 690315 5247341 := bstep (se 3 (by rfl) ⟨983876, by rfl⟩ : syracuseStep 5247341 = 1967753) B1967753
theorem B2331719 : Blo 690315 2331719 := bstep (se 1 (by rfl) ⟨1748789, by rfl⟩ : syracuseStep 2331719 = 3497579) B3497579
theorem B4429343 : Blo 690315 4429343 := bstep (se 1 (by rfl) ⟨3322007, by rfl⟩ : syracuseStep 4429343 = 6644015) B6644015
theorem B1316407 : Blo 690315 1316407 := bstep (se 1 (by rfl) ⟨987305, by rfl⟩ : syracuseStep 1316407 = 1974611) B1974611
theorem B2631311 : Blo 690315 2631311 := bstep (se 1 (by rfl) ⟨1973483, by rfl⟩ : syracuseStep 2631311 = 3946967) B3946967
theorem B2632283 : Blo 690315 2632283 := bstep (se 1 (by rfl) ⟨1974212, by rfl⟩ : syracuseStep 2632283 = 3948425) B3948425
theorem B2337659 : Blo 690315 2337659 := bstep (se 1 (by rfl) ⟨1753244, by rfl⟩ : syracuseStep 2337659 = 3506489) B3506489
theorem B2632571 : Blo 690315 2632571 := bstep (se 1 (by rfl) ⟨1974428, by rfl⟩ : syracuseStep 2632571 = 3948857) B3948857
theorem B2633543 : Blo 690315 2633543 := bstep (se 1 (by rfl) ⟨1975157, by rfl⟩ : syracuseStep 2633543 = 3950315) B3950315
theorem B1749215 : Blo 690315 1749215 := bstep (se 1 (by rfl) ⟨1311911, by rfl⟩ : syracuseStep 1749215 = 2623823) B2623823
theorem B1750207 : Blo 690315 1750207 := bstep (se 1 (by rfl) ⟨1312655, by rfl⟩ : syracuseStep 1750207 = 2625311) B2625311
theorem B1751807 : Blo 690315 1751807 := bstep (se 1 (by rfl) ⟨1313855, by rfl⟩ : syracuseStep 1751807 = 2627711) B2627711
theorem B1555667 : Blo 690315 1555667 := bstep (se 1 (by rfl) ⟨1166750, by rfl⟩ : syracuseStep 1555667 = 2333501) B2333501
theorem B1555775 : Blo 690315 1555775 := bstep (se 1 (by rfl) ⟨1166831, by rfl⟩ : syracuseStep 1555775 = 2333663) B2333663
theorem B933223 : Blo 690315 933223 := bstep (se 1 (by rfl) ⟨699917, by rfl⟩ : syracuseStep 933223 = 1399835) B1399835
theorem B2342735 : Blo 690315 2342735 := bstep (se 1 (by rfl) ⟨1757051, by rfl⟩ : syracuseStep 2342735 = 3514103) B3514103
theorem B3752831 : Blo 690315 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B1557665 : Blo 690315 1557665 := bstep (se 2 (by rfl) ⟨584124, by rfl⟩ : syracuseStep 1557665 = 1168249) B1168249
theorem B1165367 : Blo 690315 1165367 := bstep (se 1 (by rfl) ⟨874025, by rfl⟩ : syracuseStep 1165367 = 1748051) B1748051
theorem B1037039 : Blo 690315 1037039 := bstep (se 1 (by rfl) ⟨777779, by rfl⟩ : syracuseStep 1037039 = 1555559) B1555559
theorem B1037225 : Blo 690315 1037225 := bstep (se 2 (by rfl) ⟨388959, by rfl⟩ : syracuseStep 1037225 = 777919) B777919
theorem B1039295 : Blo 690315 1039295 := bstep (se 1 (by rfl) ⟨779471, by rfl⟩ : syracuseStep 1039295 = 1558943) B1558943
theorem B6413687 : Blo 690315 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B1040063 : Blo 690315 1040063 := bstep (se 1 (by rfl) ⟨780047, by rfl⟩ : syracuseStep 1040063 = 1560095) B1560095
theorem B16801901 : Blo 690315 16801901 := bstep (se 3 (by rfl) ⟨3150356, by rfl⟩ : syracuseStep 16801901 = 6300713) B6300713
theorem B3498551 : Blo 690315 3498551 := bstep (se 1 (by rfl) ⟨2623913, by rfl⟩ : syracuseStep 3498551 = 5247827) B5247827
theorem B1041191 : Blo 690315 1041191 := bstep (se 1 (by rfl) ⟨780893, by rfl⟩ : syracuseStep 1041191 = 1561787) B1561787
theorem B18246059 : Blo 690315 18246059 := bstep (se 1 (by rfl) ⟨13684544, by rfl⟩ : syracuseStep 18246059 = 27369089) B27369089
theorem B780799 : Blo 690315 780799 := bstep (se 1 (by rfl) ⟨585599, by rfl⟩ : syracuseStep 780799 = 1171199) B1171199
theorem B1665791 : Blo 690315 1665791 := bstep (se 1 (by rfl) ⟨1249343, by rfl⟩ : syracuseStep 1665791 = 2498687) B2498687
theorem B5926223 : Blo 690315 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B8846279 : Blo 690315 8846279 := bstep (se 1 (by rfl) ⟨6634709, by rfl⟩ : syracuseStep 8846279 = 13269419) B13269419
theorem B5244911 : Blo 690315 5244911 := bstep (se 1 (by rfl) ⟨3933683, by rfl⟩ : syracuseStep 5244911 = 7867367) B7867367
theorem B1312823 : Blo 690315 1312823 := bstep (se 1 (by rfl) ⟨984617, by rfl⟩ : syracuseStep 1312823 = 1969235) B1969235
theorem B29165831 : Blo 690315 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B691359 : Blo 690315 691359 := bstep (se 1 (by rfl) ⟨518519, by rfl⟩ : syracuseStep 691359 = 1037039) B1037039
theorem B691483 : Blo 690315 691483 := bstep (se 1 (by rfl) ⟨518612, by rfl⟩ : syracuseStep 691483 = 1037225) B1037225
theorem B2952895 : Blo 690315 2952895 := bstep (se 1 (by rfl) ⟨2214671, by rfl⟩ : syracuseStep 2952895 = 4429343) B4429343
theorem B692863 : Blo 690315 692863 := bstep (se 1 (by rfl) ⟨519647, by rfl⟩ : syracuseStep 692863 = 1039295) B1039295
theorem B693375 : Blo 690315 693375 := bstep (se 1 (by rfl) ⟨520031, by rfl⟩ : syracuseStep 693375 = 1040063) B1040063
theorem B5248313 : Blo 690315 5248313 := bstep (se 2 (by rfl) ⟨1968117, by rfl⟩ : syracuseStep 5248313 = 3936235) B3936235
theorem B2332367 : Blo 690315 2332367 := bstep (se 1 (by rfl) ⟨1749275, by rfl⟩ : syracuseStep 2332367 = 3498551) B3498551
theorem B694127 : Blo 690315 694127 := bstep (se 1 (by rfl) ⟨520595, by rfl⟩ : syracuseStep 694127 = 1041191) B1041191
theorem B2333609 : Blo 690315 2333609 := bstep (se 2 (by rfl) ⟨875103, by rfl⟩ : syracuseStep 2333609 = 1750207) B1750207
theorem B12164039 : Blo 690315 12164039 := bstep (se 1 (by rfl) ⟨9123029, by rfl⟩ : syracuseStep 12164039 = 18246059) B18246059
theorem B2501887 : Blo 690315 2501887 := bstep (se 1 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 2501887 = 3752831) B3752831
theorem B1554479 : Blo 690315 1554479 := bstep (se 1 (by rfl) ⟨1165859, by rfl⟩ : syracuseStep 1554479 = 2331719) B2331719
theorem B4275791 : Blo 690315 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B1754207 : Blo 690315 1754207 := bstep (se 1 (by rfl) ⟨1315655, by rfl⟩ : syracuseStep 1754207 = 2631311) B2631311
theorem B1754855 : Blo 690315 1754855 := bstep (se 1 (by rfl) ⟨1316141, by rfl⟩ : syracuseStep 1754855 = 2632283) B2632283
theorem B1558439 : Blo 690315 1558439 := bstep (se 1 (by rfl) ⟨1168829, by rfl⟩ : syracuseStep 1558439 = 2337659) B2337659
theorem B1755047 : Blo 690315 1755047 := bstep (se 1 (by rfl) ⟨1316285, by rfl⟩ : syracuseStep 1755047 = 2632571) B2632571
theorem B1755209 : Blo 690315 1755209 := bstep (se 2 (by rfl) ⟨658203, by rfl⟩ : syracuseStep 1755209 = 1316407) B1316407
theorem B3950815 : Blo 690315 3950815 := bstep (se 1 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 3950815 = 5926223) B5926223
theorem B1755695 : Blo 690315 1755695 := bstep (se 1 (by rfl) ⟨1316771, by rfl⟩ : syracuseStep 1755695 = 2633543) B2633543
theorem B1166143 : Blo 690315 1166143 := bstep (se 1 (by rfl) ⟨874607, by rfl⟩ : syracuseStep 1166143 = 1749215) B1749215
theorem B1167871 : Blo 690315 1167871 := bstep (se 1 (by rfl) ⟨875903, by rfl⟩ : syracuseStep 1167871 = 1751807) B1751807
theorem B1037111 : Blo 690315 1037111 := bstep (se 1 (by rfl) ⟨777833, by rfl⟩ : syracuseStep 1037111 = 1555667) B1555667
theorem B1037183 : Blo 690315 1037183 := bstep (se 1 (by rfl) ⟨777887, by rfl⟩ : syracuseStep 1037183 = 1555775) B1555775
theorem B1561823 : Blo 690315 1561823 := bstep (se 1 (by rfl) ⟨1171367, by rfl⟩ : syracuseStep 1561823 = 2342735) B2342735
theorem B1038443 : Blo 690315 1038443 := bstep (se 1 (by rfl) ⟨778832, by rfl⟩ : syracuseStep 1038443 = 1557665) B1557665
theorem B776911 : Blo 690315 776911 := bstep (se 1 (by rfl) ⟨582683, by rfl⟩ : syracuseStep 776911 = 1165367) B1165367
theorem B3498227 : Blo 690315 3498227 := bstep (se 1 (by rfl) ⟨2623670, by rfl⟩ : syracuseStep 3498227 = 5247341) B5247341
theorem B1041065 : Blo 690315 1041065 := bstep (se 2 (by rfl) ⟨390399, by rfl⟩ : syracuseStep 1041065 = 780799) B780799
theorem B11201267 : Blo 690315 11201267 := bstep (se 1 (by rfl) ⟨8400950, by rfl⟩ : syracuseStep 11201267 = 16801901) B16801901
theorem B1110527 : Blo 690315 1110527 := bstep (se 1 (by rfl) ⟨832895, by rfl⟩ : syracuseStep 1110527 = 1665791) B1665791
theorem B1244297 : Blo 690315 1244297 := bstep (se 2 (by rfl) ⟨466611, by rfl⟩ : syracuseStep 1244297 = 933223) B933223
theorem B5897519 : Blo 690315 5897519 := bstep (se 1 (by rfl) ⟨4423139, by rfl⟩ : syracuseStep 5897519 = 8846279) B8846279
theorem B691407 : Blo 690315 691407 := bstep (se 1 (by rfl) ⟨518555, by rfl⟩ : syracuseStep 691407 = 1037111) B1037111
theorem B691455 : Blo 690315 691455 := bstep (se 1 (by rfl) ⟨518591, by rfl⟩ : syracuseStep 691455 = 1037183) B1037183
theorem B692295 : Blo 690315 692295 := bstep (se 1 (by rfl) ⟨519221, by rfl⟩ : syracuseStep 692295 = 1038443) B1038443
theorem B3937193 : Blo 690315 3937193 := bstep (se 2 (by rfl) ⟨1476447, by rfl⟩ : syracuseStep 3937193 = 2952895) B2952895
theorem B2332151 : Blo 690315 2332151 := bstep (se 1 (by rfl) ⟨1749113, by rfl⟩ : syracuseStep 2332151 = 3498227) B3498227
theorem B694043 : Blo 690315 694043 := bstep (se 1 (by rfl) ⟨520532, by rfl⟩ : syracuseStep 694043 = 1041065) B1041065
theorem B829531 : Blo 690315 829531 := bstep (se 1 (by rfl) ⟨622148, by rfl⟩ : syracuseStep 829531 = 1244297) B1244297
theorem B19443887 : Blo 690315 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B1554857 : Blo 690315 1554857 := bstep (se 2 (by rfl) ⟨583071, by rfl⟩ : syracuseStep 1554857 = 1166143) B1166143
theorem B1554911 : Blo 690315 1554911 := bstep (se 1 (by rfl) ⟨1166183, by rfl⟩ : syracuseStep 1554911 = 2332367) B2332367
theorem B1555739 : Blo 690315 1555739 := bstep (se 1 (by rfl) ⟨1166804, by rfl⟩ : syracuseStep 1555739 = 2333609) B2333609
theorem B8109359 : Blo 690315 8109359 := bstep (se 1 (by rfl) ⟨6082019, by rfl⟩ : syracuseStep 8109359 = 12164039) B12164039
theorem B1557161 : Blo 690315 1557161 := bstep (se 2 (by rfl) ⟨583935, by rfl⟩ : syracuseStep 1557161 = 1167871) B1167871
theorem B740351 : Blo 690315 740351 := bstep (se 1 (by rfl) ⟨555263, by rfl⟩ : syracuseStep 740351 = 1110527) B1110527
theorem B1035881 : Blo 690315 1035881 := bstep (se 2 (by rfl) ⟨388455, by rfl⟩ : syracuseStep 1035881 = 776911) B776911
theorem B1036319 : Blo 690315 1036319 := bstep (se 1 (by rfl) ⟨777239, by rfl⟩ : syracuseStep 1036319 = 1554479) B1554479
theorem B1169471 : Blo 690315 1169471 := bstep (se 1 (by rfl) ⟨877103, by rfl⟩ : syracuseStep 1169471 = 1754207) B1754207
theorem B1169903 : Blo 690315 1169903 := bstep (se 1 (by rfl) ⟨877427, by rfl⟩ : syracuseStep 1169903 = 1754855) B1754855
theorem B1038959 : Blo 690315 1038959 := bstep (se 1 (by rfl) ⟨779219, by rfl⟩ : syracuseStep 1038959 = 1558439) B1558439
theorem B1170031 : Blo 690315 1170031 := bstep (se 1 (by rfl) ⟨877523, by rfl⟩ : syracuseStep 1170031 = 1755047) B1755047
theorem B3496607 : Blo 690315 3496607 := bstep (se 1 (by rfl) ⟨2622455, by rfl⟩ : syracuseStep 3496607 = 5244911) B5244911
theorem B875215 : Blo 690315 875215 := bstep (se 1 (by rfl) ⟨656411, by rfl⟩ : syracuseStep 875215 = 1312823) B1312823
theorem B1170139 : Blo 690315 1170139 := bstep (se 1 (by rfl) ⟨877604, by rfl⟩ : syracuseStep 1170139 = 1755209) B1755209
theorem B1170463 : Blo 690315 1170463 := bstep (se 1 (by rfl) ⟨877847, by rfl⟩ : syracuseStep 1170463 = 1755695) B1755695
theorem B5267753 : Blo 690315 5267753 := bstep (se 2 (by rfl) ⟨1975407, by rfl⟩ : syracuseStep 5267753 = 3950815) B3950815
theorem B1041215 : Blo 690315 1041215 := bstep (se 1 (by rfl) ⟨780911, by rfl⟩ : syracuseStep 1041215 = 1561823) B1561823
theorem B3498875 : Blo 690315 3498875 := bstep (se 1 (by rfl) ⟨2624156, by rfl⟩ : syracuseStep 3498875 = 5248313) B5248313
theorem B3335849 : Blo 690315 3335849 := bstep (se 2 (by rfl) ⟨1250943, by rfl⟩ : syracuseStep 3335849 = 2501887) B2501887
theorem B7467511 : Blo 690315 7467511 := bstep (se 1 (by rfl) ⟨5600633, by rfl⟩ : syracuseStep 7467511 = 11201267) B11201267
theorem B3931679 : Blo 690315 3931679 := bstep (se 1 (by rfl) ⟨2948759, by rfl⟩ : syracuseStep 3931679 = 5897519) B5897519
theorem B2850527 : Blo 690315 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B4424165 : Blo 690315 4424165 := bstep (se 4 (by rfl) ⟨414765, by rfl⟩ : syracuseStep 4424165 = 829531) B829531
theorem B690587 : Blo 690315 690587 := bstep (se 1 (by rfl) ⟨517940, by rfl⟩ : syracuseStep 690587 = 1035881) B1035881
theorem B690879 : Blo 690315 690879 := bstep (se 1 (by rfl) ⟨518159, by rfl⟩ : syracuseStep 690879 = 1036319) B1036319
theorem B2624795 : Blo 690315 2624795 := bstep (se 1 (by rfl) ⟨1968596, by rfl⟩ : syracuseStep 2624795 = 3937193) B3937193
theorem B692639 : Blo 690315 692639 := bstep (se 1 (by rfl) ⟨519479, by rfl⟩ : syracuseStep 692639 = 1038959) B1038959
theorem B2331071 : Blo 690315 2331071 := bstep (se 1 (by rfl) ⟨1748303, by rfl⟩ : syracuseStep 2331071 = 3496607) B3496607
theorem B3511835 : Blo 690315 3511835 := bstep (se 1 (by rfl) ⟨2633876, by rfl⟩ : syracuseStep 3511835 = 5267753) B5267753
theorem B694143 : Blo 690315 694143 := bstep (se 1 (by rfl) ⟨520607, by rfl⟩ : syracuseStep 694143 = 1041215) B1041215
theorem B2332583 : Blo 690315 2332583 := bstep (se 1 (by rfl) ⟨1749437, by rfl⟩ : syracuseStep 2332583 = 3498875) B3498875
theorem B1974269 : Blo 690315 1974269 := bstep (se 3 (by rfl) ⟨370175, by rfl⟩ : syracuseStep 1974269 = 740351) B740351
theorem B1554767 : Blo 690315 1554767 := bstep (se 1 (by rfl) ⟨1166075, by rfl⟩ : syracuseStep 1554767 = 2332151) B2332151
theorem B12962591 : Blo 690315 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B1560041 : Blo 690315 1560041 := bstep (se 2 (by rfl) ⟨585015, by rfl⟩ : syracuseStep 1560041 = 1170031) B1170031
theorem B1166953 : Blo 690315 1166953 := bstep (se 2 (by rfl) ⟨437607, by rfl⟩ : syracuseStep 1166953 = 875215) B875215
theorem B1560185 : Blo 690315 1560185 := bstep (se 2 (by rfl) ⟨585069, by rfl⟩ : syracuseStep 1560185 = 1170139) B1170139
theorem B1560617 : Blo 690315 1560617 := bstep (se 2 (by rfl) ⟨585231, by rfl⟩ : syracuseStep 1560617 = 1170463) B1170463
theorem B1036571 : Blo 690315 1036571 := bstep (se 1 (by rfl) ⟨777428, by rfl⟩ : syracuseStep 1036571 = 1554857) B1554857
theorem B1036607 : Blo 690315 1036607 := bstep (se 1 (by rfl) ⟨777455, by rfl⟩ : syracuseStep 1036607 = 1554911) B1554911
theorem B1037159 : Blo 690315 1037159 := bstep (se 1 (by rfl) ⟨777869, by rfl⟩ : syracuseStep 1037159 = 1555739) B1555739
theorem B1038107 : Blo 690315 1038107 := bstep (se 1 (by rfl) ⟨778580, by rfl⟩ : syracuseStep 1038107 = 1557161) B1557161
theorem B779647 : Blo 690315 779647 := bstep (se 1 (by rfl) ⟨584735, by rfl⟩ : syracuseStep 779647 = 1169471) B1169471
theorem B779935 : Blo 690315 779935 := bstep (se 1 (by rfl) ⟨584951, by rfl⟩ : syracuseStep 779935 = 1169903) B1169903
theorem B9956681 : Blo 690315 9956681 := bstep (se 2 (by rfl) ⟨3733755, by rfl⟩ : syracuseStep 9956681 = 7467511) B7467511
theorem B2223899 : Blo 690315 2223899 := bstep (se 1 (by rfl) ⟨1667924, by rfl⟩ : syracuseStep 2223899 = 3335849) B3335849
theorem B5406239 : Blo 690315 5406239 := bstep (se 1 (by rfl) ⟨4054679, by rfl⟩ : syracuseStep 5406239 = 8109359) B8109359
theorem B2621119 : Blo 690315 2621119 := bstep (se 1 (by rfl) ⟨1965839, by rfl⟩ : syracuseStep 2621119 = 3931679) B3931679
theorem B1900351 : Blo 690315 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B2949443 : Blo 690315 2949443 := bstep (se 1 (by rfl) ⟨2212082, by rfl⟩ : syracuseStep 2949443 = 4424165) B4424165
theorem B691047 : Blo 690315 691047 := bstep (se 1 (by rfl) ⟨518285, by rfl⟩ : syracuseStep 691047 = 1036571) B1036571
theorem B691071 : Blo 690315 691071 := bstep (se 1 (by rfl) ⟨518303, by rfl⟩ : syracuseStep 691071 = 1036607) B1036607
theorem B691439 : Blo 690315 691439 := bstep (se 1 (by rfl) ⟨518579, by rfl⟩ : syracuseStep 691439 = 1037159) B1037159
theorem B692071 : Blo 690315 692071 := bstep (se 1 (by rfl) ⟨519053, by rfl⟩ : syracuseStep 692071 = 1038107) B1038107
theorem B1316179 : Blo 690315 1316179 := bstep (se 1 (by rfl) ⟨987134, by rfl⟩ : syracuseStep 1316179 = 1974269) B1974269
theorem B1482599 : Blo 690315 1482599 := bstep (se 1 (by rfl) ⟨1111949, by rfl⟩ : syracuseStep 1482599 = 2223899) B2223899
theorem B10135205 : Blo 690315 10135205 := bstep (se 4 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 10135205 = 1900351) B1900351
theorem B1749863 : Blo 690315 1749863 := bstep (se 1 (by rfl) ⟨1312397, by rfl⟩ : syracuseStep 1749863 = 2624795) B2624795
theorem B1554047 : Blo 690315 1554047 := bstep (se 1 (by rfl) ⟨1165535, by rfl⟩ : syracuseStep 1554047 = 2331071) B2331071
theorem B2341223 : Blo 690315 2341223 := bstep (se 1 (by rfl) ⟨1755917, by rfl⟩ : syracuseStep 2341223 = 3511835) B3511835
theorem B1555055 : Blo 690315 1555055 := bstep (se 1 (by rfl) ⟨1166291, by rfl⟩ : syracuseStep 1555055 = 2332583) B2332583
theorem B1555937 : Blo 690315 1555937 := bstep (se 2 (by rfl) ⟨583476, by rfl⟩ : syracuseStep 1555937 = 1166953) B1166953
theorem B6637787 : Blo 690315 6637787 := bstep (se 1 (by rfl) ⟨4978340, by rfl⟩ : syracuseStep 6637787 = 9956681) B9956681
theorem B1036511 : Blo 690315 1036511 := bstep (se 1 (by rfl) ⟨777383, by rfl⟩ : syracuseStep 1036511 = 1554767) B1554767
theorem B3494825 : Blo 690315 3494825 := bstep (se 2 (by rfl) ⟨1310559, by rfl⟩ : syracuseStep 3494825 = 2621119) B2621119
theorem B1039529 : Blo 690315 1039529 := bstep (se 2 (by rfl) ⟨389823, by rfl⟩ : syracuseStep 1039529 = 779647) B779647
theorem B8641727 : Blo 690315 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B1039913 : Blo 690315 1039913 := bstep (se 2 (by rfl) ⟨389967, by rfl⟩ : syracuseStep 1039913 = 779935) B779935
theorem B1040027 : Blo 690315 1040027 := bstep (se 1 (by rfl) ⟨780020, by rfl⟩ : syracuseStep 1040027 = 1560041) B1560041
theorem B1040123 : Blo 690315 1040123 := bstep (se 1 (by rfl) ⟨780092, by rfl⟩ : syracuseStep 1040123 = 1560185) B1560185
theorem B1040411 : Blo 690315 1040411 := bstep (se 1 (by rfl) ⟨780308, by rfl⟩ : syracuseStep 1040411 = 1560617) B1560617
theorem B3604159 : Blo 690315 3604159 := bstep (se 1 (by rfl) ⟨2703119, by rfl⟩ : syracuseStep 3604159 = 5406239) B5406239
theorem B1966295 : Blo 690315 1966295 := bstep (se 1 (by rfl) ⟨1474721, by rfl⟩ : syracuseStep 1966295 = 2949443) B2949443
theorem B4425191 : Blo 690315 4425191 := bstep (se 1 (by rfl) ⟨3318893, by rfl⟩ : syracuseStep 4425191 = 6637787) B6637787
theorem B691007 : Blo 690315 691007 := bstep (se 1 (by rfl) ⟨518255, by rfl⟩ : syracuseStep 691007 = 1036511) B1036511
theorem B2329883 : Blo 690315 2329883 := bstep (se 1 (by rfl) ⟨1747412, by rfl⟩ : syracuseStep 2329883 = 3494825) B3494825
theorem B693019 : Blo 690315 693019 := bstep (se 1 (by rfl) ⟨519764, by rfl⟩ : syracuseStep 693019 = 1039529) B1039529
theorem B693275 : Blo 690315 693275 := bstep (se 1 (by rfl) ⟨519956, by rfl⟩ : syracuseStep 693275 = 1039913) B1039913
theorem B693351 : Blo 690315 693351 := bstep (se 1 (by rfl) ⟨520013, by rfl⟩ : syracuseStep 693351 = 1040027) B1040027
theorem B693415 : Blo 690315 693415 := bstep (se 1 (by rfl) ⟨520061, by rfl⟩ : syracuseStep 693415 = 1040123) B1040123
theorem B988399 : Blo 690315 988399 := bstep (se 1 (by rfl) ⟨741299, by rfl⟩ : syracuseStep 988399 = 1482599) B1482599
theorem B693607 : Blo 690315 693607 := bstep (se 1 (by rfl) ⟨520205, by rfl⟩ : syracuseStep 693607 = 1040411) B1040411
theorem B6756803 : Blo 690315 6756803 := bstep (se 1 (by rfl) ⟨5067602, by rfl⟩ : syracuseStep 6756803 = 10135205) B10135205
theorem B1754905 : Blo 690315 1754905 := bstep (se 2 (by rfl) ⟨658089, by rfl⟩ : syracuseStep 1754905 = 1316179) B1316179
theorem B1166575 : Blo 690315 1166575 := bstep (se 1 (by rfl) ⟨874931, by rfl⟩ : syracuseStep 1166575 = 1749863) B1749863
theorem B19222181 : Blo 690315 19222181 := bstep (se 4 (by rfl) ⟨1802079, by rfl⟩ : syracuseStep 19222181 = 3604159) B3604159
theorem B1036031 : Blo 690315 1036031 := bstep (se 1 (by rfl) ⟨777023, by rfl⟩ : syracuseStep 1036031 = 1554047) B1554047
theorem B1560815 : Blo 690315 1560815 := bstep (se 1 (by rfl) ⟨1170611, by rfl⟩ : syracuseStep 1560815 = 2341223) B2341223
theorem B1036703 : Blo 690315 1036703 := bstep (se 1 (by rfl) ⟨777527, by rfl⟩ : syracuseStep 1036703 = 1555055) B1555055
theorem B1037291 : Blo 690315 1037291 := bstep (se 1 (by rfl) ⟨777968, by rfl⟩ : syracuseStep 1037291 = 1555937) B1555937
theorem B5761151 : Blo 690315 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B5243453 : Blo 690315 5243453 := bstep (se 3 (by rfl) ⟨983147, by rfl⟩ : syracuseStep 5243453 = 1966295) B1966295
theorem B2950127 : Blo 690315 2950127 := bstep (se 1 (by rfl) ⟨2212595, by rfl⟩ : syracuseStep 2950127 = 4425191) B4425191
theorem B12814787 : Blo 690315 12814787 := bstep (se 1 (by rfl) ⟨9611090, by rfl⟩ : syracuseStep 12814787 = 19222181) B19222181
theorem B690687 : Blo 690315 690687 := bstep (se 1 (by rfl) ⟨518015, by rfl⟩ : syracuseStep 690687 = 1036031) B1036031
theorem B691135 : Blo 690315 691135 := bstep (se 1 (by rfl) ⟨518351, by rfl⟩ : syracuseStep 691135 = 1036703) B1036703
theorem B691527 : Blo 690315 691527 := bstep (se 1 (by rfl) ⟨518645, by rfl⟩ : syracuseStep 691527 = 1037291) B1037291
theorem B3840767 : Blo 690315 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B1317865 : Blo 690315 1317865 := bstep (se 2 (by rfl) ⟨494199, by rfl⟩ : syracuseStep 1317865 = 988399) B988399
theorem B1553255 : Blo 690315 1553255 := bstep (se 1 (by rfl) ⟨1164941, by rfl⟩ : syracuseStep 1553255 = 2329883) B2329883
theorem B2339873 : Blo 690315 2339873 := bstep (se 2 (by rfl) ⟨877452, by rfl⟩ : syracuseStep 2339873 = 1754905) B1754905
theorem B4504535 : Blo 690315 4504535 := bstep (se 1 (by rfl) ⟨3378401, by rfl⟩ : syracuseStep 4504535 = 6756803) B6756803
theorem B1555433 : Blo 690315 1555433 := bstep (se 2 (by rfl) ⟨583287, by rfl⟩ : syracuseStep 1555433 = 1166575) B1166575
theorem B1040543 : Blo 690315 1040543 := bstep (se 1 (by rfl) ⟨780407, by rfl⟩ : syracuseStep 1040543 = 1560815) B1560815
theorem B1966751 : Blo 690315 1966751 := bstep (se 1 (by rfl) ⟨1475063, by rfl⟩ : syracuseStep 1966751 = 2950127) B2950127
theorem B2560511 : Blo 690315 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B693695 : Blo 690315 693695 := bstep (se 1 (by rfl) ⟨520271, by rfl⟩ : syracuseStep 693695 = 1040543) B1040543
theorem B1035503 : Blo 690315 1035503 := bstep (se 1 (by rfl) ⟨776627, by rfl⟩ : syracuseStep 1035503 = 1553255) B1553255
theorem B1559915 : Blo 690315 1559915 := bstep (se 1 (by rfl) ⟨1169936, by rfl⟩ : syracuseStep 1559915 = 2339873) B2339873
theorem B1757153 : Blo 690315 1757153 := bstep (se 2 (by rfl) ⟨658932, by rfl⟩ : syracuseStep 1757153 = 1317865) B1317865
theorem B3003023 : Blo 690315 3003023 := bstep (se 1 (by rfl) ⟨2252267, by rfl⟩ : syracuseStep 3003023 = 4504535) B4504535
theorem B1036955 : Blo 690315 1036955 := bstep (se 1 (by rfl) ⟨777716, by rfl⟩ : syracuseStep 1036955 = 1555433) B1555433
theorem B3495635 : Blo 690315 3495635 := bstep (se 1 (by rfl) ⟨2621726, by rfl⟩ : syracuseStep 3495635 = 5243453) B5243453
theorem B34172765 : Blo 690315 34172765 := bstep (se 3 (by rfl) ⟨6407393, by rfl⟩ : syracuseStep 34172765 = 12814787) B12814787
theorem B1311167 : Blo 690315 1311167 := bstep (se 1 (by rfl) ⟨983375, by rfl⟩ : syracuseStep 1311167 = 1966751) B1966751
theorem B690335 : Blo 690315 690335 := bstep (se 1 (by rfl) ⟨517751, by rfl⟩ : syracuseStep 690335 = 1035503) B1035503
theorem B1707007 : Blo 690315 1707007 := bstep (se 1 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 1707007 = 2560511) B2560511
theorem B2002015 : Blo 690315 2002015 := bstep (se 1 (by rfl) ⟨1501511, by rfl⟩ : syracuseStep 2002015 = 3003023) B3003023
theorem B691303 : Blo 690315 691303 := bstep (se 1 (by rfl) ⟨518477, by rfl⟩ : syracuseStep 691303 = 1036955) B1036955
theorem B2330423 : Blo 690315 2330423 := bstep (se 1 (by rfl) ⟨1747817, by rfl⟩ : syracuseStep 2330423 = 3495635) B3495635
theorem B22781843 : Blo 690315 22781843 := bstep (se 1 (by rfl) ⟨17086382, by rfl⟩ : syracuseStep 22781843 = 34172765) B34172765
theorem B1039943 : Blo 690315 1039943 := bstep (se 1 (by rfl) ⟨779957, by rfl⟩ : syracuseStep 1039943 = 1559915) B1559915
theorem B1171435 : Blo 690315 1171435 := bstep (se 1 (by rfl) ⟨878576, by rfl⟩ : syracuseStep 1171435 = 1757153) B1757153
theorem B693295 : Blo 690315 693295 := bstep (se 1 (by rfl) ⟨519971, by rfl⟩ : syracuseStep 693295 = 1039943) B1039943
theorem B1553615 : Blo 690315 1553615 := bstep (se 1 (by rfl) ⟨1165211, by rfl⟩ : syracuseStep 1553615 = 2330423) B2330423
theorem B2276009 : Blo 690315 2276009 := bstep (se 2 (by rfl) ⟨853503, by rfl⟩ : syracuseStep 2276009 = 1707007) B1707007
theorem B15187895 : Blo 690315 15187895 := bstep (se 1 (by rfl) ⟨11390921, by rfl⟩ : syracuseStep 15187895 = 22781843) B22781843
theorem B1561913 : Blo 690315 1561913 := bstep (se 2 (by rfl) ⟨585717, by rfl⟩ : syracuseStep 1561913 = 1171435) B1171435
theorem B3496445 : Blo 690315 3496445 := bstep (se 3 (by rfl) ⟨655583, by rfl⟩ : syracuseStep 3496445 = 1311167) B1311167
theorem B10677413 : Blo 690315 10677413 := bstep (se 4 (by rfl) ⟨1001007, by rfl⟩ : syracuseStep 10677413 = 2002015) B2002015
theorem B2330963 : Blo 690315 2330963 := bstep (se 1 (by rfl) ⟨1748222, by rfl⟩ : syracuseStep 2330963 = 3496445) B3496445
theorem B7118275 : Blo 690315 7118275 := bstep (se 1 (by rfl) ⟨5338706, by rfl⟩ : syracuseStep 7118275 = 10677413) B10677413
theorem B1517339 : Blo 690315 1517339 := bstep (se 1 (by rfl) ⟨1138004, by rfl⟩ : syracuseStep 1517339 = 2276009) B2276009
theorem B1035743 : Blo 690315 1035743 := bstep (se 1 (by rfl) ⟨776807, by rfl⟩ : syracuseStep 1035743 = 1553615) B1553615
theorem B1041275 : Blo 690315 1041275 := bstep (se 1 (by rfl) ⟨780956, by rfl⟩ : syracuseStep 1041275 = 1561913) B1561913
theorem B10125263 : Blo 690315 10125263 := bstep (se 1 (by rfl) ⟨7593947, by rfl⟩ : syracuseStep 10125263 = 15187895) B15187895
theorem B690495 : Blo 690315 690495 := bstep (se 1 (by rfl) ⟨517871, by rfl⟩ : syracuseStep 690495 = 1035743) B1035743
theorem B694183 : Blo 690315 694183 := bstep (se 1 (by rfl) ⟨520637, by rfl⟩ : syracuseStep 694183 = 1041275) B1041275
theorem B1553975 : Blo 690315 1553975 := bstep (se 1 (by rfl) ⟨1165481, by rfl⟩ : syracuseStep 1553975 = 2330963) B2330963
theorem B9491033 : Blo 690315 9491033 := bstep (se 2 (by rfl) ⟨3559137, by rfl⟩ : syracuseStep 9491033 = 7118275) B7118275
theorem B1011559 : Blo 690315 1011559 := bstep (se 1 (by rfl) ⟨758669, by rfl⟩ : syracuseStep 1011559 = 1517339) B1517339
theorem B27000701 : Blo 690315 27000701 := bstep (se 3 (by rfl) ⟨5062631, by rfl⟩ : syracuseStep 27000701 = 10125263) B10125263
theorem B1348745 : Blo 690315 1348745 := bstep (se 2 (by rfl) ⟨505779, by rfl⟩ : syracuseStep 1348745 = 1011559) B1011559
theorem B18000467 : Blo 690315 18000467 := bstep (se 1 (by rfl) ⟨13500350, by rfl⟩ : syracuseStep 18000467 = 27000701) B27000701
theorem B25309421 : Blo 690315 25309421 := bstep (se 3 (by rfl) ⟨4745516, by rfl⟩ : syracuseStep 25309421 = 9491033) B9491033
theorem B1035983 : Blo 690315 1035983 := bstep (se 1 (by rfl) ⟨776987, by rfl⟩ : syracuseStep 1035983 = 1553975) B1553975
theorem B690655 : Blo 690315 690655 := bstep (se 1 (by rfl) ⟨517991, by rfl⟩ : syracuseStep 690655 = 1035983) B1035983
theorem B12000311 : Blo 690315 12000311 := bstep (se 1 (by rfl) ⟨9000233, by rfl⟩ : syracuseStep 12000311 = 18000467) B18000467
theorem B3596653 : Blo 690315 3596653 := bstep (se 3 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 3596653 = 1348745) B1348745
theorem B16872947 : Blo 690315 16872947 := bstep (se 1 (by rfl) ⟨12654710, by rfl⟩ : syracuseStep 16872947 = 25309421) B25309421
theorem B8000207 : Blo 690315 8000207 := bstep (se 1 (by rfl) ⟨6000155, by rfl⟩ : syracuseStep 8000207 = 12000311) B12000311
theorem B11248631 : Blo 690315 11248631 := bstep (se 1 (by rfl) ⟨8436473, by rfl⟩ : syracuseStep 11248631 = 16872947) B16872947
theorem B4795537 : Blo 690315 4795537 := bstep (se 2 (by rfl) ⟨1798326, by rfl⟩ : syracuseStep 4795537 = 3596653) B3596653
theorem B6394049 : Blo 690315 6394049 := bstep (se 2 (by rfl) ⟨2397768, by rfl⟩ : syracuseStep 6394049 = 4795537) B4795537
theorem B5333471 : Blo 690315 5333471 := bstep (se 1 (by rfl) ⟨4000103, by rfl⟩ : syracuseStep 5333471 = 8000207) B8000207
theorem B7499087 : Blo 690315 7499087 := bstep (se 1 (by rfl) ⟨5624315, by rfl⟩ : syracuseStep 7499087 = 11248631) B11248631
theorem B4262699 : Blo 690315 4262699 := bstep (se 1 (by rfl) ⟨3197024, by rfl⟩ : syracuseStep 4262699 = 6394049) B6394049
theorem B3555647 : Blo 690315 3555647 := bstep (se 1 (by rfl) ⟨2666735, by rfl⟩ : syracuseStep 3555647 = 5333471) B5333471
theorem B4999391 : Blo 690315 4999391 := bstep (se 1 (by rfl) ⟨3749543, by rfl⟩ : syracuseStep 4999391 = 7499087) B7499087
theorem B2370431 : Blo 690315 2370431 := bstep (se 1 (by rfl) ⟨1777823, by rfl⟩ : syracuseStep 2370431 = 3555647) B3555647
theorem B3332927 : Blo 690315 3332927 := bstep (se 1 (by rfl) ⟨2499695, by rfl⟩ : syracuseStep 3332927 = 4999391) B4999391
theorem B2841799 : Blo 690315 2841799 := bstep (se 1 (by rfl) ⟨2131349, by rfl⟩ : syracuseStep 2841799 = 4262699) B4262699
theorem B3789065 : Blo 690315 3789065 := bstep (se 2 (by rfl) ⟨1420899, by rfl⟩ : syracuseStep 3789065 = 2841799) B2841799
theorem B2221951 : Blo 690315 2221951 := bstep (se 1 (by rfl) ⟨1666463, by rfl⟩ : syracuseStep 2221951 = 3332927) B3332927
theorem B6321149 : Blo 690315 6321149 := bstep (se 3 (by rfl) ⟨1185215, by rfl⟩ : syracuseStep 6321149 = 2370431) B2370431
theorem B10104173 : Blo 690315 10104173 := bstep (se 3 (by rfl) ⟨1894532, by rfl⟩ : syracuseStep 10104173 = 3789065) B3789065
theorem B2962601 : Blo 690315 2962601 := bstep (se 2 (by rfl) ⟨1110975, by rfl⟩ : syracuseStep 2962601 = 2221951) B2221951
theorem B4214099 : Blo 690315 4214099 := bstep (se 1 (by rfl) ⟨3160574, by rfl⟩ : syracuseStep 4214099 = 6321149) B6321149
theorem B1975067 : Blo 690315 1975067 := bstep (se 1 (by rfl) ⟨1481300, by rfl⟩ : syracuseStep 1975067 = 2962601) B2962601
theorem B6736115 : Blo 690315 6736115 := bstep (se 1 (by rfl) ⟨5052086, by rfl⟩ : syracuseStep 6736115 = 10104173) B10104173
theorem B2809399 : Blo 690315 2809399 := bstep (se 1 (by rfl) ⟨2107049, by rfl⟩ : syracuseStep 2809399 = 4214099) B4214099
theorem B4490743 : Blo 690315 4490743 := bstep (se 1 (by rfl) ⟨3368057, by rfl⟩ : syracuseStep 4490743 = 6736115) B6736115
theorem B1316711 : Blo 690315 1316711 := bstep (se 1 (by rfl) ⟨987533, by rfl⟩ : syracuseStep 1316711 = 1975067) B1975067
theorem B3745865 : Blo 690315 3745865 := bstep (se 2 (by rfl) ⟨1404699, by rfl⟩ : syracuseStep 3745865 = 2809399) B2809399
theorem B2497243 : Blo 690315 2497243 := bstep (se 1 (by rfl) ⟨1872932, by rfl⟩ : syracuseStep 2497243 = 3745865) B3745865
theorem B5987657 : Blo 690315 5987657 := bstep (se 2 (by rfl) ⟨2245371, by rfl⟩ : syracuseStep 5987657 = 4490743) B4490743
theorem B877807 : Blo 690315 877807 := bstep (se 1 (by rfl) ⟨658355, by rfl⟩ : syracuseStep 877807 = 1316711) B1316711
theorem B3329657 : Blo 690315 3329657 := bstep (se 2 (by rfl) ⟨1248621, by rfl⟩ : syracuseStep 3329657 = 2497243) B2497243
theorem B1170409 : Blo 690315 1170409 := bstep (se 2 (by rfl) ⟨438903, by rfl⟩ : syracuseStep 1170409 = 877807) B877807
theorem B3991771 : Blo 690315 3991771 := bstep (se 1 (by rfl) ⟨2993828, by rfl⟩ : syracuseStep 3991771 = 5987657) B5987657
theorem B5322361 : Blo 690315 5322361 := bstep (se 2 (by rfl) ⟨1995885, by rfl⟩ : syracuseStep 5322361 = 3991771) B3991771
theorem B1560545 : Blo 690315 1560545 := bstep (se 2 (by rfl) ⟨585204, by rfl⟩ : syracuseStep 1560545 = 1170409) B1170409
theorem B2219771 : Blo 690315 2219771 := bstep (se 1 (by rfl) ⟨1664828, by rfl⟩ : syracuseStep 2219771 = 3329657) B3329657
theorem B7096481 : Blo 690315 7096481 := bstep (se 2 (by rfl) ⟨2661180, by rfl⟩ : syracuseStep 7096481 = 5322361) B5322361
theorem B5919389 : Blo 690315 5919389 := bstep (se 3 (by rfl) ⟨1109885, by rfl⟩ : syracuseStep 5919389 = 2219771) B2219771
theorem B1040363 : Blo 690315 1040363 := bstep (se 1 (by rfl) ⟨780272, by rfl⟩ : syracuseStep 1040363 = 1560545) B1560545
theorem B693575 : Blo 690315 693575 := bstep (se 1 (by rfl) ⟨520181, by rfl⟩ : syracuseStep 693575 = 1040363) B1040363
theorem B4730987 : Blo 690315 4730987 := bstep (se 1 (by rfl) ⟨3548240, by rfl⟩ : syracuseStep 4730987 = 7096481) B7096481
theorem B3946259 : Blo 690315 3946259 := bstep (se 1 (by rfl) ⟨2959694, by rfl⟩ : syracuseStep 3946259 = 5919389) B5919389
theorem B3153991 : Blo 690315 3153991 := bstep (se 1 (by rfl) ⟨2365493, by rfl⟩ : syracuseStep 3153991 = 4730987) B4730987
theorem B2630839 : Blo 690315 2630839 := bstep (se 1 (by rfl) ⟨1973129, by rfl⟩ : syracuseStep 2630839 = 3946259) B3946259
theorem B3507785 : Blo 690315 3507785 := bstep (se 2 (by rfl) ⟨1315419, by rfl⟩ : syracuseStep 3507785 = 2630839) B2630839
theorem B4205321 : Blo 690315 4205321 := bstep (se 2 (by rfl) ⟨1576995, by rfl⟩ : syracuseStep 4205321 = 3153991) B3153991
theorem B2338523 : Blo 690315 2338523 := bstep (se 1 (by rfl) ⟨1753892, by rfl⟩ : syracuseStep 2338523 = 3507785) B3507785
theorem B2803547 : Blo 690315 2803547 := bstep (se 1 (by rfl) ⟨2102660, by rfl⟩ : syracuseStep 2803547 = 4205321) B4205321
theorem B1869031 : Blo 690315 1869031 := bstep (se 1 (by rfl) ⟨1401773, by rfl⟩ : syracuseStep 1869031 = 2803547) B2803547
theorem B1559015 : Blo 690315 1559015 := bstep (se 1 (by rfl) ⟨1169261, by rfl⟩ : syracuseStep 1559015 = 2338523) B2338523
theorem B2492041 : Blo 690315 2492041 := bstep (se 2 (by rfl) ⟨934515, by rfl⟩ : syracuseStep 2492041 = 1869031) B1869031
theorem B1039343 : Blo 690315 1039343 := bstep (se 1 (by rfl) ⟨779507, by rfl⟩ : syracuseStep 1039343 = 1559015) B1559015
theorem B692895 : Blo 690315 692895 := bstep (se 1 (by rfl) ⟨519671, by rfl⟩ : syracuseStep 692895 = 1039343) B1039343
theorem B3322721 : Blo 690315 3322721 := bstep (se 2 (by rfl) ⟨1246020, by rfl⟩ : syracuseStep 3322721 = 2492041) B2492041
theorem B2215147 : Blo 690315 2215147 := bstep (se 1 (by rfl) ⟨1661360, by rfl⟩ : syracuseStep 2215147 = 3322721) B3322721
theorem B2953529 : Blo 690315 2953529 := bstep (se 2 (by rfl) ⟨1107573, by rfl⟩ : syracuseStep 2953529 = 2215147) B2215147
theorem B1969019 : Blo 690315 1969019 := bstep (se 1 (by rfl) ⟨1476764, by rfl⟩ : syracuseStep 1969019 = 2953529) B2953529
theorem B1312679 : Blo 690315 1312679 := bstep (se 1 (by rfl) ⟨984509, by rfl⟩ : syracuseStep 1312679 = 1969019) B1969019
theorem B875119 : Blo 690315 875119 := bstep (se 1 (by rfl) ⟨656339, by rfl⟩ : syracuseStep 875119 = 1312679) B1312679
theorem B1166825 : Blo 690315 1166825 := bstep (se 2 (by rfl) ⟨437559, by rfl⟩ : syracuseStep 1166825 = 875119) B875119
theorem B777883 : Blo 690315 777883 := bstep (se 1 (by rfl) ⟨583412, by rfl⟩ : syracuseStep 777883 = 1166825) B1166825
theorem B1037177 : Blo 690315 1037177 := bstep (se 2 (by rfl) ⟨388941, by rfl⟩ : syracuseStep 1037177 = 777883) B777883
theorem B691451 : Blo 690315 691451 := bstep (se 1 (by rfl) ⟨518588, by rfl⟩ : syracuseStep 691451 = 1037177) B1037177

theorem C0 (j : ℕ) (h1 : 172578 ≤ j) (h2 : j ≤ 173277) : Blo 690315 (4 * j + 3) := by
  interval_cases j
  · exact B690315
  · exact B690319
  · exact B690323
  · exact B690327
  · exact B690331
  · exact B690335
  · exact B690339
  · exact B690343
  · exact B690347
  · exact B690351
  · exact B690355
  · exact B690359
  · exact B690363
  · exact B690367
  · exact B690371
  · exact B690375
  · exact B690379
  · exact B690383
  · exact B690387
  · exact B690391
  · exact B690395
  · exact B690399
  · exact B690403
  · exact B690407
  · exact B690411
  · exact B690415
  · exact B690419
  · exact B690423
  · exact B690427
  · exact B690431
  · exact B690435
  · exact B690439
  · exact B690443
  · exact B690447
  · exact B690451
  · exact B690455
  · exact B690459
  · exact B690463
  · exact B690467
  · exact B690471
  · exact B690475
  · exact B690479
  · exact B690483
  · exact B690487
  · exact B690491
  · exact B690495
  · exact B690499
  · exact B690503
  · exact B690507
  · exact B690511
  · exact B690515
  · exact B690519
  · exact B690523
  · exact B690527
  · exact B690531
  · exact B690535
  · exact B690539
  · exact B690543
  · exact B690547
  · exact B690551
  · exact B690555
  · exact B690559
  · exact B690563
  · exact B690567
  · exact B690571
  · exact B690575
  · exact B690579
  · exact B690583
  · exact B690587
  · exact B690591
  · exact B690595
  · exact B690599
  · exact B690603
  · exact B690607
  · exact B690611
  · exact B690615
  · exact B690619
  · exact B690623
  · exact B690627
  · exact B690631
  · exact B690635
  · exact B690639
  · exact B690643
  · exact B690647
  · exact B690651
  · exact B690655
  · exact B690659
  · exact B690663
  · exact B690667
  · exact B690671
  · exact B690675
  · exact B690679
  · exact B690683
  · exact B690687
  · exact B690691
  · exact B690695
  · exact B690699
  · exact B690703
  · exact B690707
  · exact B690711
  · exact B690715
  · exact B690719
  · exact B690723
  · exact B690727
  · exact B690731
  · exact B690735
  · exact B690739
  · exact B690743
  · exact B690747
  · exact B690751
  · exact B690755
  · exact B690759
  · exact B690763
  · exact B690767
  · exact B690771
  · exact B690775
  · exact B690779
  · exact B690783
  · exact B690787
  · exact B690791
  · exact B690795
  · exact B690799
  · exact B690803
  · exact B690807
  · exact B690811
  · exact B690815
  · exact B690819
  · exact B690823
  · exact B690827
  · exact B690831
  · exact B690835
  · exact B690839
  · exact B690843
  · exact B690847
  · exact B690851
  · exact B690855
  · exact B690859
  · exact B690863
  · exact B690867
  · exact B690871
  · exact B690875
  · exact B690879
  · exact B690883
  · exact B690887
  · exact B690891
  · exact B690895
  · exact B690899
  · exact B690903
  · exact B690907
  · exact B690911
  · exact B690915
  · exact B690919
  · exact B690923
  · exact B690927
  · exact B690931
  · exact B690935
  · exact B690939
  · exact B690943
  · exact B690947
  · exact B690951
  · exact B690955
  · exact B690959
  · exact B690963
  · exact B690967
  · exact B690971
  · exact B690975
  · exact B690979
  · exact B690983
  · exact B690987
  · exact B690991
  · exact B690995
  · exact B690999
  · exact B691003
  · exact B691007
  · exact B691011
  · exact B691015
  · exact B691019
  · exact B691023
  · exact B691027
  · exact B691031
  · exact B691035
  · exact B691039
  · exact B691043
  · exact B691047
  · exact B691051
  · exact B691055
  · exact B691059
  · exact B691063
  · exact B691067
  · exact B691071
  · exact B691075
  · exact B691079
  · exact B691083
  · exact B691087
  · exact B691091
  · exact B691095
  · exact B691099
  · exact B691103
  · exact B691107
  · exact B691111
  · exact B691115
  · exact B691119
  · exact B691123
  · exact B691127
  · exact B691131
  · exact B691135
  · exact B691139
  · exact B691143
  · exact B691147
  · exact B691151
  · exact B691155
  · exact B691159
  · exact B691163
  · exact B691167
  · exact B691171
  · exact B691175
  · exact B691179
  · exact B691183
  · exact B691187
  · exact B691191
  · exact B691195
  · exact B691199
  · exact B691203
  · exact B691207
  · exact B691211
  · exact B691215
  · exact B691219
  · exact B691223
  · exact B691227
  · exact B691231
  · exact B691235
  · exact B691239
  · exact B691243
  · exact B691247
  · exact B691251
  · exact B691255
  · exact B691259
  · exact B691263
  · exact B691267
  · exact B691271
  · exact B691275
  · exact B691279
  · exact B691283
  · exact B691287
  · exact B691291
  · exact B691295
  · exact B691299
  · exact B691303
  · exact B691307
  · exact B691311
  · exact B691315
  · exact B691319
  · exact B691323
  · exact B691327
  · exact B691331
  · exact B691335
  · exact B691339
  · exact B691343
  · exact B691347
  · exact B691351
  · exact B691355
  · exact B691359
  · exact B691363
  · exact B691367
  · exact B691371
  · exact B691375
  · exact B691379
  · exact B691383
  · exact B691387
  · exact B691391
  · exact B691395
  · exact B691399
  · exact B691403
  · exact B691407
  · exact B691411
  · exact B691415
  · exact B691419
  · exact B691423
  · exact B691427
  · exact B691431
  · exact B691435
  · exact B691439
  · exact B691443
  · exact B691447
  · exact B691451
  · exact B691455
  · exact B691459
  · exact B691463
  · exact B691467
  · exact B691471
  · exact B691475
  · exact B691479
  · exact B691483
  · exact B691487
  · exact B691491
  · exact B691495
  · exact B691499
  · exact B691503
  · exact B691507
  · exact B691511
  · exact B691515
  · exact B691519
  · exact B691523
  · exact B691527
  · exact B691531
  · exact B691535
  · exact B691539
  · exact B691543
  · exact B691547
  · exact B691551
  · exact B691555
  · exact B691559
  · exact B691563
  · exact B691567
  · exact B691571
  · exact B691575
  · exact B691579
  · exact B691583
  · exact B691587
  · exact B691591
  · exact B691595
  · exact B691599
  · exact B691603
  · exact B691607
  · exact B691611
  · exact B691615
  · exact B691619
  · exact B691623
  · exact B691627
  · exact B691631
  · exact B691635
  · exact B691639
  · exact B691643
  · exact B691647
  · exact B691651
  · exact B691655
  · exact B691659
  · exact B691663
  · exact B691667
  · exact B691671
  · exact B691675
  · exact B691679
  · exact B691683
  · exact B691687
  · exact B691691
  · exact B691695
  · exact B691699
  · exact B691703
  · exact B691707
  · exact B691711
  · exact B691715
  · exact B691719
  · exact B691723
  · exact B691727
  · exact B691731
  · exact B691735
  · exact B691739
  · exact B691743
  · exact B691747
  · exact B691751
  · exact B691755
  · exact B691759
  · exact B691763
  · exact B691767
  · exact B691771
  · exact B691775
  · exact B691779
  · exact B691783
  · exact B691787
  · exact B691791
  · exact B691795
  · exact B691799
  · exact B691803
  · exact B691807
  · exact B691811
  · exact B691815
  · exact B691819
  · exact B691823
  · exact B691827
  · exact B691831
  · exact B691835
  · exact B691839
  · exact B691843
  · exact B691847
  · exact B691851
  · exact B691855
  · exact B691859
  · exact B691863
  · exact B691867
  · exact B691871
  · exact B691875
  · exact B691879
  · exact B691883
  · exact B691887
  · exact B691891
  · exact B691895
  · exact B691899
  · exact B691903
  · exact B691907
  · exact B691911
  · exact B691915
  · exact B691919
  · exact B691923
  · exact B691927
  · exact B691931
  · exact B691935
  · exact B691939
  · exact B691943
  · exact B691947
  · exact B691951
  · exact B691955
  · exact B691959
  · exact B691963
  · exact B691967
  · exact B691971
  · exact B691975
  · exact B691979
  · exact B691983
  · exact B691987
  · exact B691991
  · exact B691995
  · exact B691999
  · exact B692003
  · exact B692007
  · exact B692011
  · exact B692015
  · exact B692019
  · exact B692023
  · exact B692027
  · exact B692031
  · exact B692035
  · exact B692039
  · exact B692043
  · exact B692047
  · exact B692051
  · exact B692055
  · exact B692059
  · exact B692063
  · exact B692067
  · exact B692071
  · exact B692075
  · exact B692079
  · exact B692083
  · exact B692087
  · exact B692091
  · exact B692095
  · exact B692099
  · exact B692103
  · exact B692107
  · exact B692111
  · exact B692115
  · exact B692119
  · exact B692123
  · exact B692127
  · exact B692131
  · exact B692135
  · exact B692139
  · exact B692143
  · exact B692147
  · exact B692151
  · exact B692155
  · exact B692159
  · exact B692163
  · exact B692167
  · exact B692171
  · exact B692175
  · exact B692179
  · exact B692183
  · exact B692187
  · exact B692191
  · exact B692195
  · exact B692199
  · exact B692203
  · exact B692207
  · exact B692211
  · exact B692215
  · exact B692219
  · exact B692223
  · exact B692227
  · exact B692231
  · exact B692235
  · exact B692239
  · exact B692243
  · exact B692247
  · exact B692251
  · exact B692255
  · exact B692259
  · exact B692263
  · exact B692267
  · exact B692271
  · exact B692275
  · exact B692279
  · exact B692283
  · exact B692287
  · exact B692291
  · exact B692295
  · exact B692299
  · exact B692303
  · exact B692307
  · exact B692311
  · exact B692315
  · exact B692319
  · exact B692323
  · exact B692327
  · exact B692331
  · exact B692335
  · exact B692339
  · exact B692343
  · exact B692347
  · exact B692351
  · exact B692355
  · exact B692359
  · exact B692363
  · exact B692367
  · exact B692371
  · exact B692375
  · exact B692379
  · exact B692383
  · exact B692387
  · exact B692391
  · exact B692395
  · exact B692399
  · exact B692403
  · exact B692407
  · exact B692411
  · exact B692415
  · exact B692419
  · exact B692423
  · exact B692427
  · exact B692431
  · exact B692435
  · exact B692439
  · exact B692443
  · exact B692447
  · exact B692451
  · exact B692455
  · exact B692459
  · exact B692463
  · exact B692467
  · exact B692471
  · exact B692475
  · exact B692479
  · exact B692483
  · exact B692487
  · exact B692491
  · exact B692495
  · exact B692499
  · exact B692503
  · exact B692507
  · exact B692511
  · exact B692515
  · exact B692519
  · exact B692523
  · exact B692527
  · exact B692531
  · exact B692535
  · exact B692539
  · exact B692543
  · exact B692547
  · exact B692551
  · exact B692555
  · exact B692559
  · exact B692563
  · exact B692567
  · exact B692571
  · exact B692575
  · exact B692579
  · exact B692583
  · exact B692587
  · exact B692591
  · exact B692595
  · exact B692599
  · exact B692603
  · exact B692607
  · exact B692611
  · exact B692615
  · exact B692619
  · exact B692623
  · exact B692627
  · exact B692631
  · exact B692635
  · exact B692639
  · exact B692643
  · exact B692647
  · exact B692651
  · exact B692655
  · exact B692659
  · exact B692663
  · exact B692667
  · exact B692671
  · exact B692675
  · exact B692679
  · exact B692683
  · exact B692687
  · exact B692691
  · exact B692695
  · exact B692699
  · exact B692703
  · exact B692707
  · exact B692711
  · exact B692715
  · exact B692719
  · exact B692723
  · exact B692727
  · exact B692731
  · exact B692735
  · exact B692739
  · exact B692743
  · exact B692747
  · exact B692751
  · exact B692755
  · exact B692759
  · exact B692763
  · exact B692767
  · exact B692771
  · exact B692775
  · exact B692779
  · exact B692783
  · exact B692787
  · exact B692791
  · exact B692795
  · exact B692799
  · exact B692803
  · exact B692807
  · exact B692811
  · exact B692815
  · exact B692819
  · exact B692823
  · exact B692827
  · exact B692831
  · exact B692835
  · exact B692839
  · exact B692843
  · exact B692847
  · exact B692851
  · exact B692855
  · exact B692859
  · exact B692863
  · exact B692867
  · exact B692871
  · exact B692875
  · exact B692879
  · exact B692883
  · exact B692887
  · exact B692891
  · exact B692895
  · exact B692899
  · exact B692903
  · exact B692907
  · exact B692911
  · exact B692915
  · exact B692919
  · exact B692923
  · exact B692927
  · exact B692931
  · exact B692935
  · exact B692939
  · exact B692943
  · exact B692947
  · exact B692951
  · exact B692955
  · exact B692959
  · exact B692963
  · exact B692967
  · exact B692971
  · exact B692975
  · exact B692979
  · exact B692983
  · exact B692987
  · exact B692991
  · exact B692995
  · exact B692999
  · exact B693003
  · exact B693007
  · exact B693011
  · exact B693015
  · exact B693019
  · exact B693023
  · exact B693027
  · exact B693031
  · exact B693035
  · exact B693039
  · exact B693043
  · exact B693047
  · exact B693051
  · exact B693055
  · exact B693059
  · exact B693063
  · exact B693067
  · exact B693071
  · exact B693075
  · exact B693079
  · exact B693083
  · exact B693087
  · exact B693091
  · exact B693095
  · exact B693099
  · exact B693103
  · exact B693107
  · exact B693111

theorem C1 (j : ℕ) (h1 : 173278 ≤ j) (h2 : j ≤ 173578) : Blo 690315 (4 * j + 3) := by
  interval_cases j
  · exact B693115
  · exact B693119
  · exact B693123
  · exact B693127
  · exact B693131
  · exact B693135
  · exact B693139
  · exact B693143
  · exact B693147
  · exact B693151
  · exact B693155
  · exact B693159
  · exact B693163
  · exact B693167
  · exact B693171
  · exact B693175
  · exact B693179
  · exact B693183
  · exact B693187
  · exact B693191
  · exact B693195
  · exact B693199
  · exact B693203
  · exact B693207
  · exact B693211
  · exact B693215
  · exact B693219
  · exact B693223
  · exact B693227
  · exact B693231
  · exact B693235
  · exact B693239
  · exact B693243
  · exact B693247
  · exact B693251
  · exact B693255
  · exact B693259
  · exact B693263
  · exact B693267
  · exact B693271
  · exact B693275
  · exact B693279
  · exact B693283
  · exact B693287
  · exact B693291
  · exact B693295
  · exact B693299
  · exact B693303
  · exact B693307
  · exact B693311
  · exact B693315
  · exact B693319
  · exact B693323
  · exact B693327
  · exact B693331
  · exact B693335
  · exact B693339
  · exact B693343
  · exact B693347
  · exact B693351
  · exact B693355
  · exact B693359
  · exact B693363
  · exact B693367
  · exact B693371
  · exact B693375
  · exact B693379
  · exact B693383
  · exact B693387
  · exact B693391
  · exact B693395
  · exact B693399
  · exact B693403
  · exact B693407
  · exact B693411
  · exact B693415
  · exact B693419
  · exact B693423
  · exact B693427
  · exact B693431
  · exact B693435
  · exact B693439
  · exact B693443
  · exact B693447
  · exact B693451
  · exact B693455
  · exact B693459
  · exact B693463
  · exact B693467
  · exact B693471
  · exact B693475
  · exact B693479
  · exact B693483
  · exact B693487
  · exact B693491
  · exact B693495
  · exact B693499
  · exact B693503
  · exact B693507
  · exact B693511
  · exact B693515
  · exact B693519
  · exact B693523
  · exact B693527
  · exact B693531
  · exact B693535
  · exact B693539
  · exact B693543
  · exact B693547
  · exact B693551
  · exact B693555
  · exact B693559
  · exact B693563
  · exact B693567
  · exact B693571
  · exact B693575
  · exact B693579
  · exact B693583
  · exact B693587
  · exact B693591
  · exact B693595
  · exact B693599
  · exact B693603
  · exact B693607
  · exact B693611
  · exact B693615
  · exact B693619
  · exact B693623
  · exact B693627
  · exact B693631
  · exact B693635
  · exact B693639
  · exact B693643
  · exact B693647
  · exact B693651
  · exact B693655
  · exact B693659
  · exact B693663
  · exact B693667
  · exact B693671
  · exact B693675
  · exact B693679
  · exact B693683
  · exact B693687
  · exact B693691
  · exact B693695
  · exact B693699
  · exact B693703
  · exact B693707
  · exact B693711
  · exact B693715
  · exact B693719
  · exact B693723
  · exact B693727
  · exact B693731
  · exact B693735
  · exact B693739
  · exact B693743
  · exact B693747
  · exact B693751
  · exact B693755
  · exact B693759
  · exact B693763
  · exact B693767
  · exact B693771
  · exact B693775
  · exact B693779
  · exact B693783
  · exact B693787
  · exact B693791
  · exact B693795
  · exact B693799
  · exact B693803
  · exact B693807
  · exact B693811
  · exact B693815
  · exact B693819
  · exact B693823
  · exact B693827
  · exact B693831
  · exact B693835
  · exact B693839
  · exact B693843
  · exact B693847
  · exact B693851
  · exact B693855
  · exact B693859
  · exact B693863
  · exact B693867
  · exact B693871
  · exact B693875
  · exact B693879
  · exact B693883
  · exact B693887
  · exact B693891
  · exact B693895
  · exact B693899
  · exact B693903
  · exact B693907
  · exact B693911
  · exact B693915
  · exact B693919
  · exact B693923
  · exact B693927
  · exact B693931
  · exact B693935
  · exact B693939
  · exact B693943
  · exact B693947
  · exact B693951
  · exact B693955
  · exact B693959
  · exact B693963
  · exact B693967
  · exact B693971
  · exact B693975
  · exact B693979
  · exact B693983
  · exact B693987
  · exact B693991
  · exact B693995
  · exact B693999
  · exact B694003
  · exact B694007
  · exact B694011
  · exact B694015
  · exact B694019
  · exact B694023
  · exact B694027
  · exact B694031
  · exact B694035
  · exact B694039
  · exact B694043
  · exact B694047
  · exact B694051
  · exact B694055
  · exact B694059
  · exact B694063
  · exact B694067
  · exact B694071
  · exact B694075
  · exact B694079
  · exact B694083
  · exact B694087
  · exact B694091
  · exact B694095
  · exact B694099
  · exact B694103
  · exact B694107
  · exact B694111
  · exact B694115
  · exact B694119
  · exact B694123
  · exact B694127
  · exact B694131
  · exact B694135
  · exact B694139
  · exact B694143
  · exact B694147
  · exact B694151
  · exact B694155
  · exact B694159
  · exact B694163
  · exact B694167
  · exact B694171
  · exact B694175
  · exact B694179
  · exact B694183
  · exact B694187
  · exact B694191
  · exact B694195
  · exact B694199
  · exact B694203
  · exact B694207
  · exact B694211
  · exact B694215
  · exact B694219
  · exact B694223
  · exact B694227
  · exact B694231
  · exact B694235
  · exact B694239
  · exact B694243
  · exact B694247
  · exact B694251
  · exact B694255
  · exact B694259
  · exact B694263
  · exact B694267
  · exact B694271
  · exact B694275
  · exact B694279
  · exact B694283
  · exact B694287
  · exact B694291
  · exact B694295
  · exact B694299
  · exact B694303
  · exact B694307
  · exact B694311
  · exact B694315

theorem solution (m : ℕ) (hlo : 690315 ≤ m) (hhi : m ≤ 694315) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 172578 ≤ j := by omega
    have hj2 : j ≤ 173578 := by omega
    have hb : Blo 690315 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 173278 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
