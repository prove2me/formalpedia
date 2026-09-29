-- Prove2me | solution 1 for syracuse_descends_range_1437538_1439538
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:42:30.314481+00:00
-- url     : https://prove2.me/submissions/88a595a6-5c4f-416e-b370-286b72358c1c

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


theorem B7282709 : Blo 1437538 7282709 := bbase (se 6 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 7282709 = 341377) (by norm_num)
theorem B3235877 : Blo 1437538 3235877 := bbase (se 4 (by rfl) ⟨303363, by rfl⟩ : syracuseStep 3235877 = 606727) (by norm_num)
theorem B4857893 : Blo 1437538 4857893 := bbase (se 4 (by rfl) ⟨455427, by rfl⟩ : syracuseStep 4857893 = 910855) (by norm_num)
theorem B3235949 : Blo 1437538 3235949 := bbase (se 3 (by rfl) ⟨606740, by rfl⟩ : syracuseStep 3235949 = 1213481) (by norm_num)
theorem B3236021 : Blo 1437538 3236021 := bbase (se 5 (by rfl) ⟨151688, by rfl⟩ : syracuseStep 3236021 = 303377) (by norm_num)
theorem B3072181 : Blo 1437538 3072181 := bbase (se 5 (by rfl) ⟨144008, by rfl⟩ : syracuseStep 3072181 = 288017) (by norm_num)
theorem B1728721 : Blo 1437538 1728721 := bbase (se 2 (by rfl) ⟨648270, by rfl⟩ : syracuseStep 1728721 = 1296541) (by norm_num)
theorem B3236093 : Blo 1437538 3236093 := bbase (se 3 (by rfl) ⟨606767, by rfl⟩ : syracuseStep 3236093 = 1213535) (by norm_num)
theorem B2048285 : Blo 1437538 2048285 := bbase (se 3 (by rfl) ⟨384053, by rfl⟩ : syracuseStep 2048285 = 768107) (by norm_num)
theorem B3236165 : Blo 1437538 3236165 := bbase (se 4 (by rfl) ⟨303390, by rfl⟩ : syracuseStep 3236165 = 606781) (by norm_num)
theorem B3072325 : Blo 1437538 3072325 := bbase (se 4 (by rfl) ⟨288030, by rfl⟩ : syracuseStep 3072325 = 576061) (by norm_num)
theorem B2048365 : Blo 1437538 2048365 := bbase (se 3 (by rfl) ⟨384068, by rfl⟩ : syracuseStep 2048365 = 768137) (by norm_num)
theorem B3236237 : Blo 1437538 3236237 := bbase (se 3 (by rfl) ⟨606794, by rfl⟩ : syracuseStep 3236237 = 1213589) (by norm_num)
theorem B1458577 : Blo 1437538 1458577 := bbase (se 2 (by rfl) ⟨546966, by rfl⟩ : syracuseStep 1458577 = 1093933) (by norm_num)
theorem B13304213 : Blo 1437538 13304213 := bbase (se 6 (by rfl) ⟨311817, by rfl⟩ : syracuseStep 13304213 = 623635) (by norm_num)
theorem B3236309 : Blo 1437538 3236309 := bbase (se 7 (by rfl) ⟨37925, by rfl⟩ : syracuseStep 3236309 = 75851) (by norm_num)
theorem B4858325 : Blo 1437538 4858325 := bbase (se 7 (by rfl) ⟨56933, by rfl⟩ : syracuseStep 4858325 = 113867) (by norm_num)
theorem B2048485 : Blo 1437538 2048485 := bbase (se 4 (by rfl) ⟨192045, by rfl⟩ : syracuseStep 2048485 = 384091) (by norm_num)
theorem B3236381 : Blo 1437538 3236381 := bbase (se 3 (by rfl) ⟨606821, by rfl⟩ : syracuseStep 3236381 = 1213643) (by norm_num)
theorem B2048581 : Blo 1437538 2048581 := bbase (se 4 (by rfl) ⟨192054, by rfl⟩ : syracuseStep 2048581 = 384109) (by norm_num)
theorem B3236453 : Blo 1437538 3236453 := bbase (se 4 (by rfl) ⟨303417, by rfl⟩ : syracuseStep 3236453 = 606835) (by norm_num)
theorem B3236525 : Blo 1437538 3236525 := bbase (se 3 (by rfl) ⟨606848, by rfl⟩ : syracuseStep 3236525 = 1213697) (by norm_num)
theorem B3072701 : Blo 1437538 3072701 := bbase (se 3 (by rfl) ⟨576131, by rfl⟩ : syracuseStep 3072701 = 1152263) (by norm_num)
theorem B5767877 : Blo 1437538 5767877 := bbase (se 4 (by rfl) ⟨540738, by rfl⟩ : syracuseStep 5767877 = 1081477) (by norm_num)
theorem B1458901 : Blo 1437538 1458901 := bbase (se 7 (by rfl) ⟨17096, by rfl⟩ : syracuseStep 1458901 = 34193) (by norm_num)
theorem B3236597 : Blo 1437538 3236597 := bbase (se 5 (by rfl) ⟨151715, by rfl⟩ : syracuseStep 3236597 = 303431) (by norm_num)
theorem B1819417 : Blo 1437538 1819417 := bbase (se 2 (by rfl) ⟨682281, by rfl⟩ : syracuseStep 1819417 = 1364563) (by norm_num)
theorem B3236669 : Blo 1437538 3236669 := bbase (se 3 (by rfl) ⟨606875, by rfl⟩ : syracuseStep 3236669 = 1213751) (by norm_num)
theorem B2188109 : Blo 1437538 2188109 := bbase (se 3 (by rfl) ⟨410270, by rfl⟩ : syracuseStep 2188109 = 820541) (by norm_num)
theorem B7775093 : Blo 1437538 7775093 := bbase (se 5 (by rfl) ⟨364457, by rfl⟩ : syracuseStep 7775093 = 728915) (by norm_num)
theorem B1819513 : Blo 1437538 1819513 := bbase (se 2 (by rfl) ⟨682317, by rfl⟩ : syracuseStep 1819513 = 1364635) (by norm_num)
theorem B3236741 : Blo 1437538 3236741 := bbase (se 4 (by rfl) ⟨303444, by rfl⟩ : syracuseStep 3236741 = 606889) (by norm_num)
theorem B3457981 : Blo 1437538 3457981 := bbase (se 3 (by rfl) ⟨648371, by rfl⟩ : syracuseStep 3457981 = 1296743) (by norm_num)
theorem B3236813 : Blo 1437538 3236813 := bbase (se 3 (by rfl) ⟨606902, by rfl⟩ : syracuseStep 3236813 = 1213805) (by norm_num)
theorem B1557469 : Blo 1437538 1557469 := bbase (se 3 (by rfl) ⟨292025, by rfl⟩ : syracuseStep 1557469 = 584051) (by norm_num)
theorem B3236885 : Blo 1437538 3236885 := bbase (se 6 (by rfl) ⟨75864, by rfl⟩ : syracuseStep 3236885 = 151729) (by norm_num)
theorem B1819685 : Blo 1437538 1819685 := bbase (se 4 (by rfl) ⟨170595, by rfl⟩ : syracuseStep 1819685 = 341191) (by norm_num)
theorem B3073069 : Blo 1437538 3073069 := bbase (se 3 (by rfl) ⟨576200, by rfl⟩ : syracuseStep 3073069 = 1152401) (by norm_num)
theorem B2425909 : Blo 1437538 2425909 := bbase (se 5 (by rfl) ⟨113714, by rfl⟩ : syracuseStep 2425909 = 227429) (by norm_num)
theorem B2049077 : Blo 1437538 2049077 := bbase (se 5 (by rfl) ⟨96050, by rfl⟩ : syracuseStep 2049077 = 192101) (by norm_num)
theorem B1819741 : Blo 1437538 1819741 := bbase (se 3 (by rfl) ⟨341201, by rfl⟩ : syracuseStep 1819741 = 682403) (by norm_num)
theorem B3236957 : Blo 1437538 3236957 := bbase (se 3 (by rfl) ⟨606929, by rfl⟩ : syracuseStep 3236957 = 1213859) (by norm_num)
theorem B2425997 : Blo 1437538 2425997 := bbase (se 3 (by rfl) ⟨454874, by rfl⟩ : syracuseStep 2425997 = 909749) (by norm_num)
theorem B12297365 : Blo 1437538 12297365 := bbase (se 6 (by rfl) ⟨288219, by rfl⟩ : syracuseStep 12297365 = 576439) (by norm_num)
theorem B3237029 : Blo 1437538 3237029 := bbase (se 4 (by rfl) ⟨303471, by rfl⟩ : syracuseStep 3237029 = 606943) (by norm_num)
theorem B1819837 : Blo 1437538 1819837 := bbase (se 3 (by rfl) ⟨341219, by rfl⟩ : syracuseStep 1819837 = 682439) (by norm_num)
theorem B4670693 : Blo 1437538 4670693 := bbase (se 4 (by rfl) ⟨437877, by rfl⟩ : syracuseStep 4670693 = 875755) (by norm_num)
theorem B3237101 : Blo 1437538 3237101 := bbase (se 3 (by rfl) ⟨606956, by rfl⟩ : syracuseStep 3237101 = 1213913) (by norm_num)
theorem B1844473 : Blo 1437538 1844473 := bbase (se 2 (by rfl) ⟨691677, by rfl⟩ : syracuseStep 1844473 = 1383355) (by norm_num)
theorem B2426125 : Blo 1437538 2426125 := bbase (se 3 (by rfl) ⟨454898, by rfl⟩ : syracuseStep 2426125 = 909797) (by norm_num)
theorem B2303245 : Blo 1437538 2303245 := bbase (se 3 (by rfl) ⟨431858, by rfl⟩ : syracuseStep 2303245 = 863717) (by norm_num)
theorem B7284005 : Blo 1437538 7284005 := bbase (se 4 (by rfl) ⟨682875, by rfl⟩ : syracuseStep 7284005 = 1365751) (by norm_num)
theorem B3237173 : Blo 1437538 3237173 := bbase (se 5 (by rfl) ⟨151742, by rfl⟩ : syracuseStep 3237173 = 303485) (by norm_num)
theorem B2729285 : Blo 1437538 2729285 := bbase (se 4 (by rfl) ⟨255870, by rfl⟩ : syracuseStep 2729285 = 511741) (by norm_num)
theorem B2426213 : Blo 1437538 2426213 := bbase (se 4 (by rfl) ⟨227457, by rfl⟩ : syracuseStep 2426213 = 454915) (by norm_num)
theorem B1820009 : Blo 1437538 1820009 := bbase (se 2 (by rfl) ⟨682503, by rfl⟩ : syracuseStep 1820009 = 1365007) (by norm_num)
theorem B3237245 : Blo 1437538 3237245 := bbase (se 3 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 3237245 = 1213967) (by norm_num)
theorem B1820065 : Blo 1437538 1820065 := bbase (se 2 (by rfl) ⟨682524, by rfl⟩ : syracuseStep 1820065 = 1365049) (by norm_num)
theorem B3237317 : Blo 1437538 3237317 := bbase (se 4 (by rfl) ⟨303498, by rfl⟩ : syracuseStep 3237317 = 606997) (by norm_num)
theorem B18433493 : Blo 1437538 18433493 := bbase (se 7 (by rfl) ⟨216017, by rfl⟩ : syracuseStep 18433493 = 432035) (by norm_num)
theorem B2426341 : Blo 1437538 2426341 := bbase (se 4 (by rfl) ⟨227469, by rfl⟩ : syracuseStep 2426341 = 454939) (by norm_num)
theorem B10929653 : Blo 1437538 10929653 := bbase (se 5 (by rfl) ⟨512327, by rfl⟩ : syracuseStep 10929653 = 1024655) (by norm_num)
theorem B1820161 : Blo 1437538 1820161 := bbase (se 2 (by rfl) ⟨682560, by rfl⟩ : syracuseStep 1820161 = 1365121) (by norm_num)
theorem B3237389 : Blo 1437538 3237389 := bbase (se 3 (by rfl) ⟨607010, by rfl⟩ : syracuseStep 3237389 = 1214021) (by norm_num)
theorem B4097573 : Blo 1437538 4097573 := bbase (se 4 (by rfl) ⟨384147, by rfl⟩ : syracuseStep 4097573 = 768295) (by norm_num)
theorem B2426429 : Blo 1437538 2426429 := bbase (se 3 (by rfl) ⟨454955, by rfl⟩ : syracuseStep 2426429 = 909911) (by norm_num)
theorem B3237461 : Blo 1437538 3237461 := bbase (se 8 (by rfl) ⟨18969, by rfl⟩ : syracuseStep 3237461 = 37939) (by norm_num)
theorem B2049629 : Blo 1437538 2049629 := bbase (se 3 (by rfl) ⟨384305, by rfl⟩ : syracuseStep 2049629 = 768611) (by norm_num)
theorem B3237533 : Blo 1437538 3237533 := bbase (se 3 (by rfl) ⟨607037, by rfl⟩ : syracuseStep 3237533 = 1214075) (by norm_num)
theorem B1820333 : Blo 1437538 1820333 := bbase (se 3 (by rfl) ⟨341312, by rfl⟩ : syracuseStep 1820333 = 682625) (by norm_num)
theorem B3638965 : Blo 1437538 3638965 := bbase (se 5 (by rfl) ⟨170576, by rfl⟩ : syracuseStep 3638965 = 341153) (by norm_num)
theorem B2426557 : Blo 1437538 2426557 := bbase (se 3 (by rfl) ⟨454979, by rfl⟩ : syracuseStep 2426557 = 909959) (by norm_num)
theorem B1820389 : Blo 1437538 1820389 := bbase (se 4 (by rfl) ⟨170661, by rfl⟩ : syracuseStep 1820389 = 341323) (by norm_num)
theorem B3237605 : Blo 1437538 3237605 := bbase (se 4 (by rfl) ⟨303525, by rfl⟩ : syracuseStep 3237605 = 607051) (by norm_num)
theorem B1943309 : Blo 1437538 1943309 := bbase (se 3 (by rfl) ⟨364370, by rfl⟩ : syracuseStep 1943309 = 728741) (by norm_num)
theorem B2156309 : Blo 1437538 2156309 := bbase (se 6 (by rfl) ⟨50538, by rfl⟩ : syracuseStep 2156309 = 101077) (by norm_num)
theorem B2426645 : Blo 1437538 2426645 := bbase (se 6 (by rfl) ⟨56874, by rfl⟩ : syracuseStep 2426645 = 113749) (by norm_num)
theorem B3639077 : Blo 1437538 3639077 := bbase (se 4 (by rfl) ⟨341163, by rfl⟩ : syracuseStep 3639077 = 682327) (by norm_num)
theorem B2156333 : Blo 1437538 2156333 := bbase (se 3 (by rfl) ⟨404312, by rfl⟩ : syracuseStep 2156333 = 808625) (by norm_num)
theorem B3237677 : Blo 1437538 3237677 := bbase (se 3 (by rfl) ⟨607064, by rfl⟩ : syracuseStep 3237677 = 1214129) (by norm_num)
theorem B2590517 : Blo 1437538 2590517 := bbase (se 5 (by rfl) ⟨121430, by rfl⟩ : syracuseStep 2590517 = 242861) (by norm_num)
theorem B5834549 : Blo 1437538 5834549 := bbase (se 5 (by rfl) ⟨273494, by rfl⟩ : syracuseStep 5834549 = 546989) (by norm_num)
theorem B2156357 : Blo 1437538 2156357 := bbase (se 4 (by rfl) ⟨202158, by rfl⟩ : syracuseStep 2156357 = 404317) (by norm_num)
theorem B1820485 : Blo 1437538 1820485 := bbase (se 4 (by rfl) ⟨170670, by rfl⟩ : syracuseStep 1820485 = 341341) (by norm_num)
theorem B2156381 : Blo 1437538 2156381 := bbase (se 3 (by rfl) ⟨404321, by rfl⟩ : syracuseStep 2156381 = 808643) (by norm_num)
theorem B1845109 : Blo 1437538 1845109 := bbase (se 5 (by rfl) ⟨86489, by rfl⟩ : syracuseStep 1845109 = 172979) (by norm_num)
theorem B2156405 : Blo 1437538 2156405 := bbase (se 5 (by rfl) ⟨101081, by rfl⟩ : syracuseStep 2156405 = 202163) (by norm_num)
theorem B3237749 : Blo 1437538 3237749 := bbase (se 5 (by rfl) ⟨151769, by rfl⟩ : syracuseStep 3237749 = 303539) (by norm_num)
theorem B2156429 : Blo 1437538 2156429 := bbase (se 3 (by rfl) ⟨404330, by rfl⟩ : syracuseStep 2156429 = 808661) (by norm_num)
theorem B2426773 : Blo 1437538 2426773 := bbase (se 6 (by rfl) ⟨56877, by rfl⟩ : syracuseStep 2426773 = 113755) (by norm_num)
theorem B10921877 : Blo 1437538 10921877 := bbase (se 6 (by rfl) ⟨255981, by rfl⟩ : syracuseStep 10921877 = 511963) (by norm_num)
theorem B2156453 : Blo 1437538 2156453 := bbase (se 4 (by rfl) ⟨202167, by rfl⟩ : syracuseStep 2156453 = 404335) (by norm_num)
theorem B2156477 : Blo 1437538 2156477 := bbase (se 3 (by rfl) ⟨404339, by rfl⟩ : syracuseStep 2156477 = 808679) (by norm_num)
theorem B3237821 : Blo 1437538 3237821 := bbase (se 3 (by rfl) ⟨607091, by rfl⟩ : syracuseStep 3237821 = 1214183) (by norm_num)
theorem B2156501 : Blo 1437538 2156501 := bbase (se 7 (by rfl) ⟨25271, by rfl⟩ : syracuseStep 2156501 = 50543) (by norm_num)
theorem B4605925 : Blo 1437538 4605925 := bbase (se 4 (by rfl) ⟨431805, by rfl⟩ : syracuseStep 4605925 = 863611) (by norm_num)
theorem B3639269 : Blo 1437538 3639269 := bbase (se 4 (by rfl) ⟨341181, by rfl⟩ : syracuseStep 3639269 = 682363) (by norm_num)
theorem B2156525 : Blo 1437538 2156525 := bbase (se 3 (by rfl) ⟨404348, by rfl⟩ : syracuseStep 2156525 = 808697) (by norm_num)
theorem B2426861 : Blo 1437538 2426861 := bbase (se 3 (by rfl) ⟨455036, by rfl⟩ : syracuseStep 2426861 = 910073) (by norm_num)
theorem B1820657 : Blo 1437538 1820657 := bbase (se 2 (by rfl) ⟨682746, by rfl⟩ : syracuseStep 1820657 = 1365493) (by norm_num)
theorem B2156549 : Blo 1437538 2156549 := bbase (se 4 (by rfl) ⟨202176, by rfl⟩ : syracuseStep 2156549 = 404353) (by norm_num)
theorem B3237893 : Blo 1437538 3237893 := bbase (se 4 (by rfl) ⟨303552, by rfl⟩ : syracuseStep 3237893 = 607105) (by norm_num)
theorem B2156573 : Blo 1437538 2156573 := bbase (se 3 (by rfl) ⟨404357, by rfl⟩ : syracuseStep 2156573 = 808715) (by norm_num)
theorem B1820713 : Blo 1437538 1820713 := bbase (se 2 (by rfl) ⟨682767, by rfl⟩ : syracuseStep 1820713 = 1365535) (by norm_num)
theorem B1640497 : Blo 1437538 1640497 := bbase (se 2 (by rfl) ⟨615186, by rfl⟩ : syracuseStep 1640497 = 1230373) (by norm_num)
theorem B2156597 : Blo 1437538 2156597 := bbase (se 5 (by rfl) ⟨101090, by rfl⟩ : syracuseStep 2156597 = 202181) (by norm_num)
theorem B2730037 : Blo 1437538 2730037 := bbase (se 5 (by rfl) ⟨127970, by rfl⟩ : syracuseStep 2730037 = 255941) (by norm_num)
theorem B2156621 : Blo 1437538 2156621 := bbase (se 3 (by rfl) ⟨404366, by rfl⟩ : syracuseStep 2156621 = 808733) (by norm_num)
theorem B3237965 : Blo 1437538 3237965 := bbase (se 3 (by rfl) ⟨607118, by rfl⟩ : syracuseStep 3237965 = 1214237) (by norm_num)
theorem B2156645 : Blo 1437538 2156645 := bbase (se 4 (by rfl) ⟨202185, by rfl⟩ : syracuseStep 2156645 = 404371) (by norm_num)
theorem B2426989 : Blo 1437538 2426989 := bbase (se 3 (by rfl) ⟨455060, by rfl⟩ : syracuseStep 2426989 = 910121) (by norm_num)
theorem B4376693 : Blo 1437538 4376693 := bbase (se 5 (by rfl) ⟨205157, by rfl⟩ : syracuseStep 4376693 = 410315) (by norm_num)
theorem B2156669 : Blo 1437538 2156669 := bbase (se 3 (by rfl) ⟨404375, by rfl⟩ : syracuseStep 2156669 = 808751) (by norm_num)
theorem B4851845 : Blo 1437538 4851845 := bbase (se 4 (by rfl) ⟨454860, by rfl⟩ : syracuseStep 4851845 = 909721) (by norm_num)
theorem B1820809 : Blo 1437538 1820809 := bbase (se 2 (by rfl) ⟨682803, by rfl⟩ : syracuseStep 1820809 = 1365607) (by norm_num)
theorem B2156693 : Blo 1437538 2156693 := bbase (se 6 (by rfl) ⟨50547, by rfl⟩ : syracuseStep 2156693 = 101095) (by norm_num)
theorem B3238037 : Blo 1437538 3238037 := bbase (se 6 (by rfl) ⟨75891, by rfl⟩ : syracuseStep 3238037 = 151783) (by norm_num)
theorem B2156717 : Blo 1437538 2156717 := bbase (se 3 (by rfl) ⟨404384, by rfl⟩ : syracuseStep 2156717 = 808769) (by norm_num)
theorem B2156741 : Blo 1437538 2156741 := bbase (se 4 (by rfl) ⟨202194, by rfl⟩ : syracuseStep 2156741 = 404389) (by norm_num)
theorem B2730181 : Blo 1437538 2730181 := bbase (se 4 (by rfl) ⟨255954, by rfl⟩ : syracuseStep 2730181 = 511909) (by norm_num)
theorem B2427077 : Blo 1437538 2427077 := bbase (se 4 (by rfl) ⟨227538, by rfl⟩ : syracuseStep 2427077 = 455077) (by norm_num)
theorem B44902613 : Blo 1437538 44902613 := bbase (se 7 (by rfl) ⟨526202, by rfl⟩ : syracuseStep 44902613 = 1052405) (by norm_num)
theorem B2156765 : Blo 1437538 2156765 := bbase (se 3 (by rfl) ⟨404393, by rfl⟩ : syracuseStep 2156765 = 808787) (by norm_num)
theorem B3238109 : Blo 1437538 3238109 := bbase (se 3 (by rfl) ⟨607145, by rfl⟩ : syracuseStep 3238109 = 1214291) (by norm_num)
theorem B6310133 : Blo 1437538 6310133 := bbase (se 5 (by rfl) ⟨295787, by rfl⟩ : syracuseStep 6310133 = 591575) (by norm_num)
theorem B2156789 : Blo 1437538 2156789 := bbase (se 5 (by rfl) ⟨101099, by rfl⟩ : syracuseStep 2156789 = 202199) (by norm_num)
theorem B2156813 : Blo 1437538 2156813 := bbase (se 3 (by rfl) ⟨404402, by rfl⟩ : syracuseStep 2156813 = 808805) (by norm_num)
theorem B2156837 : Blo 1437538 2156837 := bbase (se 4 (by rfl) ⟨202203, by rfl⟩ : syracuseStep 2156837 = 404407) (by norm_num)
theorem B3238181 : Blo 1437538 3238181 := bbase (se 4 (by rfl) ⟨303579, by rfl⟩ : syracuseStep 3238181 = 607159) (by norm_num)
theorem B1640749 : Blo 1437538 1640749 := bbase (se 3 (by rfl) ⟨307640, by rfl⟩ : syracuseStep 1640749 = 615281) (by norm_num)
theorem B1820981 : Blo 1437538 1820981 := bbase (se 5 (by rfl) ⟨85358, by rfl⟩ : syracuseStep 1820981 = 170717) (by norm_num)
theorem B3639613 : Blo 1437538 3639613 := bbase (se 3 (by rfl) ⟨682427, by rfl⟩ : syracuseStep 3639613 = 1364855) (by norm_num)
theorem B2156861 : Blo 1437538 2156861 := bbase (se 3 (by rfl) ⟨404411, by rfl⟩ : syracuseStep 2156861 = 808823) (by norm_num)
theorem B2427205 : Blo 1437538 2427205 := bbase (se 4 (by rfl) ⟨227550, by rfl⟩ : syracuseStep 2427205 = 455101) (by norm_num)
theorem B2156885 : Blo 1437538 2156885 := bbase (se 10 (by rfl) ⟨3159, by rfl⟩ : syracuseStep 2156885 = 6319) (by norm_num)
theorem B2730341 : Blo 1437538 2730341 := bbase (se 4 (by rfl) ⟨255969, by rfl⟩ : syracuseStep 2730341 = 511939) (by norm_num)
theorem B2156909 : Blo 1437538 2156909 := bbase (se 3 (by rfl) ⟨404420, by rfl⟩ : syracuseStep 2156909 = 808841) (by norm_num)
theorem B1821037 : Blo 1437538 1821037 := bbase (se 3 (by rfl) ⟨341444, by rfl⟩ : syracuseStep 1821037 = 682889) (by norm_num)
theorem B3238253 : Blo 1437538 3238253 := bbase (se 3 (by rfl) ⟨607172, by rfl⟩ : syracuseStep 3238253 = 1214345) (by norm_num)
theorem B2156933 : Blo 1437538 2156933 := bbase (se 4 (by rfl) ⟨202212, by rfl⟩ : syracuseStep 2156933 = 404425) (by norm_num)
theorem B8751509 : Blo 1437538 8751509 := bbase (se 6 (by rfl) ⟨205113, by rfl⟩ : syracuseStep 8751509 = 410227) (by norm_num)
theorem B2156957 : Blo 1437538 2156957 := bbase (se 3 (by rfl) ⟨404429, by rfl⟩ : syracuseStep 2156957 = 808859) (by norm_num)
theorem B2427293 : Blo 1437538 2427293 := bbase (se 3 (by rfl) ⟨455117, by rfl⟩ : syracuseStep 2427293 = 910235) (by norm_num)
theorem B3639725 : Blo 1437538 3639725 := bbase (se 3 (by rfl) ⟨682448, by rfl⟩ : syracuseStep 3639725 = 1364897) (by norm_num)
theorem B2156981 : Blo 1437538 2156981 := bbase (se 5 (by rfl) ⟨101108, by rfl⟩ : syracuseStep 2156981 = 202217) (by norm_num)
theorem B3238325 : Blo 1437538 3238325 := bbase (se 5 (by rfl) ⟨151796, by rfl⟩ : syracuseStep 3238325 = 303593) (by norm_num)
theorem B5458373 : Blo 1437538 5458373 := bbase (se 4 (by rfl) ⟨511722, by rfl⟩ : syracuseStep 5458373 = 1023445) (by norm_num)
theorem B2157005 : Blo 1437538 2157005 := bbase (se 3 (by rfl) ⟨404438, by rfl⟩ : syracuseStep 2157005 = 808877) (by norm_num)
theorem B1821133 : Blo 1437538 1821133 := bbase (se 3 (by rfl) ⟨341462, by rfl⟩ : syracuseStep 1821133 = 682925) (by norm_num)
theorem B2157029 : Blo 1437538 2157029 := bbase (se 4 (by rfl) ⟨202221, by rfl⟩ : syracuseStep 2157029 = 404443) (by norm_num)
theorem B2730485 : Blo 1437538 2730485 := bbase (se 5 (by rfl) ⟨127991, by rfl⟩ : syracuseStep 2730485 = 255983) (by norm_num)
theorem B6146549 : Blo 1437538 6146549 := bbase (se 5 (by rfl) ⟨288119, by rfl⟩ : syracuseStep 6146549 = 576239) (by norm_num)
theorem B2157053 : Blo 1437538 2157053 := bbase (se 3 (by rfl) ⟨404447, by rfl⟩ : syracuseStep 2157053 = 808895) (by norm_num)
theorem B3238397 : Blo 1437538 3238397 := bbase (se 3 (by rfl) ⟨607199, by rfl⟩ : syracuseStep 3238397 = 1214399) (by norm_num)
theorem B2591237 : Blo 1437538 2591237 := bbase (se 4 (by rfl) ⟨242928, by rfl⟩ : syracuseStep 2591237 = 485857) (by norm_num)
theorem B2157077 : Blo 1437538 2157077 := bbase (se 6 (by rfl) ⟨50556, by rfl⟩ : syracuseStep 2157077 = 101113) (by norm_num)
theorem B2427421 : Blo 1437538 2427421 := bbase (se 3 (by rfl) ⟨455141, by rfl⟩ : syracuseStep 2427421 = 910283) (by norm_num)
theorem B2157101 : Blo 1437538 2157101 := bbase (se 3 (by rfl) ⟨404456, by rfl⟩ : syracuseStep 2157101 = 808913) (by norm_num)
theorem B4852277 : Blo 1437538 4852277 := bbase (se 5 (by rfl) ⟨227450, by rfl⟩ : syracuseStep 4852277 = 454901) (by norm_num)
theorem B7285301 : Blo 1437538 7285301 := bbase (se 5 (by rfl) ⟨341498, by rfl⟩ : syracuseStep 7285301 = 682997) (by norm_num)
theorem B2157125 : Blo 1437538 2157125 := bbase (se 4 (by rfl) ⟨202230, by rfl⟩ : syracuseStep 2157125 = 404461) (by norm_num)
theorem B3238469 : Blo 1437538 3238469 := bbase (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) (by norm_num)
theorem B2157149 : Blo 1437538 2157149 := bbase (se 3 (by rfl) ⟨404465, by rfl⟩ : syracuseStep 2157149 = 808931) (by norm_num)
theorem B3639917 : Blo 1437538 3639917 := bbase (se 3 (by rfl) ⟨682484, by rfl⟩ : syracuseStep 3639917 = 1364969) (by norm_num)
theorem B2157173 : Blo 1437538 2157173 := bbase (se 5 (by rfl) ⟨101117, by rfl⟩ : syracuseStep 2157173 = 202235) (by norm_num)
theorem B2427509 : Blo 1437538 2427509 := bbase (se 5 (by rfl) ⟨113789, by rfl⟩ : syracuseStep 2427509 = 227579) (by norm_num)
theorem B2304629 : Blo 1437538 2304629 := bbase (se 5 (by rfl) ⟨108029, by rfl⟩ : syracuseStep 2304629 = 216059) (by norm_num)
theorem B1821305 : Blo 1437538 1821305 := bbase (se 2 (by rfl) ⟨682989, by rfl⟩ : syracuseStep 1821305 = 1365979) (by norm_num)
theorem B6564469 : Blo 1437538 6564469 := bbase (se 5 (by rfl) ⟨307709, by rfl⟩ : syracuseStep 6564469 = 615419) (by norm_num)
theorem B2157197 : Blo 1437538 2157197 := bbase (se 3 (by rfl) ⟨404474, by rfl⟩ : syracuseStep 2157197 = 808949) (by norm_num)
theorem B3238541 : Blo 1437538 3238541 := bbase (se 3 (by rfl) ⟨607226, by rfl⟩ : syracuseStep 3238541 = 1214453) (by norm_num)
theorem B2157221 : Blo 1437538 2157221 := bbase (se 4 (by rfl) ⟨202239, by rfl⟩ : syracuseStep 2157221 = 404479) (by norm_num)
theorem B1845929 : Blo 1437538 1845929 := bbase (se 2 (by rfl) ⟨692223, by rfl⟩ : syracuseStep 1845929 = 1384447) (by norm_num)
theorem B1821361 : Blo 1437538 1821361 := bbase (se 2 (by rfl) ⟨683010, by rfl⟩ : syracuseStep 1821361 = 1366021) (by norm_num)
theorem B2157245 : Blo 1437538 2157245 := bbase (se 3 (by rfl) ⟨404483, by rfl⟩ : syracuseStep 2157245 = 808967) (by norm_num)
theorem B4098757 : Blo 1437538 4098757 := bbase (se 4 (by rfl) ⟨384258, by rfl⟩ : syracuseStep 4098757 = 768517) (by norm_num)
theorem B2157269 : Blo 1437538 2157269 := bbase (se 7 (by rfl) ⟨25280, by rfl⟩ : syracuseStep 2157269 = 50561) (by norm_num)
theorem B15551189 : Blo 1437538 15551189 := bbase (se 7 (by rfl) ⟨182240, by rfl⟩ : syracuseStep 15551189 = 364481) (by norm_num)
theorem B3238613 : Blo 1437538 3238613 := bbase (se 7 (by rfl) ⟨37952, by rfl⟩ : syracuseStep 3238613 = 75905) (by norm_num)
theorem B5458661 : Blo 1437538 5458661 := bbase (se 4 (by rfl) ⟨511749, by rfl⟩ : syracuseStep 5458661 = 1023499) (by norm_num)
theorem B2157293 : Blo 1437538 2157293 := bbase (se 3 (by rfl) ⟨404492, by rfl⟩ : syracuseStep 2157293 = 808985) (by norm_num)
theorem B2427637 : Blo 1437538 2427637 := bbase (se 5 (by rfl) ⟨113795, by rfl⟩ : syracuseStep 2427637 = 227591) (by norm_num)
theorem B2157317 : Blo 1437538 2157317 := bbase (se 4 (by rfl) ⟨202248, by rfl⟩ : syracuseStep 2157317 = 404497) (by norm_num)
theorem B1821457 : Blo 1437538 1821457 := bbase (se 2 (by rfl) ⟨683046, by rfl⟩ : syracuseStep 1821457 = 1366093) (by norm_num)
theorem B2730773 : Blo 1437538 2730773 := bbase (se 6 (by rfl) ⟨64002, by rfl⟩ : syracuseStep 2730773 = 128005) (by norm_num)
theorem B6146837 : Blo 1437538 6146837 := bbase (se 6 (by rfl) ⟨144066, by rfl⟩ : syracuseStep 6146837 = 288133) (by norm_num)
theorem B2157341 : Blo 1437538 2157341 := bbase (se 3 (by rfl) ⟨404501, by rfl⟩ : syracuseStep 2157341 = 809003) (by norm_num)
theorem B3238685 : Blo 1437538 3238685 := bbase (se 3 (by rfl) ⟨607253, by rfl⟩ : syracuseStep 3238685 = 1214507) (by norm_num)
theorem B2591525 : Blo 1437538 2591525 := bbase (se 4 (by rfl) ⟨242955, by rfl⟩ : syracuseStep 2591525 = 485911) (by norm_num)
theorem B2157365 : Blo 1437538 2157365 := bbase (se 5 (by rfl) ⟨101126, by rfl⟩ : syracuseStep 2157365 = 202253) (by norm_num)
theorem B2304821 : Blo 1437538 2304821 := bbase (se 5 (by rfl) ⟨108038, by rfl⟩ : syracuseStep 2304821 = 216077) (by norm_num)
theorem B1477441 : Blo 1437538 1477441 := bbase (se 2 (by rfl) ⟨554040, by rfl⟩ : syracuseStep 1477441 = 1108081) (by norm_num)
theorem B2157389 : Blo 1437538 2157389 := bbase (se 3 (by rfl) ⟨404510, by rfl⟩ : syracuseStep 2157389 = 809021) (by norm_num)
theorem B2427725 : Blo 1437538 2427725 := bbase (se 3 (by rfl) ⟨455198, by rfl⟩ : syracuseStep 2427725 = 910397) (by norm_num)
theorem B2157413 : Blo 1437538 2157413 := bbase (se 4 (by rfl) ⟨202257, by rfl⟩ : syracuseStep 2157413 = 404515) (by norm_num)
theorem B4098917 : Blo 1437538 4098917 := bbase (se 4 (by rfl) ⟨384273, by rfl⟩ : syracuseStep 4098917 = 768547) (by norm_num)
theorem B3238757 : Blo 1437538 3238757 := bbase (se 4 (by rfl) ⟨303633, by rfl⟩ : syracuseStep 3238757 = 607267) (by norm_num)
theorem B2157437 : Blo 1437538 2157437 := bbase (se 3 (by rfl) ⟨404519, by rfl⟩ : syracuseStep 2157437 = 809039) (by norm_num)
theorem B2157461 : Blo 1437538 2157461 := bbase (se 6 (by rfl) ⟨50565, by rfl⟩ : syracuseStep 2157461 = 101131) (by norm_num)
theorem B2157485 : Blo 1437538 2157485 := bbase (se 3 (by rfl) ⟨404528, by rfl⟩ : syracuseStep 2157485 = 809057) (by norm_num)
theorem B2730925 : Blo 1437538 2730925 := bbase (se 3 (by rfl) ⟨512048, by rfl⟩ : syracuseStep 2730925 = 1024097) (by norm_num)
theorem B3238829 : Blo 1437538 3238829 := bbase (se 3 (by rfl) ⟨607280, by rfl⟩ : syracuseStep 3238829 = 1214561) (by norm_num)
theorem B1821629 : Blo 1437538 1821629 := bbase (se 3 (by rfl) ⟨341555, by rfl⟩ : syracuseStep 1821629 = 683111) (by norm_num)
theorem B1641409 : Blo 1437538 1641409 := bbase (se 2 (by rfl) ⟨615528, by rfl⟩ : syracuseStep 1641409 = 1231057) (by norm_num)
theorem B3640261 : Blo 1437538 3640261 := bbase (se 4 (by rfl) ⟨341274, by rfl⟩ : syracuseStep 3640261 = 682549) (by norm_num)
theorem B2157509 : Blo 1437538 2157509 := bbase (se 4 (by rfl) ⟨202266, by rfl⟩ : syracuseStep 2157509 = 404533) (by norm_num)
theorem B2427853 : Blo 1437538 2427853 := bbase (se 3 (by rfl) ⟨455222, by rfl⟩ : syracuseStep 2427853 = 910445) (by norm_num)
theorem B2157533 : Blo 1437538 2157533 := bbase (se 3 (by rfl) ⟨404537, by rfl⟩ : syracuseStep 2157533 = 809075) (by norm_num)
theorem B4852709 : Blo 1437538 4852709 := bbase (se 4 (by rfl) ⟨454941, by rfl⟩ : syracuseStep 4852709 = 909883) (by norm_num)
theorem B2157557 : Blo 1437538 2157557 := bbase (se 5 (by rfl) ⟨101135, by rfl⟩ : syracuseStep 2157557 = 202271) (by norm_num)
theorem B1821685 : Blo 1437538 1821685 := bbase (se 5 (by rfl) ⟨85391, by rfl⟩ : syracuseStep 1821685 = 170783) (by norm_num)
theorem B3238901 : Blo 1437538 3238901 := bbase (se 5 (by rfl) ⟨151823, by rfl⟩ : syracuseStep 3238901 = 303647) (by norm_num)
theorem B2157581 : Blo 1437538 2157581 := bbase (se 3 (by rfl) ⟨404546, by rfl⟩ : syracuseStep 2157581 = 809093) (by norm_num)
theorem B3116045 : Blo 1437538 3116045 := bbase (se 3 (by rfl) ⟨584258, by rfl⟩ : syracuseStep 3116045 = 1168517) (by norm_num)
theorem B2157605 : Blo 1437538 2157605 := bbase (se 4 (by rfl) ⟨202275, by rfl⟩ : syracuseStep 2157605 = 404551) (by norm_num)
theorem B2427941 : Blo 1437538 2427941 := bbase (se 4 (by rfl) ⟨227619, by rfl⟩ : syracuseStep 2427941 = 455239) (by norm_num)
theorem B14756917 : Blo 1437538 14756917 := bbase (se 5 (by rfl) ⟨691730, by rfl⟩ : syracuseStep 14756917 = 1383461) (by norm_num)
theorem B3640373 : Blo 1437538 3640373 := bbase (se 5 (by rfl) ⟨170642, by rfl⟩ : syracuseStep 3640373 = 341285) (by norm_num)
theorem B2157629 : Blo 1437538 2157629 := bbase (se 3 (by rfl) ⟨404555, by rfl⟩ : syracuseStep 2157629 = 809111) (by norm_num)
theorem B2157653 : Blo 1437538 2157653 := bbase (se 8 (by rfl) ⟨12642, by rfl⟩ : syracuseStep 2157653 = 25285) (by norm_num)
theorem B1821781 : Blo 1437538 1821781 := bbase (se 8 (by rfl) ⟨10674, by rfl⟩ : syracuseStep 1821781 = 21349) (by norm_num)
theorem B4099157 : Blo 1437538 4099157 := bbase (se 8 (by rfl) ⟨24018, by rfl⟩ : syracuseStep 4099157 = 48037) (by norm_num)
theorem B3279973 : Blo 1437538 3279973 := bbase (se 4 (by rfl) ⟨307497, by rfl⟩ : syracuseStep 3279973 = 614995) (by norm_num)
theorem B2157677 : Blo 1437538 2157677 := bbase (se 3 (by rfl) ⟨404564, by rfl⟩ : syracuseStep 2157677 = 809129) (by norm_num)
theorem B1846381 : Blo 1437538 1846381 := bbase (se 3 (by rfl) ⟨346196, by rfl⟩ : syracuseStep 1846381 = 692393) (by norm_num)
theorem B2157701 : Blo 1437538 2157701 := bbase (se 4 (by rfl) ⟨202284, by rfl⟩ : syracuseStep 2157701 = 404569) (by norm_num)
theorem B2157725 : Blo 1437538 2157725 := bbase (se 3 (by rfl) ⟨404573, by rfl⟩ : syracuseStep 2157725 = 809147) (by norm_num)
theorem B2428069 : Blo 1437538 2428069 := bbase (se 4 (by rfl) ⟨227631, by rfl⟩ : syracuseStep 2428069 = 455263) (by norm_num)
theorem B2157749 : Blo 1437538 2157749 := bbase (se 5 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 2157749 = 202289) (by norm_num)
theorem B2157773 : Blo 1437538 2157773 := bbase (se 3 (by rfl) ⟨404582, by rfl⟩ : syracuseStep 2157773 = 809165) (by norm_num)
theorem B2731229 : Blo 1437538 2731229 := bbase (se 3 (by rfl) ⟨512105, by rfl⟩ : syracuseStep 2731229 = 1024211) (by norm_num)
theorem B2157797 : Blo 1437538 2157797 := bbase (se 4 (by rfl) ⟨202293, by rfl⟩ : syracuseStep 2157797 = 404587) (by norm_num)
theorem B3640565 : Blo 1437538 3640565 := bbase (se 5 (by rfl) ⟨170651, by rfl⟩ : syracuseStep 3640565 = 341303) (by norm_num)
theorem B2157821 : Blo 1437538 2157821 := bbase (se 3 (by rfl) ⟨404591, by rfl⟩ : syracuseStep 2157821 = 809183) (by norm_num)
theorem B2428157 : Blo 1437538 2428157 := bbase (se 3 (by rfl) ⟨455279, by rfl⟩ : syracuseStep 2428157 = 910559) (by norm_num)
theorem B2157845 : Blo 1437538 2157845 := bbase (se 6 (by rfl) ⟨50574, by rfl⟩ : syracuseStep 2157845 = 101149) (by norm_num)
theorem B1535257 : Blo 1437538 1535257 := bbase (se 2 (by rfl) ⟨575721, by rfl⟩ : syracuseStep 1535257 = 1151443) (by norm_num)
theorem B2157869 : Blo 1437538 2157869 := bbase (se 3 (by rfl) ⟨404600, by rfl⟩ : syracuseStep 2157869 = 809201) (by norm_num)
theorem B2157893 : Blo 1437538 2157893 := bbase (se 4 (by rfl) ⟨202302, by rfl⟩ : syracuseStep 2157893 = 404605) (by norm_num)
theorem B1617241 : Blo 1437538 1617241 := bbase (se 2 (by rfl) ⟨606465, by rfl⟩ : syracuseStep 1617241 = 1212931) (by norm_num)
theorem B2157917 : Blo 1437538 2157917 := bbase (se 3 (by rfl) ⟨404609, by rfl⟩ : syracuseStep 2157917 = 809219) (by norm_num)
theorem B2157941 : Blo 1437538 2157941 := bbase (se 5 (by rfl) ⟨101153, by rfl⟩ : syracuseStep 2157941 = 202307) (by norm_num)
theorem B1617277 : Blo 1437538 1617277 := bbase (se 3 (by rfl) ⟨303239, by rfl⟩ : syracuseStep 1617277 = 606479) (by norm_num)
theorem B2428285 : Blo 1437538 2428285 := bbase (se 3 (by rfl) ⟨455303, by rfl⟩ : syracuseStep 2428285 = 910607) (by norm_num)
theorem B2157965 : Blo 1437538 2157965 := bbase (se 3 (by rfl) ⟨404618, by rfl⟩ : syracuseStep 2157965 = 809237) (by norm_num)
theorem B12283285 : Blo 1437538 12283285 := bbase (se 6 (by rfl) ⟨287889, by rfl⟩ : syracuseStep 12283285 = 575779) (by norm_num)
theorem B4853141 : Blo 1437538 4853141 := bbase (se 6 (by rfl) ⟨113745, by rfl⟩ : syracuseStep 4853141 = 227491) (by norm_num)
theorem B1617313 : Blo 1437538 1617313 := bbase (se 2 (by rfl) ⟨606492, by rfl⟩ : syracuseStep 1617313 = 1212985) (by norm_num)
theorem B2157989 : Blo 1437538 2157989 := bbase (se 4 (by rfl) ⟨202311, by rfl⟩ : syracuseStep 2157989 = 404623) (by norm_num)
theorem B2158013 : Blo 1437538 2158013 := bbase (se 3 (by rfl) ⟨404627, by rfl⟩ : syracuseStep 2158013 = 809255) (by norm_num)
theorem B1617349 : Blo 1437538 1617349 := bbase (se 4 (by rfl) ⟨151626, by rfl⟩ : syracuseStep 1617349 = 303253) (by norm_num)
theorem B1535441 : Blo 1437538 1535441 := bbase (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) (by norm_num)
theorem B2158037 : Blo 1437538 2158037 := bbase (se 7 (by rfl) ⟨25289, by rfl⟩ : syracuseStep 2158037 = 50579) (by norm_num)
theorem B2428373 : Blo 1437538 2428373 := bbase (se 7 (by rfl) ⟨28457, by rfl⟩ : syracuseStep 2428373 = 56915) (by norm_num)
theorem B1617385 : Blo 1437538 1617385 := bbase (se 2 (by rfl) ⟨606519, by rfl⟩ : syracuseStep 1617385 = 1213039) (by norm_num)
theorem B2158061 : Blo 1437538 2158061 := bbase (se 3 (by rfl) ⟨404636, by rfl⟩ : syracuseStep 2158061 = 809273) (by norm_num)
theorem B2158085 : Blo 1437538 2158085 := bbase (se 4 (by rfl) ⟨202320, by rfl⟩ : syracuseStep 2158085 = 404641) (by norm_num)
theorem B6147589 : Blo 1437538 6147589 := bbase (se 4 (by rfl) ⟨576336, by rfl⟩ : syracuseStep 6147589 = 1152673) (by norm_num)
theorem B1617421 : Blo 1437538 1617421 := bbase (se 3 (by rfl) ⟨303266, by rfl⟩ : syracuseStep 1617421 = 606533) (by norm_num)
theorem B2158109 : Blo 1437538 2158109 := bbase (se 3 (by rfl) ⟨404645, by rfl⟩ : syracuseStep 2158109 = 809291) (by norm_num)
theorem B1617457 : Blo 1437538 1617457 := bbase (se 2 (by rfl) ⟨606546, by rfl⟩ : syracuseStep 1617457 = 1213093) (by norm_num)
theorem B2158133 : Blo 1437538 2158133 := bbase (se 5 (by rfl) ⟨101162, by rfl⟩ : syracuseStep 2158133 = 202325) (by norm_num)
theorem B3640909 : Blo 1437538 3640909 := bbase (se 3 (by rfl) ⟨682670, by rfl⟩ : syracuseStep 3640909 = 1365341) (by norm_num)
theorem B2158157 : Blo 1437538 2158157 := bbase (se 3 (by rfl) ⟨404654, by rfl⟩ : syracuseStep 2158157 = 809309) (by norm_num)
theorem B1617493 : Blo 1437538 1617493 := bbase (se 8 (by rfl) ⟨9477, by rfl⟩ : syracuseStep 1617493 = 18955) (by norm_num)
theorem B2428501 : Blo 1437538 2428501 := bbase (se 8 (by rfl) ⟨14229, by rfl⟩ : syracuseStep 2428501 = 28459) (by norm_num)
theorem B2158181 : Blo 1437538 2158181 := bbase (se 4 (by rfl) ⟨202329, by rfl⟩ : syracuseStep 2158181 = 404659) (by norm_num)
theorem B1617529 : Blo 1437538 1617529 := bbase (se 2 (by rfl) ⟨606573, by rfl⟩ : syracuseStep 1617529 = 1213147) (by norm_num)
theorem B2158205 : Blo 1437538 2158205 := bbase (se 3 (by rfl) ⟨404663, by rfl⟩ : syracuseStep 2158205 = 809327) (by norm_num)
theorem B2158229 : Blo 1437538 2158229 := bbase (se 6 (by rfl) ⟨50583, by rfl⟩ : syracuseStep 2158229 = 101167) (by norm_num)
theorem B1617565 : Blo 1437538 1617565 := bbase (se 3 (by rfl) ⟨303293, by rfl⟩ : syracuseStep 1617565 = 606587) (by norm_num)
theorem B2158253 : Blo 1437538 2158253 := bbase (se 3 (by rfl) ⟨404672, by rfl⟩ : syracuseStep 2158253 = 809345) (by norm_num)
theorem B2428589 : Blo 1437538 2428589 := bbase (se 3 (by rfl) ⟨455360, by rfl⟩ : syracuseStep 2428589 = 910721) (by norm_num)
theorem B3641021 : Blo 1437538 3641021 := bbase (se 3 (by rfl) ⟨682691, by rfl⟩ : syracuseStep 3641021 = 1365383) (by norm_num)
theorem B1617601 : Blo 1437538 1617601 := bbase (se 2 (by rfl) ⟨606600, by rfl⟩ : syracuseStep 1617601 = 1213201) (by norm_num)
theorem B2158277 : Blo 1437538 2158277 := bbase (se 4 (by rfl) ⟨202338, by rfl⟩ : syracuseStep 2158277 = 404677) (by norm_num)
theorem B2158301 : Blo 1437538 2158301 := bbase (se 3 (by rfl) ⟨404681, by rfl⟩ : syracuseStep 2158301 = 809363) (by norm_num)
theorem B1617637 : Blo 1437538 1617637 := bbase (se 4 (by rfl) ⟨151653, by rfl⟩ : syracuseStep 1617637 = 303307) (by norm_num)
theorem B2158325 : Blo 1437538 2158325 := bbase (se 5 (by rfl) ⟨101171, by rfl⟩ : syracuseStep 2158325 = 202343) (by norm_num)
theorem B1617673 : Blo 1437538 1617673 := bbase (se 2 (by rfl) ⟨606627, by rfl⟩ : syracuseStep 1617673 = 1213255) (by norm_num)
theorem B2158349 : Blo 1437538 2158349 := bbase (se 3 (by rfl) ⟨404690, by rfl⟩ : syracuseStep 2158349 = 809381) (by norm_num)
theorem B5181205 : Blo 1437538 5181205 := bbase (se 6 (by rfl) ⟨121434, by rfl⟩ : syracuseStep 5181205 = 242869) (by norm_num)
theorem B2158373 : Blo 1437538 2158373 := bbase (se 4 (by rfl) ⟨202347, by rfl⟩ : syracuseStep 2158373 = 404695) (by norm_num)
theorem B1617709 : Blo 1437538 1617709 := bbase (se 3 (by rfl) ⟨303320, by rfl⟩ : syracuseStep 1617709 = 606641) (by norm_num)
theorem B2428717 : Blo 1437538 2428717 := bbase (se 3 (by rfl) ⟨455384, by rfl⟩ : syracuseStep 2428717 = 910769) (by norm_num)
theorem B2158397 : Blo 1437538 2158397 := bbase (se 3 (by rfl) ⟨404699, by rfl⟩ : syracuseStep 2158397 = 809399) (by norm_num)
theorem B4853573 : Blo 1437538 4853573 := bbase (se 4 (by rfl) ⟨455022, by rfl⟩ : syracuseStep 4853573 = 910045) (by norm_num)
theorem B7286597 : Blo 1437538 7286597 := bbase (se 4 (by rfl) ⟨683118, by rfl⟩ : syracuseStep 7286597 = 1366237) (by norm_num)
theorem B1617745 : Blo 1437538 1617745 := bbase (se 2 (by rfl) ⟨606654, by rfl⟩ : syracuseStep 1617745 = 1213309) (by norm_num)
theorem B2158421 : Blo 1437538 2158421 := bbase (se 9 (by rfl) ⟨6323, by rfl⟩ : syracuseStep 2158421 = 12647) (by norm_num)
theorem B2158445 : Blo 1437538 2158445 := bbase (se 3 (by rfl) ⟨404708, by rfl⟩ : syracuseStep 2158445 = 809417) (by norm_num)
theorem B1617781 : Blo 1437538 1617781 := bbase (se 5 (by rfl) ⟨75833, by rfl⟩ : syracuseStep 1617781 = 151667) (by norm_num)
theorem B3641213 : Blo 1437538 3641213 := bbase (se 3 (by rfl) ⟨682727, by rfl⟩ : syracuseStep 3641213 = 1365455) (by norm_num)
theorem B5459845 : Blo 1437538 5459845 := bbase (se 4 (by rfl) ⟨511860, by rfl⟩ : syracuseStep 5459845 = 1023721) (by norm_num)
theorem B2158469 : Blo 1437538 2158469 := bbase (se 4 (by rfl) ⟨202356, by rfl⟩ : syracuseStep 2158469 = 404713) (by norm_num)
theorem B2428805 : Blo 1437538 2428805 := bbase (se 4 (by rfl) ⟨227700, by rfl⟩ : syracuseStep 2428805 = 455401) (by norm_num)
theorem B1617817 : Blo 1437538 1617817 := bbase (se 2 (by rfl) ⟨606681, by rfl⟩ : syracuseStep 1617817 = 1213363) (by norm_num)
theorem B2158493 : Blo 1437538 2158493 := bbase (se 3 (by rfl) ⟨404717, by rfl⟩ : syracuseStep 2158493 = 809435) (by norm_num)
theorem B2158517 : Blo 1437538 2158517 := bbase (se 5 (by rfl) ⟨101180, by rfl⟩ : syracuseStep 2158517 = 202361) (by norm_num)
theorem B1617853 : Blo 1437538 1617853 := bbase (se 3 (by rfl) ⟨303347, by rfl⟩ : syracuseStep 1617853 = 606695) (by norm_num)
theorem B2158541 : Blo 1437538 2158541 := bbase (se 3 (by rfl) ⟨404726, by rfl⟩ : syracuseStep 2158541 = 809453) (by norm_num)
theorem B2731981 : Blo 1437538 2731981 := bbase (se 3 (by rfl) ⟨512246, by rfl⟩ : syracuseStep 2731981 = 1024493) (by norm_num)
theorem B1478617 : Blo 1437538 1478617 := bbase (se 2 (by rfl) ⟨554481, by rfl⟩ : syracuseStep 1478617 = 1108963) (by norm_num)
theorem B1617889 : Blo 1437538 1617889 := bbase (se 2 (by rfl) ⟨606708, by rfl⟩ : syracuseStep 1617889 = 1213417) (by norm_num)
theorem B2158565 : Blo 1437538 2158565 := bbase (se 4 (by rfl) ⟨202365, by rfl⟩ : syracuseStep 2158565 = 404731) (by norm_num)
theorem B2158589 : Blo 1437538 2158589 := bbase (se 3 (by rfl) ⟨404735, by rfl⟩ : syracuseStep 2158589 = 809471) (by norm_num)
theorem B1617925 : Blo 1437538 1617925 := bbase (se 4 (by rfl) ⟨151680, by rfl⟩ : syracuseStep 1617925 = 303361) (by norm_num)
theorem B2428933 : Blo 1437538 2428933 := bbase (se 4 (by rfl) ⟨227712, by rfl⟩ : syracuseStep 2428933 = 455425) (by norm_num)
theorem B5615621 : Blo 1437538 5615621 := bbase (se 4 (by rfl) ⟨526464, by rfl⟩ : syracuseStep 5615621 = 1052929) (by norm_num)
theorem B2158613 : Blo 1437538 2158613 := bbase (se 6 (by rfl) ⟨50592, by rfl⟩ : syracuseStep 2158613 = 101185) (by norm_num)
theorem B1617961 : Blo 1437538 1617961 := bbase (se 2 (by rfl) ⟨606735, by rfl⟩ : syracuseStep 1617961 = 1213471) (by norm_num)
theorem B2158637 : Blo 1437538 2158637 := bbase (se 3 (by rfl) ⟨404744, by rfl⟩ : syracuseStep 2158637 = 809489) (by norm_num)
theorem B5992501 : Blo 1437538 5992501 := bbase (se 5 (by rfl) ⟨280898, by rfl⟩ : syracuseStep 5992501 = 561797) (by norm_num)
theorem B2158661 : Blo 1437538 2158661 := bbase (se 4 (by rfl) ⟨202374, by rfl⟩ : syracuseStep 2158661 = 404749) (by norm_num)
theorem B1617997 : Blo 1437538 1617997 := bbase (se 3 (by rfl) ⟨303374, by rfl⟩ : syracuseStep 1617997 = 606749) (by norm_num)
theorem B2158685 : Blo 1437538 2158685 := bbase (se 3 (by rfl) ⟨404753, by rfl⟩ : syracuseStep 2158685 = 809507) (by norm_num)
theorem B2732125 : Blo 1437538 2732125 := bbase (se 3 (by rfl) ⟨512273, by rfl⟩ : syracuseStep 2732125 = 1024547) (by norm_num)
theorem B2429021 : Blo 1437538 2429021 := bbase (se 3 (by rfl) ⟨455441, by rfl⟩ : syracuseStep 2429021 = 910883) (by norm_num)
theorem B1618033 : Blo 1437538 1618033 := bbase (se 2 (by rfl) ⟨606762, by rfl⟩ : syracuseStep 1618033 = 1213525) (by norm_num)
theorem B2158709 : Blo 1437538 2158709 := bbase (se 5 (by rfl) ⟨101189, by rfl⟩ : syracuseStep 2158709 = 202379) (by norm_num)
theorem B2158733 : Blo 1437538 2158733 := bbase (se 3 (by rfl) ⟨404762, by rfl⟩ : syracuseStep 2158733 = 809525) (by norm_num)
theorem B1618069 : Blo 1437538 1618069 := bbase (se 6 (by rfl) ⟨37923, by rfl⟩ : syracuseStep 1618069 = 75847) (by norm_num)
theorem B2158757 : Blo 1437538 2158757 := bbase (se 4 (by rfl) ⟨202383, by rfl⟩ : syracuseStep 2158757 = 404767) (by norm_num)
theorem B5460149 : Blo 1437538 5460149 := bbase (se 5 (by rfl) ⟨255944, by rfl⟩ : syracuseStep 5460149 = 511889) (by norm_num)
theorem B1618105 : Blo 1437538 1618105 := bbase (se 2 (by rfl) ⟨606789, by rfl⟩ : syracuseStep 1618105 = 1213579) (by norm_num)
theorem B2158781 : Blo 1437538 2158781 := bbase (se 3 (by rfl) ⟨404771, by rfl⟩ : syracuseStep 2158781 = 809543) (by norm_num)
theorem B1536193 : Blo 1437538 1536193 := bbase (se 2 (by rfl) ⟨576072, by rfl⟩ : syracuseStep 1536193 = 1152145) (by norm_num)
theorem B5181653 : Blo 1437538 5181653 := bbase (se 7 (by rfl) ⟨60722, by rfl⟩ : syracuseStep 5181653 = 121445) (by norm_num)
theorem B3641557 : Blo 1437538 3641557 := bbase (se 7 (by rfl) ⟨42674, by rfl⟩ : syracuseStep 3641557 = 85349) (by norm_num)
theorem B2158805 : Blo 1437538 2158805 := bbase (se 7 (by rfl) ⟨25298, by rfl⟩ : syracuseStep 2158805 = 50597) (by norm_num)
theorem B1618141 : Blo 1437538 1618141 := bbase (se 3 (by rfl) ⟨303401, by rfl⟩ : syracuseStep 1618141 = 606803) (by norm_num)
theorem B2429149 : Blo 1437538 2429149 := bbase (se 3 (by rfl) ⟨455465, by rfl⟩ : syracuseStep 2429149 = 910931) (by norm_num)
theorem B7278821 : Blo 1437538 7278821 := bbase (se 4 (by rfl) ⟨682389, by rfl⟩ : syracuseStep 7278821 = 1364779) (by norm_num)
theorem B6148325 : Blo 1437538 6148325 := bbase (se 4 (by rfl) ⟨576405, by rfl⟩ : syracuseStep 6148325 = 1152811) (by norm_num)
theorem B2158829 : Blo 1437538 2158829 := bbase (se 3 (by rfl) ⟨404780, by rfl⟩ : syracuseStep 2158829 = 809561) (by norm_num)
theorem B4854005 : Blo 1437538 4854005 := bbase (se 5 (by rfl) ⟨227531, by rfl⟩ : syracuseStep 4854005 = 455063) (by norm_num)
theorem B3281141 : Blo 1437538 3281141 := bbase (se 5 (by rfl) ⟨153803, by rfl⟩ : syracuseStep 3281141 = 307607) (by norm_num)
theorem B3690749 : Blo 1437538 3690749 := bbase (se 3 (by rfl) ⟨692015, by rfl⟩ : syracuseStep 3690749 = 1384031) (by norm_num)
theorem B2732285 : Blo 1437538 2732285 := bbase (se 3 (by rfl) ⟨512303, by rfl⟩ : syracuseStep 2732285 = 1024607) (by norm_num)
theorem B1618177 : Blo 1437538 1618177 := bbase (se 2 (by rfl) ⟨606816, by rfl⟩ : syracuseStep 1618177 = 1213633) (by norm_num)
theorem B2158853 : Blo 1437538 2158853 := bbase (se 4 (by rfl) ⟨202392, by rfl⟩ : syracuseStep 2158853 = 404785) (by norm_num)
theorem B1536265 : Blo 1437538 1536265 := bbase (se 2 (by rfl) ⟨576099, by rfl⟩ : syracuseStep 1536265 = 1152199) (by norm_num)
theorem B12144917 : Blo 1437538 12144917 := bbase (se 6 (by rfl) ⟨284646, by rfl⟩ : syracuseStep 12144917 = 569293) (by norm_num)
theorem B2158877 : Blo 1437538 2158877 := bbase (se 3 (by rfl) ⟨404789, by rfl⟩ : syracuseStep 2158877 = 809579) (by norm_num)
theorem B1618213 : Blo 1437538 1618213 := bbase (se 4 (by rfl) ⟨151707, by rfl⟩ : syracuseStep 1618213 = 303415) (by norm_num)
theorem B2158901 : Blo 1437538 2158901 := bbase (se 5 (by rfl) ⟨101198, by rfl⟩ : syracuseStep 2158901 = 202397) (by norm_num)
theorem B3641669 : Blo 1437538 3641669 := bbase (se 4 (by rfl) ⟨341406, by rfl⟩ : syracuseStep 3641669 = 682813) (by norm_num)
theorem B1618249 : Blo 1437538 1618249 := bbase (se 2 (by rfl) ⟨606843, by rfl⟩ : syracuseStep 1618249 = 1213687) (by norm_num)
theorem B1970509 : Blo 1437538 1970509 := bbase (se 3 (by rfl) ⟨369470, by rfl⟩ : syracuseStep 1970509 = 738941) (by norm_num)
theorem B2158925 : Blo 1437538 2158925 := bbase (se 3 (by rfl) ⟨404798, by rfl⟩ : syracuseStep 2158925 = 809597) (by norm_num)
theorem B3887461 : Blo 1437538 3887461 := bbase (se 4 (by rfl) ⟨364449, by rfl⟩ : syracuseStep 3887461 = 728899) (by norm_num)
theorem B2158949 : Blo 1437538 2158949 := bbase (se 4 (by rfl) ⟨202401, by rfl⟩ : syracuseStep 2158949 = 404803) (by norm_num)
theorem B1618285 : Blo 1437538 1618285 := bbase (se 3 (by rfl) ⟨303428, by rfl⟩ : syracuseStep 1618285 = 606857) (by norm_num)
theorem B2158973 : Blo 1437538 2158973 := bbase (se 3 (by rfl) ⟨404807, by rfl⟩ : syracuseStep 2158973 = 809615) (by norm_num)
theorem B2732429 : Blo 1437538 2732429 := bbase (se 3 (by rfl) ⟨512330, by rfl⟩ : syracuseStep 2732429 = 1024661) (by norm_num)
theorem B1618321 : Blo 1437538 1618321 := bbase (se 2 (by rfl) ⟨606870, by rfl⟩ : syracuseStep 1618321 = 1213741) (by norm_num)
theorem B2158997 : Blo 1437538 2158997 := bbase (se 6 (by rfl) ⟨50601, by rfl⟩ : syracuseStep 2158997 = 101203) (by norm_num)
theorem B2077085 : Blo 1437538 2077085 := bbase (se 3 (by rfl) ⟨389453, by rfl⟩ : syracuseStep 2077085 = 778907) (by norm_num)
theorem B2159021 : Blo 1437538 2159021 := bbase (se 3 (by rfl) ⟨404816, by rfl⟩ : syracuseStep 2159021 = 809633) (by norm_num)
theorem B1618357 : Blo 1437538 1618357 := bbase (se 5 (by rfl) ⟨75860, by rfl⟩ : syracuseStep 1618357 = 151721) (by norm_num)
theorem B1536445 : Blo 1437538 1536445 := bbase (se 3 (by rfl) ⟨288083, by rfl⟩ : syracuseStep 1536445 = 576167) (by norm_num)
theorem B2159045 : Blo 1437538 2159045 := bbase (se 4 (by rfl) ⟨202410, by rfl⟩ : syracuseStep 2159045 = 404821) (by norm_num)
theorem B1618393 : Blo 1437538 1618393 := bbase (se 2 (by rfl) ⟨606897, by rfl⟩ : syracuseStep 1618393 = 1213795) (by norm_num)
theorem B2159069 : Blo 1437538 2159069 := bbase (se 3 (by rfl) ⟨404825, by rfl⟩ : syracuseStep 2159069 = 809651) (by norm_num)
theorem B13832693 : Blo 1437538 13832693 := bbase (se 5 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 13832693 = 1296815) (by norm_num)
theorem B2159093 : Blo 1437538 2159093 := bbase (se 5 (by rfl) ⟨101207, by rfl⟩ : syracuseStep 2159093 = 202415) (by norm_num)
theorem B1618429 : Blo 1437538 1618429 := bbase (se 3 (by rfl) ⟨303455, by rfl⟩ : syracuseStep 1618429 = 606911) (by norm_num)
theorem B3641861 : Blo 1437538 3641861 := bbase (se 4 (by rfl) ⟨341424, by rfl⟩ : syracuseStep 3641861 = 682849) (by norm_num)
theorem B2159117 : Blo 1437538 2159117 := bbase (se 3 (by rfl) ⟨404834, by rfl⟩ : syracuseStep 2159117 = 809669) (by norm_num)
theorem B1618465 : Blo 1437538 1618465 := bbase (se 2 (by rfl) ⟨606924, by rfl⟩ : syracuseStep 1618465 = 1213849) (by norm_num)
theorem B2159141 : Blo 1437538 2159141 := bbase (se 4 (by rfl) ⟨202419, by rfl⟩ : syracuseStep 2159141 = 404839) (by norm_num)
theorem B2159165 : Blo 1437538 2159165 := bbase (se 3 (by rfl) ⟨404843, by rfl⟩ : syracuseStep 2159165 = 809687) (by norm_num)
theorem B1618501 : Blo 1437538 1618501 := bbase (se 4 (by rfl) ⟨151734, by rfl⟩ : syracuseStep 1618501 = 303469) (by norm_num)
theorem B2159189 : Blo 1437538 2159189 := bbase (se 8 (by rfl) ⟨12651, by rfl⟩ : syracuseStep 2159189 = 25303) (by norm_num)
theorem B1618537 : Blo 1437538 1618537 := bbase (se 2 (by rfl) ⟨606951, by rfl⟩ : syracuseStep 1618537 = 1213903) (by norm_num)
theorem B2159213 : Blo 1437538 2159213 := bbase (se 3 (by rfl) ⟨404852, by rfl⟩ : syracuseStep 2159213 = 809705) (by norm_num)
theorem B6140549 : Blo 1437538 6140549 := bbase (se 4 (by rfl) ⟨575676, by rfl⟩ : syracuseStep 6140549 = 1151353) (by norm_num)
theorem B2159237 : Blo 1437538 2159237 := bbase (se 4 (by rfl) ⟨202428, by rfl⟩ : syracuseStep 2159237 = 404857) (by norm_num)
theorem B1618573 : Blo 1437538 1618573 := bbase (se 3 (by rfl) ⟨303482, by rfl⟩ : syracuseStep 1618573 = 606965) (by norm_num)
theorem B2159261 : Blo 1437538 2159261 := bbase (se 3 (by rfl) ⟨404861, by rfl⟩ : syracuseStep 2159261 = 809723) (by norm_num)
theorem B4854437 : Blo 1437538 4854437 := bbase (se 4 (by rfl) ⟨455103, by rfl⟩ : syracuseStep 4854437 = 910207) (by norm_num)
theorem B2732717 : Blo 1437538 2732717 := bbase (se 3 (by rfl) ⟨512384, by rfl⟩ : syracuseStep 2732717 = 1024769) (by norm_num)
theorem B1618609 : Blo 1437538 1618609 := bbase (se 2 (by rfl) ⟨606978, by rfl⟩ : syracuseStep 1618609 = 1213957) (by norm_num)
theorem B2159285 : Blo 1437538 2159285 := bbase (se 5 (by rfl) ⟨101216, by rfl⟩ : syracuseStep 2159285 = 202433) (by norm_num)
theorem B5534405 : Blo 1437538 5534405 := bbase (se 4 (by rfl) ⟨518850, by rfl⟩ : syracuseStep 5534405 = 1037701) (by norm_num)
theorem B16380629 : Blo 1437538 16380629 := bbase (se 7 (by rfl) ⟨191960, by rfl⟩ : syracuseStep 16380629 = 383921) (by norm_num)
theorem B1618645 : Blo 1437538 1618645 := bbase (se 7 (by rfl) ⟨18968, by rfl⟩ : syracuseStep 1618645 = 37937) (by norm_num)
theorem B1618681 : Blo 1437538 1618681 := bbase (se 2 (by rfl) ⟨607005, by rfl⟩ : syracuseStep 1618681 = 1214011) (by norm_num)
theorem B7484165 : Blo 1437538 7484165 := bbase (se 4 (by rfl) ⟨701640, by rfl⟩ : syracuseStep 7484165 = 1403281) (by norm_num)
theorem B1618717 : Blo 1437538 1618717 := bbase (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) (by norm_num)
theorem B3281725 : Blo 1437538 3281725 := bbase (se 3 (by rfl) ⟨615323, by rfl⟩ : syracuseStep 3281725 = 1230647) (by norm_num)
theorem B1618753 : Blo 1437538 1618753 := bbase (se 2 (by rfl) ⟨607032, by rfl⟩ : syracuseStep 1618753 = 1214065) (by norm_num)
theorem B2732869 : Blo 1437538 2732869 := bbase (se 4 (by rfl) ⟨256206, by rfl⟩ : syracuseStep 2732869 = 512413) (by norm_num)
theorem B3642205 : Blo 1437538 3642205 := bbase (se 3 (by rfl) ⟨682913, by rfl⟩ : syracuseStep 3642205 = 1365827) (by norm_num)
theorem B1618789 : Blo 1437538 1618789 := bbase (se 4 (by rfl) ⟨151761, by rfl⟩ : syracuseStep 1618789 = 303523) (by norm_num)
theorem B1536889 : Blo 1437538 1536889 := bbase (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) (by norm_num)
theorem B1618825 : Blo 1437538 1618825 := bbase (se 2 (by rfl) ⟨607059, by rfl⟩ : syracuseStep 1618825 = 1214119) (by norm_num)
theorem B2077589 : Blo 1437538 2077589 := bbase (se 6 (by rfl) ⟨48693, by rfl⟩ : syracuseStep 2077589 = 97387) (by norm_num)
theorem B1618861 : Blo 1437538 1618861 := bbase (se 3 (by rfl) ⟨303536, by rfl⟩ : syracuseStep 1618861 = 607073) (by norm_num)
theorem B3642317 : Blo 1437538 3642317 := bbase (se 3 (by rfl) ⟨682934, by rfl⟩ : syracuseStep 3642317 = 1365869) (by norm_num)
theorem B1618897 : Blo 1437538 1618897 := bbase (se 2 (by rfl) ⟨607086, by rfl⟩ : syracuseStep 1618897 = 1214173) (by norm_num)
theorem B1618933 : Blo 1437538 1618933 := bbase (se 5 (by rfl) ⟨75887, by rfl⟩ : syracuseStep 1618933 = 151775) (by norm_num)
theorem B1537013 : Blo 1437538 1537013 := bbase (se 5 (by rfl) ⟨72047, by rfl⟩ : syracuseStep 1537013 = 144095) (by norm_num)
theorem B1618969 : Blo 1437538 1618969 := bbase (se 2 (by rfl) ⟨607113, by rfl⟩ : syracuseStep 1618969 = 1214227) (by norm_num)
theorem B1619005 : Blo 1437538 1619005 := bbase (se 3 (by rfl) ⟨303563, by rfl⟩ : syracuseStep 1619005 = 607127) (by norm_num)
theorem B4854869 : Blo 1437538 4854869 := bbase (se 8 (by rfl) ⟨28446, by rfl⟩ : syracuseStep 4854869 = 56893) (by norm_num)
theorem B1619041 : Blo 1437538 1619041 := bbase (se 2 (by rfl) ⟨607140, by rfl⟩ : syracuseStep 1619041 = 1214281) (by norm_num)
theorem B3503213 : Blo 1437538 3503213 := bbase (se 3 (by rfl) ⟨656852, by rfl⟩ : syracuseStep 3503213 = 1313705) (by norm_num)
theorem B1619077 : Blo 1437538 1619077 := bbase (se 4 (by rfl) ⟨151788, by rfl⟩ : syracuseStep 1619077 = 303577) (by norm_num)
theorem B3740813 : Blo 1437538 3740813 := bbase (se 3 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 3740813 = 1402805) (by norm_num)
theorem B3642509 : Blo 1437538 3642509 := bbase (se 3 (by rfl) ⟨682970, by rfl⟩ : syracuseStep 3642509 = 1365941) (by norm_num)
theorem B1619113 : Blo 1437538 1619113 := bbase (se 2 (by rfl) ⟨607167, by rfl⟩ : syracuseStep 1619113 = 1214335) (by norm_num)
theorem B3372205 : Blo 1437538 3372205 := bbase (se 3 (by rfl) ⟨632288, by rfl⟩ : syracuseStep 3372205 = 1264577) (by norm_num)
theorem B7779509 : Blo 1437538 7779509 := bbase (se 5 (by rfl) ⟨364664, by rfl⟩ : syracuseStep 7779509 = 729329) (by norm_num)
theorem B3454157 : Blo 1437538 3454157 := bbase (se 3 (by rfl) ⟨647654, by rfl⟩ : syracuseStep 3454157 = 1295309) (by norm_num)
theorem B1619149 : Blo 1437538 1619149 := bbase (se 3 (by rfl) ⟨303590, by rfl⟩ : syracuseStep 1619149 = 607181) (by norm_num)
theorem B1619185 : Blo 1437538 1619185 := bbase (se 2 (by rfl) ⟨607194, by rfl⟩ : syracuseStep 1619185 = 1214389) (by norm_num)
theorem B3454213 : Blo 1437538 3454213 := bbase (se 4 (by rfl) ⟨323832, by rfl⟩ : syracuseStep 3454213 = 647665) (by norm_num)
theorem B1619221 : Blo 1437538 1619221 := bbase (se 6 (by rfl) ⟨37950, by rfl⟩ : syracuseStep 1619221 = 75901) (by norm_num)
theorem B1619257 : Blo 1437538 1619257 := bbase (se 2 (by rfl) ⟨607221, by rfl⟩ : syracuseStep 1619257 = 1214443) (by norm_num)
theorem B12285269 : Blo 1437538 12285269 := bbase (se 13 (by rfl) ⟨2249, by rfl⟩ : syracuseStep 12285269 = 4499) (by norm_num)
theorem B1619293 : Blo 1437538 1619293 := bbase (se 3 (by rfl) ⟨303617, by rfl⟩ : syracuseStep 1619293 = 607235) (by norm_num)
theorem B1619329 : Blo 1437538 1619329 := bbase (se 2 (by rfl) ⟨607248, by rfl⟩ : syracuseStep 1619329 = 1214497) (by norm_num)
theorem B4920725 : Blo 1437538 4920725 := bbase (se 6 (by rfl) ⟨115329, by rfl⟩ : syracuseStep 4920725 = 230659) (by norm_num)
theorem B1619365 : Blo 1437538 1619365 := bbase (se 4 (by rfl) ⟨151815, by rfl⟩ : syracuseStep 1619365 = 303631) (by norm_num)
theorem B1619401 : Blo 1437538 1619401 := bbase (se 2 (by rfl) ⟨607275, by rfl⟩ : syracuseStep 1619401 = 1214551) (by norm_num)
theorem B2627029 : Blo 1437538 2627029 := bbase (se 7 (by rfl) ⟨30785, by rfl⟩ : syracuseStep 2627029 = 61571) (by norm_num)
theorem B3642853 : Blo 1437538 3642853 := bbase (se 4 (by rfl) ⟨341517, by rfl⟩ : syracuseStep 3642853 = 683035) (by norm_num)
theorem B1619437 : Blo 1437538 1619437 := bbase (se 3 (by rfl) ⟨303644, by rfl⟩ : syracuseStep 1619437 = 607289) (by norm_num)
theorem B7280117 : Blo 1437538 7280117 := bbase (se 5 (by rfl) ⟨341255, by rfl⟩ : syracuseStep 7280117 = 682511) (by norm_num)
theorem B4855301 : Blo 1437538 4855301 := bbase (se 4 (by rfl) ⟨455184, by rfl⟩ : syracuseStep 4855301 = 910369) (by norm_num)
theorem B1619473 : Blo 1437538 1619473 := bbase (se 2 (by rfl) ⟨607302, by rfl⟩ : syracuseStep 1619473 = 1214605) (by norm_num)
theorem B3642965 : Blo 1437538 3642965 := bbase (se 8 (by rfl) ⟨21345, by rfl⟩ : syracuseStep 3642965 = 42691) (by norm_num)
theorem B6141541 : Blo 1437538 6141541 := bbase (se 4 (by rfl) ⟨575769, by rfl⟩ : syracuseStep 6141541 = 1151539) (by norm_num)
theorem B3454589 : Blo 1437538 3454589 := bbase (se 3 (by rfl) ⟨647735, by rfl⟩ : syracuseStep 3454589 = 1295471) (by norm_num)
theorem B3643157 : Blo 1437538 3643157 := bbase (se 6 (by rfl) ⟨85386, by rfl⟩ : syracuseStep 3643157 = 170773) (by norm_num)
theorem B9213749 : Blo 1437538 9213749 := bbase (se 5 (by rfl) ⟨431894, by rfl⟩ : syracuseStep 9213749 = 863789) (by norm_num)
theorem B3454829 : Blo 1437538 3454829 := bbase (se 3 (by rfl) ⟨647780, by rfl⟩ : syracuseStep 3454829 = 1295561) (by norm_num)
theorem B4855733 : Blo 1437538 4855733 := bbase (se 5 (by rfl) ⟨227612, by rfl⟩ : syracuseStep 4855733 = 455225) (by norm_num)
theorem B3282893 : Blo 1437538 3282893 := bbase (se 3 (by rfl) ⟨615542, by rfl⟩ : syracuseStep 3282893 = 1231085) (by norm_num)
theorem B2807765 : Blo 1437538 2807765 := bbase (se 7 (by rfl) ⟨32903, by rfl⟩ : syracuseStep 2807765 = 65807) (by norm_num)
theorem B4093973 : Blo 1437538 4093973 := bbase (se 6 (by rfl) ⟨95952, by rfl⟩ : syracuseStep 4093973 = 191905) (by norm_num)
theorem B4151333 : Blo 1437538 4151333 := bbase (se 4 (by rfl) ⟨389187, by rfl⟩ : syracuseStep 4151333 = 778375) (by norm_num)
theorem B3643501 : Blo 1437538 3643501 := bbase (se 3 (by rfl) ⟨683156, by rfl⟩ : syracuseStep 3643501 = 1366313) (by norm_num)
theorem B3643613 : Blo 1437538 3643613 := bbase (se 3 (by rfl) ⟨683177, by rfl⟩ : syracuseStep 3643613 = 1366355) (by norm_num)
theorem B5462261 : Blo 1437538 5462261 := bbase (se 5 (by rfl) ⟨256043, by rfl⟩ : syracuseStep 5462261 = 512087) (by norm_num)
theorem B4856165 : Blo 1437538 4856165 := bbase (se 4 (by rfl) ⟨455265, by rfl⟩ : syracuseStep 4856165 = 910531) (by norm_num)
theorem B3643805 : Blo 1437538 3643805 := bbase (se 3 (by rfl) ⟨683213, by rfl⟩ : syracuseStep 3643805 = 1366427) (by norm_num)
theorem B2628053 : Blo 1437538 2628053 := bbase (se 7 (by rfl) ⟨30797, by rfl⟩ : syracuseStep 2628053 = 61595) (by norm_num)
theorem B5257685 : Blo 1437538 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B5462549 : Blo 1437538 5462549 := bbase (se 6 (by rfl) ⟨128028, by rfl⟩ : syracuseStep 5462549 = 256057) (by norm_num)
theorem B3070541 : Blo 1437538 3070541 := bbase (se 3 (by rfl) ⟨575726, by rfl⟩ : syracuseStep 3070541 = 1151453) (by norm_num)
theorem B3234509 : Blo 1437538 3234509 := bbase (se 3 (by rfl) ⟨606470, by rfl⟩ : syracuseStep 3234509 = 1212941) (by norm_num)
theorem B3070685 : Blo 1437538 3070685 := bbase (se 3 (by rfl) ⟨575753, by rfl⟩ : syracuseStep 3070685 = 1151507) (by norm_num)
theorem B4094725 : Blo 1437538 4094725 := bbase (se 4 (by rfl) ⟨383880, by rfl⟩ : syracuseStep 4094725 = 767761) (by norm_num)
theorem B7281413 : Blo 1437538 7281413 := bbase (se 4 (by rfl) ⟨682632, by rfl⟩ : syracuseStep 7281413 = 1365265) (by norm_num)
theorem B6912773 : Blo 1437538 6912773 := bbase (se 4 (by rfl) ⟨648072, by rfl⟩ : syracuseStep 6912773 = 1296145) (by norm_num)
theorem B3234581 : Blo 1437538 3234581 := bbase (se 6 (by rfl) ⟨75810, by rfl⟩ : syracuseStep 3234581 = 151621) (by norm_num)
theorem B4856597 : Blo 1437538 4856597 := bbase (se 6 (by rfl) ⟨113826, by rfl⟩ : syracuseStep 4856597 = 227653) (by norm_num)
theorem B3234653 : Blo 1437538 3234653 := bbase (se 3 (by rfl) ⟨606497, by rfl⟩ : syracuseStep 3234653 = 1212995) (by norm_num)
theorem B3234725 : Blo 1437538 3234725 := bbase (se 4 (by rfl) ⟨303255, by rfl⟩ : syracuseStep 3234725 = 606511) (by norm_num)
theorem B1727453 : Blo 1437538 1727453 := bbase (se 3 (by rfl) ⟨323897, by rfl⟩ : syracuseStep 1727453 = 647795) (by norm_num)
theorem B3234797 : Blo 1437538 3234797 := bbase (se 3 (by rfl) ⟨606524, by rfl⟩ : syracuseStep 3234797 = 1213049) (by norm_num)
theorem B4611077 : Blo 1437538 4611077 := bbase (se 4 (by rfl) ⟨432288, by rfl⟩ : syracuseStep 4611077 = 864577) (by norm_num)
theorem B1727525 : Blo 1437538 1727525 := bbase (se 4 (by rfl) ⟨161955, by rfl⟩ : syracuseStep 1727525 = 323911) (by norm_num)
theorem B3234869 : Blo 1437538 3234869 := bbase (se 5 (by rfl) ⟨151634, by rfl⟩ : syracuseStep 3234869 = 303269) (by norm_num)
theorem B3234941 : Blo 1437538 3234941 := bbase (se 3 (by rfl) ⟨606551, by rfl⟩ : syracuseStep 3234941 = 1213103) (by norm_num)
theorem B2956429 : Blo 1437538 2956429 := bbase (se 3 (by rfl) ⟨554330, by rfl⟩ : syracuseStep 2956429 = 1108661) (by norm_num)
theorem B3235013 : Blo 1437538 3235013 := bbase (se 4 (by rfl) ⟨303282, by rfl⟩ : syracuseStep 3235013 = 606565) (by norm_num)
theorem B4857029 : Blo 1437538 4857029 := bbase (se 4 (by rfl) ⟨455346, by rfl⟩ : syracuseStep 4857029 = 910693) (by norm_num)
theorem B4668661 : Blo 1437538 4668661 := bbase (se 5 (by rfl) ⟨218843, by rfl⟩ : syracuseStep 4668661 = 437687) (by norm_num)
theorem B13122805 : Blo 1437538 13122805 := bbase (se 5 (by rfl) ⟨615131, by rfl⟩ : syracuseStep 13122805 = 1230263) (by norm_num)
theorem B3235085 : Blo 1437538 3235085 := bbase (se 3 (by rfl) ⟨606578, by rfl⟩ : syracuseStep 3235085 = 1213157) (by norm_num)
theorem B1457425 : Blo 1437538 1457425 := bbase (se 2 (by rfl) ⟨546534, by rfl⟩ : syracuseStep 1457425 = 1093069) (by norm_num)
theorem B3235157 : Blo 1437538 3235157 := bbase (se 11 (by rfl) ⟨2369, by rfl⟩ : syracuseStep 3235157 = 4739) (by norm_num)
theorem B1727833 : Blo 1437538 1727833 := bbase (se 2 (by rfl) ⟨647937, by rfl⟩ : syracuseStep 1727833 = 1295875) (by norm_num)
theorem B3235229 : Blo 1437538 3235229 := bbase (se 3 (by rfl) ⟨606605, by rfl⟩ : syracuseStep 3235229 = 1213211) (by norm_num)
theorem B2768293 : Blo 1437538 2768293 := bbase (se 4 (by rfl) ⟨259527, by rfl⟩ : syracuseStep 2768293 = 519055) (by norm_num)
theorem B3071429 : Blo 1437538 3071429 := bbase (se 4 (by rfl) ⟨287946, by rfl⟩ : syracuseStep 3071429 = 575893) (by norm_num)
theorem B3235301 : Blo 1437538 3235301 := bbase (se 4 (by rfl) ⟨303309, by rfl⟩ : syracuseStep 3235301 = 606619) (by norm_num)
theorem B1728001 : Blo 1437538 1728001 := bbase (se 2 (by rfl) ⟨648000, by rfl⟩ : syracuseStep 1728001 = 1296001) (by norm_num)
theorem B3939877 : Blo 1437538 3939877 := bbase (se 4 (by rfl) ⟨369363, by rfl⟩ : syracuseStep 3939877 = 738727) (by norm_num)
theorem B7380517 : Blo 1437538 7380517 := bbase (se 4 (by rfl) ⟨691923, by rfl⟩ : syracuseStep 7380517 = 1383847) (by norm_num)
theorem B3235373 : Blo 1437538 3235373 := bbase (se 3 (by rfl) ⟨606632, by rfl⟩ : syracuseStep 3235373 = 1213265) (by norm_num)
theorem B1728049 : Blo 1437538 1728049 := bbase (se 2 (by rfl) ⟨648018, by rfl⟩ : syracuseStep 1728049 = 1296037) (by norm_num)
theorem B3235445 : Blo 1437538 3235445 := bbase (se 5 (by rfl) ⟨151661, by rfl⟩ : syracuseStep 3235445 = 303323) (by norm_num)
theorem B4857461 : Blo 1437538 4857461 := bbase (se 5 (by rfl) ⟨227693, by rfl⟩ : syracuseStep 4857461 = 455387) (by norm_num)
theorem B1728145 : Blo 1437538 1728145 := bbase (se 2 (by rfl) ⟨648054, by rfl⟩ : syracuseStep 1728145 = 1296109) (by norm_num)
theorem B8191637 : Blo 1437538 8191637 := bbase (se 6 (by rfl) ⟨191991, by rfl⟩ : syracuseStep 8191637 = 383983) (by norm_num)
theorem B5463733 : Blo 1437538 5463733 := bbase (se 5 (by rfl) ⟨256112, by rfl⟩ : syracuseStep 5463733 = 512225) (by norm_num)
theorem B3235517 : Blo 1437538 3235517 := bbase (se 3 (by rfl) ⟨606659, by rfl⟩ : syracuseStep 3235517 = 1213319) (by norm_num)
theorem B2047693 : Blo 1437538 2047693 := bbase (se 3 (by rfl) ⟨383942, by rfl⟩ : syracuseStep 2047693 = 767885) (by norm_num)
theorem B3235589 : Blo 1437538 3235589 := bbase (se 4 (by rfl) ⟨303336, by rfl⟩ : syracuseStep 3235589 = 606673) (by norm_num)
theorem B2629397 : Blo 1437538 2629397 := bbase (se 6 (by rfl) ⟨61626, by rfl⟩ : syracuseStep 2629397 = 123253) (by norm_num)
theorem B5537605 : Blo 1437538 5537605 := bbase (se 4 (by rfl) ⟨519150, by rfl⟩ : syracuseStep 5537605 = 1038301) (by norm_num)
theorem B3235661 : Blo 1437538 3235661 := bbase (se 3 (by rfl) ⟨606686, by rfl⟩ : syracuseStep 3235661 = 1213373) (by norm_num)
theorem B3235733 : Blo 1437538 3235733 := bbase (se 6 (by rfl) ⟨75837, by rfl⟩ : syracuseStep 3235733 = 151675) (by norm_num)
theorem B14753717 : Blo 1437538 14753717 := bbase (se 5 (by rfl) ⟨691580, by rfl⟩ : syracuseStep 14753717 = 1383161) (by norm_num)
theorem B3235805 : Blo 1437538 3235805 := bbase (se 3 (by rfl) ⟨606713, by rfl⟩ : syracuseStep 3235805 = 1213427) (by norm_num)
theorem B5464037 : Blo 1437538 5464037 := bbase (se 4 (by rfl) ⟨512253, by rfl⟩ : syracuseStep 5464037 = 1024507) (by norm_num)
theorem B3743747 : Blo 1437538 3743747 := bstep (se 1 (by rfl) ⟨2807810, by rfl⟩ : syracuseStep 3743747 = 5615621) B5615621
theorem B2187329 : Blo 1437538 2187329 := bstep (se 2 (by rfl) ⟨820248, by rfl⟩ : syracuseStep 2187329 = 1640497) B1640497
theorem B5464205 : Blo 1437538 5464205 := bstep (se 3 (by rfl) ⟨1024538, by rfl⟩ : syracuseStep 5464205 = 2049077) B2049077
theorem B3235985 : Blo 1437538 3235985 := bstep (se 2 (by rfl) ⟨1213494, by rfl⟩ : syracuseStep 3235985 = 2426989) B2426989
theorem B4858001 : Blo 1437538 4858001 := bstep (se 2 (by rfl) ⟨1821750, by rfl⟩ : syracuseStep 4858001 = 3643501) B3643501
theorem B3236003 : Blo 1437538 3236003 := bstep (se 1 (by rfl) ⟨2427002, by rfl⟩ : syracuseStep 3236003 = 4854005) B4854005
theorem B2187427 : Blo 1437538 2187427 := bstep (se 1 (by rfl) ⟨1640570, by rfl⟩ : syracuseStep 2187427 = 3281141) B3281141
theorem B4096241 : Blo 1437538 4096241 := bstep (se 2 (by rfl) ⟨1536090, by rfl⟩ : syracuseStep 4096241 = 3072181) B3072181
theorem B2048257 : Blo 1437538 2048257 := bstep (se 2 (by rfl) ⟨768096, by rfl⟩ : syracuseStep 2048257 = 1536193) B1536193
theorem B2187665 : Blo 1437538 2187665 := bstep (se 2 (by rfl) ⟨820374, by rfl⟩ : syracuseStep 2187665 = 1640749) B1640749
theorem B3236273 : Blo 1437538 3236273 := bstep (se 2 (by rfl) ⟨1213602, by rfl⟩ : syracuseStep 3236273 = 2427205) B2427205
theorem B4096433 : Blo 1437538 4096433 := bstep (se 2 (by rfl) ⟨1536162, by rfl⟩ : syracuseStep 4096433 = 3072325) B3072325
theorem B3236291 : Blo 1437538 3236291 := bstep (se 1 (by rfl) ⟨2427218, by rfl⟩ : syracuseStep 3236291 = 4854437) B4854437
theorem B10920419 : Blo 1437538 10920419 := bstep (se 1 (by rfl) ⟨8190314, by rfl⟩ : syracuseStep 10920419 = 16380629) B16380629
theorem B4989443 : Blo 1437538 4989443 := bstep (se 1 (by rfl) ⟨3742082, by rfl⟩ : syracuseStep 4989443 = 7484165) B7484165
theorem B1458739 : Blo 1437538 1458739 := bstep (se 1 (by rfl) ⟨1094054, by rfl⟩ : syracuseStep 1458739 = 2188109) B2188109
theorem B2048593 : Blo 1437538 2048593 := bstep (se 2 (by rfl) ⟨768222, by rfl⟩ : syracuseStep 2048593 = 1536445) B1536445
theorem B3236561 : Blo 1437538 3236561 := bstep (se 2 (by rfl) ⟨1213710, by rfl⟩ : syracuseStep 3236561 = 2427421) B2427421
theorem B3236579 : Blo 1437538 3236579 := bstep (se 1 (by rfl) ⟨2427434, by rfl⟩ : syracuseStep 3236579 = 4854869) B4854869
theorem B2335475 : Blo 1437538 2335475 := bstep (se 1 (by rfl) ⟨1751606, by rfl⟩ : syracuseStep 2335475 = 3503213) B3503213
theorem B5186339 : Blo 1437538 5186339 := bstep (se 1 (by rfl) ⟨3889754, by rfl⟩ : syracuseStep 5186339 = 7779509) B7779509
theorem B2302771 : Blo 1437538 2302771 := bstep (se 1 (by rfl) ⟨1727078, by rfl⟩ : syracuseStep 2302771 = 3454157) B3454157
theorem B3113795 : Blo 1437538 3113795 := bstep (se 1 (by rfl) ⟨2335346, by rfl⟩ : syracuseStep 3113795 = 4670693) B4670693
theorem B1819523 : Blo 1437538 1819523 := bstep (se 1 (by rfl) ⟨1364642, by rfl⟩ : syracuseStep 1819523 = 2729285) B2729285
theorem B5465009 : Blo 1437538 5465009 := bstep (se 2 (by rfl) ⟨2049378, by rfl⟩ : syracuseStep 5465009 = 4098757) B4098757
theorem B12288995 : Blo 1437538 12288995 := bstep (se 1 (by rfl) ⟨9216746, by rfl⟩ : syracuseStep 12288995 = 18433493) B18433493
theorem B3236849 : Blo 1437538 3236849 := bstep (se 2 (by rfl) ⟨1213818, by rfl⟩ : syracuseStep 3236849 = 2427637) B2427637
theorem B3236867 : Blo 1437538 3236867 := bstep (se 1 (by rfl) ⟨2427650, by rfl⟩ : syracuseStep 3236867 = 4855301) B4855301
theorem B2425889 : Blo 1437538 2425889 := bstep (se 2 (by rfl) ⟨909708, by rfl⟩ : syracuseStep 2425889 = 1819417) B1819417
theorem B5538893 : Blo 1437538 5538893 := bstep (se 3 (by rfl) ⟨1038542, by rfl⟩ : syracuseStep 5538893 = 2077085) B2077085
theorem B4375633 : Blo 1437538 4375633 := bstep (se 2 (by rfl) ⟨1640862, by rfl⟩ : syracuseStep 4375633 = 3281725) B3281725
theorem B2426017 : Blo 1437538 2426017 := bstep (se 2 (by rfl) ⟨909756, by rfl⟩ : syracuseStep 2426017 = 1819513) B1819513
theorem B2049185 : Blo 1437538 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B2426051 : Blo 1437538 2426051 := bstep (se 1 (by rfl) ⟨1819538, by rfl⟩ : syracuseStep 2426051 = 3639077) B3639077
theorem B2303219 : Blo 1437538 2303219 := bstep (se 1 (by rfl) ⟨1727414, by rfl⟩ : syracuseStep 2303219 = 3454829) B3454829
theorem B3237137 : Blo 1437538 3237137 := bstep (se 2 (by rfl) ⟨1213926, by rfl⟩ : syracuseStep 3237137 = 2427853) B2427853
theorem B3237155 : Blo 1437538 3237155 := bstep (se 1 (by rfl) ⟨2427866, by rfl⟩ : syracuseStep 3237155 = 4855733) B4855733
theorem B2188595 : Blo 1437538 2188595 := bstep (se 1 (by rfl) ⟨1641446, by rfl⟩ : syracuseStep 2188595 = 3282893) B3282893
theorem B2426179 : Blo 1437538 2426179 := bstep (se 1 (by rfl) ⟨1819634, by rfl⟩ : syracuseStep 2426179 = 3639269) B3639269
theorem B2729315 : Blo 1437538 2729315 := bstep (se 1 (by rfl) ⟨2046986, by rfl⟩ : syracuseStep 2729315 = 4093973) B4093973
theorem B8193413 : Blo 1437538 8193413 := bstep (se 4 (by rfl) ⟨768132, by rfl⟩ : syracuseStep 8193413 = 1536265) B1536265
theorem B4097425 : Blo 1437538 4097425 := bstep (se 2 (by rfl) ⟨1536534, by rfl⟩ : syracuseStep 4097425 = 3073069) B3073069
theorem B2917795 : Blo 1437538 2917795 := bstep (se 1 (by rfl) ⟨2188346, by rfl⟩ : syracuseStep 2917795 = 4376693) B4376693
theorem B2426321 : Blo 1437538 2426321 := bstep (se 2 (by rfl) ⟨909870, by rfl⟩ : syracuseStep 2426321 = 1819741) B1819741
theorem B3941905 : Blo 1437538 3941905 := bstep (se 2 (by rfl) ⟨1478214, by rfl⟩ : syracuseStep 3941905 = 2956429) B2956429
theorem B3237425 : Blo 1437538 3237425 := bstep (se 2 (by rfl) ⟨1214034, by rfl⟩ : syracuseStep 3237425 = 2428069) B2428069
theorem B1820227 : Blo 1437538 1820227 := bstep (se 1 (by rfl) ⟨1365170, by rfl⟩ : syracuseStep 1820227 = 2730341) B2730341
theorem B3237443 : Blo 1437538 3237443 := bstep (se 1 (by rfl) ⟨2428082, by rfl⟩ : syracuseStep 3237443 = 4856165) B4856165
theorem B5465677 : Blo 1437538 5465677 := bstep (se 3 (by rfl) ⟨1024814, by rfl⟩ : syracuseStep 5465677 = 2049629) B2049629
theorem B2426449 : Blo 1437538 2426449 := bstep (se 2 (by rfl) ⟨909918, by rfl⟩ : syracuseStep 2426449 = 1819837) B1819837
theorem B5834339 : Blo 1437538 5834339 := bstep (se 1 (by rfl) ⟨4375754, by rfl⟩ : syracuseStep 5834339 = 8751509) B8751509
theorem B2426483 : Blo 1437538 2426483 := bstep (se 1 (by rfl) ⟨1819862, by rfl⟩ : syracuseStep 2426483 = 3639725) B3639725
theorem B3638915 : Blo 1437538 3638915 := bstep (se 1 (by rfl) ⟨2729186, by rfl⟩ : syracuseStep 3638915 = 5458373) B5458373
theorem B2459297 : Blo 1437538 2459297 := bstep (se 2 (by rfl) ⟨922236, by rfl⟩ : syracuseStep 2459297 = 1844473) B1844473
theorem B1820323 : Blo 1437538 1820323 := bstep (se 1 (by rfl) ⟨1365242, by rfl⟩ : syracuseStep 1820323 = 2730485) B2730485
theorem B4097699 : Blo 1437538 4097699 := bstep (se 1 (by rfl) ⟨3073274, by rfl⟩ : syracuseStep 4097699 = 6146549) B6146549
theorem B4605617 : Blo 1437538 4605617 := bstep (se 2 (by rfl) ⟨1727106, by rfl⟩ : syracuseStep 4605617 = 3454213) B3454213
theorem B1943233 : Blo 1437538 1943233 := bstep (se 2 (by rfl) ⟨728712, by rfl⟩ : syracuseStep 1943233 = 1457425) B1457425
theorem B2426611 : Blo 1437538 2426611 := bstep (se 1 (by rfl) ⟨1819958, by rfl⟩ : syracuseStep 2426611 = 3639917) B3639917
theorem B2156321 : Blo 1437538 2156321 := bstep (se 2 (by rfl) ⟨808620, by rfl⟩ : syracuseStep 2156321 = 1617241) B1617241
theorem B2303777 : Blo 1437538 2303777 := bstep (se 2 (by rfl) ⟨863916, by rfl⟩ : syracuseStep 2303777 = 1727833) B1727833
theorem B2156339 : Blo 1437538 2156339 := bstep (se 1 (by rfl) ⟨1617254, by rfl⟩ : syracuseStep 2156339 = 3234509) B3234509
theorem B3639107 : Blo 1437538 3639107 := bstep (se 1 (by rfl) ⟨2729330, by rfl⟩ : syracuseStep 3639107 = 5458661) B5458661
theorem B8193869 : Blo 1437538 8193869 := bstep (se 3 (by rfl) ⟨1536350, by rfl⟩ : syracuseStep 8193869 = 3072701) B3072701
theorem B2156369 : Blo 1437538 2156369 := bstep (se 2 (by rfl) ⟨808638, by rfl⟩ : syracuseStep 2156369 = 1617277) B1617277
theorem B3237713 : Blo 1437538 3237713 := bstep (se 2 (by rfl) ⟨1214142, by rfl⟩ : syracuseStep 3237713 = 2428285) B2428285
theorem B2156387 : Blo 1437538 2156387 := bstep (se 1 (by rfl) ⟨1617290, by rfl⟩ : syracuseStep 2156387 = 3234581) B3234581
theorem B3237731 : Blo 1437538 3237731 := bstep (se 1 (by rfl) ⟨2428298, by rfl⟩ : syracuseStep 3237731 = 4856597) B4856597
theorem B4097891 : Blo 1437538 4097891 := bstep (se 1 (by rfl) ⟨3073418, by rfl⟩ : syracuseStep 4097891 = 6146837) B6146837
theorem B16377713 : Blo 1437538 16377713 := bstep (se 2 (by rfl) ⟨6141642, by rfl⟩ : syracuseStep 16377713 = 12283285) B12283285
theorem B2156417 : Blo 1437538 2156417 := bstep (se 2 (by rfl) ⟨808656, by rfl⟩ : syracuseStep 2156417 = 1617313) B1617313
theorem B2426753 : Blo 1437538 2426753 := bstep (se 2 (by rfl) ⟨910032, by rfl⟩ : syracuseStep 2426753 = 1820065) B1820065
theorem B2156435 : Blo 1437538 2156435 := bstep (se 1 (by rfl) ⟨1617326, by rfl⟩ : syracuseStep 2156435 = 3234653) B3234653
theorem B2156465 : Blo 1437538 2156465 := bstep (se 2 (by rfl) ⟨808674, by rfl⟩ : syracuseStep 2156465 = 1617349) B1617349
theorem B2156483 : Blo 1437538 2156483 := bstep (se 1 (by rfl) ⟨1617362, by rfl⟩ : syracuseStep 2156483 = 3234725) B3234725
theorem B2156513 : Blo 1437538 2156513 := bstep (se 2 (by rfl) ⟨808692, by rfl⟩ : syracuseStep 2156513 = 1617385) B1617385
theorem B2156531 : Blo 1437538 2156531 := bstep (se 1 (by rfl) ⟨1617398, by rfl⟩ : syracuseStep 2156531 = 3234797) B3234797
theorem B2426881 : Blo 1437538 2426881 := bstep (se 2 (by rfl) ⟨910080, by rfl⟩ : syracuseStep 2426881 = 1820161) B1820161
theorem B2304001 : Blo 1437538 2304001 := bstep (se 2 (by rfl) ⟨864000, by rfl⟩ : syracuseStep 2304001 = 1728001) B1728001
theorem B3074051 : Blo 1437538 3074051 := bstep (se 1 (by rfl) ⟨2305538, by rfl⟩ : syracuseStep 3074051 = 4611077) B4611077
theorem B2156561 : Blo 1437538 2156561 := bstep (se 2 (by rfl) ⟨808710, by rfl⟩ : syracuseStep 2156561 = 1617421) B1617421
theorem B2156579 : Blo 1437538 2156579 := bstep (se 1 (by rfl) ⟨1617434, by rfl⟩ : syracuseStep 2156579 = 3234869) B3234869
theorem B2426915 : Blo 1437538 2426915 := bstep (se 1 (by rfl) ⟨1820186, by rfl⟩ : syracuseStep 2426915 = 3640373) B3640373
theorem B5253169 : Blo 1437538 5253169 := bstep (se 2 (by rfl) ⟨1969938, by rfl⟩ : syracuseStep 5253169 = 3939877) B3939877
theorem B9840689 : Blo 1437538 9840689 := bstep (se 2 (by rfl) ⟨3690258, by rfl⟩ : syracuseStep 9840689 = 7380517) B7380517
theorem B2156609 : Blo 1437538 2156609 := bstep (se 2 (by rfl) ⟨808728, by rfl⟩ : syracuseStep 2156609 = 1617457) B1617457
theorem B2304065 : Blo 1437538 2304065 := bstep (se 2 (by rfl) ⟨864024, by rfl⟩ : syracuseStep 2304065 = 1728049) B1728049
theorem B2156627 : Blo 1437538 2156627 := bstep (se 1 (by rfl) ⟨1617470, by rfl⟩ : syracuseStep 2156627 = 3234941) B3234941
theorem B2156657 : Blo 1437538 2156657 := bstep (se 2 (by rfl) ⟨808746, by rfl⟩ : syracuseStep 2156657 = 1617493) B1617493
theorem B3238001 : Blo 1437538 3238001 := bstep (se 2 (by rfl) ⟨1214250, by rfl⟩ : syracuseStep 3238001 = 2428501) B2428501
theorem B2156675 : Blo 1437538 2156675 := bstep (se 1 (by rfl) ⟨1617506, by rfl⟩ : syracuseStep 2156675 = 3235013) B3235013
theorem B3238019 : Blo 1437538 3238019 := bstep (se 1 (by rfl) ⟨2428514, by rfl⟩ : syracuseStep 3238019 = 4857029) B4857029
theorem B6146189 : Blo 1437538 6146189 := bstep (se 3 (by rfl) ⟨1152410, by rfl⟩ : syracuseStep 6146189 = 2304821) B2304821
theorem B15558797 : Blo 1437538 15558797 := bstep (se 3 (by rfl) ⟨2917274, by rfl⟩ : syracuseStep 15558797 = 5834549) B5834549
theorem B1820819 : Blo 1437538 1820819 := bstep (se 1 (by rfl) ⟨1365614, by rfl⟩ : syracuseStep 1820819 = 2731229) B2731229
theorem B2156705 : Blo 1437538 2156705 := bstep (se 2 (by rfl) ⟨808764, by rfl⟩ : syracuseStep 2156705 = 1617529) B1617529
theorem B2427043 : Blo 1437538 2427043 := bstep (se 1 (by rfl) ⟨1820282, by rfl⟩ : syracuseStep 2427043 = 3640565) B3640565
theorem B2156723 : Blo 1437538 2156723 := bstep (se 1 (by rfl) ⟨1617542, by rfl⟩ : syracuseStep 2156723 = 3235085) B3235085
theorem B2304193 : Blo 1437538 2304193 := bstep (se 2 (by rfl) ⟨864072, by rfl⟩ : syracuseStep 2304193 = 1728145) B1728145
theorem B2156753 : Blo 1437538 2156753 := bstep (se 2 (by rfl) ⟨808782, by rfl⟩ : syracuseStep 2156753 = 1617565) B1617565
theorem B2156771 : Blo 1437538 2156771 := bstep (se 1 (by rfl) ⟨1617578, by rfl⟩ : syracuseStep 2156771 = 3235157) B3235157
theorem B4851953 : Blo 1437538 4851953 := bstep (se 2 (by rfl) ⟨1819482, by rfl⟩ : syracuseStep 4851953 = 3638965) B3638965
theorem B7284977 : Blo 1437538 7284977 := bstep (se 2 (by rfl) ⟨2731866, by rfl⟩ : syracuseStep 7284977 = 5463733) B5463733
theorem B2156801 : Blo 1437538 2156801 := bstep (se 2 (by rfl) ⟨808800, by rfl⟩ : syracuseStep 2156801 = 1617601) B1617601
theorem B2730257 : Blo 1437538 2730257 := bstep (se 2 (by rfl) ⟨1023846, by rfl⟩ : syracuseStep 2730257 = 2047693) B2047693
theorem B2156819 : Blo 1437538 2156819 := bstep (se 1 (by rfl) ⟨1617614, by rfl⟩ : syracuseStep 2156819 = 3235229) B3235229
theorem B2156849 : Blo 1437538 2156849 := bstep (se 2 (by rfl) ⟨808818, by rfl⟩ : syracuseStep 2156849 = 1617637) B1617637
theorem B2427185 : Blo 1437538 2427185 := bstep (se 2 (by rfl) ⟨910194, by rfl⟩ : syracuseStep 2427185 = 1820389) B1820389
theorem B2156867 : Blo 1437538 2156867 := bstep (se 1 (by rfl) ⟨1617650, by rfl⟩ : syracuseStep 2156867 = 3235301) B3235301
theorem B2156897 : Blo 1437538 2156897 := bstep (se 2 (by rfl) ⟨808836, by rfl⟩ : syracuseStep 2156897 = 1617673) B1617673
theorem B6908273 : Blo 1437538 6908273 := bstep (se 2 (by rfl) ⟨2590602, by rfl⟩ : syracuseStep 6908273 = 5181205) B5181205
theorem B2156915 : Blo 1437538 2156915 := bstep (se 1 (by rfl) ⟨1617686, by rfl⟩ : syracuseStep 2156915 = 3235373) B3235373
theorem B5540237 : Blo 1437538 5540237 := bstep (se 3 (by rfl) ⟨1038794, by rfl⟩ : syracuseStep 5540237 = 2077589) B2077589
theorem B2156945 : Blo 1437538 2156945 := bstep (se 2 (by rfl) ⟨808854, by rfl⟩ : syracuseStep 2156945 = 1617709) B1617709
theorem B3238289 : Blo 1437538 3238289 := bstep (se 2 (by rfl) ⟨1214358, by rfl⟩ : syracuseStep 3238289 = 2428717) B2428717
theorem B2156963 : Blo 1437538 2156963 := bstep (se 1 (by rfl) ⟨1617722, by rfl⟩ : syracuseStep 2156963 = 3235445) B3235445
theorem B3238307 : Blo 1437538 3238307 := bstep (se 1 (by rfl) ⟨2428730, by rfl⟩ : syracuseStep 3238307 = 4857461) B4857461
theorem B2427313 : Blo 1437538 2427313 := bstep (se 2 (by rfl) ⟨910242, by rfl⟩ : syracuseStep 2427313 = 1820485) B1820485
theorem B7383473 : Blo 1437538 7383473 := bstep (se 2 (by rfl) ⟨2768802, by rfl⟩ : syracuseStep 7383473 = 5537605) B5537605
theorem B2156993 : Blo 1437538 2156993 := bstep (se 2 (by rfl) ⟨808872, by rfl⟩ : syracuseStep 2156993 = 1617745) B1617745
theorem B2157011 : Blo 1437538 2157011 := bstep (se 1 (by rfl) ⟨1617758, by rfl⟩ : syracuseStep 2157011 = 3235517) B3235517
theorem B2427347 : Blo 1437538 2427347 := bstep (se 1 (by rfl) ⟨1820510, by rfl⟩ : syracuseStep 2427347 = 3641021) B3641021
theorem B2157041 : Blo 1437538 2157041 := bstep (se 2 (by rfl) ⟨808890, by rfl⟩ : syracuseStep 2157041 = 1617781) B1617781
theorem B2460145 : Blo 1437538 2460145 := bstep (se 2 (by rfl) ⟨922554, by rfl⟩ : syracuseStep 2460145 = 1845109) B1845109
theorem B2157059 : Blo 1437538 2157059 := bstep (se 1 (by rfl) ⟨1617794, by rfl⟩ : syracuseStep 2157059 = 3235589) B3235589
theorem B2157089 : Blo 1437538 2157089 := bstep (se 2 (by rfl) ⟨808908, by rfl⟩ : syracuseStep 2157089 = 1617817) B1617817
theorem B2157107 : Blo 1437538 2157107 := bstep (se 1 (by rfl) ⟨1617830, by rfl⟩ : syracuseStep 2157107 = 3235661) B3235661
theorem B4606541 : Blo 1437538 4606541 := bstep (se 3 (by rfl) ⟨863726, by rfl⟩ : syracuseStep 4606541 = 1727453) B1727453
theorem B2157137 : Blo 1437538 2157137 := bstep (se 2 (by rfl) ⟨808926, by rfl⟩ : syracuseStep 2157137 = 1617853) B1617853
theorem B2427475 : Blo 1437538 2427475 := bstep (se 1 (by rfl) ⟨1820606, by rfl⟩ : syracuseStep 2427475 = 3641213) B3641213
theorem B2157155 : Blo 1437538 2157155 := bstep (se 1 (by rfl) ⟨1617866, by rfl⟩ : syracuseStep 2157155 = 3235733) B3235733
theorem B2157185 : Blo 1437538 2157185 := bstep (se 2 (by rfl) ⟨808944, by rfl⟩ : syracuseStep 2157185 = 1617889) B1617889
theorem B4098701 : Blo 1437538 4098701 := bstep (se 3 (by rfl) ⟨768506, by rfl⟩ : syracuseStep 4098701 = 1537013) B1537013
theorem B2157203 : Blo 1437538 2157203 := bstep (se 1 (by rfl) ⟨1617902, by rfl⟩ : syracuseStep 2157203 = 3235805) B3235805
theorem B2157233 : Blo 1437538 2157233 := bstep (se 2 (by rfl) ⟨808962, by rfl⟩ : syracuseStep 2157233 = 1617925) B1617925
theorem B3238577 : Blo 1437538 3238577 := bstep (se 2 (by rfl) ⟨1214466, by rfl⟩ : syracuseStep 3238577 = 2428933) B2428933
theorem B2157251 : Blo 1437538 2157251 := bstep (se 1 (by rfl) ⟨1617938, by rfl⟩ : syracuseStep 2157251 = 3235877) B3235877
theorem B3238595 : Blo 1437538 3238595 := bstep (se 1 (by rfl) ⟨2428946, by rfl⟩ : syracuseStep 3238595 = 4857893) B4857893
theorem B2157281 : Blo 1437538 2157281 := bstep (se 2 (by rfl) ⟨808980, by rfl⟩ : syracuseStep 2157281 = 1617961) B1617961
theorem B2427617 : Blo 1437538 2427617 := bstep (se 2 (by rfl) ⟨910356, by rfl⟩ : syracuseStep 2427617 = 1820713) B1820713
theorem B3640049 : Blo 1437538 3640049 := bstep (se 2 (by rfl) ⟨1365018, by rfl⟩ : syracuseStep 3640049 = 2730037) B2730037
theorem B7990001 : Blo 1437538 7990001 := bstep (se 2 (by rfl) ⟨2996250, by rfl⟩ : syracuseStep 7990001 = 5992501) B5992501
theorem B2157299 : Blo 1437538 2157299 := bstep (se 1 (by rfl) ⟨1617974, by rfl⟩ : syracuseStep 2157299 = 3235949) B3235949
theorem B4852493 : Blo 1437538 4852493 := bstep (se 3 (by rfl) ⟨909842, by rfl⟩ : syracuseStep 4852493 = 1819685) B1819685
theorem B4606733 : Blo 1437538 4606733 := bstep (se 3 (by rfl) ⟨863762, by rfl⟩ : syracuseStep 4606733 = 1727525) B1727525
theorem B2157329 : Blo 1437538 2157329 := bstep (se 2 (by rfl) ⟨808998, by rfl⟩ : syracuseStep 2157329 = 1617997) B1617997
theorem B3640099 : Blo 1437538 3640099 := bstep (se 1 (by rfl) ⟨2730074, by rfl⟩ : syracuseStep 3640099 = 5460149) B5460149
theorem B2157347 : Blo 1437538 2157347 := bstep (se 1 (by rfl) ⟨1618010, by rfl⟩ : syracuseStep 2157347 = 3236021) B3236021
theorem B2157377 : Blo 1437538 2157377 := bstep (se 2 (by rfl) ⟨809016, by rfl⟩ : syracuseStep 2157377 = 1618033) B1618033
theorem B4852547 : Blo 1437538 4852547 := bstep (se 1 (by rfl) ⟨3639410, by rfl⟩ : syracuseStep 4852547 = 7278821) B7278821
theorem B4098883 : Blo 1437538 4098883 := bstep (se 1 (by rfl) ⟨3074162, by rfl⟩ : syracuseStep 4098883 = 6148325) B6148325
theorem B2157395 : Blo 1437538 2157395 := bstep (se 1 (by rfl) ⟨1618046, by rfl⟩ : syracuseStep 2157395 = 3236093) B3236093
theorem B2460499 : Blo 1437538 2460499 := bstep (se 1 (by rfl) ⟨1845374, by rfl⟩ : syracuseStep 2460499 = 3690749) B3690749
theorem B1821523 : Blo 1437538 1821523 := bstep (se 1 (by rfl) ⟨1366142, by rfl⟩ : syracuseStep 1821523 = 2732285) B2732285
theorem B2427745 : Blo 1437538 2427745 := bstep (se 2 (by rfl) ⟨910404, by rfl⟩ : syracuseStep 2427745 = 1820809) B1820809
theorem B8096611 : Blo 1437538 8096611 := bstep (se 1 (by rfl) ⟨6072458, by rfl⟩ : syracuseStep 8096611 = 12144917) B12144917
theorem B2157425 : Blo 1437538 2157425 := bstep (se 2 (by rfl) ⟨809034, by rfl⟩ : syracuseStep 2157425 = 1618069) B1618069
theorem B2157443 : Blo 1437538 2157443 := bstep (se 1 (by rfl) ⟨1618082, by rfl⟩ : syracuseStep 2157443 = 3236165) B3236165
theorem B2427779 : Blo 1437538 2427779 := bstep (se 1 (by rfl) ⟨1820834, by rfl⟩ : syracuseStep 2427779 = 3641669) B3641669
theorem B2157473 : Blo 1437538 2157473 := bstep (se 2 (by rfl) ⟨809052, by rfl⟩ : syracuseStep 2157473 = 1618105) B1618105
theorem B3640241 : Blo 1437538 3640241 := bstep (se 2 (by rfl) ⟨1365090, by rfl⟩ : syracuseStep 3640241 = 2730181) B2730181
theorem B2157491 : Blo 1437538 2157491 := bstep (se 1 (by rfl) ⟨1618118, by rfl⟩ : syracuseStep 2157491 = 3236237) B3236237
theorem B1821619 : Blo 1437538 1821619 := bstep (se 1 (by rfl) ⟨1366214, by rfl⟩ : syracuseStep 1821619 = 2732429) B2732429
theorem B2157521 : Blo 1437538 2157521 := bstep (se 2 (by rfl) ⟨809070, by rfl⟩ : syracuseStep 2157521 = 1618141) B1618141
theorem B3238865 : Blo 1437538 3238865 := bstep (se 2 (by rfl) ⟨1214574, by rfl⟩ : syracuseStep 3238865 = 2429149) B2429149
theorem B2157539 : Blo 1437538 2157539 := bstep (se 1 (by rfl) ⟨1618154, by rfl⟩ : syracuseStep 2157539 = 3236309) B3236309
theorem B3238883 : Blo 1437538 3238883 := bstep (se 1 (by rfl) ⟨2429162, by rfl⟩ : syracuseStep 3238883 = 4858325) B4858325
theorem B2157569 : Blo 1437538 2157569 := bstep (se 2 (by rfl) ⟨809088, by rfl⟩ : syracuseStep 2157569 = 1618177) B1618177
theorem B2427907 : Blo 1437538 2427907 := bstep (se 1 (by rfl) ⟨1820930, by rfl⟩ : syracuseStep 2427907 = 3641861) B3641861
theorem B2157587 : Blo 1437538 2157587 := bstep (se 1 (by rfl) ⟨1618190, by rfl⟩ : syracuseStep 2157587 = 3236381) B3236381
theorem B2157617 : Blo 1437538 2157617 := bstep (se 2 (by rfl) ⟨809106, by rfl⟩ : syracuseStep 2157617 = 1618213) B1618213
theorem B2157635 : Blo 1437538 2157635 := bstep (se 1 (by rfl) ⟨1618226, by rfl⟩ : syracuseStep 2157635 = 3236453) B3236453
theorem B4852817 : Blo 1437538 4852817 := bstep (se 2 (by rfl) ⟨1819806, by rfl⟩ : syracuseStep 4852817 = 3639613) B3639613
theorem B2157665 : Blo 1437538 2157665 := bstep (se 2 (by rfl) ⟨809124, by rfl⟩ : syracuseStep 2157665 = 1618249) B1618249
theorem B2157683 : Blo 1437538 2157683 := bstep (se 1 (by rfl) ⟨1618262, by rfl⟩ : syracuseStep 2157683 = 3236525) B3236525
theorem B3689603 : Blo 1437538 3689603 := bstep (se 1 (by rfl) ⟨2767202, by rfl⟩ : syracuseStep 3689603 = 5534405) B5534405
theorem B3845251 : Blo 1437538 3845251 := bstep (se 1 (by rfl) ⟨2883938, by rfl⟩ : syracuseStep 3845251 = 5767877) B5767877
theorem B2157713 : Blo 1437538 2157713 := bstep (se 2 (by rfl) ⟨809142, by rfl⟩ : syracuseStep 2157713 = 1618285) B1618285
theorem B2731153 : Blo 1437538 2731153 := bstep (se 2 (by rfl) ⟨1024182, by rfl⟩ : syracuseStep 2731153 = 2048365) B2048365
theorem B2428049 : Blo 1437538 2428049 := bstep (se 2 (by rfl) ⟨910518, by rfl⟩ : syracuseStep 2428049 = 1821037) B1821037
theorem B2157731 : Blo 1437538 2157731 := bstep (se 1 (by rfl) ⟨1618298, by rfl⟩ : syracuseStep 2157731 = 3236597) B3236597
theorem B2157761 : Blo 1437538 2157761 := bstep (se 2 (by rfl) ⟨809160, by rfl⟩ : syracuseStep 2157761 = 1618321) B1618321
theorem B2157779 : Blo 1437538 2157779 := bstep (se 1 (by rfl) ⟨1618334, by rfl⟩ : syracuseStep 2157779 = 3236669) B3236669
theorem B2157809 : Blo 1437538 2157809 := bstep (se 2 (by rfl) ⟨809178, by rfl⟩ : syracuseStep 2157809 = 1618357) B1618357
theorem B2157827 : Blo 1437538 2157827 := bstep (se 1 (by rfl) ⟨1618370, by rfl⟩ : syracuseStep 2157827 = 3236741) B3236741
theorem B2428177 : Blo 1437538 2428177 := bstep (se 2 (by rfl) ⟨910566, by rfl⟩ : syracuseStep 2428177 = 1821133) B1821133
theorem B2157857 : Blo 1437538 2157857 := bstep (se 2 (by rfl) ⟨809196, by rfl⟩ : syracuseStep 2157857 = 1618393) B1618393
theorem B2731313 : Blo 1437538 2731313 := bstep (se 2 (by rfl) ⟨1024242, by rfl⟩ : syracuseStep 2731313 = 2048485) B2048485
theorem B2157875 : Blo 1437538 2157875 := bstep (se 1 (by rfl) ⟨1618406, by rfl⟩ : syracuseStep 2157875 = 3236813) B3236813
theorem B2428211 : Blo 1437538 2428211 := bstep (se 1 (by rfl) ⟨1821158, by rfl⟩ : syracuseStep 2428211 = 3642317) B3642317
theorem B2157905 : Blo 1437538 2157905 := bstep (se 2 (by rfl) ⟨809214, by rfl⟩ : syracuseStep 2157905 = 1618429) B1618429
theorem B2157923 : Blo 1437538 2157923 := bstep (se 1 (by rfl) ⟨1618442, by rfl⟩ : syracuseStep 2157923 = 3236885) B3236885
theorem B2157953 : Blo 1437538 2157953 := bstep (se 2 (by rfl) ⟨809232, by rfl⟩ : syracuseStep 2157953 = 1618465) B1618465
theorem B2157971 : Blo 1437538 2157971 := bstep (se 1 (by rfl) ⟨1618478, by rfl⟩ : syracuseStep 2157971 = 3236957) B3236957
theorem B2158001 : Blo 1437538 2158001 := bstep (se 2 (by rfl) ⟨809250, by rfl⟩ : syracuseStep 2158001 = 1618501) B1618501
theorem B1617331 : Blo 1437538 1617331 := bstep (se 1 (by rfl) ⟨1212998, by rfl⟩ : syracuseStep 1617331 = 2425997) B2425997
theorem B2493875 : Blo 1437538 2493875 := bstep (se 1 (by rfl) ⟨1870406, by rfl⟩ : syracuseStep 2493875 = 3740813) B3740813
theorem B2428339 : Blo 1437538 2428339 := bstep (se 1 (by rfl) ⟨1821254, by rfl⟩ : syracuseStep 2428339 = 3642509) B3642509
theorem B2158019 : Blo 1437538 2158019 := bstep (se 1 (by rfl) ⟨1618514, by rfl⟩ : syracuseStep 2158019 = 3237029) B3237029
theorem B2158049 : Blo 1437538 2158049 := bstep (se 2 (by rfl) ⟨809268, by rfl⟩ : syracuseStep 2158049 = 1618537) B1618537
theorem B8752625 : Blo 1437538 8752625 := bstep (se 2 (by rfl) ⟨3282234, by rfl⟩ : syracuseStep 8752625 = 6564469) B6564469
theorem B2158067 : Blo 1437538 2158067 := bstep (se 1 (by rfl) ⟨1618550, by rfl⟩ : syracuseStep 2158067 = 3237101) B3237101
theorem B2158097 : Blo 1437538 2158097 := bstep (se 2 (by rfl) ⟨809286, by rfl⟩ : syracuseStep 2158097 = 1618573) B1618573
theorem B2158115 : Blo 1437538 2158115 := bstep (se 1 (by rfl) ⟨1618586, by rfl⟩ : syracuseStep 2158115 = 3237173) B3237173
theorem B2158145 : Blo 1437538 2158145 := bstep (se 2 (by rfl) ⟨809304, by rfl⟩ : syracuseStep 2158145 = 1618609) B1618609
theorem B2428481 : Blo 1437538 2428481 := bstep (se 2 (by rfl) ⟨910680, by rfl⟩ : syracuseStep 2428481 = 1821361) B1821361
theorem B1617475 : Blo 1437538 1617475 := bstep (se 1 (by rfl) ⟨1213106, by rfl⟩ : syracuseStep 1617475 = 2426213) B2426213
theorem B2158163 : Blo 1437538 2158163 := bstep (se 1 (by rfl) ⟨1618622, by rfl⟩ : syracuseStep 2158163 = 3237245) B3237245
theorem B3280483 : Blo 1437538 3280483 := bstep (se 1 (by rfl) ⟨2460362, by rfl⟩ : syracuseStep 3280483 = 4920725) B4920725
theorem B4853357 : Blo 1437538 4853357 := bstep (se 3 (by rfl) ⟨910004, by rfl⟩ : syracuseStep 4853357 = 1820009) B1820009
theorem B2158193 : Blo 1437538 2158193 := bstep (se 2 (by rfl) ⟨809322, by rfl⟩ : syracuseStep 2158193 = 1618645) B1618645
theorem B2158211 : Blo 1437538 2158211 := bstep (se 1 (by rfl) ⟨1618658, by rfl⟩ : syracuseStep 2158211 = 3237317) B3237317
theorem B2158241 : Blo 1437538 2158241 := bstep (se 2 (by rfl) ⟨809340, by rfl⟩ : syracuseStep 2158241 = 1618681) B1618681
theorem B4853411 : Blo 1437538 4853411 := bstep (se 1 (by rfl) ⟨3640058, by rfl⟩ : syracuseStep 4853411 = 7280117) B7280117
theorem B7286435 : Blo 1437538 7286435 := bstep (se 1 (by rfl) ⟨5464826, by rfl⟩ : syracuseStep 7286435 = 10929653) B10929653
theorem B5459633 : Blo 1437538 5459633 := bstep (se 2 (by rfl) ⟨2047362, by rfl⟩ : syracuseStep 5459633 = 4094725) B4094725
theorem B2158259 : Blo 1437538 2158259 := bstep (se 1 (by rfl) ⟨1618694, by rfl⟩ : syracuseStep 2158259 = 3237389) B3237389
theorem B2428609 : Blo 1437538 2428609 := bstep (se 2 (by rfl) ⟨910728, by rfl⟩ : syracuseStep 2428609 = 1821457) B1821457
theorem B2731715 : Blo 1437538 2731715 := bstep (se 1 (by rfl) ⟨2048786, by rfl⟩ : syracuseStep 2731715 = 4097573) B4097573
theorem B2158289 : Blo 1437538 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B1617619 : Blo 1437538 1617619 := bstep (se 1 (by rfl) ⟨1213214, by rfl⟩ : syracuseStep 1617619 = 2426429) B2426429
theorem B2158307 : Blo 1437538 2158307 := bstep (se 1 (by rfl) ⟨1618730, by rfl⟩ : syracuseStep 2158307 = 3237461) B3237461
theorem B2428643 : Blo 1437538 2428643 := bstep (se 1 (by rfl) ⟨1821482, by rfl⟩ : syracuseStep 2428643 = 3642965) B3642965
theorem B1969921 : Blo 1437538 1969921 := bstep (se 2 (by rfl) ⟨738720, by rfl⟩ : syracuseStep 1969921 = 1477441) B1477441
theorem B2158337 : Blo 1437538 2158337 := bstep (se 2 (by rfl) ⟨809376, by rfl⟩ : syracuseStep 2158337 = 1618753) B1618753
theorem B9219845 : Blo 1437538 9219845 := bstep (se 4 (by rfl) ⟨864360, by rfl⟩ : syracuseStep 9219845 = 1728721) B1728721
theorem B2158355 : Blo 1437538 2158355 := bstep (se 1 (by rfl) ⟨1618766, by rfl⟩ : syracuseStep 2158355 = 3237533) B3237533
theorem B2158385 : Blo 1437538 2158385 := bstep (se 2 (by rfl) ⟨809394, by rfl⟩ : syracuseStep 2158385 = 1618789) B1618789
theorem B2158403 : Blo 1437538 2158403 := bstep (se 1 (by rfl) ⟨1618802, by rfl⟩ : syracuseStep 2158403 = 3237605) B3237605
theorem B2158433 : Blo 1437538 2158433 := bstep (se 2 (by rfl) ⟨809412, by rfl⟩ : syracuseStep 2158433 = 1618825) B1618825
theorem B1437539 : Blo 1437538 1437539 := bstep (se 1 (by rfl) ⟨1078154, by rfl⟩ : syracuseStep 1437539 = 2156309) B2156309
theorem B1617763 : Blo 1437538 1617763 := bstep (se 1 (by rfl) ⟨1213322, by rfl⟩ : syracuseStep 1617763 = 2426645) B2426645
theorem B2428771 : Blo 1437538 2428771 := bstep (se 1 (by rfl) ⟨1821578, by rfl⟩ : syracuseStep 2428771 = 3643157) B3643157
theorem B1437555 : Blo 1437538 1437555 := bstep (se 1 (by rfl) ⟨1078166, by rfl⟩ : syracuseStep 1437555 = 2156333) B2156333
theorem B2158451 : Blo 1437538 2158451 := bstep (se 1 (by rfl) ⟨1618838, by rfl⟩ : syracuseStep 2158451 = 3237677) B3237677
theorem B1437571 : Blo 1437538 1437571 := bstep (se 1 (by rfl) ⟨1078178, by rfl⟩ : syracuseStep 1437571 = 2156357) B2156357
theorem B3641233 : Blo 1437538 3641233 := bstep (se 2 (by rfl) ⟨1365462, by rfl⟩ : syracuseStep 3641233 = 2730925) B2730925
theorem B2158481 : Blo 1437538 2158481 := bstep (se 2 (by rfl) ⟨809430, by rfl⟩ : syracuseStep 2158481 = 1618861) B1618861
theorem B1437587 : Blo 1437538 1437587 := bstep (se 1 (by rfl) ⟨1078190, by rfl⟩ : syracuseStep 1437587 = 2156381) B2156381
theorem B1437603 : Blo 1437538 1437603 := bstep (se 1 (by rfl) ⟨1078202, by rfl⟩ : syracuseStep 1437603 = 2156405) B2156405
theorem B2158499 : Blo 1437538 2158499 := bstep (se 1 (by rfl) ⟨1618874, by rfl⟩ : syracuseStep 2158499 = 3237749) B3237749
theorem B4853681 : Blo 1437538 4853681 := bstep (se 2 (by rfl) ⟨1820130, by rfl⟩ : syracuseStep 4853681 = 3640261) B3640261
theorem B1437619 : Blo 1437538 1437619 := bstep (se 1 (by rfl) ⟨1078214, by rfl⟩ : syracuseStep 1437619 = 2156429) B2156429
theorem B2158529 : Blo 1437538 2158529 := bstep (se 2 (by rfl) ⟨809448, by rfl⟩ : syracuseStep 2158529 = 1618897) B1618897
theorem B1437635 : Blo 1437538 1437635 := bstep (se 1 (by rfl) ⟨1078226, by rfl⟩ : syracuseStep 1437635 = 2156453) B2156453
theorem B2076625 : Blo 1437538 2076625 := bstep (se 2 (by rfl) ⟨778734, by rfl⟩ : syracuseStep 2076625 = 1557469) B1557469
theorem B1437651 : Blo 1437538 1437651 := bstep (se 1 (by rfl) ⟨1078238, by rfl⟩ : syracuseStep 1437651 = 2156477) B2156477
theorem B2158547 : Blo 1437538 2158547 := bstep (se 1 (by rfl) ⟨1618910, by rfl⟩ : syracuseStep 2158547 = 3237821) B3237821
theorem B1437667 : Blo 1437538 1437667 := bstep (se 1 (by rfl) ⟨1078250, by rfl⟩ : syracuseStep 1437667 = 2156501) B2156501
theorem B1871843 : Blo 1437538 1871843 := bstep (se 1 (by rfl) ⟨1403882, by rfl⟩ : syracuseStep 1871843 = 2807765) B2807765
theorem B2158577 : Blo 1437538 2158577 := bstep (se 2 (by rfl) ⟨809466, by rfl⟩ : syracuseStep 2158577 = 1618933) B1618933
theorem B2428913 : Blo 1437538 2428913 := bstep (se 2 (by rfl) ⟨910842, by rfl⟩ : syracuseStep 2428913 = 1821685) B1821685
theorem B1437683 : Blo 1437538 1437683 := bstep (se 1 (by rfl) ⟨1078262, by rfl⟩ : syracuseStep 1437683 = 2156525) B2156525
theorem B1617907 : Blo 1437538 1617907 := bstep (se 1 (by rfl) ⟨1213430, by rfl⟩ : syracuseStep 1617907 = 2426861) B2426861
theorem B1437699 : Blo 1437538 1437699 := bstep (se 1 (by rfl) ⟨1078274, by rfl⟩ : syracuseStep 1437699 = 2156549) B2156549
theorem B2158595 : Blo 1437538 2158595 := bstep (se 1 (by rfl) ⟨1618946, by rfl⟩ : syracuseStep 2158595 = 3237893) B3237893
theorem B1437715 : Blo 1437538 1437715 := bstep (se 1 (by rfl) ⟨1078286, by rfl⟩ : syracuseStep 1437715 = 2156573) B2156573
theorem B35016725 : Blo 1437538 35016725 := bstep (se 6 (by rfl) ⟨820704, by rfl⟩ : syracuseStep 35016725 = 1641409) B1641409
theorem B2158625 : Blo 1437538 2158625 := bstep (se 2 (by rfl) ⟨809484, by rfl⟩ : syracuseStep 2158625 = 1618969) B1618969
theorem B1437731 : Blo 1437538 1437731 := bstep (se 1 (by rfl) ⟨1078298, by rfl⟩ : syracuseStep 1437731 = 2156597) B2156597
theorem B1437747 : Blo 1437538 1437747 := bstep (se 1 (by rfl) ⟨1078310, by rfl⟩ : syracuseStep 1437747 = 2156621) B2156621
theorem B2158643 : Blo 1437538 2158643 := bstep (se 1 (by rfl) ⟨1618982, by rfl⟩ : syracuseStep 2158643 = 3237965) B3237965
theorem B1437763 : Blo 1437538 1437763 := bstep (se 1 (by rfl) ⟨1078322, by rfl⟩ : syracuseStep 1437763 = 2156645) B2156645
theorem B2158673 : Blo 1437538 2158673 := bstep (se 2 (by rfl) ⟨809502, by rfl⟩ : syracuseStep 2158673 = 1619005) B1619005
theorem B1437779 : Blo 1437538 1437779 := bstep (se 1 (by rfl) ⟨1078334, by rfl⟩ : syracuseStep 1437779 = 2156669) B2156669
theorem B1437795 : Blo 1437538 1437795 := bstep (se 1 (by rfl) ⟨1078346, by rfl⟩ : syracuseStep 1437795 = 2156693) B2156693
theorem B2158691 : Blo 1437538 2158691 := bstep (se 1 (by rfl) ⟨1619018, by rfl⟩ : syracuseStep 2158691 = 3238037) B3238037
theorem B2429041 : Blo 1437538 2429041 := bstep (se 2 (by rfl) ⟨910890, by rfl⟩ : syracuseStep 2429041 = 1821781) B1821781
theorem B1437811 : Blo 1437538 1437811 := bstep (se 1 (by rfl) ⟨1078358, by rfl⟩ : syracuseStep 1437811 = 2156717) B2156717
theorem B2158721 : Blo 1437538 2158721 := bstep (se 2 (by rfl) ⟨809520, by rfl⟩ : syracuseStep 2158721 = 1619041) B1619041
theorem B1618051 : Blo 1437538 1618051 := bstep (se 1 (by rfl) ⟨1213538, by rfl⟩ : syracuseStep 1618051 = 2427077) B2427077
theorem B1437827 : Blo 1437538 1437827 := bstep (se 1 (by rfl) ⟨1078370, by rfl⟩ : syracuseStep 1437827 = 2156741) B2156741
theorem B8188037 : Blo 1437538 8188037 := bstep (se 4 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 8188037 = 1535257) B1535257
theorem B2461841 : Blo 1437538 2461841 := bstep (se 2 (by rfl) ⟨923190, by rfl⟩ : syracuseStep 2461841 = 1846381) B1846381
theorem B1437843 : Blo 1437538 1437843 := bstep (se 1 (by rfl) ⟨1078382, by rfl⟩ : syracuseStep 1437843 = 2156765) B2156765
theorem B2158739 : Blo 1437538 2158739 := bstep (se 1 (by rfl) ⟨1619054, by rfl⟩ : syracuseStep 2158739 = 3238109) B3238109
theorem B2429075 : Blo 1437538 2429075 := bstep (se 1 (by rfl) ⟨1821806, by rfl⟩ : syracuseStep 2429075 = 3643613) B3643613
theorem B4206755 : Blo 1437538 4206755 := bstep (se 1 (by rfl) ⟨3155066, by rfl⟩ : syracuseStep 4206755 = 6310133) B6310133
theorem B1437859 : Blo 1437538 1437859 := bstep (se 1 (by rfl) ⟨1078394, by rfl⟩ : syracuseStep 1437859 = 2156789) B2156789
theorem B3641507 : Blo 1437538 3641507 := bstep (se 1 (by rfl) ⟨2731130, by rfl⟩ : syracuseStep 3641507 = 5462261) B5462261
theorem B2158769 : Blo 1437538 2158769 := bstep (se 2 (by rfl) ⟨809538, by rfl⟩ : syracuseStep 2158769 = 1619077) B1619077
theorem B1437875 : Blo 1437538 1437875 := bstep (se 1 (by rfl) ⟨1078406, by rfl⟩ : syracuseStep 1437875 = 2156813) B2156813
theorem B1437891 : Blo 1437538 1437891 := bstep (se 1 (by rfl) ⟨1078418, by rfl⟩ : syracuseStep 1437891 = 2156837) B2156837
theorem B2158787 : Blo 1437538 2158787 := bstep (se 1 (by rfl) ⟨1619090, by rfl⟩ : syracuseStep 2158787 = 3238181) B3238181
theorem B1437907 : Blo 1437538 1437907 := bstep (se 1 (by rfl) ⟨1078430, by rfl⟩ : syracuseStep 1437907 = 2156861) B2156861
theorem B2158817 : Blo 1437538 2158817 := bstep (se 2 (by rfl) ⟨809556, by rfl⟩ : syracuseStep 2158817 = 1619113) B1619113
theorem B1437923 : Blo 1437538 1437923 := bstep (se 1 (by rfl) ⟨1078442, by rfl⟩ : syracuseStep 1437923 = 2156885) B2156885
theorem B1437939 : Blo 1437538 1437939 := bstep (se 1 (by rfl) ⟨1078454, by rfl⟩ : syracuseStep 1437939 = 2156909) B2156909
theorem B2158835 : Blo 1437538 2158835 := bstep (se 1 (by rfl) ⟨1619126, by rfl⟩ : syracuseStep 2158835 = 3238253) B3238253
theorem B1437955 : Blo 1437538 1437955 := bstep (se 1 (by rfl) ⟨1078466, by rfl⟩ : syracuseStep 1437955 = 2156933) B2156933
theorem B2158865 : Blo 1437538 2158865 := bstep (se 2 (by rfl) ⟨809574, by rfl⟩ : syracuseStep 2158865 = 1619149) B1619149
theorem B1437971 : Blo 1437538 1437971 := bstep (se 1 (by rfl) ⟨1078478, by rfl⟩ : syracuseStep 1437971 = 2156957) B2156957
theorem B1618195 : Blo 1437538 1618195 := bstep (se 1 (by rfl) ⟨1213646, by rfl⟩ : syracuseStep 1618195 = 2427293) B2427293
theorem B2429203 : Blo 1437538 2429203 := bstep (se 1 (by rfl) ⟨1821902, by rfl⟩ : syracuseStep 2429203 = 3643805) B3643805
theorem B1437987 : Blo 1437538 1437987 := bstep (se 1 (by rfl) ⟨1078490, by rfl⟩ : syracuseStep 1437987 = 2156981) B2156981
theorem B2158883 : Blo 1437538 2158883 := bstep (se 1 (by rfl) ⟨1619162, by rfl⟩ : syracuseStep 2158883 = 3238325) B3238325
theorem B1438003 : Blo 1437538 1438003 := bstep (se 1 (by rfl) ⟨1078502, by rfl⟩ : syracuseStep 1438003 = 2157005) B2157005
theorem B2158913 : Blo 1437538 2158913 := bstep (se 2 (by rfl) ⟨809592, by rfl⟩ : syracuseStep 2158913 = 1619185) B1619185
theorem B1438019 : Blo 1437538 1438019 := bstep (se 1 (by rfl) ⟨1078514, by rfl⟩ : syracuseStep 1438019 = 2157029) B2157029
theorem B9212237 : Blo 1437538 9212237 := bstep (se 3 (by rfl) ⟨1727294, by rfl⟩ : syracuseStep 9212237 = 3454589) B3454589
theorem B1438035 : Blo 1437538 1438035 := bstep (se 1 (by rfl) ⟨1078526, by rfl⟩ : syracuseStep 1438035 = 2157053) B2157053
theorem B2158931 : Blo 1437538 2158931 := bstep (se 1 (by rfl) ⟨1619198, by rfl⟩ : syracuseStep 2158931 = 3238397) B3238397
theorem B1438051 : Blo 1437538 1438051 := bstep (se 1 (by rfl) ⟨1078538, by rfl⟩ : syracuseStep 1438051 = 2157077) B2157077
theorem B3641699 : Blo 1437538 3641699 := bstep (se 1 (by rfl) ⟨2731274, by rfl⟩ : syracuseStep 3641699 = 5462549) B5462549
theorem B2158961 : Blo 1437538 2158961 := bstep (se 2 (by rfl) ⟨809610, by rfl⟩ : syracuseStep 2158961 = 1619221) B1619221
theorem B1438067 : Blo 1437538 1438067 := bstep (se 1 (by rfl) ⟨1078550, by rfl⟩ : syracuseStep 1438067 = 2157101) B2157101
theorem B1438083 : Blo 1437538 1438083 := bstep (se 1 (by rfl) ⟨1078562, by rfl⟩ : syracuseStep 1438083 = 2157125) B2157125
theorem B2158979 : Blo 1437538 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B1438099 : Blo 1437538 1438099 := bstep (se 1 (by rfl) ⟨1078574, by rfl⟩ : syracuseStep 1438099 = 2157149) B2157149
theorem B2159009 : Blo 1437538 2159009 := bstep (se 2 (by rfl) ⟨809628, by rfl⟩ : syracuseStep 2159009 = 1619257) B1619257
theorem B1438115 : Blo 1437538 1438115 := bstep (se 1 (by rfl) ⟨1078586, by rfl⟩ : syracuseStep 1438115 = 2157173) B2157173
theorem B1618339 : Blo 1437538 1618339 := bstep (se 1 (by rfl) ⟨1213754, by rfl⟩ : syracuseStep 1618339 = 2427509) B2427509
theorem B1536419 : Blo 1437538 1536419 := bstep (se 1 (by rfl) ⟨1152314, by rfl⟩ : syracuseStep 1536419 = 2304629) B2304629
theorem B1438131 : Blo 1437538 1438131 := bstep (se 1 (by rfl) ⟨1078598, by rfl⟩ : syracuseStep 1438131 = 2157197) B2157197
theorem B2159027 : Blo 1437538 2159027 := bstep (se 1 (by rfl) ⟨1619270, by rfl⟩ : syracuseStep 2159027 = 3238541) B3238541
theorem B1438147 : Blo 1437538 1438147 := bstep (se 1 (by rfl) ⟨1078610, by rfl⟩ : syracuseStep 1438147 = 2157221) B2157221
theorem B4854221 : Blo 1437538 4854221 := bstep (se 3 (by rfl) ⟨910166, by rfl⟩ : syracuseStep 4854221 = 1820333) B1820333
theorem B1438163 : Blo 1437538 1438163 := bstep (se 1 (by rfl) ⟨1078622, by rfl⟩ : syracuseStep 1438163 = 2157245) B2157245
theorem B2159057 : Blo 1437538 2159057 := bstep (se 2 (by rfl) ⟨809646, by rfl⟩ : syracuseStep 2159057 = 1619293) B1619293
theorem B7287245 : Blo 1437538 7287245 := bstep (se 3 (by rfl) ⟨1366358, by rfl⟩ : syracuseStep 7287245 = 2732717) B2732717
theorem B1438179 : Blo 1437538 1438179 := bstep (se 1 (by rfl) ⟨1078634, by rfl⟩ : syracuseStep 1438179 = 2157269) B2157269
theorem B10367459 : Blo 1437538 10367459 := bstep (se 1 (by rfl) ⟨7775594, by rfl⟩ : syracuseStep 10367459 = 15551189) B15551189
theorem B2159075 : Blo 1437538 2159075 := bstep (se 1 (by rfl) ⟨1619306, by rfl⟩ : syracuseStep 2159075 = 3238613) B3238613
theorem B1438195 : Blo 1437538 1438195 := bstep (se 1 (by rfl) ⟨1078646, by rfl⟩ : syracuseStep 1438195 = 2157293) B2157293
theorem B2159105 : Blo 1437538 2159105 := bstep (se 2 (by rfl) ⟨809664, by rfl⟩ : syracuseStep 2159105 = 1619329) B1619329
theorem B1438211 : Blo 1437538 1438211 := bstep (se 1 (by rfl) ⟨1078658, by rfl⟩ : syracuseStep 1438211 = 2157317) B2157317
theorem B4854275 : Blo 1437538 4854275 := bstep (se 1 (by rfl) ⟨3640706, by rfl⟩ : syracuseStep 4854275 = 7281413) B7281413
theorem B4608515 : Blo 1437538 4608515 := bstep (se 1 (by rfl) ⟨3456386, by rfl⟩ : syracuseStep 4608515 = 6912773) B6912773
theorem B1438227 : Blo 1437538 1438227 := bstep (se 1 (by rfl) ⟨1078670, by rfl⟩ : syracuseStep 1438227 = 2157341) B2157341
theorem B2159123 : Blo 1437538 2159123 := bstep (se 1 (by rfl) ⟨1619342, by rfl⟩ : syracuseStep 2159123 = 3238685) B3238685
theorem B1438243 : Blo 1437538 1438243 := bstep (se 1 (by rfl) ⟨1078682, by rfl⟩ : syracuseStep 1438243 = 2157365) B2157365
theorem B3691057 : Blo 1437538 3691057 := bstep (se 2 (by rfl) ⟨1384146, by rfl⟩ : syracuseStep 3691057 = 2768293) B2768293
theorem B2159153 : Blo 1437538 2159153 := bstep (se 2 (by rfl) ⟨809682, by rfl⟩ : syracuseStep 2159153 = 1619365) B1619365
theorem B1438259 : Blo 1437538 1438259 := bstep (se 1 (by rfl) ⟨1078694, by rfl⟩ : syracuseStep 1438259 = 2157389) B2157389
theorem B1618483 : Blo 1437538 1618483 := bstep (se 1 (by rfl) ⟨1213862, by rfl⟩ : syracuseStep 1618483 = 2427725) B2427725
theorem B1438275 : Blo 1437538 1438275 := bstep (se 1 (by rfl) ⟨1078706, by rfl⟩ : syracuseStep 1438275 = 2157413) B2157413
theorem B2732611 : Blo 1437538 2732611 := bstep (se 1 (by rfl) ⟨2049458, by rfl⟩ : syracuseStep 2732611 = 4098917) B4098917
theorem B2159171 : Blo 1437538 2159171 := bstep (se 1 (by rfl) ⟨1619378, by rfl⟩ : syracuseStep 2159171 = 3238757) B3238757
theorem B1438291 : Blo 1437538 1438291 := bstep (se 1 (by rfl) ⟨1078718, by rfl⟩ : syracuseStep 1438291 = 2157437) B2157437
theorem B2159201 : Blo 1437538 2159201 := bstep (se 2 (by rfl) ⟨809700, by rfl⟩ : syracuseStep 2159201 = 1619401) B1619401
theorem B1438307 : Blo 1437538 1438307 := bstep (se 1 (by rfl) ⟨1078730, by rfl⟩ : syracuseStep 1438307 = 2157461) B2157461
theorem B3502705 : Blo 1437538 3502705 := bstep (se 2 (by rfl) ⟨1313514, by rfl⟩ : syracuseStep 3502705 = 2627029) B2627029
theorem B1438323 : Blo 1437538 1438323 := bstep (se 1 (by rfl) ⟨1078742, by rfl⟩ : syracuseStep 1438323 = 2157485) B2157485
theorem B2159219 : Blo 1437538 2159219 := bstep (se 1 (by rfl) ⟨1619414, by rfl⟩ : syracuseStep 2159219 = 3238829) B3238829
theorem B1438339 : Blo 1437538 1438339 := bstep (se 1 (by rfl) ⟨1078754, by rfl⟩ : syracuseStep 1438339 = 2157509) B2157509
theorem B2159249 : Blo 1437538 2159249 := bstep (se 2 (by rfl) ⟨809718, by rfl⟩ : syracuseStep 2159249 = 1619437) B1619437
theorem B1438355 : Blo 1437538 1438355 := bstep (se 1 (by rfl) ⟨1078766, by rfl⟩ : syracuseStep 1438355 = 2157533) B2157533
theorem B1438371 : Blo 1437538 1438371 := bstep (se 1 (by rfl) ⟨1078778, by rfl⟩ : syracuseStep 1438371 = 2157557) B2157557
theorem B2159267 : Blo 1437538 2159267 := bstep (se 1 (by rfl) ⟨1619450, by rfl⟩ : syracuseStep 2159267 = 3238901) B3238901
theorem B8196785 : Blo 1437538 8196785 := bstep (se 2 (by rfl) ⟨3073794, by rfl⟩ : syracuseStep 8196785 = 6147589) B6147589
theorem B1438387 : Blo 1437538 1438387 := bstep (se 1 (by rfl) ⟨1078790, by rfl⟩ : syracuseStep 1438387 = 2157581) B2157581
theorem B2077363 : Blo 1437538 2077363 := bstep (se 1 (by rfl) ⟨1558022, by rfl⟩ : syracuseStep 2077363 = 3116045) B3116045
theorem B2159297 : Blo 1437538 2159297 := bstep (se 2 (by rfl) ⟨809736, by rfl⟩ : syracuseStep 2159297 = 1619473) B1619473
theorem B1438403 : Blo 1437538 1438403 := bstep (se 1 (by rfl) ⟨1078802, by rfl⟩ : syracuseStep 1438403 = 2157605) B2157605
theorem B1618627 : Blo 1437538 1618627 := bstep (se 1 (by rfl) ⟨1213970, by rfl⟩ : syracuseStep 1618627 = 2427941) B2427941
theorem B5182157 : Blo 1437538 5182157 := bstep (se 3 (by rfl) ⟨971654, by rfl⟩ : syracuseStep 5182157 = 1943309) B1943309
theorem B1438419 : Blo 1437538 1438419 := bstep (se 1 (by rfl) ⟨1078814, by rfl⟩ : syracuseStep 1438419 = 2157629) B2157629
theorem B1438435 : Blo 1437538 1438435 := bstep (se 1 (by rfl) ⟨1078826, by rfl⟩ : syracuseStep 1438435 = 2157653) B2157653
theorem B2732771 : Blo 1437538 2732771 := bstep (se 1 (by rfl) ⟨2049578, by rfl⟩ : syracuseStep 2732771 = 4099157) B4099157
theorem B1438451 : Blo 1437538 1438451 := bstep (se 1 (by rfl) ⟨1078838, by rfl⟩ : syracuseStep 1438451 = 2157677) B2157677
theorem B1438467 : Blo 1437538 1438467 := bstep (se 1 (by rfl) ⟨1078850, by rfl⟩ : syracuseStep 1438467 = 2157701) B2157701
theorem B7779077 : Blo 1437538 7779077 := bstep (se 4 (by rfl) ⟨729288, by rfl⟩ : syracuseStep 7779077 = 1458577) B1458577
theorem B6910733 : Blo 1437538 6910733 := bstep (se 3 (by rfl) ⟨1295762, by rfl⟩ : syracuseStep 6910733 = 2591525) B2591525
theorem B4854545 : Blo 1437538 4854545 := bstep (se 2 (by rfl) ⟨1820454, by rfl⟩ : syracuseStep 4854545 = 3640909) B3640909
theorem B1438483 : Blo 1437538 1438483 := bstep (se 1 (by rfl) ⟨1078862, by rfl⟩ : syracuseStep 1438483 = 2157725) B2157725
theorem B1438499 : Blo 1437538 1438499 := bstep (se 1 (by rfl) ⟨1078874, by rfl⟩ : syracuseStep 1438499 = 2157749) B2157749
theorem B8188721 : Blo 1437538 8188721 := bstep (se 2 (by rfl) ⟨3070770, by rfl⟩ : syracuseStep 8188721 = 6141541) B6141541
theorem B1438515 : Blo 1437538 1438515 := bstep (se 1 (by rfl) ⟨1078886, by rfl⟩ : syracuseStep 1438515 = 2157773) B2157773
theorem B1438531 : Blo 1437538 1438531 := bstep (se 1 (by rfl) ⟨1078898, by rfl⟩ : syracuseStep 1438531 = 2157797) B2157797
theorem B1438547 : Blo 1437538 1438547 := bstep (se 1 (by rfl) ⟨1078910, by rfl⟩ : syracuseStep 1438547 = 2157821) B2157821
theorem B1618771 : Blo 1437538 1618771 := bstep (se 1 (by rfl) ⟨1214078, by rfl⟩ : syracuseStep 1618771 = 2428157) B2428157
theorem B1438563 : Blo 1437538 1438563 := bstep (se 1 (by rfl) ⟨1078922, by rfl⟩ : syracuseStep 1438563 = 2157845) B2157845
theorem B1438579 : Blo 1437538 1438579 := bstep (se 1 (by rfl) ⟨1078934, by rfl⟩ : syracuseStep 1438579 = 2157869) B2157869
theorem B1438595 : Blo 1437538 1438595 := bstep (se 1 (by rfl) ⟨1078946, by rfl⟩ : syracuseStep 1438595 = 2157893) B2157893
theorem B1438611 : Blo 1437538 1438611 := bstep (se 1 (by rfl) ⟨1078958, by rfl⟩ : syracuseStep 1438611 = 2157917) B2157917
theorem B1438627 : Blo 1437538 1438627 := bstep (se 1 (by rfl) ⟨1078970, by rfl⟩ : syracuseStep 1438627 = 2157941) B2157941
theorem B1438643 : Blo 1437538 1438643 := bstep (se 1 (by rfl) ⟨1078982, by rfl⟩ : syracuseStep 1438643 = 2157965) B2157965
theorem B1438659 : Blo 1437538 1438659 := bstep (se 1 (by rfl) ⟨1078994, by rfl⟩ : syracuseStep 1438659 = 2157989) B2157989
theorem B1438675 : Blo 1437538 1438675 := bstep (se 1 (by rfl) ⟨1079006, by rfl⟩ : syracuseStep 1438675 = 2158013) B2158013
theorem B1438691 : Blo 1437538 1438691 := bstep (se 1 (by rfl) ⟨1079018, by rfl⟩ : syracuseStep 1438691 = 2158037) B2158037
theorem B1618915 : Blo 1437538 1618915 := bstep (se 1 (by rfl) ⟨1214186, by rfl⟩ : syracuseStep 1618915 = 2428373) B2428373
theorem B1438707 : Blo 1437538 1438707 := bstep (se 1 (by rfl) ⟨1079030, by rfl⟩ : syracuseStep 1438707 = 2158061) B2158061
theorem B1438723 : Blo 1437538 1438723 := bstep (se 1 (by rfl) ⟨1079042, by rfl⟩ : syracuseStep 1438723 = 2158085) B2158085
theorem B1438739 : Blo 1437538 1438739 := bstep (se 1 (by rfl) ⟨1079054, by rfl⟩ : syracuseStep 1438739 = 2158109) B2158109
theorem B1438755 : Blo 1437538 1438755 := bstep (se 1 (by rfl) ⟨1079066, by rfl⟩ : syracuseStep 1438755 = 2158133) B2158133
theorem B1438771 : Blo 1437538 1438771 := bstep (se 1 (by rfl) ⟨1079078, by rfl⟩ : syracuseStep 1438771 = 2158157) B2158157
theorem B1438787 : Blo 1437538 1438787 := bstep (se 1 (by rfl) ⟨1079090, by rfl⟩ : syracuseStep 1438787 = 2158181) B2158181
theorem B1438803 : Blo 1437538 1438803 := bstep (se 1 (by rfl) ⟨1079102, by rfl⟩ : syracuseStep 1438803 = 2158205) B2158205
theorem B5461091 : Blo 1437538 5461091 := bstep (se 1 (by rfl) ⟨4095818, by rfl⟩ : syracuseStep 5461091 = 8191637) B8191637
theorem B1438819 : Blo 1437538 1438819 := bstep (se 1 (by rfl) ⟨1079114, by rfl⟩ : syracuseStep 1438819 = 2158229) B2158229
theorem B1438835 : Blo 1437538 1438835 := bstep (se 1 (by rfl) ⟨1079126, by rfl⟩ : syracuseStep 1438835 = 2158253) B2158253
theorem B1619059 : Blo 1437538 1619059 := bstep (se 1 (by rfl) ⟨1214294, by rfl⟩ : syracuseStep 1619059 = 2428589) B2428589
theorem B1438851 : Blo 1437538 1438851 := bstep (se 1 (by rfl) ⟨1079138, by rfl⟩ : syracuseStep 1438851 = 2158277) B2158277
theorem B7885957 : Blo 1437538 7885957 := bstep (se 4 (by rfl) ⟨739308, by rfl⟩ : syracuseStep 7885957 = 1478617) B1478617
theorem B1438867 : Blo 1437538 1438867 := bstep (se 1 (by rfl) ⟨1079150, by rfl⟩ : syracuseStep 1438867 = 2158301) B2158301
theorem B1438883 : Blo 1437538 1438883 := bstep (se 1 (by rfl) ⟨1079162, by rfl⟩ : syracuseStep 1438883 = 2158325) B2158325
theorem B7279793 : Blo 1437538 7279793 := bstep (se 2 (by rfl) ⟨2729922, by rfl⟩ : syracuseStep 7279793 = 5459845) B5459845
theorem B1438899 : Blo 1437538 1438899 := bstep (se 1 (by rfl) ⟨1079174, by rfl⟩ : syracuseStep 1438899 = 2158349) B2158349
theorem B1438915 : Blo 1437538 1438915 := bstep (se 1 (by rfl) ⟨1079186, by rfl⟩ : syracuseStep 1438915 = 2158373) B2158373
theorem B1438931 : Blo 1437538 1438931 := bstep (se 1 (by rfl) ⟨1079198, by rfl⟩ : syracuseStep 1438931 = 2158397) B2158397
theorem B1438947 : Blo 1437538 1438947 := bstep (se 1 (by rfl) ⟨1079210, by rfl⟩ : syracuseStep 1438947 = 2158421) B2158421
theorem B1438963 : Blo 1437538 1438963 := bstep (se 1 (by rfl) ⟨1079222, by rfl⟩ : syracuseStep 1438963 = 2158445) B2158445
theorem B1438979 : Blo 1437538 1438979 := bstep (se 1 (by rfl) ⟨1079234, by rfl⟩ : syracuseStep 1438979 = 2158469) B2158469
theorem B1619203 : Blo 1437538 1619203 := bstep (se 1 (by rfl) ⟨1214402, by rfl⟩ : syracuseStep 1619203 = 2428805) B2428805
theorem B3642641 : Blo 1437538 3642641 := bstep (se 2 (by rfl) ⟨1365990, by rfl⟩ : syracuseStep 3642641 = 2731981) B2731981
theorem B1438995 : Blo 1437538 1438995 := bstep (se 1 (by rfl) ⟨1079246, by rfl⟩ : syracuseStep 1438995 = 2158493) B2158493
theorem B9835811 : Blo 1437538 9835811 := bstep (se 1 (by rfl) ⟨7376858, by rfl⟩ : syracuseStep 9835811 = 14753717) B14753717
theorem B1439011 : Blo 1437538 1439011 := bstep (se 1 (by rfl) ⟨1079258, by rfl⟩ : syracuseStep 1439011 = 2158517) B2158517
theorem B4855085 : Blo 1437538 4855085 := bstep (se 3 (by rfl) ⟨910328, by rfl⟩ : syracuseStep 4855085 = 1820657) B1820657
theorem B6141233 : Blo 1437538 6141233 := bstep (se 2 (by rfl) ⟨2302962, by rfl⟩ : syracuseStep 6141233 = 4605925) B4605925
theorem B1439027 : Blo 1437538 1439027 := bstep (se 1 (by rfl) ⟨1079270, by rfl⟩ : syracuseStep 1439027 = 2158541) B2158541
theorem B1439043 : Blo 1437538 1439043 := bstep (se 1 (by rfl) ⟨1079282, by rfl⟩ : syracuseStep 1439043 = 2158565) B2158565
theorem B3642691 : Blo 1437538 3642691 := bstep (se 1 (by rfl) ⟨2732018, by rfl⟩ : syracuseStep 3642691 = 5464037) B5464037
theorem B1439059 : Blo 1437538 1439059 := bstep (se 1 (by rfl) ⟨1079294, by rfl⟩ : syracuseStep 1439059 = 2158589) B2158589
theorem B4855139 : Blo 1437538 4855139 := bstep (se 1 (by rfl) ⟨3641354, by rfl⟩ : syracuseStep 4855139 = 7282709) B7282709
theorem B1439075 : Blo 1437538 1439075 := bstep (se 1 (by rfl) ⟨1079306, by rfl⟩ : syracuseStep 1439075 = 2158613) B2158613
theorem B1439091 : Blo 1437538 1439091 := bstep (se 1 (by rfl) ⟨1079318, by rfl⟩ : syracuseStep 1439091 = 2158637) B2158637
theorem B1439107 : Blo 1437538 1439107 := bstep (se 1 (by rfl) ⟨1079330, by rfl⟩ : syracuseStep 1439107 = 2158661) B2158661
theorem B1439123 : Blo 1437538 1439123 := bstep (se 1 (by rfl) ⟨1079342, by rfl⟩ : syracuseStep 1439123 = 2158685) B2158685
theorem B1619347 : Blo 1437538 1619347 := bstep (se 1 (by rfl) ⟨1214510, by rfl⟩ : syracuseStep 1619347 = 2429021) B2429021
theorem B1439139 : Blo 1437538 1439139 := bstep (se 1 (by rfl) ⟨1079354, by rfl⟩ : syracuseStep 1439139 = 2158709) B2158709
theorem B1439155 : Blo 1437538 1439155 := bstep (se 1 (by rfl) ⟨1079366, by rfl⟩ : syracuseStep 1439155 = 2158733) B2158733
theorem B1439171 : Blo 1437538 1439171 := bstep (se 1 (by rfl) ⟨1079378, by rfl⟩ : syracuseStep 1439171 = 2158757) B2158757
theorem B3642833 : Blo 1437538 3642833 := bstep (se 2 (by rfl) ⟨1366062, by rfl⟩ : syracuseStep 3642833 = 2732125) B2732125
theorem B1439187 : Blo 1437538 1439187 := bstep (se 1 (by rfl) ⟨1079390, by rfl⟩ : syracuseStep 1439187 = 2158781) B2158781
theorem B3454435 : Blo 1437538 3454435 := bstep (se 1 (by rfl) ⟨2590826, by rfl⟩ : syracuseStep 3454435 = 5181653) B5181653
theorem B1439203 : Blo 1437538 1439203 := bstep (se 1 (by rfl) ⟨1079402, by rfl⟩ : syracuseStep 1439203 = 2158805) B2158805
theorem B1439219 : Blo 1437538 1439219 := bstep (se 1 (by rfl) ⟨1079414, by rfl⟩ : syracuseStep 1439219 = 2158829) B2158829
theorem B1439235 : Blo 1437538 1439235 := bstep (se 1 (by rfl) ⟨1079426, by rfl⟩ : syracuseStep 1439235 = 2158853) B2158853
theorem B1439251 : Blo 1437538 1439251 := bstep (se 1 (by rfl) ⟨1079438, by rfl⟩ : syracuseStep 1439251 = 2158877) B2158877
theorem B1439267 : Blo 1437538 1439267 := bstep (se 1 (by rfl) ⟨1079450, by rfl⟩ : syracuseStep 1439267 = 2158901) B2158901
theorem B1439283 : Blo 1437538 1439283 := bstep (se 1 (by rfl) ⟨1079462, by rfl⟩ : syracuseStep 1439283 = 2158925) B2158925
theorem B1439299 : Blo 1437538 1439299 := bstep (se 1 (by rfl) ⟨1079474, by rfl⟩ : syracuseStep 1439299 = 2158949) B2158949
theorem B1439315 : Blo 1437538 1439315 := bstep (se 1 (by rfl) ⟨1079486, by rfl⟩ : syracuseStep 1439315 = 2158973) B2158973
theorem B8869475 : Blo 1437538 8869475 := bstep (se 1 (by rfl) ⟨6652106, by rfl⟩ : syracuseStep 8869475 = 13304213) B13304213
theorem B1439331 : Blo 1437538 1439331 := bstep (se 1 (by rfl) ⟨1079498, by rfl⟩ : syracuseStep 1439331 = 2158997) B2158997
theorem B4855409 : Blo 1437538 4855409 := bstep (se 2 (by rfl) ⟨1820778, by rfl⟩ : syracuseStep 4855409 = 3641557) B3641557
theorem B1439347 : Blo 1437538 1439347 := bstep (se 1 (by rfl) ⟨1079510, by rfl⟩ : syracuseStep 1439347 = 2159021) B2159021
theorem B1439363 : Blo 1437538 1439363 := bstep (se 1 (by rfl) ⟨1079522, by rfl⟩ : syracuseStep 1439363 = 2159045) B2159045
theorem B1439379 : Blo 1437538 1439379 := bstep (se 1 (by rfl) ⟨1079534, by rfl⟩ : syracuseStep 1439379 = 2159069) B2159069
theorem B9221795 : Blo 1437538 9221795 := bstep (se 1 (by rfl) ⟨6916346, by rfl⟩ : syracuseStep 9221795 = 13832693) B13832693
theorem B1439395 : Blo 1437538 1439395 := bstep (se 1 (by rfl) ⟨1079546, by rfl⟩ : syracuseStep 1439395 = 2159093) B2159093
theorem B1439411 : Blo 1437538 1439411 := bstep (se 1 (by rfl) ⟨1079558, by rfl⟩ : syracuseStep 1439411 = 2159117) B2159117
theorem B1439427 : Blo 1437538 1439427 := bstep (se 1 (by rfl) ⟨1079570, by rfl⟩ : syracuseStep 1439427 = 2159141) B2159141
theorem B10925765 : Blo 1437538 10925765 := bstep (se 4 (by rfl) ⟨1024290, by rfl⟩ : syracuseStep 10925765 = 2048581) B2048581
theorem B1439443 : Blo 1437538 1439443 := bstep (se 1 (by rfl) ⟨1079582, by rfl⟩ : syracuseStep 1439443 = 2159165) B2159165
theorem B1439459 : Blo 1437538 1439459 := bstep (se 1 (by rfl) ⟨1079594, by rfl⟩ : syracuseStep 1439459 = 2159189) B2159189
theorem B1439475 : Blo 1437538 1439475 := bstep (se 1 (by rfl) ⟨1079606, by rfl⟩ : syracuseStep 1439475 = 2159213) B2159213
theorem B1439491 : Blo 1437538 1439491 := bstep (se 1 (by rfl) ⟨1079618, by rfl⟩ : syracuseStep 1439491 = 2159237) B2159237
theorem B2627345 : Blo 1437538 2627345 := bstep (se 2 (by rfl) ⟨985254, by rfl⟩ : syracuseStep 2627345 = 1970509) B1970509
theorem B1439507 : Blo 1437538 1439507 := bstep (se 1 (by rfl) ⟨1079630, by rfl⟩ : syracuseStep 1439507 = 2159261) B2159261
theorem B1439523 : Blo 1437538 1439523 := bstep (se 1 (by rfl) ⟨1079642, by rfl⟩ : syracuseStep 1439523 = 2159285) B2159285
theorem B5183281 : Blo 1437538 5183281 := bstep (se 2 (by rfl) ⟨1943730, by rfl⟩ : syracuseStep 5183281 = 3887461) B3887461
theorem B119740301 : Blo 1437538 119740301 := bstep (se 3 (by rfl) ⟨22451306, by rfl⟩ : syracuseStep 119740301 = 44902613) B44902613
theorem B5183395 : Blo 1437538 5183395 := bstep (se 1 (by rfl) ⟨3887546, by rfl⟩ : syracuseStep 5183395 = 7775093) B7775093
theorem B5462093 : Blo 1437538 5462093 := bstep (se 3 (by rfl) ⟨1024142, by rfl⟩ : syracuseStep 5462093 = 2048285) B2048285
theorem B8198243 : Blo 1437538 8198243 := bstep (se 1 (by rfl) ⟨6148682, by rfl⟩ : syracuseStep 8198243 = 12297365) B12297365
theorem B4855949 : Blo 1437538 4855949 := bstep (se 3 (by rfl) ⟨910490, by rfl⟩ : syracuseStep 4855949 = 1820981) B1820981
theorem B4856003 : Blo 1437538 4856003 := bstep (se 1 (by rfl) ⟨3642002, by rfl⟩ : syracuseStep 4856003 = 7284005) B7284005
theorem B8190179 : Blo 1437538 8190179 := bstep (se 1 (by rfl) ⟨6142634, by rfl⟩ : syracuseStep 8190179 = 12285269) B12285269
theorem B3643825 : Blo 1437538 3643825 := bstep (se 2 (by rfl) ⟨1366434, by rfl⟩ : syracuseStep 3643825 = 2732869) B2732869
theorem B7780805 : Blo 1437538 7780805 := bstep (se 4 (by rfl) ⟨729450, by rfl⟩ : syracuseStep 7780805 = 1458901) B1458901
theorem B4856273 : Blo 1437538 4856273 := bstep (se 2 (by rfl) ⟨1821102, by rfl⟩ : syracuseStep 4856273 = 3642205) B3642205
theorem B1727011 : Blo 1437538 1727011 := bstep (se 1 (by rfl) ⟨1295258, by rfl⟩ : syracuseStep 1727011 = 2590517) B2590517
theorem B6142499 : Blo 1437538 6142499 := bstep (se 1 (by rfl) ⟨4606874, by rfl⟩ : syracuseStep 6142499 = 9213749) B9213749
theorem B4094509 : Blo 1437538 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B4610641 : Blo 1437538 4610641 := bstep (se 2 (by rfl) ⟨1728990, by rfl⟩ : syracuseStep 4610641 = 3457981) B3457981
theorem B7281251 : Blo 1437538 7281251 := bstep (se 1 (by rfl) ⟨5460938, by rfl⟩ : syracuseStep 7281251 = 10921877) B10921877
theorem B2767555 : Blo 1437538 2767555 := bstep (se 1 (by rfl) ⟨2075666, by rfl⟩ : syracuseStep 2767555 = 4151333) B4151333
theorem B3234545 : Blo 1437538 3234545 := bstep (se 2 (by rfl) ⟨1212954, by rfl⟩ : syracuseStep 3234545 = 2425909) B2425909
theorem B19675889 : Blo 1437538 19675889 := bstep (se 2 (by rfl) ⟨7378458, by rfl⟩ : syracuseStep 19675889 = 14756917) B14756917
theorem B3234563 : Blo 1437538 3234563 := bstep (se 1 (by rfl) ⟨2425922, by rfl⟩ : syracuseStep 3234563 = 4851845) B4851845
theorem B4373297 : Blo 1437538 4373297 := bstep (se 2 (by rfl) ⟨1639986, by rfl⟩ : syracuseStep 4373297 = 3279973) B3279973
theorem B4496273 : Blo 1437538 4496273 := bstep (se 2 (by rfl) ⟨1686102, by rfl⟩ : syracuseStep 4496273 = 3372205) B3372205
theorem B1752035 : Blo 1437538 1752035 := bstep (se 1 (by rfl) ⟨1314026, by rfl⟩ : syracuseStep 1752035 = 2628053) B2628053
theorem B3505123 : Blo 1437538 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B4856813 : Blo 1437538 4856813 := bstep (se 3 (by rfl) ⟨910652, by rfl⟩ : syracuseStep 4856813 = 1821305) B1821305
theorem B6224881 : Blo 1437538 6224881 := bstep (se 2 (by rfl) ⟨2334330, by rfl⟩ : syracuseStep 6224881 = 4668661) B4668661
theorem B17497073 : Blo 1437538 17497073 := bstep (se 2 (by rfl) ⟨6561402, by rfl⟩ : syracuseStep 17497073 = 13122805) B13122805
theorem B1727491 : Blo 1437538 1727491 := bstep (se 1 (by rfl) ⟨1295618, by rfl⟩ : syracuseStep 1727491 = 2591237) B2591237
theorem B16374797 : Blo 1437538 16374797 := bstep (se 3 (by rfl) ⟨3070274, by rfl⟩ : syracuseStep 16374797 = 6140549) B6140549
theorem B3234833 : Blo 1437538 3234833 := bstep (se 2 (by rfl) ⟨1213062, by rfl⟩ : syracuseStep 3234833 = 2426125) B2426125
theorem B3070993 : Blo 1437538 3070993 := bstep (se 2 (by rfl) ⟨1151622, by rfl⟩ : syracuseStep 3070993 = 2303245) B2303245
theorem B3234851 : Blo 1437538 3234851 := bstep (se 1 (by rfl) ⟨2426138, by rfl⟩ : syracuseStep 3234851 = 4852277) B4852277
theorem B4856867 : Blo 1437538 4856867 := bstep (se 1 (by rfl) ⟨3642650, by rfl⟩ : syracuseStep 4856867 = 7285301) B7285301
theorem B2047027 : Blo 1437538 2047027 := bstep (se 1 (by rfl) ⟨1535270, by rfl⟩ : syracuseStep 2047027 = 3070541) B3070541
theorem B4922477 : Blo 1437538 4922477 := bstep (se 3 (by rfl) ⟨922964, by rfl⟩ : syracuseStep 4922477 = 1845929) B1845929
theorem B2047123 : Blo 1437538 2047123 := bstep (se 1 (by rfl) ⟨1535342, by rfl⟩ : syracuseStep 2047123 = 3070685) B3070685
theorem B3235121 : Blo 1437538 3235121 := bstep (se 2 (by rfl) ⟨1213170, by rfl⟩ : syracuseStep 3235121 = 2426341) B2426341
theorem B4857137 : Blo 1437538 4857137 := bstep (se 2 (by rfl) ⟨1821426, by rfl⟩ : syracuseStep 4857137 = 3642853) B3642853
theorem B3235139 : Blo 1437538 3235139 := bstep (se 1 (by rfl) ⟨2426354, by rfl⟩ : syracuseStep 3235139 = 4852709) B4852709
theorem B7282061 : Blo 1437538 7282061 := bstep (se 3 (by rfl) ⟨1365386, by rfl⟩ : syracuseStep 7282061 = 2730773) B2730773
theorem B3235409 : Blo 1437538 3235409 := bstep (se 2 (by rfl) ⟨1213278, by rfl⟩ : syracuseStep 3235409 = 2426557) B2426557
theorem B3235427 : Blo 1437538 3235427 := bstep (se 1 (by rfl) ⟨2426570, by rfl⟩ : syracuseStep 3235427 = 4853141) B4853141
theorem B2047619 : Blo 1437538 2047619 := bstep (se 1 (by rfl) ⟨1535714, by rfl⟩ : syracuseStep 2047619 = 3071429) B3071429
theorem B4857677 : Blo 1437538 4857677 := bstep (se 3 (by rfl) ⟨910814, by rfl⟩ : syracuseStep 4857677 = 1821629) B1821629
theorem B1752931 : Blo 1437538 1752931 := bstep (se 1 (by rfl) ⟨1314698, by rfl⟩ : syracuseStep 1752931 = 2629397) B2629397
theorem B3235697 : Blo 1437538 3235697 := bstep (se 2 (by rfl) ⟨1213386, by rfl⟩ : syracuseStep 3235697 = 2426773) B2426773
theorem B3235715 : Blo 1437538 3235715 := bstep (se 1 (by rfl) ⟨2426786, by rfl⟩ : syracuseStep 3235715 = 4853573) B4853573
theorem B4857731 : Blo 1437538 4857731 := bstep (se 1 (by rfl) ⟨3643298, by rfl⟩ : syracuseStep 4857731 = 7286597) B7286597
theorem B3235841 : Blo 1437538 3235841 := bstep (se 2 (by rfl) ⟨1213440, by rfl⟩ : syracuseStep 3235841 = 2426881) B2426881
theorem B3072001 : Blo 1437538 3072001 := bstep (se 2 (by rfl) ⟨1152000, by rfl⟩ : syracuseStep 3072001 = 2304001) B2304001
theorem B7004225 : Blo 1437538 7004225 := bstep (se 2 (by rfl) ⟨2626584, by rfl⟩ : syracuseStep 7004225 = 5253169) B5253169
theorem B6144173 : Blo 1437538 6144173 := bstep (se 3 (by rfl) ⟨1152032, by rfl⟩ : syracuseStep 6144173 = 2304065) B2304065
theorem B3236057 : Blo 1437538 3236057 := bstep (se 2 (by rfl) ⟨1213521, by rfl⟩ : syracuseStep 3236057 = 2427043) B2427043
theorem B2916569 : Blo 1437538 2916569 := bstep (se 2 (by rfl) ⟨1093713, by rfl⟩ : syracuseStep 2916569 = 2187427) B2187427
theorem B3072257 : Blo 1437538 3072257 := bstep (se 2 (by rfl) ⟨1152096, by rfl⟩ : syracuseStep 3072257 = 2304193) B2304193
theorem B1458443 : Blo 1437538 1458443 := bstep (se 1 (by rfl) ⟨1093832, by rfl⟩ : syracuseStep 1458443 = 2187665) B2187665
theorem B3236147 : Blo 1437538 3236147 := bstep (se 1 (by rfl) ⟨2427110, by rfl⟩ : syracuseStep 3236147 = 4854221) B4854221
theorem B4858163 : Blo 1437538 4858163 := bstep (se 1 (by rfl) ⟨3643622, by rfl⟩ : syracuseStep 4858163 = 7287245) B7287245
theorem B3236183 : Blo 1437538 3236183 := bstep (se 1 (by rfl) ⟨2427137, by rfl⟩ : syracuseStep 3236183 = 4854275) B4854275
theorem B3072343 : Blo 1437538 3072343 := bstep (se 1 (by rfl) ⟨2304257, by rfl⟩ : syracuseStep 3072343 = 4608515) B4608515
theorem B5464493 : Blo 1437538 5464493 := bstep (se 3 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 5464493 = 2049185) B2049185
theorem B5464523 : Blo 1437538 5464523 := bstep (se 1 (by rfl) ⟨4098392, by rfl⟩ : syracuseStep 5464523 = 8196785) B8196785
theorem B1556983 : Blo 1437538 1556983 := bstep (se 1 (by rfl) ⟨1167737, by rfl⟩ : syracuseStep 1556983 = 2335475) B2335475
theorem B5186051 : Blo 1437538 5186051 := bstep (se 1 (by rfl) ⟨3889538, by rfl⟩ : syracuseStep 5186051 = 7779077) B7779077
theorem B3236363 : Blo 1437538 3236363 := bstep (se 1 (by rfl) ⟨2427272, by rfl⟩ : syracuseStep 3236363 = 4854545) B4854545
theorem B3457559 : Blo 1437538 3457559 := bstep (se 1 (by rfl) ⟨2593169, by rfl⟩ : syracuseStep 3457559 = 5186339) B5186339
theorem B3236417 : Blo 1437538 3236417 := bstep (se 2 (by rfl) ⟨1213656, by rfl⟩ : syracuseStep 3236417 = 2427313) B2427313
theorem B4858433 : Blo 1437538 4858433 := bstep (se 2 (by rfl) ⟨1821912, by rfl⟩ : syracuseStep 4858433 = 3643825) B3643825
theorem B8192663 : Blo 1437538 8192663 := bstep (se 1 (by rfl) ⟨6144497, by rfl⟩ : syracuseStep 8192663 = 12288995) B12288995
theorem B23331509 : Blo 1437538 23331509 := bstep (se 5 (by rfl) ⟨1093664, by rfl⟩ : syracuseStep 23331509 = 2187329) B2187329
theorem B2302681 : Blo 1437538 2302681 := bstep (se 2 (by rfl) ⟨863505, by rfl⟩ : syracuseStep 2302681 = 1727011) B1727011
theorem B3236633 : Blo 1437538 3236633 := bstep (se 2 (by rfl) ⟨1213737, by rfl⟩ : syracuseStep 3236633 = 2427475) B2427475
theorem B59081525 : Blo 1437538 59081525 := bstep (se 5 (by rfl) ⟨2769446, by rfl⟩ : syracuseStep 59081525 = 5538893) B5538893
theorem B4670273 : Blo 1437538 4670273 := bstep (se 2 (by rfl) ⟨1751352, by rfl⟩ : syracuseStep 4670273 = 3502705) B3502705
theorem B3236723 : Blo 1437538 3236723 := bstep (se 1 (by rfl) ⟨2427542, by rfl⟩ : syracuseStep 3236723 = 4855085) B4855085
theorem B1459063 : Blo 1437538 1459063 := bstep (se 1 (by rfl) ⟨1094297, by rfl⟩ : syracuseStep 1459063 = 2188595) B2188595
theorem B3236759 : Blo 1437538 3236759 := bstep (se 1 (by rfl) ⟨2427569, by rfl⟩ : syracuseStep 3236759 = 4855139) B4855139
theorem B2769817 : Blo 1437538 2769817 := bstep (se 2 (by rfl) ⟨1038681, by rfl⟩ : syracuseStep 2769817 = 2077363) B2077363
theorem B10363909 : Blo 1437538 10363909 := bstep (se 4 (by rfl) ⟨971616, by rfl⟩ : syracuseStep 10363909 = 1943233) B1943233
theorem B3236939 : Blo 1437538 3236939 := bstep (se 1 (by rfl) ⟨2427704, by rfl⟩ : syracuseStep 3236939 = 4855409) B4855409
theorem B2425943 : Blo 1437538 2425943 := bstep (se 1 (by rfl) ⟨1819457, by rfl⟩ : syracuseStep 2425943 = 3638915) B3638915
theorem B5465177 : Blo 1437538 5465177 := bstep (se 2 (by rfl) ⟨2049441, by rfl⟩ : syracuseStep 5465177 = 4098883) B4098883
theorem B4097117 : Blo 1437538 4097117 := bstep (se 3 (by rfl) ⟨768209, by rfl⟩ : syracuseStep 4097117 = 1536419) B1536419
theorem B1639531 : Blo 1437538 1639531 := bstep (se 1 (by rfl) ⟨1229648, by rfl⟩ : syracuseStep 1639531 = 2459297) B2459297
theorem B3236993 : Blo 1437538 3236993 := bstep (se 2 (by rfl) ⟨1213872, by rfl⟩ : syracuseStep 3236993 = 2427745) B2427745
theorem B7283843 : Blo 1437538 7283843 := bstep (se 1 (by rfl) ⟨5462882, by rfl⟩ : syracuseStep 7283843 = 10925765) B10925765
theorem B2426071 : Blo 1437538 2426071 := bstep (se 1 (by rfl) ⟨1819553, by rfl⟩ : syracuseStep 2426071 = 3639107) B3639107
theorem B8299841 : Blo 1437538 8299841 := bstep (se 2 (by rfl) ⟨3112440, by rfl⟩ : syracuseStep 8299841 = 6224881) B6224881
theorem B2303321 : Blo 1437538 2303321 := bstep (se 2 (by rfl) ⟨863745, by rfl⟩ : syracuseStep 2303321 = 1727491) B1727491
theorem B3237209 : Blo 1437538 3237209 := bstep (se 2 (by rfl) ⟨1213953, by rfl⟩ : syracuseStep 3237209 = 2427907) B2427907
theorem B13305181 : Blo 1437538 13305181 := bstep (se 3 (by rfl) ⟨2494721, by rfl⟩ : syracuseStep 13305181 = 4989443) B4989443
theorem B5465495 : Blo 1437538 5465495 := bstep (se 1 (by rfl) ⟨4099121, by rfl⟩ : syracuseStep 5465495 = 8198243) B8198243
theorem B2729369 : Blo 1437538 2729369 := bstep (se 2 (by rfl) ⟨1023513, by rfl⟩ : syracuseStep 2729369 = 2047027) B2047027
theorem B3237299 : Blo 1437538 3237299 := bstep (se 1 (by rfl) ⟨2427974, by rfl⟩ : syracuseStep 3237299 = 4855949) B4855949
theorem B4097459 : Blo 1437538 4097459 := bstep (se 1 (by rfl) ⟨3073094, by rfl⟩ : syracuseStep 4097459 = 6146189) B6146189
theorem B10372531 : Blo 1437538 10372531 := bstep (se 1 (by rfl) ⟨7779398, by rfl⟩ : syracuseStep 10372531 = 15558797) B15558797
theorem B5834177 : Blo 1437538 5834177 := bstep (se 2 (by rfl) ⟨2187816, by rfl⟩ : syracuseStep 5834177 = 4375633) B4375633
theorem B3237335 : Blo 1437538 3237335 := bstep (se 1 (by rfl) ⟨2428001, by rfl⟩ : syracuseStep 3237335 = 4856003) B4856003
theorem B1820171 : Blo 1437538 1820171 := bstep (se 1 (by rfl) ⟨1365128, by rfl⟩ : syracuseStep 1820171 = 2730257) B2730257
theorem B4605515 : Blo 1437538 4605515 := bstep (se 1 (by rfl) ⟨3454136, by rfl⟩ : syracuseStep 4605515 = 6908273) B6908273
theorem B5187203 : Blo 1437538 5187203 := bstep (se 1 (by rfl) ⟨3890402, by rfl⟩ : syracuseStep 5187203 = 7780805) B7780805
theorem B3237515 : Blo 1437538 3237515 := bstep (se 1 (by rfl) ⟨2428136, by rfl⟩ : syracuseStep 3237515 = 4856273) B4856273
theorem B3237569 : Blo 1437538 3237569 := bstep (se 2 (by rfl) ⟨1214088, by rfl⟩ : syracuseStep 3237569 = 2428177) B2428177
theorem B12281645 : Blo 1437538 12281645 := bstep (se 3 (by rfl) ⟨2302808, by rfl⟩ : syracuseStep 12281645 = 4605617) B4605617
theorem B2156363 : Blo 1437538 2156363 := bstep (se 1 (by rfl) ⟨1617272, by rfl⟩ : syracuseStep 2156363 = 3234545) B3234545
theorem B13117259 : Blo 1437538 13117259 := bstep (se 1 (by rfl) ⟨9837944, by rfl⟩ : syracuseStep 13117259 = 19675889) B19675889
theorem B2426699 : Blo 1437538 2426699 := bstep (se 1 (by rfl) ⟨1820024, by rfl⟩ : syracuseStep 2426699 = 3640049) B3640049
theorem B5326667 : Blo 1437538 5326667 := bstep (se 1 (by rfl) ⟨3995000, by rfl⟩ : syracuseStep 5326667 = 7990001) B7990001
theorem B2156375 : Blo 1437538 2156375 := bstep (se 1 (by rfl) ⟨1617281, by rfl⟩ : syracuseStep 2156375 = 3234563) B3234563
theorem B2156441 : Blo 1437538 2156441 := bstep (se 2 (by rfl) ⟨808665, by rfl⟩ : syracuseStep 2156441 = 1617331) B1617331
theorem B3237785 : Blo 1437538 3237785 := bstep (se 2 (by rfl) ⟨1214169, by rfl⟩ : syracuseStep 3237785 = 2428339) B2428339
theorem B2426827 : Blo 1437538 2426827 := bstep (se 1 (by rfl) ⟨1820120, by rfl⟩ : syracuseStep 2426827 = 3640241) B3640241
theorem B4605913 : Blo 1437538 4605913 := bstep (se 2 (by rfl) ⟨1727217, by rfl⟩ : syracuseStep 4605913 = 3454435) B3454435
theorem B3237875 : Blo 1437538 3237875 := bstep (se 1 (by rfl) ⟨2428406, by rfl⟩ : syracuseStep 3237875 = 4856813) B4856813
theorem B2156555 : Blo 1437538 2156555 := bstep (se 1 (by rfl) ⟨1617416, by rfl⟩ : syracuseStep 2156555 = 3234833) B3234833
theorem B24586253 : Blo 1437538 24586253 := bstep (se 3 (by rfl) ⟨4609922, by rfl⟩ : syracuseStep 24586253 = 9219845) B9219845
theorem B2156567 : Blo 1437538 2156567 := bstep (se 1 (by rfl) ⟨1617425, by rfl⟩ : syracuseStep 2156567 = 3234851) B3234851
theorem B3237911 : Blo 1437538 3237911 := bstep (se 1 (by rfl) ⟨2428433, by rfl⟩ : syracuseStep 3237911 = 4856867) B4856867
theorem B2459735 : Blo 1437538 2459735 := bstep (se 1 (by rfl) ⟨1844801, by rfl⟩ : syracuseStep 2459735 = 3689603) B3689603
theorem B2156633 : Blo 1437538 2156633 := bstep (se 2 (by rfl) ⟨808737, by rfl⟩ : syracuseStep 2156633 = 1617475) B1617475
theorem B2426969 : Blo 1437538 2426969 := bstep (se 2 (by rfl) ⟨910113, by rfl⟩ : syracuseStep 2426969 = 1820227) B1820227
theorem B2156747 : Blo 1437538 2156747 := bstep (se 1 (by rfl) ⟨1617560, by rfl⟩ : syracuseStep 2156747 = 3235121) B3235121
theorem B1820875 : Blo 1437538 1820875 := bstep (se 1 (by rfl) ⟨1365656, by rfl⟩ : syracuseStep 1820875 = 2731313) B2731313
theorem B3238091 : Blo 1437538 3238091 := bstep (se 1 (by rfl) ⟨2428568, by rfl⟩ : syracuseStep 3238091 = 4857137) B4857137
theorem B2156759 : Blo 1437538 2156759 := bstep (se 1 (by rfl) ⟨1617569, by rfl⟩ : syracuseStep 2156759 = 3235139) B3235139
theorem B2427097 : Blo 1437538 2427097 := bstep (se 2 (by rfl) ⟨910161, by rfl⟩ : syracuseStep 2427097 = 1820323) B1820323
theorem B3238145 : Blo 1437538 3238145 := bstep (se 2 (by rfl) ⟨1214304, by rfl⟩ : syracuseStep 3238145 = 2428609) B2428609
theorem B2156825 : Blo 1437538 2156825 := bstep (se 2 (by rfl) ⟨808809, by rfl⟩ : syracuseStep 2156825 = 1617619) B1617619
theorem B5835083 : Blo 1437538 5835083 := bstep (se 1 (by rfl) ⟨4376312, by rfl⟩ : syracuseStep 5835083 = 8752625) B8752625
theorem B4852061 : Blo 1437538 4852061 := bstep (se 3 (by rfl) ⟨909761, by rfl⟩ : syracuseStep 4852061 = 1819523) B1819523
theorem B2156939 : Blo 1437538 2156939 := bstep (se 1 (by rfl) ⟨1617704, by rfl⟩ : syracuseStep 2156939 = 3235409) B3235409
theorem B2156951 : Blo 1437538 2156951 := bstep (se 1 (by rfl) ⟨1617713, by rfl⟩ : syracuseStep 2156951 = 3235427) B3235427
theorem B3639755 : Blo 1437538 3639755 := bstep (se 1 (by rfl) ⟨2729816, by rfl⟩ : syracuseStep 3639755 = 5459633) B5459633
theorem B1821143 : Blo 1437538 1821143 := bstep (se 1 (by rfl) ⟨1365857, by rfl⟩ : syracuseStep 1821143 = 2731715) B2731715
theorem B2157017 : Blo 1437538 2157017 := bstep (se 2 (by rfl) ⟨808881, by rfl⟩ : syracuseStep 2157017 = 1617763) B1617763
theorem B3238361 : Blo 1437538 3238361 := bstep (se 2 (by rfl) ⟨1214385, by rfl⟩ : syracuseStep 3238361 = 2428771) B2428771
theorem B2337241 : Blo 1437538 2337241 := bstep (se 2 (by rfl) ⟨876465, by rfl⟩ : syracuseStep 2337241 = 1752931) B1752931
theorem B3238451 : Blo 1437538 3238451 := bstep (se 1 (by rfl) ⟨2428838, by rfl⟩ : syracuseStep 3238451 = 4857677) B4857677
theorem B2157131 : Blo 1437538 2157131 := bstep (se 1 (by rfl) ⟨1617848, by rfl⟩ : syracuseStep 2157131 = 3235697) B3235697
theorem B2157143 : Blo 1437538 2157143 := bstep (se 1 (by rfl) ⟨1617857, by rfl⟩ : syracuseStep 2157143 = 3235715) B3235715
theorem B3238487 : Blo 1437538 3238487 := bstep (se 1 (by rfl) ⟨2428865, by rfl⟩ : syracuseStep 3238487 = 4857731) B4857731
theorem B4672093 : Blo 1437538 4672093 := bstep (se 3 (by rfl) ⟨876017, by rfl⟩ : syracuseStep 4672093 = 1752035) B1752035
theorem B4991581 : Blo 1437538 4991581 := bstep (se 3 (by rfl) ⟨935921, by rfl⟩ : syracuseStep 4991581 = 1871843) B1871843
theorem B2157209 : Blo 1437538 2157209 := bstep (se 2 (by rfl) ⟨808953, by rfl⟩ : syracuseStep 2157209 = 1617907) B1617907
theorem B5458691 : Blo 1437538 5458691 := bstep (se 1 (by rfl) ⟨4094018, by rfl⟩ : syracuseStep 5458691 = 8188037) B8188037
theorem B2157323 : Blo 1437538 2157323 := bstep (se 1 (by rfl) ⟨1617992, by rfl⟩ : syracuseStep 2157323 = 3235985) B3235985
theorem B1641227 : Blo 1437538 1641227 := bstep (se 1 (by rfl) ⟨1230920, by rfl⟩ : syracuseStep 1641227 = 2461841) B2461841
theorem B3238667 : Blo 1437538 3238667 := bstep (se 1 (by rfl) ⟨2429000, by rfl⟩ : syracuseStep 3238667 = 4858001) B4858001
theorem B2804503 : Blo 1437538 2804503 := bstep (se 1 (by rfl) ⟨2103377, by rfl⟩ : syracuseStep 2804503 = 4206755) B4206755
theorem B2157335 : Blo 1437538 2157335 := bstep (se 1 (by rfl) ⟨1618001, by rfl⟩ : syracuseStep 2157335 = 3236003) B3236003
theorem B2427671 : Blo 1437538 2427671 := bstep (se 1 (by rfl) ⟨1820753, by rfl⟩ : syracuseStep 2427671 = 3641507) B3641507
theorem B3238721 : Blo 1437538 3238721 := bstep (se 2 (by rfl) ⟨1214520, by rfl⟩ : syracuseStep 3238721 = 2429041) B2429041
theorem B2730827 : Blo 1437538 2730827 := bstep (se 1 (by rfl) ⟨2048120, by rfl⟩ : syracuseStep 2730827 = 4096241) B4096241
theorem B2157401 : Blo 1437538 2157401 := bstep (se 2 (by rfl) ⟨809025, by rfl⟩ : syracuseStep 2157401 = 1618051) B1618051
theorem B2427799 : Blo 1437538 2427799 := bstep (se 1 (by rfl) ⟨1820849, by rfl⟩ : syracuseStep 2427799 = 3641699) B3641699
theorem B2157515 : Blo 1437538 2157515 := bstep (se 1 (by rfl) ⟨1618136, by rfl⟩ : syracuseStep 2157515 = 3236273) B3236273
theorem B2157527 : Blo 1437538 2157527 := bstep (se 1 (by rfl) ⟨1618145, by rfl⟩ : syracuseStep 2157527 = 3236291) B3236291
theorem B2731009 : Blo 1437538 2731009 := bstep (se 2 (by rfl) ⟨1024128, by rfl⟩ : syracuseStep 2731009 = 2048257) B2048257
theorem B2157593 : Blo 1437538 2157593 := bstep (se 2 (by rfl) ⟨809097, by rfl⟩ : syracuseStep 2157593 = 1618195) B1618195
theorem B3238937 : Blo 1437538 3238937 := bstep (se 2 (by rfl) ⟨1214601, by rfl⟩ : syracuseStep 3238937 = 2429203) B2429203
theorem B2157707 : Blo 1437538 2157707 := bstep (se 1 (by rfl) ⟨1618280, by rfl⟩ : syracuseStep 2157707 = 3236561) B3236561
theorem B2157719 : Blo 1437538 2157719 := bstep (se 1 (by rfl) ⟨1618289, by rfl⟩ : syracuseStep 2157719 = 3236579) B3236579
theorem B1821847 : Blo 1437538 1821847 := bstep (se 1 (by rfl) ⟨1366385, by rfl⟩ : syracuseStep 1821847 = 2732771) B2732771
theorem B4607155 : Blo 1437538 4607155 := bstep (se 1 (by rfl) ⟨3455366, by rfl⟩ : syracuseStep 4607155 = 6910733) B6910733
theorem B5459147 : Blo 1437538 5459147 := bstep (se 1 (by rfl) ⟨4094360, by rfl⟩ : syracuseStep 5459147 = 8188721) B8188721
theorem B2075863 : Blo 1437538 2075863 := bstep (se 1 (by rfl) ⟨1556897, by rfl⟩ : syracuseStep 2075863 = 3113795) B3113795
theorem B2157785 : Blo 1437538 2157785 := bstep (se 2 (by rfl) ⟨809169, by rfl⟩ : syracuseStep 2157785 = 1618339) B1618339
theorem B3280193 : Blo 1437538 3280193 := bstep (se 2 (by rfl) ⟨1230072, by rfl⟩ : syracuseStep 3280193 = 2460145) B2460145
theorem B2157899 : Blo 1437538 2157899 := bstep (se 1 (by rfl) ⟨1618424, by rfl⟩ : syracuseStep 2157899 = 3236849) B3236849
theorem B2157911 : Blo 1437538 2157911 := bstep (se 1 (by rfl) ⟨1618433, by rfl⟩ : syracuseStep 2157911 = 3236867) B3236867
theorem B20508005 : Blo 1437538 20508005 := bstep (se 4 (by rfl) ⟨1922625, by rfl⟩ : syracuseStep 20508005 = 3845251) B3845251
theorem B1617259 : Blo 1437538 1617259 := bstep (se 1 (by rfl) ⟨1212944, by rfl⟩ : syracuseStep 1617259 = 2425889) B2425889
theorem B5459345 : Blo 1437538 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B3640727 : Blo 1437538 3640727 := bstep (se 1 (by rfl) ⟨2730545, by rfl⟩ : syracuseStep 3640727 = 5461091) B5461091
theorem B2157977 : Blo 1437538 2157977 := bstep (se 2 (by rfl) ⟨809241, by rfl⟩ : syracuseStep 2157977 = 1618483) B1618483
theorem B1944985 : Blo 1437538 1944985 := bstep (se 2 (by rfl) ⟨729369, by rfl⟩ : syracuseStep 1944985 = 1458739) B1458739
theorem B2731457 : Blo 1437538 2731457 := bstep (se 2 (by rfl) ⟨1024296, by rfl⟩ : syracuseStep 2731457 = 2048593) B2048593
theorem B6147521 : Blo 1437538 6147521 := bstep (se 2 (by rfl) ⟨2305320, by rfl⟩ : syracuseStep 6147521 = 4610641) B4610641
theorem B4853195 : Blo 1437538 4853195 := bstep (se 1 (by rfl) ⟨3639896, by rfl⟩ : syracuseStep 4853195 = 7279793) B7279793
theorem B1617367 : Blo 1437538 1617367 := bstep (se 1 (by rfl) ⟨1213025, by rfl⟩ : syracuseStep 1617367 = 2426051) B2426051
theorem B1535479 : Blo 1437538 1535479 := bstep (se 1 (by rfl) ⟨1151609, by rfl⟩ : syracuseStep 1535479 = 2303219) B2303219
theorem B2158091 : Blo 1437538 2158091 := bstep (se 1 (by rfl) ⟨1618568, by rfl⟩ : syracuseStep 2158091 = 3237137) B3237137
theorem B2428427 : Blo 1437538 2428427 := bstep (se 1 (by rfl) ⟨1821320, by rfl⟩ : syracuseStep 2428427 = 3642641) B3642641
theorem B6557207 : Blo 1437538 6557207 := bstep (se 1 (by rfl) ⟨4917905, by rfl⟩ : syracuseStep 6557207 = 9835811) B9835811
theorem B2158103 : Blo 1437538 2158103 := bstep (se 1 (by rfl) ⟨1618577, by rfl⟩ : syracuseStep 2158103 = 3237155) B3237155
theorem B3690073 : Blo 1437538 3690073 := bstep (se 2 (by rfl) ⟨1383777, by rfl⟩ : syracuseStep 3690073 = 2767555) B2767555
theorem B2158169 : Blo 1437538 2158169 := bstep (se 2 (by rfl) ⟨809313, by rfl⟩ : syracuseStep 2158169 = 1618627) B1618627
theorem B7278173 : Blo 1437538 7278173 := bstep (se 3 (by rfl) ⟨1364657, by rfl⟩ : syracuseStep 7278173 = 2729315) B2729315
theorem B1617547 : Blo 1437538 1617547 := bstep (se 1 (by rfl) ⟨1213160, by rfl⟩ : syracuseStep 1617547 = 2426321) B2426321
theorem B2428555 : Blo 1437538 2428555 := bstep (se 1 (by rfl) ⟨1821416, by rfl⟩ : syracuseStep 2428555 = 3642833) B3642833
theorem B2158283 : Blo 1437538 2158283 := bstep (se 1 (by rfl) ⟨1618712, by rfl⟩ : syracuseStep 2158283 = 3237425) B3237425
theorem B2158295 : Blo 1437538 2158295 := bstep (se 1 (by rfl) ⟨1618721, by rfl⟩ : syracuseStep 2158295 = 3237443) B3237443
theorem B4853465 : Blo 1437538 4853465 := bstep (se 2 (by rfl) ⟨1820049, by rfl⟩ : syracuseStep 4853465 = 3640099) B3640099
theorem B1617655 : Blo 1437538 1617655 := bstep (se 1 (by rfl) ⟨1213241, by rfl⟩ : syracuseStep 1617655 = 2426483) B2426483
theorem B2731799 : Blo 1437538 2731799 := bstep (se 1 (by rfl) ⟨2048849, by rfl⟩ : syracuseStep 2731799 = 4097699) B4097699
theorem B6147863 : Blo 1437538 6147863 := bstep (se 1 (by rfl) ⟨4610897, by rfl⟩ : syracuseStep 6147863 = 9221795) B9221795
theorem B2158361 : Blo 1437538 2158361 := bstep (se 2 (by rfl) ⟨809385, by rfl⟩ : syracuseStep 2158361 = 1618771) B1618771
theorem B2428697 : Blo 1437538 2428697 := bstep (se 2 (by rfl) ⟨910761, by rfl⟩ : syracuseStep 2428697 = 1821523) B1821523
theorem B10923821 : Blo 1437538 10923821 := bstep (se 3 (by rfl) ⟨2048216, by rfl⟩ : syracuseStep 10923821 = 4096433) B4096433
theorem B1437547 : Blo 1437538 1437547 := bstep (se 1 (by rfl) ⟨1078160, by rfl⟩ : syracuseStep 1437547 = 2156321) B2156321
theorem B1535851 : Blo 1437538 1535851 := bstep (se 1 (by rfl) ⟨1151888, by rfl⟩ : syracuseStep 1535851 = 2303777) B2303777
theorem B1437559 : Blo 1437538 1437559 := bstep (se 1 (by rfl) ⟨1078169, by rfl⟩ : syracuseStep 1437559 = 2156339) B2156339
theorem B1437579 : Blo 1437538 1437579 := bstep (se 1 (by rfl) ⟨1078184, by rfl⟩ : syracuseStep 1437579 = 2156369) B2156369
theorem B2158475 : Blo 1437538 2158475 := bstep (se 1 (by rfl) ⟨1618856, by rfl⟩ : syracuseStep 2158475 = 3237713) B3237713
theorem B1437591 : Blo 1437538 1437591 := bstep (se 1 (by rfl) ⟨1078193, by rfl⟩ : syracuseStep 1437591 = 2156387) B2156387
theorem B2158487 : Blo 1437538 2158487 := bstep (se 1 (by rfl) ⟨1618865, by rfl⟩ : syracuseStep 2158487 = 3237731) B3237731
theorem B2428825 : Blo 1437538 2428825 := bstep (se 2 (by rfl) ⟨910809, by rfl⟩ : syracuseStep 2428825 = 1821619) B1821619
theorem B1437611 : Blo 1437538 1437611 := bstep (se 1 (by rfl) ⟨1078208, by rfl⟩ : syracuseStep 1437611 = 2156417) B2156417
theorem B1617835 : Blo 1437538 1617835 := bstep (se 1 (by rfl) ⟨1213376, by rfl⟩ : syracuseStep 1617835 = 2426753) B2426753
theorem B79826867 : Blo 1437538 79826867 := bstep (se 1 (by rfl) ⟨59870150, by rfl⟩ : syracuseStep 79826867 = 119740301) B119740301
theorem B1437623 : Blo 1437538 1437623 := bstep (se 1 (by rfl) ⟨1078217, by rfl⟩ : syracuseStep 1437623 = 2156435) B2156435
theorem B1437643 : Blo 1437538 1437643 := bstep (se 1 (by rfl) ⟨1078232, by rfl⟩ : syracuseStep 1437643 = 2156465) B2156465
theorem B1437655 : Blo 1437538 1437655 := bstep (se 1 (by rfl) ⟨1078241, by rfl⟩ : syracuseStep 1437655 = 2156483) B2156483
theorem B2158553 : Blo 1437538 2158553 := bstep (se 2 (by rfl) ⟨809457, by rfl⟩ : syracuseStep 2158553 = 1618915) B1618915
theorem B1437675 : Blo 1437538 1437675 := bstep (se 1 (by rfl) ⟨1078256, by rfl⟩ : syracuseStep 1437675 = 2156513) B2156513
theorem B1437687 : Blo 1437538 1437687 := bstep (se 1 (by rfl) ⟨1078265, by rfl⟩ : syracuseStep 1437687 = 2156531) B2156531
theorem B1437707 : Blo 1437538 1437707 := bstep (se 1 (by rfl) ⟨1078280, by rfl⟩ : syracuseStep 1437707 = 2156561) B2156561
theorem B1437719 : Blo 1437538 1437719 := bstep (se 1 (by rfl) ⟨1078289, by rfl⟩ : syracuseStep 1437719 = 2156579) B2156579
theorem B1617943 : Blo 1437538 1617943 := bstep (se 1 (by rfl) ⟨1213457, by rfl⟩ : syracuseStep 1617943 = 2426915) B2426915
theorem B1437739 : Blo 1437538 1437739 := bstep (se 1 (by rfl) ⟨1078304, by rfl⟩ : syracuseStep 1437739 = 2156609) B2156609
theorem B3641395 : Blo 1437538 3641395 := bstep (se 1 (by rfl) ⟨2731046, by rfl⟩ : syracuseStep 3641395 = 5462093) B5462093
theorem B1437751 : Blo 1437538 1437751 := bstep (se 1 (by rfl) ⟨1078313, by rfl⟩ : syracuseStep 1437751 = 2156627) B2156627
theorem B1437771 : Blo 1437538 1437771 := bstep (se 1 (by rfl) ⟨1078328, by rfl⟩ : syracuseStep 1437771 = 2156657) B2156657
theorem B2158667 : Blo 1437538 2158667 := bstep (se 1 (by rfl) ⟨1619000, by rfl⟩ : syracuseStep 2158667 = 3238001) B3238001
theorem B1437783 : Blo 1437538 1437783 := bstep (se 1 (by rfl) ⟨1078337, by rfl⟩ : syracuseStep 1437783 = 2156675) B2156675
theorem B2158679 : Blo 1437538 2158679 := bstep (se 1 (by rfl) ⟨1619009, by rfl⟩ : syracuseStep 2158679 = 3238019) B3238019
theorem B1437803 : Blo 1437538 1437803 := bstep (se 1 (by rfl) ⟨1078352, by rfl⟩ : syracuseStep 1437803 = 2156705) B2156705
theorem B1437815 : Blo 1437538 1437815 := bstep (se 1 (by rfl) ⟨1078361, by rfl⟩ : syracuseStep 1437815 = 2156723) B2156723
theorem B1437835 : Blo 1437538 1437835 := bstep (se 1 (by rfl) ⟨1078376, by rfl⟩ : syracuseStep 1437835 = 2156753) B2156753
theorem B1437847 : Blo 1437538 1437847 := bstep (se 1 (by rfl) ⟨1078385, by rfl⟩ : syracuseStep 1437847 = 2156771) B2156771
theorem B5460119 : Blo 1437538 5460119 := bstep (se 1 (by rfl) ⟨4095089, by rfl⟩ : syracuseStep 5460119 = 8190179) B8190179
theorem B2158745 : Blo 1437538 2158745 := bstep (se 2 (by rfl) ⟨809529, by rfl⟩ : syracuseStep 2158745 = 1619059) B1619059
theorem B1437867 : Blo 1437538 1437867 := bstep (se 1 (by rfl) ⟨1078400, by rfl⟩ : syracuseStep 1437867 = 2156801) B2156801
theorem B10514609 : Blo 1437538 10514609 := bstep (se 2 (by rfl) ⟨3942978, by rfl⟩ : syracuseStep 10514609 = 7885957) B7885957
theorem B1437879 : Blo 1437538 1437879 := bstep (se 1 (by rfl) ⟨1078409, by rfl⟩ : syracuseStep 1437879 = 2156819) B2156819
theorem B3641537 : Blo 1437538 3641537 := bstep (se 2 (by rfl) ⟨1365576, by rfl⟩ : syracuseStep 3641537 = 2731153) B2731153
theorem B1437899 : Blo 1437538 1437899 := bstep (se 1 (by rfl) ⟨1078424, by rfl⟩ : syracuseStep 1437899 = 2156849) B2156849
theorem B1618123 : Blo 1437538 1618123 := bstep (se 1 (by rfl) ⟨1213592, by rfl⟩ : syracuseStep 1618123 = 2427185) B2427185
theorem B1437911 : Blo 1437538 1437911 := bstep (se 1 (by rfl) ⟨1078433, by rfl⟩ : syracuseStep 1437911 = 2156867) B2156867
theorem B1437931 : Blo 1437538 1437931 := bstep (se 1 (by rfl) ⟨1078448, by rfl⟩ : syracuseStep 1437931 = 2156897) B2156897
theorem B1437943 : Blo 1437538 1437943 := bstep (se 1 (by rfl) ⟨1078457, by rfl⟩ : syracuseStep 1437943 = 2156915) B2156915
theorem B1437963 : Blo 1437538 1437963 := bstep (se 1 (by rfl) ⟨1078472, by rfl⟩ : syracuseStep 1437963 = 2156945) B2156945
theorem B2158859 : Blo 1437538 2158859 := bstep (se 1 (by rfl) ⟨1619144, by rfl⟩ : syracuseStep 2158859 = 3238289) B3238289
theorem B1437975 : Blo 1437538 1437975 := bstep (se 1 (by rfl) ⟨1078481, by rfl⟩ : syracuseStep 1437975 = 2156963) B2156963
theorem B2158871 : Blo 1437538 2158871 := bstep (se 1 (by rfl) ⟨1619153, by rfl⟩ : syracuseStep 2158871 = 3238307) B3238307
theorem B1437995 : Blo 1437538 1437995 := bstep (se 1 (by rfl) ⟨1078496, by rfl⟩ : syracuseStep 1437995 = 2156993) B2156993
theorem B1438007 : Blo 1437538 1438007 := bstep (se 1 (by rfl) ⟨1078505, by rfl⟩ : syracuseStep 1438007 = 2157011) B2157011
theorem B1618231 : Blo 1437538 1618231 := bstep (se 1 (by rfl) ⟨1213673, by rfl⟩ : syracuseStep 1618231 = 2427347) B2427347
theorem B1438027 : Blo 1437538 1438027 := bstep (se 1 (by rfl) ⟨1078520, by rfl⟩ : syracuseStep 1438027 = 2157041) B2157041
theorem B1438039 : Blo 1437538 1438039 := bstep (se 1 (by rfl) ⟨1078529, by rfl⟩ : syracuseStep 1438039 = 2157059) B2157059
theorem B2158937 : Blo 1437538 2158937 := bstep (se 2 (by rfl) ⟨809601, by rfl⟩ : syracuseStep 2158937 = 1619203) B1619203
theorem B5460317 : Blo 1437538 5460317 := bstep (se 3 (by rfl) ⟨1023809, by rfl⟩ : syracuseStep 5460317 = 2047619) B2047619
theorem B1438059 : Blo 1437538 1438059 := bstep (se 1 (by rfl) ⟨1078544, by rfl⟩ : syracuseStep 1438059 = 2157089) B2157089
theorem B1438071 : Blo 1437538 1438071 := bstep (se 1 (by rfl) ⟨1078553, by rfl⟩ : syracuseStep 1438071 = 2157107) B2157107
theorem B1438091 : Blo 1437538 1438091 := bstep (se 1 (by rfl) ⟨1078568, by rfl⟩ : syracuseStep 1438091 = 2157137) B2157137
theorem B1438103 : Blo 1437538 1438103 := bstep (se 1 (by rfl) ⟨1078577, by rfl⟩ : syracuseStep 1438103 = 2157155) B2157155
theorem B4854167 : Blo 1437538 4854167 := bstep (se 1 (by rfl) ⟨3640625, by rfl⟩ : syracuseStep 4854167 = 7281251) B7281251
theorem B1438123 : Blo 1437538 1438123 := bstep (se 1 (by rfl) ⟨1078592, by rfl⟩ : syracuseStep 1438123 = 2157185) B2157185
theorem B2732467 : Blo 1437538 2732467 := bstep (se 1 (by rfl) ⟨2049350, by rfl⟩ : syracuseStep 2732467 = 4098701) B4098701
theorem B1438135 : Blo 1437538 1438135 := bstep (se 1 (by rfl) ⟨1078601, by rfl⟩ : syracuseStep 1438135 = 2157203) B2157203
theorem B1438155 : Blo 1437538 1438155 := bstep (se 1 (by rfl) ⟨1078616, by rfl⟩ : syracuseStep 1438155 = 2157233) B2157233
theorem B2159051 : Blo 1437538 2159051 := bstep (se 1 (by rfl) ⟨1619288, by rfl⟩ : syracuseStep 2159051 = 3238577) B3238577
theorem B1438167 : Blo 1437538 1438167 := bstep (se 1 (by rfl) ⟨1078625, by rfl⟩ : syracuseStep 1438167 = 2157251) B2157251
theorem B2159063 : Blo 1437538 2159063 := bstep (se 1 (by rfl) ⟨1619297, by rfl⟩ : syracuseStep 2159063 = 3238595) B3238595
theorem B1438187 : Blo 1437538 1438187 := bstep (se 1 (by rfl) ⟨1078640, by rfl⟩ : syracuseStep 1438187 = 2157281) B2157281
theorem B1618411 : Blo 1437538 1618411 := bstep (se 1 (by rfl) ⟨1213808, by rfl⟩ : syracuseStep 1618411 = 2427617) B2427617
theorem B1438199 : Blo 1437538 1438199 := bstep (se 1 (by rfl) ⟨1078649, by rfl⟩ : syracuseStep 1438199 = 2157299) B2157299
theorem B1438219 : Blo 1437538 1438219 := bstep (se 1 (by rfl) ⟨1078664, by rfl⟩ : syracuseStep 1438219 = 2157329) B2157329
theorem B1438231 : Blo 1437538 1438231 := bstep (se 1 (by rfl) ⟨1078673, by rfl⟩ : syracuseStep 1438231 = 2157347) B2157347
theorem B2159129 : Blo 1437538 2159129 := bstep (se 2 (by rfl) ⟨809673, by rfl⟩ : syracuseStep 2159129 = 1619347) B1619347
theorem B1438251 : Blo 1437538 1438251 := bstep (se 1 (by rfl) ⟨1078688, by rfl⟩ : syracuseStep 1438251 = 2157377) B2157377
theorem B1438263 : Blo 1437538 1438263 := bstep (se 1 (by rfl) ⟨1078697, by rfl⟩ : syracuseStep 1438263 = 2157395) B2157395
theorem B1438283 : Blo 1437538 1438283 := bstep (se 1 (by rfl) ⟨1078712, by rfl⟩ : syracuseStep 1438283 = 2157425) B2157425
theorem B1438295 : Blo 1437538 1438295 := bstep (se 1 (by rfl) ⟨1078721, by rfl⟩ : syracuseStep 1438295 = 2157443) B2157443
theorem B1618519 : Blo 1437538 1618519 := bstep (se 1 (by rfl) ⟨1213889, by rfl⟩ : syracuseStep 1618519 = 2427779) B2427779
theorem B1438315 : Blo 1437538 1438315 := bstep (se 1 (by rfl) ⟨1078736, by rfl⟩ : syracuseStep 1438315 = 2157473) B2157473
theorem B1438327 : Blo 1437538 1438327 := bstep (se 1 (by rfl) ⟨1078745, by rfl⟩ : syracuseStep 1438327 = 2157491) B2157491
theorem B1438347 : Blo 1437538 1438347 := bstep (se 1 (by rfl) ⟨1078760, by rfl⟩ : syracuseStep 1438347 = 2157521) B2157521
theorem B2159243 : Blo 1437538 2159243 := bstep (se 1 (by rfl) ⟨1619432, by rfl⟩ : syracuseStep 2159243 = 3238865) B3238865
theorem B1438359 : Blo 1437538 1438359 := bstep (se 1 (by rfl) ⟨1078769, by rfl⟩ : syracuseStep 1438359 = 2157539) B2157539
theorem B2159255 : Blo 1437538 2159255 := bstep (se 1 (by rfl) ⟨1619441, by rfl⟩ : syracuseStep 2159255 = 3238883) B3238883
theorem B1438379 : Blo 1437538 1438379 := bstep (se 1 (by rfl) ⟨1078784, by rfl⟩ : syracuseStep 1438379 = 2157569) B2157569
theorem B10916531 : Blo 1437538 10916531 := bstep (se 1 (by rfl) ⟨8187398, by rfl⟩ : syracuseStep 10916531 = 16374797) B16374797
theorem B1438391 : Blo 1437538 1438391 := bstep (se 1 (by rfl) ⟨1078793, by rfl⟩ : syracuseStep 1438391 = 2157587) B2157587
theorem B5255873 : Blo 1437538 5255873 := bstep (se 2 (by rfl) ⟨1970952, by rfl⟩ : syracuseStep 5255873 = 3941905) B3941905
theorem B1438411 : Blo 1437538 1438411 := bstep (se 1 (by rfl) ⟨1078808, by rfl⟩ : syracuseStep 1438411 = 2157617) B2157617
theorem B12284621 : Blo 1437538 12284621 := bstep (se 3 (by rfl) ⟨2303366, by rfl⟩ : syracuseStep 12284621 = 4606733) B4606733
theorem B1438423 : Blo 1437538 1438423 := bstep (se 1 (by rfl) ⟨1078817, by rfl⟩ : syracuseStep 1438423 = 2157635) B2157635
theorem B1438443 : Blo 1437538 1438443 := bstep (se 1 (by rfl) ⟨1078832, by rfl⟩ : syracuseStep 1438443 = 2157665) B2157665
theorem B3281651 : Blo 1437538 3281651 := bstep (se 1 (by rfl) ⟨2461238, by rfl⟩ : syracuseStep 3281651 = 4922477) B4922477
theorem B1438455 : Blo 1437538 1438455 := bstep (se 1 (by rfl) ⟨1078841, by rfl⟩ : syracuseStep 1438455 = 2157683) B2157683
theorem B1438475 : Blo 1437538 1438475 := bstep (se 1 (by rfl) ⟨1078856, by rfl⟩ : syracuseStep 1438475 = 2157713) B2157713
theorem B1618699 : Blo 1437538 1618699 := bstep (se 1 (by rfl) ⟨1214024, by rfl⟩ : syracuseStep 1618699 = 2428049) B2428049
theorem B7287569 : Blo 1437538 7287569 := bstep (se 2 (by rfl) ⟨2732838, by rfl⟩ : syracuseStep 7287569 = 5465677) B5465677
theorem B1438487 : Blo 1437538 1438487 := bstep (se 1 (by rfl) ⟨1078865, by rfl⟩ : syracuseStep 1438487 = 2157731) B2157731
theorem B1438507 : Blo 1437538 1438507 := bstep (se 1 (by rfl) ⟨1078880, by rfl⟩ : syracuseStep 1438507 = 2157761) B2157761
theorem B1438519 : Blo 1437538 1438519 := bstep (se 1 (by rfl) ⟨1078889, by rfl⟩ : syracuseStep 1438519 = 2157779) B2157779
theorem B1438539 : Blo 1437538 1438539 := bstep (se 1 (by rfl) ⟨1078904, by rfl⟩ : syracuseStep 1438539 = 2157809) B2157809
theorem B1438551 : Blo 1437538 1438551 := bstep (se 1 (by rfl) ⟨1078913, by rfl⟩ : syracuseStep 1438551 = 2157827) B2157827
theorem B27644773 : Blo 1437538 27644773 := bstep (se 4 (by rfl) ⟨2591697, by rfl⟩ : syracuseStep 27644773 = 5183395) B5183395
theorem B1438571 : Blo 1437538 1438571 := bstep (se 1 (by rfl) ⟨1078928, by rfl⟩ : syracuseStep 1438571 = 2157857) B2157857
theorem B1438583 : Blo 1437538 1438583 := bstep (se 1 (by rfl) ⟨1078937, by rfl⟩ : syracuseStep 1438583 = 2157875) B2157875
theorem B1618807 : Blo 1437538 1618807 := bstep (se 1 (by rfl) ⟨1214105, by rfl⟩ : syracuseStep 1618807 = 2428211) B2428211
theorem B1438603 : Blo 1437538 1438603 := bstep (se 1 (by rfl) ⟨1078952, by rfl⟩ : syracuseStep 1438603 = 2157905) B2157905
theorem B1438615 : Blo 1437538 1438615 := bstep (se 1 (by rfl) ⟨1078961, by rfl⟩ : syracuseStep 1438615 = 2157923) B2157923
theorem B1438635 : Blo 1437538 1438635 := bstep (se 1 (by rfl) ⟨1078976, by rfl⟩ : syracuseStep 1438635 = 2157953) B2157953
theorem B4854707 : Blo 1437538 4854707 := bstep (se 1 (by rfl) ⟨3641030, by rfl⟩ : syracuseStep 4854707 = 7282061) B7282061
theorem B1438647 : Blo 1437538 1438647 := bstep (se 1 (by rfl) ⟨1078985, by rfl⟩ : syracuseStep 1438647 = 2157971) B2157971
theorem B1438667 : Blo 1437538 1438667 := bstep (se 1 (by rfl) ⟨1079000, by rfl⟩ : syracuseStep 1438667 = 2158001) B2158001
theorem B1438679 : Blo 1437538 1438679 := bstep (se 1 (by rfl) ⟨1079009, by rfl⟩ : syracuseStep 1438679 = 2158019) B2158019
theorem B1438699 : Blo 1437538 1438699 := bstep (se 1 (by rfl) ⟨1079024, by rfl⟩ : syracuseStep 1438699 = 2158049) B2158049
theorem B1438711 : Blo 1437538 1438711 := bstep (se 1 (by rfl) ⟨1079033, by rfl⟩ : syracuseStep 1438711 = 2158067) B2158067
theorem B2626561 : Blo 1437538 2626561 := bstep (se 2 (by rfl) ⟨984960, by rfl⟩ : syracuseStep 2626561 = 1969921) B1969921
theorem B1438731 : Blo 1437538 1438731 := bstep (se 1 (by rfl) ⟨1079048, by rfl⟩ : syracuseStep 1438731 = 2158097) B2158097
theorem B1438743 : Blo 1437538 1438743 := bstep (se 1 (by rfl) ⟨1079057, by rfl⟩ : syracuseStep 1438743 = 2158115) B2158115
theorem B1438763 : Blo 1437538 1438763 := bstep (se 1 (by rfl) ⟨1079072, by rfl⟩ : syracuseStep 1438763 = 2158145) B2158145
theorem B1618987 : Blo 1437538 1618987 := bstep (se 1 (by rfl) ⟨1214240, by rfl⟩ : syracuseStep 1618987 = 2428481) B2428481
theorem B1438775 : Blo 1437538 1438775 := bstep (se 1 (by rfl) ⟨1079081, by rfl⟩ : syracuseStep 1438775 = 2158163) B2158163
theorem B6911041 : Blo 1437538 6911041 := bstep (se 2 (by rfl) ⟨2591640, by rfl⟩ : syracuseStep 6911041 = 5183281) B5183281
theorem B1438795 : Blo 1437538 1438795 := bstep (se 1 (by rfl) ⟨1079096, by rfl⟩ : syracuseStep 1438795 = 2158193) B2158193
theorem B1438807 : Blo 1437538 1438807 := bstep (se 1 (by rfl) ⟨1079105, by rfl⟩ : syracuseStep 1438807 = 2158211) B2158211
theorem B1438827 : Blo 1437538 1438827 := bstep (se 1 (by rfl) ⟨1079120, by rfl⟩ : syracuseStep 1438827 = 2158241) B2158241
theorem B1438839 : Blo 1437538 1438839 := bstep (se 1 (by rfl) ⟨1079129, by rfl⟩ : syracuseStep 1438839 = 2158259) B2158259
theorem B1438859 : Blo 1437538 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B1438871 : Blo 1437538 1438871 := bstep (se 1 (by rfl) ⟨1079153, by rfl⟩ : syracuseStep 1438871 = 2158307) B2158307
theorem B1619095 : Blo 1437538 1619095 := bstep (se 1 (by rfl) ⟨1214321, by rfl⟩ : syracuseStep 1619095 = 2428643) B2428643
theorem B1438891 : Blo 1437538 1438891 := bstep (se 1 (by rfl) ⟨1079168, by rfl⟩ : syracuseStep 1438891 = 2158337) B2158337
theorem B1438903 : Blo 1437538 1438903 := bstep (se 1 (by rfl) ⟨1079177, by rfl⟩ : syracuseStep 1438903 = 2158355) B2158355
theorem B4854977 : Blo 1437538 4854977 := bstep (se 2 (by rfl) ⟨1820616, by rfl⟩ : syracuseStep 4854977 = 3641233) B3641233
theorem B1438923 : Blo 1437538 1438923 := bstep (se 1 (by rfl) ⟨1079192, by rfl⟩ : syracuseStep 1438923 = 2158385) B2158385
theorem B1438935 : Blo 1437538 1438935 := bstep (se 1 (by rfl) ⟨1079201, by rfl⟩ : syracuseStep 1438935 = 2158403) B2158403
theorem B1438955 : Blo 1437538 1438955 := bstep (se 1 (by rfl) ⟨1079216, by rfl⟩ : syracuseStep 1438955 = 2158433) B2158433
theorem B1438967 : Blo 1437538 1438967 := bstep (se 1 (by rfl) ⟨1079225, by rfl⟩ : syracuseStep 1438967 = 2158451) B2158451
theorem B1438987 : Blo 1437538 1438987 := bstep (se 1 (by rfl) ⟨1079240, by rfl⟩ : syracuseStep 1438987 = 2158481) B2158481
theorem B1438999 : Blo 1437538 1438999 := bstep (se 1 (by rfl) ⟨1079249, by rfl⟩ : syracuseStep 1438999 = 2158499) B2158499
theorem B1439019 : Blo 1437538 1439019 := bstep (se 1 (by rfl) ⟨1079264, by rfl⟩ : syracuseStep 1439019 = 2158529) B2158529
theorem B46658861 : Blo 1437538 46658861 := bstep (se 3 (by rfl) ⟨8748536, by rfl⟩ : syracuseStep 46658861 = 17497073) B17497073
theorem B1439031 : Blo 1437538 1439031 := bstep (se 1 (by rfl) ⟨1079273, by rfl⟩ : syracuseStep 1439031 = 2158547) B2158547
theorem B1439051 : Blo 1437538 1439051 := bstep (se 1 (by rfl) ⟨1079288, by rfl⟩ : syracuseStep 1439051 = 2158577) B2158577
theorem B1619275 : Blo 1437538 1619275 := bstep (se 1 (by rfl) ⟨1214456, by rfl⟩ : syracuseStep 1619275 = 2428913) B2428913
theorem B1439063 : Blo 1437538 1439063 := bstep (se 1 (by rfl) ⟨1079297, by rfl⟩ : syracuseStep 1439063 = 2158595) B2158595
theorem B2495831 : Blo 1437538 2495831 := bstep (se 1 (by rfl) ⟨1871873, by rfl⟩ : syracuseStep 2495831 = 3743747) B3743747
theorem B8197469 : Blo 1437538 8197469 := bstep (se 3 (by rfl) ⟨1537025, by rfl⟩ : syracuseStep 8197469 = 3074051) B3074051
theorem B23344483 : Blo 1437538 23344483 := bstep (se 1 (by rfl) ⟨17508362, by rfl⟩ : syracuseStep 23344483 = 35016725) B35016725
theorem B1439083 : Blo 1437538 1439083 := bstep (se 1 (by rfl) ⟨1079312, by rfl⟩ : syracuseStep 1439083 = 2158625) B2158625
theorem B1439095 : Blo 1437538 1439095 := bstep (se 1 (by rfl) ⟨1079321, by rfl⟩ : syracuseStep 1439095 = 2158643) B2158643
theorem B1439115 : Blo 1437538 1439115 := bstep (se 1 (by rfl) ⟨1079336, by rfl⟩ : syracuseStep 1439115 = 2158673) B2158673
theorem B1439127 : Blo 1437538 1439127 := bstep (se 1 (by rfl) ⟨1079345, by rfl⟩ : syracuseStep 1439127 = 2158691) B2158691
theorem B1439147 : Blo 1437538 1439147 := bstep (se 1 (by rfl) ⟨1079360, by rfl⟩ : syracuseStep 1439147 = 2158721) B2158721
theorem B3642803 : Blo 1437538 3642803 := bstep (se 1 (by rfl) ⟨2732102, by rfl⟩ : syracuseStep 3642803 = 5464205) B5464205
theorem B1439159 : Blo 1437538 1439159 := bstep (se 1 (by rfl) ⟨1079369, by rfl⟩ : syracuseStep 1439159 = 2158739) B2158739
theorem B1619383 : Blo 1437538 1619383 := bstep (se 1 (by rfl) ⟨1214537, by rfl⟩ : syracuseStep 1619383 = 2429075) B2429075
theorem B1439179 : Blo 1437538 1439179 := bstep (se 1 (by rfl) ⟨1079384, by rfl⟩ : syracuseStep 1439179 = 2158769) B2158769
theorem B1439191 : Blo 1437538 1439191 := bstep (se 1 (by rfl) ⟨1079393, by rfl⟩ : syracuseStep 1439191 = 2158787) B2158787
theorem B1439211 : Blo 1437538 1439211 := bstep (se 1 (by rfl) ⟨1079408, by rfl⟩ : syracuseStep 1439211 = 2158817) B2158817
theorem B1439223 : Blo 1437538 1439223 := bstep (se 1 (by rfl) ⟨1079417, by rfl⟩ : syracuseStep 1439223 = 2158835) B2158835
theorem B1439243 : Blo 1437538 1439243 := bstep (se 1 (by rfl) ⟨1079432, by rfl⟩ : syracuseStep 1439243 = 2158865) B2158865
theorem B1439255 : Blo 1437538 1439255 := bstep (se 1 (by rfl) ⟨1079441, by rfl⟩ : syracuseStep 1439255 = 2158883) B2158883
theorem B1439275 : Blo 1437538 1439275 := bstep (se 1 (by rfl) ⟨1079456, by rfl⟩ : syracuseStep 1439275 = 2158913) B2158913
theorem B6141491 : Blo 1437538 6141491 := bstep (se 1 (by rfl) ⟨4606118, by rfl⟩ : syracuseStep 6141491 = 9212237) B9212237
theorem B1439287 : Blo 1437538 1439287 := bstep (se 1 (by rfl) ⟨1079465, by rfl⟩ : syracuseStep 1439287 = 2158931) B2158931
theorem B1439307 : Blo 1437538 1439307 := bstep (se 1 (by rfl) ⟨1079480, by rfl⟩ : syracuseStep 1439307 = 2158961) B2158961
theorem B1439319 : Blo 1437538 1439319 := bstep (se 1 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 1439319 = 2158979) B2158979
theorem B1439339 : Blo 1437538 1439339 := bstep (se 1 (by rfl) ⟨1079504, by rfl⟩ : syracuseStep 1439339 = 2159009) B2159009
theorem B1439351 : Blo 1437538 1439351 := bstep (se 1 (by rfl) ⟨1079513, by rfl⟩ : syracuseStep 1439351 = 2159027) B2159027
theorem B1439371 : Blo 1437538 1439371 := bstep (se 1 (by rfl) ⟨1079528, by rfl⟩ : syracuseStep 1439371 = 2159057) B2159057
theorem B7280279 : Blo 1437538 7280279 := bstep (se 1 (by rfl) ⟨5460209, by rfl⟩ : syracuseStep 7280279 = 10920419) B10920419
theorem B6911639 : Blo 1437538 6911639 := bstep (se 1 (by rfl) ⟨5183729, by rfl⟩ : syracuseStep 6911639 = 10367459) B10367459
theorem B1439383 : Blo 1437538 1439383 := bstep (se 1 (by rfl) ⟨1079537, by rfl⟩ : syracuseStep 1439383 = 2159075) B2159075
theorem B1439403 : Blo 1437538 1439403 := bstep (se 1 (by rfl) ⟨1079552, by rfl⟩ : syracuseStep 1439403 = 2159105) B2159105
theorem B1439415 : Blo 1437538 1439415 := bstep (se 1 (by rfl) ⟨1079561, by rfl⟩ : syracuseStep 1439415 = 2159123) B2159123
theorem B1439435 : Blo 1437538 1439435 := bstep (se 1 (by rfl) ⟨1079576, by rfl⟩ : syracuseStep 1439435 = 2159153) B2159153
theorem B1439447 : Blo 1437538 1439447 := bstep (se 1 (by rfl) ⟨1079585, by rfl⟩ : syracuseStep 1439447 = 2159171) B2159171
theorem B4855517 : Blo 1437538 4855517 := bstep (se 3 (by rfl) ⟨910409, by rfl⟩ : syracuseStep 4855517 = 1820819) B1820819
theorem B1439467 : Blo 1437538 1439467 := bstep (se 1 (by rfl) ⟨1079600, by rfl⟩ : syracuseStep 1439467 = 2159201) B2159201
theorem B1439479 : Blo 1437538 1439479 := bstep (se 1 (by rfl) ⟨1079609, by rfl⟩ : syracuseStep 1439479 = 2159219) B2159219
theorem B1439499 : Blo 1437538 1439499 := bstep (se 1 (by rfl) ⟨1079624, by rfl⟩ : syracuseStep 1439499 = 2159249) B2159249
theorem B1439511 : Blo 1437538 1439511 := bstep (se 1 (by rfl) ⟨1079633, by rfl⟩ : syracuseStep 1439511 = 2159267) B2159267
theorem B1439531 : Blo 1437538 1439531 := bstep (se 1 (by rfl) ⟨1079648, by rfl⟩ : syracuseStep 1439531 = 2159297) B2159297
theorem B17495909 : Blo 1437538 17495909 := bstep (se 4 (by rfl) ⟨1640241, by rfl⟩ : syracuseStep 17495909 = 3280483) B3280483
theorem B3643339 : Blo 1437538 3643339 := bstep (se 1 (by rfl) ⟨2732504, by rfl⟩ : syracuseStep 3643339 = 5465009) B5465009
theorem B4921409 : Blo 1437538 4921409 := bstep (se 2 (by rfl) ⟨1845528, by rfl⟩ : syracuseStep 4921409 = 3691057) B3691057
theorem B3643481 : Blo 1437538 3643481 := bstep (se 2 (by rfl) ⟨1366305, by rfl⟩ : syracuseStep 3643481 = 2732611) B2732611
theorem B10917989 : Blo 1437538 10917989 := bstep (se 4 (by rfl) ⟨1023561, by rfl⟩ : syracuseStep 10917989 = 2047123) B2047123
theorem B4094155 : Blo 1437538 4094155 := bstep (se 1 (by rfl) ⟨3070616, by rfl⟩ : syracuseStep 4094155 = 6141233) B6141233
theorem B5462275 : Blo 1437538 5462275 := bstep (se 1 (by rfl) ⟨4096706, by rfl⟩ : syracuseStep 5462275 = 8193413) B8193413
theorem B5912983 : Blo 1437538 5912983 := bstep (se 1 (by rfl) ⟨4434737, by rfl⟩ : syracuseStep 5912983 = 8869475) B8869475
theorem B3889559 : Blo 1437538 3889559 := bstep (se 1 (by rfl) ⟨2917169, by rfl⟩ : syracuseStep 3889559 = 5834339) B5834339
theorem B3070361 : Blo 1437538 3070361 := bstep (se 2 (by rfl) ⟨1151385, by rfl⟩ : syracuseStep 3070361 = 2302771) B2302771
theorem B10795481 : Blo 1437538 10795481 := bstep (se 2 (by rfl) ⟨4048305, by rfl⟩ : syracuseStep 10795481 = 8096611) B8096611
theorem B6650333 : Blo 1437538 6650333 := bstep (se 3 (by rfl) ⟨1246937, by rfl⟩ : syracuseStep 6650333 = 2493875) B2493875
theorem B1751563 : Blo 1437538 1751563 := bstep (se 1 (by rfl) ⟨1313672, by rfl⟩ : syracuseStep 1751563 = 2627345) B2627345
theorem B5462579 : Blo 1437538 5462579 := bstep (se 1 (by rfl) ⟨4096934, by rfl⟩ : syracuseStep 5462579 = 8193869) B8193869
theorem B10918475 : Blo 1437538 10918475 := bstep (se 1 (by rfl) ⟨8188856, by rfl⟩ : syracuseStep 10918475 = 16377713) B16377713
theorem B4094657 : Blo 1437538 4094657 := bstep (se 2 (by rfl) ⟨1535496, by rfl⟩ : syracuseStep 4094657 = 3070993) B3070993
theorem B6560459 : Blo 1437538 6560459 := bstep (se 1 (by rfl) ⟨4920344, by rfl⟩ : syracuseStep 6560459 = 9840689) B9840689
theorem B3234635 : Blo 1437538 3234635 := bstep (se 1 (by rfl) ⟨2425976, by rfl⟩ : syracuseStep 3234635 = 4851953) B4851953
theorem B4856651 : Blo 1437538 4856651 := bstep (se 1 (by rfl) ⟨3642488, by rfl⟩ : syracuseStep 4856651 = 7284977) B7284977
theorem B3234689 : Blo 1437538 3234689 := bstep (se 2 (by rfl) ⟨1213008, by rfl⟩ : syracuseStep 3234689 = 2426017) B2426017
theorem B3693491 : Blo 1437538 3693491 := bstep (se 1 (by rfl) ⟨2770118, by rfl⟩ : syracuseStep 3693491 = 5540237) B5540237
theorem B4922315 : Blo 1437538 4922315 := bstep (se 1 (by rfl) ⟨3691736, by rfl⟩ : syracuseStep 4922315 = 7383473) B7383473
theorem B4094999 : Blo 1437538 4094999 := bstep (se 1 (by rfl) ⟨3071249, by rfl⟩ : syracuseStep 4094999 = 6142499) B6142499
theorem B3071027 : Blo 1437538 3071027 := bstep (se 1 (by rfl) ⟨2303270, by rfl⟩ : syracuseStep 3071027 = 4606541) B4606541
theorem B3234905 : Blo 1437538 3234905 := bstep (se 2 (by rfl) ⟨1213089, by rfl⟩ : syracuseStep 3234905 = 2426179) B2426179
theorem B4856921 : Blo 1437538 4856921 := bstep (se 2 (by rfl) ⟨1821345, by rfl⟩ : syracuseStep 4856921 = 3642691) B3642691
theorem B13122661 : Blo 1437538 13122661 := bstep (se 4 (by rfl) ⟨1230249, by rfl⟩ : syracuseStep 13122661 = 2460499) B2460499
theorem B3234995 : Blo 1437538 3234995 := bstep (se 1 (by rfl) ⟨2426246, by rfl⟩ : syracuseStep 3234995 = 4852493) B4852493
theorem B5463233 : Blo 1437538 5463233 := bstep (se 2 (by rfl) ⟨2048712, by rfl⟩ : syracuseStep 5463233 = 4097425) B4097425
theorem B2915531 : Blo 1437538 2915531 := bstep (se 1 (by rfl) ⟨2186648, by rfl⟩ : syracuseStep 2915531 = 4373297) B4373297
theorem B13819085 : Blo 1437538 13819085 := bstep (se 3 (by rfl) ⟨2591078, by rfl⟩ : syracuseStep 13819085 = 5182157) B5182157
theorem B3235031 : Blo 1437538 3235031 := bstep (se 1 (by rfl) ⟨2426273, by rfl⟩ : syracuseStep 3235031 = 4852547) B4852547
theorem B3890393 : Blo 1437538 3890393 := bstep (se 2 (by rfl) ⟨1458897, by rfl⟩ : syracuseStep 3890393 = 2917795) B2917795
theorem B2997515 : Blo 1437538 2997515 := bstep (se 1 (by rfl) ⟨2248136, by rfl⟩ : syracuseStep 2997515 = 4496273) B4496273
theorem B3235211 : Blo 1437538 3235211 := bstep (se 1 (by rfl) ⟨2426408, by rfl⟩ : syracuseStep 3235211 = 4852817) B4852817
theorem B3235265 : Blo 1437538 3235265 := bstep (se 2 (by rfl) ⟨1213224, by rfl⟩ : syracuseStep 3235265 = 2426449) B2426449
theorem B10927709 : Blo 1437538 10927709 := bstep (se 3 (by rfl) ⟨2048945, by rfl⟩ : syracuseStep 10927709 = 4097891) B4097891
theorem B3235481 : Blo 1437538 3235481 := bstep (se 2 (by rfl) ⟨1213305, by rfl⟩ : syracuseStep 3235481 = 2426611) B2426611
theorem B3235571 : Blo 1437538 3235571 := bstep (se 1 (by rfl) ⟨2426678, by rfl⟩ : syracuseStep 3235571 = 4853357) B4853357
theorem B3235607 : Blo 1437538 3235607 := bstep (se 1 (by rfl) ⟨2426705, by rfl⟩ : syracuseStep 3235607 = 4853411) B4853411
theorem B4857623 : Blo 1437538 4857623 := bstep (se 1 (by rfl) ⟨3643217, by rfl⟩ : syracuseStep 4857623 = 7286435) B7286435
theorem B18693989 : Blo 1437538 18693989 := bstep (se 4 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 18693989 = 3505123) B3505123
theorem B2768833 : Blo 1437538 2768833 := bstep (se 2 (by rfl) ⟨1038312, by rfl⟩ : syracuseStep 2768833 = 2076625) B2076625
theorem B3235787 : Blo 1437538 3235787 := bstep (se 1 (by rfl) ⟨2426840, by rfl⟩ : syracuseStep 3235787 = 4853681) B4853681
theorem B4096001 : Blo 1437538 4096001 := bstep (se 2 (by rfl) ⟨1536000, by rfl⟩ : syracuseStep 4096001 = 3072001) B3072001
theorem B4669483 : Blo 1437538 4669483 := bstep (se 1 (by rfl) ⟨3502112, by rfl⟩ : syracuseStep 4669483 = 7004225) B7004225
theorem B4096115 : Blo 1437538 4096115 := bstep (se 1 (by rfl) ⟨3072086, by rfl⟩ : syracuseStep 4096115 = 6144173) B6144173
theorem B2048171 : Blo 1437538 2048171 := bstep (se 1 (by rfl) ⟨1536128, by rfl⟩ : syracuseStep 2048171 = 3072257) B3072257
theorem B13123757 : Blo 1437538 13123757 := bstep (se 3 (by rfl) ⟨2460704, by rfl⟩ : syracuseStep 13123757 = 4921409) B4921409
theorem B3236111 : Blo 1437538 3236111 := bstep (se 1 (by rfl) ⟨2427083, by rfl⟩ : syracuseStep 3236111 = 4854167) B4854167
theorem B3236129 : Blo 1437538 3236129 := bstep (se 2 (by rfl) ⟨1213548, by rfl⟩ : syracuseStep 3236129 = 2427097) B2427097
theorem B7283033 : Blo 1437538 7283033 := bstep (se 2 (by rfl) ⟨2731137, by rfl⟩ : syracuseStep 7283033 = 5462275) B5462275
theorem B3457367 : Blo 1437538 3457367 := bstep (se 1 (by rfl) ⟨2593025, by rfl⟩ : syracuseStep 3457367 = 5186051) B5186051
theorem B4096457 : Blo 1437538 4096457 := bstep (se 2 (by rfl) ⟨1536171, by rfl⟩ : syracuseStep 4096457 = 3072343) B3072343
theorem B2187767 : Blo 1437538 2187767 := bstep (se 1 (by rfl) ⟨1640825, by rfl⟩ : syracuseStep 2187767 = 3281651) B3281651
theorem B4858379 : Blo 1437538 4858379 := bstep (se 1 (by rfl) ⟨3643784, by rfl⟩ : syracuseStep 4858379 = 7287569) B7287569
theorem B39387683 : Blo 1437538 39387683 := bstep (se 1 (by rfl) ⟨29540762, by rfl⟩ : syracuseStep 39387683 = 59081525) B59081525
theorem B3113515 : Blo 1437538 3113515 := bstep (se 1 (by rfl) ⟨2335136, by rfl⟩ : syracuseStep 3113515 = 4670273) B4670273
theorem B3236471 : Blo 1437538 3236471 := bstep (se 1 (by rfl) ⟨2427353, by rfl⟩ : syracuseStep 3236471 = 4854707) B4854707
theorem B3236651 : Blo 1437538 3236651 := bstep (se 1 (by rfl) ⟨2427488, by rfl⟩ : syracuseStep 3236651 = 4854977) B4854977
theorem B31105907 : Blo 1437538 31105907 := bstep (se 1 (by rfl) ⟨23329430, by rfl⟩ : syracuseStep 31105907 = 46658861) B46658861
theorem B5464979 : Blo 1437538 5464979 := bstep (se 1 (by rfl) ⟨4098734, by rfl⟩ : syracuseStep 5464979 = 8197469) B8197469
theorem B24568757 : Blo 1437538 24568757 := bstep (se 5 (by rfl) ⟨1151660, by rfl⟩ : syracuseStep 24568757 = 2303321) B2303321
theorem B1819579 : Blo 1437538 1819579 := bstep (se 1 (by rfl) ⟨1364684, by rfl⟩ : syracuseStep 1819579 = 2729369) B2729369
theorem B10372157 : Blo 1437538 10372157 := bstep (se 3 (by rfl) ⟨1944779, by rfl⟩ : syracuseStep 10372157 = 3889559) B3889559
theorem B3458135 : Blo 1437538 3458135 := bstep (se 1 (by rfl) ⟨2593601, by rfl⟩ : syracuseStep 3458135 = 5187203) B5187203
theorem B3237011 : Blo 1437538 3237011 := bstep (se 1 (by rfl) ⟨2427758, by rfl⟩ : syracuseStep 3237011 = 4855517) B4855517
theorem B3237065 : Blo 1437538 3237065 := bstep (se 2 (by rfl) ⟨1213899, by rfl⟩ : syracuseStep 3237065 = 2427799) B2427799
theorem B1639823 : Blo 1437538 1639823 := bstep (se 1 (by rfl) ⟨1229867, by rfl⟩ : syracuseStep 1639823 = 2459735) B2459735
theorem B2426503 : Blo 1437538 2426503 := bstep (se 1 (by rfl) ⟨1819877, by rfl⟩ : syracuseStep 2426503 = 3639755) B3639755
theorem B4433555 : Blo 1437538 4433555 := bstep (se 1 (by rfl) ⟨3325166, by rfl⟩ : syracuseStep 4433555 = 6650333) B6650333
theorem B2729771 : Blo 1437538 2729771 := bstep (se 1 (by rfl) ⟨2047328, by rfl⟩ : syracuseStep 2729771 = 4094657) B4094657
theorem B2156345 : Blo 1437538 2156345 := bstep (se 2 (by rfl) ⟨808629, by rfl⟩ : syracuseStep 2156345 = 1617259) B1617259
theorem B3639127 : Blo 1437538 3639127 := bstep (se 1 (by rfl) ⟨2729345, by rfl⟩ : syracuseStep 3639127 = 5458691) B5458691
theorem B2156423 : Blo 1437538 2156423 := bstep (se 1 (by rfl) ⟨1617317, by rfl⟩ : syracuseStep 2156423 = 3234635) B3234635
theorem B1820551 : Blo 1437538 1820551 := bstep (se 1 (by rfl) ⟨1365413, by rfl⟩ : syracuseStep 1820551 = 2730827) B2730827
theorem B3237767 : Blo 1437538 3237767 := bstep (se 1 (by rfl) ⟨2428325, by rfl⟩ : syracuseStep 3237767 = 4856651) B4856651
theorem B13830041 : Blo 1437538 13830041 := bstep (se 2 (by rfl) ⟨5186265, by rfl⟩ : syracuseStep 13830041 = 10372531) B10372531
theorem B2156459 : Blo 1437538 2156459 := bstep (se 1 (by rfl) ⟨1617344, by rfl⟩ : syracuseStep 2156459 = 3234689) B3234689
theorem B2156489 : Blo 1437538 2156489 := bstep (se 2 (by rfl) ⟨808683, by rfl⟩ : syracuseStep 2156489 = 1617367) B1617367
theorem B2729999 : Blo 1437538 2729999 := bstep (se 1 (by rfl) ⟨2047499, by rfl⟩ : syracuseStep 2729999 = 4094999) B4094999
theorem B4376605 : Blo 1437538 4376605 := bstep (se 3 (by rfl) ⟨820613, by rfl⟩ : syracuseStep 4376605 = 1641227) B1641227
theorem B2156603 : Blo 1437538 2156603 := bstep (se 1 (by rfl) ⟨1617452, by rfl⟩ : syracuseStep 2156603 = 3234905) B3234905
theorem B3237947 : Blo 1437538 3237947 := bstep (se 1 (by rfl) ⟨2428460, by rfl⟩ : syracuseStep 3237947 = 4856921) B4856921
theorem B2156663 : Blo 1437538 2156663 := bstep (se 1 (by rfl) ⟨1617497, by rfl⟩ : syracuseStep 2156663 = 3234995) B3234995
theorem B3639431 : Blo 1437538 3639431 := bstep (se 1 (by rfl) ⟨2729573, by rfl⟩ : syracuseStep 3639431 = 5459147) B5459147
theorem B1943687 : Blo 1437538 1943687 := bstep (se 1 (by rfl) ⟨1457765, by rfl⟩ : syracuseStep 1943687 = 2915531) B2915531
theorem B2156687 : Blo 1437538 2156687 := bstep (se 1 (by rfl) ⟨1617515, by rfl⟩ : syracuseStep 2156687 = 3235031) B3235031
theorem B2156729 : Blo 1437538 2156729 := bstep (se 2 (by rfl) ⟨808773, by rfl⟩ : syracuseStep 2156729 = 1617547) B1617547
theorem B3238073 : Blo 1437538 3238073 := bstep (se 2 (by rfl) ⟨1214277, by rfl⟩ : syracuseStep 3238073 = 2428555) B2428555
theorem B2156807 : Blo 1437538 2156807 := bstep (se 1 (by rfl) ⟨1617605, by rfl⟩ : syracuseStep 2156807 = 3235211) B3235211
theorem B3639563 : Blo 1437538 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B2427151 : Blo 1437538 2427151 := bstep (se 1 (by rfl) ⟨1820363, by rfl⟩ : syracuseStep 2427151 = 3640727) B3640727
theorem B2156843 : Blo 1437538 2156843 := bstep (se 1 (by rfl) ⟨1617632, by rfl⟩ : syracuseStep 2156843 = 3235265) B3235265
theorem B1820971 : Blo 1437538 1820971 := bstep (se 1 (by rfl) ⟨1365728, by rfl⟩ : syracuseStep 1820971 = 2731457) B2731457
theorem B4098347 : Blo 1437538 4098347 := bstep (se 1 (by rfl) ⟨3073760, by rfl⟩ : syracuseStep 4098347 = 6147521) B6147521
theorem B2156873 : Blo 1437538 2156873 := bstep (se 2 (by rfl) ⟨808827, by rfl⟩ : syracuseStep 2156873 = 1617655) B1617655
theorem B4852115 : Blo 1437538 4852115 := bstep (se 1 (by rfl) ⟨3639086, by rfl⟩ : syracuseStep 4852115 = 7278173) B7278173
theorem B7285139 : Blo 1437538 7285139 := bstep (se 1 (by rfl) ⟨5463854, by rfl⟩ : syracuseStep 7285139 = 10927709) B10927709
theorem B2156987 : Blo 1437538 2156987 := bstep (se 1 (by rfl) ⟨1617740, by rfl⟩ : syracuseStep 2156987 = 3235481) B3235481
theorem B2157047 : Blo 1437538 2157047 := bstep (se 1 (by rfl) ⟨1617785, by rfl⟩ : syracuseStep 2157047 = 3235571) B3235571
theorem B2157071 : Blo 1437538 2157071 := bstep (se 1 (by rfl) ⟨1617803, by rfl⟩ : syracuseStep 2157071 = 3235607) B3235607
theorem B1821199 : Blo 1437538 1821199 := bstep (se 1 (by rfl) ⟨1365899, by rfl⟩ : syracuseStep 1821199 = 2731799) B2731799
theorem B4098575 : Blo 1437538 4098575 := bstep (se 1 (by rfl) ⟨3073931, by rfl⟩ : syracuseStep 4098575 = 6147863) B6147863
theorem B3238415 : Blo 1437538 3238415 := bstep (se 1 (by rfl) ⟨2428811, by rfl⟩ : syracuseStep 3238415 = 4857623) B4857623
theorem B3238433 : Blo 1437538 3238433 := bstep (se 2 (by rfl) ⟨1214412, by rfl⟩ : syracuseStep 3238433 = 2428825) B2428825
theorem B2157113 : Blo 1437538 2157113 := bstep (se 2 (by rfl) ⟨808917, by rfl⟩ : syracuseStep 2157113 = 1617835) B1617835
theorem B12462659 : Blo 1437538 12462659 := bstep (se 1 (by rfl) ⟨9346994, by rfl⟩ : syracuseStep 12462659 = 18693989) B18693989
theorem B53217911 : Blo 1437538 53217911 := bstep (se 1 (by rfl) ⟨39913433, by rfl⟩ : syracuseStep 53217911 = 79826867) B79826867
theorem B2157191 : Blo 1437538 2157191 := bstep (se 1 (by rfl) ⟨1617893, by rfl⟩ : syracuseStep 2157191 = 3235787) B3235787
theorem B2157227 : Blo 1437538 2157227 := bstep (se 1 (by rfl) ⟨1617920, by rfl⟩ : syracuseStep 2157227 = 3235841) B3235841
theorem B2157257 : Blo 1437538 2157257 := bstep (se 2 (by rfl) ⟨808971, by rfl⟩ : syracuseStep 2157257 = 1617943) B1617943
theorem B9341669 : Blo 1437538 9341669 := bstep (se 4 (by rfl) ⟨875781, by rfl⟩ : syracuseStep 9341669 = 1751563) B1751563
theorem B3640079 : Blo 1437538 3640079 := bstep (se 1 (by rfl) ⟨2730059, by rfl⟩ : syracuseStep 3640079 = 5460119) B5460119
theorem B2427691 : Blo 1437538 2427691 := bstep (se 1 (by rfl) ⟨1820768, by rfl⟩ : syracuseStep 2427691 = 3641537) B3641537
theorem B2157371 : Blo 1437538 2157371 := bstep (se 1 (by rfl) ⟨1618028, by rfl⟩ : syracuseStep 2157371 = 3236057) B3236057
theorem B1944379 : Blo 1437538 1944379 := bstep (se 1 (by rfl) ⟨1458284, by rfl⟩ : syracuseStep 1944379 = 2916569) B2916569
theorem B2157431 : Blo 1437538 2157431 := bstep (se 1 (by rfl) ⟨1618073, by rfl⟩ : syracuseStep 2157431 = 3236147) B3236147
theorem B3238775 : Blo 1437538 3238775 := bstep (se 1 (by rfl) ⟨2429081, by rfl⟩ : syracuseStep 3238775 = 4858163) B4858163
theorem B2157455 : Blo 1437538 2157455 := bstep (se 1 (by rfl) ⟨1618091, by rfl⟩ : syracuseStep 2157455 = 3236183) B3236183
theorem B3640211 : Blo 1437538 3640211 := bstep (se 1 (by rfl) ⟨2730158, by rfl⟩ : syracuseStep 3640211 = 5460317) B5460317
theorem B5458873 : Blo 1437538 5458873 := bstep (se 2 (by rfl) ⟨2047077, by rfl⟩ : syracuseStep 5458873 = 4094155) B4094155
theorem B2157497 : Blo 1437538 2157497 := bstep (se 2 (by rfl) ⟨809061, by rfl⟩ : syracuseStep 2157497 = 1618123) B1618123
theorem B2427833 : Blo 1437538 2427833 := bstep (se 2 (by rfl) ⟨910437, by rfl⟩ : syracuseStep 2427833 = 1820875) B1820875
theorem B2157575 : Blo 1437538 2157575 := bstep (se 1 (by rfl) ⟨1618181, by rfl⟩ : syracuseStep 2157575 = 3236363) B3236363
theorem B2305039 : Blo 1437538 2305039 := bstep (se 1 (by rfl) ⟨1728779, by rfl⟩ : syracuseStep 2305039 = 3457559) B3457559
theorem B2157611 : Blo 1437538 2157611 := bstep (se 1 (by rfl) ⟨1618208, by rfl⟩ : syracuseStep 2157611 = 3236417) B3236417
theorem B3238955 : Blo 1437538 3238955 := bstep (se 1 (by rfl) ⟨2429216, by rfl⟩ : syracuseStep 3238955 = 4858433) B4858433
theorem B2157641 : Blo 1437538 2157641 := bstep (se 2 (by rfl) ⟨809115, by rfl⟩ : syracuseStep 2157641 = 1618231) B1618231
theorem B7277687 : Blo 1437538 7277687 := bstep (se 1 (by rfl) ⟨5458265, by rfl⟩ : syracuseStep 7277687 = 10916531) B10916531
theorem B2157755 : Blo 1437538 2157755 := bstep (se 1 (by rfl) ⟨1618316, by rfl⟩ : syracuseStep 2157755 = 3236633) B3236633
theorem B2157815 : Blo 1437538 2157815 := bstep (se 1 (by rfl) ⟨1618361, by rfl⟩ : syracuseStep 2157815 = 3236723) B3236723
theorem B2157839 : Blo 1437538 2157839 := bstep (se 1 (by rfl) ⟨1618379, by rfl⟩ : syracuseStep 2157839 = 3236759) B3236759
theorem B3116321 : Blo 1437538 3116321 := bstep (se 2 (by rfl) ⟨1168620, by rfl⟩ : syracuseStep 3116321 = 2337241) B2337241
theorem B2157881 : Blo 1437538 2157881 := bstep (se 2 (by rfl) ⟨809205, by rfl⟩ : syracuseStep 2157881 = 1618411) B1618411
theorem B2075977 : Blo 1437538 2075977 := bstep (se 2 (by rfl) ⟨778491, by rfl⟩ : syracuseStep 2075977 = 1556983) B1556983
theorem B2157959 : Blo 1437538 2157959 := bstep (se 1 (by rfl) ⟨1618469, by rfl⟩ : syracuseStep 2157959 = 3236939) B3236939
theorem B1617295 : Blo 1437538 1617295 := bstep (se 1 (by rfl) ⟨1212971, by rfl⟩ : syracuseStep 1617295 = 2425943) B2425943
theorem B2731411 : Blo 1437538 2731411 := bstep (se 1 (by rfl) ⟨2048558, by rfl⟩ : syracuseStep 2731411 = 4097117) B4097117
theorem B2157995 : Blo 1437538 2157995 := bstep (se 1 (by rfl) ⟨1618496, by rfl⟩ : syracuseStep 2157995 = 3236993) B3236993
theorem B2158025 : Blo 1437538 2158025 := bstep (se 2 (by rfl) ⟨809259, by rfl⟩ : syracuseStep 2158025 = 1618519) B1618519
theorem B6229457 : Blo 1437538 6229457 := bstep (se 2 (by rfl) ⟨2336046, by rfl⟩ : syracuseStep 6229457 = 4672093) B4672093
theorem B6655441 : Blo 1437538 6655441 := bstep (se 2 (by rfl) ⟨2495790, by rfl⟩ : syracuseStep 6655441 = 4991581) B4991581
theorem B15560221 : Blo 1437538 15560221 := bstep (se 3 (by rfl) ⟨2917541, by rfl⟩ : syracuseStep 15560221 = 5835083) B5835083
theorem B2158139 : Blo 1437538 2158139 := bstep (se 1 (by rfl) ⟨1618604, by rfl⟩ : syracuseStep 2158139 = 3237209) B3237209
theorem B6655549 : Blo 1437538 6655549 := bstep (se 3 (by rfl) ⟨1247915, by rfl⟩ : syracuseStep 6655549 = 2495831) B2495831
theorem B2158199 : Blo 1437538 2158199 := bstep (se 1 (by rfl) ⟨1618649, by rfl⟩ : syracuseStep 2158199 = 3237299) B3237299
theorem B2731639 : Blo 1437538 2731639 := bstep (se 1 (by rfl) ⟨2048729, by rfl⟩ : syracuseStep 2731639 = 4097459) B4097459
theorem B2428535 : Blo 1437538 2428535 := bstep (se 1 (by rfl) ⟨1821401, by rfl⟩ : syracuseStep 2428535 = 3642803) B3642803
theorem B2158223 : Blo 1437538 2158223 := bstep (se 1 (by rfl) ⟨1618667, by rfl⟩ : syracuseStep 2158223 = 3237335) B3237335
theorem B2158265 : Blo 1437538 2158265 := bstep (se 2 (by rfl) ⟨809349, by rfl⟩ : syracuseStep 2158265 = 1618699) B1618699
theorem B3739337 : Blo 1437538 3739337 := bstep (se 2 (by rfl) ⟨1402251, by rfl⟩ : syracuseStep 3739337 = 2804503) B2804503
theorem B2158343 : Blo 1437538 2158343 := bstep (se 1 (by rfl) ⟨1618757, by rfl⟩ : syracuseStep 2158343 = 3237515) B3237515
theorem B4853519 : Blo 1437538 4853519 := bstep (se 1 (by rfl) ⟨3640139, by rfl⟩ : syracuseStep 4853519 = 7280279) B7280279
theorem B4607759 : Blo 1437538 4607759 := bstep (se 1 (by rfl) ⟨3455819, by rfl⟩ : syracuseStep 4607759 = 6911639) B6911639
theorem B2158379 : Blo 1437538 2158379 := bstep (se 1 (by rfl) ⟨1618784, by rfl⟩ : syracuseStep 2158379 = 3237569) B3237569
theorem B36859697 : Blo 1437538 36859697 := bstep (se 2 (by rfl) ⟨13822386, by rfl⟩ : syracuseStep 36859697 = 27644773) B27644773
theorem B2158409 : Blo 1437538 2158409 := bstep (se 2 (by rfl) ⟨809403, by rfl⟩ : syracuseStep 2158409 = 1618807) B1618807
theorem B8187763 : Blo 1437538 8187763 := bstep (se 1 (by rfl) ⟨6140822, by rfl⟩ : syracuseStep 8187763 = 12281645) B12281645
theorem B1437575 : Blo 1437538 1437575 := bstep (se 1 (by rfl) ⟨1078181, by rfl⟩ : syracuseStep 1437575 = 2156363) B2156363
theorem B1617799 : Blo 1437538 1617799 := bstep (se 1 (by rfl) ⟨1213349, by rfl⟩ : syracuseStep 1617799 = 2426699) B2426699
theorem B3551111 : Blo 1437538 3551111 := bstep (se 1 (by rfl) ⟨2663333, by rfl⟩ : syracuseStep 3551111 = 5326667) B5326667
theorem B1437583 : Blo 1437538 1437583 := bstep (se 1 (by rfl) ⟨1078187, by rfl⟩ : syracuseStep 1437583 = 2156375) B2156375
theorem B1437627 : Blo 1437538 1437627 := bstep (se 1 (by rfl) ⟨1078220, by rfl⟩ : syracuseStep 1437627 = 2156441) B2156441
theorem B2158523 : Blo 1437538 2158523 := bstep (se 1 (by rfl) ⟨1618892, by rfl⟩ : syracuseStep 2158523 = 3237785) B3237785
theorem B2158583 : Blo 1437538 2158583 := bstep (se 1 (by rfl) ⟨1618937, by rfl⟩ : syracuseStep 2158583 = 3237875) B3237875
theorem B3502081 : Blo 1437538 3502081 := bstep (se 2 (by rfl) ⟨1313280, by rfl⟩ : syracuseStep 3502081 = 2626561) B2626561
theorem B3641345 : Blo 1437538 3641345 := bstep (se 2 (by rfl) ⟨1365504, by rfl⟩ : syracuseStep 3641345 = 2731009) B2731009
theorem B1437703 : Blo 1437538 1437703 := bstep (se 1 (by rfl) ⟨1078277, by rfl⟩ : syracuseStep 1437703 = 2156555) B2156555
theorem B1437711 : Blo 1437538 1437711 := bstep (se 1 (by rfl) ⟨1078283, by rfl⟩ : syracuseStep 1437711 = 2156567) B2156567
theorem B2158607 : Blo 1437538 2158607 := bstep (se 1 (by rfl) ⟨1618955, by rfl⟩ : syracuseStep 2158607 = 3237911) B3237911
theorem B4853789 : Blo 1437538 4853789 := bstep (se 3 (by rfl) ⟨910085, by rfl⟩ : syracuseStep 4853789 = 1820171) B1820171
theorem B2158649 : Blo 1437538 2158649 := bstep (se 2 (by rfl) ⟨809493, by rfl⟩ : syracuseStep 2158649 = 1618987) B1618987
theorem B1437755 : Blo 1437538 1437755 := bstep (se 1 (by rfl) ⟨1078316, by rfl⟩ : syracuseStep 1437755 = 2156633) B2156633
theorem B1617979 : Blo 1437538 1617979 := bstep (se 1 (by rfl) ⟨1213484, by rfl⟩ : syracuseStep 1617979 = 2426969) B2426969
theorem B17485885 : Blo 1437538 17485885 := bstep (se 3 (by rfl) ⟨3278603, by rfl⟩ : syracuseStep 17485885 = 6557207) B6557207
theorem B7278659 : Blo 1437538 7278659 := bstep (se 1 (by rfl) ⟨5458994, by rfl⟩ : syracuseStep 7278659 = 10917989) B10917989
theorem B1437831 : Blo 1437538 1437831 := bstep (se 1 (by rfl) ⟨1078373, by rfl⟩ : syracuseStep 1437831 = 2156747) B2156747
theorem B2158727 : Blo 1437538 2158727 := bstep (se 1 (by rfl) ⟨1619045, by rfl⟩ : syracuseStep 2158727 = 3238091) B3238091
theorem B1437839 : Blo 1437538 1437839 := bstep (se 1 (by rfl) ⟨1078379, by rfl⟩ : syracuseStep 1437839 = 2156759) B2156759
theorem B2158763 : Blo 1437538 2158763 := bstep (se 1 (by rfl) ⟨1619072, by rfl⟩ : syracuseStep 2158763 = 3238145) B3238145
theorem B1437883 : Blo 1437538 1437883 := bstep (se 1 (by rfl) ⟨1078412, by rfl⟩ : syracuseStep 1437883 = 2156825) B2156825
theorem B2158793 : Blo 1437538 2158793 := bstep (se 2 (by rfl) ⟨809547, by rfl⟩ : syracuseStep 2158793 = 1619095) B1619095
theorem B2429129 : Blo 1437538 2429129 := bstep (se 2 (by rfl) ⟨910923, by rfl⟩ : syracuseStep 2429129 = 1821847) B1821847
theorem B1437959 : Blo 1437538 1437959 := bstep (se 1 (by rfl) ⟨1078469, by rfl⟩ : syracuseStep 1437959 = 2156939) B2156939
theorem B1437967 : Blo 1437538 1437967 := bstep (se 1 (by rfl) ⟨1078475, by rfl⟩ : syracuseStep 1437967 = 2156951) B2156951
theorem B1438011 : Blo 1437538 1438011 := bstep (se 1 (by rfl) ⟨1078508, by rfl⟩ : syracuseStep 1438011 = 2157017) B2157017
theorem B7196987 : Blo 1437538 7196987 := bstep (se 1 (by rfl) ⟨5397740, by rfl⟩ : syracuseStep 7196987 = 10795481) B10795481
theorem B2158907 : Blo 1437538 2158907 := bstep (se 1 (by rfl) ⟨1619180, by rfl⟩ : syracuseStep 2158907 = 3238361) B3238361
theorem B3641719 : Blo 1437538 3641719 := bstep (se 1 (by rfl) ⟨2731289, by rfl⟩ : syracuseStep 3641719 = 5462579) B5462579
theorem B2158967 : Blo 1437538 2158967 := bstep (se 1 (by rfl) ⟨1619225, by rfl⟩ : syracuseStep 2158967 = 3238451) B3238451
theorem B7278983 : Blo 1437538 7278983 := bstep (se 1 (by rfl) ⟨5459237, by rfl⟩ : syracuseStep 7278983 = 10918475) B10918475
theorem B1438087 : Blo 1437538 1438087 := bstep (se 1 (by rfl) ⟨1078565, by rfl⟩ : syracuseStep 1438087 = 2157131) B2157131
theorem B1438095 : Blo 1437538 1438095 := bstep (se 1 (by rfl) ⟨1078571, by rfl⟩ : syracuseStep 1438095 = 2157143) B2157143
theorem B2158991 : Blo 1437538 2158991 := bstep (se 1 (by rfl) ⟨1619243, by rfl⟩ : syracuseStep 2158991 = 3238487) B3238487
theorem B2159033 : Blo 1437538 2159033 := bstep (se 2 (by rfl) ⟨809637, by rfl⟩ : syracuseStep 2159033 = 1619275) B1619275
theorem B1438139 : Blo 1437538 1438139 := bstep (se 1 (by rfl) ⟨1078604, by rfl⟩ : syracuseStep 1438139 = 2157209) B2157209
theorem B17740241 : Blo 1437538 17740241 := bstep (se 2 (by rfl) ⟨6652590, by rfl⟩ : syracuseStep 17740241 = 13305181) B13305181
theorem B31125977 : Blo 1437538 31125977 := bstep (se 2 (by rfl) ⟨11672241, by rfl⟩ : syracuseStep 31125977 = 23344483) B23344483
theorem B1438215 : Blo 1437538 1438215 := bstep (se 1 (by rfl) ⟨1078661, by rfl⟩ : syracuseStep 1438215 = 2157323) B2157323
theorem B2159111 : Blo 1437538 2159111 := bstep (se 1 (by rfl) ⟨1619333, by rfl⟩ : syracuseStep 2159111 = 3238667) B3238667
theorem B1438223 : Blo 1437538 1438223 := bstep (se 1 (by rfl) ⟨1078667, by rfl⟩ : syracuseStep 1438223 = 2157335) B2157335
theorem B1618447 : Blo 1437538 1618447 := bstep (se 1 (by rfl) ⟨1213835, by rfl⟩ : syracuseStep 1618447 = 2427671) B2427671
theorem B2593313 : Blo 1437538 2593313 := bstep (se 2 (by rfl) ⟨972492, by rfl⟩ : syracuseStep 2593313 = 1944985) B1944985
theorem B2159147 : Blo 1437538 2159147 := bstep (se 1 (by rfl) ⟨1619360, by rfl⟩ : syracuseStep 2159147 = 3238721) B3238721
theorem B1438267 : Blo 1437538 1438267 := bstep (se 1 (by rfl) ⟨1078700, by rfl⟩ : syracuseStep 1438267 = 2157401) B2157401
theorem B2159177 : Blo 1437538 2159177 := bstep (se 2 (by rfl) ⟨809691, by rfl⟩ : syracuseStep 2159177 = 1619383) B1619383
theorem B2462327 : Blo 1437538 2462327 := bstep (se 1 (by rfl) ⟨1846745, by rfl⟩ : syracuseStep 2462327 = 3693491) B3693491
theorem B1438343 : Blo 1437538 1438343 := bstep (se 1 (by rfl) ⟨1078757, by rfl⟩ : syracuseStep 1438343 = 2157515) B2157515
theorem B3281543 : Blo 1437538 3281543 := bstep (se 1 (by rfl) ⟨2461157, by rfl⟩ : syracuseStep 3281543 = 4922315) B4922315
theorem B1438351 : Blo 1437538 1438351 := bstep (se 1 (by rfl) ⟨1078763, by rfl⟩ : syracuseStep 1438351 = 2157527) B2157527
theorem B1438395 : Blo 1437538 1438395 := bstep (se 1 (by rfl) ⟨1078796, by rfl⟩ : syracuseStep 1438395 = 2157593) B2157593
theorem B2159291 : Blo 1437538 2159291 := bstep (se 1 (by rfl) ⟨1619468, by rfl⟩ : syracuseStep 2159291 = 3238937) B3238937
theorem B1438471 : Blo 1437538 1438471 := bstep (se 1 (by rfl) ⟨1078853, by rfl⟩ : syracuseStep 1438471 = 2157707) B2157707
theorem B1438479 : Blo 1437538 1438479 := bstep (se 1 (by rfl) ⟨1078859, by rfl⟩ : syracuseStep 1438479 = 2157719) B2157719
theorem B4920097 : Blo 1437538 4920097 := bstep (se 2 (by rfl) ⟨1845036, by rfl⟩ : syracuseStep 4920097 = 3690073) B3690073
theorem B31535909 : Blo 1437538 31535909 := bstep (se 4 (by rfl) ⟨2956491, by rfl⟩ : syracuseStep 31535909 = 5912983) B5912983
theorem B3642155 : Blo 1437538 3642155 := bstep (se 1 (by rfl) ⟨2731616, by rfl⟩ : syracuseStep 3642155 = 5463233) B5463233
theorem B9212723 : Blo 1437538 9212723 := bstep (se 1 (by rfl) ⟨6909542, by rfl⟩ : syracuseStep 9212723 = 13819085) B13819085
theorem B1438523 : Blo 1437538 1438523 := bstep (se 1 (by rfl) ⟨1078892, by rfl⟩ : syracuseStep 1438523 = 2157785) B2157785
theorem B2593595 : Blo 1437538 2593595 := bstep (se 1 (by rfl) ⟨1945196, by rfl⟩ : syracuseStep 2593595 = 3890393) B3890393
theorem B1438599 : Blo 1437538 1438599 := bstep (se 1 (by rfl) ⟨1078949, by rfl⟩ : syracuseStep 1438599 = 2157899) B2157899
theorem B1438607 : Blo 1437538 1438607 := bstep (se 1 (by rfl) ⟨1078955, by rfl⟩ : syracuseStep 1438607 = 2157911) B2157911
theorem B1438651 : Blo 1437538 1438651 := bstep (se 1 (by rfl) ⟨1078988, by rfl⟩ : syracuseStep 1438651 = 2157977) B2157977
theorem B1438727 : Blo 1437538 1438727 := bstep (se 1 (by rfl) ⟨1079045, by rfl⟩ : syracuseStep 1438727 = 2158091) B2158091
theorem B1618951 : Blo 1437538 1618951 := bstep (se 1 (by rfl) ⟨1214213, by rfl⟩ : syracuseStep 1618951 = 2428427) B2428427
theorem B1438735 : Blo 1437538 1438735 := bstep (se 1 (by rfl) ⟨1079051, by rfl⟩ : syracuseStep 1438735 = 2158103) B2158103
theorem B1438779 : Blo 1437538 1438779 := bstep (se 1 (by rfl) ⟨1079084, by rfl⟩ : syracuseStep 1438779 = 2158169) B2158169
theorem B1438855 : Blo 1437538 1438855 := bstep (se 1 (by rfl) ⟨1079141, by rfl⟩ : syracuseStep 1438855 = 2158283) B2158283
theorem B1438863 : Blo 1437538 1438863 := bstep (se 1 (by rfl) ⟨1079147, by rfl⟩ : syracuseStep 1438863 = 2158295) B2158295
theorem B1438907 : Blo 1437538 1438907 := bstep (se 1 (by rfl) ⟨1079180, by rfl⟩ : syracuseStep 1438907 = 2158361) B2158361
theorem B1619131 : Blo 1437538 1619131 := bstep (se 1 (by rfl) ⟨1214348, by rfl⟩ : syracuseStep 1619131 = 2428697) B2428697
theorem B3691777 : Blo 1437538 3691777 := bstep (se 2 (by rfl) ⟨1384416, by rfl⟩ : syracuseStep 3691777 = 2768833) B2768833
theorem B1438983 : Blo 1437538 1438983 := bstep (se 1 (by rfl) ⟨1079237, by rfl⟩ : syracuseStep 1438983 = 2158475) B2158475
theorem B1438991 : Blo 1437538 1438991 := bstep (se 1 (by rfl) ⟨1079243, by rfl⟩ : syracuseStep 1438991 = 2158487) B2158487
theorem B6141217 : Blo 1437538 6141217 := bstep (se 2 (by rfl) ⟨2302956, by rfl⟩ : syracuseStep 6141217 = 4605913) B4605913
theorem B8189221 : Blo 1437538 8189221 := bstep (se 4 (by rfl) ⟨767739, by rfl⟩ : syracuseStep 8189221 = 1535479) B1535479
theorem B1439035 : Blo 1437538 1439035 := bstep (se 1 (by rfl) ⟨1079276, by rfl⟩ : syracuseStep 1439035 = 2158553) B2158553
theorem B1439111 : Blo 1437538 1439111 := bstep (se 1 (by rfl) ⟨1079333, by rfl⟩ : syracuseStep 1439111 = 2158667) B2158667
theorem B1439119 : Blo 1437538 1439119 := bstep (se 1 (by rfl) ⟨1079339, by rfl⟩ : syracuseStep 1439119 = 2158679) B2158679
theorem B4855193 : Blo 1437538 4855193 := bstep (se 2 (by rfl) ⟨1820697, by rfl⟩ : syracuseStep 4855193 = 3641395) B3641395
theorem B1439163 : Blo 1437538 1439163 := bstep (se 1 (by rfl) ⟨1079372, by rfl⟩ : syracuseStep 1439163 = 2158745) B2158745
theorem B7009739 : Blo 1437538 7009739 := bstep (se 1 (by rfl) ⟨5257304, by rfl⟩ : syracuseStep 7009739 = 10514609) B10514609
theorem B1439239 : Blo 1437538 1439239 := bstep (se 1 (by rfl) ⟨1079429, by rfl⟩ : syracuseStep 1439239 = 2158859) B2158859
theorem B1439247 : Blo 1437538 1439247 := bstep (se 1 (by rfl) ⟨1079435, by rfl⟩ : syracuseStep 1439247 = 2158871) B2158871
theorem B1439291 : Blo 1437538 1439291 := bstep (se 1 (by rfl) ⟨1079468, by rfl⟩ : syracuseStep 1439291 = 2158937) B2158937
theorem B3642995 : Blo 1437538 3642995 := bstep (se 1 (by rfl) ⟨2732246, by rfl⟩ : syracuseStep 3642995 = 5464493) B5464493
theorem B3643015 : Blo 1437538 3643015 := bstep (se 1 (by rfl) ⟨2732261, by rfl⟩ : syracuseStep 3643015 = 5464523) B5464523
theorem B1439367 : Blo 1437538 1439367 := bstep (se 1 (by rfl) ⟨1079525, by rfl⟩ : syracuseStep 1439367 = 2159051) B2159051
theorem B1439375 : Blo 1437538 1439375 := bstep (se 1 (by rfl) ⟨1079531, by rfl⟩ : syracuseStep 1439375 = 2159063) B2159063
theorem B1439419 : Blo 1437538 1439419 := bstep (se 1 (by rfl) ⟨1079564, by rfl⟩ : syracuseStep 1439419 = 2159129) B2159129
theorem B1439495 : Blo 1437538 1439495 := bstep (se 1 (by rfl) ⟨1079621, by rfl⟩ : syracuseStep 1439495 = 2159243) B2159243
theorem B5461775 : Blo 1437538 5461775 := bstep (se 1 (by rfl) ⟨4096331, by rfl⟩ : syracuseStep 5461775 = 8192663) B8192663
theorem B1439503 : Blo 1437538 1439503 := bstep (se 1 (by rfl) ⟨1079627, by rfl⟩ : syracuseStep 1439503 = 2159255) B2159255
theorem B15554339 : Blo 1437538 15554339 := bstep (se 1 (by rfl) ⟨11665754, by rfl⟩ : syracuseStep 15554339 = 23331509) B23331509
theorem B3503915 : Blo 1437538 3503915 := bstep (se 1 (by rfl) ⟨2627936, by rfl⟩ : syracuseStep 3503915 = 5255873) B5255873
theorem B8189747 : Blo 1437538 8189747 := bstep (se 1 (by rfl) ⟨6142310, by rfl⟩ : syracuseStep 8189747 = 12284621) B12284621
theorem B3643289 : Blo 1437538 3643289 := bstep (se 2 (by rfl) ⟨1366233, by rfl⟩ : syracuseStep 3643289 = 2732467) B2732467
theorem B3889181 : Blo 1437538 3889181 := bstep (se 3 (by rfl) ⟨729221, by rfl⟩ : syracuseStep 3889181 = 1458443) B1458443
theorem B3643451 : Blo 1437538 3643451 := bstep (se 1 (by rfl) ⟨2732588, by rfl⟩ : syracuseStep 3643451 = 5465177) B5465177
theorem B4855895 : Blo 1437538 4855895 := bstep (se 1 (by rfl) ⟨3641921, by rfl⟩ : syracuseStep 4855895 = 7283843) B7283843
theorem B22132909 : Blo 1437538 22132909 := bstep (se 3 (by rfl) ⟨4149920, by rfl⟩ : syracuseStep 22132909 = 8299841) B8299841
theorem B3643663 : Blo 1437538 3643663 := bstep (se 1 (by rfl) ⟨2732747, by rfl⟩ : syracuseStep 3643663 = 5465495) B5465495
theorem B3070241 : Blo 1437538 3070241 := bstep (se 2 (by rfl) ⟨1151340, by rfl⟩ : syracuseStep 3070241 = 2302681) B2302681
theorem B3889451 : Blo 1437538 3889451 := bstep (se 1 (by rfl) ⟨2917088, by rfl⟩ : syracuseStep 3889451 = 5834177) B5834177
theorem B4094327 : Blo 1437538 4094327 := bstep (se 1 (by rfl) ⟨3070745, by rfl⟩ : syracuseStep 4094327 = 6141491) B6141491
theorem B3070343 : Blo 1437538 3070343 := bstep (se 1 (by rfl) ⟨2302757, by rfl⟩ : syracuseStep 3070343 = 4605515) B4605515
theorem B2428987 : Blo 1437538 2428987 := bstep (se 1 (by rfl) ⟨1821740, by rfl⟩ : syracuseStep 2428987 = 3643481) B3643481
theorem B3693089 : Blo 1437538 3693089 := bstep (se 2 (by rfl) ⟨1384908, by rfl⟩ : syracuseStep 3693089 = 2769817) B2769817
theorem B4856381 : Blo 1437538 4856381 := bstep (se 3 (by rfl) ⟨910571, by rfl⟩ : syracuseStep 4856381 = 1821143) B1821143
theorem B11663939 : Blo 1437538 11663939 := bstep (se 1 (by rfl) ⟨8747954, by rfl⟩ : syracuseStep 11663939 = 17495909) B17495909
theorem B13818545 : Blo 1437538 13818545 := bstep (se 2 (by rfl) ⟨5181954, by rfl⟩ : syracuseStep 13818545 = 10363909) B10363909
theorem B16390835 : Blo 1437538 16390835 := bstep (se 1 (by rfl) ⟨12293126, by rfl⟩ : syracuseStep 16390835 = 24586253) B24586253
theorem B9214721 : Blo 1437538 9214721 := bstep (se 2 (by rfl) ⟨3455520, by rfl⟩ : syracuseStep 9214721 = 6911041) B6911041
theorem B17496881 : Blo 1437538 17496881 := bstep (se 2 (by rfl) ⟨6561330, by rfl⟩ : syracuseStep 17496881 = 13122661) B13122661
theorem B2186041 : Blo 1437538 2186041 := bstep (se 2 (by rfl) ⟨819765, by rfl⟩ : syracuseStep 2186041 = 1639531) B1639531
theorem B3234707 : Blo 1437538 3234707 := bstep (se 1 (by rfl) ⟨2426030, by rfl⟩ : syracuseStep 3234707 = 4852061) B4852061
theorem B6142873 : Blo 1437538 6142873 := bstep (se 2 (by rfl) ⟨2303577, by rfl⟩ : syracuseStep 6142873 = 4607155) B4607155
theorem B2046907 : Blo 1437538 2046907 := bstep (se 1 (by rfl) ⟨1535180, by rfl⟩ : syracuseStep 2046907 = 3070361) B3070361
theorem B3234761 : Blo 1437538 3234761 := bstep (se 2 (by rfl) ⟨1213035, by rfl⟩ : syracuseStep 3234761 = 2426071) B2426071
theorem B2767817 : Blo 1437538 2767817 := bstep (se 2 (by rfl) ⟨1037931, by rfl⟩ : syracuseStep 2767817 = 2075863) B2075863
theorem B4373639 : Blo 1437538 4373639 := bstep (se 1 (by rfl) ⟨3280229, by rfl⟩ : syracuseStep 4373639 = 6560459) B6560459
theorem B8191205 : Blo 1437538 8191205 := bstep (se 4 (by rfl) ⟨767925, by rfl⟩ : syracuseStep 8191205 = 1535851) B1535851
theorem B7781669 : Blo 1437538 7781669 := bstep (se 4 (by rfl) ⟨729531, by rfl⟩ : syracuseStep 7781669 = 1459063) B1459063
theorem B2047351 : Blo 1437538 2047351 := bstep (se 1 (by rfl) ⟨1535513, by rfl⟩ : syracuseStep 2047351 = 3071027) B3071027
theorem B1998343 : Blo 1437538 1998343 := bstep (se 1 (by rfl) ⟨1498757, by rfl⟩ : syracuseStep 1998343 = 2997515) B2997515
theorem B34979357 : Blo 1437538 34979357 := bstep (se 3 (by rfl) ⟨6558629, by rfl⟩ : syracuseStep 34979357 = 13117259) B13117259
theorem B2186795 : Blo 1437538 2186795 := bstep (se 1 (by rfl) ⟨1640096, by rfl⟩ : syracuseStep 2186795 = 3280193) B3280193
theorem B13672003 : Blo 1437538 13672003 := bstep (se 1 (by rfl) ⟨10254002, by rfl⟩ : syracuseStep 13672003 = 20508005) B20508005
theorem B3235463 : Blo 1437538 3235463 := bstep (se 1 (by rfl) ⟨2426597, by rfl⟩ : syracuseStep 3235463 = 4853195) B4853195
theorem B3235643 : Blo 1437538 3235643 := bstep (se 1 (by rfl) ⟨2426732, by rfl⟩ : syracuseStep 3235643 = 4853465) B4853465
theorem B7282547 : Blo 1437538 7282547 := bstep (se 1 (by rfl) ⟨5461910, by rfl⟩ : syracuseStep 7282547 = 10923821) B10923821
theorem B3235769 : Blo 1437538 3235769 := bstep (se 2 (by rfl) ⟨1213413, by rfl⟩ : syracuseStep 3235769 = 2426827) B2426827
theorem B4857785 : Blo 1437538 4857785 := bstep (se 2 (by rfl) ⟨1821669, by rfl⟩ : syracuseStep 4857785 = 3643339) B3643339
theorem B18677765 : Blo 1437538 18677765 := bstep (se 4 (by rfl) ⟨1751040, by rfl⟩ : syracuseStep 18677765 = 3502081) B3502081
theorem B3235859 : Blo 1437538 3235859 := bstep (se 1 (by rfl) ⟨2426894, by rfl⟩ : syracuseStep 3235859 = 4853789) B4853789
theorem B6225977 : Blo 1437538 6225977 := bstep (se 2 (by rfl) ⟨2334741, by rfl⟩ : syracuseStep 6225977 = 4669483) B4669483
theorem B10371149 : Blo 1437538 10371149 := bstep (se 3 (by rfl) ⟨1944590, by rfl⟩ : syracuseStep 10371149 = 3889181) B3889181
theorem B8749171 : Blo 1437538 8749171 := bstep (se 1 (by rfl) ⟨6561878, by rfl⟩ : syracuseStep 8749171 = 13123757) B13123757
theorem B16605413 : Blo 1437538 16605413 := bstep (se 4 (by rfl) ⟨1556757, by rfl⟩ : syracuseStep 16605413 = 3113515) B3113515
theorem B20750651 : Blo 1437538 20750651 := bstep (se 1 (by rfl) ⟨15562988, by rfl⟩ : syracuseStep 20750651 = 31125977) B31125977
theorem B93258053 : Blo 1437538 93258053 := bstep (se 4 (by rfl) ⟨8742942, by rfl⟩ : syracuseStep 93258053 = 17485885) B17485885
theorem B3236201 : Blo 1437538 3236201 := bstep (se 2 (by rfl) ⟨1213575, by rfl⟩ : syracuseStep 3236201 = 2427151) B2427151
theorem B4858217 : Blo 1437538 4858217 := bstep (se 2 (by rfl) ⟨1821831, by rfl⟩ : syracuseStep 4858217 = 3643663) B3643663
theorem B1728875 : Blo 1437538 1728875 := bstep (se 1 (by rfl) ⟨1296656, by rfl⟩ : syracuseStep 1728875 = 2593313) B2593313
theorem B2187695 : Blo 1437538 2187695 := bstep (se 1 (by rfl) ⟨1640771, by rfl⟩ : syracuseStep 2187695 = 3281543) B3281543
theorem B1729063 : Blo 1437538 1729063 := bstep (se 1 (by rfl) ⟨1296797, by rfl⟩ : syracuseStep 1729063 = 2593595) B2593595
theorem B6914771 : Blo 1437538 6914771 := bstep (se 1 (by rfl) ⟨5186078, by rfl⟩ : syracuseStep 6914771 = 10372157) B10372157
theorem B3236795 : Blo 1437538 3236795 := bstep (se 1 (by rfl) ⟨2427596, by rfl⟩ : syracuseStep 3236795 = 4855193) B4855193
theorem B3236921 : Blo 1437538 3236921 := bstep (se 2 (by rfl) ⟨1213845, by rfl⟩ : syracuseStep 3236921 = 2427691) B2427691
theorem B1819847 : Blo 1437538 1819847 := bstep (se 1 (by rfl) ⟨1364885, by rfl⟩ : syracuseStep 1819847 = 2729771) B2729771
theorem B2335943 : Blo 1437538 2335943 := bstep (se 1 (by rfl) ⟨1751957, by rfl⟩ : syracuseStep 2335943 = 3503915) B3503915
theorem B2729209 : Blo 1437538 2729209 := bstep (se 2 (by rfl) ⟨1023453, by rfl⟩ : syracuseStep 2729209 = 2046907) B2046907
theorem B2426105 : Blo 1437538 2426105 := bstep (se 2 (by rfl) ⟨909789, by rfl⟩ : syracuseStep 2426105 = 1819579) B1819579
theorem B5834045 : Blo 1437538 5834045 := bstep (se 3 (by rfl) ⟨1093883, by rfl⟩ : syracuseStep 5834045 = 2187767) B2187767
theorem B1819999 : Blo 1437538 1819999 := bstep (se 1 (by rfl) ⟨1364999, by rfl⟩ : syracuseStep 1819999 = 2729999) B2729999
theorem B3073385 : Blo 1437538 3073385 := bstep (se 2 (by rfl) ⟨1152519, by rfl⟩ : syracuseStep 3073385 = 2305039) B2305039
theorem B3237263 : Blo 1437538 3237263 := bstep (se 1 (by rfl) ⟨2427947, by rfl⟩ : syracuseStep 3237263 = 4855895) B4855895
theorem B2426287 : Blo 1437538 2426287 := bstep (se 1 (by rfl) ⟨1819715, by rfl⟩ : syracuseStep 2426287 = 3639431) B3639431
theorem B2426375 : Blo 1437538 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B2729551 : Blo 1437538 2729551 := bstep (se 1 (by rfl) ⟨2047163, by rfl⟩ : syracuseStep 2729551 = 4094327) B4094327
theorem B3237587 : Blo 1437538 3237587 := bstep (se 1 (by rfl) ⟨2428190, by rfl⟩ : syracuseStep 3237587 = 4856381) B4856381
theorem B7775959 : Blo 1437538 7775959 := bstep (se 1 (by rfl) ⟨5831969, by rfl⟩ : syracuseStep 7775959 = 11663939) B11663939
theorem B8308439 : Blo 1437538 8308439 := bstep (se 1 (by rfl) ⟨6231329, by rfl⟩ : syracuseStep 8308439 = 12462659) B12462659
theorem B6227779 : Blo 1437538 6227779 := bstep (se 1 (by rfl) ⟨4670834, by rfl⟩ : syracuseStep 6227779 = 9341669) B9341669
theorem B2729801 : Blo 1437538 2729801 := bstep (se 2 (by rfl) ⟨1023675, by rfl⟩ : syracuseStep 2729801 = 2047351) B2047351
theorem B2426719 : Blo 1437538 2426719 := bstep (se 1 (by rfl) ⟨1820039, by rfl⟩ : syracuseStep 2426719 = 3640079) B3640079
theorem B2156393 : Blo 1437538 2156393 := bstep (se 2 (by rfl) ⟨808647, by rfl⟩ : syracuseStep 2156393 = 1617295) B1617295
theorem B2156471 : Blo 1437538 2156471 := bstep (se 1 (by rfl) ⟨1617353, by rfl⟩ : syracuseStep 2156471 = 3234707) B3234707
theorem B2426807 : Blo 1437538 2426807 := bstep (se 1 (by rfl) ⟨1820105, by rfl⟩ : syracuseStep 2426807 = 3640211) B3640211
theorem B8873921 : Blo 1437538 8873921 := bstep (se 2 (by rfl) ⟨3327720, by rfl⟩ : syracuseStep 8873921 = 6655441) B6655441
theorem B2156507 : Blo 1437538 2156507 := bstep (se 1 (by rfl) ⟨1617380, by rfl⟩ : syracuseStep 2156507 = 3234761) B3234761
theorem B2664457 : Blo 1437538 2664457 := bstep (se 2 (by rfl) ⟨999171, by rfl⟩ : syracuseStep 2664457 = 1998343) B1998343
theorem B4851791 : Blo 1437538 4851791 := bstep (se 1 (by rfl) ⟨3638843, by rfl⟩ : syracuseStep 4851791 = 7277687) B7277687
theorem B8874065 : Blo 1437538 8874065 := bstep (se 2 (by rfl) ⟨3327774, by rfl⟩ : syracuseStep 8874065 = 6655549) B6655549
theorem B18229337 : Blo 1437538 18229337 := bstep (se 2 (by rfl) ⟨6836001, by rfl⟩ : syracuseStep 18229337 = 13672003) B13672003
theorem B5187779 : Blo 1437538 5187779 := bstep (se 1 (by rfl) ⟨3890834, by rfl⟩ : syracuseStep 5187779 = 7781669) B7781669
theorem B2156975 : Blo 1437538 2156975 := bstep (se 1 (by rfl) ⟨1617731, by rfl⟩ : syracuseStep 2156975 = 3235463) B3235463
theorem B4852169 : Blo 1437538 4852169 := bstep (se 2 (by rfl) ⟨1819563, by rfl⟩ : syracuseStep 4852169 = 3639127) B3639127
theorem B2492891 : Blo 1437538 2492891 := bstep (se 1 (by rfl) ⟨1869668, by rfl⟩ : syracuseStep 2492891 = 3739337) B3739337
theorem B2157065 : Blo 1437538 2157065 := bstep (se 2 (by rfl) ⟨808899, by rfl⟩ : syracuseStep 2157065 = 1617799) B1617799
theorem B2427401 : Blo 1437538 2427401 := bstep (se 2 (by rfl) ⟨910275, by rfl⟩ : syracuseStep 2427401 = 1820551) B1820551
theorem B2157095 : Blo 1437538 2157095 := bstep (se 1 (by rfl) ⟨1617821, by rfl⟩ : syracuseStep 2157095 = 3235643) B3235643
theorem B2157179 : Blo 1437538 2157179 := bstep (se 1 (by rfl) ⟨1617884, by rfl⟩ : syracuseStep 2157179 = 3235769) B3235769
theorem B3238523 : Blo 1437538 3238523 := bstep (se 1 (by rfl) ⟨2428892, by rfl⟩ : syracuseStep 3238523 = 4857785) B4857785
theorem B2730667 : Blo 1437538 2730667 := bstep (se 1 (by rfl) ⟨2048000, by rfl⟩ : syracuseStep 2730667 = 4096001) B4096001
theorem B2427563 : Blo 1437538 2427563 := bstep (se 1 (by rfl) ⟨1820672, by rfl⟩ : syracuseStep 2427563 = 3641345) B3641345
theorem B5835473 : Blo 1437538 5835473 := bstep (se 2 (by rfl) ⟨2188302, by rfl⟩ : syracuseStep 5835473 = 4376605) B4376605
theorem B4852439 : Blo 1437538 4852439 := bstep (se 1 (by rfl) ⟨3639329, by rfl⟩ : syracuseStep 4852439 = 7278659) B7278659
theorem B2730743 : Blo 1437538 2730743 := bstep (se 1 (by rfl) ⟨2048057, by rfl⟩ : syracuseStep 2730743 = 4096115) B4096115
theorem B2157305 : Blo 1437538 2157305 := bstep (se 2 (by rfl) ⟨808989, by rfl⟩ : syracuseStep 2157305 = 1617979) B1617979
theorem B3238649 : Blo 1437538 3238649 := bstep (se 2 (by rfl) ⟨1214493, by rfl⟩ : syracuseStep 3238649 = 2428987) B2428987
theorem B2157407 : Blo 1437538 2157407 := bstep (se 1 (by rfl) ⟨1618055, by rfl⟩ : syracuseStep 2157407 = 3236111) B3236111
theorem B2157419 : Blo 1437538 2157419 := bstep (se 1 (by rfl) ⟨1618064, by rfl⟩ : syracuseStep 2157419 = 3236129) B3236129
theorem B2304911 : Blo 1437538 2304911 := bstep (se 1 (by rfl) ⟨1728683, by rfl⟩ : syracuseStep 2304911 = 3457367) B3457367
theorem B4852655 : Blo 1437538 4852655 := bstep (se 1 (by rfl) ⟨3639491, by rfl⟩ : syracuseStep 4852655 = 7278983) B7278983
theorem B2730971 : Blo 1437538 2730971 := bstep (se 1 (by rfl) ⟨2048228, by rfl⟩ : syracuseStep 2730971 = 4096457) B4096457
theorem B3238919 : Blo 1437538 3238919 := bstep (se 1 (by rfl) ⟨2429189, by rfl⟩ : syracuseStep 3238919 = 4858379) B4858379
theorem B26258455 : Blo 1437538 26258455 := bstep (se 1 (by rfl) ⟨19693841, by rfl⟩ : syracuseStep 26258455 = 39387683) B39387683
theorem B2427961 : Blo 1437538 2427961 := bstep (se 2 (by rfl) ⟨910485, by rfl⟩ : syracuseStep 2427961 = 1820971) B1820971
theorem B2157647 : Blo 1437538 2157647 := bstep (se 1 (by rfl) ⟨1618235, by rfl⟩ : syracuseStep 2157647 = 3236471) B3236471
theorem B1641551 : Blo 1437538 1641551 := bstep (se 1 (by rfl) ⟨1231163, by rfl⟩ : syracuseStep 1641551 = 2462327) B2462327
theorem B21023939 : Blo 1437538 21023939 := bstep (se 1 (by rfl) ⟨15767954, by rfl⟩ : syracuseStep 21023939 = 31535909) B31535909
theorem B2157767 : Blo 1437538 2157767 := bstep (se 1 (by rfl) ⟨1618325, by rfl⟩ : syracuseStep 2157767 = 3236651) B3236651
theorem B2428103 : Blo 1437538 2428103 := bstep (se 1 (by rfl) ⟨1821077, by rfl⟩ : syracuseStep 2428103 = 3642155) B3642155
theorem B20737271 : Blo 1437538 20737271 := bstep (se 1 (by rfl) ⟨15552953, by rfl⟩ : syracuseStep 20737271 = 31105907) B31105907
theorem B16379171 : Blo 1437538 16379171 := bstep (se 1 (by rfl) ⟨12284378, by rfl⟩ : syracuseStep 16379171 = 24568757) B24568757
theorem B2157929 : Blo 1437538 2157929 := bstep (se 2 (by rfl) ⟨809223, by rfl⟩ : syracuseStep 2157929 = 1618447) B1618447
theorem B2428265 : Blo 1437538 2428265 := bstep (se 2 (by rfl) ⟨910599, by rfl⟩ : syracuseStep 2428265 = 1821199) B1821199
theorem B2305423 : Blo 1437538 2305423 := bstep (se 1 (by rfl) ⟨1729067, by rfl⟩ : syracuseStep 2305423 = 3458135) B3458135
theorem B2158007 : Blo 1437538 2158007 := bstep (se 1 (by rfl) ⟨1618505, by rfl⟩ : syracuseStep 2158007 = 3237011) B3237011
theorem B2158043 : Blo 1437538 2158043 := bstep (se 1 (by rfl) ⟨1618532, by rfl⟩ : syracuseStep 2158043 = 3237065) B3237065
theorem B118042181 : Blo 1437538 118042181 := bstep (se 4 (by rfl) ⟨11066454, by rfl⟩ : syracuseStep 118042181 = 22132909) B22132909
theorem B4673159 : Blo 1437538 4673159 := bstep (se 1 (by rfl) ⟨3504869, by rfl⟩ : syracuseStep 4673159 = 7009739) B7009739
theorem B8187581 : Blo 1437538 8187581 := bstep (se 3 (by rfl) ⟨1535171, by rfl⟩ : syracuseStep 8187581 = 3070343) B3070343
theorem B2428663 : Blo 1437538 2428663 := bstep (se 1 (by rfl) ⟨1821497, by rfl⟩ : syracuseStep 2428663 = 3642995) B3642995
theorem B2592505 : Blo 1437538 2592505 := bstep (se 2 (by rfl) ⟨972189, by rfl⟩ : syracuseStep 2592505 = 1944379) B1944379
theorem B3641183 : Blo 1437538 3641183 := bstep (se 1 (by rfl) ⟨2730887, by rfl⟩ : syracuseStep 3641183 = 5461775) B5461775
theorem B5459831 : Blo 1437538 5459831 := bstep (se 1 (by rfl) ⟨4094873, by rfl⟩ : syracuseStep 5459831 = 8189747) B8189747
theorem B1437563 : Blo 1437538 1437563 := bstep (se 1 (by rfl) ⟨1078172, by rfl⟩ : syracuseStep 1437563 = 2156345) B2156345
theorem B7278497 : Blo 1437538 7278497 := bstep (se 2 (by rfl) ⟨2729436, by rfl⟩ : syracuseStep 7278497 = 5458873) B5458873
theorem B1437615 : Blo 1437538 1437615 := bstep (se 1 (by rfl) ⟨1078211, by rfl⟩ : syracuseStep 1437615 = 2156423) B2156423
theorem B2158511 : Blo 1437538 2158511 := bstep (se 1 (by rfl) ⟨1618883, by rfl⟩ : syracuseStep 2158511 = 3237767) B3237767
theorem B9220027 : Blo 1437538 9220027 := bstep (se 1 (by rfl) ⟨6915020, by rfl⟩ : syracuseStep 9220027 = 13830041) B13830041
theorem B2428859 : Blo 1437538 2428859 := bstep (se 1 (by rfl) ⟨1821644, by rfl⟩ : syracuseStep 2428859 = 3643289) B3643289
theorem B1437639 : Blo 1437538 1437639 := bstep (se 1 (by rfl) ⟨1078229, by rfl⟩ : syracuseStep 1437639 = 2156459) B2156459
theorem B1437659 : Blo 1437538 1437659 := bstep (se 1 (by rfl) ⟨1078244, by rfl⟩ : syracuseStep 1437659 = 2156489) B2156489
theorem B2158601 : Blo 1437538 2158601 := bstep (se 2 (by rfl) ⟨809475, by rfl⟩ : syracuseStep 2158601 = 1618951) B1618951
theorem B1437735 : Blo 1437538 1437735 := bstep (se 1 (by rfl) ⟨1078301, by rfl⟩ : syracuseStep 1437735 = 2156603) B2156603
theorem B2158631 : Blo 1437538 2158631 := bstep (se 1 (by rfl) ⟨1618973, by rfl⟩ : syracuseStep 2158631 = 3237947) B3237947
theorem B2428967 : Blo 1437538 2428967 := bstep (se 1 (by rfl) ⟨1821725, by rfl⟩ : syracuseStep 2428967 = 3643451) B3643451
theorem B1437775 : Blo 1437538 1437775 := bstep (se 1 (by rfl) ⟨1078331, by rfl⟩ : syracuseStep 1437775 = 2156663) B2156663
theorem B1437791 : Blo 1437538 1437791 := bstep (se 1 (by rfl) ⟨1078343, by rfl⟩ : syracuseStep 1437791 = 2156687) B2156687
theorem B1437819 : Blo 1437538 1437819 := bstep (se 1 (by rfl) ⟨1078364, by rfl⟩ : syracuseStep 1437819 = 2156729) B2156729
theorem B2158715 : Blo 1437538 2158715 := bstep (se 1 (by rfl) ⟨1619036, by rfl⟩ : syracuseStep 2158715 = 3238073) B3238073
theorem B1437871 : Blo 1437538 1437871 := bstep (se 1 (by rfl) ⟨1078403, by rfl⟩ : syracuseStep 1437871 = 2156807) B2156807
theorem B1437895 : Blo 1437538 1437895 := bstep (se 1 (by rfl) ⟨1078421, by rfl⟩ : syracuseStep 1437895 = 2156843) B2156843
theorem B2592967 : Blo 1437538 2592967 := bstep (se 1 (by rfl) ⟨1944725, by rfl⟩ : syracuseStep 2592967 = 3889451) B3889451
theorem B2732231 : Blo 1437538 2732231 := bstep (se 1 (by rfl) ⟨2049173, by rfl⟩ : syracuseStep 2732231 = 4098347) B4098347
theorem B1437915 : Blo 1437538 1437915 := bstep (se 1 (by rfl) ⟨1078436, by rfl⟩ : syracuseStep 1437915 = 2156873) B2156873
theorem B2158841 : Blo 1437538 2158841 := bstep (se 2 (by rfl) ⟨809565, by rfl⟩ : syracuseStep 2158841 = 1619131) B1619131
theorem B1437991 : Blo 1437538 1437991 := bstep (se 1 (by rfl) ⟨1078493, by rfl⟩ : syracuseStep 1437991 = 2156987) B2156987
theorem B141914429 : Blo 1437538 141914429 := bstep (se 3 (by rfl) ⟨26608955, by rfl⟩ : syracuseStep 141914429 = 53217911) B53217911
theorem B1438031 : Blo 1437538 1438031 := bstep (se 1 (by rfl) ⟨1078523, by rfl⟩ : syracuseStep 1438031 = 2157047) B2157047
theorem B1438047 : Blo 1437538 1438047 := bstep (se 1 (by rfl) ⟨1078535, by rfl⟩ : syracuseStep 1438047 = 2157071) B2157071
theorem B2732383 : Blo 1437538 2732383 := bstep (se 1 (by rfl) ⟨2049287, by rfl⟩ : syracuseStep 2732383 = 4098575) B4098575
theorem B2158943 : Blo 1437538 2158943 := bstep (se 1 (by rfl) ⟨1619207, by rfl⟩ : syracuseStep 2158943 = 3238415) B3238415
theorem B2158955 : Blo 1437538 2158955 := bstep (se 1 (by rfl) ⟨1619216, by rfl⟩ : syracuseStep 2158955 = 3238433) B3238433
theorem B2462059 : Blo 1437538 2462059 := bstep (se 1 (by rfl) ⟨1846544, by rfl⟩ : syracuseStep 2462059 = 3693089) B3693089
theorem B1438075 : Blo 1437538 1438075 := bstep (se 1 (by rfl) ⟨1078556, by rfl⟩ : syracuseStep 1438075 = 2157113) B2157113
theorem B8188289 : Blo 1437538 8188289 := bstep (se 2 (by rfl) ⟨3070608, by rfl⟩ : syracuseStep 8188289 = 6141217) B6141217
theorem B1438127 : Blo 1437538 1438127 := bstep (se 1 (by rfl) ⟨1078595, by rfl⟩ : syracuseStep 1438127 = 2157191) B2157191
theorem B1438151 : Blo 1437538 1438151 := bstep (se 1 (by rfl) ⟨1078613, by rfl⟩ : syracuseStep 1438151 = 2157227) B2157227
theorem B9212363 : Blo 1437538 9212363 := bstep (se 1 (by rfl) ⟨6909272, by rfl⟩ : syracuseStep 9212363 = 13818545) B13818545
theorem B1438171 : Blo 1437538 1438171 := bstep (se 1 (by rfl) ⟨1078628, by rfl⟩ : syracuseStep 1438171 = 2157257) B2157257
theorem B3641881 : Blo 1437538 3641881 := bstep (se 2 (by rfl) ⟨1365705, by rfl⟩ : syracuseStep 3641881 = 2731411) B2731411
theorem B1438247 : Blo 1437538 1438247 := bstep (se 1 (by rfl) ⟨1078685, by rfl⟩ : syracuseStep 1438247 = 2157371) B2157371
theorem B1438287 : Blo 1437538 1438287 := bstep (se 1 (by rfl) ⟨1078715, by rfl⟩ : syracuseStep 1438287 = 2157431) B2157431
theorem B2159183 : Blo 1437538 2159183 := bstep (se 1 (by rfl) ⟨1619387, by rfl⟩ : syracuseStep 2159183 = 3238775) B3238775
theorem B1438303 : Blo 1437538 1438303 := bstep (se 1 (by rfl) ⟨1078727, by rfl⟩ : syracuseStep 1438303 = 2157455) B2157455
theorem B1438331 : Blo 1437538 1438331 := bstep (se 1 (by rfl) ⟨1078748, by rfl⟩ : syracuseStep 1438331 = 2157497) B2157497
theorem B1618555 : Blo 1437538 1618555 := bstep (se 1 (by rfl) ⟨1213916, by rfl⟩ : syracuseStep 1618555 = 2427833) B2427833
theorem B1438383 : Blo 1437538 1438383 := bstep (se 1 (by rfl) ⟨1078787, by rfl⟩ : syracuseStep 1438383 = 2157575) B2157575
theorem B1438407 : Blo 1437538 1438407 := bstep (se 1 (by rfl) ⟨1078805, by rfl⟩ : syracuseStep 1438407 = 2157611) B2157611
theorem B2159303 : Blo 1437538 2159303 := bstep (se 1 (by rfl) ⟨1619477, by rfl⟩ : syracuseStep 2159303 = 3238955) B3238955
theorem B20746961 : Blo 1437538 20746961 := bstep (se 2 (by rfl) ⟨7780110, by rfl⟩ : syracuseStep 20746961 = 15560221) B15560221
theorem B1438427 : Blo 1437538 1438427 := bstep (se 1 (by rfl) ⟨1078820, by rfl⟩ : syracuseStep 1438427 = 2157641) B2157641
theorem B1438503 : Blo 1437538 1438503 := bstep (se 1 (by rfl) ⟨1078877, by rfl⟩ : syracuseStep 1438503 = 2157755) B2157755
theorem B5460803 : Blo 1437538 5460803 := bstep (se 1 (by rfl) ⟨4095602, by rfl⟩ : syracuseStep 5460803 = 8191205) B8191205
theorem B3642185 : Blo 1437538 3642185 := bstep (se 2 (by rfl) ⟨1365819, by rfl⟩ : syracuseStep 3642185 = 2731639) B2731639
theorem B1438543 : Blo 1437538 1438543 := bstep (se 1 (by rfl) ⟨1078907, by rfl⟩ : syracuseStep 1438543 = 2157815) B2157815
theorem B1438559 : Blo 1437538 1438559 := bstep (se 1 (by rfl) ⟨1078919, by rfl⟩ : syracuseStep 1438559 = 2157839) B2157839
theorem B2077547 : Blo 1437538 2077547 := bstep (se 1 (by rfl) ⟨1558160, by rfl⟩ : syracuseStep 2077547 = 3116321) B3116321
theorem B1438587 : Blo 1437538 1438587 := bstep (se 1 (by rfl) ⟨1078940, by rfl⟩ : syracuseStep 1438587 = 2157881) B2157881
theorem B1438639 : Blo 1437538 1438639 := bstep (se 1 (by rfl) ⟨1078979, by rfl⟩ : syracuseStep 1438639 = 2157959) B2157959
theorem B1438663 : Blo 1437538 1438663 := bstep (se 1 (by rfl) ⟨1078997, by rfl⟩ : syracuseStep 1438663 = 2157995) B2157995
theorem B1438683 : Blo 1437538 1438683 := bstep (se 1 (by rfl) ⟨1079012, by rfl⟩ : syracuseStep 1438683 = 2158025) B2158025
theorem B23319571 : Blo 1437538 23319571 := bstep (se 1 (by rfl) ⟨17489678, by rfl⟩ : syracuseStep 23319571 = 34979357) B34979357
theorem B1438759 : Blo 1437538 1438759 := bstep (se 1 (by rfl) ⟨1079069, by rfl⟩ : syracuseStep 1438759 = 2158139) B2158139
theorem B1438799 : Blo 1437538 1438799 := bstep (se 1 (by rfl) ⟨1079099, by rfl⟩ : syracuseStep 1438799 = 2158199) B2158199
theorem B1619023 : Blo 1437538 1619023 := bstep (se 1 (by rfl) ⟨1214267, by rfl⟩ : syracuseStep 1619023 = 2428535) B2428535
theorem B1438815 : Blo 1437538 1438815 := bstep (se 1 (by rfl) ⟨1079111, by rfl⟩ : syracuseStep 1438815 = 2158223) B2158223
theorem B1438843 : Blo 1437538 1438843 := bstep (se 1 (by rfl) ⟨1079132, by rfl⟩ : syracuseStep 1438843 = 2158265) B2158265
theorem B10917017 : Blo 1437538 10917017 := bstep (se 2 (by rfl) ⟨4093881, by rfl⟩ : syracuseStep 10917017 = 8187763) B8187763
theorem B1438895 : Blo 1437538 1438895 := bstep (se 1 (by rfl) ⟨1079171, by rfl⟩ : syracuseStep 1438895 = 2158343) B2158343
theorem B1438919 : Blo 1437538 1438919 := bstep (se 1 (by rfl) ⟨1079189, by rfl⟩ : syracuseStep 1438919 = 2158379) B2158379
theorem B24573131 : Blo 1437538 24573131 := bstep (se 1 (by rfl) ⟨18429848, by rfl⟩ : syracuseStep 24573131 = 36859697) B36859697
theorem B1438939 : Blo 1437538 1438939 := bstep (se 1 (by rfl) ⟨1079204, by rfl⟩ : syracuseStep 1438939 = 2158409) B2158409
theorem B4855031 : Blo 1437538 4855031 := bstep (se 1 (by rfl) ⟨3641273, by rfl⟩ : syracuseStep 4855031 = 7282547) B7282547
theorem B1439015 : Blo 1437538 1439015 := bstep (se 1 (by rfl) ⟨1079261, by rfl⟩ : syracuseStep 1439015 = 2158523) B2158523
theorem B1439055 : Blo 1437538 1439055 := bstep (se 1 (by rfl) ⟨1079291, by rfl⟩ : syracuseStep 1439055 = 2158583) B2158583
theorem B1439071 : Blo 1437538 1439071 := bstep (se 1 (by rfl) ⟨1079303, by rfl⟩ : syracuseStep 1439071 = 2158607) B2158607
theorem B1439099 : Blo 1437538 1439099 := bstep (se 1 (by rfl) ⟨1079324, by rfl⟩ : syracuseStep 1439099 = 2158649) B2158649
theorem B1439151 : Blo 1437538 1439151 := bstep (se 1 (by rfl) ⟨1079363, by rfl⟩ : syracuseStep 1439151 = 2158727) B2158727
theorem B1439175 : Blo 1437538 1439175 := bstep (se 1 (by rfl) ⟨1079381, by rfl⟩ : syracuseStep 1439175 = 2158763) B2158763
theorem B1439195 : Blo 1437538 1439195 := bstep (se 1 (by rfl) ⟨1079396, by rfl⟩ : syracuseStep 1439195 = 2158793) B2158793
theorem B1619419 : Blo 1437538 1619419 := bstep (se 1 (by rfl) ⟨1214564, by rfl⟩ : syracuseStep 1619419 = 2429129) B2429129
theorem B4797991 : Blo 1437538 4797991 := bstep (se 1 (by rfl) ⟨3598493, by rfl⟩ : syracuseStep 4797991 = 7196987) B7196987
theorem B1439271 : Blo 1437538 1439271 := bstep (se 1 (by rfl) ⟨1079453, by rfl⟩ : syracuseStep 1439271 = 2158907) B2158907
theorem B4855355 : Blo 1437538 4855355 := bstep (se 1 (by rfl) ⟨3641516, by rfl⟩ : syracuseStep 4855355 = 7283033) B7283033
theorem B1439311 : Blo 1437538 1439311 := bstep (se 1 (by rfl) ⟨1079483, by rfl⟩ : syracuseStep 1439311 = 2158967) B2158967
theorem B1439327 : Blo 1437538 1439327 := bstep (se 1 (by rfl) ⟨1079495, by rfl⟩ : syracuseStep 1439327 = 2158991) B2158991
theorem B1439355 : Blo 1437538 1439355 := bstep (se 1 (by rfl) ⟨1079516, by rfl⟩ : syracuseStep 1439355 = 2159033) B2159033
theorem B11826827 : Blo 1437538 11826827 := bstep (se 1 (by rfl) ⟨8870120, by rfl⟩ : syracuseStep 11826827 = 17740241) B17740241
theorem B1439407 : Blo 1437538 1439407 := bstep (se 1 (by rfl) ⟨1079555, by rfl⟩ : syracuseStep 1439407 = 2159111) B2159111
theorem B5183165 : Blo 1437538 5183165 := bstep (se 3 (by rfl) ⟨971843, by rfl⟩ : syracuseStep 5183165 = 1943687) B1943687
theorem B1439431 : Blo 1437538 1439431 := bstep (se 1 (by rfl) ⟨1079573, by rfl⟩ : syracuseStep 1439431 = 2159147) B2159147
theorem B1439451 : Blo 1437538 1439451 := bstep (se 1 (by rfl) ⟨1079588, by rfl⟩ : syracuseStep 1439451 = 2159177) B2159177
theorem B5461789 : Blo 1437538 5461789 := bstep (se 3 (by rfl) ⟨1024085, by rfl⟩ : syracuseStep 5461789 = 2048171) B2048171
theorem B1439527 : Blo 1437538 1439527 := bstep (se 1 (by rfl) ⟨1079645, by rfl⟩ : syracuseStep 1439527 = 2159291) B2159291
theorem B4855625 : Blo 1437538 4855625 := bstep (se 2 (by rfl) ⟨1820859, by rfl⟩ : syracuseStep 4855625 = 3641719) B3641719
theorem B6141815 : Blo 1437538 6141815 := bstep (se 1 (by rfl) ⟨4606361, by rfl⟩ : syracuseStep 6141815 = 9212723) B9212723
theorem B3643319 : Blo 1437538 3643319 := bstep (se 1 (by rfl) ⟨2732489, by rfl⟩ : syracuseStep 3643319 = 5464979) B5464979
theorem B4372861 : Blo 1437538 4372861 := bstep (se 3 (by rfl) ⟨819911, by rfl⟩ : syracuseStep 4372861 = 1639823) B1639823
theorem B6560129 : Blo 1437538 6560129 := bstep (se 2 (by rfl) ⟨2460048, by rfl⟩ : syracuseStep 6560129 = 4920097) B4920097
theorem B2914721 : Blo 1437538 2914721 := bstep (se 2 (by rfl) ⟨1093020, by rfl⟩ : syracuseStep 2914721 = 2186041) B2186041
theorem B2955703 : Blo 1437538 2955703 := bstep (se 1 (by rfl) ⟨2216777, by rfl⟩ : syracuseStep 2955703 = 4433555) B4433555
theorem B10369559 : Blo 1437538 10369559 := bstep (se 1 (by rfl) ⟨7777169, by rfl⟩ : syracuseStep 10369559 = 15554339) B15554339
theorem B8190497 : Blo 1437538 8190497 := bstep (se 2 (by rfl) ⟨3071436, by rfl⟩ : syracuseStep 8190497 = 6142873) B6142873
theorem B5831453 : Blo 1437538 5831453 := bstep (se 3 (by rfl) ⟨1093397, by rfl⟩ : syracuseStep 5831453 = 2186795) B2186795
theorem B2046827 : Blo 1437538 2046827 := bstep (se 1 (by rfl) ⟨1535120, by rfl⟩ : syracuseStep 2046827 = 3070241) B3070241
theorem B3234743 : Blo 1437538 3234743 := bstep (se 1 (by rfl) ⟨2426057, by rfl⟩ : syracuseStep 3234743 = 4852115) B4852115
theorem B4856759 : Blo 1437538 4856759 := bstep (se 1 (by rfl) ⟨3642569, by rfl⟩ : syracuseStep 4856759 = 7285139) B7285139
theorem B4922369 : Blo 1437538 4922369 := bstep (se 2 (by rfl) ⟨1845888, by rfl⟩ : syracuseStep 4922369 = 3691777) B3691777
theorem B10918961 : Blo 1437538 10918961 := bstep (se 2 (by rfl) ⟨4094610, by rfl⟩ : syracuseStep 10918961 = 8189221) B8189221
theorem B2767969 : Blo 1437538 2767969 := bstep (se 2 (by rfl) ⟨1037988, by rfl⟩ : syracuseStep 2767969 = 2075977) B2075977
theorem B10927223 : Blo 1437538 10927223 := bstep (se 1 (by rfl) ⟨8195417, by rfl⟩ : syracuseStep 10927223 = 16390835) B16390835
theorem B6143147 : Blo 1437538 6143147 := bstep (se 1 (by rfl) ⟨4607360, by rfl⟩ : syracuseStep 6143147 = 9214721) B9214721
theorem B11664587 : Blo 1437538 11664587 := bstep (se 1 (by rfl) ⟨8748440, by rfl⟩ : syracuseStep 11664587 = 17496881) B17496881
theorem B2915759 : Blo 1437538 2915759 := bstep (se 1 (by rfl) ⟨2186819, by rfl⟩ : syracuseStep 2915759 = 4373639) B4373639
theorem B3235337 : Blo 1437538 3235337 := bstep (se 2 (by rfl) ⟨1213251, by rfl⟩ : syracuseStep 3235337 = 2426503) B2426503
theorem B4857353 : Blo 1437538 4857353 := bstep (se 2 (by rfl) ⟨1821507, by rfl⟩ : syracuseStep 4857353 = 3643015) B3643015
theorem B4152971 : Blo 1437538 4152971 := bstep (se 1 (by rfl) ⟨3114728, by rfl⟩ : syracuseStep 4152971 = 6229457) B6229457
theorem B3235679 : Blo 1437538 3235679 := bstep (se 1 (by rfl) ⟨2426759, by rfl⟩ : syracuseStep 3235679 = 4853519) B4853519
theorem B3071839 : Blo 1437538 3071839 := bstep (se 1 (by rfl) ⟨2303879, by rfl⟩ : syracuseStep 3071839 = 4607759) B4607759
theorem B7380845 : Blo 1437538 7380845 := bstep (se 3 (by rfl) ⟨1383908, by rfl⟩ : syracuseStep 7380845 = 2767817) B2767817
theorem B2367407 : Blo 1437538 2367407 := bstep (se 1 (by rfl) ⟨1775555, by rfl⟩ : syracuseStep 2367407 = 3551111) B3551111
theorem B12451843 : Blo 1437538 12451843 := bstep (se 1 (by rfl) ⟨9338882, by rfl⟩ : syracuseStep 12451843 = 18677765) B18677765
theorem B6914099 : Blo 1437538 6914099 := bstep (se 1 (by rfl) ⟨5185574, by rfl⟩ : syracuseStep 6914099 = 10371149) B10371149
theorem B11665561 : Blo 1437538 11665561 := bstep (se 2 (by rfl) ⟨4374585, by rfl⟩ : syracuseStep 11665561 = 8749171) B8749171
theorem B94609619 : Blo 1437538 94609619 := bstep (se 1 (by rfl) ⟨70957214, by rfl⟩ : syracuseStep 94609619 = 141914429) B141914429
theorem B3457289 : Blo 1437538 3457289 := bstep (se 2 (by rfl) ⟨1296483, by rfl⟩ : syracuseStep 3457289 = 2592967) B2592967
theorem B14762501 : Blo 1437538 14762501 := bstep (se 4 (by rfl) ⟨1383984, by rfl⟩ : syracuseStep 14762501 = 2767969) B2767969
theorem B31105565 : Blo 1437538 31105565 := bstep (se 3 (by rfl) ⟨5832293, by rfl⟩ : syracuseStep 31105565 = 11664587) B11664587
theorem B3940937 : Blo 1437538 3940937 := bstep (se 2 (by rfl) ⟨1477851, by rfl⟩ : syracuseStep 3940937 = 2955703) B2955703
theorem B1557295 : Blo 1437538 1557295 := bstep (se 1 (by rfl) ⟨1167971, by rfl⟩ : syracuseStep 1557295 = 2335943) B2335943
theorem B15557453 : Blo 1437538 15557453 := bstep (se 3 (by rfl) ⟨2917022, by rfl⟩ : syracuseStep 15557453 = 5834045) B5834045
theorem B3236687 : Blo 1437538 3236687 := bstep (se 1 (by rfl) ⟨2427515, by rfl⟩ : syracuseStep 3236687 = 4855031) B4855031
theorem B2048923 : Blo 1437538 2048923 := bstep (se 1 (by rfl) ⟨1536692, by rfl⟩ : syracuseStep 2048923 = 3073385) B3073385
theorem B3236903 : Blo 1437538 3236903 := bstep (se 1 (by rfl) ⟨2427677, by rfl⟩ : syracuseStep 3236903 = 4855355) B4855355
theorem B5833853 : Blo 1437538 5833853 := bstep (se 3 (by rfl) ⟨1093847, by rfl⟩ : syracuseStep 5833853 = 2187695) B2187695
theorem B5538959 : Blo 1437538 5538959 := bstep (se 1 (by rfl) ⟨4154219, by rfl⟩ : syracuseStep 5538959 = 8308439) B8308439
theorem B3237083 : Blo 1437538 3237083 := bstep (se 1 (by rfl) ⟨2427812, by rfl⟩ : syracuseStep 3237083 = 4855625) B4855625
theorem B5916043 : Blo 1437538 5916043 := bstep (se 1 (by rfl) ⟨4437032, by rfl⟩ : syracuseStep 5916043 = 8874065) B8874065
theorem B3237281 : Blo 1437538 3237281 := bstep (se 2 (by rfl) ⟨1213980, by rfl⟩ : syracuseStep 3237281 = 2427961) B2427961
theorem B3458519 : Blo 1437538 3458519 := bstep (se 1 (by rfl) ⟨2593889, by rfl⟩ : syracuseStep 3458519 = 5187779) B5187779
theorem B1943147 : Blo 1437538 1943147 := bstep (se 1 (by rfl) ⟨1457360, by rfl⟩ : syracuseStep 1943147 = 2914721) B2914721
theorem B3638945 : Blo 1437538 3638945 := bstep (se 2 (by rfl) ⟨1364604, by rfl⟩ : syracuseStep 3638945 = 2729209) B2729209
theorem B2426665 : Blo 1437538 2426665 := bstep (se 2 (by rfl) ⟨909999, by rfl⟩ : syracuseStep 2426665 = 1819999) B1819999
theorem B1820495 : Blo 1437538 1820495 := bstep (se 1 (by rfl) ⟨1365371, by rfl⟩ : syracuseStep 1820495 = 2730743) B2730743
theorem B3073897 : Blo 1437538 3073897 := bstep (se 2 (by rfl) ⟨1152711, by rfl⟩ : syracuseStep 3073897 = 2305423) B2305423
theorem B2156495 : Blo 1437538 2156495 := bstep (se 1 (by rfl) ⟨1617371, by rfl⟩ : syracuseStep 2156495 = 3234743) B3234743
theorem B3237839 : Blo 1437538 3237839 := bstep (se 1 (by rfl) ⟨2428379, by rfl⟩ : syracuseStep 3237839 = 4856759) B4856759
theorem B1820647 : Blo 1437538 1820647 := bstep (se 1 (by rfl) ⟨1365485, by rfl⟩ : syracuseStep 1820647 = 2730971) B2730971
theorem B7284815 : Blo 1437538 7284815 := bstep (se 1 (by rfl) ⟨5463611, by rfl⟩ : syracuseStep 7284815 = 10927223) B10927223
theorem B3639401 : Blo 1437538 3639401 := bstep (se 2 (by rfl) ⟨1364775, by rfl⟩ : syracuseStep 3639401 = 2729551) B2729551
theorem B5458205 : Blo 1437538 5458205 := bstep (se 3 (by rfl) ⟨1023413, by rfl⟩ : syracuseStep 5458205 = 2046827) B2046827
theorem B5540125 : Blo 1437538 5540125 := bstep (se 3 (by rfl) ⟨1038773, by rfl⟩ : syracuseStep 5540125 = 2077547) B2077547
theorem B1943839 : Blo 1437538 1943839 := bstep (se 1 (by rfl) ⟨1457879, by rfl⟩ : syracuseStep 1943839 = 2915759) B2915759
theorem B3238217 : Blo 1437538 3238217 := bstep (se 2 (by rfl) ⟨1214331, by rfl⟩ : syracuseStep 3238217 = 2428663) B2428663
theorem B2156891 : Blo 1437538 2156891 := bstep (se 1 (by rfl) ⟨1617668, by rfl⟩ : syracuseStep 2156891 = 3235337) B3235337
theorem B3238235 : Blo 1437538 3238235 := bstep (se 1 (by rfl) ⟨2428676, by rfl⟩ : syracuseStep 3238235 = 4857353) B4857353
theorem B78694787 : Blo 1437538 78694787 := bstep (se 1 (by rfl) ⟨59021090, by rfl⟩ : syracuseStep 78694787 = 118042181) B118042181
theorem B3115439 : Blo 1437538 3115439 := bstep (se 1 (by rfl) ⟨2336579, by rfl⟩ : syracuseStep 3115439 = 4673159) B4673159
theorem B5458387 : Blo 1437538 5458387 := bstep (se 1 (by rfl) ⟨4093790, by rfl⟩ : syracuseStep 5458387 = 8187581) B8187581
theorem B2157119 : Blo 1437538 2157119 := bstep (se 1 (by rfl) ⟨1617839, by rfl⟩ : syracuseStep 2157119 = 3235679) B3235679
theorem B2427455 : Blo 1437538 2427455 := bstep (se 1 (by rfl) ⟨1820591, by rfl⟩ : syracuseStep 2427455 = 3641183) B3641183
theorem B3639887 : Blo 1437538 3639887 := bstep (se 1 (by rfl) ⟨2729915, by rfl⟩ : syracuseStep 3639887 = 5459831) B5459831
theorem B4852331 : Blo 1437538 4852331 := bstep (se 1 (by rfl) ⟨3639248, by rfl⟩ : syracuseStep 4852331 = 7278497) B7278497
theorem B2157239 : Blo 1437538 2157239 := bstep (se 1 (by rfl) ⟨1617929, by rfl⟩ : syracuseStep 2157239 = 3235859) B3235859
theorem B11070275 : Blo 1437538 11070275 := bstep (se 1 (by rfl) ⟨8302706, by rfl⟩ : syracuseStep 11070275 = 16605413) B16605413
theorem B4377469 : Blo 1437538 4377469 := bstep (se 3 (by rfl) ⟨820775, by rfl⟩ : syracuseStep 4377469 = 1641551) B1641551
theorem B62172035 : Blo 1437538 62172035 := bstep (se 1 (by rfl) ⟨46629026, by rfl⟩ : syracuseStep 62172035 = 93258053) B93258053
theorem B2157467 : Blo 1437538 2157467 := bstep (se 1 (by rfl) ⟨1618100, by rfl⟩ : syracuseStep 2157467 = 3236201) B3236201
theorem B3238811 : Blo 1437538 3238811 := bstep (se 1 (by rfl) ⟨2429108, by rfl⟩ : syracuseStep 3238811 = 4858217) B4858217
theorem B5458859 : Blo 1437538 5458859 := bstep (se 1 (by rfl) ⟨4094144, by rfl⟩ : syracuseStep 5458859 = 8188289) B8188289
theorem B13831307 : Blo 1437538 13831307 := bstep (se 1 (by rfl) ⟨10373480, by rfl⟩ : syracuseStep 13831307 = 20746961) B20746961
theorem B4852925 : Blo 1437538 4852925 := bstep (se 3 (by rfl) ⟨909923, by rfl⟩ : syracuseStep 4852925 = 1819847) B1819847
theorem B7285949 : Blo 1437538 7285949 := bstep (se 3 (by rfl) ⟨1366115, by rfl⟩ : syracuseStep 7285949 = 2732231) B2732231
theorem B3640535 : Blo 1437538 3640535 := bstep (se 1 (by rfl) ⟨2730401, by rfl⟩ : syracuseStep 3640535 = 5460803) B5460803
theorem B2428123 : Blo 1437538 2428123 := bstep (se 1 (by rfl) ⟨1821092, by rfl⟩ : syracuseStep 2428123 = 3642185) B3642185
theorem B2157863 : Blo 1437538 2157863 := bstep (se 1 (by rfl) ⟨1618397, by rfl⟩ : syracuseStep 2157863 = 3236795) B3236795
theorem B2157947 : Blo 1437538 2157947 := bstep (se 1 (by rfl) ⟨1618460, by rfl⟩ : syracuseStep 2157947 = 3236921) B3236921
theorem B2305417 : Blo 1437538 2305417 := bstep (se 2 (by rfl) ⟨864531, by rfl⟩ : syracuseStep 2305417 = 1729063) B1729063
theorem B7278011 : Blo 1437538 7278011 := bstep (se 1 (by rfl) ⟨5458508, by rfl⟩ : syracuseStep 7278011 = 10917017) B10917017
theorem B2158073 : Blo 1437538 2158073 := bstep (se 2 (by rfl) ⟨809277, by rfl⟩ : syracuseStep 2158073 = 1618555) B1618555
theorem B1617403 : Blo 1437538 1617403 := bstep (se 1 (by rfl) ⟨1213052, by rfl⟩ : syracuseStep 1617403 = 2426105) B2426105
theorem B3640889 : Blo 1437538 3640889 := bstep (se 2 (by rfl) ⟨1365333, by rfl⟩ : syracuseStep 3640889 = 2730667) B2730667
theorem B2158175 : Blo 1437538 2158175 := bstep (se 1 (by rfl) ⟨1618631, by rfl⟩ : syracuseStep 2158175 = 3237263) B3237263
theorem B17493677 : Blo 1437538 17493677 := bstep (se 3 (by rfl) ⟨3280064, by rfl⟩ : syracuseStep 17493677 = 6560129) B6560129
theorem B1617583 : Blo 1437538 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B7884551 : Blo 1437538 7884551 := bstep (se 1 (by rfl) ⟨5913413, by rfl⟩ : syracuseStep 7884551 = 11826827) B11826827
theorem B2158391 : Blo 1437538 2158391 := bstep (se 1 (by rfl) ⟨1618793, by rfl⟩ : syracuseStep 2158391 = 3237587) B3237587
theorem B1437595 : Blo 1437538 1437595 := bstep (se 1 (by rfl) ⟨1078196, by rfl⟩ : syracuseStep 1437595 = 2156393) B2156393
theorem B1437647 : Blo 1437538 1437647 := bstep (se 1 (by rfl) ⟨1078235, by rfl⟩ : syracuseStep 1437647 = 2156471) B2156471
theorem B1617871 : Blo 1437538 1617871 := bstep (se 1 (by rfl) ⟨1213403, by rfl⟩ : syracuseStep 1617871 = 2426807) B2426807
theorem B2428879 : Blo 1437538 2428879 := bstep (se 1 (by rfl) ⟨1821659, by rfl⟩ : syracuseStep 2428879 = 3643319) B3643319
theorem B1437671 : Blo 1437538 1437671 := bstep (se 1 (by rfl) ⟨1078253, by rfl⟩ : syracuseStep 1437671 = 2156507) B2156507
theorem B31092761 : Blo 1437538 31092761 := bstep (se 2 (by rfl) ⟨11659785, by rfl⟩ : syracuseStep 31092761 = 23319571) B23319571
theorem B12152891 : Blo 1437538 12152891 := bstep (se 1 (by rfl) ⟨9114668, by rfl⟩ : syracuseStep 12152891 = 18229337) B18229337
theorem B2158697 : Blo 1437538 2158697 := bstep (se 2 (by rfl) ⟨809511, by rfl⟩ : syracuseStep 2158697 = 1619023) B1619023
theorem B1437983 : Blo 1437538 1437983 := bstep (se 1 (by rfl) ⟨1078487, by rfl⟩ : syracuseStep 1437983 = 2156975) B2156975
theorem B1438043 : Blo 1437538 1438043 := bstep (se 1 (by rfl) ⟨1078532, by rfl⟩ : syracuseStep 1438043 = 2157065) B2157065
theorem B1618267 : Blo 1437538 1618267 := bstep (se 1 (by rfl) ⟨1213700, by rfl⟩ : syracuseStep 1618267 = 2427401) B2427401
theorem B5460331 : Blo 1437538 5460331 := bstep (se 1 (by rfl) ⟨4095248, by rfl⟩ : syracuseStep 5460331 = 8190497) B8190497
theorem B1438063 : Blo 1437538 1438063 := bstep (se 1 (by rfl) ⟨1078547, by rfl⟩ : syracuseStep 1438063 = 2157095) B2157095
theorem B1438119 : Blo 1437538 1438119 := bstep (se 1 (by rfl) ⟨1078589, by rfl⟩ : syracuseStep 1438119 = 2157179) B2157179
theorem B2159015 : Blo 1437538 2159015 := bstep (se 1 (by rfl) ⟨1619261, by rfl⟩ : syracuseStep 2159015 = 3238523) B3238523
theorem B1618375 : Blo 1437538 1618375 := bstep (se 1 (by rfl) ⟨1213781, by rfl⟩ : syracuseStep 1618375 = 2427563) B2427563
theorem B1438203 : Blo 1437538 1438203 := bstep (se 1 (by rfl) ⟨1078652, by rfl⟩ : syracuseStep 1438203 = 2157305) B2157305
theorem B2159099 : Blo 1437538 2159099 := bstep (se 1 (by rfl) ⟨1619324, by rfl⟩ : syracuseStep 2159099 = 3238649) B3238649
theorem B3887635 : Blo 1437538 3887635 := bstep (se 1 (by rfl) ⟨2915726, by rfl⟩ : syracuseStep 3887635 = 5831453) B5831453
theorem B1438271 : Blo 1437538 1438271 := bstep (se 1 (by rfl) ⟨1078703, by rfl⟩ : syracuseStep 1438271 = 2157407) B2157407
theorem B1438279 : Blo 1437538 1438279 := bstep (se 1 (by rfl) ⟨1078709, by rfl⟩ : syracuseStep 1438279 = 2157419) B2157419
theorem B1536607 : Blo 1437538 1536607 := bstep (se 1 (by rfl) ⟨1152455, by rfl⟩ : syracuseStep 1536607 = 2304911) B2304911
theorem B2159225 : Blo 1437538 2159225 := bstep (se 2 (by rfl) ⟨809709, by rfl⟩ : syracuseStep 2159225 = 1619419) B1619419
theorem B3281579 : Blo 1437538 3281579 := bstep (se 1 (by rfl) ⟨2461184, by rfl⟩ : syracuseStep 3281579 = 4922369) B4922369
theorem B2159279 : Blo 1437538 2159279 := bstep (se 1 (by rfl) ⟨1619459, by rfl⟩ : syracuseStep 2159279 = 3238919) B3238919
theorem B7279307 : Blo 1437538 7279307 := bstep (se 1 (by rfl) ⟨5459480, by rfl⟩ : syracuseStep 7279307 = 10918961) B10918961
theorem B1438431 : Blo 1437538 1438431 := bstep (se 1 (by rfl) ⟨1078823, by rfl⟩ : syracuseStep 1438431 = 2157647) B2157647
theorem B1438511 : Blo 1437538 1438511 := bstep (se 1 (by rfl) ⟨1078883, by rfl⟩ : syracuseStep 1438511 = 2157767) B2157767
theorem B1618735 : Blo 1437538 1618735 := bstep (se 1 (by rfl) ⟨1214051, by rfl⟩ : syracuseStep 1618735 = 2428103) B2428103
theorem B13824847 : Blo 1437538 13824847 := bstep (se 1 (by rfl) ⟨10368635, by rfl⟩ : syracuseStep 13824847 = 20737271) B20737271
theorem B7279469 : Blo 1437538 7279469 := bstep (se 3 (by rfl) ⟨1364900, by rfl⟩ : syracuseStep 7279469 = 2729801) B2729801
theorem B1438619 : Blo 1437538 1438619 := bstep (se 1 (by rfl) ⟨1078964, by rfl⟩ : syracuseStep 1438619 = 2157929) B2157929
theorem B1618843 : Blo 1437538 1618843 := bstep (se 1 (by rfl) ⟨1214132, by rfl⟩ : syracuseStep 1618843 = 2428265) B2428265
theorem B10367945 : Blo 1437538 10367945 := bstep (se 2 (by rfl) ⟨3887979, by rfl⟩ : syracuseStep 10367945 = 7775959) B7775959
theorem B1438671 : Blo 1437538 1438671 := bstep (se 1 (by rfl) ⟨1079003, by rfl⟩ : syracuseStep 1438671 = 2158007) B2158007
theorem B1438695 : Blo 1437538 1438695 := bstep (se 1 (by rfl) ⟨1079021, by rfl⟩ : syracuseStep 1438695 = 2158043) B2158043
theorem B8303705 : Blo 1437538 8303705 := bstep (se 2 (by rfl) ⟨3113889, by rfl⟩ : syracuseStep 8303705 = 6227779) B6227779
theorem B6313085 : Blo 1437538 6313085 := bstep (se 3 (by rfl) ⟨1183703, by rfl⟩ : syracuseStep 6313085 = 2367407) B2367407
theorem B23663789 : Blo 1437538 23663789 := bstep (se 3 (by rfl) ⟨4436960, by rfl⟩ : syracuseStep 23663789 = 8873921) B8873921
theorem B4920563 : Blo 1437538 4920563 := bstep (se 1 (by rfl) ⟨3690422, by rfl⟩ : syracuseStep 4920563 = 7380845) B7380845
theorem B12293369 : Blo 1437538 12293369 := bstep (se 2 (by rfl) ⟨4610013, by rfl⟩ : syracuseStep 12293369 = 9220027) B9220027
theorem B1439007 : Blo 1437538 1439007 := bstep (se 1 (by rfl) ⟨1079255, by rfl⟩ : syracuseStep 1439007 = 2158511) B2158511
theorem B1619239 : Blo 1437538 1619239 := bstep (se 1 (by rfl) ⟨1214429, by rfl⟩ : syracuseStep 1619239 = 2428859) B2428859
theorem B1439067 : Blo 1437538 1439067 := bstep (se 1 (by rfl) ⟨1079300, by rfl⟩ : syracuseStep 1439067 = 2158601) B2158601
theorem B1439087 : Blo 1437538 1439087 := bstep (se 1 (by rfl) ⟨1079315, by rfl⟩ : syracuseStep 1439087 = 2158631) B2158631
theorem B1619311 : Blo 1437538 1619311 := bstep (se 1 (by rfl) ⟨1214483, by rfl⟩ : syracuseStep 1619311 = 2428967) B2428967
theorem B4150651 : Blo 1437538 4150651 := bstep (se 1 (by rfl) ⟨3112988, by rfl⟩ : syracuseStep 4150651 = 6225977) B6225977
theorem B1439143 : Blo 1437538 1439143 := bstep (se 1 (by rfl) ⟨1079357, by rfl⟩ : syracuseStep 1439143 = 2158715) B2158715
theorem B1439227 : Blo 1437538 1439227 := bstep (se 1 (by rfl) ⟨1079420, by rfl⟩ : syracuseStep 1439227 = 2158841) B2158841
theorem B56841749 : Blo 1437538 56841749 := bstep (se 6 (by rfl) ⟨1332228, by rfl⟩ : syracuseStep 56841749 = 2664457) B2664457
theorem B13833767 : Blo 1437538 13833767 := bstep (se 1 (by rfl) ⟨10375325, by rfl⟩ : syracuseStep 13833767 = 20750651) B20750651
theorem B1439295 : Blo 1437538 1439295 := bstep (se 1 (by rfl) ⟨1079471, by rfl⟩ : syracuseStep 1439295 = 2158943) B2158943
theorem B1439303 : Blo 1437538 1439303 := bstep (se 1 (by rfl) ⟨1079477, by rfl⟩ : syracuseStep 1439303 = 2158955) B2158955
theorem B6141575 : Blo 1437538 6141575 := bstep (se 1 (by rfl) ⟨4606181, by rfl⟩ : syracuseStep 6141575 = 9212363) B9212363
theorem B1439455 : Blo 1437538 1439455 := bstep (se 1 (by rfl) ⟨1079591, by rfl⟩ : syracuseStep 1439455 = 2159183) B2159183
theorem B3643177 : Blo 1437538 3643177 := bstep (se 2 (by rfl) ⟨1366191, by rfl⟩ : syracuseStep 3643177 = 2732383) B2732383
theorem B1439535 : Blo 1437538 1439535 := bstep (se 1 (by rfl) ⟨1079651, by rfl⟩ : syracuseStep 1439535 = 2159303) B2159303
theorem B4609847 : Blo 1437538 4609847 := bstep (se 1 (by rfl) ⟨3457385, by rfl⟩ : syracuseStep 4609847 = 6914771) B6914771
theorem B5830481 : Blo 1437538 5830481 := bstep (se 2 (by rfl) ⟨2186430, by rfl⟩ : syracuseStep 5830481 = 4372861) B4372861
theorem B4855841 : Blo 1437538 4855841 := bstep (se 2 (by rfl) ⟨1820940, by rfl⟩ : syracuseStep 4855841 = 3641881) B3641881
theorem B16382087 : Blo 1437538 16382087 := bstep (se 1 (by rfl) ⟨12286565, by rfl⟩ : syracuseStep 16382087 = 24573131) B24573131
theorem B4610333 : Blo 1437538 4610333 := bstep (se 3 (by rfl) ⟨864437, by rfl⟩ : syracuseStep 4610333 = 1728875) B1728875
theorem B3455443 : Blo 1437538 3455443 := bstep (se 1 (by rfl) ⟨2591582, by rfl⟩ : syracuseStep 3455443 = 5183165) B5183165
theorem B4094543 : Blo 1437538 4094543 := bstep (se 1 (by rfl) ⟨3070907, by rfl⟩ : syracuseStep 4094543 = 6141815) B6141815
theorem B13826693 : Blo 1437538 13826693 := bstep (se 4 (by rfl) ⟨1296252, by rfl⟩ : syracuseStep 13826693 = 2592505) B2592505
theorem B35011273 : Blo 1437538 35011273 := bstep (se 2 (by rfl) ⟨13129227, by rfl⟩ : syracuseStep 35011273 = 26258455) B26258455
theorem B3234527 : Blo 1437538 3234527 := bstep (se 1 (by rfl) ⟨2425895, by rfl⟩ : syracuseStep 3234527 = 4851791) B4851791
theorem B3234779 : Blo 1437538 3234779 := bstep (se 1 (by rfl) ⟨2426084, by rfl⟩ : syracuseStep 3234779 = 4852169) B4852169
theorem B6913039 : Blo 1437538 6913039 := bstep (se 1 (by rfl) ⟨5184779, by rfl⟩ : syracuseStep 6913039 = 10369559) B10369559
theorem B11074589 : Blo 1437538 11074589 := bstep (se 3 (by rfl) ⟨2076485, by rfl⟩ : syracuseStep 11074589 = 4152971) B4152971
theorem B3890315 : Blo 1437538 3890315 := bstep (se 1 (by rfl) ⟨2917736, by rfl⟩ : syracuseStep 3890315 = 5835473) B5835473
theorem B3234959 : Blo 1437538 3234959 := bstep (se 1 (by rfl) ⟨2426219, by rfl⟩ : syracuseStep 3234959 = 4852439) B4852439
theorem B13130981 : Blo 1437538 13130981 := bstep (se 4 (by rfl) ⟨1231029, by rfl⟩ : syracuseStep 13130981 = 2462059) B2462059
theorem B3235049 : Blo 1437538 3235049 := bstep (se 2 (by rfl) ⟨1213143, by rfl⟩ : syracuseStep 3235049 = 2426287) B2426287
theorem B3235103 : Blo 1437538 3235103 := bstep (se 1 (by rfl) ⟨2426327, by rfl⟩ : syracuseStep 3235103 = 4852655) B4852655
theorem B6397321 : Blo 1437538 6397321 := bstep (se 2 (by rfl) ⟨2398995, by rfl⟩ : syracuseStep 6397321 = 4797991) B4797991
theorem B4095431 : Blo 1437538 4095431 := bstep (se 1 (by rfl) ⟨3071573, by rfl⟩ : syracuseStep 4095431 = 6143147) B6143147
theorem B14015959 : Blo 1437538 14015959 := bstep (se 1 (by rfl) ⟨10511969, by rfl⟩ : syracuseStep 14015959 = 21023939) B21023939
theorem B10919447 : Blo 1437538 10919447 := bstep (se 1 (by rfl) ⟨8189585, by rfl⟩ : syracuseStep 10919447 = 16379171) B16379171
theorem B26590837 : Blo 1437538 26590837 := bstep (se 5 (by rfl) ⟨1246445, by rfl⟩ : syracuseStep 26590837 = 2492891) B2492891
theorem B7282385 : Blo 1437538 7282385 := bstep (se 2 (by rfl) ⟨2730894, by rfl⟩ : syracuseStep 7282385 = 5461789) B5461789
theorem B3235625 : Blo 1437538 3235625 := bstep (se 2 (by rfl) ⟨1213359, by rfl⟩ : syracuseStep 3235625 = 2426719) B2426719
theorem B4095785 : Blo 1437538 4095785 := bstep (se 2 (by rfl) ⟨1535919, by rfl⟩ : syracuseStep 4095785 = 3071839) B3071839
theorem B8101927 : Blo 1437538 8101927 := bstep (se 1 (by rfl) ⟨6076445, by rfl⟩ : syracuseStep 8101927 = 12152891) B12152891
theorem B2187719 : Blo 1437538 2187719 := bstep (se 1 (by rfl) ⟨1640789, by rfl⟩ : syracuseStep 2187719 = 3281579) B3281579
theorem B10371635 : Blo 1437538 10371635 := bstep (se 1 (by rfl) ⟨7778726, by rfl⟩ : syracuseStep 10371635 = 15557453) B15557453
theorem B2048809 : Blo 1437538 2048809 := bstep (se 2 (by rfl) ⟨768303, by rfl⟩ : syracuseStep 2048809 = 1536607) B1536607
theorem B18433129 : Blo 1437538 18433129 := bstep (se 2 (by rfl) ⟨6912423, by rfl⟩ : syracuseStep 18433129 = 13824847) B13824847
theorem B2425963 : Blo 1437538 2425963 := bstep (se 1 (by rfl) ⟨1819472, by rfl⟩ : syracuseStep 2425963 = 3638945) B3638945
theorem B3073231 : Blo 1437538 3073231 := bstep (se 1 (by rfl) ⟨2304923, by rfl⟩ : syracuseStep 3073231 = 4609847) B4609847
theorem B9217385 : Blo 1437538 9217385 := bstep (se 2 (by rfl) ⟨3456519, by rfl⟩ : syracuseStep 9217385 = 6913039) B6913039
theorem B3237227 : Blo 1437538 3237227 := bstep (se 1 (by rfl) ⟨2427920, by rfl⟩ : syracuseStep 3237227 = 4855841) B4855841
theorem B2426267 : Blo 1437538 2426267 := bstep (se 1 (by rfl) ⟨1819700, by rfl⟩ : syracuseStep 2426267 = 3639401) B3639401
theorem B10921391 : Blo 1437538 10921391 := bstep (se 1 (by rfl) ⟨8191043, by rfl⟩ : syracuseStep 10921391 = 16382087) B16382087
theorem B3638803 : Blo 1437538 3638803 := bstep (se 1 (by rfl) ⟨2729102, by rfl⟩ : syracuseStep 3638803 = 5458205) B5458205
theorem B3073555 : Blo 1437538 3073555 := bstep (se 1 (by rfl) ⟨2305166, by rfl⟩ : syracuseStep 3073555 = 4610333) B4610333
theorem B3237497 : Blo 1437538 3237497 := bstep (se 2 (by rfl) ⟨1214061, by rfl⟩ : syracuseStep 3237497 = 2428123) B2428123
theorem B2729695 : Blo 1437538 2729695 := bstep (se 1 (by rfl) ⟨2047271, by rfl⟩ : syracuseStep 2729695 = 4094543) B4094543
theorem B2426591 : Blo 1437538 2426591 := bstep (se 1 (by rfl) ⟨1819943, by rfl⟩ : syracuseStep 2426591 = 3639887) B3639887
theorem B9217795 : Blo 1437538 9217795 := bstep (se 1 (by rfl) ⟨6913346, by rfl⟩ : syracuseStep 9217795 = 13826693) B13826693
theorem B2156351 : Blo 1437538 2156351 := bstep (se 1 (by rfl) ⟨1617263, by rfl⟩ : syracuseStep 2156351 = 3234527) B3234527
theorem B8529761 : Blo 1437538 8529761 := bstep (se 2 (by rfl) ⟨3198660, by rfl⟩ : syracuseStep 8529761 = 6397321) B6397321
theorem B3073889 : Blo 1437538 3073889 := bstep (se 2 (by rfl) ⟨1152708, by rfl⟩ : syracuseStep 3073889 = 2305417) B2305417
theorem B3639239 : Blo 1437538 3639239 := bstep (se 1 (by rfl) ⟨2729429, by rfl⟩ : syracuseStep 3639239 = 5458859) B5458859
theorem B2156519 : Blo 1437538 2156519 := bstep (se 1 (by rfl) ⟨1617389, by rfl⟩ : syracuseStep 2156519 = 3234779) B3234779
theorem B2156537 : Blo 1437538 2156537 := bstep (se 2 (by rfl) ⟨808701, by rfl⟩ : syracuseStep 2156537 = 1617403) B1617403
theorem B7383059 : Blo 1437538 7383059 := bstep (se 1 (by rfl) ⟨5537294, by rfl⟩ : syracuseStep 7383059 = 11074589) B11074589
theorem B2156639 : Blo 1437538 2156639 := bstep (se 1 (by rfl) ⟨1617479, by rfl⟩ : syracuseStep 2156639 = 3234959) B3234959
theorem B2427023 : Blo 1437538 2427023 := bstep (se 1 (by rfl) ⟨1820267, by rfl⟩ : syracuseStep 2427023 = 3640535) B3640535
theorem B2156699 : Blo 1437538 2156699 := bstep (se 1 (by rfl) ⟨1617524, by rfl⟩ : syracuseStep 2156699 = 3235049) B3235049
theorem B2156735 : Blo 1437538 2156735 := bstep (se 1 (by rfl) ⟨1617551, by rfl⟩ : syracuseStep 2156735 = 3235103) B3235103
theorem B2156777 : Blo 1437538 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B4852007 : Blo 1437538 4852007 := bstep (se 1 (by rfl) ⟨3639005, by rfl⟩ : syracuseStep 4852007 = 7278011) B7278011
theorem B2730287 : Blo 1437538 2730287 := bstep (se 1 (by rfl) ⟨2047715, by rfl⟩ : syracuseStep 2730287 = 4095431) B4095431
theorem B2427259 : Blo 1437538 2427259 := bstep (se 1 (by rfl) ⟨1820444, by rfl⟩ : syracuseStep 2427259 = 3640889) B3640889
theorem B4098529 : Blo 1437538 4098529 := bstep (se 2 (by rfl) ⟨1536948, by rfl⟩ : syracuseStep 4098529 = 3073897) B3073897
theorem B2157083 : Blo 1437538 2157083 := bstep (se 1 (by rfl) ⟨1617812, by rfl⟩ : syracuseStep 2157083 = 3235625) B3235625
theorem B2730523 : Blo 1437538 2730523 := bstep (se 1 (by rfl) ⟨2047892, by rfl⟩ : syracuseStep 2730523 = 4095785) B4095785
theorem B2157161 : Blo 1437538 2157161 := bstep (se 2 (by rfl) ⟨808935, by rfl⟩ : syracuseStep 2157161 = 1617871) B1617871
theorem B3238505 : Blo 1437538 3238505 := bstep (se 2 (by rfl) ⟨1214439, by rfl⟩ : syracuseStep 3238505 = 2428879) B2428879
theorem B2427529 : Blo 1437538 2427529 := bstep (se 2 (by rfl) ⟨910323, by rfl⟩ : syracuseStep 2427529 = 1820647) B1820647
theorem B20728507 : Blo 1437538 20728507 := bstep (se 1 (by rfl) ⟨15546380, by rfl⟩ : syracuseStep 20728507 = 31092761) B31092761
theorem B63073079 : Blo 1437538 63073079 := bstep (se 1 (by rfl) ⟨47304809, by rfl⟩ : syracuseStep 63073079 = 94609619) B94609619
theorem B2304859 : Blo 1437538 2304859 := bstep (se 1 (by rfl) ⟨1728644, by rfl⟩ : syracuseStep 2304859 = 3457289) B3457289
theorem B9841667 : Blo 1437538 9841667 := bstep (se 1 (by rfl) ⟨7381250, by rfl⟩ : syracuseStep 9841667 = 14762501) B14762501
theorem B20737043 : Blo 1437538 20737043 := bstep (se 1 (by rfl) ⟨15552782, by rfl⟩ : syracuseStep 20737043 = 31105565) B31105565
theorem B2591785 : Blo 1437538 2591785 := bstep (se 2 (by rfl) ⟨971919, by rfl⟩ : syracuseStep 2591785 = 1943839) B1943839
theorem B2157689 : Blo 1437538 2157689 := bstep (se 2 (by rfl) ⟨809133, by rfl⟩ : syracuseStep 2157689 = 1618267) B1618267
theorem B4852871 : Blo 1437538 4852871 := bstep (se 1 (by rfl) ⟨3639653, by rfl⟩ : syracuseStep 4852871 = 7279307) B7279307
theorem B2157791 : Blo 1437538 2157791 := bstep (se 1 (by rfl) ⟨1618343, by rfl⟩ : syracuseStep 2157791 = 3236687) B3236687
theorem B4852979 : Blo 1437538 4852979 := bstep (se 1 (by rfl) ⟨3639734, by rfl⟩ : syracuseStep 4852979 = 7279469) B7279469
theorem B2157833 : Blo 1437538 2157833 := bstep (se 2 (by rfl) ⟨809187, by rfl⟩ : syracuseStep 2157833 = 1618375) B1618375
theorem B7277849 : Blo 1437538 7277849 := bstep (se 2 (by rfl) ⟨2729193, by rfl⟩ : syracuseStep 7277849 = 5458387) B5458387
theorem B2157935 : Blo 1437538 2157935 := bstep (se 1 (by rfl) ⟨1618451, by rfl⟩ : syracuseStep 2157935 = 3236903) B3236903
theorem B118082933 : Blo 1437538 118082933 := bstep (se 5 (by rfl) ⟨5535137, by rfl⟩ : syracuseStep 118082933 = 11070275) B11070275
theorem B42036661 : Blo 1437538 42036661 := bstep (se 5 (by rfl) ⟨1970468, by rfl⟩ : syracuseStep 42036661 = 3940937) B3940937
theorem B2158055 : Blo 1437538 2158055 := bstep (se 1 (by rfl) ⟨1618541, by rfl⟩ : syracuseStep 2158055 = 3237083) B3237083
theorem B3280375 : Blo 1437538 3280375 := bstep (se 1 (by rfl) ⟨2460281, by rfl⟩ : syracuseStep 3280375 = 4920563) B4920563
theorem B8195579 : Blo 1437538 8195579 := bstep (se 1 (by rfl) ⟨6146684, by rfl⟩ : syracuseStep 8195579 = 12293369) B12293369
theorem B46681697 : Blo 1437538 46681697 := bstep (se 2 (by rfl) ⟨17505636, by rfl⟩ : syracuseStep 46681697 = 35011273) B35011273
theorem B2158187 : Blo 1437538 2158187 := bstep (se 1 (by rfl) ⟨1618640, by rfl⟩ : syracuseStep 2158187 = 3237281) B3237281
theorem B2305679 : Blo 1437538 2305679 := bstep (se 1 (by rfl) ⟨1729259, by rfl⟩ : syracuseStep 2305679 = 3458519) B3458519
theorem B2158313 : Blo 1437538 2158313 := bstep (se 2 (by rfl) ⟨809367, by rfl⟩ : syracuseStep 2158313 = 1618735) B1618735
theorem B5836625 : Blo 1437538 5836625 := bstep (se 2 (by rfl) ⟨2188734, by rfl⟩ : syracuseStep 5836625 = 4377469) B4377469
theorem B2158457 : Blo 1437538 2158457 := bstep (se 2 (by rfl) ⟨809421, by rfl⟩ : syracuseStep 2158457 = 1618843) B1618843
theorem B2731897 : Blo 1437538 2731897 := bstep (se 2 (by rfl) ⟨1024461, by rfl⟩ : syracuseStep 2731897 = 2048923) B2048923
theorem B3886987 : Blo 1437538 3886987 := bstep (se 1 (by rfl) ⟨2915240, by rfl⟩ : syracuseStep 3886987 = 5830481) B5830481
theorem B1437663 : Blo 1437538 1437663 := bstep (se 1 (by rfl) ⟨1078247, by rfl⟩ : syracuseStep 1437663 = 2156495) B2156495
theorem B2158559 : Blo 1437538 2158559 := bstep (se 1 (by rfl) ⟨1618919, by rfl⟩ : syracuseStep 2158559 = 3237839) B3237839
theorem B2158811 : Blo 1437538 2158811 := bstep (se 1 (by rfl) ⟨1619108, by rfl⟩ : syracuseStep 2158811 = 3238217) B3238217
theorem B1437927 : Blo 1437538 1437927 := bstep (se 1 (by rfl) ⟨1078445, by rfl⟩ : syracuseStep 1437927 = 2156891) B2156891
theorem B2158823 : Blo 1437538 2158823 := bstep (se 1 (by rfl) ⟨1619117, by rfl⟩ : syracuseStep 2158823 = 3238235) B3238235
theorem B5181725 : Blo 1437538 5181725 := bstep (se 3 (by rfl) ⟨971573, by rfl⟩ : syracuseStep 5181725 = 1943147) B1943147
theorem B2076959 : Blo 1437538 2076959 := bstep (se 1 (by rfl) ⟨1557719, by rfl⟩ : syracuseStep 2076959 = 3115439) B3115439
theorem B1438079 : Blo 1437538 1438079 := bstep (se 1 (by rfl) ⟨1078559, by rfl⟩ : syracuseStep 1438079 = 2157119) B2157119
theorem B1618303 : Blo 1437538 1618303 := bstep (se 1 (by rfl) ⟨1213727, by rfl⟩ : syracuseStep 1618303 = 2427455) B2427455
theorem B2158985 : Blo 1437538 2158985 := bstep (se 2 (by rfl) ⟨809619, by rfl⟩ : syracuseStep 2158985 = 1619239) B1619239
theorem B1438159 : Blo 1437538 1438159 := bstep (se 1 (by rfl) ⟨1078619, by rfl⟩ : syracuseStep 1438159 = 2157239) B2157239
theorem B2159081 : Blo 1437538 2159081 := bstep (se 2 (by rfl) ⟨809655, by rfl⟩ : syracuseStep 2159081 = 1619311) B1619311
theorem B5534201 : Blo 1437538 5534201 := bstep (se 2 (by rfl) ⟨2075325, by rfl⟩ : syracuseStep 5534201 = 4150651) B4150651
theorem B41448023 : Blo 1437538 41448023 := bstep (se 1 (by rfl) ⟨31086017, by rfl⟩ : syracuseStep 41448023 = 62172035) B62172035
theorem B1438311 : Blo 1437538 1438311 := bstep (se 1 (by rfl) ⟨1078733, by rfl⟩ : syracuseStep 1438311 = 2157467) B2157467
theorem B2159207 : Blo 1437538 2159207 := bstep (se 1 (by rfl) ⟨1619405, by rfl⟩ : syracuseStep 2159207 = 3238811) B3238811
theorem B21025469 : Blo 1437538 21025469 := bstep (se 3 (by rfl) ⟨3942275, by rfl⟩ : syracuseStep 21025469 = 7884551) B7884551
theorem B31552229 : Blo 1437538 31552229 := bstep (se 4 (by rfl) ⟨2958021, by rfl⟩ : syracuseStep 31552229 = 5916043) B5916043
theorem B9220871 : Blo 1437538 9220871 := bstep (se 1 (by rfl) ⟨6915653, by rfl⟩ : syracuseStep 9220871 = 13831307) B13831307
theorem B2593543 : Blo 1437538 2593543 := bstep (se 1 (by rfl) ⟨1945157, by rfl⟩ : syracuseStep 2593543 = 3890315) B3890315
theorem B8753987 : Blo 1437538 8753987 := bstep (se 1 (by rfl) ⟨6565490, by rfl⟩ : syracuseStep 8753987 = 13130981) B13130981
theorem B1438575 : Blo 1437538 1438575 := bstep (se 1 (by rfl) ⟨1078931, by rfl⟩ : syracuseStep 1438575 = 2157863) B2157863
theorem B4854653 : Blo 1437538 4854653 := bstep (se 3 (by rfl) ⟨910247, by rfl⟩ : syracuseStep 4854653 = 1820495) B1820495
theorem B1438631 : Blo 1437538 1438631 := bstep (se 1 (by rfl) ⟨1078973, by rfl⟩ : syracuseStep 1438631 = 2157947) B2157947
theorem B1438715 : Blo 1437538 1438715 := bstep (se 1 (by rfl) ⟨1079036, by rfl⟩ : syracuseStep 1438715 = 2158073) B2158073
theorem B7279631 : Blo 1437538 7279631 := bstep (se 1 (by rfl) ⟨5459723, by rfl⟩ : syracuseStep 7279631 = 10919447) B10919447
theorem B1438783 : Blo 1437538 1438783 := bstep (se 1 (by rfl) ⟨1079087, by rfl⟩ : syracuseStep 1438783 = 2158175) B2158175
theorem B18429029 : Blo 1437538 18429029 := bstep (se 4 (by rfl) ⟨1727721, by rfl⟩ : syracuseStep 18429029 = 3455443) B3455443
theorem B11662451 : Blo 1437538 11662451 := bstep (se 1 (by rfl) ⟨8746838, by rfl⟩ : syracuseStep 11662451 = 17493677) B17493677
theorem B4854923 : Blo 1437538 4854923 := bstep (se 1 (by rfl) ⟨3641192, by rfl⟩ : syracuseStep 4854923 = 7282385) B7282385
theorem B1438927 : Blo 1437538 1438927 := bstep (se 1 (by rfl) ⟨1079195, by rfl⟩ : syracuseStep 1438927 = 2158391) B2158391
theorem B16602457 : Blo 1437538 16602457 := bstep (se 2 (by rfl) ⟨6225921, by rfl⟩ : syracuseStep 16602457 = 12451843) B12451843
theorem B4609399 : Blo 1437538 4609399 := bstep (se 1 (by rfl) ⟨3457049, by rfl⟩ : syracuseStep 4609399 = 6914099) B6914099
theorem B1439131 : Blo 1437538 1439131 := bstep (se 1 (by rfl) ⟨1079348, by rfl⟩ : syracuseStep 1439131 = 2158697) B2158697
theorem B15554081 : Blo 1437538 15554081 := bstep (se 2 (by rfl) ⟨5832780, by rfl⟩ : syracuseStep 15554081 = 11665561) B11665561
theorem B1439343 : Blo 1437538 1439343 := bstep (se 1 (by rfl) ⟨1079507, by rfl⟩ : syracuseStep 1439343 = 2159015) B2159015
theorem B1439399 : Blo 1437538 1439399 := bstep (se 1 (by rfl) ⟨1079549, by rfl⟩ : syracuseStep 1439399 = 2159099) B2159099
theorem B7386833 : Blo 1437538 7386833 := bstep (se 2 (by rfl) ⟨2770062, by rfl⟩ : syracuseStep 7386833 = 5540125) B5540125
theorem B1439483 : Blo 1437538 1439483 := bstep (se 1 (by rfl) ⟨1079612, by rfl⟩ : syracuseStep 1439483 = 2159225) B2159225
theorem B1439519 : Blo 1437538 1439519 := bstep (se 1 (by rfl) ⟨1079639, by rfl⟩ : syracuseStep 1439519 = 2159279) B2159279
theorem B7280441 : Blo 1437538 7280441 := bstep (se 2 (by rfl) ⟨2730165, by rfl⟩ : syracuseStep 7280441 = 5460331) B5460331
theorem B6911963 : Blo 1437538 6911963 := bstep (se 1 (by rfl) ⟨5183972, by rfl⟩ : syracuseStep 6911963 = 10367945) B10367945
theorem B5183513 : Blo 1437538 5183513 := bstep (se 2 (by rfl) ⟨1943817, by rfl⟩ : syracuseStep 5183513 = 3887635) B3887635
theorem B5535803 : Blo 1437538 5535803 := bstep (se 1 (by rfl) ⟨4151852, by rfl⟩ : syracuseStep 5535803 = 8303705) B8303705
theorem B4208723 : Blo 1437538 4208723 := bstep (se 1 (by rfl) ⟨3156542, by rfl⟩ : syracuseStep 4208723 = 6313085) B6313085
theorem B3889235 : Blo 1437538 3889235 := bstep (se 1 (by rfl) ⟨2916926, by rfl⟩ : syracuseStep 3889235 = 5833853) B5833853
theorem B3692639 : Blo 1437538 3692639 := bstep (se 1 (by rfl) ⟨2769479, by rfl⟩ : syracuseStep 3692639 = 5538959) B5538959
theorem B15775859 : Blo 1437538 15775859 := bstep (se 1 (by rfl) ⟨11831894, by rfl⟩ : syracuseStep 15775859 = 23663789) B23663789
theorem B209852765 : Blo 1437538 209852765 := bstep (se 3 (by rfl) ⟨39347393, by rfl⟩ : syracuseStep 209852765 = 78694787) B78694787
theorem B37894499 : Blo 1437538 37894499 := bstep (se 1 (by rfl) ⟨28420874, by rfl⟩ : syracuseStep 37894499 = 56841749) B56841749
theorem B9222511 : Blo 1437538 9222511 := bstep (se 1 (by rfl) ⟨6916883, by rfl⟩ : syracuseStep 9222511 = 13833767) B13833767
theorem B4094383 : Blo 1437538 4094383 := bstep (se 1 (by rfl) ⟨3070787, by rfl⟩ : syracuseStep 4094383 = 6141575) B6141575
theorem B4856543 : Blo 1437538 4856543 := bstep (se 1 (by rfl) ⟨3642407, by rfl⟩ : syracuseStep 4856543 = 7284815) B7284815
theorem B8305573 : Blo 1437538 8305573 := bstep (se 4 (by rfl) ⟨778647, by rfl⟩ : syracuseStep 8305573 = 1557295) B1557295
theorem B3234887 : Blo 1437538 3234887 := bstep (se 1 (by rfl) ⟨2426165, by rfl⟩ : syracuseStep 3234887 = 4852331) B4852331
theorem B3235283 : Blo 1437538 3235283 := bstep (se 1 (by rfl) ⟨2426462, by rfl⟩ : syracuseStep 3235283 = 4852925) B4852925
theorem B4857299 : Blo 1437538 4857299 := bstep (se 1 (by rfl) ⟨3642974, by rfl⟩ : syracuseStep 4857299 = 7285949) B7285949
theorem B35454449 : Blo 1437538 35454449 := bstep (se 2 (by rfl) ⟨13295418, by rfl⟩ : syracuseStep 35454449 = 26590837) B26590837
theorem B3235553 : Blo 1437538 3235553 := bstep (se 2 (by rfl) ⟨1213332, by rfl⟩ : syracuseStep 3235553 = 2426665) B2426665
theorem B4857569 : Blo 1437538 4857569 := bstep (se 2 (by rfl) ⟨1821588, by rfl⟩ : syracuseStep 4857569 = 3643177) B3643177
theorem B74751781 : Blo 1437538 74751781 := bstep (se 4 (by rfl) ⟨7007979, by rfl⟩ : syracuseStep 74751781 = 14015959) B14015959
theorem B16392293 : Blo 1437538 16392293 := bstep (se 4 (by rfl) ⟨1536777, by rfl⟩ : syracuseStep 16392293 = 3073555) B3073555
theorem B1458479 : Blo 1437538 1458479 := bstep (se 1 (by rfl) ⟨1093859, by rfl⟩ : syracuseStep 1458479 = 2187719) B2187719
theorem B6914423 : Blo 1437538 6914423 := bstep (se 1 (by rfl) ⟨5185817, by rfl⟩ : syracuseStep 6914423 = 10371635) B10371635
theorem B27632015 : Blo 1437538 27632015 := bstep (se 1 (by rfl) ⟨20724011, by rfl⟩ : syracuseStep 27632015 = 41448023) B41448023
theorem B14016979 : Blo 1437538 14016979 := bstep (se 1 (by rfl) ⟨10512734, by rfl⟩ : syracuseStep 14016979 = 21025469) B21025469
theorem B12296681 : Blo 1437538 12296681 := bstep (se 2 (by rfl) ⟨4611255, by rfl⟩ : syracuseStep 12296681 = 9222511) B9222511
theorem B3236345 : Blo 1437538 3236345 := bstep (se 2 (by rfl) ⟨1213629, by rfl⟩ : syracuseStep 3236345 = 2427259) B2427259
theorem B3236435 : Blo 1437538 3236435 := bstep (se 1 (by rfl) ⟨2427326, by rfl⟩ : syracuseStep 3236435 = 4854653) B4854653
theorem B5464705 : Blo 1437538 5464705 := bstep (se 2 (by rfl) ⟨2049264, by rfl⟩ : syracuseStep 5464705 = 4098529) B4098529
theorem B7774967 : Blo 1437538 7774967 := bstep (se 1 (by rfl) ⟨5831225, by rfl⟩ : syracuseStep 7774967 = 11662451) B11662451
theorem B5538557 : Blo 1437538 5538557 := bstep (se 3 (by rfl) ⟨1038479, by rfl⟩ : syracuseStep 5538557 = 2076959) B2076959
theorem B3236615 : Blo 1437538 3236615 := bstep (se 1 (by rfl) ⟨2427461, by rfl⟩ : syracuseStep 3236615 = 4854923) B4854923
theorem B3236705 : Blo 1437538 3236705 := bstep (se 2 (by rfl) ⟨1213764, by rfl⟩ : syracuseStep 3236705 = 2427529) B2427529
theorem B6144923 : Blo 1437538 6144923 := bstep (se 1 (by rfl) ⟨4608692, by rfl⟩ : syracuseStep 6144923 = 9217385) B9217385
theorem B3458057 : Blo 1437538 3458057 := bstep (se 2 (by rfl) ⟨1296771, by rfl⟩ : syracuseStep 3458057 = 2593543) B2593543
theorem B3073145 : Blo 1437538 3073145 := bstep (se 2 (by rfl) ⟨1152429, by rfl⟩ : syracuseStep 3073145 = 2304859) B2304859
theorem B5686507 : Blo 1437538 5686507 := bstep (se 1 (by rfl) ⟨4264880, by rfl⟩ : syracuseStep 5686507 = 8529761) B8529761
theorem B2426159 : Blo 1437538 2426159 := bstep (se 1 (by rfl) ⟨1819619, by rfl⟩ : syracuseStep 2426159 = 3639239) B3639239
theorem B24577505 : Blo 1437538 24577505 := bstep (se 2 (by rfl) ⟨9216564, by rfl⟩ : syracuseStep 24577505 = 18433129) B18433129
theorem B4097641 : Blo 1437538 4097641 := bstep (se 2 (by rfl) ⟨1536615, by rfl⟩ : syracuseStep 4097641 = 3073231) B3073231
theorem B22136609 : Blo 1437538 22136609 := bstep (se 2 (by rfl) ⟨8301228, by rfl⟩ : syracuseStep 22136609 = 16602457) B16602457
theorem B3237695 : Blo 1437538 3237695 := bstep (se 1 (by rfl) ⟨2428271, by rfl⟩ : syracuseStep 3237695 = 4856543) B4856543
theorem B6145865 : Blo 1437538 6145865 := bstep (se 2 (by rfl) ⟨2304699, by rfl⟩ : syracuseStep 6145865 = 4609399) B4609399
theorem B4851737 : Blo 1437538 4851737 := bstep (se 2 (by rfl) ⟨1819401, by rfl⟩ : syracuseStep 4851737 = 3638803) B3638803
theorem B2156591 : Blo 1437538 2156591 := bstep (se 1 (by rfl) ⟨1617443, by rfl⟩ : syracuseStep 2156591 = 3234887) B3234887
theorem B4851899 : Blo 1437538 4851899 := bstep (se 1 (by rfl) ⟨3638924, by rfl⟩ : syracuseStep 4851899 = 7277849) B7277849
theorem B3639593 : Blo 1437538 3639593 := bstep (se 2 (by rfl) ⟨1364847, by rfl⟩ : syracuseStep 3639593 = 2729695) B2729695
theorem B2156855 : Blo 1437538 2156855 := bstep (se 1 (by rfl) ⟨1617641, by rfl⟩ : syracuseStep 2156855 = 3235283) B3235283
theorem B3238199 : Blo 1437538 3238199 := bstep (se 1 (by rfl) ⟨2428649, by rfl⟩ : syracuseStep 3238199 = 4857299) B4857299
theorem B23636299 : Blo 1437538 23636299 := bstep (se 1 (by rfl) ⟨17727224, by rfl⟩ : syracuseStep 23636299 = 35454449) B35454449
theorem B12290393 : Blo 1437538 12290393 := bstep (se 2 (by rfl) ⟨4608897, by rfl⟩ : syracuseStep 12290393 = 9217795) B9217795
theorem B2157035 : Blo 1437538 2157035 := bstep (se 1 (by rfl) ⟨1617776, by rfl⟩ : syracuseStep 2157035 = 3235553) B3235553
theorem B3238379 : Blo 1437538 3238379 := bstep (se 1 (by rfl) ⟨2428784, by rfl⟩ : syracuseStep 3238379 = 4857569) B4857569
theorem B2157737 : Blo 1437538 2157737 := bstep (se 2 (by rfl) ⟨809151, by rfl⟩ : syracuseStep 2157737 = 1618303) B1618303
theorem B6147247 : Blo 1437538 6147247 := bstep (se 1 (by rfl) ⟨4610435, by rfl⟩ : syracuseStep 6147247 = 9220871) B9220871
theorem B5835991 : Blo 1437538 5835991 := bstep (se 1 (by rfl) ⟨4376993, by rfl⟩ : syracuseStep 5835991 = 8753987) B8753987
theorem B5459177 : Blo 1437538 5459177 := bstep (se 2 (by rfl) ⟨2047191, by rfl⟩ : syracuseStep 5459177 = 4094383) B4094383
theorem B4853087 : Blo 1437538 4853087 := bstep (se 1 (by rfl) ⟨3639815, by rfl⟩ : syracuseStep 4853087 = 7279631) B7279631
theorem B3640697 : Blo 1437538 3640697 := bstep (se 2 (by rfl) ⟨1365261, by rfl⟩ : syracuseStep 3640697 = 2730523) B2730523
theorem B2158151 : Blo 1437538 2158151 := bstep (se 1 (by rfl) ⟨1618613, by rfl⟩ : syracuseStep 2158151 = 3237227) B3237227
theorem B1617511 : Blo 1437538 1617511 := bstep (se 1 (by rfl) ⟨1213133, by rfl⟩ : syracuseStep 1617511 = 2426267) B2426267
theorem B2731745 : Blo 1437538 2731745 := bstep (se 2 (by rfl) ⟨1024404, by rfl⟩ : syracuseStep 2731745 = 2048809) B2048809
theorem B2158331 : Blo 1437538 2158331 := bstep (se 1 (by rfl) ⟨1618748, by rfl⟩ : syracuseStep 2158331 = 3237497) B3237497
theorem B1617727 : Blo 1437538 1617727 := bstep (se 1 (by rfl) ⟨1213295, by rfl⟩ : syracuseStep 1617727 = 2426591) B2426591
theorem B4853627 : Blo 1437538 4853627 := bstep (se 1 (by rfl) ⟨3640220, by rfl⟩ : syracuseStep 4853627 = 7280441) B7280441
theorem B1437567 : Blo 1437538 1437567 := bstep (se 1 (by rfl) ⟨1078175, by rfl⟩ : syracuseStep 1437567 = 2156351) B2156351
theorem B4607975 : Blo 1437538 4607975 := bstep (se 1 (by rfl) ⟨3455981, by rfl⟩ : syracuseStep 4607975 = 6911963) B6911963
theorem B14757869 : Blo 1437538 14757869 := bstep (se 3 (by rfl) ⟨2767100, by rfl⟩ : syracuseStep 14757869 = 5534201) B5534201
theorem B1437679 : Blo 1437538 1437679 := bstep (se 1 (by rfl) ⟨1078259, by rfl⟩ : syracuseStep 1437679 = 2156519) B2156519
theorem B1437691 : Blo 1437538 1437691 := bstep (se 1 (by rfl) ⟨1078268, by rfl⟩ : syracuseStep 1437691 = 2156537) B2156537
theorem B3690535 : Blo 1437538 3690535 := bstep (se 1 (by rfl) ⟨2767901, by rfl⟩ : syracuseStep 3690535 = 5535803) B5535803
theorem B2805815 : Blo 1437538 2805815 := bstep (se 1 (by rfl) ⟨2104361, by rfl⟩ : syracuseStep 2805815 = 4208723) B4208723
theorem B2592823 : Blo 1437538 2592823 := bstep (se 1 (by rfl) ⟨1944617, by rfl⟩ : syracuseStep 2592823 = 3889235) B3889235
theorem B1437759 : Blo 1437538 1437759 := bstep (se 1 (by rfl) ⟨1078319, by rfl⟩ : syracuseStep 1437759 = 2156639) B2156639
theorem B2461759 : Blo 1437538 2461759 := bstep (se 1 (by rfl) ⟨1846319, by rfl⟩ : syracuseStep 2461759 = 3692639) B3692639
theorem B1618015 : Blo 1437538 1618015 := bstep (se 1 (by rfl) ⟨1213511, by rfl⟩ : syracuseStep 1618015 = 2427023) B2427023
theorem B1437799 : Blo 1437538 1437799 := bstep (se 1 (by rfl) ⟨1078349, by rfl⟩ : syracuseStep 1437799 = 2156699) B2156699
theorem B1437823 : Blo 1437538 1437823 := bstep (se 1 (by rfl) ⟨1078367, by rfl⟩ : syracuseStep 1437823 = 2156735) B2156735
theorem B1437851 : Blo 1437538 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B1438055 : Blo 1437538 1438055 := bstep (se 1 (by rfl) ⟨1078541, by rfl⟩ : syracuseStep 1438055 = 2157083) B2157083
theorem B6148477 : Blo 1437538 6148477 := bstep (se 3 (by rfl) ⟨1152839, by rfl⟩ : syracuseStep 6148477 = 2305679) B2305679
theorem B1438107 : Blo 1437538 1438107 := bstep (se 1 (by rfl) ⟨1078580, by rfl⟩ : syracuseStep 1438107 = 2157161) B2157161
theorem B2159003 : Blo 1437538 2159003 := bstep (se 1 (by rfl) ⟨1619252, by rfl⟩ : syracuseStep 2159003 = 3238505) B3238505
theorem B19698221 : Blo 1437538 19698221 := bstep (se 3 (by rfl) ⟨3693416, by rfl⟩ : syracuseStep 19698221 = 7386833) B7386833
theorem B13824695 : Blo 1437538 13824695 := bstep (se 1 (by rfl) ⟨10368521, by rfl⟩ : syracuseStep 13824695 = 20737043) B20737043
theorem B1438459 : Blo 1437538 1438459 := bstep (se 1 (by rfl) ⟨1078844, by rfl⟩ : syracuseStep 1438459 = 2157689) B2157689
theorem B1438527 : Blo 1437538 1438527 := bstep (se 1 (by rfl) ⟨1078895, by rfl⟩ : syracuseStep 1438527 = 2157791) B2157791
theorem B1438555 : Blo 1437538 1438555 := bstep (se 1 (by rfl) ⟨1078916, by rfl⟩ : syracuseStep 1438555 = 2157833) B2157833
theorem B1438623 : Blo 1437538 1438623 := bstep (se 1 (by rfl) ⟨1078967, by rfl⟩ : syracuseStep 1438623 = 2157935) B2157935
theorem B78721955 : Blo 1437538 78721955 := bstep (se 1 (by rfl) ⟨59041466, by rfl⟩ : syracuseStep 78721955 = 118082933) B118082933
theorem B8197037 : Blo 1437538 8197037 := bstep (se 3 (by rfl) ⟨1536944, by rfl⟩ : syracuseStep 8197037 = 3073889) B3073889
theorem B1438703 : Blo 1437538 1438703 := bstep (se 1 (by rfl) ⟨1079027, by rfl⟩ : syracuseStep 1438703 = 2158055) B2158055
theorem B99669041 : Blo 1437538 99669041 := bstep (se 2 (by rfl) ⟨37375890, by rfl⟩ : syracuseStep 99669041 = 74751781) B74751781
theorem B1438791 : Blo 1437538 1438791 := bstep (se 1 (by rfl) ⟨1079093, by rfl⟩ : syracuseStep 1438791 = 2158187) B2158187
theorem B1438875 : Blo 1437538 1438875 := bstep (se 1 (by rfl) ⟨1079156, by rfl⟩ : syracuseStep 1438875 = 2158313) B2158313
theorem B3642529 : Blo 1437538 3642529 := bstep (se 2 (by rfl) ⟨1365948, by rfl⟩ : syracuseStep 3642529 = 2731897) B2731897
theorem B5182649 : Blo 1437538 5182649 := bstep (se 2 (by rfl) ⟨1943493, by rfl⟩ : syracuseStep 5182649 = 3886987) B3886987
theorem B1438971 : Blo 1437538 1438971 := bstep (se 1 (by rfl) ⟨1079228, by rfl⟩ : syracuseStep 1438971 = 2158457) B2158457
theorem B1439039 : Blo 1437538 1439039 := bstep (se 1 (by rfl) ⟨1079279, by rfl⟩ : syracuseStep 1439039 = 2158559) B2158559
theorem B26244445 : Blo 1437538 26244445 := bstep (se 3 (by rfl) ⟨4920833, by rfl⟩ : syracuseStep 26244445 = 9841667) B9841667
theorem B10802569 : Blo 1437538 10802569 := bstep (se 2 (by rfl) ⟨4050963, by rfl⟩ : syracuseStep 10802569 = 8101927) B8101927
theorem B1439207 : Blo 1437538 1439207 := bstep (se 1 (by rfl) ⟨1079405, by rfl⟩ : syracuseStep 1439207 = 2158811) B2158811
theorem B1439215 : Blo 1437538 1439215 := bstep (se 1 (by rfl) ⟨1079411, by rfl⟩ : syracuseStep 1439215 = 2158823) B2158823
theorem B3454483 : Blo 1437538 3454483 := bstep (se 1 (by rfl) ⟨2590862, by rfl⟩ : syracuseStep 3454483 = 5181725) B5181725
theorem B1439323 : Blo 1437538 1439323 := bstep (se 1 (by rfl) ⟨1079492, by rfl⟩ : syracuseStep 1439323 = 2158985) B2158985
theorem B1439387 : Blo 1437538 1439387 := bstep (se 1 (by rfl) ⟨1079540, by rfl⟩ : syracuseStep 1439387 = 2159081) B2159081
theorem B1439471 : Blo 1437538 1439471 := bstep (se 1 (by rfl) ⟨1079603, by rfl⟩ : syracuseStep 1439471 = 2159207) B2159207
theorem B21034819 : Blo 1437538 21034819 := bstep (se 1 (by rfl) ⟨15776114, by rfl⟩ : syracuseStep 21034819 = 31552229) B31552229
theorem B12286019 : Blo 1437538 12286019 := bstep (se 1 (by rfl) ⟨9214514, by rfl⟩ : syracuseStep 12286019 = 18429029) B18429029
theorem B7280765 : Blo 1437538 7280765 := bstep (se 3 (by rfl) ⟨1365143, by rfl⟩ : syracuseStep 7280765 = 2730287) B2730287
theorem B27638009 : Blo 1437538 27638009 := bstep (se 2 (by rfl) ⟨10364253, by rfl⟩ : syracuseStep 27638009 = 20728507) B20728507
theorem B7280927 : Blo 1437538 7280927 := bstep (se 1 (by rfl) ⟨5460695, by rfl⟩ : syracuseStep 7280927 = 10921391) B10921391
theorem B10369387 : Blo 1437538 10369387 := bstep (se 1 (by rfl) ⟨7777040, by rfl⟩ : syracuseStep 10369387 = 15554081) B15554081
theorem B11074097 : Blo 1437538 11074097 := bstep (se 2 (by rfl) ⟨4152786, by rfl⟩ : syracuseStep 11074097 = 8305573) B8305573
theorem B4922039 : Blo 1437538 4922039 := bstep (se 1 (by rfl) ⟨3691529, by rfl⟩ : syracuseStep 4922039 = 7383059) B7383059
theorem B3455675 : Blo 1437538 3455675 := bstep (se 1 (by rfl) ⟨2591756, by rfl⟩ : syracuseStep 3455675 = 5183513) B5183513
theorem B3455713 : Blo 1437538 3455713 := bstep (se 2 (by rfl) ⟨1295892, by rfl⟩ : syracuseStep 3455713 = 2591785) B2591785
theorem B10517239 : Blo 1437538 10517239 := bstep (se 1 (by rfl) ⟨7887929, by rfl⟩ : syracuseStep 10517239 = 15775859) B15775859
theorem B3234617 : Blo 1437538 3234617 := bstep (se 2 (by rfl) ⟨1212981, by rfl⟩ : syracuseStep 3234617 = 2425963) B2425963
theorem B3234671 : Blo 1437538 3234671 := bstep (se 1 (by rfl) ⟨2426003, by rfl⟩ : syracuseStep 3234671 = 4852007) B4852007
theorem B139901843 : Blo 1437538 139901843 := bstep (se 1 (by rfl) ⟨104926382, by rfl⟩ : syracuseStep 139901843 = 209852765) B209852765
theorem B25262999 : Blo 1437538 25262999 := bstep (se 1 (by rfl) ⟨18947249, by rfl⟩ : syracuseStep 25262999 = 37894499) B37894499
theorem B42048719 : Blo 1437538 42048719 := bstep (se 1 (by rfl) ⟨31536539, by rfl⟩ : syracuseStep 42048719 = 63073079) B63073079
theorem B56048881 : Blo 1437538 56048881 := bstep (se 2 (by rfl) ⟨21018330, by rfl⟩ : syracuseStep 56048881 = 42036661) B42036661
theorem B4373833 : Blo 1437538 4373833 := bstep (se 2 (by rfl) ⟨1640187, by rfl⟩ : syracuseStep 4373833 = 3280375) B3280375
theorem B3235247 : Blo 1437538 3235247 := bstep (se 1 (by rfl) ⟨2426435, by rfl⟩ : syracuseStep 3235247 = 4852871) B4852871
theorem B3235319 : Blo 1437538 3235319 := bstep (se 1 (by rfl) ⟨2426489, by rfl⟩ : syracuseStep 3235319 = 4852979) B4852979
theorem B5463719 : Blo 1437538 5463719 := bstep (se 1 (by rfl) ⟨4097789, by rfl⟩ : syracuseStep 5463719 = 8195579) B8195579
theorem B31121131 : Blo 1437538 31121131 := bstep (se 1 (by rfl) ⟨23340848, by rfl⟩ : syracuseStep 31121131 = 46681697) B46681697
theorem B3891083 : Blo 1437538 3891083 := bstep (se 1 (by rfl) ⟨2918312, by rfl⟩ : syracuseStep 3891083 = 5836625) B5836625
theorem B10928195 : Blo 1437538 10928195 := bstep (se 1 (by rfl) ⟨8196146, by rfl⟩ : syracuseStep 10928195 = 16392293) B16392293
theorem B3457097 : Blo 1437538 3457097 := bstep (se 2 (by rfl) ⟨1296411, by rfl⟩ : syracuseStep 3457097 = 2592823) B2592823
theorem B13132147 : Blo 1437538 13132147 := bstep (se 1 (by rfl) ⟨9849110, by rfl⟩ : syracuseStep 13132147 = 19698221) B19698221
theorem B31515065 : Blo 1437538 31515065 := bstep (se 2 (by rfl) ⟨11818149, by rfl⟩ : syracuseStep 31515065 = 23636299) B23636299
theorem B9216463 : Blo 1437538 9216463 := bstep (se 1 (by rfl) ⟨6912347, by rfl⟩ : syracuseStep 9216463 = 13824695) B13824695
theorem B5464691 : Blo 1437538 5464691 := bstep (se 1 (by rfl) ⟨4098518, by rfl⟩ : syracuseStep 5464691 = 8197037) B8197037
theorem B66446027 : Blo 1437538 66446027 := bstep (se 1 (by rfl) ⟨49834520, by rfl⟩ : syracuseStep 66446027 = 99669041) B99669041
theorem B16385003 : Blo 1437538 16385003 := bstep (se 1 (by rfl) ⟨12288752, by rfl⟩ : syracuseStep 16385003 = 24577505) B24577505
theorem B4097243 : Blo 1437538 4097243 := bstep (se 1 (by rfl) ⟨3072932, by rfl⟩ : syracuseStep 4097243 = 6145865) B6145865
theorem B18425339 : Blo 1437538 18425339 := bstep (se 1 (by rfl) ⟨13819004, by rfl⟩ : syracuseStep 18425339 = 27638009) B27638009
theorem B2426395 : Blo 1437538 2426395 := bstep (se 1 (by rfl) ⟨1819796, by rfl⟩ : syracuseStep 2426395 = 3639593) B3639593
theorem B8193595 : Blo 1437538 8193595 := bstep (se 1 (by rfl) ⟨6145196, by rfl⟩ : syracuseStep 8193595 = 12290393) B12290393
theorem B2303783 : Blo 1437538 2303783 := bstep (se 1 (by rfl) ⟨1727837, by rfl⟩ : syracuseStep 2303783 = 3455675) B3455675
theorem B14403425 : Blo 1437538 14403425 := bstep (se 2 (by rfl) ⟨5401284, by rfl⟩ : syracuseStep 14403425 = 10802569) B10802569
theorem B2156411 : Blo 1437538 2156411 := bstep (se 1 (by rfl) ⟨1617308, by rfl⟩ : syracuseStep 2156411 = 3234617) B3234617
theorem B2156447 : Blo 1437538 2156447 := bstep (se 1 (by rfl) ⟨1617335, by rfl⟩ : syracuseStep 2156447 = 3234671) B3234671
theorem B7284653 : Blo 1437538 7284653 := bstep (se 3 (by rfl) ⟨1365872, by rfl⟩ : syracuseStep 7284653 = 2731745) B2731745
theorem B93267895 : Blo 1437538 93267895 := bstep (se 1 (by rfl) ⟨69950921, by rfl⟩ : syracuseStep 93267895 = 139901843) B139901843
theorem B4605977 : Blo 1437538 4605977 := bstep (se 2 (by rfl) ⟨1727241, by rfl⟩ : syracuseStep 4605977 = 3454483) B3454483
theorem B2156681 : Blo 1437538 2156681 := bstep (se 2 (by rfl) ⟨808755, by rfl⟩ : syracuseStep 2156681 = 1617511) B1617511
theorem B3639451 : Blo 1437538 3639451 := bstep (se 1 (by rfl) ⟨2729588, by rfl⟩ : syracuseStep 3639451 = 5459177) B5459177
theorem B2427131 : Blo 1437538 2427131 := bstep (se 1 (by rfl) ⟨1820348, by rfl⟩ : syracuseStep 2427131 = 3640697) B3640697
theorem B2156831 : Blo 1437538 2156831 := bstep (se 1 (by rfl) ⟨1617623, by rfl⟩ : syracuseStep 2156831 = 3235247) B3235247
theorem B41494841 : Blo 1437538 41494841 := bstep (se 2 (by rfl) ⟨15560565, by rfl⟩ : syracuseStep 41494841 = 31121131) B31121131
theorem B2156879 : Blo 1437538 2156879 := bstep (se 1 (by rfl) ⟨1617659, by rfl⟩ : syracuseStep 2156879 = 3235319) B3235319
theorem B16386461 : Blo 1437538 16386461 := bstep (se 3 (by rfl) ⟨3072461, by rfl⟩ : syracuseStep 16386461 = 6144923) B6144923
theorem B2156969 : Blo 1437538 2156969 := bstep (se 2 (by rfl) ⟨808863, by rfl⟩ : syracuseStep 2156969 = 1617727) B1617727
theorem B1870543 : Blo 1437538 1870543 := bstep (se 1 (by rfl) ⟨1402907, by rfl⟩ : syracuseStep 1870543 = 2805815) B2805815
theorem B2157353 : Blo 1437538 2157353 := bstep (se 2 (by rfl) ⟨809007, by rfl⟩ : syracuseStep 2157353 = 1618015) B1618015
theorem B8195053 : Blo 1437538 8195053 := bstep (se 3 (by rfl) ⟨1536572, by rfl⟩ : syracuseStep 8195053 = 3073145) B3073145
theorem B2157563 : Blo 1437538 2157563 := bstep (se 1 (by rfl) ⟨1618172, by rfl⟩ : syracuseStep 2157563 = 3236345) B3236345
theorem B2157623 : Blo 1437538 2157623 := bstep (se 1 (by rfl) ⟨1618217, by rfl⟩ : syracuseStep 2157623 = 3236435) B3236435
theorem B2157743 : Blo 1437538 2157743 := bstep (se 1 (by rfl) ⟨1618307, by rfl⟩ : syracuseStep 2157743 = 3236615) B3236615
theorem B2157803 : Blo 1437538 2157803 := bstep (se 1 (by rfl) ⟨1618352, by rfl⟩ : syracuseStep 2157803 = 3236705) B3236705
theorem B52481303 : Blo 1437538 52481303 := bstep (se 1 (by rfl) ⟨39360977, by rfl⟩ : syracuseStep 52481303 = 78721955) B78721955
theorem B18689305 : Blo 1437538 18689305 := bstep (se 2 (by rfl) ⟨7008489, by rfl⟩ : syracuseStep 18689305 = 14016979) B14016979
theorem B7286273 : Blo 1437538 7286273 := bstep (se 2 (by rfl) ⟨2732352, by rfl⟩ : syracuseStep 7286273 = 5464705) B5464705
theorem B1617439 : Blo 1437538 1617439 := bstep (se 1 (by rfl) ⟨1213079, by rfl⟩ : syracuseStep 1617439 = 2426159) B2426159
theorem B4607617 : Blo 1437538 4607617 := bstep (se 2 (by rfl) ⟨1727856, by rfl⟩ : syracuseStep 4607617 = 3455713) B3455713
theorem B2158463 : Blo 1437538 2158463 := bstep (se 1 (by rfl) ⟨1618847, by rfl⟩ : syracuseStep 2158463 = 3237695) B3237695
theorem B1437727 : Blo 1437538 1437727 := bstep (se 1 (by rfl) ⟨1078295, by rfl⟩ : syracuseStep 1437727 = 2156591) B2156591
theorem B4853843 : Blo 1437538 4853843 := bstep (se 1 (by rfl) ⟨3640382, by rfl⟩ : syracuseStep 4853843 = 7280765) B7280765
theorem B41504885 : Blo 1437538 41504885 := bstep (se 5 (by rfl) ⟨1945541, by rfl⟩ : syracuseStep 41504885 = 3891083) B3891083
theorem B4853951 : Blo 1437538 4853951 := bstep (se 1 (by rfl) ⟨3640463, by rfl⟩ : syracuseStep 4853951 = 7280927) B7280927
theorem B1437903 : Blo 1437538 1437903 := bstep (se 1 (by rfl) ⟨1078427, by rfl⟩ : syracuseStep 1437903 = 2156855) B2156855
theorem B2158799 : Blo 1437538 2158799 := bstep (se 1 (by rfl) ⟨1619099, by rfl⟩ : syracuseStep 2158799 = 3238199) B3238199
theorem B8196329 : Blo 1437538 8196329 := bstep (se 2 (by rfl) ⟨3073623, by rfl⟩ : syracuseStep 8196329 = 6147247) B6147247
theorem B7582009 : Blo 1437538 7582009 := bstep (se 2 (by rfl) ⟨2843253, by rfl⟩ : syracuseStep 7582009 = 5686507) B5686507
theorem B74731841 : Blo 1437538 74731841 := bstep (se 2 (by rfl) ⟨28024440, by rfl⟩ : syracuseStep 74731841 = 56048881) B56048881
theorem B1438023 : Blo 1437538 1438023 := bstep (se 1 (by rfl) ⟨1078517, by rfl⟩ : syracuseStep 1438023 = 2157035) B2157035
theorem B2158919 : Blo 1437538 2158919 := bstep (se 1 (by rfl) ⟨1619189, by rfl⟩ : syracuseStep 2158919 = 3238379) B3238379
theorem B3281359 : Blo 1437538 3281359 := bstep (se 1 (by rfl) ⟨2461019, by rfl⟩ : syracuseStep 3281359 = 4922039) B4922039
theorem B34992593 : Blo 1437538 34992593 := bstep (se 2 (by rfl) ⟨13122222, by rfl⟩ : syracuseStep 34992593 = 26244445) B26244445
theorem B1438491 : Blo 1437538 1438491 := bstep (se 1 (by rfl) ⟨1078868, by rfl⟩ : syracuseStep 1438491 = 2157737) B2157737
theorem B1438767 : Blo 1437538 1438767 := bstep (se 1 (by rfl) ⟨1079075, by rfl⟩ : syracuseStep 1438767 = 2158151) B2158151
theorem B28046425 : Blo 1437538 28046425 := bstep (se 2 (by rfl) ⟨10517409, by rfl⟩ : syracuseStep 28046425 = 21034819) B21034819
theorem B3642479 : Blo 1437538 3642479 := bstep (se 1 (by rfl) ⟨2731859, by rfl⟩ : syracuseStep 3642479 = 5463719) B5463719
theorem B1438887 : Blo 1437538 1438887 := bstep (se 1 (by rfl) ⟨1079165, by rfl⟩ : syracuseStep 1438887 = 2158331) B2158331
theorem B4920713 : Blo 1437538 4920713 := bstep (se 2 (by rfl) ⟨1845267, by rfl⟩ : syracuseStep 4920713 = 3690535) B3690535
theorem B36885941 : Blo 1437538 36885941 := bstep (se 5 (by rfl) ⟨1729028, by rfl⟩ : syracuseStep 36885941 = 3458057) B3458057
theorem B18421343 : Blo 1437538 18421343 := bstep (se 1 (by rfl) ⟨13816007, by rfl⟩ : syracuseStep 18421343 = 27632015) B27632015
theorem B1439335 : Blo 1437538 1439335 := bstep (se 1 (by rfl) ⟨1079501, by rfl⟩ : syracuseStep 1439335 = 2159003) B2159003
theorem B8197787 : Blo 1437538 8197787 := bstep (se 1 (by rfl) ⟨6148340, by rfl⟩ : syracuseStep 8197787 = 12296681) B12296681
theorem B13129381 : Blo 1437538 13129381 := bstep (se 4 (by rfl) ⟨1230879, by rfl⟩ : syracuseStep 13129381 = 2461759) B2461759
theorem B13825849 : Blo 1437538 13825849 := bstep (se 2 (by rfl) ⟨5184693, by rfl⟩ : syracuseStep 13825849 = 10369387) B10369387
theorem B5183311 : Blo 1437538 5183311 := bstep (se 1 (by rfl) ⟨3887483, by rfl⟩ : syracuseStep 5183311 = 7774967) B7774967
theorem B8197969 : Blo 1437538 8197969 := bstep (se 2 (by rfl) ⟨3074238, by rfl⟩ : syracuseStep 8197969 = 6148477) B6148477
theorem B3455099 : Blo 1437538 3455099 := bstep (se 1 (by rfl) ⟨2591324, by rfl⟩ : syracuseStep 3455099 = 5182649) B5182649
theorem B3889277 : Blo 1437538 3889277 := bstep (se 3 (by rfl) ⟨729239, by rfl⟩ : syracuseStep 3889277 = 1458479) B1458479
theorem B18438461 : Blo 1437538 18438461 := bstep (se 3 (by rfl) ⟨3457211, by rfl⟩ : syracuseStep 18438461 = 6914423) B6914423
theorem B14022985 : Blo 1437538 14022985 := bstep (se 2 (by rfl) ⟨5258619, by rfl⟩ : syracuseStep 14022985 = 10517239) B10517239
theorem B3234491 : Blo 1437538 3234491 := bstep (se 1 (by rfl) ⟨2425868, by rfl⟩ : syracuseStep 3234491 = 4851737) B4851737
theorem B8190679 : Blo 1437538 8190679 := bstep (se 1 (by rfl) ⟨6143009, by rfl⟩ : syracuseStep 8190679 = 12286019) B12286019
theorem B3234599 : Blo 1437538 3234599 := bstep (se 1 (by rfl) ⟨2425949, by rfl⟩ : syracuseStep 3234599 = 4851899) B4851899
theorem B29530925 : Blo 1437538 29530925 := bstep (se 3 (by rfl) ⟨5537048, by rfl⟩ : syracuseStep 29530925 = 11074097) B11074097
theorem B4856705 : Blo 1437538 4856705 := bstep (se 2 (by rfl) ⟨1821264, by rfl⟩ : syracuseStep 4856705 = 3642529) B3642529
theorem B7781321 : Blo 1437538 7781321 := bstep (se 2 (by rfl) ⟨2917995, by rfl⟩ : syracuseStep 7781321 = 5835991) B5835991
theorem B5831777 : Blo 1437538 5831777 := bstep (se 2 (by rfl) ⟨2186916, by rfl⟩ : syracuseStep 5831777 = 4373833) B4373833
theorem B16841999 : Blo 1437538 16841999 := bstep (se 1 (by rfl) ⟨12631499, by rfl⟩ : syracuseStep 16841999 = 25262999) B25262999
theorem B14769485 : Blo 1437538 14769485 := bstep (se 3 (by rfl) ⟨2769278, by rfl⟩ : syracuseStep 14769485 = 5538557) B5538557
theorem B59030957 : Blo 1437538 59030957 := bstep (se 3 (by rfl) ⟨11068304, by rfl⟩ : syracuseStep 59030957 = 22136609) B22136609
theorem B28032479 : Blo 1437538 28032479 := bstep (se 1 (by rfl) ⟨21024359, by rfl⟩ : syracuseStep 28032479 = 42048719) B42048719
theorem B5463521 : Blo 1437538 5463521 := bstep (se 2 (by rfl) ⟨2048820, by rfl⟩ : syracuseStep 5463521 = 4097641) B4097641
theorem B3235391 : Blo 1437538 3235391 := bstep (se 1 (by rfl) ⟨2426543, by rfl⟩ : syracuseStep 3235391 = 4853087) B4853087
theorem B3235751 : Blo 1437538 3235751 := bstep (se 1 (by rfl) ⟨2426813, by rfl⟩ : syracuseStep 3235751 = 4853627) B4853627
theorem B12287933 : Blo 1437538 12287933 := bstep (se 3 (by rfl) ⟨2303987, by rfl⟩ : syracuseStep 12287933 = 4607975) B4607975
theorem B9838579 : Blo 1437538 9838579 := bstep (se 1 (by rfl) ⟨7378934, by rfl⟩ : syracuseStep 9838579 = 14757869) B14757869
theorem B3235895 : Blo 1437538 3235895 := bstep (se 1 (by rfl) ⟨2426921, by rfl⟩ : syracuseStep 3235895 = 4853843) B4853843
theorem B3235967 : Blo 1437538 3235967 := bstep (se 1 (by rfl) ⟨2426975, by rfl⟩ : syracuseStep 3235967 = 4853951) B4853951
theorem B5464219 : Blo 1437538 5464219 := bstep (se 1 (by rfl) ⟨4098164, by rfl⟩ : syracuseStep 5464219 = 8196329) B8196329
theorem B10109345 : Blo 1437538 10109345 := bstep (se 2 (by rfl) ⟨3791004, by rfl⟩ : syracuseStep 10109345 = 7582009) B7582009
theorem B12288617 : Blo 1437538 12288617 := bstep (se 2 (by rfl) ⟨4608231, by rfl⟩ : syracuseStep 12288617 = 9216463) B9216463
theorem B4375145 : Blo 1437538 4375145 := bstep (se 2 (by rfl) ⟨1640679, by rfl⟩ : syracuseStep 4375145 = 3281359) B3281359
theorem B10920905 : Blo 1437538 10920905 := bstep (se 2 (by rfl) ⟨4095339, by rfl⟩ : syracuseStep 10920905 = 8190679) B8190679
theorem B12280895 : Blo 1437538 12280895 := bstep (se 1 (by rfl) ⟨9210671, by rfl⟩ : syracuseStep 12280895 = 18421343) B18421343
theorem B5465191 : Blo 1437538 5465191 := bstep (se 1 (by rfl) ⟨4098893, by rfl⟩ : syracuseStep 5465191 = 8197787) B8197787
theorem B2303399 : Blo 1437538 2303399 := bstep (se 1 (by rfl) ⟨1727549, by rfl⟩ : syracuseStep 2303399 = 3455099) B3455099
theorem B2156327 : Blo 1437538 2156327 := bstep (se 1 (by rfl) ⟨1617245, by rfl⟩ : syracuseStep 2156327 = 3234491) B3234491
theorem B2156399 : Blo 1437538 2156399 := bstep (se 1 (by rfl) ⟨1617299, by rfl⟩ : syracuseStep 2156399 = 3234599) B3234599
theorem B19687283 : Blo 1437538 19687283 := bstep (se 1 (by rfl) ⟨14765462, by rfl⟩ : syracuseStep 19687283 = 29530925) B29530925
theorem B3237803 : Blo 1437538 3237803 := bstep (se 1 (by rfl) ⟨2428352, by rfl⟩ : syracuseStep 3237803 = 4856705) B4856705
theorem B5187547 : Blo 1437538 5187547 := bstep (se 1 (by rfl) ⟨3890660, by rfl⟩ : syracuseStep 5187547 = 7781321) B7781321
theorem B2156585 : Blo 1437538 2156585 := bstep (se 2 (by rfl) ⟨808719, by rfl⟩ : syracuseStep 2156585 = 1617439) B1617439
theorem B18688319 : Blo 1437538 18688319 := bstep (se 1 (by rfl) ⟨14016239, by rfl⟩ : syracuseStep 18688319 = 28032479) B28032479
theorem B2156927 : Blo 1437538 2156927 := bstep (se 1 (by rfl) ⟨1617695, by rfl⟩ : syracuseStep 2156927 = 3235391) B3235391
theorem B18434465 : Blo 1437538 18434465 := bstep (se 2 (by rfl) ⟨6912924, by rfl⟩ : syracuseStep 18434465 = 13825849) B13825849
theorem B10930625 : Blo 1437538 10930625 := bstep (se 2 (by rfl) ⟨4098984, by rfl⟩ : syracuseStep 10930625 = 8197969) B8197969
theorem B124357193 : Blo 1437538 124357193 := bstep (se 2 (by rfl) ⟨46633947, by rfl⟩ : syracuseStep 124357193 = 93267895) B93267895
theorem B2157167 : Blo 1437538 2157167 := bstep (se 1 (by rfl) ⟨1617875, by rfl⟩ : syracuseStep 2157167 = 3235751) B3235751
theorem B13118105 : Blo 1437538 13118105 := bstep (se 2 (by rfl) ⟨4919289, by rfl⟩ : syracuseStep 13118105 = 9838579) B9838579
theorem B7285463 : Blo 1437538 7285463 := bstep (se 1 (by rfl) ⟨5464097, by rfl⟩ : syracuseStep 7285463 = 10928195) B10928195
theorem B2304731 : Blo 1437538 2304731 := bstep (se 1 (by rfl) ⟨1728548, by rfl⟩ : syracuseStep 2304731 = 3457097) B3457097
theorem B4852601 : Blo 1437538 4852601 := bstep (se 2 (by rfl) ⟨1819725, by rfl⟩ : syracuseStep 4852601 = 3639451) B3639451
theorem B18697313 : Blo 1437538 18697313 := bstep (se 2 (by rfl) ⟨7011492, by rfl⟩ : syracuseStep 18697313 = 14022985) B14022985
theorem B44297351 : Blo 1437538 44297351 := bstep (se 1 (by rfl) ⟨33223013, by rfl⟩ : syracuseStep 44297351 = 66446027) B66446027
theorem B17509529 : Blo 1437538 17509529 := bstep (se 2 (by rfl) ⟨6566073, by rfl⟩ : syracuseStep 17509529 = 13132147) B13132147
theorem B10923335 : Blo 1437538 10923335 := bstep (se 1 (by rfl) ⟨8192501, by rfl⟩ : syracuseStep 10923335 = 16385003) B16385003
theorem B2428319 : Blo 1437538 2428319 := bstep (se 1 (by rfl) ⟨1821239, by rfl⟩ : syracuseStep 2428319 = 3642479) B3642479
theorem B2731495 : Blo 1437538 2731495 := bstep (se 1 (by rfl) ⟨2048621, by rfl⟩ : syracuseStep 2731495 = 4097243) B4097243
theorem B3280475 : Blo 1437538 3280475 := bstep (se 1 (by rfl) ⟨2460356, by rfl⟩ : syracuseStep 3280475 = 4920713) B4920713
theorem B12283559 : Blo 1437538 12283559 := bstep (se 1 (by rfl) ⟨9212669, by rfl⟩ : syracuseStep 12283559 = 18425339) B18425339
theorem B153636533 : Blo 1437538 153636533 := bstep (se 5 (by rfl) ⟨7201712, by rfl⟩ : syracuseStep 153636533 = 14403425) B14403425
theorem B1535855 : Blo 1437538 1535855 := bstep (se 1 (by rfl) ⟨1151891, by rfl⟩ : syracuseStep 1535855 = 2303783) B2303783
theorem B1437607 : Blo 1437538 1437607 := bstep (se 1 (by rfl) ⟨1078205, by rfl⟩ : syracuseStep 1437607 = 2156411) B2156411
theorem B1437631 : Blo 1437538 1437631 := bstep (se 1 (by rfl) ⟨1078223, by rfl⟩ : syracuseStep 1437631 = 2156447) B2156447
theorem B2592851 : Blo 1437538 2592851 := bstep (se 1 (by rfl) ⟨1944638, by rfl⟩ : syracuseStep 2592851 = 3889277) B3889277
theorem B1437787 : Blo 1437538 1437787 := bstep (se 1 (by rfl) ⟨1078340, by rfl⟩ : syracuseStep 1437787 = 2156681) B2156681
theorem B1618087 : Blo 1437538 1618087 := bstep (se 1 (by rfl) ⟨1213565, by rfl⟩ : syracuseStep 1618087 = 2427131) B2427131
theorem B1437887 : Blo 1437538 1437887 := bstep (se 1 (by rfl) ⟨1078415, by rfl⟩ : syracuseStep 1437887 = 2156831) B2156831
theorem B12292307 : Blo 1437538 12292307 := bstep (se 1 (by rfl) ⟨9219230, by rfl⟩ : syracuseStep 12292307 = 18438461) B18438461
theorem B1437919 : Blo 1437538 1437919 := bstep (se 1 (by rfl) ⟨1078439, by rfl⟩ : syracuseStep 1437919 = 2156879) B2156879
theorem B10924307 : Blo 1437538 10924307 := bstep (se 1 (by rfl) ⟨8193230, by rfl⟩ : syracuseStep 10924307 = 16386461) B16386461
theorem B1437979 : Blo 1437538 1437979 := bstep (se 1 (by rfl) ⟨1078484, by rfl⟩ : syracuseStep 1437979 = 2156969) B2156969
theorem B1438235 : Blo 1437538 1438235 := bstep (se 1 (by rfl) ⟨1078676, by rfl⟩ : syracuseStep 1438235 = 2157353) B2157353
theorem B1438375 : Blo 1437538 1438375 := bstep (se 1 (by rfl) ⟨1078781, by rfl⟩ : syracuseStep 1438375 = 2157563) B2157563
theorem B1438415 : Blo 1437538 1438415 := bstep (se 1 (by rfl) ⟨1078811, by rfl⟩ : syracuseStep 1438415 = 2157623) B2157623
theorem B3887851 : Blo 1437538 3887851 := bstep (se 1 (by rfl) ⟨2915888, by rfl⟩ : syracuseStep 3887851 = 5831777) B5831777
theorem B10924793 : Blo 1437538 10924793 := bstep (se 2 (by rfl) ⟨4096797, by rfl⟩ : syracuseStep 10924793 = 8193595) B8193595
theorem B1438495 : Blo 1437538 1438495 := bstep (se 1 (by rfl) ⟨1078871, by rfl⟩ : syracuseStep 1438495 = 2157743) B2157743
theorem B1438535 : Blo 1437538 1438535 := bstep (se 1 (by rfl) ⟨1078901, by rfl⟩ : syracuseStep 1438535 = 2157803) B2157803
theorem B11227999 : Blo 1437538 11227999 := bstep (se 1 (by rfl) ⟨8420999, by rfl⟩ : syracuseStep 11227999 = 16841999) B16841999
theorem B3642347 : Blo 1437538 3642347 := bstep (se 1 (by rfl) ⟨2731760, by rfl⟩ : syracuseStep 3642347 = 5463521) B5463521
theorem B6911081 : Blo 1437538 6911081 := bstep (se 2 (by rfl) ⟨2591655, by rfl⟩ : syracuseStep 6911081 = 5183311) B5183311
theorem B1438975 : Blo 1437538 1438975 := bstep (se 1 (by rfl) ⟨1079231, by rfl⟩ : syracuseStep 1438975 = 2158463) B2158463
theorem B27669923 : Blo 1437538 27669923 := bstep (se 1 (by rfl) ⟨20752442, by rfl⟩ : syracuseStep 27669923 = 41504885) B41504885
theorem B1439199 : Blo 1437538 1439199 := bstep (se 1 (by rfl) ⟨1079399, by rfl⟩ : syracuseStep 1439199 = 2158799) B2158799
theorem B49821227 : Blo 1437538 49821227 := bstep (se 1 (by rfl) ⟨37365920, by rfl⟩ : syracuseStep 49821227 = 74731841) B74731841
theorem B1439279 : Blo 1437538 1439279 := bstep (se 1 (by rfl) ⟨1079459, by rfl⟩ : syracuseStep 1439279 = 2158919) B2158919
theorem B21010043 : Blo 1437538 21010043 := bstep (se 1 (by rfl) ⟨15757532, by rfl⟩ : syracuseStep 21010043 = 31515065) B31515065
theorem B23328395 : Blo 1437538 23328395 := bstep (se 1 (by rfl) ⟨17496296, by rfl⟩ : syracuseStep 23328395 = 34992593) B34992593
theorem B3643127 : Blo 1437538 3643127 := bstep (se 1 (by rfl) ⟨2732345, by rfl⟩ : syracuseStep 3643127 = 5464691) B5464691
theorem B24590627 : Blo 1437538 24590627 := bstep (se 1 (by rfl) ⟨18442970, by rfl⟩ : syracuseStep 24590627 = 36885941) B36885941
theorem B9976229 : Blo 1437538 9976229 := bstep (se 4 (by rfl) ⟨935271, by rfl⟩ : syracuseStep 9976229 = 1870543) B1870543
theorem B4856435 : Blo 1437538 4856435 := bstep (se 1 (by rfl) ⟨3642326, by rfl⟩ : syracuseStep 4856435 = 7284653) B7284653
theorem B10926737 : Blo 1437538 10926737 := bstep (se 2 (by rfl) ⟨4097526, by rfl⟩ : syracuseStep 10926737 = 8195053) B8195053
theorem B3070651 : Blo 1437538 3070651 := bstep (se 1 (by rfl) ⟨2302988, by rfl⟩ : syracuseStep 3070651 = 4605977) B4605977
theorem B37395233 : Blo 1437538 37395233 := bstep (se 2 (by rfl) ⟨14023212, by rfl⟩ : syracuseStep 37395233 = 28046425) B28046425
theorem B27663227 : Blo 1437538 27663227 := bstep (se 1 (by rfl) ⟨20747420, by rfl⟩ : syracuseStep 27663227 = 41494841) B41494841
theorem B24919073 : Blo 1437538 24919073 := bstep (se 2 (by rfl) ⟨9344652, by rfl⟩ : syracuseStep 24919073 = 18689305) B18689305
theorem B3235193 : Blo 1437538 3235193 := bstep (se 2 (by rfl) ⟨1213197, by rfl⟩ : syracuseStep 3235193 = 2426395) B2426395
theorem B6143489 : Blo 1437538 6143489 := bstep (se 2 (by rfl) ⟨2303808, by rfl⟩ : syracuseStep 6143489 = 4607617) B4607617
theorem B34987535 : Blo 1437538 34987535 := bstep (se 1 (by rfl) ⟨26240651, by rfl⟩ : syracuseStep 34987535 = 52481303) B52481303
theorem B17505841 : Blo 1437538 17505841 := bstep (se 2 (by rfl) ⟨6564690, by rfl⟩ : syracuseStep 17505841 = 13129381) B13129381
theorem B9846323 : Blo 1437538 9846323 := bstep (se 1 (by rfl) ⟨7384742, by rfl⟩ : syracuseStep 9846323 = 14769485) B14769485
theorem B39353971 : Blo 1437538 39353971 := bstep (se 1 (by rfl) ⟨29515478, by rfl⟩ : syracuseStep 39353971 = 59030957) B59030957
theorem B4857515 : Blo 1437538 4857515 := bstep (se 1 (by rfl) ⟨3643136, by rfl⟩ : syracuseStep 4857515 = 7286273) B7286273
theorem B8191955 : Blo 1437538 8191955 := bstep (se 1 (by rfl) ⟨6143966, by rfl⟩ : syracuseStep 8191955 = 12287933) B12287933
theorem B7282871 : Blo 1437538 7282871 := bstep (se 1 (by rfl) ⟨5462153, by rfl⟩ : syracuseStep 7282871 = 10924307) B10924307
theorem B6914269 : Blo 1437538 6914269 := bstep (se 3 (by rfl) ⟨1296425, by rfl⟩ : syracuseStep 6914269 = 2592851) B2592851
theorem B8192411 : Blo 1437538 8192411 := bstep (se 1 (by rfl) ⟨6144308, by rfl⟩ : syracuseStep 8192411 = 12288617) B12288617
theorem B7283195 : Blo 1437538 7283195 := bstep (se 1 (by rfl) ⟨5462396, by rfl⟩ : syracuseStep 7283195 = 10924793) B10924793
theorem B13124855 : Blo 1437538 13124855 := bstep (se 1 (by rfl) ⟨9843641, by rfl⟩ : syracuseStep 13124855 = 19687283) B19687283
theorem B16393751 : Blo 1437538 16393751 := bstep (se 1 (by rfl) ⟨12295313, by rfl⟩ : syracuseStep 16393751 = 24590627) B24590627
theorem B12289643 : Blo 1437538 12289643 := bstep (se 1 (by rfl) ⟨9217232, by rfl⟩ : syracuseStep 12289643 = 18434465) B18434465
theorem B11667053 : Blo 1437538 11667053 := bstep (se 3 (by rfl) ⟨2187572, by rfl⟩ : syracuseStep 11667053 = 4375145) B4375145
theorem B82904795 : Blo 1437538 82904795 := bstep (se 1 (by rfl) ⟨62178596, by rfl⟩ : syracuseStep 82904795 = 124357193) B124357193
theorem B3237623 : Blo 1437538 3237623 := bstep (se 1 (by rfl) ⟨2428217, by rfl⟩ : syracuseStep 3237623 = 4856435) B4856435
theorem B7284491 : Blo 1437538 7284491 := bstep (se 1 (by rfl) ⟨5463368, by rfl⟩ : syracuseStep 7284491 = 10926737) B10926737
theorem B24930155 : Blo 1437538 24930155 := bstep (se 1 (by rfl) ⟨18697616, by rfl⟩ : syracuseStep 24930155 = 37395233) B37395233
theorem B6145949 : Blo 1437538 6145949 := bstep (se 3 (by rfl) ⟨1152365, by rfl⟩ : syracuseStep 6145949 = 2304731) B2304731
theorem B18442151 : Blo 1437538 18442151 := bstep (se 1 (by rfl) ⟨13831613, by rfl⟩ : syracuseStep 18442151 = 27663227) B27663227
theorem B23341121 : Blo 1437538 23341121 := bstep (se 2 (by rfl) ⟨8752920, by rfl⟩ : syracuseStep 23341121 = 17505841) B17505841
theorem B52471961 : Blo 1437538 52471961 := bstep (se 2 (by rfl) ⟨19676985, by rfl⟩ : syracuseStep 52471961 = 39353971) B39353971
theorem B2156795 : Blo 1437538 2156795 := bstep (se 1 (by rfl) ⟨1617596, by rfl⟩ : syracuseStep 2156795 = 3235193) B3235193
theorem B23325023 : Blo 1437538 23325023 := bstep (se 1 (by rfl) ⟨17493767, by rfl⟩ : syracuseStep 23325023 = 34987535) B34987535
theorem B6564215 : Blo 1437538 6564215 := bstep (se 1 (by rfl) ⟨4923161, by rfl⟩ : syracuseStep 6564215 = 9846323) B9846323
theorem B3238343 : Blo 1437538 3238343 := bstep (se 1 (by rfl) ⟨2428757, by rfl⟩ : syracuseStep 3238343 = 4857515) B4857515
theorem B27666917 : Blo 1437538 27666917 := bstep (se 4 (by rfl) ⟨2593773, by rfl⟩ : syracuseStep 27666917 = 5187547) B5187547
theorem B2157263 : Blo 1437538 2157263 := bstep (se 1 (by rfl) ⟨1617947, by rfl⟩ : syracuseStep 2157263 = 3235895) B3235895
theorem B2157311 : Blo 1437538 2157311 := bstep (se 1 (by rfl) ⟨1617983, by rfl⟩ : syracuseStep 2157311 = 3235967) B3235967
theorem B8194871 : Blo 1437538 8194871 := bstep (se 1 (by rfl) ⟨6146153, by rfl⟩ : syracuseStep 8194871 = 12292307) B12292307
theorem B7285625 : Blo 1437538 7285625 := bstep (se 2 (by rfl) ⟨2732109, by rfl⟩ : syracuseStep 7285625 = 5464219) B5464219
theorem B2157449 : Blo 1437538 2157449 := bstep (se 2 (by rfl) ⟨809043, by rfl⟩ : syracuseStep 2157449 = 1618087) B1618087
theorem B2428231 : Blo 1437538 2428231 := bstep (se 1 (by rfl) ⟨1821173, by rfl⟩ : syracuseStep 2428231 = 3642347) B3642347
theorem B8187263 : Blo 1437538 8187263 := bstep (se 1 (by rfl) ⟨6140447, by rfl⟩ : syracuseStep 8187263 = 12280895) B12280895
theorem B4607387 : Blo 1437538 4607387 := bstep (se 1 (by rfl) ⟨3455540, by rfl⟩ : syracuseStep 4607387 = 6911081) B6911081
theorem B1535599 : Blo 1437538 1535599 := bstep (se 1 (by rfl) ⟨1151699, by rfl⟩ : syracuseStep 1535599 = 2303399) B2303399
theorem B33214151 : Blo 1437538 33214151 := bstep (se 1 (by rfl) ⟨24910613, by rfl⟩ : syracuseStep 33214151 = 49821227) B49821227
theorem B15552263 : Blo 1437538 15552263 := bstep (se 1 (by rfl) ⟨11664197, by rfl⟩ : syracuseStep 15552263 = 23328395) B23328395
theorem B14970665 : Blo 1437538 14970665 := bstep (se 2 (by rfl) ⟨5613999, by rfl⟩ : syracuseStep 14970665 = 11227999) B11227999
theorem B2428751 : Blo 1437538 2428751 := bstep (se 1 (by rfl) ⟨1821563, by rfl⟩ : syracuseStep 2428751 = 3643127) B3643127
theorem B1437551 : Blo 1437538 1437551 := bstep (se 1 (by rfl) ⟨1078163, by rfl⟩ : syracuseStep 1437551 = 2156327) B2156327
theorem B1437599 : Blo 1437538 1437599 := bstep (se 1 (by rfl) ⟨1078199, by rfl⟩ : syracuseStep 1437599 = 2156399) B2156399
theorem B2158535 : Blo 1437538 2158535 := bstep (se 1 (by rfl) ⟨1618901, by rfl⟩ : syracuseStep 2158535 = 3237803) B3237803
theorem B1437723 : Blo 1437538 1437723 := bstep (se 1 (by rfl) ⟨1078292, by rfl⟩ : syracuseStep 1437723 = 2156585) B2156585
theorem B7286921 : Blo 1437538 7286921 := bstep (se 2 (by rfl) ⟨2732595, by rfl⟩ : syracuseStep 7286921 = 5465191) B5465191
theorem B1437951 : Blo 1437538 1437951 := bstep (se 1 (by rfl) ⟨1078463, by rfl⟩ : syracuseStep 1437951 = 2156927) B2156927
theorem B7287083 : Blo 1437538 7287083 := bstep (se 1 (by rfl) ⟨5465312, by rfl⟩ : syracuseStep 7287083 = 10930625) B10930625
theorem B1438111 : Blo 1437538 1438111 := bstep (se 1 (by rfl) ⟨1078583, by rfl⟩ : syracuseStep 1438111 = 2157167) B2157167
theorem B8745403 : Blo 1437538 8745403 := bstep (se 1 (by rfl) ⟨6559052, by rfl⟩ : syracuseStep 8745403 = 13118105) B13118105
theorem B3641993 : Blo 1437538 3641993 := bstep (se 2 (by rfl) ⟨1365747, by rfl⟩ : syracuseStep 3641993 = 2731495) B2731495
theorem B12464875 : Blo 1437538 12464875 := bstep (se 1 (by rfl) ⟨9348656, by rfl⟩ : syracuseStep 12464875 = 18697313) B18697313
theorem B1618879 : Blo 1437538 1618879 := bstep (se 1 (by rfl) ⟨1214159, by rfl⟩ : syracuseStep 1618879 = 2428319) B2428319
theorem B8189039 : Blo 1437538 8189039 := bstep (se 1 (by rfl) ⟨6141779, by rfl⟩ : syracuseStep 8189039 = 12283559) B12283559
theorem B5461303 : Blo 1437538 5461303 := bstep (se 1 (by rfl) ⟨4095977, by rfl⟩ : syracuseStep 5461303 = 8191955) B8191955
theorem B7280603 : Blo 1437538 7280603 := bstep (se 1 (by rfl) ⟨5460452, by rfl⟩ : syracuseStep 7280603 = 10920905) B10920905
theorem B4094201 : Blo 1437538 4094201 := bstep (se 2 (by rfl) ⟨1535325, by rfl⟩ : syracuseStep 4094201 = 3070651) B3070651
theorem B18446615 : Blo 1437538 18446615 := bstep (se 1 (by rfl) ⟨13834961, by rfl⟩ : syracuseStep 18446615 = 27669923) B27669923
theorem B5183801 : Blo 1437538 5183801 := bstep (se 2 (by rfl) ⟨1943925, by rfl⟩ : syracuseStep 5183801 = 3887851) B3887851
theorem B14006695 : Blo 1437538 14006695 := bstep (se 1 (by rfl) ⟨10505021, by rfl⟩ : syracuseStep 14006695 = 21010043) B21010043
theorem B26958253 : Blo 1437538 26958253 := bstep (se 3 (by rfl) ⟨5054672, by rfl⟩ : syracuseStep 26958253 = 10109345) B10109345
theorem B12458879 : Blo 1437538 12458879 := bstep (se 1 (by rfl) ⟨9344159, by rfl⟩ : syracuseStep 12458879 = 18688319) B18688319
theorem B6650819 : Blo 1437538 6650819 := bstep (se 1 (by rfl) ⟨4988114, by rfl⟩ : syracuseStep 6650819 = 9976229) B9976229
theorem B4856975 : Blo 1437538 4856975 := bstep (se 1 (by rfl) ⟨3642731, by rfl⟩ : syracuseStep 4856975 = 7285463) B7285463
theorem B3235067 : Blo 1437538 3235067 := bstep (se 1 (by rfl) ⟨2426300, by rfl⟩ : syracuseStep 3235067 = 4852601) B4852601
theorem B16612715 : Blo 1437538 16612715 := bstep (se 1 (by rfl) ⟨12459536, by rfl⟩ : syracuseStep 16612715 = 24919073) B24919073
theorem B29531567 : Blo 1437538 29531567 := bstep (se 1 (by rfl) ⟨22148675, by rfl⟩ : syracuseStep 29531567 = 44297351) B44297351
theorem B11673019 : Blo 1437538 11673019 := bstep (se 1 (by rfl) ⟨8754764, by rfl⟩ : syracuseStep 11673019 = 17509529) B17509529
theorem B7282223 : Blo 1437538 7282223 := bstep (se 1 (by rfl) ⟨5461667, by rfl⟩ : syracuseStep 7282223 = 10923335) B10923335
theorem B4095613 : Blo 1437538 4095613 := bstep (se 3 (by rfl) ⟨767927, by rfl⟩ : syracuseStep 4095613 = 1535855) B1535855
theorem B4095659 : Blo 1437538 4095659 := bstep (se 1 (by rfl) ⟨3071744, by rfl⟩ : syracuseStep 4095659 = 6143489) B6143489
theorem B2186983 : Blo 1437538 2186983 := bstep (se 1 (by rfl) ⟨1640237, by rfl⟩ : syracuseStep 2186983 = 3280475) B3280475
theorem B102424355 : Blo 1437538 102424355 := bstep (se 1 (by rfl) ⟨76818266, by rfl⟩ : syracuseStep 102424355 = 153636533) B153636533
theorem B4857947 : Blo 1437538 4857947 := bstep (se 1 (by rfl) ⟨3643460, by rfl⟩ : syracuseStep 4857947 = 7286921) B7286921
theorem B4858055 : Blo 1437538 4858055 := bstep (se 1 (by rfl) ⟨3643541, by rfl⟩ : syracuseStep 4858055 = 7287083) B7287083
theorem B8749903 : Blo 1437538 8749903 := bstep (se 1 (by rfl) ⟨6562427, by rfl⟩ : syracuseStep 8749903 = 13124855) B13124855
theorem B10929167 : Blo 1437538 10929167 := bstep (se 1 (by rfl) ⟨8196875, by rfl⟩ : syracuseStep 10929167 = 16393751) B16393751
theorem B8193095 : Blo 1437538 8193095 := bstep (se 1 (by rfl) ⟨6144821, by rfl⟩ : syracuseStep 8193095 = 12289643) B12289643
theorem B4097299 : Blo 1437538 4097299 := bstep (se 1 (by rfl) ⟨3072974, by rfl⟩ : syracuseStep 4097299 = 6145949) B6145949
theorem B34981307 : Blo 1437538 34981307 := bstep (se 1 (by rfl) ⟨26235980, by rfl⟩ : syracuseStep 34981307 = 52471961) B52471961
theorem B2729467 : Blo 1437538 2729467 := bstep (se 1 (by rfl) ⟨2047100, by rfl⟩ : syracuseStep 2729467 = 4094201) B4094201
theorem B12297743 : Blo 1437538 12297743 := bstep (se 1 (by rfl) ⟨9223307, by rfl⟩ : syracuseStep 12297743 = 18446615) B18446615
theorem B15550015 : Blo 1437538 15550015 := bstep (se 1 (by rfl) ⟨11662511, by rfl⟩ : syracuseStep 15550015 = 23325023) B23325023
theorem B4376143 : Blo 1437538 4376143 := bstep (se 1 (by rfl) ⟨3282107, by rfl⟩ : syracuseStep 4376143 = 6564215) B6564215
theorem B3237641 : Blo 1437538 3237641 := bstep (se 2 (by rfl) ⟨1214115, by rfl⟩ : syracuseStep 3237641 = 2428231) B2428231
theorem B4433879 : Blo 1437538 4433879 := bstep (se 1 (by rfl) ⟨3325409, by rfl⟩ : syracuseStep 4433879 = 6650819) B6650819
theorem B3237983 : Blo 1437538 3237983 := bstep (se 1 (by rfl) ⟨2428487, by rfl⟩ : syracuseStep 3237983 = 4856975) B4856975
theorem B2156711 : Blo 1437538 2156711 := bstep (se 1 (by rfl) ⟨1617533, by rfl⟩ : syracuseStep 2156711 = 3235067) B3235067
theorem B5458175 : Blo 1437538 5458175 := bstep (se 1 (by rfl) ⟨4093631, by rfl⟩ : syracuseStep 5458175 = 8187263) B8187263
theorem B19687711 : Blo 1437538 19687711 := bstep (se 1 (by rfl) ⟨14765783, by rfl⟩ : syracuseStep 19687711 = 29531567) B29531567
theorem B2730439 : Blo 1437538 2730439 := bstep (se 1 (by rfl) ⟨2047829, by rfl⟩ : syracuseStep 2730439 = 4095659) B4095659
theorem B68282903 : Blo 1437538 68282903 := bstep (se 1 (by rfl) ⟨51212177, by rfl⟩ : syracuseStep 68282903 = 102424355) B102424355
theorem B9980443 : Blo 1437538 9980443 := bstep (se 1 (by rfl) ⟨7485332, by rfl⟩ : syracuseStep 9980443 = 14970665) B14970665
theorem B9219025 : Blo 1437538 9219025 := bstep (se 2 (by rfl) ⟨3457134, by rfl⟩ : syracuseStep 9219025 = 6914269) B6914269
theorem B2427995 : Blo 1437538 2427995 := bstep (se 1 (by rfl) ⟨1820996, by rfl⟩ : syracuseStep 2427995 = 3641993) B3641993
theorem B11660537 : Blo 1437538 11660537 := bstep (se 2 (by rfl) ⟨4372701, by rfl⟩ : syracuseStep 11660537 = 8745403) B8745403
theorem B5459359 : Blo 1437538 5459359 := bstep (se 1 (by rfl) ⟨4094519, by rfl⟩ : syracuseStep 5459359 = 8189039) B8189039
theorem B7778035 : Blo 1437538 7778035 := bstep (se 1 (by rfl) ⟨5833526, by rfl⟩ : syracuseStep 7778035 = 11667053) B11667053
theorem B2158415 : Blo 1437538 2158415 := bstep (se 1 (by rfl) ⟨1618811, by rfl⟩ : syracuseStep 2158415 = 3237623) B3237623
theorem B2158505 : Blo 1437538 2158505 := bstep (se 2 (by rfl) ⟨809439, by rfl⟩ : syracuseStep 2158505 = 1618879) B1618879
theorem B4853735 : Blo 1437538 4853735 := bstep (se 1 (by rfl) ⟨3640301, by rfl⟩ : syracuseStep 4853735 = 7280603) B7280603
theorem B15560747 : Blo 1437538 15560747 := bstep (se 1 (by rfl) ⟨11670560, by rfl⟩ : syracuseStep 15560747 = 23341121) B23341121
theorem B1437863 : Blo 1437538 1437863 := bstep (se 1 (by rfl) ⟨1078397, by rfl⟩ : syracuseStep 1437863 = 2156795) B2156795
theorem B2158895 : Blo 1437538 2158895 := bstep (se 1 (by rfl) ⟨1619171, by rfl⟩ : syracuseStep 2158895 = 3238343) B3238343
theorem B18444611 : Blo 1437538 18444611 := bstep (se 1 (by rfl) ⟨13833458, by rfl⟩ : syracuseStep 18444611 = 27666917) B27666917
theorem B1438175 : Blo 1437538 1438175 := bstep (se 1 (by rfl) ⟨1078631, by rfl⟩ : syracuseStep 1438175 = 2157263) B2157263
theorem B1438207 : Blo 1437538 1438207 := bstep (se 1 (by rfl) ⟨1078655, by rfl⟩ : syracuseStep 1438207 = 2157311) B2157311
theorem B1438299 : Blo 1437538 1438299 := bstep (se 1 (by rfl) ⟨1078724, by rfl⟩ : syracuseStep 1438299 = 2157449) B2157449
theorem B5460817 : Blo 1437538 5460817 := bstep (se 2 (by rfl) ⟨2047806, by rfl⟩ : syracuseStep 5460817 = 4095613) B4095613
theorem B4854815 : Blo 1437538 4854815 := bstep (se 1 (by rfl) ⟨3641111, by rfl⟩ : syracuseStep 4854815 = 7282223) B7282223
theorem B10368175 : Blo 1437538 10368175 := bstep (se 1 (by rfl) ⟨7776131, by rfl⟩ : syracuseStep 10368175 = 15552263) B15552263
theorem B1619167 : Blo 1437538 1619167 := bstep (se 1 (by rfl) ⟨1214375, by rfl⟩ : syracuseStep 1619167 = 2428751) B2428751
theorem B1439023 : Blo 1437538 1439023 := bstep (se 1 (by rfl) ⟨1079267, by rfl⟩ : syracuseStep 1439023 = 2158535) B2158535
theorem B4855247 : Blo 1437538 4855247 := bstep (se 1 (by rfl) ⟨3641435, by rfl⟩ : syracuseStep 4855247 = 7282871) B7282871
theorem B5461607 : Blo 1437538 5461607 := bstep (se 1 (by rfl) ⟨4096205, by rfl⟩ : syracuseStep 5461607 = 8192411) B8192411
theorem B4855463 : Blo 1437538 4855463 := bstep (se 1 (by rfl) ⟨3641597, by rfl⟩ : syracuseStep 4855463 = 7283195) B7283195
theorem B18675593 : Blo 1437538 18675593 := bstep (se 2 (by rfl) ⟨7003347, by rfl⟩ : syracuseStep 18675593 = 14006695) B14006695
theorem B35944337 : Blo 1437538 35944337 := bstep (se 2 (by rfl) ⟨13479126, by rfl⟩ : syracuseStep 35944337 = 26958253) B26958253
theorem B16619833 : Blo 1437538 16619833 := bstep (se 2 (by rfl) ⟨6232437, by rfl⟩ : syracuseStep 16619833 = 12464875) B12464875
theorem B55269863 : Blo 1437538 55269863 := bstep (se 1 (by rfl) ⟨41452397, by rfl⟩ : syracuseStep 55269863 = 82904795) B82904795
theorem B4856327 : Blo 1437538 4856327 := bstep (se 1 (by rfl) ⟨3642245, by rfl⟩ : syracuseStep 4856327 = 7284491) B7284491
theorem B11663909 : Blo 1437538 11663909 := bstep (se 4 (by rfl) ⟨1093491, by rfl⟩ : syracuseStep 11663909 = 2186983) B2186983
theorem B16620103 : Blo 1437538 16620103 := bstep (se 1 (by rfl) ⟨12465077, by rfl⟩ : syracuseStep 16620103 = 24930155) B24930155
theorem B12294767 : Blo 1437538 12294767 := bstep (se 1 (by rfl) ⟨9221075, by rfl⟩ : syracuseStep 12294767 = 18442151) B18442151
theorem B3455867 : Blo 1437538 3455867 := bstep (se 1 (by rfl) ⟨2591900, by rfl⟩ : syracuseStep 3455867 = 5183801) B5183801
theorem B7281737 : Blo 1437538 7281737 := bstep (se 2 (by rfl) ⟨2730651, by rfl⟩ : syracuseStep 7281737 = 5461303) B5461303
theorem B5463247 : Blo 1437538 5463247 := bstep (se 1 (by rfl) ⟨4097435, by rfl⟩ : syracuseStep 5463247 = 8194871) B8194871
theorem B15564025 : Blo 1437538 15564025 := bstep (se 2 (by rfl) ⟨5836509, by rfl⟩ : syracuseStep 15564025 = 11673019) B11673019
theorem B4857083 : Blo 1437538 4857083 := bstep (se 1 (by rfl) ⟨3642812, by rfl⟩ : syracuseStep 4857083 = 7285625) B7285625
theorem B8305919 : Blo 1437538 8305919 := bstep (se 1 (by rfl) ⟨6229439, by rfl⟩ : syracuseStep 8305919 = 12458879) B12458879
theorem B2047465 : Blo 1437538 2047465 := bstep (se 2 (by rfl) ⟨767799, by rfl⟩ : syracuseStep 2047465 = 1535599) B1535599
theorem B11075143 : Blo 1437538 11075143 := bstep (se 1 (by rfl) ⟨8306357, by rfl⟩ : syracuseStep 11075143 = 16612715) B16612715
theorem B3071591 : Blo 1437538 3071591 := bstep (se 1 (by rfl) ⟨2303693, by rfl⟩ : syracuseStep 3071591 = 4607387) B4607387
theorem B22142767 : Blo 1437538 22142767 := bstep (se 1 (by rfl) ⟨16607075, by rfl⟩ : syracuseStep 22142767 = 33214151) B33214151
theorem B12296407 : Blo 1437538 12296407 := bstep (se 1 (by rfl) ⟨9222305, by rfl⟩ : syracuseStep 12296407 = 18444611) B18444611
theorem B22159777 : Blo 1437538 22159777 := bstep (se 2 (by rfl) ⟨8309916, by rfl⟩ : syracuseStep 22159777 = 16619833) B16619833
theorem B3236543 : Blo 1437538 3236543 := bstep (se 1 (by rfl) ⟨2427407, by rfl⟩ : syracuseStep 3236543 = 4854815) B4854815
theorem B22160137 : Blo 1437538 22160137 := bstep (se 2 (by rfl) ⟨8310051, by rfl⟩ : syracuseStep 22160137 = 16620103) B16620103
theorem B3236831 : Blo 1437538 3236831 := bstep (se 1 (by rfl) ⟨2427623, by rfl⟩ : syracuseStep 3236831 = 4855247) B4855247
theorem B11666537 : Blo 1437538 11666537 := bstep (se 2 (by rfl) ⟨4374951, by rfl⟩ : syracuseStep 11666537 = 8749903) B8749903
theorem B3236975 : Blo 1437538 3236975 := bstep (se 1 (by rfl) ⟨2427731, by rfl⟩ : syracuseStep 3236975 = 4855463) B4855463
theorem B3638783 : Blo 1437538 3638783 := bstep (se 1 (by rfl) ⟨2729087, by rfl⟩ : syracuseStep 3638783 = 5458175) B5458175
theorem B7284329 : Blo 1437538 7284329 := bstep (se 2 (by rfl) ⟨2731623, by rfl⟩ : syracuseStep 7284329 = 5463247) B5463247
theorem B20752033 : Blo 1437538 20752033 := bstep (se 2 (by rfl) ⟨7782012, by rfl⟩ : syracuseStep 20752033 = 15564025) B15564025
theorem B3237551 : Blo 1437538 3237551 := bstep (se 1 (by rfl) ⟨2428163, by rfl⟩ : syracuseStep 3237551 = 4856327) B4856327
theorem B7775939 : Blo 1437538 7775939 := bstep (se 1 (by rfl) ⟨5831954, by rfl⟩ : syracuseStep 7775939 = 11663909) B11663909
theorem B2303911 : Blo 1437538 2303911 := bstep (se 1 (by rfl) ⟨1727933, by rfl⟩ : syracuseStep 2303911 = 3455867) B3455867
theorem B2729953 : Blo 1437538 2729953 := bstep (se 2 (by rfl) ⟨1023732, by rfl⟩ : syracuseStep 2729953 = 2047465) B2047465
theorem B3639289 : Blo 1437538 3639289 := bstep (se 2 (by rfl) ⟨1364733, by rfl⟩ : syracuseStep 3639289 = 2729467) B2729467
theorem B5834857 : Blo 1437538 5834857 := bstep (se 2 (by rfl) ⟨2188071, by rfl⟩ : syracuseStep 5834857 = 4376143) B4376143
theorem B3238055 : Blo 1437538 3238055 := bstep (se 1 (by rfl) ⟨2428541, by rfl⟩ : syracuseStep 3238055 = 4857083) B4857083
theorem B10373831 : Blo 1437538 10373831 := bstep (se 1 (by rfl) ⟨7780373, by rfl⟩ : syracuseStep 10373831 = 15560747) B15560747
theorem B3238631 : Blo 1437538 3238631 := bstep (se 1 (by rfl) ⟨2428973, by rfl⟩ : syracuseStep 3238631 = 4857947) B4857947
theorem B3238703 : Blo 1437538 3238703 := bstep (se 1 (by rfl) ⟨2429027, by rfl⟩ : syracuseStep 3238703 = 4858055) B4858055
theorem B26250281 : Blo 1437538 26250281 := bstep (se 2 (by rfl) ⟨9843855, by rfl⟩ : syracuseStep 26250281 = 19687711) B19687711
theorem B3640585 : Blo 1437538 3640585 := bstep (se 2 (by rfl) ⟨1365219, by rfl⟩ : syracuseStep 3640585 = 2730439) B2730439
theorem B7286111 : Blo 1437538 7286111 := bstep (se 1 (by rfl) ⟨5464583, by rfl⟩ : syracuseStep 7286111 = 10929167) B10929167
theorem B13307257 : Blo 1437538 13307257 := bstep (se 2 (by rfl) ⟨4990221, by rfl⟩ : syracuseStep 13307257 = 9980443) B9980443
theorem B3641071 : Blo 1437538 3641071 := bstep (se 1 (by rfl) ⟨2730803, by rfl⟩ : syracuseStep 3641071 = 5461607) B5461607
theorem B2158427 : Blo 1437538 2158427 := bstep (se 1 (by rfl) ⟨1618820, by rfl⟩ : syracuseStep 2158427 = 3237641) B3237641
theorem B12292033 : Blo 1437538 12292033 := bstep (se 2 (by rfl) ⟨4609512, by rfl⟩ : syracuseStep 12292033 = 9219025) B9219025
theorem B182087741 : Blo 1437538 182087741 := bstep (se 3 (by rfl) ⟨34141451, by rfl⟩ : syracuseStep 182087741 = 68282903) B68282903
theorem B2158655 : Blo 1437538 2158655 := bstep (se 1 (by rfl) ⟨1618991, by rfl⟩ : syracuseStep 2158655 = 3237983) B3237983
theorem B1437807 : Blo 1437538 1437807 := bstep (se 1 (by rfl) ⟨1078355, by rfl⟩ : syracuseStep 1437807 = 2156711) B2156711
theorem B13824233 : Blo 1437538 13824233 := bstep (se 2 (by rfl) ⟨5184087, by rfl⟩ : syracuseStep 13824233 = 10368175) B10368175
theorem B2158889 : Blo 1437538 2158889 := bstep (se 2 (by rfl) ⟨809583, by rfl⟩ : syracuseStep 2158889 = 1619167) B1619167
theorem B8196511 : Blo 1437538 8196511 := bstep (se 1 (by rfl) ⟨6147383, by rfl⟩ : syracuseStep 8196511 = 12294767) B12294767
theorem B7279145 : Blo 1437538 7279145 := bstep (se 2 (by rfl) ⟨2729679, by rfl⟩ : syracuseStep 7279145 = 5459359) B5459359
theorem B4854491 : Blo 1437538 4854491 := bstep (se 1 (by rfl) ⟨3640868, by rfl⟩ : syracuseStep 4854491 = 7281737) B7281737
theorem B1618663 : Blo 1437538 1618663 := bstep (se 1 (by rfl) ⟨1213997, by rfl⟩ : syracuseStep 1618663 = 2427995) B2427995
theorem B14766857 : Blo 1437538 14766857 := bstep (se 2 (by rfl) ⟨5537571, by rfl⟩ : syracuseStep 14766857 = 11075143) B11075143
theorem B95851565 : Blo 1437538 95851565 := bstep (se 3 (by rfl) ⟨17972168, by rfl⟩ : syracuseStep 95851565 = 35944337) B35944337
theorem B1438943 : Blo 1437538 1438943 := bstep (se 1 (by rfl) ⟨1079207, by rfl⟩ : syracuseStep 1438943 = 2158415) B2158415
theorem B1439003 : Blo 1437538 1439003 := bstep (se 1 (by rfl) ⟨1079252, by rfl⟩ : syracuseStep 1439003 = 2158505) B2158505
theorem B1439263 : Blo 1437538 1439263 := bstep (se 1 (by rfl) ⟨1079447, by rfl⟩ : syracuseStep 1439263 = 2158895) B2158895
theorem B31094765 : Blo 1437538 31094765 := bstep (se 3 (by rfl) ⟨5830268, by rfl⟩ : syracuseStep 31094765 = 11660537) B11660537
theorem B5462063 : Blo 1437538 5462063 := bstep (se 1 (by rfl) ⟨4096547, by rfl⟩ : syracuseStep 5462063 = 8193095) B8193095
theorem B23320871 : Blo 1437538 23320871 := bstep (se 1 (by rfl) ⟨17490653, by rfl⟩ : syracuseStep 23320871 = 34981307) B34981307
theorem B8198495 : Blo 1437538 8198495 := bstep (se 1 (by rfl) ⟨6148871, by rfl⟩ : syracuseStep 8198495 = 12297743) B12297743
theorem B7281089 : Blo 1437538 7281089 := bstep (se 2 (by rfl) ⟨2730408, by rfl⟩ : syracuseStep 7281089 = 5460817) B5460817
theorem B12450395 : Blo 1437538 12450395 := bstep (se 1 (by rfl) ⟨9337796, by rfl⟩ : syracuseStep 12450395 = 18675593) B18675593
theorem B2955919 : Blo 1437538 2955919 := bstep (se 1 (by rfl) ⟨2216939, by rfl⟩ : syracuseStep 2955919 = 4433879) B4433879
theorem B36846575 : Blo 1437538 36846575 := bstep (se 1 (by rfl) ⟨27634931, by rfl⟩ : syracuseStep 36846575 = 55269863) B55269863
theorem B5463065 : Blo 1437538 5463065 := bstep (se 2 (by rfl) ⟨2048649, by rfl⟩ : syracuseStep 5463065 = 4097299) B4097299
theorem B20733353 : Blo 1437538 20733353 := bstep (se 2 (by rfl) ⟨7775007, by rfl⟩ : syracuseStep 20733353 = 15550015) B15550015
theorem B5537279 : Blo 1437538 5537279 := bstep (se 1 (by rfl) ⟨4152959, by rfl⟩ : syracuseStep 5537279 = 8305919) B8305919
theorem B10370713 : Blo 1437538 10370713 := bstep (se 2 (by rfl) ⟨3889017, by rfl⟩ : syracuseStep 10370713 = 7778035) B7778035
theorem B29523689 : Blo 1437538 29523689 := bstep (se 2 (by rfl) ⟨11071383, by rfl⟩ : syracuseStep 29523689 = 22142767) B22142767
theorem B2047727 : Blo 1437538 2047727 := bstep (se 1 (by rfl) ⟨1535795, by rfl⟩ : syracuseStep 2047727 = 3071591) B3071591
theorem B3235823 : Blo 1437538 3235823 := bstep (se 1 (by rfl) ⟨2426867, by rfl⟩ : syracuseStep 3235823 = 4853735) B4853735
theorem B9216155 : Blo 1437538 9216155 := bstep (se 1 (by rfl) ⟨6912116, by rfl⟩ : syracuseStep 9216155 = 13824233) B13824233
theorem B3236327 : Blo 1437538 3236327 := bstep (se 1 (by rfl) ⟨2427245, by rfl⟩ : syracuseStep 3236327 = 4854491) B4854491
theorem B10928681 : Blo 1437538 10928681 := bstep (se 2 (by rfl) ⟨4098255, by rfl⟩ : syracuseStep 10928681 = 8196511) B8196511
theorem B3941225 : Blo 1437538 3941225 := bstep (se 2 (by rfl) ⟨1477959, by rfl⟩ : syracuseStep 3941225 = 2955919) B2955919
theorem B2425855 : Blo 1437538 2425855 := bstep (se 1 (by rfl) ⟨1819391, by rfl⟩ : syracuseStep 2425855 = 3638783) B3638783
theorem B5465663 : Blo 1437538 5465663 := bstep (se 1 (by rfl) ⟨4099247, by rfl⟩ : syracuseStep 5465663 = 8198495) B8198495
theorem B6915887 : Blo 1437538 6915887 := bstep (se 1 (by rfl) ⟨5186915, by rfl⟩ : syracuseStep 6915887 = 10373831) B10373831
theorem B20735837 : Blo 1437538 20735837 := bstep (se 3 (by rfl) ⟨3887969, by rfl⟩ : syracuseStep 20735837 = 7775939) B7775939
theorem B17500187 : Blo 1437538 17500187 := bstep (se 1 (by rfl) ⟨13125140, by rfl⟩ : syracuseStep 17500187 = 26250281) B26250281
theorem B13822235 : Blo 1437538 13822235 := bstep (se 1 (by rfl) ⟨10366676, by rfl⟩ : syracuseStep 13822235 = 20733353) B20733353
theorem B3639937 : Blo 1437538 3639937 := bstep (se 2 (by rfl) ⟨1364976, by rfl⟩ : syracuseStep 3639937 = 2729953) B2729953
theorem B2157215 : Blo 1437538 2157215 := bstep (se 1 (by rfl) ⟨1617911, by rfl⟩ : syracuseStep 2157215 = 3235823) B3235823
theorem B4852385 : Blo 1437538 4852385 := bstep (se 2 (by rfl) ⟨1819644, by rfl⟩ : syracuseStep 4852385 = 3639289) B3639289
theorem B121391827 : Blo 1437538 121391827 := bstep (se 1 (by rfl) ⟨91043870, by rfl⟩ : syracuseStep 121391827 = 182087741) B182087741
theorem B16395209 : Blo 1437538 16395209 := bstep (se 2 (by rfl) ⟨6148203, by rfl⟩ : syracuseStep 16395209 = 12296407) B12296407
theorem B4852763 : Blo 1437538 4852763 := bstep (se 1 (by rfl) ⟨3639572, by rfl⟩ : syracuseStep 4852763 = 7279145) B7279145
theorem B2157695 : Blo 1437538 2157695 := bstep (se 1 (by rfl) ⟨1618271, by rfl⟩ : syracuseStep 2157695 = 3236543) B3236543
theorem B2157887 : Blo 1437538 2157887 := bstep (se 1 (by rfl) ⟨1618415, by rfl⟩ : syracuseStep 2157887 = 3236831) B3236831
theorem B63901043 : Blo 1437538 63901043 := bstep (se 1 (by rfl) ⟨47925782, by rfl⟩ : syracuseStep 63901043 = 95851565) B95851565
theorem B7777691 : Blo 1437538 7777691 := bstep (se 1 (by rfl) ⟨5833268, by rfl⟩ : syracuseStep 7777691 = 11666537) B11666537
theorem B2157983 : Blo 1437538 2157983 := bstep (se 1 (by rfl) ⟨1618487, by rfl⟩ : syracuseStep 2157983 = 3236975) B3236975
theorem B2158217 : Blo 1437538 2158217 := bstep (se 2 (by rfl) ⟨809331, by rfl⟩ : syracuseStep 2158217 = 1618663) B1618663
theorem B2158367 : Blo 1437538 2158367 := bstep (se 1 (by rfl) ⟨1618775, by rfl⟩ : syracuseStep 2158367 = 3237551) B3237551
theorem B20729843 : Blo 1437538 20729843 := bstep (se 1 (by rfl) ⟨15547382, by rfl⟩ : syracuseStep 20729843 = 31094765) B31094765
theorem B14766077 : Blo 1437538 14766077 := bstep (se 3 (by rfl) ⟨2768639, by rfl⟩ : syracuseStep 14766077 = 5537279) B5537279
theorem B3641375 : Blo 1437538 3641375 := bstep (se 1 (by rfl) ⟨2731031, by rfl⟩ : syracuseStep 3641375 = 5462063) B5462063
theorem B2158703 : Blo 1437538 2158703 := bstep (se 1 (by rfl) ⟨1619027, by rfl⟩ : syracuseStep 2158703 = 3238055) B3238055
theorem B4854059 : Blo 1437538 4854059 := bstep (se 1 (by rfl) ⟨3640544, by rfl⟩ : syracuseStep 4854059 = 7281089) B7281089
theorem B4854113 : Blo 1437538 4854113 := bstep (se 2 (by rfl) ⟨1820292, by rfl⟩ : syracuseStep 4854113 = 3640585) B3640585
theorem B2159087 : Blo 1437538 2159087 := bstep (se 1 (by rfl) ⟨1619315, by rfl⟩ : syracuseStep 2159087 = 3238631) B3238631
theorem B2159135 : Blo 1437538 2159135 := bstep (se 1 (by rfl) ⟨1619351, by rfl⟩ : syracuseStep 2159135 = 3238703) B3238703
theorem B5460605 : Blo 1437538 5460605 := bstep (se 3 (by rfl) ⟨1023863, by rfl⟩ : syracuseStep 5460605 = 2047727) B2047727
theorem B24564383 : Blo 1437538 24564383 := bstep (se 1 (by rfl) ⟨18423287, by rfl⟩ : syracuseStep 24564383 = 36846575) B36846575
theorem B3642043 : Blo 1437538 3642043 := bstep (se 1 (by rfl) ⟨2731532, by rfl⟩ : syracuseStep 3642043 = 5463065) B5463065
theorem B27669377 : Blo 1437538 27669377 := bstep (se 2 (by rfl) ⟨10376016, by rfl⟩ : syracuseStep 27669377 = 20752033) B20752033
theorem B4854761 : Blo 1437538 4854761 := bstep (se 2 (by rfl) ⟨1820535, by rfl⟩ : syracuseStep 4854761 = 3641071) B3641071
theorem B19682459 : Blo 1437538 19682459 := bstep (se 1 (by rfl) ⟨14761844, by rfl⟩ : syracuseStep 19682459 = 29523689) B29523689
theorem B1438951 : Blo 1437538 1438951 := bstep (se 1 (by rfl) ⟨1079213, by rfl⟩ : syracuseStep 1438951 = 2158427) B2158427
theorem B16389377 : Blo 1437538 16389377 := bstep (se 2 (by rfl) ⟨6146016, by rfl⟩ : syracuseStep 16389377 = 12292033) B12292033
theorem B1439103 : Blo 1437538 1439103 := bstep (se 1 (by rfl) ⟨1079327, by rfl⟩ : syracuseStep 1439103 = 2158655) B2158655
theorem B7779809 : Blo 1437538 7779809 := bstep (se 2 (by rfl) ⟨2917428, by rfl⟩ : syracuseStep 7779809 = 5834857) B5834857
theorem B1439259 : Blo 1437538 1439259 := bstep (se 1 (by rfl) ⟨1079444, by rfl⟩ : syracuseStep 1439259 = 2158889) B2158889
theorem B9844571 : Blo 1437538 9844571 := bstep (se 1 (by rfl) ⟨7383428, by rfl⟩ : syracuseStep 9844571 = 14766857) B14766857
theorem B29546369 : Blo 1437538 29546369 := bstep (se 2 (by rfl) ⟨11079888, by rfl⟩ : syracuseStep 29546369 = 22159777) B22159777
theorem B29546849 : Blo 1437538 29546849 := bstep (se 2 (by rfl) ⟨11080068, by rfl⟩ : syracuseStep 29546849 = 22160137) B22160137
theorem B4856219 : Blo 1437538 4856219 := bstep (se 1 (by rfl) ⟨3642164, by rfl⟩ : syracuseStep 4856219 = 7284329) B7284329
theorem B15547247 : Blo 1437538 15547247 := bstep (se 1 (by rfl) ⟨11660435, by rfl⟩ : syracuseStep 15547247 = 23320871) B23320871
theorem B33201053 : Blo 1437538 33201053 := bstep (se 3 (by rfl) ⟨6225197, by rfl⟩ : syracuseStep 33201053 = 12450395) B12450395
theorem B17743009 : Blo 1437538 17743009 := bstep (se 2 (by rfl) ⟨6653628, by rfl⟩ : syracuseStep 17743009 = 13307257) B13307257
theorem B13827617 : Blo 1437538 13827617 := bstep (se 2 (by rfl) ⟨5185356, by rfl⟩ : syracuseStep 13827617 = 10370713) B10370713
theorem B4857407 : Blo 1437538 4857407 := bstep (se 1 (by rfl) ⟨3643055, by rfl⟩ : syracuseStep 4857407 = 7286111) B7286111
theorem B3071881 : Blo 1437538 3071881 := bstep (se 2 (by rfl) ⟨1151955, by rfl⟩ : syracuseStep 3071881 = 2303911) B2303911
theorem B6144103 : Blo 1437538 6144103 := bstep (se 1 (by rfl) ⟨4608077, by rfl⟩ : syracuseStep 6144103 = 9216155) B9216155
theorem B3236039 : Blo 1437538 3236039 := bstep (se 1 (by rfl) ⟨2427029, by rfl⟩ : syracuseStep 3236039 = 4854059) B4854059
theorem B3236075 : Blo 1437538 3236075 := bstep (se 1 (by rfl) ⟨2427056, by rfl⟩ : syracuseStep 3236075 = 4854113) B4854113
theorem B16376255 : Blo 1437538 16376255 := bstep (se 1 (by rfl) ⟨12282191, by rfl⟩ : syracuseStep 16376255 = 24564383) B24564383
theorem B3236507 : Blo 1437538 3236507 := bstep (se 1 (by rfl) ⟨2427380, by rfl⟩ : syracuseStep 3236507 = 4854761) B4854761
theorem B5186539 : Blo 1437538 5186539 := bstep (se 1 (by rfl) ⟨3889904, by rfl⟩ : syracuseStep 5186539 = 7779809) B7779809
theorem B647423077 : Blo 1437538 647423077 := bstep (se 4 (by rfl) ⟨60695913, by rfl⟩ : syracuseStep 647423077 = 121391827) B121391827
theorem B6563047 : Blo 1437538 6563047 := bstep (se 1 (by rfl) ⟨4922285, by rfl⟩ : syracuseStep 6563047 = 9844571) B9844571
theorem B11666791 : Blo 1437538 11666791 := bstep (se 1 (by rfl) ⟨8750093, by rfl⟩ : syracuseStep 11666791 = 17500187) B17500187
theorem B3237479 : Blo 1437538 3237479 := bstep (se 1 (by rfl) ⟨2428109, by rfl⟩ : syracuseStep 3237479 = 4856219) B4856219
theorem B10364831 : Blo 1437538 10364831 := bstep (se 1 (by rfl) ⟨7773623, by rfl⟩ : syracuseStep 10364831 = 15547247) B15547247
theorem B10930139 : Blo 1437538 10930139 := bstep (se 1 (by rfl) ⟨8197604, by rfl⟩ : syracuseStep 10930139 = 16395209) B16395209
theorem B42600695 : Blo 1437538 42600695 := bstep (se 1 (by rfl) ⟨31950521, by rfl⟩ : syracuseStep 42600695 = 63901043) B63901043
theorem B9218411 : Blo 1437538 9218411 := bstep (se 1 (by rfl) ⟨6913808, by rfl⟩ : syracuseStep 9218411 = 13827617) B13827617
theorem B3238271 : Blo 1437538 3238271 := bstep (se 1 (by rfl) ⟨2428703, by rfl⟩ : syracuseStep 3238271 = 4857407) B4857407
theorem B2427583 : Blo 1437538 2427583 := bstep (se 1 (by rfl) ⟨1820687, by rfl⟩ : syracuseStep 2427583 = 3641375) B3641375
theorem B2157551 : Blo 1437538 2157551 := bstep (se 1 (by rfl) ⟨1618163, by rfl⟩ : syracuseStep 2157551 = 3236327) B3236327
theorem B7285787 : Blo 1437538 7285787 := bstep (se 1 (by rfl) ⟨5464340, by rfl⟩ : syracuseStep 7285787 = 10928681) B10928681
theorem B3640403 : Blo 1437538 3640403 := bstep (se 1 (by rfl) ⟨2730302, by rfl⟩ : syracuseStep 3640403 = 5460605) B5460605
theorem B4853249 : Blo 1437538 4853249 := bstep (se 2 (by rfl) ⟨1819968, by rfl⟩ : syracuseStep 4853249 = 3639937) B3639937
theorem B13823891 : Blo 1437538 13823891 := bstep (se 1 (by rfl) ⟨10367918, by rfl⟩ : syracuseStep 13823891 = 20735837) B20735837
theorem B19697579 : Blo 1437538 19697579 := bstep (se 1 (by rfl) ⟨14773184, by rfl⟩ : syracuseStep 19697579 = 29546369) B29546369
theorem B19697899 : Blo 1437538 19697899 := bstep (se 1 (by rfl) ⟨14773424, by rfl⟩ : syracuseStep 19697899 = 29546849) B29546849
theorem B1438143 : Blo 1437538 1438143 := bstep (se 1 (by rfl) ⟨1078607, by rfl⟩ : syracuseStep 1438143 = 2157215) B2157215
theorem B1438463 : Blo 1437538 1438463 := bstep (se 1 (by rfl) ⟨1078847, by rfl⟩ : syracuseStep 1438463 = 2157695) B2157695
theorem B1438591 : Blo 1437538 1438591 := bstep (se 1 (by rfl) ⟨1078943, by rfl⟩ : syracuseStep 1438591 = 2157887) B2157887
theorem B1438655 : Blo 1437538 1438655 := bstep (se 1 (by rfl) ⟨1078991, by rfl⟩ : syracuseStep 1438655 = 2157983) B2157983
theorem B1438811 : Blo 1437538 1438811 := bstep (se 1 (by rfl) ⟨1079108, by rfl⟩ : syracuseStep 1438811 = 2158217) B2158217
theorem B1438911 : Blo 1437538 1438911 := bstep (se 1 (by rfl) ⟨1079183, by rfl⟩ : syracuseStep 1438911 = 2158367) B2158367
theorem B39376205 : Blo 1437538 39376205 := bstep (se 3 (by rfl) ⟨7383038, by rfl⟩ : syracuseStep 39376205 = 14766077) B14766077
theorem B1439135 : Blo 1437538 1439135 := bstep (se 1 (by rfl) ⟨1079351, by rfl⟩ : syracuseStep 1439135 = 2158703) B2158703
theorem B1439391 : Blo 1437538 1439391 := bstep (se 1 (by rfl) ⟨1079543, by rfl⟩ : syracuseStep 1439391 = 2159087) B2159087
theorem B1439423 : Blo 1437538 1439423 := bstep (se 1 (by rfl) ⟨1079567, by rfl⟩ : syracuseStep 1439423 = 2159135) B2159135
theorem B2627483 : Blo 1437538 2627483 := bstep (se 1 (by rfl) ⟨1970612, by rfl⟩ : syracuseStep 2627483 = 3941225) B3941225
theorem B18446251 : Blo 1437538 18446251 := bstep (se 1 (by rfl) ⟨13834688, by rfl⟩ : syracuseStep 18446251 = 27669377) B27669377
theorem B13121639 : Blo 1437538 13121639 := bstep (se 1 (by rfl) ⟨9841229, by rfl⟩ : syracuseStep 13121639 = 19682459) B19682459
theorem B10926251 : Blo 1437538 10926251 := bstep (se 1 (by rfl) ⟨8194688, by rfl⟩ : syracuseStep 10926251 = 16389377) B16389377
theorem B4856057 : Blo 1437538 4856057 := bstep (se 2 (by rfl) ⟨1821021, by rfl⟩ : syracuseStep 4856057 = 3642043) B3642043
theorem B3643775 : Blo 1437538 3643775 := bstep (se 1 (by rfl) ⟨2732831, by rfl⟩ : syracuseStep 3643775 = 5465663) B5465663
theorem B4610591 : Blo 1437538 4610591 := bstep (se 1 (by rfl) ⟨3457943, by rfl⟩ : syracuseStep 4610591 = 6915887) B6915887
theorem B3234473 : Blo 1437538 3234473 := bstep (se 2 (by rfl) ⟨1212927, by rfl⟩ : syracuseStep 3234473 = 2425855) B2425855
theorem B9214823 : Blo 1437538 9214823 := bstep (se 1 (by rfl) ⟨6911117, by rfl⟩ : syracuseStep 9214823 = 13822235) B13822235
theorem B23657345 : Blo 1437538 23657345 := bstep (se 2 (by rfl) ⟨8871504, by rfl⟩ : syracuseStep 23657345 = 17743009) B17743009
theorem B3234923 : Blo 1437538 3234923 := bstep (se 1 (by rfl) ⟨2426192, by rfl⟩ : syracuseStep 3234923 = 4852385) B4852385
theorem B22134035 : Blo 1437538 22134035 := bstep (se 1 (by rfl) ⟨16600526, by rfl⟩ : syracuseStep 22134035 = 33201053) B33201053
theorem B3235175 : Blo 1437538 3235175 := bstep (se 1 (by rfl) ⟨2426381, by rfl⟩ : syracuseStep 3235175 = 4852763) B4852763
theorem B5185127 : Blo 1437538 5185127 := bstep (se 1 (by rfl) ⟨3888845, by rfl⟩ : syracuseStep 5185127 = 7777691) B7777691
theorem B4095841 : Blo 1437538 4095841 := bstep (se 2 (by rfl) ⟨1535940, by rfl⟩ : syracuseStep 4095841 = 3071881) B3071881
theorem B13819895 : Blo 1437538 13819895 := bstep (se 1 (by rfl) ⟨10364921, by rfl⟩ : syracuseStep 13819895 = 20729843) B20729843
theorem B8192137 : Blo 1437538 8192137 := bstep (se 2 (by rfl) ⟨3072051, by rfl⟩ : syracuseStep 8192137 = 6144103) B6144103
theorem B26263865 : Blo 1437538 26263865 := bstep (se 2 (by rfl) ⟨9848949, by rfl⟩ : syracuseStep 26263865 = 19697899) B19697899
theorem B3236777 : Blo 1437538 3236777 := bstep (se 2 (by rfl) ⟨1213791, by rfl⟩ : syracuseStep 3236777 = 2427583) B2427583
theorem B6915385 : Blo 1437538 6915385 := bstep (se 2 (by rfl) ⟨2593269, by rfl⟩ : syracuseStep 6915385 = 5186539) B5186539
theorem B7284167 : Blo 1437538 7284167 := bstep (se 1 (by rfl) ⟨5463125, by rfl⟩ : syracuseStep 7284167 = 10926251) B10926251
theorem B3237371 : Blo 1437538 3237371 := bstep (se 1 (by rfl) ⟨2428028, by rfl⟩ : syracuseStep 3237371 = 4856057) B4856057
theorem B6145607 : Blo 1437538 6145607 := bstep (se 1 (by rfl) ⟨4609205, by rfl⟩ : syracuseStep 6145607 = 9218411) B9218411
theorem B8750729 : Blo 1437538 8750729 := bstep (se 2 (by rfl) ⟨3281523, by rfl⟩ : syracuseStep 8750729 = 6563047) B6563047
theorem B3073727 : Blo 1437538 3073727 := bstep (se 1 (by rfl) ⟨2305295, by rfl⟩ : syracuseStep 3073727 = 4610591) B4610591
theorem B2156315 : Blo 1437538 2156315 := bstep (se 1 (by rfl) ⟨1617236, by rfl⟩ : syracuseStep 2156315 = 3234473) B3234473
theorem B15771563 : Blo 1437538 15771563 := bstep (se 1 (by rfl) ⟨11828672, by rfl⟩ : syracuseStep 15771563 = 23657345) B23657345
theorem B2426935 : Blo 1437538 2426935 := bstep (se 1 (by rfl) ⟨1820201, by rfl⟩ : syracuseStep 2426935 = 3640403) B3640403
theorem B2156615 : Blo 1437538 2156615 := bstep (se 1 (by rfl) ⟨1617461, by rfl⟩ : syracuseStep 2156615 = 3234923) B3234923
theorem B14756023 : Blo 1437538 14756023 := bstep (se 1 (by rfl) ⟨11067017, by rfl⟩ : syracuseStep 14756023 = 22134035) B22134035
theorem B2156783 : Blo 1437538 2156783 := bstep (se 1 (by rfl) ⟨1617587, by rfl⟩ : syracuseStep 2156783 = 3235175) B3235175
theorem B7006621 : Blo 1437538 7006621 := bstep (se 3 (by rfl) ⟨1313741, by rfl⟩ : syracuseStep 7006621 = 2627483) B2627483
theorem B24595001 : Blo 1437538 24595001 := bstep (se 2 (by rfl) ⟨9223125, by rfl⟩ : syracuseStep 24595001 = 18446251) B18446251
theorem B2157359 : Blo 1437538 2157359 := bstep (se 1 (by rfl) ⟨1618019, by rfl⟩ : syracuseStep 2157359 = 3236039) B3236039
theorem B2157383 : Blo 1437538 2157383 := bstep (se 1 (by rfl) ⟨1618037, by rfl⟩ : syracuseStep 2157383 = 3236075) B3236075
theorem B2157671 : Blo 1437538 2157671 := bstep (se 1 (by rfl) ⟨1618253, by rfl⟩ : syracuseStep 2157671 = 3236507) B3236507
theorem B113601853 : Blo 1437538 113601853 := bstep (se 3 (by rfl) ⟨21300347, by rfl⟩ : syracuseStep 113601853 = 42600695) B42600695
theorem B26250803 : Blo 1437538 26250803 := bstep (se 1 (by rfl) ⟨19688102, by rfl⟩ : syracuseStep 26250803 = 39376205) B39376205
theorem B2158319 : Blo 1437538 2158319 := bstep (se 1 (by rfl) ⟨1618739, by rfl⟩ : syracuseStep 2158319 = 3237479) B3237479
theorem B6909887 : Blo 1437538 6909887 := bstep (se 1 (by rfl) ⟨5182415, by rfl⟩ : syracuseStep 6909887 = 10364831) B10364831
theorem B7286759 : Blo 1437538 7286759 := bstep (se 1 (by rfl) ⟨5465069, by rfl⟩ : syracuseStep 7286759 = 10930139) B10930139
theorem B2158847 : Blo 1437538 2158847 := bstep (se 1 (by rfl) ⟨1619135, by rfl⟩ : syracuseStep 2158847 = 3238271) B3238271
theorem B2429183 : Blo 1437538 2429183 := bstep (se 1 (by rfl) ⟨1821887, by rfl⟩ : syracuseStep 2429183 = 3643775) B3643775
theorem B1438367 : Blo 1437538 1438367 := bstep (se 1 (by rfl) ⟨1078775, by rfl⟩ : syracuseStep 1438367 = 2157551) B2157551
theorem B5461121 : Blo 1437538 5461121 := bstep (se 2 (by rfl) ⟨2047920, by rfl⟩ : syracuseStep 5461121 = 4095841) B4095841
theorem B9213263 : Blo 1437538 9213263 := bstep (se 1 (by rfl) ⟨6909947, by rfl⟩ : syracuseStep 9213263 = 13819895) B13819895
theorem B10917503 : Blo 1437538 10917503 := bstep (se 1 (by rfl) ⟨8188127, by rfl⟩ : syracuseStep 10917503 = 16376255) B16376255
theorem B8747759 : Blo 1437538 8747759 := bstep (se 1 (by rfl) ⟨6560819, by rfl⟩ : syracuseStep 8747759 = 13121639) B13121639
theorem B863230769 : Blo 1437538 863230769 := bstep (se 2 (by rfl) ⟨323711538, by rfl⟩ : syracuseStep 863230769 = 647423077) B647423077
theorem B15555721 : Blo 1437538 15555721 := bstep (se 2 (by rfl) ⟨5833395, by rfl⟩ : syracuseStep 15555721 = 11666791) B11666791
theorem B6143215 : Blo 1437538 6143215 := bstep (se 1 (by rfl) ⟨4607411, by rfl⟩ : syracuseStep 6143215 = 9214823) B9214823
theorem B4857191 : Blo 1437538 4857191 := bstep (se 1 (by rfl) ⟨3642893, by rfl⟩ : syracuseStep 4857191 = 7285787) B7285787
theorem B3235499 : Blo 1437538 3235499 := bstep (se 1 (by rfl) ⟨2426624, by rfl⟩ : syracuseStep 3235499 = 4853249) B4853249
theorem B3456751 : Blo 1437538 3456751 := bstep (se 1 (by rfl) ⟨2592563, by rfl⟩ : syracuseStep 3456751 = 5185127) B5185127
theorem B9215927 : Blo 1437538 9215927 := bstep (se 1 (by rfl) ⟨6911945, by rfl⟩ : syracuseStep 9215927 = 13823891) B13823891
theorem B13131719 : Blo 1437538 13131719 := bstep (se 1 (by rfl) ⟨9848789, by rfl⟩ : syracuseStep 13131719 = 19697579) B19697579
theorem B3235913 : Blo 1437538 3235913 := bstep (se 2 (by rfl) ⟨1213467, by rfl⟩ : syracuseStep 3235913 = 2426935) B2426935
theorem B4097071 : Blo 1437538 4097071 := bstep (se 1 (by rfl) ⟨3072803, by rfl⟩ : syracuseStep 4097071 = 6145607) B6145607
theorem B5833819 : Blo 1437538 5833819 := bstep (se 1 (by rfl) ⟨4375364, by rfl⟩ : syracuseStep 5833819 = 8750729) B8750729
theorem B2049151 : Blo 1437538 2049151 := bstep (se 1 (by rfl) ⟨1536863, by rfl⟩ : syracuseStep 2049151 = 3073727) B3073727
theorem B3238127 : Blo 1437538 3238127 := bstep (se 1 (by rfl) ⟨2428595, by rfl⟩ : syracuseStep 3238127 = 4857191) B4857191
theorem B17500535 : Blo 1437538 17500535 := bstep (se 1 (by rfl) ⟨13125401, by rfl⟩ : syracuseStep 17500535 = 26250803) B26250803
theorem B2156999 : Blo 1437538 2156999 := bstep (se 1 (by rfl) ⟨1617749, by rfl⟩ : syracuseStep 2156999 = 3235499) B3235499
theorem B18426365 : Blo 1437538 18426365 := bstep (se 3 (by rfl) ⟨3454943, by rfl⟩ : syracuseStep 18426365 = 6909887) B6909887
theorem B10922849 : Blo 1437538 10922849 := bstep (se 2 (by rfl) ⟨4096068, by rfl⟩ : syracuseStep 10922849 = 8192137) B8192137
theorem B17509243 : Blo 1437538 17509243 := bstep (se 1 (by rfl) ⟨13131932, by rfl⟩ : syracuseStep 17509243 = 26263865) B26263865
theorem B9342161 : Blo 1437538 9342161 := bstep (se 2 (by rfl) ⟨3503310, by rfl⟩ : syracuseStep 9342161 = 7006621) B7006621
theorem B2157851 : Blo 1437538 2157851 := bstep (se 1 (by rfl) ⟨1618388, by rfl⟩ : syracuseStep 2157851 = 3236777) B3236777
theorem B3640747 : Blo 1437538 3640747 := bstep (se 1 (by rfl) ⟨2730560, by rfl⟩ : syracuseStep 3640747 = 5461121) B5461121
theorem B2158247 : Blo 1437538 2158247 := bstep (se 1 (by rfl) ⟨1618685, by rfl⟩ : syracuseStep 2158247 = 3237371) B3237371
theorem B7278335 : Blo 1437538 7278335 := bstep (se 1 (by rfl) ⟨5458751, by rfl⟩ : syracuseStep 7278335 = 10917503) B10917503
theorem B1437543 : Blo 1437538 1437543 := bstep (se 1 (by rfl) ⟨1078157, by rfl⟩ : syracuseStep 1437543 = 2156315) B2156315
theorem B10514375 : Blo 1437538 10514375 := bstep (se 1 (by rfl) ⟨7885781, by rfl⟩ : syracuseStep 10514375 = 15771563) B15771563
theorem B1437743 : Blo 1437538 1437743 := bstep (se 1 (by rfl) ⟨1078307, by rfl⟩ : syracuseStep 1437743 = 2156615) B2156615
theorem B1437855 : Blo 1437538 1437855 := bstep (se 1 (by rfl) ⟨1078391, by rfl⟩ : syracuseStep 1437855 = 2156783) B2156783
theorem B16396667 : Blo 1437538 16396667 := bstep (se 1 (by rfl) ⟨12297500, by rfl⟩ : syracuseStep 16396667 = 24595001) B24595001
theorem B9220513 : Blo 1437538 9220513 := bstep (se 2 (by rfl) ⟨3457692, by rfl⟩ : syracuseStep 9220513 = 6915385) B6915385
theorem B1438239 : Blo 1437538 1438239 := bstep (se 1 (by rfl) ⟨1078679, by rfl⟩ : syracuseStep 1438239 = 2157359) B2157359
theorem B1438255 : Blo 1437538 1438255 := bstep (se 1 (by rfl) ⟨1078691, by rfl⟩ : syracuseStep 1438255 = 2157383) B2157383
theorem B1438447 : Blo 1437538 1438447 := bstep (se 1 (by rfl) ⟨1078835, by rfl⟩ : syracuseStep 1438447 = 2157671) B2157671
theorem B4609001 : Blo 1437538 4609001 := bstep (se 2 (by rfl) ⟨1728375, by rfl⟩ : syracuseStep 4609001 = 3456751) B3456751
theorem B1438879 : Blo 1437538 1438879 := bstep (se 1 (by rfl) ⟨1079159, by rfl⟩ : syracuseStep 1438879 = 2158319) B2158319
theorem B8754479 : Blo 1437538 8754479 := bstep (se 1 (by rfl) ⟨6565859, by rfl⟩ : syracuseStep 8754479 = 13131719) B13131719
theorem B1439231 : Blo 1437538 1439231 := bstep (se 1 (by rfl) ⟨1079423, by rfl⟩ : syracuseStep 1439231 = 2158847) B2158847
theorem B1619455 : Blo 1437538 1619455 := bstep (se 1 (by rfl) ⟨1214591, by rfl⟩ : syracuseStep 1619455 = 2429183) B2429183
theorem B19674697 : Blo 1437538 19674697 := bstep (se 2 (by rfl) ⟨7378011, by rfl⟩ : syracuseStep 19674697 = 14756023) B14756023
theorem B6142175 : Blo 1437538 6142175 := bstep (se 1 (by rfl) ⟨4606631, by rfl⟩ : syracuseStep 6142175 = 9213263) B9213263
theorem B4856111 : Blo 1437538 4856111 := bstep (se 1 (by rfl) ⟨3642083, by rfl⟩ : syracuseStep 4856111 = 7284167) B7284167
theorem B20740961 : Blo 1437538 20740961 := bstep (se 2 (by rfl) ⟨7777860, by rfl⟩ : syracuseStep 20740961 = 15555721) B15555721
theorem B8190953 : Blo 1437538 8190953 := bstep (se 2 (by rfl) ⟨3071607, by rfl⟩ : syracuseStep 8190953 = 6143215) B6143215
theorem B151469137 : Blo 1437538 151469137 := bstep (se 2 (by rfl) ⟨56800926, by rfl⟩ : syracuseStep 151469137 = 113601853) B113601853
theorem B5831839 : Blo 1437538 5831839 := bstep (se 1 (by rfl) ⟨4373879, by rfl⟩ : syracuseStep 5831839 = 8747759) B8747759
theorem B575487179 : Blo 1437538 575487179 := bstep (se 1 (by rfl) ⟨431615384, by rfl⟩ : syracuseStep 575487179 = 863230769) B863230769
theorem B6143951 : Blo 1437538 6143951 := bstep (se 1 (by rfl) ⟨4607963, by rfl⟩ : syracuseStep 6143951 = 9215927) B9215927
theorem B4857839 : Blo 1437538 4857839 := bstep (se 1 (by rfl) ⟨3643379, by rfl⟩ : syracuseStep 4857839 = 7286759) B7286759
theorem B3072667 : Blo 1437538 3072667 := bstep (se 1 (by rfl) ⟨2304500, by rfl⟩ : syracuseStep 3072667 = 4609001) B4609001
theorem B201958849 : Blo 1437538 201958849 := bstep (se 2 (by rfl) ⟨75734568, by rfl⟩ : syracuseStep 201958849 = 151469137) B151469137
theorem B3237407 : Blo 1437538 3237407 := bstep (se 1 (by rfl) ⟨2428055, by rfl⟩ : syracuseStep 3237407 = 4856111) B4856111
theorem B7775785 : Blo 1437538 7775785 := bstep (se 2 (by rfl) ⟨2915919, by rfl⟩ : syracuseStep 7775785 = 5831839) B5831839
theorem B11667023 : Blo 1437538 11667023 := bstep (se 1 (by rfl) ⟨8750267, by rfl⟩ : syracuseStep 11667023 = 17500535) B17500535
theorem B26232929 : Blo 1437538 26232929 := bstep (se 2 (by rfl) ⟨9837348, by rfl⟩ : syracuseStep 26232929 = 19674697) B19674697
theorem B6228107 : Blo 1437538 6228107 := bstep (se 1 (by rfl) ⟨4671080, by rfl⟩ : syracuseStep 6228107 = 9342161) B9342161
theorem B383658119 : Blo 1437538 383658119 := bstep (se 1 (by rfl) ⟨287743589, by rfl⟩ : syracuseStep 383658119 = 575487179) B575487179
theorem B4852223 : Blo 1437538 4852223 := bstep (se 1 (by rfl) ⟨3639167, by rfl⟩ : syracuseStep 4852223 = 7278335) B7278335
theorem B3238559 : Blo 1437538 3238559 := bstep (se 1 (by rfl) ⟨2428919, by rfl⟩ : syracuseStep 3238559 = 4857839) B4857839
theorem B2157275 : Blo 1437538 2157275 := bstep (se 1 (by rfl) ⟨1617956, by rfl⟩ : syracuseStep 2157275 = 3235913) B3235913
theorem B10931111 : Blo 1437538 10931111 := bstep (se 1 (by rfl) ⟨8198333, by rfl⟩ : syracuseStep 10931111 = 16396667) B16396667
theorem B5836319 : Blo 1437538 5836319 := bstep (se 1 (by rfl) ⟨4377239, by rfl⟩ : syracuseStep 5836319 = 8754479) B8754479
theorem B7778425 : Blo 1437538 7778425 := bstep (se 2 (by rfl) ⟨2916909, by rfl⟩ : syracuseStep 7778425 = 5833819) B5833819
theorem B2158751 : Blo 1437538 2158751 := bstep (se 1 (by rfl) ⟨1619063, by rfl⟩ : syracuseStep 2158751 = 3238127) B3238127
theorem B2732201 : Blo 1437538 2732201 := bstep (se 2 (by rfl) ⟨1024575, by rfl⟩ : syracuseStep 2732201 = 2049151) B2049151
theorem B1437999 : Blo 1437538 1437999 := bstep (se 1 (by rfl) ⟨1078499, by rfl⟩ : syracuseStep 1437999 = 2156999) B2156999
theorem B12284243 : Blo 1437538 12284243 := bstep (se 1 (by rfl) ⟨9213182, by rfl⟩ : syracuseStep 12284243 = 18426365) B18426365
theorem B4854329 : Blo 1437538 4854329 := bstep (se 2 (by rfl) ⟨1820373, by rfl⟩ : syracuseStep 4854329 = 3640747) B3640747
theorem B5460635 : Blo 1437538 5460635 := bstep (se 1 (by rfl) ⟨4095476, by rfl⟩ : syracuseStep 5460635 = 8190953) B8190953
theorem B2159273 : Blo 1437538 2159273 := bstep (se 2 (by rfl) ⟨809727, by rfl⟩ : syracuseStep 2159273 = 1619455) B1619455
theorem B1438567 : Blo 1437538 1438567 := bstep (se 1 (by rfl) ⟨1078925, by rfl⟩ : syracuseStep 1438567 = 2157851) B2157851
theorem B55309229 : Blo 1437538 55309229 := bstep (se 3 (by rfl) ⟨10370480, by rfl⟩ : syracuseStep 55309229 = 20740961) B20740961
theorem B1438831 : Blo 1437538 1438831 := bstep (se 1 (by rfl) ⟨1079123, by rfl⟩ : syracuseStep 1438831 = 2158247) B2158247
theorem B7009583 : Blo 1437538 7009583 := bstep (se 1 (by rfl) ⟨5257187, by rfl⟩ : syracuseStep 7009583 = 10514375) B10514375
theorem B12294017 : Blo 1437538 12294017 := bstep (se 2 (by rfl) ⟨4610256, by rfl⟩ : syracuseStep 12294017 = 9220513) B9220513
theorem B23345657 : Blo 1437538 23345657 := bstep (se 2 (by rfl) ⟨8754621, by rfl⟩ : syracuseStep 23345657 = 17509243) B17509243
theorem B5462761 : Blo 1437538 5462761 := bstep (se 2 (by rfl) ⟨2048535, by rfl⟩ : syracuseStep 5462761 = 4097071) B4097071
theorem B4094783 : Blo 1437538 4094783 := bstep (se 1 (by rfl) ⟨3071087, by rfl⟩ : syracuseStep 4094783 = 6142175) B6142175
theorem B7281899 : Blo 1437538 7281899 := bstep (se 1 (by rfl) ⟨5461424, by rfl⟩ : syracuseStep 7281899 = 10922849) B10922849
theorem B4095967 : Blo 1437538 4095967 := bstep (se 1 (by rfl) ⟨3071975, by rfl⟩ : syracuseStep 4095967 = 6143951) B6143951
theorem B10371233 : Blo 1437538 10371233 := bstep (se 2 (by rfl) ⟨3889212, by rfl⟩ : syracuseStep 10371233 = 7778425) B7778425
theorem B3236219 : Blo 1437538 3236219 := bstep (se 1 (by rfl) ⟨2427164, by rfl⟩ : syracuseStep 3236219 = 4854329) B4854329
theorem B36872819 : Blo 1437538 36872819 := bstep (se 1 (by rfl) ⟨27654614, by rfl⟩ : syracuseStep 36872819 = 55309229) B55309229
theorem B4096889 : Blo 1437538 4096889 := bstep (se 2 (by rfl) ⟨1536333, by rfl⟩ : syracuseStep 4096889 = 3072667) B3072667
theorem B7283681 : Blo 1437538 7283681 := bstep (se 2 (by rfl) ⟨2731380, by rfl⟩ : syracuseStep 7283681 = 5462761) B5462761
theorem B255772079 : Blo 1437538 255772079 := bstep (se 1 (by rfl) ⟨191829059, by rfl⟩ : syracuseStep 255772079 = 383658119) B383658119
theorem B2729855 : Blo 1437538 2729855 := bstep (se 1 (by rfl) ⟨2047391, by rfl⟩ : syracuseStep 2729855 = 4094783) B4094783
theorem B1821467 : Blo 1437538 1821467 := bstep (se 1 (by rfl) ⟨1366100, by rfl⟩ : syracuseStep 1821467 = 2732201) B2732201
theorem B3640423 : Blo 1437538 3640423 := bstep (se 1 (by rfl) ⟨2730317, by rfl⟩ : syracuseStep 3640423 = 5460635) B5460635
theorem B2158271 : Blo 1437538 2158271 := bstep (se 1 (by rfl) ⟨1618703, by rfl⟩ : syracuseStep 2158271 = 3237407) B3237407
theorem B7778015 : Blo 1437538 7778015 := bstep (se 1 (by rfl) ⟨5833511, by rfl⟩ : syracuseStep 7778015 = 11667023) B11667023
theorem B8196011 : Blo 1437538 8196011 := bstep (se 1 (by rfl) ⟨6147008, by rfl⟩ : syracuseStep 8196011 = 12294017) B12294017
theorem B2159039 : Blo 1437538 2159039 := bstep (se 1 (by rfl) ⟨1619279, by rfl⟩ : syracuseStep 2159039 = 3238559) B3238559
theorem B1438183 : Blo 1437538 1438183 := bstep (se 1 (by rfl) ⟨1078637, by rfl⟩ : syracuseStep 1438183 = 2157275) B2157275
theorem B7287407 : Blo 1437538 7287407 := bstep (se 1 (by rfl) ⟨5465555, by rfl⟩ : syracuseStep 7287407 = 10931111) B10931111
theorem B10367713 : Blo 1437538 10367713 := bstep (se 2 (by rfl) ⟨3887892, by rfl⟩ : syracuseStep 10367713 = 7775785) B7775785
theorem B4854599 : Blo 1437538 4854599 := bstep (se 1 (by rfl) ⟨3640949, by rfl⟩ : syracuseStep 4854599 = 7281899) B7281899
theorem B5461289 : Blo 1437538 5461289 := bstep (se 2 (by rfl) ⟨2047983, by rfl⟩ : syracuseStep 5461289 = 4095967) B4095967
theorem B1439167 : Blo 1437538 1439167 := bstep (se 1 (by rfl) ⟨1079375, by rfl⟩ : syracuseStep 1439167 = 2158751) B2158751
theorem B8189495 : Blo 1437538 8189495 := bstep (se 1 (by rfl) ⟨6142121, by rfl⟩ : syracuseStep 8189495 = 12284243) B12284243
theorem B1439515 : Blo 1437538 1439515 := bstep (se 1 (by rfl) ⟨1079636, by rfl⟩ : syracuseStep 1439515 = 2159273) B2159273
theorem B18692221 : Blo 1437538 18692221 := bstep (se 3 (by rfl) ⟨3504791, by rfl⟩ : syracuseStep 18692221 = 7009583) B7009583
theorem B17488619 : Blo 1437538 17488619 := bstep (se 1 (by rfl) ⟨13116464, by rfl⟩ : syracuseStep 17488619 = 26232929) B26232929
theorem B4152071 : Blo 1437538 4152071 := bstep (se 1 (by rfl) ⟨3114053, by rfl⟩ : syracuseStep 4152071 = 6228107) B6228107
theorem B15563771 : Blo 1437538 15563771 := bstep (se 1 (by rfl) ⟨11672828, by rfl⟩ : syracuseStep 15563771 = 23345657) B23345657
theorem B3234815 : Blo 1437538 3234815 := bstep (se 1 (by rfl) ⟨2426111, by rfl⟩ : syracuseStep 3234815 = 4852223) B4852223
theorem B269278465 : Blo 1437538 269278465 := bstep (se 2 (by rfl) ⟨100979424, by rfl⟩ : syracuseStep 269278465 = 201958849) B201958849
theorem B3890879 : Blo 1437538 3890879 := bstep (se 1 (by rfl) ⟨2918159, by rfl⟩ : syracuseStep 3890879 = 5836319) B5836319
theorem B6914155 : Blo 1437538 6914155 := bstep (se 1 (by rfl) ⟨5185616, by rfl⟩ : syracuseStep 6914155 = 10371233) B10371233
theorem B4858271 : Blo 1437538 4858271 := bstep (se 1 (by rfl) ⟨3643703, by rfl⟩ : syracuseStep 4858271 = 7287407) B7287407
theorem B3236399 : Blo 1437538 3236399 := bstep (se 1 (by rfl) ⟨2427299, by rfl⟩ : syracuseStep 3236399 = 4854599) B4854599
theorem B1819903 : Blo 1437538 1819903 := bstep (se 1 (by rfl) ⟨1364927, by rfl⟩ : syracuseStep 1819903 = 2729855) B2729855
theorem B11659079 : Blo 1437538 11659079 := bstep (se 1 (by rfl) ⟨8744309, by rfl⟩ : syracuseStep 11659079 = 17488619) B17488619
theorem B2156543 : Blo 1437538 2156543 := bstep (se 1 (by rfl) ⟨1617407, by rfl⟩ : syracuseStep 2156543 = 3234815) B3234815
theorem B24922961 : Blo 1437538 24922961 := bstep (se 2 (by rfl) ⟨9346110, by rfl⟩ : syracuseStep 24922961 = 18692221) B18692221
theorem B2157479 : Blo 1437538 2157479 := bstep (se 1 (by rfl) ⟨1618109, by rfl⟩ : syracuseStep 2157479 = 3236219) B3236219
theorem B2731259 : Blo 1437538 2731259 := bstep (se 1 (by rfl) ⟨2048444, by rfl⟩ : syracuseStep 2731259 = 4096889) B4096889
theorem B3640859 : Blo 1437538 3640859 := bstep (se 1 (by rfl) ⟨2730644, by rfl⟩ : syracuseStep 3640859 = 5461289) B5461289
theorem B13823617 : Blo 1437538 13823617 := bstep (se 2 (by rfl) ⟨5183856, by rfl⟩ : syracuseStep 13823617 = 10367713) B10367713
theorem B5459663 : Blo 1437538 5459663 := bstep (se 1 (by rfl) ⟨4094747, by rfl⟩ : syracuseStep 5459663 = 8189495) B8189495
theorem B4853897 : Blo 1437538 4853897 := bstep (se 2 (by rfl) ⟨1820211, by rfl⟩ : syracuseStep 4853897 = 3640423) B3640423
theorem B10375847 : Blo 1437538 10375847 := bstep (se 1 (by rfl) ⟨7781885, by rfl⟩ : syracuseStep 10375847 = 15563771) B15563771
theorem B11072189 : Blo 1437538 11072189 := bstep (se 3 (by rfl) ⟨2076035, by rfl⟩ : syracuseStep 11072189 = 4152071) B4152071
theorem B1438847 : Blo 1437538 1438847 := bstep (se 1 (by rfl) ⟨1079135, by rfl⟩ : syracuseStep 1438847 = 2158271) B2158271
theorem B2593919 : Blo 1437538 2593919 := bstep (se 1 (by rfl) ⟨1945439, by rfl⟩ : syracuseStep 2593919 = 3890879) B3890879
theorem B1439359 : Blo 1437538 1439359 := bstep (se 1 (by rfl) ⟨1079519, by rfl⟩ : syracuseStep 1439359 = 2159039) B2159039
theorem B24581879 : Blo 1437538 24581879 := bstep (se 1 (by rfl) ⟨18436409, by rfl⟩ : syracuseStep 24581879 = 36872819) B36872819
theorem B4855787 : Blo 1437538 4855787 := bstep (se 1 (by rfl) ⟨3641840, by rfl⟩ : syracuseStep 4855787 = 7283681) B7283681
theorem B170514719 : Blo 1437538 170514719 := bstep (se 1 (by rfl) ⟨127886039, by rfl⟩ : syracuseStep 170514719 = 255772079) B255772079
theorem B359037953 : Blo 1437538 359037953 := bstep (se 2 (by rfl) ⟨134639232, by rfl⟩ : syracuseStep 359037953 = 269278465) B269278465
theorem B4857245 : Blo 1437538 4857245 := bstep (se 3 (by rfl) ⟨910733, by rfl⟩ : syracuseStep 4857245 = 1821467) B1821467
theorem B5185343 : Blo 1437538 5185343 := bstep (se 1 (by rfl) ⟨3889007, by rfl⟩ : syracuseStep 5185343 = 7778015) B7778015
theorem B5464007 : Blo 1437538 5464007 := bstep (se 1 (by rfl) ⟨4098005, by rfl⟩ : syracuseStep 5464007 = 8196011) B8196011
theorem B3235931 : Blo 1437538 3235931 := bstep (se 1 (by rfl) ⟨2426948, by rfl⟩ : syracuseStep 3235931 = 4853897) B4853897
theorem B7381459 : Blo 1437538 7381459 := bstep (se 1 (by rfl) ⟨5536094, by rfl⟩ : syracuseStep 7381459 = 11072189) B11072189
theorem B7283357 : Blo 1437538 7283357 := bstep (se 3 (by rfl) ⟨1365629, by rfl⟩ : syracuseStep 7283357 = 2731259) B2731259
theorem B1729279 : Blo 1437538 1729279 := bstep (se 1 (by rfl) ⟨1296959, by rfl⟩ : syracuseStep 1729279 = 2593919) B2593919
theorem B3237191 : Blo 1437538 3237191 := bstep (se 1 (by rfl) ⟨2427893, by rfl⟩ : syracuseStep 3237191 = 4855787) B4855787
theorem B2426537 : Blo 1437538 2426537 := bstep (se 2 (by rfl) ⟨909951, by rfl⟩ : syracuseStep 2426537 = 1819903) B1819903
theorem B16615307 : Blo 1437538 16615307 := bstep (se 1 (by rfl) ⟨12461480, by rfl⟩ : syracuseStep 16615307 = 24922961) B24922961
theorem B3238163 : Blo 1437538 3238163 := bstep (se 1 (by rfl) ⟨2428622, by rfl⟩ : syracuseStep 3238163 = 4857245) B4857245
theorem B2427239 : Blo 1437538 2427239 := bstep (se 1 (by rfl) ⟨1820429, by rfl⟩ : syracuseStep 2427239 = 3640859) B3640859
theorem B3639775 : Blo 1437538 3639775 := bstep (se 1 (by rfl) ⟨2729831, by rfl⟩ : syracuseStep 3639775 = 5459663) B5459663
theorem B9218873 : Blo 1437538 9218873 := bstep (se 2 (by rfl) ⟨3457077, by rfl⟩ : syracuseStep 9218873 = 6914155) B6914155
theorem B3238847 : Blo 1437538 3238847 := bstep (se 1 (by rfl) ⟨2429135, by rfl⟩ : syracuseStep 3238847 = 4858271) B4858271
theorem B2157599 : Blo 1437538 2157599 := bstep (se 1 (by rfl) ⟨1618199, by rfl⟩ : syracuseStep 2157599 = 3236399) B3236399
theorem B6917231 : Blo 1437538 6917231 := bstep (se 1 (by rfl) ⟨5187923, by rfl⟩ : syracuseStep 6917231 = 10375847) B10375847
theorem B16387919 : Blo 1437538 16387919 := bstep (se 1 (by rfl) ⟨12290939, by rfl⟩ : syracuseStep 16387919 = 24581879) B24581879
theorem B1437695 : Blo 1437538 1437695 := bstep (se 1 (by rfl) ⟨1078271, by rfl⟩ : syracuseStep 1437695 = 2156543) B2156543
theorem B113676479 : Blo 1437538 113676479 := bstep (se 1 (by rfl) ⟨85257359, by rfl⟩ : syracuseStep 113676479 = 170514719) B170514719
theorem B1438319 : Blo 1437538 1438319 := bstep (se 1 (by rfl) ⟨1078739, by rfl⟩ : syracuseStep 1438319 = 2157479) B2157479
theorem B239358635 : Blo 1437538 239358635 := bstep (se 1 (by rfl) ⟨179518976, by rfl⟩ : syracuseStep 239358635 = 359037953) B359037953
theorem B3642671 : Blo 1437538 3642671 := bstep (se 1 (by rfl) ⟨2732003, by rfl⟩ : syracuseStep 3642671 = 5464007) B5464007
theorem B7772719 : Blo 1437538 7772719 := bstep (se 1 (by rfl) ⟨5829539, by rfl⟩ : syracuseStep 7772719 = 11659079) B11659079
theorem B13827581 : Blo 1437538 13827581 := bstep (se 3 (by rfl) ⟨2592671, by rfl⟩ : syracuseStep 13827581 = 5185343) B5185343
theorem B18431489 : Blo 1437538 18431489 := bstep (se 2 (by rfl) ⟨6911808, by rfl⟩ : syracuseStep 18431489 = 13823617) B13823617
theorem B75784319 : Blo 1437538 75784319 := bstep (se 1 (by rfl) ⟨56838239, by rfl⟩ : syracuseStep 75784319 = 113676479) B113676479
theorem B159572423 : Blo 1437538 159572423 := bstep (se 1 (by rfl) ⟨119679317, by rfl⟩ : syracuseStep 159572423 = 239358635) B239358635
theorem B10363625 : Blo 1437538 10363625 := bstep (se 2 (by rfl) ⟨3886359, by rfl⟩ : syracuseStep 10363625 = 7772719) B7772719
theorem B11076871 : Blo 1437538 11076871 := bstep (se 1 (by rfl) ⟨8307653, by rfl⟩ : syracuseStep 11076871 = 16615307) B16615307
theorem B6145915 : Blo 1437538 6145915 := bstep (se 1 (by rfl) ⟨4609436, by rfl⟩ : syracuseStep 6145915 = 9218873) B9218873
theorem B9218387 : Blo 1437538 9218387 := bstep (se 1 (by rfl) ⟨6913790, by rfl⟩ : syracuseStep 9218387 = 13827581) B13827581
theorem B2157287 : Blo 1437538 2157287 := bstep (se 1 (by rfl) ⟨1617965, by rfl⟩ : syracuseStep 2157287 = 3235931) B3235931
theorem B9841945 : Blo 1437538 9841945 := bstep (se 2 (by rfl) ⟨3690729, by rfl⟩ : syracuseStep 9841945 = 7381459) B7381459
theorem B4853033 : Blo 1437538 4853033 := bstep (se 2 (by rfl) ⟨1819887, by rfl⟩ : syracuseStep 4853033 = 3639775) B3639775
theorem B2428447 : Blo 1437538 2428447 := bstep (se 1 (by rfl) ⟨1821335, by rfl⟩ : syracuseStep 2428447 = 3642671) B3642671
theorem B2158127 : Blo 1437538 2158127 := bstep (se 1 (by rfl) ⟨1618595, by rfl⟩ : syracuseStep 2158127 = 3237191) B3237191
theorem B1617691 : Blo 1437538 1617691 := bstep (se 1 (by rfl) ⟨1213268, by rfl⟩ : syracuseStep 1617691 = 2426537) B2426537
theorem B2158775 : Blo 1437538 2158775 := bstep (se 1 (by rfl) ⟨1619081, by rfl⟩ : syracuseStep 2158775 = 3238163) B3238163
theorem B1618159 : Blo 1437538 1618159 := bstep (se 1 (by rfl) ⟨1213619, by rfl⟩ : syracuseStep 1618159 = 2427239) B2427239
theorem B2159231 : Blo 1437538 2159231 := bstep (se 1 (by rfl) ⟨1619423, by rfl⟩ : syracuseStep 2159231 = 3238847) B3238847
theorem B1438399 : Blo 1437538 1438399 := bstep (se 1 (by rfl) ⟨1078799, by rfl⟩ : syracuseStep 1438399 = 2157599) B2157599
theorem B10925279 : Blo 1437538 10925279 := bstep (se 1 (by rfl) ⟨8193959, by rfl⟩ : syracuseStep 10925279 = 16387919) B16387919
theorem B4855571 : Blo 1437538 4855571 := bstep (se 1 (by rfl) ⟨3641678, by rfl⟩ : syracuseStep 4855571 = 7283357) B7283357
theorem B9222821 : Blo 1437538 9222821 := bstep (se 4 (by rfl) ⟨864639, by rfl⟩ : syracuseStep 9222821 = 1729279) B1729279
theorem B4611487 : Blo 1437538 4611487 := bstep (se 1 (by rfl) ⟨3458615, by rfl⟩ : syracuseStep 4611487 = 6917231) B6917231
theorem B12287659 : Blo 1437538 12287659 := bstep (se 1 (by rfl) ⟨9215744, by rfl⟩ : syracuseStep 12287659 = 18431489) B18431489
theorem B106381615 : Blo 1437538 106381615 := bstep (se 1 (by rfl) ⟨79786211, by rfl⟩ : syracuseStep 106381615 = 159572423) B159572423
theorem B7283519 : Blo 1437538 7283519 := bstep (se 1 (by rfl) ⟨5462639, by rfl⟩ : syracuseStep 7283519 = 10925279) B10925279
theorem B3237047 : Blo 1437538 3237047 := bstep (se 1 (by rfl) ⟨2427785, by rfl⟩ : syracuseStep 3237047 = 4855571) B4855571
theorem B6145591 : Blo 1437538 6145591 := bstep (se 1 (by rfl) ⟨4609193, by rfl⟩ : syracuseStep 6145591 = 9218387) B9218387
theorem B3237929 : Blo 1437538 3237929 := bstep (se 2 (by rfl) ⟨1214223, by rfl⟩ : syracuseStep 3237929 = 2428447) B2428447
theorem B2156921 : Blo 1437538 2156921 := bstep (se 2 (by rfl) ⟨808845, by rfl⟩ : syracuseStep 2156921 = 1617691) B1617691
theorem B8194553 : Blo 1437538 8194553 := bstep (se 2 (by rfl) ⟨3072957, by rfl⟩ : syracuseStep 8194553 = 6145915) B6145915
theorem B50522879 : Blo 1437538 50522879 := bstep (se 1 (by rfl) ⟨37892159, by rfl⟩ : syracuseStep 50522879 = 75784319) B75784319
theorem B2157545 : Blo 1437538 2157545 := bstep (se 2 (by rfl) ⟨809079, by rfl⟩ : syracuseStep 2157545 = 1618159) B1618159
theorem B6909083 : Blo 1437538 6909083 := bstep (se 1 (by rfl) ⟨5181812, by rfl⟩ : syracuseStep 6909083 = 10363625) B10363625
theorem B6148547 : Blo 1437538 6148547 := bstep (se 1 (by rfl) ⟨4611410, by rfl⟩ : syracuseStep 6148547 = 9222821) B9222821
theorem B1438191 : Blo 1437538 1438191 := bstep (se 1 (by rfl) ⟨1078643, by rfl⟩ : syracuseStep 1438191 = 2157287) B2157287
theorem B6148649 : Blo 1437538 6148649 := bstep (se 2 (by rfl) ⟨2305743, by rfl⟩ : syracuseStep 6148649 = 4611487) B4611487
theorem B1438751 : Blo 1437538 1438751 := bstep (se 1 (by rfl) ⟨1079063, by rfl⟩ : syracuseStep 1438751 = 2158127) B2158127
theorem B1439183 : Blo 1437538 1439183 := bstep (se 1 (by rfl) ⟨1079387, by rfl⟩ : syracuseStep 1439183 = 2158775) B2158775
theorem B1439487 : Blo 1437538 1439487 := bstep (se 1 (by rfl) ⟨1079615, by rfl⟩ : syracuseStep 1439487 = 2159231) B2159231
theorem B14769161 : Blo 1437538 14769161 := bstep (se 2 (by rfl) ⟨5538435, by rfl⟩ : syracuseStep 14769161 = 11076871) B11076871
theorem B13122593 : Blo 1437538 13122593 := bstep (se 2 (by rfl) ⟨4920972, by rfl⟩ : syracuseStep 13122593 = 9841945) B9841945
theorem B3235355 : Blo 1437538 3235355 := bstep (se 1 (by rfl) ⟨2426516, by rfl⟩ : syracuseStep 3235355 = 4853033) B4853033
theorem B16383545 : Blo 1437538 16383545 := bstep (se 2 (by rfl) ⟨6143829, by rfl⟩ : syracuseStep 16383545 = 12287659) B12287659
theorem B8194121 : Blo 1437538 8194121 := bstep (se 2 (by rfl) ⟨3072795, by rfl⟩ : syracuseStep 8194121 = 6145591) B6145591
theorem B4606055 : Blo 1437538 4606055 := bstep (se 1 (by rfl) ⟨3454541, by rfl⟩ : syracuseStep 4606055 = 6909083) B6909083
theorem B2156903 : Blo 1437538 2156903 := bstep (se 1 (by rfl) ⟨1617677, by rfl⟩ : syracuseStep 2156903 = 3235355) B3235355
theorem B10922363 : Blo 1437538 10922363 := bstep (se 1 (by rfl) ⟨8191772, by rfl⟩ : syracuseStep 10922363 = 16383545) B16383545
theorem B4099031 : Blo 1437538 4099031 := bstep (se 1 (by rfl) ⟨3074273, by rfl⟩ : syracuseStep 4099031 = 6148547) B6148547
theorem B4099099 : Blo 1437538 4099099 := bstep (se 1 (by rfl) ⟨3074324, by rfl⟩ : syracuseStep 4099099 = 6148649) B6148649
theorem B2158031 : Blo 1437538 2158031 := bstep (se 1 (by rfl) ⟨1618523, by rfl⟩ : syracuseStep 2158031 = 3237047) B3237047
theorem B2158619 : Blo 1437538 2158619 := bstep (se 1 (by rfl) ⟨1618964, by rfl⟩ : syracuseStep 2158619 = 3237929) B3237929
theorem B1437947 : Blo 1437538 1437947 := bstep (se 1 (by rfl) ⟨1078460, by rfl⟩ : syracuseStep 1437947 = 2156921) B2156921
theorem B33681919 : Blo 1437538 33681919 := bstep (se 1 (by rfl) ⟨25261439, by rfl⟩ : syracuseStep 33681919 = 50522879) B50522879
theorem B1438363 : Blo 1437538 1438363 := bstep (se 1 (by rfl) ⟨1078772, by rfl⟩ : syracuseStep 1438363 = 2157545) B2157545
theorem B141842153 : Blo 1437538 141842153 := bstep (se 2 (by rfl) ⟨53190807, by rfl⟩ : syracuseStep 141842153 = 106381615) B106381615
theorem B4855679 : Blo 1437538 4855679 := bstep (se 1 (by rfl) ⟨3641759, by rfl⟩ : syracuseStep 4855679 = 7283519) B7283519
theorem B5463035 : Blo 1437538 5463035 := bstep (se 1 (by rfl) ⟨4097276, by rfl⟩ : syracuseStep 5463035 = 8194553) B8194553
theorem B9846107 : Blo 1437538 9846107 := bstep (se 1 (by rfl) ⟨7384580, by rfl⟩ : syracuseStep 9846107 = 14769161) B14769161
theorem B8748395 : Blo 1437538 8748395 := bstep (se 1 (by rfl) ⟨6561296, by rfl⟩ : syracuseStep 8748395 = 13122593) B13122593
theorem B44909225 : Blo 1437538 44909225 := bstep (se 2 (by rfl) ⟨16840959, by rfl⟩ : syracuseStep 44909225 = 33681919) B33681919
theorem B94561435 : Blo 1437538 94561435 := bstep (se 1 (by rfl) ⟨70921076, by rfl⟩ : syracuseStep 94561435 = 141842153) B141842153
theorem B3237119 : Blo 1437538 3237119 := bstep (se 1 (by rfl) ⟨2427839, by rfl⟩ : syracuseStep 3237119 = 4855679) B4855679
theorem B5465465 : Blo 1437538 5465465 := bstep (se 2 (by rfl) ⟨2049549, by rfl⟩ : syracuseStep 5465465 = 4099099) B4099099
theorem B6564071 : Blo 1437538 6564071 := bstep (se 1 (by rfl) ⟨4923053, by rfl⟩ : syracuseStep 6564071 = 9846107) B9846107
theorem B1437935 : Blo 1437538 1437935 := bstep (se 1 (by rfl) ⟨1078451, by rfl⟩ : syracuseStep 1437935 = 2156903) B2156903
theorem B2732687 : Blo 1437538 2732687 := bstep (se 1 (by rfl) ⟨2049515, by rfl⟩ : syracuseStep 2732687 = 4099031) B4099031
theorem B3642023 : Blo 1437538 3642023 := bstep (se 1 (by rfl) ⟨2731517, by rfl⟩ : syracuseStep 3642023 = 5463035) B5463035
theorem B1438687 : Blo 1437538 1438687 := bstep (se 1 (by rfl) ⟨1079015, by rfl⟩ : syracuseStep 1438687 = 2158031) B2158031
theorem B1439079 : Blo 1437538 1439079 := bstep (se 1 (by rfl) ⟨1079309, by rfl⟩ : syracuseStep 1439079 = 2158619) B2158619
theorem B5462747 : Blo 1437538 5462747 := bstep (se 1 (by rfl) ⟨4097060, by rfl⟩ : syracuseStep 5462747 = 8194121) B8194121
theorem B3070703 : Blo 1437538 3070703 := bstep (se 1 (by rfl) ⟨2303027, by rfl⟩ : syracuseStep 3070703 = 4606055) B4606055
theorem B7281575 : Blo 1437538 7281575 := bstep (se 1 (by rfl) ⟨5461181, by rfl⟩ : syracuseStep 7281575 = 10922363) B10922363
theorem B5832263 : Blo 1437538 5832263 := bstep (se 1 (by rfl) ⟨4374197, by rfl⟩ : syracuseStep 5832263 = 8748395) B8748395
theorem B4376047 : Blo 1437538 4376047 := bstep (se 1 (by rfl) ⟨3282035, by rfl⟩ : syracuseStep 4376047 = 6564071) B6564071
theorem B1821791 : Blo 1437538 1821791 := bstep (se 1 (by rfl) ⟨1366343, by rfl⟩ : syracuseStep 1821791 = 2732687) B2732687
theorem B2428015 : Blo 1437538 2428015 := bstep (se 1 (by rfl) ⟨1821011, by rfl⟩ : syracuseStep 2428015 = 3642023) B3642023
theorem B504327653 : Blo 1437538 504327653 := bstep (se 4 (by rfl) ⟨47280717, by rfl⟩ : syracuseStep 504327653 = 94561435) B94561435
theorem B2158079 : Blo 1437538 2158079 := bstep (se 1 (by rfl) ⟨1618559, by rfl⟩ : syracuseStep 2158079 = 3237119) B3237119
theorem B3641831 : Blo 1437538 3641831 := bstep (se 1 (by rfl) ⟨2731373, by rfl⟩ : syracuseStep 3641831 = 5462747) B5462747
theorem B4854383 : Blo 1437538 4854383 := bstep (se 1 (by rfl) ⟨3640787, by rfl⟩ : syracuseStep 4854383 = 7281575) B7281575
theorem B3888175 : Blo 1437538 3888175 := bstep (se 1 (by rfl) ⟨2916131, by rfl⟩ : syracuseStep 3888175 = 5832263) B5832263
theorem B29939483 : Blo 1437538 29939483 := bstep (se 1 (by rfl) ⟨22454612, by rfl⟩ : syracuseStep 29939483 = 44909225) B44909225
theorem B3643643 : Blo 1437538 3643643 := bstep (se 1 (by rfl) ⟨2732732, by rfl⟩ : syracuseStep 3643643 = 5465465) B5465465
theorem B2047135 : Blo 1437538 2047135 := bstep (se 1 (by rfl) ⟨1535351, by rfl⟩ : syracuseStep 2047135 = 3070703) B3070703
theorem B4858109 : Blo 1437538 4858109 := bstep (se 3 (by rfl) ⟨910895, by rfl⟩ : syracuseStep 4858109 = 1821791) B1821791
theorem B3236255 : Blo 1437538 3236255 := bstep (se 1 (by rfl) ⟨2427191, by rfl⟩ : syracuseStep 3236255 = 4854383) B4854383
theorem B3237353 : Blo 1437538 3237353 := bstep (se 2 (by rfl) ⟨1214007, by rfl⟩ : syracuseStep 3237353 = 2428015) B2428015
theorem B2729513 : Blo 1437538 2729513 := bstep (se 2 (by rfl) ⟨1023567, by rfl⟩ : syracuseStep 2729513 = 2047135) B2047135
theorem B5834729 : Blo 1437538 5834729 := bstep (se 2 (by rfl) ⟨2188023, by rfl⟩ : syracuseStep 5834729 = 4376047) B4376047
theorem B336218435 : Blo 1437538 336218435 := bstep (se 1 (by rfl) ⟨252163826, by rfl⟩ : syracuseStep 336218435 = 504327653) B504327653
theorem B2427887 : Blo 1437538 2427887 := bstep (se 1 (by rfl) ⟨1820915, by rfl⟩ : syracuseStep 2427887 = 3641831) B3641831
theorem B19959655 : Blo 1437538 19959655 := bstep (se 1 (by rfl) ⟨14969741, by rfl⟩ : syracuseStep 19959655 = 29939483) B29939483
theorem B2429095 : Blo 1437538 2429095 := bstep (se 1 (by rfl) ⟨1821821, by rfl⟩ : syracuseStep 2429095 = 3643643) B3643643
theorem B1438719 : Blo 1437538 1438719 := bstep (se 1 (by rfl) ⟨1079039, by rfl⟩ : syracuseStep 1438719 = 2158079) B2158079
theorem B5184233 : Blo 1437538 5184233 := bstep (se 2 (by rfl) ⟨1944087, by rfl⟩ : syracuseStep 5184233 = 3888175) B3888175
theorem B1819675 : Blo 1437538 1819675 := bstep (se 1 (by rfl) ⟨1364756, by rfl⟩ : syracuseStep 1819675 = 2729513) B2729513
theorem B3238739 : Blo 1437538 3238739 := bstep (se 1 (by rfl) ⟨2429054, by rfl⟩ : syracuseStep 3238739 = 4858109) B4858109
theorem B3238793 : Blo 1437538 3238793 := bstep (se 2 (by rfl) ⟨1214547, by rfl⟩ : syracuseStep 3238793 = 2429095) B2429095
theorem B2157503 : Blo 1437538 2157503 := bstep (se 1 (by rfl) ⟨1618127, by rfl⟩ : syracuseStep 2157503 = 3236255) B3236255
theorem B2158235 : Blo 1437538 2158235 := bstep (se 1 (by rfl) ⟨1618676, by rfl⟩ : syracuseStep 2158235 = 3237353) B3237353
theorem B224145623 : Blo 1437538 224145623 := bstep (se 1 (by rfl) ⟨168109217, by rfl⟩ : syracuseStep 224145623 = 336218435) B336218435
theorem B1618591 : Blo 1437538 1618591 := bstep (se 1 (by rfl) ⟨1213943, by rfl⟩ : syracuseStep 1618591 = 2427887) B2427887
theorem B26612873 : Blo 1437538 26612873 := bstep (se 2 (by rfl) ⟨9979827, by rfl⟩ : syracuseStep 26612873 = 19959655) B19959655
theorem B3889819 : Blo 1437538 3889819 := bstep (se 1 (by rfl) ⟨2917364, by rfl⟩ : syracuseStep 3889819 = 5834729) B5834729
theorem B3456155 : Blo 1437538 3456155 := bstep (se 1 (by rfl) ⟨2592116, by rfl⟩ : syracuseStep 3456155 = 5184233) B5184233
theorem B149430415 : Blo 1437538 149430415 := bstep (se 1 (by rfl) ⟨112072811, by rfl⟩ : syracuseStep 149430415 = 224145623) B224145623
theorem B9216413 : Blo 1437538 9216413 := bstep (se 3 (by rfl) ⟨1728077, by rfl⟩ : syracuseStep 9216413 = 3456155) B3456155
theorem B5186425 : Blo 1437538 5186425 := bstep (se 2 (by rfl) ⟨1944909, by rfl⟩ : syracuseStep 5186425 = 3889819) B3889819
theorem B2426233 : Blo 1437538 2426233 := bstep (se 2 (by rfl) ⟨909837, by rfl⟩ : syracuseStep 2426233 = 1819675) B1819675
theorem B2158121 : Blo 1437538 2158121 := bstep (se 2 (by rfl) ⟨809295, by rfl⟩ : syracuseStep 2158121 = 1618591) B1618591
theorem B2159159 : Blo 1437538 2159159 := bstep (se 1 (by rfl) ⟨1619369, by rfl⟩ : syracuseStep 2159159 = 3238739) B3238739
theorem B2159195 : Blo 1437538 2159195 := bstep (se 1 (by rfl) ⟨1619396, by rfl⟩ : syracuseStep 2159195 = 3238793) B3238793
theorem B1438335 : Blo 1437538 1438335 := bstep (se 1 (by rfl) ⟨1078751, by rfl⟩ : syracuseStep 1438335 = 2157503) B2157503
theorem B1438823 : Blo 1437538 1438823 := bstep (se 1 (by rfl) ⟨1079117, by rfl⟩ : syracuseStep 1438823 = 2158235) B2158235
theorem B17741915 : Blo 1437538 17741915 := bstep (se 1 (by rfl) ⟨13306436, by rfl⟩ : syracuseStep 17741915 = 26612873) B26612873
theorem B6144275 : Blo 1437538 6144275 := bstep (se 1 (by rfl) ⟨4608206, by rfl⟩ : syracuseStep 6144275 = 9216413) B9216413
theorem B6915233 : Blo 1437538 6915233 := bstep (se 2 (by rfl) ⟨2593212, by rfl⟩ : syracuseStep 6915233 = 5186425) B5186425
theorem B199240553 : Blo 1437538 199240553 := bstep (se 2 (by rfl) ⟨74715207, by rfl⟩ : syracuseStep 199240553 = 149430415) B149430415
theorem B1438747 : Blo 1437538 1438747 := bstep (se 1 (by rfl) ⟨1079060, by rfl⟩ : syracuseStep 1438747 = 2158121) B2158121
theorem B1439439 : Blo 1437538 1439439 := bstep (se 1 (by rfl) ⟨1079579, by rfl⟩ : syracuseStep 1439439 = 2159159) B2159159
theorem B1439463 : Blo 1437538 1439463 := bstep (se 1 (by rfl) ⟨1079597, by rfl⟩ : syracuseStep 1439463 = 2159195) B2159195
theorem B11827943 : Blo 1437538 11827943 := bstep (se 1 (by rfl) ⟨8870957, by rfl⟩ : syracuseStep 11827943 = 17741915) B17741915
theorem B3234977 : Blo 1437538 3234977 := bstep (se 2 (by rfl) ⟨1213116, by rfl⟩ : syracuseStep 3234977 = 2426233) B2426233
theorem B4096183 : Blo 1437538 4096183 := bstep (se 1 (by rfl) ⟨3072137, by rfl⟩ : syracuseStep 4096183 = 6144275) B6144275
theorem B132827035 : Blo 1437538 132827035 := bstep (se 1 (by rfl) ⟨99620276, by rfl⟩ : syracuseStep 132827035 = 199240553) B199240553
theorem B2156651 : Blo 1437538 2156651 := bstep (se 1 (by rfl) ⟨1617488, by rfl⟩ : syracuseStep 2156651 = 3234977) B3234977
theorem B7885295 : Blo 1437538 7885295 := bstep (se 1 (by rfl) ⟨5913971, by rfl⟩ : syracuseStep 7885295 = 11827943) B11827943
theorem B4610155 : Blo 1437538 4610155 := bstep (se 1 (by rfl) ⟨3457616, by rfl⟩ : syracuseStep 4610155 = 6915233) B6915233
theorem B6146873 : Blo 1437538 6146873 := bstep (se 2 (by rfl) ⟨2305077, by rfl⟩ : syracuseStep 6146873 = 4610155) B4610155
theorem B1437767 : Blo 1437538 1437767 := bstep (se 1 (by rfl) ⟨1078325, by rfl⟩ : syracuseStep 1437767 = 2156651) B2156651
theorem B5461577 : Blo 1437538 5461577 := bstep (se 2 (by rfl) ⟨2048091, by rfl⟩ : syracuseStep 5461577 = 4096183) B4096183
theorem B5256863 : Blo 1437538 5256863 := bstep (se 1 (by rfl) ⟨3942647, by rfl⟩ : syracuseStep 5256863 = 7885295) B7885295
theorem B177102713 : Blo 1437538 177102713 := bstep (se 2 (by rfl) ⟨66413517, by rfl⟩ : syracuseStep 177102713 = 132827035) B132827035
theorem B4097915 : Blo 1437538 4097915 := bstep (se 1 (by rfl) ⟨3073436, by rfl⟩ : syracuseStep 4097915 = 6146873) B6146873
theorem B3641051 : Blo 1437538 3641051 := bstep (se 1 (by rfl) ⟨2730788, by rfl⟩ : syracuseStep 3641051 = 5461577) B5461577
theorem B118068475 : Blo 1437538 118068475 := bstep (se 1 (by rfl) ⟨88551356, by rfl⟩ : syracuseStep 118068475 = 177102713) B177102713
theorem B3504575 : Blo 1437538 3504575 := bstep (se 1 (by rfl) ⟨2628431, by rfl⟩ : syracuseStep 3504575 = 5256863) B5256863
theorem B2336383 : Blo 1437538 2336383 := bstep (se 1 (by rfl) ⟨1752287, by rfl⟩ : syracuseStep 2336383 = 3504575) B3504575
theorem B2427367 : Blo 1437538 2427367 := bstep (se 1 (by rfl) ⟨1820525, by rfl⟩ : syracuseStep 2427367 = 3641051) B3641051
theorem B2731943 : Blo 1437538 2731943 := bstep (se 1 (by rfl) ⟨2048957, by rfl⟩ : syracuseStep 2731943 = 4097915) B4097915
theorem B157424633 : Blo 1437538 157424633 := bstep (se 2 (by rfl) ⟨59034237, by rfl⟩ : syracuseStep 157424633 = 118068475) B118068475
theorem B3236489 : Blo 1437538 3236489 := bstep (se 2 (by rfl) ⟨1213683, by rfl⟩ : syracuseStep 3236489 = 2427367) B2427367
theorem B12460709 : Blo 1437538 12460709 := bstep (se 4 (by rfl) ⟨1168191, by rfl⟩ : syracuseStep 12460709 = 2336383) B2336383
theorem B104949755 : Blo 1437538 104949755 := bstep (se 1 (by rfl) ⟨78712316, by rfl⟩ : syracuseStep 104949755 = 157424633) B157424633
theorem B1821295 : Blo 1437538 1821295 := bstep (se 1 (by rfl) ⟨1365971, by rfl⟩ : syracuseStep 1821295 = 2731943) B2731943
theorem B33228557 : Blo 1437538 33228557 := bstep (se 3 (by rfl) ⟨6230354, by rfl⟩ : syracuseStep 33228557 = 12460709) B12460709
theorem B2157659 : Blo 1437538 2157659 := bstep (se 1 (by rfl) ⟨1618244, by rfl⟩ : syracuseStep 2157659 = 3236489) B3236489
theorem B2428393 : Blo 1437538 2428393 := bstep (se 2 (by rfl) ⟨910647, by rfl⟩ : syracuseStep 2428393 = 1821295) B1821295
theorem B69966503 : Blo 1437538 69966503 := bstep (se 1 (by rfl) ⟨52474877, by rfl⟩ : syracuseStep 69966503 = 104949755) B104949755
theorem B22152371 : Blo 1437538 22152371 := bstep (se 1 (by rfl) ⟨16614278, by rfl⟩ : syracuseStep 22152371 = 33228557) B33228557
theorem B3237857 : Blo 1437538 3237857 := bstep (se 2 (by rfl) ⟨1214196, by rfl⟩ : syracuseStep 3237857 = 2428393) B2428393
theorem B1438439 : Blo 1437538 1438439 := bstep (se 1 (by rfl) ⟨1078829, by rfl⟩ : syracuseStep 1438439 = 2157659) B2157659
theorem B46644335 : Blo 1437538 46644335 := bstep (se 1 (by rfl) ⟨34983251, by rfl⟩ : syracuseStep 46644335 = 69966503) B69966503
theorem B59072989 : Blo 1437538 59072989 := bstep (se 3 (by rfl) ⟨11076185, by rfl⟩ : syracuseStep 59072989 = 22152371) B22152371
theorem B2158571 : Blo 1437538 2158571 := bstep (se 1 (by rfl) ⟨1618928, by rfl⟩ : syracuseStep 2158571 = 3237857) B3237857
theorem B31096223 : Blo 1437538 31096223 := bstep (se 1 (by rfl) ⟨23322167, by rfl⟩ : syracuseStep 31096223 = 46644335) B46644335
theorem B20730815 : Blo 1437538 20730815 := bstep (se 1 (by rfl) ⟨15548111, by rfl⟩ : syracuseStep 20730815 = 31096223) B31096223
theorem B1439047 : Blo 1437538 1439047 := bstep (se 1 (by rfl) ⟨1079285, by rfl⟩ : syracuseStep 1439047 = 2158571) B2158571
theorem B78763985 : Blo 1437538 78763985 := bstep (se 2 (by rfl) ⟨29536494, by rfl⟩ : syracuseStep 78763985 = 59072989) B59072989
theorem B13820543 : Blo 1437538 13820543 := bstep (se 1 (by rfl) ⟨10365407, by rfl⟩ : syracuseStep 13820543 = 20730815) B20730815
theorem B52509323 : Blo 1437538 52509323 := bstep (se 1 (by rfl) ⟨39381992, by rfl⟩ : syracuseStep 52509323 = 78763985) B78763985
theorem B9213695 : Blo 1437538 9213695 := bstep (se 1 (by rfl) ⟨6910271, by rfl⟩ : syracuseStep 9213695 = 13820543) B13820543
theorem B140024861 : Blo 1437538 140024861 := bstep (se 3 (by rfl) ⟨26254661, by rfl⟩ : syracuseStep 140024861 = 52509323) B52509323
theorem B93349907 : Blo 1437538 93349907 := bstep (se 1 (by rfl) ⟨70012430, by rfl⟩ : syracuseStep 93349907 = 140024861) B140024861
theorem B6142463 : Blo 1437538 6142463 := bstep (se 1 (by rfl) ⟨4606847, by rfl⟩ : syracuseStep 6142463 = 9213695) B9213695
theorem B62233271 : Blo 1437538 62233271 := bstep (se 1 (by rfl) ⟨46674953, by rfl⟩ : syracuseStep 62233271 = 93349907) B93349907
theorem B4094975 : Blo 1437538 4094975 := bstep (se 1 (by rfl) ⟨3071231, by rfl⟩ : syracuseStep 4094975 = 6142463) B6142463
theorem B41488847 : Blo 1437538 41488847 := bstep (se 1 (by rfl) ⟨31116635, by rfl⟩ : syracuseStep 41488847 = 62233271) B62233271
theorem B10919933 : Blo 1437538 10919933 := bstep (se 3 (by rfl) ⟨2047487, by rfl⟩ : syracuseStep 10919933 = 4094975) B4094975
theorem B27659231 : Blo 1437538 27659231 := bstep (se 1 (by rfl) ⟨20744423, by rfl⟩ : syracuseStep 27659231 = 41488847) B41488847
theorem B7279955 : Blo 1437538 7279955 := bstep (se 1 (by rfl) ⟨5459966, by rfl⟩ : syracuseStep 7279955 = 10919933) B10919933
theorem B4853303 : Blo 1437538 4853303 := bstep (se 1 (by rfl) ⟨3639977, by rfl⟩ : syracuseStep 4853303 = 7279955) B7279955
theorem B18439487 : Blo 1437538 18439487 := bstep (se 1 (by rfl) ⟨13829615, by rfl⟩ : syracuseStep 18439487 = 27659231) B27659231
theorem B12292991 : Blo 1437538 12292991 := bstep (se 1 (by rfl) ⟨9219743, by rfl⟩ : syracuseStep 12292991 = 18439487) B18439487
theorem B3235535 : Blo 1437538 3235535 := bstep (se 1 (by rfl) ⟨2426651, by rfl⟩ : syracuseStep 3235535 = 4853303) B4853303
theorem B2157023 : Blo 1437538 2157023 := bstep (se 1 (by rfl) ⟨1617767, by rfl⟩ : syracuseStep 2157023 = 3235535) B3235535
theorem B8195327 : Blo 1437538 8195327 := bstep (se 1 (by rfl) ⟨6146495, by rfl⟩ : syracuseStep 8195327 = 12292991) B12292991
theorem B1438015 : Blo 1437538 1438015 := bstep (se 1 (by rfl) ⟨1078511, by rfl⟩ : syracuseStep 1438015 = 2157023) B2157023
theorem B5463551 : Blo 1437538 5463551 := bstep (se 1 (by rfl) ⟨4097663, by rfl⟩ : syracuseStep 5463551 = 8195327) B8195327
theorem B3642367 : Blo 1437538 3642367 := bstep (se 1 (by rfl) ⟨2731775, by rfl⟩ : syracuseStep 3642367 = 5463551) B5463551
theorem B4856489 : Blo 1437538 4856489 := bstep (se 2 (by rfl) ⟨1821183, by rfl⟩ : syracuseStep 4856489 = 3642367) B3642367
theorem B3237659 : Blo 1437538 3237659 := bstep (se 1 (by rfl) ⟨2428244, by rfl⟩ : syracuseStep 3237659 = 4856489) B4856489
theorem B2158439 : Blo 1437538 2158439 := bstep (se 1 (by rfl) ⟨1618829, by rfl⟩ : syracuseStep 2158439 = 3237659) B3237659
theorem B1438959 : Blo 1437538 1438959 := bstep (se 1 (by rfl) ⟨1079219, by rfl⟩ : syracuseStep 1438959 = 2158439) B2158439

theorem C0 (j : ℕ) (h1 : 359384 ≤ j) (h2 : j ≤ 359883) : Blo 1437538 (4 * j + 3) := by
  interval_cases j
  · exact B1437539
  · exact B1437543
  · exact B1437547
  · exact B1437551
  · exact B1437555
  · exact B1437559
  · exact B1437563
  · exact B1437567
  · exact B1437571
  · exact B1437575
  · exact B1437579
  · exact B1437583
  · exact B1437587
  · exact B1437591
  · exact B1437595
  · exact B1437599
  · exact B1437603
  · exact B1437607
  · exact B1437611
  · exact B1437615
  · exact B1437619
  · exact B1437623
  · exact B1437627
  · exact B1437631
  · exact B1437635
  · exact B1437639
  · exact B1437643
  · exact B1437647
  · exact B1437651
  · exact B1437655
  · exact B1437659
  · exact B1437663
  · exact B1437667
  · exact B1437671
  · exact B1437675
  · exact B1437679
  · exact B1437683
  · exact B1437687
  · exact B1437691
  · exact B1437695
  · exact B1437699
  · exact B1437703
  · exact B1437707
  · exact B1437711
  · exact B1437715
  · exact B1437719
  · exact B1437723
  · exact B1437727
  · exact B1437731
  · exact B1437735
  · exact B1437739
  · exact B1437743
  · exact B1437747
  · exact B1437751
  · exact B1437755
  · exact B1437759
  · exact B1437763
  · exact B1437767
  · exact B1437771
  · exact B1437775
  · exact B1437779
  · exact B1437783
  · exact B1437787
  · exact B1437791
  · exact B1437795
  · exact B1437799
  · exact B1437803
  · exact B1437807
  · exact B1437811
  · exact B1437815
  · exact B1437819
  · exact B1437823
  · exact B1437827
  · exact B1437831
  · exact B1437835
  · exact B1437839
  · exact B1437843
  · exact B1437847
  · exact B1437851
  · exact B1437855
  · exact B1437859
  · exact B1437863
  · exact B1437867
  · exact B1437871
  · exact B1437875
  · exact B1437879
  · exact B1437883
  · exact B1437887
  · exact B1437891
  · exact B1437895
  · exact B1437899
  · exact B1437903
  · exact B1437907
  · exact B1437911
  · exact B1437915
  · exact B1437919
  · exact B1437923
  · exact B1437927
  · exact B1437931
  · exact B1437935
  · exact B1437939
  · exact B1437943
  · exact B1437947
  · exact B1437951
  · exact B1437955
  · exact B1437959
  · exact B1437963
  · exact B1437967
  · exact B1437971
  · exact B1437975
  · exact B1437979
  · exact B1437983
  · exact B1437987
  · exact B1437991
  · exact B1437995
  · exact B1437999
  · exact B1438003
  · exact B1438007
  · exact B1438011
  · exact B1438015
  · exact B1438019
  · exact B1438023
  · exact B1438027
  · exact B1438031
  · exact B1438035
  · exact B1438039
  · exact B1438043
  · exact B1438047
  · exact B1438051
  · exact B1438055
  · exact B1438059
  · exact B1438063
  · exact B1438067
  · exact B1438071
  · exact B1438075
  · exact B1438079
  · exact B1438083
  · exact B1438087
  · exact B1438091
  · exact B1438095
  · exact B1438099
  · exact B1438103
  · exact B1438107
  · exact B1438111
  · exact B1438115
  · exact B1438119
  · exact B1438123
  · exact B1438127
  · exact B1438131
  · exact B1438135
  · exact B1438139
  · exact B1438143
  · exact B1438147
  · exact B1438151
  · exact B1438155
  · exact B1438159
  · exact B1438163
  · exact B1438167
  · exact B1438171
  · exact B1438175
  · exact B1438179
  · exact B1438183
  · exact B1438187
  · exact B1438191
  · exact B1438195
  · exact B1438199
  · exact B1438203
  · exact B1438207
  · exact B1438211
  · exact B1438215
  · exact B1438219
  · exact B1438223
  · exact B1438227
  · exact B1438231
  · exact B1438235
  · exact B1438239
  · exact B1438243
  · exact B1438247
  · exact B1438251
  · exact B1438255
  · exact B1438259
  · exact B1438263
  · exact B1438267
  · exact B1438271
  · exact B1438275
  · exact B1438279
  · exact B1438283
  · exact B1438287
  · exact B1438291
  · exact B1438295
  · exact B1438299
  · exact B1438303
  · exact B1438307
  · exact B1438311
  · exact B1438315
  · exact B1438319
  · exact B1438323
  · exact B1438327
  · exact B1438331
  · exact B1438335
  · exact B1438339
  · exact B1438343
  · exact B1438347
  · exact B1438351
  · exact B1438355
  · exact B1438359
  · exact B1438363
  · exact B1438367
  · exact B1438371
  · exact B1438375
  · exact B1438379
  · exact B1438383
  · exact B1438387
  · exact B1438391
  · exact B1438395
  · exact B1438399
  · exact B1438403
  · exact B1438407
  · exact B1438411
  · exact B1438415
  · exact B1438419
  · exact B1438423
  · exact B1438427
  · exact B1438431
  · exact B1438435
  · exact B1438439
  · exact B1438443
  · exact B1438447
  · exact B1438451
  · exact B1438455
  · exact B1438459
  · exact B1438463
  · exact B1438467
  · exact B1438471
  · exact B1438475
  · exact B1438479
  · exact B1438483
  · exact B1438487
  · exact B1438491
  · exact B1438495
  · exact B1438499
  · exact B1438503
  · exact B1438507
  · exact B1438511
  · exact B1438515
  · exact B1438519
  · exact B1438523
  · exact B1438527
  · exact B1438531
  · exact B1438535
  · exact B1438539
  · exact B1438543
  · exact B1438547
  · exact B1438551
  · exact B1438555
  · exact B1438559
  · exact B1438563
  · exact B1438567
  · exact B1438571
  · exact B1438575
  · exact B1438579
  · exact B1438583
  · exact B1438587
  · exact B1438591
  · exact B1438595
  · exact B1438599
  · exact B1438603
  · exact B1438607
  · exact B1438611
  · exact B1438615
  · exact B1438619
  · exact B1438623
  · exact B1438627
  · exact B1438631
  · exact B1438635
  · exact B1438639
  · exact B1438643
  · exact B1438647
  · exact B1438651
  · exact B1438655
  · exact B1438659
  · exact B1438663
  · exact B1438667
  · exact B1438671
  · exact B1438675
  · exact B1438679
  · exact B1438683
  · exact B1438687
  · exact B1438691
  · exact B1438695
  · exact B1438699
  · exact B1438703
  · exact B1438707
  · exact B1438711
  · exact B1438715
  · exact B1438719
  · exact B1438723
  · exact B1438727
  · exact B1438731
  · exact B1438735
  · exact B1438739
  · exact B1438743
  · exact B1438747
  · exact B1438751
  · exact B1438755
  · exact B1438759
  · exact B1438763
  · exact B1438767
  · exact B1438771
  · exact B1438775
  · exact B1438779
  · exact B1438783
  · exact B1438787
  · exact B1438791
  · exact B1438795
  · exact B1438799
  · exact B1438803
  · exact B1438807
  · exact B1438811
  · exact B1438815
  · exact B1438819
  · exact B1438823
  · exact B1438827
  · exact B1438831
  · exact B1438835
  · exact B1438839
  · exact B1438843
  · exact B1438847
  · exact B1438851
  · exact B1438855
  · exact B1438859
  · exact B1438863
  · exact B1438867
  · exact B1438871
  · exact B1438875
  · exact B1438879
  · exact B1438883
  · exact B1438887
  · exact B1438891
  · exact B1438895
  · exact B1438899
  · exact B1438903
  · exact B1438907
  · exact B1438911
  · exact B1438915
  · exact B1438919
  · exact B1438923
  · exact B1438927
  · exact B1438931
  · exact B1438935
  · exact B1438939
  · exact B1438943
  · exact B1438947
  · exact B1438951
  · exact B1438955
  · exact B1438959
  · exact B1438963
  · exact B1438967
  · exact B1438971
  · exact B1438975
  · exact B1438979
  · exact B1438983
  · exact B1438987
  · exact B1438991
  · exact B1438995
  · exact B1438999
  · exact B1439003
  · exact B1439007
  · exact B1439011
  · exact B1439015
  · exact B1439019
  · exact B1439023
  · exact B1439027
  · exact B1439031
  · exact B1439035
  · exact B1439039
  · exact B1439043
  · exact B1439047
  · exact B1439051
  · exact B1439055
  · exact B1439059
  · exact B1439063
  · exact B1439067
  · exact B1439071
  · exact B1439075
  · exact B1439079
  · exact B1439083
  · exact B1439087
  · exact B1439091
  · exact B1439095
  · exact B1439099
  · exact B1439103
  · exact B1439107
  · exact B1439111
  · exact B1439115
  · exact B1439119
  · exact B1439123
  · exact B1439127
  · exact B1439131
  · exact B1439135
  · exact B1439139
  · exact B1439143
  · exact B1439147
  · exact B1439151
  · exact B1439155
  · exact B1439159
  · exact B1439163
  · exact B1439167
  · exact B1439171
  · exact B1439175
  · exact B1439179
  · exact B1439183
  · exact B1439187
  · exact B1439191
  · exact B1439195
  · exact B1439199
  · exact B1439203
  · exact B1439207
  · exact B1439211
  · exact B1439215
  · exact B1439219
  · exact B1439223
  · exact B1439227
  · exact B1439231
  · exact B1439235
  · exact B1439239
  · exact B1439243
  · exact B1439247
  · exact B1439251
  · exact B1439255
  · exact B1439259
  · exact B1439263
  · exact B1439267
  · exact B1439271
  · exact B1439275
  · exact B1439279
  · exact B1439283
  · exact B1439287
  · exact B1439291
  · exact B1439295
  · exact B1439299
  · exact B1439303
  · exact B1439307
  · exact B1439311
  · exact B1439315
  · exact B1439319
  · exact B1439323
  · exact B1439327
  · exact B1439331
  · exact B1439335
  · exact B1439339
  · exact B1439343
  · exact B1439347
  · exact B1439351
  · exact B1439355
  · exact B1439359
  · exact B1439363
  · exact B1439367
  · exact B1439371
  · exact B1439375
  · exact B1439379
  · exact B1439383
  · exact B1439387
  · exact B1439391
  · exact B1439395
  · exact B1439399
  · exact B1439403
  · exact B1439407
  · exact B1439411
  · exact B1439415
  · exact B1439419
  · exact B1439423
  · exact B1439427
  · exact B1439431
  · exact B1439435
  · exact B1439439
  · exact B1439443
  · exact B1439447
  · exact B1439451
  · exact B1439455
  · exact B1439459
  · exact B1439463
  · exact B1439467
  · exact B1439471
  · exact B1439475
  · exact B1439479
  · exact B1439483
  · exact B1439487
  · exact B1439491
  · exact B1439495
  · exact B1439499
  · exact B1439503
  · exact B1439507
  · exact B1439511
  · exact B1439515
  · exact B1439519
  · exact B1439523
  · exact B1439527
  · exact B1439531
  · exact B1439535

theorem solution (m : ℕ) (hlo : 1437538 ≤ m) (hhi : m ≤ 1439538) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 359384 ≤ j := by omega
    have hj2 : j ≤ 359883 := by omega
    have hb : Blo 1437538 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
