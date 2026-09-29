-- Prove2me | solution 1 for syracuse_descends_range_1715058_1717058
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:28:36.455065+00:00
-- url     : https://prove2.me/submissions/ddc6c841-4ea7-4ecc-b61d-2ca3324a2c0c

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


theorem B1957897 : Blo 1715058 1957897 := bbase (se 2 (by rfl) ⟨734211, by rfl⟩ : syracuseStep 1957897 = 1468423) (by norm_num)
theorem B2170901 : Blo 1715058 2170901 := bbase (se 6 (by rfl) ⟨50880, by rfl⟩ : syracuseStep 2170901 = 101761) (by norm_num)
theorem B4636693 : Blo 1715058 4636693 := bbase (se 6 (by rfl) ⟨108672, by rfl⟩ : syracuseStep 4636693 = 217345) (by norm_num)
theorem B2170957 : Blo 1715058 2170957 := bbase (se 3 (by rfl) ⟨407054, by rfl⟩ : syracuseStep 2170957 = 814109) (by norm_num)
theorem B5791877 : Blo 1715058 5791877 := bbase (se 4 (by rfl) ⟨542988, by rfl⟩ : syracuseStep 5791877 = 1085977) (by norm_num)
theorem B8683685 : Blo 1715058 8683685 := bbase (se 4 (by rfl) ⟨814095, by rfl⟩ : syracuseStep 8683685 = 1628191) (by norm_num)
theorem B2171053 : Blo 1715058 2171053 := bbase (se 3 (by rfl) ⟨407072, by rfl⟩ : syracuseStep 2171053 = 814145) (by norm_num)
theorem B8249525 : Blo 1715058 8249525 := bbase (se 5 (by rfl) ⟨386696, by rfl⟩ : syracuseStep 8249525 = 773393) (by norm_num)
theorem B6955253 : Blo 1715058 6955253 := bbase (se 5 (by rfl) ⟨326027, by rfl⟩ : syracuseStep 6955253 = 652055) (by norm_num)
theorem B5873909 : Blo 1715058 5873909 := bbase (se 5 (by rfl) ⟨275339, by rfl⟩ : syracuseStep 5873909 = 550679) (by norm_num)
theorem B5497093 : Blo 1715058 5497093 := bbase (se 4 (by rfl) ⟨515352, by rfl⟩ : syracuseStep 5497093 = 1030705) (by norm_num)
theorem B4342045 : Blo 1715058 4342045 := bbase (se 3 (by rfl) ⟨814133, by rfl⟩ : syracuseStep 4342045 = 1628267) (by norm_num)
theorem B2572589 : Blo 1715058 2572589 := bbase (se 3 (by rfl) ⟨482360, by rfl⟩ : syracuseStep 2572589 = 964721) (by norm_num)
theorem B2572613 : Blo 1715058 2572613 := bbase (se 4 (by rfl) ⟨241182, by rfl⟩ : syracuseStep 2572613 = 482365) (by norm_num)
theorem B2171225 : Blo 1715058 2171225 := bbase (se 2 (by rfl) ⟨814209, by rfl⟩ : syracuseStep 2171225 = 1628419) (by norm_num)
theorem B2572637 : Blo 1715058 2572637 := bbase (se 3 (by rfl) ⟨482369, by rfl⟩ : syracuseStep 2572637 = 964739) (by norm_num)
theorem B2572661 : Blo 1715058 2572661 := bbase (se 5 (by rfl) ⟨120593, by rfl⟩ : syracuseStep 2572661 = 241187) (by norm_num)
theorem B2572685 : Blo 1715058 2572685 := bbase (se 3 (by rfl) ⟨482378, by rfl⟩ : syracuseStep 2572685 = 964757) (by norm_num)
theorem B4342157 : Blo 1715058 4342157 := bbase (se 3 (by rfl) ⟨814154, by rfl⟩ : syracuseStep 4342157 = 1628309) (by norm_num)
theorem B2171281 : Blo 1715058 2171281 := bbase (se 2 (by rfl) ⟨814230, by rfl⟩ : syracuseStep 2171281 = 1628461) (by norm_num)
theorem B2572709 : Blo 1715058 2572709 := bbase (se 4 (by rfl) ⟨241191, by rfl⟩ : syracuseStep 2572709 = 482383) (by norm_num)
theorem B2572733 : Blo 1715058 2572733 := bbase (se 3 (by rfl) ⟨482387, by rfl⟩ : syracuseStep 2572733 = 964775) (by norm_num)
theorem B3858893 : Blo 1715058 3858893 := bbase (se 3 (by rfl) ⟨723542, by rfl⟩ : syracuseStep 3858893 = 1447085) (by norm_num)
theorem B2572757 : Blo 1715058 2572757 := bbase (se 7 (by rfl) ⟨30149, by rfl⟩ : syracuseStep 2572757 = 60299) (by norm_num)
theorem B7053797 : Blo 1715058 7053797 := bbase (se 4 (by rfl) ⟨661293, by rfl⟩ : syracuseStep 7053797 = 1322587) (by norm_num)
theorem B2572781 : Blo 1715058 2572781 := bbase (se 3 (by rfl) ⟨482396, by rfl⟩ : syracuseStep 2572781 = 964793) (by norm_num)
theorem B2171377 : Blo 1715058 2171377 := bbase (se 2 (by rfl) ⟨814266, by rfl⟩ : syracuseStep 2171377 = 1628533) (by norm_num)
theorem B2572805 : Blo 1715058 2572805 := bbase (se 4 (by rfl) ⟨241200, by rfl⟩ : syracuseStep 2572805 = 482401) (by norm_num)
theorem B3858965 : Blo 1715058 3858965 := bbase (se 6 (by rfl) ⟨90444, by rfl⟩ : syracuseStep 3858965 = 180889) (by norm_num)
theorem B2572829 : Blo 1715058 2572829 := bbase (se 3 (by rfl) ⟨482405, by rfl⟩ : syracuseStep 2572829 = 964811) (by norm_num)
theorem B2572853 : Blo 1715058 2572853 := bbase (se 5 (by rfl) ⟨120602, by rfl⟩ : syracuseStep 2572853 = 241205) (by norm_num)
theorem B5792309 : Blo 1715058 5792309 := bbase (se 5 (by rfl) ⟨271514, by rfl⟩ : syracuseStep 5792309 = 543029) (by norm_num)
theorem B2572877 : Blo 1715058 2572877 := bbase (se 3 (by rfl) ⟨482414, by rfl⟩ : syracuseStep 2572877 = 964829) (by norm_num)
theorem B4342349 : Blo 1715058 4342349 := bbase (se 3 (by rfl) ⟨814190, by rfl⟩ : syracuseStep 4342349 = 1628381) (by norm_num)
theorem B3859037 : Blo 1715058 3859037 := bbase (se 3 (by rfl) ⟨723569, by rfl⟩ : syracuseStep 3859037 = 1447139) (by norm_num)
theorem B2572901 : Blo 1715058 2572901 := bbase (se 4 (by rfl) ⟨241209, by rfl⟩ : syracuseStep 2572901 = 482419) (by norm_num)
theorem B7938661 : Blo 1715058 7938661 := bbase (se 4 (by rfl) ⟨744249, by rfl⟩ : syracuseStep 7938661 = 1488499) (by norm_num)
theorem B2572925 : Blo 1715058 2572925 := bbase (se 3 (by rfl) ⟨482423, by rfl⟩ : syracuseStep 2572925 = 964847) (by norm_num)
theorem B2572949 : Blo 1715058 2572949 := bbase (se 6 (by rfl) ⟨60303, by rfl⟩ : syracuseStep 2572949 = 120607) (by norm_num)
theorem B2171549 : Blo 1715058 2171549 := bbase (se 3 (by rfl) ⟨407165, by rfl⟩ : syracuseStep 2171549 = 814331) (by norm_num)
theorem B3859109 : Blo 1715058 3859109 := bbase (se 4 (by rfl) ⟨361791, by rfl⟩ : syracuseStep 3859109 = 723583) (by norm_num)
theorem B2572973 : Blo 1715058 2572973 := bbase (se 3 (by rfl) ⟨482432, by rfl⟩ : syracuseStep 2572973 = 964865) (by norm_num)
theorem B2572997 : Blo 1715058 2572997 := bbase (se 4 (by rfl) ⟨241218, by rfl⟩ : syracuseStep 2572997 = 482437) (by norm_num)
theorem B2171605 : Blo 1715058 2171605 := bbase (se 7 (by rfl) ⟨25448, by rfl⟩ : syracuseStep 2171605 = 50897) (by norm_num)
theorem B2573021 : Blo 1715058 2573021 := bbase (se 3 (by rfl) ⟨482441, by rfl⟩ : syracuseStep 2573021 = 964883) (by norm_num)
theorem B3859181 : Blo 1715058 3859181 := bbase (se 3 (by rfl) ⟨723596, by rfl⟩ : syracuseStep 3859181 = 1447193) (by norm_num)
theorem B2573045 : Blo 1715058 2573045 := bbase (se 5 (by rfl) ⟨120611, by rfl⟩ : syracuseStep 2573045 = 241223) (by norm_num)
theorem B6185717 : Blo 1715058 6185717 := bbase (se 5 (by rfl) ⟨289955, by rfl⟩ : syracuseStep 6185717 = 579911) (by norm_num)
theorem B2573069 : Blo 1715058 2573069 := bbase (se 3 (by rfl) ⟨482450, by rfl⟩ : syracuseStep 2573069 = 964901) (by norm_num)
theorem B2573093 : Blo 1715058 2573093 := bbase (se 4 (by rfl) ⟨241227, by rfl⟩ : syracuseStep 2573093 = 482455) (by norm_num)
theorem B3859253 : Blo 1715058 3859253 := bbase (se 5 (by rfl) ⟨180902, by rfl⟩ : syracuseStep 3859253 = 361805) (by norm_num)
theorem B7824181 : Blo 1715058 7824181 := bbase (se 5 (by rfl) ⟨366758, by rfl⟩ : syracuseStep 7824181 = 733517) (by norm_num)
theorem B2171701 : Blo 1715058 2171701 := bbase (se 5 (by rfl) ⟨101798, by rfl⟩ : syracuseStep 2171701 = 203597) (by norm_num)
theorem B2573117 : Blo 1715058 2573117 := bbase (se 3 (by rfl) ⟨482459, by rfl⟩ : syracuseStep 2573117 = 964919) (by norm_num)
theorem B2786125 : Blo 1715058 2786125 := bbase (se 3 (by rfl) ⟨522398, by rfl⟩ : syracuseStep 2786125 = 1044797) (by norm_num)
theorem B2573141 : Blo 1715058 2573141 := bbase (se 9 (by rfl) ⟨7538, by rfl⟩ : syracuseStep 2573141 = 15077) (by norm_num)
theorem B6513493 : Blo 1715058 6513493 := bbase (se 9 (by rfl) ⟨19082, by rfl⟩ : syracuseStep 6513493 = 38165) (by norm_num)
theorem B2573165 : Blo 1715058 2573165 := bbase (se 3 (by rfl) ⟨482468, by rfl⟩ : syracuseStep 2573165 = 964937) (by norm_num)
theorem B3859325 : Blo 1715058 3859325 := bbase (se 3 (by rfl) ⟨723623, by rfl⟩ : syracuseStep 3859325 = 1447247) (by norm_num)
theorem B2573189 : Blo 1715058 2573189 := bbase (se 4 (by rfl) ⟨241236, by rfl⟩ : syracuseStep 2573189 = 482473) (by norm_num)
theorem B2573213 : Blo 1715058 2573213 := bbase (se 3 (by rfl) ⟨482477, by rfl⟩ : syracuseStep 2573213 = 964955) (by norm_num)
theorem B4342693 : Blo 1715058 4342693 := bbase (se 4 (by rfl) ⟨407127, by rfl⟩ : syracuseStep 4342693 = 814255) (by norm_num)
theorem B2573237 : Blo 1715058 2573237 := bbase (se 5 (by rfl) ⟨120620, by rfl⟩ : syracuseStep 2573237 = 241241) (by norm_num)
theorem B4121533 : Blo 1715058 4121533 := bbase (se 3 (by rfl) ⟨772787, by rfl⟩ : syracuseStep 4121533 = 1545575) (by norm_num)
theorem B3859397 : Blo 1715058 3859397 := bbase (se 4 (by rfl) ⟨361818, by rfl⟩ : syracuseStep 3859397 = 723637) (by norm_num)
theorem B2573261 : Blo 1715058 2573261 := bbase (se 3 (by rfl) ⟨482486, by rfl⟩ : syracuseStep 2573261 = 964973) (by norm_num)
theorem B2171873 : Blo 1715058 2171873 := bbase (se 2 (by rfl) ⟨814452, by rfl⟩ : syracuseStep 2171873 = 1628905) (by norm_num)
theorem B2573285 : Blo 1715058 2573285 := bbase (se 4 (by rfl) ⟨241245, by rfl⟩ : syracuseStep 2573285 = 482491) (by norm_num)
theorem B5792741 : Blo 1715058 5792741 := bbase (se 4 (by rfl) ⟨543069, by rfl⟩ : syracuseStep 5792741 = 1086139) (by norm_num)
theorem B2573309 : Blo 1715058 2573309 := bbase (se 3 (by rfl) ⟨482495, by rfl⟩ : syracuseStep 2573309 = 964991) (by norm_num)
theorem B8242181 : Blo 1715058 8242181 := bbase (se 4 (by rfl) ⟨772704, by rfl⟩ : syracuseStep 8242181 = 1545409) (by norm_num)
theorem B2442253 : Blo 1715058 2442253 := bbase (se 3 (by rfl) ⟨457922, by rfl⟩ : syracuseStep 2442253 = 915845) (by norm_num)
theorem B3859469 : Blo 1715058 3859469 := bbase (se 3 (by rfl) ⟨723650, by rfl⟩ : syracuseStep 3859469 = 1447301) (by norm_num)
theorem B2573333 : Blo 1715058 2573333 := bbase (se 6 (by rfl) ⟨60312, by rfl⟩ : syracuseStep 2573333 = 120625) (by norm_num)
theorem B4342805 : Blo 1715058 4342805 := bbase (se 6 (by rfl) ⟨101784, by rfl⟩ : syracuseStep 4342805 = 203569) (by norm_num)
theorem B14664725 : Blo 1715058 14664725 := bbase (se 6 (by rfl) ⟨343704, by rfl⟩ : syracuseStep 14664725 = 687409) (by norm_num)
theorem B2171929 : Blo 1715058 2171929 := bbase (se 2 (by rfl) ⟨814473, by rfl⟩ : syracuseStep 2171929 = 1628947) (by norm_num)
theorem B2573357 : Blo 1715058 2573357 := bbase (se 3 (by rfl) ⟨482504, by rfl⟩ : syracuseStep 2573357 = 965009) (by norm_num)
theorem B7824437 : Blo 1715058 7824437 := bbase (se 5 (by rfl) ⟨366770, by rfl⟩ : syracuseStep 7824437 = 733541) (by norm_num)
theorem B2573381 : Blo 1715058 2573381 := bbase (se 4 (by rfl) ⟨241254, by rfl⟩ : syracuseStep 2573381 = 482509) (by norm_num)
theorem B3859541 : Blo 1715058 3859541 := bbase (se 8 (by rfl) ⟨22614, by rfl⟩ : syracuseStep 3859541 = 45229) (by norm_num)
theorem B20866133 : Blo 1715058 20866133 := bbase (se 8 (by rfl) ⟨122262, by rfl⟩ : syracuseStep 20866133 = 244525) (by norm_num)
theorem B2573405 : Blo 1715058 2573405 := bbase (se 3 (by rfl) ⟨482513, by rfl⟩ : syracuseStep 2573405 = 965027) (by norm_num)
theorem B2573429 : Blo 1715058 2573429 := bbase (se 5 (by rfl) ⟨120629, by rfl⟩ : syracuseStep 2573429 = 241259) (by norm_num)
theorem B2172025 : Blo 1715058 2172025 := bbase (se 2 (by rfl) ⟨814509, by rfl⟩ : syracuseStep 2172025 = 1629019) (by norm_num)
theorem B6513797 : Blo 1715058 6513797 := bbase (se 4 (by rfl) ⟨610668, by rfl⟩ : syracuseStep 6513797 = 1221337) (by norm_num)
theorem B2573453 : Blo 1715058 2573453 := bbase (se 3 (by rfl) ⟨482522, by rfl⟩ : syracuseStep 2573453 = 965045) (by norm_num)
theorem B32998549 : Blo 1715058 32998549 := bbase (se 6 (by rfl) ⟨773403, by rfl⟩ : syracuseStep 32998549 = 1546807) (by norm_num)
theorem B3859613 : Blo 1715058 3859613 := bbase (se 3 (by rfl) ⟨723677, by rfl⟩ : syracuseStep 3859613 = 1447355) (by norm_num)
theorem B2573477 : Blo 1715058 2573477 := bbase (se 4 (by rfl) ⟨241263, by rfl⟩ : syracuseStep 2573477 = 482527) (by norm_num)
theorem B2573501 : Blo 1715058 2573501 := bbase (se 3 (by rfl) ⟨482531, by rfl⟩ : syracuseStep 2573501 = 965063) (by norm_num)
theorem B4342997 : Blo 1715058 4342997 := bbase (se 7 (by rfl) ⟨50894, by rfl⟩ : syracuseStep 4342997 = 101789) (by norm_num)
theorem B2573525 : Blo 1715058 2573525 := bbase (se 7 (by rfl) ⟨30158, by rfl⟩ : syracuseStep 2573525 = 60317) (by norm_num)
theorem B3859685 : Blo 1715058 3859685 := bbase (se 4 (by rfl) ⟨361845, by rfl⟩ : syracuseStep 3859685 = 723691) (by norm_num)
theorem B2442469 : Blo 1715058 2442469 := bbase (se 4 (by rfl) ⟨228981, by rfl⟩ : syracuseStep 2442469 = 457963) (by norm_num)
theorem B2573549 : Blo 1715058 2573549 := bbase (se 3 (by rfl) ⟨482540, by rfl⟩ : syracuseStep 2573549 = 965081) (by norm_num)
theorem B2090233 : Blo 1715058 2090233 := bbase (se 2 (by rfl) ⟨783837, by rfl⟩ : syracuseStep 2090233 = 1567675) (by norm_num)
theorem B3302653 : Blo 1715058 3302653 := bbase (se 3 (by rfl) ⟨619247, by rfl⟩ : syracuseStep 3302653 = 1238495) (by norm_num)
theorem B2573573 : Blo 1715058 2573573 := bbase (se 4 (by rfl) ⟨241272, by rfl⟩ : syracuseStep 2573573 = 482545) (by norm_num)
theorem B2573597 : Blo 1715058 2573597 := bbase (se 3 (by rfl) ⟨482549, by rfl⟩ : syracuseStep 2573597 = 965099) (by norm_num)
theorem B2172197 : Blo 1715058 2172197 := bbase (se 4 (by rfl) ⟨203643, by rfl⟩ : syracuseStep 2172197 = 407287) (by norm_num)
theorem B3859757 : Blo 1715058 3859757 := bbase (se 3 (by rfl) ⟨723704, by rfl⟩ : syracuseStep 3859757 = 1447409) (by norm_num)
theorem B3663157 : Blo 1715058 3663157 := bbase (se 5 (by rfl) ⟨171710, by rfl⟩ : syracuseStep 3663157 = 343421) (by norm_num)
theorem B2573621 : Blo 1715058 2573621 := bbase (se 5 (by rfl) ⟨120638, by rfl⟩ : syracuseStep 2573621 = 241277) (by norm_num)
theorem B2573645 : Blo 1715058 2573645 := bbase (se 3 (by rfl) ⟨482558, by rfl⟩ : syracuseStep 2573645 = 965117) (by norm_num)
theorem B2172253 : Blo 1715058 2172253 := bbase (se 3 (by rfl) ⟨407297, by rfl⟩ : syracuseStep 2172253 = 814595) (by norm_num)
theorem B2573669 : Blo 1715058 2573669 := bbase (se 4 (by rfl) ⟨241281, by rfl⟩ : syracuseStep 2573669 = 482563) (by norm_num)
theorem B3859829 : Blo 1715058 3859829 := bbase (se 5 (by rfl) ⟨180929, by rfl⟩ : syracuseStep 3859829 = 361859) (by norm_num)
theorem B2573693 : Blo 1715058 2573693 := bbase (se 3 (by rfl) ⟨482567, by rfl⟩ : syracuseStep 2573693 = 965135) (by norm_num)
theorem B2573717 : Blo 1715058 2573717 := bbase (se 6 (by rfl) ⟨60321, by rfl⟩ : syracuseStep 2573717 = 120643) (by norm_num)
theorem B5793173 : Blo 1715058 5793173 := bbase (se 6 (by rfl) ⟨135777, by rfl⟩ : syracuseStep 5793173 = 271555) (by norm_num)
theorem B2573741 : Blo 1715058 2573741 := bbase (se 3 (by rfl) ⟨482576, by rfl⟩ : syracuseStep 2573741 = 965153) (by norm_num)
theorem B8684981 : Blo 1715058 8684981 := bbase (se 5 (by rfl) ⟨407108, by rfl⟩ : syracuseStep 8684981 = 814217) (by norm_num)
theorem B3859901 : Blo 1715058 3859901 := bbase (se 3 (by rfl) ⟨723731, by rfl⟩ : syracuseStep 3859901 = 1447463) (by norm_num)
theorem B2172349 : Blo 1715058 2172349 := bbase (se 3 (by rfl) ⟨407315, by rfl⟩ : syracuseStep 2172349 = 814631) (by norm_num)
theorem B2573765 : Blo 1715058 2573765 := bbase (se 4 (by rfl) ⟨241290, by rfl⟩ : syracuseStep 2573765 = 482581) (by norm_num)
theorem B2573789 : Blo 1715058 2573789 := bbase (se 3 (by rfl) ⟨482585, by rfl⟩ : syracuseStep 2573789 = 965171) (by norm_num)
theorem B2573813 : Blo 1715058 2573813 := bbase (se 5 (by rfl) ⟨120647, by rfl⟩ : syracuseStep 2573813 = 241295) (by norm_num)
theorem B3859973 : Blo 1715058 3859973 := bbase (se 4 (by rfl) ⟨361872, by rfl⟩ : syracuseStep 3859973 = 723745) (by norm_num)
theorem B2573837 : Blo 1715058 2573837 := bbase (se 3 (by rfl) ⟨482594, by rfl⟩ : syracuseStep 2573837 = 965189) (by norm_num)
theorem B2573861 : Blo 1715058 2573861 := bbase (se 4 (by rfl) ⟨241299, by rfl⟩ : syracuseStep 2573861 = 482599) (by norm_num)
theorem B4343341 : Blo 1715058 4343341 := bbase (se 3 (by rfl) ⟨814376, by rfl⟩ : syracuseStep 4343341 = 1628753) (by norm_num)
theorem B6956597 : Blo 1715058 6956597 := bbase (se 5 (by rfl) ⟨326090, by rfl⟩ : syracuseStep 6956597 = 652181) (by norm_num)
theorem B2573885 : Blo 1715058 2573885 := bbase (se 3 (by rfl) ⟨482603, by rfl⟩ : syracuseStep 2573885 = 965207) (by norm_num)
theorem B3860045 : Blo 1715058 3860045 := bbase (se 3 (by rfl) ⟨723758, by rfl⟩ : syracuseStep 3860045 = 1447517) (by norm_num)
theorem B2573909 : Blo 1715058 2573909 := bbase (se 8 (by rfl) ⟨15081, by rfl⟩ : syracuseStep 2573909 = 30163) (by norm_num)
theorem B2442845 : Blo 1715058 2442845 := bbase (se 3 (by rfl) ⟨458033, by rfl⟩ : syracuseStep 2442845 = 916067) (by norm_num)
theorem B2172521 : Blo 1715058 2172521 := bbase (se 2 (by rfl) ⟨814695, by rfl⟩ : syracuseStep 2172521 = 1629391) (by norm_num)
theorem B2573933 : Blo 1715058 2573933 := bbase (se 3 (by rfl) ⟨482612, by rfl⟩ : syracuseStep 2573933 = 965225) (by norm_num)
theorem B4122245 : Blo 1715058 4122245 := bbase (se 4 (by rfl) ⟨386460, by rfl⟩ : syracuseStep 4122245 = 772921) (by norm_num)
theorem B2573957 : Blo 1715058 2573957 := bbase (se 4 (by rfl) ⟨241308, by rfl⟩ : syracuseStep 2573957 = 482617) (by norm_num)
theorem B27821717 : Blo 1715058 27821717 := bbase (se 6 (by rfl) ⟨652071, by rfl⟩ : syracuseStep 27821717 = 1304143) (by norm_num)
theorem B3860117 : Blo 1715058 3860117 := bbase (se 6 (by rfl) ⟨90471, by rfl⟩ : syracuseStep 3860117 = 180943) (by norm_num)
theorem B4343453 : Blo 1715058 4343453 := bbase (se 3 (by rfl) ⟨814397, by rfl⟩ : syracuseStep 4343453 = 1628795) (by norm_num)
theorem B2573981 : Blo 1715058 2573981 := bbase (se 3 (by rfl) ⟨482621, by rfl⟩ : syracuseStep 2573981 = 965243) (by norm_num)
theorem B2172577 : Blo 1715058 2172577 := bbase (se 2 (by rfl) ⟨814716, by rfl⟩ : syracuseStep 2172577 = 1629433) (by norm_num)
theorem B2574005 : Blo 1715058 2574005 := bbase (se 5 (by rfl) ⟨120656, by rfl⟩ : syracuseStep 2574005 = 241313) (by norm_num)
theorem B2574029 : Blo 1715058 2574029 := bbase (se 3 (by rfl) ⟨482630, by rfl⟩ : syracuseStep 2574029 = 965261) (by norm_num)
theorem B3860189 : Blo 1715058 3860189 := bbase (se 3 (by rfl) ⟨723785, by rfl⟩ : syracuseStep 3860189 = 1447571) (by norm_num)
theorem B2574053 : Blo 1715058 2574053 := bbase (se 4 (by rfl) ⟨241317, by rfl⟩ : syracuseStep 2574053 = 482635) (by norm_num)
theorem B2574077 : Blo 1715058 2574077 := bbase (se 3 (by rfl) ⟨482639, by rfl⟩ : syracuseStep 2574077 = 965279) (by norm_num)
theorem B2172673 : Blo 1715058 2172673 := bbase (se 2 (by rfl) ⟨814752, by rfl⟩ : syracuseStep 2172673 = 1629505) (by norm_num)
theorem B1738513 : Blo 1715058 1738513 := bbase (se 2 (by rfl) ⟨651942, by rfl⟩ : syracuseStep 1738513 = 1303885) (by norm_num)
theorem B2574101 : Blo 1715058 2574101 := bbase (se 6 (by rfl) ⟨60330, by rfl⟩ : syracuseStep 2574101 = 120661) (by norm_num)
theorem B3860261 : Blo 1715058 3860261 := bbase (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) (by norm_num)
theorem B2574125 : Blo 1715058 2574125 := bbase (se 3 (by rfl) ⟨482648, by rfl⟩ : syracuseStep 2574125 = 965297) (by norm_num)
theorem B2574149 : Blo 1715058 2574149 := bbase (se 4 (by rfl) ⟨241326, by rfl⟩ : syracuseStep 2574149 = 482653) (by norm_num)
theorem B5793605 : Blo 1715058 5793605 := bbase (se 4 (by rfl) ⟨543150, by rfl⟩ : syracuseStep 5793605 = 1086301) (by norm_num)
theorem B4343645 : Blo 1715058 4343645 := bbase (se 3 (by rfl) ⟨814433, by rfl⟩ : syracuseStep 4343645 = 1628867) (by norm_num)
theorem B2574173 : Blo 1715058 2574173 := bbase (se 3 (by rfl) ⟨482657, by rfl⟩ : syracuseStep 2574173 = 965315) (by norm_num)
theorem B3860333 : Blo 1715058 3860333 := bbase (se 3 (by rfl) ⟨723812, by rfl⟩ : syracuseStep 3860333 = 1447625) (by norm_num)
theorem B2574197 : Blo 1715058 2574197 := bbase (se 5 (by rfl) ⟨120665, by rfl⟩ : syracuseStep 2574197 = 241331) (by norm_num)
theorem B10438517 : Blo 1715058 10438517 := bbase (se 5 (by rfl) ⟨489305, by rfl⟩ : syracuseStep 10438517 = 978611) (by norm_num)
theorem B2574221 : Blo 1715058 2574221 := bbase (se 3 (by rfl) ⟨482666, by rfl⟩ : syracuseStep 2574221 = 965333) (by norm_num)
theorem B2574245 : Blo 1715058 2574245 := bbase (se 4 (by rfl) ⟨241335, by rfl⟩ : syracuseStep 2574245 = 482671) (by norm_num)
theorem B2172845 : Blo 1715058 2172845 := bbase (se 3 (by rfl) ⟨407408, by rfl⟩ : syracuseStep 2172845 = 814817) (by norm_num)
theorem B3860405 : Blo 1715058 3860405 := bbase (se 5 (by rfl) ⟨180956, by rfl⟩ : syracuseStep 3860405 = 361913) (by norm_num)
theorem B2574269 : Blo 1715058 2574269 := bbase (se 3 (by rfl) ⟨482675, by rfl⟩ : syracuseStep 2574269 = 965351) (by norm_num)
theorem B4884437 : Blo 1715058 4884437 := bbase (se 7 (by rfl) ⟨57239, by rfl⟩ : syracuseStep 4884437 = 114479) (by norm_num)
theorem B2574293 : Blo 1715058 2574293 := bbase (se 7 (by rfl) ⟨30167, by rfl⟩ : syracuseStep 2574293 = 60335) (by norm_num)
theorem B5498837 : Blo 1715058 5498837 := bbase (se 7 (by rfl) ⟨64439, by rfl⟩ : syracuseStep 5498837 = 128879) (by norm_num)
theorem B4401125 : Blo 1715058 4401125 := bbase (se 4 (by rfl) ⟨412605, by rfl⟩ : syracuseStep 4401125 = 825211) (by norm_num)
theorem B2172901 : Blo 1715058 2172901 := bbase (se 4 (by rfl) ⟨203709, by rfl⟩ : syracuseStep 2172901 = 407419) (by norm_num)
theorem B2574317 : Blo 1715058 2574317 := bbase (se 3 (by rfl) ⟨482684, by rfl⟩ : syracuseStep 2574317 = 965369) (by norm_num)
theorem B3860477 : Blo 1715058 3860477 := bbase (se 3 (by rfl) ⟨723839, by rfl⟩ : syracuseStep 3860477 = 1447679) (by norm_num)
theorem B4122629 : Blo 1715058 4122629 := bbase (se 4 (by rfl) ⟨386496, by rfl⟩ : syracuseStep 4122629 = 772993) (by norm_num)
theorem B2574341 : Blo 1715058 2574341 := bbase (se 4 (by rfl) ⟨241344, by rfl⟩ : syracuseStep 2574341 = 482689) (by norm_num)
theorem B2574365 : Blo 1715058 2574365 := bbase (se 3 (by rfl) ⟨482693, by rfl⟩ : syracuseStep 2574365 = 965387) (by norm_num)
theorem B2574389 : Blo 1715058 2574389 := bbase (se 5 (by rfl) ⟨120674, by rfl⟩ : syracuseStep 2574389 = 241349) (by norm_num)
theorem B3860549 : Blo 1715058 3860549 := bbase (se 4 (by rfl) ⟨361926, by rfl⟩ : syracuseStep 3860549 = 723853) (by norm_num)
theorem B2172997 : Blo 1715058 2172997 := bbase (se 4 (by rfl) ⟨203718, by rfl⟩ : syracuseStep 2172997 = 407437) (by norm_num)
theorem B2574413 : Blo 1715058 2574413 := bbase (se 3 (by rfl) ⟨482702, by rfl⟩ : syracuseStep 2574413 = 965405) (by norm_num)
theorem B1738837 : Blo 1715058 1738837 := bbase (se 8 (by rfl) ⟨10188, by rfl⟩ : syracuseStep 1738837 = 20377) (by norm_num)
theorem B2476117 : Blo 1715058 2476117 := bbase (se 8 (by rfl) ⟨14508, by rfl⟩ : syracuseStep 2476117 = 29017) (by norm_num)
theorem B2574437 : Blo 1715058 2574437 := bbase (se 4 (by rfl) ⟨241353, by rfl⟩ : syracuseStep 2574437 = 482707) (by norm_num)
theorem B2574461 : Blo 1715058 2574461 := bbase (se 3 (by rfl) ⟨482711, by rfl⟩ : syracuseStep 2574461 = 965423) (by norm_num)
theorem B3860621 : Blo 1715058 3860621 := bbase (se 3 (by rfl) ⟨723866, by rfl⟩ : syracuseStep 3860621 = 1447733) (by norm_num)
theorem B2320525 : Blo 1715058 2320525 := bbase (se 3 (by rfl) ⟨435098, by rfl⟩ : syracuseStep 2320525 = 870197) (by norm_num)
theorem B2574485 : Blo 1715058 2574485 := bbase (se 6 (by rfl) ⟨60339, by rfl⟩ : syracuseStep 2574485 = 120679) (by norm_num)
theorem B5499029 : Blo 1715058 5499029 := bbase (se 6 (by rfl) ⟨128883, by rfl⟩ : syracuseStep 5499029 = 257767) (by norm_num)
theorem B3664045 : Blo 1715058 3664045 := bbase (se 3 (by rfl) ⟨687008, by rfl⟩ : syracuseStep 3664045 = 1374017) (by norm_num)
theorem B2574509 : Blo 1715058 2574509 := bbase (se 3 (by rfl) ⟨482720, by rfl⟩ : syracuseStep 2574509 = 965441) (by norm_num)
theorem B4343989 : Blo 1715058 4343989 := bbase (se 5 (by rfl) ⟨203624, by rfl⟩ : syracuseStep 4343989 = 407249) (by norm_num)
theorem B2574533 : Blo 1715058 2574533 := bbase (se 4 (by rfl) ⟨241362, by rfl⟩ : syracuseStep 2574533 = 482725) (by norm_num)
theorem B3860693 : Blo 1715058 3860693 := bbase (se 7 (by rfl) ⟨45242, by rfl⟩ : syracuseStep 3860693 = 90485) (by norm_num)
theorem B2574557 : Blo 1715058 2574557 := bbase (se 3 (by rfl) ⟨482729, by rfl⟩ : syracuseStep 2574557 = 965459) (by norm_num)
theorem B5572853 : Blo 1715058 5572853 := bbase (se 5 (by rfl) ⟨261227, by rfl⟩ : syracuseStep 5572853 = 522455) (by norm_num)
theorem B2574581 : Blo 1715058 2574581 := bbase (se 5 (by rfl) ⟨120683, by rfl⟩ : syracuseStep 2574581 = 241367) (by norm_num)
theorem B5794037 : Blo 1715058 5794037 := bbase (se 5 (by rfl) ⟨271595, by rfl⟩ : syracuseStep 5794037 = 543191) (by norm_num)
theorem B2574605 : Blo 1715058 2574605 := bbase (se 3 (by rfl) ⟨482738, by rfl⟩ : syracuseStep 2574605 = 965477) (by norm_num)
theorem B3860765 : Blo 1715058 3860765 := bbase (se 3 (by rfl) ⟨723893, by rfl⟩ : syracuseStep 3860765 = 1447787) (by norm_num)
theorem B4122917 : Blo 1715058 4122917 := bbase (se 4 (by rfl) ⟨386523, by rfl⟩ : syracuseStep 4122917 = 773047) (by norm_num)
theorem B4344101 : Blo 1715058 4344101 := bbase (se 4 (by rfl) ⟨407259, by rfl⟩ : syracuseStep 4344101 = 814519) (by norm_num)
theorem B2574629 : Blo 1715058 2574629 := bbase (se 4 (by rfl) ⟨241371, by rfl⟩ : syracuseStep 2574629 = 482743) (by norm_num)
theorem B2574653 : Blo 1715058 2574653 := bbase (se 3 (by rfl) ⟨482747, by rfl⟩ : syracuseStep 2574653 = 965495) (by norm_num)
theorem B2574677 : Blo 1715058 2574677 := bbase (se 10 (by rfl) ⟨3771, by rfl⟩ : syracuseStep 2574677 = 7543) (by norm_num)
theorem B3860837 : Blo 1715058 3860837 := bbase (se 4 (by rfl) ⟨361953, by rfl⟩ : syracuseStep 3860837 = 723907) (by norm_num)
theorem B2574701 : Blo 1715058 2574701 := bbase (se 3 (by rfl) ⟨482756, by rfl⟩ : syracuseStep 2574701 = 965513) (by norm_num)
theorem B2894197 : Blo 1715058 2894197 := bbase (se 5 (by rfl) ⟨135665, by rfl⟩ : syracuseStep 2894197 = 271331) (by norm_num)
theorem B2574725 : Blo 1715058 2574725 := bbase (se 4 (by rfl) ⟨241380, by rfl⟩ : syracuseStep 2574725 = 482761) (by norm_num)
theorem B2574749 : Blo 1715058 2574749 := bbase (se 3 (by rfl) ⟨482765, by rfl⟩ : syracuseStep 2574749 = 965531) (by norm_num)
theorem B3860909 : Blo 1715058 3860909 := bbase (se 3 (by rfl) ⟨723920, by rfl⟩ : syracuseStep 3860909 = 1447841) (by norm_num)
theorem B2574773 : Blo 1715058 2574773 := bbase (se 5 (by rfl) ⟨120692, by rfl⟩ : syracuseStep 2574773 = 241385) (by norm_num)
theorem B2894285 : Blo 1715058 2894285 := bbase (se 3 (by rfl) ⟨542678, by rfl⟩ : syracuseStep 2894285 = 1085357) (by norm_num)
theorem B2574797 : Blo 1715058 2574797 := bbase (se 3 (by rfl) ⟨482774, by rfl⟩ : syracuseStep 2574797 = 965549) (by norm_num)
theorem B2935253 : Blo 1715058 2935253 := bbase (se 7 (by rfl) ⟨34397, by rfl⟩ : syracuseStep 2935253 = 68795) (by norm_num)
theorem B4344293 : Blo 1715058 4344293 := bbase (se 4 (by rfl) ⟨407277, by rfl⟩ : syracuseStep 4344293 = 814555) (by norm_num)
theorem B2574821 : Blo 1715058 2574821 := bbase (se 4 (by rfl) ⟨241389, by rfl⟩ : syracuseStep 2574821 = 482779) (by norm_num)
theorem B3860981 : Blo 1715058 3860981 := bbase (se 5 (by rfl) ⟨180983, by rfl⟩ : syracuseStep 3860981 = 361967) (by norm_num)
theorem B2574845 : Blo 1715058 2574845 := bbase (se 3 (by rfl) ⟨482783, by rfl⟩ : syracuseStep 2574845 = 965567) (by norm_num)
theorem B2574869 : Blo 1715058 2574869 := bbase (se 6 (by rfl) ⟨60348, by rfl⟩ : syracuseStep 2574869 = 120697) (by norm_num)
theorem B2574893 : Blo 1715058 2574893 := bbase (se 3 (by rfl) ⟨482792, by rfl⟩ : syracuseStep 2574893 = 965585) (by norm_num)
theorem B3861053 : Blo 1715058 3861053 := bbase (se 3 (by rfl) ⟨723947, by rfl⟩ : syracuseStep 3861053 = 1447895) (by norm_num)
theorem B2574917 : Blo 1715058 2574917 := bbase (se 4 (by rfl) ⟨241398, by rfl⟩ : syracuseStep 2574917 = 482797) (by norm_num)
theorem B2894413 : Blo 1715058 2894413 := bbase (se 3 (by rfl) ⟨542702, by rfl⟩ : syracuseStep 2894413 = 1085405) (by norm_num)
theorem B2574941 : Blo 1715058 2574941 := bbase (se 3 (by rfl) ⟨482801, by rfl⟩ : syracuseStep 2574941 = 965603) (by norm_num)
theorem B2574965 : Blo 1715058 2574965 := bbase (se 5 (by rfl) ⟨120701, by rfl⟩ : syracuseStep 2574965 = 241403) (by norm_num)
theorem B3861125 : Blo 1715058 3861125 := bbase (se 4 (by rfl) ⟨361980, by rfl⟩ : syracuseStep 3861125 = 723961) (by norm_num)
theorem B2574989 : Blo 1715058 2574989 := bbase (se 3 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 2574989 = 965621) (by norm_num)
theorem B3664541 : Blo 1715058 3664541 := bbase (se 3 (by rfl) ⟨687101, by rfl⟩ : syracuseStep 3664541 = 1374203) (by norm_num)
theorem B2894501 : Blo 1715058 2894501 := bbase (se 4 (by rfl) ⟨271359, by rfl⟩ : syracuseStep 2894501 = 542719) (by norm_num)
theorem B2575013 : Blo 1715058 2575013 := bbase (se 4 (by rfl) ⟨241407, by rfl⟩ : syracuseStep 2575013 = 482815) (by norm_num)
theorem B5794469 : Blo 1715058 5794469 := bbase (se 4 (by rfl) ⟨543231, by rfl⟩ : syracuseStep 5794469 = 1086463) (by norm_num)
theorem B2607805 : Blo 1715058 2607805 := bbase (se 3 (by rfl) ⟨488963, by rfl⟩ : syracuseStep 2607805 = 977927) (by norm_num)
theorem B2575037 : Blo 1715058 2575037 := bbase (se 3 (by rfl) ⟨482819, by rfl⟩ : syracuseStep 2575037 = 965639) (by norm_num)
theorem B8686277 : Blo 1715058 8686277 := bbase (se 4 (by rfl) ⟨814338, by rfl⟩ : syracuseStep 8686277 = 1628677) (by norm_num)
theorem B3861197 : Blo 1715058 3861197 := bbase (se 3 (by rfl) ⟨723974, by rfl⟩ : syracuseStep 3861197 = 1447949) (by norm_num)
theorem B2575061 : Blo 1715058 2575061 := bbase (se 7 (by rfl) ⟨30176, by rfl⟩ : syracuseStep 2575061 = 60353) (by norm_num)
theorem B2575085 : Blo 1715058 2575085 := bbase (se 3 (by rfl) ⟨482828, by rfl⟩ : syracuseStep 2575085 = 965657) (by norm_num)
theorem B4639493 : Blo 1715058 4639493 := bbase (se 4 (by rfl) ⟨434952, by rfl⟩ : syracuseStep 4639493 = 869905) (by norm_num)
theorem B2575109 : Blo 1715058 2575109 := bbase (se 4 (by rfl) ⟨241416, by rfl⟩ : syracuseStep 2575109 = 482833) (by norm_num)
theorem B3861269 : Blo 1715058 3861269 := bbase (se 6 (by rfl) ⟨90498, by rfl⟩ : syracuseStep 3861269 = 180997) (by norm_num)
theorem B2575133 : Blo 1715058 2575133 := bbase (se 3 (by rfl) ⟨482837, by rfl⟩ : syracuseStep 2575133 = 965675) (by norm_num)
theorem B2894629 : Blo 1715058 2894629 := bbase (se 4 (by rfl) ⟨271371, by rfl⟩ : syracuseStep 2894629 = 542743) (by norm_num)
theorem B2575157 : Blo 1715058 2575157 := bbase (se 5 (by rfl) ⟨120710, by rfl⟩ : syracuseStep 2575157 = 241421) (by norm_num)
theorem B4344637 : Blo 1715058 4344637 := bbase (se 3 (by rfl) ⟨814619, by rfl⟩ : syracuseStep 4344637 = 1629239) (by norm_num)
theorem B2575181 : Blo 1715058 2575181 := bbase (se 3 (by rfl) ⟨482846, by rfl⟩ : syracuseStep 2575181 = 965693) (by norm_num)
theorem B3861341 : Blo 1715058 3861341 := bbase (se 3 (by rfl) ⟨724001, by rfl⟩ : syracuseStep 3861341 = 1448003) (by norm_num)
theorem B2575205 : Blo 1715058 2575205 := bbase (se 4 (by rfl) ⟨241425, by rfl⟩ : syracuseStep 2575205 = 482851) (by norm_num)
theorem B2894717 : Blo 1715058 2894717 := bbase (se 3 (by rfl) ⟨542759, by rfl⟩ : syracuseStep 2894717 = 1085519) (by norm_num)
theorem B2575229 : Blo 1715058 2575229 := bbase (se 3 (by rfl) ⟨482855, by rfl⟩ : syracuseStep 2575229 = 965711) (by norm_num)
theorem B2575253 : Blo 1715058 2575253 := bbase (se 6 (by rfl) ⟨60357, by rfl⟩ : syracuseStep 2575253 = 120715) (by norm_num)
theorem B3861413 : Blo 1715058 3861413 := bbase (se 4 (by rfl) ⟨362007, by rfl⟩ : syracuseStep 3861413 = 724015) (by norm_num)
theorem B4344749 : Blo 1715058 4344749 := bbase (se 3 (by rfl) ⟨814640, by rfl⟩ : syracuseStep 4344749 = 1629281) (by norm_num)
theorem B2575277 : Blo 1715058 2575277 := bbase (se 3 (by rfl) ⟨482864, by rfl⟩ : syracuseStep 2575277 = 965729) (by norm_num)
theorem B4402109 : Blo 1715058 4402109 := bbase (se 3 (by rfl) ⟨825395, by rfl⟩ : syracuseStep 4402109 = 1650791) (by norm_num)
theorem B2575301 : Blo 1715058 2575301 := bbase (se 4 (by rfl) ⟨241434, by rfl⟩ : syracuseStep 2575301 = 482869) (by norm_num)
theorem B2575325 : Blo 1715058 2575325 := bbase (se 3 (by rfl) ⟨482873, by rfl⟩ : syracuseStep 2575325 = 965747) (by norm_num)
theorem B3861485 : Blo 1715058 3861485 := bbase (se 3 (by rfl) ⟨724028, by rfl⟩ : syracuseStep 3861485 = 1448057) (by norm_num)
theorem B2444269 : Blo 1715058 2444269 := bbase (se 3 (by rfl) ⟨458300, by rfl⟩ : syracuseStep 2444269 = 916601) (by norm_num)
theorem B2575349 : Blo 1715058 2575349 := bbase (se 5 (by rfl) ⟨120719, by rfl⟩ : syracuseStep 2575349 = 241439) (by norm_num)
theorem B2894845 : Blo 1715058 2894845 := bbase (se 3 (by rfl) ⟨542783, by rfl⟩ : syracuseStep 2894845 = 1085567) (by norm_num)
theorem B2575373 : Blo 1715058 2575373 := bbase (se 3 (by rfl) ⟨482882, by rfl⟩ : syracuseStep 2575373 = 965765) (by norm_num)
theorem B2575397 : Blo 1715058 2575397 := bbase (se 4 (by rfl) ⟨241443, by rfl⟩ : syracuseStep 2575397 = 482887) (by norm_num)
theorem B3861557 : Blo 1715058 3861557 := bbase (se 5 (by rfl) ⟨181010, by rfl⟩ : syracuseStep 3861557 = 362021) (by norm_num)
theorem B2575421 : Blo 1715058 2575421 := bbase (se 3 (by rfl) ⟨482891, by rfl⟩ : syracuseStep 2575421 = 965783) (by norm_num)
theorem B2894933 : Blo 1715058 2894933 := bbase (se 8 (by rfl) ⟨16962, by rfl⟩ : syracuseStep 2894933 = 33925) (by norm_num)
theorem B2575445 : Blo 1715058 2575445 := bbase (se 8 (by rfl) ⟨15090, by rfl⟩ : syracuseStep 2575445 = 30181) (by norm_num)
theorem B5794901 : Blo 1715058 5794901 := bbase (se 8 (by rfl) ⟨33954, by rfl⟩ : syracuseStep 5794901 = 67909) (by norm_num)
theorem B4344941 : Blo 1715058 4344941 := bbase (se 3 (by rfl) ⟨814676, by rfl⟩ : syracuseStep 4344941 = 1629353) (by norm_num)
theorem B2575469 : Blo 1715058 2575469 := bbase (se 3 (by rfl) ⟨482900, by rfl⟩ : syracuseStep 2575469 = 965801) (by norm_num)
theorem B9768053 : Blo 1715058 9768053 := bbase (se 5 (by rfl) ⟨457877, by rfl⟩ : syracuseStep 9768053 = 915755) (by norm_num)
theorem B3861629 : Blo 1715058 3861629 := bbase (se 3 (by rfl) ⟨724055, by rfl⟩ : syracuseStep 3861629 = 1448111) (by norm_num)
theorem B2575493 : Blo 1715058 2575493 := bbase (se 4 (by rfl) ⟨241452, by rfl⟩ : syracuseStep 2575493 = 482905) (by norm_num)
theorem B2575517 : Blo 1715058 2575517 := bbase (se 3 (by rfl) ⟨482909, by rfl⟩ : syracuseStep 2575517 = 965819) (by norm_num)
theorem B2575541 : Blo 1715058 2575541 := bbase (se 5 (by rfl) ⟨120728, by rfl⟩ : syracuseStep 2575541 = 241457) (by norm_num)
theorem B6515909 : Blo 1715058 6515909 := bbase (se 4 (by rfl) ⟨610866, by rfl⟩ : syracuseStep 6515909 = 1221733) (by norm_num)
theorem B3861701 : Blo 1715058 3861701 := bbase (se 4 (by rfl) ⟨362034, by rfl⟩ : syracuseStep 3861701 = 724069) (by norm_num)
theorem B2575565 : Blo 1715058 2575565 := bbase (se 3 (by rfl) ⟨482918, by rfl⟩ : syracuseStep 2575565 = 965837) (by norm_num)
theorem B15650005 : Blo 1715058 15650005 := bbase (se 7 (by rfl) ⟨183398, by rfl⟩ : syracuseStep 15650005 = 366797) (by norm_num)
theorem B2895061 : Blo 1715058 2895061 := bbase (se 7 (by rfl) ⟨33926, by rfl⟩ : syracuseStep 2895061 = 67853) (by norm_num)
theorem B3861773 : Blo 1715058 3861773 := bbase (se 3 (by rfl) ⟨724082, by rfl⟩ : syracuseStep 3861773 = 1448165) (by norm_num)
theorem B1740061 : Blo 1715058 1740061 := bbase (se 3 (by rfl) ⟨326261, by rfl⟩ : syracuseStep 1740061 = 652523) (by norm_num)
theorem B2895149 : Blo 1715058 2895149 := bbase (se 3 (by rfl) ⟨542840, by rfl⟩ : syracuseStep 2895149 = 1085681) (by norm_num)
theorem B3861845 : Blo 1715058 3861845 := bbase (se 11 (by rfl) ⟨2828, by rfl⟩ : syracuseStep 3861845 = 5657) (by norm_num)
theorem B2936189 : Blo 1715058 2936189 := bbase (se 3 (by rfl) ⟨550535, by rfl⟩ : syracuseStep 2936189 = 1101071) (by norm_num)
theorem B13036949 : Blo 1715058 13036949 := bbase (se 6 (by rfl) ⟨305553, by rfl⟩ : syracuseStep 13036949 = 611107) (by norm_num)
theorem B3861917 : Blo 1715058 3861917 := bbase (se 3 (by rfl) ⟨724109, by rfl⟩ : syracuseStep 3861917 = 1448219) (by norm_num)
theorem B2895277 : Blo 1715058 2895277 := bbase (se 3 (by rfl) ⟨542864, by rfl⟩ : syracuseStep 2895277 = 1085729) (by norm_num)
theorem B4345285 : Blo 1715058 4345285 := bbase (se 4 (by rfl) ⟨407370, by rfl⟩ : syracuseStep 4345285 = 814741) (by norm_num)
theorem B9530837 : Blo 1715058 9530837 := bbase (se 7 (by rfl) ⟨111689, by rfl⟩ : syracuseStep 9530837 = 223379) (by norm_num)
theorem B6516197 : Blo 1715058 6516197 := bbase (se 4 (by rfl) ⟨610893, by rfl⟩ : syracuseStep 6516197 = 1221787) (by norm_num)
theorem B3861989 : Blo 1715058 3861989 := bbase (se 4 (by rfl) ⟨362061, by rfl⟩ : syracuseStep 3861989 = 724123) (by norm_num)
theorem B14855669 : Blo 1715058 14855669 := bbase (se 5 (by rfl) ⟨696359, by rfl⟩ : syracuseStep 14855669 = 1392719) (by norm_num)
theorem B3665405 : Blo 1715058 3665405 := bbase (se 3 (by rfl) ⟨687263, by rfl⟩ : syracuseStep 3665405 = 1374527) (by norm_num)
theorem B2895365 : Blo 1715058 2895365 := bbase (se 4 (by rfl) ⟨271440, by rfl⟩ : syracuseStep 2895365 = 542881) (by norm_num)
theorem B4886021 : Blo 1715058 4886021 := bbase (se 4 (by rfl) ⟨458064, by rfl⟩ : syracuseStep 4886021 = 916129) (by norm_num)
theorem B3862061 : Blo 1715058 3862061 := bbase (se 3 (by rfl) ⟨724136, by rfl⟩ : syracuseStep 3862061 = 1448273) (by norm_num)
theorem B4345397 : Blo 1715058 4345397 := bbase (se 5 (by rfl) ⟨203690, by rfl⟩ : syracuseStep 4345397 = 407381) (by norm_num)
theorem B2010685 : Blo 1715058 2010685 := bbase (se 3 (by rfl) ⟨377003, by rfl⟩ : syracuseStep 2010685 = 754007) (by norm_num)
theorem B3862133 : Blo 1715058 3862133 := bbase (se 5 (by rfl) ⟨181037, by rfl⟩ : syracuseStep 3862133 = 362075) (by norm_num)
theorem B2895493 : Blo 1715058 2895493 := bbase (se 4 (by rfl) ⟨271452, by rfl⟩ : syracuseStep 2895493 = 542905) (by norm_num)
theorem B3665549 : Blo 1715058 3665549 := bbase (se 3 (by rfl) ⟨687290, by rfl⟩ : syracuseStep 3665549 = 1374581) (by norm_num)
theorem B3862205 : Blo 1715058 3862205 := bbase (se 3 (by rfl) ⟨724163, by rfl⟩ : syracuseStep 3862205 = 1448327) (by norm_num)
theorem B8244949 : Blo 1715058 8244949 := bbase (se 7 (by rfl) ⟨96620, by rfl⟩ : syracuseStep 8244949 = 193241) (by norm_num)
theorem B2895581 : Blo 1715058 2895581 := bbase (se 3 (by rfl) ⟨542921, by rfl⟩ : syracuseStep 2895581 = 1085843) (by norm_num)
theorem B4345589 : Blo 1715058 4345589 := bbase (se 5 (by rfl) ⟨203699, by rfl⟩ : syracuseStep 4345589 = 407399) (by norm_num)
theorem B3862277 : Blo 1715058 3862277 := bbase (se 4 (by rfl) ⟨362088, by rfl⟩ : syracuseStep 3862277 = 724177) (by norm_num)
theorem B3256109 : Blo 1715058 3256109 := bbase (se 3 (by rfl) ⟨610520, by rfl⟩ : syracuseStep 3256109 = 1221041) (by norm_num)
theorem B13029173 : Blo 1715058 13029173 := bbase (se 5 (by rfl) ⟨610742, by rfl⟩ : syracuseStep 13029173 = 1221485) (by norm_num)
theorem B3862349 : Blo 1715058 3862349 := bbase (se 3 (by rfl) ⟨724190, by rfl⟩ : syracuseStep 3862349 = 1448381) (by norm_num)
theorem B18550613 : Blo 1715058 18550613 := bbase (se 9 (by rfl) ⟨54347, by rfl⟩ : syracuseStep 18550613 = 108695) (by norm_num)
theorem B2895709 : Blo 1715058 2895709 := bbase (se 3 (by rfl) ⟨542945, by rfl⟩ : syracuseStep 2895709 = 1085891) (by norm_num)
theorem B3862421 : Blo 1715058 3862421 := bbase (se 6 (by rfl) ⟨90525, by rfl⟩ : syracuseStep 3862421 = 181051) (by norm_num)
theorem B2011049 : Blo 1715058 2011049 := bbase (se 2 (by rfl) ⟨754143, by rfl⟩ : syracuseStep 2011049 = 1508287) (by norm_num)
theorem B2895797 : Blo 1715058 2895797 := bbase (se 5 (by rfl) ⟨135740, by rfl⟩ : syracuseStep 2895797 = 271481) (by norm_num)
theorem B8687573 : Blo 1715058 8687573 := bbase (se 7 (by rfl) ⟨101807, by rfl⟩ : syracuseStep 8687573 = 203615) (by norm_num)
theorem B3862493 : Blo 1715058 3862493 := bbase (se 3 (by rfl) ⟨724217, by rfl⟩ : syracuseStep 3862493 = 1448435) (by norm_num)
theorem B11145205 : Blo 1715058 11145205 := bbase (se 5 (by rfl) ⟨522431, by rfl⟩ : syracuseStep 11145205 = 1044863) (by norm_num)
theorem B8802325 : Blo 1715058 8802325 := bbase (se 6 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 8802325 = 412609) (by norm_num)
theorem B3862565 : Blo 1715058 3862565 := bbase (se 4 (by rfl) ⟨362115, by rfl⟩ : syracuseStep 3862565 = 724231) (by norm_num)
theorem B2895925 : Blo 1715058 2895925 := bbase (se 5 (by rfl) ⟨135746, by rfl⟩ : syracuseStep 2895925 = 271493) (by norm_num)
theorem B4345933 : Blo 1715058 4345933 := bbase (se 3 (by rfl) ⟨814862, by rfl⟩ : syracuseStep 4345933 = 1629725) (by norm_num)
theorem B2748509 : Blo 1715058 2748509 := bbase (se 3 (by rfl) ⟨515345, by rfl⟩ : syracuseStep 2748509 = 1030691) (by norm_num)
theorem B3862637 : Blo 1715058 3862637 := bbase (se 3 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 3862637 = 1448489) (by norm_num)
theorem B2896013 : Blo 1715058 2896013 := bbase (se 3 (by rfl) ⟨543002, by rfl⟩ : syracuseStep 2896013 = 1086005) (by norm_num)
theorem B4886693 : Blo 1715058 4886693 := bbase (se 4 (by rfl) ⟨458127, by rfl⟩ : syracuseStep 4886693 = 916255) (by norm_num)
theorem B3862709 : Blo 1715058 3862709 := bbase (se 5 (by rfl) ⟨181064, by rfl⟩ : syracuseStep 3862709 = 362129) (by norm_num)
theorem B4346045 : Blo 1715058 4346045 := bbase (se 3 (by rfl) ⟨814883, by rfl⟩ : syracuseStep 4346045 = 1629767) (by norm_num)
theorem B1929469 : Blo 1715058 1929469 := bbase (se 3 (by rfl) ⟨361775, by rfl⟩ : syracuseStep 1929469 = 723551) (by norm_num)
theorem B3862781 : Blo 1715058 3862781 := bbase (se 3 (by rfl) ⟨724271, by rfl⟩ : syracuseStep 3862781 = 1448543) (by norm_num)
theorem B4403461 : Blo 1715058 4403461 := bbase (se 4 (by rfl) ⟨412824, by rfl⟩ : syracuseStep 4403461 = 825649) (by norm_num)
theorem B2896141 : Blo 1715058 2896141 := bbase (se 3 (by rfl) ⟨543026, by rfl⟩ : syracuseStep 2896141 = 1086053) (by norm_num)
theorem B2748701 : Blo 1715058 2748701 := bbase (se 3 (by rfl) ⟨515381, by rfl⟩ : syracuseStep 2748701 = 1030763) (by norm_num)
theorem B1929505 : Blo 1715058 1929505 := bbase (se 2 (by rfl) ⟨723564, by rfl⟩ : syracuseStep 1929505 = 1447129) (by norm_num)
theorem B1929541 : Blo 1715058 1929541 := bbase (se 4 (by rfl) ⟨180894, by rfl⟩ : syracuseStep 1929541 = 361789) (by norm_num)
theorem B3862853 : Blo 1715058 3862853 := bbase (se 4 (by rfl) ⟨362142, by rfl⟩ : syracuseStep 3862853 = 724285) (by norm_num)
theorem B2896229 : Blo 1715058 2896229 := bbase (se 4 (by rfl) ⟨271521, by rfl⟩ : syracuseStep 2896229 = 543043) (by norm_num)
theorem B1929577 : Blo 1715058 1929577 := bbase (se 2 (by rfl) ⟨723591, by rfl⟩ : syracuseStep 1929577 = 1447183) (by norm_num)
theorem B3666293 : Blo 1715058 3666293 := bbase (se 5 (by rfl) ⟨171857, by rfl⟩ : syracuseStep 3666293 = 343715) (by norm_num)
theorem B2609533 : Blo 1715058 2609533 := bbase (se 3 (by rfl) ⟨489287, by rfl⟩ : syracuseStep 2609533 = 978575) (by norm_num)
theorem B4346237 : Blo 1715058 4346237 := bbase (se 3 (by rfl) ⟨814919, by rfl⟩ : syracuseStep 4346237 = 1629839) (by norm_num)
theorem B1929613 : Blo 1715058 1929613 := bbase (se 3 (by rfl) ⟨361802, by rfl⟩ : syracuseStep 1929613 = 723605) (by norm_num)
theorem B3862925 : Blo 1715058 3862925 := bbase (se 3 (by rfl) ⟨724298, by rfl⟩ : syracuseStep 3862925 = 1448597) (by norm_num)
theorem B2748829 : Blo 1715058 2748829 := bbase (se 3 (by rfl) ⟨515405, by rfl⟩ : syracuseStep 2748829 = 1030811) (by norm_num)
theorem B1929649 : Blo 1715058 1929649 := bbase (se 2 (by rfl) ⟨723618, by rfl⟩ : syracuseStep 1929649 = 1447237) (by norm_num)
theorem B1929685 : Blo 1715058 1929685 := bbase (se 7 (by rfl) ⟨22613, by rfl⟩ : syracuseStep 1929685 = 45227) (by norm_num)
theorem B3862997 : Blo 1715058 3862997 := bbase (se 7 (by rfl) ⟨45269, by rfl⟩ : syracuseStep 3862997 = 90539) (by norm_num)
theorem B7827941 : Blo 1715058 7827941 := bbase (se 4 (by rfl) ⟨733869, by rfl⟩ : syracuseStep 7827941 = 1467739) (by norm_num)
theorem B2896357 : Blo 1715058 2896357 := bbase (se 4 (by rfl) ⟨271533, by rfl⟩ : syracuseStep 2896357 = 543067) (by norm_num)
theorem B5870069 : Blo 1715058 5870069 := bbase (se 5 (by rfl) ⟨275159, by rfl⟩ : syracuseStep 5870069 = 550319) (by norm_num)
theorem B1929721 : Blo 1715058 1929721 := bbase (se 2 (by rfl) ⟨723645, by rfl⟩ : syracuseStep 1929721 = 1447291) (by norm_num)
theorem B8811013 : Blo 1715058 8811013 := bbase (se 4 (by rfl) ⟨826032, by rfl⟩ : syracuseStep 8811013 = 1652065) (by norm_num)
theorem B1929757 : Blo 1715058 1929757 := bbase (se 3 (by rfl) ⟨361829, by rfl⟩ : syracuseStep 1929757 = 723659) (by norm_num)
theorem B3256861 : Blo 1715058 3256861 := bbase (se 3 (by rfl) ⟨610661, by rfl⟩ : syracuseStep 3256861 = 1221323) (by norm_num)
theorem B3863069 : Blo 1715058 3863069 := bbase (se 3 (by rfl) ⟨724325, by rfl⟩ : syracuseStep 3863069 = 1448651) (by norm_num)
theorem B2896445 : Blo 1715058 2896445 := bbase (se 3 (by rfl) ⟨543083, by rfl⟩ : syracuseStep 2896445 = 1086167) (by norm_num)
theorem B1929793 : Blo 1715058 1929793 := bbase (se 2 (by rfl) ⟨723672, by rfl⟩ : syracuseStep 1929793 = 1447345) (by norm_num)
theorem B4887125 : Blo 1715058 4887125 := bbase (se 8 (by rfl) ⟨28635, by rfl⟩ : syracuseStep 4887125 = 57271) (by norm_num)
theorem B3912293 : Blo 1715058 3912293 := bbase (se 4 (by rfl) ⟨366777, by rfl⟩ : syracuseStep 3912293 = 733555) (by norm_num)
theorem B1929829 : Blo 1715058 1929829 := bbase (se 4 (by rfl) ⟨180921, by rfl⟩ : syracuseStep 1929829 = 361843) (by norm_num)
theorem B3863141 : Blo 1715058 3863141 := bbase (se 4 (by rfl) ⟨362169, by rfl⟩ : syracuseStep 3863141 = 724339) (by norm_num)
theorem B6517381 : Blo 1715058 6517381 := bbase (se 4 (by rfl) ⟨611004, by rfl⟩ : syracuseStep 6517381 = 1222009) (by norm_num)
theorem B1929865 : Blo 1715058 1929865 := bbase (se 2 (by rfl) ⟨723699, by rfl⟩ : syracuseStep 1929865 = 1447399) (by norm_num)
theorem B5870245 : Blo 1715058 5870245 := bbase (se 4 (by rfl) ⟨550335, by rfl⟩ : syracuseStep 5870245 = 1100671) (by norm_num)
theorem B1929901 : Blo 1715058 1929901 := bbase (se 3 (by rfl) ⟨361856, by rfl⟩ : syracuseStep 1929901 = 723713) (by norm_num)
theorem B3257005 : Blo 1715058 3257005 := bbase (se 3 (by rfl) ⟨610688, by rfl⟩ : syracuseStep 3257005 = 1221377) (by norm_num)
theorem B3863213 : Blo 1715058 3863213 := bbase (se 3 (by rfl) ⟨724352, by rfl⟩ : syracuseStep 3863213 = 1448705) (by norm_num)
theorem B1831609 : Blo 1715058 1831609 := bbase (se 2 (by rfl) ⟨686853, by rfl⟩ : syracuseStep 1831609 = 1373707) (by norm_num)
theorem B2200253 : Blo 1715058 2200253 := bbase (se 3 (by rfl) ⟨412547, by rfl⟩ : syracuseStep 2200253 = 825095) (by norm_num)
theorem B2896573 : Blo 1715058 2896573 := bbase (se 3 (by rfl) ⟨543107, by rfl⟩ : syracuseStep 2896573 = 1086215) (by norm_num)
theorem B1929937 : Blo 1715058 1929937 := bbase (se 2 (by rfl) ⟨723726, by rfl⟩ : syracuseStep 1929937 = 1447453) (by norm_num)
theorem B3912437 : Blo 1715058 3912437 := bbase (se 5 (by rfl) ⟨183395, by rfl⟩ : syracuseStep 3912437 = 366791) (by norm_num)
theorem B1929973 : Blo 1715058 1929973 := bbase (se 5 (by rfl) ⟨90467, by rfl⟩ : syracuseStep 1929973 = 180935) (by norm_num)
theorem B7328501 : Blo 1715058 7328501 := bbase (se 5 (by rfl) ⟨343523, by rfl⟩ : syracuseStep 7328501 = 687047) (by norm_num)
theorem B3863285 : Blo 1715058 3863285 := bbase (se 5 (by rfl) ⟨181091, by rfl⟩ : syracuseStep 3863285 = 362183) (by norm_num)
theorem B1831681 : Blo 1715058 1831681 := bbase (se 2 (by rfl) ⟨686880, by rfl⟩ : syracuseStep 1831681 = 1373761) (by norm_num)
theorem B5788421 : Blo 1715058 5788421 := bbase (se 4 (by rfl) ⟨542664, by rfl⟩ : syracuseStep 5788421 = 1085329) (by norm_num)
theorem B2896661 : Blo 1715058 2896661 := bbase (se 6 (by rfl) ⟨67890, by rfl⟩ : syracuseStep 2896661 = 135781) (by norm_num)
theorem B9777941 : Blo 1715058 9777941 := bbase (se 6 (by rfl) ⟨229170, by rfl⟩ : syracuseStep 9777941 = 458341) (by norm_num)
theorem B1930009 : Blo 1715058 1930009 := bbase (se 2 (by rfl) ⟨723753, by rfl⟩ : syracuseStep 1930009 = 1447507) (by norm_num)
theorem B1930045 : Blo 1715058 1930045 := bbase (se 3 (by rfl) ⟨361883, by rfl⟩ : syracuseStep 1930045 = 723767) (by norm_num)
theorem B3863357 : Blo 1715058 3863357 := bbase (se 3 (by rfl) ⟨724379, by rfl⟩ : syracuseStep 3863357 = 1448759) (by norm_num)
theorem B3257165 : Blo 1715058 3257165 := bbase (se 3 (by rfl) ⟨610718, by rfl⟩ : syracuseStep 3257165 = 1221437) (by norm_num)
theorem B1930081 : Blo 1715058 1930081 := bbase (se 2 (by rfl) ⟨723780, by rfl⟩ : syracuseStep 1930081 = 1447561) (by norm_num)
theorem B1930117 : Blo 1715058 1930117 := bbase (se 4 (by rfl) ⟨180948, by rfl⟩ : syracuseStep 1930117 = 361897) (by norm_num)
theorem B2896789 : Blo 1715058 2896789 := bbase (se 6 (by rfl) ⟨67893, by rfl⟩ : syracuseStep 2896789 = 135787) (by norm_num)
theorem B6607781 : Blo 1715058 6607781 := bbase (se 4 (by rfl) ⟨619479, by rfl⟩ : syracuseStep 6607781 = 1238959) (by norm_num)
theorem B1930153 : Blo 1715058 1930153 := bbase (se 2 (by rfl) ⟨723807, by rfl⟩ : syracuseStep 1930153 = 1447615) (by norm_num)
theorem B6517685 : Blo 1715058 6517685 := bbase (se 5 (by rfl) ⟨305516, by rfl⟩ : syracuseStep 6517685 = 611033) (by norm_num)
theorem B1930189 : Blo 1715058 1930189 := bbase (se 3 (by rfl) ⟨361910, by rfl⟩ : syracuseStep 1930189 = 723821) (by norm_num)
theorem B2200537 : Blo 1715058 2200537 := bbase (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) (by norm_num)
theorem B3257309 : Blo 1715058 3257309 := bbase (se 3 (by rfl) ⟨610745, by rfl⟩ : syracuseStep 3257309 = 1221491) (by norm_num)
theorem B2896877 : Blo 1715058 2896877 := bbase (se 3 (by rfl) ⟨543164, by rfl⟩ : syracuseStep 2896877 = 1086329) (by norm_num)
theorem B1930225 : Blo 1715058 1930225 := bbase (se 2 (by rfl) ⟨723834, by rfl⟩ : syracuseStep 1930225 = 1447669) (by norm_num)
theorem B1930261 : Blo 1715058 1930261 := bbase (se 6 (by rfl) ⟨45240, by rfl⟩ : syracuseStep 1930261 = 90481) (by norm_num)
theorem B2749469 : Blo 1715058 2749469 := bbase (se 3 (by rfl) ⟨515525, by rfl⟩ : syracuseStep 2749469 = 1031051) (by norm_num)
theorem B3478565 : Blo 1715058 3478565 := bbase (se 4 (by rfl) ⟨326115, by rfl⟩ : syracuseStep 3478565 = 652231) (by norm_num)
theorem B3093557 : Blo 1715058 3093557 := bbase (se 5 (by rfl) ⟨145010, by rfl⟩ : syracuseStep 3093557 = 290021) (by norm_num)
theorem B1930297 : Blo 1715058 1930297 := bbase (se 2 (by rfl) ⟨723861, by rfl⟩ : syracuseStep 1930297 = 1447723) (by norm_num)
theorem B2864189 : Blo 1715058 2864189 := bbase (se 3 (by rfl) ⟨537035, by rfl⟩ : syracuseStep 2864189 = 1074071) (by norm_num)
theorem B12375125 : Blo 1715058 12375125 := bbase (se 8 (by rfl) ⟨72510, by rfl⟩ : syracuseStep 12375125 = 145021) (by norm_num)
theorem B1930333 : Blo 1715058 1930333 := bbase (se 3 (by rfl) ⟨361937, by rfl⟩ : syracuseStep 1930333 = 723875) (by norm_num)
theorem B3667045 : Blo 1715058 3667045 := bbase (se 4 (by rfl) ⟨343785, by rfl⟩ : syracuseStep 3667045 = 687571) (by norm_num)
theorem B2897005 : Blo 1715058 2897005 := bbase (se 3 (by rfl) ⟨543188, by rfl⟩ : syracuseStep 2897005 = 1086377) (by norm_num)
theorem B1832053 : Blo 1715058 1832053 := bbase (se 5 (by rfl) ⟨85877, by rfl⟩ : syracuseStep 1832053 = 171755) (by norm_num)
theorem B1930369 : Blo 1715058 1930369 := bbase (se 2 (by rfl) ⟨723888, by rfl⟩ : syracuseStep 1930369 = 1447777) (by norm_num)
theorem B1930405 : Blo 1715058 1930405 := bbase (se 4 (by rfl) ⟨180975, by rfl⟩ : syracuseStep 1930405 = 361951) (by norm_num)
theorem B5788853 : Blo 1715058 5788853 := bbase (se 5 (by rfl) ⟨271352, by rfl⟩ : syracuseStep 5788853 = 542705) (by norm_num)
theorem B3527869 : Blo 1715058 3527869 := bbase (se 3 (by rfl) ⟨661475, by rfl⟩ : syracuseStep 3527869 = 1322951) (by norm_num)
theorem B2897093 : Blo 1715058 2897093 := bbase (se 4 (by rfl) ⟨271602, by rfl⟩ : syracuseStep 2897093 = 543205) (by norm_num)
theorem B1930441 : Blo 1715058 1930441 := bbase (se 2 (by rfl) ⟨723915, by rfl⟩ : syracuseStep 1930441 = 1447831) (by norm_num)
theorem B8688869 : Blo 1715058 8688869 := bbase (se 4 (by rfl) ⟨814581, by rfl⟩ : syracuseStep 8688869 = 1629163) (by norm_num)
theorem B1930477 : Blo 1715058 1930477 := bbase (se 3 (by rfl) ⟨361964, by rfl⟩ : syracuseStep 1930477 = 723929) (by norm_num)
theorem B3667189 : Blo 1715058 3667189 := bbase (se 5 (by rfl) ⟨171899, by rfl⟩ : syracuseStep 3667189 = 343799) (by norm_num)
theorem B3257597 : Blo 1715058 3257597 := bbase (se 3 (by rfl) ⟨610799, by rfl⟩ : syracuseStep 3257597 = 1221599) (by norm_num)
theorem B1930513 : Blo 1715058 1930513 := bbase (se 2 (by rfl) ⟨723942, by rfl⟩ : syracuseStep 1930513 = 1447885) (by norm_num)
theorem B1930549 : Blo 1715058 1930549 := bbase (se 5 (by rfl) ⟨90494, by rfl⟩ : syracuseStep 1930549 = 180989) (by norm_num)
theorem B4887877 : Blo 1715058 4887877 := bbase (se 4 (by rfl) ⟨458238, by rfl⟩ : syracuseStep 4887877 = 916477) (by norm_num)
theorem B2897221 : Blo 1715058 2897221 := bbase (se 4 (by rfl) ⟨271614, by rfl⟩ : syracuseStep 2897221 = 543229) (by norm_num)
theorem B1930585 : Blo 1715058 1930585 := bbase (se 2 (by rfl) ⟨723969, by rfl⟩ : syracuseStep 1930585 = 1447939) (by norm_num)
theorem B1930621 : Blo 1715058 1930621 := bbase (se 3 (by rfl) ⟨361991, by rfl⟩ : syracuseStep 1930621 = 723983) (by norm_num)
theorem B4404613 : Blo 1715058 4404613 := bbase (se 4 (by rfl) ⟨412932, by rfl⟩ : syracuseStep 4404613 = 825865) (by norm_num)
theorem B3257749 : Blo 1715058 3257749 := bbase (se 6 (by rfl) ⟨76353, by rfl⟩ : syracuseStep 3257749 = 152707) (by norm_num)
theorem B2897309 : Blo 1715058 2897309 := bbase (se 3 (by rfl) ⟨543245, by rfl⟩ : syracuseStep 2897309 = 1086491) (by norm_num)
theorem B1930657 : Blo 1715058 1930657 := bbase (se 2 (by rfl) ⟨723996, by rfl⟩ : syracuseStep 1930657 = 1447993) (by norm_num)
theorem B1930693 : Blo 1715058 1930693 := bbase (se 4 (by rfl) ⟨181002, by rfl⟩ : syracuseStep 1930693 = 362005) (by norm_num)
theorem B2749925 : Blo 1715058 2749925 := bbase (se 4 (by rfl) ⟨257805, by rfl⟩ : syracuseStep 2749925 = 515611) (by norm_num)
theorem B1930729 : Blo 1715058 1930729 := bbase (se 2 (by rfl) ⟨724023, by rfl⟩ : syracuseStep 1930729 = 1448047) (by norm_num)
theorem B1832429 : Blo 1715058 1832429 := bbase (se 3 (by rfl) ⟨343580, by rfl⟩ : syracuseStep 1832429 = 687161) (by norm_num)
theorem B2061833 : Blo 1715058 2061833 := bbase (se 2 (by rfl) ⟨773187, by rfl⟩ : syracuseStep 2061833 = 1546375) (by norm_num)
theorem B1930765 : Blo 1715058 1930765 := bbase (se 3 (by rfl) ⟨362018, by rfl⟩ : syracuseStep 1930765 = 724037) (by norm_num)
theorem B2897437 : Blo 1715058 2897437 := bbase (se 3 (by rfl) ⟨543269, by rfl⟩ : syracuseStep 2897437 = 1086539) (by norm_num)
theorem B1930801 : Blo 1715058 1930801 := bbase (se 2 (by rfl) ⟨724050, by rfl⟩ : syracuseStep 1930801 = 1448101) (by norm_num)
theorem B1832501 : Blo 1715058 1832501 := bbase (se 5 (by rfl) ⟨85898, by rfl⟩ : syracuseStep 1832501 = 171797) (by norm_num)
theorem B1930837 : Blo 1715058 1930837 := bbase (se 8 (by rfl) ⟨11313, by rfl⟩ : syracuseStep 1930837 = 22627) (by norm_num)
theorem B5789285 : Blo 1715058 5789285 := bbase (se 4 (by rfl) ⟨542745, by rfl⟩ : syracuseStep 5789285 = 1085491) (by norm_num)
theorem B3479149 : Blo 1715058 3479149 := bbase (se 3 (by rfl) ⟨652340, by rfl⟩ : syracuseStep 3479149 = 1304681) (by norm_num)
theorem B2897525 : Blo 1715058 2897525 := bbase (se 5 (by rfl) ⟨135821, by rfl⟩ : syracuseStep 2897525 = 271643) (by norm_num)
theorem B1930873 : Blo 1715058 1930873 := bbase (se 2 (by rfl) ⟨724077, by rfl⟩ : syracuseStep 1930873 = 1448155) (by norm_num)
theorem B1930909 : Blo 1715058 1930909 := bbase (se 3 (by rfl) ⟨362045, by rfl⟩ : syracuseStep 1930909 = 724091) (by norm_num)
theorem B4404901 : Blo 1715058 4404901 := bbase (se 4 (by rfl) ⟨412959, by rfl⟩ : syracuseStep 4404901 = 825919) (by norm_num)
theorem B1930945 : Blo 1715058 1930945 := bbase (se 2 (by rfl) ⟨724104, by rfl⟩ : syracuseStep 1930945 = 1448209) (by norm_num)
theorem B3258053 : Blo 1715058 3258053 := bbase (se 4 (by rfl) ⟨305442, by rfl⟩ : syracuseStep 3258053 = 610885) (by norm_num)
theorem B2750149 : Blo 1715058 2750149 := bbase (se 4 (by rfl) ⟨257826, by rfl⟩ : syracuseStep 2750149 = 515653) (by norm_num)
theorem B2062045 : Blo 1715058 2062045 := bbase (se 3 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 2062045 = 773267) (by norm_num)
theorem B1930981 : Blo 1715058 1930981 := bbase (se 4 (by rfl) ⟨181029, by rfl⟩ : syracuseStep 1930981 = 362059) (by norm_num)
theorem B1832689 : Blo 1715058 1832689 := bbase (se 2 (by rfl) ⟨687258, by rfl⟩ : syracuseStep 1832689 = 1374517) (by norm_num)
theorem B2750213 : Blo 1715058 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B1931017 : Blo 1715058 1931017 := bbase (se 2 (by rfl) ⟨724131, by rfl⟩ : syracuseStep 1931017 = 1448263) (by norm_num)
theorem B1931053 : Blo 1715058 1931053 := bbase (se 3 (by rfl) ⟨362072, by rfl⟩ : syracuseStep 1931053 = 724145) (by norm_num)
theorem B1931089 : Blo 1715058 1931089 := bbase (se 2 (by rfl) ⟨724158, by rfl⟩ : syracuseStep 1931089 = 1448317) (by norm_num)
theorem B2062189 : Blo 1715058 2062189 := bbase (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) (by norm_num)
theorem B1931125 : Blo 1715058 1931125 := bbase (se 5 (by rfl) ⟨90521, by rfl⟩ : syracuseStep 1931125 = 181043) (by norm_num)
theorem B2750341 : Blo 1715058 2750341 := bbase (se 4 (by rfl) ⟨257844, by rfl⟩ : syracuseStep 2750341 = 515689) (by norm_num)
theorem B1931161 : Blo 1715058 1931161 := bbase (se 2 (by rfl) ⟨724185, by rfl⟩ : syracuseStep 1931161 = 1448371) (by norm_num)
theorem B1832873 : Blo 1715058 1832873 := bbase (se 2 (by rfl) ⟨687327, by rfl⟩ : syracuseStep 1832873 = 1374655) (by norm_num)
theorem B1931197 : Blo 1715058 1931197 := bbase (se 3 (by rfl) ⟨362099, by rfl⟩ : syracuseStep 1931197 = 724199) (by norm_num)
theorem B1931233 : Blo 1715058 1931233 := bbase (se 2 (by rfl) ⟨724212, by rfl⟩ : syracuseStep 1931233 = 1448425) (by norm_num)
theorem B1931269 : Blo 1715058 1931269 := bbase (se 4 (by rfl) ⟨181056, by rfl⟩ : syracuseStep 1931269 = 362113) (by norm_num)
theorem B5789717 : Blo 1715058 5789717 := bbase (se 6 (by rfl) ⟨135696, by rfl⟩ : syracuseStep 5789717 = 271393) (by norm_num)
theorem B1931305 : Blo 1715058 1931305 := bbase (se 2 (by rfl) ⟨724239, by rfl⟩ : syracuseStep 1931305 = 1448479) (by norm_num)
theorem B1931341 : Blo 1715058 1931341 := bbase (se 3 (by rfl) ⟨362126, by rfl⟩ : syracuseStep 1931341 = 724253) (by norm_num)
theorem B1931377 : Blo 1715058 1931377 := bbase (se 2 (by rfl) ⟨724266, by rfl⟩ : syracuseStep 1931377 = 1448533) (by norm_num)
theorem B3479669 : Blo 1715058 3479669 := bbase (se 5 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 3479669 = 326219) (by norm_num)
theorem B1931413 : Blo 1715058 1931413 := bbase (se 6 (by rfl) ⟨45267, by rfl⟩ : syracuseStep 1931413 = 90535) (by norm_num)
theorem B1931449 : Blo 1715058 1931449 := bbase (se 2 (by rfl) ⟨724293, by rfl⟩ : syracuseStep 1931449 = 1448587) (by norm_num)
theorem B3479765 : Blo 1715058 3479765 := bbase (se 7 (by rfl) ⟨40778, by rfl⟩ : syracuseStep 3479765 = 81557) (by norm_num)
theorem B1931485 : Blo 1715058 1931485 := bbase (se 3 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 1931485 = 724307) (by norm_num)
theorem B1931521 : Blo 1715058 1931521 := bbase (se 2 (by rfl) ⟨724320, by rfl⟩ : syracuseStep 1931521 = 1448641) (by norm_num)
theorem B1931557 : Blo 1715058 1931557 := bbase (se 4 (by rfl) ⟨181083, by rfl⟩ : syracuseStep 1931557 = 362167) (by norm_num)
theorem B1931593 : Blo 1715058 1931593 := bbase (se 2 (by rfl) ⟨724347, by rfl⟩ : syracuseStep 1931593 = 1448695) (by norm_num)
theorem B1931629 : Blo 1715058 1931629 := bbase (se 3 (by rfl) ⟨362180, by rfl⟩ : syracuseStep 1931629 = 724361) (by norm_num)
theorem B1931665 : Blo 1715058 1931665 := bbase (se 2 (by rfl) ⟨724374, by rfl⟩ : syracuseStep 1931665 = 1448749) (by norm_num)
theorem B3258805 : Blo 1715058 3258805 := bbase (se 5 (by rfl) ⟨152756, by rfl⟩ : syracuseStep 3258805 = 305513) (by norm_num)
theorem B5790149 : Blo 1715058 5790149 := bbase (se 4 (by rfl) ⟨542826, by rfl⟩ : syracuseStep 5790149 = 1085653) (by norm_num)
theorem B7330277 : Blo 1715058 7330277 := bbase (se 4 (by rfl) ⟨687213, by rfl⟩ : syracuseStep 7330277 = 1374427) (by norm_num)
theorem B1956337 : Blo 1715058 1956337 := bbase (se 2 (by rfl) ⟨733626, by rfl⟩ : syracuseStep 1956337 = 1467253) (by norm_num)
theorem B8690165 : Blo 1715058 8690165 := bbase (se 5 (by rfl) ⟨407351, by rfl⟩ : syracuseStep 8690165 = 814703) (by norm_num)
theorem B3258949 : Blo 1715058 3258949 := bbase (se 4 (by rfl) ⟨305526, by rfl⟩ : syracuseStep 3258949 = 611053) (by norm_num)
theorem B10992341 : Blo 1715058 10992341 := bbase (se 7 (by rfl) ⟨128816, by rfl⟩ : syracuseStep 10992341 = 257633) (by norm_num)
theorem B3259109 : Blo 1715058 3259109 := bbase (se 4 (by rfl) ⟨305541, by rfl⟩ : syracuseStep 3259109 = 611083) (by norm_num)
theorem B5790581 : Blo 1715058 5790581 := bbase (se 5 (by rfl) ⟨271433, by rfl⟩ : syracuseStep 5790581 = 542867) (by norm_num)
theorem B3259253 : Blo 1715058 3259253 := bbase (se 5 (by rfl) ⟨152777, by rfl⟩ : syracuseStep 3259253 = 305555) (by norm_num)
theorem B19553237 : Blo 1715058 19553237 := bbase (se 7 (by rfl) ⟨229139, by rfl⟩ : syracuseStep 19553237 = 458279) (by norm_num)
theorem B2202589 : Blo 1715058 2202589 := bbase (se 3 (by rfl) ⟨412985, by rfl⟩ : syracuseStep 2202589 = 825971) (by norm_num)
theorem B5495813 : Blo 1715058 5495813 := bbase (se 4 (by rfl) ⟨515232, by rfl⟩ : syracuseStep 5495813 = 1030465) (by norm_num)
theorem B17603669 : Blo 1715058 17603669 := bbase (se 8 (by rfl) ⟨103146, by rfl⟩ : syracuseStep 17603669 = 206293) (by norm_num)
theorem B14662741 : Blo 1715058 14662741 := bbase (se 8 (by rfl) ⟨85914, by rfl⟩ : syracuseStep 14662741 = 171829) (by norm_num)
theorem B4234349 : Blo 1715058 4234349 := bbase (se 3 (by rfl) ⟨793940, by rfl⟩ : syracuseStep 4234349 = 1587881) (by norm_num)
theorem B3914885 : Blo 1715058 3914885 := bbase (se 4 (by rfl) ⟨367020, by rfl⟩ : syracuseStep 3914885 = 734041) (by norm_num)
theorem B3259541 : Blo 1715058 3259541 := bbase (se 6 (by rfl) ⟨76395, by rfl⟩ : syracuseStep 3259541 = 152791) (by norm_num)
theorem B9280757 : Blo 1715058 9280757 := bbase (se 5 (by rfl) ⟨435035, by rfl⟩ : syracuseStep 9280757 = 870071) (by norm_num)
theorem B5791013 : Blo 1715058 5791013 := bbase (se 4 (by rfl) ⟨542907, by rfl⟩ : syracuseStep 5791013 = 1085815) (by norm_num)
theorem B3259693 : Blo 1715058 3259693 := bbase (se 3 (by rfl) ⟨611192, by rfl⟩ : syracuseStep 3259693 = 1222385) (by norm_num)
theorem B9272693 : Blo 1715058 9272693 := bbase (se 5 (by rfl) ⟨434657, by rfl⟩ : syracuseStep 9272693 = 869315) (by norm_num)
theorem B6512021 : Blo 1715058 6512021 := bbase (se 6 (by rfl) ⟨152625, by rfl⟩ : syracuseStep 6512021 = 305251) (by norm_num)
theorem B7331269 : Blo 1715058 7331269 := bbase (se 4 (by rfl) ⟨687306, by rfl⟩ : syracuseStep 7331269 = 1374613) (by norm_num)
theorem B4955701 : Blo 1715058 4955701 := bbase (se 5 (by rfl) ⟨232298, by rfl⟩ : syracuseStep 4955701 = 464597) (by norm_num)
theorem B7429733 : Blo 1715058 7429733 := bbase (se 4 (by rfl) ⟨696537, by rfl⟩ : syracuseStep 7429733 = 1393075) (by norm_num)
theorem B4341397 : Blo 1715058 4341397 := bbase (se 6 (by rfl) ⟨101751, by rfl⟩ : syracuseStep 4341397 = 203503) (by norm_num)
theorem B6512309 : Blo 1715058 6512309 := bbase (se 5 (by rfl) ⟨305264, by rfl⟩ : syracuseStep 6512309 = 610529) (by norm_num)
theorem B5791445 : Blo 1715058 5791445 := bbase (se 7 (by rfl) ⟨67868, by rfl⟩ : syracuseStep 5791445 = 135737) (by norm_num)
theorem B6602485 : Blo 1715058 6602485 := bbase (se 5 (by rfl) ⟨309491, by rfl⟩ : syracuseStep 6602485 = 618983) (by norm_num)
theorem B4341509 : Blo 1715058 4341509 := bbase (se 4 (by rfl) ⟨407016, by rfl⟩ : syracuseStep 4341509 = 814033) (by norm_num)
theorem B5496581 : Blo 1715058 5496581 := bbase (se 4 (by rfl) ⟨515304, by rfl⟩ : syracuseStep 5496581 = 1030609) (by norm_num)
theorem B8691461 : Blo 1715058 8691461 := bbase (se 4 (by rfl) ⟨814824, by rfl⟩ : syracuseStep 8691461 = 1629649) (by norm_num)
theorem B2170633 : Blo 1715058 2170633 := bbase (se 2 (by rfl) ⟨813987, by rfl⟩ : syracuseStep 2170633 = 1627975) (by norm_num)
theorem B2170729 : Blo 1715058 2170729 := bbase (se 2 (by rfl) ⟨814023, by rfl⟩ : syracuseStep 2170729 = 1628047) (by norm_num)
theorem B4341701 : Blo 1715058 4341701 := bbase (se 4 (by rfl) ⟨407034, by rfl⟩ : syracuseStep 4341701 = 814069) (by norm_num)
theorem B3301489 : Blo 1715058 3301489 := bstep (se 2 (by rfl) ⟨1238058, by rfl⟩ : syracuseStep 3301489 = 2476117) B2476117
theorem B8249485 : Blo 1715058 8249485 := bstep (se 3 (by rfl) ⟨1546778, by rfl⟩ : syracuseStep 8249485 = 3093557) B3093557
theorem B4636835 : Blo 1715058 4636835 := bstep (se 1 (by rfl) ⟨3477626, by rfl⟩ : syracuseStep 4636835 = 6955253) B6955253
theorem B5791985 : Blo 1715058 5791985 := bstep (se 2 (by rfl) ⟨2171994, by rfl⟩ : syracuseStep 5791985 = 4343989) B4343989
theorem B2572595 : Blo 1715058 2572595 := bstep (se 1 (by rfl) ⟨1929446, by rfl⟩ : syracuseStep 2572595 = 3858893) B3858893
theorem B29327669 : Blo 1715058 29327669 := bstep (se 5 (by rfl) ⟨1374734, by rfl⟩ : syracuseStep 29327669 = 2749469) B2749469
theorem B5218627 : Blo 1715058 5218627 := bstep (se 1 (by rfl) ⟨3913970, by rfl⟩ : syracuseStep 5218627 = 7827941) B7827941
theorem B4702531 : Blo 1715058 4702531 := bstep (se 1 (by rfl) ⟨3526898, by rfl⟩ : syracuseStep 4702531 = 7053797) B7053797
theorem B2572625 : Blo 1715058 2572625 := bstep (se 2 (by rfl) ⟨964734, by rfl⟩ : syracuseStep 2572625 = 1929469) B1929469
theorem B2572643 : Blo 1715058 2572643 := bstep (se 1 (by rfl) ⟨1929482, by rfl⟩ : syracuseStep 2572643 = 3858965) B3858965
theorem B2572673 : Blo 1715058 2572673 := bstep (se 2 (by rfl) ⟨964752, by rfl⟩ : syracuseStep 2572673 = 1929505) B1929505
theorem B14664077 : Blo 1715058 14664077 := bstep (se 3 (by rfl) ⟨2749514, by rfl⟩ : syracuseStep 14664077 = 5499029) B5499029
theorem B8692109 : Blo 1715058 8692109 := bstep (se 3 (by rfl) ⟨1629770, by rfl⟩ : syracuseStep 8692109 = 3259541) B3259541
theorem B2572691 : Blo 1715058 2572691 := bstep (se 1 (by rfl) ⟨1929518, by rfl⟩ : syracuseStep 2572691 = 3859037) B3859037
theorem B2572721 : Blo 1715058 2572721 := bstep (se 2 (by rfl) ⟨964770, by rfl⟩ : syracuseStep 2572721 = 1929541) B1929541
theorem B2572739 : Blo 1715058 2572739 := bstep (se 1 (by rfl) ⟨1929554, by rfl⟩ : syracuseStep 2572739 = 3859109) B3859109
theorem B9273797 : Blo 1715058 9273797 := bstep (se 4 (by rfl) ⟨869418, by rfl⟩ : syracuseStep 9273797 = 1738837) B1738837
theorem B2572769 : Blo 1715058 2572769 := bstep (se 2 (by rfl) ⟨964788, by rfl⟩ : syracuseStep 2572769 = 1929577) B1929577
theorem B3858929 : Blo 1715058 3858929 := bstep (se 2 (by rfl) ⟨1447098, by rfl⟩ : syracuseStep 3858929 = 2894197) B2894197
theorem B2572787 : Blo 1715058 2572787 := bstep (se 1 (by rfl) ⟨1929590, by rfl⟩ : syracuseStep 2572787 = 3859181) B3859181
theorem B3858947 : Blo 1715058 3858947 := bstep (se 1 (by rfl) ⟨2894210, by rfl⟩ : syracuseStep 3858947 = 5788421) B5788421
theorem B2572817 : Blo 1715058 2572817 := bstep (se 2 (by rfl) ⟨964806, by rfl⟩ : syracuseStep 2572817 = 1929613) B1929613
theorem B2572835 : Blo 1715058 2572835 := bstep (se 1 (by rfl) ⟨1929626, by rfl⟩ : syracuseStep 2572835 = 3859253) B3859253
theorem B2171443 : Blo 1715058 2171443 := bstep (se 1 (by rfl) ⟨1628582, by rfl⟩ : syracuseStep 2171443 = 3257165) B3257165
theorem B2572865 : Blo 1715058 2572865 := bstep (se 2 (by rfl) ⟨964824, by rfl⟩ : syracuseStep 2572865 = 1929649) B1929649
theorem B2572883 : Blo 1715058 2572883 := bstep (se 1 (by rfl) ⟨1929662, by rfl⟩ : syracuseStep 2572883 = 3859325) B3859325
theorem B2572913 : Blo 1715058 2572913 := bstep (se 2 (by rfl) ⟨964842, by rfl⟩ : syracuseStep 2572913 = 1929685) B1929685
theorem B2572931 : Blo 1715058 2572931 := bstep (se 1 (by rfl) ⟨1929698, by rfl⟩ : syracuseStep 2572931 = 3859397) B3859397
theorem B24748685 : Blo 1715058 24748685 := bstep (se 3 (by rfl) ⟨4640378, by rfl⟩ : syracuseStep 24748685 = 9280757) B9280757
theorem B2171539 : Blo 1715058 2171539 := bstep (se 1 (by rfl) ⟨1628654, by rfl⟩ : syracuseStep 2171539 = 3257309) B3257309
theorem B2572961 : Blo 1715058 2572961 := bstep (se 2 (by rfl) ⟨964860, by rfl⟩ : syracuseStep 2572961 = 1929721) B1929721
theorem B11748017 : Blo 1715058 11748017 := bstep (se 2 (by rfl) ⟨4405506, by rfl⟩ : syracuseStep 11748017 = 8811013) B8811013
theorem B2572979 : Blo 1715058 2572979 := bstep (se 1 (by rfl) ⟨1929734, by rfl⟩ : syracuseStep 2572979 = 3859469) B3859469
theorem B2573009 : Blo 1715058 2573009 := bstep (se 2 (by rfl) ⟨964878, by rfl⟩ : syracuseStep 2573009 = 1929757) B1929757
theorem B4342481 : Blo 1715058 4342481 := bstep (se 2 (by rfl) ⟨1628430, by rfl⟩ : syracuseStep 4342481 = 3256861) B3256861
theorem B1909459 : Blo 1715058 1909459 := bstep (se 1 (by rfl) ⟨1432094, by rfl⟩ : syracuseStep 1909459 = 2864189) B2864189
theorem B2573027 : Blo 1715058 2573027 := bstep (se 1 (by rfl) ⟨1929770, by rfl⟩ : syracuseStep 2573027 = 3859541) B3859541
theorem B8250083 : Blo 1715058 8250083 := bstep (se 1 (by rfl) ⟨6187562, by rfl⟩ : syracuseStep 8250083 = 12375125) B12375125
theorem B2573057 : Blo 1715058 2573057 := bstep (se 2 (by rfl) ⟨964896, by rfl⟩ : syracuseStep 2573057 = 1929793) B1929793
theorem B4342531 : Blo 1715058 4342531 := bstep (se 1 (by rfl) ⟨3256898, by rfl⟩ : syracuseStep 4342531 = 6513797) B6513797
theorem B5792525 : Blo 1715058 5792525 := bstep (se 3 (by rfl) ⟨1086098, by rfl⟩ : syracuseStep 5792525 = 2172197) B2172197
theorem B3859217 : Blo 1715058 3859217 := bstep (se 2 (by rfl) ⟨1447206, by rfl⟩ : syracuseStep 3859217 = 2894413) B2894413
theorem B2573075 : Blo 1715058 2573075 := bstep (se 1 (by rfl) ⟨1929806, by rfl⟩ : syracuseStep 2573075 = 3859613) B3859613
theorem B3859235 : Blo 1715058 3859235 := bstep (se 1 (by rfl) ⟨2894426, by rfl⟩ : syracuseStep 3859235 = 5788853) B5788853
theorem B2573105 : Blo 1715058 2573105 := bstep (se 2 (by rfl) ⟨964914, by rfl⟩ : syracuseStep 2573105 = 1929829) B1929829
theorem B10584881 : Blo 1715058 10584881 := bstep (se 2 (by rfl) ⟨3969330, by rfl⟩ : syracuseStep 10584881 = 7938661) B7938661
theorem B2573123 : Blo 1715058 2573123 := bstep (se 1 (by rfl) ⟨1929842, by rfl⟩ : syracuseStep 2573123 = 3859685) B3859685
theorem B5792579 : Blo 1715058 5792579 := bstep (se 1 (by rfl) ⟨4344434, by rfl⟩ : syracuseStep 5792579 = 8688869) B8688869
theorem B2573153 : Blo 1715058 2573153 := bstep (se 2 (by rfl) ⟨964932, by rfl⟩ : syracuseStep 2573153 = 1929865) B1929865
theorem B2573171 : Blo 1715058 2573171 := bstep (se 1 (by rfl) ⟨1929878, by rfl⟩ : syracuseStep 2573171 = 3859757) B3859757
theorem B2573201 : Blo 1715058 2573201 := bstep (se 2 (by rfl) ⟨964950, by rfl⟩ : syracuseStep 2573201 = 1929901) B1929901
theorem B4342673 : Blo 1715058 4342673 := bstep (se 2 (by rfl) ⟨1628502, by rfl⟩ : syracuseStep 4342673 = 3257005) B3257005
theorem B2442145 : Blo 1715058 2442145 := bstep (se 2 (by rfl) ⟨915804, by rfl⟩ : syracuseStep 2442145 = 1831609) B1831609
theorem B2573219 : Blo 1715058 2573219 := bstep (se 1 (by rfl) ⟨1929914, by rfl⟩ : syracuseStep 2573219 = 3859829) B3859829
theorem B2573249 : Blo 1715058 2573249 := bstep (se 2 (by rfl) ⟨964968, by rfl⟩ : syracuseStep 2573249 = 1929937) B1929937
theorem B2573267 : Blo 1715058 2573267 := bstep (se 1 (by rfl) ⟨1929950, by rfl⟩ : syracuseStep 2573267 = 3859901) B3859901
theorem B2573297 : Blo 1715058 2573297 := bstep (se 2 (by rfl) ⟨964986, by rfl⟩ : syracuseStep 2573297 = 1929973) B1929973
theorem B2442241 : Blo 1715058 2442241 := bstep (se 2 (by rfl) ⟨915840, by rfl⟩ : syracuseStep 2442241 = 1831681) B1831681
theorem B2573315 : Blo 1715058 2573315 := bstep (se 1 (by rfl) ⟨1929986, by rfl⟩ : syracuseStep 2573315 = 3859973) B3859973
theorem B2573345 : Blo 1715058 2573345 := bstep (se 2 (by rfl) ⟨965004, by rfl⟩ : syracuseStep 2573345 = 1930009) B1930009
theorem B4637731 : Blo 1715058 4637731 := bstep (se 1 (by rfl) ⟨3478298, by rfl⟩ : syracuseStep 4637731 = 6956597) B6956597
theorem B3859505 : Blo 1715058 3859505 := bstep (se 2 (by rfl) ⟨1447314, by rfl⟩ : syracuseStep 3859505 = 2894629) B2894629
theorem B2573363 : Blo 1715058 2573363 := bstep (se 1 (by rfl) ⟨1930022, by rfl⟩ : syracuseStep 2573363 = 3860045) B3860045
theorem B3859523 : Blo 1715058 3859523 := bstep (se 1 (by rfl) ⟨2894642, by rfl⟩ : syracuseStep 3859523 = 5789285) B5789285
theorem B2573393 : Blo 1715058 2573393 := bstep (se 2 (by rfl) ⟨965022, by rfl⟩ : syracuseStep 2573393 = 1930045) B1930045
theorem B5792849 : Blo 1715058 5792849 := bstep (se 2 (by rfl) ⟨2172318, by rfl⟩ : syracuseStep 5792849 = 4344637) B4344637
theorem B18547811 : Blo 1715058 18547811 := bstep (se 1 (by rfl) ⟨13910858, by rfl⟩ : syracuseStep 18547811 = 27821717) B27821717
theorem B2573411 : Blo 1715058 2573411 := bstep (se 1 (by rfl) ⟨1930058, by rfl⟩ : syracuseStep 2573411 = 3860117) B3860117
theorem B8684657 : Blo 1715058 8684657 := bstep (se 2 (by rfl) ⟨3256746, by rfl⟩ : syracuseStep 8684657 = 6513493) B6513493
theorem B2573441 : Blo 1715058 2573441 := bstep (se 2 (by rfl) ⟨965040, by rfl⟩ : syracuseStep 2573441 = 1930081) B1930081
theorem B2172035 : Blo 1715058 2172035 := bstep (se 1 (by rfl) ⟨1629026, by rfl⟩ : syracuseStep 2172035 = 3258053) B3258053
theorem B2573459 : Blo 1715058 2573459 := bstep (se 1 (by rfl) ⟨1930094, by rfl⟩ : syracuseStep 2573459 = 3860189) B3860189
theorem B2573489 : Blo 1715058 2573489 := bstep (se 2 (by rfl) ⟨965058, by rfl⟩ : syracuseStep 2573489 = 1930117) B1930117
theorem B2573507 : Blo 1715058 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B2573537 : Blo 1715058 2573537 := bstep (se 2 (by rfl) ⟨965076, by rfl⟩ : syracuseStep 2573537 = 1930153) B1930153
theorem B2573555 : Blo 1715058 2573555 := bstep (se 1 (by rfl) ⟨1930166, by rfl⟩ : syracuseStep 2573555 = 3860333) B3860333
theorem B9774341 : Blo 1715058 9774341 := bstep (se 4 (by rfl) ⟨916344, by rfl⟩ : syracuseStep 9774341 = 1832689) B1832689
theorem B19547405 : Blo 1715058 19547405 := bstep (se 3 (by rfl) ⟨3665138, by rfl⟩ : syracuseStep 19547405 = 7330277) B7330277
theorem B2573585 : Blo 1715058 2573585 := bstep (se 2 (by rfl) ⟨965094, by rfl⟩ : syracuseStep 2573585 = 1930189) B1930189
theorem B2934049 : Blo 1715058 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B2573603 : Blo 1715058 2573603 := bstep (se 1 (by rfl) ⟨1930202, by rfl⟩ : syracuseStep 2573603 = 3860405) B3860405
theorem B2573633 : Blo 1715058 2573633 := bstep (se 2 (by rfl) ⟨965112, by rfl⟩ : syracuseStep 2573633 = 1930225) B1930225
theorem B2934083 : Blo 1715058 2934083 := bstep (se 1 (by rfl) ⟨2200562, by rfl⟩ : syracuseStep 2934083 = 4401125) B4401125
theorem B3859793 : Blo 1715058 3859793 := bstep (se 2 (by rfl) ⟨1447422, by rfl⟩ : syracuseStep 3859793 = 2894845) B2894845
theorem B2573651 : Blo 1715058 2573651 := bstep (se 1 (by rfl) ⟨1930238, by rfl⟩ : syracuseStep 2573651 = 3860477) B3860477
theorem B3859811 : Blo 1715058 3859811 := bstep (se 1 (by rfl) ⟨2894858, by rfl⟩ : syracuseStep 3859811 = 5789717) B5789717
theorem B5498221 : Blo 1715058 5498221 := bstep (se 3 (by rfl) ⟨1030916, by rfl⟩ : syracuseStep 5498221 = 2061833) B2061833
theorem B2573681 : Blo 1715058 2573681 := bstep (se 2 (by rfl) ⟨965130, by rfl⟩ : syracuseStep 2573681 = 1930261) B1930261
theorem B2573699 : Blo 1715058 2573699 := bstep (se 1 (by rfl) ⟨1930274, by rfl⟩ : syracuseStep 2573699 = 3860549) B3860549
theorem B2573729 : Blo 1715058 2573729 := bstep (se 2 (by rfl) ⟨965148, by rfl⟩ : syracuseStep 2573729 = 1930297) B1930297
theorem B2319779 : Blo 1715058 2319779 := bstep (se 1 (by rfl) ⟨1739834, by rfl⟩ : syracuseStep 2319779 = 3479669) B3479669
theorem B2573747 : Blo 1715058 2573747 := bstep (se 1 (by rfl) ⟨1930310, by rfl⟩ : syracuseStep 2573747 = 3860621) B3860621
theorem B2573777 : Blo 1715058 2573777 := bstep (se 2 (by rfl) ⟨965166, by rfl⟩ : syracuseStep 2573777 = 1930333) B1930333
theorem B2573795 : Blo 1715058 2573795 := bstep (se 1 (by rfl) ⟨1930346, by rfl⟩ : syracuseStep 2573795 = 3860693) B3860693
theorem B2442737 : Blo 1715058 2442737 := bstep (se 2 (by rfl) ⟨916026, by rfl⟩ : syracuseStep 2442737 = 1832053) B1832053
theorem B2573825 : Blo 1715058 2573825 := bstep (se 2 (by rfl) ⟨965184, by rfl⟩ : syracuseStep 2573825 = 1930369) B1930369
theorem B2573843 : Blo 1715058 2573843 := bstep (se 1 (by rfl) ⟨1930382, by rfl⟩ : syracuseStep 2573843 = 3860765) B3860765
theorem B2573873 : Blo 1715058 2573873 := bstep (se 2 (by rfl) ⟨965202, by rfl⟩ : syracuseStep 2573873 = 1930405) B1930405
theorem B2573891 : Blo 1715058 2573891 := bstep (se 1 (by rfl) ⟨1930418, by rfl⟩ : syracuseStep 2573891 = 3860837) B3860837
theorem B6514253 : Blo 1715058 6514253 := bstep (se 3 (by rfl) ⟨1221422, by rfl⟩ : syracuseStep 6514253 = 2442845) B2442845
theorem B4703825 : Blo 1715058 4703825 := bstep (se 2 (by rfl) ⟨1763934, by rfl⟩ : syracuseStep 4703825 = 3527869) B3527869
theorem B2573921 : Blo 1715058 2573921 := bstep (se 2 (by rfl) ⟨965220, by rfl⟩ : syracuseStep 2573921 = 1930441) B1930441
theorem B5793389 : Blo 1715058 5793389 := bstep (se 3 (by rfl) ⟨1086260, by rfl⟩ : syracuseStep 5793389 = 2172521) B2172521
theorem B20866673 : Blo 1715058 20866673 := bstep (se 2 (by rfl) ⟨7825002, by rfl⟩ : syracuseStep 20866673 = 15650005) B15650005
theorem B3860081 : Blo 1715058 3860081 := bstep (se 2 (by rfl) ⟨1447530, by rfl⟩ : syracuseStep 3860081 = 2895061) B2895061
theorem B2573939 : Blo 1715058 2573939 := bstep (se 1 (by rfl) ⟨1930454, by rfl⟩ : syracuseStep 2573939 = 3860909) B3860909
theorem B3860099 : Blo 1715058 3860099 := bstep (se 1 (by rfl) ⟨2895074, by rfl⟩ : syracuseStep 3860099 = 5790149) B5790149
theorem B2573969 : Blo 1715058 2573969 := bstep (se 2 (by rfl) ⟨965238, by rfl⟩ : syracuseStep 2573969 = 1930477) B1930477
theorem B2786977 : Blo 1715058 2786977 := bstep (se 2 (by rfl) ⟨1045116, by rfl⟩ : syracuseStep 2786977 = 2090233) B2090233
theorem B2573987 : Blo 1715058 2573987 := bstep (se 1 (by rfl) ⟨1930490, by rfl⟩ : syracuseStep 2573987 = 3860981) B3860981
theorem B5793443 : Blo 1715058 5793443 := bstep (se 1 (by rfl) ⟨4345082, by rfl⟩ : syracuseStep 5793443 = 8690165) B8690165
theorem B2574017 : Blo 1715058 2574017 := bstep (se 2 (by rfl) ⟨965256, by rfl⟩ : syracuseStep 2574017 = 1930513) B1930513
theorem B2574035 : Blo 1715058 2574035 := bstep (se 1 (by rfl) ⟨1930526, by rfl⟩ : syracuseStep 2574035 = 3861053) B3861053
theorem B4884209 : Blo 1715058 4884209 := bstep (se 2 (by rfl) ⟨1831578, by rfl⟩ : syracuseStep 4884209 = 3663157) B3663157
theorem B2574065 : Blo 1715058 2574065 := bstep (se 2 (by rfl) ⟨965274, by rfl⟩ : syracuseStep 2574065 = 1930549) B1930549
theorem B2574083 : Blo 1715058 2574083 := bstep (se 1 (by rfl) ⟨1930562, by rfl⟩ : syracuseStep 2574083 = 3861125) B3861125
theorem B2574113 : Blo 1715058 2574113 := bstep (se 2 (by rfl) ⟨965292, by rfl⟩ : syracuseStep 2574113 = 1930585) B1930585
theorem B2574131 : Blo 1715058 2574131 := bstep (se 1 (by rfl) ⟨1930598, by rfl⟩ : syracuseStep 2574131 = 3861197) B3861197
theorem B2172739 : Blo 1715058 2172739 := bstep (se 1 (by rfl) ⟨1629554, by rfl⟩ : syracuseStep 2172739 = 3259109) B3259109
theorem B2574161 : Blo 1715058 2574161 := bstep (se 2 (by rfl) ⟨965310, by rfl⟩ : syracuseStep 2574161 = 1930621) B1930621
theorem B2574179 : Blo 1715058 2574179 := bstep (se 1 (by rfl) ⟨1930634, by rfl⟩ : syracuseStep 2574179 = 3861269) B3861269
theorem B4343665 : Blo 1715058 4343665 := bstep (se 2 (by rfl) ⟨1628874, by rfl⟩ : syracuseStep 4343665 = 3257749) B3257749
theorem B2574209 : Blo 1715058 2574209 := bstep (se 2 (by rfl) ⟨965328, by rfl⟩ : syracuseStep 2574209 = 1930657) B1930657
theorem B3860369 : Blo 1715058 3860369 := bstep (se 2 (by rfl) ⟨1447638, by rfl⟩ : syracuseStep 3860369 = 2895277) B2895277
theorem B2574227 : Blo 1715058 2574227 := bstep (se 1 (by rfl) ⟨1930670, by rfl⟩ : syracuseStep 2574227 = 3861341) B3861341
theorem B3860387 : Blo 1715058 3860387 := bstep (se 1 (by rfl) ⟨2895290, by rfl⟩ : syracuseStep 3860387 = 5790581) B5790581
theorem B2172835 : Blo 1715058 2172835 := bstep (se 1 (by rfl) ⟨1629626, by rfl⟩ : syracuseStep 2172835 = 3259253) B3259253
theorem B2574257 : Blo 1715058 2574257 := bstep (se 2 (by rfl) ⟨965346, by rfl⟩ : syracuseStep 2574257 = 1930693) B1930693
theorem B9775025 : Blo 1715058 9775025 := bstep (se 2 (by rfl) ⟨3665634, by rfl⟩ : syracuseStep 9775025 = 7331269) B7331269
theorem B5793713 : Blo 1715058 5793713 := bstep (se 2 (by rfl) ⟨2172642, by rfl⟩ : syracuseStep 5793713 = 4345285) B4345285
theorem B2574275 : Blo 1715058 2574275 := bstep (se 1 (by rfl) ⟨1930706, by rfl⟩ : syracuseStep 2574275 = 3861413) B3861413
theorem B2934739 : Blo 1715058 2934739 := bstep (se 1 (by rfl) ⟨2201054, by rfl⟩ : syracuseStep 2934739 = 4402109) B4402109
theorem B2574305 : Blo 1715058 2574305 := bstep (se 2 (by rfl) ⟨965364, by rfl⟩ : syracuseStep 2574305 = 1930729) B1930729
theorem B13035491 : Blo 1715058 13035491 := bstep (se 1 (by rfl) ⟨9776618, by rfl⟩ : syracuseStep 13035491 = 19553237) B19553237
theorem B2574323 : Blo 1715058 2574323 := bstep (se 1 (by rfl) ⟨1930742, by rfl⟩ : syracuseStep 2574323 = 3861485) B3861485
theorem B3663875 : Blo 1715058 3663875 := bstep (se 1 (by rfl) ⟨2747906, by rfl⟩ : syracuseStep 3663875 = 5495813) B5495813
theorem B7333901 : Blo 1715058 7333901 := bstep (se 3 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 7333901 = 2750213) B2750213
theorem B2574353 : Blo 1715058 2574353 := bstep (se 2 (by rfl) ⟨965382, by rfl⟩ : syracuseStep 2574353 = 1930765) B1930765
theorem B2574371 : Blo 1715058 2574371 := bstep (se 1 (by rfl) ⟨1930778, by rfl⟩ : syracuseStep 2574371 = 3861557) B3861557
theorem B2574401 : Blo 1715058 2574401 := bstep (se 2 (by rfl) ⟨965400, by rfl⟩ : syracuseStep 2574401 = 1930801) B1930801
theorem B2680913 : Blo 1715058 2680913 := bstep (se 2 (by rfl) ⟨1005342, by rfl⟩ : syracuseStep 2680913 = 2010685) B2010685
theorem B2574419 : Blo 1715058 2574419 := bstep (se 1 (by rfl) ⟨1930814, by rfl⟩ : syracuseStep 2574419 = 3861629) B3861629
theorem B2574449 : Blo 1715058 2574449 := bstep (se 2 (by rfl) ⟨965418, by rfl⟩ : syracuseStep 2574449 = 1930837) B1930837
theorem B4343939 : Blo 1715058 4343939 := bstep (se 1 (by rfl) ⟨3257954, by rfl⟩ : syracuseStep 4343939 = 6515909) B6515909
theorem B2574467 : Blo 1715058 2574467 := bstep (se 1 (by rfl) ⟨1930850, by rfl⟩ : syracuseStep 2574467 = 3861701) B3861701
theorem B4638865 : Blo 1715058 4638865 := bstep (se 2 (by rfl) ⟨1739574, by rfl⟩ : syracuseStep 4638865 = 3479149) B3479149
theorem B2574497 : Blo 1715058 2574497 := bstep (se 2 (by rfl) ⟨965436, by rfl⟩ : syracuseStep 2574497 = 1930873) B1930873
theorem B3860657 : Blo 1715058 3860657 := bstep (se 2 (by rfl) ⟨1447746, by rfl⟩ : syracuseStep 3860657 = 2895493) B2895493
theorem B2574515 : Blo 1715058 2574515 := bstep (se 1 (by rfl) ⟨1930886, by rfl⟩ : syracuseStep 2574515 = 3861773) B3861773
theorem B3860675 : Blo 1715058 3860675 := bstep (se 1 (by rfl) ⟨2895506, by rfl⟩ : syracuseStep 3860675 = 5791013) B5791013
theorem B2574545 : Blo 1715058 2574545 := bstep (se 2 (by rfl) ⟨965454, by rfl⟩ : syracuseStep 2574545 = 1930909) B1930909
theorem B2574563 : Blo 1715058 2574563 := bstep (se 1 (by rfl) ⟨1930922, by rfl⟩ : syracuseStep 2574563 = 3861845) B3861845
theorem B2574593 : Blo 1715058 2574593 := bstep (se 2 (by rfl) ⟨965472, by rfl⟩ : syracuseStep 2574593 = 1930945) B1930945
theorem B2574611 : Blo 1715058 2574611 := bstep (se 1 (by rfl) ⟨1930958, by rfl⟩ : syracuseStep 2574611 = 3861917) B3861917
theorem B2574641 : Blo 1715058 2574641 := bstep (se 2 (by rfl) ⟨965490, by rfl⟩ : syracuseStep 2574641 = 1930981) B1930981
theorem B4344131 : Blo 1715058 4344131 := bstep (se 1 (by rfl) ⟨3258098, by rfl⟩ : syracuseStep 4344131 = 6516197) B6516197
theorem B2574659 : Blo 1715058 2574659 := bstep (se 1 (by rfl) ⟨1930994, by rfl⟩ : syracuseStep 2574659 = 3861989) B3861989
theorem B2443603 : Blo 1715058 2443603 := bstep (se 1 (by rfl) ⟨1832702, by rfl⟩ : syracuseStep 2443603 = 3665405) B3665405
theorem B2894177 : Blo 1715058 2894177 := bstep (se 2 (by rfl) ⟨1085316, by rfl⟩ : syracuseStep 2894177 = 2170633) B2170633
theorem B2574689 : Blo 1715058 2574689 := bstep (se 2 (by rfl) ⟨965508, by rfl⟩ : syracuseStep 2574689 = 1931017) B1931017
theorem B2574707 : Blo 1715058 2574707 := bstep (se 1 (by rfl) ⟨1931030, by rfl⟩ : syracuseStep 2574707 = 3862061) B3862061
theorem B2574737 : Blo 1715058 2574737 := bstep (se 2 (by rfl) ⟨965526, by rfl⟩ : syracuseStep 2574737 = 1931053) B1931053
theorem B2574755 : Blo 1715058 2574755 := bstep (se 1 (by rfl) ⟨1931066, by rfl⟩ : syracuseStep 2574755 = 3862133) B3862133
theorem B2443699 : Blo 1715058 2443699 := bstep (se 1 (by rfl) ⟨1832774, by rfl⟩ : syracuseStep 2443699 = 3665549) B3665549
theorem B2574785 : Blo 1715058 2574785 := bstep (se 2 (by rfl) ⟨965544, by rfl⟩ : syracuseStep 2574785 = 1931089) B1931089
theorem B5794253 : Blo 1715058 5794253 := bstep (se 3 (by rfl) ⟨1086422, by rfl⟩ : syracuseStep 5794253 = 2172845) B2172845
theorem B3860945 : Blo 1715058 3860945 := bstep (se 2 (by rfl) ⟨1447854, by rfl⟩ : syracuseStep 3860945 = 2895709) B2895709
theorem B2574803 : Blo 1715058 2574803 := bstep (se 1 (by rfl) ⟨1931102, by rfl⟩ : syracuseStep 2574803 = 3862205) B3862205
theorem B2894305 : Blo 1715058 2894305 := bstep (se 2 (by rfl) ⟨1085364, by rfl⟩ : syracuseStep 2894305 = 2170729) B2170729
theorem B3860963 : Blo 1715058 3860963 := bstep (se 1 (by rfl) ⟨2895722, by rfl⟩ : syracuseStep 3860963 = 5791445) B5791445
theorem B2574833 : Blo 1715058 2574833 := bstep (se 2 (by rfl) ⟨965562, by rfl⟩ : syracuseStep 2574833 = 1931125) B1931125
theorem B2894339 : Blo 1715058 2894339 := bstep (se 1 (by rfl) ⟨2170754, by rfl⟩ : syracuseStep 2894339 = 4341509) B4341509
theorem B3664387 : Blo 1715058 3664387 := bstep (se 1 (by rfl) ⟨2748290, by rfl⟩ : syracuseStep 3664387 = 5496581) B5496581
theorem B2574851 : Blo 1715058 2574851 := bstep (se 1 (by rfl) ⟨1931138, by rfl⟩ : syracuseStep 2574851 = 3862277) B3862277
theorem B5794307 : Blo 1715058 5794307 := bstep (se 1 (by rfl) ⟨4345730, by rfl⟩ : syracuseStep 5794307 = 8691461) B8691461
theorem B2574881 : Blo 1715058 2574881 := bstep (se 2 (by rfl) ⟨965580, by rfl⟩ : syracuseStep 2574881 = 1931161) B1931161
theorem B8686115 : Blo 1715058 8686115 := bstep (se 1 (by rfl) ⟨6514586, by rfl⟩ : syracuseStep 8686115 = 13029173) B13029173
theorem B2574899 : Blo 1715058 2574899 := bstep (se 1 (by rfl) ⟨1931174, by rfl⟩ : syracuseStep 2574899 = 3862349) B3862349
theorem B62655029 : Blo 1715058 62655029 := bstep (se 5 (by rfl) ⟨2936954, by rfl⟩ : syracuseStep 62655029 = 5873909) B5873909
theorem B2574929 : Blo 1715058 2574929 := bstep (se 2 (by rfl) ⟨965598, by rfl⟩ : syracuseStep 2574929 = 1931197) B1931197
theorem B2574947 : Blo 1715058 2574947 := bstep (se 1 (by rfl) ⟨1931210, by rfl⟩ : syracuseStep 2574947 = 3862421) B3862421
theorem B2574977 : Blo 1715058 2574977 := bstep (se 2 (by rfl) ⟨965616, by rfl⟩ : syracuseStep 2574977 = 1931233) B1931233
theorem B2894467 : Blo 1715058 2894467 := bstep (se 1 (by rfl) ⟨2170850, by rfl⟩ : syracuseStep 2894467 = 4341701) B4341701
theorem B2574995 : Blo 1715058 2574995 := bstep (se 1 (by rfl) ⟨1931246, by rfl⟩ : syracuseStep 2574995 = 3862493) B3862493
theorem B2575025 : Blo 1715058 2575025 := bstep (se 2 (by rfl) ⟨965634, by rfl⟩ : syracuseStep 2575025 = 1931269) B1931269
theorem B2575043 : Blo 1715058 2575043 := bstep (se 1 (by rfl) ⟨1931282, by rfl⟩ : syracuseStep 2575043 = 3862565) B3862565
theorem B2575073 : Blo 1715058 2575073 := bstep (se 2 (by rfl) ⟨965652, by rfl⟩ : syracuseStep 2575073 = 1931305) B1931305
theorem B3861233 : Blo 1715058 3861233 := bstep (se 2 (by rfl) ⟨1447962, by rfl⟩ : syracuseStep 3861233 = 2895925) B2895925
theorem B2575091 : Blo 1715058 2575091 := bstep (se 1 (by rfl) ⟨1931318, by rfl⟩ : syracuseStep 2575091 = 3862637) B3862637
theorem B3861251 : Blo 1715058 3861251 := bstep (se 1 (by rfl) ⟨2895938, by rfl⟩ : syracuseStep 3861251 = 5791877) B5791877
theorem B9276173 : Blo 1715058 9276173 := bstep (se 3 (by rfl) ⟨1739282, by rfl⟩ : syracuseStep 9276173 = 3478565) B3478565
theorem B2894609 : Blo 1715058 2894609 := bstep (se 2 (by rfl) ⟨1085478, by rfl⟩ : syracuseStep 2894609 = 2170957) B2170957
theorem B2575121 : Blo 1715058 2575121 := bstep (se 2 (by rfl) ⟨965670, by rfl⟩ : syracuseStep 2575121 = 1931341) B1931341
theorem B5794577 : Blo 1715058 5794577 := bstep (se 2 (by rfl) ⟨2172966, by rfl⟩ : syracuseStep 5794577 = 4345933) B4345933
theorem B93940501 : Blo 1715058 93940501 := bstep (se 6 (by rfl) ⟨2201730, by rfl⟩ : syracuseStep 93940501 = 4403461) B4403461
theorem B5499683 : Blo 1715058 5499683 := bstep (se 1 (by rfl) ⟨4124762, by rfl⟩ : syracuseStep 5499683 = 8249525) B8249525
theorem B2575139 : Blo 1715058 2575139 := bstep (se 1 (by rfl) ⟨1931354, by rfl⟩ : syracuseStep 2575139 = 3862709) B3862709
theorem B2575169 : Blo 1715058 2575169 := bstep (se 2 (by rfl) ⟨965688, by rfl⟩ : syracuseStep 2575169 = 1931377) B1931377
theorem B2575187 : Blo 1715058 2575187 := bstep (se 1 (by rfl) ⟨1931390, by rfl⟩ : syracuseStep 2575187 = 3862781) B3862781
theorem B2575217 : Blo 1715058 2575217 := bstep (se 2 (by rfl) ⟨965706, by rfl⟩ : syracuseStep 2575217 = 1931413) B1931413
theorem B1715059 : Blo 1715058 1715059 := bstep (se 1 (by rfl) ⟨1286294, by rfl⟩ : syracuseStep 1715059 = 2572589) B2572589
theorem B1715075 : Blo 1715058 1715075 := bstep (se 1 (by rfl) ⟨1286306, by rfl⟩ : syracuseStep 1715075 = 2572613) B2572613
theorem B2575235 : Blo 1715058 2575235 := bstep (se 1 (by rfl) ⟨1931426, by rfl⟩ : syracuseStep 2575235 = 3862853) B3862853
theorem B55643021 : Blo 1715058 55643021 := bstep (se 3 (by rfl) ⟨10433066, by rfl⟩ : syracuseStep 55643021 = 20866133) B20866133
theorem B2894737 : Blo 1715058 2894737 := bstep (se 2 (by rfl) ⟨1085526, by rfl⟩ : syracuseStep 2894737 = 2171053) B2171053
theorem B1715091 : Blo 1715058 1715091 := bstep (se 1 (by rfl) ⟨1286318, by rfl⟩ : syracuseStep 1715091 = 2572637) B2572637
theorem B2575265 : Blo 1715058 2575265 := bstep (se 2 (by rfl) ⟨965724, by rfl⟩ : syracuseStep 2575265 = 1931449) B1931449
theorem B1715107 : Blo 1715058 1715107 := bstep (se 1 (by rfl) ⟨1286330, by rfl⟩ : syracuseStep 1715107 = 2572661) B2572661
theorem B2444195 : Blo 1715058 2444195 := bstep (se 1 (by rfl) ⟨1833146, by rfl⟩ : syracuseStep 2444195 = 3666293) B3666293
theorem B1715123 : Blo 1715058 1715123 := bstep (se 1 (by rfl) ⟨1286342, by rfl⟩ : syracuseStep 1715123 = 2572685) B2572685
theorem B2894771 : Blo 1715058 2894771 := bstep (se 1 (by rfl) ⟨2171078, by rfl⟩ : syracuseStep 2894771 = 4342157) B4342157
theorem B2575283 : Blo 1715058 2575283 := bstep (se 1 (by rfl) ⟨1931462, by rfl⟩ : syracuseStep 2575283 = 3862925) B3862925
theorem B1715139 : Blo 1715058 1715139 := bstep (se 1 (by rfl) ⟨1286354, by rfl⟩ : syracuseStep 1715139 = 2572709) B2572709
theorem B2575313 : Blo 1715058 2575313 := bstep (se 2 (by rfl) ⟨965742, by rfl⟩ : syracuseStep 2575313 = 1931485) B1931485
theorem B1715155 : Blo 1715058 1715155 := bstep (se 1 (by rfl) ⟨1286366, by rfl⟩ : syracuseStep 1715155 = 2572733) B2572733
theorem B1715171 : Blo 1715058 1715171 := bstep (se 1 (by rfl) ⟨1286378, by rfl⟩ : syracuseStep 1715171 = 2572757) B2572757
theorem B2575331 : Blo 1715058 2575331 := bstep (se 1 (by rfl) ⟨1931498, by rfl⟩ : syracuseStep 2575331 = 3862997) B3862997
theorem B1715187 : Blo 1715058 1715187 := bstep (se 1 (by rfl) ⟨1286390, by rfl⟩ : syracuseStep 1715187 = 2572781) B2572781
theorem B2575361 : Blo 1715058 2575361 := bstep (se 2 (by rfl) ⟨965760, by rfl⟩ : syracuseStep 2575361 = 1931521) B1931521
theorem B1715203 : Blo 1715058 1715203 := bstep (se 1 (by rfl) ⟨1286402, by rfl⟩ : syracuseStep 1715203 = 2572805) B2572805
theorem B3861521 : Blo 1715058 3861521 := bstep (se 2 (by rfl) ⟨1448070, by rfl⟩ : syracuseStep 3861521 = 2896141) B2896141
theorem B1715219 : Blo 1715058 1715219 := bstep (se 1 (by rfl) ⟨1286414, by rfl⟩ : syracuseStep 1715219 = 2572829) B2572829
theorem B2575379 : Blo 1715058 2575379 := bstep (se 1 (by rfl) ⟨1931534, by rfl⟩ : syracuseStep 2575379 = 3863069) B3863069
theorem B1715235 : Blo 1715058 1715235 := bstep (se 1 (by rfl) ⟨1286426, by rfl⟩ : syracuseStep 1715235 = 2572853) B2572853
theorem B3861539 : Blo 1715058 3861539 := bstep (se 1 (by rfl) ⟨2896154, by rfl⟩ : syracuseStep 3861539 = 5792309) B5792309
theorem B2575409 : Blo 1715058 2575409 := bstep (se 2 (by rfl) ⟨965778, by rfl⟩ : syracuseStep 2575409 = 1931557) B1931557
theorem B1715251 : Blo 1715058 1715251 := bstep (se 1 (by rfl) ⟨1286438, by rfl⟩ : syracuseStep 1715251 = 2572877) B2572877
theorem B2894899 : Blo 1715058 2894899 := bstep (se 1 (by rfl) ⟨2171174, by rfl⟩ : syracuseStep 2894899 = 4342349) B4342349
theorem B1715267 : Blo 1715058 1715267 := bstep (se 1 (by rfl) ⟨1286450, by rfl⟩ : syracuseStep 1715267 = 2572901) B2572901
theorem B2608195 : Blo 1715058 2608195 := bstep (se 1 (by rfl) ⟨1956146, by rfl⟩ : syracuseStep 2608195 = 3912293) B3912293
theorem B2575427 : Blo 1715058 2575427 := bstep (se 1 (by rfl) ⟨1931570, by rfl⟩ : syracuseStep 2575427 = 3863141) B3863141
theorem B1715283 : Blo 1715058 1715283 := bstep (se 1 (by rfl) ⟨1286462, by rfl⟩ : syracuseStep 1715283 = 2572925) B2572925
theorem B2575457 : Blo 1715058 2575457 := bstep (se 2 (by rfl) ⟨965796, by rfl⟩ : syracuseStep 2575457 = 1931593) B1931593
theorem B1715299 : Blo 1715058 1715299 := bstep (se 1 (by rfl) ⟨1286474, by rfl⟩ : syracuseStep 1715299 = 2572949) B2572949
theorem B1715315 : Blo 1715058 1715315 := bstep (se 1 (by rfl) ⟨1286486, by rfl⟩ : syracuseStep 1715315 = 2572973) B2572973
theorem B2575475 : Blo 1715058 2575475 := bstep (se 1 (by rfl) ⟨1931606, by rfl⟩ : syracuseStep 2575475 = 3863213) B3863213
theorem B1715331 : Blo 1715058 1715331 := bstep (se 1 (by rfl) ⟨1286498, by rfl⟩ : syracuseStep 1715331 = 2572997) B2572997
theorem B2575505 : Blo 1715058 2575505 := bstep (se 2 (by rfl) ⟨965814, by rfl⟩ : syracuseStep 2575505 = 1931629) B1931629
theorem B1715347 : Blo 1715058 1715347 := bstep (se 1 (by rfl) ⟨1286510, by rfl⟩ : syracuseStep 1715347 = 2573021) B2573021
theorem B1715363 : Blo 1715058 1715363 := bstep (se 1 (by rfl) ⟨1286522, by rfl⟩ : syracuseStep 1715363 = 2573045) B2573045
theorem B2608291 : Blo 1715058 2608291 := bstep (se 1 (by rfl) ⟨1956218, by rfl⟩ : syracuseStep 2608291 = 3912437) B3912437
theorem B4885667 : Blo 1715058 4885667 := bstep (se 1 (by rfl) ⟨3664250, by rfl⟩ : syracuseStep 4885667 = 7328501) B7328501
theorem B4123811 : Blo 1715058 4123811 := bstep (se 1 (by rfl) ⟨3092858, by rfl⟩ : syracuseStep 4123811 = 6185717) B6185717
theorem B2575523 : Blo 1715058 2575523 := bstep (se 1 (by rfl) ⟨1931642, by rfl⟩ : syracuseStep 2575523 = 3863285) B3863285
theorem B1715379 : Blo 1715058 1715379 := bstep (se 1 (by rfl) ⟨1286534, by rfl⟩ : syracuseStep 1715379 = 2573069) B2573069
theorem B2895041 : Blo 1715058 2895041 := bstep (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) B2171281
theorem B2575553 : Blo 1715058 2575553 := bstep (se 2 (by rfl) ⟨965832, by rfl⟩ : syracuseStep 2575553 = 1931665) B1931665
theorem B1715395 : Blo 1715058 1715395 := bstep (se 1 (by rfl) ⟨1286546, by rfl⟩ : syracuseStep 1715395 = 2573093) B2573093
theorem B3665105 : Blo 1715058 3665105 := bstep (se 2 (by rfl) ⟨1374414, by rfl⟩ : syracuseStep 3665105 = 2748829) B2748829
theorem B1715411 : Blo 1715058 1715411 := bstep (se 1 (by rfl) ⟨1286558, by rfl⟩ : syracuseStep 1715411 = 2573117) B2573117
theorem B2575571 : Blo 1715058 2575571 := bstep (se 1 (by rfl) ⟨1931678, by rfl⟩ : syracuseStep 2575571 = 3863357) B3863357
theorem B1715427 : Blo 1715058 1715427 := bstep (se 1 (by rfl) ⟨1286570, by rfl⟩ : syracuseStep 1715427 = 2573141) B2573141
theorem B4345073 : Blo 1715058 4345073 := bstep (se 2 (by rfl) ⟨1629402, by rfl⟩ : syracuseStep 4345073 = 3258805) B3258805
theorem B1715443 : Blo 1715058 1715443 := bstep (se 1 (by rfl) ⟨1286582, by rfl⟩ : syracuseStep 1715443 = 2573165) B2573165
theorem B1715459 : Blo 1715058 1715459 := bstep (se 1 (by rfl) ⟨1286594, by rfl⟩ : syracuseStep 1715459 = 2573189) B2573189
theorem B1715475 : Blo 1715058 1715475 := bstep (se 1 (by rfl) ⟨1286606, by rfl⟩ : syracuseStep 1715475 = 2573213) B2573213
theorem B1715491 : Blo 1715058 1715491 := bstep (se 1 (by rfl) ⟨1286618, by rfl⟩ : syracuseStep 1715491 = 2573237) B2573237
theorem B4345123 : Blo 1715058 4345123 := bstep (se 1 (by rfl) ⟨3258842, by rfl⟩ : syracuseStep 4345123 = 6517685) B6517685
theorem B3861809 : Blo 1715058 3861809 := bstep (se 2 (by rfl) ⟨1448178, by rfl⟩ : syracuseStep 3861809 = 2896357) B2896357
theorem B1715507 : Blo 1715058 1715507 := bstep (se 1 (by rfl) ⟨1286630, by rfl⟩ : syracuseStep 1715507 = 2573261) B2573261
theorem B2895169 : Blo 1715058 2895169 := bstep (se 2 (by rfl) ⟨1085688, by rfl⟩ : syracuseStep 2895169 = 2171377) B2171377
theorem B1715523 : Blo 1715058 1715523 := bstep (se 1 (by rfl) ⟨1286642, by rfl⟩ : syracuseStep 1715523 = 2573285) B2573285
theorem B3861827 : Blo 1715058 3861827 := bstep (se 1 (by rfl) ⟨2896370, by rfl⟩ : syracuseStep 3861827 = 5792741) B5792741
theorem B8686925 : Blo 1715058 8686925 := bstep (se 3 (by rfl) ⟨1628798, by rfl⟩ : syracuseStep 8686925 = 3257597) B3257597
theorem B1715539 : Blo 1715058 1715539 := bstep (se 1 (by rfl) ⟨1286654, by rfl⟩ : syracuseStep 1715539 = 2573309) B2573309
theorem B1715555 : Blo 1715058 1715555 := bstep (se 1 (by rfl) ⟨1286666, by rfl⟩ : syracuseStep 1715555 = 2573333) B2573333
theorem B2895203 : Blo 1715058 2895203 := bstep (se 1 (by rfl) ⟨2171402, by rfl⟩ : syracuseStep 2895203 = 4342805) B4342805
theorem B9776483 : Blo 1715058 9776483 := bstep (se 1 (by rfl) ⟨7332362, by rfl⟩ : syracuseStep 9776483 = 14664725) B14664725
theorem B1715571 : Blo 1715058 1715571 := bstep (se 1 (by rfl) ⟨1286678, by rfl⟩ : syracuseStep 1715571 = 2573357) B2573357
theorem B1715587 : Blo 1715058 1715587 := bstep (se 1 (by rfl) ⟨1286690, by rfl⟩ : syracuseStep 1715587 = 2573381) B2573381
theorem B1715603 : Blo 1715058 1715603 := bstep (se 1 (by rfl) ⟨1286702, by rfl⟩ : syracuseStep 1715603 = 2573405) B2573405
theorem B1715619 : Blo 1715058 1715619 := bstep (se 1 (by rfl) ⟨1286714, by rfl⟩ : syracuseStep 1715619 = 2573429) B2573429
theorem B4345265 : Blo 1715058 4345265 := bstep (se 2 (by rfl) ⟨1629474, by rfl⟩ : syracuseStep 4345265 = 3258949) B3258949
theorem B1715635 : Blo 1715058 1715635 := bstep (se 1 (by rfl) ⟨1286726, by rfl⟩ : syracuseStep 1715635 = 2573453) B2573453
theorem B1715651 : Blo 1715058 1715651 := bstep (se 1 (by rfl) ⟨1286738, by rfl⟩ : syracuseStep 1715651 = 2573477) B2573477
theorem B1715667 : Blo 1715058 1715667 := bstep (se 1 (by rfl) ⟨1286750, by rfl⟩ : syracuseStep 1715667 = 2573501) B2573501
theorem B1715683 : Blo 1715058 1715683 := bstep (se 1 (by rfl) ⟨1286762, by rfl⟩ : syracuseStep 1715683 = 2573525) B2573525
theorem B2895331 : Blo 1715058 2895331 := bstep (se 1 (by rfl) ⟨2171498, by rfl⟩ : syracuseStep 2895331 = 4342997) B4342997
theorem B1715699 : Blo 1715058 1715699 := bstep (se 1 (by rfl) ⟨1286774, by rfl⟩ : syracuseStep 1715699 = 2573549) B2573549
theorem B1715715 : Blo 1715058 1715715 := bstep (se 1 (by rfl) ⟨1286786, by rfl⟩ : syracuseStep 1715715 = 2573573) B2573573
theorem B1715731 : Blo 1715058 1715731 := bstep (se 1 (by rfl) ⟨1286798, by rfl⟩ : syracuseStep 1715731 = 2573597) B2573597
theorem B1715747 : Blo 1715058 1715747 := bstep (se 1 (by rfl) ⟨1286810, by rfl⟩ : syracuseStep 1715747 = 2573621) B2573621
theorem B7826993 : Blo 1715058 7826993 := bstep (se 2 (by rfl) ⟨2935122, by rfl⟩ : syracuseStep 7826993 = 5870245) B5870245
theorem B1715763 : Blo 1715058 1715763 := bstep (se 1 (by rfl) ⟨1286822, by rfl⟩ : syracuseStep 1715763 = 2573645) B2573645
theorem B1715779 : Blo 1715058 1715779 := bstep (se 1 (by rfl) ⟨1286834, by rfl⟩ : syracuseStep 1715779 = 2573669) B2573669
theorem B19541573 : Blo 1715058 19541573 := bstep (se 4 (by rfl) ⟨1832022, by rfl⟩ : syracuseStep 19541573 = 3664045) B3664045
theorem B3477073 : Blo 1715058 3477073 := bstep (se 2 (by rfl) ⟨1303902, by rfl⟩ : syracuseStep 3477073 = 2607805) B2607805
theorem B1715795 : Blo 1715058 1715795 := bstep (se 1 (by rfl) ⟨1286846, by rfl⟩ : syracuseStep 1715795 = 2573693) B2573693
theorem B3862097 : Blo 1715058 3862097 := bstep (se 2 (by rfl) ⟨1448286, by rfl⟩ : syracuseStep 3862097 = 2896573) B2896573
theorem B1715811 : Blo 1715058 1715811 := bstep (se 1 (by rfl) ⟨1286858, by rfl⟩ : syracuseStep 1715811 = 2573717) B2573717
theorem B3862115 : Blo 1715058 3862115 := bstep (se 1 (by rfl) ⟨2896586, by rfl⟩ : syracuseStep 3862115 = 5793173) B5793173
theorem B2895473 : Blo 1715058 2895473 := bstep (se 2 (by rfl) ⟨1085802, by rfl⟩ : syracuseStep 2895473 = 2171605) B2171605
theorem B1715827 : Blo 1715058 1715827 := bstep (se 1 (by rfl) ⟨1286870, by rfl⟩ : syracuseStep 1715827 = 2573741) B2573741
theorem B1715843 : Blo 1715058 1715843 := bstep (se 1 (by rfl) ⟨1286882, by rfl⟩ : syracuseStep 1715843 = 2573765) B2573765
theorem B1715859 : Blo 1715058 1715859 := bstep (se 1 (by rfl) ⟨1286894, by rfl⟩ : syracuseStep 1715859 = 2573789) B2573789
theorem B1715875 : Blo 1715058 1715875 := bstep (se 1 (by rfl) ⟨1286906, by rfl⟩ : syracuseStep 1715875 = 2573813) B2573813
theorem B1715891 : Blo 1715058 1715891 := bstep (se 1 (by rfl) ⟨1286918, by rfl⟩ : syracuseStep 1715891 = 2573837) B2573837
theorem B1715907 : Blo 1715058 1715907 := bstep (se 1 (by rfl) ⟨1286930, by rfl⟩ : syracuseStep 1715907 = 2573861) B2573861
theorem B1715923 : Blo 1715058 1715923 := bstep (se 1 (by rfl) ⟨1286942, by rfl⟩ : syracuseStep 1715923 = 2573885) B2573885
theorem B1715939 : Blo 1715058 1715939 := bstep (se 1 (by rfl) ⟨1286954, by rfl⟩ : syracuseStep 1715939 = 2573909) B2573909
theorem B10432241 : Blo 1715058 10432241 := bstep (se 2 (by rfl) ⟨3912090, by rfl⟩ : syracuseStep 10432241 = 7824181) B7824181
theorem B2895601 : Blo 1715058 2895601 := bstep (se 2 (by rfl) ⟨1085850, by rfl⟩ : syracuseStep 2895601 = 2171701) B2171701
theorem B1715955 : Blo 1715058 1715955 := bstep (se 1 (by rfl) ⟨1286966, by rfl⟩ : syracuseStep 1715955 = 2573933) B2573933
theorem B2748163 : Blo 1715058 2748163 := bstep (se 1 (by rfl) ⟨2061122, by rfl⟩ : syracuseStep 2748163 = 4122245) B4122245
theorem B1715971 : Blo 1715058 1715971 := bstep (se 1 (by rfl) ⟨1286978, by rfl⟩ : syracuseStep 1715971 = 2573957) B2573957
theorem B3714833 : Blo 1715058 3714833 := bstep (se 2 (by rfl) ⟨1393062, by rfl⟩ : syracuseStep 3714833 = 2786125) B2786125
theorem B2895635 : Blo 1715058 2895635 := bstep (se 1 (by rfl) ⟨2171726, by rfl⟩ : syracuseStep 2895635 = 4343453) B4343453
theorem B1715987 : Blo 1715058 1715987 := bstep (se 1 (by rfl) ⟨1286990, by rfl⟩ : syracuseStep 1715987 = 2573981) B2573981
theorem B1716003 : Blo 1715058 1716003 := bstep (se 1 (by rfl) ⟨1287002, by rfl⟩ : syracuseStep 1716003 = 2574005) B2574005
theorem B1716019 : Blo 1715058 1716019 := bstep (se 1 (by rfl) ⟨1287014, by rfl⟩ : syracuseStep 1716019 = 2574029) B2574029
theorem B1716035 : Blo 1715058 1716035 := bstep (se 1 (by rfl) ⟨1287026, by rfl⟩ : syracuseStep 1716035 = 2574053) B2574053
theorem B1716051 : Blo 1715058 1716051 := bstep (se 1 (by rfl) ⟨1287038, by rfl⟩ : syracuseStep 1716051 = 2574077) B2574077
theorem B1716067 : Blo 1715058 1716067 := bstep (se 1 (by rfl) ⟨1287050, by rfl⟩ : syracuseStep 1716067 = 2574101) B2574101
theorem B3862385 : Blo 1715058 3862385 := bstep (se 2 (by rfl) ⟨1448394, by rfl⟩ : syracuseStep 3862385 = 2896789) B2896789
theorem B1716083 : Blo 1715058 1716083 := bstep (se 1 (by rfl) ⟨1287062, by rfl⟩ : syracuseStep 1716083 = 2574125) B2574125
theorem B1716099 : Blo 1715058 1716099 := bstep (se 1 (by rfl) ⟨1287074, by rfl⟩ : syracuseStep 1716099 = 2574149) B2574149
theorem B3862403 : Blo 1715058 3862403 := bstep (se 1 (by rfl) ⟨2896802, by rfl⟩ : syracuseStep 3862403 = 5793605) B5793605
theorem B2895763 : Blo 1715058 2895763 := bstep (se 1 (by rfl) ⟨2171822, by rfl⟩ : syracuseStep 2895763 = 4343645) B4343645
theorem B1716115 : Blo 1715058 1716115 := bstep (se 1 (by rfl) ⟨1287086, by rfl⟩ : syracuseStep 1716115 = 2574173) B2574173
theorem B1716131 : Blo 1715058 1716131 := bstep (se 1 (by rfl) ⟨1287098, by rfl⟩ : syracuseStep 1716131 = 2574197) B2574197
theorem B1716147 : Blo 1715058 1716147 := bstep (se 1 (by rfl) ⟨1287110, by rfl⟩ : syracuseStep 1716147 = 2574221) B2574221
theorem B1716163 : Blo 1715058 1716163 := bstep (se 1 (by rfl) ⟨1287122, by rfl⟩ : syracuseStep 1716163 = 2574245) B2574245
theorem B4886477 : Blo 1715058 4886477 := bstep (se 3 (by rfl) ⟨916214, by rfl⟩ : syracuseStep 4886477 = 1832429) B1832429
theorem B2936785 : Blo 1715058 2936785 := bstep (se 2 (by rfl) ⟨1101294, by rfl⟩ : syracuseStep 2936785 = 2202589) B2202589
theorem B1716179 : Blo 1715058 1716179 := bstep (se 1 (by rfl) ⟨1287134, by rfl⟩ : syracuseStep 1716179 = 2574269) B2574269
theorem B3256291 : Blo 1715058 3256291 := bstep (se 1 (by rfl) ⟨2442218, by rfl⟩ : syracuseStep 3256291 = 4884437) B4884437
theorem B1716195 : Blo 1715058 1716195 := bstep (se 1 (by rfl) ⟨1287146, by rfl⟩ : syracuseStep 1716195 = 2574293) B2574293
theorem B3665891 : Blo 1715058 3665891 := bstep (se 1 (by rfl) ⟨2749418, by rfl⟩ : syracuseStep 3665891 = 5498837) B5498837
theorem B1716211 : Blo 1715058 1716211 := bstep (se 1 (by rfl) ⟨1287158, by rfl⟩ : syracuseStep 1716211 = 2574317) B2574317
theorem B2748419 : Blo 1715058 2748419 := bstep (se 1 (by rfl) ⟨2061314, by rfl⟩ : syracuseStep 2748419 = 4122629) B4122629
theorem B1716227 : Blo 1715058 1716227 := bstep (se 1 (by rfl) ⟨1287170, by rfl⟩ : syracuseStep 1716227 = 2574341) B2574341
theorem B3256337 : Blo 1715058 3256337 := bstep (se 2 (by rfl) ⟨1221126, by rfl⟩ : syracuseStep 3256337 = 2442253) B2442253
theorem B1716243 : Blo 1715058 1716243 := bstep (se 1 (by rfl) ⟨1287182, by rfl⟩ : syracuseStep 1716243 = 2574365) B2574365
theorem B2895905 : Blo 1715058 2895905 := bstep (se 2 (by rfl) ⟨1085964, by rfl⟩ : syracuseStep 2895905 = 2171929) B2171929
theorem B1716259 : Blo 1715058 1716259 := bstep (se 1 (by rfl) ⟨1287194, by rfl⟩ : syracuseStep 1716259 = 2574389) B2574389
theorem B1716275 : Blo 1715058 1716275 := bstep (se 1 (by rfl) ⟨1287206, by rfl⟩ : syracuseStep 1716275 = 2574413) B2574413
theorem B1716291 : Blo 1715058 1716291 := bstep (se 1 (by rfl) ⟨1287218, by rfl⟩ : syracuseStep 1716291 = 2574437) B2574437
theorem B1716307 : Blo 1715058 1716307 := bstep (se 1 (by rfl) ⟨1287230, by rfl⟩ : syracuseStep 1716307 = 2574461) B2574461
theorem B1716323 : Blo 1715058 1716323 := bstep (se 1 (by rfl) ⟨1287242, by rfl⟩ : syracuseStep 1716323 = 2574485) B2574485
theorem B19550321 : Blo 1715058 19550321 := bstep (se 2 (by rfl) ⟨7331370, by rfl⟩ : syracuseStep 19550321 = 14662741) B14662741
theorem B1716339 : Blo 1715058 1716339 := bstep (se 1 (by rfl) ⟨1287254, by rfl⟩ : syracuseStep 1716339 = 2574509) B2574509
theorem B1716355 : Blo 1715058 1716355 := bstep (se 1 (by rfl) ⟨1287266, by rfl⟩ : syracuseStep 1716355 = 2574533) B2574533
theorem B4886669 : Blo 1715058 4886669 := bstep (se 3 (by rfl) ⟨916250, by rfl⟩ : syracuseStep 4886669 = 1832501) B1832501
theorem B3862673 : Blo 1715058 3862673 := bstep (se 2 (by rfl) ⟨1448502, by rfl⟩ : syracuseStep 3862673 = 2897005) B2897005
theorem B1716371 : Blo 1715058 1716371 := bstep (se 1 (by rfl) ⟨1287278, by rfl⟩ : syracuseStep 1716371 = 2574557) B2574557
theorem B2896033 : Blo 1715058 2896033 := bstep (se 2 (by rfl) ⟨1086012, by rfl⟩ : syracuseStep 2896033 = 2172025) B2172025
theorem B3715235 : Blo 1715058 3715235 := bstep (se 1 (by rfl) ⟨2786426, by rfl⟩ : syracuseStep 3715235 = 5572853) B5572853
theorem B1716387 : Blo 1715058 1716387 := bstep (se 1 (by rfl) ⟨1287290, by rfl⟩ : syracuseStep 1716387 = 2574581) B2574581
theorem B3862691 : Blo 1715058 3862691 := bstep (se 1 (by rfl) ⟨2897018, by rfl⟩ : syracuseStep 3862691 = 5794037) B5794037
theorem B1716403 : Blo 1715058 1716403 := bstep (se 1 (by rfl) ⟨1287302, by rfl⟩ : syracuseStep 1716403 = 2574605) B2574605
theorem B2748611 : Blo 1715058 2748611 := bstep (se 1 (by rfl) ⟨2061458, by rfl⟩ : syracuseStep 2748611 = 4122917) B4122917
theorem B2896067 : Blo 1715058 2896067 := bstep (se 1 (by rfl) ⟨2172050, by rfl⟩ : syracuseStep 2896067 = 4344101) B4344101
theorem B1716419 : Blo 1715058 1716419 := bstep (se 1 (by rfl) ⟨1287314, by rfl⟩ : syracuseStep 1716419 = 2574629) B2574629
theorem B1716435 : Blo 1715058 1716435 := bstep (se 1 (by rfl) ⟨1287326, by rfl⟩ : syracuseStep 1716435 = 2574653) B2574653
theorem B1716451 : Blo 1715058 1716451 := bstep (se 1 (by rfl) ⟨1287338, by rfl⟩ : syracuseStep 1716451 = 2574677) B2574677
theorem B1716467 : Blo 1715058 1716467 := bstep (se 1 (by rfl) ⟨1287350, by rfl⟩ : syracuseStep 1716467 = 2574701) B2574701
theorem B1716483 : Blo 1715058 1716483 := bstep (se 1 (by rfl) ⟨1287362, by rfl⟩ : syracuseStep 1716483 = 2574725) B2574725
theorem B1716499 : Blo 1715058 1716499 := bstep (se 1 (by rfl) ⟨1287374, by rfl⟩ : syracuseStep 1716499 = 2574749) B2574749
theorem B1716515 : Blo 1715058 1716515 := bstep (se 1 (by rfl) ⟨1287386, by rfl⟩ : syracuseStep 1716515 = 2574773) B2574773
theorem B3256625 : Blo 1715058 3256625 := bstep (se 2 (by rfl) ⟨1221234, by rfl⟩ : syracuseStep 3256625 = 2442469) B2442469
theorem B1929523 : Blo 1715058 1929523 := bstep (se 1 (by rfl) ⟨1447142, by rfl⟩ : syracuseStep 1929523 = 2894285) B2894285
theorem B1716531 : Blo 1715058 1716531 := bstep (se 1 (by rfl) ⟨1287398, by rfl⟩ : syracuseStep 1716531 = 2574797) B2574797
theorem B2896195 : Blo 1715058 2896195 := bstep (se 1 (by rfl) ⟨2172146, by rfl⟩ : syracuseStep 2896195 = 4344293) B4344293
theorem B1716547 : Blo 1715058 1716547 := bstep (se 1 (by rfl) ⟨1287410, by rfl⟩ : syracuseStep 1716547 = 2574821) B2574821
theorem B4403537 : Blo 1715058 4403537 := bstep (se 2 (by rfl) ⟨1651326, by rfl⟩ : syracuseStep 4403537 = 3302653) B3302653
theorem B1716563 : Blo 1715058 1716563 := bstep (se 1 (by rfl) ⟨1287422, by rfl⟩ : syracuseStep 1716563 = 2574845) B2574845
theorem B1716579 : Blo 1715058 1716579 := bstep (se 1 (by rfl) ⟨1287434, by rfl⟩ : syracuseStep 1716579 = 2574869) B2574869
theorem B1716595 : Blo 1715058 1716595 := bstep (se 1 (by rfl) ⟨1287446, by rfl⟩ : syracuseStep 1716595 = 2574893) B2574893
theorem B1716611 : Blo 1715058 1716611 := bstep (se 1 (by rfl) ⟨1287458, by rfl⟩ : syracuseStep 1716611 = 2574917) B2574917
theorem B4346257 : Blo 1715058 4346257 := bstep (se 2 (by rfl) ⟨1629846, by rfl⟩ : syracuseStep 4346257 = 3259693) B3259693
theorem B1716627 : Blo 1715058 1716627 := bstep (se 1 (by rfl) ⟨1287470, by rfl⟩ : syracuseStep 1716627 = 2574941) B2574941
theorem B1716643 : Blo 1715058 1716643 := bstep (se 1 (by rfl) ⟨1287482, by rfl⟩ : syracuseStep 1716643 = 2574965) B2574965
theorem B6517169 : Blo 1715058 6517169 := bstep (se 2 (by rfl) ⟨2443938, by rfl⟩ : syracuseStep 6517169 = 4887877) B4887877
theorem B1716659 : Blo 1715058 1716659 := bstep (se 1 (by rfl) ⟨1287494, by rfl⟩ : syracuseStep 1716659 = 2574989) B2574989
theorem B3862961 : Blo 1715058 3862961 := bstep (se 2 (by rfl) ⟨1448610, by rfl⟩ : syracuseStep 3862961 = 2897221) B2897221
theorem B21451189 : Blo 1715058 21451189 := bstep (se 5 (by rfl) ⟨1005524, by rfl⟩ : syracuseStep 21451189 = 2011049) B2011049
theorem B1929667 : Blo 1715058 1929667 := bstep (se 1 (by rfl) ⟨1447250, by rfl⟩ : syracuseStep 1929667 = 2894501) B2894501
theorem B1716675 : Blo 1715058 1716675 := bstep (se 1 (by rfl) ⟨1287506, by rfl⟩ : syracuseStep 1716675 = 2575013) B2575013
theorem B3862979 : Blo 1715058 3862979 := bstep (se 1 (by rfl) ⟨2897234, by rfl⟩ : syracuseStep 3862979 = 5794469) B5794469
theorem B2896337 : Blo 1715058 2896337 := bstep (se 2 (by rfl) ⟨1086126, by rfl⟩ : syracuseStep 2896337 = 2172253) B2172253
theorem B1716691 : Blo 1715058 1716691 := bstep (se 1 (by rfl) ⟨1287518, by rfl⟩ : syracuseStep 1716691 = 2575037) B2575037
theorem B7328227 : Blo 1715058 7328227 := bstep (se 1 (by rfl) ⟨5496170, by rfl⟩ : syracuseStep 7328227 = 10992341) B10992341
theorem B1716707 : Blo 1715058 1716707 := bstep (se 1 (by rfl) ⟨1287530, by rfl⟩ : syracuseStep 1716707 = 2575061) B2575061
theorem B1716723 : Blo 1715058 1716723 := bstep (se 1 (by rfl) ⟨1287542, by rfl⟩ : syracuseStep 1716723 = 2575085) B2575085
theorem B3092995 : Blo 1715058 3092995 := bstep (se 1 (by rfl) ⟨2319746, by rfl⟩ : syracuseStep 3092995 = 4639493) B4639493
theorem B1716739 : Blo 1715058 1716739 := bstep (se 1 (by rfl) ⟨1287554, by rfl⟩ : syracuseStep 1716739 = 2575109) B2575109
theorem B1716755 : Blo 1715058 1716755 := bstep (se 1 (by rfl) ⟨1287566, by rfl⟩ : syracuseStep 1716755 = 2575133) B2575133
theorem B1716771 : Blo 1715058 1716771 := bstep (se 1 (by rfl) ⟨1287578, by rfl⟩ : syracuseStep 1716771 = 2575157) B2575157
theorem B1716787 : Blo 1715058 1716787 := bstep (se 1 (by rfl) ⟨1287590, by rfl⟩ : syracuseStep 1716787 = 2575181) B2575181
theorem B1716803 : Blo 1715058 1716803 := bstep (se 1 (by rfl) ⟨1287602, by rfl⟩ : syracuseStep 1716803 = 2575205) B2575205
theorem B10998341 : Blo 1715058 10998341 := bstep (se 4 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 10998341 = 2062189) B2062189
theorem B2896465 : Blo 1715058 2896465 := bstep (se 2 (by rfl) ⟨1086174, by rfl⟩ : syracuseStep 2896465 = 2172349) B2172349
theorem B1929811 : Blo 1715058 1929811 := bstep (se 1 (by rfl) ⟨1447358, by rfl⟩ : syracuseStep 1929811 = 2894717) B2894717
theorem B1716819 : Blo 1715058 1716819 := bstep (se 1 (by rfl) ⟨1287614, by rfl⟩ : syracuseStep 1716819 = 2575229) B2575229
theorem B1716835 : Blo 1715058 1716835 := bstep (se 1 (by rfl) ⟨1287626, by rfl⟩ : syracuseStep 1716835 = 2575253) B2575253
theorem B2896499 : Blo 1715058 2896499 := bstep (se 1 (by rfl) ⟨2172374, by rfl⟩ : syracuseStep 2896499 = 4344749) B4344749
theorem B1716851 : Blo 1715058 1716851 := bstep (se 1 (by rfl) ⟨1287638, by rfl⟩ : syracuseStep 1716851 = 2575277) B2575277
theorem B1716867 : Blo 1715058 1716867 := bstep (se 1 (by rfl) ⟨1287650, by rfl⟩ : syracuseStep 1716867 = 2575301) B2575301
theorem B1716883 : Blo 1715058 1716883 := bstep (se 1 (by rfl) ⟨1287662, by rfl⟩ : syracuseStep 1716883 = 2575325) B2575325
theorem B1716899 : Blo 1715058 1716899 := bstep (se 1 (by rfl) ⟨1287674, by rfl⟩ : syracuseStep 1716899 = 2575349) B2575349
theorem B1716915 : Blo 1715058 1716915 := bstep (se 1 (by rfl) ⟨1287686, by rfl⟩ : syracuseStep 1716915 = 2575373) B2575373
theorem B1716931 : Blo 1715058 1716931 := bstep (se 1 (by rfl) ⟨1287698, by rfl⟩ : syracuseStep 1716931 = 2575397) B2575397
theorem B1716947 : Blo 1715058 1716947 := bstep (se 1 (by rfl) ⟨1287710, by rfl⟩ : syracuseStep 1716947 = 2575421) B2575421
theorem B3863249 : Blo 1715058 3863249 := bstep (se 2 (by rfl) ⟨1448718, by rfl⟩ : syracuseStep 3863249 = 2897437) B2897437
theorem B11735779 : Blo 1715058 11735779 := bstep (se 1 (by rfl) ⟨8801834, by rfl⟩ : syracuseStep 11735779 = 17603669) B17603669
theorem B1929955 : Blo 1715058 1929955 := bstep (se 1 (by rfl) ⟨1447466, by rfl⟩ : syracuseStep 1929955 = 2894933) B2894933
theorem B1716963 : Blo 1715058 1716963 := bstep (se 1 (by rfl) ⟨1287722, by rfl⟩ : syracuseStep 1716963 = 2575445) B2575445
theorem B3863267 : Blo 1715058 3863267 := bstep (se 1 (by rfl) ⟨2897450, by rfl⟩ : syracuseStep 3863267 = 5794901) B5794901
theorem B6607601 : Blo 1715058 6607601 := bstep (se 2 (by rfl) ⟨2477850, by rfl⟩ : syracuseStep 6607601 = 4955701) B4955701
theorem B2822899 : Blo 1715058 2822899 := bstep (se 1 (by rfl) ⟨2117174, by rfl⟩ : syracuseStep 2822899 = 4234349) B4234349
theorem B2896627 : Blo 1715058 2896627 := bstep (se 1 (by rfl) ⟨2172470, by rfl⟩ : syracuseStep 2896627 = 4344941) B4344941
theorem B1716979 : Blo 1715058 1716979 := bstep (se 1 (by rfl) ⟨1287734, by rfl⟩ : syracuseStep 1716979 = 2575469) B2575469
theorem B2609923 : Blo 1715058 2609923 := bstep (se 1 (by rfl) ⟨1957442, by rfl⟩ : syracuseStep 2609923 = 3914885) B3914885
theorem B1716995 : Blo 1715058 1716995 := bstep (se 1 (by rfl) ⟨1287746, by rfl⟩ : syracuseStep 1716995 = 2575493) B2575493
theorem B1717011 : Blo 1715058 1717011 := bstep (se 1 (by rfl) ⟨1287758, by rfl⟩ : syracuseStep 1717011 = 2575517) B2575517
theorem B1717027 : Blo 1715058 1717027 := bstep (se 1 (by rfl) ⟨1287770, by rfl⟩ : syracuseStep 1717027 = 2575541) B2575541
theorem B1717043 : Blo 1715058 1717043 := bstep (se 1 (by rfl) ⟨1287782, by rfl⟩ : syracuseStep 1717043 = 2575565) B2575565
theorem B5788529 : Blo 1715058 5788529 := bstep (se 2 (by rfl) ⟨2170698, by rfl⟩ : syracuseStep 5788529 = 4341397) B4341397
theorem B1930099 : Blo 1715058 1930099 := bstep (se 1 (by rfl) ⟨1447574, by rfl⟩ : syracuseStep 1930099 = 2895149) B2895149
theorem B2896769 : Blo 1715058 2896769 := bstep (se 2 (by rfl) ⟨1086288, by rfl⟩ : syracuseStep 2896769 = 2172577) B2172577
theorem B6181795 : Blo 1715058 6181795 := bstep (se 1 (by rfl) ⟨4636346, by rfl⟩ : syracuseStep 6181795 = 9272693) B9272693
theorem B3666865 : Blo 1715058 3666865 := bstep (se 2 (by rfl) ⟨1375074, by rfl⟩ : syracuseStep 3666865 = 2750149) B2750149
theorem B2749393 : Blo 1715058 2749393 := bstep (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) B2062045
theorem B6353891 : Blo 1715058 6353891 := bstep (se 1 (by rfl) ⟨4765418, by rfl⟩ : syracuseStep 6353891 = 9530837) B9530837
theorem B8803313 : Blo 1715058 8803313 := bstep (se 2 (by rfl) ⟨3301242, by rfl⟩ : syracuseStep 8803313 = 6602485) B6602485
theorem B2896897 : Blo 1715058 2896897 := bstep (se 2 (by rfl) ⟨1086336, by rfl⟩ : syracuseStep 2896897 = 2172673) B2172673
theorem B1930243 : Blo 1715058 1930243 := bstep (se 1 (by rfl) ⟨1447682, by rfl⟩ : syracuseStep 1930243 = 2895365) B2895365
theorem B3257347 : Blo 1715058 3257347 := bstep (se 1 (by rfl) ⟨2443010, by rfl⟩ : syracuseStep 3257347 = 4886021) B4886021
theorem B41735189 : Blo 1715058 41735189 := bstep (se 6 (by rfl) ⟨978168, by rfl⟩ : syracuseStep 41735189 = 1956337) B1956337
theorem B2896931 : Blo 1715058 2896931 := bstep (se 1 (by rfl) ⟨2172698, by rfl⟩ : syracuseStep 2896931 = 4345397) B4345397
theorem B4953155 : Blo 1715058 4953155 := bstep (se 1 (by rfl) ⟨3714866, by rfl⟩ : syracuseStep 4953155 = 7429733) B7429733
theorem B4887661 : Blo 1715058 4887661 := bstep (se 3 (by rfl) ⟨916436, by rfl⟩ : syracuseStep 4887661 = 1832873) B1832873
theorem B1930387 : Blo 1715058 1930387 := bstep (se 1 (by rfl) ⟨1447790, by rfl⟩ : syracuseStep 1930387 = 2895581) B2895581
theorem B2897059 : Blo 1715058 2897059 := bstep (se 1 (by rfl) ⟨2172794, by rfl⟩ : syracuseStep 2897059 = 4345589) B4345589
theorem B3667121 : Blo 1715058 3667121 := bstep (se 2 (by rfl) ⟨1375170, by rfl⟩ : syracuseStep 3667121 = 2750341) B2750341
theorem B12367075 : Blo 1715058 12367075 := bstep (se 1 (by rfl) ⟨9275306, by rfl⟩ : syracuseStep 12367075 = 18550613) B18550613
theorem B1930531 : Blo 1715058 1930531 := bstep (se 1 (by rfl) ⟨1447898, by rfl⟩ : syracuseStep 1930531 = 2895797) B2895797
theorem B2897201 : Blo 1715058 2897201 := bstep (se 2 (by rfl) ⟨1086450, by rfl⟩ : syracuseStep 2897201 = 2172901) B2172901
theorem B11736433 : Blo 1715058 11736433 := bstep (se 2 (by rfl) ⟨4401162, by rfl⟩ : syracuseStep 11736433 = 8802325) B8802325
theorem B6182257 : Blo 1715058 6182257 := bstep (se 2 (by rfl) ⟨2318346, by rfl⟩ : syracuseStep 6182257 = 4636693) B4636693
theorem B10442117 : Blo 1715058 10442117 := bstep (se 4 (by rfl) ⟨978948, by rfl⟩ : syracuseStep 10442117 = 1957897) B1957897
theorem B5789069 : Blo 1715058 5789069 := bstep (se 3 (by rfl) ⟨1085450, by rfl⟩ : syracuseStep 5789069 = 2170901) B2170901
theorem B1832339 : Blo 1715058 1832339 := bstep (se 1 (by rfl) ⟨1374254, by rfl⟩ : syracuseStep 1832339 = 2748509) B2748509
theorem B2897329 : Blo 1715058 2897329 := bstep (se 2 (by rfl) ⟨1086498, by rfl⟩ : syracuseStep 2897329 = 2172997) B2172997
theorem B1930675 : Blo 1715058 1930675 := bstep (se 1 (by rfl) ⟨1448006, by rfl⟩ : syracuseStep 1930675 = 2896013) B2896013
theorem B5789123 : Blo 1715058 5789123 := bstep (se 1 (by rfl) ⟨4341842, by rfl⟩ : syracuseStep 5789123 = 8683685) B8683685
theorem B3257795 : Blo 1715058 3257795 := bstep (se 1 (by rfl) ⟨2443346, by rfl⟩ : syracuseStep 3257795 = 4886693) B4886693
theorem B2897363 : Blo 1715058 2897363 := bstep (se 1 (by rfl) ⟨2173022, by rfl⟩ : syracuseStep 2897363 = 4346045) B4346045
theorem B3094033 : Blo 1715058 3094033 := bstep (se 2 (by rfl) ⟨1160262, by rfl⟩ : syracuseStep 3094033 = 2320525) B2320525
theorem B1832467 : Blo 1715058 1832467 := bstep (se 1 (by rfl) ⟨1374350, by rfl⟩ : syracuseStep 1832467 = 2748701) B2748701
theorem B1930819 : Blo 1715058 1930819 := bstep (se 1 (by rfl) ⟨1448114, by rfl⟩ : syracuseStep 1930819 = 2896229) B2896229
theorem B2897491 : Blo 1715058 2897491 := bstep (se 1 (by rfl) ⟨2173118, by rfl⟩ : syracuseStep 2897491 = 4346237) B4346237
theorem B3913379 : Blo 1715058 3913379 := bstep (se 1 (by rfl) ⟨2935034, by rfl⟩ : syracuseStep 3913379 = 5870069) B5870069
theorem B7329457 : Blo 1715058 7329457 := bstep (se 2 (by rfl) ⟨2748546, by rfl⟩ : syracuseStep 7329457 = 5497093) B5497093
theorem B5789393 : Blo 1715058 5789393 := bstep (se 2 (by rfl) ⟨2171022, by rfl⟩ : syracuseStep 5789393 = 4342045) B4342045
theorem B1930963 : Blo 1715058 1930963 := bstep (se 1 (by rfl) ⟨1448222, by rfl⟩ : syracuseStep 1930963 = 2896445) B2896445
theorem B3258083 : Blo 1715058 3258083 := bstep (se 1 (by rfl) ⟨2443562, by rfl⟩ : syracuseStep 3258083 = 4887125) B4887125
theorem B3479377 : Blo 1715058 3479377 := bstep (se 2 (by rfl) ⟨1304766, by rfl⟩ : syracuseStep 3479377 = 2609533) B2609533
theorem B1931107 : Blo 1715058 1931107 := bstep (se 1 (by rfl) ⟨1448330, by rfl⟩ : syracuseStep 1931107 = 2896661) B2896661
theorem B6518627 : Blo 1715058 6518627 := bstep (se 1 (by rfl) ⟨4888970, by rfl⟩ : syracuseStep 6518627 = 9777941) B9777941
theorem B9279373 : Blo 1715058 9279373 := bstep (se 3 (by rfl) ⟨1739882, by rfl⟩ : syracuseStep 9279373 = 3479765) B3479765
theorem B4405187 : Blo 1715058 4405187 := bstep (se 1 (by rfl) ⟨3303890, by rfl⟩ : syracuseStep 4405187 = 6607781) B6607781
theorem B1931251 : Blo 1715058 1931251 := bstep (se 1 (by rfl) ⟨1448438, by rfl⟩ : syracuseStep 1931251 = 2896877) B2896877
theorem B5494787 : Blo 1715058 5494787 := bstep (se 1 (by rfl) ⟨4121090, by rfl⟩ : syracuseStep 5494787 = 8242181) B8242181
theorem B5216291 : Blo 1715058 5216291 := bstep (se 1 (by rfl) ⟨3912218, by rfl⟩ : syracuseStep 5216291 = 7824437) B7824437
theorem B1931395 : Blo 1715058 1931395 := bstep (se 1 (by rfl) ⟨1448546, by rfl⟩ : syracuseStep 1931395 = 2897093) B2897093
theorem B8689841 : Blo 1715058 8689841 := bstep (se 2 (by rfl) ⟨3258690, by rfl⟩ : syracuseStep 8689841 = 6517381) B6517381
theorem B5789933 : Blo 1715058 5789933 := bstep (se 3 (by rfl) ⟨1085612, by rfl⟩ : syracuseStep 5789933 = 2171225) B2171225
theorem B1931539 : Blo 1715058 1931539 := bstep (se 1 (by rfl) ⟨1448654, by rfl⟩ : syracuseStep 1931539 = 2897309) B2897309
theorem B5789987 : Blo 1715058 5789987 := bstep (se 1 (by rfl) ⟨4342490, by rfl⟩ : syracuseStep 5789987 = 8684981) B8684981
theorem B1833283 : Blo 1715058 1833283 := bstep (se 1 (by rfl) ⟨1374962, by rfl⟩ : syracuseStep 1833283 = 2749925) B2749925
theorem B7829837 : Blo 1715058 7829837 := bstep (se 3 (by rfl) ⟨1468094, by rfl⟩ : syracuseStep 7829837 = 2936189) B2936189
theorem B1931683 : Blo 1715058 1931683 := bstep (se 1 (by rfl) ⟨1448762, by rfl⟩ : syracuseStep 1931683 = 2897525) B2897525
theorem B5790257 : Blo 1715058 5790257 := bstep (se 2 (by rfl) ⟨2171346, by rfl⟩ : syracuseStep 5790257 = 4342693) B4342693
theorem B5495377 : Blo 1715058 5495377 := bstep (se 2 (by rfl) ⟨2060766, by rfl⟩ : syracuseStep 5495377 = 4121533) B4121533
theorem B3259025 : Blo 1715058 3259025 := bstep (se 2 (by rfl) ⟨1222134, by rfl⟩ : syracuseStep 3259025 = 2444269) B2444269
theorem B9272069 : Blo 1715058 9272069 := bstep (se 4 (by rfl) ⟨869256, by rfl⟩ : syracuseStep 9272069 = 1738513) B1738513
theorem B4889393 : Blo 1715058 4889393 := bstep (se 2 (by rfl) ⟨1833522, by rfl⟩ : syracuseStep 4889393 = 3667045) B3667045
theorem B9280325 : Blo 1715058 9280325 := bstep (se 4 (by rfl) ⟨870030, by rfl⟩ : syracuseStep 9280325 = 1740061) B1740061
theorem B43998065 : Blo 1715058 43998065 := bstep (se 2 (by rfl) ⟨16499274, by rfl⟩ : syracuseStep 43998065 = 32998549) B32998549
theorem B1956835 : Blo 1715058 1956835 := bstep (se 1 (by rfl) ⟨1467626, by rfl⟩ : syracuseStep 1956835 = 2935253) B2935253
theorem B4889585 : Blo 1715058 4889585 := bstep (se 2 (by rfl) ⟨1833594, by rfl⟩ : syracuseStep 4889585 = 3667189) B3667189
theorem B5790797 : Blo 1715058 5790797 := bstep (se 3 (by rfl) ⟨1085774, by rfl⟩ : syracuseStep 5790797 = 2171549) B2171549
theorem B9772109 : Blo 1715058 9772109 := bstep (se 3 (by rfl) ⟨1832270, by rfl⟩ : syracuseStep 9772109 = 3664541) B3664541
theorem B5790851 : Blo 1715058 5790851 := bstep (se 1 (by rfl) ⟨4343138, by rfl⟩ : syracuseStep 5790851 = 8686277) B8686277
theorem B5872817 : Blo 1715058 5872817 := bstep (se 2 (by rfl) ⟨2202306, by rfl⟩ : syracuseStep 5872817 = 4404613) B4404613
theorem B23469365 : Blo 1715058 23469365 := bstep (se 5 (by rfl) ⟨1100126, by rfl⟩ : syracuseStep 23469365 = 2200253) B2200253
theorem B5791121 : Blo 1715058 5791121 := bstep (se 2 (by rfl) ⟨2171670, by rfl⟩ : syracuseStep 5791121 = 4343341) B4343341
theorem B6512035 : Blo 1715058 6512035 := bstep (se 1 (by rfl) ⟨4884026, by rfl⟩ : syracuseStep 6512035 = 9768053) B9768053
theorem B5873201 : Blo 1715058 5873201 := bstep (se 2 (by rfl) ⟨2202450, by rfl⟩ : syracuseStep 5873201 = 4404901) B4404901
theorem B4341347 : Blo 1715058 4341347 := bstep (se 1 (by rfl) ⟨3256010, by rfl⟩ : syracuseStep 4341347 = 6512021) B6512021
theorem B8691299 : Blo 1715058 8691299 := bstep (se 1 (by rfl) ⟨6518474, by rfl⟩ : syracuseStep 8691299 = 13036949) B13036949
theorem B10993265 : Blo 1715058 10993265 := bstep (se 2 (by rfl) ⟨4122474, by rfl⟩ : syracuseStep 10993265 = 8244949) B8244949
theorem B27836045 : Blo 1715058 27836045 := bstep (se 3 (by rfl) ⟨5219258, by rfl⟩ : syracuseStep 27836045 = 10438517) B10438517
theorem B9903779 : Blo 1715058 9903779 := bstep (se 1 (by rfl) ⟨7427834, by rfl⟩ : syracuseStep 9903779 = 14855669) B14855669
theorem B4341539 : Blo 1715058 4341539 := bstep (se 1 (by rfl) ⟨3256154, by rfl⟩ : syracuseStep 4341539 = 6512309) B6512309
theorem B2170739 : Blo 1715058 2170739 := bstep (se 1 (by rfl) ⟨1628054, by rfl⟩ : syracuseStep 2170739 = 3256109) B3256109
theorem B5791661 : Blo 1715058 5791661 := bstep (se 3 (by rfl) ⟨1085936, by rfl⟩ : syracuseStep 5791661 = 2171873) B2171873
theorem B5791715 : Blo 1715058 5791715 := bstep (se 1 (by rfl) ⟨4343786, by rfl⟩ : syracuseStep 5791715 = 8687573) B8687573
theorem B14860273 : Blo 1715058 14860273 := bstep (se 2 (by rfl) ⟨5572602, by rfl⟩ : syracuseStep 14860273 = 11145205) B11145205
theorem B13025285 : Blo 1715058 13025285 := bstep (se 4 (by rfl) ⟨1221120, by rfl⟩ : syracuseStep 13025285 = 2442241) B2442241
theorem B2170891 : Blo 1715058 2170891 := bstep (se 1 (by rfl) ⟨1628168, by rfl⟩ : syracuseStep 2170891 = 3256337) B3256337
theorem B13033547 : Blo 1715058 13033547 := bstep (se 1 (by rfl) ⟨9775160, by rfl⟩ : syracuseStep 13033547 = 19550321) B19550321
theorem B6185153 : Blo 1715058 6185153 := bstep (se 2 (by rfl) ⟨2319432, by rfl⟩ : syracuseStep 6185153 = 4638865) B4638865
theorem B2572619 : Blo 1715058 2572619 := bstep (se 1 (by rfl) ⟨1929464, by rfl⟩ : syracuseStep 2572619 = 3858929) B3858929
theorem B2572631 : Blo 1715058 2572631 := bstep (se 1 (by rfl) ⟨1929473, by rfl⟩ : syracuseStep 2572631 = 3858947) B3858947
theorem B5792093 : Blo 1715058 5792093 := bstep (se 3 (by rfl) ⟨1086017, by rfl⟩ : syracuseStep 5792093 = 2172035) B2172035
theorem B7332227 : Blo 1715058 7332227 := bstep (se 1 (by rfl) ⟨5499170, by rfl⟩ : syracuseStep 7332227 = 10998341) B10998341
theorem B2572697 : Blo 1715058 2572697 := bstep (se 2 (by rfl) ⟨964761, by rfl⟩ : syracuseStep 2572697 = 1929523) B1929523
theorem B16499123 : Blo 1715058 16499123 := bstep (se 1 (by rfl) ⟨12374342, by rfl⟩ : syracuseStep 16499123 = 24748685) B24748685
theorem B7832011 : Blo 1715058 7832011 := bstep (se 1 (by rfl) ⟨5874008, by rfl⟩ : syracuseStep 7832011 = 11748017) B11748017
theorem B2572811 : Blo 1715058 2572811 := bstep (se 1 (by rfl) ⟨1929608, by rfl⟩ : syracuseStep 2572811 = 3859217) B3859217
theorem B2572823 : Blo 1715058 2572823 := bstep (se 1 (by rfl) ⟨1929617, by rfl⟩ : syracuseStep 2572823 = 3859235) B3859235
theorem B3859019 : Blo 1715058 3859019 := bstep (se 1 (by rfl) ⟨2894264, by rfl⟩ : syracuseStep 3859019 = 5788529) B5788529
theorem B2572889 : Blo 1715058 2572889 := bstep (se 2 (by rfl) ⟨964833, by rfl⟩ : syracuseStep 2572889 = 1929667) B1929667
theorem B3859073 : Blo 1715058 3859073 := bstep (se 2 (by rfl) ⟨1447152, by rfl⟩ : syracuseStep 3859073 = 2894305) B2894305
theorem B4235927 : Blo 1715058 4235927 := bstep (se 1 (by rfl) ⟨3176945, by rfl⟩ : syracuseStep 4235927 = 6353891) B6353891
theorem B2573003 : Blo 1715058 2573003 := bstep (se 1 (by rfl) ⟨1929752, by rfl⟩ : syracuseStep 2573003 = 3859505) B3859505
theorem B2573015 : Blo 1715058 2573015 := bstep (se 1 (by rfl) ⟨1929761, by rfl⟩ : syracuseStep 2573015 = 3859523) B3859523
theorem B2573081 : Blo 1715058 2573081 := bstep (se 2 (by rfl) ⟨964905, by rfl⟩ : syracuseStep 2573081 = 1929811) B1929811
theorem B8684333 : Blo 1715058 8684333 := bstep (se 3 (by rfl) ⟨1628312, by rfl⟩ : syracuseStep 8684333 = 3256625) B3256625
theorem B3859289 : Blo 1715058 3859289 := bstep (se 2 (by rfl) ⟨1447233, by rfl⟩ : syracuseStep 3859289 = 2894467) B2894467
theorem B7824221 : Blo 1715058 7824221 := bstep (se 3 (by rfl) ⟨1467041, by rfl⟩ : syracuseStep 7824221 = 2934083) B2934083
theorem B13910885 : Blo 1715058 13910885 := bstep (se 4 (by rfl) ⟨1304145, by rfl⟩ : syracuseStep 13910885 = 2608291) B2608291
theorem B2573195 : Blo 1715058 2573195 := bstep (se 1 (by rfl) ⟨1929896, by rfl⟩ : syracuseStep 2573195 = 3859793) B3859793
theorem B2573207 : Blo 1715058 2573207 := bstep (se 1 (by rfl) ⟨1929905, by rfl⟩ : syracuseStep 2573207 = 3859811) B3859811
theorem B3859379 : Blo 1715058 3859379 := bstep (se 1 (by rfl) ⟨2894534, by rfl⟩ : syracuseStep 3859379 = 5789069) B5789069
theorem B3859415 : Blo 1715058 3859415 := bstep (se 1 (by rfl) ⟨2894561, by rfl⟩ : syracuseStep 3859415 = 5789123) B5789123
theorem B2171863 : Blo 1715058 2171863 := bstep (se 1 (by rfl) ⟨1628897, by rfl⟩ : syracuseStep 2171863 = 3257795) B3257795
theorem B15647705 : Blo 1715058 15647705 := bstep (se 2 (by rfl) ⟨5867889, by rfl⟩ : syracuseStep 15647705 = 11735779) B11735779
theorem B2573273 : Blo 1715058 2573273 := bstep (se 2 (by rfl) ⟨964977, by rfl⟩ : syracuseStep 2573273 = 1929955) B1929955
theorem B4342835 : Blo 1715058 4342835 := bstep (se 1 (by rfl) ⟨3257126, by rfl⟩ : syracuseStep 4342835 = 6514253) B6514253
theorem B13911115 : Blo 1715058 13911115 := bstep (se 1 (by rfl) ⟨10433336, by rfl⟩ : syracuseStep 13911115 = 20866673) B20866673
theorem B2573387 : Blo 1715058 2573387 := bstep (se 1 (by rfl) ⟨1930040, by rfl⟩ : syracuseStep 2573387 = 3860081) B3860081
theorem B2573399 : Blo 1715058 2573399 := bstep (se 1 (by rfl) ⟨1930049, by rfl⟩ : syracuseStep 2573399 = 3860099) B3860099
theorem B6186077 : Blo 1715058 6186077 := bstep (se 3 (by rfl) ⟨1159889, by rfl⟩ : syracuseStep 6186077 = 2319779) B2319779
theorem B10183781 : Blo 1715058 10183781 := bstep (se 4 (by rfl) ⟨954729, by rfl⟩ : syracuseStep 10183781 = 1909459) B1909459
theorem B3859595 : Blo 1715058 3859595 := bstep (se 1 (by rfl) ⟨2894696, by rfl⟩ : syracuseStep 3859595 = 5789393) B5789393
theorem B2573465 : Blo 1715058 2573465 := bstep (se 2 (by rfl) ⟨965049, by rfl⟩ : syracuseStep 2573465 = 1930099) B1930099
theorem B3859649 : Blo 1715058 3859649 := bstep (se 2 (by rfl) ⟨1447368, by rfl⟩ : syracuseStep 3859649 = 2894737) B2894737
theorem B8242393 : Blo 1715058 8242393 := bstep (se 2 (by rfl) ⟨3090897, by rfl⟩ : syracuseStep 8242393 = 6181795) B6181795
theorem B2573579 : Blo 1715058 2573579 := bstep (se 1 (by rfl) ⟨1930184, by rfl⟩ : syracuseStep 2573579 = 3860369) B3860369
theorem B2573591 : Blo 1715058 2573591 := bstep (se 1 (by rfl) ⟨1930193, by rfl⟩ : syracuseStep 2573591 = 3860387) B3860387
theorem B6513965 : Blo 1715058 6513965 := bstep (se 3 (by rfl) ⟨1221368, by rfl⟩ : syracuseStep 6513965 = 2442737) B2442737
theorem B3663191 : Blo 1715058 3663191 := bstep (se 1 (by rfl) ⟨2747393, by rfl⟩ : syracuseStep 3663191 = 5494787) B5494787
theorem B2442583 : Blo 1715058 2442583 := bstep (se 1 (by rfl) ⟨1831937, by rfl⟩ : syracuseStep 2442583 = 3663875) B3663875
theorem B2573657 : Blo 1715058 2573657 := bstep (se 2 (by rfl) ⟨965121, by rfl⟩ : syracuseStep 2573657 = 1930243) B1930243
theorem B4343129 : Blo 1715058 4343129 := bstep (se 2 (by rfl) ⟨1628673, by rfl⟩ : syracuseStep 4343129 = 3257347) B3257347
theorem B1787275 : Blo 1715058 1787275 := bstep (se 1 (by rfl) ⟨1340456, by rfl⟩ : syracuseStep 1787275 = 2680913) B2680913
theorem B3859865 : Blo 1715058 3859865 := bstep (se 2 (by rfl) ⟨1447449, by rfl⟩ : syracuseStep 3859865 = 2894899) B2894899
theorem B2573771 : Blo 1715058 2573771 := bstep (se 1 (by rfl) ⟨1930328, by rfl⟩ : syracuseStep 2573771 = 3860657) B3860657
theorem B5793227 : Blo 1715058 5793227 := bstep (se 1 (by rfl) ⟨4344920, by rfl⟩ : syracuseStep 5793227 = 8689841) B8689841
theorem B2573783 : Blo 1715058 2573783 := bstep (se 1 (by rfl) ⟨1930337, by rfl⟩ : syracuseStep 2573783 = 3860675) B3860675
theorem B3859955 : Blo 1715058 3859955 := bstep (se 1 (by rfl) ⟨2894966, by rfl⟩ : syracuseStep 3859955 = 5789933) B5789933
theorem B3859991 : Blo 1715058 3859991 := bstep (se 1 (by rfl) ⟨2894993, by rfl⟩ : syracuseStep 3859991 = 5789987) B5789987
theorem B2573849 : Blo 1715058 2573849 := bstep (se 2 (by rfl) ⟨965193, by rfl⟩ : syracuseStep 2573849 = 1930387) B1930387
theorem B5219891 : Blo 1715058 5219891 := bstep (se 1 (by rfl) ⟨3914918, by rfl⟩ : syracuseStep 5219891 = 7829837) B7829837
theorem B2573963 : Blo 1715058 2573963 := bstep (se 1 (by rfl) ⟨1930472, by rfl⟩ : syracuseStep 2573963 = 3860945) B3860945
theorem B2573975 : Blo 1715058 2573975 := bstep (se 1 (by rfl) ⟨1930481, by rfl⟩ : syracuseStep 2573975 = 3860963) B3860963
theorem B3860171 : Blo 1715058 3860171 := bstep (se 1 (by rfl) ⟨2895128, by rfl⟩ : syracuseStep 3860171 = 5790257) B5790257
theorem B2574041 : Blo 1715058 2574041 := bstep (se 2 (by rfl) ⟨965265, by rfl⟩ : syracuseStep 2574041 = 1930531) B1930531
theorem B5793497 : Blo 1715058 5793497 := bstep (se 2 (by rfl) ⟨2172561, by rfl⟩ : syracuseStep 5793497 = 4345123) B4345123
theorem B3860225 : Blo 1715058 3860225 := bstep (se 2 (by rfl) ⟨1447584, by rfl⟩ : syracuseStep 3860225 = 2895169) B2895169
theorem B2172683 : Blo 1715058 2172683 := bstep (se 1 (by rfl) ⟨1629512, by rfl⟩ : syracuseStep 2172683 = 3259025) B3259025
theorem B8243009 : Blo 1715058 8243009 := bstep (se 2 (by rfl) ⟨3091128, by rfl⟩ : syracuseStep 8243009 = 6182257) B6182257
theorem B2574155 : Blo 1715058 2574155 := bstep (se 1 (by rfl) ⟨1930616, by rfl⟩ : syracuseStep 2574155 = 3861233) B3861233
theorem B2574167 : Blo 1715058 2574167 := bstep (se 1 (by rfl) ⟨1930625, by rfl⟩ : syracuseStep 2574167 = 3861251) B3861251
theorem B6186883 : Blo 1715058 6186883 := bstep (se 1 (by rfl) ⟨4640162, by rfl⟩ : syracuseStep 6186883 = 9280325) B9280325
theorem B2574233 : Blo 1715058 2574233 := bstep (se 2 (by rfl) ⟨965337, by rfl⟩ : syracuseStep 2574233 = 1930675) B1930675
theorem B37095347 : Blo 1715058 37095347 := bstep (se 1 (by rfl) ⟨27821510, by rfl⟩ : syracuseStep 37095347 = 55643021) B55643021
theorem B3860441 : Blo 1715058 3860441 := bstep (se 2 (by rfl) ⟨1447665, by rfl⟩ : syracuseStep 3860441 = 2895331) B2895331
theorem B2574347 : Blo 1715058 2574347 := bstep (se 1 (by rfl) ⟨1930760, by rfl⟩ : syracuseStep 2574347 = 3861521) B3861521
theorem B2574359 : Blo 1715058 2574359 := bstep (se 1 (by rfl) ⟨1930769, by rfl⟩ : syracuseStep 2574359 = 3861539) B3861539
theorem B2443289 : Blo 1715058 2443289 := bstep (se 2 (by rfl) ⟨916233, by rfl⟩ : syracuseStep 2443289 = 1832467) B1832467
theorem B3860531 : Blo 1715058 3860531 := bstep (se 1 (by rfl) ⟨2895398, by rfl⟩ : syracuseStep 3860531 = 5790797) B5790797
theorem B6514739 : Blo 1715058 6514739 := bstep (se 1 (by rfl) ⟨4886054, by rfl⟩ : syracuseStep 6514739 = 9772109) B9772109
theorem B3860567 : Blo 1715058 3860567 := bstep (se 1 (by rfl) ⟨2895425, by rfl⟩ : syracuseStep 3860567 = 5790851) B5790851
theorem B2574425 : Blo 1715058 2574425 := bstep (se 2 (by rfl) ⟨965409, by rfl⟩ : syracuseStep 2574425 = 1930819) B1930819
theorem B2443403 : Blo 1715058 2443403 := bstep (se 1 (by rfl) ⟨1832552, by rfl⟩ : syracuseStep 2443403 = 3665105) B3665105
theorem B2574539 : Blo 1715058 2574539 := bstep (se 1 (by rfl) ⟨1930904, by rfl⟩ : syracuseStep 2574539 = 3861809) B3861809
theorem B2574551 : Blo 1715058 2574551 := bstep (se 1 (by rfl) ⟨1930913, by rfl⟩ : syracuseStep 2574551 = 3861827) B3861827
theorem B3860747 : Blo 1715058 3860747 := bstep (se 1 (by rfl) ⟨2895560, by rfl⟩ : syracuseStep 3860747 = 5791121) B5791121
theorem B2574617 : Blo 1715058 2574617 := bstep (se 2 (by rfl) ⟨965481, by rfl⟩ : syracuseStep 2574617 = 1930963) B1930963
theorem B3860801 : Blo 1715058 3860801 := bstep (se 2 (by rfl) ⟨1447800, by rfl⟩ : syracuseStep 3860801 = 2895601) B2895601
theorem B3664217 : Blo 1715058 3664217 := bstep (se 2 (by rfl) ⟨1374081, by rfl⟩ : syracuseStep 3664217 = 2748163) B2748163
theorem B13027715 : Blo 1715058 13027715 := bstep (se 1 (by rfl) ⟨9770786, by rfl⟩ : syracuseStep 13027715 = 19541573) B19541573
theorem B2574731 : Blo 1715058 2574731 := bstep (se 1 (by rfl) ⟨1931048, by rfl⟩ : syracuseStep 2574731 = 3862097) B3862097
theorem B2894231 : Blo 1715058 2894231 := bstep (se 1 (by rfl) ⟨2170673, by rfl⟩ : syracuseStep 2894231 = 4341347) B4341347
theorem B2574743 : Blo 1715058 2574743 := bstep (se 1 (by rfl) ⟨1931057, by rfl⟩ : syracuseStep 2574743 = 3862115) B3862115
theorem B5794199 : Blo 1715058 5794199 := bstep (se 1 (by rfl) ⟨4345649, by rfl⟩ : syracuseStep 5794199 = 8691299) B8691299
theorem B18557363 : Blo 1715058 18557363 := bstep (se 1 (by rfl) ⟨13918022, by rfl⟩ : syracuseStep 18557363 = 27836045) B27836045
theorem B4639169 : Blo 1715058 4639169 := bstep (se 2 (by rfl) ⟨1739688, by rfl⟩ : syracuseStep 4639169 = 3479377) B3479377
theorem B2574809 : Blo 1715058 2574809 := bstep (se 2 (by rfl) ⟨965553, by rfl⟩ : syracuseStep 2574809 = 1931107) B1931107
theorem B2476555 : Blo 1715058 2476555 := bstep (se 1 (by rfl) ⟨1857416, by rfl⟩ : syracuseStep 2476555 = 3714833) B3714833
theorem B12372497 : Blo 1715058 12372497 := bstep (se 2 (by rfl) ⟨4639686, by rfl⟩ : syracuseStep 12372497 = 9279373) B9279373
theorem B2894359 : Blo 1715058 2894359 := bstep (se 1 (by rfl) ⟨2170769, by rfl⟩ : syracuseStep 2894359 = 4341539) B4341539
theorem B3861017 : Blo 1715058 3861017 := bstep (se 2 (by rfl) ⟨1447881, by rfl⟩ : syracuseStep 3861017 = 2895763) B2895763
theorem B2574923 : Blo 1715058 2574923 := bstep (se 1 (by rfl) ⟨1931192, by rfl⟩ : syracuseStep 2574923 = 3862385) B3862385
theorem B2574935 : Blo 1715058 2574935 := bstep (se 1 (by rfl) ⟨1931201, by rfl⟩ : syracuseStep 2574935 = 3862403) B3862403
theorem B3861107 : Blo 1715058 3861107 := bstep (se 1 (by rfl) ⟨2895830, by rfl⟩ : syracuseStep 3861107 = 5791661) B5791661
theorem B3861143 : Blo 1715058 3861143 := bstep (se 1 (by rfl) ⟨2895857, by rfl⟩ : syracuseStep 3861143 = 5791715) B5791715
theorem B2443927 : Blo 1715058 2443927 := bstep (se 1 (by rfl) ⟨1832945, by rfl⟩ : syracuseStep 2443927 = 3665891) B3665891
theorem B2575001 : Blo 1715058 2575001 := bstep (se 2 (by rfl) ⟨965625, by rfl⟩ : syracuseStep 2575001 = 1931251) B1931251
theorem B2575115 : Blo 1715058 2575115 := bstep (se 1 (by rfl) ⟨1931336, by rfl⟩ : syracuseStep 2575115 = 3862673) B3862673
theorem B3091223 : Blo 1715058 3091223 := bstep (se 1 (by rfl) ⟨2318417, by rfl⟩ : syracuseStep 3091223 = 4636835) B4636835
theorem B2476823 : Blo 1715058 2476823 := bstep (se 1 (by rfl) ⟨1857617, by rfl⟩ : syracuseStep 2476823 = 3715235) B3715235
theorem B2575127 : Blo 1715058 2575127 := bstep (se 1 (by rfl) ⟨1931345, by rfl⟩ : syracuseStep 2575127 = 3862691) B3862691
theorem B4401985 : Blo 1715058 4401985 := bstep (se 2 (by rfl) ⟨1650744, by rfl⟩ : syracuseStep 4401985 = 3301489) B3301489
theorem B3861323 : Blo 1715058 3861323 := bstep (se 1 (by rfl) ⟨2895992, by rfl⟩ : syracuseStep 3861323 = 5791985) B5791985
theorem B2575193 : Blo 1715058 2575193 := bstep (se 2 (by rfl) ⟨965697, by rfl⟩ : syracuseStep 2575193 = 1931395) B1931395
theorem B1715063 : Blo 1715058 1715063 := bstep (se 1 (by rfl) ⟨1286297, by rfl⟩ : syracuseStep 1715063 = 2572595) B2572595
theorem B3861377 : Blo 1715058 3861377 := bstep (se 2 (by rfl) ⟨1448016, by rfl⟩ : syracuseStep 3861377 = 2896033) B2896033
theorem B1715083 : Blo 1715058 1715083 := bstep (se 1 (by rfl) ⟨1286312, by rfl⟩ : syracuseStep 1715083 = 2572625) B2572625
theorem B2935691 : Blo 1715058 2935691 := bstep (se 1 (by rfl) ⟨2201768, by rfl⟩ : syracuseStep 2935691 = 4403537) B4403537
theorem B1715095 : Blo 1715058 1715095 := bstep (se 1 (by rfl) ⟨1286321, by rfl⟩ : syracuseStep 1715095 = 2572643) B2572643
theorem B1715115 : Blo 1715058 1715115 := bstep (se 1 (by rfl) ⟨1286336, by rfl⟩ : syracuseStep 1715115 = 2572673) B2572673
theorem B9776051 : Blo 1715058 9776051 := bstep (se 1 (by rfl) ⟨7332038, by rfl⟩ : syracuseStep 9776051 = 14664077) B14664077
theorem B1715127 : Blo 1715058 1715127 := bstep (se 1 (by rfl) ⟨1286345, by rfl⟩ : syracuseStep 1715127 = 2572691) B2572691
theorem B5794739 : Blo 1715058 5794739 := bstep (se 1 (by rfl) ⟨4346054, by rfl⟩ : syracuseStep 5794739 = 8692109) B8692109
theorem B1715147 : Blo 1715058 1715147 := bstep (se 1 (by rfl) ⟨1286360, by rfl⟩ : syracuseStep 1715147 = 2572721) B2572721
theorem B4344779 : Blo 1715058 4344779 := bstep (se 1 (by rfl) ⟨3258584, by rfl⟩ : syracuseStep 4344779 = 6517169) B6517169
theorem B2575307 : Blo 1715058 2575307 := bstep (se 1 (by rfl) ⟨1931480, by rfl⟩ : syracuseStep 2575307 = 3862961) B3862961
theorem B1715159 : Blo 1715058 1715159 := bstep (se 1 (by rfl) ⟨1286369, by rfl⟩ : syracuseStep 1715159 = 2572739) B2572739
theorem B2575319 : Blo 1715058 2575319 := bstep (se 1 (by rfl) ⟨1931489, by rfl⟩ : syracuseStep 2575319 = 3862979) B3862979
theorem B1715179 : Blo 1715058 1715179 := bstep (se 1 (by rfl) ⟨1286384, by rfl⟩ : syracuseStep 1715179 = 2572769) B2572769
theorem B1715191 : Blo 1715058 1715191 := bstep (se 1 (by rfl) ⟨1286393, by rfl⟩ : syracuseStep 1715191 = 2572787) B2572787
theorem B1715211 : Blo 1715058 1715211 := bstep (se 1 (by rfl) ⟨1286408, by rfl⟩ : syracuseStep 1715211 = 2572817) B2572817
theorem B1715223 : Blo 1715058 1715223 := bstep (se 1 (by rfl) ⟨1286417, by rfl⟩ : syracuseStep 1715223 = 2572835) B2572835
theorem B2575385 : Blo 1715058 2575385 := bstep (se 2 (by rfl) ⟨965769, by rfl⟩ : syracuseStep 2575385 = 1931539) B1931539
theorem B1715243 : Blo 1715058 1715243 := bstep (se 1 (by rfl) ⟨1286432, by rfl⟩ : syracuseStep 1715243 = 2572865) B2572865
theorem B1715255 : Blo 1715058 1715255 := bstep (se 1 (by rfl) ⟨1286441, by rfl⟩ : syracuseStep 1715255 = 2572883) B2572883
theorem B1715275 : Blo 1715058 1715275 := bstep (se 1 (by rfl) ⟨1286456, by rfl⟩ : syracuseStep 1715275 = 2572913) B2572913
theorem B1715287 : Blo 1715058 1715287 := bstep (se 1 (by rfl) ⟨1286465, by rfl⟩ : syracuseStep 1715287 = 2572931) B2572931
theorem B6958169 : Blo 1715058 6958169 := bstep (se 2 (by rfl) ⟨2609313, by rfl⟩ : syracuseStep 6958169 = 5218627) B5218627
theorem B3861593 : Blo 1715058 3861593 := bstep (se 2 (by rfl) ⟨1448097, by rfl⟩ : syracuseStep 3861593 = 2896195) B2896195
theorem B6270041 : Blo 1715058 6270041 := bstep (se 2 (by rfl) ⟨2351265, by rfl⟩ : syracuseStep 6270041 = 4702531) B4702531
theorem B10996829 : Blo 1715058 10996829 := bstep (se 3 (by rfl) ⟨2061905, by rfl⟩ : syracuseStep 10996829 = 4123811) B4123811
theorem B1715307 : Blo 1715058 1715307 := bstep (se 1 (by rfl) ⟨1286480, by rfl⟩ : syracuseStep 1715307 = 2572961) B2572961
theorem B1715319 : Blo 1715058 1715319 := bstep (se 1 (by rfl) ⟨1286489, by rfl⟩ : syracuseStep 1715319 = 2572979) B2572979
theorem B1715339 : Blo 1715058 1715339 := bstep (se 1 (by rfl) ⟨1286504, by rfl⟩ : syracuseStep 1715339 = 2573009) B2573009
theorem B2894987 : Blo 1715058 2894987 := bstep (se 1 (by rfl) ⟨2171240, by rfl⟩ : syracuseStep 2894987 = 4342481) B4342481
theorem B2575499 : Blo 1715058 2575499 := bstep (se 1 (by rfl) ⟨1931624, by rfl⟩ : syracuseStep 2575499 = 3863249) B3863249
theorem B1715351 : Blo 1715058 1715351 := bstep (se 1 (by rfl) ⟨1286513, by rfl⟩ : syracuseStep 1715351 = 2573027) B2573027
theorem B5500055 : Blo 1715058 5500055 := bstep (se 1 (by rfl) ⟨4125041, by rfl⟩ : syracuseStep 5500055 = 8250083) B8250083
theorem B2575511 : Blo 1715058 2575511 := bstep (se 1 (by rfl) ⟨1931633, by rfl⟩ : syracuseStep 2575511 = 3863267) B3863267
theorem B1715371 : Blo 1715058 1715371 := bstep (se 1 (by rfl) ⟨1286528, by rfl⟩ : syracuseStep 1715371 = 2573057) B2573057
theorem B3861683 : Blo 1715058 3861683 := bstep (se 1 (by rfl) ⟨2896262, by rfl⟩ : syracuseStep 3861683 = 5792525) B5792525
theorem B1715383 : Blo 1715058 1715383 := bstep (se 1 (by rfl) ⟨1286537, by rfl⟩ : syracuseStep 1715383 = 2573075) B2573075
theorem B5795009 : Blo 1715058 5795009 := bstep (se 2 (by rfl) ⟨2173128, by rfl⟩ : syracuseStep 5795009 = 4346257) B4346257
theorem B1715403 : Blo 1715058 1715403 := bstep (se 1 (by rfl) ⟨1286552, by rfl⟩ : syracuseStep 1715403 = 2573105) B2573105
theorem B7056587 : Blo 1715058 7056587 := bstep (se 1 (by rfl) ⟨5292440, by rfl⟩ : syracuseStep 7056587 = 10584881) B10584881
theorem B1715415 : Blo 1715058 1715415 := bstep (se 1 (by rfl) ⟨1286561, by rfl⟩ : syracuseStep 1715415 = 2573123) B2573123
theorem B3861719 : Blo 1715058 3861719 := bstep (se 1 (by rfl) ⟨2896289, by rfl⟩ : syracuseStep 3861719 = 5792579) B5792579
theorem B2575577 : Blo 1715058 2575577 := bstep (se 2 (by rfl) ⟨965841, by rfl⟩ : syracuseStep 2575577 = 1931683) B1931683
theorem B1715435 : Blo 1715058 1715435 := bstep (se 1 (by rfl) ⟨1286576, by rfl⟩ : syracuseStep 1715435 = 2573153) B2573153
theorem B28601585 : Blo 1715058 28601585 := bstep (se 2 (by rfl) ⟨10725594, by rfl⟩ : syracuseStep 28601585 = 21451189) B21451189
theorem B1715447 : Blo 1715058 1715447 := bstep (se 1 (by rfl) ⟨1286585, by rfl⟩ : syracuseStep 1715447 = 2573171) B2573171
theorem B1715467 : Blo 1715058 1715467 := bstep (se 1 (by rfl) ⟨1286600, by rfl⟩ : syracuseStep 1715467 = 2573201) B2573201
theorem B2895115 : Blo 1715058 2895115 := bstep (se 1 (by rfl) ⟨2171336, by rfl⟩ : syracuseStep 2895115 = 4342673) B4342673
theorem B1715479 : Blo 1715058 1715479 := bstep (se 1 (by rfl) ⟨1286609, by rfl⟩ : syracuseStep 1715479 = 2573219) B2573219
theorem B1715499 : Blo 1715058 1715499 := bstep (se 1 (by rfl) ⟨1286624, by rfl⟩ : syracuseStep 1715499 = 2573249) B2573249
theorem B1715511 : Blo 1715058 1715511 := bstep (se 1 (by rfl) ⟨1286633, by rfl⟩ : syracuseStep 1715511 = 2573267) B2573267
theorem B5868875 : Blo 1715058 5868875 := bstep (se 1 (by rfl) ⟨4401656, by rfl⟩ : syracuseStep 5868875 = 8803313) B8803313
theorem B1715531 : Blo 1715058 1715531 := bstep (se 1 (by rfl) ⟨1286648, by rfl⟩ : syracuseStep 1715531 = 2573297) B2573297
theorem B1715543 : Blo 1715058 1715543 := bstep (se 1 (by rfl) ⟨1286657, by rfl⟩ : syracuseStep 1715543 = 2573315) B2573315
theorem B4885849 : Blo 1715058 4885849 := bstep (se 2 (by rfl) ⟨1832193, by rfl⟩ : syracuseStep 4885849 = 3664387) B3664387
theorem B27823459 : Blo 1715058 27823459 := bstep (se 1 (by rfl) ⟨20867594, by rfl⟩ : syracuseStep 27823459 = 41735189) B41735189
theorem B1715563 : Blo 1715058 1715563 := bstep (se 1 (by rfl) ⟨1286672, by rfl⟩ : syracuseStep 1715563 = 2573345) B2573345
theorem B52833653 : Blo 1715058 52833653 := bstep (se 5 (by rfl) ⟨2476577, by rfl⟩ : syracuseStep 52833653 = 4953155) B4953155
theorem B1715575 : Blo 1715058 1715575 := bstep (se 1 (by rfl) ⟨1286681, by rfl⟩ : syracuseStep 1715575 = 2573363) B2573363
theorem B1715595 : Blo 1715058 1715595 := bstep (se 1 (by rfl) ⟨1286696, by rfl⟩ : syracuseStep 1715595 = 2573393) B2573393
theorem B3861899 : Blo 1715058 3861899 := bstep (se 1 (by rfl) ⟨2896424, by rfl⟩ : syracuseStep 3861899 = 5792849) B5792849
theorem B12365207 : Blo 1715058 12365207 := bstep (se 1 (by rfl) ⟨9273905, by rfl⟩ : syracuseStep 12365207 = 18547811) B18547811
theorem B1715607 : Blo 1715058 1715607 := bstep (se 1 (by rfl) ⟨1286705, by rfl⟩ : syracuseStep 1715607 = 2573411) B2573411
theorem B2895257 : Blo 1715058 2895257 := bstep (se 2 (by rfl) ⟨1085721, by rfl⟩ : syracuseStep 2895257 = 2171443) B2171443
theorem B1715627 : Blo 1715058 1715627 := bstep (se 1 (by rfl) ⟨1286720, by rfl⟩ : syracuseStep 1715627 = 2573441) B2573441
theorem B1715639 : Blo 1715058 1715639 := bstep (se 1 (by rfl) ⟨1286729, by rfl⟩ : syracuseStep 1715639 = 2573459) B2573459
theorem B7327169 : Blo 1715058 7327169 := bstep (se 2 (by rfl) ⟨2747688, by rfl⟩ : syracuseStep 7327169 = 5495377) B5495377
theorem B3861953 : Blo 1715058 3861953 := bstep (se 2 (by rfl) ⟨1448232, by rfl⟩ : syracuseStep 3861953 = 2896465) B2896465
theorem B1715659 : Blo 1715058 1715659 := bstep (se 1 (by rfl) ⟨1286744, by rfl⟩ : syracuseStep 1715659 = 2573489) B2573489
theorem B2444747 : Blo 1715058 2444747 := bstep (se 1 (by rfl) ⟨1833560, by rfl⟩ : syracuseStep 2444747 = 3667121) B3667121
theorem B1715671 : Blo 1715058 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B1715691 : Blo 1715058 1715691 := bstep (se 1 (by rfl) ⟨1286768, by rfl⟩ : syracuseStep 1715691 = 2573537) B2573537
theorem B1715703 : Blo 1715058 1715703 := bstep (se 1 (by rfl) ⟨1286777, by rfl⟩ : syracuseStep 1715703 = 2573555) B2573555
theorem B6516227 : Blo 1715058 6516227 := bstep (se 1 (by rfl) ⟨4887170, by rfl⟩ : syracuseStep 6516227 = 9774341) B9774341
theorem B1715723 : Blo 1715058 1715723 := bstep (se 1 (by rfl) ⟨1286792, by rfl⟩ : syracuseStep 1715723 = 2573585) B2573585
theorem B1715735 : Blo 1715058 1715735 := bstep (se 1 (by rfl) ⟨1286801, by rfl⟩ : syracuseStep 1715735 = 2573603) B2573603
theorem B2895385 : Blo 1715058 2895385 := bstep (se 2 (by rfl) ⟨1085769, by rfl⟩ : syracuseStep 2895385 = 2171539) B2171539
theorem B1715755 : Blo 1715058 1715755 := bstep (se 1 (by rfl) ⟨1286816, by rfl⟩ : syracuseStep 1715755 = 2573633) B2573633
theorem B1715767 : Blo 1715058 1715767 := bstep (se 1 (by rfl) ⟨1286825, by rfl⟩ : syracuseStep 1715767 = 2573651) B2573651
theorem B1715787 : Blo 1715058 1715787 := bstep (se 1 (by rfl) ⟨1286840, by rfl⟩ : syracuseStep 1715787 = 2573681) B2573681
theorem B1715799 : Blo 1715058 1715799 := bstep (se 1 (by rfl) ⟨1286849, by rfl⟩ : syracuseStep 1715799 = 2573699) B2573699
theorem B1715819 : Blo 1715058 1715819 := bstep (se 1 (by rfl) ⟨1286864, by rfl⟩ : syracuseStep 1715819 = 2573729) B2573729
theorem B1715831 : Blo 1715058 1715831 := bstep (se 1 (by rfl) ⟨1286873, by rfl⟩ : syracuseStep 1715831 = 2573747) B2573747
theorem B1715851 : Blo 1715058 1715851 := bstep (se 1 (by rfl) ⟨1286888, by rfl⟩ : syracuseStep 1715851 = 2573777) B2573777
theorem B1715863 : Blo 1715058 1715863 := bstep (se 1 (by rfl) ⟨1286897, by rfl⟩ : syracuseStep 1715863 = 2573795) B2573795
theorem B3763865 : Blo 1715058 3763865 := bstep (se 2 (by rfl) ⟨1411449, by rfl⟩ : syracuseStep 3763865 = 2822899) B2822899
theorem B3862169 : Blo 1715058 3862169 := bstep (se 2 (by rfl) ⟨1448313, by rfl⟩ : syracuseStep 3862169 = 2896627) B2896627
theorem B1715883 : Blo 1715058 1715883 := bstep (se 1 (by rfl) ⟨1286912, by rfl⟩ : syracuseStep 1715883 = 2573825) B2573825
theorem B1715895 : Blo 1715058 1715895 := bstep (se 1 (by rfl) ⟨1286921, by rfl⟩ : syracuseStep 1715895 = 2573843) B2573843
theorem B1715915 : Blo 1715058 1715915 := bstep (se 1 (by rfl) ⟨1286936, by rfl⟩ : syracuseStep 1715915 = 2573873) B2573873
theorem B1715927 : Blo 1715058 1715927 := bstep (se 1 (by rfl) ⟨1286945, by rfl⟩ : syracuseStep 1715927 = 2573891) B2573891
theorem B4886237 : Blo 1715058 4886237 := bstep (se 3 (by rfl) ⟨916169, by rfl⟩ : syracuseStep 4886237 = 1832339) B1832339
theorem B1715947 : Blo 1715058 1715947 := bstep (se 1 (by rfl) ⟨1286960, by rfl⟩ : syracuseStep 1715947 = 2573921) B2573921
theorem B3862259 : Blo 1715058 3862259 := bstep (se 1 (by rfl) ⟨2896694, by rfl⟩ : syracuseStep 3862259 = 5793389) B5793389
theorem B1715959 : Blo 1715058 1715959 := bstep (se 1 (by rfl) ⟨1286969, by rfl⟩ : syracuseStep 1715959 = 2573939) B2573939
theorem B1715979 : Blo 1715058 1715979 := bstep (se 1 (by rfl) ⟨1286984, by rfl⟩ : syracuseStep 1715979 = 2573969) B2573969
theorem B2608919 : Blo 1715058 2608919 := bstep (se 1 (by rfl) ⟨1956689, by rfl⟩ : syracuseStep 2608919 = 3913379) B3913379
theorem B1715991 : Blo 1715058 1715991 := bstep (se 1 (by rfl) ⟨1286993, by rfl⟩ : syracuseStep 1715991 = 2573987) B2573987
theorem B3862295 : Blo 1715058 3862295 := bstep (se 1 (by rfl) ⟨2896721, by rfl⟩ : syracuseStep 3862295 = 5793443) B5793443
theorem B1716011 : Blo 1715058 1716011 := bstep (se 1 (by rfl) ⟨1287008, by rfl⟩ : syracuseStep 1716011 = 2574017) B2574017
theorem B1716023 : Blo 1715058 1716023 := bstep (se 1 (by rfl) ⟨1287017, by rfl⟩ : syracuseStep 1716023 = 2574035) B2574035
theorem B3256139 : Blo 1715058 3256139 := bstep (se 1 (by rfl) ⟨2442104, by rfl⟩ : syracuseStep 3256139 = 4884209) B4884209
theorem B1716043 : Blo 1715058 1716043 := bstep (se 1 (by rfl) ⟨1287032, by rfl⟩ : syracuseStep 1716043 = 2574065) B2574065
theorem B1716055 : Blo 1715058 1716055 := bstep (se 1 (by rfl) ⟨1287041, by rfl⟩ : syracuseStep 1716055 = 2574083) B2574083
theorem B1716075 : Blo 1715058 1716075 := bstep (se 1 (by rfl) ⟨1287056, by rfl⟩ : syracuseStep 1716075 = 2574113) B2574113
theorem B1716087 : Blo 1715058 1716087 := bstep (se 1 (by rfl) ⟨1287065, by rfl⟩ : syracuseStep 1716087 = 2574131) B2574131
theorem B3256193 : Blo 1715058 3256193 := bstep (se 2 (by rfl) ⟨1221072, by rfl⟩ : syracuseStep 3256193 = 2442145) B2442145
theorem B1716107 : Blo 1715058 1716107 := bstep (se 1 (by rfl) ⟨1287080, by rfl⟩ : syracuseStep 1716107 = 2574161) B2574161
theorem B1716119 : Blo 1715058 1716119 := bstep (se 1 (by rfl) ⟨1287089, by rfl⟩ : syracuseStep 1716119 = 2574179) B2574179
theorem B4345751 : Blo 1715058 4345751 := bstep (se 1 (by rfl) ⟨3259313, by rfl⟩ : syracuseStep 4345751 = 6518627) B6518627
theorem B1716139 : Blo 1715058 1716139 := bstep (se 1 (by rfl) ⟨1287104, by rfl⟩ : syracuseStep 1716139 = 2574209) B2574209
theorem B1716151 : Blo 1715058 1716151 := bstep (se 1 (by rfl) ⟨1287113, by rfl⟩ : syracuseStep 1716151 = 2574227) B2574227
theorem B3665857 : Blo 1715058 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B1716171 : Blo 1715058 1716171 := bstep (se 1 (by rfl) ⟨1287128, by rfl⟩ : syracuseStep 1716171 = 2574257) B2574257
theorem B6516683 : Blo 1715058 6516683 := bstep (se 1 (by rfl) ⟨4887512, by rfl⟩ : syracuseStep 6516683 = 9775025) B9775025
theorem B3862475 : Blo 1715058 3862475 := bstep (se 1 (by rfl) ⟨2896856, by rfl⟩ : syracuseStep 3862475 = 5793713) B5793713
theorem B1716183 : Blo 1715058 1716183 := bstep (se 1 (by rfl) ⟨1287137, by rfl⟩ : syracuseStep 1716183 = 2574275) B2574275
theorem B2936791 : Blo 1715058 2936791 := bstep (se 1 (by rfl) ⟨2202593, by rfl⟩ : syracuseStep 2936791 = 4405187) B4405187
theorem B2609113 : Blo 1715058 2609113 := bstep (se 2 (by rfl) ⟨978417, by rfl⟩ : syracuseStep 2609113 = 1956835) B1956835
theorem B1716203 : Blo 1715058 1716203 := bstep (se 1 (by rfl) ⟨1287152, by rfl⟩ : syracuseStep 1716203 = 2574305) B2574305
theorem B1716215 : Blo 1715058 1716215 := bstep (se 1 (by rfl) ⟨1287161, by rfl⟩ : syracuseStep 1716215 = 2574323) B2574323
theorem B3862529 : Blo 1715058 3862529 := bstep (se 2 (by rfl) ⟨1448448, by rfl⟩ : syracuseStep 3862529 = 2896897) B2896897
theorem B1716235 : Blo 1715058 1716235 := bstep (se 1 (by rfl) ⟨1287176, by rfl⟩ : syracuseStep 1716235 = 2574353) B2574353
theorem B3477527 : Blo 1715058 3477527 := bstep (se 1 (by rfl) ⟨2608145, by rfl⟩ : syracuseStep 3477527 = 5216291) B5216291
theorem B1716247 : Blo 1715058 1716247 := bstep (se 1 (by rfl) ⟨1287185, by rfl⟩ : syracuseStep 1716247 = 2574371) B2574371
theorem B1716267 : Blo 1715058 1716267 := bstep (se 1 (by rfl) ⟨1287200, by rfl⟩ : syracuseStep 1716267 = 2574401) B2574401
theorem B1716279 : Blo 1715058 1716279 := bstep (se 1 (by rfl) ⟨1287209, by rfl⟩ : syracuseStep 1716279 = 2574419) B2574419
theorem B1716299 : Blo 1715058 1716299 := bstep (se 1 (by rfl) ⟨1287224, by rfl⟩ : syracuseStep 1716299 = 2574449) B2574449
theorem B2895959 : Blo 1715058 2895959 := bstep (se 1 (by rfl) ⟨2171969, by rfl⟩ : syracuseStep 2895959 = 4343939) B4343939
theorem B1716311 : Blo 1715058 1716311 := bstep (se 1 (by rfl) ⟨1287233, by rfl⟩ : syracuseStep 1716311 = 2574467) B2574467
theorem B3477593 : Blo 1715058 3477593 := bstep (se 2 (by rfl) ⟨1304097, by rfl⟩ : syracuseStep 3477593 = 2608195) B2608195
theorem B1716331 : Blo 1715058 1716331 := bstep (se 1 (by rfl) ⟨1287248, by rfl⟩ : syracuseStep 1716331 = 2574497) B2574497
theorem B1716343 : Blo 1715058 1716343 := bstep (se 1 (by rfl) ⟨1287257, by rfl⟩ : syracuseStep 1716343 = 2574515) B2574515
theorem B1716363 : Blo 1715058 1716363 := bstep (se 1 (by rfl) ⟨1287272, by rfl⟩ : syracuseStep 1716363 = 2574545) B2574545
theorem B6516881 : Blo 1715058 6516881 := bstep (se 2 (by rfl) ⟨2443830, by rfl⟩ : syracuseStep 6516881 = 4887661) B4887661
theorem B1716375 : Blo 1715058 1716375 := bstep (se 1 (by rfl) ⟨1287281, by rfl⟩ : syracuseStep 1716375 = 2574563) B2574563
theorem B1716395 : Blo 1715058 1716395 := bstep (se 1 (by rfl) ⟨1287296, by rfl⟩ : syracuseStep 1716395 = 2574593) B2574593
theorem B1716407 : Blo 1715058 1716407 := bstep (se 1 (by rfl) ⟨1287305, by rfl⟩ : syracuseStep 1716407 = 2574611) B2574611
theorem B1716427 : Blo 1715058 1716427 := bstep (se 1 (by rfl) ⟨1287320, by rfl⟩ : syracuseStep 1716427 = 2574641) B2574641
theorem B2896087 : Blo 1715058 2896087 := bstep (se 1 (by rfl) ⟨2172065, by rfl⟩ : syracuseStep 2896087 = 4344131) B4344131
theorem B1716439 : Blo 1715058 1716439 := bstep (se 1 (by rfl) ⟨1287329, by rfl⟩ : syracuseStep 1716439 = 2574659) B2574659
theorem B3862745 : Blo 1715058 3862745 := bstep (se 2 (by rfl) ⟨1448529, by rfl⟩ : syracuseStep 3862745 = 2897059) B2897059
theorem B1929451 : Blo 1715058 1929451 := bstep (se 1 (by rfl) ⟨1447088, by rfl⟩ : syracuseStep 1929451 = 2894177) B2894177
theorem B1716459 : Blo 1715058 1716459 := bstep (se 1 (by rfl) ⟨1287344, by rfl⟩ : syracuseStep 1716459 = 2574689) B2574689
theorem B1716471 : Blo 1715058 1716471 := bstep (se 1 (by rfl) ⟨1287353, by rfl⟩ : syracuseStep 1716471 = 2574707) B2574707
theorem B1716491 : Blo 1715058 1716491 := bstep (se 1 (by rfl) ⟨1287368, by rfl⟩ : syracuseStep 1716491 = 2574737) B2574737
theorem B1716503 : Blo 1715058 1716503 := bstep (se 1 (by rfl) ⟨1287377, by rfl⟩ : syracuseStep 1716503 = 2574755) B2574755
theorem B1716523 : Blo 1715058 1716523 := bstep (se 1 (by rfl) ⟨1287392, by rfl⟩ : syracuseStep 1716523 = 2574785) B2574785
theorem B3862835 : Blo 1715058 3862835 := bstep (se 1 (by rfl) ⟨2897126, by rfl⟩ : syracuseStep 3862835 = 5794253) B5794253
theorem B1716535 : Blo 1715058 1716535 := bstep (se 1 (by rfl) ⟨1287401, by rfl⟩ : syracuseStep 1716535 = 2574803) B2574803
theorem B1716555 : Blo 1715058 1716555 := bstep (se 1 (by rfl) ⟨1287416, by rfl⟩ : syracuseStep 1716555 = 2574833) B2574833
theorem B1929559 : Blo 1715058 1929559 := bstep (se 1 (by rfl) ⟨1447169, by rfl⟩ : syracuseStep 1929559 = 2894339) B2894339
theorem B1716567 : Blo 1715058 1716567 := bstep (se 1 (by rfl) ⟨1287425, by rfl⟩ : syracuseStep 1716567 = 2574851) B2574851
theorem B3862871 : Blo 1715058 3862871 := bstep (se 1 (by rfl) ⟨2897153, by rfl⟩ : syracuseStep 3862871 = 5794307) B5794307
theorem B9777509 : Blo 1715058 9777509 := bstep (se 4 (by rfl) ⟨916641, by rfl⟩ : syracuseStep 9777509 = 1833283) B1833283
theorem B1716587 : Blo 1715058 1716587 := bstep (se 1 (by rfl) ⟨1287440, by rfl⟩ : syracuseStep 1716587 = 2574881) B2574881
theorem B1716599 : Blo 1715058 1716599 := bstep (se 1 (by rfl) ⟨1287449, by rfl⟩ : syracuseStep 1716599 = 2574899) B2574899
theorem B3912065 : Blo 1715058 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B1716619 : Blo 1715058 1716619 := bstep (se 1 (by rfl) ⟨1287464, by rfl⟩ : syracuseStep 1716619 = 2574929) B2574929
theorem B1716631 : Blo 1715058 1716631 := bstep (se 1 (by rfl) ⟨1287473, by rfl⟩ : syracuseStep 1716631 = 2574947) B2574947
theorem B1716651 : Blo 1715058 1716651 := bstep (se 1 (by rfl) ⟨1287488, by rfl⟩ : syracuseStep 1716651 = 2574977) B2574977
theorem B1716663 : Blo 1715058 1716663 := bstep (se 1 (by rfl) ⟨1287497, by rfl⟩ : syracuseStep 1716663 = 2574995) B2574995
theorem B1716683 : Blo 1715058 1716683 := bstep (se 1 (by rfl) ⟨1287512, by rfl⟩ : syracuseStep 1716683 = 2575025) B2575025
theorem B1716695 : Blo 1715058 1716695 := bstep (se 1 (by rfl) ⟨1287521, by rfl⟩ : syracuseStep 1716695 = 2575043) B2575043
theorem B1716715 : Blo 1715058 1716715 := bstep (se 1 (by rfl) ⟨1287536, by rfl⟩ : syracuseStep 1716715 = 2575073) B2575073
theorem B1716727 : Blo 1715058 1716727 := bstep (se 1 (by rfl) ⟨1287545, by rfl⟩ : syracuseStep 1716727 = 2575091) B2575091
theorem B6181379 : Blo 1715058 6181379 := bstep (se 1 (by rfl) ⟨4636034, by rfl⟩ : syracuseStep 6181379 = 9272069) B9272069
theorem B1929739 : Blo 1715058 1929739 := bstep (se 1 (by rfl) ⟨1447304, by rfl⟩ : syracuseStep 1929739 = 2894609) B2894609
theorem B1716747 : Blo 1715058 1716747 := bstep (se 1 (by rfl) ⟨1287560, by rfl⟩ : syracuseStep 1716747 = 2575121) B2575121
theorem B3863051 : Blo 1715058 3863051 := bstep (se 1 (by rfl) ⟨2897288, by rfl⟩ : syracuseStep 3863051 = 5794577) B5794577
theorem B3666455 : Blo 1715058 3666455 := bstep (se 1 (by rfl) ⟨2749841, by rfl⟩ : syracuseStep 3666455 = 5499683) B5499683
theorem B1716759 : Blo 1715058 1716759 := bstep (se 1 (by rfl) ⟨1287569, by rfl⟩ : syracuseStep 1716759 = 2575139) B2575139
theorem B1716779 : Blo 1715058 1716779 := bstep (se 1 (by rfl) ⟨1287584, by rfl⟩ : syracuseStep 1716779 = 2575169) B2575169
theorem B1716791 : Blo 1715058 1716791 := bstep (se 1 (by rfl) ⟨1287593, by rfl⟩ : syracuseStep 1716791 = 2575187) B2575187
theorem B3863105 : Blo 1715058 3863105 := bstep (se 2 (by rfl) ⟨1448664, by rfl⟩ : syracuseStep 3863105 = 2897329) B2897329
theorem B29332043 : Blo 1715058 29332043 := bstep (se 1 (by rfl) ⟨21999032, by rfl⟩ : syracuseStep 29332043 = 43998065) B43998065
theorem B1716811 : Blo 1715058 1716811 := bstep (se 1 (by rfl) ⟨1287608, by rfl⟩ : syracuseStep 1716811 = 2575217) B2575217
theorem B1716823 : Blo 1715058 1716823 := bstep (se 1 (by rfl) ⟨1287617, by rfl⟩ : syracuseStep 1716823 = 2575235) B2575235
theorem B8688221 : Blo 1715058 8688221 := bstep (se 3 (by rfl) ⟨1629041, by rfl⟩ : syracuseStep 8688221 = 3258083) B3258083
theorem B1716843 : Blo 1715058 1716843 := bstep (se 1 (by rfl) ⟨1287632, by rfl⟩ : syracuseStep 1716843 = 2575265) B2575265
theorem B1929847 : Blo 1715058 1929847 := bstep (se 1 (by rfl) ⟨1447385, by rfl⟩ : syracuseStep 1929847 = 2894771) B2894771
theorem B1716855 : Blo 1715058 1716855 := bstep (se 1 (by rfl) ⟨1287641, by rfl⟩ : syracuseStep 1716855 = 2575283) B2575283
theorem B1716875 : Blo 1715058 1716875 := bstep (se 1 (by rfl) ⟨1287656, by rfl⟩ : syracuseStep 1716875 = 2575313) B2575313
theorem B1716887 : Blo 1715058 1716887 := bstep (se 1 (by rfl) ⟨1287665, by rfl⟩ : syracuseStep 1716887 = 2575331) B2575331
theorem B1716907 : Blo 1715058 1716907 := bstep (se 1 (by rfl) ⟨1287680, by rfl⟩ : syracuseStep 1716907 = 2575361) B2575361
theorem B1716919 : Blo 1715058 1716919 := bstep (se 1 (by rfl) ⟨1287689, by rfl⟩ : syracuseStep 1716919 = 2575379) B2575379
theorem B4125377 : Blo 1715058 4125377 := bstep (se 2 (by rfl) ⟨1547016, by rfl⟩ : syracuseStep 4125377 = 3094033) B3094033
theorem B1716939 : Blo 1715058 1716939 := bstep (se 1 (by rfl) ⟨1287704, by rfl⟩ : syracuseStep 1716939 = 2575409) B2575409
theorem B1716951 : Blo 1715058 1716951 := bstep (se 1 (by rfl) ⟨1287713, by rfl⟩ : syracuseStep 1716951 = 2575427) B2575427
theorem B1716971 : Blo 1715058 1716971 := bstep (se 1 (by rfl) ⟨1287728, by rfl⟩ : syracuseStep 1716971 = 2575457) B2575457
theorem B1716983 : Blo 1715058 1716983 := bstep (se 1 (by rfl) ⟨1287737, by rfl⟩ : syracuseStep 1716983 = 2575475) B2575475
theorem B1717003 : Blo 1715058 1717003 := bstep (se 1 (by rfl) ⟨1287752, by rfl⟩ : syracuseStep 1717003 = 2575505) B2575505
theorem B3257111 : Blo 1715058 3257111 := bstep (se 1 (by rfl) ⟨2442833, by rfl⟩ : syracuseStep 3257111 = 4885667) B4885667
theorem B1717015 : Blo 1715058 1717015 := bstep (se 1 (by rfl) ⟨1287761, by rfl⟩ : syracuseStep 1717015 = 2575523) B2575523
theorem B3863321 : Blo 1715058 3863321 := bstep (se 2 (by rfl) ⟨1448745, by rfl⟩ : syracuseStep 3863321 = 2897491) B2897491
theorem B1930027 : Blo 1715058 1930027 := bstep (se 1 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 1930027 = 2895041) B2895041
theorem B1717035 : Blo 1715058 1717035 := bstep (se 1 (by rfl) ⟨1287776, by rfl⟩ : syracuseStep 1717035 = 2575553) B2575553
theorem B1717047 : Blo 1715058 1717047 := bstep (se 1 (by rfl) ⟨1287785, by rfl⟩ : syracuseStep 1717047 = 2575571) B2575571
theorem B2896715 : Blo 1715058 2896715 := bstep (se 1 (by rfl) ⟨2172536, by rfl⟩ : syracuseStep 2896715 = 4345073) B4345073
theorem B3715969 : Blo 1715058 3715969 := bstep (se 2 (by rfl) ⟨1393488, by rfl⟩ : syracuseStep 3715969 = 2786977) B2786977
theorem B1930135 : Blo 1715058 1930135 := bstep (se 1 (by rfl) ⟨1447601, by rfl⟩ : syracuseStep 1930135 = 2895203) B2895203
theorem B6517655 : Blo 1715058 6517655 := bstep (se 1 (by rfl) ⟨4888241, by rfl⟩ : syracuseStep 6517655 = 9776483) B9776483
theorem B2896843 : Blo 1715058 2896843 := bstep (se 1 (by rfl) ⟨2172632, by rfl⟩ : syracuseStep 2896843 = 4345265) B4345265
theorem B5788637 : Blo 1715058 5788637 := bstep (se 3 (by rfl) ⟨1085369, by rfl⟩ : syracuseStep 5788637 = 2170739) B2170739
theorem B7328843 : Blo 1715058 7328843 := bstep (se 1 (by rfl) ⟨5496632, by rfl⟩ : syracuseStep 7328843 = 10993265) B10993265
theorem B1930315 : Blo 1715058 1930315 := bstep (se 1 (by rfl) ⟨1447736, by rfl⟩ : syracuseStep 1930315 = 2895473) B2895473
theorem B2896985 : Blo 1715058 2896985 := bstep (se 2 (by rfl) ⟨1086369, by rfl⟩ : syracuseStep 2896985 = 2172739) B2172739
theorem B6517853 : Blo 1715058 6517853 := bstep (se 3 (by rfl) ⟨1222097, by rfl⟩ : syracuseStep 6517853 = 2444195) B2444195
theorem B1930423 : Blo 1715058 1930423 := bstep (se 1 (by rfl) ⟨1447817, by rfl⟩ : syracuseStep 1930423 = 2895635) B2895635
theorem B2897113 : Blo 1715058 2897113 := bstep (se 2 (by rfl) ⟨1086417, by rfl⟩ : syracuseStep 2897113 = 2172835) B2172835
theorem B3912985 : Blo 1715058 3912985 := bstep (se 2 (by rfl) ⟨1467369, by rfl⟩ : syracuseStep 3912985 = 2934739) B2934739
theorem B13038893 : Blo 1715058 13038893 := bstep (se 3 (by rfl) ⟨2444792, by rfl⟩ : syracuseStep 13038893 = 4889585) B4889585
theorem B3257651 : Blo 1715058 3257651 := bstep (se 1 (by rfl) ⟨2443238, by rfl⟩ : syracuseStep 3257651 = 4886477) B4886477
theorem B19813697 : Blo 1715058 19813697 := bstep (se 2 (by rfl) ⟨7430136, by rfl⟩ : syracuseStep 19813697 = 14860273) B14860273
theorem B1832279 : Blo 1715058 1832279 := bstep (se 1 (by rfl) ⟨1374209, by rfl⟩ : syracuseStep 1832279 = 2748419) B2748419
theorem B16495973 : Blo 1715058 16495973 := bstep (se 4 (by rfl) ⟨1546497, by rfl⟩ : syracuseStep 16495973 = 3092995) B3092995
theorem B1930603 : Blo 1715058 1930603 := bstep (se 1 (by rfl) ⟨1447952, by rfl⟩ : syracuseStep 1930603 = 2895905) B2895905
theorem B1930711 : Blo 1715058 1930711 := bstep (se 1 (by rfl) ⟨1448033, by rfl⟩ : syracuseStep 1930711 = 2896067) B2896067
theorem B10999313 : Blo 1715058 10999313 := bstep (se 2 (by rfl) ⟨4124742, by rfl⟩ : syracuseStep 10999313 = 8249485) B8249485
theorem B19551779 : Blo 1715058 19551779 := bstep (se 1 (by rfl) ⟨14663834, by rfl⟩ : syracuseStep 19551779 = 29327669) B29327669
theorem B6182531 : Blo 1715058 6182531 := bstep (se 1 (by rfl) ⟨4636898, by rfl⟩ : syracuseStep 6182531 = 9273797) B9273797
theorem B1930891 : Blo 1715058 1930891 := bstep (se 1 (by rfl) ⟨1448168, by rfl⟩ : syracuseStep 1930891 = 2896337) B2896337
theorem B13031117 : Blo 1715058 13031117 := bstep (se 3 (by rfl) ⟨2443334, by rfl⟩ : syracuseStep 13031117 = 4886669) B4886669
theorem B1930999 : Blo 1715058 1930999 := bstep (se 1 (by rfl) ⟨1448249, by rfl⟩ : syracuseStep 1930999 = 2896499) B2896499
theorem B3258137 : Blo 1715058 3258137 := bstep (se 2 (by rfl) ⟨1221801, by rfl⟩ : syracuseStep 3258137 = 2443603) B2443603
theorem B4405067 : Blo 1715058 4405067 := bstep (se 1 (by rfl) ⟨3303800, by rfl⟩ : syracuseStep 4405067 = 6607601) B6607601
theorem B7329629 : Blo 1715058 7329629 := bstep (se 3 (by rfl) ⟨1374305, by rfl⟩ : syracuseStep 7329629 = 2748611) B2748611
theorem B1931179 : Blo 1715058 1931179 := bstep (se 1 (by rfl) ⟨1448384, by rfl⟩ : syracuseStep 1931179 = 2896769) B2896769
theorem B9770969 : Blo 1715058 9770969 := bstep (se 2 (by rfl) ⟨3664113, by rfl⟩ : syracuseStep 9770969 = 7328227) B7328227
theorem B1931287 : Blo 1715058 1931287 := bstep (se 1 (by rfl) ⟨1448465, by rfl⟩ : syracuseStep 1931287 = 2896931) B2896931
theorem B5789771 : Blo 1715058 5789771 := bstep (se 1 (by rfl) ⟨4342328, by rfl⟩ : syracuseStep 5789771 = 8684657) B8684657
theorem B13031603 : Blo 1715058 13031603 := bstep (se 1 (by rfl) ⟨9773702, by rfl⟩ : syracuseStep 13031603 = 19547405) B19547405
theorem B1931467 : Blo 1715058 1931467 := bstep (se 1 (by rfl) ⟨1448600, by rfl⟩ : syracuseStep 1931467 = 2897201) B2897201
theorem B6961411 : Blo 1715058 6961411 := bstep (se 1 (by rfl) ⟨5221058, by rfl⟩ : syracuseStep 6961411 = 10442117) B10442117
theorem B1931575 : Blo 1715058 1931575 := bstep (se 1 (by rfl) ⟨1448681, by rfl⟩ : syracuseStep 1931575 = 2897363) B2897363
theorem B5790041 : Blo 1715058 5790041 := bstep (se 2 (by rfl) ⟨2171265, by rfl⟩ : syracuseStep 5790041 = 4342531) B4342531
theorem B3479897 : Blo 1715058 3479897 := bstep (se 2 (by rfl) ⟨1304961, by rfl⟩ : syracuseStep 3479897 = 2609923) B2609923
theorem B125254001 : Blo 1715058 125254001 := bstep (se 2 (by rfl) ⟨46970250, by rfl⟩ : syracuseStep 125254001 = 93940501) B93940501
theorem B3135883 : Blo 1715058 3135883 := bstep (se 1 (by rfl) ⟨2351912, by rfl⟩ : syracuseStep 3135883 = 4703825) B4703825
theorem B4889153 : Blo 1715058 4889153 := bstep (se 2 (by rfl) ⟨1833432, by rfl⟩ : syracuseStep 4889153 = 3666865) B3666865
theorem B8690327 : Blo 1715058 8690327 := bstep (se 1 (by rfl) ⟨6517745, by rfl⟩ : syracuseStep 8690327 = 13035491) B13035491
theorem B4889267 : Blo 1715058 4889267 := bstep (se 1 (by rfl) ⟨3666950, by rfl⟩ : syracuseStep 4889267 = 7333901) B7333901
theorem B6183641 : Blo 1715058 6183641 := bstep (se 2 (by rfl) ⟨2318865, by rfl⟩ : syracuseStep 6183641 = 4637731) B4637731
theorem B16489433 : Blo 1715058 16489433 := bstep (se 2 (by rfl) ⟨6183537, by rfl⟩ : syracuseStep 16489433 = 12367075) B12367075
theorem B5790743 : Blo 1715058 5790743 := bstep (se 1 (by rfl) ⟨4343057, by rfl⟩ : syracuseStep 5790743 = 8686115) B8686115
theorem B41770019 : Blo 1715058 41770019 := bstep (se 1 (by rfl) ⟨31327514, by rfl⟩ : syracuseStep 41770019 = 62655029) B62655029
theorem B7330961 : Blo 1715058 7330961 := bstep (se 2 (by rfl) ⟨2749110, by rfl⟩ : syracuseStep 7330961 = 5498221) B5498221
theorem B6184115 : Blo 1715058 6184115 := bstep (se 1 (by rfl) ⟨4638086, by rfl⟩ : syracuseStep 6184115 = 9276173) B9276173
theorem B3259595 : Blo 1715058 3259595 := bstep (se 1 (by rfl) ⟨2444696, by rfl⟩ : syracuseStep 3259595 = 4889393) B4889393
theorem B8682713 : Blo 1715058 8682713 := bstep (se 2 (by rfl) ⟨3256017, by rfl⟩ : syracuseStep 8682713 = 6512035) B6512035
theorem B62594309 : Blo 1715058 62594309 := bstep (se 4 (by rfl) ⟨5868216, by rfl⟩ : syracuseStep 62594309 = 11736433) B11736433
theorem B4636097 : Blo 1715058 4636097 := bstep (se 2 (by rfl) ⟨1738536, by rfl⟩ : syracuseStep 4636097 = 3477073) B3477073
theorem B3915211 : Blo 1715058 3915211 := bstep (se 1 (by rfl) ⟨2936408, by rfl⟩ : syracuseStep 3915211 = 5872817) B5872817
theorem B15646243 : Blo 1715058 15646243 := bstep (se 1 (by rfl) ⟨11734682, by rfl⟩ : syracuseStep 15646243 = 23469365) B23469365
theorem B5791283 : Blo 1715058 5791283 := bstep (se 1 (by rfl) ⟨4343462, by rfl⟩ : syracuseStep 5791283 = 8686925) B8686925
theorem B9772609 : Blo 1715058 9772609 := bstep (se 2 (by rfl) ⟨3664728, by rfl⟩ : syracuseStep 9772609 = 7329457) B7329457
theorem B13033061 : Blo 1715058 13033061 := bstep (se 4 (by rfl) ⟨1221849, by rfl⟩ : syracuseStep 13033061 = 2443699) B2443699
theorem B5217995 : Blo 1715058 5217995 := bstep (se 1 (by rfl) ⟨3913496, by rfl⟩ : syracuseStep 5217995 = 7826993) B7826993
theorem B3915467 : Blo 1715058 3915467 := bstep (se 1 (by rfl) ⟨2936600, by rfl⟩ : syracuseStep 3915467 = 5873201) B5873201
theorem B6602519 : Blo 1715058 6602519 := bstep (se 1 (by rfl) ⟨4951889, by rfl⟩ : syracuseStep 6602519 = 9903779) B9903779
theorem B5791553 : Blo 1715058 5791553 := bstep (se 2 (by rfl) ⟨2171832, by rfl⟩ : syracuseStep 5791553 = 4343665) B4343665
theorem B6954827 : Blo 1715058 6954827 := bstep (se 1 (by rfl) ⟨5216120, by rfl⟩ : syracuseStep 6954827 = 10432241) B10432241
theorem B3915713 : Blo 1715058 3915713 := bstep (se 2 (by rfl) ⟨1468392, by rfl⟩ : syracuseStep 3915713 = 2936785) B2936785
theorem B4341721 : Blo 1715058 4341721 := bstep (se 2 (by rfl) ⟨1628145, by rfl⟩ : syracuseStep 4341721 = 3256291) B3256291
theorem B8683523 : Blo 1715058 8683523 := bstep (se 1 (by rfl) ⟨6512642, by rfl⟩ : syracuseStep 8683523 = 13025285) B13025285
theorem B2318351 : Blo 1715058 2318351 := bstep (se 1 (by rfl) ⟨1738763, by rfl⟩ : syracuseStep 2318351 = 3477527) B3477527
theorem B2318395 : Blo 1715058 2318395 := bstep (se 1 (by rfl) ⟨1738796, by rfl⟩ : syracuseStep 2318395 = 3477593) B3477593
theorem B2572601 : Blo 1715058 2572601 := bstep (se 2 (by rfl) ⟨964725, by rfl⟩ : syracuseStep 2572601 = 1929451) B1929451
theorem B4120919 : Blo 1715058 4120919 := bstep (se 1 (by rfl) ⟨3090689, by rfl⟩ : syracuseStep 4120919 = 6181379) B6181379
theorem B9281881 : Blo 1715058 9281881 := bstep (se 2 (by rfl) ⟨3480705, by rfl⟩ : syracuseStep 9281881 = 6961411) B6961411
theorem B2572679 : Blo 1715058 2572679 := bstep (se 1 (by rfl) ⟨1929509, by rfl⟩ : syracuseStep 2572679 = 3859019) B3859019
theorem B19554695 : Blo 1715058 19554695 := bstep (se 1 (by rfl) ⟨14666021, by rfl⟩ : syracuseStep 19554695 = 29332043) B29332043
theorem B5792147 : Blo 1715058 5792147 := bstep (se 1 (by rfl) ⟨4344110, by rfl⟩ : syracuseStep 5792147 = 8688221) B8688221
theorem B2572715 : Blo 1715058 2572715 := bstep (se 1 (by rfl) ⟨1929536, by rfl⟩ : syracuseStep 2572715 = 3859073) B3859073
theorem B2572745 : Blo 1715058 2572745 := bstep (se 2 (by rfl) ⟨964779, by rfl⟩ : syracuseStep 2572745 = 1929559) B1929559
theorem B2572859 : Blo 1715058 2572859 := bstep (se 1 (by rfl) ⟨1929644, by rfl⟩ : syracuseStep 2572859 = 3859289) B3859289
theorem B9273923 : Blo 1715058 9273923 := bstep (se 1 (by rfl) ⟨6955442, by rfl⟩ : syracuseStep 9273923 = 13910885) B13910885
theorem B2572919 : Blo 1715058 2572919 := bstep (se 1 (by rfl) ⟨1929689, by rfl⟩ : syracuseStep 2572919 = 3859379) B3859379
theorem B2572943 : Blo 1715058 2572943 := bstep (se 1 (by rfl) ⟨1929707, by rfl⟩ : syracuseStep 2572943 = 3859415) B3859415
theorem B3859091 : Blo 1715058 3859091 := bstep (se 1 (by rfl) ⟨2894318, by rfl⟩ : syracuseStep 3859091 = 5788637) B5788637
theorem B2572985 : Blo 1715058 2572985 := bstep (se 2 (by rfl) ⟨964869, by rfl⟩ : syracuseStep 2572985 = 1929739) B1929739
theorem B3859145 : Blo 1715058 3859145 := bstep (se 2 (by rfl) ⟨1447179, by rfl⟩ : syracuseStep 3859145 = 2894359) B2894359
theorem B2573063 : Blo 1715058 2573063 := bstep (se 1 (by rfl) ⟨1929797, by rfl⟩ : syracuseStep 2573063 = 3859595) B3859595
theorem B2573099 : Blo 1715058 2573099 := bstep (se 1 (by rfl) ⟨1929824, by rfl⟩ : syracuseStep 2573099 = 3859649) B3859649
theorem B2573129 : Blo 1715058 2573129 := bstep (se 2 (by rfl) ⟨964923, by rfl⟩ : syracuseStep 2573129 = 1929847) B1929847
theorem B4342643 : Blo 1715058 4342643 := bstep (se 1 (by rfl) ⟨3256982, by rfl⟩ : syracuseStep 4342643 = 6513965) B6513965
theorem B8692595 : Blo 1715058 8692595 := bstep (se 1 (by rfl) ⟨6519446, by rfl⟩ : syracuseStep 8692595 = 13038893) B13038893
theorem B2171767 : Blo 1715058 2171767 := bstep (se 1 (by rfl) ⟨1628825, by rfl⟩ : syracuseStep 2171767 = 3257651) B3257651
theorem B2573243 : Blo 1715058 2573243 := bstep (se 1 (by rfl) ⟨1929932, by rfl⟩ : syracuseStep 2573243 = 3859865) B3859865
theorem B2573303 : Blo 1715058 2573303 := bstep (se 1 (by rfl) ⟨1929977, by rfl⟩ : syracuseStep 2573303 = 3859955) B3859955
theorem B7332875 : Blo 1715058 7332875 := bstep (se 1 (by rfl) ⟨5499656, by rfl⟩ : syracuseStep 7332875 = 10999313) B10999313
theorem B2573327 : Blo 1715058 2573327 := bstep (se 1 (by rfl) ⟨1929995, by rfl⟩ : syracuseStep 2573327 = 3859991) B3859991
theorem B13034519 : Blo 1715058 13034519 := bstep (se 1 (by rfl) ⟨9775889, by rfl⟩ : syracuseStep 13034519 = 19551779) B19551779
theorem B2573369 : Blo 1715058 2573369 := bstep (se 2 (by rfl) ⟨965013, by rfl⟩ : syracuseStep 2573369 = 1930027) B1930027
theorem B4121687 : Blo 1715058 4121687 := bstep (se 1 (by rfl) ⟨3091265, by rfl⟩ : syracuseStep 4121687 = 6182531) B6182531
theorem B2573447 : Blo 1715058 2573447 := bstep (se 1 (by rfl) ⟨1930085, by rfl⟩ : syracuseStep 2573447 = 3860171) B3860171
theorem B2573483 : Blo 1715058 2573483 := bstep (se 1 (by rfl) ⟨1930112, by rfl⟩ : syracuseStep 2573483 = 3860225) B3860225
theorem B2172091 : Blo 1715058 2172091 := bstep (se 1 (by rfl) ⟨1629068, by rfl⟩ : syracuseStep 2172091 = 3258137) B3258137
theorem B2573513 : Blo 1715058 2573513 := bstep (se 2 (by rfl) ⟨965067, by rfl⟩ : syracuseStep 2573513 = 1930135) B1930135
theorem B6513979 : Blo 1715058 6513979 := bstep (se 1 (by rfl) ⟨4885484, by rfl⟩ : syracuseStep 6513979 = 9770969) B9770969
theorem B2573627 : Blo 1715058 2573627 := bstep (se 1 (by rfl) ⟨1930220, by rfl⟩ : syracuseStep 2573627 = 3860441) B3860441
theorem B2573687 : Blo 1715058 2573687 := bstep (se 1 (by rfl) ⟨1930265, by rfl⟩ : syracuseStep 2573687 = 3860531) B3860531
theorem B4343159 : Blo 1715058 4343159 := bstep (se 1 (by rfl) ⟨3257369, by rfl⟩ : syracuseStep 4343159 = 6514739) B6514739
theorem B3859847 : Blo 1715058 3859847 := bstep (se 1 (by rfl) ⟨2894885, by rfl⟩ : syracuseStep 3859847 = 5789771) B5789771
theorem B2573711 : Blo 1715058 2573711 := bstep (se 1 (by rfl) ⟨1930283, by rfl⟩ : syracuseStep 2573711 = 3860567) B3860567
theorem B18548153 : Blo 1715058 18548153 := bstep (se 2 (by rfl) ⟨6955557, by rfl⟩ : syracuseStep 18548153 = 13911115) B13911115
theorem B2573753 : Blo 1715058 2573753 := bstep (se 2 (by rfl) ⟨965157, by rfl⟩ : syracuseStep 2573753 = 1930315) B1930315
theorem B2573831 : Blo 1715058 2573831 := bstep (se 1 (by rfl) ⟨1930373, by rfl⟩ : syracuseStep 2573831 = 3860747) B3860747
theorem B2573867 : Blo 1715058 2573867 := bstep (se 1 (by rfl) ⟨1930400, by rfl⟩ : syracuseStep 2573867 = 3860801) B3860801
theorem B3860027 : Blo 1715058 3860027 := bstep (se 1 (by rfl) ⟨2895020, by rfl⟩ : syracuseStep 3860027 = 5790041) B5790041
theorem B2442811 : Blo 1715058 2442811 := bstep (se 1 (by rfl) ⟨1832108, by rfl⟩ : syracuseStep 2442811 = 3664217) B3664217
theorem B2319931 : Blo 1715058 2319931 := bstep (se 1 (by rfl) ⟨1739948, by rfl⟩ : syracuseStep 2319931 = 3479897) B3479897
theorem B2573897 : Blo 1715058 2573897 := bstep (se 2 (by rfl) ⟨965211, by rfl⟩ : syracuseStep 2573897 = 1930423) B1930423
theorem B83502667 : Blo 1715058 83502667 := bstep (se 1 (by rfl) ⟨62627000, by rfl⟩ : syracuseStep 83502667 = 125254001) B125254001
theorem B8685143 : Blo 1715058 8685143 := bstep (se 1 (by rfl) ⟨6513857, by rfl⟩ : syracuseStep 8685143 = 13027715) B13027715
theorem B12371575 : Blo 1715058 12371575 := bstep (se 1 (by rfl) ⟨9278681, by rfl⟩ : syracuseStep 12371575 = 18557363) B18557363
theorem B3860153 : Blo 1715058 3860153 := bstep (se 2 (by rfl) ⟨1447557, by rfl⟩ : syracuseStep 3860153 = 2895115) B2895115
theorem B2574011 : Blo 1715058 2574011 := bstep (se 1 (by rfl) ⟨1930508, by rfl⟩ : syracuseStep 2574011 = 3861017) B3861017
theorem B10036973 : Blo 1715058 10036973 := bstep (se 3 (by rfl) ⟨1881932, by rfl⟩ : syracuseStep 10036973 = 3763865) B3763865
theorem B2574071 : Blo 1715058 2574071 := bstep (se 1 (by rfl) ⟨1930553, by rfl⟩ : syracuseStep 2574071 = 3861107) B3861107
theorem B2574095 : Blo 1715058 2574095 := bstep (se 1 (by rfl) ⟨1930571, by rfl⟩ : syracuseStep 2574095 = 3861143) B3861143
theorem B5793551 : Blo 1715058 5793551 := bstep (se 1 (by rfl) ⟨4345163, by rfl⟩ : syracuseStep 5793551 = 8690327) B8690327
theorem B6514465 : Blo 1715058 6514465 := bstep (se 2 (by rfl) ⟨2442924, by rfl⟩ : syracuseStep 6514465 = 4885849) B4885849
theorem B2574137 : Blo 1715058 2574137 := bstep (se 2 (by rfl) ⟨965301, by rfl⟩ : syracuseStep 2574137 = 1930603) B1930603
theorem B4122427 : Blo 1715058 4122427 := bstep (se 1 (by rfl) ⟨3091820, by rfl⟩ : syracuseStep 4122427 = 6183641) B6183641
theorem B2574215 : Blo 1715058 2574215 := bstep (se 1 (by rfl) ⟨1930661, by rfl⟩ : syracuseStep 2574215 = 3861323) B3861323
theorem B2574251 : Blo 1715058 2574251 := bstep (se 1 (by rfl) ⟨1930688, by rfl⟩ : syracuseStep 2574251 = 3861377) B3861377
theorem B5220281 : Blo 1715058 5220281 := bstep (se 2 (by rfl) ⟨1957605, by rfl⟩ : syracuseStep 5220281 = 3915211) B3915211
theorem B2574281 : Blo 1715058 2574281 := bstep (se 2 (by rfl) ⟨965355, by rfl⟩ : syracuseStep 2574281 = 1930711) B1930711
theorem B3860495 : Blo 1715058 3860495 := bstep (se 1 (by rfl) ⟨2895371, by rfl⟩ : syracuseStep 3860495 = 5790743) B5790743
theorem B27846679 : Blo 1715058 27846679 := bstep (se 1 (by rfl) ⟨20885009, by rfl⟩ : syracuseStep 27846679 = 41770019) B41770019
theorem B5793821 : Blo 1715058 5793821 := bstep (se 3 (by rfl) ⟨1086341, by rfl⟩ : syracuseStep 5793821 = 2172683) B2172683
theorem B3860513 : Blo 1715058 3860513 := bstep (se 2 (by rfl) ⟨1447692, by rfl⟩ : syracuseStep 3860513 = 2895385) B2895385
theorem B4638779 : Blo 1715058 4638779 := bstep (se 1 (by rfl) ⟨3479084, by rfl⟩ : syracuseStep 4638779 = 6958169) B6958169
theorem B2574395 : Blo 1715058 2574395 := bstep (se 1 (by rfl) ⟨1930796, by rfl⟩ : syracuseStep 2574395 = 3861593) B3861593
theorem B17606717 : Blo 1715058 17606717 := bstep (se 3 (by rfl) ⟨3301259, by rfl⟩ : syracuseStep 17606717 = 6602519) B6602519
theorem B8685629 : Blo 1715058 8685629 := bstep (se 3 (by rfl) ⟨1628555, by rfl⟩ : syracuseStep 8685629 = 3257111) B3257111
theorem B6604861 : Blo 1715058 6604861 := bstep (se 3 (by rfl) ⟨1238411, by rfl⟩ : syracuseStep 6604861 = 2476823) B2476823
theorem B4180027 : Blo 1715058 4180027 := bstep (se 1 (by rfl) ⟨3135020, by rfl⟩ : syracuseStep 4180027 = 6270041) B6270041
theorem B4122743 : Blo 1715058 4122743 := bstep (se 1 (by rfl) ⟨3092057, by rfl⟩ : syracuseStep 4122743 = 6184115) B6184115
theorem B2574455 : Blo 1715058 2574455 := bstep (se 1 (by rfl) ⟨1930841, by rfl⟩ : syracuseStep 2574455 = 3861683) B3861683
theorem B4704391 : Blo 1715058 4704391 := bstep (se 1 (by rfl) ⟨3528293, by rfl⟩ : syracuseStep 4704391 = 7056587) B7056587
theorem B2173063 : Blo 1715058 2173063 := bstep (se 1 (by rfl) ⟨1629797, by rfl⟩ : syracuseStep 2173063 = 3259595) B3259595
theorem B2574479 : Blo 1715058 2574479 := bstep (se 1 (by rfl) ⟨1930859, by rfl⟩ : syracuseStep 2574479 = 3861719) B3861719
theorem B2574521 : Blo 1715058 2574521 := bstep (se 2 (by rfl) ⟨965445, by rfl⟩ : syracuseStep 2574521 = 1930891) B1930891
theorem B2574599 : Blo 1715058 2574599 := bstep (se 1 (by rfl) ⟨1930949, by rfl⟩ : syracuseStep 2574599 = 3861899) B3861899
theorem B8243471 : Blo 1715058 8243471 := bstep (se 1 (by rfl) ⟨6182603, by rfl⟩ : syracuseStep 8243471 = 12365207) B12365207
theorem B3090731 : Blo 1715058 3090731 := bstep (se 1 (by rfl) ⟨2318048, by rfl⟩ : syracuseStep 3090731 = 4636097) B4636097
theorem B4884779 : Blo 1715058 4884779 := bstep (se 1 (by rfl) ⟨3663584, by rfl⟩ : syracuseStep 4884779 = 7327169) B7327169
theorem B2574635 : Blo 1715058 2574635 := bstep (se 1 (by rfl) ⟨1930976, by rfl⟩ : syracuseStep 2574635 = 3861953) B3861953
theorem B2574665 : Blo 1715058 2574665 := bstep (se 2 (by rfl) ⟨965499, by rfl⟩ : syracuseStep 2574665 = 1930999) B1930999
theorem B4344151 : Blo 1715058 4344151 := bstep (se 1 (by rfl) ⟨3258113, by rfl⟩ : syracuseStep 4344151 = 6516227) B6516227
theorem B3860855 : Blo 1715058 3860855 := bstep (se 1 (by rfl) ⟨2895641, by rfl⟩ : syracuseStep 3860855 = 5791283) B5791283
theorem B2574779 : Blo 1715058 2574779 := bstep (se 1 (by rfl) ⟨1931084, by rfl⟩ : syracuseStep 2574779 = 3862169) B3862169
theorem B2574839 : Blo 1715058 2574839 := bstep (se 1 (by rfl) ⟨1931129, by rfl⟩ : syracuseStep 2574839 = 3862259) B3862259
theorem B1739279 : Blo 1715058 1739279 := bstep (se 1 (by rfl) ⟨1304459, by rfl⟩ : syracuseStep 1739279 = 2608919) B2608919
theorem B2574863 : Blo 1715058 2574863 := bstep (se 1 (by rfl) ⟨1931147, by rfl⟩ : syracuseStep 2574863 = 3862295) B3862295
theorem B3861035 : Blo 1715058 3861035 := bstep (se 1 (by rfl) ⟨2895776, by rfl⟩ : syracuseStep 3861035 = 5791553) B5791553
theorem B2574905 : Blo 1715058 2574905 := bstep (se 2 (by rfl) ⟨965589, by rfl⟩ : syracuseStep 2574905 = 1931179) B1931179
theorem B4344455 : Blo 1715058 4344455 := bstep (se 1 (by rfl) ⟨3258341, by rfl⟩ : syracuseStep 4344455 = 6516683) B6516683
theorem B2574983 : Blo 1715058 2574983 := bstep (se 1 (by rfl) ⟨1931237, by rfl⟩ : syracuseStep 2574983 = 3862475) B3862475
theorem B2575019 : Blo 1715058 2575019 := bstep (se 1 (by rfl) ⟨1931264, by rfl⟩ : syracuseStep 2575019 = 3862529) B3862529
theorem B2894521 : Blo 1715058 2894521 := bstep (se 2 (by rfl) ⟨1085445, by rfl⟩ : syracuseStep 2894521 = 2170891) B2170891
theorem B2575049 : Blo 1715058 2575049 := bstep (se 2 (by rfl) ⟨965643, by rfl⟩ : syracuseStep 2575049 = 1931287) B1931287
theorem B13208293 : Blo 1715058 13208293 := bstep (se 4 (by rfl) ⟨1238277, by rfl⟩ : syracuseStep 13208293 = 2476555) B2476555
theorem B6515437 : Blo 1715058 6515437 := bstep (se 3 (by rfl) ⟨1221644, by rfl⟩ : syracuseStep 6515437 = 2443289) B2443289
theorem B4344587 : Blo 1715058 4344587 := bstep (se 1 (by rfl) ⟨3258440, by rfl⟩ : syracuseStep 4344587 = 6516881) B6516881
theorem B4123435 : Blo 1715058 4123435 := bstep (se 1 (by rfl) ⟨3092576, by rfl⟩ : syracuseStep 4123435 = 6185153) B6185153
theorem B2575163 : Blo 1715058 2575163 := bstep (se 1 (by rfl) ⟨1931372, by rfl⟩ : syracuseStep 2575163 = 3862745) B3862745
theorem B2575223 : Blo 1715058 2575223 := bstep (se 1 (by rfl) ⟨1931417, by rfl⟩ : syracuseStep 2575223 = 3862835) B3862835
theorem B1715079 : Blo 1715058 1715079 := bstep (se 1 (by rfl) ⟨1286309, by rfl⟩ : syracuseStep 1715079 = 2572619) B2572619
theorem B1715087 : Blo 1715058 1715087 := bstep (se 1 (by rfl) ⟨1286315, by rfl⟩ : syracuseStep 1715087 = 2572631) B2572631
theorem B2575247 : Blo 1715058 2575247 := bstep (se 1 (by rfl) ⟨1931435, by rfl⟩ : syracuseStep 2575247 = 3862871) B3862871
theorem B3861395 : Blo 1715058 3861395 := bstep (se 1 (by rfl) ⟨2896046, by rfl⟩ : syracuseStep 3861395 = 5792093) B5792093
theorem B2608043 : Blo 1715058 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B2575289 : Blo 1715058 2575289 := bstep (se 2 (by rfl) ⟨965733, by rfl⟩ : syracuseStep 2575289 = 1931467) B1931467
theorem B1715131 : Blo 1715058 1715131 := bstep (se 1 (by rfl) ⟨1286348, by rfl⟩ : syracuseStep 1715131 = 2572697) B2572697
theorem B3861449 : Blo 1715058 3861449 := bstep (se 2 (by rfl) ⟨1448043, by rfl⟩ : syracuseStep 3861449 = 2896087) B2896087
theorem B1715207 : Blo 1715058 1715207 := bstep (se 1 (by rfl) ⟨1286405, by rfl⟩ : syracuseStep 1715207 = 2572811) B2572811
theorem B2575367 : Blo 1715058 2575367 := bstep (se 1 (by rfl) ⟨1931525, by rfl⟩ : syracuseStep 2575367 = 3863051) B3863051
theorem B1715215 : Blo 1715058 1715215 := bstep (se 1 (by rfl) ⟨1286411, by rfl⟩ : syracuseStep 1715215 = 2572823) B2572823
theorem B2444303 : Blo 1715058 2444303 := bstep (se 1 (by rfl) ⟨1833227, by rfl⟩ : syracuseStep 2444303 = 3666455) B3666455
theorem B6515741 : Blo 1715058 6515741 := bstep (se 3 (by rfl) ⟨1221701, by rfl⟩ : syracuseStep 6515741 = 2443403) B2443403
theorem B2575403 : Blo 1715058 2575403 := bstep (se 1 (by rfl) ⟨1931552, by rfl⟩ : syracuseStep 2575403 = 3863105) B3863105
theorem B1715259 : Blo 1715058 1715259 := bstep (se 1 (by rfl) ⟨1286444, by rfl⟩ : syracuseStep 1715259 = 2572889) B2572889
theorem B2575433 : Blo 1715058 2575433 := bstep (se 2 (by rfl) ⟨965787, by rfl⟩ : syracuseStep 2575433 = 1931575) B1931575
theorem B1715335 : Blo 1715058 1715335 := bstep (se 1 (by rfl) ⟨1286501, by rfl⟩ : syracuseStep 1715335 = 2573003) B2573003
theorem B1715343 : Blo 1715058 1715343 := bstep (se 1 (by rfl) ⟨1286507, by rfl⟩ : syracuseStep 1715343 = 2573015) B2573015
theorem B4181177 : Blo 1715058 4181177 := bstep (se 2 (by rfl) ⟨1567941, by rfl⟩ : syracuseStep 4181177 = 3135883) B3135883
theorem B1715387 : Blo 1715058 1715387 := bstep (se 1 (by rfl) ⟨1286540, by rfl⟩ : syracuseStep 1715387 = 2573081) B2573081
theorem B2575547 : Blo 1715058 2575547 := bstep (se 1 (by rfl) ⟨1931660, by rfl⟩ : syracuseStep 2575547 = 3863321) B3863321
theorem B1715463 : Blo 1715058 1715463 := bstep (se 1 (by rfl) ⟨1286597, by rfl⟩ : syracuseStep 1715463 = 2573195) B2573195
theorem B1715471 : Blo 1715058 1715471 := bstep (se 1 (by rfl) ⟨1286603, by rfl⟩ : syracuseStep 1715471 = 2573207) B2573207
theorem B4345103 : Blo 1715058 4345103 := bstep (se 1 (by rfl) ⟨3258827, by rfl⟩ : syracuseStep 4345103 = 6517655) B6517655
theorem B10431803 : Blo 1715058 10431803 := bstep (se 1 (by rfl) ⟨7823852, by rfl⟩ : syracuseStep 10431803 = 15647705) B15647705
theorem B1715515 : Blo 1715058 1715515 := bstep (se 1 (by rfl) ⟨1286636, by rfl⟩ : syracuseStep 1715515 = 2573273) B2573273
theorem B2895223 : Blo 1715058 2895223 := bstep (se 1 (by rfl) ⟨2171417, by rfl⟩ : syracuseStep 2895223 = 4342835) B4342835
theorem B1715591 : Blo 1715058 1715591 := bstep (se 1 (by rfl) ⟨1286693, by rfl⟩ : syracuseStep 1715591 = 2573387) B2573387
theorem B4885895 : Blo 1715058 4885895 := bstep (se 1 (by rfl) ⟨3664421, by rfl⟩ : syracuseStep 4885895 = 7328843) B7328843
theorem B1715599 : Blo 1715058 1715599 := bstep (se 1 (by rfl) ⟨1286699, by rfl⟩ : syracuseStep 1715599 = 2573399) B2573399
theorem B4124051 : Blo 1715058 4124051 := bstep (se 1 (by rfl) ⟨3093038, by rfl⟩ : syracuseStep 4124051 = 6186077) B6186077
theorem B4345235 : Blo 1715058 4345235 := bstep (se 1 (by rfl) ⟨3258926, by rfl⟩ : syracuseStep 4345235 = 6517853) B6517853
theorem B1715643 : Blo 1715058 1715643 := bstep (se 1 (by rfl) ⟨1286732, by rfl⟩ : syracuseStep 1715643 = 2573465) B2573465
theorem B1715719 : Blo 1715058 1715719 := bstep (se 1 (by rfl) ⟨1286789, by rfl⟩ : syracuseStep 1715719 = 2573579) B2573579
theorem B1715727 : Blo 1715058 1715727 := bstep (se 1 (by rfl) ⟨1286795, by rfl⟩ : syracuseStep 1715727 = 2573591) B2573591
theorem B15650333 : Blo 1715058 15650333 := bstep (se 3 (by rfl) ⟨2934437, by rfl⟩ : syracuseStep 15650333 = 5868875) B5868875
theorem B13209131 : Blo 1715058 13209131 := bstep (se 1 (by rfl) ⟨9906848, by rfl⟩ : syracuseStep 13209131 = 19813697) B19813697
theorem B1715771 : Blo 1715058 1715771 := bstep (se 1 (by rfl) ⟨1286828, by rfl⟩ : syracuseStep 1715771 = 2573657) B2573657
theorem B2895419 : Blo 1715058 2895419 := bstep (se 1 (by rfl) ⟨2171564, by rfl⟩ : syracuseStep 2895419 = 4343129) B4343129
theorem B9768509 : Blo 1715058 9768509 := bstep (se 3 (by rfl) ⟨1831595, by rfl⟩ : syracuseStep 9768509 = 3663191) B3663191
theorem B4886077 : Blo 1715058 4886077 := bstep (se 3 (by rfl) ⟨916139, by rfl⟩ : syracuseStep 4886077 = 1832279) B1832279
theorem B10997315 : Blo 1715058 10997315 := bstep (se 1 (by rfl) ⟨8247986, by rfl⟩ : syracuseStep 10997315 = 16495973) B16495973
theorem B1715847 : Blo 1715058 1715847 := bstep (se 1 (by rfl) ⟨1286885, by rfl⟩ : syracuseStep 1715847 = 2573771) B2573771
theorem B3862151 : Blo 1715058 3862151 := bstep (se 1 (by rfl) ⟨2896613, by rfl⟩ : syracuseStep 3862151 = 5793227) B5793227
theorem B1715855 : Blo 1715058 1715855 := bstep (se 1 (by rfl) ⟨1286891, by rfl⟩ : syracuseStep 1715855 = 2573783) B2573783
theorem B1715899 : Blo 1715058 1715899 := bstep (se 1 (by rfl) ⟨1286924, by rfl⟩ : syracuseStep 1715899 = 2573849) B2573849
theorem B5869313 : Blo 1715058 5869313 := bstep (se 2 (by rfl) ⟨2200992, by rfl⟩ : syracuseStep 5869313 = 4401985) B4401985
theorem B1715975 : Blo 1715058 1715975 := bstep (se 1 (by rfl) ⟨1286981, by rfl⟩ : syracuseStep 1715975 = 2573963) B2573963
theorem B1715983 : Blo 1715058 1715983 := bstep (se 1 (by rfl) ⟨1286987, by rfl⟩ : syracuseStep 1715983 = 2573975) B2573975
theorem B8687411 : Blo 1715058 8687411 := bstep (se 1 (by rfl) ⟨6515558, by rfl⟩ : syracuseStep 8687411 = 13031117) B13031117
theorem B1716027 : Blo 1715058 1716027 := bstep (se 1 (by rfl) ⟨1287020, by rfl⟩ : syracuseStep 1716027 = 2574041) B2574041
theorem B3862331 : Blo 1715058 3862331 := bstep (se 1 (by rfl) ⟨2896748, by rfl⟩ : syracuseStep 3862331 = 5793497) B5793497
theorem B1716103 : Blo 1715058 1716103 := bstep (se 1 (by rfl) ⟨1287077, by rfl⟩ : syracuseStep 1716103 = 2574155) B2574155
theorem B2936711 : Blo 1715058 2936711 := bstep (se 1 (by rfl) ⟨2202533, by rfl⟩ : syracuseStep 2936711 = 4405067) B4405067
theorem B1716111 : Blo 1715058 1716111 := bstep (se 1 (by rfl) ⟨1287083, by rfl⟩ : syracuseStep 1716111 = 2574167) B2574167
theorem B4886419 : Blo 1715058 4886419 := bstep (se 1 (by rfl) ⟨3664814, by rfl⟩ : syracuseStep 4886419 = 7329629) B7329629
theorem B3862457 : Blo 1715058 3862457 := bstep (se 2 (by rfl) ⟨1448421, by rfl⟩ : syracuseStep 3862457 = 2896843) B2896843
theorem B1716155 : Blo 1715058 1716155 := bstep (se 1 (by rfl) ⟨1287116, by rfl⟩ : syracuseStep 1716155 = 2574233) B2574233
theorem B2895817 : Blo 1715058 2895817 := bstep (se 2 (by rfl) ⟨1085931, by rfl⟩ : syracuseStep 2895817 = 2171863) B2171863
theorem B1716231 : Blo 1715058 1716231 := bstep (se 1 (by rfl) ⟨1287173, by rfl⟩ : syracuseStep 1716231 = 2574347) B2574347
theorem B1716239 : Blo 1715058 1716239 := bstep (se 1 (by rfl) ⟨1287179, by rfl⟩ : syracuseStep 1716239 = 2574359) B2574359
theorem B1716283 : Blo 1715058 1716283 := bstep (se 1 (by rfl) ⟨1287212, by rfl⟩ : syracuseStep 1716283 = 2574425) B2574425
theorem B8687735 : Blo 1715058 8687735 := bstep (se 1 (by rfl) ⟨6515801, by rfl⟩ : syracuseStep 8687735 = 13031603) B13031603
theorem B1716359 : Blo 1715058 1716359 := bstep (se 1 (by rfl) ⟨1287269, by rfl⟩ : syracuseStep 1716359 = 2574539) B2574539
theorem B1716367 : Blo 1715058 1716367 := bstep (se 1 (by rfl) ⟨1287275, by rfl⟩ : syracuseStep 1716367 = 2574551) B2574551
theorem B1716411 : Blo 1715058 1716411 := bstep (se 1 (by rfl) ⟨1287308, by rfl⟩ : syracuseStep 1716411 = 2574617) B2574617
theorem B45183221 : Blo 1715058 45183221 := bstep (se 5 (by rfl) ⟨2117963, by rfl⟩ : syracuseStep 45183221 = 4235927) B4235927
theorem B1716487 : Blo 1715058 1716487 := bstep (se 1 (by rfl) ⟨1287365, by rfl⟩ : syracuseStep 1716487 = 2574731) B2574731
theorem B1929487 : Blo 1715058 1929487 := bstep (se 1 (by rfl) ⟨1447115, by rfl⟩ : syracuseStep 1929487 = 2894231) B2894231
theorem B1716495 : Blo 1715058 1716495 := bstep (se 1 (by rfl) ⟨1287371, by rfl⟩ : syracuseStep 1716495 = 2574743) B2574743
theorem B3862799 : Blo 1715058 3862799 := bstep (se 1 (by rfl) ⟨2897099, by rfl⟩ : syracuseStep 3862799 = 5794199) B5794199
theorem B10989857 : Blo 1715058 10989857 := bstep (se 2 (by rfl) ⟨4121196, by rfl⟩ : syracuseStep 10989857 = 8242393) B8242393
theorem B3862817 : Blo 1715058 3862817 := bstep (se 2 (by rfl) ⟨1448556, by rfl⟩ : syracuseStep 3862817 = 2897113) B2897113
theorem B3092779 : Blo 1715058 3092779 := bstep (se 1 (by rfl) ⟨2319584, by rfl⟩ : syracuseStep 3092779 = 4639169) B4639169
theorem B1716539 : Blo 1715058 1716539 := bstep (se 1 (by rfl) ⟨1287404, by rfl⟩ : syracuseStep 1716539 = 2574809) B2574809
theorem B1716615 : Blo 1715058 1716615 := bstep (se 1 (by rfl) ⟨1287461, by rfl⟩ : syracuseStep 1716615 = 2574923) B2574923
theorem B1716623 : Blo 1715058 1716623 := bstep (se 1 (by rfl) ⟨1287467, by rfl⟩ : syracuseStep 1716623 = 2574935) B2574935
theorem B1716667 : Blo 1715058 1716667 := bstep (se 1 (by rfl) ⟨1287500, by rfl⟩ : syracuseStep 1716667 = 2575001) B2575001
theorem B3256777 : Blo 1715058 3256777 := bstep (se 2 (by rfl) ⟨1221291, by rfl⟩ : syracuseStep 3256777 = 2442583) B2442583
theorem B37097945 : Blo 1715058 37097945 := bstep (se 2 (by rfl) ⟨13911729, by rfl⟩ : syracuseStep 37097945 = 27823459) B27823459
theorem B1716743 : Blo 1715058 1716743 := bstep (se 1 (by rfl) ⟨1287557, by rfl⟩ : syracuseStep 1716743 = 2575115) B2575115
theorem B2060815 : Blo 1715058 2060815 := bstep (se 1 (by rfl) ⟨1545611, by rfl⟩ : syracuseStep 2060815 = 3091223) B3091223
theorem B1716751 : Blo 1715058 1716751 := bstep (se 1 (by rfl) ⟨1287563, by rfl⟩ : syracuseStep 1716751 = 2575127) B2575127
theorem B1716795 : Blo 1715058 1716795 := bstep (se 1 (by rfl) ⟨1287596, by rfl⟩ : syracuseStep 1716795 = 2575193) B2575193
theorem B6517367 : Blo 1715058 6517367 := bstep (se 1 (by rfl) ⟨4888025, by rfl⟩ : syracuseStep 6517367 = 9776051) B9776051
theorem B3863159 : Blo 1715058 3863159 := bstep (se 1 (by rfl) ⟨2897369, by rfl⟩ : syracuseStep 3863159 = 5794739) B5794739
theorem B2896519 : Blo 1715058 2896519 := bstep (se 1 (by rfl) ⟨2172389, by rfl⟩ : syracuseStep 2896519 = 4344779) B4344779
theorem B1716871 : Blo 1715058 1716871 := bstep (se 1 (by rfl) ⟨1287653, by rfl⟩ : syracuseStep 1716871 = 2575307) B2575307
theorem B1716879 : Blo 1715058 1716879 := bstep (se 1 (by rfl) ⟨1287659, by rfl⟩ : syracuseStep 1716879 = 2575319) B2575319
theorem B1716923 : Blo 1715058 1716923 := bstep (se 1 (by rfl) ⟨1287692, by rfl⟩ : syracuseStep 1716923 = 2575385) B2575385
theorem B20861657 : Blo 1715058 20861657 := bstep (se 2 (by rfl) ⟨7823121, by rfl⟩ : syracuseStep 20861657 = 15646243) B15646243
theorem B13030145 : Blo 1715058 13030145 := bstep (se 2 (by rfl) ⟨4886304, by rfl⟩ : syracuseStep 13030145 = 9772609) B9772609
theorem B1929991 : Blo 1715058 1929991 := bstep (se 1 (by rfl) ⟨1447493, by rfl⟩ : syracuseStep 1929991 = 2894987) B2894987
theorem B1716999 : Blo 1715058 1716999 := bstep (se 1 (by rfl) ⟨1287749, by rfl⟩ : syracuseStep 1716999 = 2575499) B2575499
theorem B4887307 : Blo 1715058 4887307 := bstep (se 1 (by rfl) ⟨3665480, by rfl⟩ : syracuseStep 4887307 = 7330961) B7330961
theorem B3666703 : Blo 1715058 3666703 := bstep (se 1 (by rfl) ⟨2750027, by rfl⟩ : syracuseStep 3666703 = 5500055) B5500055
theorem B1717007 : Blo 1715058 1717007 := bstep (se 1 (by rfl) ⟨1287755, by rfl⟩ : syracuseStep 1717007 = 2575511) B2575511
theorem B3863339 : Blo 1715058 3863339 := bstep (se 1 (by rfl) ⟨2897504, by rfl⟩ : syracuseStep 3863339 = 5795009) B5795009
theorem B5788475 : Blo 1715058 5788475 := bstep (se 1 (by rfl) ⟨4341356, by rfl⟩ : syracuseStep 5788475 = 8682713) B8682713
theorem B1717051 : Blo 1715058 1717051 := bstep (se 1 (by rfl) ⟨1287788, by rfl⟩ : syracuseStep 1717051 = 2575577) B2575577
theorem B19067723 : Blo 1715058 19067723 := bstep (se 1 (by rfl) ⟨14300792, by rfl⟩ : syracuseStep 19067723 = 28601585) B28601585
theorem B35222435 : Blo 1715058 35222435 := bstep (se 1 (by rfl) ⟨26416826, by rfl⟩ : syracuseStep 35222435 = 52833653) B52833653
theorem B1930171 : Blo 1715058 1930171 := bstep (se 1 (by rfl) ⟨1447628, by rfl⟩ : syracuseStep 1930171 = 2895257) B2895257
theorem B8688707 : Blo 1715058 8688707 := bstep (se 1 (by rfl) ⟨6516530, by rfl⟩ : syracuseStep 8688707 = 13033061) B13033061
theorem B3478663 : Blo 1715058 3478663 := bstep (se 1 (by rfl) ⟨2608997, by rfl⟩ : syracuseStep 3478663 = 5217995) B5217995
theorem B2610311 : Blo 1715058 2610311 := bstep (se 1 (by rfl) ⟨1957733, by rfl⟩ : syracuseStep 2610311 = 3915467) B3915467
theorem B3257491 : Blo 1715058 3257491 := bstep (se 1 (by rfl) ⟨2443118, by rfl⟩ : syracuseStep 3257491 = 4886237) B4886237
theorem B43971821 : Blo 1715058 43971821 := bstep (se 3 (by rfl) ⟨8244716, by rfl⟩ : syracuseStep 43971821 = 16489433) B16489433
theorem B4887809 : Blo 1715058 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B2897167 : Blo 1715058 2897167 := bstep (se 1 (by rfl) ⟨2172875, by rfl⟩ : syracuseStep 2897167 = 4345751) B4345751
theorem B5788961 : Blo 1715058 5788961 := bstep (se 2 (by rfl) ⟨2170860, by rfl⟩ : syracuseStep 5788961 = 4341721) B4341721
theorem B3478817 : Blo 1715058 3478817 := bstep (se 2 (by rfl) ⟨1304556, by rfl⟩ : syracuseStep 3478817 = 2609113) B2609113
theorem B2610475 : Blo 1715058 2610475 := bstep (se 1 (by rfl) ⟨1957856, by rfl⟩ : syracuseStep 2610475 = 3915713) B3915713
theorem B8689031 : Blo 1715058 8689031 := bstep (se 1 (by rfl) ⟨6516773, by rfl⟩ : syracuseStep 8689031 = 13033547) B13033547
theorem B1930639 : Blo 1715058 1930639 := bstep (se 1 (by rfl) ⟨1447979, by rfl⟩ : syracuseStep 1930639 = 2895959) B2895959
theorem B6518339 : Blo 1715058 6518339 := bstep (se 1 (by rfl) ⟨4888754, by rfl⟩ : syracuseStep 6518339 = 9777509) B9777509
theorem B4888151 : Blo 1715058 4888151 := bstep (se 1 (by rfl) ⟨3666113, by rfl⟩ : syracuseStep 4888151 = 7332227) B7332227
theorem B10999415 : Blo 1715058 10999415 := bstep (se 1 (by rfl) ⟨8249561, by rfl⟩ : syracuseStep 10999415 = 16499123) B16499123
theorem B5789555 : Blo 1715058 5789555 := bstep (se 1 (by rfl) ⟨4342166, by rfl⟩ : syracuseStep 5789555 = 8684333) B8684333
theorem B1931143 : Blo 1715058 1931143 := bstep (se 1 (by rfl) ⟨1448357, by rfl⟩ : syracuseStep 1931143 = 2896715) B2896715
theorem B5216147 : Blo 1715058 5216147 := bstep (se 1 (by rfl) ⟨3912110, by rfl⟩ : syracuseStep 5216147 = 7824221) B7824221
theorem B10442681 : Blo 1715058 10442681 := bstep (se 2 (by rfl) ⟨3916005, by rfl⟩ : syracuseStep 10442681 = 7832011) B7832011
theorem B1931323 : Blo 1715058 1931323 := bstep (se 1 (by rfl) ⟨1448492, by rfl⟩ : syracuseStep 1931323 = 2896985) B2896985
theorem B6789187 : Blo 1715058 6789187 := bstep (se 1 (by rfl) ⟨5091890, by rfl⟩ : syracuseStep 6789187 = 10183781) B10183781
theorem B3258569 : Blo 1715058 3258569 := bstep (se 2 (by rfl) ⟨1221963, by rfl⟩ : syracuseStep 3258569 = 2443927) B2443927
theorem B3479927 : Blo 1715058 3479927 := bstep (se 1 (by rfl) ⟨2609945, by rfl⟩ : syracuseStep 3479927 = 5219891) B5219891
theorem B4954625 : Blo 1715058 4954625 := bstep (se 2 (by rfl) ⟨1857984, by rfl⟩ : syracuseStep 4954625 = 3715969) B3715969
theorem B6519325 : Blo 1715058 6519325 := bstep (se 3 (by rfl) ⟨1222373, by rfl⟩ : syracuseStep 6519325 = 2444747) B2444747
theorem B5495339 : Blo 1715058 5495339 := bstep (se 1 (by rfl) ⟨4121504, by rfl⟩ : syracuseStep 5495339 = 8243009) B8243009
theorem B24730231 : Blo 1715058 24730231 := bstep (se 1 (by rfl) ⟨18547673, by rfl⟩ : syracuseStep 24730231 = 37095347) B37095347
theorem B8248331 : Blo 1715058 8248331 := bstep (se 1 (by rfl) ⟨6186248, by rfl⟩ : syracuseStep 8248331 = 12372497) B12372497
theorem B5217313 : Blo 1715058 5217313 := bstep (se 2 (by rfl) ⟨1956492, by rfl⟩ : syracuseStep 5217313 = 3912985) B3912985
theorem B3259435 : Blo 1715058 3259435 := bstep (se 1 (by rfl) ⟨2444576, by rfl⟩ : syracuseStep 3259435 = 4889153) B4889153
theorem B3259511 : Blo 1715058 3259511 := bstep (se 1 (by rfl) ⟨2444633, by rfl⟩ : syracuseStep 3259511 = 4889267) B4889267
theorem B11001005 : Blo 1715058 11001005 := bstep (se 3 (by rfl) ⟨2062688, by rfl⟩ : syracuseStep 11001005 = 4125377) B4125377
theorem B2383033 : Blo 1715058 2383033 := bstep (se 2 (by rfl) ⟨893637, by rfl⟩ : syracuseStep 2383033 = 1787275) B1787275
theorem B1957127 : Blo 1715058 1957127 := bstep (se 1 (by rfl) ⟨1467845, by rfl⟩ : syracuseStep 1957127 = 2935691) B2935691
theorem B7331219 : Blo 1715058 7331219 := bstep (se 1 (by rfl) ⟨5498414, by rfl⟩ : syracuseStep 7331219 = 10996829) B10996829
theorem B41729539 : Blo 1715058 41729539 := bstep (se 1 (by rfl) ⟨31297154, by rfl⟩ : syracuseStep 41729539 = 62594309) B62594309
theorem B8683037 : Blo 1715058 8683037 := bstep (se 3 (by rfl) ⟨1628069, by rfl⟩ : syracuseStep 8683037 = 3256139) B3256139
theorem B18546205 : Blo 1715058 18546205 := bstep (se 3 (by rfl) ⟨3477413, by rfl⟩ : syracuseStep 18546205 = 6954827) B6954827
theorem B8249177 : Blo 1715058 8249177 := bstep (se 2 (by rfl) ⟨3093441, by rfl⟩ : syracuseStep 8249177 = 6186883) B6186883
theorem B2170795 : Blo 1715058 2170795 := bstep (se 1 (by rfl) ⟨1628096, by rfl⟩ : syracuseStep 2170795 = 3256193) B3256193
theorem B3915721 : Blo 1715058 3915721 := bstep (se 2 (by rfl) ⟨1468395, by rfl⟩ : syracuseStep 3915721 = 2936791) B2936791
theorem B21995549 : Blo 1715058 21995549 := bstep (se 3 (by rfl) ⟨4124165, by rfl⟩ : syracuseStep 21995549 = 8248331) B8248331
theorem B5791823 : Blo 1715058 5791823 := bstep (se 1 (by rfl) ⟨4343867, by rfl⟩ : syracuseStep 5791823 = 8687735) B8687735
theorem B8806481 : Blo 1715058 8806481 := bstep (se 2 (by rfl) ⟨3302430, by rfl⟩ : syracuseStep 8806481 = 6604861) B6604861
theorem B9052249 : Blo 1715058 9052249 := bstep (se 2 (by rfl) ⟨3394593, by rfl⟩ : syracuseStep 9052249 = 6789187) B6789187
theorem B30122147 : Blo 1715058 30122147 := bstep (se 1 (by rfl) ⟨22591610, by rfl⟩ : syracuseStep 30122147 = 45183221) B45183221
theorem B24731963 : Blo 1715058 24731963 := bstep (se 1 (by rfl) ⟨18548972, by rfl⟩ : syracuseStep 24731963 = 37097945) B37097945
theorem B10993981 : Blo 1715058 10993981 := bstep (se 3 (by rfl) ⟨2061371, by rfl⟩ : syracuseStep 10993981 = 4122743) B4122743
theorem B2572649 : Blo 1715058 2572649 := bstep (se 2 (by rfl) ⟨964743, by rfl⟩ : syracuseStep 2572649 = 1929487) B1929487
theorem B2572727 : Blo 1715058 2572727 := bstep (se 1 (by rfl) ⟨1929545, by rfl⟩ : syracuseStep 2572727 = 3859091) B3859091
theorem B5792201 : Blo 1715058 5792201 := bstep (se 2 (by rfl) ⟨2172075, by rfl⟩ : syracuseStep 5792201 = 4344151) B4344151
theorem B2572763 : Blo 1715058 2572763 := bstep (se 1 (by rfl) ⟨1929572, by rfl⟩ : syracuseStep 2572763 = 3859145) B3859145
theorem B11149805 : Blo 1715058 11149805 := bstep (se 3 (by rfl) ⟨2090588, by rfl⟩ : syracuseStep 11149805 = 4181177) B4181177
theorem B3858983 : Blo 1715058 3858983 := bstep (se 1 (by rfl) ⟨2894237, by rfl⟩ : syracuseStep 3858983 = 5788475) B5788475
theorem B4342369 : Blo 1715058 4342369 := bstep (se 2 (by rfl) ⟨1628388, by rfl⟩ : syracuseStep 4342369 = 3256777) B3256777
theorem B5219005 : Blo 1715058 5219005 := bstep (se 3 (by rfl) ⟨978563, by rfl⟩ : syracuseStep 5219005 = 1957127) B1957127
theorem B8692433 : Blo 1715058 8692433 := bstep (se 2 (by rfl) ⟨3259662, by rfl⟩ : syracuseStep 8692433 = 6519325) B6519325
theorem B5792471 : Blo 1715058 5792471 := bstep (se 1 (by rfl) ⟨4344353, by rfl⟩ : syracuseStep 5792471 = 8688707) B8688707
theorem B8241949 : Blo 1715058 8241949 := bstep (se 3 (by rfl) ⟨1545365, by rfl⟩ : syracuseStep 8241949 = 3090731) B3090731
theorem B32973641 : Blo 1715058 32973641 := bstep (se 2 (by rfl) ⟨12365115, by rfl⟩ : syracuseStep 32973641 = 24730231) B24730231
theorem B3859307 : Blo 1715058 3859307 := bstep (se 1 (by rfl) ⟨2894480, by rfl⟩ : syracuseStep 3859307 = 5788961) B5788961
theorem B2319211 : Blo 1715058 2319211 := bstep (se 1 (by rfl) ⟨1739408, by rfl⟩ : syracuseStep 2319211 = 3478817) B3478817
theorem B3859361 : Blo 1715058 3859361 := bstep (se 2 (by rfl) ⟨1447260, by rfl⟩ : syracuseStep 3859361 = 2894521) B2894521
theorem B2573231 : Blo 1715058 2573231 := bstep (se 1 (by rfl) ⟨1929923, by rfl⟩ : syracuseStep 2573231 = 3859847) B3859847
theorem B5792687 : Blo 1715058 5792687 := bstep (se 1 (by rfl) ⟨4344515, by rfl⟩ : syracuseStep 5792687 = 8689031) B8689031
theorem B2573321 : Blo 1715058 2573321 := bstep (se 2 (by rfl) ⟨964995, by rfl⟩ : syracuseStep 2573321 = 1929991) B1929991
theorem B2573351 : Blo 1715058 2573351 := bstep (se 1 (by rfl) ⟨1930013, by rfl⟩ : syracuseStep 2573351 = 3860027) B3860027
theorem B5497913 : Blo 1715058 5497913 := bstep (se 2 (by rfl) ⟨2061717, by rfl⟩ : syracuseStep 5497913 = 4123435) B4123435
theorem B7332943 : Blo 1715058 7332943 := bstep (se 1 (by rfl) ⟨5499707, by rfl⟩ : syracuseStep 7332943 = 10999415) B10999415
theorem B2573435 : Blo 1715058 2573435 := bstep (se 1 (by rfl) ⟨1930076, by rfl⟩ : syracuseStep 2573435 = 3860153) B3860153
theorem B37119221 : Blo 1715058 37119221 := bstep (se 5 (by rfl) ⟨1739963, by rfl⟩ : syracuseStep 37119221 = 3479927) B3479927
theorem B3859703 : Blo 1715058 3859703 := bstep (se 1 (by rfl) ⟨2894777, by rfl⟩ : syracuseStep 3859703 = 5789555) B5789555
theorem B2573561 : Blo 1715058 2573561 := bstep (se 2 (by rfl) ⟨965085, by rfl⟩ : syracuseStep 2573561 = 1930171) B1930171
theorem B2573663 : Blo 1715058 2573663 := bstep (se 1 (by rfl) ⟨1930247, by rfl⟩ : syracuseStep 2573663 = 3860495) B3860495
theorem B2573675 : Blo 1715058 2573675 := bstep (se 1 (by rfl) ⟨1930256, by rfl⟩ : syracuseStep 2573675 = 3860513) B3860513
theorem B4638077 : Blo 1715058 4638077 := bstep (se 3 (by rfl) ⟨869639, by rfl⟩ : syracuseStep 4638077 = 1739279) B1739279
theorem B6956417 : Blo 1715058 6956417 := bstep (se 2 (by rfl) ⟨2608656, by rfl⟩ : syracuseStep 6956417 = 5217313) B5217313
theorem B4638217 : Blo 1715058 4638217 := bstep (se 2 (by rfl) ⟨1739331, by rfl⟩ : syracuseStep 4638217 = 3478663) B3478663
theorem B4343321 : Blo 1715058 4343321 := bstep (se 2 (by rfl) ⟨1628745, by rfl⟩ : syracuseStep 4343321 = 3257491) B3257491
theorem B2573903 : Blo 1715058 2573903 := bstep (se 1 (by rfl) ⟨1930427, by rfl⟩ : syracuseStep 2573903 = 3860855) B3860855
theorem B3303083 : Blo 1715058 3303083 := bstep (se 1 (by rfl) ⟨2477312, by rfl⟩ : syracuseStep 3303083 = 4954625) B4954625
theorem B3663559 : Blo 1715058 3663559 := bstep (se 1 (by rfl) ⟨2747669, by rfl⟩ : syracuseStep 3663559 = 5495339) B5495339
theorem B2574023 : Blo 1715058 2574023 := bstep (se 1 (by rfl) ⟨1930517, by rfl⟩ : syracuseStep 2574023 = 3861035) B3861035
theorem B8685305 : Blo 1715058 8685305 := bstep (se 2 (by rfl) ⟨3256989, by rfl⟩ : syracuseStep 8685305 = 6513979) B6513979
theorem B3860297 : Blo 1715058 3860297 := bstep (se 2 (by rfl) ⟨1447611, by rfl⟩ : syracuseStep 3860297 = 2895223) B2895223
theorem B2574185 : Blo 1715058 2574185 := bstep (se 2 (by rfl) ⟨965319, by rfl⟩ : syracuseStep 2574185 = 1930639) B1930639
theorem B2574263 : Blo 1715058 2574263 := bstep (se 1 (by rfl) ⟨1930697, by rfl⟩ : syracuseStep 2574263 = 3861395) B3861395
theorem B2574299 : Blo 1715058 2574299 := bstep (se 1 (by rfl) ⟨1930724, by rfl⟩ : syracuseStep 2574299 = 3861449) B3861449
theorem B4343827 : Blo 1715058 4343827 := bstep (se 1 (by rfl) ⟨3257870, by rfl⟩ : syracuseStep 4343827 = 6515741) B6515741
theorem B2173007 : Blo 1715058 2173007 := bstep (se 1 (by rfl) ⟨1629755, by rfl⟩ : syracuseStep 2173007 = 3259511) B3259511
theorem B6514769 : Blo 1715058 6514769 := bstep (se 2 (by rfl) ⟨2443038, by rfl⟩ : syracuseStep 6514769 = 4886077) B4886077
theorem B7334003 : Blo 1715058 7334003 := bstep (se 1 (by rfl) ⟨5500502, by rfl⟩ : syracuseStep 7334003 = 11001005) B11001005
theorem B8685953 : Blo 1715058 8685953 := bstep (se 2 (by rfl) ⟨3257232, by rfl⟩ : syracuseStep 8685953 = 6514465) B6514465
theorem B20883845 : Blo 1715058 20883845 := bstep (se 4 (by rfl) ⟨1957860, by rfl⟩ : syracuseStep 20883845 = 3915721) B3915721
theorem B2574767 : Blo 1715058 2574767 := bstep (se 1 (by rfl) ⟨1931075, by rfl⟩ : syracuseStep 2574767 = 3862151) B3862151
theorem B2574857 : Blo 1715058 2574857 := bstep (se 2 (by rfl) ⟨965571, by rfl⟩ : syracuseStep 2574857 = 1931143) B1931143
theorem B6515225 : Blo 1715058 6515225 := bstep (se 2 (by rfl) ⟨2443209, by rfl⟩ : syracuseStep 6515225 = 4886419) B4886419
theorem B2574887 : Blo 1715058 2574887 := bstep (se 1 (by rfl) ⟨1931165, by rfl⟩ : syracuseStep 2574887 = 3862331) B3862331
theorem B2894393 : Blo 1715058 2894393 := bstep (se 2 (by rfl) ⟨1085397, by rfl⟩ : syracuseStep 2894393 = 2170795) B2170795
theorem B5499451 : Blo 1715058 5499451 := bstep (se 1 (by rfl) ⟨4124588, by rfl⟩ : syracuseStep 5499451 = 8249177) B8249177
theorem B3861089 : Blo 1715058 3861089 := bstep (se 2 (by rfl) ⟨1447908, by rfl⟩ : syracuseStep 3861089 = 2895817) B2895817
theorem B2574971 : Blo 1715058 2574971 := bstep (se 1 (by rfl) ⟨1931228, by rfl⟩ : syracuseStep 2574971 = 3862457) B3862457
theorem B37128905 : Blo 1715058 37128905 := bstep (se 2 (by rfl) ⟨13923339, by rfl⟩ : syracuseStep 37128905 = 27846679) B27846679
theorem B3091193 : Blo 1715058 3091193 := bstep (se 2 (by rfl) ⟨1159197, by rfl⟩ : syracuseStep 3091193 = 2318395) B2318395
theorem B5573369 : Blo 1715058 5573369 := bstep (se 2 (by rfl) ⟨2090013, by rfl⟩ : syracuseStep 5573369 = 4180027) B4180027
theorem B2575097 : Blo 1715058 2575097 := bstep (se 2 (by rfl) ⟨965661, by rfl⟩ : syracuseStep 2575097 = 1931323) B1931323
theorem B2575199 : Blo 1715058 2575199 := bstep (se 1 (by rfl) ⟨1931399, by rfl⟩ : syracuseStep 2575199 = 3862799) B3862799
theorem B7326571 : Blo 1715058 7326571 := bstep (se 1 (by rfl) ⟨5494928, by rfl⟩ : syracuseStep 7326571 = 10989857) B10989857
theorem B2575211 : Blo 1715058 2575211 := bstep (se 1 (by rfl) ⟨1931408, by rfl⟩ : syracuseStep 2575211 = 3862817) B3862817
theorem B1715067 : Blo 1715058 1715067 := bstep (se 1 (by rfl) ⟨1286300, by rfl⟩ : syracuseStep 1715067 = 2572601) B2572601
theorem B2747279 : Blo 1715058 2747279 := bstep (se 1 (by rfl) ⟨2060459, by rfl⟩ : syracuseStep 2747279 = 4120919) B4120919
theorem B1715119 : Blo 1715058 1715119 := bstep (se 1 (by rfl) ⟨1286339, by rfl⟩ : syracuseStep 1715119 = 2572679) B2572679
theorem B13036463 : Blo 1715058 13036463 := bstep (se 1 (by rfl) ⟨9777347, by rfl⟩ : syracuseStep 13036463 = 19554695) B19554695
theorem B3861431 : Blo 1715058 3861431 := bstep (se 1 (by rfl) ⟨2896073, by rfl⟩ : syracuseStep 3861431 = 5792147) B5792147
theorem B1715143 : Blo 1715058 1715143 := bstep (se 1 (by rfl) ⟨1286357, by rfl⟩ : syracuseStep 1715143 = 2572715) B2572715
theorem B1715163 : Blo 1715058 1715163 := bstep (se 1 (by rfl) ⟨1286372, by rfl⟩ : syracuseStep 1715163 = 2572745) B2572745
theorem B1715239 : Blo 1715058 1715239 := bstep (se 1 (by rfl) ⟨1286429, by rfl⟩ : syracuseStep 1715239 = 2572859) B2572859
theorem B4123705 : Blo 1715058 4123705 := bstep (se 2 (by rfl) ⟨1546389, by rfl⟩ : syracuseStep 4123705 = 3092779) B3092779
theorem B1715279 : Blo 1715058 1715279 := bstep (se 1 (by rfl) ⟨1286459, by rfl⟩ : syracuseStep 1715279 = 2572919) B2572919
theorem B4344911 : Blo 1715058 4344911 := bstep (se 1 (by rfl) ⟨3258683, by rfl⟩ : syracuseStep 4344911 = 6517367) B6517367
theorem B2575439 : Blo 1715058 2575439 := bstep (se 1 (by rfl) ⟨1931579, by rfl⟩ : syracuseStep 2575439 = 3863159) B3863159
theorem B1715295 : Blo 1715058 1715295 := bstep (se 1 (by rfl) ⟨1286471, by rfl⟩ : syracuseStep 1715295 = 2572943) B2572943
theorem B1715323 : Blo 1715058 1715323 := bstep (se 1 (by rfl) ⟨1286492, by rfl⟩ : syracuseStep 1715323 = 2572985) B2572985
theorem B8686763 : Blo 1715058 8686763 := bstep (se 1 (by rfl) ⟨6515072, by rfl⟩ : syracuseStep 8686763 = 13030145) B13030145
theorem B1715375 : Blo 1715058 1715375 := bstep (se 1 (by rfl) ⟨1286531, by rfl⟩ : syracuseStep 1715375 = 2573063) B2573063
theorem B1715399 : Blo 1715058 1715399 := bstep (se 1 (by rfl) ⟨1286549, by rfl⟩ : syracuseStep 1715399 = 2573099) B2573099
theorem B2575559 : Blo 1715058 2575559 := bstep (se 1 (by rfl) ⟨1931669, by rfl⟩ : syracuseStep 2575559 = 3863339) B3863339
theorem B1715419 : Blo 1715058 1715419 := bstep (se 1 (by rfl) ⟨1286564, by rfl⟩ : syracuseStep 1715419 = 2573129) B2573129
theorem B2895095 : Blo 1715058 2895095 := bstep (se 1 (by rfl) ⟨2171321, by rfl⟩ : syracuseStep 2895095 = 4342643) B4342643
theorem B5795063 : Blo 1715058 5795063 := bstep (se 1 (by rfl) ⟨4346297, by rfl⟩ : syracuseStep 5795063 = 8692595) B8692595
theorem B23481623 : Blo 1715058 23481623 := bstep (se 1 (by rfl) ⟨17611217, by rfl⟩ : syracuseStep 23481623 = 35222435) B35222435
theorem B1715495 : Blo 1715058 1715495 := bstep (se 1 (by rfl) ⟨1286621, by rfl⟩ : syracuseStep 1715495 = 2573243) B2573243
theorem B1715535 : Blo 1715058 1715535 := bstep (se 1 (by rfl) ⟨1286651, by rfl⟩ : syracuseStep 1715535 = 2573303) B2573303
theorem B1715551 : Blo 1715058 1715551 := bstep (se 1 (by rfl) ⟨1286663, by rfl⟩ : syracuseStep 1715551 = 2573327) B2573327
theorem B2747753 : Blo 1715058 2747753 := bstep (se 2 (by rfl) ⟨1030407, by rfl⟩ : syracuseStep 2747753 = 2060815) B2060815
theorem B1715579 : Blo 1715058 1715579 := bstep (se 1 (by rfl) ⟨1286684, by rfl⟩ : syracuseStep 1715579 = 2573369) B2573369
theorem B2747791 : Blo 1715058 2747791 := bstep (se 1 (by rfl) ⟨2060843, by rfl⟩ : syracuseStep 2747791 = 4121687) B4121687
theorem B1715631 : Blo 1715058 1715631 := bstep (se 1 (by rfl) ⟨1286723, by rfl⟩ : syracuseStep 1715631 = 2573447) B2573447
theorem B1715655 : Blo 1715058 1715655 := bstep (se 1 (by rfl) ⟨1286741, by rfl⟩ : syracuseStep 1715655 = 2573483) B2573483
theorem B1715675 : Blo 1715058 1715675 := bstep (se 1 (by rfl) ⟨1286756, by rfl⟩ : syracuseStep 1715675 = 2573513) B2573513
theorem B29314547 : Blo 1715058 29314547 := bstep (se 1 (by rfl) ⟨21985910, by rfl⟩ : syracuseStep 29314547 = 43971821) B43971821
theorem B3862025 : Blo 1715058 3862025 := bstep (se 2 (by rfl) ⟨1448259, by rfl⟩ : syracuseStep 3862025 = 2896519) B2896519
theorem B1715751 : Blo 1715058 1715751 := bstep (se 1 (by rfl) ⟨1286813, by rfl⟩ : syracuseStep 1715751 = 2573627) B2573627
theorem B1715791 : Blo 1715058 1715791 := bstep (se 1 (by rfl) ⟨1286843, by rfl⟩ : syracuseStep 1715791 = 2573687) B2573687
theorem B2895439 : Blo 1715058 2895439 := bstep (se 1 (by rfl) ⟨2171579, by rfl⟩ : syracuseStep 2895439 = 4343159) B4343159
theorem B1715807 : Blo 1715058 1715807 := bstep (se 1 (by rfl) ⟨1286855, by rfl⟩ : syracuseStep 1715807 = 2573711) B2573711
theorem B12365435 : Blo 1715058 12365435 := bstep (se 1 (by rfl) ⟨9274076, by rfl⟩ : syracuseStep 12365435 = 18548153) B18548153
theorem B1715835 : Blo 1715058 1715835 := bstep (se 1 (by rfl) ⟨1286876, by rfl⟩ : syracuseStep 1715835 = 2573753) B2573753
theorem B8687249 : Blo 1715058 8687249 := bstep (se 2 (by rfl) ⟨3257718, by rfl⟩ : syracuseStep 8687249 = 6515437) B6515437
theorem B1715887 : Blo 1715058 1715887 := bstep (se 1 (by rfl) ⟨1286915, by rfl⟩ : syracuseStep 1715887 = 2573831) B2573831
theorem B6516409 : Blo 1715058 6516409 := bstep (se 2 (by rfl) ⟨2443653, by rfl⟩ : syracuseStep 6516409 = 4887307) B4887307
theorem B1715911 : Blo 1715058 1715911 := bstep (se 1 (by rfl) ⟨1286933, by rfl⟩ : syracuseStep 1715911 = 2573867) B2573867
theorem B4345559 : Blo 1715058 4345559 := bstep (se 1 (by rfl) ⟨3259169, by rfl⟩ : syracuseStep 4345559 = 6518339) B6518339
theorem B1715931 : Blo 1715058 1715931 := bstep (se 1 (by rfl) ⟨1286948, by rfl⟩ : syracuseStep 1715931 = 2573897) B2573897
theorem B1716007 : Blo 1715058 1716007 := bstep (se 1 (by rfl) ⟨1287005, by rfl⟩ : syracuseStep 1716007 = 2574011) B2574011
theorem B2895689 : Blo 1715058 2895689 := bstep (se 2 (by rfl) ⟨1085883, by rfl⟩ : syracuseStep 2895689 = 2171767) B2171767
theorem B1716047 : Blo 1715058 1716047 := bstep (se 1 (by rfl) ⟨1287035, by rfl⟩ : syracuseStep 1716047 = 2574071) B2574071
theorem B1716063 : Blo 1715058 1716063 := bstep (se 1 (by rfl) ⟨1287047, by rfl⟩ : syracuseStep 1716063 = 2574095) B2574095
theorem B3862367 : Blo 1715058 3862367 := bstep (se 1 (by rfl) ⟨2896775, by rfl⟩ : syracuseStep 3862367 = 5793551) B5793551
theorem B1716091 : Blo 1715058 1716091 := bstep (se 1 (by rfl) ⟨1287068, by rfl⟩ : syracuseStep 1716091 = 2574137) B2574137
theorem B1716143 : Blo 1715058 1716143 := bstep (se 1 (by rfl) ⟨1287107, by rfl⟩ : syracuseStep 1716143 = 2574215) B2574215
theorem B3477431 : Blo 1715058 3477431 := bstep (se 1 (by rfl) ⟨2608073, by rfl⟩ : syracuseStep 3477431 = 5216147) B5216147
theorem B1716167 : Blo 1715058 1716167 := bstep (se 1 (by rfl) ⟨1287125, by rfl⟩ : syracuseStep 1716167 = 2574251) B2574251
theorem B1716187 : Blo 1715058 1716187 := bstep (se 1 (by rfl) ⟨1287140, by rfl⟩ : syracuseStep 1716187 = 2574281) B2574281
theorem B3862547 : Blo 1715058 3862547 := bstep (se 1 (by rfl) ⟨2896910, by rfl⟩ : syracuseStep 3862547 = 5793821) B5793821
theorem B3092519 : Blo 1715058 3092519 := bstep (se 1 (by rfl) ⟨2319389, by rfl⟩ : syracuseStep 3092519 = 4638779) B4638779
theorem B1716263 : Blo 1715058 1716263 := bstep (se 1 (by rfl) ⟨1287197, by rfl⟩ : syracuseStep 1716263 = 2574395) B2574395
theorem B4345913 : Blo 1715058 4345913 := bstep (se 2 (by rfl) ⟨1629717, by rfl⟩ : syracuseStep 4345913 = 3259435) B3259435
theorem B1716303 : Blo 1715058 1716303 := bstep (se 1 (by rfl) ⟨1287227, by rfl⟩ : syracuseStep 1716303 = 2574455) B2574455
theorem B1716319 : Blo 1715058 1716319 := bstep (se 1 (by rfl) ⟨1287239, by rfl⟩ : syracuseStep 1716319 = 2574479) B2574479
theorem B1716347 : Blo 1715058 1716347 := bstep (se 1 (by rfl) ⟨1287260, by rfl⟩ : syracuseStep 1716347 = 2574521) B2574521
theorem B1716399 : Blo 1715058 1716399 := bstep (se 1 (by rfl) ⟨1287299, by rfl⟩ : syracuseStep 1716399 = 2574599) B2574599
theorem B3256519 : Blo 1715058 3256519 := bstep (se 1 (by rfl) ⟨2442389, by rfl⟩ : syracuseStep 3256519 = 4884779) B4884779
theorem B1716423 : Blo 1715058 1716423 := bstep (se 1 (by rfl) ⟨1287317, by rfl⟩ : syracuseStep 1716423 = 2574635) B2574635
theorem B1716443 : Blo 1715058 1716443 := bstep (se 1 (by rfl) ⟨1287332, by rfl⟩ : syracuseStep 1716443 = 2574665) B2574665
theorem B13922533 : Blo 1715058 13922533 := bstep (se 4 (by rfl) ⟨1305237, by rfl⟩ : syracuseStep 13922533 = 2610475) B2610475
theorem B2896121 : Blo 1715058 2896121 := bstep (se 2 (by rfl) ⟨1086045, by rfl⟩ : syracuseStep 2896121 = 2172091) B2172091
theorem B1716519 : Blo 1715058 1716519 := bstep (se 1 (by rfl) ⟨1287389, by rfl⟩ : syracuseStep 1716519 = 2574779) B2574779
theorem B1716559 : Blo 1715058 1716559 := bstep (se 1 (by rfl) ⟨1287419, by rfl⟩ : syracuseStep 1716559 = 2574839) B2574839
theorem B1716575 : Blo 1715058 1716575 := bstep (se 1 (by rfl) ⟨1287431, by rfl⟩ : syracuseStep 1716575 = 2574863) B2574863
theorem B3862889 : Blo 1715058 3862889 := bstep (se 2 (by rfl) ⟨1448583, by rfl⟩ : syracuseStep 3862889 = 2897167) B2897167
theorem B1716603 : Blo 1715058 1716603 := bstep (se 1 (by rfl) ⟨1287452, by rfl⟩ : syracuseStep 1716603 = 2574905) B2574905
theorem B2896303 : Blo 1715058 2896303 := bstep (se 1 (by rfl) ⟨2172227, by rfl⟩ : syracuseStep 2896303 = 4344455) B4344455
theorem B1716655 : Blo 1715058 1716655 := bstep (se 1 (by rfl) ⟨1287491, by rfl⟩ : syracuseStep 1716655 = 2574983) B2574983
theorem B1716679 : Blo 1715058 1716679 := bstep (se 1 (by rfl) ⟨1287509, by rfl⟩ : syracuseStep 1716679 = 2575019) B2575019
theorem B1716699 : Blo 1715058 1716699 := bstep (se 1 (by rfl) ⟨1287524, by rfl⟩ : syracuseStep 1716699 = 2575049) B2575049
theorem B2896391 : Blo 1715058 2896391 := bstep (se 1 (by rfl) ⟨2172293, by rfl⟩ : syracuseStep 2896391 = 4344587) B4344587
theorem B1716775 : Blo 1715058 1716775 := bstep (se 1 (by rfl) ⟨1287581, by rfl⟩ : syracuseStep 1716775 = 2575163) B2575163
theorem B1716815 : Blo 1715058 1716815 := bstep (se 1 (by rfl) ⟨1287611, by rfl⟩ : syracuseStep 1716815 = 2575223) B2575223
theorem B1716831 : Blo 1715058 1716831 := bstep (se 1 (by rfl) ⟨1287623, by rfl⟩ : syracuseStep 1716831 = 2575247) B2575247
theorem B1716859 : Blo 1715058 1716859 := bstep (se 1 (by rfl) ⟨1287644, by rfl⟩ : syracuseStep 1716859 = 2575289) B2575289
theorem B1716911 : Blo 1715058 1716911 := bstep (se 1 (by rfl) ⟨1287683, by rfl⟩ : syracuseStep 1716911 = 2575367) B2575367
theorem B1716935 : Blo 1715058 1716935 := bstep (se 1 (by rfl) ⟨1287701, by rfl⟩ : syracuseStep 1716935 = 2575403) B2575403
theorem B24728273 : Blo 1715058 24728273 := bstep (se 2 (by rfl) ⟨9273102, by rfl⟩ : syracuseStep 24728273 = 18546205) B18546205
theorem B1716955 : Blo 1715058 1716955 := bstep (se 1 (by rfl) ⟨1287716, by rfl⟩ : syracuseStep 1716955 = 2575433) B2575433
theorem B3257081 : Blo 1715058 3257081 := bstep (se 2 (by rfl) ⟨1221405, by rfl⟩ : syracuseStep 3257081 = 2442811) B2442811
theorem B3093241 : Blo 1715058 3093241 := bstep (se 2 (by rfl) ⟨1159965, by rfl⟩ : syracuseStep 3093241 = 2319931) B2319931
theorem B1717031 : Blo 1715058 1717031 := bstep (se 1 (by rfl) ⟨1287773, by rfl⟩ : syracuseStep 1717031 = 2575547) B2575547
theorem B16495433 : Blo 1715058 16495433 := bstep (se 2 (by rfl) ⟨6185787, by rfl⟩ : syracuseStep 16495433 = 12371575) B12371575
theorem B2896735 : Blo 1715058 2896735 := bstep (se 1 (by rfl) ⟨2172551, by rfl⟩ : syracuseStep 2896735 = 4345103) B4345103
theorem B3257263 : Blo 1715058 3257263 := bstep (se 1 (by rfl) ⟨2442947, by rfl⟩ : syracuseStep 3257263 = 4885895) B4885895
theorem B4887479 : Blo 1715058 4887479 := bstep (se 1 (by rfl) ⟨3665609, by rfl⟩ : syracuseStep 4887479 = 7331219) B7331219
theorem B2749367 : Blo 1715058 2749367 := bstep (se 1 (by rfl) ⟨2062025, by rfl⟩ : syracuseStep 2749367 = 4124051) B4124051
theorem B2896823 : Blo 1715058 2896823 := bstep (se 1 (by rfl) ⟨2172617, by rfl⟩ : syracuseStep 2896823 = 4345235) B4345235
theorem B5788691 : Blo 1715058 5788691 := bstep (se 1 (by rfl) ⟨4341518, by rfl⟩ : syracuseStep 5788691 = 8683037) B8683037
theorem B10433555 : Blo 1715058 10433555 := bstep (se 1 (by rfl) ⟨7825166, by rfl⟩ : syracuseStep 10433555 = 15650333) B15650333
theorem B1930279 : Blo 1715058 1930279 := bstep (se 1 (by rfl) ⟨1447709, by rfl⟩ : syracuseStep 1930279 = 2895419) B2895419
theorem B3912875 : Blo 1715058 3912875 := bstep (se 1 (by rfl) ⟨2934656, by rfl⟩ : syracuseStep 3912875 = 5869313) B5869313
theorem B5789015 : Blo 1715058 5789015 := bstep (se 1 (by rfl) ⟨4341761, by rfl⟩ : syracuseStep 5789015 = 8683523) B8683523
theorem B6518141 : Blo 1715058 6518141 := bstep (se 3 (by rfl) ⟨1222151, by rfl⟩ : syracuseStep 6518141 = 2444303) B2444303
theorem B24729077 : Blo 1715058 24729077 := bstep (se 5 (by rfl) ⟨1159175, by rfl⟩ : syracuseStep 24729077 = 2318351) B2318351
theorem B6272521 : Blo 1715058 6272521 := bstep (se 2 (by rfl) ⟨2352195, by rfl⟩ : syracuseStep 6272521 = 4704391) B4704391
theorem B2897417 : Blo 1715058 2897417 := bstep (se 2 (by rfl) ⟨1086531, by rfl⟩ : syracuseStep 2897417 = 2173063) B2173063
theorem B6960829 : Blo 1715058 6960829 := bstep (se 3 (by rfl) ⟨1305155, by rfl⟩ : syracuseStep 6960829 = 2610311) B2610311
theorem B6182615 : Blo 1715058 6182615 := bstep (se 1 (by rfl) ⟨4636961, by rfl⟩ : syracuseStep 6182615 = 9273923) B9273923
theorem B12375841 : Blo 1715058 12375841 := bstep (se 2 (by rfl) ⟨4640940, by rfl⟩ : syracuseStep 12375841 = 9281881) B9281881
theorem B13907771 : Blo 1715058 13907771 := bstep (se 1 (by rfl) ⟨10430828, by rfl⟩ : syracuseStep 13907771 = 20861657) B20861657
theorem B8689517 : Blo 1715058 8689517 := bstep (se 3 (by rfl) ⟨1629284, by rfl⟩ : syracuseStep 8689517 = 3258569) B3258569
theorem B12711815 : Blo 1715058 12711815 := bstep (se 1 (by rfl) ⟨9533861, by rfl⟩ : syracuseStep 12711815 = 19067723) B19067723
theorem B4888583 : Blo 1715058 4888583 := bstep (se 1 (by rfl) ⟨3666437, by rfl⟩ : syracuseStep 4888583 = 7332875) B7332875
theorem B8689679 : Blo 1715058 8689679 := bstep (se 1 (by rfl) ⟨6517259, by rfl⟩ : syracuseStep 8689679 = 13034519) B13034519
theorem B3258539 : Blo 1715058 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B17611057 : Blo 1715058 17611057 := bstep (se 2 (by rfl) ⟨6604146, by rfl⟩ : syracuseStep 17611057 = 13208293) B13208293
theorem B4888937 : Blo 1715058 4888937 := bstep (se 2 (by rfl) ⟨1833351, by rfl⟩ : syracuseStep 4888937 = 3666703) B3666703
theorem B5790095 : Blo 1715058 5790095 := bstep (se 1 (by rfl) ⟨4342571, by rfl⟩ : syracuseStep 5790095 = 8685143) B8685143
theorem B3258767 : Blo 1715058 3258767 := bstep (se 1 (by rfl) ⟨2444075, by rfl⟩ : syracuseStep 3258767 = 4888151) B4888151
theorem B6691315 : Blo 1715058 6691315 := bstep (se 1 (by rfl) ⟨5018486, by rfl⟩ : syracuseStep 6691315 = 10036973) B10036973
theorem B3480187 : Blo 1715058 3480187 := bstep (se 1 (by rfl) ⟨2610140, by rfl⟩ : syracuseStep 3480187 = 5220281) B5220281
theorem B6961787 : Blo 1715058 6961787 := bstep (se 1 (by rfl) ⟨5221340, by rfl⟩ : syracuseStep 6961787 = 10442681) B10442681
theorem B11737811 : Blo 1715058 11737811 := bstep (se 1 (by rfl) ⟨8803358, by rfl⟩ : syracuseStep 11737811 = 17606717) B17606717
theorem B5790419 : Blo 1715058 5790419 := bstep (se 1 (by rfl) ⟨4342814, by rfl⟩ : syracuseStep 5790419 = 8685629) B8685629
theorem B5495647 : Blo 1715058 5495647 := bstep (se 1 (by rfl) ⟨4121735, by rfl⟩ : syracuseStep 5495647 = 8243471) B8243471
theorem B3177377 : Blo 1715058 3177377 := bstep (se 2 (by rfl) ⟨1191516, by rfl⟩ : syracuseStep 3177377 = 2383033) B2383033
theorem B55639385 : Blo 1715058 55639385 := bstep (se 2 (by rfl) ⟨20864769, by rfl⟩ : syracuseStep 55639385 = 41729539) B41729539
theorem B111336889 : Blo 1715058 111336889 := bstep (se 2 (by rfl) ⟨41751333, by rfl⟩ : syracuseStep 111336889 = 83502667) B83502667
theorem B6954535 : Blo 1715058 6954535 := bstep (se 1 (by rfl) ⟨5215901, by rfl⟩ : syracuseStep 6954535 = 10431803) B10431803
theorem B8806087 : Blo 1715058 8806087 := bstep (se 1 (by rfl) ⟨6604565, by rfl⟩ : syracuseStep 8806087 = 13209131) B13209131
theorem B6512339 : Blo 1715058 6512339 := bstep (se 1 (by rfl) ⟨4884254, by rfl⟩ : syracuseStep 6512339 = 9768509) B9768509
theorem B7331543 : Blo 1715058 7331543 := bstep (se 1 (by rfl) ⟨5498657, by rfl⟩ : syracuseStep 7331543 = 10997315) B10997315
theorem B5496569 : Blo 1715058 5496569 := bstep (se 2 (by rfl) ⟨2061213, by rfl⟩ : syracuseStep 5496569 = 4122427) B4122427
theorem B6954781 : Blo 1715058 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B5791607 : Blo 1715058 5791607 := bstep (se 1 (by rfl) ⟨4343705, by rfl⟩ : syracuseStep 5791607 = 8687411) B8687411
theorem B1957807 : Blo 1715058 1957807 := bstep (se 1 (by rfl) ⟨1468355, by rfl⟩ : syracuseStep 1957807 = 2936711) B2936711
theorem B14663699 : Blo 1715058 14663699 := bstep (se 1 (by rfl) ⟨10997774, by rfl⟩ : syracuseStep 14663699 = 21995549) B21995549
theorem B5791769 : Blo 1715058 5791769 := bstep (se 2 (by rfl) ⟨2171913, by rfl⟩ : syracuseStep 5791769 = 4343827) B4343827
theorem B4342025 : Blo 1715058 4342025 := bstep (se 2 (by rfl) ⟨1628259, by rfl⟩ : syracuseStep 4342025 = 3256519) B3256519
theorem B18563377 : Blo 1715058 18563377 := bstep (se 2 (by rfl) ⟨6961266, by rfl⟩ : syracuseStep 18563377 = 13922533) B13922533
theorem B2572655 : Blo 1715058 2572655 := bstep (se 1 (by rfl) ⟨1929491, by rfl⟩ : syracuseStep 2572655 = 3858983) B3858983
theorem B2171387 : Blo 1715058 2171387 := bstep (se 1 (by rfl) ⟨1628540, by rfl⟩ : syracuseStep 2171387 = 3257081) B3257081
theorem B2572871 : Blo 1715058 2572871 := bstep (se 1 (by rfl) ⟨1929653, by rfl⟩ : syracuseStep 2572871 = 3859307) B3859307
theorem B2572907 : Blo 1715058 2572907 := bstep (se 1 (by rfl) ⟨1929680, by rfl⟩ : syracuseStep 2572907 = 3859361) B3859361
theorem B8921753 : Blo 1715058 8921753 := bstep (se 2 (by rfl) ⟨3345657, by rfl⟩ : syracuseStep 8921753 = 6691315) B6691315
theorem B3859127 : Blo 1715058 3859127 := bstep (se 1 (by rfl) ⟨2894345, by rfl⟩ : syracuseStep 3859127 = 5788691) B5788691
theorem B6955703 : Blo 1715058 6955703 := bstep (se 1 (by rfl) ⟨5216777, by rfl⟩ : syracuseStep 6955703 = 10433555) B10433555
theorem B7332601 : Blo 1715058 7332601 := bstep (se 2 (by rfl) ⟨2749725, by rfl⟩ : syracuseStep 7332601 = 5499451) B5499451
theorem B2573135 : Blo 1715058 2573135 := bstep (se 1 (by rfl) ⟨1929851, by rfl⟩ : syracuseStep 2573135 = 3859703) B3859703
theorem B3859343 : Blo 1715058 3859343 := bstep (se 1 (by rfl) ⟨2894507, by rfl⟩ : syracuseStep 3859343 = 5789015) B5789015
theorem B4637611 : Blo 1715058 4637611 := bstep (se 1 (by rfl) ⟨3478208, by rfl⟩ : syracuseStep 4637611 = 6956417) B6956417
theorem B2573531 : Blo 1715058 2573531 := bstep (se 1 (by rfl) ⟨1930148, by rfl⟩ : syracuseStep 2573531 = 3860297) B3860297
theorem B4343017 : Blo 1715058 4343017 := bstep (se 2 (by rfl) ⟨1628631, by rfl⟩ : syracuseStep 4343017 = 3257263) B3257263
theorem B5793011 : Blo 1715058 5793011 := bstep (se 1 (by rfl) ⟨4344758, by rfl⟩ : syracuseStep 5793011 = 8689517) B8689517
theorem B5793119 : Blo 1715058 5793119 := bstep (se 1 (by rfl) ⟨4344839, by rfl⟩ : syracuseStep 5793119 = 8689679) B8689679
theorem B2573705 : Blo 1715058 2573705 := bstep (se 2 (by rfl) ⟨965139, by rfl⟩ : syracuseStep 2573705 = 1930279) B1930279
theorem B4343179 : Blo 1715058 4343179 := bstep (se 1 (by rfl) ⟨3257384, by rfl⟩ : syracuseStep 4343179 = 6514769) B6514769
theorem B5498273 : Blo 1715058 5498273 := bstep (se 2 (by rfl) ⟨2061852, by rfl⟩ : syracuseStep 5498273 = 4123705) B4123705
theorem B2172359 : Blo 1715058 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B3860063 : Blo 1715058 3860063 := bstep (se 1 (by rfl) ⟨2895047, by rfl⟩ : syracuseStep 3860063 = 5790095) B5790095
theorem B2172511 : Blo 1715058 2172511 := bstep (se 1 (by rfl) ⟨1629383, by rfl⟩ : syracuseStep 2172511 = 3258767) B3258767
theorem B4343483 : Blo 1715058 4343483 := bstep (se 1 (by rfl) ⟨3257612, by rfl⟩ : syracuseStep 4343483 = 6515225) B6515225
theorem B2574059 : Blo 1715058 2574059 := bstep (se 1 (by rfl) ⟨1930544, by rfl⟩ : syracuseStep 2574059 = 3861089) B3861089
theorem B7825207 : Blo 1715058 7825207 := bstep (se 1 (by rfl) ⟨5868905, by rfl⟩ : syracuseStep 7825207 = 11737811) B11737811
theorem B3860279 : Blo 1715058 3860279 := bstep (se 1 (by rfl) ⟨2895209, by rfl⟩ : syracuseStep 3860279 = 5790419) B5790419
theorem B3663721 : Blo 1715058 3663721 := bstep (se 2 (by rfl) ⟨1373895, by rfl⟩ : syracuseStep 3663721 = 2747791) B2747791
theorem B148449185 : Blo 1715058 148449185 := bstep (se 2 (by rfl) ⟨55668444, by rfl⟩ : syracuseStep 148449185 = 111336889) B111336889
theorem B2574287 : Blo 1715058 2574287 := bstep (se 1 (by rfl) ⟨1930715, by rfl⟩ : syracuseStep 2574287 = 3861431) B3861431
theorem B3860585 : Blo 1715058 3860585 := bstep (se 2 (by rfl) ⟨1447719, by rfl⟩ : syracuseStep 3860585 = 2895439) B2895439
theorem B4884745 : Blo 1715058 4884745 := bstep (se 2 (by rfl) ⟨1831779, by rfl⟩ : syracuseStep 4884745 = 3663559) B3663559
theorem B11741449 : Blo 1715058 11741449 := bstep (se 2 (by rfl) ⟨4403043, by rfl⟩ : syracuseStep 11741449 = 8806087) B8806087
theorem B2574683 : Blo 1715058 2574683 := bstep (se 1 (by rfl) ⟨1931012, by rfl⟩ : syracuseStep 2574683 = 3862025) B3862025
theorem B16501121 : Blo 1715058 16501121 := bstep (se 2 (by rfl) ⟨6187920, by rfl⟩ : syracuseStep 16501121 = 12375841) B12375841
theorem B8243623 : Blo 1715058 8243623 := bstep (se 1 (by rfl) ⟨6182717, by rfl⟩ : syracuseStep 8243623 = 12365435) B12365435
theorem B3664379 : Blo 1715058 3664379 := bstep (se 1 (by rfl) ⟨2748284, by rfl⟩ : syracuseStep 3664379 = 5496569) B5496569
theorem B2574911 : Blo 1715058 2574911 := bstep (se 1 (by rfl) ⟨1931183, by rfl⟩ : syracuseStep 2574911 = 3862367) B3862367
theorem B3861071 : Blo 1715058 3861071 := bstep (se 1 (by rfl) ⟨2895803, by rfl⟩ : syracuseStep 3861071 = 5791607) B5791607
theorem B2575031 : Blo 1715058 2575031 := bstep (se 1 (by rfl) ⟨1931273, by rfl⟩ : syracuseStep 2575031 = 3862547) B3862547
theorem B3861215 : Blo 1715058 3861215 := bstep (se 1 (by rfl) ⟨2895911, by rfl⟩ : syracuseStep 3861215 = 5791823) B5791823
theorem B20081431 : Blo 1715058 20081431 := bstep (se 1 (by rfl) ⟨15061073, by rfl⟩ : syracuseStep 20081431 = 30122147) B30122147
theorem B12069665 : Blo 1715058 12069665 := bstep (se 2 (by rfl) ⟨4526124, by rfl⟩ : syracuseStep 12069665 = 9052249) B9052249
theorem B5794685 : Blo 1715058 5794685 := bstep (se 3 (by rfl) ⟨1086503, by rfl⟩ : syracuseStep 5794685 = 2173007) B2173007
theorem B1715099 : Blo 1715058 1715099 := bstep (se 1 (by rfl) ⟨1286324, by rfl⟩ : syracuseStep 1715099 = 2572649) B2572649
theorem B2575259 : Blo 1715058 2575259 := bstep (se 1 (by rfl) ⟨1931444, by rfl⟩ : syracuseStep 2575259 = 3862889) B3862889
theorem B1715151 : Blo 1715058 1715151 := bstep (se 1 (by rfl) ⟨1286363, by rfl⟩ : syracuseStep 1715151 = 2572727) B2572727
theorem B3861467 : Blo 1715058 3861467 := bstep (se 1 (by rfl) ⟨2896100, by rfl⟩ : syracuseStep 3861467 = 5792201) B5792201
theorem B1715175 : Blo 1715058 1715175 := bstep (se 1 (by rfl) ⟨1286381, by rfl⟩ : syracuseStep 1715175 = 2572763) B2572763
theorem B7433203 : Blo 1715058 7433203 := bstep (se 1 (by rfl) ⟨5574902, by rfl⟩ : syracuseStep 7433203 = 11149805) B11149805
theorem B23481409 : Blo 1715058 23481409 := bstep (se 2 (by rfl) ⟨8805528, by rfl⟩ : syracuseStep 23481409 = 17611057) B17611057
theorem B14658641 : Blo 1715058 14658641 := bstep (se 2 (by rfl) ⟨5496990, by rfl⟩ : syracuseStep 14658641 = 10993981) B10993981
theorem B16485515 : Blo 1715058 16485515 := bstep (se 1 (by rfl) ⟨12364136, by rfl⟩ : syracuseStep 16485515 = 24728273) B24728273
theorem B3861647 : Blo 1715058 3861647 := bstep (se 1 (by rfl) ⟨2896235, by rfl⟩ : syracuseStep 3861647 = 5792471) B5792471
theorem B5794955 : Blo 1715058 5794955 := bstep (se 1 (by rfl) ⟨4346216, by rfl⟩ : syracuseStep 5794955 = 8692433) B8692433
theorem B21982427 : Blo 1715058 21982427 := bstep (se 1 (by rfl) ⟨16486820, by rfl⟩ : syracuseStep 21982427 = 32973641) B32973641
theorem B10996955 : Blo 1715058 10996955 := bstep (se 1 (by rfl) ⟨8247716, by rfl⟩ : syracuseStep 10996955 = 16495433) B16495433
theorem B3861737 : Blo 1715058 3861737 := bstep (se 2 (by rfl) ⟨1448151, by rfl⟩ : syracuseStep 3861737 = 2896303) B2896303
theorem B1715487 : Blo 1715058 1715487 := bstep (se 1 (by rfl) ⟨1286615, by rfl⟩ : syracuseStep 1715487 = 2573231) B2573231
theorem B3861791 : Blo 1715058 3861791 := bstep (se 1 (by rfl) ⟨2896343, by rfl⟩ : syracuseStep 3861791 = 5792687) B5792687
theorem B1715547 : Blo 1715058 1715547 := bstep (se 1 (by rfl) ⟨1286660, by rfl⟩ : syracuseStep 1715547 = 2573321) B2573321
theorem B1715567 : Blo 1715058 1715567 := bstep (se 1 (by rfl) ⟨1286675, by rfl⟩ : syracuseStep 1715567 = 2573351) B2573351
theorem B1715623 : Blo 1715058 1715623 := bstep (se 1 (by rfl) ⟨1286717, by rfl⟩ : syracuseStep 1715623 = 2573435) B2573435
theorem B2608583 : Blo 1715058 2608583 := bstep (se 1 (by rfl) ⟨1956437, by rfl⟩ : syracuseStep 2608583 = 3912875) B3912875
theorem B4640249 : Blo 1715058 4640249 := bstep (se 2 (by rfl) ⟨1740093, by rfl⟩ : syracuseStep 4640249 = 3480187) B3480187
theorem B1715707 : Blo 1715058 1715707 := bstep (se 1 (by rfl) ⟨1286780, by rfl⟩ : syracuseStep 1715707 = 2573561) B2573561
theorem B1715775 : Blo 1715058 1715775 := bstep (se 1 (by rfl) ⟨1286831, by rfl⟩ : syracuseStep 1715775 = 2573663) B2573663
theorem B1715783 : Blo 1715058 1715783 := bstep (se 1 (by rfl) ⟨1286837, by rfl⟩ : syracuseStep 1715783 = 2573675) B2573675
theorem B6958673 : Blo 1715058 6958673 := bstep (se 2 (by rfl) ⟨2609502, by rfl⟩ : syracuseStep 6958673 = 5219005) B5219005
theorem B3092051 : Blo 1715058 3092051 := bstep (se 1 (by rfl) ⟨2319038, by rfl⟩ : syracuseStep 3092051 = 4638077) B4638077
theorem B4345427 : Blo 1715058 4345427 := bstep (se 1 (by rfl) ⟨3259070, by rfl⟩ : syracuseStep 4345427 = 6518141) B6518141
theorem B4124321 : Blo 1715058 4124321 := bstep (se 2 (by rfl) ⟨1546620, by rfl⟩ : syracuseStep 4124321 = 3093241) B3093241
theorem B16486051 : Blo 1715058 16486051 := bstep (se 1 (by rfl) ⟨12364538, by rfl⟩ : syracuseStep 16486051 = 24729077) B24729077
theorem B2895547 : Blo 1715058 2895547 := bstep (se 1 (by rfl) ⟨2171660, by rfl⟩ : syracuseStep 2895547 = 4343321) B4343321
theorem B10989265 : Blo 1715058 10989265 := bstep (se 2 (by rfl) ⟨4120974, by rfl⟩ : syracuseStep 10989265 = 8241949) B8241949
theorem B1715935 : Blo 1715058 1715935 := bstep (se 1 (by rfl) ⟨1286951, by rfl⟩ : syracuseStep 1715935 = 2573903) B2573903
theorem B7327529 : Blo 1715058 7327529 := bstep (se 2 (by rfl) ⟨2747823, by rfl⟩ : syracuseStep 7327529 = 5495647) B5495647
theorem B3862313 : Blo 1715058 3862313 := bstep (se 2 (by rfl) ⟨1448367, by rfl⟩ : syracuseStep 3862313 = 2896735) B2896735
theorem B1716015 : Blo 1715058 1716015 := bstep (se 1 (by rfl) ⟨1287011, by rfl⟩ : syracuseStep 1716015 = 2574023) B2574023
theorem B9768761 : Blo 1715058 9768761 := bstep (se 2 (by rfl) ⟨3663285, by rfl⟩ : syracuseStep 9768761 = 7326571) B7326571
theorem B1716123 : Blo 1715058 1716123 := bstep (se 1 (by rfl) ⟨1287092, by rfl⟩ : syracuseStep 1716123 = 2574185) B2574185
theorem B8474543 : Blo 1715058 8474543 := bstep (se 1 (by rfl) ⟨6355907, by rfl⟩ : syracuseStep 8474543 = 12711815) B12711815
theorem B1716175 : Blo 1715058 1716175 := bstep (se 1 (by rfl) ⟨1287131, by rfl⟩ : syracuseStep 1716175 = 2574263) B2574263
theorem B1716199 : Blo 1715058 1716199 := bstep (se 1 (by rfl) ⟨1287149, by rfl⟩ : syracuseStep 1716199 = 2574299) B2574299
theorem B9777257 : Blo 1715058 9777257 := bstep (se 2 (by rfl) ⟨3666471, by rfl⟩ : syracuseStep 9777257 = 7332943) B7332943
theorem B13922563 : Blo 1715058 13922563 := bstep (se 1 (by rfl) ⟨10441922, by rfl⟩ : syracuseStep 13922563 = 20883845) B20883845
theorem B1716511 : Blo 1715058 1716511 := bstep (se 1 (by rfl) ⟨1287383, by rfl⟩ : syracuseStep 1716511 = 2574767) B2574767
theorem B1716571 : Blo 1715058 1716571 := bstep (se 1 (by rfl) ⟨1287428, by rfl⟩ : syracuseStep 1716571 = 2574857) B2574857
theorem B1716591 : Blo 1715058 1716591 := bstep (se 1 (by rfl) ⟨1287443, by rfl⟩ : syracuseStep 1716591 = 2574887) B2574887
theorem B1929595 : Blo 1715058 1929595 := bstep (se 1 (by rfl) ⟨1447196, by rfl⟩ : syracuseStep 1929595 = 2894393) B2894393
theorem B1716647 : Blo 1715058 1716647 := bstep (se 1 (by rfl) ⟨1287485, by rfl⟩ : syracuseStep 1716647 = 2574971) B2574971
theorem B4641191 : Blo 1715058 4641191 := bstep (se 1 (by rfl) ⟨3480893, by rfl⟩ : syracuseStep 4641191 = 6961787) B6961787
theorem B24752603 : Blo 1715058 24752603 := bstep (se 1 (by rfl) ⟨18564452, by rfl⟩ : syracuseStep 24752603 = 37128905) B37128905
theorem B2060795 : Blo 1715058 2060795 := bstep (se 1 (by rfl) ⟨1545596, by rfl⟩ : syracuseStep 2060795 = 3091193) B3091193
theorem B3715579 : Blo 1715058 3715579 := bstep (se 1 (by rfl) ⟨2786684, by rfl⟩ : syracuseStep 3715579 = 5573369) B5573369
theorem B1716731 : Blo 1715058 1716731 := bstep (se 1 (by rfl) ⟨1287548, by rfl⟩ : syracuseStep 1716731 = 2575097) B2575097
theorem B16486973 : Blo 1715058 16486973 := bstep (se 3 (by rfl) ⟨3091307, by rfl⟩ : syracuseStep 16486973 = 6182615) B6182615
theorem B1716799 : Blo 1715058 1716799 := bstep (se 1 (by rfl) ⟨1287599, by rfl⟩ : syracuseStep 1716799 = 2575199) B2575199
theorem B1716807 : Blo 1715058 1716807 := bstep (se 1 (by rfl) ⟨1287605, by rfl⟩ : syracuseStep 1716807 = 2575211) B2575211
theorem B1831519 : Blo 1715058 1831519 := bstep (se 1 (by rfl) ⟨1373639, by rfl⟩ : syracuseStep 1831519 = 2747279) B2747279
theorem B2118251 : Blo 1715058 2118251 := bstep (se 1 (by rfl) ⟨1588688, by rfl⟩ : syracuseStep 2118251 = 3177377) B3177377
theorem B2896607 : Blo 1715058 2896607 := bstep (se 1 (by rfl) ⟨2172455, by rfl⟩ : syracuseStep 2896607 = 4344911) B4344911
theorem B1716959 : Blo 1715058 1716959 := bstep (se 1 (by rfl) ⟨1287719, by rfl⟩ : syracuseStep 1716959 = 2575439) B2575439
theorem B1717039 : Blo 1715058 1717039 := bstep (se 1 (by rfl) ⟨1287779, by rfl⟩ : syracuseStep 1717039 = 2575559) B2575559
theorem B1930063 : Blo 1715058 1930063 := bstep (se 1 (by rfl) ⟨1447547, by rfl⟩ : syracuseStep 1930063 = 2895095) B2895095
theorem B3863375 : Blo 1715058 3863375 := bstep (se 1 (by rfl) ⟨2897531, by rfl⟩ : syracuseStep 3863375 = 5795063) B5795063
theorem B1831835 : Blo 1715058 1831835 := bstep (se 1 (by rfl) ⟨1373876, by rfl⟩ : syracuseStep 1831835 = 2747753) B2747753
theorem B8688545 : Blo 1715058 8688545 := bstep (se 2 (by rfl) ⟨3258204, by rfl⟩ : syracuseStep 8688545 = 6516409) B6516409
theorem B19543031 : Blo 1715058 19543031 := bstep (se 1 (by rfl) ⟨14657273, by rfl⟩ : syracuseStep 19543031 = 29314547) B29314547
theorem B4887695 : Blo 1715058 4887695 := bstep (se 1 (by rfl) ⟨3665771, by rfl⟩ : syracuseStep 4887695 = 7331543) B7331543
theorem B2897039 : Blo 1715058 2897039 := bstep (se 1 (by rfl) ⟨2172779, by rfl⟩ : syracuseStep 2897039 = 4345559) B4345559
theorem B1930459 : Blo 1715058 1930459 := bstep (se 1 (by rfl) ⟨1447844, by rfl⟩ : syracuseStep 1930459 = 2895689) B2895689
theorem B2610409 : Blo 1715058 2610409 := bstep (se 2 (by rfl) ⟨978903, by rfl⟩ : syracuseStep 2610409 = 1957807) B1957807
theorem B2897275 : Blo 1715058 2897275 := bstep (se 1 (by rfl) ⟨2172956, by rfl⟩ : syracuseStep 2897275 = 4345913) B4345913
theorem B33453445 : Blo 1715058 33453445 := bstep (se 4 (by rfl) ⟨3136260, by rfl⟩ : syracuseStep 33453445 = 6272521) B6272521
theorem B5870987 : Blo 1715058 5870987 := bstep (se 1 (by rfl) ⟨4403240, by rfl⟩ : syracuseStep 5870987 = 8806481) B8806481
theorem B8246717 : Blo 1715058 8246717 := bstep (se 3 (by rfl) ⟨1546259, by rfl⟩ : syracuseStep 8246717 = 3092519) B3092519
theorem B14661101 : Blo 1715058 14661101 := bstep (se 3 (by rfl) ⟨2748956, by rfl⟩ : syracuseStep 14661101 = 5497913) B5497913
theorem B1930747 : Blo 1715058 1930747 := bstep (se 1 (by rfl) ⟨1448060, by rfl⟩ : syracuseStep 1930747 = 2896121) B2896121
theorem B16487975 : Blo 1715058 16487975 := bstep (se 1 (by rfl) ⟨12365981, by rfl⟩ : syracuseStep 16487975 = 24731963) B24731963
theorem B1930927 : Blo 1715058 1930927 := bstep (se 1 (by rfl) ⟨1448195, by rfl⟩ : syracuseStep 1930927 = 2896391) B2896391
theorem B3258319 : Blo 1715058 3258319 := bstep (se 1 (by rfl) ⟨2443739, by rfl⟩ : syracuseStep 3258319 = 4887479) B4887479
theorem B1832911 : Blo 1715058 1832911 := bstep (se 1 (by rfl) ⟨1374683, by rfl⟩ : syracuseStep 1832911 = 2749367) B2749367
theorem B1931215 : Blo 1715058 1931215 := bstep (se 1 (by rfl) ⟨1448411, by rfl⟩ : syracuseStep 1931215 = 2896823) B2896823
theorem B62617661 : Blo 1715058 62617661 := bstep (se 3 (by rfl) ⟨11740811, by rfl⟩ : syracuseStep 62617661 = 23481623) B23481623
theorem B5789825 : Blo 1715058 5789825 := bstep (se 2 (by rfl) ⟨2171184, by rfl⟩ : syracuseStep 5789825 = 4342369) B4342369
theorem B24746147 : Blo 1715058 24746147 := bstep (se 1 (by rfl) ⟨18559610, by rfl⟩ : syracuseStep 24746147 = 37119221) B37119221
theorem B1931611 : Blo 1715058 1931611 := bstep (se 1 (by rfl) ⟨1448708, by rfl⟩ : syracuseStep 1931611 = 2897417) B2897417
theorem B2202055 : Blo 1715058 2202055 := bstep (se 1 (by rfl) ⟨1651541, by rfl⟩ : syracuseStep 2202055 = 3303083) B3303083
theorem B5790203 : Blo 1715058 5790203 := bstep (se 1 (by rfl) ⟨4342652, by rfl⟩ : syracuseStep 5790203 = 8685305) B8685305
theorem B9271847 : Blo 1715058 9271847 := bstep (se 1 (by rfl) ⟨6953885, by rfl⟩ : syracuseStep 9271847 = 13907771) B13907771
theorem B3259055 : Blo 1715058 3259055 := bstep (se 1 (by rfl) ⟨2444291, by rfl⟩ : syracuseStep 3259055 = 4888583) B4888583
theorem B4889335 : Blo 1715058 4889335 := bstep (se 1 (by rfl) ⟨3667001, by rfl⟩ : syracuseStep 4889335 = 7334003) B7334003
theorem B3259291 : Blo 1715058 3259291 := bstep (se 1 (by rfl) ⟨2444468, by rfl⟩ : syracuseStep 3259291 = 4888937) B4888937
theorem B5790635 : Blo 1715058 5790635 := bstep (se 1 (by rfl) ⟨4342976, by rfl⟩ : syracuseStep 5790635 = 8685953) B8685953
theorem B12369125 : Blo 1715058 12369125 := bstep (se 4 (by rfl) ⟨1159605, by rfl⟩ : syracuseStep 12369125 = 2319211) B2319211
theorem B8690975 : Blo 1715058 8690975 := bstep (se 1 (by rfl) ⟨6518231, by rfl⟩ : syracuseStep 8690975 = 13036463) B13036463
theorem B6184289 : Blo 1715058 6184289 := bstep (se 2 (by rfl) ⟨2319108, by rfl⟩ : syracuseStep 6184289 = 4638217) B4638217
theorem B9272713 : Blo 1715058 9272713 := bstep (se 2 (by rfl) ⟨3477267, by rfl⟩ : syracuseStep 9272713 = 6954535) B6954535
theorem B5791175 : Blo 1715058 5791175 := bstep (se 1 (by rfl) ⟨4343381, by rfl⟩ : syracuseStep 5791175 = 8686763) B8686763
theorem B37092923 : Blo 1715058 37092923 := bstep (se 1 (by rfl) ⟨27819692, by rfl⟩ : syracuseStep 37092923 = 55639385) B55639385
theorem B9281105 : Blo 1715058 9281105 := bstep (se 2 (by rfl) ⟨3480414, by rfl⟩ : syracuseStep 9281105 = 6960829) B6960829
theorem B9273041 : Blo 1715058 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B5791499 : Blo 1715058 5791499 := bstep (se 1 (by rfl) ⟨4343624, by rfl⟩ : syracuseStep 5791499 = 8687249) B8687249
theorem B4341559 : Blo 1715058 4341559 := bstep (se 1 (by rfl) ⟨3256169, by rfl⟩ : syracuseStep 4341559 = 6512339) B6512339
theorem B2318287 : Blo 1715058 2318287 := bstep (se 1 (by rfl) ⟨1738715, by rfl⟩ : syracuseStep 2318287 = 3477431) B3477431
theorem B18563417 : Blo 1715058 18563417 := bstep (se 2 (by rfl) ⟨6961281, by rfl⟩ : syracuseStep 18563417 = 13922563) B13922563
theorem B6512993 : Blo 1715058 6512993 := bstep (se 2 (by rfl) ⟨2442372, by rfl⟩ : syracuseStep 6512993 = 4884745) B4884745
theorem B15655265 : Blo 1715058 15655265 := bstep (se 2 (by rfl) ⟨5870724, by rfl⟩ : syracuseStep 15655265 = 11741449) B11741449
theorem B5947835 : Blo 1715058 5947835 := bstep (se 1 (by rfl) ⟨4460876, by rfl⟩ : syracuseStep 5947835 = 8921753) B8921753
theorem B2572751 : Blo 1715058 2572751 := bstep (se 1 (by rfl) ⟨1929563, by rfl⟩ : syracuseStep 2572751 = 3859127) B3859127
theorem B4637135 : Blo 1715058 4637135 := bstep (se 1 (by rfl) ⟨3477851, by rfl⟩ : syracuseStep 4637135 = 6955703) B6955703
theorem B2572793 : Blo 1715058 2572793 := bstep (se 2 (by rfl) ⟨964797, by rfl⟩ : syracuseStep 2572793 = 1929595) B1929595
theorem B2572895 : Blo 1715058 2572895 := bstep (se 1 (by rfl) ⟨1929671, by rfl⟩ : syracuseStep 2572895 = 3859343) B3859343
theorem B5792363 : Blo 1715058 5792363 := bstep (se 1 (by rfl) ⟨4344272, by rfl⟩ : syracuseStep 5792363 = 8688545) B8688545
theorem B2442025 : Blo 1715058 2442025 := bstep (se 2 (by rfl) ⟨915759, by rfl⟩ : syracuseStep 2442025 = 1831519) B1831519
theorem B16491437 : Blo 1715058 16491437 := bstep (se 3 (by rfl) ⟨3092144, by rfl⟩ : syracuseStep 16491437 = 6184289) B6184289
theorem B5497811 : Blo 1715058 5497811 := bstep (se 1 (by rfl) ⟨4123358, by rfl⟩ : syracuseStep 5497811 = 8246717) B8246717
theorem B9774067 : Blo 1715058 9774067 := bstep (se 1 (by rfl) ⟨7330550, by rfl⟩ : syracuseStep 9774067 = 14661101) B14661101
theorem B2573375 : Blo 1715058 2573375 := bstep (se 1 (by rfl) ⟨1930031, by rfl⟩ : syracuseStep 2573375 = 3860063) B3860063
theorem B2573417 : Blo 1715058 2573417 := bstep (se 2 (by rfl) ⟨965031, by rfl⟩ : syracuseStep 2573417 = 1930063) B1930063
theorem B6956221 : Blo 1715058 6956221 := bstep (se 3 (by rfl) ⟨1304291, by rfl⟩ : syracuseStep 6956221 = 2608583) B2608583
theorem B5792957 : Blo 1715058 5792957 := bstep (se 3 (by rfl) ⟨1086179, by rfl⟩ : syracuseStep 5792957 = 2172359) B2172359
theorem B2573519 : Blo 1715058 2573519 := bstep (se 1 (by rfl) ⟨1930139, by rfl⟩ : syracuseStep 2573519 = 3860279) B3860279
theorem B2573723 : Blo 1715058 2573723 := bstep (se 1 (by rfl) ⟨1930292, by rfl⟩ : syracuseStep 2573723 = 3860585) B3860585
theorem B3859883 : Blo 1715058 3859883 := bstep (se 1 (by rfl) ⟨2894912, by rfl⟩ : syracuseStep 3859883 = 5789825) B5789825
theorem B24724925 : Blo 1715058 24724925 := bstep (se 3 (by rfl) ⟨4635923, by rfl⟩ : syracuseStep 24724925 = 9271847) B9271847
theorem B2573945 : Blo 1715058 2573945 := bstep (se 2 (by rfl) ⟨965229, by rfl⟩ : syracuseStep 2573945 = 1930459) B1930459
theorem B3860135 : Blo 1715058 3860135 := bstep (se 1 (by rfl) ⟨2895101, by rfl⟩ : syracuseStep 3860135 = 5790203) B5790203
theorem B2574047 : Blo 1715058 2574047 := bstep (se 1 (by rfl) ⟨1930535, by rfl⟩ : syracuseStep 2574047 = 3861071) B3861071
theorem B2574143 : Blo 1715058 2574143 := bstep (se 1 (by rfl) ⟨1930607, by rfl⟩ : syracuseStep 2574143 = 3861215) B3861215
theorem B12363617 : Blo 1715058 12363617 := bstep (se 2 (by rfl) ⟨4636356, by rfl⟩ : syracuseStep 12363617 = 9272713) B9272713
theorem B8046443 : Blo 1715058 8046443 := bstep (se 1 (by rfl) ⟨6034832, by rfl⟩ : syracuseStep 8046443 = 12069665) B12069665
theorem B3860423 : Blo 1715058 3860423 := bstep (se 1 (by rfl) ⟨2895317, by rfl⟩ : syracuseStep 3860423 = 5790635) B5790635
theorem B2574311 : Blo 1715058 2574311 := bstep (se 1 (by rfl) ⟨1930733, by rfl⟩ : syracuseStep 2574311 = 3861467) B3861467
theorem B2574329 : Blo 1715058 2574329 := bstep (se 2 (by rfl) ⟨965373, by rfl⟩ : syracuseStep 2574329 = 1930747) B1930747
theorem B2574431 : Blo 1715058 2574431 := bstep (se 1 (by rfl) ⟨1930823, by rfl⟩ : syracuseStep 2574431 = 3861647) B3861647
theorem B2574491 : Blo 1715058 2574491 := bstep (se 1 (by rfl) ⟨1930868, by rfl⟩ : syracuseStep 2574491 = 3861737) B3861737
theorem B2574527 : Blo 1715058 2574527 := bstep (se 1 (by rfl) ⟨1930895, by rfl⟩ : syracuseStep 2574527 = 3861791) B3861791
theorem B5793983 : Blo 1715058 5793983 := bstep (se 1 (by rfl) ⟨4345487, by rfl⟩ : syracuseStep 5793983 = 8690975) B8690975
theorem B21981401 : Blo 1715058 21981401 := bstep (se 2 (by rfl) ⟨8243025, by rfl⟩ : syracuseStep 21981401 = 16486051) B16486051
theorem B2574569 : Blo 1715058 2574569 := bstep (se 2 (by rfl) ⟨965463, by rfl⟩ : syracuseStep 2574569 = 1930927) B1930927
theorem B3860729 : Blo 1715058 3860729 := bstep (se 2 (by rfl) ⟨1447773, by rfl⟩ : syracuseStep 3860729 = 2895547) B2895547
theorem B3860783 : Blo 1715058 3860783 := bstep (se 1 (by rfl) ⟨2895587, by rfl⟩ : syracuseStep 3860783 = 5791175) B5791175
theorem B4639115 : Blo 1715058 4639115 := bstep (se 1 (by rfl) ⟨3479336, by rfl⟩ : syracuseStep 4639115 = 6958673) B6958673
theorem B6187403 : Blo 1715058 6187403 := bstep (se 1 (by rfl) ⟨4640552, by rfl⟩ : syracuseStep 6187403 = 9281105) B9281105
theorem B4884893 : Blo 1715058 4884893 := bstep (se 3 (by rfl) ⟨915917, by rfl⟩ : syracuseStep 4884893 = 1831835) B1831835
theorem B9775525 : Blo 1715058 9775525 := bstep (se 4 (by rfl) ⟨916455, by rfl⟩ : syracuseStep 9775525 = 1832911) B1832911
theorem B4884961 : Blo 1715058 4884961 := bstep (se 2 (by rfl) ⟨1831860, by rfl⟩ : syracuseStep 4884961 = 3663721) B3663721
theorem B3860999 : Blo 1715058 3860999 := bstep (se 1 (by rfl) ⟨2895749, by rfl⟩ : syracuseStep 3860999 = 5791499) B5791499
theorem B4885019 : Blo 1715058 4885019 := bstep (se 1 (by rfl) ⟨3663764, by rfl⟩ : syracuseStep 4885019 = 7327529) B7327529
theorem B2574875 : Blo 1715058 2574875 := bstep (se 1 (by rfl) ⟨1931156, by rfl⟩ : syracuseStep 2574875 = 3862313) B3862313
theorem B3091049 : Blo 1715058 3091049 := bstep (se 2 (by rfl) ⟨1159143, by rfl⟩ : syracuseStep 3091049 = 2318287) B2318287
theorem B4344425 : Blo 1715058 4344425 := bstep (se 2 (by rfl) ⟨1629159, by rfl⟩ : syracuseStep 4344425 = 3258319) B3258319
theorem B2574953 : Blo 1715058 2574953 := bstep (se 2 (by rfl) ⟨965607, by rfl⟩ : syracuseStep 2574953 = 1931215) B1931215
theorem B9775799 : Blo 1715058 9775799 := bstep (se 1 (by rfl) ⟨7331849, by rfl⟩ : syracuseStep 9775799 = 14663699) B14663699
theorem B3861179 : Blo 1715058 3861179 := bstep (se 1 (by rfl) ⟨2895884, by rfl⟩ : syracuseStep 3861179 = 5791769) B5791769
theorem B2894683 : Blo 1715058 2894683 := bstep (se 1 (by rfl) ⟨2171012, by rfl⟩ : syracuseStep 2894683 = 4342025) B4342025
theorem B1715103 : Blo 1715058 1715103 := bstep (se 1 (by rfl) ⟨1286327, by rfl⟩ : syracuseStep 1715103 = 2572655) B2572655
theorem B16501735 : Blo 1715058 16501735 := bstep (se 1 (by rfl) ⟨12376301, by rfl⟩ : syracuseStep 16501735 = 24752603) B24752603
theorem B1715247 : Blo 1715058 1715247 := bstep (se 1 (by rfl) ⟨1286435, by rfl⟩ : syracuseStep 1715247 = 2572871) B2572871
theorem B24751169 : Blo 1715058 24751169 := bstep (se 2 (by rfl) ⟨9281688, by rfl⟩ : syracuseStep 24751169 = 18563377) B18563377
theorem B1715271 : Blo 1715058 1715271 := bstep (se 1 (by rfl) ⟨1286453, by rfl⟩ : syracuseStep 1715271 = 2572907) B2572907
theorem B2575481 : Blo 1715058 2575481 := bstep (se 2 (by rfl) ⟨965805, by rfl⟩ : syracuseStep 2575481 = 1931611) B1931611
theorem B1715423 : Blo 1715058 1715423 := bstep (se 1 (by rfl) ⟨1286567, by rfl⟩ : syracuseStep 1715423 = 2573135) B2573135
theorem B2575583 : Blo 1715058 2575583 := bstep (se 1 (by rfl) ⟨1931687, by rfl⟩ : syracuseStep 2575583 = 3863375) B3863375
theorem B32984333 : Blo 1715058 32984333 := bstep (se 3 (by rfl) ⟨6184562, by rfl⟩ : syracuseStep 32984333 = 12369125) B12369125
theorem B13028687 : Blo 1715058 13028687 := bstep (se 1 (by rfl) ⟨9771515, by rfl⟩ : syracuseStep 13028687 = 19543031) B19543031
theorem B1715687 : Blo 1715058 1715687 := bstep (se 1 (by rfl) ⟨1286765, by rfl⟩ : syracuseStep 1715687 = 2573531) B2573531
theorem B3862007 : Blo 1715058 3862007 := bstep (se 1 (by rfl) ⟨2896505, by rfl⟩ : syracuseStep 3862007 = 5793011) B5793011
theorem B3862079 : Blo 1715058 3862079 := bstep (se 1 (by rfl) ⟨2896559, by rfl⟩ : syracuseStep 3862079 = 5793119) B5793119
theorem B1715803 : Blo 1715058 1715803 := bstep (se 1 (by rfl) ⟨1286852, by rfl⟩ : syracuseStep 1715803 = 2573705) B2573705
theorem B3665515 : Blo 1715058 3665515 := bstep (se 1 (by rfl) ⟨2749136, by rfl⟩ : syracuseStep 3665515 = 5498273) B5498273
theorem B9776801 : Blo 1715058 9776801 := bstep (se 2 (by rfl) ⟨3666300, by rfl⟩ : syracuseStep 9776801 = 7332601) B7332601
theorem B26775241 : Blo 1715058 26775241 := bstep (se 2 (by rfl) ⟨10040715, by rfl⟩ : syracuseStep 26775241 = 20081431) B20081431
theorem B2895655 : Blo 1715058 2895655 := bstep (se 1 (by rfl) ⟨2171741, by rfl⟩ : syracuseStep 2895655 = 4343483) B4343483
theorem B1716039 : Blo 1715058 1716039 := bstep (se 1 (by rfl) ⟨1287029, by rfl⟩ : syracuseStep 1716039 = 2574059) B2574059
theorem B4345721 : Blo 1715058 4345721 := bstep (se 2 (by rfl) ⟨1629645, by rfl⟩ : syracuseStep 4345721 = 3259291) B3259291
theorem B1716191 : Blo 1715058 1716191 := bstep (se 1 (by rfl) ⟨1287143, by rfl⟩ : syracuseStep 1716191 = 2574287) B2574287
theorem B8245469 : Blo 1715058 8245469 := bstep (se 3 (by rfl) ⟨1546025, by rfl⟩ : syracuseStep 8245469 = 3092051) B3092051
theorem B1716455 : Blo 1715058 1716455 := bstep (se 1 (by rfl) ⟨1287341, by rfl⟩ : syracuseStep 1716455 = 2574683) B2574683
theorem B5648669 : Blo 1715058 5648669 := bstep (se 3 (by rfl) ⟨1059125, by rfl⟩ : syracuseStep 5648669 = 2118251) B2118251
theorem B1716607 : Blo 1715058 1716607 := bstep (se 1 (by rfl) ⟨1287455, by rfl⟩ : syracuseStep 1716607 = 2574911) B2574911
theorem B1716687 : Blo 1715058 1716687 := bstep (se 1 (by rfl) ⟨1287515, by rfl⟩ : syracuseStep 1716687 = 2575031) B2575031
theorem B3863033 : Blo 1715058 3863033 := bstep (se 2 (by rfl) ⟨1448637, by rfl⟩ : syracuseStep 3863033 = 2897275) B2897275
theorem B3863123 : Blo 1715058 3863123 := bstep (se 1 (by rfl) ⟨2897342, by rfl⟩ : syracuseStep 3863123 = 5794685) B5794685
theorem B1716839 : Blo 1715058 1716839 := bstep (se 1 (by rfl) ⟨1287629, by rfl⟩ : syracuseStep 1716839 = 2575259) B2575259
theorem B10990343 : Blo 1715058 10990343 := bstep (se 1 (by rfl) ⟨8242757, by rfl⟩ : syracuseStep 10990343 = 16485515) B16485515
theorem B3863303 : Blo 1715058 3863303 := bstep (se 1 (by rfl) ⟨2897477, by rfl⟩ : syracuseStep 3863303 = 5794955) B5794955
theorem B2896681 : Blo 1715058 2896681 := bstep (se 2 (by rfl) ⟨1086255, by rfl⟩ : syracuseStep 2896681 = 2172511) B2172511
theorem B14652353 : Blo 1715058 14652353 := bstep (se 2 (by rfl) ⟨5494632, by rfl⟩ : syracuseStep 14652353 = 10989265) B10989265
theorem B3093499 : Blo 1715058 3093499 := bstep (se 1 (by rfl) ⟨2320124, by rfl⟩ : syracuseStep 3093499 = 4640249) B4640249
theorem B11744293 : Blo 1715058 11744293 := bstep (se 4 (by rfl) ⟨1101027, by rfl⟩ : syracuseStep 11744293 = 2202055) B2202055
theorem B24728615 : Blo 1715058 24728615 := bstep (se 1 (by rfl) ⟨18546461, by rfl⟩ : syracuseStep 24728615 = 37092923) B37092923
theorem B2896951 : Blo 1715058 2896951 := bstep (se 1 (by rfl) ⟨2172713, by rfl⟩ : syracuseStep 2896951 = 4345427) B4345427
theorem B5788745 : Blo 1715058 5788745 := bstep (se 2 (by rfl) ⟨2170779, by rfl⟩ : syracuseStep 5788745 = 4341559) B4341559
theorem B10433609 : Blo 1715058 10433609 := bstep (se 2 (by rfl) ⟨3912603, by rfl⟩ : syracuseStep 10433609 = 7825207) B7825207
theorem B2749547 : Blo 1715058 2749547 := bstep (se 1 (by rfl) ⟨2062160, by rfl⟩ : syracuseStep 2749547 = 4124321) B4124321
theorem B6182027 : Blo 1715058 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B5649695 : Blo 1715058 5649695 := bstep (se 1 (by rfl) ⟨4237271, by rfl⟩ : syracuseStep 5649695 = 8474543) B8474543
theorem B6518171 : Blo 1715058 6518171 := bstep (se 1 (by rfl) ⟨4888628, by rfl⟩ : syracuseStep 6518171 = 9777257) B9777257
theorem B3094127 : Blo 1715058 3094127 := bstep (se 1 (by rfl) ⟨2320595, by rfl⟩ : syracuseStep 3094127 = 4641191) B4641191
theorem B10991315 : Blo 1715058 10991315 := bstep (se 1 (by rfl) ⟨8243486, by rfl⟩ : syracuseStep 10991315 = 16486973) B16486973
theorem B1931071 : Blo 1715058 1931071 := bstep (se 1 (by rfl) ⟨1448303, by rfl⟩ : syracuseStep 1931071 = 2896607) B2896607
theorem B10991497 : Blo 1715058 10991497 := bstep (se 2 (by rfl) ⟨4121811, by rfl⟩ : syracuseStep 10991497 = 8243623) B8243623
theorem B4954105 : Blo 1715058 4954105 := bstep (se 2 (by rfl) ⟨1857789, by rfl⟩ : syracuseStep 4954105 = 3715579) B3715579
theorem B3258463 : Blo 1715058 3258463 := bstep (se 1 (by rfl) ⟨2443847, by rfl⟩ : syracuseStep 3258463 = 4887695) B4887695
theorem B1931359 : Blo 1715058 1931359 := bstep (se 1 (by rfl) ⟨1448519, by rfl⟩ : syracuseStep 1931359 = 2897039) B2897039
theorem B3913991 : Blo 1715058 3913991 := bstep (se 1 (by rfl) ⟨2935493, by rfl⟩ : syracuseStep 3913991 = 5870987) B5870987
theorem B6519113 : Blo 1715058 6519113 := bstep (se 2 (by rfl) ⟨2444667, by rfl⟩ : syracuseStep 6519113 = 4889335) B4889335
theorem B10991983 : Blo 1715058 10991983 := bstep (se 1 (by rfl) ⟨8243987, by rfl⟩ : syracuseStep 10991983 = 16487975) B16487975
theorem B6183481 : Blo 1715058 6183481 := bstep (se 2 (by rfl) ⟨2318805, by rfl⟩ : syracuseStep 6183481 = 4637611) B4637611
theorem B98966123 : Blo 1715058 98966123 := bstep (se 1 (by rfl) ⟨74224592, by rfl⟩ : syracuseStep 98966123 = 148449185) B148449185
theorem B9910937 : Blo 1715058 9910937 := bstep (se 2 (by rfl) ⟨3716601, by rfl⟩ : syracuseStep 9910937 = 7433203) B7433203
theorem B5495453 : Blo 1715058 5495453 := bstep (se 3 (by rfl) ⟨1030397, by rfl⟩ : syracuseStep 5495453 = 2060795) B2060795
theorem B5790365 : Blo 1715058 5790365 := bstep (se 3 (by rfl) ⟨1085693, by rfl⟩ : syracuseStep 5790365 = 2171387) B2171387
theorem B9771677 : Blo 1715058 9771677 := bstep (se 3 (by rfl) ⟨1832189, by rfl⟩ : syracuseStep 9771677 = 3664379) B3664379
theorem B41745107 : Blo 1715058 41745107 := bstep (se 1 (by rfl) ⟨31308830, by rfl⟩ : syracuseStep 41745107 = 62617661) B62617661
theorem B31308545 : Blo 1715058 31308545 := bstep (se 2 (by rfl) ⟨11740704, by rfl⟩ : syracuseStep 31308545 = 23481409) B23481409
theorem B16497431 : Blo 1715058 16497431 := bstep (se 1 (by rfl) ⟨12373073, by rfl⟩ : syracuseStep 16497431 = 24746147) B24746147
theorem B11000747 : Blo 1715058 11000747 := bstep (se 1 (by rfl) ⟨8250560, by rfl⟩ : syracuseStep 11000747 = 16501121) B16501121
theorem B5790689 : Blo 1715058 5790689 := bstep (se 2 (by rfl) ⟨2171508, by rfl⟩ : syracuseStep 5790689 = 4343017) B4343017
theorem B3480545 : Blo 1715058 3480545 := bstep (se 2 (by rfl) ⟨1305204, by rfl⟩ : syracuseStep 3480545 = 2610409) B2610409
theorem B8690813 : Blo 1715058 8690813 := bstep (se 3 (by rfl) ⟨1629527, by rfl⟩ : syracuseStep 8690813 = 3259055) B3259055
theorem B44604593 : Blo 1715058 44604593 := bstep (se 2 (by rfl) ⟨16726722, by rfl⟩ : syracuseStep 44604593 = 33453445) B33453445
theorem B5790905 : Blo 1715058 5790905 := bstep (se 2 (by rfl) ⟨2171589, by rfl⟩ : syracuseStep 5790905 = 4343179) B4343179
theorem B9772427 : Blo 1715058 9772427 := bstep (se 1 (by rfl) ⟨7329320, by rfl⟩ : syracuseStep 9772427 = 14658641) B14658641
theorem B14654951 : Blo 1715058 14654951 := bstep (se 1 (by rfl) ⟨10991213, by rfl⟩ : syracuseStep 14654951 = 21982427) B21982427
theorem B7331303 : Blo 1715058 7331303 := bstep (se 1 (by rfl) ⟨5498477, by rfl⟩ : syracuseStep 7331303 = 10996955) B10996955
theorem B6512507 : Blo 1715058 6512507 := bstep (se 1 (by rfl) ⟨4884380, by rfl⟩ : syracuseStep 6512507 = 9768761) B9768761
theorem B5496979 : Blo 1715058 5496979 := bstep (se 1 (by rfl) ⟨4122734, by rfl⟩ : syracuseStep 5496979 = 8245469) B8245469
theorem B4341995 : Blo 1715058 4341995 := bstep (se 1 (by rfl) ⟨3256496, by rfl⟩ : syracuseStep 4341995 = 6512993) B6512993
theorem B10436843 : Blo 1715058 10436843 := bstep (se 1 (by rfl) ⟨7827632, by rfl⟩ : syracuseStep 10436843 = 15655265) B15655265
theorem B14655977 : Blo 1715058 14655977 := bstep (se 2 (by rfl) ⟨5495991, by rfl⟩ : syracuseStep 14655977 = 10991983) B10991983
theorem B13034033 : Blo 1715058 13034033 := bstep (se 2 (by rfl) ⟨4887762, by rfl⟩ : syracuseStep 13034033 = 9775525) B9775525
theorem B10994291 : Blo 1715058 10994291 := bstep (se 1 (by rfl) ⟨8245718, by rfl⟩ : syracuseStep 10994291 = 16491437) B16491437
theorem B6513281 : Blo 1715058 6513281 := bstep (se 2 (by rfl) ⟨2442480, by rfl⟩ : syracuseStep 6513281 = 4884961) B4884961
theorem B3859163 : Blo 1715058 3859163 := bstep (se 1 (by rfl) ⟨2894372, by rfl⟩ : syracuseStep 3859163 = 5788745) B5788745
theorem B6955739 : Blo 1715058 6955739 := bstep (se 1 (by rfl) ⟨5216804, by rfl⟩ : syracuseStep 6955739 = 10433609) B10433609
theorem B4121351 : Blo 1715058 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B2573255 : Blo 1715058 2573255 := bstep (se 1 (by rfl) ⟨1929941, by rfl⟩ : syracuseStep 2573255 = 3859883) B3859883
theorem B16483283 : Blo 1715058 16483283 := bstep (se 1 (by rfl) ⟨12362462, by rfl⟩ : syracuseStep 16483283 = 24724925) B24724925
theorem B2573423 : Blo 1715058 2573423 := bstep (se 1 (by rfl) ⟨1930067, by rfl⟩ : syracuseStep 2573423 = 3860135) B3860135
theorem B3859577 : Blo 1715058 3859577 := bstep (se 2 (by rfl) ⟨1447341, by rfl⟩ : syracuseStep 3859577 = 2894683) B2894683
theorem B8242411 : Blo 1715058 8242411 := bstep (se 1 (by rfl) ⟨6181808, by rfl⟩ : syracuseStep 8242411 = 12363617) B12363617
theorem B2573615 : Blo 1715058 2573615 := bstep (se 1 (by rfl) ⟨1930211, by rfl⟩ : syracuseStep 2573615 = 3860423) B3860423
theorem B2573819 : Blo 1715058 2573819 := bstep (se 1 (by rfl) ⟨1930364, by rfl⟩ : syracuseStep 2573819 = 3860729) B3860729
theorem B571205141 : Blo 1715058 571205141 := bstep (se 6 (by rfl) ⟨13387620, by rfl⟩ : syracuseStep 571205141 = 26775241) B26775241
theorem B2573855 : Blo 1715058 2573855 := bstep (se 1 (by rfl) ⟨1930391, by rfl⟩ : syracuseStep 2573855 = 3860783) B3860783
theorem B9274961 : Blo 1715058 9274961 := bstep (se 2 (by rfl) ⟨3478110, by rfl⟩ : syracuseStep 9274961 = 6956221) B6956221
theorem B2573999 : Blo 1715058 2573999 := bstep (se 1 (by rfl) ⟨1930499, by rfl⟩ : syracuseStep 2573999 = 3860999) B3860999
theorem B26429165 : Blo 1715058 26429165 := bstep (se 3 (by rfl) ⟨4955468, by rfl⟩ : syracuseStep 26429165 = 9910937) B9910937
theorem B3663635 : Blo 1715058 3663635 := bstep (se 1 (by rfl) ⟨2747726, by rfl⟩ : syracuseStep 3663635 = 5495453) B5495453
theorem B3860243 : Blo 1715058 3860243 := bstep (se 1 (by rfl) ⟨2895182, by rfl⟩ : syracuseStep 3860243 = 5790365) B5790365
theorem B6514451 : Blo 1715058 6514451 := bstep (se 1 (by rfl) ⟨4885838, by rfl⟩ : syracuseStep 6514451 = 9771677) B9771677
theorem B2574119 : Blo 1715058 2574119 := bstep (se 1 (by rfl) ⟨1930589, by rfl⟩ : syracuseStep 2574119 = 3861179) B3861179
theorem B27830071 : Blo 1715058 27830071 := bstep (se 1 (by rfl) ⟨20872553, by rfl⟩ : syracuseStep 27830071 = 41745107) B41745107
theorem B7333831 : Blo 1715058 7333831 := bstep (se 1 (by rfl) ⟨5500373, by rfl⟩ : syracuseStep 7333831 = 11000747) B11000747
theorem B3860459 : Blo 1715058 3860459 := bstep (se 1 (by rfl) ⟨2895344, by rfl⟩ : syracuseStep 3860459 = 5790689) B5790689
theorem B2320363 : Blo 1715058 2320363 := bstep (se 1 (by rfl) ⟨1740272, by rfl⟩ : syracuseStep 2320363 = 3480545) B3480545
theorem B16500779 : Blo 1715058 16500779 := bstep (se 1 (by rfl) ⟨12375584, by rfl⟩ : syracuseStep 16500779 = 24751169) B24751169
theorem B5793875 : Blo 1715058 5793875 := bstep (se 1 (by rfl) ⟨4345406, by rfl⟩ : syracuseStep 5793875 = 8690813) B8690813
theorem B3860603 : Blo 1715058 3860603 := bstep (se 1 (by rfl) ⟨2895452, by rfl⟩ : syracuseStep 3860603 = 5790905) B5790905
theorem B21989555 : Blo 1715058 21989555 := bstep (se 1 (by rfl) ⟨16492166, by rfl⟩ : syracuseStep 21989555 = 32984333) B32984333
theorem B8685791 : Blo 1715058 8685791 := bstep (se 1 (by rfl) ⟨6514343, by rfl⟩ : syracuseStep 8685791 = 13028687) B13028687
theorem B6514951 : Blo 1715058 6514951 := bstep (se 1 (by rfl) ⟨4886213, by rfl⟩ : syracuseStep 6514951 = 9772427) B9772427
theorem B21457181 : Blo 1715058 21457181 := bstep (se 3 (by rfl) ⟨4023221, by rfl⟩ : syracuseStep 21457181 = 8046443) B8046443
theorem B2574671 : Blo 1715058 2574671 := bstep (se 1 (by rfl) ⟨1931003, by rfl⟩ : syracuseStep 2574671 = 3862007) B3862007
theorem B2574719 : Blo 1715058 2574719 := bstep (se 1 (by rfl) ⟨1931039, by rfl⟩ : syracuseStep 2574719 = 3862079) B3862079
theorem B3860873 : Blo 1715058 3860873 := bstep (se 2 (by rfl) ⟨1447827, by rfl⟩ : syracuseStep 3860873 = 2895655) B2895655
theorem B2574761 : Blo 1715058 2574761 := bstep (se 2 (by rfl) ⟨965535, by rfl⟩ : syracuseStep 2574761 = 1931071) B1931071
theorem B6605473 : Blo 1715058 6605473 := bstep (se 2 (by rfl) ⟨2477052, by rfl⟩ : syracuseStep 6605473 = 4954105) B4954105
theorem B4344617 : Blo 1715058 4344617 := bstep (se 2 (by rfl) ⟨1629231, by rfl⟩ : syracuseStep 4344617 = 3258463) B3258463
theorem B2575145 : Blo 1715058 2575145 := bstep (se 2 (by rfl) ⟨965679, by rfl⟩ : syracuseStep 2575145 = 1931359) B1931359
theorem B1715167 : Blo 1715058 1715167 := bstep (se 1 (by rfl) ⟨1286375, by rfl⟩ : syracuseStep 1715167 = 2572751) B2572751
theorem B1715195 : Blo 1715058 1715195 := bstep (se 1 (by rfl) ⟨1286396, by rfl⟩ : syracuseStep 1715195 = 2572793) B2572793
theorem B2575355 : Blo 1715058 2575355 := bstep (se 1 (by rfl) ⟨1931516, by rfl⟩ : syracuseStep 2575355 = 3863033) B3863033
theorem B2575415 : Blo 1715058 2575415 := bstep (se 1 (by rfl) ⟨1931561, by rfl⟩ : syracuseStep 2575415 = 3863123) B3863123
theorem B1715263 : Blo 1715058 1715263 := bstep (se 1 (by rfl) ⟨1286447, by rfl⟩ : syracuseStep 1715263 = 2572895) B2572895
theorem B3861575 : Blo 1715058 3861575 := bstep (se 1 (by rfl) ⟨2896181, by rfl⟩ : syracuseStep 3861575 = 5792363) B5792363
theorem B7326895 : Blo 1715058 7326895 := bstep (se 1 (by rfl) ⟨5495171, by rfl⟩ : syracuseStep 7326895 = 10990343) B10990343
theorem B2575535 : Blo 1715058 2575535 := bstep (se 1 (by rfl) ⟨1931651, by rfl⟩ : syracuseStep 2575535 = 3863303) B3863303
theorem B9768235 : Blo 1715058 9768235 := bstep (se 1 (by rfl) ⟨7326176, by rfl⟩ : syracuseStep 9768235 = 14652353) B14652353
theorem B3665207 : Blo 1715058 3665207 := bstep (se 1 (by rfl) ⟨2748905, by rfl⟩ : syracuseStep 3665207 = 5497811) B5497811
theorem B16485743 : Blo 1715058 16485743 := bstep (se 1 (by rfl) ⟨12364307, by rfl⟩ : syracuseStep 16485743 = 24728615) B24728615
theorem B1715583 : Blo 1715058 1715583 := bstep (se 1 (by rfl) ⟨1286687, by rfl⟩ : syracuseStep 1715583 = 2573375) B2573375
theorem B1715611 : Blo 1715058 1715611 := bstep (se 1 (by rfl) ⟨1286708, by rfl⟩ : syracuseStep 1715611 = 2573417) B2573417
theorem B8244641 : Blo 1715058 8244641 := bstep (se 2 (by rfl) ⟨3091740, by rfl⟩ : syracuseStep 8244641 = 6183481) B6183481
theorem B3861971 : Blo 1715058 3861971 := bstep (se 1 (by rfl) ⟨2896478, by rfl⟩ : syracuseStep 3861971 = 5792957) B5792957
theorem B1715679 : Blo 1715058 1715679 := bstep (se 1 (by rfl) ⟨1286759, by rfl⟩ : syracuseStep 1715679 = 2573519) B2573519
theorem B1715815 : Blo 1715058 1715815 := bstep (se 1 (by rfl) ⟨1286861, by rfl⟩ : syracuseStep 1715815 = 2573723) B2573723
theorem B4345447 : Blo 1715058 4345447 := bstep (se 1 (by rfl) ⟨3259085, by rfl⟩ : syracuseStep 4345447 = 6518171) B6518171
theorem B3256033 : Blo 1715058 3256033 := bstep (se 2 (by rfl) ⟨1221012, by rfl⟩ : syracuseStep 3256033 = 2442025) B2442025
theorem B3862241 : Blo 1715058 3862241 := bstep (se 2 (by rfl) ⟨1448340, by rfl⟩ : syracuseStep 3862241 = 2896681) B2896681
theorem B1715963 : Blo 1715058 1715963 := bstep (se 1 (by rfl) ⟨1286972, by rfl⟩ : syracuseStep 1715963 = 2573945) B2573945
theorem B1716031 : Blo 1715058 1716031 := bstep (se 1 (by rfl) ⟨1287023, by rfl⟩ : syracuseStep 1716031 = 2574047) B2574047
theorem B12365693 : Blo 1715058 12365693 := bstep (se 3 (by rfl) ⟨2318567, by rfl⟩ : syracuseStep 12365693 = 4637135) B4637135
theorem B1716095 : Blo 1715058 1716095 := bstep (se 1 (by rfl) ⟨1287071, by rfl⟩ : syracuseStep 1716095 = 2574143) B2574143
theorem B1716207 : Blo 1715058 1716207 := bstep (se 1 (by rfl) ⟨1287155, by rfl⟩ : syracuseStep 1716207 = 2574311) B2574311
theorem B4124665 : Blo 1715058 4124665 := bstep (se 2 (by rfl) ⟨1546749, by rfl⟩ : syracuseStep 4124665 = 3093499) B3093499
theorem B1716219 : Blo 1715058 1716219 := bstep (se 1 (by rfl) ⟨1287164, by rfl⟩ : syracuseStep 1716219 = 2574329) B2574329
theorem B15659057 : Blo 1715058 15659057 := bstep (se 2 (by rfl) ⟨5872146, by rfl⟩ : syracuseStep 15659057 = 11744293) B11744293
theorem B1716287 : Blo 1715058 1716287 := bstep (se 1 (by rfl) ⟨1287215, by rfl⟩ : syracuseStep 1716287 = 2574431) B2574431
theorem B3862601 : Blo 1715058 3862601 := bstep (se 2 (by rfl) ⟨1448475, by rfl⟩ : syracuseStep 3862601 = 2896951) B2896951
theorem B1716327 : Blo 1715058 1716327 := bstep (se 1 (by rfl) ⟨1287245, by rfl⟩ : syracuseStep 1716327 = 2574491) B2574491
theorem B1716351 : Blo 1715058 1716351 := bstep (se 1 (by rfl) ⟨1287263, by rfl⟩ : syracuseStep 1716351 = 2574527) B2574527
theorem B3862655 : Blo 1715058 3862655 := bstep (se 1 (by rfl) ⟨2896991, by rfl⟩ : syracuseStep 3862655 = 5793983) B5793983
theorem B1716379 : Blo 1715058 1716379 := bstep (se 1 (by rfl) ⟨1287284, by rfl⟩ : syracuseStep 1716379 = 2574569) B2574569
theorem B2609327 : Blo 1715058 2609327 := bstep (se 1 (by rfl) ⟨1956995, by rfl⟩ : syracuseStep 2609327 = 3913991) B3913991
theorem B4346075 : Blo 1715058 4346075 := bstep (se 1 (by rfl) ⟨3259556, by rfl⟩ : syracuseStep 4346075 = 6519113) B6519113
theorem B3092743 : Blo 1715058 3092743 := bstep (se 1 (by rfl) ⟨2319557, by rfl⟩ : syracuseStep 3092743 = 4639115) B4639115
theorem B4124935 : Blo 1715058 4124935 := bstep (se 1 (by rfl) ⟨3093701, by rfl⟩ : syracuseStep 4124935 = 6187403) B6187403
theorem B3256595 : Blo 1715058 3256595 := bstep (se 1 (by rfl) ⟨2442446, by rfl⟩ : syracuseStep 3256595 = 4884893) B4884893
theorem B3256679 : Blo 1715058 3256679 := bstep (se 1 (by rfl) ⟨2442509, by rfl⟩ : syracuseStep 3256679 = 4885019) B4885019
theorem B1716583 : Blo 1715058 1716583 := bstep (se 1 (by rfl) ⟨1287437, by rfl⟩ : syracuseStep 1716583 = 2574875) B2574875
theorem B2060699 : Blo 1715058 2060699 := bstep (se 1 (by rfl) ⟨1545524, by rfl⟩ : syracuseStep 2060699 = 3091049) B3091049
theorem B2896283 : Blo 1715058 2896283 := bstep (se 1 (by rfl) ⟨2172212, by rfl⟩ : syracuseStep 2896283 = 4344425) B4344425
theorem B1716635 : Blo 1715058 1716635 := bstep (se 1 (by rfl) ⟨1287476, by rfl⟩ : syracuseStep 1716635 = 2574953) B2574953
theorem B6517199 : Blo 1715058 6517199 := bstep (se 1 (by rfl) ⟨4887899, by rfl⟩ : syracuseStep 6517199 = 9775799) B9775799
theorem B10998287 : Blo 1715058 10998287 := bstep (se 1 (by rfl) ⟨8248715, by rfl⟩ : syracuseStep 10998287 = 16497431) B16497431
theorem B63443573 : Blo 1715058 63443573 := bstep (se 5 (by rfl) ⟨2973917, by rfl⟩ : syracuseStep 63443573 = 5947835) B5947835
theorem B1716987 : Blo 1715058 1716987 := bstep (se 1 (by rfl) ⟨1287740, by rfl⟩ : syracuseStep 1716987 = 2575481) B2575481
theorem B4887353 : Blo 1715058 4887353 := bstep (se 2 (by rfl) ⟨1832757, by rfl⟩ : syracuseStep 4887353 = 3665515) B3665515
theorem B1717055 : Blo 1715058 1717055 := bstep (se 1 (by rfl) ⟨1287791, by rfl⟩ : syracuseStep 1717055 = 2575583) B2575583
theorem B9769967 : Blo 1715058 9769967 := bstep (se 1 (by rfl) ⟨7327475, by rfl⟩ : syracuseStep 9769967 = 14654951) B14654951
theorem B4887535 : Blo 1715058 4887535 := bstep (se 1 (by rfl) ⟨3665651, by rfl⟩ : syracuseStep 4887535 = 7331303) B7331303
theorem B6517867 : Blo 1715058 6517867 := bstep (se 1 (by rfl) ⟨4888400, by rfl⟩ : syracuseStep 6517867 = 9776801) B9776801
theorem B2897147 : Blo 1715058 2897147 := bstep (se 1 (by rfl) ⟨2172860, by rfl⟩ : syracuseStep 2897147 = 4345721) B4345721
theorem B3765779 : Blo 1715058 3765779 := bstep (se 1 (by rfl) ⟨2824334, by rfl⟩ : syracuseStep 3765779 = 5648669) B5648669
theorem B12375611 : Blo 1715058 12375611 := bstep (se 1 (by rfl) ⟨9281708, by rfl⟩ : syracuseStep 12375611 = 18563417) B18563417
theorem B1833031 : Blo 1715058 1833031 := bstep (se 1 (by rfl) ⟨1374773, by rfl⟩ : syracuseStep 1833031 = 2749547) B2749547
theorem B3766463 : Blo 1715058 3766463 := bstep (se 1 (by rfl) ⟨2824847, by rfl⟩ : syracuseStep 3766463 = 5649695) B5649695
theorem B2062751 : Blo 1715058 2062751 := bstep (se 1 (by rfl) ⟨1547063, by rfl⟩ : syracuseStep 2062751 = 3094127) B3094127
theorem B22002313 : Blo 1715058 22002313 := bstep (se 2 (by rfl) ⟨8250867, by rfl⟩ : syracuseStep 22002313 = 16501735) B16501735
theorem B13032089 : Blo 1715058 13032089 := bstep (se 2 (by rfl) ⟨4887033, by rfl⟩ : syracuseStep 13032089 = 9774067) B9774067
theorem B14654267 : Blo 1715058 14654267 := bstep (se 1 (by rfl) ⟨10990700, by rfl⟩ : syracuseStep 14654267 = 21981401) B21981401
theorem B65977415 : Blo 1715058 65977415 := bstep (se 1 (by rfl) ⟨49483061, by rfl⟩ : syracuseStep 65977415 = 98966123) B98966123
theorem B20872363 : Blo 1715058 20872363 := bstep (se 1 (by rfl) ⟨15654272, by rfl⟩ : syracuseStep 20872363 = 31308545) B31308545
theorem B29310173 : Blo 1715058 29310173 := bstep (se 3 (by rfl) ⟨5495657, by rfl⟩ : syracuseStep 29310173 = 10991315) B10991315
theorem B29736395 : Blo 1715058 29736395 := bstep (se 1 (by rfl) ⟨22302296, by rfl⟩ : syracuseStep 29736395 = 44604593) B44604593
theorem B14655329 : Blo 1715058 14655329 := bstep (se 2 (by rfl) ⟨5495748, by rfl⟩ : syracuseStep 14655329 = 10991497) B10991497
theorem B4341671 : Blo 1715058 4341671 := bstep (se 1 (by rfl) ⟨3256253, by rfl⟩ : syracuseStep 4341671 = 6512507) B6512507
theorem B2171063 : Blo 1715058 2171063 := bstep (se 1 (by rfl) ⟨1628297, by rfl⟩ : syracuseStep 2171063 = 3256595) B3256595
theorem B2171119 : Blo 1715058 2171119 := bstep (se 1 (by rfl) ⟨1628339, by rfl⟩ : syracuseStep 2171119 = 3256679) B3256679
theorem B7332191 : Blo 1715058 7332191 := bstep (se 1 (by rfl) ⟨5499143, by rfl⟩ : syracuseStep 7332191 = 10998287) B10998287
theorem B42295715 : Blo 1715058 42295715 := bstep (se 1 (by rfl) ⟨31721786, by rfl⟩ : syracuseStep 42295715 = 63443573) B63443573
theorem B4342187 : Blo 1715058 4342187 := bstep (se 1 (by rfl) ⟨3256640, by rfl⟩ : syracuseStep 4342187 = 6513281) B6513281
theorem B2572775 : Blo 1715058 2572775 := bstep (se 1 (by rfl) ⟨1929581, by rfl⟩ : syracuseStep 2572775 = 3859163) B3859163
theorem B4637159 : Blo 1715058 4637159 := bstep (se 1 (by rfl) ⟨3477869, by rfl⟩ : syracuseStep 4637159 = 6955739) B6955739
theorem B6513311 : Blo 1715058 6513311 := bstep (se 1 (by rfl) ⟨4884983, by rfl⟩ : syracuseStep 6513311 = 9769967) B9769967
theorem B2573051 : Blo 1715058 2573051 := bstep (se 1 (by rfl) ⟨1929788, by rfl⟩ : syracuseStep 2573051 = 3859577) B3859577
theorem B9773885 : Blo 1715058 9773885 := bstep (se 3 (by rfl) ⟨1832603, by rfl⟩ : syracuseStep 9773885 = 3665207) B3665207
theorem B29336417 : Blo 1715058 29336417 := bstep (se 2 (by rfl) ⟨11001156, by rfl⟩ : syracuseStep 29336417 = 22002313) B22002313
theorem B8807297 : Blo 1715058 8807297 := bstep (se 2 (by rfl) ⟨3302736, by rfl⟩ : syracuseStep 8807297 = 6605473) B6605473
theorem B8250407 : Blo 1715058 8250407 := bstep (se 1 (by rfl) ⟨6187805, by rfl⟩ : syracuseStep 8250407 = 12375611) B12375611
theorem B2573495 : Blo 1715058 2573495 := bstep (se 1 (by rfl) ⟨1930121, by rfl⟩ : syracuseStep 2573495 = 3860243) B3860243
theorem B4342967 : Blo 1715058 4342967 := bstep (se 1 (by rfl) ⟨3257225, by rfl⟩ : syracuseStep 4342967 = 6514451) B6514451
theorem B2573639 : Blo 1715058 2573639 := bstep (se 1 (by rfl) ⟨1930229, by rfl⟩ : syracuseStep 2573639 = 3860459) B3860459
theorem B2573735 : Blo 1715058 2573735 := bstep (se 1 (by rfl) ⟨1930301, by rfl⟩ : syracuseStep 2573735 = 3860603) B3860603
theorem B27829817 : Blo 1715058 27829817 := bstep (se 2 (by rfl) ⟨10436181, by rfl⟩ : syracuseStep 27829817 = 20872363) B20872363
theorem B2573915 : Blo 1715058 2573915 := bstep (se 1 (by rfl) ⟨1930436, by rfl⟩ : syracuseStep 2573915 = 3860873) B3860873
theorem B43984943 : Blo 1715058 43984943 := bstep (se 1 (by rfl) ⟨32988707, by rfl⟩ : syracuseStep 43984943 = 65977415) B65977415
theorem B2574383 : Blo 1715058 2574383 := bstep (se 1 (by rfl) ⟨1930787, by rfl⟩ : syracuseStep 2574383 = 3861575) B3861575
theorem B5793929 : Blo 1715058 5793929 := bstep (se 2 (by rfl) ⟨2172723, by rfl⟩ : syracuseStep 5793929 = 4345447) B4345447
theorem B19540115 : Blo 1715058 19540115 := bstep (se 1 (by rfl) ⟨14655086, by rfl⟩ : syracuseStep 19540115 = 29310173) B29310173
theorem B2574647 : Blo 1715058 2574647 := bstep (se 1 (by rfl) ⟨1930985, by rfl⟩ : syracuseStep 2574647 = 3861971) B3861971
theorem B2574827 : Blo 1715058 2574827 := bstep (se 1 (by rfl) ⟨1931120, by rfl⟩ : syracuseStep 2574827 = 3862241) B3862241
theorem B8243795 : Blo 1715058 8243795 := bstep (se 1 (by rfl) ⟨6182846, by rfl⟩ : syracuseStep 8243795 = 12365693) B12365693
theorem B2894447 : Blo 1715058 2894447 := bstep (se 1 (by rfl) ⟨2170835, by rfl⟩ : syracuseStep 2894447 = 4341671) B4341671
theorem B21998213 : Blo 1715058 21998213 := bstep (se 4 (by rfl) ⟨2062332, by rfl⟩ : syracuseStep 21998213 = 4124665) B4124665
theorem B10439371 : Blo 1715058 10439371 := bstep (se 1 (by rfl) ⟨7829528, by rfl⟩ : syracuseStep 10439371 = 15659057) B15659057
theorem B2575067 : Blo 1715058 2575067 := bstep (se 1 (by rfl) ⟨1931300, by rfl⟩ : syracuseStep 2575067 = 3862601) B3862601
theorem B2575103 : Blo 1715058 2575103 := bstep (se 1 (by rfl) ⟨1931327, by rfl⟩ : syracuseStep 2575103 = 3862655) B3862655
theorem B2444041 : Blo 1715058 2444041 := bstep (se 2 (by rfl) ⟨916515, by rfl⟩ : syracuseStep 2444041 = 1833031) B1833031
theorem B1739551 : Blo 1715058 1739551 := bstep (se 1 (by rfl) ⟨1304663, by rfl⟩ : syracuseStep 1739551 = 2609327) B2609327
theorem B2894663 : Blo 1715058 2894663 := bstep (se 1 (by rfl) ⟨2170997, by rfl⟩ : syracuseStep 2894663 = 4341995) B4341995
theorem B6957895 : Blo 1715058 6957895 := bstep (se 1 (by rfl) ⟨5218421, by rfl⟩ : syracuseStep 6957895 = 10436843) B10436843
theorem B4344799 : Blo 1715058 4344799 := bstep (se 1 (by rfl) ⟨3258599, by rfl⟩ : syracuseStep 4344799 = 6517199) B6517199
theorem B8686601 : Blo 1715058 8686601 := bstep (se 2 (by rfl) ⟨3257475, by rfl⟩ : syracuseStep 8686601 = 6514951) B6514951
theorem B4123657 : Blo 1715058 4123657 := bstep (se 2 (by rfl) ⟨1546371, by rfl⟩ : syracuseStep 4123657 = 3092743) B3092743
theorem B5499913 : Blo 1715058 5499913 := bstep (se 2 (by rfl) ⟨2062467, by rfl⟩ : syracuseStep 5499913 = 4124935) B4124935
theorem B2747567 : Blo 1715058 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B1715503 : Blo 1715058 1715503 := bstep (se 1 (by rfl) ⟨1286627, by rfl⟩ : syracuseStep 1715503 = 2573255) B2573255
theorem B10988855 : Blo 1715058 10988855 := bstep (se 1 (by rfl) ⟨8241641, by rfl⟩ : syracuseStep 10988855 = 16483283) B16483283
theorem B1715615 : Blo 1715058 1715615 := bstep (se 1 (by rfl) ⟨1286711, by rfl⟩ : syracuseStep 1715615 = 2573423) B2573423
theorem B1715743 : Blo 1715058 1715743 := bstep (se 1 (by rfl) ⟨1286807, by rfl⟩ : syracuseStep 1715743 = 2573615) B2573615
theorem B1715879 : Blo 1715058 1715879 := bstep (se 1 (by rfl) ⟨1286909, by rfl⟩ : syracuseStep 1715879 = 2573819) B2573819
theorem B2510519 : Blo 1715058 2510519 := bstep (se 1 (by rfl) ⟨1882889, by rfl⟩ : syracuseStep 2510519 = 3765779) B3765779
theorem B1715903 : Blo 1715058 1715903 := bstep (se 1 (by rfl) ⟨1286927, by rfl⟩ : syracuseStep 1715903 = 2573855) B2573855
theorem B1715999 : Blo 1715058 1715999 := bstep (se 1 (by rfl) ⟨1286999, by rfl⟩ : syracuseStep 1715999 = 2573999) B2573999
theorem B1716079 : Blo 1715058 1716079 := bstep (se 1 (by rfl) ⟨1287059, by rfl⟩ : syracuseStep 1716079 = 2574119) B2574119
theorem B6516713 : Blo 1715058 6516713 := bstep (se 2 (by rfl) ⟨2443767, by rfl⟩ : syracuseStep 6516713 = 4887535) B4887535
theorem B3862583 : Blo 1715058 3862583 := bstep (se 1 (by rfl) ⟨2896937, by rfl⟩ : syracuseStep 3862583 = 5793875) B5793875
theorem B14659703 : Blo 1715058 14659703 := bstep (se 1 (by rfl) ⟨10994777, by rfl⟩ : syracuseStep 14659703 = 21989555) B21989555
theorem B2510975 : Blo 1715058 2510975 := bstep (se 1 (by rfl) ⟨1883231, by rfl⟩ : syracuseStep 2510975 = 3766463) B3766463
theorem B1716447 : Blo 1715058 1716447 := bstep (se 1 (by rfl) ⟨1287335, by rfl⟩ : syracuseStep 1716447 = 2574671) B2574671
theorem B9769193 : Blo 1715058 9769193 := bstep (se 2 (by rfl) ⟨3663447, by rfl⟩ : syracuseStep 9769193 = 7326895) B7326895
theorem B1716479 : Blo 1715058 1716479 := bstep (se 1 (by rfl) ⟨1287359, by rfl⟩ : syracuseStep 1716479 = 2574719) B2574719
theorem B1716507 : Blo 1715058 1716507 := bstep (se 1 (by rfl) ⟨1287380, by rfl⟩ : syracuseStep 1716507 = 2574761) B2574761
theorem B10989881 : Blo 1715058 10989881 := bstep (se 2 (by rfl) ⟨4121205, by rfl⟩ : syracuseStep 10989881 = 8242411) B8242411
theorem B8688059 : Blo 1715058 8688059 := bstep (se 1 (by rfl) ⟨6516044, by rfl⟩ : syracuseStep 8688059 = 13032089) B13032089
theorem B2896411 : Blo 1715058 2896411 := bstep (se 1 (by rfl) ⟨2172308, by rfl⟩ : syracuseStep 2896411 = 4344617) B4344617
theorem B1716763 : Blo 1715058 1716763 := bstep (se 1 (by rfl) ⟨1287572, by rfl⟩ : syracuseStep 1716763 = 2575145) B2575145
theorem B9769511 : Blo 1715058 9769511 := bstep (se 1 (by rfl) ⟨7327133, by rfl⟩ : syracuseStep 9769511 = 14654267) B14654267
theorem B1716903 : Blo 1715058 1716903 := bstep (se 1 (by rfl) ⟨1287677, by rfl⟩ : syracuseStep 1716903 = 2575355) B2575355
theorem B1716943 : Blo 1715058 1716943 := bstep (se 1 (by rfl) ⟨1287707, by rfl⟩ : syracuseStep 1716943 = 2575415) B2575415
theorem B9769693 : Blo 1715058 9769693 := bstep (se 3 (by rfl) ⟨1831817, by rfl⟩ : syracuseStep 9769693 = 3663635) B3663635
theorem B1717023 : Blo 1715058 1717023 := bstep (se 1 (by rfl) ⟨1287767, by rfl⟩ : syracuseStep 1717023 = 2575535) B2575535
theorem B10990495 : Blo 1715058 10990495 := bstep (se 1 (by rfl) ⟨8242871, by rfl⟩ : syracuseStep 10990495 = 16485743) B16485743
theorem B37106761 : Blo 1715058 37106761 := bstep (se 2 (by rfl) ⟨13915035, by rfl⟩ : syracuseStep 37106761 = 27830071) B27830071
theorem B9770219 : Blo 1715058 9770219 := bstep (se 1 (by rfl) ⟨7327664, by rfl⟩ : syracuseStep 9770219 = 14655329) B14655329
theorem B9778441 : Blo 1715058 9778441 := bstep (se 2 (by rfl) ⟨3666915, by rfl⟩ : syracuseStep 9778441 = 7333831) B7333831
theorem B3093817 : Blo 1715058 3093817 := bstep (se 2 (by rfl) ⟨1160181, by rfl⟩ : syracuseStep 3093817 = 2320363) B2320363
theorem B2897383 : Blo 1715058 2897383 := bstep (se 1 (by rfl) ⟨2173037, by rfl⟩ : syracuseStep 2897383 = 4346075) B4346075
theorem B7329305 : Blo 1715058 7329305 := bstep (se 2 (by rfl) ⟨2748489, by rfl⟩ : syracuseStep 7329305 = 5496979) B5496979
theorem B1930855 : Blo 1715058 1930855 := bstep (se 1 (by rfl) ⟨1448141, by rfl⟩ : syracuseStep 1930855 = 2896283) B2896283
theorem B9770651 : Blo 1715058 9770651 := bstep (se 1 (by rfl) ⟨7327988, by rfl⟩ : syracuseStep 9770651 = 14655977) B14655977
theorem B8689355 : Blo 1715058 8689355 := bstep (se 1 (by rfl) ⟨6517016, by rfl⟩ : syracuseStep 8689355 = 13034033) B13034033
theorem B7329527 : Blo 1715058 7329527 := bstep (se 1 (by rfl) ⟨5497145, by rfl⟩ : syracuseStep 7329527 = 10994291) B10994291
theorem B3258235 : Blo 1715058 3258235 := bstep (se 1 (by rfl) ⟨2443676, by rfl⟩ : syracuseStep 3258235 = 4887353) B4887353
theorem B57219149 : Blo 1715058 57219149 := bstep (se 3 (by rfl) ⟨10728590, by rfl⟩ : syracuseStep 57219149 = 21457181) B21457181
theorem B1931431 : Blo 1715058 1931431 := bstep (se 1 (by rfl) ⟨1448573, by rfl⟩ : syracuseStep 1931431 = 2897147) B2897147
theorem B380803427 : Blo 1715058 380803427 := bstep (se 1 (by rfl) ⟨285602570, by rfl⟩ : syracuseStep 380803427 = 571205141) B571205141
theorem B6183307 : Blo 1715058 6183307 := bstep (se 1 (by rfl) ⟨4637480, by rfl⟩ : syracuseStep 6183307 = 9274961) B9274961
theorem B5495197 : Blo 1715058 5495197 := bstep (se 3 (by rfl) ⟨1030349, by rfl⟩ : syracuseStep 5495197 = 2060699) B2060699
theorem B17619443 : Blo 1715058 17619443 := bstep (se 1 (by rfl) ⟨13214582, by rfl⟩ : syracuseStep 17619443 = 26429165) B26429165
theorem B11000519 : Blo 1715058 11000519 := bstep (se 1 (by rfl) ⟨8250389, by rfl⟩ : syracuseStep 11000519 = 16500779) B16500779
theorem B8690489 : Blo 1715058 8690489 := bstep (se 2 (by rfl) ⟨3258933, by rfl⟩ : syracuseStep 8690489 = 6517867) B6517867
theorem B5790527 : Blo 1715058 5790527 := bstep (se 1 (by rfl) ⟨4342895, by rfl⟩ : syracuseStep 5790527 = 8685791) B8685791
theorem B22002677 : Blo 1715058 22002677 := bstep (se 5 (by rfl) ⟨1031375, by rfl⟩ : syracuseStep 22002677 = 2062751) B2062751
theorem B13024313 : Blo 1715058 13024313 := bstep (se 2 (by rfl) ⟨4884117, by rfl⟩ : syracuseStep 13024313 = 9768235) B9768235
theorem B5496427 : Blo 1715058 5496427 := bstep (se 1 (by rfl) ⟨4122320, by rfl⟩ : syracuseStep 5496427 = 8244641) B8244641
theorem B4341377 : Blo 1715058 4341377 := bstep (se 2 (by rfl) ⟨1628016, by rfl⟩ : syracuseStep 4341377 = 3256033) B3256033
theorem B19824263 : Blo 1715058 19824263 := bstep (se 1 (by rfl) ⟨14868197, by rfl⟩ : syracuseStep 19824263 = 29736395) B29736395
theorem B9773135 : Blo 1715058 9773135 := bstep (se 1 (by rfl) ⟨7329851, by rfl⟩ : syracuseStep 9773135 = 14659703) B14659703
theorem B6512795 : Blo 1715058 6512795 := bstep (se 1 (by rfl) ⟨4884596, by rfl⟩ : syracuseStep 6512795 = 9769193) B9769193
theorem B152584397 : Blo 1715058 152584397 := bstep (se 3 (by rfl) ⟨28609574, by rfl⟩ : syracuseStep 152584397 = 57219149) B57219149
theorem B28197143 : Blo 1715058 28197143 := bstep (se 1 (by rfl) ⟨21147857, by rfl⟩ : syracuseStep 28197143 = 42295715) B42295715
theorem B5792039 : Blo 1715058 5792039 := bstep (se 1 (by rfl) ⟨4344029, by rfl⟩ : syracuseStep 5792039 = 8688059) B8688059
theorem B6513007 : Blo 1715058 6513007 := bstep (se 1 (by rfl) ⟨4884755, by rfl⟩ : syracuseStep 6513007 = 9769511) B9769511
theorem B4342207 : Blo 1715058 4342207 := bstep (se 1 (by rfl) ⟨3256655, by rfl⟩ : syracuseStep 4342207 = 6513311) B6513311
theorem B6513479 : Blo 1715058 6513479 := bstep (se 1 (by rfl) ⟨4885109, by rfl⟩ : syracuseStep 6513479 = 9770219) B9770219
theorem B13026257 : Blo 1715058 13026257 := bstep (se 2 (by rfl) ⟨4884846, by rfl⟩ : syracuseStep 13026257 = 9769693) B9769693
theorem B2319401 : Blo 1715058 2319401 := bstep (se 2 (by rfl) ⟨869775, by rfl⟩ : syracuseStep 2319401 = 1739551) B1739551
theorem B6513767 : Blo 1715058 6513767 := bstep (se 1 (by rfl) ⟨4885325, by rfl⟩ : syracuseStep 6513767 = 9770651) B9770651
theorem B5792903 : Blo 1715058 5792903 := bstep (se 1 (by rfl) ⟨4344677, by rfl⟩ : syracuseStep 5792903 = 8689355) B8689355
theorem B5793065 : Blo 1715058 5793065 := bstep (se 2 (by rfl) ⟨2172399, by rfl⟩ : syracuseStep 5793065 = 4344799) B4344799
theorem B5498209 : Blo 1715058 5498209 := bstep (se 2 (by rfl) ⟨2061828, by rfl⟩ : syracuseStep 5498209 = 4123657) B4123657
theorem B7333217 : Blo 1715058 7333217 := bstep (se 2 (by rfl) ⟨2749956, by rfl⟩ : syracuseStep 7333217 = 5499913) B5499913
theorem B13026743 : Blo 1715058 13026743 := bstep (se 1 (by rfl) ⟨9770057, by rfl⟩ : syracuseStep 13026743 = 19540115) B19540115
theorem B14665475 : Blo 1715058 14665475 := bstep (se 1 (by rfl) ⟨10999106, by rfl⟩ : syracuseStep 14665475 = 21998213) B21998213
theorem B7333679 : Blo 1715058 7333679 := bstep (se 1 (by rfl) ⟨5500259, by rfl⟩ : syracuseStep 7333679 = 11000519) B11000519
theorem B6694717 : Blo 1715058 6694717 := bstep (se 3 (by rfl) ⟨1255259, by rfl⟩ : syracuseStep 6694717 = 2510519) B2510519
theorem B5793659 : Blo 1715058 5793659 := bstep (se 1 (by rfl) ⟨4345244, by rfl⟩ : syracuseStep 5793659 = 8690489) B8690489
theorem B3860351 : Blo 1715058 3860351 := bstep (se 1 (by rfl) ⟨2895263, by rfl⟩ : syracuseStep 3860351 = 5790527) B5790527
theorem B2574473 : Blo 1715058 2574473 := bstep (se 2 (by rfl) ⟨965427, by rfl⟩ : syracuseStep 2574473 = 1930855) B1930855
theorem B7325903 : Blo 1715058 7325903 := bstep (se 1 (by rfl) ⟨5494427, by rfl⟩ : syracuseStep 7325903 = 10988855) B10988855
theorem B2894251 : Blo 1715058 2894251 := bstep (se 1 (by rfl) ⟨2170688, by rfl⟩ : syracuseStep 2894251 = 4341377) B4341377
theorem B13216175 : Blo 1715058 13216175 := bstep (se 1 (by rfl) ⟨9912131, by rfl⟩ : syracuseStep 13216175 = 19824263) B19824263
theorem B4344313 : Blo 1715058 4344313 := bstep (se 2 (by rfl) ⟨1629117, by rfl⟩ : syracuseStep 4344313 = 3258235) B3258235
theorem B4344475 : Blo 1715058 4344475 := bstep (se 1 (by rfl) ⟨3258356, by rfl⟩ : syracuseStep 4344475 = 6516713) B6516713
theorem B2575055 : Blo 1715058 2575055 := bstep (se 1 (by rfl) ⟨1931291, by rfl⟩ : syracuseStep 2575055 = 3862583) B3862583
theorem B7326587 : Blo 1715058 7326587 := bstep (se 1 (by rfl) ⟨5494940, by rfl⟩ : syracuseStep 7326587 = 10989881) B10989881
theorem B2575241 : Blo 1715058 2575241 := bstep (se 2 (by rfl) ⟨965715, by rfl⟩ : syracuseStep 2575241 = 1931431) B1931431
theorem B2894791 : Blo 1715058 2894791 := bstep (se 1 (by rfl) ⟨2171093, by rfl⟩ : syracuseStep 2894791 = 4342187) B4342187
theorem B2894825 : Blo 1715058 2894825 := bstep (se 2 (by rfl) ⟨1085559, by rfl⟩ : syracuseStep 2894825 = 2171119) B2171119
theorem B1715183 : Blo 1715058 1715183 := bstep (se 1 (by rfl) ⟨1286387, by rfl⟩ : syracuseStep 1715183 = 2572775) B2572775
theorem B3091439 : Blo 1715058 3091439 := bstep (se 1 (by rfl) ⟨2318579, by rfl⟩ : syracuseStep 3091439 = 4637159) B4637159
theorem B6695933 : Blo 1715058 6695933 := bstep (se 3 (by rfl) ⟨1255487, by rfl⟩ : syracuseStep 6695933 = 2510975) B2510975
theorem B7326845 : Blo 1715058 7326845 := bstep (se 3 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 7326845 = 2747567) B2747567
theorem B1715367 : Blo 1715058 1715367 := bstep (se 1 (by rfl) ⟨1286525, by rfl⟩ : syracuseStep 1715367 = 2573051) B2573051
theorem B7326929 : Blo 1715058 7326929 := bstep (se 2 (by rfl) ⟨2747598, by rfl⟩ : syracuseStep 7326929 = 5495197) B5495197
theorem B6515923 : Blo 1715058 6515923 := bstep (se 1 (by rfl) ⟨4886942, by rfl⟩ : syracuseStep 6515923 = 9773885) B9773885
theorem B19557611 : Blo 1715058 19557611 := bstep (se 1 (by rfl) ⟨14668208, by rfl⟩ : syracuseStep 19557611 = 29336417) B29336417
theorem B5500271 : Blo 1715058 5500271 := bstep (se 1 (by rfl) ⟨4125203, by rfl⟩ : syracuseStep 5500271 = 8250407) B8250407
theorem B3861881 : Blo 1715058 3861881 := bstep (se 2 (by rfl) ⟨1448205, by rfl⟩ : syracuseStep 3861881 = 2896411) B2896411
theorem B1715663 : Blo 1715058 1715663 := bstep (se 1 (by rfl) ⟨1286747, by rfl⟩ : syracuseStep 1715663 = 2573495) B2573495
theorem B2895311 : Blo 1715058 2895311 := bstep (se 1 (by rfl) ⟨2171483, by rfl⟩ : syracuseStep 2895311 = 4342967) B4342967
theorem B1715759 : Blo 1715058 1715759 := bstep (se 1 (by rfl) ⟨1286819, by rfl⟩ : syracuseStep 1715759 = 2573639) B2573639
theorem B1715823 : Blo 1715058 1715823 := bstep (se 1 (by rfl) ⟨1286867, by rfl⟩ : syracuseStep 1715823 = 2573735) B2573735
theorem B4886203 : Blo 1715058 4886203 := bstep (se 1 (by rfl) ⟨3664652, by rfl⟩ : syracuseStep 4886203 = 7329305) B7329305
theorem B55676645 : Blo 1715058 55676645 := bstep (se 4 (by rfl) ⟨5219685, by rfl⟩ : syracuseStep 55676645 = 10439371) B10439371
theorem B1715943 : Blo 1715058 1715943 := bstep (se 1 (by rfl) ⟨1286957, by rfl⟩ : syracuseStep 1715943 = 2573915) B2573915
theorem B9277193 : Blo 1715058 9277193 := bstep (se 2 (by rfl) ⟨3478947, by rfl⟩ : syracuseStep 9277193 = 6957895) B6957895
theorem B4886351 : Blo 1715058 4886351 := bstep (se 1 (by rfl) ⟨3664763, by rfl⟩ : syracuseStep 4886351 = 7329527) B7329527
theorem B29323295 : Blo 1715058 29323295 := bstep (se 1 (by rfl) ⟨21992471, by rfl⟩ : syracuseStep 29323295 = 43984943) B43984943
theorem B1716255 : Blo 1715058 1716255 := bstep (se 1 (by rfl) ⟨1287191, by rfl⟩ : syracuseStep 1716255 = 2574383) B2574383
theorem B3862619 : Blo 1715058 3862619 := bstep (se 1 (by rfl) ⟨2896964, by rfl⟩ : syracuseStep 3862619 = 5793929) B5793929
theorem B49475681 : Blo 1715058 49475681 := bstep (se 2 (by rfl) ⟨18553380, by rfl⟩ : syracuseStep 49475681 = 37106761) B37106761
theorem B1716431 : Blo 1715058 1716431 := bstep (se 1 (by rfl) ⟨1287323, by rfl⟩ : syracuseStep 1716431 = 2574647) B2574647
theorem B1716551 : Blo 1715058 1716551 := bstep (se 1 (by rfl) ⟨1287413, by rfl⟩ : syracuseStep 1716551 = 2574827) B2574827
theorem B13037921 : Blo 1715058 13037921 := bstep (se 2 (by rfl) ⟨4889220, by rfl⟩ : syracuseStep 13037921 = 9778441) B9778441
theorem B1929631 : Blo 1715058 1929631 := bstep (se 1 (by rfl) ⟨1447223, by rfl⟩ : syracuseStep 1929631 = 2894447) B2894447
theorem B4125089 : Blo 1715058 4125089 := bstep (se 2 (by rfl) ⟨1546908, by rfl⟩ : syracuseStep 4125089 = 3093817) B3093817
theorem B1716711 : Blo 1715058 1716711 := bstep (se 1 (by rfl) ⟨1287533, by rfl⟩ : syracuseStep 1716711 = 2575067) B2575067
theorem B1716735 : Blo 1715058 1716735 := bstep (se 1 (by rfl) ⟨1287551, by rfl⟩ : syracuseStep 1716735 = 2575103) B2575103
theorem B1929775 : Blo 1715058 1929775 := bstep (se 1 (by rfl) ⟨1447331, by rfl⟩ : syracuseStep 1929775 = 2894663) B2894663
theorem B3863177 : Blo 1715058 3863177 := bstep (se 2 (by rfl) ⟨1448691, by rfl⟩ : syracuseStep 3863177 = 2897383) B2897383
theorem B14668451 : Blo 1715058 14668451 := bstep (se 1 (by rfl) ⟨11001338, by rfl⟩ : syracuseStep 14668451 = 22002677) B22002677
theorem B32977637 : Blo 1715058 32977637 := bstep (se 4 (by rfl) ⟨3091653, by rfl⟩ : syracuseStep 32977637 = 6183307) B6183307
theorem B7328569 : Blo 1715058 7328569 := bstep (se 2 (by rfl) ⟨2748213, by rfl⟩ : syracuseStep 7328569 = 5496427) B5496427
theorem B4888127 : Blo 1715058 4888127 := bstep (se 1 (by rfl) ⟨3666095, by rfl⟩ : syracuseStep 4888127 = 7332191) B7332191
theorem B5789501 : Blo 1715058 5789501 := bstep (se 3 (by rfl) ⟨1085531, by rfl⟩ : syracuseStep 5789501 = 2171063) B2171063
theorem B3258721 : Blo 1715058 3258721 := bstep (se 2 (by rfl) ⟨1222020, by rfl⟩ : syracuseStep 3258721 = 2444041) B2444041
theorem B18553211 : Blo 1715058 18553211 := bstep (se 1 (by rfl) ⟨13914908, by rfl⟩ : syracuseStep 18553211 = 27829817) B27829817
theorem B14653993 : Blo 1715058 14653993 := bstep (se 2 (by rfl) ⟨5495247, by rfl⟩ : syracuseStep 14653993 = 10990495) B10990495
theorem B253868951 : Blo 1715058 253868951 := bstep (se 1 (by rfl) ⟨190401713, by rfl⟩ : syracuseStep 253868951 = 380803427) B380803427
theorem B11746295 : Blo 1715058 11746295 := bstep (se 1 (by rfl) ⟨8809721, by rfl⟩ : syracuseStep 11746295 = 17619443) B17619443
theorem B5495863 : Blo 1715058 5495863 := bstep (se 1 (by rfl) ⟨4121897, by rfl⟩ : syracuseStep 5495863 = 8243795) B8243795
theorem B5791067 : Blo 1715058 5791067 := bstep (se 1 (by rfl) ⟨4343300, by rfl⟩ : syracuseStep 5791067 = 8686601) B8686601
theorem B8682875 : Blo 1715058 8682875 := bstep (se 1 (by rfl) ⟨6512156, by rfl⟩ : syracuseStep 8682875 = 13024313) B13024313
theorem B23486125 : Blo 1715058 23486125 := bstep (se 3 (by rfl) ⟨4403648, by rfl⟩ : syracuseStep 23486125 = 8807297) B8807297
theorem B4341863 : Blo 1715058 4341863 := bstep (se 1 (by rfl) ⟨3256397, by rfl⟩ : syracuseStep 4341863 = 6512795) B6512795
theorem B6185069 : Blo 1715058 6185069 := bstep (se 3 (by rfl) ⟨1159700, by rfl⟩ : syracuseStep 6185069 = 2319401) B2319401
theorem B8691947 : Blo 1715058 8691947 := bstep (se 1 (by rfl) ⟨6518960, by rfl⟩ : syracuseStep 8691947 = 13037921) B13037921
theorem B8684009 : Blo 1715058 8684009 := bstep (se 2 (by rfl) ⟨3256503, by rfl⟩ : syracuseStep 8684009 = 6513007) B6513007
theorem B2572841 : Blo 1715058 2572841 := bstep (se 2 (by rfl) ⟨964815, by rfl⟩ : syracuseStep 2572841 = 1929631) B1929631
theorem B4342319 : Blo 1715058 4342319 := bstep (se 1 (by rfl) ⟨3256739, by rfl⟩ : syracuseStep 4342319 = 6513479) B6513479
theorem B3859001 : Blo 1715058 3859001 := bstep (se 2 (by rfl) ⟨1447125, by rfl⟩ : syracuseStep 3859001 = 2894251) B2894251
theorem B8684171 : Blo 1715058 8684171 := bstep (se 1 (by rfl) ⟨6513128, by rfl⟩ : syracuseStep 8684171 = 13026257) B13026257
theorem B5792417 : Blo 1715058 5792417 := bstep (se 2 (by rfl) ⟨2172156, by rfl⟩ : syracuseStep 5792417 = 4344313) B4344313
theorem B19538657 : Blo 1715058 19538657 := bstep (se 2 (by rfl) ⟨7326996, by rfl⟩ : syracuseStep 19538657 = 14653993) B14653993
theorem B2573033 : Blo 1715058 2573033 := bstep (se 2 (by rfl) ⟨964887, by rfl⟩ : syracuseStep 2573033 = 1929775) B1929775
theorem B4342511 : Blo 1715058 4342511 := bstep (se 1 (by rfl) ⟨3256883, by rfl⟩ : syracuseStep 4342511 = 6513767) B6513767
theorem B5792633 : Blo 1715058 5792633 := bstep (se 2 (by rfl) ⟨2172237, by rfl⟩ : syracuseStep 5792633 = 4344475) B4344475
theorem B8684495 : Blo 1715058 8684495 := bstep (se 1 (by rfl) ⟨6513371, by rfl⟩ : syracuseStep 8684495 = 13026743) B13026743
theorem B3859667 : Blo 1715058 3859667 := bstep (se 1 (by rfl) ⟨2894750, by rfl⟩ : syracuseStep 3859667 = 5789501) B5789501
theorem B2573567 : Blo 1715058 2573567 := bstep (se 1 (by rfl) ⟨1930175, by rfl⟩ : syracuseStep 2573567 = 3860351) B3860351
theorem B3859721 : Blo 1715058 3859721 := bstep (se 2 (by rfl) ⟨1447395, by rfl⟩ : syracuseStep 3859721 = 2894791) B2894791
theorem B13035005 : Blo 1715058 13035005 := bstep (se 3 (by rfl) ⟨2444063, by rfl⟩ : syracuseStep 13035005 = 4888127) B4888127
theorem B4884391 : Blo 1715058 4884391 := bstep (se 1 (by rfl) ⟨3663293, by rfl⟩ : syracuseStep 4884391 = 7326587) B7326587
theorem B4884563 : Blo 1715058 4884563 := bstep (se 1 (by rfl) ⟨3663422, by rfl⟩ : syracuseStep 4884563 = 7326845) B7326845
theorem B4884619 : Blo 1715058 4884619 := bstep (se 1 (by rfl) ⟨3663464, by rfl⟩ : syracuseStep 4884619 = 7326929) B7326929
theorem B3860711 : Blo 1715058 3860711 := bstep (se 1 (by rfl) ⟨2895533, by rfl⟩ : syracuseStep 3860711 = 5791067) B5791067
theorem B6514937 : Blo 1715058 6514937 := bstep (se 2 (by rfl) ⟨2443101, by rfl⟩ : syracuseStep 6514937 = 4886203) B4886203
theorem B2574587 : Blo 1715058 2574587 := bstep (se 1 (by rfl) ⟨1930940, by rfl⟩ : syracuseStep 2574587 = 3861881) B3861881
theorem B19548863 : Blo 1715058 19548863 := bstep (se 1 (by rfl) ⟨14661647, by rfl⟩ : syracuseStep 19548863 = 29323295) B29323295
theorem B6515423 : Blo 1715058 6515423 := bstep (se 1 (by rfl) ⟨4886567, by rfl⟩ : syracuseStep 6515423 = 9773135) B9773135
theorem B2575079 : Blo 1715058 2575079 := bstep (se 1 (by rfl) ⟨1931309, by rfl⟩ : syracuseStep 2575079 = 3862619) B3862619
theorem B32983787 : Blo 1715058 32983787 := bstep (se 1 (by rfl) ⟨24737840, by rfl⟩ : syracuseStep 32983787 = 49475681) B49475681
theorem B101722931 : Blo 1715058 101722931 := bstep (se 1 (by rfl) ⟨76292198, by rfl⟩ : syracuseStep 101722931 = 152584397) B152584397
theorem B3861359 : Blo 1715058 3861359 := bstep (se 1 (by rfl) ⟨2896019, by rfl⟩ : syracuseStep 3861359 = 5792039) B5792039
theorem B2575451 : Blo 1715058 2575451 := bstep (se 1 (by rfl) ⟨1931588, by rfl⟩ : syracuseStep 2575451 = 3863177) B3863177
theorem B4344961 : Blo 1715058 4344961 := bstep (se 2 (by rfl) ⟨1629360, by rfl⟩ : syracuseStep 4344961 = 3258721) B3258721
theorem B3861935 : Blo 1715058 3861935 := bstep (se 1 (by rfl) ⟨2896451, by rfl⟩ : syracuseStep 3861935 = 5792903) B5792903
theorem B3862043 : Blo 1715058 3862043 := bstep (se 1 (by rfl) ⟨2896532, by rfl⟩ : syracuseStep 3862043 = 5793065) B5793065
theorem B14667389 : Blo 1715058 14667389 := bstep (se 3 (by rfl) ⟨2750135, by rfl⟩ : syracuseStep 14667389 = 5500271) B5500271
theorem B9776983 : Blo 1715058 9776983 := bstep (se 1 (by rfl) ⟨7332737, by rfl⟩ : syracuseStep 9776983 = 14665475) B14665475
theorem B3862439 : Blo 1715058 3862439 := bstep (se 1 (by rfl) ⟨2896829, by rfl⟩ : syracuseStep 3862439 = 5793659) B5793659
theorem B7327817 : Blo 1715058 7327817 := bstep (se 2 (by rfl) ⟨2747931, by rfl⟩ : syracuseStep 7327817 = 5495863) B5495863
theorem B1716315 : Blo 1715058 1716315 := bstep (se 1 (by rfl) ⟨1287236, by rfl⟩ : syracuseStep 1716315 = 2574473) B2574473
theorem B8687897 : Blo 1715058 8687897 := bstep (se 2 (by rfl) ⟨3257961, by rfl⟩ : syracuseStep 8687897 = 6515923) B6515923
theorem B8810783 : Blo 1715058 8810783 := bstep (se 1 (by rfl) ⟨6608087, by rfl⟩ : syracuseStep 8810783 = 13216175) B13216175
theorem B1716703 : Blo 1715058 1716703 := bstep (se 1 (by rfl) ⟨1287527, by rfl⟩ : syracuseStep 1716703 = 2575055) B2575055
theorem B1716827 : Blo 1715058 1716827 := bstep (se 1 (by rfl) ⟨1287620, by rfl⟩ : syracuseStep 1716827 = 2575241) B2575241
theorem B1929883 : Blo 1715058 1929883 := bstep (se 1 (by rfl) ⟨1447412, by rfl⟩ : syracuseStep 1929883 = 2894825) B2894825
theorem B2060959 : Blo 1715058 2060959 := bstep (se 1 (by rfl) ⟨1545719, by rfl⟩ : syracuseStep 2060959 = 3091439) B3091439
theorem B13038407 : Blo 1715058 13038407 := bstep (se 1 (by rfl) ⟨9778805, by rfl⟩ : syracuseStep 13038407 = 19557611) B19557611
theorem B31314833 : Blo 1715058 31314833 := bstep (se 2 (by rfl) ⟨11743062, by rfl⟩ : syracuseStep 31314833 = 23486125) B23486125
theorem B5788583 : Blo 1715058 5788583 := bstep (se 1 (by rfl) ⟨4341437, by rfl⟩ : syracuseStep 5788583 = 8682875) B8682875
theorem B1930207 : Blo 1715058 1930207 := bstep (se 1 (by rfl) ⟨1447655, by rfl⟩ : syracuseStep 1930207 = 2895311) B2895311
theorem B676983869 : Blo 1715058 676983869 := bstep (se 3 (by rfl) ⟨126934475, by rfl⟩ : syracuseStep 676983869 = 253868951) B253868951
theorem B8926289 : Blo 1715058 8926289 := bstep (se 2 (by rfl) ⟨3347358, by rfl⟩ : syracuseStep 8926289 = 6694717) B6694717
theorem B3257567 : Blo 1715058 3257567 := bstep (se 1 (by rfl) ⟨2443175, by rfl⟩ : syracuseStep 3257567 = 4886351) B4886351
theorem B17855821 : Blo 1715058 17855821 := bstep (se 3 (by rfl) ⟨3347966, by rfl⟩ : syracuseStep 17855821 = 6695933) B6695933
theorem B18798095 : Blo 1715058 18798095 := bstep (se 1 (by rfl) ⟨14098571, by rfl⟩ : syracuseStep 18798095 = 28197143) B28197143
theorem B2750059 : Blo 1715058 2750059 := bstep (se 1 (by rfl) ⟨2062544, by rfl⟩ : syracuseStep 2750059 = 4125089) B4125089
theorem B9778967 : Blo 1715058 9778967 := bstep (se 1 (by rfl) ⟨7334225, by rfl⟩ : syracuseStep 9778967 = 14668451) B14668451
theorem B21985091 : Blo 1715058 21985091 := bstep (se 1 (by rfl) ⟨16488818, by rfl⟩ : syracuseStep 21985091 = 32977637) B32977637
theorem B19535741 : Blo 1715058 19535741 := bstep (se 3 (by rfl) ⟨3662951, by rfl⟩ : syracuseStep 19535741 = 7325903) B7325903
theorem B5789609 : Blo 1715058 5789609 := bstep (se 2 (by rfl) ⟨2171103, by rfl⟩ : syracuseStep 5789609 = 4342207) B4342207
theorem B4888811 : Blo 1715058 4888811 := bstep (se 1 (by rfl) ⟨3666608, by rfl⟩ : syracuseStep 4888811 = 7333217) B7333217
theorem B9771425 : Blo 1715058 9771425 := bstep (se 2 (by rfl) ⟨3664284, by rfl⟩ : syracuseStep 9771425 = 7328569) B7328569
theorem B4889119 : Blo 1715058 4889119 := bstep (se 1 (by rfl) ⟨3666839, by rfl⟩ : syracuseStep 4889119 = 7333679) B7333679
theorem B12368807 : Blo 1715058 12368807 := bstep (se 1 (by rfl) ⟨9276605, by rfl⟩ : syracuseStep 12368807 = 18553211) B18553211
theorem B7330945 : Blo 1715058 7330945 := bstep (se 2 (by rfl) ⟨2749104, by rfl⟩ : syracuseStep 7330945 = 5498209) B5498209
theorem B7830863 : Blo 1715058 7830863 := bstep (se 1 (by rfl) ⟨5873147, by rfl⟩ : syracuseStep 7830863 = 11746295) B11746295
theorem B37117763 : Blo 1715058 37117763 := bstep (se 1 (by rfl) ⟨27838322, by rfl⟩ : syracuseStep 37117763 = 55676645) B55676645
theorem B6184795 : Blo 1715058 6184795 := bstep (se 1 (by rfl) ⟨4638596, by rfl⟩ : syracuseStep 6184795 = 9277193) B9277193
theorem B6512825 : Blo 1715058 6512825 := bstep (se 2 (by rfl) ⟨2442309, by rfl⟩ : syracuseStep 6512825 = 4884619) B4884619
theorem B5791931 : Blo 1715058 5791931 := bstep (se 1 (by rfl) ⟨4343948, by rfl⟩ : syracuseStep 5791931 = 8687897) B8687897
theorem B5873855 : Blo 1715058 5873855 := bstep (se 1 (by rfl) ⟨4405391, by rfl⟩ : syracuseStep 5873855 = 8810783) B8810783
theorem B2572667 : Blo 1715058 2572667 := bstep (se 1 (by rfl) ⟨1929500, by rfl⟩ : syracuseStep 2572667 = 3859001) B3859001
theorem B13025771 : Blo 1715058 13025771 := bstep (se 1 (by rfl) ⟨9769328, by rfl⟩ : syracuseStep 13025771 = 19538657) B19538657
theorem B8692271 : Blo 1715058 8692271 := bstep (se 1 (by rfl) ⟨6519203, by rfl⟩ : syracuseStep 8692271 = 13038407) B13038407
theorem B3859055 : Blo 1715058 3859055 := bstep (se 1 (by rfl) ⟨2894291, by rfl⟩ : syracuseStep 3859055 = 5788583) B5788583
theorem B451322579 : Blo 1715058 451322579 := bstep (se 1 (by rfl) ⟨338491934, by rfl⟩ : syracuseStep 451322579 = 676983869) B676983869
theorem B2573111 : Blo 1715058 2573111 := bstep (se 1 (by rfl) ⟨1929833, by rfl⟩ : syracuseStep 2573111 = 3859667) B3859667
theorem B2171711 : Blo 1715058 2171711 := bstep (se 1 (by rfl) ⟨1628783, by rfl⟩ : syracuseStep 2171711 = 3257567) B3257567
theorem B2573147 : Blo 1715058 2573147 := bstep (se 1 (by rfl) ⟨1929860, by rfl⟩ : syracuseStep 2573147 = 3859721) B3859721
theorem B2573177 : Blo 1715058 2573177 := bstep (se 2 (by rfl) ⟨964941, by rfl⟩ : syracuseStep 2573177 = 1929883) B1929883
theorem B14656727 : Blo 1715058 14656727 := bstep (se 1 (by rfl) ⟨10992545, by rfl⟩ : syracuseStep 14656727 = 21985091) B21985091
theorem B3859739 : Blo 1715058 3859739 := bstep (se 1 (by rfl) ⟨2894804, by rfl⟩ : syracuseStep 3859739 = 5789609) B5789609
theorem B2573609 : Blo 1715058 2573609 := bstep (se 2 (by rfl) ⟨965103, by rfl⟩ : syracuseStep 2573609 = 1930207) B1930207
theorem B2573807 : Blo 1715058 2573807 := bstep (se 1 (by rfl) ⟨1930355, by rfl⟩ : syracuseStep 2573807 = 3860711) B3860711
theorem B4343291 : Blo 1715058 4343291 := bstep (se 1 (by rfl) ⟨3257468, by rfl⟩ : syracuseStep 4343291 = 6514937) B6514937
theorem B9774593 : Blo 1715058 9774593 := bstep (se 2 (by rfl) ⟨3665472, by rfl⟩ : syracuseStep 9774593 = 7330945) B7330945
theorem B5793281 : Blo 1715058 5793281 := bstep (se 2 (by rfl) ⟨2172480, by rfl⟩ : syracuseStep 5793281 = 4344961) B4344961
theorem B6514283 : Blo 1715058 6514283 := bstep (se 1 (by rfl) ⟨4885712, by rfl⟩ : syracuseStep 6514283 = 9771425) B9771425
theorem B4343615 : Blo 1715058 4343615 := bstep (se 1 (by rfl) ⟨3257711, by rfl⟩ : syracuseStep 4343615 = 6515423) B6515423
theorem B21989191 : Blo 1715058 21989191 := bstep (se 1 (by rfl) ⟨16491893, by rfl⟩ : syracuseStep 21989191 = 32983787) B32983787
theorem B67815287 : Blo 1715058 67815287 := bstep (se 1 (by rfl) ⟨50861465, by rfl⟩ : syracuseStep 67815287 = 101722931) B101722931
theorem B2574239 : Blo 1715058 2574239 := bstep (se 1 (by rfl) ⟨1930679, by rfl⟩ : syracuseStep 2574239 = 3861359) B3861359
theorem B5220575 : Blo 1715058 5220575 := bstep (se 1 (by rfl) ⟨3915431, by rfl⟩ : syracuseStep 5220575 = 7830863) B7830863
theorem B2574623 : Blo 1715058 2574623 := bstep (se 1 (by rfl) ⟨1930967, by rfl⟩ : syracuseStep 2574623 = 3861935) B3861935
theorem B2574695 : Blo 1715058 2574695 := bstep (se 1 (by rfl) ⟨1931021, by rfl⟩ : syracuseStep 2574695 = 3862043) B3862043
theorem B13035977 : Blo 1715058 13035977 := bstep (se 2 (by rfl) ⟨4888491, by rfl⟩ : syracuseStep 13035977 = 9776983) B9776983
theorem B2574959 : Blo 1715058 2574959 := bstep (se 1 (by rfl) ⟨1931219, by rfl⟩ : syracuseStep 2574959 = 3862439) B3862439
theorem B4885211 : Blo 1715058 4885211 := bstep (se 1 (by rfl) ⟨3663908, by rfl⟩ : syracuseStep 4885211 = 7327817) B7327817
theorem B2894575 : Blo 1715058 2894575 := bstep (se 1 (by rfl) ⟨2170931, by rfl⟩ : syracuseStep 2894575 = 4341863) B4341863
theorem B4123379 : Blo 1715058 4123379 := bstep (se 1 (by rfl) ⟨3092534, by rfl⟩ : syracuseStep 4123379 = 6185069) B6185069
theorem B5794631 : Blo 1715058 5794631 := bstep (se 1 (by rfl) ⟨4345973, by rfl⟩ : syracuseStep 5794631 = 8691947) B8691947
theorem B1715227 : Blo 1715058 1715227 := bstep (se 1 (by rfl) ⟨1286420, by rfl⟩ : syracuseStep 1715227 = 2572841) B2572841
theorem B2894879 : Blo 1715058 2894879 := bstep (se 1 (by rfl) ⟨2171159, by rfl⟩ : syracuseStep 2894879 = 4342319) B4342319
theorem B3861611 : Blo 1715058 3861611 := bstep (se 1 (by rfl) ⟨2896208, by rfl⟩ : syracuseStep 3861611 = 5792417) B5792417
theorem B1715355 : Blo 1715058 1715355 := bstep (se 1 (by rfl) ⟨1286516, by rfl⟩ : syracuseStep 1715355 = 2573033) B2573033
theorem B2895007 : Blo 1715058 2895007 := bstep (se 1 (by rfl) ⟨2171255, by rfl⟩ : syracuseStep 2895007 = 4342511) B4342511
theorem B3861755 : Blo 1715058 3861755 := bstep (se 1 (by rfl) ⟨2896316, by rfl⟩ : syracuseStep 3861755 = 5792633) B5792633
theorem B20876555 : Blo 1715058 20876555 := bstep (se 1 (by rfl) ⟨15657416, by rfl⟩ : syracuseStep 20876555 = 31314833) B31314833
theorem B5950859 : Blo 1715058 5950859 := bstep (se 1 (by rfl) ⟨4463144, by rfl⟩ : syracuseStep 5950859 = 8926289) B8926289
theorem B1715711 : Blo 1715058 1715711 := bstep (se 1 (by rfl) ⟨1286783, by rfl⟩ : syracuseStep 1715711 = 2573567) B2573567
theorem B2747945 : Blo 1715058 2747945 := bstep (se 2 (by rfl) ⟨1030479, by rfl⟩ : syracuseStep 2747945 = 2060959) B2060959
theorem B3256375 : Blo 1715058 3256375 := bstep (se 1 (by rfl) ⟨2442281, by rfl⟩ : syracuseStep 3256375 = 4884563) B4884563
theorem B1716391 : Blo 1715058 1716391 := bstep (se 1 (by rfl) ⟨1287293, by rfl⟩ : syracuseStep 1716391 = 2574587) B2574587
theorem B1716719 : Blo 1715058 1716719 := bstep (se 1 (by rfl) ⟨1287539, by rfl⟩ : syracuseStep 1716719 = 2575079) B2575079
theorem B8245871 : Blo 1715058 8245871 := bstep (se 1 (by rfl) ⟨6184403, by rfl⟩ : syracuseStep 8245871 = 12368807) B12368807
theorem B1716967 : Blo 1715058 1716967 := bstep (se 1 (by rfl) ⟨1287725, by rfl⟩ : syracuseStep 1716967 = 2575451) B2575451
theorem B3666745 : Blo 1715058 3666745 := bstep (se 2 (by rfl) ⟨1375029, by rfl⟩ : syracuseStep 3666745 = 2750059) B2750059
theorem B9778259 : Blo 1715058 9778259 := bstep (se 1 (by rfl) ⟨7333694, by rfl⟩ : syracuseStep 9778259 = 14667389) B14667389
theorem B8246393 : Blo 1715058 8246393 := bstep (se 2 (by rfl) ⟨3092397, by rfl⟩ : syracuseStep 8246393 = 6184795) B6184795
theorem B24745175 : Blo 1715058 24745175 := bstep (se 1 (by rfl) ⟨18558881, by rfl⟩ : syracuseStep 24745175 = 37117763) B37117763
theorem B5789339 : Blo 1715058 5789339 := bstep (se 1 (by rfl) ⟨4342004, by rfl⟩ : syracuseStep 5789339 = 8684009) B8684009
theorem B5789447 : Blo 1715058 5789447 := bstep (se 1 (by rfl) ⟨4342085, by rfl⟩ : syracuseStep 5789447 = 8684171) B8684171
theorem B5789663 : Blo 1715058 5789663 := bstep (se 1 (by rfl) ⟨4342247, by rfl⟩ : syracuseStep 5789663 = 8684495) B8684495
theorem B6518825 : Blo 1715058 6518825 := bstep (se 2 (by rfl) ⟨2444559, by rfl⟩ : syracuseStep 6518825 = 4889119) B4889119
theorem B8690003 : Blo 1715058 8690003 := bstep (se 1 (by rfl) ⟨6517502, by rfl⟩ : syracuseStep 8690003 = 13035005) B13035005
theorem B12532063 : Blo 1715058 12532063 := bstep (se 1 (by rfl) ⟨9399047, by rfl⟩ : syracuseStep 12532063 = 18798095) B18798095
theorem B6519311 : Blo 1715058 6519311 := bstep (se 1 (by rfl) ⟨4889483, by rfl⟩ : syracuseStep 6519311 = 9778967) B9778967
theorem B13023827 : Blo 1715058 13023827 := bstep (se 1 (by rfl) ⟨9767870, by rfl⟩ : syracuseStep 13023827 = 19535741) B19535741
theorem B3259207 : Blo 1715058 3259207 := bstep (se 1 (by rfl) ⟨2444405, by rfl⟩ : syracuseStep 3259207 = 4888811) B4888811
theorem B95231045 : Blo 1715058 95231045 := bstep (se 4 (by rfl) ⟨8927910, by rfl⟩ : syracuseStep 95231045 = 17855821) B17855821
theorem B13032575 : Blo 1715058 13032575 := bstep (se 1 (by rfl) ⟨9774431, by rfl⟩ : syracuseStep 13032575 = 19548863) B19548863
theorem B6512521 : Blo 1715058 6512521 := bstep (se 2 (by rfl) ⟨2442195, by rfl⟩ : syracuseStep 6512521 = 4884391) B4884391
theorem B4341833 : Blo 1715058 4341833 := bstep (se 2 (by rfl) ⟨1628187, by rfl⟩ : syracuseStep 4341833 = 3256375) B3256375
theorem B4341883 : Blo 1715058 4341883 := bstep (se 1 (by rfl) ⟨3256412, by rfl⟩ : syracuseStep 4341883 = 6512825) B6512825
theorem B8683847 : Blo 1715058 8683847 := bstep (se 1 (by rfl) ⟨6512885, by rfl⟩ : syracuseStep 8683847 = 13025771) B13025771
theorem B2572703 : Blo 1715058 2572703 := bstep (se 1 (by rfl) ⟨1929527, by rfl⟩ : syracuseStep 2572703 = 3859055) B3859055
theorem B5497247 : Blo 1715058 5497247 := bstep (se 1 (by rfl) ⟨4122935, by rfl⟩ : syracuseStep 5497247 = 8245871) B8245871
theorem B15663613 : Blo 1715058 15663613 := bstep (se 3 (by rfl) ⟨2936927, by rfl⟩ : syracuseStep 15663613 = 5873855) B5873855
theorem B5497595 : Blo 1715058 5497595 := bstep (se 1 (by rfl) ⟨4123196, by rfl⟩ : syracuseStep 5497595 = 8246393) B8246393
theorem B2573159 : Blo 1715058 2573159 := bstep (se 1 (by rfl) ⟨1929869, by rfl⟩ : syracuseStep 2573159 = 3859739) B3859739
theorem B3859433 : Blo 1715058 3859433 := bstep (se 2 (by rfl) ⟨1447287, by rfl⟩ : syracuseStep 3859433 = 2894575) B2894575
theorem B15868957 : Blo 1715058 15868957 := bstep (se 3 (by rfl) ⟨2975429, by rfl⟩ : syracuseStep 15868957 = 5950859) B5950859
theorem B4342855 : Blo 1715058 4342855 := bstep (se 1 (by rfl) ⟨3257141, by rfl⟩ : syracuseStep 4342855 = 6514283) B6514283
theorem B3859559 : Blo 1715058 3859559 := bstep (se 1 (by rfl) ⟨2894669, by rfl⟩ : syracuseStep 3859559 = 5789339) B5789339
theorem B3859631 : Blo 1715058 3859631 := bstep (se 1 (by rfl) ⟨2894723, by rfl⟩ : syracuseStep 3859631 = 5789447) B5789447
theorem B3859775 : Blo 1715058 3859775 := bstep (se 1 (by rfl) ⟨2894831, by rfl⟩ : syracuseStep 3859775 = 5789663) B5789663
theorem B3860009 : Blo 1715058 3860009 := bstep (se 2 (by rfl) ⟨1447503, by rfl⟩ : syracuseStep 3860009 = 2895007) B2895007
theorem B5793335 : Blo 1715058 5793335 := bstep (se 1 (by rfl) ⟨4345001, by rfl⟩ : syracuseStep 5793335 = 8690003) B8690003
theorem B13027229 : Blo 1715058 13027229 := bstep (se 3 (by rfl) ⟨2442605, by rfl⟩ : syracuseStep 13027229 = 4885211) B4885211
theorem B2574407 : Blo 1715058 2574407 := bstep (se 1 (by rfl) ⟨1930805, by rfl⟩ : syracuseStep 2574407 = 3861611) B3861611
theorem B2574503 : Blo 1715058 2574503 := bstep (se 1 (by rfl) ⟨1930877, by rfl⟩ : syracuseStep 2574503 = 3861755) B3861755
theorem B3861287 : Blo 1715058 3861287 := bstep (se 1 (by rfl) ⟨2895965, by rfl⟩ : syracuseStep 3861287 = 5791931) B5791931
theorem B1715111 : Blo 1715058 1715111 := bstep (se 1 (by rfl) ⟨1286333, by rfl⟩ : syracuseStep 1715111 = 2572667) B2572667
theorem B5794847 : Blo 1715058 5794847 := bstep (se 1 (by rfl) ⟨4346135, by rfl⟩ : syracuseStep 5794847 = 8692271) B8692271
theorem B1715407 : Blo 1715058 1715407 := bstep (se 1 (by rfl) ⟨1286555, by rfl⟩ : syracuseStep 1715407 = 2573111) B2573111
theorem B1715431 : Blo 1715058 1715431 := bstep (se 1 (by rfl) ⟨1286573, by rfl⟩ : syracuseStep 1715431 = 2573147) B2573147
theorem B1715451 : Blo 1715058 1715451 := bstep (se 1 (by rfl) ⟨1286588, by rfl⟩ : syracuseStep 1715451 = 2573177) B2573177
theorem B1715739 : Blo 1715058 1715739 := bstep (se 1 (by rfl) ⟨1286804, by rfl⟩ : syracuseStep 1715739 = 2573609) B2573609
theorem B1715871 : Blo 1715058 1715871 := bstep (se 1 (by rfl) ⟨1286903, by rfl⟩ : syracuseStep 1715871 = 2573807) B2573807
theorem B2895527 : Blo 1715058 2895527 := bstep (se 1 (by rfl) ⟨2171645, by rfl⟩ : syracuseStep 2895527 = 4343291) B4343291
theorem B6516395 : Blo 1715058 6516395 := bstep (se 1 (by rfl) ⟨4887296, by rfl⟩ : syracuseStep 6516395 = 9774593) B9774593
theorem B3862187 : Blo 1715058 3862187 := bstep (se 1 (by rfl) ⟨2896640, by rfl⟩ : syracuseStep 3862187 = 5793281) B5793281
theorem B4345609 : Blo 1715058 4345609 := bstep (se 2 (by rfl) ⟨1629603, by rfl⟩ : syracuseStep 4345609 = 3259207) B3259207
theorem B2895743 : Blo 1715058 2895743 := bstep (se 1 (by rfl) ⟨2171807, by rfl⟩ : syracuseStep 2895743 = 4343615) B4343615
theorem B1716159 : Blo 1715058 1716159 := bstep (se 1 (by rfl) ⟨1287119, by rfl⟩ : syracuseStep 1716159 = 2574239) B2574239
theorem B4345883 : Blo 1715058 4345883 := bstep (se 1 (by rfl) ⟨3259412, by rfl⟩ : syracuseStep 4345883 = 6518825) B6518825
theorem B7327853 : Blo 1715058 7327853 := bstep (se 3 (by rfl) ⟨1373972, by rfl⟩ : syracuseStep 7327853 = 2747945) B2747945
theorem B1716415 : Blo 1715058 1716415 := bstep (se 1 (by rfl) ⟨1287311, by rfl⟩ : syracuseStep 1716415 = 2574623) B2574623
theorem B1716463 : Blo 1715058 1716463 := bstep (se 1 (by rfl) ⟨1287347, by rfl⟩ : syracuseStep 1716463 = 2574695) B2574695
theorem B4346207 : Blo 1715058 4346207 := bstep (se 1 (by rfl) ⟨3259655, by rfl⟩ : syracuseStep 4346207 = 6519311) B6519311
theorem B1716639 : Blo 1715058 1716639 := bstep (se 1 (by rfl) ⟨1287479, by rfl⟩ : syracuseStep 1716639 = 2574959) B2574959
theorem B2748919 : Blo 1715058 2748919 := bstep (se 1 (by rfl) ⟨2061689, by rfl⟩ : syracuseStep 2748919 = 4123379) B4123379
theorem B3863087 : Blo 1715058 3863087 := bstep (se 1 (by rfl) ⟨2897315, by rfl⟩ : syracuseStep 3863087 = 5794631) B5794631
theorem B1929919 : Blo 1715058 1929919 := bstep (se 1 (by rfl) ⟨1447439, by rfl⟩ : syracuseStep 1929919 = 2894879) B2894879
theorem B8688383 : Blo 1715058 8688383 := bstep (se 1 (by rfl) ⟨6516287, by rfl⟩ : syracuseStep 8688383 = 13032575) B13032575
theorem B16709417 : Blo 1715058 16709417 := bstep (se 2 (by rfl) ⟨6266031, by rfl⟩ : syracuseStep 16709417 = 12532063) B12532063
theorem B300881719 : Blo 1715058 300881719 := bstep (se 1 (by rfl) ⟨225661289, by rfl⟩ : syracuseStep 300881719 = 451322579) B451322579
theorem B6518839 : Blo 1715058 6518839 := bstep (se 1 (by rfl) ⟨4889129, by rfl⟩ : syracuseStep 6518839 = 9778259) B9778259
theorem B9771151 : Blo 1715058 9771151 := bstep (se 1 (by rfl) ⟨7328363, by rfl⟩ : syracuseStep 9771151 = 14656727) B14656727
theorem B16496783 : Blo 1715058 16496783 := bstep (se 1 (by rfl) ⟨12372587, by rfl⟩ : syracuseStep 16496783 = 24745175) B24745175
theorem B4888993 : Blo 1715058 4888993 := bstep (se 2 (by rfl) ⟨1833372, by rfl⟩ : syracuseStep 4888993 = 3666745) B3666745
theorem B45210191 : Blo 1715058 45210191 := bstep (se 1 (by rfl) ⟨33907643, by rfl⟩ : syracuseStep 45210191 = 67815287) B67815287
theorem B3480383 : Blo 1715058 3480383 := bstep (se 1 (by rfl) ⟨2610287, by rfl⟩ : syracuseStep 3480383 = 5220575) B5220575
theorem B8690651 : Blo 1715058 8690651 := bstep (se 1 (by rfl) ⟨6517988, by rfl⟩ : syracuseStep 8690651 = 13035977) B13035977
theorem B8682551 : Blo 1715058 8682551 := bstep (se 1 (by rfl) ⟨6511913, by rfl⟩ : syracuseStep 8682551 = 13023827) B13023827
theorem B63487363 : Blo 1715058 63487363 := bstep (se 1 (by rfl) ⟨47615522, by rfl⟩ : syracuseStep 63487363 = 95231045) B95231045
theorem B5791229 : Blo 1715058 5791229 := bstep (se 3 (by rfl) ⟨1085855, by rfl⟩ : syracuseStep 5791229 = 2171711) B2171711
theorem B13917703 : Blo 1715058 13917703 := bstep (se 1 (by rfl) ⟨10438277, by rfl⟩ : syracuseStep 13917703 = 20876555) B20876555
theorem B29318921 : Blo 1715058 29318921 := bstep (se 2 (by rfl) ⟨10994595, by rfl⟩ : syracuseStep 29318921 = 21989191) B21989191
theorem B8683361 : Blo 1715058 8683361 := bstep (se 2 (by rfl) ⟨3256260, by rfl⟩ : syracuseStep 8683361 = 6512521) B6512521
theorem B8691785 : Blo 1715058 8691785 := bstep (se 2 (by rfl) ⟨3259419, by rfl⟩ : syracuseStep 8691785 = 6518839) B6518839
theorem B5792255 : Blo 1715058 5792255 := bstep (se 1 (by rfl) ⟨4344191, by rfl⟩ : syracuseStep 5792255 = 8688383) B8688383
theorem B2572955 : Blo 1715058 2572955 := bstep (se 1 (by rfl) ⟨1929716, by rfl⟩ : syracuseStep 2572955 = 3859433) B3859433
theorem B2573039 : Blo 1715058 2573039 := bstep (se 1 (by rfl) ⟨1929779, by rfl⟩ : syracuseStep 2573039 = 3859559) B3859559
theorem B2573087 : Blo 1715058 2573087 := bstep (se 1 (by rfl) ⟨1929815, by rfl⟩ : syracuseStep 2573087 = 3859631) B3859631
theorem B2573183 : Blo 1715058 2573183 := bstep (se 1 (by rfl) ⟨1929887, by rfl⟩ : syracuseStep 2573183 = 3859775) B3859775
theorem B2573225 : Blo 1715058 2573225 := bstep (se 2 (by rfl) ⟨964959, by rfl⟩ : syracuseStep 2573225 = 1929919) B1929919
theorem B2573339 : Blo 1715058 2573339 := bstep (se 1 (by rfl) ⟨1930004, by rfl⟩ : syracuseStep 2573339 = 3860009) B3860009
theorem B8684819 : Blo 1715058 8684819 := bstep (se 1 (by rfl) ⟨6513614, by rfl⟩ : syracuseStep 8684819 = 13027229) B13027229
theorem B84649817 : Blo 1715058 84649817 := bstep (se 2 (by rfl) ⟨31743681, by rfl⟩ : syracuseStep 84649817 = 63487363) B63487363
theorem B2574191 : Blo 1715058 2574191 := bstep (se 1 (by rfl) ⟨1930643, by rfl⟩ : syracuseStep 2574191 = 3861287) B3861287
theorem B2320255 : Blo 1715058 2320255 := bstep (se 1 (by rfl) ⟨1740191, by rfl⟩ : syracuseStep 2320255 = 3480383) B3480383
theorem B5793767 : Blo 1715058 5793767 := bstep (se 1 (by rfl) ⟨4345325, by rfl⟩ : syracuseStep 5793767 = 8690651) B8690651
theorem B18556937 : Blo 1715058 18556937 := bstep (se 2 (by rfl) ⟨6958851, by rfl⟩ : syracuseStep 18556937 = 13917703) B13917703
theorem B3860819 : Blo 1715058 3860819 := bstep (se 1 (by rfl) ⟨2895614, by rfl⟩ : syracuseStep 3860819 = 5791229) B5791229
theorem B5794145 : Blo 1715058 5794145 := bstep (se 2 (by rfl) ⟨2172804, by rfl⟩ : syracuseStep 5794145 = 4345609) B4345609
theorem B4344263 : Blo 1715058 4344263 := bstep (se 1 (by rfl) ⟨3258197, by rfl⟩ : syracuseStep 4344263 = 6516395) B6516395
theorem B2574791 : Blo 1715058 2574791 := bstep (se 1 (by rfl) ⟨1931093, by rfl⟩ : syracuseStep 2574791 = 3862187) B3862187
theorem B2894555 : Blo 1715058 2894555 := bstep (se 1 (by rfl) ⟨2170916, by rfl⟩ : syracuseStep 2894555 = 4341833) B4341833
theorem B4885235 : Blo 1715058 4885235 := bstep (se 1 (by rfl) ⟨3663926, by rfl⟩ : syracuseStep 4885235 = 7327853) B7327853
theorem B13028201 : Blo 1715058 13028201 := bstep (se 2 (by rfl) ⟨4885575, by rfl⟩ : syracuseStep 13028201 = 9771151) B9771151
theorem B1715135 : Blo 1715058 1715135 := bstep (se 1 (by rfl) ⟨1286351, by rfl⟩ : syracuseStep 1715135 = 2572703) B2572703
theorem B2575391 : Blo 1715058 2575391 := bstep (se 1 (by rfl) ⟨1931543, by rfl⟩ : syracuseStep 2575391 = 3863087) B3863087
theorem B3665063 : Blo 1715058 3665063 := bstep (se 1 (by rfl) ⟨2748797, by rfl⟩ : syracuseStep 3665063 = 5497595) B5497595
theorem B1715439 : Blo 1715058 1715439 := bstep (se 1 (by rfl) ⟨1286579, by rfl⟩ : syracuseStep 1715439 = 2573159) B2573159
theorem B3665225 : Blo 1715058 3665225 := bstep (se 2 (by rfl) ⟨1374459, by rfl⟩ : syracuseStep 3665225 = 2748919) B2748919
theorem B20884817 : Blo 1715058 20884817 := bstep (se 2 (by rfl) ⟨7831806, by rfl⟩ : syracuseStep 20884817 = 15663613) B15663613
theorem B3862223 : Blo 1715058 3862223 := bstep (se 1 (by rfl) ⟨2896667, by rfl⟩ : syracuseStep 3862223 = 5793335) B5793335
theorem B14659325 : Blo 1715058 14659325 := bstep (se 3 (by rfl) ⟨2748623, by rfl⟩ : syracuseStep 14659325 = 5497247) B5497247
theorem B1716271 : Blo 1715058 1716271 := bstep (se 1 (by rfl) ⟨1287203, by rfl⟩ : syracuseStep 1716271 = 2574407) B2574407
theorem B10997855 : Blo 1715058 10997855 := bstep (se 1 (by rfl) ⟨8248391, by rfl⟩ : syracuseStep 10997855 = 16496783) B16496783
theorem B1716335 : Blo 1715058 1716335 := bstep (se 1 (by rfl) ⟨1287251, by rfl⟩ : syracuseStep 1716335 = 2574503) B2574503
theorem B3863231 : Blo 1715058 3863231 := bstep (se 1 (by rfl) ⟨2897423, by rfl⟩ : syracuseStep 3863231 = 5794847) B5794847
theorem B5788367 : Blo 1715058 5788367 := bstep (se 1 (by rfl) ⟨4341275, by rfl⟩ : syracuseStep 5788367 = 8682551) B8682551
theorem B401175625 : Blo 1715058 401175625 := bstep (se 2 (by rfl) ⟨150440859, by rfl⟩ : syracuseStep 401175625 = 300881719) B300881719
theorem B1930351 : Blo 1715058 1930351 := bstep (se 1 (by rfl) ⟨1447763, by rfl⟩ : syracuseStep 1930351 = 2895527) B2895527
theorem B5788907 : Blo 1715058 5788907 := bstep (se 1 (by rfl) ⟨4341680, by rfl⟩ : syracuseStep 5788907 = 8683361) B8683361
theorem B1930495 : Blo 1715058 1930495 := bstep (se 1 (by rfl) ⟨1447871, by rfl⟩ : syracuseStep 1930495 = 2895743) B2895743
theorem B2897255 : Blo 1715058 2897255 := bstep (se 1 (by rfl) ⟨2172941, by rfl⟩ : syracuseStep 2897255 = 4345883) B4345883
theorem B5789177 : Blo 1715058 5789177 := bstep (se 2 (by rfl) ⟨2170941, by rfl⟩ : syracuseStep 5789177 = 4341883) B4341883
theorem B5789231 : Blo 1715058 5789231 := bstep (se 1 (by rfl) ⟨4341923, by rfl⟩ : syracuseStep 5789231 = 8683847) B8683847
theorem B2897471 : Blo 1715058 2897471 := bstep (se 1 (by rfl) ⟨2173103, by rfl⟩ : syracuseStep 2897471 = 4346207) B4346207
theorem B6518657 : Blo 1715058 6518657 := bstep (se 2 (by rfl) ⟨2444496, by rfl⟩ : syracuseStep 6518657 = 4888993) B4888993
theorem B11139611 : Blo 1715058 11139611 := bstep (se 1 (by rfl) ⟨8354708, by rfl⟩ : syracuseStep 11139611 = 16709417) B16709417
theorem B21158609 : Blo 1715058 21158609 := bstep (se 2 (by rfl) ⟨7934478, by rfl⟩ : syracuseStep 21158609 = 15868957) B15868957
theorem B5790473 : Blo 1715058 5790473 := bstep (se 2 (by rfl) ⟨2171427, by rfl⟩ : syracuseStep 5790473 = 4342855) B4342855
theorem B120560509 : Blo 1715058 120560509 := bstep (se 3 (by rfl) ⟨22605095, by rfl⟩ : syracuseStep 120560509 = 45210191) B45210191
theorem B19545947 : Blo 1715058 19545947 := bstep (se 1 (by rfl) ⟨14659460, by rfl⟩ : syracuseStep 19545947 = 29318921) B29318921
theorem B7331903 : Blo 1715058 7331903 := bstep (se 1 (by rfl) ⟨5498927, by rfl⟩ : syracuseStep 7331903 = 10997855) B10997855
theorem B3858911 : Blo 1715058 3858911 := bstep (se 1 (by rfl) ⟨2894183, by rfl⟩ : syracuseStep 3858911 = 5788367) B5788367
theorem B3859271 : Blo 1715058 3859271 := bstep (se 1 (by rfl) ⟨2894453, by rfl⟩ : syracuseStep 3859271 = 5788907) B5788907
theorem B3859451 : Blo 1715058 3859451 := bstep (se 1 (by rfl) ⟨2894588, by rfl⟩ : syracuseStep 3859451 = 5789177) B5789177
theorem B3859487 : Blo 1715058 3859487 := bstep (se 1 (by rfl) ⟨2894615, by rfl⟩ : syracuseStep 3859487 = 5789231) B5789231
theorem B12371291 : Blo 1715058 12371291 := bstep (se 1 (by rfl) ⟨9278468, by rfl⟩ : syracuseStep 12371291 = 18556937) B18556937
theorem B29705629 : Blo 1715058 29705629 := bstep (se 3 (by rfl) ⟨5569805, by rfl⟩ : syracuseStep 29705629 = 11139611) B11139611
theorem B2573801 : Blo 1715058 2573801 := bstep (se 2 (by rfl) ⟨965175, by rfl⟩ : syracuseStep 2573801 = 1930351) B1930351
theorem B2573879 : Blo 1715058 2573879 := bstep (se 1 (by rfl) ⟨1930409, by rfl⟩ : syracuseStep 2573879 = 3860819) B3860819
theorem B2573993 : Blo 1715058 2573993 := bstep (se 2 (by rfl) ⟨965247, by rfl⟩ : syracuseStep 2573993 = 1930495) B1930495
theorem B3860315 : Blo 1715058 3860315 := bstep (se 1 (by rfl) ⟨2895236, by rfl⟩ : syracuseStep 3860315 = 5790473) B5790473
theorem B8685467 : Blo 1715058 8685467 := bstep (se 1 (by rfl) ⟨6514100, by rfl⟩ : syracuseStep 8685467 = 13028201) B13028201
theorem B2443375 : Blo 1715058 2443375 := bstep (se 1 (by rfl) ⟨1832531, by rfl⟩ : syracuseStep 2443375 = 3665063) B3665063
theorem B225691829 : Blo 1715058 225691829 := bstep (se 5 (by rfl) ⟨10579304, by rfl⟩ : syracuseStep 225691829 = 21158609) B21158609
theorem B2443483 : Blo 1715058 2443483 := bstep (se 1 (by rfl) ⟨1832612, by rfl⟩ : syracuseStep 2443483 = 3665225) B3665225
theorem B225732845 : Blo 1715058 225732845 := bstep (se 3 (by rfl) ⟨42324908, by rfl⟩ : syracuseStep 225732845 = 84649817) B84649817
theorem B2574815 : Blo 1715058 2574815 := bstep (se 1 (by rfl) ⟨1931111, by rfl⟩ : syracuseStep 2574815 = 3862223) B3862223
theorem B5794523 : Blo 1715058 5794523 := bstep (se 1 (by rfl) ⟨4345892, by rfl⟩ : syracuseStep 5794523 = 8691785) B8691785
theorem B3861503 : Blo 1715058 3861503 := bstep (se 1 (by rfl) ⟨2896127, by rfl⟩ : syracuseStep 3861503 = 5792255) B5792255
theorem B1715303 : Blo 1715058 1715303 := bstep (se 1 (by rfl) ⟨1286477, by rfl⟩ : syracuseStep 1715303 = 2572955) B2572955
theorem B2575487 : Blo 1715058 2575487 := bstep (se 1 (by rfl) ⟨1931615, by rfl⟩ : syracuseStep 2575487 = 3863231) B3863231
theorem B1715359 : Blo 1715058 1715359 := bstep (se 1 (by rfl) ⟨1286519, by rfl⟩ : syracuseStep 1715359 = 2573039) B2573039
theorem B1715391 : Blo 1715058 1715391 := bstep (se 1 (by rfl) ⟨1286543, by rfl⟩ : syracuseStep 1715391 = 2573087) B2573087
theorem B1715455 : Blo 1715058 1715455 := bstep (se 1 (by rfl) ⟨1286591, by rfl⟩ : syracuseStep 1715455 = 2573183) B2573183
theorem B1715483 : Blo 1715058 1715483 := bstep (se 1 (by rfl) ⟨1286612, by rfl⟩ : syracuseStep 1715483 = 2573225) B2573225
theorem B1715559 : Blo 1715058 1715559 := bstep (se 1 (by rfl) ⟨1286669, by rfl⟩ : syracuseStep 1715559 = 2573339) B2573339
theorem B55692845 : Blo 1715058 55692845 := bstep (se 3 (by rfl) ⟨10442408, by rfl⟩ : syracuseStep 55692845 = 20884817) B20884817
theorem B160747345 : Blo 1715058 160747345 := bstep (se 2 (by rfl) ⟨60280254, by rfl⟩ : syracuseStep 160747345 = 120560509) B120560509
theorem B1716127 : Blo 1715058 1716127 := bstep (se 1 (by rfl) ⟨1287095, by rfl⟩ : syracuseStep 1716127 = 2574191) B2574191
theorem B4345771 : Blo 1715058 4345771 := bstep (se 1 (by rfl) ⟨3259328, by rfl⟩ : syracuseStep 4345771 = 6518657) B6518657
theorem B3862511 : Blo 1715058 3862511 := bstep (se 1 (by rfl) ⟨2896883, by rfl⟩ : syracuseStep 3862511 = 5793767) B5793767
theorem B534900833 : Blo 1715058 534900833 := bstep (se 2 (by rfl) ⟨200587812, by rfl⟩ : syracuseStep 534900833 = 401175625) B401175625
theorem B3862763 : Blo 1715058 3862763 := bstep (se 1 (by rfl) ⟨2897072, by rfl⟩ : syracuseStep 3862763 = 5794145) B5794145
theorem B2896175 : Blo 1715058 2896175 := bstep (se 1 (by rfl) ⟨2172131, by rfl⟩ : syracuseStep 2896175 = 4344263) B4344263
theorem B1716527 : Blo 1715058 1716527 := bstep (se 1 (by rfl) ⟨1287395, by rfl⟩ : syracuseStep 1716527 = 2574791) B2574791
theorem B1929703 : Blo 1715058 1929703 := bstep (se 1 (by rfl) ⟨1447277, by rfl⟩ : syracuseStep 1929703 = 2894555) B2894555
theorem B3256823 : Blo 1715058 3256823 := bstep (se 1 (by rfl) ⟨2442617, by rfl⟩ : syracuseStep 3256823 = 4885235) B4885235
theorem B1716927 : Blo 1715058 1716927 := bstep (se 1 (by rfl) ⟨1287695, by rfl⟩ : syracuseStep 1716927 = 2575391) B2575391
theorem B3093673 : Blo 1715058 3093673 := bstep (se 2 (by rfl) ⟨1160127, by rfl⟩ : syracuseStep 3093673 = 2320255) B2320255
theorem B13030631 : Blo 1715058 13030631 := bstep (se 1 (by rfl) ⟨9772973, by rfl⟩ : syracuseStep 13030631 = 19545947) B19545947
theorem B5789879 : Blo 1715058 5789879 := bstep (se 1 (by rfl) ⟨4342409, by rfl⟩ : syracuseStep 5789879 = 8684819) B8684819
theorem B1931503 : Blo 1715058 1931503 := bstep (se 1 (by rfl) ⟨1448627, by rfl⟩ : syracuseStep 1931503 = 2897255) B2897255
theorem B1931647 : Blo 1715058 1931647 := bstep (se 1 (by rfl) ⟨1448735, by rfl⟩ : syracuseStep 1931647 = 2897471) B2897471
theorem B9772883 : Blo 1715058 9772883 := bstep (se 1 (by rfl) ⟨7329662, by rfl⟩ : syracuseStep 9772883 = 14659325) B14659325
theorem B2572607 : Blo 1715058 2572607 := bstep (se 1 (by rfl) ⟨1929455, by rfl⟩ : syracuseStep 2572607 = 3858911) B3858911
theorem B2171215 : Blo 1715058 2171215 := bstep (se 1 (by rfl) ⟨1628411, by rfl⟩ : syracuseStep 2171215 = 3256823) B3256823
theorem B2572847 : Blo 1715058 2572847 := bstep (se 1 (by rfl) ⟨1929635, by rfl⟩ : syracuseStep 2572847 = 3859271) B3859271
theorem B2572937 : Blo 1715058 2572937 := bstep (se 2 (by rfl) ⟨964851, by rfl⟩ : syracuseStep 2572937 = 1929703) B1929703
theorem B2572967 : Blo 1715058 2572967 := bstep (se 1 (by rfl) ⟨1929725, by rfl⟩ : syracuseStep 2572967 = 3859451) B3859451
theorem B2572991 : Blo 1715058 2572991 := bstep (se 1 (by rfl) ⟨1929743, by rfl⟩ : syracuseStep 2572991 = 3859487) B3859487
theorem B2573543 : Blo 1715058 2573543 := bstep (se 1 (by rfl) ⟨1930157, by rfl⟩ : syracuseStep 2573543 = 3860315) B3860315
theorem B3859919 : Blo 1715058 3859919 := bstep (se 1 (by rfl) ⟨2894939, by rfl⟩ : syracuseStep 3859919 = 5789879) B5789879
theorem B857319173 : Blo 1715058 857319173 := bstep (se 4 (by rfl) ⟨80373672, by rfl⟩ : syracuseStep 857319173 = 160747345) B160747345
theorem B2574335 : Blo 1715058 2574335 := bstep (se 1 (by rfl) ⟨1930751, by rfl⟩ : syracuseStep 2574335 = 3861503) B3861503
theorem B37128563 : Blo 1715058 37128563 := bstep (se 1 (by rfl) ⟨27846422, by rfl⟩ : syracuseStep 37128563 = 55692845) B55692845
theorem B6515255 : Blo 1715058 6515255 := bstep (se 1 (by rfl) ⟨4886441, by rfl⟩ : syracuseStep 6515255 = 9772883) B9772883
theorem B5794361 : Blo 1715058 5794361 := bstep (se 2 (by rfl) ⟨2172885, by rfl⟩ : syracuseStep 5794361 = 4345771) B4345771
theorem B2575007 : Blo 1715058 2575007 := bstep (se 1 (by rfl) ⟨1931255, by rfl⟩ : syracuseStep 2575007 = 3862511) B3862511
theorem B356600555 : Blo 1715058 356600555 := bstep (se 1 (by rfl) ⟨267450416, by rfl⟩ : syracuseStep 356600555 = 534900833) B534900833
theorem B2575175 : Blo 1715058 2575175 := bstep (se 1 (by rfl) ⟨1931381, by rfl⟩ : syracuseStep 2575175 = 3862763) B3862763
theorem B2575337 : Blo 1715058 2575337 := bstep (se 2 (by rfl) ⟨965751, by rfl⟩ : syracuseStep 2575337 = 1931503) B1931503
theorem B2575529 : Blo 1715058 2575529 := bstep (se 2 (by rfl) ⟨965823, by rfl⟩ : syracuseStep 2575529 = 1931647) B1931647
theorem B8687087 : Blo 1715058 8687087 := bstep (se 1 (by rfl) ⟨6515315, by rfl⟩ : syracuseStep 8687087 = 13030631) B13030631
theorem B1715867 : Blo 1715058 1715867 := bstep (se 1 (by rfl) ⟨1286900, by rfl⟩ : syracuseStep 1715867 = 2573801) B2573801
theorem B1715919 : Blo 1715058 1715919 := bstep (se 1 (by rfl) ⟨1286939, by rfl⟩ : syracuseStep 1715919 = 2573879) B2573879
theorem B1715995 : Blo 1715058 1715995 := bstep (se 1 (by rfl) ⟨1286996, by rfl⟩ : syracuseStep 1715995 = 2573993) B2573993
theorem B4124897 : Blo 1715058 4124897 := bstep (se 2 (by rfl) ⟨1546836, by rfl⟩ : syracuseStep 4124897 = 3093673) B3093673
theorem B1716543 : Blo 1715058 1716543 := bstep (se 1 (by rfl) ⟨1287407, by rfl⟩ : syracuseStep 1716543 = 2574815) B2574815
theorem B3863015 : Blo 1715058 3863015 := bstep (se 1 (by rfl) ⟨2897261, by rfl⟩ : syracuseStep 3863015 = 5794523) B5794523
theorem B1716991 : Blo 1715058 1716991 := bstep (se 1 (by rfl) ⟨1287743, by rfl⟩ : syracuseStep 1716991 = 2575487) B2575487
theorem B4887935 : Blo 1715058 4887935 := bstep (se 1 (by rfl) ⟨3665951, by rfl⟩ : syracuseStep 4887935 = 7331903) B7331903
theorem B3257833 : Blo 1715058 3257833 := bstep (se 2 (by rfl) ⟨1221687, by rfl⟩ : syracuseStep 3257833 = 2443375) B2443375
theorem B1930783 : Blo 1715058 1930783 := bstep (se 1 (by rfl) ⟨1448087, by rfl⟩ : syracuseStep 1930783 = 2896175) B2896175
theorem B3257977 : Blo 1715058 3257977 := bstep (se 2 (by rfl) ⟨1221741, by rfl⟩ : syracuseStep 3257977 = 2443483) B2443483
theorem B601954253 : Blo 1715058 601954253 := bstep (se 3 (by rfl) ⟨112866422, by rfl⟩ : syracuseStep 601954253 = 225732845) B225732845
theorem B8247527 : Blo 1715058 8247527 := bstep (se 1 (by rfl) ⟨6185645, by rfl⟩ : syracuseStep 8247527 = 12371291) B12371291
theorem B5790311 : Blo 1715058 5790311 := bstep (se 1 (by rfl) ⟨4342733, by rfl⟩ : syracuseStep 5790311 = 8685467) B8685467
theorem B150461219 : Blo 1715058 150461219 := bstep (se 1 (by rfl) ⟨112845914, by rfl⟩ : syracuseStep 150461219 = 225691829) B225691829
theorem B39607505 : Blo 1715058 39607505 := bstep (se 2 (by rfl) ⟨14852814, by rfl⟩ : syracuseStep 39607505 = 29705629) B29705629
theorem B2573279 : Blo 1715058 2573279 := bstep (se 1 (by rfl) ⟨1929959, by rfl⟩ : syracuseStep 2573279 = 3859919) B3859919
theorem B401302835 : Blo 1715058 401302835 := bstep (se 1 (by rfl) ⟨300977126, by rfl⟩ : syracuseStep 401302835 = 601954253) B601954253
theorem B5498351 : Blo 1715058 5498351 := bstep (se 1 (by rfl) ⟨4123763, by rfl⟩ : syracuseStep 5498351 = 8247527) B8247527
theorem B4343503 : Blo 1715058 4343503 := bstep (se 1 (by rfl) ⟨3257627, by rfl⟩ : syracuseStep 4343503 = 6515255) B6515255
theorem B3860207 : Blo 1715058 3860207 := bstep (se 1 (by rfl) ⟨2895155, by rfl⟩ : syracuseStep 3860207 = 5790311) B5790311
theorem B237733703 : Blo 1715058 237733703 := bstep (se 1 (by rfl) ⟨178300277, by rfl⟩ : syracuseStep 237733703 = 356600555) B356600555
theorem B4343777 : Blo 1715058 4343777 := bstep (se 2 (by rfl) ⟨1628916, by rfl⟩ : syracuseStep 4343777 = 3257833) B3257833
theorem B2574377 : Blo 1715058 2574377 := bstep (se 2 (by rfl) ⟨965391, by rfl⟩ : syracuseStep 2574377 = 1930783) B1930783
theorem B26405003 : Blo 1715058 26405003 := bstep (se 1 (by rfl) ⟨19803752, by rfl⟩ : syracuseStep 26405003 = 39607505) B39607505
theorem B4343969 : Blo 1715058 4343969 := bstep (se 2 (by rfl) ⟨1628988, by rfl⟩ : syracuseStep 4343969 = 3257977) B3257977
theorem B1715071 : Blo 1715058 1715071 := bstep (se 1 (by rfl) ⟨1286303, by rfl⟩ : syracuseStep 1715071 = 2572607) B2572607
theorem B2575343 : Blo 1715058 2575343 := bstep (se 1 (by rfl) ⟨1931507, by rfl⟩ : syracuseStep 2575343 = 3863015) B3863015
theorem B1715231 : Blo 1715058 1715231 := bstep (se 1 (by rfl) ⟨1286423, by rfl⟩ : syracuseStep 1715231 = 2572847) B2572847
theorem B1715291 : Blo 1715058 1715291 := bstep (se 1 (by rfl) ⟨1286468, by rfl⟩ : syracuseStep 1715291 = 2572937) B2572937
theorem B2894953 : Blo 1715058 2894953 := bstep (se 2 (by rfl) ⟨1085607, by rfl⟩ : syracuseStep 2894953 = 2171215) B2171215
theorem B1715311 : Blo 1715058 1715311 := bstep (se 1 (by rfl) ⟨1286483, by rfl⟩ : syracuseStep 1715311 = 2572967) B2572967
theorem B1715327 : Blo 1715058 1715327 := bstep (se 1 (by rfl) ⟨1286495, by rfl⟩ : syracuseStep 1715327 = 2572991) B2572991
theorem B1715695 : Blo 1715058 1715695 := bstep (se 1 (by rfl) ⟨1286771, by rfl⟩ : syracuseStep 1715695 = 2573543) B2573543
theorem B1716223 : Blo 1715058 1716223 := bstep (se 1 (by rfl) ⟨1287167, by rfl⟩ : syracuseStep 1716223 = 2574335) B2574335
theorem B24752375 : Blo 1715058 24752375 := bstep (se 1 (by rfl) ⟨18564281, by rfl⟩ : syracuseStep 24752375 = 37128563) B37128563
theorem B3862907 : Blo 1715058 3862907 := bstep (se 1 (by rfl) ⟨2897180, by rfl⟩ : syracuseStep 3862907 = 5794361) B5794361
theorem B1716671 : Blo 1715058 1716671 := bstep (se 1 (by rfl) ⟨1287503, by rfl⟩ : syracuseStep 1716671 = 2575007) B2575007
theorem B100307479 : Blo 1715058 100307479 := bstep (se 1 (by rfl) ⟨75230609, by rfl⟩ : syracuseStep 100307479 = 150461219) B150461219
theorem B1716783 : Blo 1715058 1716783 := bstep (se 1 (by rfl) ⟨1287587, by rfl⟩ : syracuseStep 1716783 = 2575175) B2575175
theorem B1716891 : Blo 1715058 1716891 := bstep (se 1 (by rfl) ⟨1287668, by rfl⟩ : syracuseStep 1716891 = 2575337) B2575337
theorem B1717019 : Blo 1715058 1717019 := bstep (se 1 (by rfl) ⟨1287764, by rfl⟩ : syracuseStep 1717019 = 2575529) B2575529
theorem B2749931 : Blo 1715058 2749931 := bstep (se 1 (by rfl) ⟨2062448, by rfl⟩ : syracuseStep 2749931 = 4124897) B4124897
theorem B3258623 : Blo 1715058 3258623 := bstep (se 1 (by rfl) ⟨2443967, by rfl⟩ : syracuseStep 3258623 = 4887935) B4887935
theorem B571546115 : Blo 1715058 571546115 := bstep (se 1 (by rfl) ⟨428659586, by rfl⟩ : syracuseStep 571546115 = 857319173) B857319173
theorem B5791391 : Blo 1715058 5791391 := bstep (se 1 (by rfl) ⟨4343543, by rfl⟩ : syracuseStep 5791391 = 8687087) B8687087
theorem B133743305 : Blo 1715058 133743305 := bstep (se 2 (by rfl) ⟨50153739, by rfl⟩ : syracuseStep 133743305 = 100307479) B100307479
theorem B267535223 : Blo 1715058 267535223 := bstep (se 1 (by rfl) ⟨200651417, by rfl⟩ : syracuseStep 267535223 = 401302835) B401302835
theorem B2573471 : Blo 1715058 2573471 := bstep (se 1 (by rfl) ⟨1930103, by rfl⟩ : syracuseStep 2573471 = 3860207) B3860207
theorem B3859937 : Blo 1715058 3859937 := bstep (se 2 (by rfl) ⟨1447476, by rfl⟩ : syracuseStep 3859937 = 2894953) B2894953
theorem B2172415 : Blo 1715058 2172415 := bstep (se 1 (by rfl) ⟨1629311, by rfl⟩ : syracuseStep 2172415 = 3258623) B3258623
theorem B3860927 : Blo 1715058 3860927 := bstep (se 1 (by rfl) ⟨2895695, by rfl⟩ : syracuseStep 3860927 = 5791391) B5791391
theorem B16501583 : Blo 1715058 16501583 := bstep (se 1 (by rfl) ⟨12376187, by rfl⟩ : syracuseStep 16501583 = 24752375) B24752375
theorem B2575271 : Blo 1715058 2575271 := bstep (se 1 (by rfl) ⟨1931453, by rfl⟩ : syracuseStep 2575271 = 3862907) B3862907
theorem B1715519 : Blo 1715058 1715519 := bstep (se 1 (by rfl) ⟨1286639, by rfl⟩ : syracuseStep 1715519 = 2573279) B2573279
theorem B3665567 : Blo 1715058 3665567 := bstep (se 1 (by rfl) ⟨2749175, by rfl⟩ : syracuseStep 3665567 = 5498351) B5498351
theorem B2895851 : Blo 1715058 2895851 := bstep (se 1 (by rfl) ⟨2171888, by rfl⟩ : syracuseStep 2895851 = 4343777) B4343777
theorem B1716251 : Blo 1715058 1716251 := bstep (se 1 (by rfl) ⟨1287188, by rfl⟩ : syracuseStep 1716251 = 2574377) B2574377
theorem B2895979 : Blo 1715058 2895979 := bstep (se 1 (by rfl) ⟨2171984, by rfl⟩ : syracuseStep 2895979 = 4343969) B4343969
theorem B381030743 : Blo 1715058 381030743 := bstep (se 1 (by rfl) ⟨285773057, by rfl⟩ : syracuseStep 381030743 = 571546115) B571546115
theorem B1716895 : Blo 1715058 1716895 := bstep (se 1 (by rfl) ⟨1287671, by rfl⟩ : syracuseStep 1716895 = 2575343) B2575343
theorem B1833287 : Blo 1715058 1833287 := bstep (se 1 (by rfl) ⟨1374965, by rfl⟩ : syracuseStep 1833287 = 2749931) B2749931
theorem B158489135 : Blo 1715058 158489135 := bstep (se 1 (by rfl) ⟨118866851, by rfl⟩ : syracuseStep 158489135 = 237733703) B237733703
theorem B17603335 : Blo 1715058 17603335 := bstep (se 1 (by rfl) ⟨13202501, by rfl⟩ : syracuseStep 17603335 = 26405003) B26405003
theorem B5791337 : Blo 1715058 5791337 := bstep (se 2 (by rfl) ⟨2171751, by rfl⟩ : syracuseStep 5791337 = 4343503) B4343503
theorem B89162203 : Blo 1715058 89162203 := bstep (se 1 (by rfl) ⟨66871652, by rfl⟩ : syracuseStep 89162203 = 133743305) B133743305
theorem B178356815 : Blo 1715058 178356815 := bstep (se 1 (by rfl) ⟨133767611, by rfl⟩ : syracuseStep 178356815 = 267535223) B267535223
theorem B2573291 : Blo 1715058 2573291 := bstep (se 1 (by rfl) ⟨1929968, by rfl⟩ : syracuseStep 2573291 = 3859937) B3859937
theorem B2573951 : Blo 1715058 2573951 := bstep (se 1 (by rfl) ⟨1930463, by rfl⟩ : syracuseStep 2573951 = 3860927) B3860927
theorem B3860891 : Blo 1715058 3860891 := bstep (se 1 (by rfl) ⟨2895668, by rfl⟩ : syracuseStep 3860891 = 5791337) B5791337
theorem B2443711 : Blo 1715058 2443711 := bstep (se 1 (by rfl) ⟨1832783, by rfl⟩ : syracuseStep 2443711 = 3665567) B3665567
theorem B3861305 : Blo 1715058 3861305 := bstep (se 2 (by rfl) ⟨1447989, by rfl⟩ : syracuseStep 3861305 = 2895979) B2895979
theorem B254020495 : Blo 1715058 254020495 := bstep (se 1 (by rfl) ⟨190515371, by rfl⟩ : syracuseStep 254020495 = 381030743) B381030743
theorem B1715647 : Blo 1715058 1715647 := bstep (se 1 (by rfl) ⟨1286735, by rfl⟩ : syracuseStep 1715647 = 2573471) B2573471
theorem B93884453 : Blo 1715058 93884453 := bstep (se 4 (by rfl) ⟨8801667, by rfl⟩ : syracuseStep 93884453 = 17603335) B17603335
theorem B1716847 : Blo 1715058 1716847 := bstep (se 1 (by rfl) ⟨1287635, by rfl⟩ : syracuseStep 1716847 = 2575271) B2575271
theorem B2896553 : Blo 1715058 2896553 := bstep (se 2 (by rfl) ⟨1086207, by rfl⟩ : syracuseStep 2896553 = 2172415) B2172415
theorem B1930567 : Blo 1715058 1930567 := bstep (se 1 (by rfl) ⟨1447925, by rfl⟩ : syracuseStep 1930567 = 2895851) B2895851
theorem B4888765 : Blo 1715058 4888765 := bstep (se 3 (by rfl) ⟨916643, by rfl⟩ : syracuseStep 4888765 = 1833287) B1833287
theorem B105659423 : Blo 1715058 105659423 := bstep (se 1 (by rfl) ⟨79244567, by rfl⟩ : syracuseStep 105659423 = 158489135) B158489135
theorem B11001055 : Blo 1715058 11001055 := bstep (se 1 (by rfl) ⟨8250791, by rfl⟩ : syracuseStep 11001055 = 16501583) B16501583
theorem B118882937 : Blo 1715058 118882937 := bstep (se 2 (by rfl) ⟨44581101, by rfl⟩ : syracuseStep 118882937 = 89162203) B89162203
theorem B2573927 : Blo 1715058 2573927 := bstep (se 1 (by rfl) ⟨1930445, by rfl⟩ : syracuseStep 2573927 = 3860891) B3860891
theorem B2574089 : Blo 1715058 2574089 := bstep (se 2 (by rfl) ⟨965283, by rfl⟩ : syracuseStep 2574089 = 1930567) B1930567
theorem B2574203 : Blo 1715058 2574203 := bstep (se 1 (by rfl) ⟨1930652, by rfl⟩ : syracuseStep 2574203 = 3861305) B3861305
theorem B62589635 : Blo 1715058 62589635 := bstep (se 1 (by rfl) ⟨46942226, by rfl⟩ : syracuseStep 62589635 = 93884453) B93884453
theorem B1715527 : Blo 1715058 1715527 := bstep (se 1 (by rfl) ⟨1286645, by rfl⟩ : syracuseStep 1715527 = 2573291) B2573291
theorem B1715967 : Blo 1715058 1715967 := bstep (se 1 (by rfl) ⟨1286975, by rfl⟩ : syracuseStep 1715967 = 2573951) B2573951
theorem B338693993 : Blo 1715058 338693993 := bstep (se 2 (by rfl) ⟨127010247, by rfl⟩ : syracuseStep 338693993 = 254020495) B254020495
theorem B14668073 : Blo 1715058 14668073 := bstep (se 2 (by rfl) ⟨5500527, by rfl⟩ : syracuseStep 14668073 = 11001055) B11001055
theorem B70439615 : Blo 1715058 70439615 := bstep (se 1 (by rfl) ⟨52829711, by rfl⟩ : syracuseStep 70439615 = 105659423) B105659423
theorem B6518353 : Blo 1715058 6518353 := bstep (se 2 (by rfl) ⟨2444382, by rfl⟩ : syracuseStep 6518353 = 4888765) B4888765
theorem B118904543 : Blo 1715058 118904543 := bstep (se 1 (by rfl) ⟨89178407, by rfl⟩ : syracuseStep 118904543 = 178356815) B178356815
theorem B1931035 : Blo 1715058 1931035 := bstep (se 1 (by rfl) ⟨1448276, by rfl⟩ : syracuseStep 1931035 = 2896553) B2896553
theorem B3258281 : Blo 1715058 3258281 := bstep (se 2 (by rfl) ⟨1221855, by rfl⟩ : syracuseStep 3258281 = 2443711) B2443711
theorem B2172187 : Blo 1715058 2172187 := bstep (se 1 (by rfl) ⟨1629140, by rfl⟩ : syracuseStep 2172187 = 3258281) B3258281
theorem B2574713 : Blo 1715058 2574713 := bstep (se 2 (by rfl) ⟨965517, by rfl⟩ : syracuseStep 2574713 = 1931035) B1931035
theorem B46959743 : Blo 1715058 46959743 := bstep (se 1 (by rfl) ⟨35219807, by rfl⟩ : syracuseStep 46959743 = 70439615) B70439615
theorem B1715951 : Blo 1715058 1715951 := bstep (se 1 (by rfl) ⟨1286963, by rfl⟩ : syracuseStep 1715951 = 2573927) B2573927
theorem B79269695 : Blo 1715058 79269695 := bstep (se 1 (by rfl) ⟨59452271, by rfl⟩ : syracuseStep 79269695 = 118904543) B118904543
theorem B1716059 : Blo 1715058 1716059 := bstep (se 1 (by rfl) ⟨1287044, by rfl⟩ : syracuseStep 1716059 = 2574089) B2574089
theorem B1716135 : Blo 1715058 1716135 := bstep (se 1 (by rfl) ⟨1287101, by rfl⟩ : syracuseStep 1716135 = 2574203) B2574203
theorem B41726423 : Blo 1715058 41726423 := bstep (se 1 (by rfl) ⟨31294817, by rfl⟩ : syracuseStep 41726423 = 62589635) B62589635
theorem B9778715 : Blo 1715058 9778715 := bstep (se 1 (by rfl) ⟨7334036, by rfl⟩ : syracuseStep 9778715 = 14668073) B14668073
theorem B317021165 : Blo 1715058 317021165 := bstep (se 3 (by rfl) ⟨59441468, by rfl⟩ : syracuseStep 317021165 = 118882937) B118882937
theorem B8691137 : Blo 1715058 8691137 := bstep (se 2 (by rfl) ⟨3259176, by rfl⟩ : syracuseStep 8691137 = 6518353) B6518353
theorem B225795995 : Blo 1715058 225795995 := bstep (se 1 (by rfl) ⟨169346996, by rfl⟩ : syracuseStep 225795995 = 338693993) B338693993
theorem B211347443 : Blo 1715058 211347443 := bstep (se 1 (by rfl) ⟨158510582, by rfl⟩ : syracuseStep 211347443 = 317021165) B317021165
theorem B5794091 : Blo 1715058 5794091 := bstep (se 1 (by rfl) ⟨4345568, by rfl⟩ : syracuseStep 5794091 = 8691137) B8691137
theorem B150530663 : Blo 1715058 150530663 := bstep (se 1 (by rfl) ⟨112897997, by rfl⟩ : syracuseStep 150530663 = 225795995) B225795995
theorem B1716475 : Blo 1715058 1716475 := bstep (se 1 (by rfl) ⟨1287356, by rfl⟩ : syracuseStep 1716475 = 2574713) B2574713
theorem B2896249 : Blo 1715058 2896249 := bstep (se 2 (by rfl) ⟨1086093, by rfl⟩ : syracuseStep 2896249 = 2172187) B2172187
theorem B31306495 : Blo 1715058 31306495 := bstep (se 1 (by rfl) ⟨23479871, by rfl⟩ : syracuseStep 31306495 = 46959743) B46959743
theorem B27817615 : Blo 1715058 27817615 := bstep (se 1 (by rfl) ⟨20863211, by rfl⟩ : syracuseStep 27817615 = 41726423) B41726423
theorem B6519143 : Blo 1715058 6519143 := bstep (se 1 (by rfl) ⟨4889357, by rfl⟩ : syracuseStep 6519143 = 9778715) B9778715
theorem B52846463 : Blo 1715058 52846463 := bstep (se 1 (by rfl) ⟨39634847, by rfl⟩ : syracuseStep 52846463 = 79269695) B79269695
theorem B3861665 : Blo 1715058 3861665 := bstep (se 2 (by rfl) ⟨1448124, by rfl⟩ : syracuseStep 3861665 = 2896249) B2896249
theorem B41741993 : Blo 1715058 41741993 := bstep (se 2 (by rfl) ⟨15653247, by rfl⟩ : syracuseStep 41741993 = 31306495) B31306495
theorem B140898295 : Blo 1715058 140898295 := bstep (se 1 (by rfl) ⟨105673721, by rfl⟩ : syracuseStep 140898295 = 211347443) B211347443
theorem B3862727 : Blo 1715058 3862727 := bstep (se 1 (by rfl) ⟨2897045, by rfl⟩ : syracuseStep 3862727 = 5794091) B5794091
theorem B4346095 : Blo 1715058 4346095 := bstep (se 1 (by rfl) ⟨3259571, by rfl⟩ : syracuseStep 4346095 = 6519143) B6519143
theorem B37090153 : Blo 1715058 37090153 := bstep (se 2 (by rfl) ⟨13908807, by rfl⟩ : syracuseStep 37090153 = 27817615) B27817615
theorem B140923901 : Blo 1715058 140923901 := bstep (se 3 (by rfl) ⟨26423231, by rfl⟩ : syracuseStep 140923901 = 52846463) B52846463
theorem B401415101 : Blo 1715058 401415101 := bstep (se 3 (by rfl) ⟨75265331, by rfl⟩ : syracuseStep 401415101 = 150530663) B150530663
theorem B267610067 : Blo 1715058 267610067 := bstep (se 1 (by rfl) ⟨200707550, by rfl⟩ : syracuseStep 267610067 = 401415101) B401415101
theorem B2574443 : Blo 1715058 2574443 := bstep (se 1 (by rfl) ⟨1930832, by rfl⟩ : syracuseStep 2574443 = 3861665) B3861665
theorem B2575151 : Blo 1715058 2575151 := bstep (se 1 (by rfl) ⟨1931363, by rfl⟩ : syracuseStep 2575151 = 3862727) B3862727
theorem B5794793 : Blo 1715058 5794793 := bstep (se 2 (by rfl) ⟨2173047, by rfl⟩ : syracuseStep 5794793 = 4346095) B4346095
theorem B93949267 : Blo 1715058 93949267 := bstep (se 1 (by rfl) ⟨70461950, by rfl⟩ : syracuseStep 93949267 = 140923901) B140923901
theorem B187864393 : Blo 1715058 187864393 := bstep (se 2 (by rfl) ⟨70449147, by rfl⟩ : syracuseStep 187864393 = 140898295) B140898295
theorem B49453537 : Blo 1715058 49453537 := bstep (se 2 (by rfl) ⟨18545076, by rfl⟩ : syracuseStep 49453537 = 37090153) B37090153
theorem B111311981 : Blo 1715058 111311981 := bstep (se 3 (by rfl) ⟨20870996, by rfl⟩ : syracuseStep 111311981 = 41741993) B41741993
theorem B65938049 : Blo 1715058 65938049 := bstep (se 2 (by rfl) ⟨24726768, by rfl⟩ : syracuseStep 65938049 = 49453537) B49453537
theorem B178406711 : Blo 1715058 178406711 := bstep (se 1 (by rfl) ⟨133805033, by rfl⟩ : syracuseStep 178406711 = 267610067) B267610067
theorem B125265689 : Blo 1715058 125265689 := bstep (se 2 (by rfl) ⟨46974633, by rfl⟩ : syracuseStep 125265689 = 93949267) B93949267
theorem B1716295 : Blo 1715058 1716295 := bstep (se 1 (by rfl) ⟨1287221, by rfl⟩ : syracuseStep 1716295 = 2574443) B2574443
theorem B1716767 : Blo 1715058 1716767 := bstep (se 1 (by rfl) ⟨1287575, by rfl⟩ : syracuseStep 1716767 = 2575151) B2575151
theorem B3863195 : Blo 1715058 3863195 := bstep (se 1 (by rfl) ⟨2897396, by rfl⟩ : syracuseStep 3863195 = 5794793) B5794793
theorem B74207987 : Blo 1715058 74207987 := bstep (se 1 (by rfl) ⟨55655990, by rfl⟩ : syracuseStep 74207987 = 111311981) B111311981
theorem B250485857 : Blo 1715058 250485857 := bstep (se 2 (by rfl) ⟨93932196, by rfl⟩ : syracuseStep 250485857 = 187864393) B187864393
theorem B43958699 : Blo 1715058 43958699 := bstep (se 1 (by rfl) ⟨32969024, by rfl⟩ : syracuseStep 43958699 = 65938049) B65938049
theorem B49471991 : Blo 1715058 49471991 := bstep (se 1 (by rfl) ⟨37103993, by rfl⟩ : syracuseStep 49471991 = 74207987) B74207987
theorem B83510459 : Blo 1715058 83510459 := bstep (se 1 (by rfl) ⟨62632844, by rfl⟩ : syracuseStep 83510459 = 125265689) B125265689
theorem B2575463 : Blo 1715058 2575463 := bstep (se 1 (by rfl) ⟨1931597, by rfl⟩ : syracuseStep 2575463 = 3863195) B3863195
theorem B166990571 : Blo 1715058 166990571 := bstep (se 1 (by rfl) ⟨125242928, by rfl⟩ : syracuseStep 166990571 = 250485857) B250485857
theorem B118937807 : Blo 1715058 118937807 := bstep (se 1 (by rfl) ⟨89203355, by rfl⟩ : syracuseStep 118937807 = 178406711) B178406711
theorem B32981327 : Blo 1715058 32981327 := bstep (se 1 (by rfl) ⟨24735995, by rfl⟩ : syracuseStep 32981327 = 49471991) B49471991
theorem B55673639 : Blo 1715058 55673639 := bstep (se 1 (by rfl) ⟨41755229, by rfl⟩ : syracuseStep 55673639 = 83510459) B83510459
theorem B79291871 : Blo 1715058 79291871 := bstep (se 1 (by rfl) ⟨59468903, by rfl⟩ : syracuseStep 79291871 = 118937807) B118937807
theorem B29305799 : Blo 1715058 29305799 := bstep (se 1 (by rfl) ⟨21979349, by rfl⟩ : syracuseStep 29305799 = 43958699) B43958699
theorem B1716975 : Blo 1715058 1716975 := bstep (se 1 (by rfl) ⟨1287731, by rfl⟩ : syracuseStep 1716975 = 2575463) B2575463
theorem B111327047 : Blo 1715058 111327047 := bstep (se 1 (by rfl) ⟨83495285, by rfl⟩ : syracuseStep 111327047 = 166990571) B166990571
theorem B21987551 : Blo 1715058 21987551 := bstep (se 1 (by rfl) ⟨16490663, by rfl⟩ : syracuseStep 21987551 = 32981327) B32981327
theorem B37115759 : Blo 1715058 37115759 := bstep (se 1 (by rfl) ⟨27836819, by rfl⟩ : syracuseStep 37115759 = 55673639) B55673639
theorem B52861247 : Blo 1715058 52861247 := bstep (se 1 (by rfl) ⟨39645935, by rfl⟩ : syracuseStep 52861247 = 79291871) B79291871
theorem B74218031 : Blo 1715058 74218031 := bstep (se 1 (by rfl) ⟨55663523, by rfl⟩ : syracuseStep 74218031 = 111327047) B111327047
theorem B19537199 : Blo 1715058 19537199 := bstep (se 1 (by rfl) ⟨14652899, by rfl⟩ : syracuseStep 19537199 = 29305799) B29305799
theorem B14658367 : Blo 1715058 14658367 := bstep (se 1 (by rfl) ⟨10993775, by rfl⟩ : syracuseStep 14658367 = 21987551) B21987551
theorem B24743839 : Blo 1715058 24743839 := bstep (se 1 (by rfl) ⟨18557879, by rfl⟩ : syracuseStep 24743839 = 37115759) B37115759
theorem B35240831 : Blo 1715058 35240831 := bstep (se 1 (by rfl) ⟨26430623, by rfl⟩ : syracuseStep 35240831 = 52861247) B52861247
theorem B49478687 : Blo 1715058 49478687 := bstep (se 1 (by rfl) ⟨37109015, by rfl⟩ : syracuseStep 49478687 = 74218031) B74218031
theorem B13024799 : Blo 1715058 13024799 := bstep (se 1 (by rfl) ⟨9768599, by rfl⟩ : syracuseStep 13024799 = 19537199) B19537199
theorem B32991785 : Blo 1715058 32991785 := bstep (se 2 (by rfl) ⟨12371919, by rfl⟩ : syracuseStep 32991785 = 24743839) B24743839
theorem B32985791 : Blo 1715058 32985791 := bstep (se 1 (by rfl) ⟨24739343, by rfl⟩ : syracuseStep 32985791 = 49478687) B49478687
theorem B19544489 : Blo 1715058 19544489 := bstep (se 2 (by rfl) ⟨7329183, by rfl⟩ : syracuseStep 19544489 = 14658367) B14658367
theorem B23493887 : Blo 1715058 23493887 := bstep (se 1 (by rfl) ⟨17620415, by rfl⟩ : syracuseStep 23493887 = 35240831) B35240831
theorem B8683199 : Blo 1715058 8683199 := bstep (se 1 (by rfl) ⟨6512399, by rfl⟩ : syracuseStep 8683199 = 13024799) B13024799
theorem B21990527 : Blo 1715058 21990527 := bstep (se 1 (by rfl) ⟨16492895, by rfl⟩ : syracuseStep 21990527 = 32985791) B32985791
theorem B13029659 : Blo 1715058 13029659 := bstep (se 1 (by rfl) ⟨9772244, by rfl⟩ : syracuseStep 13029659 = 19544489) B19544489
theorem B5788799 : Blo 1715058 5788799 := bstep (se 1 (by rfl) ⟨4341599, by rfl⟩ : syracuseStep 5788799 = 8683199) B8683199
theorem B21994523 : Blo 1715058 21994523 := bstep (se 1 (by rfl) ⟨16495892, by rfl⟩ : syracuseStep 21994523 = 32991785) B32991785
theorem B15662591 : Blo 1715058 15662591 := bstep (se 1 (by rfl) ⟨11746943, by rfl⟩ : syracuseStep 15662591 = 23493887) B23493887
theorem B3859199 : Blo 1715058 3859199 := bstep (se 1 (by rfl) ⟨2894399, by rfl⟩ : syracuseStep 3859199 = 5788799) B5788799
theorem B8686439 : Blo 1715058 8686439 := bstep (se 1 (by rfl) ⟨6514829, by rfl⟩ : syracuseStep 8686439 = 13029659) B13029659
theorem B14660351 : Blo 1715058 14660351 := bstep (se 1 (by rfl) ⟨10995263, by rfl⟩ : syracuseStep 14660351 = 21990527) B21990527
theorem B10441727 : Blo 1715058 10441727 := bstep (se 1 (by rfl) ⟨7831295, by rfl⟩ : syracuseStep 10441727 = 15662591) B15662591
theorem B14663015 : Blo 1715058 14663015 := bstep (se 1 (by rfl) ⟨10997261, by rfl⟩ : syracuseStep 14663015 = 21994523) B21994523
theorem B2572799 : Blo 1715058 2572799 := bstep (se 1 (by rfl) ⟨1929599, by rfl⟩ : syracuseStep 2572799 = 3859199) B3859199
theorem B9773567 : Blo 1715058 9773567 := bstep (se 1 (by rfl) ⟨7330175, by rfl⟩ : syracuseStep 9773567 = 14660351) B14660351
theorem B9775343 : Blo 1715058 9775343 := bstep (se 1 (by rfl) ⟨7331507, by rfl⟩ : syracuseStep 9775343 = 14663015) B14663015
theorem B6961151 : Blo 1715058 6961151 := bstep (se 1 (by rfl) ⟨5220863, by rfl⟩ : syracuseStep 6961151 = 10441727) B10441727
theorem B5790959 : Blo 1715058 5790959 := bstep (se 1 (by rfl) ⟨4343219, by rfl⟩ : syracuseStep 5790959 = 8686439) B8686439
theorem B3860639 : Blo 1715058 3860639 := bstep (se 1 (by rfl) ⟨2895479, by rfl⟩ : syracuseStep 3860639 = 5790959) B5790959
theorem B1715199 : Blo 1715058 1715199 := bstep (se 1 (by rfl) ⟨1286399, by rfl⟩ : syracuseStep 1715199 = 2572799) B2572799
theorem B6515711 : Blo 1715058 6515711 := bstep (se 1 (by rfl) ⟨4886783, by rfl⟩ : syracuseStep 6515711 = 9773567) B9773567
theorem B6516895 : Blo 1715058 6516895 := bstep (se 1 (by rfl) ⟨4887671, by rfl⟩ : syracuseStep 6516895 = 9775343) B9775343
theorem B18563069 : Blo 1715058 18563069 := bstep (se 3 (by rfl) ⟨3480575, by rfl⟩ : syracuseStep 18563069 = 6961151) B6961151
theorem B2573759 : Blo 1715058 2573759 := bstep (se 1 (by rfl) ⟨1930319, by rfl⟩ : syracuseStep 2573759 = 3860639) B3860639
theorem B4343807 : Blo 1715058 4343807 := bstep (se 1 (by rfl) ⟨3257855, by rfl⟩ : syracuseStep 4343807 = 6515711) B6515711
theorem B12375379 : Blo 1715058 12375379 := bstep (se 1 (by rfl) ⟨9281534, by rfl⟩ : syracuseStep 12375379 = 18563069) B18563069
theorem B8689193 : Blo 1715058 8689193 := bstep (se 2 (by rfl) ⟨3258447, by rfl⟩ : syracuseStep 8689193 = 6516895) B6516895
theorem B5792795 : Blo 1715058 5792795 := bstep (se 1 (by rfl) ⟨4344596, by rfl⟩ : syracuseStep 5792795 = 8689193) B8689193
theorem B16500505 : Blo 1715058 16500505 := bstep (se 2 (by rfl) ⟨6187689, by rfl⟩ : syracuseStep 16500505 = 12375379) B12375379
theorem B1715839 : Blo 1715058 1715839 := bstep (se 1 (by rfl) ⟨1286879, by rfl⟩ : syracuseStep 1715839 = 2573759) B2573759
theorem B2895871 : Blo 1715058 2895871 := bstep (se 1 (by rfl) ⟨2171903, by rfl⟩ : syracuseStep 2895871 = 4343807) B4343807
theorem B3861161 : Blo 1715058 3861161 := bstep (se 2 (by rfl) ⟨1447935, by rfl⟩ : syracuseStep 3861161 = 2895871) B2895871
theorem B3861863 : Blo 1715058 3861863 := bstep (se 1 (by rfl) ⟨2896397, by rfl⟩ : syracuseStep 3861863 = 5792795) B5792795
theorem B22000673 : Blo 1715058 22000673 := bstep (se 2 (by rfl) ⟨8250252, by rfl⟩ : syracuseStep 22000673 = 16500505) B16500505
theorem B2574107 : Blo 1715058 2574107 := bstep (se 1 (by rfl) ⟨1930580, by rfl⟩ : syracuseStep 2574107 = 3861161) B3861161
theorem B2574575 : Blo 1715058 2574575 := bstep (se 1 (by rfl) ⟨1930931, by rfl⟩ : syracuseStep 2574575 = 3861863) B3861863
theorem B14667115 : Blo 1715058 14667115 := bstep (se 1 (by rfl) ⟨11000336, by rfl⟩ : syracuseStep 14667115 = 22000673) B22000673
theorem B19556153 : Blo 1715058 19556153 := bstep (se 2 (by rfl) ⟨7333557, by rfl⟩ : syracuseStep 19556153 = 14667115) B14667115
theorem B1716071 : Blo 1715058 1716071 := bstep (se 1 (by rfl) ⟨1287053, by rfl⟩ : syracuseStep 1716071 = 2574107) B2574107
theorem B1716383 : Blo 1715058 1716383 := bstep (se 1 (by rfl) ⟨1287287, by rfl⟩ : syracuseStep 1716383 = 2574575) B2574575
theorem B13037435 : Blo 1715058 13037435 := bstep (se 1 (by rfl) ⟨9778076, by rfl⟩ : syracuseStep 13037435 = 19556153) B19556153
theorem B8691623 : Blo 1715058 8691623 := bstep (se 1 (by rfl) ⟨6518717, by rfl⟩ : syracuseStep 8691623 = 13037435) B13037435
theorem B5794415 : Blo 1715058 5794415 := bstep (se 1 (by rfl) ⟨4345811, by rfl⟩ : syracuseStep 5794415 = 8691623) B8691623
theorem B3862943 : Blo 1715058 3862943 := bstep (se 1 (by rfl) ⟨2897207, by rfl⟩ : syracuseStep 3862943 = 5794415) B5794415
theorem B2575295 : Blo 1715058 2575295 := bstep (se 1 (by rfl) ⟨1931471, by rfl⟩ : syracuseStep 2575295 = 3862943) B3862943
theorem B1716863 : Blo 1715058 1716863 := bstep (se 1 (by rfl) ⟨1287647, by rfl⟩ : syracuseStep 1716863 = 2575295) B2575295

theorem C0 (j : ℕ) (h1 : 428764 ≤ j) (h2 : j ≤ 429263) : Blo 1715058 (4 * j + 3) := by
  interval_cases j
  · exact B1715059
  · exact B1715063
  · exact B1715067
  · exact B1715071
  · exact B1715075
  · exact B1715079
  · exact B1715083
  · exact B1715087
  · exact B1715091
  · exact B1715095
  · exact B1715099
  · exact B1715103
  · exact B1715107
  · exact B1715111
  · exact B1715115
  · exact B1715119
  · exact B1715123
  · exact B1715127
  · exact B1715131
  · exact B1715135
  · exact B1715139
  · exact B1715143
  · exact B1715147
  · exact B1715151
  · exact B1715155
  · exact B1715159
  · exact B1715163
  · exact B1715167
  · exact B1715171
  · exact B1715175
  · exact B1715179
  · exact B1715183
  · exact B1715187
  · exact B1715191
  · exact B1715195
  · exact B1715199
  · exact B1715203
  · exact B1715207
  · exact B1715211
  · exact B1715215
  · exact B1715219
  · exact B1715223
  · exact B1715227
  · exact B1715231
  · exact B1715235
  · exact B1715239
  · exact B1715243
  · exact B1715247
  · exact B1715251
  · exact B1715255
  · exact B1715259
  · exact B1715263
  · exact B1715267
  · exact B1715271
  · exact B1715275
  · exact B1715279
  · exact B1715283
  · exact B1715287
  · exact B1715291
  · exact B1715295
  · exact B1715299
  · exact B1715303
  · exact B1715307
  · exact B1715311
  · exact B1715315
  · exact B1715319
  · exact B1715323
  · exact B1715327
  · exact B1715331
  · exact B1715335
  · exact B1715339
  · exact B1715343
  · exact B1715347
  · exact B1715351
  · exact B1715355
  · exact B1715359
  · exact B1715363
  · exact B1715367
  · exact B1715371
  · exact B1715375
  · exact B1715379
  · exact B1715383
  · exact B1715387
  · exact B1715391
  · exact B1715395
  · exact B1715399
  · exact B1715403
  · exact B1715407
  · exact B1715411
  · exact B1715415
  · exact B1715419
  · exact B1715423
  · exact B1715427
  · exact B1715431
  · exact B1715435
  · exact B1715439
  · exact B1715443
  · exact B1715447
  · exact B1715451
  · exact B1715455
  · exact B1715459
  · exact B1715463
  · exact B1715467
  · exact B1715471
  · exact B1715475
  · exact B1715479
  · exact B1715483
  · exact B1715487
  · exact B1715491
  · exact B1715495
  · exact B1715499
  · exact B1715503
  · exact B1715507
  · exact B1715511
  · exact B1715515
  · exact B1715519
  · exact B1715523
  · exact B1715527
  · exact B1715531
  · exact B1715535
  · exact B1715539
  · exact B1715543
  · exact B1715547
  · exact B1715551
  · exact B1715555
  · exact B1715559
  · exact B1715563
  · exact B1715567
  · exact B1715571
  · exact B1715575
  · exact B1715579
  · exact B1715583
  · exact B1715587
  · exact B1715591
  · exact B1715595
  · exact B1715599
  · exact B1715603
  · exact B1715607
  · exact B1715611
  · exact B1715615
  · exact B1715619
  · exact B1715623
  · exact B1715627
  · exact B1715631
  · exact B1715635
  · exact B1715639
  · exact B1715643
  · exact B1715647
  · exact B1715651
  · exact B1715655
  · exact B1715659
  · exact B1715663
  · exact B1715667
  · exact B1715671
  · exact B1715675
  · exact B1715679
  · exact B1715683
  · exact B1715687
  · exact B1715691
  · exact B1715695
  · exact B1715699
  · exact B1715703
  · exact B1715707
  · exact B1715711
  · exact B1715715
  · exact B1715719
  · exact B1715723
  · exact B1715727
  · exact B1715731
  · exact B1715735
  · exact B1715739
  · exact B1715743
  · exact B1715747
  · exact B1715751
  · exact B1715755
  · exact B1715759
  · exact B1715763
  · exact B1715767
  · exact B1715771
  · exact B1715775
  · exact B1715779
  · exact B1715783
  · exact B1715787
  · exact B1715791
  · exact B1715795
  · exact B1715799
  · exact B1715803
  · exact B1715807
  · exact B1715811
  · exact B1715815
  · exact B1715819
  · exact B1715823
  · exact B1715827
  · exact B1715831
  · exact B1715835
  · exact B1715839
  · exact B1715843
  · exact B1715847
  · exact B1715851
  · exact B1715855
  · exact B1715859
  · exact B1715863
  · exact B1715867
  · exact B1715871
  · exact B1715875
  · exact B1715879
  · exact B1715883
  · exact B1715887
  · exact B1715891
  · exact B1715895
  · exact B1715899
  · exact B1715903
  · exact B1715907
  · exact B1715911
  · exact B1715915
  · exact B1715919
  · exact B1715923
  · exact B1715927
  · exact B1715931
  · exact B1715935
  · exact B1715939
  · exact B1715943
  · exact B1715947
  · exact B1715951
  · exact B1715955
  · exact B1715959
  · exact B1715963
  · exact B1715967
  · exact B1715971
  · exact B1715975
  · exact B1715979
  · exact B1715983
  · exact B1715987
  · exact B1715991
  · exact B1715995
  · exact B1715999
  · exact B1716003
  · exact B1716007
  · exact B1716011
  · exact B1716015
  · exact B1716019
  · exact B1716023
  · exact B1716027
  · exact B1716031
  · exact B1716035
  · exact B1716039
  · exact B1716043
  · exact B1716047
  · exact B1716051
  · exact B1716055
  · exact B1716059
  · exact B1716063
  · exact B1716067
  · exact B1716071
  · exact B1716075
  · exact B1716079
  · exact B1716083
  · exact B1716087
  · exact B1716091
  · exact B1716095
  · exact B1716099
  · exact B1716103
  · exact B1716107
  · exact B1716111
  · exact B1716115
  · exact B1716119
  · exact B1716123
  · exact B1716127
  · exact B1716131
  · exact B1716135
  · exact B1716139
  · exact B1716143
  · exact B1716147
  · exact B1716151
  · exact B1716155
  · exact B1716159
  · exact B1716163
  · exact B1716167
  · exact B1716171
  · exact B1716175
  · exact B1716179
  · exact B1716183
  · exact B1716187
  · exact B1716191
  · exact B1716195
  · exact B1716199
  · exact B1716203
  · exact B1716207
  · exact B1716211
  · exact B1716215
  · exact B1716219
  · exact B1716223
  · exact B1716227
  · exact B1716231
  · exact B1716235
  · exact B1716239
  · exact B1716243
  · exact B1716247
  · exact B1716251
  · exact B1716255
  · exact B1716259
  · exact B1716263
  · exact B1716267
  · exact B1716271
  · exact B1716275
  · exact B1716279
  · exact B1716283
  · exact B1716287
  · exact B1716291
  · exact B1716295
  · exact B1716299
  · exact B1716303
  · exact B1716307
  · exact B1716311
  · exact B1716315
  · exact B1716319
  · exact B1716323
  · exact B1716327
  · exact B1716331
  · exact B1716335
  · exact B1716339
  · exact B1716343
  · exact B1716347
  · exact B1716351
  · exact B1716355
  · exact B1716359
  · exact B1716363
  · exact B1716367
  · exact B1716371
  · exact B1716375
  · exact B1716379
  · exact B1716383
  · exact B1716387
  · exact B1716391
  · exact B1716395
  · exact B1716399
  · exact B1716403
  · exact B1716407
  · exact B1716411
  · exact B1716415
  · exact B1716419
  · exact B1716423
  · exact B1716427
  · exact B1716431
  · exact B1716435
  · exact B1716439
  · exact B1716443
  · exact B1716447
  · exact B1716451
  · exact B1716455
  · exact B1716459
  · exact B1716463
  · exact B1716467
  · exact B1716471
  · exact B1716475
  · exact B1716479
  · exact B1716483
  · exact B1716487
  · exact B1716491
  · exact B1716495
  · exact B1716499
  · exact B1716503
  · exact B1716507
  · exact B1716511
  · exact B1716515
  · exact B1716519
  · exact B1716523
  · exact B1716527
  · exact B1716531
  · exact B1716535
  · exact B1716539
  · exact B1716543
  · exact B1716547
  · exact B1716551
  · exact B1716555
  · exact B1716559
  · exact B1716563
  · exact B1716567
  · exact B1716571
  · exact B1716575
  · exact B1716579
  · exact B1716583
  · exact B1716587
  · exact B1716591
  · exact B1716595
  · exact B1716599
  · exact B1716603
  · exact B1716607
  · exact B1716611
  · exact B1716615
  · exact B1716619
  · exact B1716623
  · exact B1716627
  · exact B1716631
  · exact B1716635
  · exact B1716639
  · exact B1716643
  · exact B1716647
  · exact B1716651
  · exact B1716655
  · exact B1716659
  · exact B1716663
  · exact B1716667
  · exact B1716671
  · exact B1716675
  · exact B1716679
  · exact B1716683
  · exact B1716687
  · exact B1716691
  · exact B1716695
  · exact B1716699
  · exact B1716703
  · exact B1716707
  · exact B1716711
  · exact B1716715
  · exact B1716719
  · exact B1716723
  · exact B1716727
  · exact B1716731
  · exact B1716735
  · exact B1716739
  · exact B1716743
  · exact B1716747
  · exact B1716751
  · exact B1716755
  · exact B1716759
  · exact B1716763
  · exact B1716767
  · exact B1716771
  · exact B1716775
  · exact B1716779
  · exact B1716783
  · exact B1716787
  · exact B1716791
  · exact B1716795
  · exact B1716799
  · exact B1716803
  · exact B1716807
  · exact B1716811
  · exact B1716815
  · exact B1716819
  · exact B1716823
  · exact B1716827
  · exact B1716831
  · exact B1716835
  · exact B1716839
  · exact B1716843
  · exact B1716847
  · exact B1716851
  · exact B1716855
  · exact B1716859
  · exact B1716863
  · exact B1716867
  · exact B1716871
  · exact B1716875
  · exact B1716879
  · exact B1716883
  · exact B1716887
  · exact B1716891
  · exact B1716895
  · exact B1716899
  · exact B1716903
  · exact B1716907
  · exact B1716911
  · exact B1716915
  · exact B1716919
  · exact B1716923
  · exact B1716927
  · exact B1716931
  · exact B1716935
  · exact B1716939
  · exact B1716943
  · exact B1716947
  · exact B1716951
  · exact B1716955
  · exact B1716959
  · exact B1716963
  · exact B1716967
  · exact B1716971
  · exact B1716975
  · exact B1716979
  · exact B1716983
  · exact B1716987
  · exact B1716991
  · exact B1716995
  · exact B1716999
  · exact B1717003
  · exact B1717007
  · exact B1717011
  · exact B1717015
  · exact B1717019
  · exact B1717023
  · exact B1717027
  · exact B1717031
  · exact B1717035
  · exact B1717039
  · exact B1717043
  · exact B1717047
  · exact B1717051
  · exact B1717055

theorem solution (m : ℕ) (hlo : 1715058 ≤ m) (hhi : m ≤ 1717058) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 428764 ≤ j := by omega
    have hj2 : j ≤ 429263 := by omega
    have hb : Blo 1715058 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
