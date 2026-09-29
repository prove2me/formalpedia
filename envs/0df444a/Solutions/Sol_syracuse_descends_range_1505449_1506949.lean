-- Prove2me | solution 1 for syracuse_descends_range_1505449_1506949
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:03.217471+00:00
-- url     : https://prove2.me/submissions/bb39a07e-0ff5-4cd6-8a6a-38437f52187c

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


theorem B2859077 : Blo 1505449 2859077 := bbase (se 4 (by rfl) ⟨268038, by rfl⟩ : syracuseStep 2859077 = 536077) (by norm_num)
theorem B2859229 : Blo 1505449 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B3531005 : Blo 1505449 3531005 := bbase (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) (by norm_num)
theorem B4071701 : Blo 1505449 4071701 := bbase (se 6 (by rfl) ⟨95430, by rfl⟩ : syracuseStep 4071701 = 190861) (by norm_num)
theorem B2859533 : Blo 1505449 2859533 := bbase (se 3 (by rfl) ⟨536162, by rfl⟩ : syracuseStep 2859533 = 1072325) (by norm_num)
theorem B4072069 : Blo 1505449 4072069 := bbase (se 4 (by rfl) ⟨381756, by rfl⟩ : syracuseStep 4072069 = 763513) (by norm_num)
theorem B7627445 : Blo 1505449 7627445 := bbase (se 5 (by rfl) ⟨357536, by rfl⟩ : syracuseStep 7627445 = 715073) (by norm_num)
theorem B4072133 : Blo 1505449 4072133 := bbase (se 4 (by rfl) ⟨381762, by rfl⟩ : syracuseStep 4072133 = 763525) (by norm_num)
theorem B3261197 : Blo 1505449 3261197 := bbase (se 3 (by rfl) ⟨611474, by rfl⟩ : syracuseStep 3261197 = 1222949) (by norm_num)
theorem B6431557 : Blo 1505449 6431557 := bbase (se 4 (by rfl) ⟨602958, by rfl⟩ : syracuseStep 6431557 = 1205917) (by norm_num)
theorem B5718869 : Blo 1505449 5718869 := bbase (se 9 (by rfl) ⟨16754, by rfl⟩ : syracuseStep 5718869 = 33509) (by norm_num)
theorem B2540477 : Blo 1505449 2540477 := bbase (se 3 (by rfl) ⟨476339, by rfl⟩ : syracuseStep 2540477 = 952679) (by norm_num)
theorem B4826117 : Blo 1505449 4826117 := bbase (se 4 (by rfl) ⟨452448, by rfl⟩ : syracuseStep 4826117 = 904897) (by norm_num)
theorem B2540605 : Blo 1505449 2540605 := bbase (se 3 (by rfl) ⟨476363, by rfl⟩ : syracuseStep 2540605 = 952727) (by norm_num)
theorem B3433565 : Blo 1505449 3433565 := bbase (se 3 (by rfl) ⟨643793, by rfl⟩ : syracuseStep 3433565 = 1287587) (by norm_num)
theorem B5719157 : Blo 1505449 5719157 := bbase (se 5 (by rfl) ⟨268085, by rfl⟩ : syracuseStep 5719157 = 536171) (by norm_num)
theorem B2540693 : Blo 1505449 2540693 := bbase (se 6 (by rfl) ⟨59547, by rfl⟩ : syracuseStep 2540693 = 119095) (by norm_num)
theorem B3433637 : Blo 1505449 3433637 := bbase (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) (by norm_num)
theorem B9651413 : Blo 1505449 9651413 := bbase (se 7 (by rfl) ⟨113102, by rfl⟩ : syracuseStep 9651413 = 226205) (by norm_num)
theorem B2860285 : Blo 1505449 2860285 := bbase (se 3 (by rfl) ⟨536303, by rfl⟩ : syracuseStep 2860285 = 1072607) (by norm_num)
theorem B2540821 : Blo 1505449 2540821 := bbase (se 6 (by rfl) ⟨59550, by rfl⟩ : syracuseStep 2540821 = 119101) (by norm_num)
theorem B8578325 : Blo 1505449 8578325 := bbase (se 6 (by rfl) ⟨201054, by rfl⟩ : syracuseStep 8578325 = 402109) (by norm_num)
theorem B2540909 : Blo 1505449 2540909 := bbase (se 3 (by rfl) ⟨476420, by rfl⟩ : syracuseStep 2540909 = 952841) (by norm_num)
theorem B3810685 : Blo 1505449 3810685 := bbase (se 3 (by rfl) ⟨714503, by rfl⟩ : syracuseStep 3810685 = 1429007) (by norm_num)
theorem B2860429 : Blo 1505449 2860429 := bbase (se 3 (by rfl) ⟨536330, by rfl⟩ : syracuseStep 2860429 = 1072661) (by norm_num)
theorem B3810797 : Blo 1505449 3810797 := bbase (se 3 (by rfl) ⟨714524, by rfl⟩ : syracuseStep 3810797 = 1429049) (by norm_num)
theorem B2541037 : Blo 1505449 2541037 := bbase (se 3 (by rfl) ⟨476444, by rfl⟩ : syracuseStep 2541037 = 952889) (by norm_num)
theorem B2860589 : Blo 1505449 2860589 := bbase (se 3 (by rfl) ⟨536360, by rfl⟩ : syracuseStep 2860589 = 1072721) (by norm_num)
theorem B2541125 : Blo 1505449 2541125 := bbase (se 4 (by rfl) ⟨238230, by rfl⟩ : syracuseStep 2541125 = 476461) (by norm_num)
theorem B2713213 : Blo 1505449 2713213 := bbase (se 3 (by rfl) ⟨508727, by rfl⟩ : syracuseStep 2713213 = 1017455) (by norm_num)
theorem B3810989 : Blo 1505449 3810989 := bbase (se 3 (by rfl) ⟨714560, by rfl⟩ : syracuseStep 3810989 = 1429121) (by norm_num)
theorem B2860733 : Blo 1505449 2860733 := bbase (se 3 (by rfl) ⟨536387, by rfl⟩ : syracuseStep 2860733 = 1072775) (by norm_num)
theorem B2541253 : Blo 1505449 2541253 := bbase (se 4 (by rfl) ⟨238242, by rfl⟩ : syracuseStep 2541253 = 476485) (by norm_num)
theorem B2541341 : Blo 1505449 2541341 := bbase (se 3 (by rfl) ⟨476501, by rfl⟩ : syracuseStep 2541341 = 953003) (by norm_num)
theorem B2713429 : Blo 1505449 2713429 := bbase (se 9 (by rfl) ⟨7949, by rfl⟩ : syracuseStep 2713429 = 15899) (by norm_num)
theorem B2541469 : Blo 1505449 2541469 := bbase (se 3 (by rfl) ⟨476525, by rfl⟩ : syracuseStep 2541469 = 953051) (by norm_num)
theorem B7628741 : Blo 1505449 7628741 := bbase (se 4 (by rfl) ⟨715194, by rfl⟩ : syracuseStep 7628741 = 1430389) (by norm_num)
theorem B2541557 : Blo 1505449 2541557 := bbase (se 5 (by rfl) ⟨119135, by rfl⟩ : syracuseStep 2541557 = 238271) (by norm_num)
theorem B3811333 : Blo 1505449 3811333 := bbase (se 4 (by rfl) ⟨357312, by rfl⟩ : syracuseStep 3811333 = 714625) (by norm_num)
theorem B1607693 : Blo 1505449 1607693 := bbase (se 3 (by rfl) ⟨301442, by rfl⟩ : syracuseStep 1607693 = 602885) (by norm_num)
theorem B4827205 : Blo 1505449 4827205 := bbase (se 4 (by rfl) ⟨452550, by rfl⟩ : syracuseStep 4827205 = 905101) (by norm_num)
theorem B3917917 : Blo 1505449 3917917 := bbase (se 3 (by rfl) ⟨734609, by rfl⟩ : syracuseStep 3917917 = 1469219) (by norm_num)
theorem B3811445 : Blo 1505449 3811445 := bbase (se 5 (by rfl) ⟨178661, by rfl⟩ : syracuseStep 3811445 = 357323) (by norm_num)
theorem B2713717 : Blo 1505449 2713717 := bbase (se 5 (by rfl) ⟨127205, by rfl⟩ : syracuseStep 2713717 = 254411) (by norm_num)
theorem B2541685 : Blo 1505449 2541685 := bbase (se 5 (by rfl) ⟨119141, by rfl⟩ : syracuseStep 2541685 = 238283) (by norm_num)
theorem B5081237 : Blo 1505449 5081237 := bbase (se 6 (by rfl) ⟨119091, by rfl⟩ : syracuseStep 5081237 = 238183) (by norm_num)
theorem B2541773 : Blo 1505449 2541773 := bbase (se 3 (by rfl) ⟨476582, by rfl⟩ : syracuseStep 2541773 = 953165) (by norm_num)
theorem B1607941 : Blo 1505449 1607941 := bbase (se 4 (by rfl) ⟨150744, by rfl⟩ : syracuseStep 1607941 = 301489) (by norm_num)
theorem B5720341 : Blo 1505449 5720341 := bbase (se 6 (by rfl) ⟨134070, by rfl⟩ : syracuseStep 5720341 = 268141) (by norm_num)
theorem B1526045 : Blo 1505449 1526045 := bbase (se 3 (by rfl) ⟨286133, by rfl⟩ : syracuseStep 1526045 = 572267) (by norm_num)
theorem B3811637 : Blo 1505449 3811637 := bbase (se 5 (by rfl) ⟨178670, by rfl⟩ : syracuseStep 3811637 = 357341) (by norm_num)
theorem B1526077 : Blo 1505449 1526077 := bbase (se 3 (by rfl) ⟨286139, by rfl⟩ : syracuseStep 1526077 = 572279) (by norm_num)
theorem B2541901 : Blo 1505449 2541901 := bbase (se 3 (by rfl) ⟨476606, by rfl⟩ : syracuseStep 2541901 = 953213) (by norm_num)
theorem B2541989 : Blo 1505449 2541989 := bbase (se 4 (by rfl) ⟨238311, by rfl⟩ : syracuseStep 2541989 = 476623) (by norm_num)
theorem B1907165 : Blo 1505449 1907165 := bbase (se 3 (by rfl) ⟨357593, by rfl⟩ : syracuseStep 1907165 = 715187) (by norm_num)
theorem B2542117 : Blo 1505449 2542117 := bbase (se 4 (by rfl) ⟨238323, by rfl⟩ : syracuseStep 2542117 = 476647) (by norm_num)
theorem B5081669 : Blo 1505449 5081669 := bbase (se 4 (by rfl) ⟨476406, by rfl⟩ : syracuseStep 5081669 = 952813) (by norm_num)
theorem B5720645 : Blo 1505449 5720645 := bbase (se 4 (by rfl) ⟨536310, by rfl⟩ : syracuseStep 5720645 = 1072621) (by norm_num)
theorem B2542205 : Blo 1505449 2542205 := bbase (se 3 (by rfl) ⟨476663, by rfl⟩ : syracuseStep 2542205 = 953327) (by norm_num)
theorem B3811981 : Blo 1505449 3811981 := bbase (se 3 (by rfl) ⟨714746, by rfl⟩ : syracuseStep 3811981 = 1429493) (by norm_num)
theorem B6965909 : Blo 1505449 6965909 := bbase (se 6 (by rfl) ⟨163263, by rfl⟩ : syracuseStep 6965909 = 326527) (by norm_num)
theorem B1608385 : Blo 1505449 1608385 := bbase (se 2 (by rfl) ⟨603144, by rfl⟩ : syracuseStep 1608385 = 1206289) (by norm_num)
theorem B3812093 : Blo 1505449 3812093 := bbase (se 3 (by rfl) ⟨714767, by rfl⟩ : syracuseStep 3812093 = 1429535) (by norm_num)
theorem B1608445 : Blo 1505449 1608445 := bbase (se 3 (by rfl) ⟨301583, by rfl⟩ : syracuseStep 1608445 = 603167) (by norm_num)
theorem B2542333 : Blo 1505449 2542333 := bbase (se 3 (by rfl) ⟨476687, by rfl⟩ : syracuseStep 2542333 = 953375) (by norm_num)
theorem B2714381 : Blo 1505449 2714381 := bbase (se 3 (by rfl) ⟨508946, by rfl⟩ : syracuseStep 2714381 = 1017893) (by norm_num)
theorem B9161525 : Blo 1505449 9161525 := bbase (se 5 (by rfl) ⟨429446, by rfl⟩ : syracuseStep 9161525 = 858893) (by norm_num)
theorem B2542421 : Blo 1505449 2542421 := bbase (se 9 (by rfl) ⟨7448, by rfl⟩ : syracuseStep 2542421 = 14897) (by norm_num)
theorem B1764229 : Blo 1505449 1764229 := bbase (se 4 (by rfl) ⟨165396, by rfl⟩ : syracuseStep 1764229 = 330793) (by norm_num)
theorem B3812285 : Blo 1505449 3812285 := bbase (se 3 (by rfl) ⟨714803, by rfl⟩ : syracuseStep 3812285 = 1429607) (by norm_num)
theorem B2542549 : Blo 1505449 2542549 := bbase (se 7 (by rfl) ⟨29795, by rfl⟩ : syracuseStep 2542549 = 59591) (by norm_num)
theorem B5082101 : Blo 1505449 5082101 := bbase (se 5 (by rfl) ⟨238223, by rfl⟩ : syracuseStep 5082101 = 476447) (by norm_num)
theorem B2542637 : Blo 1505449 2542637 := bbase (se 3 (by rfl) ⟨476744, by rfl⟩ : syracuseStep 2542637 = 953489) (by norm_num)
theorem B1608761 : Blo 1505449 1608761 := bbase (se 2 (by rfl) ⟨603285, by rfl⟩ : syracuseStep 1608761 = 1206571) (by norm_num)
theorem B7236773 : Blo 1505449 7236773 := bbase (se 4 (by rfl) ⟨678447, by rfl⟩ : syracuseStep 7236773 = 1356895) (by norm_num)
theorem B2542765 : Blo 1505449 2542765 := bbase (se 3 (by rfl) ⟨476768, by rfl⟩ : syracuseStep 2542765 = 953537) (by norm_num)
theorem B1526969 : Blo 1505449 1526969 := bbase (se 2 (by rfl) ⟨572613, by rfl⟩ : syracuseStep 1526969 = 1145227) (by norm_num)
theorem B3181765 : Blo 1505449 3181765 := bbase (se 4 (by rfl) ⟨298290, by rfl⟩ : syracuseStep 3181765 = 596581) (by norm_num)
theorem B2542853 : Blo 1505449 2542853 := bbase (se 4 (by rfl) ⟨238392, by rfl⟩ : syracuseStep 2542853 = 476785) (by norm_num)
theorem B3812629 : Blo 1505449 3812629 := bbase (se 6 (by rfl) ⟨89358, by rfl⟩ : syracuseStep 3812629 = 178717) (by norm_num)
theorem B7236965 : Blo 1505449 7236965 := bbase (se 4 (by rfl) ⟨678465, by rfl⟩ : syracuseStep 7236965 = 1356931) (by norm_num)
theorem B3812741 : Blo 1505449 3812741 := bbase (se 4 (by rfl) ⟨357444, by rfl⟩ : syracuseStep 3812741 = 714889) (by norm_num)
theorem B5082533 : Blo 1505449 5082533 := bbase (se 4 (by rfl) ⟨476487, by rfl⟩ : syracuseStep 5082533 = 952975) (by norm_num)
theorem B1609205 : Blo 1505449 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B4288069 : Blo 1505449 4288069 := bbase (se 4 (by rfl) ⟨402006, by rfl⟩ : syracuseStep 4288069 = 804013) (by norm_num)
theorem B3812933 : Blo 1505449 3812933 := bbase (se 4 (by rfl) ⟨357462, by rfl⟩ : syracuseStep 3812933 = 714925) (by norm_num)
theorem B7622261 : Blo 1505449 7622261 := bbase (se 5 (by rfl) ⟨357293, by rfl⟩ : syracuseStep 7622261 = 714587) (by norm_num)
theorem B4181701 : Blo 1505449 4181701 := bbase (se 4 (by rfl) ⟨392034, by rfl⟩ : syracuseStep 4181701 = 784069) (by norm_num)
theorem B7237349 : Blo 1505449 7237349 := bbase (se 4 (by rfl) ⟨678501, by rfl⟩ : syracuseStep 7237349 = 1357003) (by norm_num)
theorem B5590757 : Blo 1505449 5590757 := bbase (se 4 (by rfl) ⟨524133, by rfl⟩ : syracuseStep 5590757 = 1048267) (by norm_num)
theorem B6434549 : Blo 1505449 6434549 := bbase (se 5 (by rfl) ⟨301619, by rfl⟩ : syracuseStep 6434549 = 603239) (by norm_num)
theorem B3436301 : Blo 1505449 3436301 := bbase (se 3 (by rfl) ⟨644306, by rfl⟩ : syracuseStep 3436301 = 1288613) (by norm_num)
theorem B12865301 : Blo 1505449 12865301 := bbase (se 6 (by rfl) ⟨301530, by rfl⟩ : syracuseStep 12865301 = 603061) (by norm_num)
theorem B5082965 : Blo 1505449 5082965 := bbase (se 9 (by rfl) ⟨14891, by rfl⟩ : syracuseStep 5082965 = 29783) (by norm_num)
theorem B3387293 : Blo 1505449 3387293 := bbase (se 3 (by rfl) ⟨635117, by rfl⟩ : syracuseStep 3387293 = 1270235) (by norm_num)
theorem B3813277 : Blo 1505449 3813277 := bbase (se 3 (by rfl) ⟨714989, by rfl⟩ : syracuseStep 3813277 = 1429979) (by norm_num)
theorem B3387365 : Blo 1505449 3387365 := bbase (se 4 (by rfl) ⟨317565, by rfl⟩ : syracuseStep 3387365 = 635131) (by norm_num)
theorem B3813389 : Blo 1505449 3813389 := bbase (se 3 (by rfl) ⟨715010, by rfl⟩ : syracuseStep 3813389 = 1430021) (by norm_num)
theorem B3387437 : Blo 1505449 3387437 := bbase (se 3 (by rfl) ⟨635144, by rfl⟩ : syracuseStep 3387437 = 1270289) (by norm_num)
theorem B3387509 : Blo 1505449 3387509 := bbase (se 5 (by rfl) ⟨158789, by rfl⟩ : syracuseStep 3387509 = 317579) (by norm_num)
theorem B2289797 : Blo 1505449 2289797 := bbase (se 4 (by rfl) ⟨214668, by rfl⟩ : syracuseStep 2289797 = 429337) (by norm_num)
theorem B3969181 : Blo 1505449 3969181 := bbase (se 3 (by rfl) ⟨744221, by rfl⟩ : syracuseStep 3969181 = 1488443) (by norm_num)
theorem B3387581 : Blo 1505449 3387581 := bbase (se 3 (by rfl) ⟨635171, by rfl⟩ : syracuseStep 3387581 = 1270343) (by norm_num)
theorem B3813581 : Blo 1505449 3813581 := bbase (se 3 (by rfl) ⟨715046, by rfl⟩ : syracuseStep 3813581 = 1430093) (by norm_num)
theorem B2412757 : Blo 1505449 2412757 := bbase (se 7 (by rfl) ⟨28274, by rfl⟩ : syracuseStep 2412757 = 56549) (by norm_num)
theorem B3387653 : Blo 1505449 3387653 := bbase (se 4 (by rfl) ⟨317592, by rfl⟩ : syracuseStep 3387653 = 635185) (by norm_num)
theorem B5083397 : Blo 1505449 5083397 := bbase (se 4 (by rfl) ⟨476568, by rfl⟩ : syracuseStep 5083397 = 953137) (by norm_num)
theorem B3387725 : Blo 1505449 3387725 := bbase (se 3 (by rfl) ⟨635198, by rfl⟩ : syracuseStep 3387725 = 1270397) (by norm_num)
theorem B3387797 : Blo 1505449 3387797 := bbase (se 6 (by rfl) ⟨79401, by rfl⟩ : syracuseStep 3387797 = 158803) (by norm_num)
theorem B3387869 : Blo 1505449 3387869 := bbase (se 3 (by rfl) ⟨635225, by rfl⟩ : syracuseStep 3387869 = 1270451) (by norm_num)
theorem B16282133 : Blo 1505449 16282133 := bbase (se 6 (by rfl) ⟨381612, by rfl⟩ : syracuseStep 16282133 = 763225) (by norm_num)
theorem B3863069 : Blo 1505449 3863069 := bbase (se 3 (by rfl) ⟨724325, by rfl⟩ : syracuseStep 3863069 = 1448651) (by norm_num)
theorem B3387941 : Blo 1505449 3387941 := bbase (se 4 (by rfl) ⟨317619, by rfl⟩ : syracuseStep 3387941 = 635239) (by norm_num)
theorem B3813925 : Blo 1505449 3813925 := bbase (se 4 (by rfl) ⟨357555, by rfl⟩ : syracuseStep 3813925 = 715111) (by norm_num)
theorem B3215933 : Blo 1505449 3215933 := bbase (se 3 (by rfl) ⟨602987, by rfl⟩ : syracuseStep 3215933 = 1205975) (by norm_num)
theorem B1716833 : Blo 1505449 1716833 := bbase (se 2 (by rfl) ⟨643812, by rfl⟩ : syracuseStep 1716833 = 1287625) (by norm_num)
theorem B3388013 : Blo 1505449 3388013 := bbase (se 3 (by rfl) ⟨635252, by rfl⟩ : syracuseStep 3388013 = 1270505) (by norm_num)
theorem B3814037 : Blo 1505449 3814037 := bbase (se 6 (by rfl) ⟨89391, by rfl⟩ : syracuseStep 3814037 = 178783) (by norm_num)
theorem B3388085 : Blo 1505449 3388085 := bbase (se 5 (by rfl) ⟨158816, by rfl⟩ : syracuseStep 3388085 = 317633) (by norm_num)
theorem B5083829 : Blo 1505449 5083829 := bbase (se 5 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 5083829 = 476609) (by norm_num)
theorem B1905373 : Blo 1505449 1905373 := bbase (se 3 (by rfl) ⟨357257, by rfl⟩ : syracuseStep 1905373 = 714515) (by norm_num)
theorem B6435557 : Blo 1505449 6435557 := bbase (se 4 (by rfl) ⟨603333, by rfl⟩ : syracuseStep 6435557 = 1206667) (by norm_num)
theorem B3863285 : Blo 1505449 3863285 := bbase (se 5 (by rfl) ⟨181091, by rfl⟩ : syracuseStep 3863285 = 362183) (by norm_num)
theorem B3388157 : Blo 1505449 3388157 := bbase (se 3 (by rfl) ⟨635279, by rfl⟩ : syracuseStep 3388157 = 1270559) (by norm_num)
theorem B3216181 : Blo 1505449 3216181 := bbase (se 5 (by rfl) ⟨150758, by rfl⟩ : syracuseStep 3216181 = 301517) (by norm_num)
theorem B3388229 : Blo 1505449 3388229 := bbase (se 4 (by rfl) ⟨317646, by rfl⟩ : syracuseStep 3388229 = 635293) (by norm_num)
theorem B3814229 : Blo 1505449 3814229 := bbase (se 9 (by rfl) ⟨11174, by rfl⟩ : syracuseStep 3814229 = 22349) (by norm_num)
theorem B7623557 : Blo 1505449 7623557 := bbase (se 4 (by rfl) ⟨714708, by rfl⟩ : syracuseStep 7623557 = 1429417) (by norm_num)
theorem B1905545 : Blo 1505449 1905545 := bbase (se 2 (by rfl) ⟨714579, by rfl⟩ : syracuseStep 1905545 = 1429159) (by norm_num)
theorem B3388301 : Blo 1505449 3388301 := bbase (se 3 (by rfl) ⟨635306, by rfl⟩ : syracuseStep 3388301 = 1270613) (by norm_num)
theorem B2413469 : Blo 1505449 2413469 := bbase (se 3 (by rfl) ⟨452525, by rfl⟩ : syracuseStep 2413469 = 905051) (by norm_num)
theorem B14480309 : Blo 1505449 14480309 := bbase (se 5 (by rfl) ⟨678764, by rfl⟩ : syracuseStep 14480309 = 1357529) (by norm_num)
theorem B1905601 : Blo 1505449 1905601 := bbase (se 2 (by rfl) ⟨714600, by rfl⟩ : syracuseStep 1905601 = 1429201) (by norm_num)
theorem B3388373 : Blo 1505449 3388373 := bbase (se 7 (by rfl) ⟨39707, by rfl⟩ : syracuseStep 3388373 = 79415) (by norm_num)
theorem B10187797 : Blo 1505449 10187797 := bbase (se 6 (by rfl) ⟨238776, by rfl⟩ : syracuseStep 10187797 = 477553) (by norm_num)
theorem B3388445 : Blo 1505449 3388445 := bbase (se 3 (by rfl) ⟨635333, by rfl⟩ : syracuseStep 3388445 = 1270667) (by norm_num)
theorem B1905697 : Blo 1505449 1905697 := bbase (se 2 (by rfl) ⟨714636, by rfl⟩ : syracuseStep 1905697 = 1429273) (by norm_num)
theorem B4289573 : Blo 1505449 4289573 := bbase (se 4 (by rfl) ⟨402147, by rfl⟩ : syracuseStep 4289573 = 804295) (by norm_num)
theorem B3388517 : Blo 1505449 3388517 := bbase (se 4 (by rfl) ⟨317673, by rfl⟩ : syracuseStep 3388517 = 635347) (by norm_num)
theorem B5084261 : Blo 1505449 5084261 := bbase (se 4 (by rfl) ⟨476649, by rfl⟩ : syracuseStep 5084261 = 953299) (by norm_num)
theorem B1717393 : Blo 1505449 1717393 := bbase (se 2 (by rfl) ⟨644022, by rfl⟩ : syracuseStep 1717393 = 1288045) (by norm_num)
theorem B3388589 : Blo 1505449 3388589 := bbase (se 3 (by rfl) ⟨635360, by rfl⟩ : syracuseStep 3388589 = 1270721) (by norm_num)
theorem B8574133 : Blo 1505449 8574133 := bbase (se 5 (by rfl) ⟨401912, by rfl⟩ : syracuseStep 8574133 = 803825) (by norm_num)
theorem B1905869 : Blo 1505449 1905869 := bbase (se 3 (by rfl) ⟨357350, by rfl⟩ : syracuseStep 1905869 = 714701) (by norm_num)
theorem B1717453 : Blo 1505449 1717453 := bbase (se 3 (by rfl) ⟨322022, by rfl⟩ : syracuseStep 1717453 = 644045) (by norm_num)
theorem B3388661 : Blo 1505449 3388661 := bbase (se 5 (by rfl) ⟨158843, by rfl⟩ : syracuseStep 3388661 = 317687) (by norm_num)
theorem B1905925 : Blo 1505449 1905925 := bbase (se 4 (by rfl) ⟨178680, by rfl⟩ : syracuseStep 1905925 = 357361) (by norm_num)
theorem B2258189 : Blo 1505449 2258189 := bbase (se 3 (by rfl) ⟨423410, by rfl⟩ : syracuseStep 2258189 = 846821) (by norm_num)
theorem B2258213 : Blo 1505449 2258213 := bbase (se 4 (by rfl) ⟨211707, by rfl⟩ : syracuseStep 2258213 = 423415) (by norm_num)
theorem B3216685 : Blo 1505449 3216685 := bbase (se 3 (by rfl) ⟨603128, by rfl⟩ : syracuseStep 3216685 = 1206257) (by norm_num)
theorem B2258237 : Blo 1505449 2258237 := bbase (se 3 (by rfl) ⟨423419, by rfl⟩ : syracuseStep 2258237 = 846839) (by norm_num)
theorem B3388733 : Blo 1505449 3388733 := bbase (se 3 (by rfl) ⟨635387, by rfl⟩ : syracuseStep 3388733 = 1270775) (by norm_num)
theorem B2938189 : Blo 1505449 2938189 := bbase (se 3 (by rfl) ⟨550910, by rfl⟩ : syracuseStep 2938189 = 1101821) (by norm_num)
theorem B2258261 : Blo 1505449 2258261 := bbase (se 13 (by rfl) ⟨413, by rfl⟩ : syracuseStep 2258261 = 827) (by norm_num)
theorem B3052885 : Blo 1505449 3052885 := bbase (se 14 (by rfl) ⟨279, by rfl⟩ : syracuseStep 3052885 = 559) (by norm_num)
theorem B1906021 : Blo 1505449 1906021 := bbase (se 4 (by rfl) ⟨178689, by rfl⟩ : syracuseStep 1906021 = 357379) (by norm_num)
theorem B2258285 : Blo 1505449 2258285 := bbase (se 3 (by rfl) ⟨423428, by rfl⟩ : syracuseStep 2258285 = 846857) (by norm_num)
theorem B2258309 : Blo 1505449 2258309 := bbase (se 4 (by rfl) ⟨211716, by rfl⟩ : syracuseStep 2258309 = 423433) (by norm_num)
theorem B3388805 : Blo 1505449 3388805 := bbase (se 4 (by rfl) ⟨317700, by rfl⟩ : syracuseStep 3388805 = 635401) (by norm_num)
theorem B2258333 : Blo 1505449 2258333 := bbase (se 3 (by rfl) ⟨423437, by rfl⟩ : syracuseStep 2258333 = 846875) (by norm_num)
theorem B2258357 : Blo 1505449 2258357 := bbase (se 5 (by rfl) ⟨105860, by rfl⟩ : syracuseStep 2258357 = 211721) (by norm_num)
theorem B2143693 : Blo 1505449 2143693 := bbase (se 3 (by rfl) ⟨401942, by rfl⟩ : syracuseStep 2143693 = 803885) (by norm_num)
theorem B2258381 : Blo 1505449 2258381 := bbase (se 3 (by rfl) ⟨423446, by rfl⟩ : syracuseStep 2258381 = 846893) (by norm_num)
theorem B3388877 : Blo 1505449 3388877 := bbase (se 3 (by rfl) ⟨635414, by rfl⟩ : syracuseStep 3388877 = 1270829) (by norm_num)
theorem B2258405 : Blo 1505449 2258405 := bbase (se 4 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 2258405 = 423451) (by norm_num)
theorem B2258429 : Blo 1505449 2258429 := bbase (se 3 (by rfl) ⟨423455, by rfl⟩ : syracuseStep 2258429 = 846911) (by norm_num)
theorem B1906193 : Blo 1505449 1906193 := bbase (se 2 (by rfl) ⟨714822, by rfl⟩ : syracuseStep 1906193 = 1429645) (by norm_num)
theorem B2258453 : Blo 1505449 2258453 := bbase (se 6 (by rfl) ⟨52932, by rfl⟩ : syracuseStep 2258453 = 105865) (by norm_num)
theorem B3388949 : Blo 1505449 3388949 := bbase (se 6 (by rfl) ⟨79428, by rfl⟩ : syracuseStep 3388949 = 158857) (by norm_num)
theorem B5084693 : Blo 1505449 5084693 := bbase (se 6 (by rfl) ⟨119172, by rfl⟩ : syracuseStep 5084693 = 238345) (by norm_num)
theorem B2258477 : Blo 1505449 2258477 := bbase (se 3 (by rfl) ⟨423464, by rfl⟩ : syracuseStep 2258477 = 846929) (by norm_num)
theorem B2258501 : Blo 1505449 2258501 := bbase (se 4 (by rfl) ⟨211734, by rfl⟩ : syracuseStep 2258501 = 423469) (by norm_num)
theorem B1906249 : Blo 1505449 1906249 := bbase (se 2 (by rfl) ⟨714843, by rfl⟩ : syracuseStep 1906249 = 1429687) (by norm_num)
theorem B2258525 : Blo 1505449 2258525 := bbase (se 3 (by rfl) ⟨423473, by rfl⟩ : syracuseStep 2258525 = 846947) (by norm_num)
theorem B3389021 : Blo 1505449 3389021 := bbase (se 3 (by rfl) ⟨635441, by rfl⟩ : syracuseStep 3389021 = 1270883) (by norm_num)
theorem B2258549 : Blo 1505449 2258549 := bbase (se 5 (by rfl) ⟨105869, by rfl⟩ : syracuseStep 2258549 = 211739) (by norm_num)
theorem B2258573 : Blo 1505449 2258573 := bbase (se 3 (by rfl) ⟨423482, by rfl⟩ : syracuseStep 2258573 = 846965) (by norm_num)
theorem B2258597 : Blo 1505449 2258597 := bbase (se 4 (by rfl) ⟨211743, by rfl⟩ : syracuseStep 2258597 = 423487) (by norm_num)
theorem B3389093 : Blo 1505449 3389093 := bbase (se 4 (by rfl) ⟨317727, by rfl⟩ : syracuseStep 3389093 = 635455) (by norm_num)
theorem B1906345 : Blo 1505449 1906345 := bbase (se 2 (by rfl) ⟨714879, by rfl⟩ : syracuseStep 1906345 = 1429759) (by norm_num)
theorem B2258621 : Blo 1505449 2258621 := bbase (se 3 (by rfl) ⟨423491, by rfl⟩ : syracuseStep 2258621 = 846983) (by norm_num)
theorem B2258645 : Blo 1505449 2258645 := bbase (se 7 (by rfl) ⟨26468, by rfl⟩ : syracuseStep 2258645 = 52937) (by norm_num)
theorem B4126421 : Blo 1505449 4126421 := bbase (se 7 (by rfl) ⟨48356, by rfl⟩ : syracuseStep 4126421 = 96713) (by norm_num)
theorem B2258669 : Blo 1505449 2258669 := bbase (se 3 (by rfl) ⟨423500, by rfl⟩ : syracuseStep 2258669 = 847001) (by norm_num)
theorem B3389165 : Blo 1505449 3389165 := bbase (se 3 (by rfl) ⟨635468, by rfl⟩ : syracuseStep 3389165 = 1270937) (by norm_num)
theorem B2258693 : Blo 1505449 2258693 := bbase (se 4 (by rfl) ⟨211752, by rfl⟩ : syracuseStep 2258693 = 423505) (by norm_num)
theorem B2258717 : Blo 1505449 2258717 := bbase (se 3 (by rfl) ⟨423509, by rfl⟩ : syracuseStep 2258717 = 847019) (by norm_num)
theorem B3618589 : Blo 1505449 3618589 := bbase (se 3 (by rfl) ⟨678485, by rfl⟩ : syracuseStep 3618589 = 1356971) (by norm_num)
theorem B2258741 : Blo 1505449 2258741 := bbase (se 5 (by rfl) ⟨105878, by rfl⟩ : syracuseStep 2258741 = 211757) (by norm_num)
theorem B3389237 : Blo 1505449 3389237 := bbase (se 5 (by rfl) ⟨158870, by rfl⟩ : syracuseStep 3389237 = 317741) (by norm_num)
theorem B2258765 : Blo 1505449 2258765 := bbase (se 3 (by rfl) ⟨423518, by rfl⟩ : syracuseStep 2258765 = 847037) (by norm_num)
theorem B1906517 : Blo 1505449 1906517 := bbase (se 9 (by rfl) ⟨5585, by rfl⟩ : syracuseStep 1906517 = 11171) (by norm_num)
theorem B2258789 : Blo 1505449 2258789 := bbase (se 4 (by rfl) ⟨211761, by rfl⟩ : syracuseStep 2258789 = 423523) (by norm_num)
theorem B2258813 : Blo 1505449 2258813 := bbase (se 3 (by rfl) ⟨423527, by rfl⟩ : syracuseStep 2258813 = 847055) (by norm_num)
theorem B3389309 : Blo 1505449 3389309 := bbase (se 3 (by rfl) ⟨635495, by rfl⟩ : syracuseStep 3389309 = 1270991) (by norm_num)
theorem B1906573 : Blo 1505449 1906573 := bbase (se 3 (by rfl) ⟨357482, by rfl⟩ : syracuseStep 1906573 = 714965) (by norm_num)
theorem B2258837 : Blo 1505449 2258837 := bbase (se 6 (by rfl) ⟨52941, by rfl⟩ : syracuseStep 2258837 = 105883) (by norm_num)
theorem B3528605 : Blo 1505449 3528605 := bbase (se 3 (by rfl) ⟨661613, by rfl⟩ : syracuseStep 3528605 = 1323227) (by norm_num)
theorem B2258861 : Blo 1505449 2258861 := bbase (se 3 (by rfl) ⟨423536, by rfl⟩ : syracuseStep 2258861 = 847073) (by norm_num)
theorem B1693633 : Blo 1505449 1693633 := bbase (se 2 (by rfl) ⟨635112, by rfl⟩ : syracuseStep 1693633 = 1270225) (by norm_num)
theorem B2258885 : Blo 1505449 2258885 := bbase (se 4 (by rfl) ⟨211770, by rfl⟩ : syracuseStep 2258885 = 423541) (by norm_num)
theorem B3389381 : Blo 1505449 3389381 := bbase (se 4 (by rfl) ⟨317754, by rfl⟩ : syracuseStep 3389381 = 635509) (by norm_num)
theorem B5085125 : Blo 1505449 5085125 := bbase (se 4 (by rfl) ⟨476730, by rfl⟩ : syracuseStep 5085125 = 953461) (by norm_num)
theorem B2258909 : Blo 1505449 2258909 := bbase (se 3 (by rfl) ⟨423545, by rfl⟩ : syracuseStep 2258909 = 847091) (by norm_num)
theorem B1693669 : Blo 1505449 1693669 := bbase (se 4 (by rfl) ⟨158781, by rfl⟩ : syracuseStep 1693669 = 317563) (by norm_num)
theorem B1906669 : Blo 1505449 1906669 := bbase (se 3 (by rfl) ⟨357500, by rfl⟩ : syracuseStep 1906669 = 715001) (by norm_num)
theorem B2258933 : Blo 1505449 2258933 := bbase (se 5 (by rfl) ⟨105887, by rfl⟩ : syracuseStep 2258933 = 211775) (by norm_num)
theorem B1693705 : Blo 1505449 1693705 := bbase (se 2 (by rfl) ⟨635139, by rfl⟩ : syracuseStep 1693705 = 1270279) (by norm_num)
theorem B2258957 : Blo 1505449 2258957 := bbase (se 3 (by rfl) ⟨423554, by rfl⟩ : syracuseStep 2258957 = 847109) (by norm_num)
theorem B3389453 : Blo 1505449 3389453 := bbase (se 3 (by rfl) ⟨635522, by rfl⟩ : syracuseStep 3389453 = 1271045) (by norm_num)
theorem B2258981 : Blo 1505449 2258981 := bbase (se 4 (by rfl) ⟨211779, by rfl⟩ : syracuseStep 2258981 = 423559) (by norm_num)
theorem B1693741 : Blo 1505449 1693741 := bbase (se 3 (by rfl) ⟨317576, by rfl⟩ : syracuseStep 1693741 = 635153) (by norm_num)
theorem B1718329 : Blo 1505449 1718329 := bbase (se 2 (by rfl) ⟨644373, by rfl⟩ : syracuseStep 1718329 = 1288747) (by norm_num)
theorem B2259005 : Blo 1505449 2259005 := bbase (se 3 (by rfl) ⟨423563, by rfl⟩ : syracuseStep 2259005 = 847127) (by norm_num)
theorem B1693777 : Blo 1505449 1693777 := bbase (se 2 (by rfl) ⟨635166, by rfl⟩ : syracuseStep 1693777 = 1270333) (by norm_num)
theorem B2259029 : Blo 1505449 2259029 := bbase (se 8 (by rfl) ⟨13236, by rfl⟩ : syracuseStep 2259029 = 26473) (by norm_num)
theorem B3389525 : Blo 1505449 3389525 := bbase (se 8 (by rfl) ⟨19860, by rfl⟩ : syracuseStep 3389525 = 39721) (by norm_num)
theorem B2259053 : Blo 1505449 2259053 := bbase (se 3 (by rfl) ⟨423572, by rfl⟩ : syracuseStep 2259053 = 847145) (by norm_num)
theorem B1693813 : Blo 1505449 1693813 := bbase (se 5 (by rfl) ⟨79397, by rfl⟩ : syracuseStep 1693813 = 158795) (by norm_num)
theorem B2259077 : Blo 1505449 2259077 := bbase (se 4 (by rfl) ⟨211788, by rfl⟩ : syracuseStep 2259077 = 423577) (by norm_num)
theorem B7624853 : Blo 1505449 7624853 := bbase (se 6 (by rfl) ⟨178707, by rfl⟩ : syracuseStep 7624853 = 357415) (by norm_num)
theorem B1693849 : Blo 1505449 1693849 := bbase (se 2 (by rfl) ⟨635193, by rfl⟩ : syracuseStep 1693849 = 1270387) (by norm_num)
theorem B1906841 : Blo 1505449 1906841 := bbase (se 2 (by rfl) ⟨715065, by rfl⟩ : syracuseStep 1906841 = 1430131) (by norm_num)
theorem B2259101 : Blo 1505449 2259101 := bbase (se 3 (by rfl) ⟨423581, by rfl⟩ : syracuseStep 2259101 = 847163) (by norm_num)
theorem B3668125 : Blo 1505449 3668125 := bbase (se 3 (by rfl) ⟨687773, by rfl⟩ : syracuseStep 3668125 = 1375547) (by norm_num)
theorem B3389597 : Blo 1505449 3389597 := bbase (se 3 (by rfl) ⟨635549, by rfl⟩ : syracuseStep 3389597 = 1271099) (by norm_num)
theorem B3217573 : Blo 1505449 3217573 := bbase (se 4 (by rfl) ⟨301647, by rfl⟩ : syracuseStep 3217573 = 603295) (by norm_num)
theorem B2259125 : Blo 1505449 2259125 := bbase (se 5 (by rfl) ⟨105896, by rfl⟩ : syracuseStep 2259125 = 211793) (by norm_num)
theorem B11598005 : Blo 1505449 11598005 := bbase (se 5 (by rfl) ⟨543656, by rfl⟩ : syracuseStep 11598005 = 1087313) (by norm_num)
theorem B1693885 : Blo 1505449 1693885 := bbase (se 3 (by rfl) ⟨317603, by rfl⟩ : syracuseStep 1693885 = 635207) (by norm_num)
theorem B2259149 : Blo 1505449 2259149 := bbase (se 3 (by rfl) ⟨423590, by rfl⟩ : syracuseStep 2259149 = 847181) (by norm_num)
theorem B1906897 : Blo 1505449 1906897 := bbase (se 2 (by rfl) ⟨715086, by rfl⟩ : syracuseStep 1906897 = 1430173) (by norm_num)
theorem B1693921 : Blo 1505449 1693921 := bbase (se 2 (by rfl) ⟨635220, by rfl⟩ : syracuseStep 1693921 = 1270441) (by norm_num)
theorem B2259173 : Blo 1505449 2259173 := bbase (se 4 (by rfl) ⟨211797, by rfl⟩ : syracuseStep 2259173 = 423595) (by norm_num)
theorem B2144485 : Blo 1505449 2144485 := bbase (se 4 (by rfl) ⟨201045, by rfl⟩ : syracuseStep 2144485 = 402091) (by norm_num)
theorem B3389669 : Blo 1505449 3389669 := bbase (se 4 (by rfl) ⟨317781, by rfl⟩ : syracuseStep 3389669 = 635563) (by norm_num)
theorem B2259197 : Blo 1505449 2259197 := bbase (se 3 (by rfl) ⟨423599, by rfl⟩ : syracuseStep 2259197 = 847199) (by norm_num)
theorem B1693957 : Blo 1505449 1693957 := bbase (se 4 (by rfl) ⟨158808, by rfl⟩ : syracuseStep 1693957 = 317617) (by norm_num)
theorem B2259221 : Blo 1505449 2259221 := bbase (se 6 (by rfl) ⟨52950, by rfl⟩ : syracuseStep 2259221 = 105901) (by norm_num)
theorem B1693993 : Blo 1505449 1693993 := bbase (se 2 (by rfl) ⟨635247, by rfl⟩ : syracuseStep 1693993 = 1270495) (by norm_num)
theorem B2259245 : Blo 1505449 2259245 := bbase (se 3 (by rfl) ⟨423608, by rfl⟩ : syracuseStep 2259245 = 847217) (by norm_num)
theorem B3389741 : Blo 1505449 3389741 := bbase (se 3 (by rfl) ⟨635576, by rfl⟩ : syracuseStep 3389741 = 1271153) (by norm_num)
theorem B1906993 : Blo 1505449 1906993 := bbase (se 2 (by rfl) ⟨715122, by rfl⟩ : syracuseStep 1906993 = 1430245) (by norm_num)
theorem B2259269 : Blo 1505449 2259269 := bbase (se 4 (by rfl) ⟨211806, by rfl⟩ : syracuseStep 2259269 = 423613) (by norm_num)
theorem B1694029 : Blo 1505449 1694029 := bbase (se 3 (by rfl) ⟨317630, by rfl⟩ : syracuseStep 1694029 = 635261) (by norm_num)
theorem B2259293 : Blo 1505449 2259293 := bbase (se 3 (by rfl) ⟨423617, by rfl⟩ : syracuseStep 2259293 = 847235) (by norm_num)
theorem B1694065 : Blo 1505449 1694065 := bbase (se 2 (by rfl) ⟨635274, by rfl⟩ : syracuseStep 1694065 = 1270549) (by norm_num)
theorem B2259317 : Blo 1505449 2259317 := bbase (se 5 (by rfl) ⟨105905, by rfl⟩ : syracuseStep 2259317 = 211811) (by norm_num)
theorem B3389813 : Blo 1505449 3389813 := bbase (se 5 (by rfl) ⟨158897, by rfl⟩ : syracuseStep 3389813 = 317795) (by norm_num)
theorem B5085557 : Blo 1505449 5085557 := bbase (se 5 (by rfl) ⟨238385, by rfl⟩ : syracuseStep 5085557 = 476771) (by norm_num)
theorem B3619205 : Blo 1505449 3619205 := bbase (se 4 (by rfl) ⟨339300, by rfl⟩ : syracuseStep 3619205 = 678601) (by norm_num)
theorem B2259341 : Blo 1505449 2259341 := bbase (se 3 (by rfl) ⟨423626, by rfl⟩ : syracuseStep 2259341 = 847253) (by norm_num)
theorem B1694101 : Blo 1505449 1694101 := bbase (se 6 (by rfl) ⟨39705, by rfl⟩ : syracuseStep 1694101 = 79411) (by norm_num)
theorem B2259365 : Blo 1505449 2259365 := bbase (se 4 (by rfl) ⟨211815, by rfl⟩ : syracuseStep 2259365 = 423631) (by norm_num)
theorem B1694137 : Blo 1505449 1694137 := bbase (se 2 (by rfl) ⟨635301, by rfl⟩ : syracuseStep 1694137 = 1270603) (by norm_num)
theorem B2259389 : Blo 1505449 2259389 := bbase (se 3 (by rfl) ⟨423635, by rfl⟩ : syracuseStep 2259389 = 847271) (by norm_num)
theorem B3389885 : Blo 1505449 3389885 := bbase (se 3 (by rfl) ⟨635603, by rfl⟩ : syracuseStep 3389885 = 1271207) (by norm_num)
theorem B2259413 : Blo 1505449 2259413 := bbase (se 7 (by rfl) ⟨26477, by rfl⟩ : syracuseStep 2259413 = 52955) (by norm_num)
theorem B1694173 : Blo 1505449 1694173 := bbase (se 3 (by rfl) ⟨317657, by rfl⟩ : syracuseStep 1694173 = 635315) (by norm_num)
theorem B5716453 : Blo 1505449 5716453 := bbase (se 4 (by rfl) ⟨535917, by rfl⟩ : syracuseStep 5716453 = 1071835) (by norm_num)
theorem B1931749 : Blo 1505449 1931749 := bbase (se 4 (by rfl) ⟨181101, by rfl⟩ : syracuseStep 1931749 = 362203) (by norm_num)
theorem B2259437 : Blo 1505449 2259437 := bbase (se 3 (by rfl) ⟨423644, by rfl⟩ : syracuseStep 2259437 = 847289) (by norm_num)
theorem B1694209 : Blo 1505449 1694209 := bbase (se 2 (by rfl) ⟨635328, by rfl⟩ : syracuseStep 1694209 = 1270657) (by norm_num)
theorem B2259461 : Blo 1505449 2259461 := bbase (se 4 (by rfl) ⟨211824, by rfl⟩ : syracuseStep 2259461 = 423649) (by norm_num)
theorem B3389957 : Blo 1505449 3389957 := bbase (se 4 (by rfl) ⟨317808, by rfl⟩ : syracuseStep 3389957 = 635617) (by norm_num)
theorem B1907221 : Blo 1505449 1907221 := bbase (se 6 (by rfl) ⟨44700, by rfl⟩ : syracuseStep 1907221 = 89401) (by norm_num)
theorem B2259485 : Blo 1505449 2259485 := bbase (se 3 (by rfl) ⟨423653, by rfl⟩ : syracuseStep 2259485 = 847307) (by norm_num)
theorem B1694245 : Blo 1505449 1694245 := bbase (se 4 (by rfl) ⟨158835, by rfl⟩ : syracuseStep 1694245 = 317671) (by norm_num)
theorem B2259509 : Blo 1505449 2259509 := bbase (se 5 (by rfl) ⟨105914, by rfl⟩ : syracuseStep 2259509 = 211829) (by norm_num)
theorem B2144821 : Blo 1505449 2144821 := bbase (se 5 (by rfl) ⟨100538, by rfl⟩ : syracuseStep 2144821 = 201077) (by norm_num)
theorem B1694281 : Blo 1505449 1694281 := bbase (se 2 (by rfl) ⟨635355, by rfl⟩ : syracuseStep 1694281 = 1270711) (by norm_num)
theorem B2259533 : Blo 1505449 2259533 := bbase (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) (by norm_num)
theorem B3390029 : Blo 1505449 3390029 := bbase (se 3 (by rfl) ⟨635630, by rfl⟩ : syracuseStep 3390029 = 1271261) (by norm_num)
theorem B4291157 : Blo 1505449 4291157 := bbase (se 8 (by rfl) ⟨25143, by rfl⟩ : syracuseStep 4291157 = 50287) (by norm_num)
theorem B2259557 : Blo 1505449 2259557 := bbase (se 4 (by rfl) ⟨211833, by rfl⟩ : syracuseStep 2259557 = 423667) (by norm_num)
theorem B1694317 : Blo 1505449 1694317 := bbase (se 3 (by rfl) ⟨317684, by rfl⟩ : syracuseStep 1694317 = 635369) (by norm_num)
theorem B3054197 : Blo 1505449 3054197 := bbase (se 5 (by rfl) ⟨143165, by rfl⟩ : syracuseStep 3054197 = 286331) (by norm_num)
theorem B2259581 : Blo 1505449 2259581 := bbase (se 3 (by rfl) ⟨423671, by rfl⟩ : syracuseStep 2259581 = 847343) (by norm_num)
theorem B1694353 : Blo 1505449 1694353 := bbase (se 2 (by rfl) ⟨635382, by rfl⟩ : syracuseStep 1694353 = 1270765) (by norm_num)
theorem B2259605 : Blo 1505449 2259605 := bbase (se 6 (by rfl) ⟨52959, by rfl⟩ : syracuseStep 2259605 = 105919) (by norm_num)
theorem B3054229 : Blo 1505449 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B3390101 : Blo 1505449 3390101 := bbase (se 6 (by rfl) ⟨79455, by rfl⟩ : syracuseStep 3390101 = 158911) (by norm_num)
theorem B1809049 : Blo 1505449 1809049 := bbase (se 2 (by rfl) ⟨678393, by rfl⟩ : syracuseStep 1809049 = 1356787) (by norm_num)
theorem B3218069 : Blo 1505449 3218069 := bbase (se 6 (by rfl) ⟨75423, by rfl⟩ : syracuseStep 3218069 = 150847) (by norm_num)
theorem B2259629 : Blo 1505449 2259629 := bbase (se 3 (by rfl) ⟨423680, by rfl⟩ : syracuseStep 2259629 = 847361) (by norm_num)
theorem B1694389 : Blo 1505449 1694389 := bbase (se 5 (by rfl) ⟨79424, by rfl⟩ : syracuseStep 1694389 = 158849) (by norm_num)
theorem B11442869 : Blo 1505449 11442869 := bbase (se 5 (by rfl) ⟨536384, by rfl⟩ : syracuseStep 11442869 = 1072769) (by norm_num)
theorem B6273733 : Blo 1505449 6273733 := bbase (se 4 (by rfl) ⟨588162, by rfl⟩ : syracuseStep 6273733 = 1176325) (by norm_num)
theorem B2259653 : Blo 1505449 2259653 := bbase (se 4 (by rfl) ⟨211842, by rfl⟩ : syracuseStep 2259653 = 423685) (by norm_num)
theorem B1694425 : Blo 1505449 1694425 := bbase (se 2 (by rfl) ⟨635409, by rfl⟩ : syracuseStep 1694425 = 1270819) (by norm_num)
theorem B2259677 : Blo 1505449 2259677 := bbase (se 3 (by rfl) ⟨423689, by rfl⟩ : syracuseStep 2259677 = 847379) (by norm_num)
theorem B3390173 : Blo 1505449 3390173 := bbase (se 3 (by rfl) ⟨635657, by rfl⟩ : syracuseStep 3390173 = 1271315) (by norm_num)
theorem B2259701 : Blo 1505449 2259701 := bbase (se 5 (by rfl) ⟨105923, by rfl⟩ : syracuseStep 2259701 = 211847) (by norm_num)
theorem B1694461 : Blo 1505449 1694461 := bbase (se 3 (by rfl) ⟨317711, by rfl⟩ : syracuseStep 1694461 = 635423) (by norm_num)
theorem B2259725 : Blo 1505449 2259725 := bbase (se 3 (by rfl) ⟨423698, by rfl⟩ : syracuseStep 2259725 = 847397) (by norm_num)
theorem B2145037 : Blo 1505449 2145037 := bbase (se 3 (by rfl) ⟨402194, by rfl⟩ : syracuseStep 2145037 = 804389) (by norm_num)
theorem B5716757 : Blo 1505449 5716757 := bbase (se 6 (by rfl) ⟨133986, by rfl⟩ : syracuseStep 5716757 = 267973) (by norm_num)
theorem B1694497 : Blo 1505449 1694497 := bbase (se 2 (by rfl) ⟨635436, by rfl⟩ : syracuseStep 1694497 = 1270873) (by norm_num)
theorem B2259749 : Blo 1505449 2259749 := bbase (se 4 (by rfl) ⟨211851, by rfl⟩ : syracuseStep 2259749 = 423703) (by norm_num)
theorem B3390245 : Blo 1505449 3390245 := bbase (se 4 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 3390245 = 635671) (by norm_num)
theorem B2259773 : Blo 1505449 2259773 := bbase (se 3 (by rfl) ⟨423707, by rfl⟩ : syracuseStep 2259773 = 847415) (by norm_num)
theorem B1694533 : Blo 1505449 1694533 := bbase (se 4 (by rfl) ⟨158862, by rfl⟩ : syracuseStep 1694533 = 317725) (by norm_num)
theorem B2259797 : Blo 1505449 2259797 := bbase (se 9 (by rfl) ⟨6620, by rfl⟩ : syracuseStep 2259797 = 13241) (by norm_num)
theorem B74316629 : Blo 1505449 74316629 := bbase (se 9 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 74316629 = 435449) (by norm_num)
theorem B1694569 : Blo 1505449 1694569 := bbase (se 2 (by rfl) ⟨635463, by rfl⟩ : syracuseStep 1694569 = 1270927) (by norm_num)
theorem B2259821 : Blo 1505449 2259821 := bbase (se 3 (by rfl) ⟨423716, by rfl⟩ : syracuseStep 2259821 = 847433) (by norm_num)
theorem B3390317 : Blo 1505449 3390317 := bbase (se 3 (by rfl) ⟨635684, by rfl⟩ : syracuseStep 3390317 = 1271369) (by norm_num)
theorem B2259845 : Blo 1505449 2259845 := bbase (se 4 (by rfl) ⟨211860, by rfl⟩ : syracuseStep 2259845 = 423721) (by norm_num)
theorem B1694605 : Blo 1505449 1694605 := bbase (se 3 (by rfl) ⟨317738, by rfl⟩ : syracuseStep 1694605 = 635477) (by norm_num)
theorem B9059221 : Blo 1505449 9059221 := bbase (se 6 (by rfl) ⟨212325, by rfl⟩ : syracuseStep 9059221 = 424651) (by norm_num)
theorem B2259869 : Blo 1505449 2259869 := bbase (se 3 (by rfl) ⟨423725, by rfl⟩ : syracuseStep 2259869 = 847451) (by norm_num)
theorem B1694641 : Blo 1505449 1694641 := bbase (se 2 (by rfl) ⟨635490, by rfl⟩ : syracuseStep 1694641 = 1270981) (by norm_num)
theorem B2259893 : Blo 1505449 2259893 := bbase (se 5 (by rfl) ⟨105932, by rfl⟩ : syracuseStep 2259893 = 211865) (by norm_num)
theorem B3390389 : Blo 1505449 3390389 := bbase (se 5 (by rfl) ⟨158924, by rfl⟩ : syracuseStep 3390389 = 317849) (by norm_num)
theorem B2259917 : Blo 1505449 2259917 := bbase (se 3 (by rfl) ⟨423734, by rfl⟩ : syracuseStep 2259917 = 847469) (by norm_num)
theorem B1694677 : Blo 1505449 1694677 := bbase (se 7 (by rfl) ⟨19859, by rfl⟩ : syracuseStep 1694677 = 39719) (by norm_num)
theorem B2259941 : Blo 1505449 2259941 := bbase (se 4 (by rfl) ⟨211869, by rfl⟩ : syracuseStep 2259941 = 423739) (by norm_num)
theorem B1694713 : Blo 1505449 1694713 := bbase (se 2 (by rfl) ⟨635517, by rfl⟩ : syracuseStep 1694713 = 1271035) (by norm_num)
theorem B2259965 : Blo 1505449 2259965 := bbase (se 3 (by rfl) ⟨423743, by rfl⟩ : syracuseStep 2259965 = 847487) (by norm_num)
theorem B3390461 : Blo 1505449 3390461 := bbase (se 3 (by rfl) ⟨635711, by rfl⟩ : syracuseStep 3390461 = 1271423) (by norm_num)
theorem B2898949 : Blo 1505449 2898949 := bbase (se 4 (by rfl) ⟨271776, by rfl⟩ : syracuseStep 2898949 = 543553) (by norm_num)
theorem B2259989 : Blo 1505449 2259989 := bbase (se 6 (by rfl) ⟨52968, by rfl⟩ : syracuseStep 2259989 = 105937) (by norm_num)
theorem B1694749 : Blo 1505449 1694749 := bbase (se 3 (by rfl) ⟨317765, by rfl⟩ : syracuseStep 1694749 = 635531) (by norm_num)
theorem B2260013 : Blo 1505449 2260013 := bbase (se 3 (by rfl) ⟨423752, by rfl⟩ : syracuseStep 2260013 = 847505) (by norm_num)
theorem B1694785 : Blo 1505449 1694785 := bbase (se 2 (by rfl) ⟨635544, by rfl⟩ : syracuseStep 1694785 = 1271089) (by norm_num)
theorem B2260037 : Blo 1505449 2260037 := bbase (se 4 (by rfl) ⟨211878, by rfl⟩ : syracuseStep 2260037 = 423757) (by norm_num)
theorem B3390533 : Blo 1505449 3390533 := bbase (se 4 (by rfl) ⟨317862, by rfl⟩ : syracuseStep 3390533 = 635725) (by norm_num)
theorem B11435093 : Blo 1505449 11435093 := bbase (se 8 (by rfl) ⟨67002, by rfl⟩ : syracuseStep 11435093 = 134005) (by norm_num)
theorem B2260061 : Blo 1505449 2260061 := bbase (se 3 (by rfl) ⟨423761, by rfl⟩ : syracuseStep 2260061 = 847523) (by norm_num)
theorem B3054685 : Blo 1505449 3054685 := bbase (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) (by norm_num)
theorem B1694821 : Blo 1505449 1694821 := bbase (se 4 (by rfl) ⟨158889, by rfl⟩ : syracuseStep 1694821 = 317779) (by norm_num)
theorem B8576117 : Blo 1505449 8576117 := bbase (se 5 (by rfl) ⟨402005, by rfl⟩ : syracuseStep 8576117 = 804011) (by norm_num)
theorem B4127861 : Blo 1505449 4127861 := bbase (se 5 (by rfl) ⟨193493, by rfl⟩ : syracuseStep 4127861 = 386987) (by norm_num)
theorem B1809529 : Blo 1505449 1809529 := bbase (se 2 (by rfl) ⟨678573, by rfl⟩ : syracuseStep 1809529 = 1357147) (by norm_num)
theorem B2260085 : Blo 1505449 2260085 := bbase (se 5 (by rfl) ⟨105941, by rfl⟩ : syracuseStep 2260085 = 211883) (by norm_num)
theorem B2145413 : Blo 1505449 2145413 := bbase (se 4 (by rfl) ⟨201132, by rfl⟩ : syracuseStep 2145413 = 402265) (by norm_num)
theorem B1694857 : Blo 1505449 1694857 := bbase (se 2 (by rfl) ⟨635571, by rfl⟩ : syracuseStep 1694857 = 1271143) (by norm_num)
theorem B3619981 : Blo 1505449 3619981 := bbase (se 3 (by rfl) ⟨678746, by rfl⟩ : syracuseStep 3619981 = 1357493) (by norm_num)
theorem B2260109 : Blo 1505449 2260109 := bbase (se 3 (by rfl) ⟨423770, by rfl⟩ : syracuseStep 2260109 = 847541) (by norm_num)
theorem B3390605 : Blo 1505449 3390605 := bbase (se 3 (by rfl) ⟨635738, by rfl⟩ : syracuseStep 3390605 = 1271477) (by norm_num)
theorem B2260133 : Blo 1505449 2260133 := bbase (se 4 (by rfl) ⟨211887, by rfl⟩ : syracuseStep 2260133 = 423775) (by norm_num)
theorem B1694893 : Blo 1505449 1694893 := bbase (se 3 (by rfl) ⟨317792, by rfl⟩ : syracuseStep 1694893 = 635585) (by norm_num)
theorem B2260157 : Blo 1505449 2260157 := bbase (se 3 (by rfl) ⟨423779, by rfl⟩ : syracuseStep 2260157 = 847559) (by norm_num)
theorem B1694929 : Blo 1505449 1694929 := bbase (se 2 (by rfl) ⟨635598, by rfl⟩ : syracuseStep 1694929 = 1271197) (by norm_num)
theorem B2260181 : Blo 1505449 2260181 := bbase (se 7 (by rfl) ⟨26486, by rfl⟩ : syracuseStep 2260181 = 52973) (by norm_num)
theorem B2260205 : Blo 1505449 2260205 := bbase (se 3 (by rfl) ⟨423788, by rfl⟩ : syracuseStep 2260205 = 847577) (by norm_num)
theorem B1694965 : Blo 1505449 1694965 := bbase (se 5 (by rfl) ⟨79451, by rfl⟩ : syracuseStep 1694965 = 158903) (by norm_num)
theorem B2260229 : Blo 1505449 2260229 := bbase (se 4 (by rfl) ⟨211896, by rfl⟩ : syracuseStep 2260229 = 423793) (by norm_num)
theorem B1695001 : Blo 1505449 1695001 := bbase (se 2 (by rfl) ⟨635625, by rfl⟩ : syracuseStep 1695001 = 1271251) (by norm_num)
theorem B2260253 : Blo 1505449 2260253 := bbase (se 3 (by rfl) ⟨423797, by rfl⟩ : syracuseStep 2260253 = 847595) (by norm_num)
theorem B2260277 : Blo 1505449 2260277 := bbase (se 5 (by rfl) ⟨105950, by rfl⟩ : syracuseStep 2260277 = 211901) (by norm_num)
theorem B1695037 : Blo 1505449 1695037 := bbase (se 3 (by rfl) ⟨317819, by rfl⟩ : syracuseStep 1695037 = 635639) (by norm_num)
theorem B2260301 : Blo 1505449 2260301 := bbase (se 3 (by rfl) ⟨423806, by rfl⟩ : syracuseStep 2260301 = 847613) (by norm_num)
theorem B1695073 : Blo 1505449 1695073 := bbase (se 2 (by rfl) ⟨635652, by rfl⟩ : syracuseStep 1695073 = 1271305) (by norm_num)
theorem B2858341 : Blo 1505449 2858341 := bbase (se 4 (by rfl) ⟨267969, by rfl⟩ : syracuseStep 2858341 = 535939) (by norm_num)
theorem B2260325 : Blo 1505449 2260325 := bbase (se 4 (by rfl) ⟨211905, by rfl⟩ : syracuseStep 2260325 = 423811) (by norm_num)
theorem B2260349 : Blo 1505449 2260349 := bbase (se 3 (by rfl) ⟨423815, by rfl⟩ : syracuseStep 2260349 = 847631) (by norm_num)
theorem B1695109 : Blo 1505449 1695109 := bbase (se 4 (by rfl) ⟨158916, by rfl⟩ : syracuseStep 1695109 = 317833) (by norm_num)
theorem B2260373 : Blo 1505449 2260373 := bbase (se 6 (by rfl) ⟨52977, by rfl⟩ : syracuseStep 2260373 = 105955) (by norm_num)
theorem B7626149 : Blo 1505449 7626149 := bbase (se 4 (by rfl) ⟨714951, by rfl⟩ : syracuseStep 7626149 = 1429903) (by norm_num)
theorem B1695145 : Blo 1505449 1695145 := bbase (se 2 (by rfl) ⟨635679, by rfl⟩ : syracuseStep 1695145 = 1271359) (by norm_num)
theorem B2260397 : Blo 1505449 2260397 := bbase (se 3 (by rfl) ⟨423824, by rfl⟩ : syracuseStep 2260397 = 847649) (by norm_num)
theorem B2260421 : Blo 1505449 2260421 := bbase (se 4 (by rfl) ⟨211914, by rfl⟩ : syracuseStep 2260421 = 423829) (by norm_num)
theorem B1695181 : Blo 1505449 1695181 := bbase (se 3 (by rfl) ⟨317846, by rfl⟩ : syracuseStep 1695181 = 635693) (by norm_num)
theorem B1695217 : Blo 1505449 1695217 := bbase (se 2 (by rfl) ⟨635706, by rfl⟩ : syracuseStep 1695217 = 1271413) (by norm_num)
theorem B2858485 : Blo 1505449 2858485 := bbase (se 5 (by rfl) ⟨133991, by rfl⟩ : syracuseStep 2858485 = 267983) (by norm_num)
theorem B5152261 : Blo 1505449 5152261 := bbase (se 4 (by rfl) ⟨483024, by rfl⟩ : syracuseStep 5152261 = 966049) (by norm_num)
theorem B1695253 : Blo 1505449 1695253 := bbase (se 6 (by rfl) ⟨39732, by rfl⟩ : syracuseStep 1695253 = 79465) (by norm_num)
theorem B1695289 : Blo 1505449 1695289 := bbase (se 2 (by rfl) ⟨635733, by rfl⟩ : syracuseStep 1695289 = 1271467) (by norm_num)
theorem B2858645 : Blo 1505449 2858645 := bbase (se 6 (by rfl) ⟨66999, by rfl⟩ : syracuseStep 2858645 = 133999) (by norm_num)
theorem B12385973 : Blo 1505449 12385973 := bbase (se 5 (by rfl) ⟨580592, by rfl⟩ : syracuseStep 12385973 = 1161185) (by norm_num)
theorem B2858789 : Blo 1505449 2858789 := bbase (se 4 (by rfl) ⟨268011, by rfl⟩ : syracuseStep 2858789 = 536023) (by norm_num)
theorem B3620693 : Blo 1505449 3620693 := bbase (se 9 (by rfl) ⟨10607, by rfl⟩ : syracuseStep 3620693 = 21215) (by norm_num)
theorem B10305397 : Blo 1505449 10305397 := bbase (se 5 (by rfl) ⟨483065, by rfl⟩ : syracuseStep 10305397 = 966131) (by norm_num)
theorem B3915661 : Blo 1505449 3915661 := bbase (se 3 (by rfl) ⟨734186, by rfl⟩ : syracuseStep 3915661 = 1468373) (by norm_num)
theorem B4890833 : Blo 1505449 4890833 := bstep (se 2 (by rfl) ⟨1834062, by rfl⟩ : syracuseStep 4890833 = 3668125) B3668125
theorem B2859313 : Blo 1505449 2859313 := bstep (se 2 (by rfl) ⟨1072242, by rfl⟩ : syracuseStep 2859313 = 2144485) B2144485
theorem B10854755 : Blo 1505449 10854755 := bstep (se 1 (by rfl) ⟨8141066, by rfl⟩ : syracuseStep 10854755 = 16282133) B16282133
theorem B7627121 : Blo 1505449 7627121 := bstep (se 2 (by rfl) ⟨2860170, by rfl⟩ : syracuseStep 7627121 = 5720341) B5720341
theorem B4071917 : Blo 1505449 4071917 := bstep (se 3 (by rfl) ⟨763484, by rfl⟩ : syracuseStep 4071917 = 1526969) B1526969
theorem B9650821 : Blo 1505449 9650821 := bstep (se 4 (by rfl) ⟨904764, by rfl⟩ : syracuseStep 9650821 = 1809529) B1809529
theorem B2859715 : Blo 1505449 2859715 := bstep (se 1 (by rfl) ⟨2144786, by rfl⟩ : syracuseStep 2859715 = 4289573) B4289573
theorem B2859761 : Blo 1505449 2859761 := bstep (se 2 (by rfl) ⟨1072410, by rfl⟩ : syracuseStep 2859761 = 2144821) B2144821
theorem B21168965 : Blo 1505449 21168965 := bstep (se 4 (by rfl) ⟨1984590, by rfl⟩ : syracuseStep 21168965 = 3969181) B3969181
theorem B5718883 : Blo 1505449 5718883 := bstep (se 1 (by rfl) ⟨4289162, by rfl⟩ : syracuseStep 5718883 = 8578325) B8578325
theorem B8364977 : Blo 1505449 8364977 := bstep (se 2 (by rfl) ⟨3136866, by rfl⟩ : syracuseStep 8364977 = 6273733) B6273733
theorem B2540497 : Blo 1505449 2540497 := bstep (se 2 (by rfl) ⟨952686, by rfl⟩ : syracuseStep 2540497 = 1905373) B1905373
theorem B2540531 : Blo 1505449 2540531 := bstep (se 1 (by rfl) ⟨1905398, by rfl⟩ : syracuseStep 2540531 = 3810797) B3810797
theorem B2860049 : Blo 1505449 2860049 := bstep (se 2 (by rfl) ⟨1072518, by rfl⟩ : syracuseStep 2860049 = 2145037) B2145037
theorem B2540659 : Blo 1505449 2540659 := bstep (se 1 (by rfl) ⟨1905494, by rfl⟩ : syracuseStep 2540659 = 3810989) B3810989
theorem B2352305 : Blo 1505449 2352305 := bstep (se 2 (by rfl) ⟨882114, by rfl⟩ : syracuseStep 2352305 = 1764229) B1764229
theorem B2540801 : Blo 1505449 2540801 := bstep (se 2 (by rfl) ⟨952800, by rfl⟩ : syracuseStep 2540801 = 1905601) B1905601
theorem B13583729 : Blo 1505449 13583729 := bstep (se 2 (by rfl) ⟨5093898, by rfl⟩ : syracuseStep 13583729 = 10187797) B10187797
theorem B2540929 : Blo 1505449 2540929 := bstep (se 2 (by rfl) ⟨952848, by rfl⟩ : syracuseStep 2540929 = 1905697) B1905697
theorem B2540963 : Blo 1505449 2540963 := bstep (se 1 (by rfl) ⟨1905722, by rfl⟩ : syracuseStep 2540963 = 3811445) B3811445
theorem B4072913 : Blo 1505449 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B4826641 : Blo 1505449 4826641 := bstep (se 2 (by rfl) ⟨1809990, by rfl⟩ : syracuseStep 4826641 = 3619981) B3619981
theorem B2541091 : Blo 1505449 2541091 := bstep (se 1 (by rfl) ⟨1905818, by rfl⟩ : syracuseStep 2541091 = 3811637) B3811637
theorem B8144525 : Blo 1505449 8144525 := bstep (se 3 (by rfl) ⟨1527098, by rfl⟩ : syracuseStep 8144525 = 3054197) B3054197
theorem B2541233 : Blo 1505449 2541233 := bstep (se 2 (by rfl) ⟨952962, by rfl⟩ : syracuseStep 2541233 = 1905925) B1905925
theorem B2860771 : Blo 1505449 2860771 := bstep (se 1 (by rfl) ⟨2145578, by rfl⟩ : syracuseStep 2860771 = 4291157) B4291157
theorem B3917585 : Blo 1505449 3917585 := bstep (se 2 (by rfl) ⟨1469094, by rfl⟩ : syracuseStep 3917585 = 2938189) B2938189
theorem B7628579 : Blo 1505449 7628579 := bstep (se 1 (by rfl) ⟨5721434, by rfl⟩ : syracuseStep 7628579 = 11442869) B11442869
theorem B3811121 : Blo 1505449 3811121 := bstep (se 2 (by rfl) ⟨1429170, by rfl⟩ : syracuseStep 3811121 = 2858341) B2858341
theorem B2541361 : Blo 1505449 2541361 := bstep (se 2 (by rfl) ⟨953010, by rfl⟩ : syracuseStep 2541361 = 1906021) B1906021
theorem B5080913 : Blo 1505449 5080913 := bstep (se 2 (by rfl) ⟨1905342, by rfl⟩ : syracuseStep 5080913 = 3810685) B3810685
theorem B2541395 : Blo 1505449 2541395 := bstep (se 1 (by rfl) ⟨1906046, by rfl⟩ : syracuseStep 2541395 = 3812093) B3812093
theorem B3811171 : Blo 1505449 3811171 := bstep (se 1 (by rfl) ⟨2858378, by rfl⟩ : syracuseStep 3811171 = 5716757) B5716757
theorem B11003789 : Blo 1505449 11003789 := bstep (se 3 (by rfl) ⟨2063210, by rfl⟩ : syracuseStep 11003789 = 4126421) B4126421
theorem B2541523 : Blo 1505449 2541523 := bstep (se 1 (by rfl) ⟨1906142, by rfl⟩ : syracuseStep 2541523 = 3812285) B3812285
theorem B3811313 : Blo 1505449 3811313 := bstep (se 2 (by rfl) ⟨1429242, by rfl⟩ : syracuseStep 3811313 = 2858485) B2858485
theorem B2541665 : Blo 1505449 2541665 := bstep (se 2 (by rfl) ⟨953124, by rfl⟩ : syracuseStep 2541665 = 1906249) B1906249
theorem B2541793 : Blo 1505449 2541793 := bstep (se 2 (by rfl) ⟨953172, by rfl⟩ : syracuseStep 2541793 = 1906345) B1906345
theorem B2541827 : Blo 1505449 2541827 := bstep (se 1 (by rfl) ⟨1906370, by rfl⟩ : syracuseStep 2541827 = 3812741) B3812741
theorem B5081453 : Blo 1505449 5081453 := bstep (se 3 (by rfl) ⟨952772, by rfl⟩ : syracuseStep 5081453 = 1905545) B1905545
theorem B2541955 : Blo 1505449 2541955 := bstep (se 1 (by rfl) ⟨1906466, by rfl⟩ : syracuseStep 2541955 = 3812933) B3812933
theorem B5081507 : Blo 1505449 5081507 := bstep (se 1 (by rfl) ⟨3811130, by rfl⟩ : syracuseStep 5081507 = 7622261) B7622261
theorem B1907155 : Blo 1505449 1907155 := bstep (se 1 (by rfl) ⟨1430366, by rfl⟩ : syracuseStep 1907155 = 2860733) B2860733
theorem B13740529 : Blo 1505449 13740529 := bstep (se 2 (by rfl) ⟨5152698, by rfl⟩ : syracuseStep 13740529 = 10305397) B10305397
theorem B5220881 : Blo 1505449 5220881 := bstep (se 2 (by rfl) ⟨1957830, by rfl⟩ : syracuseStep 5220881 = 3915661) B3915661
theorem B2542097 : Blo 1505449 2542097 := bstep (se 2 (by rfl) ⟨953286, by rfl⟩ : syracuseStep 2542097 = 1906573) B1906573
theorem B2542225 : Blo 1505449 2542225 := bstep (se 2 (by rfl) ⟨953334, by rfl⟩ : syracuseStep 2542225 = 1906669) B1906669
theorem B5081777 : Blo 1505449 5081777 := bstep (se 2 (by rfl) ⟨1905666, by rfl⟩ : syracuseStep 5081777 = 3811333) B3811333
theorem B2542259 : Blo 1505449 2542259 := bstep (se 1 (by rfl) ⟨1906694, by rfl⟩ : syracuseStep 2542259 = 3813389) B3813389
theorem B4287181 : Blo 1505449 4287181 := bstep (se 3 (by rfl) ⟨803846, by rfl⟩ : syracuseStep 4287181 = 1607693) B1607693
theorem B1526531 : Blo 1505449 1526531 := bstep (se 1 (by rfl) ⟨1144898, by rfl⟩ : syracuseStep 1526531 = 2289797) B2289797
theorem B2542387 : Blo 1505449 2542387 := bstep (se 1 (by rfl) ⟨1906790, by rfl⟩ : syracuseStep 2542387 = 3813581) B3813581
theorem B2354003 : Blo 1505449 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B2714467 : Blo 1505449 2714467 := bstep (se 1 (by rfl) ⟨2035850, by rfl⟩ : syracuseStep 2714467 = 4071701) B4071701
theorem B2542529 : Blo 1505449 2542529 := bstep (se 2 (by rfl) ⟨953448, by rfl⟩ : syracuseStep 2542529 = 1906897) B1906897
theorem B3812305 : Blo 1505449 3812305 := bstep (se 2 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 3812305 = 2859229) B2859229
theorem B5721101 : Blo 1505449 5721101 := bstep (se 3 (by rfl) ⟨1072706, by rfl⟩ : syracuseStep 5721101 = 2145413) B2145413
theorem B2575379 : Blo 1505449 2575379 := bstep (se 1 (by rfl) ⟨1931534, by rfl⟩ : syracuseStep 2575379 = 3863069) B3863069
theorem B36637717 : Blo 1505449 36637717 := bstep (se 6 (by rfl) ⟨858696, by rfl⟩ : syracuseStep 36637717 = 1717393) B1717393
theorem B2542657 : Blo 1505449 2542657 := bstep (se 2 (by rfl) ⟨953496, by rfl⟩ : syracuseStep 2542657 = 1906993) B1906993
theorem B2034769 : Blo 1505449 2034769 := bstep (se 2 (by rfl) ⟨763038, by rfl⟩ : syracuseStep 2034769 = 1526077) B1526077
theorem B2542691 : Blo 1505449 2542691 := bstep (se 1 (by rfl) ⟨1907018, by rfl⟩ : syracuseStep 2542691 = 3814037) B3814037
theorem B30928013 : Blo 1505449 30928013 := bstep (se 3 (by rfl) ⟨5799002, by rfl⟩ : syracuseStep 30928013 = 11598005) B11598005
theorem B2575523 : Blo 1505449 2575523 := bstep (se 1 (by rfl) ⟨1931642, by rfl⟩ : syracuseStep 2575523 = 3863285) B3863285
theorem B2174131 : Blo 1505449 2174131 := bstep (se 1 (by rfl) ⟨1630598, by rfl⟩ : syracuseStep 2174131 = 3261197) B3261197
theorem B5082317 : Blo 1505449 5082317 := bstep (se 3 (by rfl) ⟨952934, by rfl⟩ : syracuseStep 5082317 = 1905869) B1905869
theorem B3812579 : Blo 1505449 3812579 := bstep (se 1 (by rfl) ⟨2859434, by rfl⟩ : syracuseStep 3812579 = 5718869) B5718869
theorem B2542819 : Blo 1505449 2542819 := bstep (se 1 (by rfl) ⟨1907114, by rfl⟩ : syracuseStep 2542819 = 3814229) B3814229
theorem B5082371 : Blo 1505449 5082371 := bstep (se 1 (by rfl) ⟨3811778, by rfl⟩ : syracuseStep 5082371 = 7623557) B7623557
theorem B1608979 : Blo 1505449 1608979 := bstep (se 1 (by rfl) ⟨1206734, by rfl⟩ : syracuseStep 1608979 = 2413469) B2413469
theorem B9653539 : Blo 1505449 9653539 := bstep (se 1 (by rfl) ⟨7240154, by rfl⟩ : syracuseStep 9653539 = 14480309) B14480309
theorem B7621937 : Blo 1505449 7621937 := bstep (se 2 (by rfl) ⟨2858226, by rfl⟩ : syracuseStep 7621937 = 5716453) B5716453
theorem B2542961 : Blo 1505449 2542961 := bstep (se 2 (by rfl) ⟨953610, by rfl⟩ : syracuseStep 2542961 = 1907221) B1907221
theorem B2289043 : Blo 1505449 2289043 := bstep (se 1 (by rfl) ⟨1716782, by rfl⟩ : syracuseStep 2289043 = 3433565) B3433565
theorem B3812771 : Blo 1505449 3812771 := bstep (se 1 (by rfl) ⟨2859578, by rfl⟩ : syracuseStep 3812771 = 5719157) B5719157
theorem B2289091 : Blo 1505449 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B16289221 : Blo 1505449 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B6434275 : Blo 1505449 6434275 := bstep (se 1 (by rfl) ⟨4825706, by rfl⟩ : syracuseStep 6434275 = 9651413) B9651413
theorem B5082641 : Blo 1505449 5082641 := bstep (se 2 (by rfl) ⟨1905990, by rfl⟩ : syracuseStep 5082641 = 3811981) B3811981
theorem B2412065 : Blo 1505449 2412065 := bstep (se 2 (by rfl) ⟨904524, by rfl⟩ : syracuseStep 2412065 = 1809049) B1809049
theorem B4288241 : Blo 1505449 4288241 := bstep (se 2 (by rfl) ⟨1608090, by rfl⟩ : syracuseStep 4288241 = 3216181) B3216181
theorem B5083181 : Blo 1505449 5083181 := bstep (se 3 (by rfl) ⟨953096, by rfl⟩ : syracuseStep 5083181 = 1906193) B1906193
theorem B3387473 : Blo 1505449 3387473 := bstep (se 2 (by rfl) ⟨1270302, by rfl⟩ : syracuseStep 3387473 = 2540605) B2540605
theorem B3387491 : Blo 1505449 3387491 := bstep (se 1 (by rfl) ⟨2540618, by rfl⟩ : syracuseStep 3387491 = 5081237) B5081237
theorem B5083235 : Blo 1505449 5083235 := bstep (se 1 (by rfl) ⟨3812426, by rfl⟩ : syracuseStep 5083235 = 7624853) B7624853
theorem B11432177 : Blo 1505449 11432177 := bstep (se 2 (by rfl) ⟨4287066, by rfl⟩ : syracuseStep 11432177 = 8574133) B8574133
theorem B2412803 : Blo 1505449 2412803 := bstep (se 1 (by rfl) ⟨1809602, by rfl⟩ : syracuseStep 2412803 = 3619205) B3619205
theorem B2289937 : Blo 1505449 2289937 := bstep (se 2 (by rfl) ⟨858726, by rfl⟩ : syracuseStep 2289937 = 1717453) B1717453
theorem B3813713 : Blo 1505449 3813713 := bstep (se 2 (by rfl) ⟨1430142, by rfl⟩ : syracuseStep 3813713 = 2860285) B2860285
theorem B3387761 : Blo 1505449 3387761 := bstep (se 2 (by rfl) ⟨1270410, by rfl⟩ : syracuseStep 3387761 = 2540821) B2540821
theorem B5083505 : Blo 1505449 5083505 := bstep (se 2 (by rfl) ⟨1906314, by rfl⟩ : syracuseStep 5083505 = 3812629) B3812629
theorem B3387779 : Blo 1505449 3387779 := bstep (se 1 (by rfl) ⟨2540834, by rfl⟩ : syracuseStep 3387779 = 5081669) B5081669
theorem B3813763 : Blo 1505449 3813763 := bstep (se 1 (by rfl) ⟨2860322, by rfl⟩ : syracuseStep 3813763 = 5720645) B5720645
theorem B4288913 : Blo 1505449 4288913 := bstep (se 2 (by rfl) ⟨1608342, by rfl⟩ : syracuseStep 4288913 = 3216685) B3216685
theorem B14471621 : Blo 1505449 14471621 := bstep (se 4 (by rfl) ⟨1356714, by rfl⟩ : syracuseStep 14471621 = 2713429) B2713429
theorem B10859021 : Blo 1505449 10859021 := bstep (se 3 (by rfl) ⟨2036066, by rfl⟩ : syracuseStep 10859021 = 4072133) B4072133
theorem B3813905 : Blo 1505449 3813905 := bstep (se 2 (by rfl) ⟨1430214, by rfl⟩ : syracuseStep 3813905 = 2860429) B2860429
theorem B6107683 : Blo 1505449 6107683 := bstep (se 1 (by rfl) ⟨4580762, by rfl⟩ : syracuseStep 6107683 = 9161525) B9161525
theorem B3388049 : Blo 1505449 3388049 := bstep (se 2 (by rfl) ⟨1270518, by rfl⟩ : syracuseStep 3388049 = 2541037) B2541037
theorem B3388067 : Blo 1505449 3388067 := bstep (se 1 (by rfl) ⟨2541050, by rfl⟩ : syracuseStep 3388067 = 5082101) B5082101
theorem B6869681 : Blo 1505449 6869681 := bstep (se 2 (by rfl) ⟨2576130, by rfl⟩ : syracuseStep 6869681 = 5152261) B5152261
theorem B9163469 : Blo 1505449 9163469 := bstep (se 3 (by rfl) ⟨1718150, by rfl⟩ : syracuseStep 9163469 = 3436301) B3436301
theorem B7623395 : Blo 1505449 7623395 := bstep (se 1 (by rfl) ⟨5717546, by rfl⟩ : syracuseStep 7623395 = 11435093) B11435093
theorem B3617617 : Blo 1505449 3617617 := bstep (se 2 (by rfl) ⟨1356606, by rfl⟩ : syracuseStep 3617617 = 2713213) B2713213
theorem B5084045 : Blo 1505449 5084045 := bstep (se 3 (by rfl) ⟨953258, by rfl⟩ : syracuseStep 5084045 = 1906517) B1906517
theorem B5575601 : Blo 1505449 5575601 := bstep (se 2 (by rfl) ⟨2090850, by rfl⟩ : syracuseStep 5575601 = 4181701) B4181701
theorem B3388337 : Blo 1505449 3388337 := bstep (se 2 (by rfl) ⟨1270626, by rfl⟩ : syracuseStep 3388337 = 2541253) B2541253
theorem B3388355 : Blo 1505449 3388355 := bstep (se 1 (by rfl) ⟨2541266, by rfl⟩ : syracuseStep 3388355 = 5082533) B5082533
theorem B5084099 : Blo 1505449 5084099 := bstep (se 1 (by rfl) ⟨3813074, by rfl⟩ : syracuseStep 5084099 = 7626149) B7626149
theorem B9409613 : Blo 1505449 9409613 := bstep (se 3 (by rfl) ⟨1764302, by rfl⟩ : syracuseStep 9409613 = 3528605) B3528605
theorem B1905763 : Blo 1505449 1905763 := bstep (se 1 (by rfl) ⟨1429322, by rfl⟩ : syracuseStep 1905763 = 2858645) B2858645
theorem B4289699 : Blo 1505449 4289699 := bstep (se 1 (by rfl) ⟨3217274, by rfl⟩ : syracuseStep 4289699 = 6434549) B6434549
theorem B1905859 : Blo 1505449 1905859 := bstep (se 1 (by rfl) ⟨1429394, by rfl⟩ : syracuseStep 1905859 = 2858789) B2858789
theorem B10302661 : Blo 1505449 10302661 := bstep (se 4 (by rfl) ⟨965874, by rfl⟩ : syracuseStep 10302661 = 1931749) B1931749
theorem B3388625 : Blo 1505449 3388625 := bstep (se 2 (by rfl) ⟨1270734, by rfl⟩ : syracuseStep 3388625 = 2541469) B2541469
theorem B5084369 : Blo 1505449 5084369 := bstep (se 2 (by rfl) ⟨1906638, by rfl⟩ : syracuseStep 5084369 = 3813277) B3813277
theorem B3388643 : Blo 1505449 3388643 := bstep (se 1 (by rfl) ⟨2541482, by rfl⟩ : syracuseStep 3388643 = 5082965) B5082965
theorem B2413795 : Blo 1505449 2413795 := bstep (se 1 (by rfl) ⟨1810346, by rfl⟩ : syracuseStep 2413795 = 3620693) B3620693
theorem B2258177 : Blo 1505449 2258177 := bstep (se 2 (by rfl) ⟨846816, by rfl⟩ : syracuseStep 2258177 = 1693633) B1693633
theorem B2258195 : Blo 1505449 2258195 := bstep (se 1 (by rfl) ⟨1693646, by rfl⟩ : syracuseStep 2258195 = 3387293) B3387293
theorem B2258225 : Blo 1505449 2258225 := bstep (se 2 (by rfl) ⟨846834, by rfl⟩ : syracuseStep 2258225 = 1693669) B1693669
theorem B2258243 : Blo 1505449 2258243 := bstep (se 1 (by rfl) ⟨1693682, by rfl⟩ : syracuseStep 2258243 = 3387365) B3387365
theorem B2258273 : Blo 1505449 2258273 := bstep (se 2 (by rfl) ⟨846852, by rfl⟩ : syracuseStep 2258273 = 1693705) B1693705
theorem B2258291 : Blo 1505449 2258291 := bstep (se 1 (by rfl) ⟨1693718, by rfl⟩ : syracuseStep 2258291 = 3387437) B3387437
theorem B2258321 : Blo 1505449 2258321 := bstep (se 2 (by rfl) ⟨846870, by rfl⟩ : syracuseStep 2258321 = 1693741) B1693741
theorem B2291105 : Blo 1505449 2291105 := bstep (se 2 (by rfl) ⟨859164, by rfl⟩ : syracuseStep 2291105 = 1718329) B1718329
theorem B2258339 : Blo 1505449 2258339 := bstep (se 1 (by rfl) ⟨1693754, by rfl⟩ : syracuseStep 2258339 = 3387509) B3387509
theorem B6436273 : Blo 1505449 6436273 := bstep (se 2 (by rfl) ⟨2413602, by rfl⟩ : syracuseStep 6436273 = 4827205) B4827205
theorem B2258369 : Blo 1505449 2258369 := bstep (se 2 (by rfl) ⟨846888, by rfl⟩ : syracuseStep 2258369 = 1693777) B1693777
theorem B5223889 : Blo 1505449 5223889 := bstep (se 2 (by rfl) ⟨1958958, by rfl⟩ : syracuseStep 5223889 = 3917917) B3917917
theorem B2258387 : Blo 1505449 2258387 := bstep (se 1 (by rfl) ⟨1693790, by rfl⟩ : syracuseStep 2258387 = 3387581) B3387581
theorem B4290029 : Blo 1505449 4290029 := bstep (se 3 (by rfl) ⟨804380, by rfl⟩ : syracuseStep 4290029 = 1608761) B1608761
theorem B2258417 : Blo 1505449 2258417 := bstep (se 2 (by rfl) ⟨846906, by rfl⟩ : syracuseStep 2258417 = 1693813) B1693813
theorem B3618289 : Blo 1505449 3618289 := bstep (se 2 (by rfl) ⟨1356858, by rfl⟩ : syracuseStep 3618289 = 2713717) B2713717
theorem B3388913 : Blo 1505449 3388913 := bstep (se 2 (by rfl) ⟨1270842, by rfl⟩ : syracuseStep 3388913 = 2541685) B2541685
theorem B2258435 : Blo 1505449 2258435 := bstep (se 1 (by rfl) ⟨1693826, by rfl⟩ : syracuseStep 2258435 = 3387653) B3387653
theorem B3388931 : Blo 1505449 3388931 := bstep (se 1 (by rfl) ⟨2541698, by rfl⟩ : syracuseStep 3388931 = 5083397) B5083397
theorem B7624205 : Blo 1505449 7624205 := bstep (se 3 (by rfl) ⟨1429538, by rfl⟩ : syracuseStep 7624205 = 2859077) B2859077
theorem B2258465 : Blo 1505449 2258465 := bstep (se 2 (by rfl) ⟨846924, by rfl⟩ : syracuseStep 2258465 = 1693849) B1693849
theorem B4290097 : Blo 1505449 4290097 := bstep (se 2 (by rfl) ⟨1608786, by rfl⟩ : syracuseStep 4290097 = 3217573) B3217573
theorem B2258483 : Blo 1505449 2258483 := bstep (se 1 (by rfl) ⟨1693862, by rfl⟩ : syracuseStep 2258483 = 3387725) B3387725
theorem B2258513 : Blo 1505449 2258513 := bstep (se 2 (by rfl) ⟨846942, by rfl⟩ : syracuseStep 2258513 = 1693885) B1693885
theorem B2258531 : Blo 1505449 2258531 := bstep (se 1 (by rfl) ⟨1693898, by rfl⟩ : syracuseStep 2258531 = 3387797) B3387797
theorem B3217009 : Blo 1505449 3217009 := bstep (se 2 (by rfl) ⟨1206378, by rfl⟩ : syracuseStep 3217009 = 2412757) B2412757
theorem B2258561 : Blo 1505449 2258561 := bstep (se 2 (by rfl) ⟨846960, by rfl⟩ : syracuseStep 2258561 = 1693921) B1693921
theorem B2258579 : Blo 1505449 2258579 := bstep (se 1 (by rfl) ⟨1693934, by rfl⟩ : syracuseStep 2258579 = 3387869) B3387869
theorem B2258609 : Blo 1505449 2258609 := bstep (se 2 (by rfl) ⟨846978, by rfl⟩ : syracuseStep 2258609 = 1693957) B1693957
theorem B2143921 : Blo 1505449 2143921 := bstep (se 2 (by rfl) ⟨803970, by rfl⟩ : syracuseStep 2143921 = 1607941) B1607941
theorem B1906355 : Blo 1505449 1906355 := bstep (se 1 (by rfl) ⟨1429766, by rfl⟩ : syracuseStep 1906355 = 2859533) B2859533
theorem B2258627 : Blo 1505449 2258627 := bstep (se 1 (by rfl) ⟨1693970, by rfl⟩ : syracuseStep 2258627 = 3387941) B3387941
theorem B2143955 : Blo 1505449 2143955 := bstep (se 1 (by rfl) ⟨1607966, by rfl⟩ : syracuseStep 2143955 = 3215933) B3215933
theorem B2258657 : Blo 1505449 2258657 := bstep (se 2 (by rfl) ⟨846996, by rfl⟩ : syracuseStep 2258657 = 1693993) B1693993
theorem B5084909 : Blo 1505449 5084909 := bstep (se 3 (by rfl) ⟨953420, by rfl⟩ : syracuseStep 5084909 = 1906841) B1906841
theorem B2258675 : Blo 1505449 2258675 := bstep (se 1 (by rfl) ⟨1694006, by rfl⟩ : syracuseStep 2258675 = 3388013) B3388013
theorem B2258705 : Blo 1505449 2258705 := bstep (se 2 (by rfl) ⟨847014, by rfl⟩ : syracuseStep 2258705 = 1694029) B1694029
theorem B3389201 : Blo 1505449 3389201 := bstep (se 2 (by rfl) ⟨1270950, by rfl⟩ : syracuseStep 3389201 = 2541901) B2541901
theorem B2258723 : Blo 1505449 2258723 := bstep (se 1 (by rfl) ⟨1694042, by rfl⟩ : syracuseStep 2258723 = 3388085) B3388085
theorem B3389219 : Blo 1505449 3389219 := bstep (se 1 (by rfl) ⟨2541914, by rfl⟩ : syracuseStep 3389219 = 5083829) B5083829
theorem B5084963 : Blo 1505449 5084963 := bstep (se 1 (by rfl) ⟨3813722, by rfl⟩ : syracuseStep 5084963 = 7627445) B7627445
theorem B2258753 : Blo 1505449 2258753 := bstep (se 2 (by rfl) ⟨847032, by rfl⟩ : syracuseStep 2258753 = 1694065) B1694065
theorem B4290371 : Blo 1505449 4290371 := bstep (se 1 (by rfl) ⟨3217778, by rfl⟩ : syracuseStep 4290371 = 6435557) B6435557
theorem B2258771 : Blo 1505449 2258771 := bstep (se 1 (by rfl) ⟨1694078, by rfl⟩ : syracuseStep 2258771 = 3388157) B3388157
theorem B2258801 : Blo 1505449 2258801 := bstep (se 2 (by rfl) ⟨847050, by rfl⟩ : syracuseStep 2258801 = 1694101) B1694101
theorem B2258819 : Blo 1505449 2258819 := bstep (se 1 (by rfl) ⟨1694114, by rfl⟩ : syracuseStep 2258819 = 3388229) B3388229
theorem B2258849 : Blo 1505449 2258849 := bstep (se 2 (by rfl) ⟨847068, by rfl⟩ : syracuseStep 2258849 = 1694137) B1694137
theorem B2258867 : Blo 1505449 2258867 := bstep (se 1 (by rfl) ⟨1694150, by rfl⟩ : syracuseStep 2258867 = 3388301) B3388301
theorem B2258897 : Blo 1505449 2258897 := bstep (se 2 (by rfl) ⟨847086, by rfl⟩ : syracuseStep 2258897 = 1694173) B1694173
theorem B1693651 : Blo 1505449 1693651 := bstep (se 1 (by rfl) ⟨1270238, by rfl⟩ : syracuseStep 1693651 = 2540477) B2540477
theorem B2258915 : Blo 1505449 2258915 := bstep (se 1 (by rfl) ⟨1694186, by rfl⟩ : syracuseStep 2258915 = 3388373) B3388373
theorem B2258945 : Blo 1505449 2258945 := bstep (se 2 (by rfl) ⟨847104, by rfl⟩ : syracuseStep 2258945 = 1694209) B1694209
theorem B3217411 : Blo 1505449 3217411 := bstep (se 1 (by rfl) ⟨2413058, by rfl⟩ : syracuseStep 3217411 = 4826117) B4826117
theorem B2258963 : Blo 1505449 2258963 := bstep (se 1 (by rfl) ⟨1694222, by rfl⟩ : syracuseStep 2258963 = 3388445) B3388445
theorem B2258993 : Blo 1505449 2258993 := bstep (se 2 (by rfl) ⟨847122, by rfl⟩ : syracuseStep 2258993 = 1694245) B1694245
theorem B3389489 : Blo 1505449 3389489 := bstep (se 2 (by rfl) ⟨1271058, by rfl⟩ : syracuseStep 3389489 = 2542117) B2542117
theorem B5085233 : Blo 1505449 5085233 := bstep (se 2 (by rfl) ⟨1906962, by rfl⟩ : syracuseStep 5085233 = 3813925) B3813925
theorem B2259011 : Blo 1505449 2259011 := bstep (se 1 (by rfl) ⟨1694258, by rfl⟩ : syracuseStep 2259011 = 3388517) B3388517
theorem B3389507 : Blo 1505449 3389507 := bstep (se 1 (by rfl) ⟨2542130, by rfl⟩ : syracuseStep 3389507 = 5084261) B5084261
theorem B4069453 : Blo 1505449 4069453 := bstep (se 3 (by rfl) ⟨763022, by rfl⟩ : syracuseStep 4069453 = 1526045) B1526045
theorem B2259041 : Blo 1505449 2259041 := bstep (se 2 (by rfl) ⟨847140, by rfl⟩ : syracuseStep 2259041 = 1694281) B1694281
theorem B1693795 : Blo 1505449 1693795 := bstep (se 1 (by rfl) ⟨1270346, by rfl⟩ : syracuseStep 1693795 = 2540693) B2540693
theorem B2259059 : Blo 1505449 2259059 := bstep (se 1 (by rfl) ⟨1694294, by rfl⟩ : syracuseStep 2259059 = 3388589) B3388589
theorem B2259089 : Blo 1505449 2259089 := bstep (se 2 (by rfl) ⟨847158, by rfl⟩ : syracuseStep 2259089 = 1694317) B1694317
theorem B2259107 : Blo 1505449 2259107 := bstep (se 1 (by rfl) ⟨1694330, by rfl⟩ : syracuseStep 2259107 = 3388661) B3388661
theorem B5429425 : Blo 1505449 5429425 := bstep (se 2 (by rfl) ⟨2036034, by rfl⟩ : syracuseStep 5429425 = 4072069) B4072069
theorem B1505459 : Blo 1505449 1505459 := bstep (se 1 (by rfl) ⟨1129094, by rfl⟩ : syracuseStep 1505459 = 2258189) B2258189
theorem B2259137 : Blo 1505449 2259137 := bstep (se 2 (by rfl) ⟨847176, by rfl⟩ : syracuseStep 2259137 = 1694353) B1694353
theorem B1505475 : Blo 1505449 1505475 := bstep (se 1 (by rfl) ⟨1129106, by rfl⟩ : syracuseStep 1505475 = 2258213) B2258213
theorem B1505491 : Blo 1505449 1505491 := bstep (se 1 (by rfl) ⟨1129118, by rfl⟩ : syracuseStep 1505491 = 2258237) B2258237
theorem B2259155 : Blo 1505449 2259155 := bstep (se 1 (by rfl) ⟨1694366, by rfl⟩ : syracuseStep 2259155 = 3388733) B3388733
theorem B1505507 : Blo 1505449 1505507 := bstep (se 1 (by rfl) ⟨1129130, by rfl⟩ : syracuseStep 1505507 = 2258261) B2258261
theorem B2259185 : Blo 1505449 2259185 := bstep (se 2 (by rfl) ⟨847194, by rfl⟩ : syracuseStep 2259185 = 1694389) B1694389
theorem B1505523 : Blo 1505449 1505523 := bstep (se 1 (by rfl) ⟨1129142, by rfl⟩ : syracuseStep 1505523 = 2258285) B2258285
theorem B1693939 : Blo 1505449 1693939 := bstep (se 1 (by rfl) ⟨1270454, by rfl⟩ : syracuseStep 1693939 = 2540909) B2540909
theorem B2144513 : Blo 1505449 2144513 := bstep (se 2 (by rfl) ⟨804192, by rfl⟩ : syracuseStep 2144513 = 1608385) B1608385
theorem B1505539 : Blo 1505449 1505539 := bstep (se 1 (by rfl) ⟨1129154, by rfl⟩ : syracuseStep 1505539 = 2258309) B2258309
theorem B2259203 : Blo 1505449 2259203 := bstep (se 1 (by rfl) ⟨1694402, by rfl⟩ : syracuseStep 2259203 = 3388805) B3388805
theorem B1505555 : Blo 1505449 1505555 := bstep (se 1 (by rfl) ⟨1129166, by rfl⟩ : syracuseStep 1505555 = 2258333) B2258333
theorem B2259233 : Blo 1505449 2259233 := bstep (se 2 (by rfl) ⟨847212, by rfl⟩ : syracuseStep 2259233 = 1694425) B1694425
theorem B1505571 : Blo 1505449 1505571 := bstep (se 1 (by rfl) ⟨1129178, by rfl⟩ : syracuseStep 1505571 = 2258357) B2258357
theorem B1505587 : Blo 1505449 1505587 := bstep (se 1 (by rfl) ⟨1129190, by rfl⟩ : syracuseStep 1505587 = 2258381) B2258381
theorem B2259251 : Blo 1505449 2259251 := bstep (se 1 (by rfl) ⟨1694438, by rfl⟩ : syracuseStep 2259251 = 3388877) B3388877
theorem B1505603 : Blo 1505449 1505603 := bstep (se 1 (by rfl) ⟨1129202, by rfl⟩ : syracuseStep 1505603 = 2258405) B2258405
theorem B2259281 : Blo 1505449 2259281 := bstep (se 2 (by rfl) ⟨847230, by rfl⟩ : syracuseStep 2259281 = 1694461) B1694461
theorem B2144593 : Blo 1505449 2144593 := bstep (se 2 (by rfl) ⟨804222, by rfl⟩ : syracuseStep 2144593 = 1608445) B1608445
theorem B1505619 : Blo 1505449 1505619 := bstep (se 1 (by rfl) ⟨1129214, by rfl⟩ : syracuseStep 1505619 = 2258429) B2258429
theorem B3389777 : Blo 1505449 3389777 := bstep (se 2 (by rfl) ⟨1271166, by rfl⟩ : syracuseStep 3389777 = 2542333) B2542333
theorem B1505635 : Blo 1505449 1505635 := bstep (se 1 (by rfl) ⟨1129226, by rfl⟩ : syracuseStep 1505635 = 2258453) B2258453
theorem B2259299 : Blo 1505449 2259299 := bstep (se 1 (by rfl) ⟨1694474, by rfl⟩ : syracuseStep 2259299 = 3388949) B3388949
theorem B3389795 : Blo 1505449 3389795 := bstep (se 1 (by rfl) ⟨2542346, by rfl⟩ : syracuseStep 3389795 = 5084693) B5084693
theorem B1505651 : Blo 1505449 1505651 := bstep (se 1 (by rfl) ⟨1129238, by rfl⟩ : syracuseStep 1505651 = 2258477) B2258477
theorem B1907059 : Blo 1505449 1907059 := bstep (se 1 (by rfl) ⟨1430294, by rfl⟩ : syracuseStep 1907059 = 2860589) B2860589
theorem B2259329 : Blo 1505449 2259329 := bstep (se 2 (by rfl) ⟨847248, by rfl⟩ : syracuseStep 2259329 = 1694497) B1694497
theorem B1505667 : Blo 1505449 1505667 := bstep (se 1 (by rfl) ⟨1129250, by rfl⟩ : syracuseStep 1505667 = 2258501) B2258501
theorem B1694083 : Blo 1505449 1694083 := bstep (se 1 (by rfl) ⟨1270562, by rfl⟩ : syracuseStep 1694083 = 2541125) B2541125
theorem B1505683 : Blo 1505449 1505683 := bstep (se 1 (by rfl) ⟨1129262, by rfl⟩ : syracuseStep 1505683 = 2258525) B2258525
theorem B2259347 : Blo 1505449 2259347 := bstep (se 1 (by rfl) ⟨1694510, by rfl⟩ : syracuseStep 2259347 = 3389021) B3389021
theorem B1505699 : Blo 1505449 1505699 := bstep (se 1 (by rfl) ⟨1129274, by rfl⟩ : syracuseStep 1505699 = 2258549) B2258549
theorem B8575409 : Blo 1505449 8575409 := bstep (se 2 (by rfl) ⟨3215778, by rfl⟩ : syracuseStep 8575409 = 6431557) B6431557
theorem B2259377 : Blo 1505449 2259377 := bstep (se 2 (by rfl) ⟨847266, by rfl⟩ : syracuseStep 2259377 = 1694533) B1694533
theorem B1505715 : Blo 1505449 1505715 := bstep (se 1 (by rfl) ⟨1129286, by rfl⟩ : syracuseStep 1505715 = 2258573) B2258573
theorem B1505731 : Blo 1505449 1505731 := bstep (se 1 (by rfl) ⟨1129298, by rfl⟩ : syracuseStep 1505731 = 2258597) B2258597
theorem B2259395 : Blo 1505449 2259395 := bstep (se 1 (by rfl) ⟨1694546, by rfl⟩ : syracuseStep 2259395 = 3389093) B3389093
theorem B1505747 : Blo 1505449 1505747 := bstep (se 1 (by rfl) ⟨1129310, by rfl⟩ : syracuseStep 1505747 = 2258621) B2258621
theorem B2259425 : Blo 1505449 2259425 := bstep (se 2 (by rfl) ⟨847284, by rfl⟩ : syracuseStep 2259425 = 1694569) B1694569
theorem B1505763 : Blo 1505449 1505763 := bstep (se 1 (by rfl) ⟨1129322, by rfl⟩ : syracuseStep 1505763 = 2258645) B2258645
theorem B1505779 : Blo 1505449 1505779 := bstep (se 1 (by rfl) ⟨1129334, by rfl⟩ : syracuseStep 1505779 = 2258669) B2258669
theorem B2259443 : Blo 1505449 2259443 := bstep (se 1 (by rfl) ⟨1694582, by rfl⟩ : syracuseStep 2259443 = 3389165) B3389165
theorem B1505795 : Blo 1505449 1505795 := bstep (se 1 (by rfl) ⟨1129346, by rfl⟩ : syracuseStep 1505795 = 2258693) B2258693
theorem B2259473 : Blo 1505449 2259473 := bstep (se 2 (by rfl) ⟨847302, by rfl⟩ : syracuseStep 2259473 = 1694605) B1694605
theorem B1505811 : Blo 1505449 1505811 := bstep (se 1 (by rfl) ⟨1129358, by rfl⟩ : syracuseStep 1505811 = 2258717) B2258717
theorem B1694227 : Blo 1505449 1694227 := bstep (se 1 (by rfl) ⟨1270670, by rfl⟩ : syracuseStep 1694227 = 2541341) B2541341
theorem B1505827 : Blo 1505449 1505827 := bstep (se 1 (by rfl) ⟨1129370, by rfl⟩ : syracuseStep 1505827 = 2258741) B2258741
theorem B2259491 : Blo 1505449 2259491 := bstep (se 1 (by rfl) ⟨1694618, by rfl⟩ : syracuseStep 2259491 = 3389237) B3389237
theorem B1505843 : Blo 1505449 1505843 := bstep (se 1 (by rfl) ⟨1129382, by rfl⟩ : syracuseStep 1505843 = 2258765) B2258765
theorem B2259521 : Blo 1505449 2259521 := bstep (se 2 (by rfl) ⟨847320, by rfl⟩ : syracuseStep 2259521 = 1694641) B1694641
theorem B1505859 : Blo 1505449 1505859 := bstep (se 1 (by rfl) ⟨1129394, by rfl⟩ : syracuseStep 1505859 = 2258789) B2258789
theorem B5085773 : Blo 1505449 5085773 := bstep (se 3 (by rfl) ⟨953582, by rfl⟩ : syracuseStep 5085773 = 1907165) B1907165
theorem B1505875 : Blo 1505449 1505875 := bstep (se 1 (by rfl) ⟨1129406, by rfl⟩ : syracuseStep 1505875 = 2258813) B2258813
theorem B2259539 : Blo 1505449 2259539 := bstep (se 1 (by rfl) ⟨1694654, by rfl⟩ : syracuseStep 2259539 = 3389309) B3389309
theorem B1505891 : Blo 1505449 1505891 := bstep (se 1 (by rfl) ⟨1129418, by rfl⟩ : syracuseStep 1505891 = 2258837) B2258837
theorem B2259569 : Blo 1505449 2259569 := bstep (se 2 (by rfl) ⟨847338, by rfl⟩ : syracuseStep 2259569 = 1694677) B1694677
theorem B3390065 : Blo 1505449 3390065 := bstep (se 2 (by rfl) ⟨1271274, by rfl⟩ : syracuseStep 3390065 = 2542549) B2542549
theorem B1505907 : Blo 1505449 1505907 := bstep (se 1 (by rfl) ⟨1129430, by rfl⟩ : syracuseStep 1505907 = 2258861) B2258861
theorem B1505923 : Blo 1505449 1505923 := bstep (se 1 (by rfl) ⟨1129442, by rfl⟩ : syracuseStep 1505923 = 2258885) B2258885
theorem B2259587 : Blo 1505449 2259587 := bstep (se 1 (by rfl) ⟨1694690, by rfl⟩ : syracuseStep 2259587 = 3389381) B3389381
theorem B3390083 : Blo 1505449 3390083 := bstep (se 1 (by rfl) ⟨2542562, by rfl⟩ : syracuseStep 3390083 = 5085125) B5085125
theorem B5085827 : Blo 1505449 5085827 := bstep (se 1 (by rfl) ⟨3814370, by rfl⟩ : syracuseStep 5085827 = 7628741) B7628741
theorem B4291213 : Blo 1505449 4291213 := bstep (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) B1609205
theorem B1505939 : Blo 1505449 1505939 := bstep (se 1 (by rfl) ⟨1129454, by rfl⟩ : syracuseStep 1505939 = 2258909) B2258909
theorem B2259617 : Blo 1505449 2259617 := bstep (se 2 (by rfl) ⟨847356, by rfl⟩ : syracuseStep 2259617 = 1694713) B1694713
theorem B1505955 : Blo 1505449 1505955 := bstep (se 1 (by rfl) ⟨1129466, by rfl⟩ : syracuseStep 1505955 = 2258933) B2258933
theorem B1694371 : Blo 1505449 1694371 := bstep (se 1 (by rfl) ⟨1270778, by rfl⟩ : syracuseStep 1694371 = 2541557) B2541557
theorem B3865265 : Blo 1505449 3865265 := bstep (se 2 (by rfl) ⟨1449474, by rfl⟩ : syracuseStep 3865265 = 2898949) B2898949
theorem B1505971 : Blo 1505449 1505971 := bstep (se 1 (by rfl) ⟨1129478, by rfl⟩ : syracuseStep 1505971 = 2258957) B2258957
theorem B2259635 : Blo 1505449 2259635 := bstep (se 1 (by rfl) ⟨1694726, by rfl⟩ : syracuseStep 2259635 = 3389453) B3389453
theorem B1505987 : Blo 1505449 1505987 := bstep (se 1 (by rfl) ⟨1129490, by rfl⟩ : syracuseStep 1505987 = 2258981) B2258981
theorem B2259665 : Blo 1505449 2259665 := bstep (se 2 (by rfl) ⟨847374, by rfl⟩ : syracuseStep 2259665 = 1694749) B1694749
theorem B1506003 : Blo 1505449 1506003 := bstep (se 1 (by rfl) ⟨1129502, by rfl⟩ : syracuseStep 1506003 = 2259005) B2259005
theorem B1506019 : Blo 1505449 1506019 := bstep (se 1 (by rfl) ⟨1129514, by rfl⟩ : syracuseStep 1506019 = 2259029) B2259029
theorem B2259683 : Blo 1505449 2259683 := bstep (se 1 (by rfl) ⟨1694762, by rfl⟩ : syracuseStep 2259683 = 3389525) B3389525
theorem B1506035 : Blo 1505449 1506035 := bstep (se 1 (by rfl) ⟨1129526, by rfl⟩ : syracuseStep 1506035 = 2259053) B2259053
theorem B2259713 : Blo 1505449 2259713 := bstep (se 2 (by rfl) ⟨847392, by rfl⟩ : syracuseStep 2259713 = 1694785) B1694785
theorem B1506051 : Blo 1505449 1506051 := bstep (se 1 (by rfl) ⟨1129538, by rfl⟩ : syracuseStep 1506051 = 2259077) B2259077
theorem B1506067 : Blo 1505449 1506067 := bstep (se 1 (by rfl) ⟨1129550, by rfl⟩ : syracuseStep 1506067 = 2259101) B2259101
theorem B2259731 : Blo 1505449 2259731 := bstep (se 1 (by rfl) ⟨1694798, by rfl⟩ : syracuseStep 2259731 = 3389597) B3389597
theorem B1506083 : Blo 1505449 1506083 := bstep (se 1 (by rfl) ⟨1129562, by rfl⟩ : syracuseStep 1506083 = 2259125) B2259125
theorem B2259761 : Blo 1505449 2259761 := bstep (se 2 (by rfl) ⟨847410, by rfl⟩ : syracuseStep 2259761 = 1694821) B1694821
theorem B1506099 : Blo 1505449 1506099 := bstep (se 1 (by rfl) ⟨1129574, by rfl⟩ : syracuseStep 1506099 = 2259149) B2259149
theorem B1694515 : Blo 1505449 1694515 := bstep (se 1 (by rfl) ⟨1270886, by rfl⟩ : syracuseStep 1694515 = 2541773) B2541773
theorem B1506115 : Blo 1505449 1506115 := bstep (se 1 (by rfl) ⟨1129586, by rfl⟩ : syracuseStep 1506115 = 2259173) B2259173
theorem B2259779 : Blo 1505449 2259779 := bstep (se 1 (by rfl) ⟨1694834, by rfl⟩ : syracuseStep 2259779 = 3389669) B3389669
theorem B1506131 : Blo 1505449 1506131 := bstep (se 1 (by rfl) ⟨1129598, by rfl⟩ : syracuseStep 1506131 = 2259197) B2259197
theorem B2259809 : Blo 1505449 2259809 := bstep (se 2 (by rfl) ⟨847428, by rfl⟩ : syracuseStep 2259809 = 1694857) B1694857
theorem B1506147 : Blo 1505449 1506147 := bstep (se 1 (by rfl) ⟨1129610, by rfl⟩ : syracuseStep 1506147 = 2259221) B2259221
theorem B1506163 : Blo 1505449 1506163 := bstep (se 1 (by rfl) ⟨1129622, by rfl⟩ : syracuseStep 1506163 = 2259245) B2259245
theorem B2259827 : Blo 1505449 2259827 := bstep (se 1 (by rfl) ⟨1694870, by rfl⟩ : syracuseStep 2259827 = 3389741) B3389741
theorem B1506179 : Blo 1505449 1506179 := bstep (se 1 (by rfl) ⟨1129634, by rfl⟩ : syracuseStep 1506179 = 2259269) B2259269
theorem B2259857 : Blo 1505449 2259857 := bstep (se 2 (by rfl) ⟨847446, by rfl⟩ : syracuseStep 2259857 = 1694893) B1694893
theorem B3390353 : Blo 1505449 3390353 := bstep (se 2 (by rfl) ⟨1271382, by rfl⟩ : syracuseStep 3390353 = 2542765) B2542765
theorem B1506195 : Blo 1505449 1506195 := bstep (se 1 (by rfl) ⟨1129646, by rfl⟩ : syracuseStep 1506195 = 2259293) B2259293
theorem B1506211 : Blo 1505449 1506211 := bstep (se 1 (by rfl) ⟨1129658, by rfl⟩ : syracuseStep 1506211 = 2259317) B2259317
theorem B2259875 : Blo 1505449 2259875 := bstep (se 1 (by rfl) ⟨1694906, by rfl⟩ : syracuseStep 2259875 = 3389813) B3389813
theorem B3390371 : Blo 1505449 3390371 := bstep (se 1 (by rfl) ⟨2542778, by rfl⟩ : syracuseStep 3390371 = 5085557) B5085557
theorem B4578221 : Blo 1505449 4578221 := bstep (se 3 (by rfl) ⟨858416, by rfl⟩ : syracuseStep 4578221 = 1716833) B1716833
theorem B1506227 : Blo 1505449 1506227 := bstep (se 1 (by rfl) ⟨1129670, by rfl⟩ : syracuseStep 1506227 = 2259341) B2259341
theorem B4242353 : Blo 1505449 4242353 := bstep (se 2 (by rfl) ⟨1590882, by rfl⟩ : syracuseStep 4242353 = 3181765) B3181765
theorem B2259905 : Blo 1505449 2259905 := bstep (se 2 (by rfl) ⟨847464, by rfl⟩ : syracuseStep 2259905 = 1694929) B1694929
theorem B1506243 : Blo 1505449 1506243 := bstep (se 1 (by rfl) ⟨1129682, by rfl⟩ : syracuseStep 1506243 = 2259365) B2259365
theorem B1694659 : Blo 1505449 1694659 := bstep (se 1 (by rfl) ⟨1270994, by rfl⟩ : syracuseStep 1694659 = 2541989) B2541989
theorem B1506259 : Blo 1505449 1506259 := bstep (se 1 (by rfl) ⟨1129694, by rfl⟩ : syracuseStep 1506259 = 2259389) B2259389
theorem B2259923 : Blo 1505449 2259923 := bstep (se 1 (by rfl) ⟨1694942, by rfl⟩ : syracuseStep 2259923 = 3389885) B3389885
theorem B1506275 : Blo 1505449 1506275 := bstep (se 1 (by rfl) ⟨1129706, by rfl⟩ : syracuseStep 1506275 = 2259413) B2259413
theorem B2259953 : Blo 1505449 2259953 := bstep (se 2 (by rfl) ⟨847482, by rfl⟩ : syracuseStep 2259953 = 1694965) B1694965
theorem B1506291 : Blo 1505449 1506291 := bstep (se 1 (by rfl) ⟨1129718, by rfl⟩ : syracuseStep 1506291 = 2259437) B2259437
theorem B1506307 : Blo 1505449 1506307 := bstep (se 1 (by rfl) ⟨1129730, by rfl⟩ : syracuseStep 1506307 = 2259461) B2259461
theorem B2259971 : Blo 1505449 2259971 := bstep (se 1 (by rfl) ⟨1694978, by rfl⟩ : syracuseStep 2259971 = 3389957) B3389957
theorem B1506323 : Blo 1505449 1506323 := bstep (se 1 (by rfl) ⟨1129742, by rfl⟩ : syracuseStep 1506323 = 2259485) B2259485
theorem B2260001 : Blo 1505449 2260001 := bstep (se 2 (by rfl) ⟨847500, by rfl⟩ : syracuseStep 2260001 = 1695001) B1695001
theorem B1506339 : Blo 1505449 1506339 := bstep (se 1 (by rfl) ⟨1129754, by rfl⟩ : syracuseStep 1506339 = 2259509) B2259509
theorem B1506355 : Blo 1505449 1506355 := bstep (se 1 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 1506355 = 2259533) B2259533
theorem B2260019 : Blo 1505449 2260019 := bstep (se 1 (by rfl) ⟨1695014, by rfl⟩ : syracuseStep 2260019 = 3390029) B3390029
theorem B1506371 : Blo 1505449 1506371 := bstep (se 1 (by rfl) ⟨1129778, by rfl⟩ : syracuseStep 1506371 = 2259557) B2259557
theorem B2260049 : Blo 1505449 2260049 := bstep (se 2 (by rfl) ⟨847518, by rfl⟩ : syracuseStep 2260049 = 1695037) B1695037
theorem B1506387 : Blo 1505449 1506387 := bstep (se 1 (by rfl) ⟨1129790, by rfl⟩ : syracuseStep 1506387 = 2259581) B2259581
theorem B1694803 : Blo 1505449 1694803 := bstep (se 1 (by rfl) ⟨1271102, by rfl⟩ : syracuseStep 1694803 = 2542205) B2542205
theorem B1506403 : Blo 1505449 1506403 := bstep (se 1 (by rfl) ⟨1129802, by rfl⟩ : syracuseStep 1506403 = 2259605) B2259605
theorem B4643939 : Blo 1505449 4643939 := bstep (se 1 (by rfl) ⟨3482954, by rfl⟩ : syracuseStep 4643939 = 6965909) B6965909
theorem B2260067 : Blo 1505449 2260067 := bstep (se 1 (by rfl) ⟨1695050, by rfl⟩ : syracuseStep 2260067 = 3390101) B3390101
theorem B2145379 : Blo 1505449 2145379 := bstep (se 1 (by rfl) ⟨1609034, by rfl⟩ : syracuseStep 2145379 = 3218069) B3218069
theorem B4070513 : Blo 1505449 4070513 := bstep (se 2 (by rfl) ⟨1526442, by rfl⟩ : syracuseStep 4070513 = 3052885) B3052885
theorem B1506419 : Blo 1505449 1506419 := bstep (se 1 (by rfl) ⟨1129814, by rfl⟩ : syracuseStep 1506419 = 2259629) B2259629
theorem B2260097 : Blo 1505449 2260097 := bstep (se 2 (by rfl) ⟨847536, by rfl⟩ : syracuseStep 2260097 = 1695073) B1695073
theorem B1506435 : Blo 1505449 1506435 := bstep (se 1 (by rfl) ⟨1129826, by rfl⟩ : syracuseStep 1506435 = 2259653) B2259653
theorem B1506451 : Blo 1505449 1506451 := bstep (se 1 (by rfl) ⟨1129838, by rfl⟩ : syracuseStep 1506451 = 2259677) B2259677
theorem B2260115 : Blo 1505449 2260115 := bstep (se 1 (by rfl) ⟨1695086, by rfl⟩ : syracuseStep 2260115 = 3390173) B3390173
theorem B1506467 : Blo 1505449 1506467 := bstep (se 1 (by rfl) ⟨1129850, by rfl⟩ : syracuseStep 1506467 = 2259701) B2259701
theorem B2260145 : Blo 1505449 2260145 := bstep (se 2 (by rfl) ⟨847554, by rfl⟩ : syracuseStep 2260145 = 1695109) B1695109
theorem B1809587 : Blo 1505449 1809587 := bstep (se 1 (by rfl) ⟨1357190, by rfl⟩ : syracuseStep 1809587 = 2714381) B2714381
theorem B1506483 : Blo 1505449 1506483 := bstep (se 1 (by rfl) ⟨1129862, by rfl⟩ : syracuseStep 1506483 = 2259725) B2259725
theorem B1506499 : Blo 1505449 1506499 := bstep (se 1 (by rfl) ⟨1129874, by rfl⟩ : syracuseStep 1506499 = 2259749) B2259749
theorem B2260163 : Blo 1505449 2260163 := bstep (se 1 (by rfl) ⟨1695122, by rfl⟩ : syracuseStep 2260163 = 3390245) B3390245
theorem B1506515 : Blo 1505449 1506515 := bstep (se 1 (by rfl) ⟨1129886, by rfl⟩ : syracuseStep 1506515 = 2259773) B2259773
theorem B2260193 : Blo 1505449 2260193 := bstep (se 2 (by rfl) ⟨847572, by rfl⟩ : syracuseStep 2260193 = 1695145) B1695145
theorem B1506531 : Blo 1505449 1506531 := bstep (se 1 (by rfl) ⟨1129898, by rfl⟩ : syracuseStep 1506531 = 2259797) B2259797
theorem B1694947 : Blo 1505449 1694947 := bstep (se 1 (by rfl) ⟨1271210, by rfl⟩ : syracuseStep 1694947 = 2542421) B2542421
theorem B49544419 : Blo 1505449 49544419 := bstep (se 1 (by rfl) ⟨37158314, by rfl⟩ : syracuseStep 49544419 = 74316629) B74316629
theorem B1506547 : Blo 1505449 1506547 := bstep (se 1 (by rfl) ⟨1129910, by rfl⟩ : syracuseStep 1506547 = 2259821) B2259821
theorem B2260211 : Blo 1505449 2260211 := bstep (se 1 (by rfl) ⟨1695158, by rfl⟩ : syracuseStep 2260211 = 3390317) B3390317
theorem B1506563 : Blo 1505449 1506563 := bstep (se 1 (by rfl) ⟨1129922, by rfl⟩ : syracuseStep 1506563 = 2259845) B2259845
theorem B2858257 : Blo 1505449 2858257 := bstep (se 2 (by rfl) ⟨1071846, by rfl⟩ : syracuseStep 2858257 = 2143693) B2143693
theorem B2260241 : Blo 1505449 2260241 := bstep (se 2 (by rfl) ⟨847590, by rfl⟩ : syracuseStep 2260241 = 1695181) B1695181
theorem B1506579 : Blo 1505449 1506579 := bstep (se 1 (by rfl) ⟨1129934, by rfl⟩ : syracuseStep 1506579 = 2259869) B2259869
theorem B1506595 : Blo 1505449 1506595 := bstep (se 1 (by rfl) ⟨1129946, by rfl⟩ : syracuseStep 1506595 = 2259893) B2259893
theorem B2260259 : Blo 1505449 2260259 := bstep (se 1 (by rfl) ⟨1695194, by rfl⟩ : syracuseStep 2260259 = 3390389) B3390389
theorem B1506611 : Blo 1505449 1506611 := bstep (se 1 (by rfl) ⟨1129958, by rfl⟩ : syracuseStep 1506611 = 2259917) B2259917
theorem B2260289 : Blo 1505449 2260289 := bstep (se 2 (by rfl) ⟨847608, by rfl⟩ : syracuseStep 2260289 = 1695217) B1695217
theorem B1506627 : Blo 1505449 1506627 := bstep (se 1 (by rfl) ⟨1129970, by rfl⟩ : syracuseStep 1506627 = 2259941) B2259941
theorem B1506643 : Blo 1505449 1506643 := bstep (se 1 (by rfl) ⟨1129982, by rfl⟩ : syracuseStep 1506643 = 2259965) B2259965
theorem B2260307 : Blo 1505449 2260307 := bstep (se 1 (by rfl) ⟨1695230, by rfl⟩ : syracuseStep 2260307 = 3390461) B3390461
theorem B1506659 : Blo 1505449 1506659 := bstep (se 1 (by rfl) ⟨1129994, by rfl⟩ : syracuseStep 1506659 = 2259989) B2259989
theorem B2260337 : Blo 1505449 2260337 := bstep (se 2 (by rfl) ⟨847626, by rfl⟩ : syracuseStep 2260337 = 1695253) B1695253
theorem B1506675 : Blo 1505449 1506675 := bstep (se 1 (by rfl) ⟨1130006, by rfl⟩ : syracuseStep 1506675 = 2260013) B2260013
theorem B1695091 : Blo 1505449 1695091 := bstep (se 1 (by rfl) ⟨1271318, by rfl⟩ : syracuseStep 1695091 = 2542637) B2542637
theorem B1506691 : Blo 1505449 1506691 := bstep (se 1 (by rfl) ⟨1130018, by rfl⟩ : syracuseStep 1506691 = 2260037) B2260037
theorem B2260355 : Blo 1505449 2260355 := bstep (se 1 (by rfl) ⟨1695266, by rfl⟩ : syracuseStep 2260355 = 3390533) B3390533
theorem B1506707 : Blo 1505449 1506707 := bstep (se 1 (by rfl) ⟨1130030, by rfl⟩ : syracuseStep 1506707 = 2260061) B2260061
theorem B2260385 : Blo 1505449 2260385 := bstep (se 2 (by rfl) ⟨847644, by rfl⟩ : syracuseStep 2260385 = 1695289) B1695289
theorem B5717411 : Blo 1505449 5717411 := bstep (se 1 (by rfl) ⟨4288058, by rfl⟩ : syracuseStep 5717411 = 8576117) B8576117
theorem B2751907 : Blo 1505449 2751907 := bstep (se 1 (by rfl) ⟨2063930, by rfl⟩ : syracuseStep 2751907 = 4127861) B4127861
theorem B1506723 : Blo 1505449 1506723 := bstep (se 1 (by rfl) ⟨1130042, by rfl⟩ : syracuseStep 1506723 = 2260085) B2260085
theorem B5717425 : Blo 1505449 5717425 := bstep (se 2 (by rfl) ⟨2144034, by rfl⟩ : syracuseStep 5717425 = 4288069) B4288069
theorem B1506739 : Blo 1505449 1506739 := bstep (se 1 (by rfl) ⟨1130054, by rfl⟩ : syracuseStep 1506739 = 2260109) B2260109
theorem B2260403 : Blo 1505449 2260403 := bstep (se 1 (by rfl) ⟨1695302, by rfl⟩ : syracuseStep 2260403 = 3390605) B3390605
theorem B4824515 : Blo 1505449 4824515 := bstep (se 1 (by rfl) ⟨3618386, by rfl⟩ : syracuseStep 4824515 = 7236773) B7236773
theorem B1506755 : Blo 1505449 1506755 := bstep (se 1 (by rfl) ⟨1130066, by rfl⟩ : syracuseStep 1506755 = 2260133) B2260133
theorem B48315845 : Blo 1505449 48315845 := bstep (se 4 (by rfl) ⟨4529610, by rfl⟩ : syracuseStep 48315845 = 9059221) B9059221
theorem B1506771 : Blo 1505449 1506771 := bstep (se 1 (by rfl) ⟨1130078, by rfl⟩ : syracuseStep 1506771 = 2260157) B2260157
theorem B1506787 : Blo 1505449 1506787 := bstep (se 1 (by rfl) ⟨1130090, by rfl⟩ : syracuseStep 1506787 = 2260181) B2260181
theorem B1506803 : Blo 1505449 1506803 := bstep (se 1 (by rfl) ⟨1130102, by rfl⟩ : syracuseStep 1506803 = 2260205) B2260205
theorem B1506819 : Blo 1505449 1506819 := bstep (se 1 (by rfl) ⟨1130114, by rfl⟩ : syracuseStep 1506819 = 2260229) B2260229
theorem B1695235 : Blo 1505449 1695235 := bstep (se 1 (by rfl) ⟨1271426, by rfl⟩ : syracuseStep 1695235 = 2542853) B2542853
theorem B1506835 : Blo 1505449 1506835 := bstep (se 1 (by rfl) ⟨1130126, by rfl⟩ : syracuseStep 1506835 = 2260253) B2260253
theorem B1506851 : Blo 1505449 1506851 := bstep (se 1 (by rfl) ⟨1130138, by rfl⟩ : syracuseStep 1506851 = 2260277) B2260277
theorem B1506867 : Blo 1505449 1506867 := bstep (se 1 (by rfl) ⟨1130150, by rfl⟩ : syracuseStep 1506867 = 2260301) B2260301
theorem B4824643 : Blo 1505449 4824643 := bstep (se 1 (by rfl) ⟨3618482, by rfl⟩ : syracuseStep 4824643 = 7236965) B7236965
theorem B1506883 : Blo 1505449 1506883 := bstep (se 1 (by rfl) ⟨1130162, by rfl⟩ : syracuseStep 1506883 = 2260325) B2260325
theorem B1506899 : Blo 1505449 1506899 := bstep (se 1 (by rfl) ⟨1130174, by rfl⟩ : syracuseStep 1506899 = 2260349) B2260349
theorem B1506915 : Blo 1505449 1506915 := bstep (se 1 (by rfl) ⟨1130186, by rfl⟩ : syracuseStep 1506915 = 2260373) B2260373
theorem B1506931 : Blo 1505449 1506931 := bstep (se 1 (by rfl) ⟨1130198, by rfl⟩ : syracuseStep 1506931 = 2260397) B2260397
theorem B1506947 : Blo 1505449 1506947 := bstep (se 1 (by rfl) ⟨1130210, by rfl⟩ : syracuseStep 1506947 = 2260421) B2260421
theorem B4824785 : Blo 1505449 4824785 := bstep (se 2 (by rfl) ⟨1809294, by rfl⟩ : syracuseStep 4824785 = 3618589) B3618589
theorem B8257315 : Blo 1505449 8257315 := bstep (se 1 (by rfl) ⟨6192986, by rfl⟩ : syracuseStep 8257315 = 12385973) B12385973
theorem B4824899 : Blo 1505449 4824899 := bstep (se 1 (by rfl) ⟨3618674, by rfl⟩ : syracuseStep 4824899 = 7237349) B7237349
theorem B3727171 : Blo 1505449 3727171 := bstep (se 1 (by rfl) ⟨2795378, by rfl⟩ : syracuseStep 3727171 = 5590757) B5590757
theorem B8576867 : Blo 1505449 8576867 := bstep (se 1 (by rfl) ⟨6432650, by rfl⟩ : syracuseStep 8576867 = 12865301) B12865301
theorem B7626797 : Blo 1505449 7626797 := bstep (se 3 (by rfl) ⟨1430024, by rfl⟩ : syracuseStep 7626797 = 2860049) B2860049
theorem B3260555 : Blo 1505449 3260555 := bstep (se 1 (by rfl) ⟨2445416, by rfl⟩ : syracuseStep 3260555 = 4890833) B4890833
theorem B25092301 : Blo 1505449 25092301 := bstep (se 3 (by rfl) ⟨4704806, by rfl⟩ : syracuseStep 25092301 = 9409613) B9409613
theorem B2859275 : Blo 1505449 2859275 := bstep (se 1 (by rfl) ⟨2144456, by rfl⟩ : syracuseStep 2859275 = 4288913) B4288913
theorem B2859457 : Blo 1505449 2859457 := bstep (se 2 (by rfl) ⟨1072296, by rfl⟩ : syracuseStep 2859457 = 2144593) B2144593
theorem B4579787 : Blo 1505449 4579787 := bstep (se 1 (by rfl) ⟨3434840, by rfl⟩ : syracuseStep 4579787 = 6869681) B6869681
theorem B4825565 : Blo 1505449 4825565 := bstep (se 3 (by rfl) ⟨904793, by rfl⟩ : syracuseStep 4825565 = 1809587) B1809587
theorem B5718701 : Blo 1505449 5718701 := bstep (se 3 (by rfl) ⟨1072256, by rfl⟩ : syracuseStep 5718701 = 2144513) B2144513
theorem B8143577 : Blo 1505449 8143577 := bstep (se 2 (by rfl) ⟨3053841, by rfl⟩ : syracuseStep 8143577 = 6107683) B6107683
theorem B2859799 : Blo 1505449 2859799 := bstep (se 1 (by rfl) ⟨2144849, by rfl⟩ : syracuseStep 2859799 = 4289699) B4289699
theorem B25109365 : Blo 1505449 25109365 := bstep (se 5 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 25109365 = 2354003) B2354003
theorem B2860019 : Blo 1505449 2860019 := bstep (se 1 (by rfl) ⟨2145014, by rfl⟩ : syracuseStep 2860019 = 4290029) B4290029
theorem B2540747 : Blo 1505449 2540747 := bstep (se 1 (by rfl) ⟨1905560, by rfl⟩ : syracuseStep 2540747 = 3811121) B3811121
theorem B2860247 : Blo 1505449 2860247 := bstep (se 1 (by rfl) ⟨2145185, by rfl⟩ : syracuseStep 2860247 = 4290371) B4290371
theorem B2540875 : Blo 1505449 2540875 := bstep (se 1 (by rfl) ⟨1905656, by rfl⟩ : syracuseStep 2540875 = 3811313) B3811313
theorem B48850289 : Blo 1505449 48850289 := bstep (se 2 (by rfl) ⟨18318858, by rfl⟩ : syracuseStep 48850289 = 36637717) B36637717
theorem B6432173 : Blo 1505449 6432173 := bstep (se 3 (by rfl) ⟨1206032, by rfl⟩ : syracuseStep 6432173 = 2412065) B2412065
theorem B2713025 : Blo 1505449 2713025 := bstep (se 2 (by rfl) ⟨1017384, by rfl⟩ : syracuseStep 2713025 = 2034769) B2034769
theorem B2541017 : Blo 1505449 2541017 := bstep (se 2 (by rfl) ⟨952881, by rfl⟩ : syracuseStep 2541017 = 1905763) B1905763
theorem B2860505 : Blo 1505449 2860505 := bstep (se 2 (by rfl) ⟨1072689, by rfl⟩ : syracuseStep 2860505 = 2145379) B2145379
theorem B2541145 : Blo 1505449 2541145 := bstep (se 2 (by rfl) ⟨952929, by rfl⟩ : syracuseStep 2541145 = 1905859) B1905859
theorem B3811009 : Blo 1505449 3811009 := bstep (se 2 (by rfl) ⟨1429128, by rfl⟩ : syracuseStep 3811009 = 2858257) B2858257
theorem B12871385 : Blo 1505449 12871385 := bstep (se 2 (by rfl) ⟨4826769, by rfl⟩ : syracuseStep 12871385 = 9653539) B9653539
theorem B21718961 : Blo 1505449 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B6965185 : Blo 1505449 6965185 := bstep (se 2 (by rfl) ⟨2611944, by rfl⟩ : syracuseStep 6965185 = 5223889) B5223889
theorem B8579033 : Blo 1505449 8579033 := bstep (se 2 (by rfl) ⟨3217137, by rfl⟩ : syracuseStep 8579033 = 6434275) B6434275
theorem B5720129 : Blo 1505449 5720129 := bstep (se 2 (by rfl) ⟨2145048, by rfl⟩ : syracuseStep 5720129 = 4290097) B4290097
theorem B2713675 : Blo 1505449 2713675 := bstep (se 1 (by rfl) ⟨2035256, by rfl⟩ : syracuseStep 2713675 = 4070513) B4070513
theorem B6432857 : Blo 1505449 6432857 := bstep (se 2 (by rfl) ⟨2412321, by rfl⟩ : syracuseStep 6432857 = 4824643) B4824643
theorem B12208229 : Blo 1505449 12208229 := bstep (se 4 (by rfl) ⟨1144521, by rfl⟩ : syracuseStep 12208229 = 2289043) B2289043
theorem B2541719 : Blo 1505449 2541719 := bstep (se 1 (by rfl) ⟨1906289, by rfl⟩ : syracuseStep 2541719 = 3812579) B3812579
theorem B5081291 : Blo 1505449 5081291 := bstep (se 1 (by rfl) ⟨3810968, by rfl⟩ : syracuseStep 5081291 = 7621937) B7621937
theorem B3811607 : Blo 1505449 3811607 := bstep (se 1 (by rfl) ⟨2858705, by rfl⟩ : syracuseStep 3811607 = 5717411) B5717411
theorem B2541847 : Blo 1505449 2541847 := bstep (se 1 (by rfl) ⟨1906385, by rfl⟩ : syracuseStep 2541847 = 3812771) B3812771
theorem B5081561 : Blo 1505449 5081561 := bstep (se 2 (by rfl) ⟨1905585, by rfl⟩ : syracuseStep 5081561 = 3811171) B3811171
theorem B5425937 : Blo 1505449 5425937 := bstep (se 2 (by rfl) ⟨2034726, by rfl⟩ : syracuseStep 5425937 = 4069453) B4069453
theorem B7621451 : Blo 1505449 7621451 := bstep (se 1 (by rfl) ⟨5716088, by rfl⟩ : syracuseStep 7621451 = 11432177) B11432177
theorem B1608535 : Blo 1505449 1608535 := bstep (se 1 (by rfl) ⟨1206401, by rfl⟩ : syracuseStep 1608535 = 2412803) B2412803
theorem B2542475 : Blo 1505449 2542475 := bstep (se 1 (by rfl) ⟨1906856, by rfl⟩ : syracuseStep 2542475 = 3813713) B3813713
theorem B7236503 : Blo 1505449 7236503 := bstep (se 1 (by rfl) ⟨5427377, by rfl⟩ : syracuseStep 7236503 = 10854755) B10854755
theorem B2542603 : Blo 1505449 2542603 := bstep (se 1 (by rfl) ⟨1906952, by rfl⟩ : syracuseStep 2542603 = 3813905) B3813905
theorem B3812417 : Blo 1505449 3812417 := bstep (se 2 (by rfl) ⟨1429656, by rfl⟩ : syracuseStep 3812417 = 2859313) B2859313
theorem B6868061 : Blo 1505449 6868061 := bstep (se 3 (by rfl) ⟨1287761, by rfl⟩ : syracuseStep 6868061 = 2575523) B2575523
theorem B5082263 : Blo 1505449 5082263 := bstep (se 1 (by rfl) ⟨3811697, by rfl⟩ : syracuseStep 5082263 = 7623395) B7623395
theorem B2542745 : Blo 1505449 2542745 := bstep (se 2 (by rfl) ⟨953529, by rfl⟩ : syracuseStep 2542745 = 1907059) B1907059
theorem B2542873 : Blo 1505449 2542873 := bstep (se 2 (by rfl) ⟨953577, by rfl⟩ : syracuseStep 2542873 = 1907155) B1907155
theorem B18320705 : Blo 1505449 18320705 := bstep (se 2 (by rfl) ⟨6870264, by rfl⟩ : syracuseStep 18320705 = 13740529) B13740529
theorem B1568203 : Blo 1505449 1568203 := bstep (se 1 (by rfl) ⟨1176152, by rfl⟩ : syracuseStep 1568203 = 2352305) B2352305
theorem B5721617 : Blo 1505449 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B9055819 : Blo 1505449 9055819 := bstep (se 1 (by rfl) ⟨6791864, by rfl⟩ : syracuseStep 9055819 = 13583729) B13583729
theorem B3812953 : Blo 1505449 3812953 := bstep (se 2 (by rfl) ⟨1429857, by rfl⟩ : syracuseStep 3812953 = 2859715) B2859715
theorem B2715275 : Blo 1505449 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B5082803 : Blo 1505449 5082803 := bstep (se 1 (by rfl) ⟨3812102, by rfl⟩ : syracuseStep 5082803 = 7624205) B7624205
theorem B3387275 : Blo 1505449 3387275 := bstep (se 1 (by rfl) ⟨2540456, by rfl⟩ : syracuseStep 3387275 = 5080913) B5080913
theorem B7335859 : Blo 1505449 7335859 := bstep (se 1 (by rfl) ⟨5501894, by rfl⟩ : syracuseStep 7335859 = 11003789) B11003789
theorem B3387329 : Blo 1505449 3387329 := bstep (se 2 (by rfl) ⟨1270248, by rfl⟩ : syracuseStep 3387329 = 2540497) B2540497
theorem B5083073 : Blo 1505449 5083073 := bstep (se 2 (by rfl) ⟨1906152, by rfl⟩ : syracuseStep 5083073 = 3812305) B3812305
theorem B10858445 : Blo 1505449 10858445 := bstep (se 3 (by rfl) ⟨2035958, by rfl⟩ : syracuseStep 10858445 = 4071917) B4071917
theorem B3387545 : Blo 1505449 3387545 := bstep (se 2 (by rfl) ⟨1270329, by rfl⟩ : syracuseStep 3387545 = 2540659) B2540659
theorem B3387635 : Blo 1505449 3387635 := bstep (se 1 (by rfl) ⟨2540726, by rfl⟩ : syracuseStep 3387635 = 5081453) B5081453
theorem B3387671 : Blo 1505449 3387671 := bstep (se 1 (by rfl) ⟨2540753, by rfl⟩ : syracuseStep 3387671 = 5081507) B5081507
theorem B3387851 : Blo 1505449 3387851 := bstep (se 1 (by rfl) ⟨2540888, by rfl⟩ : syracuseStep 3387851 = 5081777) B5081777
theorem B2576843 : Blo 1505449 2576843 := bstep (se 1 (by rfl) ⟨1932632, by rfl⟩ : syracuseStep 2576843 = 3865265) B3865265
theorem B5083613 : Blo 1505449 5083613 := bstep (se 3 (by rfl) ⟨953177, by rfl⟩ : syracuseStep 5083613 = 1906355) B1906355
theorem B3387905 : Blo 1505449 3387905 := bstep (se 2 (by rfl) ⟨1270464, by rfl⟩ : syracuseStep 3387905 = 2540929) B2540929
theorem B7623233 : Blo 1505449 7623233 := bstep (se 2 (by rfl) ⟨2858712, by rfl⟩ : syracuseStep 7623233 = 5717425) B5717425
theorem B8581697 : Blo 1505449 8581697 := bstep (se 2 (by rfl) ⟨3218136, by rfl⟩ : syracuseStep 8581697 = 6436273) B6436273
theorem B3052121 : Blo 1505449 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B3052147 : Blo 1505449 3052147 := bstep (se 1 (by rfl) ⟨2289110, by rfl⟩ : syracuseStep 3052147 = 4578221) B4578221
theorem B3814067 : Blo 1505449 3814067 := bstep (se 1 (by rfl) ⟨2860550, by rfl⟩ : syracuseStep 3814067 = 5721101) B5721101
theorem B1716919 : Blo 1505449 1716919 := bstep (se 1 (by rfl) ⟨1287689, by rfl⟩ : syracuseStep 1716919 = 2575379) B2575379
theorem B6435521 : Blo 1505449 6435521 := bstep (se 2 (by rfl) ⟨2413320, by rfl⟩ : syracuseStep 6435521 = 4826641) B4826641
theorem B3388121 : Blo 1505449 3388121 := bstep (se 2 (by rfl) ⟨1270545, by rfl⟩ : syracuseStep 3388121 = 2541091) B2541091
theorem B3388211 : Blo 1505449 3388211 := bstep (se 1 (by rfl) ⟨2541158, by rfl⟩ : syracuseStep 3388211 = 5082317) B5082317
theorem B4289345 : Blo 1505449 4289345 := bstep (se 2 (by rfl) ⟨1608504, by rfl⟩ : syracuseStep 4289345 = 3217009) B3217009
theorem B3388247 : Blo 1505449 3388247 := bstep (se 1 (by rfl) ⟨2541185, by rfl⟩ : syracuseStep 3388247 = 5082371) B5082371
theorem B3216343 : Blo 1505449 3216343 := bstep (se 1 (by rfl) ⟨2412257, by rfl⟩ : syracuseStep 3216343 = 4824515) B4824515
theorem B3814361 : Blo 1505449 3814361 := bstep (se 2 (by rfl) ⟨1430385, by rfl⟩ : syracuseStep 3814361 = 2860771) B2860771
theorem B3388427 : Blo 1505449 3388427 := bstep (se 1 (by rfl) ⟨2541320, by rfl⟩ : syracuseStep 3388427 = 5082641) B5082641
theorem B3388481 : Blo 1505449 3388481 := bstep (se 2 (by rfl) ⟨1270680, by rfl⟩ : syracuseStep 3388481 = 2541361) B2541361
theorem B4969561 : Blo 1505449 4969561 := bstep (se 2 (by rfl) ⟨1863585, by rfl⟩ : syracuseStep 4969561 = 3727171) B3727171
theorem B3216523 : Blo 1505449 3216523 := bstep (se 1 (by rfl) ⟨2412392, by rfl⟩ : syracuseStep 3216523 = 4824785) B4824785
theorem B3216599 : Blo 1505449 3216599 := bstep (se 1 (by rfl) ⟨2412449, by rfl⟩ : syracuseStep 3216599 = 4824899) B4824899
theorem B19297541 : Blo 1505449 19297541 := bstep (se 4 (by rfl) ⟨1809144, by rfl⟩ : syracuseStep 19297541 = 3618289) B3618289
theorem B2258201 : Blo 1505449 2258201 := bstep (se 2 (by rfl) ⟨846825, by rfl⟩ : syracuseStep 2258201 = 1693651) B1693651
theorem B3388697 : Blo 1505449 3388697 := bstep (se 2 (by rfl) ⟨1270761, by rfl⟩ : syracuseStep 3388697 = 2541523) B2541523
theorem B4289881 : Blo 1505449 4289881 := bstep (se 2 (by rfl) ⟨1608705, by rfl⟩ : syracuseStep 4289881 = 3217411) B3217411
theorem B3388787 : Blo 1505449 3388787 := bstep (se 1 (by rfl) ⟨2541590, by rfl⟩ : syracuseStep 3388787 = 5083181) B5083181
theorem B2258315 : Blo 1505449 2258315 := bstep (se 1 (by rfl) ⟨1693736, by rfl⟩ : syracuseStep 2258315 = 3387473) B3387473
theorem B2258327 : Blo 1505449 2258327 := bstep (se 1 (by rfl) ⟨1693745, by rfl⟩ : syracuseStep 2258327 = 3387491) B3387491
theorem B3388823 : Blo 1505449 3388823 := bstep (se 1 (by rfl) ⟨2541617, by rfl⟩ : syracuseStep 3388823 = 5083235) B5083235
theorem B2258393 : Blo 1505449 2258393 := bstep (se 2 (by rfl) ⟨846897, by rfl⟩ : syracuseStep 2258393 = 1693795) B1693795
theorem B7239233 : Blo 1505449 7239233 := bstep (se 2 (by rfl) ⟨2714712, by rfl⟩ : syracuseStep 7239233 = 5429425) B5429425
theorem B2258507 : Blo 1505449 2258507 := bstep (se 1 (by rfl) ⟨1693880, by rfl⟩ : syracuseStep 2258507 = 3387761) B3387761
theorem B3389003 : Blo 1505449 3389003 := bstep (se 1 (by rfl) ⟨2541752, by rfl⟩ : syracuseStep 3389003 = 5083505) B5083505
theorem B5084747 : Blo 1505449 5084747 := bstep (se 1 (by rfl) ⟨3813560, by rfl⟩ : syracuseStep 5084747 = 7627121) B7627121
theorem B2258519 : Blo 1505449 2258519 := bstep (se 1 (by rfl) ⟨1693889, by rfl⟩ : syracuseStep 2258519 = 3387779) B3387779
theorem B12383837 : Blo 1505449 12383837 := bstep (se 3 (by rfl) ⟨2321969, by rfl⟩ : syracuseStep 12383837 = 4643939) B4643939
theorem B3389057 : Blo 1505449 3389057 := bstep (se 2 (by rfl) ⟨1270896, by rfl⟩ : syracuseStep 3389057 = 2541793) B2541793
theorem B9647747 : Blo 1505449 9647747 := bstep (se 1 (by rfl) ⟨7235810, by rfl⟩ : syracuseStep 9647747 = 14471621) B14471621
theorem B2258585 : Blo 1505449 2258585 := bstep (se 2 (by rfl) ⟨846969, by rfl⟩ : syracuseStep 2258585 = 1693939) B1693939
theorem B7239347 : Blo 1505449 7239347 := bstep (se 1 (by rfl) ⟨5429510, by rfl⟩ : syracuseStep 7239347 = 10859021) B10859021
theorem B3053249 : Blo 1505449 3053249 := bstep (se 2 (by rfl) ⟨1144968, by rfl⟩ : syracuseStep 3053249 = 2289937) B2289937
theorem B2258699 : Blo 1505449 2258699 := bstep (se 1 (by rfl) ⟨1694024, by rfl⟩ : syracuseStep 2258699 = 3388049) B3388049
theorem B2258711 : Blo 1505449 2258711 := bstep (se 1 (by rfl) ⟨1694033, by rfl⟩ : syracuseStep 2258711 = 3388067) B3388067
theorem B6108979 : Blo 1505449 6108979 := bstep (se 1 (by rfl) ⟨4581734, by rfl⟩ : syracuseStep 6108979 = 9163469) B9163469
theorem B1906507 : Blo 1505449 1906507 := bstep (se 1 (by rfl) ⟨1429880, by rfl⟩ : syracuseStep 1906507 = 2859761) B2859761
theorem B2258777 : Blo 1505449 2258777 := bstep (se 2 (by rfl) ⟨847041, by rfl⟩ : syracuseStep 2258777 = 1694083) B1694083
theorem B3389273 : Blo 1505449 3389273 := bstep (se 2 (by rfl) ⟨1270977, by rfl⟩ : syracuseStep 3389273 = 2541955) B2541955
theorem B5085017 : Blo 1505449 5085017 := bstep (se 2 (by rfl) ⟨1906881, by rfl⟩ : syracuseStep 5085017 = 3813763) B3813763
theorem B14112643 : Blo 1505449 14112643 := bstep (se 1 (by rfl) ⟨10584482, by rfl⟩ : syracuseStep 14112643 = 21168965) B21168965
theorem B3389363 : Blo 1505449 3389363 := bstep (se 1 (by rfl) ⟨2542022, by rfl⟩ : syracuseStep 3389363 = 5084045) B5084045
theorem B2258891 : Blo 1505449 2258891 := bstep (se 1 (by rfl) ⟨1694168, by rfl⟩ : syracuseStep 2258891 = 3388337) B3388337
theorem B5576651 : Blo 1505449 5576651 := bstep (se 1 (by rfl) ⟨4182488, by rfl⟩ : syracuseStep 5576651 = 8364977) B8364977
theorem B2258903 : Blo 1505449 2258903 := bstep (se 1 (by rfl) ⟨1694177, by rfl⟩ : syracuseStep 2258903 = 3388355) B3388355
theorem B3389399 : Blo 1505449 3389399 := bstep (se 1 (by rfl) ⟨2542049, by rfl⟩ : syracuseStep 3389399 = 5084099) B5084099
theorem B1693687 : Blo 1505449 1693687 := bstep (se 1 (by rfl) ⟨1270265, by rfl⟩ : syracuseStep 1693687 = 2540531) B2540531
theorem B2258969 : Blo 1505449 2258969 := bstep (se 2 (by rfl) ⟨847113, by rfl⟩ : syracuseStep 2258969 = 1694227) B1694227
theorem B2259083 : Blo 1505449 2259083 := bstep (se 1 (by rfl) ⟨1694312, by rfl⟩ : syracuseStep 2259083 = 3388625) B3388625
theorem B3389579 : Blo 1505449 3389579 := bstep (se 1 (by rfl) ⟨2542184, by rfl⟩ : syracuseStep 3389579 = 5084369) B5084369
theorem B2259095 : Blo 1505449 2259095 := bstep (se 1 (by rfl) ⟨1694321, by rfl⟩ : syracuseStep 2259095 = 3388643) B3388643
theorem B1505451 : Blo 1505449 1505451 := bstep (se 1 (by rfl) ⟨1129088, by rfl⟩ : syracuseStep 1505451 = 2258177) B2258177
theorem B1693867 : Blo 1505449 1693867 := bstep (se 1 (by rfl) ⟨1270400, by rfl⟩ : syracuseStep 1693867 = 2540801) B2540801
theorem B12867761 : Blo 1505449 12867761 := bstep (se 2 (by rfl) ⟨4825410, by rfl⟩ : syracuseStep 12867761 = 9650821) B9650821
theorem B1505463 : Blo 1505449 1505463 := bstep (se 1 (by rfl) ⟨1129097, by rfl⟩ : syracuseStep 1505463 = 2258195) B2258195
theorem B3389633 : Blo 1505449 3389633 := bstep (se 2 (by rfl) ⟨1271112, by rfl⟩ : syracuseStep 3389633 = 2542225) B2542225
theorem B1505483 : Blo 1505449 1505483 := bstep (se 1 (by rfl) ⟨1129112, by rfl⟩ : syracuseStep 1505483 = 2258225) B2258225
theorem B1505495 : Blo 1505449 1505495 := bstep (se 1 (by rfl) ⟨1129121, by rfl⟩ : syracuseStep 1505495 = 2258243) B2258243
theorem B2259161 : Blo 1505449 2259161 := bstep (se 2 (by rfl) ⟨847185, by rfl⟩ : syracuseStep 2259161 = 1694371) B1694371
theorem B1505515 : Blo 1505449 1505515 := bstep (se 1 (by rfl) ⟨1129136, by rfl⟩ : syracuseStep 1505515 = 2258273) B2258273
theorem B1505527 : Blo 1505449 1505527 := bstep (se 1 (by rfl) ⟨1129145, by rfl⟩ : syracuseStep 1505527 = 2258291) B2258291
theorem B1505547 : Blo 1505449 1505547 := bstep (se 1 (by rfl) ⟨1129160, by rfl⟩ : syracuseStep 1505547 = 2258321) B2258321
theorem B5716241 : Blo 1505449 5716241 := bstep (se 2 (by rfl) ⟨2143590, by rfl⟩ : syracuseStep 5716241 = 4287181) B4287181
theorem B1505559 : Blo 1505449 1505559 := bstep (se 1 (by rfl) ⟨1129169, by rfl⟩ : syracuseStep 1505559 = 2258339) B2258339
theorem B1693975 : Blo 1505449 1693975 := bstep (se 1 (by rfl) ⟨1270481, by rfl⟩ : syracuseStep 1693975 = 2540963) B2540963
theorem B1505579 : Blo 1505449 1505579 := bstep (se 1 (by rfl) ⟨1129184, by rfl⟩ : syracuseStep 1505579 = 2258369) B2258369
theorem B1505591 : Blo 1505449 1505591 := bstep (se 1 (by rfl) ⟨1129193, by rfl⟩ : syracuseStep 1505591 = 2258387) B2258387
theorem B1505611 : Blo 1505449 1505611 := bstep (se 1 (by rfl) ⟨1129208, by rfl⟩ : syracuseStep 1505611 = 2258417) B2258417
theorem B2259275 : Blo 1505449 2259275 := bstep (se 1 (by rfl) ⟨1694456, by rfl⟩ : syracuseStep 2259275 = 3388913) B3388913
theorem B1505623 : Blo 1505449 1505623 := bstep (se 1 (by rfl) ⟨1129217, by rfl⟩ : syracuseStep 1505623 = 2258435) B2258435
theorem B2259287 : Blo 1505449 2259287 := bstep (se 1 (by rfl) ⟨1694465, by rfl⟩ : syracuseStep 2259287 = 3388931) B3388931
theorem B1505643 : Blo 1505449 1505643 := bstep (se 1 (by rfl) ⟨1129232, by rfl⟩ : syracuseStep 1505643 = 2258465) B2258465
theorem B1505655 : Blo 1505449 1505655 := bstep (se 1 (by rfl) ⟨1129241, by rfl⟩ : syracuseStep 1505655 = 2258483) B2258483
theorem B1505675 : Blo 1505449 1505675 := bstep (se 1 (by rfl) ⟨1129256, by rfl⟩ : syracuseStep 1505675 = 2258513) B2258513
theorem B1505687 : Blo 1505449 1505687 := bstep (se 1 (by rfl) ⟨1129265, by rfl⟩ : syracuseStep 1505687 = 2258531) B2258531
theorem B2259353 : Blo 1505449 2259353 := bstep (se 2 (by rfl) ⟨847257, by rfl⟩ : syracuseStep 2259353 = 1694515) B1694515
theorem B3389849 : Blo 1505449 3389849 := bstep (se 2 (by rfl) ⟨1271193, by rfl⟩ : syracuseStep 3389849 = 2542387) B2542387
theorem B1505707 : Blo 1505449 1505707 := bstep (se 1 (by rfl) ⟨1129280, by rfl⟩ : syracuseStep 1505707 = 2258561) B2258561
theorem B6109613 : Blo 1505449 6109613 := bstep (se 3 (by rfl) ⟨1145552, by rfl⟩ : syracuseStep 6109613 = 2291105) B2291105
theorem B5429683 : Blo 1505449 5429683 := bstep (se 1 (by rfl) ⟨4072262, by rfl⟩ : syracuseStep 5429683 = 8144525) B8144525
theorem B1505719 : Blo 1505449 1505719 := bstep (se 1 (by rfl) ⟨1129289, by rfl⟩ : syracuseStep 1505719 = 2258579) B2258579
theorem B4823489 : Blo 1505449 4823489 := bstep (se 2 (by rfl) ⟨1808808, by rfl⟩ : syracuseStep 4823489 = 3617617) B3617617
theorem B1505739 : Blo 1505449 1505739 := bstep (se 1 (by rfl) ⟨1129304, by rfl⟩ : syracuseStep 1505739 = 2258609) B2258609
theorem B1694155 : Blo 1505449 1694155 := bstep (se 1 (by rfl) ⟨1270616, by rfl⟩ : syracuseStep 1694155 = 2541233) B2541233
theorem B1505751 : Blo 1505449 1505751 := bstep (se 1 (by rfl) ⟨1129313, by rfl⟩ : syracuseStep 1505751 = 2258627) B2258627
theorem B7625177 : Blo 1505449 7625177 := bstep (se 2 (by rfl) ⟨2859441, by rfl⟩ : syracuseStep 7625177 = 5718883) B5718883
theorem B3619289 : Blo 1505449 3619289 := bstep (se 2 (by rfl) ⟨1357233, by rfl⟩ : syracuseStep 3619289 = 2714467) B2714467
theorem B1505771 : Blo 1505449 1505771 := bstep (se 1 (by rfl) ⟨1129328, by rfl⟩ : syracuseStep 1505771 = 2258657) B2258657
theorem B3389939 : Blo 1505449 3389939 := bstep (se 1 (by rfl) ⟨2542454, by rfl⟩ : syracuseStep 3389939 = 5084909) B5084909
theorem B1505783 : Blo 1505449 1505783 := bstep (se 1 (by rfl) ⟨1129337, by rfl⟩ : syracuseStep 1505783 = 2258675) B2258675
theorem B1505803 : Blo 1505449 1505803 := bstep (se 1 (by rfl) ⟨1129352, by rfl⟩ : syracuseStep 1505803 = 2258705) B2258705
theorem B2611723 : Blo 1505449 2611723 := bstep (se 1 (by rfl) ⟨1958792, by rfl⟩ : syracuseStep 2611723 = 3917585) B3917585
theorem B2259467 : Blo 1505449 2259467 := bstep (se 1 (by rfl) ⟨1694600, by rfl⟩ : syracuseStep 2259467 = 3389201) B3389201
theorem B128842253 : Blo 1505449 128842253 := bstep (se 3 (by rfl) ⟨24157922, by rfl⟩ : syracuseStep 128842253 = 48315845) B48315845
theorem B1505815 : Blo 1505449 1505815 := bstep (se 1 (by rfl) ⟨1129361, by rfl⟩ : syracuseStep 1505815 = 2258723) B2258723
theorem B2259479 : Blo 1505449 2259479 := bstep (se 1 (by rfl) ⟨1694609, by rfl⟩ : syracuseStep 2259479 = 3389219) B3389219
theorem B3389975 : Blo 1505449 3389975 := bstep (se 1 (by rfl) ⟨2542481, by rfl⟩ : syracuseStep 3389975 = 5084963) B5084963
theorem B5085719 : Blo 1505449 5085719 := bstep (se 1 (by rfl) ⟨3814289, by rfl⟩ : syracuseStep 5085719 = 7628579) B7628579
theorem B1505835 : Blo 1505449 1505835 := bstep (se 1 (by rfl) ⟨1129376, by rfl⟩ : syracuseStep 1505835 = 2258753) B2258753
theorem B1505847 : Blo 1505449 1505847 := bstep (se 1 (by rfl) ⟨1129385, by rfl⟩ : syracuseStep 1505847 = 2258771) B2258771
theorem B1694263 : Blo 1505449 1694263 := bstep (se 1 (by rfl) ⟨1270697, by rfl⟩ : syracuseStep 1694263 = 2541395) B2541395
theorem B1505867 : Blo 1505449 1505867 := bstep (se 1 (by rfl) ⟨1129400, by rfl⟩ : syracuseStep 1505867 = 2258801) B2258801
theorem B1505879 : Blo 1505449 1505879 := bstep (se 1 (by rfl) ⟨1129409, by rfl⟩ : syracuseStep 1505879 = 2258819) B2258819
theorem B2259545 : Blo 1505449 2259545 := bstep (se 2 (by rfl) ⟨847329, by rfl⟩ : syracuseStep 2259545 = 1694659) B1694659
theorem B1505899 : Blo 1505449 1505899 := bstep (se 1 (by rfl) ⟨1129424, by rfl⟩ : syracuseStep 1505899 = 2258849) B2258849
theorem B1505911 : Blo 1505449 1505911 := bstep (se 1 (by rfl) ⟨1129433, by rfl⟩ : syracuseStep 1505911 = 2258867) B2258867
theorem B1505931 : Blo 1505449 1505931 := bstep (se 1 (by rfl) ⟨1129448, by rfl⟩ : syracuseStep 1505931 = 2258897) B2258897
theorem B1505943 : Blo 1505449 1505943 := bstep (se 1 (by rfl) ⟨1129457, by rfl⟩ : syracuseStep 1505943 = 2258915) B2258915
theorem B1505963 : Blo 1505449 1505963 := bstep (se 1 (by rfl) ⟨1129472, by rfl⟩ : syracuseStep 1505963 = 2258945) B2258945
theorem B1505975 : Blo 1505449 1505975 := bstep (se 1 (by rfl) ⟨1129481, by rfl⟩ : syracuseStep 1505975 = 2258963) B2258963
theorem B1505995 : Blo 1505449 1505995 := bstep (se 1 (by rfl) ⟨1129496, by rfl⟩ : syracuseStep 1505995 = 2258993) B2258993
theorem B2259659 : Blo 1505449 2259659 := bstep (se 1 (by rfl) ⟨1694744, by rfl⟩ : syracuseStep 2259659 = 3389489) B3389489
theorem B3390155 : Blo 1505449 3390155 := bstep (se 1 (by rfl) ⟨2542616, by rfl⟩ : syracuseStep 3390155 = 5085233) B5085233
theorem B1506007 : Blo 1505449 1506007 := bstep (se 1 (by rfl) ⟨1129505, by rfl⟩ : syracuseStep 1506007 = 2259011) B2259011
theorem B2259671 : Blo 1505449 2259671 := bstep (se 1 (by rfl) ⟨1694753, by rfl⟩ : syracuseStep 2259671 = 3389507) B3389507
theorem B1506027 : Blo 1505449 1506027 := bstep (se 1 (by rfl) ⟨1129520, by rfl⟩ : syracuseStep 1506027 = 2259041) B2259041
theorem B1694443 : Blo 1505449 1694443 := bstep (se 1 (by rfl) ⟨1270832, by rfl⟩ : syracuseStep 1694443 = 2541665) B2541665
theorem B1506039 : Blo 1505449 1506039 := bstep (se 1 (by rfl) ⟨1129529, by rfl⟩ : syracuseStep 1506039 = 2259059) B2259059
theorem B3390209 : Blo 1505449 3390209 := bstep (se 2 (by rfl) ⟨1271328, by rfl⟩ : syracuseStep 3390209 = 2542657) B2542657
theorem B1506059 : Blo 1505449 1506059 := bstep (se 1 (by rfl) ⟨1129544, by rfl⟩ : syracuseStep 1506059 = 2259089) B2259089
theorem B1506071 : Blo 1505449 1506071 := bstep (se 1 (by rfl) ⟨1129553, by rfl⟩ : syracuseStep 1506071 = 2259107) B2259107
theorem B2259737 : Blo 1505449 2259737 := bstep (se 2 (by rfl) ⟨847401, by rfl⟩ : syracuseStep 2259737 = 1694803) B1694803
theorem B1506091 : Blo 1505449 1506091 := bstep (se 1 (by rfl) ⟨1129568, by rfl⟩ : syracuseStep 1506091 = 2259137) B2259137
theorem B1506103 : Blo 1505449 1506103 := bstep (se 1 (by rfl) ⟨1129577, by rfl⟩ : syracuseStep 1506103 = 2259155) B2259155
theorem B1506123 : Blo 1505449 1506123 := bstep (se 1 (by rfl) ⟨1129592, by rfl⟩ : syracuseStep 1506123 = 2259185) B2259185
theorem B1506135 : Blo 1505449 1506135 := bstep (se 1 (by rfl) ⟨1129601, by rfl⟩ : syracuseStep 1506135 = 2259203) B2259203
theorem B1694551 : Blo 1505449 1694551 := bstep (se 1 (by rfl) ⟨1270913, by rfl⟩ : syracuseStep 1694551 = 2541827) B2541827
theorem B1506155 : Blo 1505449 1506155 := bstep (se 1 (by rfl) ⟨1129616, by rfl⟩ : syracuseStep 1506155 = 2259233) B2259233
theorem B1506167 : Blo 1505449 1506167 := bstep (se 1 (by rfl) ⟨1129625, by rfl⟩ : syracuseStep 1506167 = 2259251) B2259251
theorem B1506187 : Blo 1505449 1506187 := bstep (se 1 (by rfl) ⟨1129640, by rfl⟩ : syracuseStep 1506187 = 2259281) B2259281
theorem B2259851 : Blo 1505449 2259851 := bstep (se 1 (by rfl) ⟨1694888, by rfl⟩ : syracuseStep 2259851 = 3389777) B3389777
theorem B1506199 : Blo 1505449 1506199 := bstep (se 1 (by rfl) ⟨1129649, by rfl⟩ : syracuseStep 1506199 = 2259299) B2259299
theorem B2259863 : Blo 1505449 2259863 := bstep (se 1 (by rfl) ⟨1694897, by rfl⟩ : syracuseStep 2259863 = 3389795) B3389795
theorem B2898841 : Blo 1505449 2898841 := bstep (se 2 (by rfl) ⟨1087065, by rfl⟩ : syracuseStep 2898841 = 2174131) B2174131
theorem B1506219 : Blo 1505449 1506219 := bstep (se 1 (by rfl) ⟨1129664, by rfl⟩ : syracuseStep 1506219 = 2259329) B2259329
theorem B13736881 : Blo 1505449 13736881 := bstep (se 2 (by rfl) ⟨5151330, by rfl⟩ : syracuseStep 13736881 = 10302661) B10302661
theorem B1506231 : Blo 1505449 1506231 := bstep (se 1 (by rfl) ⟨1129673, by rfl⟩ : syracuseStep 1506231 = 2259347) B2259347
theorem B5716939 : Blo 1505449 5716939 := bstep (se 1 (by rfl) ⟨4287704, by rfl⟩ : syracuseStep 5716939 = 8575409) B8575409
theorem B1506251 : Blo 1505449 1506251 := bstep (se 1 (by rfl) ⟨1129688, by rfl⟩ : syracuseStep 1506251 = 2259377) B2259377
theorem B1506263 : Blo 1505449 1506263 := bstep (se 1 (by rfl) ⟨1129697, by rfl⟩ : syracuseStep 1506263 = 2259395) B2259395
theorem B2259929 : Blo 1505449 2259929 := bstep (se 2 (by rfl) ⟨847473, by rfl⟩ : syracuseStep 2259929 = 1694947) B1694947
theorem B3390425 : Blo 1505449 3390425 := bstep (se 2 (by rfl) ⟨1271409, by rfl⟩ : syracuseStep 3390425 = 2542819) B2542819
theorem B66059225 : Blo 1505449 66059225 := bstep (se 2 (by rfl) ⟨24772209, by rfl⟩ : syracuseStep 66059225 = 49544419) B49544419
theorem B3218393 : Blo 1505449 3218393 := bstep (se 2 (by rfl) ⟨1206897, by rfl⟩ : syracuseStep 3218393 = 2413795) B2413795
theorem B1506283 : Blo 1505449 1506283 := bstep (se 1 (by rfl) ⟨1129712, by rfl⟩ : syracuseStep 1506283 = 2259425) B2259425
theorem B1506295 : Blo 1505449 1506295 := bstep (se 1 (by rfl) ⟨1129721, by rfl⟩ : syracuseStep 1506295 = 2259443) B2259443
theorem B3480587 : Blo 1505449 3480587 := bstep (se 1 (by rfl) ⟨2610440, by rfl⟩ : syracuseStep 3480587 = 5220881) B5220881
theorem B1506315 : Blo 1505449 1506315 := bstep (se 1 (by rfl) ⟨1129736, by rfl⟩ : syracuseStep 1506315 = 2259473) B2259473
theorem B1694731 : Blo 1505449 1694731 := bstep (se 1 (by rfl) ⟨1271048, by rfl⟩ : syracuseStep 1694731 = 2542097) B2542097
theorem B1506327 : Blo 1505449 1506327 := bstep (se 1 (by rfl) ⟨1129745, by rfl⟩ : syracuseStep 1506327 = 2259491) B2259491
theorem B2145305 : Blo 1505449 2145305 := bstep (se 2 (by rfl) ⟨804489, by rfl⟩ : syracuseStep 2145305 = 1608979) B1608979
theorem B1506347 : Blo 1505449 1506347 := bstep (se 1 (by rfl) ⟨1129760, by rfl⟩ : syracuseStep 1506347 = 2259521) B2259521
theorem B3390515 : Blo 1505449 3390515 := bstep (se 1 (by rfl) ⟨2542886, by rfl⟩ : syracuseStep 3390515 = 5085773) B5085773
theorem B1506359 : Blo 1505449 1506359 := bstep (se 1 (by rfl) ⟨1129769, by rfl⟩ : syracuseStep 1506359 = 2259539) B2259539
theorem B1506379 : Blo 1505449 1506379 := bstep (se 1 (by rfl) ⟨1129784, by rfl⟩ : syracuseStep 1506379 = 2259569) B2259569
theorem B2260043 : Blo 1505449 2260043 := bstep (se 1 (by rfl) ⟨1695032, by rfl⟩ : syracuseStep 2260043 = 3390065) B3390065
theorem B1506391 : Blo 1505449 1506391 := bstep (se 1 (by rfl) ⟨1129793, by rfl⟩ : syracuseStep 1506391 = 2259587) B2259587
theorem B2260055 : Blo 1505449 2260055 := bstep (se 1 (by rfl) ⟨1695041, by rfl⟩ : syracuseStep 2260055 = 3390083) B3390083
theorem B3390551 : Blo 1505449 3390551 := bstep (se 1 (by rfl) ⟨2542913, by rfl⟩ : syracuseStep 3390551 = 5085827) B5085827
theorem B1506411 : Blo 1505449 1506411 := bstep (se 1 (by rfl) ⟨1129808, by rfl⟩ : syracuseStep 1506411 = 2259617) B2259617
theorem B1506423 : Blo 1505449 1506423 := bstep (se 1 (by rfl) ⟨1129817, by rfl⟩ : syracuseStep 1506423 = 2259635) B2259635
theorem B1694839 : Blo 1505449 1694839 := bstep (se 1 (by rfl) ⟨1271129, by rfl⟩ : syracuseStep 1694839 = 2542259) B2542259
theorem B1506443 : Blo 1505449 1506443 := bstep (se 1 (by rfl) ⟨1129832, by rfl⟩ : syracuseStep 1506443 = 2259665) B2259665
theorem B1506455 : Blo 1505449 1506455 := bstep (se 1 (by rfl) ⟨1129841, by rfl⟩ : syracuseStep 1506455 = 2259683) B2259683
theorem B2260121 : Blo 1505449 2260121 := bstep (se 2 (by rfl) ⟨847545, by rfl⟩ : syracuseStep 2260121 = 1695091) B1695091
theorem B1506475 : Blo 1505449 1506475 := bstep (se 1 (by rfl) ⟨1129856, by rfl⟩ : syracuseStep 1506475 = 2259713) B2259713
theorem B1506487 : Blo 1505449 1506487 := bstep (se 1 (by rfl) ⟨1129865, by rfl⟩ : syracuseStep 1506487 = 2259731) B2259731
theorem B1506507 : Blo 1505449 1506507 := bstep (se 1 (by rfl) ⟨1129880, by rfl⟩ : syracuseStep 1506507 = 2259761) B2259761
theorem B1506519 : Blo 1505449 1506519 := bstep (se 1 (by rfl) ⟨1129889, by rfl⟩ : syracuseStep 1506519 = 2259779) B2259779
theorem B3669209 : Blo 1505449 3669209 := bstep (se 2 (by rfl) ⟨1375953, by rfl⟩ : syracuseStep 3669209 = 2751907) B2751907
theorem B5717213 : Blo 1505449 5717213 := bstep (se 3 (by rfl) ⟨1071977, by rfl⟩ : syracuseStep 5717213 = 2143955) B2143955
theorem B1506539 : Blo 1505449 1506539 := bstep (se 1 (by rfl) ⟨1129904, by rfl⟩ : syracuseStep 1506539 = 2259809) B2259809
theorem B1506551 : Blo 1505449 1506551 := bstep (se 1 (by rfl) ⟨1129913, by rfl⟩ : syracuseStep 1506551 = 2259827) B2259827
theorem B1506571 : Blo 1505449 1506571 := bstep (se 1 (by rfl) ⟨1129928, by rfl⟩ : syracuseStep 1506571 = 2259857) B2259857
theorem B2260235 : Blo 1505449 2260235 := bstep (se 1 (by rfl) ⟨1695176, by rfl⟩ : syracuseStep 2260235 = 3390353) B3390353
theorem B1506583 : Blo 1505449 1506583 := bstep (se 1 (by rfl) ⟨1129937, by rfl⟩ : syracuseStep 1506583 = 2259875) B2259875
theorem B2260247 : Blo 1505449 2260247 := bstep (se 1 (by rfl) ⟨1695185, by rfl⟩ : syracuseStep 2260247 = 3390371) B3390371
theorem B1506603 : Blo 1505449 1506603 := bstep (se 1 (by rfl) ⟨1129952, by rfl⟩ : syracuseStep 1506603 = 2259905) B2259905
theorem B1695019 : Blo 1505449 1695019 := bstep (se 1 (by rfl) ⟨1271264, by rfl⟩ : syracuseStep 1695019 = 2542529) B2542529
theorem B1506615 : Blo 1505449 1506615 := bstep (se 1 (by rfl) ⟨1129961, by rfl⟩ : syracuseStep 1506615 = 2259923) B2259923
theorem B1506635 : Blo 1505449 1506635 := bstep (se 1 (by rfl) ⟨1129976, by rfl⟩ : syracuseStep 1506635 = 2259953) B2259953
theorem B1506647 : Blo 1505449 1506647 := bstep (se 1 (by rfl) ⟨1129985, by rfl⟩ : syracuseStep 1506647 = 2259971) B2259971
theorem B2260313 : Blo 1505449 2260313 := bstep (se 2 (by rfl) ⟨847617, by rfl⟩ : syracuseStep 2260313 = 1695235) B1695235
theorem B4070749 : Blo 1505449 4070749 := bstep (se 3 (by rfl) ⟨763265, by rfl⟩ : syracuseStep 4070749 = 1526531) B1526531
theorem B1506667 : Blo 1505449 1506667 := bstep (se 1 (by rfl) ⟨1130000, by rfl⟩ : syracuseStep 1506667 = 2260001) B2260001
theorem B1506679 : Blo 1505449 1506679 := bstep (se 1 (by rfl) ⟨1130009, by rfl⟩ : syracuseStep 1506679 = 2260019) B2260019
theorem B1506699 : Blo 1505449 1506699 := bstep (se 1 (by rfl) ⟨1130024, by rfl⟩ : syracuseStep 1506699 = 2260049) B2260049
theorem B1506711 : Blo 1505449 1506711 := bstep (se 1 (by rfl) ⟨1130033, by rfl⟩ : syracuseStep 1506711 = 2260067) B2260067
theorem B1695127 : Blo 1505449 1695127 := bstep (se 1 (by rfl) ⟨1271345, by rfl⟩ : syracuseStep 1695127 = 2542691) B2542691
theorem B1506731 : Blo 1505449 1506731 := bstep (se 1 (by rfl) ⟨1130048, by rfl⟩ : syracuseStep 1506731 = 2260097) B2260097
theorem B20618675 : Blo 1505449 20618675 := bstep (se 1 (by rfl) ⟨15464006, by rfl⟩ : syracuseStep 20618675 = 30928013) B30928013
theorem B1506743 : Blo 1505449 1506743 := bstep (se 1 (by rfl) ⟨1130057, by rfl⟩ : syracuseStep 1506743 = 2260115) B2260115
theorem B1506763 : Blo 1505449 1506763 := bstep (se 1 (by rfl) ⟨1130072, by rfl⟩ : syracuseStep 1506763 = 2260145) B2260145
theorem B1506775 : Blo 1505449 1506775 := bstep (se 1 (by rfl) ⟨1130081, by rfl⟩ : syracuseStep 1506775 = 2260163) B2260163
theorem B1506795 : Blo 1505449 1506795 := bstep (se 1 (by rfl) ⟨1130096, by rfl⟩ : syracuseStep 1506795 = 2260193) B2260193
theorem B1506807 : Blo 1505449 1506807 := bstep (se 1 (by rfl) ⟨1130105, by rfl⟩ : syracuseStep 1506807 = 2260211) B2260211
theorem B1506827 : Blo 1505449 1506827 := bstep (se 1 (by rfl) ⟨1130120, by rfl⟩ : syracuseStep 1506827 = 2260241) B2260241
theorem B1506839 : Blo 1505449 1506839 := bstep (se 1 (by rfl) ⟨1130129, by rfl⟩ : syracuseStep 1506839 = 2260259) B2260259
theorem B1506859 : Blo 1505449 1506859 := bstep (se 1 (by rfl) ⟨1130144, by rfl⟩ : syracuseStep 1506859 = 2260289) B2260289
theorem B1506871 : Blo 1505449 1506871 := bstep (se 1 (by rfl) ⟨1130153, by rfl⟩ : syracuseStep 1506871 = 2260307) B2260307
theorem B2858561 : Blo 1505449 2858561 := bstep (se 2 (by rfl) ⟨1071960, by rfl⟩ : syracuseStep 2858561 = 2143921) B2143921
theorem B1506891 : Blo 1505449 1506891 := bstep (se 1 (by rfl) ⟨1130168, by rfl⟩ : syracuseStep 1506891 = 2260337) B2260337
theorem B1695307 : Blo 1505449 1695307 := bstep (se 1 (by rfl) ⟨1271480, by rfl⟩ : syracuseStep 1695307 = 2542961) B2542961
theorem B1506903 : Blo 1505449 1506903 := bstep (se 1 (by rfl) ⟨1130177, by rfl⟩ : syracuseStep 1506903 = 2260355) B2260355
theorem B1506923 : Blo 1505449 1506923 := bstep (se 1 (by rfl) ⟨1130192, by rfl⟩ : syracuseStep 1506923 = 2260385) B2260385
theorem B1506935 : Blo 1505449 1506935 := bstep (se 1 (by rfl) ⟨1130201, by rfl⟩ : syracuseStep 1506935 = 2260403) B2260403
theorem B11009753 : Blo 1505449 11009753 := bstep (se 2 (by rfl) ⟨4128657, by rfl⟩ : syracuseStep 11009753 = 8257315) B8257315
theorem B14868269 : Blo 1505449 14868269 := bstep (se 3 (by rfl) ⟨2787800, by rfl⟩ : syracuseStep 14868269 = 5575601) B5575601
theorem B11312941 : Blo 1505449 11312941 := bstep (se 3 (by rfl) ⟨2121176, by rfl⟩ : syracuseStep 11312941 = 4242353) B4242353
theorem B2858827 : Blo 1505449 2858827 := bstep (se 1 (by rfl) ⟨2144120, by rfl⟩ : syracuseStep 2858827 = 4288241) B4288241
theorem B5717911 : Blo 1505449 5717911 := bstep (se 1 (by rfl) ⟨4288433, by rfl⟩ : syracuseStep 5717911 = 8576867) B8576867
theorem B33456401 : Blo 1505449 33456401 := bstep (se 2 (by rfl) ⟨12546150, by rfl⟩ : syracuseStep 33456401 = 25092301) B25092301
theorem B2859563 : Blo 1505449 2859563 := bstep (se 1 (by rfl) ⟨2144672, by rfl⟩ : syracuseStep 2859563 = 4289345) B4289345
theorem B3482297 : Blo 1505449 3482297 := bstep (se 2 (by rfl) ⟨1305861, by rfl⟩ : syracuseStep 3482297 = 2611723) B2611723
theorem B4826155 : Blo 1505449 4826155 := bstep (se 1 (by rfl) ⟨3619616, by rfl⟩ : syracuseStep 4826155 = 7239233) B7239233
theorem B6431831 : Blo 1505449 6431831 := bstep (se 1 (by rfl) ⟨4823873, by rfl⟩ : syracuseStep 6431831 = 9647747) B9647747
theorem B4826231 : Blo 1505449 4826231 := bstep (se 1 (by rfl) ⟨3619673, by rfl⟩ : syracuseStep 4826231 = 7239347) B7239347
theorem B7234733 : Blo 1505449 7234733 := bstep (se 3 (by rfl) ⟨1356512, by rfl⟩ : syracuseStep 7234733 = 2713025) B2713025
theorem B12862637 : Blo 1505449 12862637 := bstep (se 3 (by rfl) ⟨2411744, by rfl⟩ : syracuseStep 12862637 = 4823489) B4823489
theorem B9651437 : Blo 1505449 9651437 := bstep (se 3 (by rfl) ⟨1809644, by rfl⟩ : syracuseStep 9651437 = 3619289) B3619289
theorem B5719355 : Blo 1505449 5719355 := bstep (se 1 (by rfl) ⟨4289516, by rfl⟩ : syracuseStep 5719355 = 8579033) B8579033
theorem B8578507 : Blo 1505449 8578507 := bstep (se 1 (by rfl) ⟨6433880, by rfl⟩ : syracuseStep 8578507 = 12867761) B12867761
theorem B3810827 : Blo 1505449 3810827 := bstep (se 1 (by rfl) ⟨2858120, by rfl⟩ : syracuseStep 3810827 = 5716241) B5716241
theorem B2541071 : Blo 1505449 2541071 := bstep (se 1 (by rfl) ⟨1905803, by rfl⟩ : syracuseStep 2541071 = 3811607) B3811607
theorem B4073075 : Blo 1505449 4073075 := bstep (se 1 (by rfl) ⟨3054806, by rfl⟩ : syracuseStep 4073075 = 6109613) B6109613
theorem B85894835 : Blo 1505449 85894835 := bstep (se 1 (by rfl) ⟨64421126, by rfl⟩ : syracuseStep 85894835 = 128842253) B128842253
theorem B5719841 : Blo 1505449 5719841 := bstep (se 2 (by rfl) ⟨2144940, by rfl⟩ : syracuseStep 5719841 = 4289881) B4289881
theorem B5080967 : Blo 1505449 5080967 := bstep (se 1 (by rfl) ⟨3810725, by rfl⟩ : syracuseStep 5080967 = 7621451) B7621451
theorem B2320391 : Blo 1505449 2320391 := bstep (se 1 (by rfl) ⟨1740293, by rfl⟩ : syracuseStep 2320391 = 3480587) B3480587
theorem B2541611 : Blo 1505449 2541611 := bstep (se 1 (by rfl) ⟨1906208, by rfl⟩ : syracuseStep 2541611 = 3812417) B3812417
theorem B3811475 : Blo 1505449 3811475 := bstep (se 1 (by rfl) ⟨2858606, by rfl⟩ : syracuseStep 3811475 = 5717213) B5717213
theorem B5081345 : Blo 1505449 5081345 := bstep (se 2 (by rfl) ⟨1905504, by rfl⟩ : syracuseStep 5081345 = 3811009) B3811009
theorem B15083921 : Blo 1505449 15083921 := bstep (se 2 (by rfl) ⟨5656470, by rfl⟩ : syracuseStep 15083921 = 11312941) B11312941
theorem B8145305 : Blo 1505449 8145305 := bstep (se 2 (by rfl) ⟨3054489, by rfl⟩ : syracuseStep 8145305 = 6108979) B6108979
theorem B3811769 : Blo 1505449 3811769 := bstep (se 2 (by rfl) ⟨1429413, by rfl⟩ : syracuseStep 3811769 = 2858827) B2858827
theorem B2542009 : Blo 1505449 2542009 := bstep (se 2 (by rfl) ⟨953253, by rfl⟩ : syracuseStep 2542009 = 1906507) B1906507
theorem B5720813 : Blo 1505449 5720813 := bstep (se 3 (by rfl) ⟨1072652, by rfl⟩ : syracuseStep 5720813 = 2145305) B2145305
theorem B2173703 : Blo 1505449 2173703 := bstep (se 1 (by rfl) ⟨1630277, by rfl⟩ : syracuseStep 2173703 = 3260555) B3260555
theorem B5082155 : Blo 1505449 5082155 := bstep (se 1 (by rfl) ⟨3811616, by rfl⟩ : syracuseStep 5082155 = 7623233) B7623233
theorem B5721131 : Blo 1505449 5721131 := bstep (se 1 (by rfl) ⟨4290848, by rfl⟩ : syracuseStep 5721131 = 8581697) B8581697
theorem B3812467 : Blo 1505449 3812467 := bstep (se 1 (by rfl) ⟨2859350, by rfl⟩ : syracuseStep 3812467 = 5718701) B5718701
theorem B2542711 : Blo 1505449 2542711 := bstep (se 1 (by rfl) ⟨1907033, by rfl⟩ : syracuseStep 2542711 = 3814067) B3814067
theorem B3812609 : Blo 1505449 3812609 := bstep (se 2 (by rfl) ⟨1429728, by rfl⟩ : syracuseStep 3812609 = 2859457) B2859457
theorem B2542907 : Blo 1505449 2542907 := bstep (se 1 (by rfl) ⟨1907180, by rfl⟩ : syracuseStep 2542907 = 3814361) B3814361
theorem B12865027 : Blo 1505449 12865027 := bstep (se 1 (by rfl) ⟨9648770, by rfl⟩ : syracuseStep 12865027 = 19297541) B19297541
theorem B32566859 : Blo 1505449 32566859 := bstep (se 1 (by rfl) ⟨24425144, by rfl⟩ : syracuseStep 32566859 = 48850289) B48850289
theorem B4288115 : Blo 1505449 4288115 := bstep (se 1 (by rfl) ⟨3216086, by rfl⟩ : syracuseStep 4288115 = 6432173) B6432173
theorem B3813065 : Blo 1505449 3813065 := bstep (se 2 (by rfl) ⟨1429899, by rfl⟩ : syracuseStep 3813065 = 2859799) B2859799
theorem B2035499 : Blo 1505449 2035499 := bstep (se 1 (by rfl) ⟨1526624, by rfl⟩ : syracuseStep 2035499 = 3053249) B3053249
theorem B8580923 : Blo 1505449 8580923 := bstep (se 1 (by rfl) ⟨6435692, by rfl⟩ : syracuseStep 8580923 = 12871385) B12871385
theorem B7622585 : Blo 1505449 7622585 := bstep (se 2 (by rfl) ⟨2858469, by rfl⟩ : syracuseStep 7622585 = 5716939) B5716939
theorem B4288457 : Blo 1505449 4288457 := bstep (se 2 (by rfl) ⟨1608171, by rfl⟩ : syracuseStep 4288457 = 3216343) B3216343
theorem B14479307 : Blo 1505449 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B3813419 : Blo 1505449 3813419 := bstep (se 1 (by rfl) ⟨2860064, by rfl⟩ : syracuseStep 3813419 = 5720129) B5720129
theorem B4288571 : Blo 1505449 4288571 := bstep (se 1 (by rfl) ⟨3216428, by rfl⟩ : syracuseStep 4288571 = 6432857) B6432857
theorem B8138819 : Blo 1505449 8138819 := bstep (se 1 (by rfl) ⟨6104114, by rfl⟩ : syracuseStep 8138819 = 12208229) B12208229
theorem B3387527 : Blo 1505449 3387527 := bstep (se 1 (by rfl) ⟨2540645, by rfl⟩ : syracuseStep 3387527 = 5081291) B5081291
theorem B4288697 : Blo 1505449 4288697 := bstep (se 2 (by rfl) ⟨1608261, by rfl⟩ : syracuseStep 4288697 = 3216523) B3216523
theorem B8138989 : Blo 1505449 8138989 := bstep (se 3 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 8138989 = 3052121) B3052121
theorem B3387707 : Blo 1505449 3387707 := bstep (se 1 (by rfl) ⟨2540780, by rfl⟩ : syracuseStep 3387707 = 5081561) B5081561
theorem B5083451 : Blo 1505449 5083451 := bstep (se 1 (by rfl) ⟨3812588, by rfl⟩ : syracuseStep 5083451 = 7625177) B7625177
theorem B3387833 : Blo 1505449 3387833 := bstep (se 2 (by rfl) ⟨1270437, by rfl⟩ : syracuseStep 3387833 = 2540875) B2540875
theorem B5427665 : Blo 1505449 5427665 := bstep (se 2 (by rfl) ⟨2035374, by rfl⟩ : syracuseStep 5427665 = 4070749) B4070749
theorem B3617291 : Blo 1505449 3617291 := bstep (se 1 (by rfl) ⟨2712968, by rfl⟩ : syracuseStep 3617291 = 5425937) B5425937
theorem B3388175 : Blo 1505449 3388175 := bstep (se 1 (by rfl) ⟨2541131, by rfl⟩ : syracuseStep 3388175 = 5082263) B5082263
theorem B3388193 : Blo 1505449 3388193 := bstep (se 2 (by rfl) ⟨1270572, by rfl⟩ : syracuseStep 3388193 = 2541145) B2541145
theorem B5083937 : Blo 1505449 5083937 := bstep (se 2 (by rfl) ⟨1906476, by rfl⟩ : syracuseStep 5083937 = 3812953) B3812953
theorem B2446139 : Blo 1505449 2446139 := bstep (se 1 (by rfl) ⟨1834604, by rfl⟩ : syracuseStep 2446139 = 3669209) B3669209
theorem B3814411 : Blo 1505449 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B1905707 : Blo 1505449 1905707 := bstep (se 1 (by rfl) ⟨1429280, by rfl⟩ : syracuseStep 1905707 = 2858561) B2858561
theorem B3388535 : Blo 1505449 3388535 := bstep (se 1 (by rfl) ⟨2541401, by rfl⟩ : syracuseStep 3388535 = 5082803) B5082803
theorem B7623881 : Blo 1505449 7623881 := bstep (se 2 (by rfl) ⟨2858955, by rfl⟩ : syracuseStep 7623881 = 5717911) B5717911
theorem B8582381 : Blo 1505449 8582381 := bstep (se 3 (by rfl) ⟨1609196, by rfl⟩ : syracuseStep 8582381 = 3218393) B3218393
theorem B9286913 : Blo 1505449 9286913 := bstep (se 2 (by rfl) ⟨3482592, by rfl⟩ : syracuseStep 9286913 = 6965185) B6965185
theorem B2258183 : Blo 1505449 2258183 := bstep (se 1 (by rfl) ⟨1693637, by rfl⟩ : syracuseStep 2258183 = 3387275) B3387275
theorem B2258219 : Blo 1505449 2258219 := bstep (se 1 (by rfl) ⟨1693664, by rfl⟩ : syracuseStep 2258219 = 3387329) B3387329
theorem B3388715 : Blo 1505449 3388715 := bstep (se 1 (by rfl) ⟨2541536, by rfl⟩ : syracuseStep 3388715 = 5083073) B5083073
theorem B7238963 : Blo 1505449 7238963 := bstep (se 1 (by rfl) ⟨5429222, by rfl⟩ : syracuseStep 7238963 = 10858445) B10858445
theorem B2258249 : Blo 1505449 2258249 := bstep (se 2 (by rfl) ⟨846843, by rfl⟩ : syracuseStep 2258249 = 1693687) B1693687
theorem B5084531 : Blo 1505449 5084531 := bstep (se 1 (by rfl) ⟨3813398, by rfl⟩ : syracuseStep 5084531 = 7626797) B7626797
theorem B3618233 : Blo 1505449 3618233 := bstep (se 2 (by rfl) ⟨1356837, by rfl⟩ : syracuseStep 3618233 = 2713675) B2713675
theorem B2258363 : Blo 1505449 2258363 := bstep (se 1 (by rfl) ⟨1693772, by rfl⟩ : syracuseStep 2258363 = 3387545) B3387545
theorem B2258423 : Blo 1505449 2258423 := bstep (se 1 (by rfl) ⟨1693817, by rfl⟩ : syracuseStep 2258423 = 3387635) B3387635
theorem B1906183 : Blo 1505449 1906183 := bstep (se 1 (by rfl) ⟨1429637, by rfl⟩ : syracuseStep 1906183 = 2859275) B2859275
theorem B2258447 : Blo 1505449 2258447 := bstep (se 1 (by rfl) ⟨1693835, by rfl⟩ : syracuseStep 2258447 = 3387671) B3387671
theorem B2258489 : Blo 1505449 2258489 := bstep (se 2 (by rfl) ⟨846933, by rfl⟩ : syracuseStep 2258489 = 1693867) B1693867
theorem B2258567 : Blo 1505449 2258567 := bstep (se 1 (by rfl) ⟨1693925, by rfl⟩ : syracuseStep 2258567 = 3387851) B3387851
theorem B1717895 : Blo 1505449 1717895 := bstep (se 1 (by rfl) ⟨1288421, by rfl⟩ : syracuseStep 1717895 = 2576843) B2576843
theorem B3389075 : Blo 1505449 3389075 := bstep (se 1 (by rfl) ⟨2541806, by rfl⟩ : syracuseStep 3389075 = 5083613) B5083613
theorem B3217043 : Blo 1505449 3217043 := bstep (se 1 (by rfl) ⟨2412782, by rfl⟩ : syracuseStep 3217043 = 4825565) B4825565
theorem B2258603 : Blo 1505449 2258603 := bstep (se 1 (by rfl) ⟨1693952, by rfl⟩ : syracuseStep 2258603 = 3387905) B3387905
theorem B2258633 : Blo 1505449 2258633 := bstep (se 2 (by rfl) ⟨846987, by rfl⟩ : syracuseStep 2258633 = 1693975) B1693975
theorem B3389129 : Blo 1505449 3389129 := bstep (se 2 (by rfl) ⟨1270923, by rfl⟩ : syracuseStep 3389129 = 2541847) B2541847
theorem B48297701 : Blo 1505449 48297701 := bstep (se 4 (by rfl) ⟨4527909, by rfl⟩ : syracuseStep 48297701 = 9055819) B9055819
theorem B4290347 : Blo 1505449 4290347 := bstep (se 1 (by rfl) ⟨3217760, by rfl⟩ : syracuseStep 4290347 = 6435521) B6435521
theorem B2258747 : Blo 1505449 2258747 := bstep (se 1 (by rfl) ⟨1694060, by rfl⟩ : syracuseStep 2258747 = 3388121) B3388121
theorem B5429051 : Blo 1505449 5429051 := bstep (se 1 (by rfl) ⟨4071788, by rfl⟩ : syracuseStep 5429051 = 8143577) B8143577
theorem B2258807 : Blo 1505449 2258807 := bstep (se 1 (by rfl) ⟨1694105, by rfl⟩ : syracuseStep 2258807 = 3388211) B3388211
theorem B2258831 : Blo 1505449 2258831 := bstep (se 1 (by rfl) ⟨1694123, by rfl⟩ : syracuseStep 2258831 = 3388247) B3388247
theorem B2258873 : Blo 1505449 2258873 := bstep (se 2 (by rfl) ⟨847077, by rfl⟩ : syracuseStep 2258873 = 1694155) B1694155
theorem B1906679 : Blo 1505449 1906679 := bstep (se 1 (by rfl) ⟨1430009, by rfl⟩ : syracuseStep 1906679 = 2860019) B2860019
theorem B2258951 : Blo 1505449 2258951 := bstep (se 1 (by rfl) ⟨1694213, by rfl⟩ : syracuseStep 2258951 = 3388427) B3388427
theorem B2258987 : Blo 1505449 2258987 := bstep (se 1 (by rfl) ⟨1694240, by rfl⟩ : syracuseStep 2258987 = 3388481) B3388481
theorem B2259017 : Blo 1505449 2259017 := bstep (se 2 (by rfl) ⟨847131, by rfl⟩ : syracuseStep 2259017 = 1694263) B1694263
theorem B1693831 : Blo 1505449 1693831 := bstep (se 1 (by rfl) ⟨1270373, by rfl⟩ : syracuseStep 1693831 = 2540747) B2540747
theorem B2144399 : Blo 1505449 2144399 := bstep (se 1 (by rfl) ⟨1608299, by rfl⟩ : syracuseStep 2144399 = 3216599) B3216599
theorem B1906831 : Blo 1505449 1906831 := bstep (se 1 (by rfl) ⟨1430123, by rfl⟩ : syracuseStep 1906831 = 2860247) B2860247
theorem B4069529 : Blo 1505449 4069529 := bstep (se 2 (by rfl) ⟨1526073, by rfl⟩ : syracuseStep 4069529 = 3052147) B3052147
theorem B1505467 : Blo 1505449 1505467 := bstep (se 1 (by rfl) ⟨1129100, by rfl⟩ : syracuseStep 1505467 = 2258201) B2258201
theorem B2259131 : Blo 1505449 2259131 := bstep (se 1 (by rfl) ⟨1694348, by rfl⟩ : syracuseStep 2259131 = 3388697) B3388697
theorem B2259191 : Blo 1505449 2259191 := bstep (se 1 (by rfl) ⟨1694393, by rfl⟩ : syracuseStep 2259191 = 3388787) B3388787
theorem B1505543 : Blo 1505449 1505543 := bstep (se 1 (by rfl) ⟨1129157, by rfl⟩ : syracuseStep 1505543 = 2258315) B2258315
theorem B1505551 : Blo 1505449 1505551 := bstep (se 1 (by rfl) ⟨1129163, by rfl⟩ : syracuseStep 1505551 = 2258327) B2258327
theorem B2259215 : Blo 1505449 2259215 := bstep (se 1 (by rfl) ⟨1694411, by rfl⟩ : syracuseStep 2259215 = 3388823) B3388823
theorem B9156901 : Blo 1505449 9156901 := bstep (se 4 (by rfl) ⟨858459, by rfl⟩ : syracuseStep 9156901 = 1716919) B1716919
theorem B2259257 : Blo 1505449 2259257 := bstep (se 2 (by rfl) ⟨847221, by rfl⟩ : syracuseStep 2259257 = 1694443) B1694443
theorem B1505595 : Blo 1505449 1505595 := bstep (se 1 (by rfl) ⟨1129196, by rfl⟩ : syracuseStep 1505595 = 2258393) B2258393
theorem B1694011 : Blo 1505449 1694011 := bstep (se 1 (by rfl) ⟨1270508, by rfl⟩ : syracuseStep 1694011 = 2541017) B2541017
theorem B1907003 : Blo 1505449 1907003 := bstep (se 1 (by rfl) ⟨1430252, by rfl⟩ : syracuseStep 1907003 = 2860505) B2860505
theorem B1505671 : Blo 1505449 1505671 := bstep (se 1 (by rfl) ⟨1129253, by rfl⟩ : syracuseStep 1505671 = 2258507) B2258507
theorem B2259335 : Blo 1505449 2259335 := bstep (se 1 (by rfl) ⟨1694501, by rfl⟩ : syracuseStep 2259335 = 3389003) B3389003
theorem B3389831 : Blo 1505449 3389831 := bstep (se 1 (by rfl) ⟨2542373, by rfl⟩ : syracuseStep 3389831 = 5084747) B5084747
theorem B1505679 : Blo 1505449 1505679 := bstep (se 1 (by rfl) ⟨1129259, by rfl⟩ : syracuseStep 1505679 = 2258519) B2258519
theorem B8255891 : Blo 1505449 8255891 := bstep (se 1 (by rfl) ⟨6191918, by rfl⟩ : syracuseStep 8255891 = 12383837) B12383837
theorem B2259371 : Blo 1505449 2259371 := bstep (se 1 (by rfl) ⟨1694528, by rfl⟩ : syracuseStep 2259371 = 3389057) B3389057
theorem B1505723 : Blo 1505449 1505723 := bstep (se 1 (by rfl) ⟨1129292, by rfl⟩ : syracuseStep 1505723 = 2258585) B2258585
theorem B2259401 : Blo 1505449 2259401 := bstep (se 2 (by rfl) ⟨847275, by rfl⟩ : syracuseStep 2259401 = 1694551) B1694551
theorem B2144713 : Blo 1505449 2144713 := bstep (se 2 (by rfl) ⟨804267, by rfl⟩ : syracuseStep 2144713 = 1608535) B1608535
theorem B33479153 : Blo 1505449 33479153 := bstep (se 2 (by rfl) ⟨12554682, by rfl⟩ : syracuseStep 33479153 = 25109365) B25109365
theorem B1505799 : Blo 1505449 1505799 := bstep (se 1 (by rfl) ⟨1129349, by rfl⟩ : syracuseStep 1505799 = 2258699) B2258699
theorem B1505807 : Blo 1505449 1505807 := bstep (se 1 (by rfl) ⟨1129355, by rfl⟩ : syracuseStep 1505807 = 2258711) B2258711
theorem B12212765 : Blo 1505449 12212765 := bstep (se 3 (by rfl) ⟨2289893, by rfl⟩ : syracuseStep 12212765 = 4579787) B4579787
theorem B3865121 : Blo 1505449 3865121 := bstep (se 2 (by rfl) ⟨1449420, by rfl⟩ : syracuseStep 3865121 = 2898841) B2898841
theorem B1505851 : Blo 1505449 1505851 := bstep (se 1 (by rfl) ⟨1129388, by rfl⟩ : syracuseStep 1505851 = 2258777) B2258777
theorem B2259515 : Blo 1505449 2259515 := bstep (se 1 (by rfl) ⟨1694636, by rfl⟩ : syracuseStep 2259515 = 3389273) B3389273
theorem B3390011 : Blo 1505449 3390011 := bstep (se 1 (by rfl) ⟨2542508, by rfl⟩ : syracuseStep 3390011 = 5085017) B5085017
theorem B18315841 : Blo 1505449 18315841 := bstep (se 2 (by rfl) ⟨6868440, by rfl⟩ : syracuseStep 18315841 = 13736881) B13736881
theorem B2259575 : Blo 1505449 2259575 := bstep (se 1 (by rfl) ⟨1694681, by rfl⟩ : syracuseStep 2259575 = 3389363) B3389363
theorem B1505927 : Blo 1505449 1505927 := bstep (se 1 (by rfl) ⟨1129445, by rfl⟩ : syracuseStep 1505927 = 2258891) B2258891
theorem B3717767 : Blo 1505449 3717767 := bstep (se 1 (by rfl) ⟨2788325, by rfl⟩ : syracuseStep 3717767 = 5576651) B5576651
theorem B1505935 : Blo 1505449 1505935 := bstep (se 1 (by rfl) ⟨1129451, by rfl⟩ : syracuseStep 1505935 = 2258903) B2258903
theorem B2259599 : Blo 1505449 2259599 := bstep (se 1 (by rfl) ⟨1694699, by rfl⟩ : syracuseStep 2259599 = 3389399) B3389399
theorem B2259641 : Blo 1505449 2259641 := bstep (se 2 (by rfl) ⟨847365, by rfl⟩ : syracuseStep 2259641 = 1694731) B1694731
theorem B3390137 : Blo 1505449 3390137 := bstep (se 2 (by rfl) ⟨1271301, by rfl⟩ : syracuseStep 3390137 = 2542603) B2542603
theorem B1505979 : Blo 1505449 1505979 := bstep (se 1 (by rfl) ⟨1129484, by rfl⟩ : syracuseStep 1505979 = 2258969) B2258969
theorem B1506055 : Blo 1505449 1506055 := bstep (se 1 (by rfl) ⟨1129541, by rfl⟩ : syracuseStep 1506055 = 2259083) B2259083
theorem B2259719 : Blo 1505449 2259719 := bstep (se 1 (by rfl) ⟨1694789, by rfl⟩ : syracuseStep 2259719 = 3389579) B3389579
theorem B1506063 : Blo 1505449 1506063 := bstep (se 1 (by rfl) ⟨1129547, by rfl⟩ : syracuseStep 1506063 = 2259095) B2259095
theorem B1694479 : Blo 1505449 1694479 := bstep (se 1 (by rfl) ⟨1270859, by rfl⟩ : syracuseStep 1694479 = 2541719) B2541719
theorem B6626081 : Blo 1505449 6626081 := bstep (se 2 (by rfl) ⟨2484780, by rfl⟩ : syracuseStep 6626081 = 4969561) B4969561
theorem B2259755 : Blo 1505449 2259755 := bstep (se 1 (by rfl) ⟨1694816, by rfl⟩ : syracuseStep 2259755 = 3389633) B3389633
theorem B1506107 : Blo 1505449 1506107 := bstep (se 1 (by rfl) ⟨1129580, by rfl⟩ : syracuseStep 1506107 = 2259161) B2259161
theorem B2259785 : Blo 1505449 2259785 := bstep (se 2 (by rfl) ⟨847419, by rfl⟩ : syracuseStep 2259785 = 1694839) B1694839
theorem B1506183 : Blo 1505449 1506183 := bstep (se 1 (by rfl) ⟨1129637, by rfl⟩ : syracuseStep 1506183 = 2259275) B2259275
theorem B1506191 : Blo 1505449 1506191 := bstep (se 1 (by rfl) ⟨1129643, by rfl⟩ : syracuseStep 1506191 = 2259287) B2259287
theorem B1506235 : Blo 1505449 1506235 := bstep (se 1 (by rfl) ⟨1129676, by rfl⟩ : syracuseStep 1506235 = 2259353) B2259353
theorem B2259899 : Blo 1505449 2259899 := bstep (se 1 (by rfl) ⟨1694924, by rfl⟩ : syracuseStep 2259899 = 3389849) B3389849
theorem B2259959 : Blo 1505449 2259959 := bstep (se 1 (by rfl) ⟨1694969, by rfl⟩ : syracuseStep 2259959 = 3389939) B3389939
theorem B1506311 : Blo 1505449 1506311 := bstep (se 1 (by rfl) ⟨1129733, by rfl⟩ : syracuseStep 1506311 = 2259467) B2259467
theorem B1506319 : Blo 1505449 1506319 := bstep (se 1 (by rfl) ⟨1129739, by rfl⟩ : syracuseStep 1506319 = 2259479) B2259479
theorem B2259983 : Blo 1505449 2259983 := bstep (se 1 (by rfl) ⟨1694987, by rfl⟩ : syracuseStep 2259983 = 3389975) B3389975
theorem B3390479 : Blo 1505449 3390479 := bstep (se 1 (by rfl) ⟨2542859, by rfl⟩ : syracuseStep 3390479 = 5085719) B5085719
theorem B3390497 : Blo 1505449 3390497 := bstep (se 2 (by rfl) ⟨1271436, by rfl⟩ : syracuseStep 3390497 = 2542873) B2542873
theorem B2260025 : Blo 1505449 2260025 := bstep (se 2 (by rfl) ⟨847509, by rfl⟩ : syracuseStep 2260025 = 1695019) B1695019
theorem B1506363 : Blo 1505449 1506363 := bstep (se 1 (by rfl) ⟨1129772, by rfl⟩ : syracuseStep 1506363 = 2259545) B2259545
theorem B1506439 : Blo 1505449 1506439 := bstep (se 1 (by rfl) ⟨1129829, by rfl⟩ : syracuseStep 1506439 = 2259659) B2259659
theorem B2260103 : Blo 1505449 2260103 := bstep (se 1 (by rfl) ⟨1695077, by rfl⟩ : syracuseStep 2260103 = 3390155) B3390155
theorem B1506447 : Blo 1505449 1506447 := bstep (se 1 (by rfl) ⟨1129835, by rfl⟩ : syracuseStep 1506447 = 2259671) B2259671
theorem B2260139 : Blo 1505449 2260139 := bstep (se 1 (by rfl) ⟨1695104, by rfl⟩ : syracuseStep 2260139 = 3390209) B3390209
theorem B1506491 : Blo 1505449 1506491 := bstep (se 1 (by rfl) ⟨1129868, by rfl⟩ : syracuseStep 1506491 = 2259737) B2259737
theorem B2260169 : Blo 1505449 2260169 := bstep (se 2 (by rfl) ⟨847563, by rfl⟩ : syracuseStep 2260169 = 1695127) B1695127
theorem B1506567 : Blo 1505449 1506567 := bstep (se 1 (by rfl) ⟨1129925, by rfl⟩ : syracuseStep 1506567 = 2259851) B2259851
theorem B1694983 : Blo 1505449 1694983 := bstep (se 1 (by rfl) ⟨1271237, by rfl⟩ : syracuseStep 1694983 = 2542475) B2542475
theorem B4824335 : Blo 1505449 4824335 := bstep (se 1 (by rfl) ⟨3618251, by rfl⟩ : syracuseStep 4824335 = 7236503) B7236503
theorem B1506575 : Blo 1505449 1506575 := bstep (se 1 (by rfl) ⟨1129931, by rfl⟩ : syracuseStep 1506575 = 2259863) B2259863
theorem B1506619 : Blo 1505449 1506619 := bstep (se 1 (by rfl) ⟨1129964, by rfl⟩ : syracuseStep 1506619 = 2259929) B2259929
theorem B2260283 : Blo 1505449 2260283 := bstep (se 1 (by rfl) ⟨1695212, by rfl⟩ : syracuseStep 2260283 = 3390425) B3390425
theorem B44039483 : Blo 1505449 44039483 := bstep (se 1 (by rfl) ⟨33029612, by rfl⟩ : syracuseStep 44039483 = 66059225) B66059225
theorem B2260343 : Blo 1505449 2260343 := bstep (se 1 (by rfl) ⟨1695257, by rfl⟩ : syracuseStep 2260343 = 3390515) B3390515
theorem B1506695 : Blo 1505449 1506695 := bstep (se 1 (by rfl) ⟨1130021, by rfl⟩ : syracuseStep 1506695 = 2260043) B2260043
theorem B1506703 : Blo 1505449 1506703 := bstep (se 1 (by rfl) ⟨1130027, by rfl⟩ : syracuseStep 1506703 = 2260055) B2260055
theorem B2260367 : Blo 1505449 2260367 := bstep (se 1 (by rfl) ⟨1695275, by rfl⟩ : syracuseStep 2260367 = 3390551) B3390551
theorem B4578707 : Blo 1505449 4578707 := bstep (se 1 (by rfl) ⟨3434030, by rfl⟩ : syracuseStep 4578707 = 6868061) B6868061
theorem B2260409 : Blo 1505449 2260409 := bstep (se 2 (by rfl) ⟨847653, by rfl⟩ : syracuseStep 2260409 = 1695307) B1695307
theorem B1506747 : Blo 1505449 1506747 := bstep (se 1 (by rfl) ⟨1130060, by rfl⟩ : syracuseStep 1506747 = 2260121) B2260121
theorem B1695163 : Blo 1505449 1695163 := bstep (se 1 (by rfl) ⟨1271372, by rfl⟩ : syracuseStep 1695163 = 2542745) B2542745
theorem B1506823 : Blo 1505449 1506823 := bstep (se 1 (by rfl) ⟨1130117, by rfl⟩ : syracuseStep 1506823 = 2260235) B2260235
theorem B1506831 : Blo 1505449 1506831 := bstep (se 1 (by rfl) ⟨1130123, by rfl⟩ : syracuseStep 1506831 = 2260247) B2260247
theorem B12213803 : Blo 1505449 12213803 := bstep (se 1 (by rfl) ⟨9160352, by rfl⟩ : syracuseStep 12213803 = 18320705) B18320705
theorem B1506875 : Blo 1505449 1506875 := bstep (se 1 (by rfl) ⟨1130156, by rfl⟩ : syracuseStep 1506875 = 2260313) B2260313
theorem B28958309 : Blo 1505449 28958309 := bstep (se 4 (by rfl) ⟨2714841, by rfl⟩ : syracuseStep 28958309 = 5429683) B5429683
theorem B13745783 : Blo 1505449 13745783 := bstep (se 1 (by rfl) ⟨10309337, by rfl⟩ : syracuseStep 13745783 = 20618675) B20618675
theorem B8363749 : Blo 1505449 8363749 := bstep (se 4 (by rfl) ⟨784101, by rfl⟩ : syracuseStep 8363749 = 1568203) B1568203
theorem B1810183 : Blo 1505449 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B7339835 : Blo 1505449 7339835 := bstep (se 1 (by rfl) ⟨5504876, by rfl⟩ : syracuseStep 7339835 = 11009753) B11009753
theorem B18816857 : Blo 1505449 18816857 := bstep (se 2 (by rfl) ⟨7056321, by rfl⟩ : syracuseStep 18816857 = 14112643) B14112643
theorem B9912179 : Blo 1505449 9912179 := bstep (se 1 (by rfl) ⟨7434134, by rfl⟩ : syracuseStep 9912179 = 14868269) B14868269
theorem B9781145 : Blo 1505449 9781145 := bstep (se 2 (by rfl) ⟨3667929, by rfl⟩ : syracuseStep 9781145 = 7335859) B7335859
theorem B2859047 : Blo 1505449 2859047 := bstep (se 1 (by rfl) ⟨2144285, by rfl⟩ : syracuseStep 2859047 = 4288571) B4288571
theorem B2859131 : Blo 1505449 2859131 := bstep (se 1 (by rfl) ⟨2144348, by rfl⟩ : syracuseStep 2859131 = 4288697) B4288697
theorem B5718397 : Blo 1505449 5718397 := bstep (se 3 (by rfl) ⟨1072199, by rfl⟩ : syracuseStep 5718397 = 2144399) B2144399
theorem B2859617 : Blo 1505449 2859617 := bstep (se 2 (by rfl) ⟨1072356, by rfl⟩ : syracuseStep 2859617 = 2144713) B2144713
theorem B24421121 : Blo 1505449 24421121 := bstep (se 2 (by rfl) ⟨9157920, by rfl⟩ : syracuseStep 24421121 = 18315841) B18315841
theorem B4825975 : Blo 1505449 4825975 := bstep (se 1 (by rfl) ⟨3619481, by rfl⟩ : syracuseStep 4825975 = 7238963) B7238963
theorem B2540551 : Blo 1505449 2540551 := bstep (se 1 (by rfl) ⟨1905413, by rfl⟩ : syracuseStep 2540551 = 3810827) B3810827
theorem B2540983 : Blo 1505449 2540983 := bstep (se 1 (by rfl) ⟨1905737, by rfl⟩ : syracuseStep 2540983 = 3811475) B3811475
theorem B2713019 : Blo 1505449 2713019 := bstep (se 1 (by rfl) ⟨2034764, by rfl⟩ : syracuseStep 2713019 = 4069529) B4069529
theorem B2541179 : Blo 1505449 2541179 := bstep (se 1 (by rfl) ⟨1905884, by rfl⟩ : syracuseStep 2541179 = 3811769) B3811769
theorem B4581053 : Blo 1505449 4581053 := bstep (se 3 (by rfl) ⟨858947, by rfl⟩ : syracuseStep 4581053 = 1717895) B1717895
theorem B8578781 : Blo 1505449 8578781 := bstep (se 3 (by rfl) ⟨1608521, by rfl⟩ : syracuseStep 8578781 = 3217043) B3217043
theorem B11438009 : Blo 1505449 11438009 := bstep (se 2 (by rfl) ⟨4289253, by rfl⟩ : syracuseStep 11438009 = 8578507) B8578507
theorem B2541577 : Blo 1505449 2541577 := bstep (se 2 (by rfl) ⟨953091, by rfl⟩ : syracuseStep 2541577 = 1906183) B1906183
theorem B6523037 : Blo 1505449 6523037 := bstep (se 3 (by rfl) ⟨1223069, by rfl⟩ : syracuseStep 6523037 = 2446139) B2446139
theorem B2541739 : Blo 1505449 2541739 := bstep (se 1 (by rfl) ⟨1906304, by rfl⟩ : syracuseStep 2541739 = 3812609) B3812609
theorem B11151665 : Blo 1505449 11151665 := bstep (se 2 (by rfl) ⟨4181874, by rfl⟩ : syracuseStep 11151665 = 8363749) B8363749
theorem B21711239 : Blo 1505449 21711239 := bstep (se 1 (by rfl) ⟨16283429, by rfl⟩ : syracuseStep 21711239 = 32566859) B32566859
theorem B2542043 : Blo 1505449 2542043 := bstep (se 1 (by rfl) ⟨1906532, by rfl⟩ : syracuseStep 2542043 = 3813065) B3813065
theorem B5720615 : Blo 1505449 5720615 := bstep (se 1 (by rfl) ⟨4290461, by rfl⟩ : syracuseStep 5720615 = 8580923) B8580923
theorem B4893223 : Blo 1505449 4893223 := bstep (se 1 (by rfl) ⟨3669917, by rfl⟩ : syracuseStep 4893223 = 7339835) B7339835
theorem B12544571 : Blo 1505449 12544571 := bstep (se 1 (by rfl) ⟨9408428, by rfl⟩ : syracuseStep 12544571 = 18816857) B18816857
theorem B5081723 : Blo 1505449 5081723 := bstep (se 1 (by rfl) ⟨3811292, by rfl⟩ : syracuseStep 5081723 = 7622585) B7622585
theorem B9652871 : Blo 1505449 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B6187709 : Blo 1505449 6187709 := bstep (se 3 (by rfl) ⟨1160195, by rfl⟩ : syracuseStep 6187709 = 2320391) B2320391
theorem B2542279 : Blo 1505449 2542279 := bstep (se 1 (by rfl) ⟨1906709, by rfl⟩ : syracuseStep 2542279 = 3813419) B3813419
theorem B5425879 : Blo 1505449 5425879 := bstep (se 1 (by rfl) ⟨4069409, by rfl⟩ : syracuseStep 5425879 = 8138819) B8138819
theorem B5081885 : Blo 1505449 5081885 := bstep (se 3 (by rfl) ⟨952853, by rfl⟩ : syracuseStep 5081885 = 1905707) B1905707
theorem B2542441 : Blo 1505449 2542441 := bstep (se 2 (by rfl) ⟨953415, by rfl⟩ : syracuseStep 2542441 = 1906831) B1906831
theorem B2411527 : Blo 1505449 2411527 := bstep (se 1 (by rfl) ⟨1808645, by rfl⟩ : syracuseStep 2411527 = 3617291) B3617291
theorem B12209201 : Blo 1505449 12209201 := bstep (se 2 (by rfl) ⟨4578450, by rfl⟩ : syracuseStep 12209201 = 9156901) B9156901
theorem B21711989 : Blo 1505449 21711989 := bstep (se 5 (by rfl) ⟨1017749, by rfl⟩ : syracuseStep 21711989 = 2035499) B2035499
theorem B2321531 : Blo 1505449 2321531 := bstep (se 1 (by rfl) ⟨1741148, by rfl⟩ : syracuseStep 2321531 = 3482297) B3482297
theorem B4287887 : Blo 1505449 4287887 := bstep (se 1 (by rfl) ⟨3215915, by rfl⟩ : syracuseStep 4287887 = 6431831) B6431831
theorem B5082587 : Blo 1505449 5082587 := bstep (se 1 (by rfl) ⟨3811940, by rfl⟩ : syracuseStep 5082587 = 7623881) B7623881
theorem B6434291 : Blo 1505449 6434291 := bstep (se 1 (by rfl) ⟨4825718, by rfl⟩ : syracuseStep 6434291 = 9651437) B9651437
theorem B5721587 : Blo 1505449 5721587 := bstep (se 1 (by rfl) ⟨4291190, by rfl⟩ : syracuseStep 5721587 = 8582381) B8582381
theorem B3812903 : Blo 1505449 3812903 := bstep (se 1 (by rfl) ⟨2859677, by rfl⟩ : syracuseStep 3812903 = 5719355) B5719355
theorem B2412155 : Blo 1505449 2412155 := bstep (se 1 (by rfl) ⟨1809116, by rfl⟩ : syracuseStep 2412155 = 3618233) B3618233
theorem B12209885 : Blo 1505449 12209885 := bstep (se 3 (by rfl) ⟨2289353, by rfl⟩ : syracuseStep 12209885 = 4578707) B4578707
theorem B22015709 : Blo 1505449 22015709 := bstep (se 3 (by rfl) ⟨4127945, by rfl⟩ : syracuseStep 22015709 = 8255891) B8255891
theorem B2715383 : Blo 1505449 2715383 := bstep (se 1 (by rfl) ⟨2036537, by rfl⟩ : syracuseStep 2715383 = 4073075) B4073075
theorem B32198467 : Blo 1505449 32198467 := bstep (se 1 (by rfl) ⟨24148850, by rfl⟩ : syracuseStep 32198467 = 48297701) B48297701
theorem B3813227 : Blo 1505449 3813227 := bstep (se 1 (by rfl) ⟨2859920, by rfl⟩ : syracuseStep 3813227 = 5719841) B5719841
theorem B3387311 : Blo 1505449 3387311 := bstep (se 1 (by rfl) ⟨2540483, by rfl⟩ : syracuseStep 3387311 = 5080967) B5080967
theorem B6434873 : Blo 1505449 6434873 := bstep (se 2 (by rfl) ⟨2413077, by rfl⟩ : syracuseStep 6434873 = 4826155) B4826155
theorem B5083289 : Blo 1505449 5083289 := bstep (se 2 (by rfl) ⟨1906233, by rfl⟩ : syracuseStep 5083289 = 3812467) B3812467
theorem B3387563 : Blo 1505449 3387563 := bstep (se 1 (by rfl) ⟨2540672, by rfl⟩ : syracuseStep 3387563 = 5081345) B5081345
theorem B10055947 : Blo 1505449 10055947 := bstep (se 1 (by rfl) ⟨7541960, by rfl⟩ : syracuseStep 10055947 = 15083921) B15083921
theorem B22319435 : Blo 1505449 22319435 := bstep (se 1 (by rfl) ⟨16739576, by rfl⟩ : syracuseStep 22319435 = 33479153) B33479153
theorem B2576747 : Blo 1505449 2576747 := bstep (se 1 (by rfl) ⟨1932560, by rfl⟩ : syracuseStep 2576747 = 3865121) B3865121
theorem B2478511 : Blo 1505449 2478511 := bstep (se 1 (by rfl) ⟨1858883, by rfl⟩ : syracuseStep 2478511 = 3717767) B3717767
theorem B229052893 : Blo 1505449 229052893 := bstep (se 3 (by rfl) ⟨42947417, by rfl⟩ : syracuseStep 229052893 = 85894835) B85894835
theorem B3813875 : Blo 1505449 3813875 := bstep (se 1 (by rfl) ⟨2860406, by rfl⟩ : syracuseStep 3813875 = 5720813) B5720813
theorem B5796541 : Blo 1505449 5796541 := bstep (se 3 (by rfl) ⟨1086851, by rfl⟩ : syracuseStep 5796541 = 2173703) B2173703
theorem B3388103 : Blo 1505449 3388103 := bstep (se 1 (by rfl) ⟨2541077, by rfl⟩ : syracuseStep 3388103 = 5082155) B5082155
theorem B3814087 : Blo 1505449 3814087 := bstep (se 1 (by rfl) ⟨2860565, by rfl⟩ : syracuseStep 3814087 = 5721131) B5721131
theorem B11440925 : Blo 1505449 11440925 := bstep (se 3 (by rfl) ⟨2145173, by rfl⟩ : syracuseStep 11440925 = 4290347) B4290347
theorem B3216223 : Blo 1505449 3216223 := bstep (se 1 (by rfl) ⟨2412167, by rfl⟩ : syracuseStep 3216223 = 4824335) B4824335
theorem B26432477 : Blo 1505449 26432477 := bstep (se 3 (by rfl) ⟨4956089, by rfl⟩ : syracuseStep 26432477 = 9912179) B9912179
theorem B2413577 : Blo 1505449 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B19305539 : Blo 1505449 19305539 := bstep (se 1 (by rfl) ⟨14479154, by rfl⟩ : syracuseStep 19305539 = 28958309) B28958309
theorem B9163855 : Blo 1505449 9163855 := bstep (se 1 (by rfl) ⟨6872891, by rfl⟩ : syracuseStep 9163855 = 13745783) B13745783
theorem B5084477 : Blo 1505449 5084477 := bstep (se 3 (by rfl) ⟨953339, by rfl⟩ : syracuseStep 5084477 = 1906679) B1906679
theorem B2258351 : Blo 1505449 2258351 := bstep (se 1 (by rfl) ⟨1693763, by rfl⟩ : syracuseStep 2258351 = 3387527) B3387527
theorem B2258441 : Blo 1505449 2258441 := bstep (se 2 (by rfl) ⟨846915, by rfl⟩ : syracuseStep 2258441 = 1693831) B1693831
theorem B22304267 : Blo 1505449 22304267 := bstep (se 1 (by rfl) ⟨16728200, by rfl⟩ : syracuseStep 22304267 = 33456401) B33456401
theorem B2258471 : Blo 1505449 2258471 := bstep (se 1 (by rfl) ⟨1693853, by rfl⟩ : syracuseStep 2258471 = 3387707) B3387707
theorem B3388967 : Blo 1505449 3388967 := bstep (se 1 (by rfl) ⟨2541725, by rfl⟩ : syracuseStep 3388967 = 5083451) B5083451
theorem B2258555 : Blo 1505449 2258555 := bstep (se 1 (by rfl) ⟨1693916, by rfl⟩ : syracuseStep 2258555 = 3387833) B3387833
theorem B3618443 : Blo 1505449 3618443 := bstep (se 1 (by rfl) ⟨2713832, by rfl⟩ : syracuseStep 3618443 = 5427665) B5427665
theorem B10851985 : Blo 1505449 10851985 := bstep (se 2 (by rfl) ⟨4069494, by rfl⟩ : syracuseStep 10851985 = 8138989) B8138989
theorem B2258681 : Blo 1505449 2258681 := bstep (se 2 (by rfl) ⟨847005, by rfl⟩ : syracuseStep 2258681 = 1694011) B1694011
theorem B2258783 : Blo 1505449 2258783 := bstep (se 1 (by rfl) ⟨1694087, by rfl⟩ : syracuseStep 2258783 = 3388175) B3388175
theorem B2258795 : Blo 1505449 2258795 := bstep (se 1 (by rfl) ⟨1694096, by rfl⟩ : syracuseStep 2258795 = 3388193) B3388193
theorem B3389291 : Blo 1505449 3389291 := bstep (se 1 (by rfl) ⟨2541968, by rfl⟩ : syracuseStep 3389291 = 5083937) B5083937
theorem B3389345 : Blo 1505449 3389345 := bstep (se 2 (by rfl) ⟨1271004, by rfl⟩ : syracuseStep 3389345 = 2542009) B2542009
theorem B2259023 : Blo 1505449 2259023 := bstep (se 1 (by rfl) ⟨1694267, by rfl⟩ : syracuseStep 2259023 = 3388535) B3388535
theorem B3217487 : Blo 1505449 3217487 := bstep (se 1 (by rfl) ⟨2413115, by rfl⟩ : syracuseStep 3217487 = 4826231) B4826231
theorem B4823155 : Blo 1505449 4823155 := bstep (se 1 (by rfl) ⟨3617366, by rfl⟩ : syracuseStep 4823155 = 7234733) B7234733
theorem B8575091 : Blo 1505449 8575091 := bstep (se 1 (by rfl) ⟨6431318, by rfl⟩ : syracuseStep 8575091 = 12862637) B12862637
theorem B5085341 : Blo 1505449 5085341 := bstep (se 3 (by rfl) ⟨953501, by rfl⟩ : syracuseStep 5085341 = 1907003) B1907003
theorem B6191275 : Blo 1505449 6191275 := bstep (se 1 (by rfl) ⟨4643456, by rfl⟩ : syracuseStep 6191275 = 9286913) B9286913
theorem B1505455 : Blo 1505449 1505455 := bstep (se 1 (by rfl) ⟨1129091, by rfl⟩ : syracuseStep 1505455 = 2258183) B2258183
theorem B1505479 : Blo 1505449 1505479 := bstep (se 1 (by rfl) ⟨1129109, by rfl⟩ : syracuseStep 1505479 = 2258219) B2258219
theorem B2259143 : Blo 1505449 2259143 := bstep (se 1 (by rfl) ⟨1694357, by rfl⟩ : syracuseStep 2259143 = 3388715) B3388715
theorem B1505499 : Blo 1505449 1505499 := bstep (se 1 (by rfl) ⟨1129124, by rfl⟩ : syracuseStep 1505499 = 2258249) B2258249
theorem B3389687 : Blo 1505449 3389687 := bstep (se 1 (by rfl) ⟨2542265, by rfl⟩ : syracuseStep 3389687 = 5084531) B5084531
theorem B1505575 : Blo 1505449 1505575 := bstep (se 1 (by rfl) ⟨1129181, by rfl⟩ : syracuseStep 1505575 = 2258363) B2258363
theorem B1505615 : Blo 1505449 1505615 := bstep (se 1 (by rfl) ⟨1129211, by rfl⟩ : syracuseStep 1505615 = 2258423) B2258423
theorem B1505631 : Blo 1505449 1505631 := bstep (se 1 (by rfl) ⟨1129223, by rfl⟩ : syracuseStep 1505631 = 2258447) B2258447
theorem B1694047 : Blo 1505449 1694047 := bstep (se 1 (by rfl) ⟨1270535, by rfl⟩ : syracuseStep 1694047 = 2541071) B2541071
theorem B2259305 : Blo 1505449 2259305 := bstep (se 2 (by rfl) ⟨847239, by rfl⟩ : syracuseStep 2259305 = 1694479) B1694479
theorem B1505659 : Blo 1505449 1505659 := bstep (se 1 (by rfl) ⟨1129244, by rfl⟩ : syracuseStep 1505659 = 2258489) B2258489
theorem B1505711 : Blo 1505449 1505711 := bstep (se 1 (by rfl) ⟨1129283, by rfl⟩ : syracuseStep 1505711 = 2258567) B2258567
theorem B2259383 : Blo 1505449 2259383 := bstep (se 1 (by rfl) ⟨1694537, by rfl⟩ : syracuseStep 2259383 = 3389075) B3389075
theorem B1505735 : Blo 1505449 1505735 := bstep (se 1 (by rfl) ⟨1129301, by rfl⟩ : syracuseStep 1505735 = 2258603) B2258603
theorem B1505755 : Blo 1505449 1505755 := bstep (se 1 (by rfl) ⟨1129316, by rfl⟩ : syracuseStep 1505755 = 2258633) B2258633
theorem B2259419 : Blo 1505449 2259419 := bstep (se 1 (by rfl) ⟨1694564, by rfl⟩ : syracuseStep 2259419 = 3389129) B3389129
theorem B1505831 : Blo 1505449 1505831 := bstep (se 1 (by rfl) ⟨1129373, by rfl⟩ : syracuseStep 1505831 = 2258747) B2258747
theorem B3619367 : Blo 1505449 3619367 := bstep (se 1 (by rfl) ⟨2714525, by rfl⟩ : syracuseStep 3619367 = 5429051) B5429051
theorem B1505871 : Blo 1505449 1505871 := bstep (se 1 (by rfl) ⟨1129403, by rfl⟩ : syracuseStep 1505871 = 2258807) B2258807
theorem B1505887 : Blo 1505449 1505887 := bstep (se 1 (by rfl) ⟨1129415, by rfl⟩ : syracuseStep 1505887 = 2258831) B2258831
theorem B1505915 : Blo 1505449 1505915 := bstep (se 1 (by rfl) ⟨1129436, by rfl⟩ : syracuseStep 1505915 = 2258873) B2258873
theorem B1505967 : Blo 1505449 1505967 := bstep (se 1 (by rfl) ⟨1129475, by rfl⟩ : syracuseStep 1505967 = 2258951) B2258951
theorem B5085881 : Blo 1505449 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B1505991 : Blo 1505449 1505991 := bstep (se 1 (by rfl) ⟨1129493, by rfl⟩ : syracuseStep 1505991 = 2258987) B2258987
theorem B1694407 : Blo 1505449 1694407 := bstep (se 1 (by rfl) ⟨1270805, by rfl⟩ : syracuseStep 1694407 = 2541611) B2541611
theorem B1506011 : Blo 1505449 1506011 := bstep (se 1 (by rfl) ⟨1129508, by rfl⟩ : syracuseStep 1506011 = 2259017) B2259017
theorem B7625501 : Blo 1505449 7625501 := bstep (se 3 (by rfl) ⟨1429781, by rfl⟩ : syracuseStep 7625501 = 2859563) B2859563
theorem B1506087 : Blo 1505449 1506087 := bstep (se 1 (by rfl) ⟨1129565, by rfl⟩ : syracuseStep 1506087 = 2259131) B2259131
theorem B3390281 : Blo 1505449 3390281 := bstep (se 2 (by rfl) ⟨1271355, by rfl⟩ : syracuseStep 3390281 = 2542711) B2542711
theorem B1506127 : Blo 1505449 1506127 := bstep (se 1 (by rfl) ⟨1129595, by rfl⟩ : syracuseStep 1506127 = 2259191) B2259191
theorem B1506143 : Blo 1505449 1506143 := bstep (se 1 (by rfl) ⟨1129607, by rfl⟩ : syracuseStep 1506143 = 2259215) B2259215
theorem B1506171 : Blo 1505449 1506171 := bstep (se 1 (by rfl) ⟨1129628, by rfl⟩ : syracuseStep 1506171 = 2259257) B2259257
theorem B1506223 : Blo 1505449 1506223 := bstep (se 1 (by rfl) ⟨1129667, by rfl⟩ : syracuseStep 1506223 = 2259335) B2259335
theorem B2259887 : Blo 1505449 2259887 := bstep (se 1 (by rfl) ⟨1694915, by rfl⟩ : syracuseStep 2259887 = 3389831) B3389831
theorem B5430203 : Blo 1505449 5430203 := bstep (se 1 (by rfl) ⟨4072652, by rfl⟩ : syracuseStep 5430203 = 8145305) B8145305
theorem B1506247 : Blo 1505449 1506247 := bstep (se 1 (by rfl) ⟨1129685, by rfl⟩ : syracuseStep 1506247 = 2259371) B2259371
theorem B1506267 : Blo 1505449 1506267 := bstep (se 1 (by rfl) ⟨1129700, by rfl⟩ : syracuseStep 1506267 = 2259401) B2259401
theorem B2259977 : Blo 1505449 2259977 := bstep (se 2 (by rfl) ⟨847491, by rfl⟩ : syracuseStep 2259977 = 1694983) B1694983
theorem B8141843 : Blo 1505449 8141843 := bstep (se 1 (by rfl) ⟨6106382, by rfl⟩ : syracuseStep 8141843 = 12212765) B12212765
theorem B1506343 : Blo 1505449 1506343 := bstep (se 1 (by rfl) ⟨1129757, by rfl⟩ : syracuseStep 1506343 = 2259515) B2259515
theorem B2260007 : Blo 1505449 2260007 := bstep (se 1 (by rfl) ⟨1695005, by rfl⟩ : syracuseStep 2260007 = 3390011) B3390011
theorem B1506383 : Blo 1505449 1506383 := bstep (se 1 (by rfl) ⟨1129787, by rfl⟩ : syracuseStep 1506383 = 2259575) B2259575
theorem B1506399 : Blo 1505449 1506399 := bstep (se 1 (by rfl) ⟨1129799, by rfl⟩ : syracuseStep 1506399 = 2259599) B2259599
theorem B1506427 : Blo 1505449 1506427 := bstep (se 1 (by rfl) ⟨1129820, by rfl⟩ : syracuseStep 1506427 = 2259641) B2259641
theorem B2260091 : Blo 1505449 2260091 := bstep (se 1 (by rfl) ⟨1695068, by rfl⟩ : syracuseStep 2260091 = 3390137) B3390137
theorem B1506479 : Blo 1505449 1506479 := bstep (se 1 (by rfl) ⟨1129859, by rfl⟩ : syracuseStep 1506479 = 2259719) B2259719
theorem B1506503 : Blo 1505449 1506503 := bstep (se 1 (by rfl) ⟨1129877, by rfl⟩ : syracuseStep 1506503 = 2259755) B2259755
theorem B1506523 : Blo 1505449 1506523 := bstep (se 1 (by rfl) ⟨1129892, by rfl⟩ : syracuseStep 1506523 = 2259785) B2259785
theorem B2260217 : Blo 1505449 2260217 := bstep (se 2 (by rfl) ⟨847581, by rfl⟩ : syracuseStep 2260217 = 1695163) B1695163
theorem B1506599 : Blo 1505449 1506599 := bstep (se 1 (by rfl) ⟨1129949, by rfl⟩ : syracuseStep 1506599 = 2259899) B2259899
theorem B1506639 : Blo 1505449 1506639 := bstep (se 1 (by rfl) ⟨1129979, by rfl⟩ : syracuseStep 1506639 = 2259959) B2259959
theorem B17153369 : Blo 1505449 17153369 := bstep (se 2 (by rfl) ⟨6432513, by rfl⟩ : syracuseStep 17153369 = 12865027) B12865027
theorem B1506655 : Blo 1505449 1506655 := bstep (se 1 (by rfl) ⟨1129991, by rfl⟩ : syracuseStep 1506655 = 2259983) B2259983
theorem B2260319 : Blo 1505449 2260319 := bstep (se 1 (by rfl) ⟨1695239, by rfl⟩ : syracuseStep 2260319 = 3390479) B3390479
theorem B2260331 : Blo 1505449 2260331 := bstep (se 1 (by rfl) ⟨1695248, by rfl⟩ : syracuseStep 2260331 = 3390497) B3390497
theorem B1506683 : Blo 1505449 1506683 := bstep (se 1 (by rfl) ⟨1130012, by rfl⟩ : syracuseStep 1506683 = 2260025) B2260025
theorem B17669549 : Blo 1505449 17669549 := bstep (se 3 (by rfl) ⟨3313040, by rfl⟩ : syracuseStep 17669549 = 6626081) B6626081
theorem B1506735 : Blo 1505449 1506735 := bstep (se 1 (by rfl) ⟨1130051, by rfl⟩ : syracuseStep 1506735 = 2260103) B2260103
theorem B1506759 : Blo 1505449 1506759 := bstep (se 1 (by rfl) ⟨1130069, by rfl⟩ : syracuseStep 1506759 = 2260139) B2260139
theorem B1506779 : Blo 1505449 1506779 := bstep (se 1 (by rfl) ⟨1130084, by rfl⟩ : syracuseStep 1506779 = 2260169) B2260169
theorem B1506855 : Blo 1505449 1506855 := bstep (se 1 (by rfl) ⟨1130141, by rfl⟩ : syracuseStep 1506855 = 2260283) B2260283
theorem B29359655 : Blo 1505449 29359655 := bstep (se 1 (by rfl) ⟨22019741, by rfl⟩ : syracuseStep 29359655 = 44039483) B44039483
theorem B1695271 : Blo 1505449 1695271 := bstep (se 1 (by rfl) ⟨1271453, by rfl⟩ : syracuseStep 1695271 = 2542907) B2542907
theorem B1506895 : Blo 1505449 1506895 := bstep (se 1 (by rfl) ⟨1130171, by rfl⟩ : syracuseStep 1506895 = 2260343) B2260343
theorem B1506911 : Blo 1505449 1506911 := bstep (se 1 (by rfl) ⟨1130183, by rfl⟩ : syracuseStep 1506911 = 2260367) B2260367
theorem B1506939 : Blo 1505449 1506939 := bstep (se 1 (by rfl) ⟨1130204, by rfl⟩ : syracuseStep 1506939 = 2260409) B2260409
theorem B8142535 : Blo 1505449 8142535 := bstep (se 1 (by rfl) ⟨6106901, by rfl⟩ : syracuseStep 8142535 = 12213803) B12213803
theorem B2858743 : Blo 1505449 2858743 := bstep (se 1 (by rfl) ⟨2144057, by rfl⟩ : syracuseStep 2858743 = 4288115) B4288115
theorem B6520763 : Blo 1505449 6520763 := bstep (se 1 (by rfl) ⟨4890572, by rfl⟩ : syracuseStep 6520763 = 9781145) B9781145
theorem B2858971 : Blo 1505449 2858971 := bstep (se 1 (by rfl) ⟨2144228, by rfl⟩ : syracuseStep 2858971 = 4288457) B4288457
theorem B7627283 : Blo 1505449 7627283 := bstep (se 1 (by rfl) ⟨5720462, by rfl⟩ : syracuseStep 7627283 = 11440925) B11440925
theorem B25723493 : Blo 1505449 25723493 := bstep (se 4 (by rfl) ⟨2411577, by rfl⟩ : syracuseStep 25723493 = 4823155) B4823155
theorem B17621651 : Blo 1505449 17621651 := bstep (se 1 (by rfl) ⟨13216238, by rfl⟩ : syracuseStep 17621651 = 26432477) B26432477
theorem B12870359 : Blo 1505449 12870359 := bstep (se 1 (by rfl) ⟨9652769, by rfl⟩ : syracuseStep 12870359 = 19305539) B19305539
theorem B7234505 : Blo 1505449 7234505 := bstep (se 2 (by rfl) ⟨2712939, by rfl⟩ : syracuseStep 7234505 = 5425879) B5425879
theorem B14869511 : Blo 1505449 14869511 := bstep (se 1 (by rfl) ⟨11152133, by rfl⟩ : syracuseStep 14869511 = 22304267) B22304267
theorem B5719187 : Blo 1505449 5719187 := bstep (se 1 (by rfl) ⟨4289390, by rfl⟩ : syracuseStep 5719187 = 8578781) B8578781
theorem B7234717 : Blo 1505449 7234717 := bstep (se 3 (by rfl) ⟨1356509, by rfl⟩ : syracuseStep 7234717 = 2713019) B2713019
theorem B25740989 : Blo 1505449 25740989 := bstep (se 3 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 25740989 = 9652871) B9652871
theorem B16500557 : Blo 1505449 16500557 := bstep (se 3 (by rfl) ⟨3093854, by rfl⟩ : syracuseStep 16500557 = 6187709) B6187709
theorem B14469313 : Blo 1505449 14469313 := bstep (se 2 (by rfl) ⟨5425992, by rfl⟩ : syracuseStep 14469313 = 10851985) B10851985
theorem B10856713 : Blo 1505449 10856713 := bstep (se 2 (by rfl) ⟨4071267, by rfl⟩ : syracuseStep 10856713 = 8142535) B8142535
theorem B3811657 : Blo 1505449 3811657 := bstep (se 2 (by rfl) ⟨1429371, by rfl⟩ : syracuseStep 3811657 = 2858743) B2858743
theorem B2541935 : Blo 1505449 2541935 := bstep (se 1 (by rfl) ⟨1906451, by rfl⟩ : syracuseStep 2541935 = 3812903) B3812903
theorem B19573103 : Blo 1505449 19573103 := bstep (se 1 (by rfl) ⟨14679827, by rfl⟩ : syracuseStep 19573103 = 29359655) B29359655
theorem B1608103 : Blo 1505449 1608103 := bstep (se 1 (by rfl) ⟨1206077, by rfl⟩ : syracuseStep 1608103 = 2412155) B2412155
theorem B2542151 : Blo 1505449 2542151 := bstep (se 1 (by rfl) ⟨1906613, by rfl⟩ : syracuseStep 2542151 = 3813227) B3813227
theorem B3811961 : Blo 1505449 3811961 := bstep (se 2 (by rfl) ⟨1429485, by rfl⟩ : syracuseStep 3811961 = 2858971) B2858971
theorem B8579965 : Blo 1505449 8579965 := bstep (se 3 (by rfl) ⟨1608743, by rfl⟩ : syracuseStep 8579965 = 3217487) B3217487
theorem B14879623 : Blo 1505449 14879623 := bstep (se 1 (by rfl) ⟨11159717, by rfl⟩ : syracuseStep 14879623 = 22319435) B22319435
theorem B2542583 : Blo 1505449 2542583 := bstep (se 1 (by rfl) ⟨1906937, by rfl⟩ : syracuseStep 2542583 = 3813875) B3813875
theorem B16280747 : Blo 1505449 16280747 := bstep (se 1 (by rfl) ⟨12210560, by rfl⟩ : syracuseStep 16280747 = 24421121) B24421121
theorem B3304681 : Blo 1505449 3304681 := bstep (se 2 (by rfl) ⟨1239255, by rfl⟩ : syracuseStep 3304681 = 2478511) B2478511
theorem B6524297 : Blo 1505449 6524297 := bstep (se 2 (by rfl) ⟨2446611, by rfl⟩ : syracuseStep 6524297 = 4893223) B4893223
theorem B4288297 : Blo 1505449 4288297 := bstep (se 2 (by rfl) ⟨1608111, by rfl⟩ : syracuseStep 4288297 = 3216223) B3216223
theorem B6434633 : Blo 1505449 6434633 := bstep (se 2 (by rfl) ⟨2412987, by rfl⟩ : syracuseStep 6434633 = 4825975) B4825975
theorem B3215369 : Blo 1505449 3215369 := bstep (se 2 (by rfl) ⟨1205763, by rfl⟩ : syracuseStep 3215369 = 2411527) B2411527
theorem B3387401 : Blo 1505449 3387401 := bstep (se 2 (by rfl) ⟨1270275, by rfl⟩ : syracuseStep 3387401 = 2540551) B2540551
theorem B12218473 : Blo 1505449 12218473 := bstep (se 2 (by rfl) ⟨4581927, by rfl⟩ : syracuseStep 12218473 = 9163855) B9163855
theorem B7434443 : Blo 1505449 7434443 := bstep (se 1 (by rfl) ⟨5575832, by rfl⟩ : syracuseStep 7434443 = 11151665) B11151665
theorem B2412911 : Blo 1505449 2412911 := bstep (se 1 (by rfl) ⟨1809683, by rfl⟩ : syracuseStep 2412911 = 3619367) B3619367
theorem B3813743 : Blo 1505449 3813743 := bstep (se 1 (by rfl) ⟨2860307, by rfl⟩ : syracuseStep 3813743 = 5720615) B5720615
theorem B3387815 : Blo 1505449 3387815 := bstep (se 1 (by rfl) ⟨2540861, by rfl⟩ : syracuseStep 3387815 = 5081723) B5081723
theorem B3387923 : Blo 1505449 3387923 := bstep (se 1 (by rfl) ⟨2540942, by rfl⟩ : syracuseStep 3387923 = 5081885) B5081885
theorem B5083667 : Blo 1505449 5083667 := bstep (se 1 (by rfl) ⟨3812750, by rfl⟩ : syracuseStep 5083667 = 7625501) B7625501
theorem B3387977 : Blo 1505449 3387977 := bstep (se 2 (by rfl) ⟨1270491, by rfl⟩ : syracuseStep 3387977 = 2540983) B2540983
theorem B5427895 : Blo 1505449 5427895 := bstep (se 1 (by rfl) ⟨4070921, by rfl⟩ : syracuseStep 5427895 = 8141843) B8141843
theorem B8139467 : Blo 1505449 8139467 := bstep (se 1 (by rfl) ⟨6104600, by rfl⟩ : syracuseStep 8139467 = 12209201) B12209201
theorem B3388391 : Blo 1505449 3388391 := bstep (se 1 (by rfl) ⟨2541293, by rfl⟩ : syracuseStep 3388391 = 5082587) B5082587
theorem B4289527 : Blo 1505449 4289527 := bstep (se 1 (by rfl) ⟨3217145, by rfl⟩ : syracuseStep 4289527 = 6434291) B6434291
theorem B3814391 : Blo 1505449 3814391 := bstep (se 1 (by rfl) ⟨2860793, by rfl⟩ : syracuseStep 3814391 = 5721587) B5721587
theorem B42931289 : Blo 1505449 42931289 := bstep (se 2 (by rfl) ⟨16099233, by rfl⟩ : syracuseStep 42931289 = 32198467) B32198467
theorem B8139923 : Blo 1505449 8139923 := bstep (se 1 (by rfl) ⟨6104942, by rfl⟩ : syracuseStep 8139923 = 12209885) B12209885
theorem B14677139 : Blo 1505449 14677139 := bstep (se 1 (by rfl) ⟨11007854, by rfl⟩ : syracuseStep 14677139 = 22015709) B22015709
theorem B17388701 : Blo 1505449 17388701 := bstep (se 3 (by rfl) ⟨3260381, by rfl⟩ : syracuseStep 17388701 = 6520763) B6520763
theorem B2258207 : Blo 1505449 2258207 := bstep (se 1 (by rfl) ⟨1693655, by rfl⟩ : syracuseStep 2258207 = 3387311) B3387311
theorem B3388769 : Blo 1505449 3388769 := bstep (se 2 (by rfl) ⟨1270788, by rfl⟩ : syracuseStep 3388769 = 2541577) B2541577
theorem B1906031 : Blo 1505449 1906031 := bstep (se 1 (by rfl) ⟨1429523, by rfl⟩ : syracuseStep 1906031 = 2859047) B2859047
theorem B6436205 : Blo 1505449 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B4289915 : Blo 1505449 4289915 := bstep (se 1 (by rfl) ⟨3217436, by rfl⟩ : syracuseStep 4289915 = 6434873) B6434873
theorem B1906087 : Blo 1505449 1906087 := bstep (se 1 (by rfl) ⟨1429565, by rfl⟩ : syracuseStep 1906087 = 2859131) B2859131
theorem B3388859 : Blo 1505449 3388859 := bstep (se 1 (by rfl) ⟨2541644, by rfl⟩ : syracuseStep 3388859 = 5083289) B5083289
theorem B2258375 : Blo 1505449 2258375 := bstep (se 1 (by rfl) ⟨1693781, by rfl⟩ : syracuseStep 2258375 = 3387563) B3387563
theorem B3388985 : Blo 1505449 3388985 := bstep (se 2 (by rfl) ⟨1270869, by rfl⟩ : syracuseStep 3388985 = 2541739) B2541739
theorem B8255033 : Blo 1505449 8255033 := bstep (se 2 (by rfl) ⟨3095637, by rfl⟩ : syracuseStep 8255033 = 6191275) B6191275
theorem B1717831 : Blo 1505449 1717831 := bstep (se 1 (by rfl) ⟨1288373, by rfl⟩ : syracuseStep 1717831 = 2576747) B2576747
theorem B13407929 : Blo 1505449 13407929 := bstep (se 2 (by rfl) ⟨5027973, by rfl⟩ : syracuseStep 13407929 = 10055947) B10055947
theorem B1906411 : Blo 1505449 1906411 := bstep (se 1 (by rfl) ⟨1429808, by rfl⟩ : syracuseStep 1906411 = 2859617) B2859617
theorem B2258729 : Blo 1505449 2258729 := bstep (se 2 (by rfl) ⟨847023, by rfl⟩ : syracuseStep 2258729 = 1694047) B1694047
theorem B2258735 : Blo 1505449 2258735 := bstep (se 1 (by rfl) ⟨1694051, by rfl⟩ : syracuseStep 2258735 = 3388103) B3388103
theorem B7624529 : Blo 1505449 7624529 := bstep (se 2 (by rfl) ⟨2859198, by rfl⟩ : syracuseStep 7624529 = 5718397) B5718397
theorem B305403857 : Blo 1505449 305403857 := bstep (se 2 (by rfl) ⟨114526446, by rfl⟩ : syracuseStep 305403857 = 229052893) B229052893
theorem B3389651 : Blo 1505449 3389651 := bstep (se 1 (by rfl) ⟨2542238, by rfl⟩ : syracuseStep 3389651 = 5084477) B5084477
theorem B2259209 : Blo 1505449 2259209 := bstep (se 2 (by rfl) ⟨847203, by rfl⟩ : syracuseStep 2259209 = 1694407) B1694407
theorem B3389705 : Blo 1505449 3389705 := bstep (se 2 (by rfl) ⟨1271139, by rfl⟩ : syracuseStep 3389705 = 2542279) B2542279
theorem B5085449 : Blo 1505449 5085449 := bstep (se 2 (by rfl) ⟨1907043, by rfl⟩ : syracuseStep 5085449 = 3814087) B3814087
theorem B1505567 : Blo 1505449 1505567 := bstep (se 1 (by rfl) ⟨1129175, by rfl⟩ : syracuseStep 1505567 = 2258351) B2258351
theorem B30914885 : Blo 1505449 30914885 := bstep (se 4 (by rfl) ⟨2898270, by rfl⟩ : syracuseStep 30914885 = 5796541) B5796541
theorem B1505627 : Blo 1505449 1505627 := bstep (se 1 (by rfl) ⟨1129220, by rfl⟩ : syracuseStep 1505627 = 2258441) B2258441
theorem B1505647 : Blo 1505449 1505647 := bstep (se 1 (by rfl) ⟨1129235, by rfl⟩ : syracuseStep 1505647 = 2258471) B2258471
theorem B2259311 : Blo 1505449 2259311 := bstep (se 1 (by rfl) ⟨1694483, by rfl⟩ : syracuseStep 2259311 = 3388967) B3388967
theorem B1505703 : Blo 1505449 1505703 := bstep (se 1 (by rfl) ⟨1129277, by rfl⟩ : syracuseStep 1505703 = 2258555) B2258555
theorem B1694119 : Blo 1505449 1694119 := bstep (se 1 (by rfl) ⟨1270589, by rfl⟩ : syracuseStep 1694119 = 2541179) B2541179
theorem B47118797 : Blo 1505449 47118797 := bstep (se 3 (by rfl) ⟨8834774, by rfl⟩ : syracuseStep 47118797 = 17669549) B17669549
theorem B3054035 : Blo 1505449 3054035 := bstep (se 1 (by rfl) ⟨2290526, by rfl⟩ : syracuseStep 3054035 = 4581053) B4581053
theorem B3389921 : Blo 1505449 3389921 := bstep (se 2 (by rfl) ⟨1271220, by rfl⟩ : syracuseStep 3389921 = 2542441) B2542441
theorem B1505787 : Blo 1505449 1505787 := bstep (se 1 (by rfl) ⟨1129340, by rfl⟩ : syracuseStep 1505787 = 2258681) B2258681
theorem B1505855 : Blo 1505449 1505855 := bstep (se 1 (by rfl) ⟨1129391, by rfl⟩ : syracuseStep 1505855 = 2258783) B2258783
theorem B1505863 : Blo 1505449 1505863 := bstep (se 1 (by rfl) ⟨1129397, by rfl⟩ : syracuseStep 1505863 = 2258795) B2258795
theorem B2259527 : Blo 1505449 2259527 := bstep (se 1 (by rfl) ⟨1694645, by rfl⟩ : syracuseStep 2259527 = 3389291) B3389291
theorem B2259563 : Blo 1505449 2259563 := bstep (se 1 (by rfl) ⟨1694672, by rfl⟩ : syracuseStep 2259563 = 3389345) B3389345
theorem B7625339 : Blo 1505449 7625339 := bstep (se 1 (by rfl) ⟨5719004, by rfl⟩ : syracuseStep 7625339 = 11438009) B11438009
theorem B1506015 : Blo 1505449 1506015 := bstep (se 1 (by rfl) ⟨1129511, by rfl⟩ : syracuseStep 1506015 = 2259023) B2259023
theorem B5716727 : Blo 1505449 5716727 := bstep (se 1 (by rfl) ⟨4287545, by rfl⟩ : syracuseStep 5716727 = 8575091) B8575091
theorem B4348691 : Blo 1505449 4348691 := bstep (se 1 (by rfl) ⟨3261518, by rfl⟩ : syracuseStep 4348691 = 6523037) B6523037
theorem B3390227 : Blo 1505449 3390227 := bstep (se 1 (by rfl) ⟨2542670, by rfl⟩ : syracuseStep 3390227 = 5085341) B5085341
theorem B1506095 : Blo 1505449 1506095 := bstep (se 1 (by rfl) ⟨1129571, by rfl⟩ : syracuseStep 1506095 = 2259143) B2259143
theorem B2259791 : Blo 1505449 2259791 := bstep (se 1 (by rfl) ⟨1694843, by rfl⟩ : syracuseStep 2259791 = 3389687) B3389687
theorem B1506203 : Blo 1505449 1506203 := bstep (se 1 (by rfl) ⟨1129652, by rfl⟩ : syracuseStep 1506203 = 2259305) B2259305
theorem B14474159 : Blo 1505449 14474159 := bstep (se 1 (by rfl) ⟨10855619, by rfl⟩ : syracuseStep 14474159 = 21711239) B21711239
theorem B1506255 : Blo 1505449 1506255 := bstep (se 1 (by rfl) ⟨1129691, by rfl⟩ : syracuseStep 1506255 = 2259383) B2259383
theorem B1506279 : Blo 1505449 1506279 := bstep (se 1 (by rfl) ⟨1129709, by rfl⟩ : syracuseStep 1506279 = 2259419) B2259419
theorem B1694695 : Blo 1505449 1694695 := bstep (se 1 (by rfl) ⟨1271021, by rfl⟩ : syracuseStep 1694695 = 2542043) B2542043
theorem B9649181 : Blo 1505449 9649181 := bstep (se 3 (by rfl) ⟨1809221, by rfl⟩ : syracuseStep 9649181 = 3618443) B3618443
theorem B8363047 : Blo 1505449 8363047 := bstep (se 1 (by rfl) ⟨6272285, by rfl⟩ : syracuseStep 8363047 = 12544571) B12544571
theorem B3390587 : Blo 1505449 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B2260187 : Blo 1505449 2260187 := bstep (se 1 (by rfl) ⟨1695140, by rfl⟩ : syracuseStep 2260187 = 3390281) B3390281
theorem B1506591 : Blo 1505449 1506591 := bstep (se 1 (by rfl) ⟨1129943, by rfl⟩ : syracuseStep 1506591 = 2259887) B2259887
theorem B3620135 : Blo 1505449 3620135 := bstep (se 1 (by rfl) ⟨2715101, by rfl⟩ : syracuseStep 3620135 = 5430203) B5430203
theorem B7241021 : Blo 1505449 7241021 := bstep (se 3 (by rfl) ⟨1357691, by rfl⟩ : syracuseStep 7241021 = 2715383) B2715383
theorem B1506651 : Blo 1505449 1506651 := bstep (se 1 (by rfl) ⟨1129988, by rfl⟩ : syracuseStep 1506651 = 2259977) B2259977
theorem B1506671 : Blo 1505449 1506671 := bstep (se 1 (by rfl) ⟨1130003, by rfl⟩ : syracuseStep 1506671 = 2260007) B2260007
theorem B2260361 : Blo 1505449 2260361 := bstep (se 2 (by rfl) ⟨847635, by rfl⟩ : syracuseStep 2260361 = 1695271) B1695271
theorem B14474659 : Blo 1505449 14474659 := bstep (se 1 (by rfl) ⟨10855994, by rfl⟩ : syracuseStep 14474659 = 21711989) B21711989
theorem B1547687 : Blo 1505449 1547687 := bstep (se 1 (by rfl) ⟨1160765, by rfl⟩ : syracuseStep 1547687 = 2321531) B2321531
theorem B1506727 : Blo 1505449 1506727 := bstep (se 1 (by rfl) ⟨1130045, by rfl⟩ : syracuseStep 1506727 = 2260091) B2260091
theorem B1506811 : Blo 1505449 1506811 := bstep (se 1 (by rfl) ⟨1130108, by rfl⟩ : syracuseStep 1506811 = 2260217) B2260217
theorem B11435579 : Blo 1505449 11435579 := bstep (se 1 (by rfl) ⟨8576684, by rfl⟩ : syracuseStep 11435579 = 17153369) B17153369
theorem B1506879 : Blo 1505449 1506879 := bstep (se 1 (by rfl) ⟨1130159, by rfl⟩ : syracuseStep 1506879 = 2260319) B2260319
theorem B1506887 : Blo 1505449 1506887 := bstep (se 1 (by rfl) ⟨1130165, by rfl⟩ : syracuseStep 1506887 = 2260331) B2260331
theorem B2858591 : Blo 1505449 2858591 := bstep (se 1 (by rfl) ⟨2143943, by rfl⟩ : syracuseStep 2858591 = 4287887) B4287887
theorem B4956295 : Blo 1505449 4956295 := bstep (se 1 (by rfl) ⟨3717221, by rfl⟩ : syracuseStep 4956295 = 7434443) B7434443
theorem B19292417 : Blo 1505449 19292417 := bstep (se 2 (by rfl) ⟨7234656, by rfl⟩ : syracuseStep 19292417 = 14469313) B14469313
theorem B14475617 : Blo 1505449 14475617 := bstep (se 2 (by rfl) ⟨5428356, by rfl⟩ : syracuseStep 14475617 = 10856713) B10856713
theorem B11747767 : Blo 1505449 11747767 := bstep (se 1 (by rfl) ⟨8810825, by rfl⟩ : syracuseStep 11747767 = 17621651) B17621651
theorem B9913007 : Blo 1505449 9913007 := bstep (se 1 (by rfl) ⟨7434755, by rfl⟩ : syracuseStep 9913007 = 14869511) B14869511
theorem B11592467 : Blo 1505449 11592467 := bstep (se 1 (by rfl) ⟨8694350, by rfl⟩ : syracuseStep 11592467 = 17388701) B17388701
theorem B2859943 : Blo 1505449 2859943 := bstep (se 1 (by rfl) ⟨2144957, by rfl⟩ : syracuseStep 2859943 = 4289915) B4289915
theorem B8938619 : Blo 1505449 8938619 := bstep (se 1 (by rfl) ⟨6703964, by rfl⟩ : syracuseStep 8938619 = 13407929) B13407929
theorem B5719369 : Blo 1505449 5719369 := bstep (se 2 (by rfl) ⟨2144763, by rfl⟩ : syracuseStep 5719369 = 4289527) B4289527
theorem B11150729 : Blo 1505449 11150729 := bstep (se 2 (by rfl) ⟨4181523, by rfl⟩ : syracuseStep 11150729 = 8363047) B8363047
theorem B2541307 : Blo 1505449 2541307 := bstep (se 1 (by rfl) ⟨1905980, by rfl⟩ : syracuseStep 2541307 = 3811961) B3811961
theorem B3811151 : Blo 1505449 3811151 := bstep (se 1 (by rfl) ⟨2858363, by rfl⟩ : syracuseStep 3811151 = 5716727) B5716727
theorem B2541449 : Blo 1505449 2541449 := bstep (se 2 (by rfl) ⟨953043, by rfl⟩ : syracuseStep 2541449 = 1906087) B1906087
theorem B6432787 : Blo 1505449 6432787 := bstep (se 1 (by rfl) ⟨4824590, by rfl⟩ : syracuseStep 6432787 = 9649181) B9649181
theorem B4827347 : Blo 1505449 4827347 := bstep (se 1 (by rfl) ⟨3620510, by rfl⟩ : syracuseStep 4827347 = 7241021) B7241021
theorem B2541881 : Blo 1505449 2541881 := bstep (se 2 (by rfl) ⟨953205, by rfl⟩ : syracuseStep 2541881 = 1906411) B1906411
theorem B1608607 : Blo 1505449 1608607 := bstep (se 1 (by rfl) ⟨1206455, by rfl⟩ : syracuseStep 1608607 = 2412911) B2412911
theorem B2542495 : Blo 1505449 2542495 := bstep (se 1 (by rfl) ⟨1906871, by rfl⟩ : syracuseStep 2542495 = 3813743) B3813743
theorem B9161765 : Blo 1505449 9161765 := bstep (se 4 (by rfl) ⟨858915, by rfl⟩ : syracuseStep 9161765 = 1717831) B1717831
theorem B17148995 : Blo 1505449 17148995 := bstep (se 1 (by rfl) ⟨12861746, by rfl⟩ : syracuseStep 17148995 = 25723493) B25723493
theorem B5082209 : Blo 1505449 5082209 := bstep (se 2 (by rfl) ⟨1905828, by rfl⟩ : syracuseStep 5082209 = 3811657) B3811657
theorem B8580239 : Blo 1505449 8580239 := bstep (se 1 (by rfl) ⟨6435179, by rfl⟩ : syracuseStep 8580239 = 12870359) B12870359
theorem B2542927 : Blo 1505449 2542927 := bstep (se 1 (by rfl) ⟨1907195, by rfl⟩ : syracuseStep 2542927 = 3814391) B3814391
theorem B5426615 : Blo 1505449 5426615 := bstep (se 1 (by rfl) ⟨4069961, by rfl⟩ : syracuseStep 5426615 = 8139923) B8139923
theorem B3812791 : Blo 1505449 3812791 := bstep (se 1 (by rfl) ⟨2859593, by rfl⟩ : syracuseStep 3812791 = 5719187) B5719187
theorem B9784759 : Blo 1505449 9784759 := bstep (se 1 (by rfl) ⟨7338569, by rfl⟩ : syracuseStep 9784759 = 14677139) B14677139
theorem B7237193 : Blo 1505449 7237193 := bstep (se 2 (by rfl) ⟨2713947, by rfl⟩ : syracuseStep 7237193 = 5427895) B5427895
theorem B5082749 : Blo 1505449 5082749 := bstep (se 3 (by rfl) ⟨953015, by rfl⟩ : syracuseStep 5082749 = 1906031) B1906031
theorem B52194941 : Blo 1505449 52194941 := bstep (se 3 (by rfl) ⟨9786551, by rfl⟩ : syracuseStep 52194941 = 19573103) B19573103
theorem B11439953 : Blo 1505449 11439953 := bstep (se 2 (by rfl) ⟨4289982, by rfl⟩ : syracuseStep 11439953 = 8579965) B8579965
theorem B17624965 : Blo 1505449 17624965 := bstep (se 4 (by rfl) ⟨1652340, by rfl⟩ : syracuseStep 17624965 = 3304681) B3304681
theorem B5083019 : Blo 1505449 5083019 := bstep (se 1 (by rfl) ⟨3812264, by rfl⟩ : syracuseStep 5083019 = 7624529) B7624529
theorem B9646289 : Blo 1505449 9646289 := bstep (se 2 (by rfl) ⟨3617358, by rfl⟩ : syracuseStep 9646289 = 7234717) B7234717
theorem B7622909 : Blo 1505449 7622909 := bstep (se 3 (by rfl) ⟨1429295, by rfl⟩ : syracuseStep 7622909 = 2858591) B2858591
theorem B31412531 : Blo 1505449 31412531 := bstep (se 1 (by rfl) ⟨23559398, by rfl⟩ : syracuseStep 31412531 = 47118797) B47118797
theorem B2036023 : Blo 1505449 2036023 := bstep (se 1 (by rfl) ⟨1527017, by rfl⟩ : syracuseStep 2036023 = 3054035) B3054035
theorem B5083559 : Blo 1505449 5083559 := bstep (se 1 (by rfl) ⟨3812669, by rfl⟩ : syracuseStep 5083559 = 7625339) B7625339
theorem B21705245 : Blo 1505449 21705245 := bstep (se 3 (by rfl) ⟨4069733, by rfl⟩ : syracuseStep 21705245 = 8139467) B8139467
theorem B2413423 : Blo 1505449 2413423 := bstep (se 1 (by rfl) ⟨1810067, by rfl⟩ : syracuseStep 2413423 = 3620135) B3620135
theorem B7623719 : Blo 1505449 7623719 := bstep (se 1 (by rfl) ⟨5717789, by rfl⟩ : syracuseStep 7623719 = 11435579) B11435579
theorem B4289755 : Blo 1505449 4289755 := bstep (se 1 (by rfl) ⟨3217316, by rfl⟩ : syracuseStep 4289755 = 6434633) B6434633
theorem B2143579 : Blo 1505449 2143579 := bstep (se 1 (by rfl) ⟨1607684, by rfl⟩ : syracuseStep 2143579 = 3215369) B3215369
theorem B2258267 : Blo 1505449 2258267 := bstep (se 1 (by rfl) ⟨1693700, by rfl⟩ : syracuseStep 2258267 = 3387401) B3387401
theorem B16291297 : Blo 1505449 16291297 := bstep (se 2 (by rfl) ⟨6109236, by rfl⟩ : syracuseStep 16291297 = 12218473) B12218473
theorem B2258543 : Blo 1505449 2258543 := bstep (se 1 (by rfl) ⟨1693907, by rfl⟩ : syracuseStep 2258543 = 3387815) B3387815
theorem B2258615 : Blo 1505449 2258615 := bstep (se 1 (by rfl) ⟨1693961, by rfl⟩ : syracuseStep 2258615 = 3387923) B3387923
theorem B3389111 : Blo 1505449 3389111 := bstep (se 1 (by rfl) ⟨2541833, by rfl⟩ : syracuseStep 3389111 = 5083667) B5083667
theorem B5084855 : Blo 1505449 5084855 := bstep (se 1 (by rfl) ⟨3813641, by rfl⟩ : syracuseStep 5084855 = 7627283) B7627283
theorem B2258651 : Blo 1505449 2258651 := bstep (se 1 (by rfl) ⟨1693988, by rfl⟩ : syracuseStep 2258651 = 3387977) B3387977
theorem B2258825 : Blo 1505449 2258825 := bstep (se 2 (by rfl) ⟨847059, by rfl⟩ : syracuseStep 2258825 = 1694119) B1694119
theorem B4823003 : Blo 1505449 4823003 := bstep (se 1 (by rfl) ⟨3617252, by rfl⟩ : syracuseStep 4823003 = 7234505) B7234505
theorem B2258927 : Blo 1505449 2258927 := bstep (se 1 (by rfl) ⟨1694195, by rfl⟩ : syracuseStep 2258927 = 3388391) B3388391
theorem B28620859 : Blo 1505449 28620859 := bstep (se 1 (by rfl) ⟨21465644, by rfl⟩ : syracuseStep 28620859 = 42931289) B42931289
theorem B1505471 : Blo 1505449 1505471 := bstep (se 1 (by rfl) ⟨1129103, by rfl⟩ : syracuseStep 1505471 = 2258207) B2258207
theorem B2259179 : Blo 1505449 2259179 := bstep (se 1 (by rfl) ⟨1694384, by rfl⟩ : syracuseStep 2259179 = 3388769) B3388769
theorem B4290803 : Blo 1505449 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B2259239 : Blo 1505449 2259239 := bstep (se 1 (by rfl) ⟨1694429, by rfl⟩ : syracuseStep 2259239 = 3388859) B3388859
theorem B1505583 : Blo 1505449 1505583 := bstep (se 1 (by rfl) ⟨1129187, by rfl⟩ : syracuseStep 1505583 = 2258375) B2258375
theorem B2259323 : Blo 1505449 2259323 := bstep (se 1 (by rfl) ⟨1694492, by rfl⟩ : syracuseStep 2259323 = 3388985) B3388985
theorem B5503355 : Blo 1505449 5503355 := bstep (se 1 (by rfl) ⟨4127516, by rfl⟩ : syracuseStep 5503355 = 8255033) B8255033
theorem B4127165 : Blo 1505449 4127165 := bstep (se 3 (by rfl) ⟨773843, by rfl⟩ : syracuseStep 4127165 = 1547687) B1547687
theorem B17160659 : Blo 1505449 17160659 := bstep (se 1 (by rfl) ⟨12870494, by rfl⟩ : syracuseStep 17160659 = 25740989) B25740989
theorem B19839497 : Blo 1505449 19839497 := bstep (se 2 (by rfl) ⟨7439811, by rfl⟩ : syracuseStep 19839497 = 14879623) B14879623
theorem B1505819 : Blo 1505449 1505819 := bstep (se 1 (by rfl) ⟨1129364, by rfl⟩ : syracuseStep 1505819 = 2258729) B2258729
theorem B1505823 : Blo 1505449 1505823 := bstep (se 1 (by rfl) ⟨1129367, by rfl⟩ : syracuseStep 1505823 = 2258735) B2258735
theorem B11000371 : Blo 1505449 11000371 := bstep (se 1 (by rfl) ⟨8250278, by rfl⟩ : syracuseStep 11000371 = 16500557) B16500557
theorem B2259593 : Blo 1505449 2259593 := bstep (se 2 (by rfl) ⟨847347, by rfl⟩ : syracuseStep 2259593 = 1694695) B1694695
theorem B203602571 : Blo 1505449 203602571 := bstep (se 1 (by rfl) ⟨152701928, by rfl⟩ : syracuseStep 203602571 = 305403857) B305403857
theorem B2259767 : Blo 1505449 2259767 := bstep (se 1 (by rfl) ⟨1694825, by rfl⟩ : syracuseStep 2259767 = 3389651) B3389651
theorem B1506139 : Blo 1505449 1506139 := bstep (se 1 (by rfl) ⟨1129604, by rfl⟩ : syracuseStep 1506139 = 2259209) B2259209
theorem B2259803 : Blo 1505449 2259803 := bstep (se 1 (by rfl) ⟨1694852, by rfl⟩ : syracuseStep 2259803 = 3389705) B3389705
theorem B3390299 : Blo 1505449 3390299 := bstep (se 1 (by rfl) ⟨2542724, by rfl⟩ : syracuseStep 3390299 = 5085449) B5085449
theorem B20609923 : Blo 1505449 20609923 := bstep (se 1 (by rfl) ⟨15457442, by rfl⟩ : syracuseStep 20609923 = 30914885) B30914885
theorem B1506207 : Blo 1505449 1506207 := bstep (se 1 (by rfl) ⟨1129655, by rfl⟩ : syracuseStep 1506207 = 2259311) B2259311
theorem B1694623 : Blo 1505449 1694623 := bstep (se 1 (by rfl) ⟨1270967, by rfl⟩ : syracuseStep 1694623 = 2541935) B2541935
theorem B2259947 : Blo 1505449 2259947 := bstep (se 1 (by rfl) ⟨1694960, by rfl⟩ : syracuseStep 2259947 = 3389921) B3389921
theorem B1506351 : Blo 1505449 1506351 := bstep (se 1 (by rfl) ⟨1129763, by rfl⟩ : syracuseStep 1506351 = 2259527) B2259527
theorem B1694767 : Blo 1505449 1694767 := bstep (se 1 (by rfl) ⟨1271075, by rfl⟩ : syracuseStep 1694767 = 2542151) B2542151
theorem B1506375 : Blo 1505449 1506375 := bstep (se 1 (by rfl) ⟨1129781, by rfl⟩ : syracuseStep 1506375 = 2259563) B2259563
theorem B2899127 : Blo 1505449 2899127 := bstep (se 1 (by rfl) ⟨2174345, by rfl⟩ : syracuseStep 2899127 = 4348691) B4348691
theorem B2260151 : Blo 1505449 2260151 := bstep (se 1 (by rfl) ⟨1695113, by rfl⟩ : syracuseStep 2260151 = 3390227) B3390227
theorem B19299545 : Blo 1505449 19299545 := bstep (se 2 (by rfl) ⟨7237329, by rfl⟩ : syracuseStep 19299545 = 14474659) B14474659
theorem B1506527 : Blo 1505449 1506527 := bstep (se 1 (by rfl) ⟨1129895, by rfl⟩ : syracuseStep 1506527 = 2259791) B2259791
theorem B9649439 : Blo 1505449 9649439 := bstep (se 1 (by rfl) ⟨7237079, by rfl⟩ : syracuseStep 9649439 = 14474159) B14474159
theorem B1695055 : Blo 1505449 1695055 := bstep (se 1 (by rfl) ⟨1271291, by rfl⟩ : syracuseStep 1695055 = 2542583) B2542583
theorem B2260391 : Blo 1505449 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B10853831 : Blo 1505449 10853831 := bstep (se 1 (by rfl) ⟨8140373, by rfl⟩ : syracuseStep 10853831 = 16280747) B16280747
theorem B1506791 : Blo 1505449 1506791 := bstep (se 1 (by rfl) ⟨1130093, by rfl⟩ : syracuseStep 1506791 = 2260187) B2260187
theorem B8576549 : Blo 1505449 8576549 := bstep (se 4 (by rfl) ⟨804051, by rfl⟩ : syracuseStep 8576549 = 1608103) B1608103
theorem B4349531 : Blo 1505449 4349531 := bstep (se 1 (by rfl) ⟨3262148, by rfl⟩ : syracuseStep 4349531 = 6524297) B6524297
theorem B1506907 : Blo 1505449 1506907 := bstep (se 1 (by rfl) ⟨1130180, by rfl⟩ : syracuseStep 1506907 = 2260361) B2260361
theorem B5717729 : Blo 1505449 5717729 := bstep (se 2 (by rfl) ⟨2144148, by rfl⟩ : syracuseStep 5717729 = 4288297) B4288297
theorem B8577049 : Blo 1505449 8577049 := bstep (se 2 (by rfl) ⟨3216393, by rfl⟩ : syracuseStep 8577049 = 6432787) B6432787
theorem B6430859 : Blo 1505449 6430859 := bstep (se 1 (by rfl) ⟨4823144, by rfl⟩ : syracuseStep 6430859 = 9646289) B9646289
theorem B12861611 : Blo 1505449 12861611 := bstep (se 1 (by rfl) ⟨9646208, by rfl⟩ : syracuseStep 12861611 = 19292417) B19292417
theorem B9650411 : Blo 1505449 9650411 := bstep (se 1 (by rfl) ⟨7237808, by rfl⟩ : syracuseStep 9650411 = 14475617) B14475617
theorem B15663689 : Blo 1505449 15663689 := bstep (se 2 (by rfl) ⟨5873883, by rfl⟩ : syracuseStep 15663689 = 11747767) B11747767
theorem B2540767 : Blo 1505449 2540767 := bstep (se 1 (by rfl) ⟨1905575, by rfl⟩ : syracuseStep 2540767 = 3811151) B3811151
theorem B52905325 : Blo 1505449 52905325 := bstep (se 3 (by rfl) ⟨9919748, by rfl⟩ : syracuseStep 52905325 = 19839497) B19839497
theorem B2860535 : Blo 1505449 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B5719673 : Blo 1505449 5719673 := bstep (se 2 (by rfl) ⟨2144877, by rfl⟩ : syracuseStep 5719673 = 4289755) B4289755
theorem B135735047 : Blo 1505449 135735047 := bstep (se 1 (by rfl) ⟨101801285, by rfl⟩ : syracuseStep 135735047 = 203602571) B203602571
theorem B5720159 : Blo 1505449 5720159 := bstep (se 1 (by rfl) ⟨4290119, by rfl⟩ : syracuseStep 5720159 = 8580239) B8580239
theorem B6432959 : Blo 1505449 6432959 := bstep (se 1 (by rfl) ⟨4824719, by rfl⟩ : syracuseStep 6432959 = 9649439) B9649439
theorem B7235887 : Blo 1505449 7235887 := bstep (se 1 (by rfl) ⟨5426915, by rfl⟩ : syracuseStep 7235887 = 10853831) B10853831
theorem B3811819 : Blo 1505449 3811819 := bstep (se 1 (by rfl) ⟨2858864, by rfl⟩ : syracuseStep 3811819 = 5717729) B5717729
theorem B38161145 : Blo 1505449 38161145 := bstep (se 2 (by rfl) ⟨14310429, by rfl⟩ : syracuseStep 38161145 = 28620859) B28620859
theorem B5081939 : Blo 1505449 5081939 := bstep (se 1 (by rfl) ⟨3811454, by rfl⟩ : syracuseStep 5081939 = 7622909) B7622909
theorem B20941687 : Blo 1505449 20941687 := bstep (se 1 (by rfl) ⟨15706265, by rfl⟩ : syracuseStep 20941687 = 31412531) B31412531
theorem B14470163 : Blo 1505449 14470163 := bstep (se 1 (by rfl) ⟨10852622, by rfl⟩ : syracuseStep 14470163 = 21705245) B21705245
theorem B7728311 : Blo 1505449 7728311 := bstep (se 1 (by rfl) ⟨5796233, by rfl⟩ : syracuseStep 7728311 = 11592467) B11592467
theorem B5082479 : Blo 1505449 5082479 := bstep (se 1 (by rfl) ⟨3811859, by rfl⟩ : syracuseStep 5082479 = 7623719) B7623719
theorem B14667161 : Blo 1505449 14667161 := bstep (se 2 (by rfl) ⟨5500185, by rfl⟩ : syracuseStep 14667161 = 11000371) B11000371
theorem B5959079 : Blo 1505449 5959079 := bstep (se 1 (by rfl) ⟨4469309, by rfl⟩ : syracuseStep 5959079 = 8938619) B8938619
theorem B7433819 : Blo 1505449 7433819 := bstep (se 1 (by rfl) ⟨5575364, by rfl⟩ : syracuseStep 7433819 = 11150729) B11150729
theorem B27479897 : Blo 1505449 27479897 := bstep (se 2 (by rfl) ⟨10304961, by rfl⟩ : syracuseStep 27479897 = 20609923) B20609923
theorem B3813257 : Blo 1505449 3813257 := bstep (se 2 (by rfl) ⟨1429971, by rfl⟩ : syracuseStep 3813257 = 2859943) B2859943
theorem B3215335 : Blo 1505449 3215335 := bstep (se 1 (by rfl) ⟨2411501, by rfl⟩ : syracuseStep 3215335 = 4823003) B4823003
theorem B10858789 : Blo 1505449 10858789 := bstep (se 4 (by rfl) ⟨1018011, by rfl⟩ : syracuseStep 10858789 = 2036023) B2036023
theorem B11440439 : Blo 1505449 11440439 := bstep (se 1 (by rfl) ⟨8580329, by rfl⟩ : syracuseStep 11440439 = 17160659) B17160659
theorem B5083721 : Blo 1505449 5083721 := bstep (se 2 (by rfl) ⟨1906395, by rfl⟩ : syracuseStep 5083721 = 3812791) B3812791
theorem B13046345 : Blo 1505449 13046345 := bstep (se 2 (by rfl) ⟨4892379, by rfl⟩ : syracuseStep 13046345 = 9784759) B9784759
theorem B21721729 : Blo 1505449 21721729 := bstep (se 2 (by rfl) ⟨8145648, by rfl⟩ : syracuseStep 21721729 = 16291297) B16291297
theorem B6107843 : Blo 1505449 6107843 := bstep (se 1 (by rfl) ⟨4580882, by rfl⟩ : syracuseStep 6107843 = 9161765) B9161765
theorem B11432663 : Blo 1505449 11432663 := bstep (se 1 (by rfl) ⟨8574497, by rfl⟩ : syracuseStep 11432663 = 17148995) B17148995
theorem B3388139 : Blo 1505449 3388139 := bstep (se 1 (by rfl) ⟨2541104, by rfl⟩ : syracuseStep 3388139 = 5082209) B5082209
theorem B12866363 : Blo 1505449 12866363 := bstep (se 1 (by rfl) ⟨9649772, by rfl⟩ : syracuseStep 12866363 = 19299545) B19299545
theorem B3617743 : Blo 1505449 3617743 := bstep (se 1 (by rfl) ⟨2713307, by rfl⟩ : syracuseStep 3617743 = 5426615) B5426615
theorem B3388409 : Blo 1505449 3388409 := bstep (se 2 (by rfl) ⟨1270653, by rfl⟩ : syracuseStep 3388409 = 2541307) B2541307
theorem B3388499 : Blo 1505449 3388499 := bstep (se 1 (by rfl) ⟨2541374, by rfl⟩ : syracuseStep 3388499 = 5082749) B5082749
theorem B34796627 : Blo 1505449 34796627 := bstep (se 1 (by rfl) ⟨26097470, by rfl⟩ : syracuseStep 34796627 = 52194941) B52194941
theorem B23499953 : Blo 1505449 23499953 := bstep (se 2 (by rfl) ⟨8812482, by rfl⟩ : syracuseStep 23499953 = 17624965) B17624965
theorem B3388679 : Blo 1505449 3388679 := bstep (se 1 (by rfl) ⟨2541509, by rfl⟩ : syracuseStep 3388679 = 5083019) B5083019
theorem B6608393 : Blo 1505449 6608393 := bstep (se 2 (by rfl) ⟨2478147, by rfl⟩ : syracuseStep 6608393 = 4956295) B4956295
theorem B3389039 : Blo 1505449 3389039 := bstep (se 1 (by rfl) ⟨2541779, by rfl⟩ : syracuseStep 3389039 = 5083559) B5083559
theorem B6608671 : Blo 1505449 6608671 := bstep (se 1 (by rfl) ⟨4956503, by rfl⟩ : syracuseStep 6608671 = 9913007) B9913007
theorem B1505511 : Blo 1505449 1505511 := bstep (se 1 (by rfl) ⟨1129133, by rfl⟩ : syracuseStep 1505511 = 2258267) B2258267
theorem B1505695 : Blo 1505449 1505695 := bstep (se 1 (by rfl) ⟨1129271, by rfl⟩ : syracuseStep 1505695 = 2258543) B2258543
theorem B1505743 : Blo 1505449 1505743 := bstep (se 1 (by rfl) ⟨1129307, by rfl⟩ : syracuseStep 1505743 = 2258615) B2258615
theorem B2259407 : Blo 1505449 2259407 := bstep (se 1 (by rfl) ⟨1694555, by rfl⟩ : syracuseStep 2259407 = 3389111) B3389111
theorem B3389903 : Blo 1505449 3389903 := bstep (se 1 (by rfl) ⟨2542427, by rfl⟩ : syracuseStep 3389903 = 5084855) B5084855
theorem B1505767 : Blo 1505449 1505767 := bstep (se 1 (by rfl) ⟨1129325, by rfl⟩ : syracuseStep 1505767 = 2258651) B2258651
theorem B3217897 : Blo 1505449 3217897 := bstep (se 2 (by rfl) ⟨1206711, by rfl⟩ : syracuseStep 3217897 = 2413423) B2413423
theorem B2259497 : Blo 1505449 2259497 := bstep (se 2 (by rfl) ⟨847311, by rfl⟩ : syracuseStep 2259497 = 1694623) B1694623
theorem B2144809 : Blo 1505449 2144809 := bstep (se 2 (by rfl) ⟨804303, by rfl⟩ : syracuseStep 2144809 = 1608607) B1608607
theorem B3389993 : Blo 1505449 3389993 := bstep (se 2 (by rfl) ⟨1271247, by rfl⟩ : syracuseStep 3389993 = 2542495) B2542495
theorem B1505883 : Blo 1505449 1505883 := bstep (se 1 (by rfl) ⟨1129412, by rfl⟩ : syracuseStep 1505883 = 2258825) B2258825
theorem B1694299 : Blo 1505449 1694299 := bstep (se 1 (by rfl) ⟨1270724, by rfl⟩ : syracuseStep 1694299 = 2541449) B2541449
theorem B1505951 : Blo 1505449 1505951 := bstep (se 1 (by rfl) ⟨1129463, by rfl⟩ : syracuseStep 1505951 = 2258927) B2258927
theorem B2259689 : Blo 1505449 2259689 := bstep (se 2 (by rfl) ⟨847383, by rfl⟩ : syracuseStep 2259689 = 1694767) B1694767
theorem B3218231 : Blo 1505449 3218231 := bstep (se 1 (by rfl) ⟨2413673, by rfl⟩ : syracuseStep 3218231 = 4827347) B4827347
theorem B1506119 : Blo 1505449 1506119 := bstep (se 1 (by rfl) ⟨1129589, by rfl⟩ : syracuseStep 1506119 = 2259179) B2259179
theorem B19299181 : Blo 1505449 19299181 := bstep (se 3 (by rfl) ⟨3618596, by rfl⟩ : syracuseStep 19299181 = 7237193) B7237193
theorem B1506159 : Blo 1505449 1506159 := bstep (se 1 (by rfl) ⟨1129619, by rfl⟩ : syracuseStep 1506159 = 2259239) B2259239
theorem B1694587 : Blo 1505449 1694587 := bstep (se 1 (by rfl) ⟨1270940, by rfl⟩ : syracuseStep 1694587 = 2541881) B2541881
theorem B1506215 : Blo 1505449 1506215 := bstep (se 1 (by rfl) ⟨1129661, by rfl⟩ : syracuseStep 1506215 = 2259323) B2259323
theorem B3668903 : Blo 1505449 3668903 := bstep (se 1 (by rfl) ⟨2751677, by rfl⟩ : syracuseStep 3668903 = 5503355) B5503355
theorem B2751443 : Blo 1505449 2751443 := bstep (se 1 (by rfl) ⟨2063582, by rfl⟩ : syracuseStep 2751443 = 4127165) B4127165
theorem B1506395 : Blo 1505449 1506395 := bstep (se 1 (by rfl) ⟨1129796, by rfl⟩ : syracuseStep 1506395 = 2259593) B2259593
theorem B7625825 : Blo 1505449 7625825 := bstep (se 2 (by rfl) ⟨2859684, by rfl⟩ : syracuseStep 7625825 = 5719369) B5719369
theorem B2260073 : Blo 1505449 2260073 := bstep (se 2 (by rfl) ⟨847527, by rfl⟩ : syracuseStep 2260073 = 1695055) B1695055
theorem B3390569 : Blo 1505449 3390569 := bstep (se 2 (by rfl) ⟨1271463, by rfl⟩ : syracuseStep 3390569 = 2542927) B2542927
theorem B2858105 : Blo 1505449 2858105 := bstep (se 2 (by rfl) ⟨1071789, by rfl⟩ : syracuseStep 2858105 = 2143579) B2143579
theorem B1506511 : Blo 1505449 1506511 := bstep (se 1 (by rfl) ⟨1129883, by rfl⟩ : syracuseStep 1506511 = 2259767) B2259767
theorem B1506535 : Blo 1505449 1506535 := bstep (se 1 (by rfl) ⟨1129901, by rfl⟩ : syracuseStep 1506535 = 2259803) B2259803
theorem B2260199 : Blo 1505449 2260199 := bstep (se 1 (by rfl) ⟨1695149, by rfl⟩ : syracuseStep 2260199 = 3390299) B3390299
theorem B1506631 : Blo 1505449 1506631 := bstep (se 1 (by rfl) ⟨1129973, by rfl⟩ : syracuseStep 1506631 = 2259947) B2259947
theorem B1932751 : Blo 1505449 1932751 := bstep (se 1 (by rfl) ⟨1449563, by rfl⟩ : syracuseStep 1932751 = 2899127) B2899127
theorem B1506767 : Blo 1505449 1506767 := bstep (se 1 (by rfl) ⟨1130075, by rfl⟩ : syracuseStep 1506767 = 2260151) B2260151
theorem B1506927 : Blo 1505449 1506927 := bstep (se 1 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 1506927 = 2260391) B2260391
theorem B5717699 : Blo 1505449 5717699 := bstep (se 1 (by rfl) ⟨4288274, by rfl⟩ : syracuseStep 5717699 = 8576549) B8576549
theorem B2899687 : Blo 1505449 2899687 := bstep (se 1 (by rfl) ⟨2174765, by rfl⟩ : syracuseStep 2899687 = 4349531) B4349531
theorem B7626635 : Blo 1505449 7626635 := bstep (se 1 (by rfl) ⟨5719976, by rfl⟩ : syracuseStep 7626635 = 11439953) B11439953
theorem B11436065 : Blo 1505449 11436065 := bstep (se 2 (by rfl) ⟨4288524, by rfl⟩ : syracuseStep 11436065 = 8577049) B8577049
theorem B7626959 : Blo 1505449 7626959 := bstep (se 1 (by rfl) ⟨5720219, by rfl⟩ : syracuseStep 7626959 = 11440439) B11440439
theorem B8577575 : Blo 1505449 8577575 := bstep (se 1 (by rfl) ⟨6433181, by rfl⟩ : syracuseStep 8577575 = 12866363) B12866363
theorem B25732241 : Blo 1505449 25732241 := bstep (se 2 (by rfl) ⟨9649590, by rfl⟩ : syracuseStep 25732241 = 19299181) B19299181
theorem B90490031 : Blo 1505449 90490031 := bstep (se 1 (by rfl) ⟨67867523, by rfl⟩ : syracuseStep 90490031 = 135735047) B135735047
theorem B7628093 : Blo 1505449 7628093 := bstep (se 3 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 7628093 = 2860535) B2860535
theorem B16287581 : Blo 1505449 16287581 := bstep (se 3 (by rfl) ⟨3053921, by rfl⟩ : syracuseStep 16287581 = 6107843) B6107843
theorem B10308005 : Blo 1505449 10308005 := bstep (se 4 (by rfl) ⟨966375, by rfl⟩ : syracuseStep 10308005 = 1932751) B1932751
theorem B3811799 : Blo 1505449 3811799 := bstep (se 1 (by rfl) ⟨2858849, by rfl⟩ : syracuseStep 3811799 = 5717699) B5717699
theorem B18319931 : Blo 1505449 18319931 := bstep (se 1 (by rfl) ⟨13739948, by rfl⟩ : syracuseStep 18319931 = 27479897) B27479897
theorem B2542171 : Blo 1505449 2542171 := bstep (se 1 (by rfl) ⟨1906628, by rfl⟩ : syracuseStep 2542171 = 3813257) B3813257
theorem B4287113 : Blo 1505449 4287113 := bstep (se 2 (by rfl) ⟨1607667, by rfl⟩ : syracuseStep 4287113 = 3215335) B3215335
theorem B4287239 : Blo 1505449 4287239 := bstep (se 1 (by rfl) ⟨3215429, by rfl⟩ : syracuseStep 4287239 = 6430859) B6430859
theorem B6433607 : Blo 1505449 6433607 := bstep (se 1 (by rfl) ⟨4825205, by rfl⟩ : syracuseStep 6433607 = 9650411) B9650411
theorem B11438981 : Blo 1505449 11438981 := bstep (se 4 (by rfl) ⟨1072404, by rfl⟩ : syracuseStep 11438981 = 2144809) B2144809
theorem B7621613 : Blo 1505449 7621613 := bstep (se 3 (by rfl) ⟨1429052, by rfl⟩ : syracuseStep 7621613 = 2858105) B2858105
theorem B14478385 : Blo 1505449 14478385 := bstep (se 2 (by rfl) ⟨5429394, by rfl⟩ : syracuseStep 14478385 = 10858789) B10858789
theorem B7621775 : Blo 1505449 7621775 := bstep (se 1 (by rfl) ⟨5716331, by rfl⟩ : syracuseStep 7621775 = 11432663) B11432663
theorem B5082425 : Blo 1505449 5082425 := bstep (se 2 (by rfl) ⟨1905909, by rfl⟩ : syracuseStep 5082425 = 3811819) B3811819
theorem B15666635 : Blo 1505449 15666635 := bstep (se 1 (by rfl) ⟨11749976, by rfl⟩ : syracuseStep 15666635 = 23499953) B23499953
theorem B28962305 : Blo 1505449 28962305 := bstep (se 2 (by rfl) ⟨10860864, by rfl⟩ : syracuseStep 28962305 = 21721729) B21721729
theorem B39112429 : Blo 1505449 39112429 := bstep (se 3 (by rfl) ⟨7333580, by rfl⟩ : syracuseStep 39112429 = 14667161) B14667161
theorem B3813115 : Blo 1505449 3813115 := bstep (se 1 (by rfl) ⟨2859836, by rfl⟩ : syracuseStep 3813115 = 5719673) B5719673
theorem B27922249 : Blo 1505449 27922249 := bstep (se 2 (by rfl) ⟨10470843, by rfl⟩ : syracuseStep 27922249 = 20941687) B20941687
theorem B3813439 : Blo 1505449 3813439 := bstep (se 1 (by rfl) ⟨2860079, by rfl⟩ : syracuseStep 3813439 = 5720159) B5720159
theorem B4288639 : Blo 1505449 4288639 := bstep (se 1 (by rfl) ⟨3216479, by rfl⟩ : syracuseStep 4288639 = 6432959) B6432959
theorem B35246245 : Blo 1505449 35246245 := bstep (se 4 (by rfl) ⟨3304335, by rfl⟩ : syracuseStep 35246245 = 6608671) B6608671
theorem B3387689 : Blo 1505449 3387689 := bstep (se 2 (by rfl) ⟨1270383, by rfl⟩ : syracuseStep 3387689 = 2540767) B2540767
theorem B25440763 : Blo 1505449 25440763 := bstep (se 1 (by rfl) ⟨19080572, by rfl⟩ : syracuseStep 25440763 = 38161145) B38161145
theorem B3387959 : Blo 1505449 3387959 := bstep (se 1 (by rfl) ⟨2540969, by rfl⟩ : syracuseStep 3387959 = 5081939) B5081939
theorem B2445935 : Blo 1505449 2445935 := bstep (se 1 (by rfl) ⟨1834451, by rfl⟩ : syracuseStep 2445935 = 3668903) B3668903
theorem B9646775 : Blo 1505449 9646775 := bstep (se 1 (by rfl) ⟨7235081, by rfl⟩ : syracuseStep 9646775 = 14470163) B14470163
theorem B5083883 : Blo 1505449 5083883 := bstep (se 1 (by rfl) ⟨3812912, by rfl⟩ : syracuseStep 5083883 = 7625825) B7625825
theorem B8581949 : Blo 1505449 8581949 := bstep (se 3 (by rfl) ⟨1609115, by rfl⟩ : syracuseStep 8581949 = 3218231) B3218231
theorem B3388319 : Blo 1505449 3388319 := bstep (se 1 (by rfl) ⟨2541239, by rfl⟩ : syracuseStep 3388319 = 5082479) B5082479
theorem B5084423 : Blo 1505449 5084423 := bstep (se 1 (by rfl) ⟨3813317, by rfl⟩ : syracuseStep 5084423 = 7626635) B7626635
theorem B8574407 : Blo 1505449 8574407 := bstep (se 1 (by rfl) ⟨6430805, by rfl⟩ : syracuseStep 8574407 = 12861611) B12861611
theorem B10442459 : Blo 1505449 10442459 := bstep (se 1 (by rfl) ⟨7831844, by rfl⟩ : syracuseStep 10442459 = 15663689) B15663689
theorem B3389147 : Blo 1505449 3389147 := bstep (se 1 (by rfl) ⟨2541860, by rfl⟩ : syracuseStep 3389147 = 5083721) B5083721
theorem B8697563 : Blo 1505449 8697563 := bstep (se 1 (by rfl) ⟨6523172, by rfl⟩ : syracuseStep 8697563 = 13046345) B13046345
theorem B9647849 : Blo 1505449 9647849 := bstep (se 2 (by rfl) ⟨3617943, by rfl⟩ : syracuseStep 9647849 = 7235887) B7235887
theorem B20608829 : Blo 1505449 20608829 := bstep (se 3 (by rfl) ⟨3864155, by rfl⟩ : syracuseStep 20608829 = 7728311) B7728311
theorem B2258759 : Blo 1505449 2258759 := bstep (se 1 (by rfl) ⟨1694069, by rfl⟩ : syracuseStep 2258759 = 3388139) B3388139
theorem B2258939 : Blo 1505449 2258939 := bstep (se 1 (by rfl) ⟨1694204, by rfl⟩ : syracuseStep 2258939 = 3388409) B3388409
theorem B2258999 : Blo 1505449 2258999 := bstep (se 1 (by rfl) ⟨1694249, by rfl⟩ : syracuseStep 2258999 = 3388499) B3388499
theorem B23197751 : Blo 1505449 23197751 := bstep (se 1 (by rfl) ⟨17398313, by rfl⟩ : syracuseStep 23197751 = 34796627) B34796627
theorem B2259065 : Blo 1505449 2259065 := bstep (se 2 (by rfl) ⟨847149, by rfl⟩ : syracuseStep 2259065 = 1694299) B1694299
theorem B2259119 : Blo 1505449 2259119 := bstep (se 1 (by rfl) ⟨1694339, by rfl⟩ : syracuseStep 2259119 = 3388679) B3388679
theorem B4405595 : Blo 1505449 4405595 := bstep (se 1 (by rfl) ⟨3304196, by rfl⟩ : syracuseStep 4405595 = 6608393) B6608393
theorem B2259359 : Blo 1505449 2259359 := bstep (se 1 (by rfl) ⟨1694519, by rfl⟩ : syracuseStep 2259359 = 3389039) B3389039
theorem B2259449 : Blo 1505449 2259449 := bstep (se 2 (by rfl) ⟨847293, by rfl⟩ : syracuseStep 2259449 = 1694587) B1694587
theorem B4823657 : Blo 1505449 4823657 := bstep (se 2 (by rfl) ⟨1808871, by rfl⟩ : syracuseStep 4823657 = 3617743) B3617743
theorem B1506271 : Blo 1505449 1506271 := bstep (se 1 (by rfl) ⟨1129703, by rfl⟩ : syracuseStep 1506271 = 2259407) B2259407
theorem B2259935 : Blo 1505449 2259935 := bstep (se 1 (by rfl) ⟨1694951, by rfl⟩ : syracuseStep 2259935 = 3389903) B3389903
theorem B1506331 : Blo 1505449 1506331 := bstep (se 1 (by rfl) ⟨1129748, by rfl⟩ : syracuseStep 1506331 = 2259497) B2259497
theorem B2259995 : Blo 1505449 2259995 := bstep (se 1 (by rfl) ⟨1694996, by rfl⟩ : syracuseStep 2259995 = 3389993) B3389993
theorem B70540433 : Blo 1505449 70540433 := bstep (se 2 (by rfl) ⟨26452662, by rfl⟩ : syracuseStep 70540433 = 52905325) B52905325
theorem B1506459 : Blo 1505449 1506459 := bstep (se 1 (by rfl) ⟨1129844, by rfl⟩ : syracuseStep 1506459 = 2259689) B2259689
theorem B1834295 : Blo 1505449 1834295 := bstep (se 1 (by rfl) ⟨1375721, by rfl⟩ : syracuseStep 1834295 = 2751443) B2751443
theorem B1506715 : Blo 1505449 1506715 := bstep (se 1 (by rfl) ⟨1130036, by rfl⟩ : syracuseStep 1506715 = 2260073) B2260073
theorem B2260379 : Blo 1505449 2260379 := bstep (se 1 (by rfl) ⟨1695284, by rfl⟩ : syracuseStep 2260379 = 3390569) B3390569
theorem B1506799 : Blo 1505449 1506799 := bstep (se 1 (by rfl) ⟨1130099, by rfl⟩ : syracuseStep 1506799 = 2260199) B2260199
theorem B3972719 : Blo 1505449 3972719 := bstep (se 1 (by rfl) ⟨2979539, by rfl⟩ : syracuseStep 3972719 = 5959079) B5959079
theorem B3866249 : Blo 1505449 3866249 := bstep (se 2 (by rfl) ⟨1449843, by rfl⟩ : syracuseStep 3866249 = 2899687) B2899687
theorem B4955879 : Blo 1505449 4955879 := bstep (se 1 (by rfl) ⟨3716909, by rfl⟩ : syracuseStep 4955879 = 7433819) B7433819
theorem B17162117 : Blo 1505449 17162117 := bstep (se 4 (by rfl) ⟨1608948, by rfl⟩ : syracuseStep 17162117 = 3217897) B3217897
theorem B5718185 : Blo 1505449 5718185 := bstep (se 2 (by rfl) ⟨2144319, by rfl⟩ : syracuseStep 5718185 = 4288639) B4288639
theorem B5718383 : Blo 1505449 5718383 := bstep (se 1 (by rfl) ⟨4288787, by rfl⟩ : syracuseStep 5718383 = 8577575) B8577575
theorem B6431183 : Blo 1505449 6431183 := bstep (se 1 (by rfl) ⟨4823387, by rfl⟩ : syracuseStep 6431183 = 9646775) B9646775
theorem B17154827 : Blo 1505449 17154827 := bstep (se 1 (by rfl) ⟨12866120, by rfl⟩ : syracuseStep 17154827 = 25732241) B25732241
theorem B60326687 : Blo 1505449 60326687 := bstep (se 1 (by rfl) ⟨45245015, by rfl⟩ : syracuseStep 60326687 = 90490031) B90490031
theorem B11748253 : Blo 1505449 11748253 := bstep (se 3 (by rfl) ⟨2202797, by rfl⟩ : syracuseStep 11748253 = 4405595) B4405595
theorem B6431899 : Blo 1505449 6431899 := bstep (se 1 (by rfl) ⟨4823924, by rfl⟩ : syracuseStep 6431899 = 9647849) B9647849
theorem B13739219 : Blo 1505449 13739219 := bstep (se 1 (by rfl) ⟨10304414, by rfl⟩ : syracuseStep 13739219 = 20608829) B20608829
theorem B6522493 : Blo 1505449 6522493 := bstep (se 3 (by rfl) ⟨1222967, by rfl⟩ : syracuseStep 6522493 = 2445935) B2445935
theorem B2541199 : Blo 1505449 2541199 := bstep (se 1 (by rfl) ⟨1905899, by rfl⟩ : syracuseStep 2541199 = 3811799) B3811799
theorem B5081075 : Blo 1505449 5081075 := bstep (se 1 (by rfl) ⟨3810806, by rfl⟩ : syracuseStep 5081075 = 7621613) B7621613
theorem B5081183 : Blo 1505449 5081183 := bstep (se 1 (by rfl) ⟨3810887, by rfl⟩ : syracuseStep 5081183 = 7621775) B7621775
theorem B17156285 : Blo 1505449 17156285 := bstep (se 3 (by rfl) ⟨3216803, by rfl⟩ : syracuseStep 17156285 = 6433607) B6433607
theorem B2648479 : Blo 1505449 2648479 := bstep (se 1 (by rfl) ⟨1986359, by rfl⟩ : syracuseStep 2648479 = 3972719) B3972719
theorem B3303919 : Blo 1505449 3303919 := bstep (se 1 (by rfl) ⟨2477939, by rfl⟩ : syracuseStep 3303919 = 4955879) B4955879
theorem B5721299 : Blo 1505449 5721299 := bstep (se 1 (by rfl) ⟨4290974, by rfl⟩ : syracuseStep 5721299 = 8581949) B8581949
theorem B19565813 : Blo 1505449 19565813 := bstep (se 5 (by rfl) ⟨917147, by rfl⟩ : syracuseStep 19565813 = 1834295) B1834295
theorem B10858387 : Blo 1505449 10858387 := bstep (se 1 (by rfl) ⟨8143790, by rfl⟩ : syracuseStep 10858387 = 16287581) B16287581
theorem B19304513 : Blo 1505449 19304513 := bstep (se 2 (by rfl) ⟨7239192, by rfl⟩ : syracuseStep 19304513 = 14478385) B14478385
theorem B10309997 : Blo 1505449 10309997 := bstep (se 3 (by rfl) ⟨1933124, by rfl⟩ : syracuseStep 10309997 = 3866249) B3866249
theorem B3215771 : Blo 1505449 3215771 := bstep (se 1 (by rfl) ⟨2411828, by rfl⟩ : syracuseStep 3215771 = 4823657) B4823657
theorem B47026955 : Blo 1505449 47026955 := bstep (se 1 (by rfl) ⟨35270216, by rfl⟩ : syracuseStep 47026955 = 70540433) B70540433
theorem B3388283 : Blo 1505449 3388283 := bstep (se 1 (by rfl) ⟨2541212, by rfl⟩ : syracuseStep 3388283 = 5082425) B5082425
theorem B5084153 : Blo 1505449 5084153 := bstep (se 2 (by rfl) ⟨1906557, by rfl⟩ : syracuseStep 5084153 = 3813115) B3813115
theorem B37229665 : Blo 1505449 37229665 := bstep (se 2 (by rfl) ⟨13961124, by rfl⟩ : syracuseStep 37229665 = 27922249) B27922249
theorem B11441411 : Blo 1505449 11441411 := bstep (se 1 (by rfl) ⟨8581058, by rfl⟩ : syracuseStep 11441411 = 17162117) B17162117
theorem B7624043 : Blo 1505449 7624043 := bstep (se 1 (by rfl) ⟨5718032, by rfl⟩ : syracuseStep 7624043 = 11436065) B11436065
theorem B5084585 : Blo 1505449 5084585 := bstep (se 2 (by rfl) ⟨1906719, by rfl⟩ : syracuseStep 5084585 = 3813439) B3813439
theorem B5084639 : Blo 1505449 5084639 := bstep (se 1 (by rfl) ⟨3813479, by rfl⟩ : syracuseStep 5084639 = 7626959) B7626959
theorem B2258459 : Blo 1505449 2258459 := bstep (se 1 (by rfl) ⟨1693844, by rfl⟩ : syracuseStep 2258459 = 3387689) B3387689
theorem B46994993 : Blo 1505449 46994993 := bstep (se 2 (by rfl) ⟨17623122, by rfl⟩ : syracuseStep 46994993 = 35246245) B35246245
theorem B2258639 : Blo 1505449 2258639 := bstep (se 1 (by rfl) ⟨1693979, by rfl⟩ : syracuseStep 2258639 = 3387959) B3387959
theorem B3389255 : Blo 1505449 3389255 := bstep (se 1 (by rfl) ⟨2541941, by rfl⟩ : syracuseStep 3389255 = 5083883) B5083883
theorem B2258879 : Blo 1505449 2258879 := bstep (se 1 (by rfl) ⟨1694159, by rfl⟩ : syracuseStep 2258879 = 3388319) B3388319
theorem B33921017 : Blo 1505449 33921017 := bstep (se 2 (by rfl) ⟨12720381, by rfl⟩ : syracuseStep 33921017 = 25440763) B25440763
theorem B3389561 : Blo 1505449 3389561 := bstep (se 2 (by rfl) ⟨1271085, by rfl⟩ : syracuseStep 3389561 = 2542171) B2542171
theorem B3389615 : Blo 1505449 3389615 := bstep (se 1 (by rfl) ⟨2542211, by rfl⟩ : syracuseStep 3389615 = 5084423) B5084423
theorem B5085395 : Blo 1505449 5085395 := bstep (se 1 (by rfl) ⟨3814046, by rfl⟩ : syracuseStep 5085395 = 7628093) B7628093
theorem B5716271 : Blo 1505449 5716271 := bstep (se 1 (by rfl) ⟨4287203, by rfl⟩ : syracuseStep 5716271 = 8574407) B8574407
theorem B6961639 : Blo 1505449 6961639 := bstep (se 1 (by rfl) ⟨5221229, by rfl⟩ : syracuseStep 6961639 = 10442459) B10442459
theorem B2259431 : Blo 1505449 2259431 := bstep (se 1 (by rfl) ⟨1694573, by rfl⟩ : syracuseStep 2259431 = 3389147) B3389147
theorem B5798375 : Blo 1505449 5798375 := bstep (se 1 (by rfl) ⟨4348781, by rfl⟩ : syracuseStep 5798375 = 8697563) B8697563
theorem B41777693 : Blo 1505449 41777693 := bstep (se 3 (by rfl) ⟨7833317, by rfl⟩ : syracuseStep 41777693 = 15666635) B15666635
theorem B1505839 : Blo 1505449 1505839 := bstep (se 1 (by rfl) ⟨1129379, by rfl⟩ : syracuseStep 1505839 = 2258759) B2258759
theorem B1505959 : Blo 1505449 1505959 := bstep (se 1 (by rfl) ⟨1129469, by rfl⟩ : syracuseStep 1505959 = 2258939) B2258939
theorem B1505999 : Blo 1505449 1505999 := bstep (se 1 (by rfl) ⟨1129499, by rfl⟩ : syracuseStep 1505999 = 2258999) B2258999
theorem B15465167 : Blo 1505449 15465167 := bstep (se 1 (by rfl) ⟨11598875, by rfl⟩ : syracuseStep 15465167 = 23197751) B23197751
theorem B1506043 : Blo 1505449 1506043 := bstep (se 1 (by rfl) ⟨1129532, by rfl⟩ : syracuseStep 1506043 = 2259065) B2259065
theorem B1506079 : Blo 1505449 1506079 := bstep (se 1 (by rfl) ⟨1129559, by rfl⟩ : syracuseStep 1506079 = 2259119) B2259119
theorem B1506239 : Blo 1505449 1506239 := bstep (se 1 (by rfl) ⟨1129679, by rfl⟩ : syracuseStep 1506239 = 2259359) B2259359
theorem B6872003 : Blo 1505449 6872003 := bstep (se 1 (by rfl) ⟨5154002, by rfl⟩ : syracuseStep 6872003 = 10308005) B10308005
theorem B1506299 : Blo 1505449 1506299 := bstep (se 1 (by rfl) ⟨1129724, by rfl⟩ : syracuseStep 1506299 = 2259449) B2259449
theorem B12213287 : Blo 1505449 12213287 := bstep (se 1 (by rfl) ⟨9159965, by rfl⟩ : syracuseStep 12213287 = 18319931) B18319931
theorem B2858075 : Blo 1505449 2858075 := bstep (se 1 (by rfl) ⟨2143556, by rfl⟩ : syracuseStep 2858075 = 4287113) B4287113
theorem B2858159 : Blo 1505449 2858159 := bstep (se 1 (by rfl) ⟨2143619, by rfl⟩ : syracuseStep 2858159 = 4287239) B4287239
theorem B7625987 : Blo 1505449 7625987 := bstep (se 1 (by rfl) ⟨5719490, by rfl⟩ : syracuseStep 7625987 = 11438981) B11438981
theorem B1506623 : Blo 1505449 1506623 := bstep (se 1 (by rfl) ⟨1129967, by rfl⟩ : syracuseStep 1506623 = 2259935) B2259935
theorem B1506663 : Blo 1505449 1506663 := bstep (se 1 (by rfl) ⟨1129997, by rfl⟩ : syracuseStep 1506663 = 2259995) B2259995
theorem B1506919 : Blo 1505449 1506919 := bstep (se 1 (by rfl) ⟨1130189, by rfl⟩ : syracuseStep 1506919 = 2260379) B2260379
theorem B52149905 : Blo 1505449 52149905 := bstep (se 2 (by rfl) ⟨19556214, by rfl⟩ : syracuseStep 52149905 = 39112429) B39112429
theorem B19308203 : Blo 1505449 19308203 := bstep (se 1 (by rfl) ⟨14481152, by rfl⟩ : syracuseStep 19308203 = 28962305) B28962305
theorem B12869675 : Blo 1505449 12869675 := bstep (se 1 (by rfl) ⟨9652256, by rfl⟩ : syracuseStep 12869675 = 19304513) B19304513
theorem B6873331 : Blo 1505449 6873331 := bstep (se 1 (by rfl) ⟨5154998, by rfl⟩ : syracuseStep 6873331 = 10309997) B10309997
theorem B11436551 : Blo 1505449 11436551 := bstep (se 1 (by rfl) ⟨8577413, by rfl⟩ : syracuseStep 11436551 = 17154827) B17154827
theorem B31351303 : Blo 1505449 31351303 := bstep (se 1 (by rfl) ⟨23513477, by rfl⟩ : syracuseStep 31351303 = 47026955) B47026955
theorem B3531305 : Blo 1505449 3531305 := bstep (se 2 (by rfl) ⟨1324239, by rfl⟩ : syracuseStep 3531305 = 2648479) B2648479
theorem B9282185 : Blo 1505449 9282185 := bstep (se 2 (by rfl) ⟨3480819, by rfl⟩ : syracuseStep 9282185 = 6961639) B6961639
theorem B52175501 : Blo 1505449 52175501 := bstep (se 3 (by rfl) ⟨9782906, by rfl⟩ : syracuseStep 52175501 = 19565813) B19565813
theorem B9159479 : Blo 1505449 9159479 := bstep (se 1 (by rfl) ⟨6869609, by rfl⟩ : syracuseStep 9159479 = 13739219) B13739219
theorem B7627607 : Blo 1505449 7627607 := bstep (se 1 (by rfl) ⟨5720705, by rfl⟩ : syracuseStep 7627607 = 11441411) B11441411
theorem B15664337 : Blo 1505449 15664337 := bstep (se 2 (by rfl) ⟨5874126, by rfl⟩ : syracuseStep 15664337 = 11748253) B11748253
theorem B11437523 : Blo 1505449 11437523 := bstep (se 1 (by rfl) ⟨8578142, by rfl⟩ : syracuseStep 11437523 = 17156285) B17156285
theorem B3810847 : Blo 1505449 3810847 := bstep (se 1 (by rfl) ⟨2858135, by rfl⟩ : syracuseStep 3810847 = 5716271) B5716271
theorem B4581335 : Blo 1505449 4581335 := bstep (se 1 (by rfl) ⟨3436001, by rfl⟩ : syracuseStep 4581335 = 6872003) B6872003
theorem B12872135 : Blo 1505449 12872135 := bstep (se 1 (by rfl) ⟨9654101, by rfl⟩ : syracuseStep 12872135 = 19308203) B19308203
theorem B14477849 : Blo 1505449 14477849 := bstep (se 2 (by rfl) ⟨5429193, by rfl⟩ : syracuseStep 14477849 = 10858387) B10858387
theorem B3812123 : Blo 1505449 3812123 := bstep (se 1 (by rfl) ⟨2859092, by rfl⟩ : syracuseStep 3812123 = 5718185) B5718185
theorem B3812255 : Blo 1505449 3812255 := bstep (se 1 (by rfl) ⟨2859191, by rfl⟩ : syracuseStep 3812255 = 5718383) B5718383
theorem B4287455 : Blo 1505449 4287455 := bstep (se 1 (by rfl) ⟨3215591, by rfl⟩ : syracuseStep 4287455 = 6431183) B6431183
theorem B40217791 : Blo 1505449 40217791 := bstep (se 1 (by rfl) ⟨30163343, by rfl⟩ : syracuseStep 40217791 = 60326687) B60326687
theorem B5082695 : Blo 1505449 5082695 := bstep (se 1 (by rfl) ⟨3812021, by rfl⟩ : syracuseStep 5082695 = 7624043) B7624043
theorem B31329995 : Blo 1505449 31329995 := bstep (se 1 (by rfl) ⟨23497496, by rfl⟩ : syracuseStep 31329995 = 46994993) B46994993
theorem B3387383 : Blo 1505449 3387383 := bstep (se 1 (by rfl) ⟨2540537, by rfl⟩ : syracuseStep 3387383 = 5081075) B5081075
theorem B22614011 : Blo 1505449 22614011 := bstep (se 1 (by rfl) ⟨16960508, by rfl⟩ : syracuseStep 22614011 = 33921017) B33921017
theorem B3387455 : Blo 1505449 3387455 := bstep (se 1 (by rfl) ⟨2540591, by rfl⟩ : syracuseStep 3387455 = 5081183) B5081183
theorem B49639553 : Blo 1505449 49639553 := bstep (se 2 (by rfl) ⟨18614832, by rfl⟩ : syracuseStep 49639553 = 37229665) B37229665
theorem B10310111 : Blo 1505449 10310111 := bstep (se 1 (by rfl) ⟨7732583, by rfl⟩ : syracuseStep 10310111 = 15465167) B15465167
theorem B1905383 : Blo 1505449 1905383 := bstep (se 1 (by rfl) ⟨1429037, by rfl⟩ : syracuseStep 1905383 = 2858075) B2858075
theorem B1905439 : Blo 1505449 1905439 := bstep (se 1 (by rfl) ⟨1429079, by rfl⟩ : syracuseStep 1905439 = 2858159) B2858159
theorem B3814199 : Blo 1505449 3814199 := bstep (se 1 (by rfl) ⟨2860649, by rfl⟩ : syracuseStep 3814199 = 5721299) B5721299
theorem B8696657 : Blo 1505449 8696657 := bstep (se 2 (by rfl) ⟨3261246, by rfl⟩ : syracuseStep 8696657 = 6522493) B6522493
theorem B5083991 : Blo 1505449 5083991 := bstep (se 1 (by rfl) ⟨3812993, by rfl⟩ : syracuseStep 5083991 = 7625987) B7625987
theorem B3388265 : Blo 1505449 3388265 := bstep (se 2 (by rfl) ⟨1270599, by rfl⟩ : syracuseStep 3388265 = 2541199) B2541199
theorem B2143847 : Blo 1505449 2143847 := bstep (se 1 (by rfl) ⟨1607885, by rfl⟩ : syracuseStep 2143847 = 3215771) B3215771
theorem B2258855 : Blo 1505449 2258855 := bstep (se 1 (by rfl) ⟨1694141, by rfl⟩ : syracuseStep 2258855 = 3388283) B3388283
theorem B3389435 : Blo 1505449 3389435 := bstep (se 1 (by rfl) ⟨2542076, by rfl⟩ : syracuseStep 3389435 = 5084153) B5084153
theorem B3389723 : Blo 1505449 3389723 := bstep (se 1 (by rfl) ⟨2542292, by rfl⟩ : syracuseStep 3389723 = 5084585) B5084585
theorem B3389759 : Blo 1505449 3389759 := bstep (se 1 (by rfl) ⟨2542319, by rfl⟩ : syracuseStep 3389759 = 5084639) B5084639
theorem B1505639 : Blo 1505449 1505639 := bstep (se 1 (by rfl) ⟨1129229, by rfl⟩ : syracuseStep 1505639 = 2258459) B2258459
theorem B1505759 : Blo 1505449 1505759 := bstep (se 1 (by rfl) ⟨1129319, by rfl⟩ : syracuseStep 1505759 = 2258639) B2258639
theorem B2259503 : Blo 1505449 2259503 := bstep (se 1 (by rfl) ⟨1694627, by rfl⟩ : syracuseStep 2259503 = 3389255) B3389255
theorem B1505919 : Blo 1505449 1505919 := bstep (se 1 (by rfl) ⟨1129439, by rfl⟩ : syracuseStep 1505919 = 2258879) B2258879
theorem B2259707 : Blo 1505449 2259707 := bstep (se 1 (by rfl) ⟨1694780, by rfl⟩ : syracuseStep 2259707 = 3389561) B3389561
theorem B2259743 : Blo 1505449 2259743 := bstep (se 1 (by rfl) ⟨1694807, by rfl⟩ : syracuseStep 2259743 = 3389615) B3389615
theorem B3390263 : Blo 1505449 3390263 := bstep (se 1 (by rfl) ⟨2542697, by rfl⟩ : syracuseStep 3390263 = 5085395) B5085395
theorem B8575865 : Blo 1505449 8575865 := bstep (se 2 (by rfl) ⟨3215949, by rfl⟩ : syracuseStep 8575865 = 6431899) B6431899
theorem B1506287 : Blo 1505449 1506287 := bstep (se 1 (by rfl) ⟨1129715, by rfl⟩ : syracuseStep 1506287 = 2259431) B2259431
theorem B3865583 : Blo 1505449 3865583 := bstep (se 1 (by rfl) ⟨2899187, by rfl⟩ : syracuseStep 3865583 = 5798375) B5798375
theorem B27851795 : Blo 1505449 27851795 := bstep (se 1 (by rfl) ⟨20888846, by rfl⟩ : syracuseStep 27851795 = 41777693) B41777693
theorem B8142191 : Blo 1505449 8142191 := bstep (se 1 (by rfl) ⟨6106643, by rfl⟩ : syracuseStep 8142191 = 12213287) B12213287
theorem B34766603 : Blo 1505449 34766603 := bstep (se 1 (by rfl) ⟨26074952, by rfl⟩ : syracuseStep 34766603 = 52149905) B52149905
theorem B17620901 : Blo 1505449 17620901 := bstep (se 4 (by rfl) ⟨1651959, by rfl⟩ : syracuseStep 17620901 = 3303919) B3303919
theorem B167206949 : Blo 1505449 167206949 := bstep (se 4 (by rfl) ⟨15675651, by rfl⟩ : syracuseStep 167206949 = 31351303) B31351303
theorem B6873407 : Blo 1505449 6873407 := bstep (se 1 (by rfl) ⟨5155055, by rfl⟩ : syracuseStep 6873407 = 10310111) B10310111
theorem B34783667 : Blo 1505449 34783667 := bstep (se 1 (by rfl) ⟨26087750, by rfl⟩ : syracuseStep 34783667 = 52175501) B52175501
theorem B2540585 : Blo 1505449 2540585 := bstep (se 2 (by rfl) ⟨952719, by rfl⟩ : syracuseStep 2540585 = 1905439) B1905439
theorem B9651899 : Blo 1505449 9651899 := bstep (se 1 (by rfl) ⟨7238924, by rfl⟩ : syracuseStep 9651899 = 14477849) B14477849
theorem B2541415 : Blo 1505449 2541415 := bstep (se 1 (by rfl) ⟨1906061, by rfl⟩ : syracuseStep 2541415 = 3812123) B3812123
theorem B5081021 : Blo 1505449 5081021 := bstep (se 3 (by rfl) ⟨952691, by rfl⟩ : syracuseStep 5081021 = 1905383) B1905383
theorem B2541503 : Blo 1505449 2541503 := bstep (se 1 (by rfl) ⟨1906127, by rfl⟩ : syracuseStep 2541503 = 3812255) B3812255
theorem B5081129 : Blo 1505449 5081129 := bstep (se 2 (by rfl) ⟨1905423, by rfl⟩ : syracuseStep 5081129 = 3810847) B3810847
theorem B23177735 : Blo 1505449 23177735 := bstep (se 1 (by rfl) ⟨17383301, by rfl⟩ : syracuseStep 23177735 = 34766603) B34766603
theorem B10308221 : Blo 1505449 10308221 := bstep (se 3 (by rfl) ⟨1932791, by rfl⟩ : syracuseStep 10308221 = 3865583) B3865583
theorem B15076007 : Blo 1505449 15076007 := bstep (se 1 (by rfl) ⟨11307005, by rfl⟩ : syracuseStep 15076007 = 22614011) B22614011
theorem B8579783 : Blo 1505449 8579783 := bstep (se 1 (by rfl) ⟨6434837, by rfl⟩ : syracuseStep 8579783 = 12869675) B12869675
theorem B2354203 : Blo 1505449 2354203 := bstep (se 1 (by rfl) ⟨1765652, by rfl⟩ : syracuseStep 2354203 = 3531305) B3531305
theorem B6188123 : Blo 1505449 6188123 := bstep (se 1 (by rfl) ⟨4641092, by rfl⟩ : syracuseStep 6188123 = 9282185) B9282185
theorem B6106319 : Blo 1505449 6106319 := bstep (se 1 (by rfl) ⟨4579739, by rfl⟩ : syracuseStep 6106319 = 9159479) B9159479
theorem B2542799 : Blo 1505449 2542799 := bstep (se 1 (by rfl) ⟨1907099, by rfl⟩ : syracuseStep 2542799 = 3814199) B3814199
theorem B8581423 : Blo 1505449 8581423 := bstep (se 1 (by rfl) ⟨6436067, by rfl⟩ : syracuseStep 8581423 = 12872135) B12872135
theorem B83546653 : Blo 1505449 83546653 := bstep (se 3 (by rfl) ⟨15664997, by rfl⟩ : syracuseStep 83546653 = 31329995) B31329995
theorem B18567863 : Blo 1505449 18567863 := bstep (se 1 (by rfl) ⟨13925897, by rfl⟩ : syracuseStep 18567863 = 27851795) B27851795
theorem B5428127 : Blo 1505449 5428127 := bstep (se 1 (by rfl) ⟨4071095, by rfl⟩ : syracuseStep 5428127 = 8142191) B8142191
theorem B3388463 : Blo 1505449 3388463 := bstep (se 1 (by rfl) ⟨2541347, by rfl⟩ : syracuseStep 3388463 = 5082695) B5082695
theorem B2258255 : Blo 1505449 2258255 := bstep (se 1 (by rfl) ⟨1693691, by rfl⟩ : syracuseStep 2258255 = 3387383) B3387383
theorem B2258303 : Blo 1505449 2258303 := bstep (se 1 (by rfl) ⟨1693727, by rfl⟩ : syracuseStep 2258303 = 3387455) B3387455
theorem B33093035 : Blo 1505449 33093035 := bstep (se 1 (by rfl) ⟨24819776, by rfl⟩ : syracuseStep 33093035 = 49639553) B49639553
theorem B9164441 : Blo 1505449 9164441 := bstep (se 2 (by rfl) ⟨3436665, by rfl⟩ : syracuseStep 9164441 = 6873331) B6873331
theorem B7624367 : Blo 1505449 7624367 := bstep (se 1 (by rfl) ⟨5718275, by rfl⟩ : syracuseStep 7624367 = 11436551) B11436551
theorem B3389327 : Blo 1505449 3389327 := bstep (se 1 (by rfl) ⟨2541995, by rfl⟩ : syracuseStep 3389327 = 5083991) B5083991
theorem B5085071 : Blo 1505449 5085071 := bstep (se 1 (by rfl) ⟨3813803, by rfl⟩ : syracuseStep 5085071 = 7627607) B7627607
theorem B2258843 : Blo 1505449 2258843 := bstep (se 1 (by rfl) ⟨1694132, by rfl⟩ : syracuseStep 2258843 = 3388265) B3388265
theorem B10442891 : Blo 1505449 10442891 := bstep (se 1 (by rfl) ⟨7832168, by rfl⟩ : syracuseStep 10442891 = 15664337) B15664337
theorem B7625015 : Blo 1505449 7625015 := bstep (se 1 (by rfl) ⟨5718761, by rfl⟩ : syracuseStep 7625015 = 11437523) B11437523
theorem B1505903 : Blo 1505449 1505903 := bstep (se 1 (by rfl) ⟨1129427, by rfl⟩ : syracuseStep 1505903 = 2258855) B2258855
theorem B3054223 : Blo 1505449 3054223 := bstep (se 1 (by rfl) ⟨2290667, by rfl⟩ : syracuseStep 3054223 = 4581335) B4581335
theorem B2259623 : Blo 1505449 2259623 := bstep (se 1 (by rfl) ⟨1694717, by rfl⟩ : syracuseStep 2259623 = 3389435) B3389435
theorem B2259815 : Blo 1505449 2259815 := bstep (se 1 (by rfl) ⟨1694861, by rfl⟩ : syracuseStep 2259815 = 3389723) B3389723
theorem B2259839 : Blo 1505449 2259839 := bstep (se 1 (by rfl) ⟨1694879, by rfl⟩ : syracuseStep 2259839 = 3389759) B3389759
theorem B53623721 : Blo 1505449 53623721 := bstep (se 2 (by rfl) ⟨20108895, by rfl⟩ : syracuseStep 53623721 = 40217791) B40217791
theorem B5716925 : Blo 1505449 5716925 := bstep (se 3 (by rfl) ⟨1071923, by rfl⟩ : syracuseStep 5716925 = 2143847) B2143847
theorem B1506335 : Blo 1505449 1506335 := bstep (se 1 (by rfl) ⟨1129751, by rfl⟩ : syracuseStep 1506335 = 2259503) B2259503
theorem B1506471 : Blo 1505449 1506471 := bstep (se 1 (by rfl) ⟨1129853, by rfl⟩ : syracuseStep 1506471 = 2259707) B2259707
theorem B1506495 : Blo 1505449 1506495 := bstep (se 1 (by rfl) ⟨1129871, by rfl⟩ : syracuseStep 1506495 = 2259743) B2259743
theorem B2260175 : Blo 1505449 2260175 := bstep (se 1 (by rfl) ⟨1695131, by rfl⟩ : syracuseStep 2260175 = 3390263) B3390263
theorem B5717243 : Blo 1505449 5717243 := bstep (se 1 (by rfl) ⟨4287932, by rfl⟩ : syracuseStep 5717243 = 8575865) B8575865
theorem B2858303 : Blo 1505449 2858303 := bstep (se 1 (by rfl) ⟨2143727, by rfl⟩ : syracuseStep 2858303 = 4287455) B4287455
theorem B23191085 : Blo 1505449 23191085 := bstep (se 3 (by rfl) ⟨4348328, by rfl⟩ : syracuseStep 23191085 = 8696657) B8696657
theorem B11747267 : Blo 1505449 11747267 := bstep (se 1 (by rfl) ⟨8810450, by rfl⟩ : syracuseStep 11747267 = 17620901) B17620901
theorem B12378575 : Blo 1505449 12378575 := bstep (se 1 (by rfl) ⟨9283931, by rfl⟩ : syracuseStep 12378575 = 18567863) B18567863
theorem B111395537 : Blo 1505449 111395537 := bstep (se 2 (by rfl) ⟨41773326, by rfl⟩ : syracuseStep 111395537 = 83546653) B83546653
theorem B4072297 : Blo 1505449 4072297 := bstep (se 2 (by rfl) ⟨1527111, by rfl⟩ : syracuseStep 4072297 = 3054223) B3054223
theorem B22062023 : Blo 1505449 22062023 := bstep (se 1 (by rfl) ⟨16546517, by rfl⟩ : syracuseStep 22062023 = 33093035) B33093035
theorem B3138937 : Blo 1505449 3138937 := bstep (se 2 (by rfl) ⟨1177101, by rfl⟩ : syracuseStep 3138937 = 2354203) B2354203
theorem B15451823 : Blo 1505449 15451823 := bstep (se 1 (by rfl) ⟨11588867, by rfl⟩ : syracuseStep 15451823 = 23177735) B23177735
theorem B24438509 : Blo 1505449 24438509 := bstep (se 3 (by rfl) ⟨4582220, by rfl⟩ : syracuseStep 24438509 = 9164441) B9164441
theorem B5719855 : Blo 1505449 5719855 := bstep (se 1 (by rfl) ⟨4289891, by rfl⟩ : syracuseStep 5719855 = 8579783) B8579783
theorem B3811283 : Blo 1505449 3811283 := bstep (se 1 (by rfl) ⟨2858462, by rfl⟩ : syracuseStep 3811283 = 5716925) B5716925
theorem B3811495 : Blo 1505449 3811495 := bstep (se 1 (by rfl) ⟨2858621, by rfl⟩ : syracuseStep 3811495 = 5717243) B5717243
theorem B15460723 : Blo 1505449 15460723 := bstep (se 1 (by rfl) ⟨11595542, by rfl⟩ : syracuseStep 15460723 = 23191085) B23191085
theorem B111471299 : Blo 1505449 111471299 := bstep (se 1 (by rfl) ⟨83603474, by rfl⟩ : syracuseStep 111471299 = 167206949) B167206949
theorem B4582271 : Blo 1505449 4582271 := bstep (se 1 (by rfl) ⟨3436703, by rfl⟩ : syracuseStep 4582271 = 6873407) B6873407
theorem B27847709 : Blo 1505449 27847709 := bstep (se 3 (by rfl) ⟨5221445, by rfl⟩ : syracuseStep 27847709 = 10442891) B10442891
theorem B5082911 : Blo 1505449 5082911 := bstep (se 1 (by rfl) ⟨3812183, by rfl⟩ : syracuseStep 5082911 = 7624367) B7624367
theorem B6434599 : Blo 1505449 6434599 := bstep (se 1 (by rfl) ⟨4825949, by rfl⟩ : syracuseStep 6434599 = 9651899) B9651899
theorem B3387347 : Blo 1505449 3387347 := bstep (se 1 (by rfl) ⟨2540510, by rfl⟩ : syracuseStep 3387347 = 5081021) B5081021
theorem B3387419 : Blo 1505449 3387419 := bstep (se 1 (by rfl) ⟨2540564, by rfl⟩ : syracuseStep 3387419 = 5081129) B5081129
theorem B5083343 : Blo 1505449 5083343 := bstep (se 1 (by rfl) ⟨3812507, by rfl⟩ : syracuseStep 5083343 = 7625015) B7625015
theorem B4125415 : Blo 1505449 4125415 := bstep (se 1 (by rfl) ⟨3094061, by rfl⟩ : syracuseStep 4125415 = 6188123) B6188123
theorem B1905535 : Blo 1505449 1905535 := bstep (se 1 (by rfl) ⟨1429151, by rfl⟩ : syracuseStep 1905535 = 2858303) B2858303
theorem B3388553 : Blo 1505449 3388553 := bstep (se 2 (by rfl) ⟨1270707, by rfl⟩ : syracuseStep 3388553 = 2541415) B2541415
theorem B23189111 : Blo 1505449 23189111 := bstep (se 1 (by rfl) ⟨17391833, by rfl⟩ : syracuseStep 23189111 = 34783667) B34783667
theorem B11441897 : Blo 1505449 11441897 := bstep (se 2 (by rfl) ⟨4290711, by rfl⟩ : syracuseStep 11441897 = 8581423) B8581423
theorem B3618751 : Blo 1505449 3618751 := bstep (se 1 (by rfl) ⟨2714063, by rfl⟩ : syracuseStep 3618751 = 5428127) B5428127
theorem B1693723 : Blo 1505449 1693723 := bstep (se 1 (by rfl) ⟨1270292, by rfl⟩ : syracuseStep 1693723 = 2540585) B2540585
theorem B2258975 : Blo 1505449 2258975 := bstep (se 1 (by rfl) ⟨1694231, by rfl⟩ : syracuseStep 2258975 = 3388463) B3388463
theorem B1505503 : Blo 1505449 1505503 := bstep (se 1 (by rfl) ⟨1129127, by rfl⟩ : syracuseStep 1505503 = 2258255) B2258255
theorem B1505535 : Blo 1505449 1505535 := bstep (se 1 (by rfl) ⟨1129151, by rfl⟩ : syracuseStep 1505535 = 2258303) B2258303
theorem B2259551 : Blo 1505449 2259551 := bstep (se 1 (by rfl) ⟨1694663, by rfl⟩ : syracuseStep 2259551 = 3389327) B3389327
theorem B3390047 : Blo 1505449 3390047 := bstep (se 1 (by rfl) ⟨2542535, by rfl⟩ : syracuseStep 3390047 = 5085071) B5085071
theorem B1505895 : Blo 1505449 1505895 := bstep (se 1 (by rfl) ⟨1129421, by rfl⟩ : syracuseStep 1505895 = 2258843) B2258843
theorem B1694335 : Blo 1505449 1694335 := bstep (se 1 (by rfl) ⟨1270751, by rfl⟩ : syracuseStep 1694335 = 2541503) B2541503
theorem B6872147 : Blo 1505449 6872147 := bstep (se 1 (by rfl) ⟨5154110, by rfl⟩ : syracuseStep 6872147 = 10308221) B10308221
theorem B10050671 : Blo 1505449 10050671 := bstep (se 1 (by rfl) ⟨7538003, by rfl⟩ : syracuseStep 10050671 = 15076007) B15076007
theorem B1506415 : Blo 1505449 1506415 := bstep (se 1 (by rfl) ⟨1129811, by rfl⟩ : syracuseStep 1506415 = 2259623) B2259623
theorem B1506543 : Blo 1505449 1506543 := bstep (se 1 (by rfl) ⟨1129907, by rfl⟩ : syracuseStep 1506543 = 2259815) B2259815
theorem B1506559 : Blo 1505449 1506559 := bstep (se 1 (by rfl) ⟨1129919, by rfl⟩ : syracuseStep 1506559 = 2259839) B2259839
theorem B35749147 : Blo 1505449 35749147 := bstep (se 1 (by rfl) ⟨26811860, by rfl⟩ : syracuseStep 35749147 = 53623721) B53623721
theorem B4070879 : Blo 1505449 4070879 := bstep (se 1 (by rfl) ⟨3053159, by rfl⟩ : syracuseStep 4070879 = 6106319) B6106319
theorem B1506783 : Blo 1505449 1506783 := bstep (se 1 (by rfl) ⟨1130087, by rfl⟩ : syracuseStep 1506783 = 2260175) B2260175
theorem B1695199 : Blo 1505449 1695199 := bstep (se 1 (by rfl) ⟨1271399, by rfl⟩ : syracuseStep 1695199 = 2542799) B2542799
theorem B7831511 : Blo 1505449 7831511 := bstep (se 1 (by rfl) ⟨5873633, by rfl⟩ : syracuseStep 7831511 = 11747267) B11747267
theorem B15459407 : Blo 1505449 15459407 := bstep (se 1 (by rfl) ⟨11594555, by rfl⟩ : syracuseStep 15459407 = 23189111) B23189111
theorem B7627931 : Blo 1505449 7627931 := bstep (se 1 (by rfl) ⟨5720948, by rfl⟩ : syracuseStep 7627931 = 11441897) B11441897
theorem B2540713 : Blo 1505449 2540713 := bstep (se 2 (by rfl) ⟨952767, by rfl⟩ : syracuseStep 2540713 = 1905535) B1905535
theorem B2540855 : Blo 1505449 2540855 := bstep (se 1 (by rfl) ⟨1905641, by rfl⟩ : syracuseStep 2540855 = 3811283) B3811283
theorem B18565139 : Blo 1505449 18565139 := bstep (se 1 (by rfl) ⟨13923854, by rfl⟩ : syracuseStep 18565139 = 27847709) B27847709
theorem B4581431 : Blo 1505449 4581431 := bstep (se 1 (by rfl) ⟨3436073, by rfl⟩ : syracuseStep 4581431 = 6872147) B6872147
theorem B2713919 : Blo 1505449 2713919 := bstep (se 1 (by rfl) ⟨2035439, by rfl⟩ : syracuseStep 2713919 = 4070879) B4070879
theorem B8579465 : Blo 1505449 8579465 := bstep (se 2 (by rfl) ⟨3217299, by rfl⟩ : syracuseStep 8579465 = 6434599) B6434599
theorem B66963989 : Blo 1505449 66963989 := bstep (se 6 (by rfl) ⟨1569468, by rfl⟩ : syracuseStep 66963989 = 3138937) B3138937
theorem B5221007 : Blo 1505449 5221007 := bstep (se 1 (by rfl) ⟨3915755, by rfl⟩ : syracuseStep 5221007 = 7831511) B7831511
theorem B5081993 : Blo 1505449 5081993 := bstep (se 2 (by rfl) ⟨1905747, by rfl⟩ : syracuseStep 5081993 = 3811495) B3811495
theorem B8252383 : Blo 1505449 8252383 := bstep (se 1 (by rfl) ⟨6189287, by rfl⟩ : syracuseStep 8252383 = 12378575) B12378575
theorem B74263691 : Blo 1505449 74263691 := bstep (se 1 (by rfl) ⟨55697768, by rfl⟩ : syracuseStep 74263691 = 111395537) B111395537
theorem B20614297 : Blo 1505449 20614297 := bstep (se 2 (by rfl) ⟨7730361, by rfl⟩ : syracuseStep 20614297 = 15460723) B15460723
theorem B14708015 : Blo 1505449 14708015 := bstep (se 1 (by rfl) ⟨11031011, by rfl⟩ : syracuseStep 14708015 = 22062023) B22062023
theorem B5500553 : Blo 1505449 5500553 := bstep (se 2 (by rfl) ⟨2062707, by rfl⟩ : syracuseStep 5500553 = 4125415) B4125415
theorem B10301215 : Blo 1505449 10301215 := bstep (se 1 (by rfl) ⟨7725911, by rfl⟩ : syracuseStep 10301215 = 15451823) B15451823
theorem B47665529 : Blo 1505449 47665529 := bstep (se 2 (by rfl) ⟨17874573, by rfl⟩ : syracuseStep 47665529 = 35749147) B35749147
theorem B74314199 : Blo 1505449 74314199 := bstep (se 1 (by rfl) ⟨55735649, by rfl⟩ : syracuseStep 74314199 = 111471299) B111471299
theorem B3388607 : Blo 1505449 3388607 := bstep (se 1 (by rfl) ⟨2541455, by rfl⟩ : syracuseStep 3388607 = 5082911) B5082911
theorem B2258231 : Blo 1505449 2258231 := bstep (se 1 (by rfl) ⟨1693673, by rfl⟩ : syracuseStep 2258231 = 3387347) B3387347
theorem B2258279 : Blo 1505449 2258279 := bstep (se 1 (by rfl) ⟨1693709, by rfl⟩ : syracuseStep 2258279 = 3387419) B3387419
theorem B2258297 : Blo 1505449 2258297 := bstep (se 2 (by rfl) ⟨846861, by rfl⟩ : syracuseStep 2258297 = 1693723) B1693723
theorem B3388895 : Blo 1505449 3388895 := bstep (se 1 (by rfl) ⟨2541671, by rfl⟩ : syracuseStep 3388895 = 5083343) B5083343
theorem B2259035 : Blo 1505449 2259035 := bstep (se 1 (by rfl) ⟨1694276, by rfl⟩ : syracuseStep 2259035 = 3388553) B3388553
theorem B2259113 : Blo 1505449 2259113 := bstep (se 2 (by rfl) ⟨847167, by rfl⟩ : syracuseStep 2259113 = 1694335) B1694335
theorem B5429729 : Blo 1505449 5429729 := bstep (se 2 (by rfl) ⟨2036148, by rfl⟩ : syracuseStep 5429729 = 4072297) B4072297
theorem B16292339 : Blo 1505449 16292339 := bstep (se 1 (by rfl) ⟨12219254, by rfl⟩ : syracuseStep 16292339 = 24438509) B24438509
theorem B1505983 : Blo 1505449 1505983 := bstep (se 1 (by rfl) ⟨1129487, by rfl⟩ : syracuseStep 1505983 = 2258975) B2258975
theorem B1506367 : Blo 1505449 1506367 := bstep (se 1 (by rfl) ⟨1129775, by rfl⟩ : syracuseStep 1506367 = 2259551) B2259551
theorem B2260031 : Blo 1505449 2260031 := bstep (se 1 (by rfl) ⟨1695023, by rfl⟩ : syracuseStep 2260031 = 3390047) B3390047
theorem B3054847 : Blo 1505449 3054847 := bstep (se 1 (by rfl) ⟨2291135, by rfl⟩ : syracuseStep 3054847 = 4582271) B4582271
theorem B2260265 : Blo 1505449 2260265 := bstep (se 2 (by rfl) ⟨847599, by rfl⟩ : syracuseStep 2260265 = 1695199) B1695199
theorem B6700447 : Blo 1505449 6700447 := bstep (se 1 (by rfl) ⟨5025335, by rfl⟩ : syracuseStep 6700447 = 10050671) B10050671
theorem B7626473 : Blo 1505449 7626473 := bstep (se 2 (by rfl) ⟨2859927, by rfl⟩ : syracuseStep 7626473 = 5719855) B5719855
theorem B4825001 : Blo 1505449 4825001 := bstep (se 2 (by rfl) ⟨1809375, by rfl⟩ : syracuseStep 4825001 = 3618751) B3618751
theorem B31777019 : Blo 1505449 31777019 := bstep (se 1 (by rfl) ⟨23832764, by rfl⟩ : syracuseStep 31777019 = 47665529) B47665529
theorem B156885493 : Blo 1505449 156885493 := bstep (se 5 (by rfl) ⟨7354007, by rfl⟩ : syracuseStep 156885493 = 14708015) B14708015
theorem B10306271 : Blo 1505449 10306271 := bstep (se 1 (by rfl) ⟨7729703, by rfl⟩ : syracuseStep 10306271 = 15459407) B15459407
theorem B11003177 : Blo 1505449 11003177 := bstep (se 2 (by rfl) ⟨4126191, by rfl⟩ : syracuseStep 11003177 = 8252383) B8252383
theorem B27485729 : Blo 1505449 27485729 := bstep (se 2 (by rfl) ⟨10307148, by rfl⟩ : syracuseStep 27485729 = 20614297) B20614297
theorem B5719643 : Blo 1505449 5719643 := bstep (se 1 (by rfl) ⟨4289732, by rfl⟩ : syracuseStep 5719643 = 8579465) B8579465
theorem B4073129 : Blo 1505449 4073129 := bstep (se 2 (by rfl) ⟨1527423, by rfl⟩ : syracuseStep 4073129 = 3054847) B3054847
theorem B35735717 : Blo 1505449 35735717 := bstep (se 4 (by rfl) ⟨3350223, by rfl⟩ : syracuseStep 35735717 = 6700447) B6700447
theorem B49507037 : Blo 1505449 49507037 := bstep (se 3 (by rfl) ⟨9282569, by rfl⟩ : syracuseStep 49507037 = 18565139) B18565139
theorem B7237117 : Blo 1505449 7237117 := bstep (se 3 (by rfl) ⟨1356959, by rfl⟩ : syracuseStep 7237117 = 2713919) B2713919
theorem B3387617 : Blo 1505449 3387617 := bstep (se 2 (by rfl) ⟨1270356, by rfl⟩ : syracuseStep 3387617 = 2540713) B2540713
theorem B44642659 : Blo 1505449 44642659 := bstep (se 1 (by rfl) ⟨33481994, by rfl⟩ : syracuseStep 44642659 = 66963989) B66963989
theorem B14668141 : Blo 1505449 14668141 := bstep (se 3 (by rfl) ⟨2750276, by rfl⟩ : syracuseStep 14668141 = 5500553) B5500553
theorem B3387995 : Blo 1505449 3387995 := bstep (se 1 (by rfl) ⟨2540996, by rfl⟩ : syracuseStep 3387995 = 5081993) B5081993
theorem B49509127 : Blo 1505449 49509127 := bstep (se 1 (by rfl) ⟨37131845, by rfl⟩ : syracuseStep 49509127 = 74263691) B74263691
theorem B13734953 : Blo 1505449 13734953 := bstep (se 2 (by rfl) ⟨5150607, by rfl⟩ : syracuseStep 13734953 = 10301215) B10301215
theorem B5084315 : Blo 1505449 5084315 := bstep (se 1 (by rfl) ⟨3813236, by rfl⟩ : syracuseStep 5084315 = 7626473) B7626473
theorem B3216667 : Blo 1505449 3216667 := bstep (se 1 (by rfl) ⟨2412500, by rfl⟩ : syracuseStep 3216667 = 4825001) B4825001
theorem B49542799 : Blo 1505449 49542799 := bstep (se 1 (by rfl) ⟨37157099, by rfl⟩ : syracuseStep 49542799 = 74314199) B74314199
theorem B5085287 : Blo 1505449 5085287 := bstep (se 1 (by rfl) ⟨3813965, by rfl⟩ : syracuseStep 5085287 = 7627931) B7627931
theorem B2259071 : Blo 1505449 2259071 := bstep (se 1 (by rfl) ⟨1694303, by rfl⟩ : syracuseStep 2259071 = 3388607) B3388607
theorem B1505487 : Blo 1505449 1505487 := bstep (se 1 (by rfl) ⟨1129115, by rfl⟩ : syracuseStep 1505487 = 2258231) B2258231
theorem B1693903 : Blo 1505449 1693903 := bstep (se 1 (by rfl) ⟨1270427, by rfl⟩ : syracuseStep 1693903 = 2540855) B2540855
theorem B1505519 : Blo 1505449 1505519 := bstep (se 1 (by rfl) ⟨1129139, by rfl⟩ : syracuseStep 1505519 = 2258279) B2258279
theorem B1505531 : Blo 1505449 1505531 := bstep (se 1 (by rfl) ⟨1129148, by rfl⟩ : syracuseStep 1505531 = 2258297) B2258297
theorem B2259263 : Blo 1505449 2259263 := bstep (se 1 (by rfl) ⟨1694447, by rfl⟩ : syracuseStep 2259263 = 3388895) B3388895
theorem B3054287 : Blo 1505449 3054287 := bstep (se 1 (by rfl) ⟨2290715, by rfl⟩ : syracuseStep 3054287 = 4581431) B4581431
theorem B1506023 : Blo 1505449 1506023 := bstep (se 1 (by rfl) ⟨1129517, by rfl⟩ : syracuseStep 1506023 = 2259035) B2259035
theorem B1506075 : Blo 1505449 1506075 := bstep (se 1 (by rfl) ⟨1129556, by rfl⟩ : syracuseStep 1506075 = 2259113) B2259113
theorem B3619819 : Blo 1505449 3619819 := bstep (se 1 (by rfl) ⟨2714864, by rfl⟩ : syracuseStep 3619819 = 5429729) B5429729
theorem B10861559 : Blo 1505449 10861559 := bstep (se 1 (by rfl) ⟨8146169, by rfl⟩ : syracuseStep 10861559 = 16292339) B16292339
theorem B3480671 : Blo 1505449 3480671 := bstep (se 1 (by rfl) ⟨2610503, by rfl⟩ : syracuseStep 3480671 = 5221007) B5221007
theorem B1506687 : Blo 1505449 1506687 := bstep (se 1 (by rfl) ⟨1130015, by rfl⟩ : syracuseStep 1506687 = 2260031) B2260031
theorem B1506843 : Blo 1505449 1506843 := bstep (se 1 (by rfl) ⟨1130132, by rfl⟩ : syracuseStep 1506843 = 2260265) B2260265
theorem B21184679 : Blo 1505449 21184679 := bstep (se 1 (by rfl) ⟨15888509, by rfl⟩ : syracuseStep 21184679 = 31777019) B31777019
theorem B9281789 : Blo 1505449 9281789 := bstep (se 3 (by rfl) ⟨1740335, by rfl⟩ : syracuseStep 9281789 = 3480671) B3480671
theorem B59523545 : Blo 1505449 59523545 := bstep (se 2 (by rfl) ⟨22321329, by rfl⟩ : syracuseStep 59523545 = 44642659) B44642659
theorem B66012169 : Blo 1505449 66012169 := bstep (se 2 (by rfl) ⟨24754563, by rfl⟩ : syracuseStep 66012169 = 49509127) B49509127
theorem B4826425 : Blo 1505449 4826425 := bstep (se 2 (by rfl) ⟨1809909, by rfl⟩ : syracuseStep 4826425 = 3619819) B3619819
theorem B23823811 : Blo 1505449 23823811 := bstep (se 1 (by rfl) ⟨17867858, by rfl⟩ : syracuseStep 23823811 = 35735717) B35735717
theorem B8144765 : Blo 1505449 8144765 := bstep (se 3 (by rfl) ⟨1527143, by rfl⟩ : syracuseStep 8144765 = 3054287) B3054287
theorem B19557521 : Blo 1505449 19557521 := bstep (se 2 (by rfl) ⟨7334070, by rfl⟩ : syracuseStep 19557521 = 14668141) B14668141
theorem B7335451 : Blo 1505449 7335451 := bstep (se 1 (by rfl) ⟨5501588, by rfl⟩ : syracuseStep 7335451 = 11003177) B11003177
theorem B3813095 : Blo 1505449 3813095 := bstep (se 1 (by rfl) ⟨2859821, by rfl⟩ : syracuseStep 3813095 = 5719643) B5719643
theorem B2715419 : Blo 1505449 2715419 := bstep (se 1 (by rfl) ⟨2036564, by rfl⟩ : syracuseStep 2715419 = 4073129) B4073129
theorem B4288889 : Blo 1505449 4288889 := bstep (se 2 (by rfl) ⟨1608333, by rfl⟩ : syracuseStep 4288889 = 3216667) B3216667
theorem B66057065 : Blo 1505449 66057065 := bstep (se 2 (by rfl) ⟨24771399, by rfl⟩ : syracuseStep 66057065 = 49542799) B49542799
theorem B2258411 : Blo 1505449 2258411 := bstep (se 1 (by rfl) ⟨1693808, by rfl⟩ : syracuseStep 2258411 = 3387617) B3387617
theorem B2258537 : Blo 1505449 2258537 := bstep (se 2 (by rfl) ⟨846951, by rfl⟩ : syracuseStep 2258537 = 1693903) B1693903
theorem B2258663 : Blo 1505449 2258663 := bstep (se 1 (by rfl) ⟨1693997, by rfl⟩ : syracuseStep 2258663 = 3387995) B3387995
theorem B209180657 : Blo 1505449 209180657 := bstep (se 2 (by rfl) ⟨78442746, by rfl⟩ : syracuseStep 209180657 = 156885493) B156885493
theorem B9156635 : Blo 1505449 9156635 := bstep (se 1 (by rfl) ⟨6867476, by rfl⟩ : syracuseStep 9156635 = 13734953) B13734953
theorem B3389543 : Blo 1505449 3389543 := bstep (se 1 (by rfl) ⟨2542157, by rfl⟩ : syracuseStep 3389543 = 5084315) B5084315
theorem B18323819 : Blo 1505449 18323819 := bstep (se 1 (by rfl) ⟨13742864, by rfl⟩ : syracuseStep 18323819 = 27485729) B27485729
theorem B3390191 : Blo 1505449 3390191 := bstep (se 1 (by rfl) ⟨2542643, by rfl⟩ : syracuseStep 3390191 = 5085287) B5085287
theorem B1506047 : Blo 1505449 1506047 := bstep (se 1 (by rfl) ⟨1129535, by rfl⟩ : syracuseStep 1506047 = 2259071) B2259071
theorem B1506175 : Blo 1505449 1506175 := bstep (se 1 (by rfl) ⟨1129631, by rfl⟩ : syracuseStep 1506175 = 2259263) B2259263
theorem B33004691 : Blo 1505449 33004691 := bstep (se 1 (by rfl) ⟨24753518, by rfl⟩ : syracuseStep 33004691 = 49507037) B49507037
theorem B27483389 : Blo 1505449 27483389 := bstep (se 3 (by rfl) ⟨5153135, by rfl⟩ : syracuseStep 27483389 = 10306271) B10306271
theorem B9649489 : Blo 1505449 9649489 := bstep (se 2 (by rfl) ⟨3618558, by rfl⟩ : syracuseStep 9649489 = 7237117) B7237117
theorem B7241039 : Blo 1505449 7241039 := bstep (se 1 (by rfl) ⟨5430779, by rfl⟩ : syracuseStep 7241039 = 10861559) B10861559
theorem B14123119 : Blo 1505449 14123119 := bstep (se 1 (by rfl) ⟨10592339, by rfl⟩ : syracuseStep 14123119 = 21184679) B21184679
theorem B11437037 : Blo 1505449 11437037 := bstep (se 3 (by rfl) ⟨2144444, by rfl⟩ : syracuseStep 11437037 = 4288889) B4288889
theorem B158729453 : Blo 1505449 158729453 := bstep (se 3 (by rfl) ⟨29761772, by rfl⟩ : syracuseStep 158729453 = 59523545) B59523545
theorem B139453771 : Blo 1505449 139453771 := bstep (se 1 (by rfl) ⟨104590328, by rfl⟩ : syracuseStep 139453771 = 209180657) B209180657
theorem B88016225 : Blo 1505449 88016225 := bstep (se 2 (by rfl) ⟨33006084, by rfl⟩ : syracuseStep 88016225 = 66012169) B66012169
theorem B6104423 : Blo 1505449 6104423 := bstep (se 1 (by rfl) ⟨4578317, by rfl⟩ : syracuseStep 6104423 = 9156635) B9156635
theorem B12215879 : Blo 1505449 12215879 := bstep (se 1 (by rfl) ⟨9161909, by rfl⟩ : syracuseStep 12215879 = 18323819) B18323819
theorem B4827359 : Blo 1505449 4827359 := bstep (se 1 (by rfl) ⟨3620519, by rfl⟩ : syracuseStep 4827359 = 7241039) B7241039
theorem B2542063 : Blo 1505449 2542063 := bstep (se 1 (by rfl) ⟨1906547, by rfl⟩ : syracuseStep 2542063 = 3813095) B3813095
theorem B6187859 : Blo 1505449 6187859 := bstep (se 1 (by rfl) ⟨4640894, by rfl⟩ : syracuseStep 6187859 = 9281789) B9281789
theorem B6435233 : Blo 1505449 6435233 := bstep (se 2 (by rfl) ⟨2413212, by rfl⟩ : syracuseStep 6435233 = 4826425) B4826425
theorem B12865985 : Blo 1505449 12865985 := bstep (se 2 (by rfl) ⟨4824744, by rfl⟩ : syracuseStep 12865985 = 9649489) B9649489
theorem B31765081 : Blo 1505449 31765081 := bstep (se 2 (by rfl) ⟨11911905, by rfl⟩ : syracuseStep 31765081 = 23823811) B23823811
theorem B13038347 : Blo 1505449 13038347 := bstep (se 1 (by rfl) ⟨9778760, by rfl⟩ : syracuseStep 13038347 = 19557521) B19557521
theorem B18322259 : Blo 1505449 18322259 := bstep (se 1 (by rfl) ⟨13741694, by rfl⟩ : syracuseStep 18322259 = 27483389) B27483389
theorem B44038043 : Blo 1505449 44038043 := bstep (se 1 (by rfl) ⟨33028532, by rfl⟩ : syracuseStep 44038043 = 66057065) B66057065
theorem B1505607 : Blo 1505449 1505607 := bstep (se 1 (by rfl) ⟨1129205, by rfl⟩ : syracuseStep 1505607 = 2258411) B2258411
theorem B1505691 : Blo 1505449 1505691 := bstep (se 1 (by rfl) ⟨1129268, by rfl⟩ : syracuseStep 1505691 = 2258537) B2258537
theorem B1505775 : Blo 1505449 1505775 := bstep (se 1 (by rfl) ⟨1129331, by rfl⟩ : syracuseStep 1505775 = 2258663) B2258663
theorem B5429843 : Blo 1505449 5429843 := bstep (se 1 (by rfl) ⟨4072382, by rfl⟩ : syracuseStep 5429843 = 8144765) B8144765
theorem B2259695 : Blo 1505449 2259695 := bstep (se 1 (by rfl) ⟨1694771, by rfl⟩ : syracuseStep 2259695 = 3389543) B3389543
theorem B2260127 : Blo 1505449 2260127 := bstep (se 1 (by rfl) ⟨1695095, by rfl⟩ : syracuseStep 2260127 = 3390191) B3390191
theorem B9780601 : Blo 1505449 9780601 := bstep (se 2 (by rfl) ⟨3667725, by rfl⟩ : syracuseStep 9780601 = 7335451) B7335451
theorem B22003127 : Blo 1505449 22003127 := bstep (se 1 (by rfl) ⟨16502345, by rfl⟩ : syracuseStep 22003127 = 33004691) B33004691
theorem B1810279 : Blo 1505449 1810279 := bstep (se 1 (by rfl) ⟨1357709, by rfl⟩ : syracuseStep 1810279 = 2715419) B2715419
theorem B8577323 : Blo 1505449 8577323 := bstep (se 1 (by rfl) ⟨6432992, by rfl⟩ : syracuseStep 8577323 = 12865985) B12865985
theorem B8692231 : Blo 1505449 8692231 := bstep (se 1 (by rfl) ⟨6519173, by rfl⟩ : syracuseStep 8692231 = 13038347) B13038347
theorem B42353441 : Blo 1505449 42353441 := bstep (se 2 (by rfl) ⟨15882540, by rfl⟩ : syracuseStep 42353441 = 31765081) B31765081
theorem B8143919 : Blo 1505449 8143919 := bstep (se 1 (by rfl) ⟨6107939, by rfl⟩ : syracuseStep 8143919 = 12215879) B12215879
theorem B48859357 : Blo 1505449 48859357 := bstep (se 3 (by rfl) ⟨9161129, by rfl⟩ : syracuseStep 48859357 = 18322259) B18322259
theorem B105819635 : Blo 1505449 105819635 := bstep (se 1 (by rfl) ⟨79364726, by rfl⟩ : syracuseStep 105819635 = 158729453) B158729453
theorem B938839733 : Blo 1505449 938839733 := bstep (se 5 (by rfl) ⟨44008112, by rfl⟩ : syracuseStep 938839733 = 88016225) B88016225
theorem B185938361 : Blo 1505449 185938361 := bstep (se 2 (by rfl) ⟨69726885, by rfl⟩ : syracuseStep 185938361 = 139453771) B139453771
theorem B9654821 : Blo 1505449 9654821 := bstep (se 4 (by rfl) ⟨905139, by rfl⟩ : syracuseStep 9654821 = 1810279) B1810279
theorem B4125239 : Blo 1505449 4125239 := bstep (se 1 (by rfl) ⟨3093929, by rfl⟩ : syracuseStep 4125239 = 6187859) B6187859
theorem B14668751 : Blo 1505449 14668751 := bstep (se 1 (by rfl) ⟨11001563, by rfl⟩ : syracuseStep 14668751 = 22003127) B22003127
theorem B18830825 : Blo 1505449 18830825 := bstep (se 2 (by rfl) ⟨7061559, by rfl⟩ : syracuseStep 18830825 = 14123119) B14123119
theorem B4290155 : Blo 1505449 4290155 := bstep (se 1 (by rfl) ⟨3217616, by rfl⟩ : syracuseStep 4290155 = 6435233) B6435233
theorem B3389417 : Blo 1505449 3389417 := bstep (se 2 (by rfl) ⟨1271031, by rfl⟩ : syracuseStep 3389417 = 2542063) B2542063
theorem B7624691 : Blo 1505449 7624691 := bstep (se 1 (by rfl) ⟨5718518, by rfl⟩ : syracuseStep 7624691 = 11437037) B11437037
theorem B4069615 : Blo 1505449 4069615 := bstep (se 1 (by rfl) ⟨3052211, by rfl⟩ : syracuseStep 4069615 = 6104423) B6104423
theorem B29358695 : Blo 1505449 29358695 := bstep (se 1 (by rfl) ⟨22019021, by rfl⟩ : syracuseStep 29358695 = 44038043) B44038043
theorem B3218239 : Blo 1505449 3218239 := bstep (se 1 (by rfl) ⟨2413679, by rfl⟩ : syracuseStep 3218239 = 4827359) B4827359
theorem B3619895 : Blo 1505449 3619895 := bstep (se 1 (by rfl) ⟨2714921, by rfl⟩ : syracuseStep 3619895 = 5429843) B5429843
theorem B1506463 : Blo 1505449 1506463 := bstep (se 1 (by rfl) ⟨1129847, by rfl⟩ : syracuseStep 1506463 = 2259695) B2259695
theorem B13040801 : Blo 1505449 13040801 := bstep (se 2 (by rfl) ⟨4890300, by rfl⟩ : syracuseStep 13040801 = 9780601) B9780601
theorem B1506751 : Blo 1505449 1506751 := bstep (se 1 (by rfl) ⟨1130063, by rfl⟩ : syracuseStep 1506751 = 2260127) B2260127
theorem B5718215 : Blo 1505449 5718215 := bstep (se 1 (by rfl) ⟨4288661, by rfl⟩ : syracuseStep 5718215 = 8577323) B8577323
theorem B2860103 : Blo 1505449 2860103 := bstep (se 1 (by rfl) ⟨2145077, by rfl⟩ : syracuseStep 2860103 = 4290155) B4290155
theorem B803448533 : Blo 1505449 803448533 := bstep (se 7 (by rfl) ⟨9415412, by rfl⟩ : syracuseStep 803448533 = 18830825) B18830825
theorem B19572463 : Blo 1505449 19572463 := bstep (se 1 (by rfl) ⟨14679347, by rfl⟩ : syracuseStep 19572463 = 29358695) B29358695
theorem B8693867 : Blo 1505449 8693867 := bstep (se 1 (by rfl) ⟨6520400, by rfl⟩ : syracuseStep 8693867 = 13040801) B13040801
theorem B9653053 : Blo 1505449 9653053 := bstep (se 3 (by rfl) ⟨1809947, by rfl⟩ : syracuseStep 9653053 = 3619895) B3619895
theorem B65145809 : Blo 1505449 65145809 := bstep (se 2 (by rfl) ⟨24429678, by rfl⟩ : syracuseStep 65145809 = 48859357) B48859357
theorem B5426153 : Blo 1505449 5426153 := bstep (se 2 (by rfl) ⟨2034807, by rfl⟩ : syracuseStep 5426153 = 4069615) B4069615
theorem B282185693 : Blo 1505449 282185693 := bstep (se 3 (by rfl) ⟨52909817, by rfl⟩ : syracuseStep 282185693 = 105819635) B105819635
theorem B5083127 : Blo 1505449 5083127 := bstep (se 1 (by rfl) ⟨3812345, by rfl⟩ : syracuseStep 5083127 = 7624691) B7624691
theorem B123958907 : Blo 1505449 123958907 := bstep (se 1 (by rfl) ⟨92969180, by rfl⟩ : syracuseStep 123958907 = 185938361) B185938361
theorem B6436547 : Blo 1505449 6436547 := bstep (se 1 (by rfl) ⟨4827410, by rfl⟩ : syracuseStep 6436547 = 9654821) B9654821
theorem B2750159 : Blo 1505449 2750159 := bstep (se 1 (by rfl) ⟨2062619, by rfl⟩ : syracuseStep 2750159 = 4125239) B4125239
theorem B28235627 : Blo 1505449 28235627 := bstep (se 1 (by rfl) ⟨21176720, by rfl⟩ : syracuseStep 28235627 = 42353441) B42353441
theorem B9779167 : Blo 1505449 9779167 := bstep (se 1 (by rfl) ⟨7334375, by rfl⟩ : syracuseStep 9779167 = 14668751) B14668751
theorem B11589641 : Blo 1505449 11589641 := bstep (se 2 (by rfl) ⟨4346115, by rfl⟩ : syracuseStep 11589641 = 8692231) B8692231
theorem B5429279 : Blo 1505449 5429279 := bstep (se 1 (by rfl) ⟨4071959, by rfl⟩ : syracuseStep 5429279 = 8143919) B8143919
theorem B4290985 : Blo 1505449 4290985 := bstep (se 2 (by rfl) ⟨1609119, by rfl⟩ : syracuseStep 4290985 = 3218239) B3218239
theorem B2259611 : Blo 1505449 2259611 := bstep (se 1 (by rfl) ⟨1694708, by rfl⟩ : syracuseStep 2259611 = 3389417) B3389417
theorem B625893155 : Blo 1505449 625893155 := bstep (se 1 (by rfl) ⟨469419866, by rfl⟩ : syracuseStep 625893155 = 938839733) B938839733
theorem B12870737 : Blo 1505449 12870737 := bstep (se 2 (by rfl) ⟨4826526, by rfl⟩ : syracuseStep 12870737 = 9653053) B9653053
theorem B7726427 : Blo 1505449 7726427 := bstep (se 1 (by rfl) ⟨5794820, by rfl⟩ : syracuseStep 7726427 = 11589641) B11589641
theorem B417262103 : Blo 1505449 417262103 := bstep (se 1 (by rfl) ⟨312946577, by rfl⟩ : syracuseStep 417262103 = 625893155) B625893155
theorem B535632355 : Blo 1505449 535632355 := bstep (se 1 (by rfl) ⟨401724266, by rfl⟩ : syracuseStep 535632355 = 803448533) B803448533
theorem B188123795 : Blo 1505449 188123795 := bstep (se 1 (by rfl) ⟨141092846, by rfl⟩ : syracuseStep 188123795 = 282185693) B282185693
theorem B14478077 : Blo 1505449 14478077 := bstep (se 3 (by rfl) ⟨2714639, by rfl⟩ : syracuseStep 14478077 = 5429279) B5429279
theorem B3812143 : Blo 1505449 3812143 := bstep (se 1 (by rfl) ⟨2859107, by rfl⟩ : syracuseStep 3812143 = 5718215) B5718215
theorem B5721313 : Blo 1505449 5721313 := bstep (se 2 (by rfl) ⟨2145492, by rfl⟩ : syracuseStep 5721313 = 4290985) B4290985
theorem B5795911 : Blo 1505449 5795911 := bstep (se 1 (by rfl) ⟨4346933, by rfl⟩ : syracuseStep 5795911 = 8693867) B8693867
theorem B43430539 : Blo 1505449 43430539 := bstep (se 1 (by rfl) ⟨32572904, by rfl⟩ : syracuseStep 43430539 = 65145809) B65145809
theorem B3617435 : Blo 1505449 3617435 := bstep (se 1 (by rfl) ⟨2713076, by rfl⟩ : syracuseStep 3617435 = 5426153) B5426153
theorem B26096617 : Blo 1505449 26096617 := bstep (se 2 (by rfl) ⟨9786231, by rfl⟩ : syracuseStep 26096617 = 19572463) B19572463
theorem B13038889 : Blo 1505449 13038889 := bstep (se 2 (by rfl) ⟨4889583, by rfl⟩ : syracuseStep 13038889 = 9779167) B9779167
theorem B3388751 : Blo 1505449 3388751 := bstep (se 1 (by rfl) ⟨2541563, by rfl⟩ : syracuseStep 3388751 = 5083127) B5083127
theorem B1906735 : Blo 1505449 1906735 := bstep (se 1 (by rfl) ⟨1430051, by rfl⟩ : syracuseStep 1906735 = 2860103) B2860103
theorem B82639271 : Blo 1505449 82639271 := bstep (se 1 (by rfl) ⟨61979453, by rfl⟩ : syracuseStep 82639271 = 123958907) B123958907
theorem B4291031 : Blo 1505449 4291031 := bstep (se 1 (by rfl) ⟨3218273, by rfl⟩ : syracuseStep 4291031 = 6436547) B6436547
theorem B1833439 : Blo 1505449 1833439 := bstep (se 1 (by rfl) ⟨1375079, by rfl⟩ : syracuseStep 1833439 = 2750159) B2750159
theorem B18823751 : Blo 1505449 18823751 := bstep (se 1 (by rfl) ⟨14117813, by rfl⟩ : syracuseStep 18823751 = 28235627) B28235627
theorem B1506407 : Blo 1505449 1506407 := bstep (se 1 (by rfl) ⟨1129805, by rfl⟩ : syracuseStep 1506407 = 2259611) B2259611
theorem B55092847 : Blo 1505449 55092847 := bstep (se 1 (by rfl) ⟨41319635, by rfl⟩ : syracuseStep 55092847 = 82639271) B82639271
theorem B7628417 : Blo 1505449 7628417 := bstep (se 2 (by rfl) ⟨2860656, by rfl⟩ : syracuseStep 7628417 = 5721313) B5721313
theorem B2860687 : Blo 1505449 2860687 := bstep (se 1 (by rfl) ⟨2145515, by rfl⟩ : syracuseStep 2860687 = 4291031) B4291031
theorem B17385185 : Blo 1505449 17385185 := bstep (se 2 (by rfl) ⟨6519444, by rfl⟩ : syracuseStep 17385185 = 13038889) B13038889
theorem B9652051 : Blo 1505449 9652051 := bstep (se 1 (by rfl) ⟨7239038, by rfl⟩ : syracuseStep 9652051 = 14478077) B14478077
theorem B2542313 : Blo 1505449 2542313 := bstep (se 2 (by rfl) ⟨953367, by rfl⟩ : syracuseStep 2542313 = 1906735) B1906735
theorem B7727881 : Blo 1505449 7727881 := bstep (se 2 (by rfl) ⟨2897955, by rfl⟩ : syracuseStep 7727881 = 5795911) B5795911
theorem B2411623 : Blo 1505449 2411623 := bstep (se 1 (by rfl) ⟨1808717, by rfl⟩ : syracuseStep 2411623 = 3617435) B3617435
theorem B2444585 : Blo 1505449 2444585 := bstep (se 2 (by rfl) ⟨916719, by rfl⟩ : syracuseStep 2444585 = 1833439) B1833439
theorem B8580491 : Blo 1505449 8580491 := bstep (se 1 (by rfl) ⟨6435368, by rfl⟩ : syracuseStep 8580491 = 12870737) B12870737
theorem B5082857 : Blo 1505449 5082857 := bstep (se 2 (by rfl) ⟨1906071, by rfl⟩ : syracuseStep 5082857 = 3812143) B3812143
theorem B34795489 : Blo 1505449 34795489 := bstep (se 2 (by rfl) ⟨13048308, by rfl⟩ : syracuseStep 34795489 = 26096617) B26096617
theorem B125415863 : Blo 1505449 125415863 := bstep (se 1 (by rfl) ⟨94061897, by rfl⟩ : syracuseStep 125415863 = 188123795) B188123795
theorem B57907385 : Blo 1505449 57907385 := bstep (se 2 (by rfl) ⟨21715269, by rfl⟩ : syracuseStep 57907385 = 43430539) B43430539
theorem B2259167 : Blo 1505449 2259167 := bstep (se 1 (by rfl) ⟨1694375, by rfl⟩ : syracuseStep 2259167 = 3388751) B3388751
theorem B5150951 : Blo 1505449 5150951 := bstep (se 1 (by rfl) ⟨3863213, by rfl⟩ : syracuseStep 5150951 = 7726427) B7726427
theorem B278174735 : Blo 1505449 278174735 := bstep (se 1 (by rfl) ⟨208631051, by rfl⟩ : syracuseStep 278174735 = 417262103) B417262103
theorem B12549167 : Blo 1505449 12549167 := bstep (se 1 (by rfl) ⟨9411875, by rfl⟩ : syracuseStep 12549167 = 18823751) B18823751
theorem B2856705893 : Blo 1505449 2856705893 := bstep (se 4 (by rfl) ⟨267816177, by rfl⟩ : syracuseStep 2856705893 = 535632355) B535632355
theorem B12861989 : Blo 1505449 12861989 := bstep (se 4 (by rfl) ⟨1205811, by rfl⟩ : syracuseStep 12861989 = 2411623) B2411623
theorem B3433967 : Blo 1505449 3433967 := bstep (se 1 (by rfl) ⟨2575475, by rfl⟩ : syracuseStep 3433967 = 5150951) B5150951
theorem B8366111 : Blo 1505449 8366111 := bstep (se 1 (by rfl) ⟨6274583, by rfl⟩ : syracuseStep 8366111 = 12549167) B12549167
theorem B5720327 : Blo 1505449 5720327 := bstep (se 1 (by rfl) ⟨4290245, by rfl⟩ : syracuseStep 5720327 = 8580491) B8580491
theorem B1904470595 : Blo 1505449 1904470595 := bstep (se 1 (by rfl) ⟨1428352946, by rfl⟩ : syracuseStep 1904470595 = 2856705893) B2856705893
theorem B46393985 : Blo 1505449 46393985 := bstep (se 2 (by rfl) ⟨17397744, by rfl⟩ : syracuseStep 46393985 = 34795489) B34795489
theorem B83610575 : Blo 1505449 83610575 := bstep (se 1 (by rfl) ⟨62707931, by rfl⟩ : syracuseStep 83610575 = 125415863) B125415863
theorem B38604923 : Blo 1505449 38604923 := bstep (se 1 (by rfl) ⟨28953692, by rfl⟩ : syracuseStep 38604923 = 57907385) B57907385
theorem B3814249 : Blo 1505449 3814249 := bstep (se 2 (by rfl) ⟨1430343, by rfl⟩ : syracuseStep 3814249 = 2860687) B2860687
theorem B3388571 : Blo 1505449 3388571 := bstep (se 1 (by rfl) ⟨2541428, by rfl⟩ : syracuseStep 3388571 = 5082857) B5082857
theorem B6518893 : Blo 1505449 6518893 := bstep (se 3 (by rfl) ⟨1222292, by rfl⟩ : syracuseStep 6518893 = 2444585) B2444585
theorem B10303841 : Blo 1505449 10303841 := bstep (se 2 (by rfl) ⟨3863940, by rfl⟩ : syracuseStep 10303841 = 7727881) B7727881
theorem B5085611 : Blo 1505449 5085611 := bstep (se 1 (by rfl) ⟨3814208, by rfl⟩ : syracuseStep 5085611 = 7628417) B7628417
theorem B11590123 : Blo 1505449 11590123 := bstep (se 1 (by rfl) ⟨8692592, by rfl⟩ : syracuseStep 11590123 = 17385185) B17385185
theorem B1506111 : Blo 1505449 1506111 := bstep (se 1 (by rfl) ⟨1129583, by rfl⟩ : syracuseStep 1506111 = 2259167) B2259167
theorem B1694875 : Blo 1505449 1694875 := bstep (se 1 (by rfl) ⟨1271156, by rfl⟩ : syracuseStep 1694875 = 2542313) B2542313
theorem B185449823 : Blo 1505449 185449823 := bstep (se 1 (by rfl) ⟨139087367, by rfl⟩ : syracuseStep 185449823 = 278174735) B278174735
theorem B73457129 : Blo 1505449 73457129 := bstep (se 2 (by rfl) ⟨27546423, by rfl⟩ : syracuseStep 73457129 = 55092847) B55092847
theorem B12869401 : Blo 1505449 12869401 := bstep (se 2 (by rfl) ⟨4826025, by rfl⟩ : syracuseStep 12869401 = 9652051) B9652051
theorem B8691857 : Blo 1505449 8691857 := bstep (se 2 (by rfl) ⟨3259446, by rfl⟩ : syracuseStep 8691857 = 6518893) B6518893
theorem B123717293 : Blo 1505449 123717293 := bstep (se 3 (by rfl) ⟨23196992, by rfl⟩ : syracuseStep 123717293 = 46393985) B46393985
theorem B3134170837 : Blo 1505449 3134170837 := bstep (se 7 (by rfl) ⟨36728564, by rfl⟩ : syracuseStep 3134170837 = 73457129) B73457129
theorem B1269647063 : Blo 1505449 1269647063 := bstep (se 1 (by rfl) ⟨952235297, by rfl⟩ : syracuseStep 1269647063 = 1904470595) B1904470595
theorem B55740383 : Blo 1505449 55740383 := bstep (se 1 (by rfl) ⟨41805287, by rfl⟩ : syracuseStep 55740383 = 83610575) B83610575
theorem B15453497 : Blo 1505449 15453497 := bstep (se 2 (by rfl) ⟨5795061, by rfl⟩ : syracuseStep 15453497 = 11590123) B11590123
theorem B5085665 : Blo 1505449 5085665 := bstep (se 2 (by rfl) ⟨1907124, by rfl⟩ : syracuseStep 5085665 = 3814249) B3814249
theorem B2289311 : Blo 1505449 2289311 := bstep (se 1 (by rfl) ⟨1716983, by rfl⟩ : syracuseStep 2289311 = 3433967) B3433967
theorem B3813551 : Blo 1505449 3813551 := bstep (se 1 (by rfl) ⟨2860163, by rfl⟩ : syracuseStep 3813551 = 5720327) B5720327
theorem B6869227 : Blo 1505449 6869227 := bstep (se 1 (by rfl) ⟨5151920, by rfl⟩ : syracuseStep 6869227 = 10303841) B10303841
theorem B17159201 : Blo 1505449 17159201 := bstep (se 2 (by rfl) ⟨6434700, by rfl⟩ : syracuseStep 17159201 = 12869401) B12869401
theorem B25736615 : Blo 1505449 25736615 := bstep (se 1 (by rfl) ⟨19302461, by rfl⟩ : syracuseStep 25736615 = 38604923) B38604923
theorem B8574659 : Blo 1505449 8574659 := bstep (se 1 (by rfl) ⟨6430994, by rfl⟩ : syracuseStep 8574659 = 12861989) B12861989
theorem B2259047 : Blo 1505449 2259047 := bstep (se 1 (by rfl) ⟨1694285, by rfl⟩ : syracuseStep 2259047 = 3388571) B3388571
theorem B5577407 : Blo 1505449 5577407 := bstep (se 1 (by rfl) ⟨4183055, by rfl⟩ : syracuseStep 5577407 = 8366111) B8366111
theorem B2259833 : Blo 1505449 2259833 := bstep (se 2 (by rfl) ⟨847437, by rfl⟩ : syracuseStep 2259833 = 1694875) B1694875
theorem B3390407 : Blo 1505449 3390407 := bstep (se 1 (by rfl) ⟨2542805, by rfl⟩ : syracuseStep 3390407 = 5085611) B5085611
theorem B123633215 : Blo 1505449 123633215 := bstep (se 1 (by rfl) ⟨92724911, by rfl⟩ : syracuseStep 123633215 = 185449823) B185449823
theorem B9158969 : Blo 1505449 9158969 := bstep (se 2 (by rfl) ⟨3434613, by rfl⟩ : syracuseStep 9158969 = 6869227) B6869227
theorem B82478195 : Blo 1505449 82478195 := bstep (se 1 (by rfl) ⟨61858646, by rfl⟩ : syracuseStep 82478195 = 123717293) B123717293
theorem B846431375 : Blo 1505449 846431375 := bstep (se 1 (by rfl) ⟨634823531, by rfl⟩ : syracuseStep 846431375 = 1269647063) B1269647063
theorem B37160255 : Blo 1505449 37160255 := bstep (se 1 (by rfl) ⟨27870191, by rfl⟩ : syracuseStep 37160255 = 55740383) B55740383
theorem B82422143 : Blo 1505449 82422143 := bstep (se 1 (by rfl) ⟨61816607, by rfl⟩ : syracuseStep 82422143 = 123633215) B123633215
theorem B1526207 : Blo 1505449 1526207 := bstep (se 1 (by rfl) ⟨1144655, by rfl⟩ : syracuseStep 1526207 = 2289311) B2289311
theorem B5794571 : Blo 1505449 5794571 := bstep (se 1 (by rfl) ⟨4345928, by rfl⟩ : syracuseStep 5794571 = 8691857) B8691857
theorem B2542367 : Blo 1505449 2542367 := bstep (se 1 (by rfl) ⟨1906775, by rfl⟩ : syracuseStep 2542367 = 3813551) B3813551
theorem B11439467 : Blo 1505449 11439467 := bstep (se 1 (by rfl) ⟨8579600, by rfl⟩ : syracuseStep 11439467 = 17159201) B17159201
theorem B17157743 : Blo 1505449 17157743 := bstep (se 1 (by rfl) ⟨12868307, by rfl⟩ : syracuseStep 17157743 = 25736615) B25736615
theorem B10302331 : Blo 1505449 10302331 := bstep (se 1 (by rfl) ⟨7726748, by rfl⟩ : syracuseStep 10302331 = 15453497) B15453497
theorem B5716439 : Blo 1505449 5716439 := bstep (se 1 (by rfl) ⟨4287329, by rfl⟩ : syracuseStep 5716439 = 8574659) B8574659
theorem B1506031 : Blo 1505449 1506031 := bstep (se 1 (by rfl) ⟨1129523, by rfl⟩ : syracuseStep 1506031 = 2259047) B2259047
theorem B3390443 : Blo 1505449 3390443 := bstep (se 1 (by rfl) ⟨2542832, by rfl⟩ : syracuseStep 3390443 = 5085665) B5085665
theorem B3718271 : Blo 1505449 3718271 := bstep (se 1 (by rfl) ⟨2788703, by rfl⟩ : syracuseStep 3718271 = 5577407) B5577407
theorem B1506555 : Blo 1505449 1506555 := bstep (se 1 (by rfl) ⟨1129916, by rfl⟩ : syracuseStep 1506555 = 2259833) B2259833
theorem B2260271 : Blo 1505449 2260271 := bstep (se 1 (by rfl) ⟨1695203, by rfl⟩ : syracuseStep 2260271 = 3390407) B3390407
theorem B4178894449 : Blo 1505449 4178894449 := bstep (se 2 (by rfl) ⟨1567085418, by rfl⟩ : syracuseStep 4178894449 = 3134170837) B3134170837
theorem B2257150333 : Blo 1505449 2257150333 := bstep (se 3 (by rfl) ⟨423215687, by rfl⟩ : syracuseStep 2257150333 = 846431375) B846431375
theorem B54985463 : Blo 1505449 54985463 := bstep (se 1 (by rfl) ⟨41239097, by rfl⟩ : syracuseStep 54985463 = 82478195) B82478195
theorem B3810959 : Blo 1505449 3810959 := bstep (se 1 (by rfl) ⟨2858219, by rfl⟩ : syracuseStep 3810959 = 5716439) B5716439
theorem B11438495 : Blo 1505449 11438495 := bstep (se 1 (by rfl) ⟨8578871, by rfl⟩ : syracuseStep 11438495 = 17157743) B17157743
theorem B6105979 : Blo 1505449 6105979 := bstep (se 1 (by rfl) ⟨4579484, by rfl⟩ : syracuseStep 6105979 = 9158969) B9158969
theorem B9915389 : Blo 1505449 9915389 := bstep (se 3 (by rfl) ⟨1859135, by rfl⟩ : syracuseStep 9915389 = 3718271) B3718271
theorem B99094013 : Blo 1505449 99094013 := bstep (se 3 (by rfl) ⟨18580127, by rfl⟩ : syracuseStep 99094013 = 37160255) B37160255
theorem B54948095 : Blo 1505449 54948095 := bstep (se 1 (by rfl) ⟨41211071, by rfl⟩ : syracuseStep 54948095 = 82422143) B82422143
theorem B3863047 : Blo 1505449 3863047 := bstep (se 1 (by rfl) ⟨2897285, by rfl⟩ : syracuseStep 3863047 = 5794571) B5794571
theorem B5571859265 : Blo 1505449 5571859265 := bstep (se 2 (by rfl) ⟨2089447224, by rfl⟩ : syracuseStep 5571859265 = 4178894449) B4178894449
theorem B13736441 : Blo 1505449 13736441 := bstep (se 2 (by rfl) ⟨5151165, by rfl⟩ : syracuseStep 13736441 = 10302331) B10302331
theorem B4069885 : Blo 1505449 4069885 := bstep (se 3 (by rfl) ⟨763103, by rfl⟩ : syracuseStep 4069885 = 1526207) B1526207
theorem B1694911 : Blo 1505449 1694911 := bstep (se 1 (by rfl) ⟨1271183, by rfl⟩ : syracuseStep 1694911 = 2542367) B2542367
theorem B2260295 : Blo 1505449 2260295 := bstep (se 1 (by rfl) ⟨1695221, by rfl⟩ : syracuseStep 2260295 = 3390443) B3390443
theorem B1506847 : Blo 1505449 1506847 := bstep (se 1 (by rfl) ⟨1130135, by rfl⟩ : syracuseStep 1506847 = 2260271) B2260271
theorem B7626311 : Blo 1505449 7626311 := bstep (se 1 (by rfl) ⟨5719733, by rfl⟩ : syracuseStep 7626311 = 11439467) B11439467
theorem B3714572843 : Blo 1505449 3714572843 := bstep (se 1 (by rfl) ⟨2785929632, by rfl⟩ : syracuseStep 3714572843 = 5571859265) B5571859265
theorem B2540639 : Blo 1505449 2540639 := bstep (se 1 (by rfl) ⟨1905479, by rfl⟩ : syracuseStep 2540639 = 3810959) B3810959
theorem B66062675 : Blo 1505449 66062675 := bstep (se 1 (by rfl) ⟨49547006, by rfl⟩ : syracuseStep 66062675 = 99094013) B99094013
theorem B5426513 : Blo 1505449 5426513 := bstep (se 2 (by rfl) ⟨2034942, by rfl⟩ : syracuseStep 5426513 = 4069885) B4069885
theorem B5084207 : Blo 1505449 5084207 := bstep (se 1 (by rfl) ⟨3813155, by rfl⟩ : syracuseStep 5084207 = 7626311) B7626311
theorem B36632063 : Blo 1505449 36632063 := bstep (se 1 (by rfl) ⟨27474047, by rfl⟩ : syracuseStep 36632063 = 54948095) B54948095
theorem B36656975 : Blo 1505449 36656975 := bstep (se 1 (by rfl) ⟨27492731, by rfl⟩ : syracuseStep 36656975 = 54985463) B54985463
theorem B3009533777 : Blo 1505449 3009533777 := bstep (se 2 (by rfl) ⟨1128575166, by rfl⟩ : syracuseStep 3009533777 = 2257150333) B2257150333
theorem B5150729 : Blo 1505449 5150729 := bstep (se 2 (by rfl) ⟨1931523, by rfl⟩ : syracuseStep 5150729 = 3863047) B3863047
theorem B8141305 : Blo 1505449 8141305 := bstep (se 2 (by rfl) ⟨3052989, by rfl⟩ : syracuseStep 8141305 = 6105979) B6105979
theorem B2259881 : Blo 1505449 2259881 := bstep (se 2 (by rfl) ⟨847455, by rfl⟩ : syracuseStep 2259881 = 1694911) B1694911
theorem B7625663 : Blo 1505449 7625663 := bstep (se 1 (by rfl) ⟨5719247, by rfl⟩ : syracuseStep 7625663 = 11438495) B11438495
theorem B9157627 : Blo 1505449 9157627 := bstep (se 1 (by rfl) ⟨6868220, by rfl⟩ : syracuseStep 9157627 = 13736441) B13736441
theorem B6610259 : Blo 1505449 6610259 := bstep (se 1 (by rfl) ⟨4957694, by rfl⟩ : syracuseStep 6610259 = 9915389) B9915389
theorem B1506863 : Blo 1505449 1506863 := bstep (se 1 (by rfl) ⟨1130147, by rfl⟩ : syracuseStep 1506863 = 2260295) B2260295
theorem B10855073 : Blo 1505449 10855073 := bstep (se 2 (by rfl) ⟨4070652, by rfl⟩ : syracuseStep 10855073 = 8141305) B8141305
theorem B24421375 : Blo 1505449 24421375 := bstep (se 1 (by rfl) ⟨18316031, by rfl⟩ : syracuseStep 24421375 = 36632063) B36632063
theorem B24437983 : Blo 1505449 24437983 := bstep (se 1 (by rfl) ⟨18328487, by rfl⟩ : syracuseStep 24437983 = 36656975) B36656975
theorem B2006355851 : Blo 1505449 2006355851 := bstep (se 1 (by rfl) ⟨1504766888, by rfl⟩ : syracuseStep 2006355851 = 3009533777) B3009533777
theorem B5083775 : Blo 1505449 5083775 := bstep (se 1 (by rfl) ⟨3812831, by rfl⟩ : syracuseStep 5083775 = 7625663) B7625663
theorem B3617675 : Blo 1505449 3617675 := bstep (se 1 (by rfl) ⟨2713256, by rfl⟩ : syracuseStep 3617675 = 5426513) B5426513
theorem B13735277 : Blo 1505449 13735277 := bstep (se 3 (by rfl) ⟨2575364, by rfl⟩ : syracuseStep 13735277 = 5150729) B5150729
theorem B2476381895 : Blo 1505449 2476381895 := bstep (se 1 (by rfl) ⟨1857286421, by rfl⟩ : syracuseStep 2476381895 = 3714572843) B3714572843
theorem B3389471 : Blo 1505449 3389471 := bstep (se 1 (by rfl) ⟨2542103, by rfl⟩ : syracuseStep 3389471 = 5084207) B5084207
theorem B1693759 : Blo 1505449 1693759 := bstep (se 1 (by rfl) ⟨1270319, by rfl⟩ : syracuseStep 1693759 = 2540639) B2540639
theorem B17627357 : Blo 1505449 17627357 := bstep (se 3 (by rfl) ⟨3305129, by rfl⟩ : syracuseStep 17627357 = 6610259) B6610259
theorem B176167133 : Blo 1505449 176167133 := bstep (se 3 (by rfl) ⟨33031337, by rfl⟩ : syracuseStep 176167133 = 66062675) B66062675
theorem B1506587 : Blo 1505449 1506587 := bstep (se 1 (by rfl) ⟨1129940, by rfl⟩ : syracuseStep 1506587 = 2259881) B2259881
theorem B48840677 : Blo 1505449 48840677 := bstep (se 4 (by rfl) ⟨4578813, by rfl⟩ : syracuseStep 48840677 = 9157627) B9157627
theorem B7236715 : Blo 1505449 7236715 := bstep (se 1 (by rfl) ⟨5427536, by rfl⟩ : syracuseStep 7236715 = 10855073) B10855073
theorem B2411783 : Blo 1505449 2411783 := bstep (se 1 (by rfl) ⟨1808837, by rfl⟩ : syracuseStep 2411783 = 3617675) B3617675
theorem B1650921263 : Blo 1505449 1650921263 := bstep (se 1 (by rfl) ⟨1238190947, by rfl⟩ : syracuseStep 1650921263 = 2476381895) B2476381895
theorem B11751571 : Blo 1505449 11751571 := bstep (se 1 (by rfl) ⟨8813678, by rfl⟩ : syracuseStep 11751571 = 17627357) B17627357
theorem B117444755 : Blo 1505449 117444755 := bstep (se 1 (by rfl) ⟨88083566, by rfl⟩ : syracuseStep 117444755 = 176167133) B176167133
theorem B32583977 : Blo 1505449 32583977 := bstep (se 2 (by rfl) ⟨12218991, by rfl⟩ : syracuseStep 32583977 = 24437983) B24437983
theorem B1337570567 : Blo 1505449 1337570567 := bstep (se 1 (by rfl) ⟨1003177925, by rfl⟩ : syracuseStep 1337570567 = 2006355851) B2006355851
theorem B32560451 : Blo 1505449 32560451 := bstep (se 1 (by rfl) ⟨24420338, by rfl⟩ : syracuseStep 32560451 = 48840677) B48840677
theorem B2258345 : Blo 1505449 2258345 := bstep (se 2 (by rfl) ⟨846879, by rfl⟩ : syracuseStep 2258345 = 1693759) B1693759
theorem B3389183 : Blo 1505449 3389183 := bstep (se 1 (by rfl) ⟨2541887, by rfl⟩ : syracuseStep 3389183 = 5083775) B5083775
theorem B9156851 : Blo 1505449 9156851 := bstep (se 1 (by rfl) ⟨6867638, by rfl⟩ : syracuseStep 9156851 = 13735277) B13735277
theorem B32561833 : Blo 1505449 32561833 := bstep (se 2 (by rfl) ⟨12210687, by rfl⟩ : syracuseStep 32561833 = 24421375) B24421375
theorem B2259647 : Blo 1505449 2259647 := bstep (se 1 (by rfl) ⟨1694735, by rfl⟩ : syracuseStep 2259647 = 3389471) B3389471
theorem B6104567 : Blo 1505449 6104567 := bstep (se 1 (by rfl) ⟨4578425, by rfl⟩ : syracuseStep 6104567 = 9156851) B9156851
theorem B1607855 : Blo 1505449 1607855 := bstep (se 1 (by rfl) ⟨1205891, by rfl⟩ : syracuseStep 1607855 = 2411783) B2411783
theorem B1100614175 : Blo 1505449 1100614175 := bstep (se 1 (by rfl) ⟨825460631, by rfl⟩ : syracuseStep 1100614175 = 1650921263) B1650921263
theorem B78296503 : Blo 1505449 78296503 := bstep (se 1 (by rfl) ⟨58722377, by rfl⟩ : syracuseStep 78296503 = 117444755) B117444755
theorem B15668761 : Blo 1505449 15668761 := bstep (se 2 (by rfl) ⟨5875785, by rfl⟩ : syracuseStep 15668761 = 11751571) B11751571
theorem B21722651 : Blo 1505449 21722651 := bstep (se 1 (by rfl) ⟨16291988, by rfl⟩ : syracuseStep 21722651 = 32583977) B32583977
theorem B891713711 : Blo 1505449 891713711 := bstep (se 1 (by rfl) ⟨668785283, by rfl⟩ : syracuseStep 891713711 = 1337570567) B1337570567
theorem B21706967 : Blo 1505449 21706967 := bstep (se 1 (by rfl) ⟨16280225, by rfl⟩ : syracuseStep 21706967 = 32560451) B32560451
theorem B43415777 : Blo 1505449 43415777 := bstep (se 2 (by rfl) ⟨16280916, by rfl⟩ : syracuseStep 43415777 = 32561833) B32561833
theorem B1505563 : Blo 1505449 1505563 := bstep (se 1 (by rfl) ⟨1129172, by rfl⟩ : syracuseStep 1505563 = 2258345) B2258345
theorem B2259455 : Blo 1505449 2259455 := bstep (se 1 (by rfl) ⟨1694591, by rfl⟩ : syracuseStep 2259455 = 3389183) B3389183
theorem B9648953 : Blo 1505449 9648953 := bstep (se 2 (by rfl) ⟨3618357, by rfl⟩ : syracuseStep 9648953 = 7236715) B7236715
theorem B1506431 : Blo 1505449 1506431 := bstep (se 1 (by rfl) ⟨1129823, by rfl⟩ : syracuseStep 1506431 = 2259647) B2259647
theorem B28943851 : Blo 1505449 28943851 := bstep (se 1 (by rfl) ⟨21707888, by rfl⟩ : syracuseStep 28943851 = 43415777) B43415777
theorem B733742783 : Blo 1505449 733742783 := bstep (se 1 (by rfl) ⟨550307087, by rfl⟩ : syracuseStep 733742783 = 1100614175) B1100614175
theorem B6432635 : Blo 1505449 6432635 := bstep (se 1 (by rfl) ⟨4824476, by rfl⟩ : syracuseStep 6432635 = 9648953) B9648953
theorem B20891681 : Blo 1505449 20891681 := bstep (se 2 (by rfl) ⟨7834380, by rfl⟩ : syracuseStep 20891681 = 15668761) B15668761
theorem B14471311 : Blo 1505449 14471311 := bstep (se 1 (by rfl) ⟨10853483, by rfl⟩ : syracuseStep 14471311 = 21706967) B21706967
theorem B17150453 : Blo 1505449 17150453 := bstep (se 5 (by rfl) ⟨803927, by rfl⟩ : syracuseStep 17150453 = 1607855) B1607855
theorem B104395337 : Blo 1505449 104395337 := bstep (se 2 (by rfl) ⟨39148251, by rfl⟩ : syracuseStep 104395337 = 78296503) B78296503
theorem B4069711 : Blo 1505449 4069711 := bstep (se 1 (by rfl) ⟨3052283, by rfl⟩ : syracuseStep 4069711 = 6104567) B6104567
theorem B14481767 : Blo 1505449 14481767 := bstep (se 1 (by rfl) ⟨10861325, by rfl⟩ : syracuseStep 14481767 = 21722651) B21722651
theorem B594475807 : Blo 1505449 594475807 := bstep (se 1 (by rfl) ⟨445856855, by rfl⟩ : syracuseStep 594475807 = 891713711) B891713711
theorem B1506303 : Blo 1505449 1506303 := bstep (se 1 (by rfl) ⟨1129727, by rfl⟩ : syracuseStep 1506303 = 2259455) B2259455
theorem B38618045 : Blo 1505449 38618045 := bstep (se 3 (by rfl) ⟨7240883, by rfl⟩ : syracuseStep 38618045 = 14481767) B14481767
theorem B792634409 : Blo 1505449 792634409 := bstep (se 2 (by rfl) ⟨297237903, by rfl⟩ : syracuseStep 792634409 = 594475807) B594475807
theorem B489161855 : Blo 1505449 489161855 := bstep (se 1 (by rfl) ⟨366871391, by rfl⟩ : syracuseStep 489161855 = 733742783) B733742783
theorem B13927787 : Blo 1505449 13927787 := bstep (se 1 (by rfl) ⟨10445840, by rfl⟩ : syracuseStep 13927787 = 20891681) B20891681
theorem B19295081 : Blo 1505449 19295081 := bstep (se 2 (by rfl) ⟨7235655, by rfl⟩ : syracuseStep 19295081 = 14471311) B14471311
theorem B5426281 : Blo 1505449 5426281 := bstep (se 2 (by rfl) ⟨2034855, by rfl⟩ : syracuseStep 5426281 = 4069711) B4069711
theorem B4288423 : Blo 1505449 4288423 := bstep (se 1 (by rfl) ⟨3216317, by rfl⟩ : syracuseStep 4288423 = 6432635) B6432635
theorem B11433635 : Blo 1505449 11433635 := bstep (se 1 (by rfl) ⟨8575226, by rfl⟩ : syracuseStep 11433635 = 17150453) B17150453
theorem B69596891 : Blo 1505449 69596891 := bstep (se 1 (by rfl) ⟨52197668, by rfl⟩ : syracuseStep 69596891 = 104395337) B104395337
theorem B38591801 : Blo 1505449 38591801 := bstep (se 2 (by rfl) ⟨14471925, by rfl⟩ : syracuseStep 38591801 = 28943851) B28943851
theorem B46397927 : Blo 1505449 46397927 := bstep (se 1 (by rfl) ⟨34798445, by rfl⟩ : syracuseStep 46397927 = 69596891) B69596891
theorem B326107903 : Blo 1505449 326107903 := bstep (se 1 (by rfl) ⟨244580927, by rfl⟩ : syracuseStep 326107903 = 489161855) B489161855
theorem B7235041 : Blo 1505449 7235041 := bstep (se 2 (by rfl) ⟨2713140, by rfl⟩ : syracuseStep 7235041 = 5426281) B5426281
theorem B12863387 : Blo 1505449 12863387 := bstep (se 1 (by rfl) ⟨9647540, by rfl⟩ : syracuseStep 12863387 = 19295081) B19295081
theorem B9285191 : Blo 1505449 9285191 := bstep (se 1 (by rfl) ⟨6963893, by rfl⟩ : syracuseStep 9285191 = 13927787) B13927787
theorem B7622423 : Blo 1505449 7622423 := bstep (se 1 (by rfl) ⟨5716817, by rfl⟩ : syracuseStep 7622423 = 11433635) B11433635
theorem B25727867 : Blo 1505449 25727867 := bstep (se 1 (by rfl) ⟨19295900, by rfl⟩ : syracuseStep 25727867 = 38591801) B38591801
theorem B25745363 : Blo 1505449 25745363 := bstep (se 1 (by rfl) ⟨19309022, by rfl⟩ : syracuseStep 25745363 = 38618045) B38618045
theorem B528422939 : Blo 1505449 528422939 := bstep (se 1 (by rfl) ⟨396317204, by rfl⟩ : syracuseStep 528422939 = 792634409) B792634409
theorem B5717897 : Blo 1505449 5717897 := bstep (se 2 (by rfl) ⟨2144211, by rfl⟩ : syracuseStep 5717897 = 4288423) B4288423
theorem B17163575 : Blo 1505449 17163575 := bstep (se 1 (by rfl) ⟨12872681, by rfl⟩ : syracuseStep 17163575 = 25745363) B25745363
theorem B352281959 : Blo 1505449 352281959 := bstep (se 1 (by rfl) ⟨264211469, by rfl⟩ : syracuseStep 352281959 = 528422939) B528422939
theorem B5081615 : Blo 1505449 5081615 := bstep (se 1 (by rfl) ⟨3811211, by rfl⟩ : syracuseStep 5081615 = 7622423) B7622423
theorem B3811931 : Blo 1505449 3811931 := bstep (se 1 (by rfl) ⟨2858948, by rfl⟩ : syracuseStep 3811931 = 5717897) B5717897
theorem B434810537 : Blo 1505449 434810537 := bstep (se 2 (by rfl) ⟨163053951, by rfl⟩ : syracuseStep 434810537 = 326107903) B326107903
theorem B9646721 : Blo 1505449 9646721 := bstep (se 2 (by rfl) ⟨3617520, by rfl⟩ : syracuseStep 9646721 = 7235041) B7235041
theorem B6190127 : Blo 1505449 6190127 := bstep (se 1 (by rfl) ⟨4642595, by rfl⟩ : syracuseStep 6190127 = 9285191) B9285191
theorem B17151911 : Blo 1505449 17151911 := bstep (se 1 (by rfl) ⟨12863933, by rfl⟩ : syracuseStep 17151911 = 25727867) B25727867
theorem B8575591 : Blo 1505449 8575591 := bstep (se 1 (by rfl) ⟨6431693, by rfl⟩ : syracuseStep 8575591 = 12863387) B12863387
theorem B30931951 : Blo 1505449 30931951 := bstep (se 1 (by rfl) ⟨23198963, by rfl⟩ : syracuseStep 30931951 = 46397927) B46397927
theorem B6431147 : Blo 1505449 6431147 := bstep (se 1 (by rfl) ⟨4823360, by rfl⟩ : syracuseStep 6431147 = 9646721) B9646721
theorem B2541287 : Blo 1505449 2541287 := bstep (se 1 (by rfl) ⟨1905965, by rfl⟩ : syracuseStep 2541287 = 3811931) B3811931
theorem B41242601 : Blo 1505449 41242601 := bstep (se 2 (by rfl) ⟨15465975, by rfl⟩ : syracuseStep 41242601 = 30931951) B30931951
theorem B11442383 : Blo 1505449 11442383 := bstep (se 1 (by rfl) ⟨8581787, by rfl⟩ : syracuseStep 11442383 = 17163575) B17163575
theorem B3387743 : Blo 1505449 3387743 := bstep (se 1 (by rfl) ⟨2540807, by rfl⟩ : syracuseStep 3387743 = 5081615) B5081615
theorem B4126751 : Blo 1505449 4126751 := bstep (se 1 (by rfl) ⟨3095063, by rfl⟩ : syracuseStep 4126751 = 6190127) B6190127
theorem B11434121 : Blo 1505449 11434121 := bstep (se 2 (by rfl) ⟨4287795, by rfl⟩ : syracuseStep 11434121 = 8575591) B8575591
theorem B234854639 : Blo 1505449 234854639 := bstep (se 1 (by rfl) ⟨176140979, by rfl⟩ : syracuseStep 234854639 = 352281959) B352281959
theorem B11434607 : Blo 1505449 11434607 := bstep (se 1 (by rfl) ⟨8575955, by rfl⟩ : syracuseStep 11434607 = 17151911) B17151911
theorem B289873691 : Blo 1505449 289873691 := bstep (se 1 (by rfl) ⟨217405268, by rfl⟩ : syracuseStep 289873691 = 434810537) B434810537
theorem B7628255 : Blo 1505449 7628255 := bstep (se 1 (by rfl) ⟨5721191, by rfl⟩ : syracuseStep 7628255 = 11442383) B11442383
theorem B27495067 : Blo 1505449 27495067 := bstep (se 1 (by rfl) ⟨20621300, by rfl⟩ : syracuseStep 27495067 = 41242601) B41242601
theorem B4287431 : Blo 1505449 4287431 := bstep (se 1 (by rfl) ⟨3215573, by rfl⟩ : syracuseStep 4287431 = 6431147) B6431147
theorem B7622747 : Blo 1505449 7622747 := bstep (se 1 (by rfl) ⟨5717060, by rfl⟩ : syracuseStep 7622747 = 11434121) B11434121
theorem B156569759 : Blo 1505449 156569759 := bstep (se 1 (by rfl) ⟨117427319, by rfl⟩ : syracuseStep 156569759 = 234854639) B234854639
theorem B7623071 : Blo 1505449 7623071 := bstep (se 1 (by rfl) ⟨5717303, by rfl⟩ : syracuseStep 7623071 = 11434607) B11434607
theorem B2258495 : Blo 1505449 2258495 := bstep (se 1 (by rfl) ⟨1693871, by rfl⟩ : syracuseStep 2258495 = 3387743) B3387743
theorem B1694191 : Blo 1505449 1694191 := bstep (se 1 (by rfl) ⟨1270643, by rfl⟩ : syracuseStep 1694191 = 2541287) B2541287
theorem B2751167 : Blo 1505449 2751167 := bstep (se 1 (by rfl) ⟨2063375, by rfl⟩ : syracuseStep 2751167 = 4126751) B4126751
theorem B193249127 : Blo 1505449 193249127 := bstep (se 1 (by rfl) ⟨144936845, by rfl⟩ : syracuseStep 193249127 = 289873691) B289873691
theorem B36660089 : Blo 1505449 36660089 := bstep (se 2 (by rfl) ⟨13747533, by rfl⟩ : syracuseStep 36660089 = 27495067) B27495067
theorem B5081831 : Blo 1505449 5081831 := bstep (se 1 (by rfl) ⟨3811373, by rfl⟩ : syracuseStep 5081831 = 7622747) B7622747
theorem B5082047 : Blo 1505449 5082047 := bstep (se 1 (by rfl) ⟨3811535, by rfl⟩ : syracuseStep 5082047 = 7623071) B7623071
theorem B11433149 : Blo 1505449 11433149 := bstep (se 3 (by rfl) ⟨2143715, by rfl⟩ : syracuseStep 11433149 = 4287431) B4287431
theorem B128832751 : Blo 1505449 128832751 := bstep (se 1 (by rfl) ⟨96624563, by rfl⟩ : syracuseStep 128832751 = 193249127) B193249127
theorem B104379839 : Blo 1505449 104379839 := bstep (se 1 (by rfl) ⟨78284879, by rfl⟩ : syracuseStep 104379839 = 156569759) B156569759
theorem B2258921 : Blo 1505449 2258921 := bstep (se 2 (by rfl) ⟨847095, by rfl⟩ : syracuseStep 2258921 = 1694191) B1694191
theorem B5085503 : Blo 1505449 5085503 := bstep (se 1 (by rfl) ⟨3814127, by rfl⟩ : syracuseStep 5085503 = 7628255) B7628255
theorem B1505663 : Blo 1505449 1505663 := bstep (se 1 (by rfl) ⟨1129247, by rfl⟩ : syracuseStep 1505663 = 2258495) B2258495
theorem B1834111 : Blo 1505449 1834111 := bstep (se 1 (by rfl) ⟨1375583, by rfl⟩ : syracuseStep 1834111 = 2751167) B2751167
theorem B24440059 : Blo 1505449 24440059 := bstep (se 1 (by rfl) ⟨18330044, by rfl⟩ : syracuseStep 24440059 = 36660089) B36660089
theorem B7622099 : Blo 1505449 7622099 := bstep (se 1 (by rfl) ⟨5716574, by rfl⟩ : syracuseStep 7622099 = 11433149) B11433149
theorem B69586559 : Blo 1505449 69586559 := bstep (se 1 (by rfl) ⟨52189919, by rfl⟩ : syracuseStep 69586559 = 104379839) B104379839
theorem B687108005 : Blo 1505449 687108005 := bstep (se 4 (by rfl) ⟨64416375, by rfl⟩ : syracuseStep 687108005 = 128832751) B128832751
theorem B2445481 : Blo 1505449 2445481 := bstep (se 2 (by rfl) ⟨917055, by rfl⟩ : syracuseStep 2445481 = 1834111) B1834111
theorem B3387887 : Blo 1505449 3387887 := bstep (se 1 (by rfl) ⟨2540915, by rfl⟩ : syracuseStep 3387887 = 5081831) B5081831
theorem B3388031 : Blo 1505449 3388031 := bstep (se 1 (by rfl) ⟨2541023, by rfl⟩ : syracuseStep 3388031 = 5082047) B5082047
theorem B1505947 : Blo 1505449 1505947 := bstep (se 1 (by rfl) ⟨1129460, by rfl⟩ : syracuseStep 1505947 = 2258921) B2258921
theorem B3390335 : Blo 1505449 3390335 := bstep (se 1 (by rfl) ⟨2542751, by rfl⟩ : syracuseStep 3390335 = 5085503) B5085503
theorem B13042565 : Blo 1505449 13042565 := bstep (se 4 (by rfl) ⟨1222740, by rfl⟩ : syracuseStep 13042565 = 2445481) B2445481
theorem B5081399 : Blo 1505449 5081399 := bstep (se 1 (by rfl) ⟨3811049, by rfl⟩ : syracuseStep 5081399 = 7622099) B7622099
theorem B2258591 : Blo 1505449 2258591 := bstep (se 1 (by rfl) ⟨1693943, by rfl⟩ : syracuseStep 2258591 = 3387887) B3387887
theorem B2258687 : Blo 1505449 2258687 := bstep (se 1 (by rfl) ⟨1694015, by rfl⟩ : syracuseStep 2258687 = 3388031) B3388031
theorem B32586745 : Blo 1505449 32586745 := bstep (se 2 (by rfl) ⟨12220029, by rfl⟩ : syracuseStep 32586745 = 24440059) B24440059
theorem B2260223 : Blo 1505449 2260223 := bstep (se 1 (by rfl) ⟨1695167, by rfl⟩ : syracuseStep 2260223 = 3390335) B3390335
theorem B46391039 : Blo 1505449 46391039 := bstep (se 1 (by rfl) ⟨34793279, by rfl⟩ : syracuseStep 46391039 = 69586559) B69586559
theorem B458072003 : Blo 1505449 458072003 := bstep (se 1 (by rfl) ⟨343554002, by rfl⟩ : syracuseStep 458072003 = 687108005) B687108005
theorem B30927359 : Blo 1505449 30927359 := bstep (se 1 (by rfl) ⟨23195519, by rfl⟩ : syracuseStep 30927359 = 46391039) B46391039
theorem B8695043 : Blo 1505449 8695043 := bstep (se 1 (by rfl) ⟨6521282, by rfl⟩ : syracuseStep 8695043 = 13042565) B13042565
theorem B3387599 : Blo 1505449 3387599 := bstep (se 1 (by rfl) ⟨2540699, by rfl⟩ : syracuseStep 3387599 = 5081399) B5081399
theorem B1505727 : Blo 1505449 1505727 := bstep (se 1 (by rfl) ⟨1129295, by rfl⟩ : syracuseStep 1505727 = 2258591) B2258591
theorem B1505791 : Blo 1505449 1505791 := bstep (se 1 (by rfl) ⟨1129343, by rfl⟩ : syracuseStep 1505791 = 2258687) B2258687
theorem B43448993 : Blo 1505449 43448993 := bstep (se 2 (by rfl) ⟨16293372, by rfl⟩ : syracuseStep 43448993 = 32586745) B32586745
theorem B1506815 : Blo 1505449 1506815 := bstep (se 1 (by rfl) ⟨1130111, by rfl⟩ : syracuseStep 1506815 = 2260223) B2260223
theorem B305381335 : Blo 1505449 305381335 := bstep (se 1 (by rfl) ⟨229036001, by rfl⟩ : syracuseStep 305381335 = 458072003) B458072003
theorem B5796695 : Blo 1505449 5796695 := bstep (se 1 (by rfl) ⟨4347521, by rfl⟩ : syracuseStep 5796695 = 8695043) B8695043
theorem B2258399 : Blo 1505449 2258399 := bstep (se 1 (by rfl) ⟨1693799, by rfl⟩ : syracuseStep 2258399 = 3387599) B3387599
theorem B20618239 : Blo 1505449 20618239 := bstep (se 1 (by rfl) ⟨15463679, by rfl⟩ : syracuseStep 20618239 = 30927359) B30927359
theorem B28965995 : Blo 1505449 28965995 := bstep (se 1 (by rfl) ⟨21724496, by rfl⟩ : syracuseStep 28965995 = 43448993) B43448993
theorem B407175113 : Blo 1505449 407175113 := bstep (se 2 (by rfl) ⟨152690667, by rfl⟩ : syracuseStep 407175113 = 305381335) B305381335
theorem B19310663 : Blo 1505449 19310663 := bstep (se 1 (by rfl) ⟨14482997, by rfl⟩ : syracuseStep 19310663 = 28965995) B28965995
theorem B1505599 : Blo 1505449 1505599 := bstep (se 1 (by rfl) ⟨1129199, by rfl⟩ : syracuseStep 1505599 = 2258399) B2258399
theorem B27490985 : Blo 1505449 27490985 := bstep (se 2 (by rfl) ⟨10309119, by rfl⟩ : syracuseStep 27490985 = 20618239) B20618239
theorem B15457853 : Blo 1505449 15457853 := bstep (se 3 (by rfl) ⟨2898347, by rfl⟩ : syracuseStep 15457853 = 5796695) B5796695
theorem B271450075 : Blo 1505449 271450075 := bstep (se 1 (by rfl) ⟨203587556, by rfl⟩ : syracuseStep 271450075 = 407175113) B407175113
theorem B18327323 : Blo 1505449 18327323 := bstep (se 1 (by rfl) ⟨13745492, by rfl⟩ : syracuseStep 18327323 = 27490985) B27490985
theorem B361933433 : Blo 1505449 361933433 := bstep (se 2 (by rfl) ⟨135725037, by rfl⟩ : syracuseStep 361933433 = 271450075) B271450075
theorem B12873775 : Blo 1505449 12873775 := bstep (se 1 (by rfl) ⟨9655331, by rfl⟩ : syracuseStep 12873775 = 19310663) B19310663
theorem B10305235 : Blo 1505449 10305235 := bstep (se 1 (by rfl) ⟨7728926, by rfl⟩ : syracuseStep 10305235 = 15457853) B15457853
theorem B241288955 : Blo 1505449 241288955 := bstep (se 1 (by rfl) ⟨180966716, by rfl⟩ : syracuseStep 241288955 = 361933433) B361933433
theorem B13740313 : Blo 1505449 13740313 := bstep (se 2 (by rfl) ⟨5152617, by rfl⟩ : syracuseStep 13740313 = 10305235) B10305235
theorem B17165033 : Blo 1505449 17165033 := bstep (se 2 (by rfl) ⟨6436887, by rfl⟩ : syracuseStep 17165033 = 12873775) B12873775
theorem B12218215 : Blo 1505449 12218215 := bstep (se 1 (by rfl) ⟨9163661, by rfl⟩ : syracuseStep 12218215 = 18327323) B18327323
theorem B160859303 : Blo 1505449 160859303 := bstep (se 1 (by rfl) ⟨120644477, by rfl⟩ : syracuseStep 160859303 = 241288955) B241288955
theorem B18320417 : Blo 1505449 18320417 := bstep (se 2 (by rfl) ⟨6870156, by rfl⟩ : syracuseStep 18320417 = 13740313) B13740313
theorem B16290953 : Blo 1505449 16290953 := bstep (se 2 (by rfl) ⟨6109107, by rfl⟩ : syracuseStep 16290953 = 12218215) B12218215
theorem B11443355 : Blo 1505449 11443355 := bstep (se 1 (by rfl) ⟨8582516, by rfl⟩ : syracuseStep 11443355 = 17165033) B17165033
theorem B7628903 : Blo 1505449 7628903 := bstep (se 1 (by rfl) ⟨5721677, by rfl⟩ : syracuseStep 7628903 = 11443355) B11443355
theorem B10860635 : Blo 1505449 10860635 := bstep (se 1 (by rfl) ⟨8145476, by rfl⟩ : syracuseStep 10860635 = 16290953) B16290953
theorem B107239535 : Blo 1505449 107239535 := bstep (se 1 (by rfl) ⟨80429651, by rfl⟩ : syracuseStep 107239535 = 160859303) B160859303
theorem B12213611 : Blo 1505449 12213611 := bstep (se 1 (by rfl) ⟨9160208, by rfl⟩ : syracuseStep 12213611 = 18320417) B18320417
theorem B71493023 : Blo 1505449 71493023 := bstep (se 1 (by rfl) ⟨53619767, by rfl⟩ : syracuseStep 71493023 = 107239535) B107239535
theorem B7240423 : Blo 1505449 7240423 := bstep (se 1 (by rfl) ⟨5430317, by rfl⟩ : syracuseStep 7240423 = 10860635) B10860635
theorem B5085935 : Blo 1505449 5085935 := bstep (se 1 (by rfl) ⟨3814451, by rfl⟩ : syracuseStep 5085935 = 7628903) B7628903
theorem B8142407 : Blo 1505449 8142407 := bstep (se 1 (by rfl) ⟨6106805, by rfl⟩ : syracuseStep 8142407 = 12213611) B12213611
theorem B47662015 : Blo 1505449 47662015 := bstep (se 1 (by rfl) ⟨35746511, by rfl⟩ : syracuseStep 47662015 = 71493023) B71493023
theorem B9653897 : Blo 1505449 9653897 := bstep (se 2 (by rfl) ⟨3620211, by rfl⟩ : syracuseStep 9653897 = 7240423) B7240423
theorem B5428271 : Blo 1505449 5428271 := bstep (se 1 (by rfl) ⟨4071203, by rfl⟩ : syracuseStep 5428271 = 8142407) B8142407
theorem B3390623 : Blo 1505449 3390623 := bstep (se 1 (by rfl) ⟨2542967, by rfl⟩ : syracuseStep 3390623 = 5085935) B5085935
theorem B63549353 : Blo 1505449 63549353 := bstep (se 2 (by rfl) ⟨23831007, by rfl⟩ : syracuseStep 63549353 = 47662015) B47662015
theorem B6435931 : Blo 1505449 6435931 := bstep (se 1 (by rfl) ⟨4826948, by rfl⟩ : syracuseStep 6435931 = 9653897) B9653897
theorem B3618847 : Blo 1505449 3618847 := bstep (se 1 (by rfl) ⟨2714135, by rfl⟩ : syracuseStep 3618847 = 5428271) B5428271
theorem B2260415 : Blo 1505449 2260415 := bstep (se 1 (by rfl) ⟨1695311, by rfl⟩ : syracuseStep 2260415 = 3390623) B3390623
theorem B19300517 : Blo 1505449 19300517 := bstep (se 4 (by rfl) ⟨1809423, by rfl⟩ : syracuseStep 19300517 = 3618847) B3618847
theorem B8581241 : Blo 1505449 8581241 := bstep (se 2 (by rfl) ⟨3217965, by rfl⟩ : syracuseStep 8581241 = 6435931) B6435931
theorem B42366235 : Blo 1505449 42366235 := bstep (se 1 (by rfl) ⟨31774676, by rfl⟩ : syracuseStep 42366235 = 63549353) B63549353
theorem B1506943 : Blo 1505449 1506943 := bstep (se 1 (by rfl) ⟨1130207, by rfl⟩ : syracuseStep 1506943 = 2260415) B2260415
theorem B5720827 : Blo 1505449 5720827 := bstep (se 1 (by rfl) ⟨4290620, by rfl⟩ : syracuseStep 5720827 = 8581241) B8581241
theorem B56488313 : Blo 1505449 56488313 := bstep (se 2 (by rfl) ⟨21183117, by rfl⟩ : syracuseStep 56488313 = 42366235) B42366235
theorem B12867011 : Blo 1505449 12867011 := bstep (se 1 (by rfl) ⟨9650258, by rfl⟩ : syracuseStep 12867011 = 19300517) B19300517
theorem B37658875 : Blo 1505449 37658875 := bstep (se 1 (by rfl) ⟨28244156, by rfl⟩ : syracuseStep 37658875 = 56488313) B56488313
theorem B8578007 : Blo 1505449 8578007 := bstep (se 1 (by rfl) ⟨6433505, by rfl⟩ : syracuseStep 8578007 = 12867011) B12867011
theorem B7627769 : Blo 1505449 7627769 := bstep (se 2 (by rfl) ⟨2860413, by rfl⟩ : syracuseStep 7627769 = 5720827) B5720827
theorem B5718671 : Blo 1505449 5718671 := bstep (se 1 (by rfl) ⟨4289003, by rfl⟩ : syracuseStep 5718671 = 8578007) B8578007
theorem B50211833 : Blo 1505449 50211833 := bstep (se 2 (by rfl) ⟨18829437, by rfl⟩ : syracuseStep 50211833 = 37658875) B37658875
theorem B5085179 : Blo 1505449 5085179 := bstep (se 1 (by rfl) ⟨3813884, by rfl⟩ : syracuseStep 5085179 = 7627769) B7627769
theorem B3812447 : Blo 1505449 3812447 := bstep (se 1 (by rfl) ⟨2859335, by rfl⟩ : syracuseStep 3812447 = 5718671) B5718671
theorem B3390119 : Blo 1505449 3390119 := bstep (se 1 (by rfl) ⟨2542589, by rfl⟩ : syracuseStep 3390119 = 5085179) B5085179
theorem B133898221 : Blo 1505449 133898221 := bstep (se 3 (by rfl) ⟨25105916, by rfl⟩ : syracuseStep 133898221 = 50211833) B50211833
theorem B2541631 : Blo 1505449 2541631 := bstep (se 1 (by rfl) ⟨1906223, by rfl⟩ : syracuseStep 2541631 = 3812447) B3812447
theorem B178530961 : Blo 1505449 178530961 := bstep (se 2 (by rfl) ⟨66949110, by rfl⟩ : syracuseStep 178530961 = 133898221) B133898221
theorem B2260079 : Blo 1505449 2260079 := bstep (se 1 (by rfl) ⟨1695059, by rfl⟩ : syracuseStep 2260079 = 3390119) B3390119
theorem B3388841 : Blo 1505449 3388841 := bstep (se 2 (by rfl) ⟨1270815, by rfl⟩ : syracuseStep 3388841 = 2541631) B2541631
theorem B238041281 : Blo 1505449 238041281 := bstep (se 2 (by rfl) ⟨89265480, by rfl⟩ : syracuseStep 238041281 = 178530961) B178530961
theorem B1506719 : Blo 1505449 1506719 := bstep (se 1 (by rfl) ⟨1130039, by rfl⟩ : syracuseStep 1506719 = 2260079) B2260079
theorem B2259227 : Blo 1505449 2259227 := bstep (se 1 (by rfl) ⟨1694420, by rfl⟩ : syracuseStep 2259227 = 3388841) B3388841
theorem B158694187 : Blo 1505449 158694187 := bstep (se 1 (by rfl) ⟨119020640, by rfl⟩ : syracuseStep 158694187 = 238041281) B238041281
theorem B211592249 : Blo 1505449 211592249 := bstep (se 2 (by rfl) ⟨79347093, by rfl⟩ : syracuseStep 211592249 = 158694187) B158694187
theorem B1506151 : Blo 1505449 1506151 := bstep (se 1 (by rfl) ⟨1129613, by rfl⟩ : syracuseStep 1506151 = 2259227) B2259227
theorem B141061499 : Blo 1505449 141061499 := bstep (se 1 (by rfl) ⟨105796124, by rfl⟩ : syracuseStep 141061499 = 211592249) B211592249
theorem B94040999 : Blo 1505449 94040999 := bstep (se 1 (by rfl) ⟨70530749, by rfl⟩ : syracuseStep 94040999 = 141061499) B141061499
theorem B62693999 : Blo 1505449 62693999 := bstep (se 1 (by rfl) ⟨47020499, by rfl⟩ : syracuseStep 62693999 = 94040999) B94040999
theorem B41795999 : Blo 1505449 41795999 := bstep (se 1 (by rfl) ⟨31346999, by rfl⟩ : syracuseStep 41795999 = 62693999) B62693999
theorem B27863999 : Blo 1505449 27863999 := bstep (se 1 (by rfl) ⟨20897999, by rfl⟩ : syracuseStep 27863999 = 41795999) B41795999
theorem B18575999 : Blo 1505449 18575999 := bstep (se 1 (by rfl) ⟨13931999, by rfl⟩ : syracuseStep 18575999 = 27863999) B27863999
theorem B12383999 : Blo 1505449 12383999 := bstep (se 1 (by rfl) ⟨9287999, by rfl⟩ : syracuseStep 12383999 = 18575999) B18575999
theorem B8255999 : Blo 1505449 8255999 := bstep (se 1 (by rfl) ⟨6191999, by rfl⟩ : syracuseStep 8255999 = 12383999) B12383999
theorem B5503999 : Blo 1505449 5503999 := bstep (se 1 (by rfl) ⟨4127999, by rfl⟩ : syracuseStep 5503999 = 8255999) B8255999
theorem B7338665 : Blo 1505449 7338665 := bstep (se 2 (by rfl) ⟨2751999, by rfl⟩ : syracuseStep 7338665 = 5503999) B5503999
theorem B4892443 : Blo 1505449 4892443 := bstep (se 1 (by rfl) ⟨3669332, by rfl⟩ : syracuseStep 4892443 = 7338665) B7338665
theorem B26093029 : Blo 1505449 26093029 := bstep (se 4 (by rfl) ⟨2446221, by rfl⟩ : syracuseStep 26093029 = 4892443) B4892443
theorem B34790705 : Blo 1505449 34790705 := bstep (se 2 (by rfl) ⟨13046514, by rfl⟩ : syracuseStep 34790705 = 26093029) B26093029
theorem B23193803 : Blo 1505449 23193803 := bstep (se 1 (by rfl) ⟨17395352, by rfl⟩ : syracuseStep 23193803 = 34790705) B34790705
theorem B15462535 : Blo 1505449 15462535 := bstep (se 1 (by rfl) ⟨11596901, by rfl⟩ : syracuseStep 15462535 = 23193803) B23193803
theorem B20616713 : Blo 1505449 20616713 := bstep (se 2 (by rfl) ⟨7731267, by rfl⟩ : syracuseStep 20616713 = 15462535) B15462535
theorem B13744475 : Blo 1505449 13744475 := bstep (se 1 (by rfl) ⟨10308356, by rfl⟩ : syracuseStep 13744475 = 20616713) B20616713
theorem B9162983 : Blo 1505449 9162983 := bstep (se 1 (by rfl) ⟨6872237, by rfl⟩ : syracuseStep 9162983 = 13744475) B13744475
theorem B24434621 : Blo 1505449 24434621 := bstep (se 3 (by rfl) ⟨4581491, by rfl⟩ : syracuseStep 24434621 = 9162983) B9162983
theorem B16289747 : Blo 1505449 16289747 := bstep (se 1 (by rfl) ⟨12217310, by rfl⟩ : syracuseStep 16289747 = 24434621) B24434621
theorem B10859831 : Blo 1505449 10859831 := bstep (se 1 (by rfl) ⟨8144873, by rfl⟩ : syracuseStep 10859831 = 16289747) B16289747
theorem B7239887 : Blo 1505449 7239887 := bstep (se 1 (by rfl) ⟨5429915, by rfl⟩ : syracuseStep 7239887 = 10859831) B10859831
theorem B4826591 : Blo 1505449 4826591 := bstep (se 1 (by rfl) ⟨3619943, by rfl⟩ : syracuseStep 4826591 = 7239887) B7239887
theorem B3217727 : Blo 1505449 3217727 := bstep (se 1 (by rfl) ⟨2413295, by rfl⟩ : syracuseStep 3217727 = 4826591) B4826591
theorem B2145151 : Blo 1505449 2145151 := bstep (se 1 (by rfl) ⟨1608863, by rfl⟩ : syracuseStep 2145151 = 3217727) B3217727
theorem B2860201 : Blo 1505449 2860201 := bstep (se 2 (by rfl) ⟨1072575, by rfl⟩ : syracuseStep 2860201 = 2145151) B2145151
theorem B3813601 : Blo 1505449 3813601 := bstep (se 2 (by rfl) ⟨1430100, by rfl⟩ : syracuseStep 3813601 = 2860201) B2860201
theorem B5084801 : Blo 1505449 5084801 := bstep (se 2 (by rfl) ⟨1906800, by rfl⟩ : syracuseStep 5084801 = 3813601) B3813601
theorem B3389867 : Blo 1505449 3389867 := bstep (se 1 (by rfl) ⟨2542400, by rfl⟩ : syracuseStep 3389867 = 5084801) B5084801
theorem B2259911 : Blo 1505449 2259911 := bstep (se 1 (by rfl) ⟨1694933, by rfl⟩ : syracuseStep 2259911 = 3389867) B3389867
theorem B1506607 : Blo 1505449 1506607 := bstep (se 1 (by rfl) ⟨1129955, by rfl⟩ : syracuseStep 1506607 = 2259911) B2259911

theorem C0 (j : ℕ) (h1 : 376362 ≤ j) (h2 : j ≤ 376736) : Blo 1505449 (4 * j + 3) := by
  interval_cases j
  · exact B1505451
  · exact B1505455
  · exact B1505459
  · exact B1505463
  · exact B1505467
  · exact B1505471
  · exact B1505475
  · exact B1505479
  · exact B1505483
  · exact B1505487
  · exact B1505491
  · exact B1505495
  · exact B1505499
  · exact B1505503
  · exact B1505507
  · exact B1505511
  · exact B1505515
  · exact B1505519
  · exact B1505523
  · exact B1505527
  · exact B1505531
  · exact B1505535
  · exact B1505539
  · exact B1505543
  · exact B1505547
  · exact B1505551
  · exact B1505555
  · exact B1505559
  · exact B1505563
  · exact B1505567
  · exact B1505571
  · exact B1505575
  · exact B1505579
  · exact B1505583
  · exact B1505587
  · exact B1505591
  · exact B1505595
  · exact B1505599
  · exact B1505603
  · exact B1505607
  · exact B1505611
  · exact B1505615
  · exact B1505619
  · exact B1505623
  · exact B1505627
  · exact B1505631
  · exact B1505635
  · exact B1505639
  · exact B1505643
  · exact B1505647
  · exact B1505651
  · exact B1505655
  · exact B1505659
  · exact B1505663
  · exact B1505667
  · exact B1505671
  · exact B1505675
  · exact B1505679
  · exact B1505683
  · exact B1505687
  · exact B1505691
  · exact B1505695
  · exact B1505699
  · exact B1505703
  · exact B1505707
  · exact B1505711
  · exact B1505715
  · exact B1505719
  · exact B1505723
  · exact B1505727
  · exact B1505731
  · exact B1505735
  · exact B1505739
  · exact B1505743
  · exact B1505747
  · exact B1505751
  · exact B1505755
  · exact B1505759
  · exact B1505763
  · exact B1505767
  · exact B1505771
  · exact B1505775
  · exact B1505779
  · exact B1505783
  · exact B1505787
  · exact B1505791
  · exact B1505795
  · exact B1505799
  · exact B1505803
  · exact B1505807
  · exact B1505811
  · exact B1505815
  · exact B1505819
  · exact B1505823
  · exact B1505827
  · exact B1505831
  · exact B1505835
  · exact B1505839
  · exact B1505843
  · exact B1505847
  · exact B1505851
  · exact B1505855
  · exact B1505859
  · exact B1505863
  · exact B1505867
  · exact B1505871
  · exact B1505875
  · exact B1505879
  · exact B1505883
  · exact B1505887
  · exact B1505891
  · exact B1505895
  · exact B1505899
  · exact B1505903
  · exact B1505907
  · exact B1505911
  · exact B1505915
  · exact B1505919
  · exact B1505923
  · exact B1505927
  · exact B1505931
  · exact B1505935
  · exact B1505939
  · exact B1505943
  · exact B1505947
  · exact B1505951
  · exact B1505955
  · exact B1505959
  · exact B1505963
  · exact B1505967
  · exact B1505971
  · exact B1505975
  · exact B1505979
  · exact B1505983
  · exact B1505987
  · exact B1505991
  · exact B1505995
  · exact B1505999
  · exact B1506003
  · exact B1506007
  · exact B1506011
  · exact B1506015
  · exact B1506019
  · exact B1506023
  · exact B1506027
  · exact B1506031
  · exact B1506035
  · exact B1506039
  · exact B1506043
  · exact B1506047
  · exact B1506051
  · exact B1506055
  · exact B1506059
  · exact B1506063
  · exact B1506067
  · exact B1506071
  · exact B1506075
  · exact B1506079
  · exact B1506083
  · exact B1506087
  · exact B1506091
  · exact B1506095
  · exact B1506099
  · exact B1506103
  · exact B1506107
  · exact B1506111
  · exact B1506115
  · exact B1506119
  · exact B1506123
  · exact B1506127
  · exact B1506131
  · exact B1506135
  · exact B1506139
  · exact B1506143
  · exact B1506147
  · exact B1506151
  · exact B1506155
  · exact B1506159
  · exact B1506163
  · exact B1506167
  · exact B1506171
  · exact B1506175
  · exact B1506179
  · exact B1506183
  · exact B1506187
  · exact B1506191
  · exact B1506195
  · exact B1506199
  · exact B1506203
  · exact B1506207
  · exact B1506211
  · exact B1506215
  · exact B1506219
  · exact B1506223
  · exact B1506227
  · exact B1506231
  · exact B1506235
  · exact B1506239
  · exact B1506243
  · exact B1506247
  · exact B1506251
  · exact B1506255
  · exact B1506259
  · exact B1506263
  · exact B1506267
  · exact B1506271
  · exact B1506275
  · exact B1506279
  · exact B1506283
  · exact B1506287
  · exact B1506291
  · exact B1506295
  · exact B1506299
  · exact B1506303
  · exact B1506307
  · exact B1506311
  · exact B1506315
  · exact B1506319
  · exact B1506323
  · exact B1506327
  · exact B1506331
  · exact B1506335
  · exact B1506339
  · exact B1506343
  · exact B1506347
  · exact B1506351
  · exact B1506355
  · exact B1506359
  · exact B1506363
  · exact B1506367
  · exact B1506371
  · exact B1506375
  · exact B1506379
  · exact B1506383
  · exact B1506387
  · exact B1506391
  · exact B1506395
  · exact B1506399
  · exact B1506403
  · exact B1506407
  · exact B1506411
  · exact B1506415
  · exact B1506419
  · exact B1506423
  · exact B1506427
  · exact B1506431
  · exact B1506435
  · exact B1506439
  · exact B1506443
  · exact B1506447
  · exact B1506451
  · exact B1506455
  · exact B1506459
  · exact B1506463
  · exact B1506467
  · exact B1506471
  · exact B1506475
  · exact B1506479
  · exact B1506483
  · exact B1506487
  · exact B1506491
  · exact B1506495
  · exact B1506499
  · exact B1506503
  · exact B1506507
  · exact B1506511
  · exact B1506515
  · exact B1506519
  · exact B1506523
  · exact B1506527
  · exact B1506531
  · exact B1506535
  · exact B1506539
  · exact B1506543
  · exact B1506547
  · exact B1506551
  · exact B1506555
  · exact B1506559
  · exact B1506563
  · exact B1506567
  · exact B1506571
  · exact B1506575
  · exact B1506579
  · exact B1506583
  · exact B1506587
  · exact B1506591
  · exact B1506595
  · exact B1506599
  · exact B1506603
  · exact B1506607
  · exact B1506611
  · exact B1506615
  · exact B1506619
  · exact B1506623
  · exact B1506627
  · exact B1506631
  · exact B1506635
  · exact B1506639
  · exact B1506643
  · exact B1506647
  · exact B1506651
  · exact B1506655
  · exact B1506659
  · exact B1506663
  · exact B1506667
  · exact B1506671
  · exact B1506675
  · exact B1506679
  · exact B1506683
  · exact B1506687
  · exact B1506691
  · exact B1506695
  · exact B1506699
  · exact B1506703
  · exact B1506707
  · exact B1506711
  · exact B1506715
  · exact B1506719
  · exact B1506723
  · exact B1506727
  · exact B1506731
  · exact B1506735
  · exact B1506739
  · exact B1506743
  · exact B1506747
  · exact B1506751
  · exact B1506755
  · exact B1506759
  · exact B1506763
  · exact B1506767
  · exact B1506771
  · exact B1506775
  · exact B1506779
  · exact B1506783
  · exact B1506787
  · exact B1506791
  · exact B1506795
  · exact B1506799
  · exact B1506803
  · exact B1506807
  · exact B1506811
  · exact B1506815
  · exact B1506819
  · exact B1506823
  · exact B1506827
  · exact B1506831
  · exact B1506835
  · exact B1506839
  · exact B1506843
  · exact B1506847
  · exact B1506851
  · exact B1506855
  · exact B1506859
  · exact B1506863
  · exact B1506867
  · exact B1506871
  · exact B1506875
  · exact B1506879
  · exact B1506883
  · exact B1506887
  · exact B1506891
  · exact B1506895
  · exact B1506899
  · exact B1506903
  · exact B1506907
  · exact B1506911
  · exact B1506915
  · exact B1506919
  · exact B1506923
  · exact B1506927
  · exact B1506931
  · exact B1506935
  · exact B1506939
  · exact B1506943
  · exact B1506947

theorem solution (m : ℕ) (hlo : 1505449 ≤ m) (hhi : m ≤ 1506949) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 376362 ≤ j := by omega
    have hj2 : j ≤ 376736 := by omega
    have hb : Blo 1505449 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
