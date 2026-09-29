-- Prove2me | solution 1 for syracuse_descends_range_892572_896572
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:47.12801+00:00
-- url     : https://prove2.me/submissions/5ec384dd-c657-4c97-a77d-077aa485e98a

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


theorem B1343501 : Blo 892572 1343501 := bbase (se 3 (by rfl) ⟨251906, by rfl⟩ : syracuseStep 1343501 = 503813) (by norm_num)
theorem B1507349 : Blo 892572 1507349 := bbase (se 6 (by rfl) ⟨35328, by rfl⟩ : syracuseStep 1507349 = 70657) (by norm_num)
theorem B1343525 : Blo 892572 1343525 := bbase (se 4 (by rfl) ⟨125955, by rfl⟩ : syracuseStep 1343525 = 251911) (by norm_num)
theorem B8257589 : Blo 892572 8257589 := bbase (se 5 (by rfl) ⟨387074, by rfl⟩ : syracuseStep 8257589 = 774149) (by norm_num)
theorem B1343549 : Blo 892572 1343549 := bbase (se 3 (by rfl) ⟨251915, by rfl⟩ : syracuseStep 1343549 = 503831) (by norm_num)
theorem B1343573 : Blo 892572 1343573 := bbase (se 8 (by rfl) ⟨7872, by rfl⟩ : syracuseStep 1343573 = 15745) (by norm_num)
theorem B1343597 : Blo 892572 1343597 := bbase (se 3 (by rfl) ⟨251924, by rfl⟩ : syracuseStep 1343597 = 503849) (by norm_num)
theorem B1343621 : Blo 892572 1343621 := bbase (se 4 (by rfl) ⟨125964, by rfl⟩ : syracuseStep 1343621 = 251929) (by norm_num)
theorem B1507477 : Blo 892572 1507477 := bbase (se 6 (by rfl) ⟨35331, by rfl⟩ : syracuseStep 1507477 = 70663) (by norm_num)
theorem B1343645 : Blo 892572 1343645 := bbase (se 3 (by rfl) ⟨251933, by rfl⟩ : syracuseStep 1343645 = 503867) (by norm_num)
theorem B1343669 : Blo 892572 1343669 := bbase (se 5 (by rfl) ⟨62984, by rfl⟩ : syracuseStep 1343669 = 125969) (by norm_num)
theorem B1343693 : Blo 892572 1343693 := bbase (se 3 (by rfl) ⟨251942, by rfl⟩ : syracuseStep 1343693 = 503885) (by norm_num)
theorem B1343717 : Blo 892572 1343717 := bbase (se 4 (by rfl) ⟨125973, by rfl⟩ : syracuseStep 1343717 = 251947) (by norm_num)
theorem B1507565 : Blo 892572 1507565 := bbase (se 3 (by rfl) ⟨282668, by rfl⟩ : syracuseStep 1507565 = 565337) (by norm_num)
theorem B4522229 : Blo 892572 4522229 := bbase (se 5 (by rfl) ⟨211979, by rfl⟩ : syracuseStep 4522229 = 423959) (by norm_num)
theorem B1343741 : Blo 892572 1343741 := bbase (se 3 (by rfl) ⟨251951, by rfl⟩ : syracuseStep 1343741 = 503903) (by norm_num)
theorem B1343765 : Blo 892572 1343765 := bbase (se 6 (by rfl) ⟨31494, by rfl⟩ : syracuseStep 1343765 = 62989) (by norm_num)
theorem B1343789 : Blo 892572 1343789 := bbase (se 3 (by rfl) ⟨251960, by rfl⟩ : syracuseStep 1343789 = 503921) (by norm_num)
theorem B3014981 : Blo 892572 3014981 := bbase (se 4 (by rfl) ⟨282654, by rfl⟩ : syracuseStep 3014981 = 565309) (by norm_num)
theorem B2261317 : Blo 892572 2261317 := bbase (se 4 (by rfl) ⟨211998, by rfl⟩ : syracuseStep 2261317 = 423997) (by norm_num)
theorem B1343813 : Blo 892572 1343813 := bbase (se 4 (by rfl) ⟨125982, by rfl⟩ : syracuseStep 1343813 = 251965) (by norm_num)
theorem B1343837 : Blo 892572 1343837 := bbase (se 3 (by rfl) ⟨251969, by rfl⟩ : syracuseStep 1343837 = 503939) (by norm_num)
theorem B1507693 : Blo 892572 1507693 := bbase (se 3 (by rfl) ⟨282692, by rfl⟩ : syracuseStep 1507693 = 565385) (by norm_num)
theorem B1343861 : Blo 892572 1343861 := bbase (se 5 (by rfl) ⟨62993, by rfl⟩ : syracuseStep 1343861 = 125987) (by norm_num)
theorem B1343885 : Blo 892572 1343885 := bbase (se 3 (by rfl) ⟨251978, by rfl⟩ : syracuseStep 1343885 = 503957) (by norm_num)
theorem B1343909 : Blo 892572 1343909 := bbase (se 4 (by rfl) ⟨125991, by rfl⟩ : syracuseStep 1343909 = 251983) (by norm_num)
theorem B2261429 : Blo 892572 2261429 := bbase (se 5 (by rfl) ⟨106004, by rfl⟩ : syracuseStep 2261429 = 212009) (by norm_num)
theorem B1343933 : Blo 892572 1343933 := bbase (se 3 (by rfl) ⟨251987, by rfl⟩ : syracuseStep 1343933 = 503975) (by norm_num)
theorem B1507781 : Blo 892572 1507781 := bbase (se 4 (by rfl) ⟨141354, by rfl⟩ : syracuseStep 1507781 = 282709) (by norm_num)
theorem B1343957 : Blo 892572 1343957 := bbase (se 7 (by rfl) ⟨15749, by rfl⟩ : syracuseStep 1343957 = 31499) (by norm_num)
theorem B1343981 : Blo 892572 1343981 := bbase (se 3 (by rfl) ⟨251996, by rfl⟩ : syracuseStep 1343981 = 503993) (by norm_num)
theorem B1344005 : Blo 892572 1344005 := bbase (se 4 (by rfl) ⟨126000, by rfl⟩ : syracuseStep 1344005 = 252001) (by norm_num)
theorem B1344029 : Blo 892572 1344029 := bbase (se 3 (by rfl) ⟨252005, by rfl⟩ : syracuseStep 1344029 = 504011) (by norm_num)
theorem B1344053 : Blo 892572 1344053 := bbase (se 5 (by rfl) ⟨63002, by rfl⟩ : syracuseStep 1344053 = 126005) (by norm_num)
theorem B1507909 : Blo 892572 1507909 := bbase (se 4 (by rfl) ⟨141366, by rfl⟩ : syracuseStep 1507909 = 282733) (by norm_num)
theorem B1344077 : Blo 892572 1344077 := bbase (se 3 (by rfl) ⟨252014, by rfl⟩ : syracuseStep 1344077 = 504029) (by norm_num)
theorem B1344101 : Blo 892572 1344101 := bbase (se 4 (by rfl) ⟨126009, by rfl⟩ : syracuseStep 1344101 = 252019) (by norm_num)
theorem B2261621 : Blo 892572 2261621 := bbase (se 5 (by rfl) ⟨106013, by rfl⟩ : syracuseStep 2261621 = 212027) (by norm_num)
theorem B1344125 : Blo 892572 1344125 := bbase (se 3 (by rfl) ⟨252023, by rfl⟩ : syracuseStep 1344125 = 504047) (by norm_num)
theorem B1344149 : Blo 892572 1344149 := bbase (se 6 (by rfl) ⟨31503, by rfl⟩ : syracuseStep 1344149 = 63007) (by norm_num)
theorem B1507997 : Blo 892572 1507997 := bbase (se 3 (by rfl) ⟨282749, by rfl⟩ : syracuseStep 1507997 = 565499) (by norm_num)
theorem B1344173 : Blo 892572 1344173 := bbase (se 3 (by rfl) ⟨252032, by rfl⟩ : syracuseStep 1344173 = 504065) (by norm_num)
theorem B1344197 : Blo 892572 1344197 := bbase (se 4 (by rfl) ⟨126018, by rfl⟩ : syracuseStep 1344197 = 252037) (by norm_num)
theorem B1344221 : Blo 892572 1344221 := bbase (se 3 (by rfl) ⟨252041, by rfl⟩ : syracuseStep 1344221 = 504083) (by norm_num)
theorem B3015413 : Blo 892572 3015413 := bbase (se 5 (by rfl) ⟨141347, by rfl⟩ : syracuseStep 3015413 = 282695) (by norm_num)
theorem B1344245 : Blo 892572 1344245 := bbase (se 5 (by rfl) ⟨63011, by rfl⟩ : syracuseStep 1344245 = 126023) (by norm_num)
theorem B1344269 : Blo 892572 1344269 := bbase (se 3 (by rfl) ⟨252050, by rfl⟩ : syracuseStep 1344269 = 504101) (by norm_num)
theorem B1508125 : Blo 892572 1508125 := bbase (se 3 (by rfl) ⟨282773, by rfl⟩ : syracuseStep 1508125 = 565547) (by norm_num)
theorem B1344293 : Blo 892572 1344293 := bbase (se 4 (by rfl) ⟨126027, by rfl⟩ : syracuseStep 1344293 = 252055) (by norm_num)
theorem B1344317 : Blo 892572 1344317 := bbase (se 3 (by rfl) ⟨252059, by rfl⟩ : syracuseStep 1344317 = 504119) (by norm_num)
theorem B1344341 : Blo 892572 1344341 := bbase (se 9 (by rfl) ⟨3938, by rfl⟩ : syracuseStep 1344341 = 7877) (by norm_num)
theorem B1344365 : Blo 892572 1344365 := bbase (se 3 (by rfl) ⟨252068, by rfl⟩ : syracuseStep 1344365 = 504137) (by norm_num)
theorem B1508213 : Blo 892572 1508213 := bbase (se 5 (by rfl) ⟨70697, by rfl⟩ : syracuseStep 1508213 = 141395) (by norm_num)
theorem B1344389 : Blo 892572 1344389 := bbase (se 4 (by rfl) ⟨126036, by rfl⟩ : syracuseStep 1344389 = 252073) (by norm_num)
theorem B1344413 : Blo 892572 1344413 := bbase (se 3 (by rfl) ⟨252077, by rfl⟩ : syracuseStep 1344413 = 504155) (by norm_num)
theorem B1344437 : Blo 892572 1344437 := bbase (se 5 (by rfl) ⟨63020, by rfl⟩ : syracuseStep 1344437 = 126041) (by norm_num)
theorem B2261965 : Blo 892572 2261965 := bbase (se 3 (by rfl) ⟨424118, by rfl⟩ : syracuseStep 2261965 = 848237) (by norm_num)
theorem B1344461 : Blo 892572 1344461 := bbase (se 3 (by rfl) ⟨252086, by rfl⟩ : syracuseStep 1344461 = 504173) (by norm_num)
theorem B1344485 : Blo 892572 1344485 := bbase (se 4 (by rfl) ⟨126045, by rfl⟩ : syracuseStep 1344485 = 252091) (by norm_num)
theorem B1508341 : Blo 892572 1508341 := bbase (se 5 (by rfl) ⟨70703, by rfl⟩ : syracuseStep 1508341 = 141407) (by norm_num)
theorem B1344509 : Blo 892572 1344509 := bbase (se 3 (by rfl) ⟨252095, by rfl⟩ : syracuseStep 1344509 = 504191) (by norm_num)
theorem B1344533 : Blo 892572 1344533 := bbase (se 6 (by rfl) ⟨31512, by rfl⟩ : syracuseStep 1344533 = 63025) (by norm_num)
theorem B1344557 : Blo 892572 1344557 := bbase (se 3 (by rfl) ⟨252104, by rfl⟩ : syracuseStep 1344557 = 504209) (by norm_num)
theorem B2262077 : Blo 892572 2262077 := bbase (se 3 (by rfl) ⟨424139, by rfl⟩ : syracuseStep 2262077 = 848279) (by norm_num)
theorem B1344581 : Blo 892572 1344581 := bbase (se 4 (by rfl) ⟨126054, by rfl⟩ : syracuseStep 1344581 = 252109) (by norm_num)
theorem B1508429 : Blo 892572 1508429 := bbase (se 3 (by rfl) ⟨282830, by rfl⟩ : syracuseStep 1508429 = 565661) (by norm_num)
theorem B1344605 : Blo 892572 1344605 := bbase (se 3 (by rfl) ⟨252113, by rfl⟩ : syracuseStep 1344605 = 504227) (by norm_num)
theorem B1344629 : Blo 892572 1344629 := bbase (se 5 (by rfl) ⟨63029, by rfl⟩ : syracuseStep 1344629 = 126059) (by norm_num)
theorem B1344653 : Blo 892572 1344653 := bbase (se 3 (by rfl) ⟨252122, by rfl⟩ : syracuseStep 1344653 = 504245) (by norm_num)
theorem B6456469 : Blo 892572 6456469 := bbase (se 6 (by rfl) ⟨151323, by rfl⟩ : syracuseStep 6456469 = 302647) (by norm_num)
theorem B3015845 : Blo 892572 3015845 := bbase (se 4 (by rfl) ⟨282735, by rfl⟩ : syracuseStep 3015845 = 565471) (by norm_num)
theorem B1344677 : Blo 892572 1344677 := bbase (se 4 (by rfl) ⟨126063, by rfl⟩ : syracuseStep 1344677 = 252127) (by norm_num)
theorem B1344701 : Blo 892572 1344701 := bbase (se 3 (by rfl) ⟨252131, by rfl⟩ : syracuseStep 1344701 = 504263) (by norm_num)
theorem B1508557 : Blo 892572 1508557 := bbase (se 3 (by rfl) ⟨282854, by rfl⟩ : syracuseStep 1508557 = 565709) (by norm_num)
theorem B1344725 : Blo 892572 1344725 := bbase (se 7 (by rfl) ⟨15758, by rfl⟩ : syracuseStep 1344725 = 31517) (by norm_num)
theorem B1344749 : Blo 892572 1344749 := bbase (se 3 (by rfl) ⟨252140, by rfl⟩ : syracuseStep 1344749 = 504281) (by norm_num)
theorem B4359413 : Blo 892572 4359413 := bbase (se 5 (by rfl) ⟨204347, by rfl⟩ : syracuseStep 4359413 = 408695) (by norm_num)
theorem B2262269 : Blo 892572 2262269 := bbase (se 3 (by rfl) ⟨424175, by rfl⟩ : syracuseStep 2262269 = 848351) (by norm_num)
theorem B1344773 : Blo 892572 1344773 := bbase (se 4 (by rfl) ⟨126072, by rfl⟩ : syracuseStep 1344773 = 252145) (by norm_num)
theorem B1344797 : Blo 892572 1344797 := bbase (se 3 (by rfl) ⟨252149, by rfl⟩ : syracuseStep 1344797 = 504299) (by norm_num)
theorem B1508645 : Blo 892572 1508645 := bbase (se 4 (by rfl) ⟨141435, by rfl⟩ : syracuseStep 1508645 = 282871) (by norm_num)
theorem B1344821 : Blo 892572 1344821 := bbase (se 5 (by rfl) ⟨63038, by rfl⟩ : syracuseStep 1344821 = 126077) (by norm_num)
theorem B1344845 : Blo 892572 1344845 := bbase (se 3 (by rfl) ⟨252158, by rfl⟩ : syracuseStep 1344845 = 504317) (by norm_num)
theorem B1508773 : Blo 892572 1508773 := bbase (se 4 (by rfl) ⟨141447, by rfl⟩ : syracuseStep 1508773 = 282895) (by norm_num)
theorem B1508861 : Blo 892572 1508861 := bbase (se 3 (by rfl) ⟨282911, by rfl⟩ : syracuseStep 1508861 = 565823) (by norm_num)
theorem B4523525 : Blo 892572 4523525 := bbase (se 4 (by rfl) ⟨424080, by rfl⟩ : syracuseStep 4523525 = 848161) (by norm_num)
theorem B3016277 : Blo 892572 3016277 := bbase (se 8 (by rfl) ⟨17673, by rfl⟩ : syracuseStep 3016277 = 35347) (by norm_num)
theorem B2262613 : Blo 892572 2262613 := bbase (se 8 (by rfl) ⟨13257, by rfl⟩ : syracuseStep 2262613 = 26515) (by norm_num)
theorem B1508989 : Blo 892572 1508989 := bbase (se 3 (by rfl) ⟨282935, by rfl⟩ : syracuseStep 1508989 = 565871) (by norm_num)
theorem B919169 : Blo 892572 919169 := bbase (se 2 (by rfl) ⟨344688, by rfl⟩ : syracuseStep 919169 = 689377) (by norm_num)
theorem B2262725 : Blo 892572 2262725 := bbase (se 4 (by rfl) ⟨212130, by rfl⟩ : syracuseStep 2262725 = 424261) (by norm_num)
theorem B1509077 : Blo 892572 1509077 := bbase (se 7 (by rfl) ⟨17684, by rfl⟩ : syracuseStep 1509077 = 35369) (by norm_num)
theorem B1509205 : Blo 892572 1509205 := bbase (se 9 (by rfl) ⟨4421, by rfl⟩ : syracuseStep 1509205 = 8843) (by norm_num)
theorem B2262917 : Blo 892572 2262917 := bbase (se 4 (by rfl) ⟨212148, by rfl⟩ : syracuseStep 2262917 = 424297) (by norm_num)
theorem B1509293 : Blo 892572 1509293 := bbase (se 3 (by rfl) ⟨282992, by rfl⟩ : syracuseStep 1509293 = 565985) (by norm_num)
theorem B21792725 : Blo 892572 21792725 := bbase (se 7 (by rfl) ⟨255383, by rfl⟩ : syracuseStep 21792725 = 510767) (by norm_num)
theorem B3016709 : Blo 892572 3016709 := bbase (se 4 (by rfl) ⟨282816, by rfl⟩ : syracuseStep 3016709 = 565633) (by norm_num)
theorem B6785045 : Blo 892572 6785045 := bbase (se 6 (by rfl) ⟨159024, by rfl⟩ : syracuseStep 6785045 = 318049) (by norm_num)
theorem B1509421 : Blo 892572 1509421 := bbase (se 3 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 1509421 = 566033) (by norm_num)
theorem B1935461 : Blo 892572 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B1509509 : Blo 892572 1509509 := bbase (se 4 (by rfl) ⟨141516, by rfl⟩ : syracuseStep 1509509 = 283033) (by norm_num)
theorem B919729 : Blo 892572 919729 := bbase (se 2 (by rfl) ⟨344898, by rfl⟩ : syracuseStep 919729 = 689797) (by norm_num)
theorem B2263261 : Blo 892572 2263261 := bbase (se 3 (by rfl) ⟨424361, by rfl⟩ : syracuseStep 2263261 = 848723) (by norm_num)
theorem B1509637 : Blo 892572 1509637 := bbase (se 4 (by rfl) ⟨141528, by rfl⟩ : syracuseStep 1509637 = 283057) (by norm_num)
theorem B2263373 : Blo 892572 2263373 := bbase (se 3 (by rfl) ⟨424382, by rfl⟩ : syracuseStep 2263373 = 848765) (by norm_num)
theorem B1509725 : Blo 892572 1509725 := bbase (se 3 (by rfl) ⟨283073, by rfl⟩ : syracuseStep 1509725 = 566147) (by norm_num)
theorem B3017141 : Blo 892572 3017141 := bbase (se 5 (by rfl) ⟨141428, by rfl⟩ : syracuseStep 3017141 = 282857) (by norm_num)
theorem B1509853 : Blo 892572 1509853 := bbase (se 3 (by rfl) ⟨283097, by rfl⟩ : syracuseStep 1509853 = 566195) (by norm_num)
theorem B2263565 : Blo 892572 2263565 := bbase (se 3 (by rfl) ⟨424418, by rfl⟩ : syracuseStep 2263565 = 848837) (by norm_num)
theorem B1935917 : Blo 892572 1935917 := bbase (se 3 (by rfl) ⟨362984, by rfl⟩ : syracuseStep 1935917 = 725969) (by norm_num)
theorem B1509941 : Blo 892572 1509941 := bbase (se 5 (by rfl) ⟨70778, by rfl⟩ : syracuseStep 1509941 = 141557) (by norm_num)
theorem B1149509 : Blo 892572 1149509 := bbase (se 4 (by rfl) ⟨107766, by rfl⟩ : syracuseStep 1149509 = 215533) (by norm_num)
theorem B1510069 : Blo 892572 1510069 := bbase (se 5 (by rfl) ⟨70784, by rfl⟩ : syracuseStep 1510069 = 141569) (by norm_num)
theorem B1510157 : Blo 892572 1510157 := bbase (se 3 (by rfl) ⟨283154, by rfl⟩ : syracuseStep 1510157 = 566309) (by norm_num)
theorem B4524821 : Blo 892572 4524821 := bbase (se 6 (by rfl) ⟨106050, by rfl⟩ : syracuseStep 4524821 = 212101) (by norm_num)
theorem B1018661 : Blo 892572 1018661 := bbase (se 4 (by rfl) ⟨95499, by rfl⟩ : syracuseStep 1018661 = 190999) (by norm_num)
theorem B1608509 : Blo 892572 1608509 := bbase (se 3 (by rfl) ⟨301595, by rfl⟩ : syracuseStep 1608509 = 603191) (by norm_num)
theorem B953165 : Blo 892572 953165 := bbase (se 3 (by rfl) ⟨178718, by rfl⟩ : syracuseStep 953165 = 357437) (by norm_num)
theorem B3017573 : Blo 892572 3017573 := bbase (se 4 (by rfl) ⟨282897, by rfl⟩ : syracuseStep 3017573 = 565795) (by norm_num)
theorem B2263909 : Blo 892572 2263909 := bbase (se 4 (by rfl) ⟨212241, by rfl⟩ : syracuseStep 2263909 = 424483) (by norm_num)
theorem B1510285 : Blo 892572 1510285 := bbase (se 3 (by rfl) ⟨283178, by rfl⟩ : syracuseStep 1510285 = 566357) (by norm_num)
theorem B8588213 : Blo 892572 8588213 := bbase (se 5 (by rfl) ⟨402572, by rfl⟩ : syracuseStep 8588213 = 805145) (by norm_num)
theorem B953293 : Blo 892572 953293 := bbase (se 3 (by rfl) ⟨178742, by rfl⟩ : syracuseStep 953293 = 357485) (by norm_num)
theorem B2264021 : Blo 892572 2264021 := bbase (se 7 (by rfl) ⟨26531, by rfl⟩ : syracuseStep 2264021 = 53063) (by norm_num)
theorem B1510373 : Blo 892572 1510373 := bbase (se 4 (by rfl) ⟨141597, by rfl⟩ : syracuseStep 1510373 = 283195) (by norm_num)
theorem B5737493 : Blo 892572 5737493 := bbase (se 6 (by rfl) ⟨134472, by rfl⟩ : syracuseStep 5737493 = 268945) (by norm_num)
theorem B1510501 : Blo 892572 1510501 := bbase (se 4 (by rfl) ⟨141609, by rfl⟩ : syracuseStep 1510501 = 283219) (by norm_num)
theorem B1019017 : Blo 892572 1019017 := bbase (se 2 (by rfl) ⟨382131, by rfl⟩ : syracuseStep 1019017 = 764263) (by norm_num)
theorem B2264213 : Blo 892572 2264213 := bbase (se 6 (by rfl) ⟨53067, by rfl⟩ : syracuseStep 2264213 = 106135) (by norm_num)
theorem B1510589 : Blo 892572 1510589 := bbase (se 3 (by rfl) ⟨283235, by rfl⟩ : syracuseStep 1510589 = 566471) (by norm_num)
theorem B920777 : Blo 892572 920777 := bbase (se 2 (by rfl) ⟨345291, by rfl⟩ : syracuseStep 920777 = 690583) (by norm_num)
theorem B3018005 : Blo 892572 3018005 := bbase (se 6 (by rfl) ⟨70734, by rfl⟩ : syracuseStep 3018005 = 141469) (by norm_num)
theorem B1510717 : Blo 892572 1510717 := bbase (se 3 (by rfl) ⟨283259, by rfl⟩ : syracuseStep 1510717 = 566519) (by norm_num)
theorem B1019209 : Blo 892572 1019209 := bbase (se 2 (by rfl) ⟨382203, by rfl⟩ : syracuseStep 1019209 = 764407) (by norm_num)
theorem B953737 : Blo 892572 953737 := bbase (se 2 (by rfl) ⟨357651, by rfl⟩ : syracuseStep 953737 = 715303) (by norm_num)
theorem B1510805 : Blo 892572 1510805 := bbase (se 6 (by rfl) ⟨35409, by rfl⟩ : syracuseStep 1510805 = 70819) (by norm_num)
theorem B1019309 : Blo 892572 1019309 := bbase (se 3 (by rfl) ⟨191120, by rfl⟩ : syracuseStep 1019309 = 382241) (by norm_num)
theorem B2264557 : Blo 892572 2264557 := bbase (se 3 (by rfl) ⟨424604, by rfl⟩ : syracuseStep 2264557 = 849209) (by norm_num)
theorem B953857 : Blo 892572 953857 := bbase (se 2 (by rfl) ⟨357696, by rfl⟩ : syracuseStep 953857 = 715393) (by norm_num)
theorem B1510933 : Blo 892572 1510933 := bbase (se 6 (by rfl) ⟨35412, by rfl⟩ : syracuseStep 1510933 = 70825) (by norm_num)
theorem B2362949 : Blo 892572 2362949 := bbase (se 4 (by rfl) ⟨221526, by rfl⟩ : syracuseStep 2362949 = 443053) (by norm_num)
theorem B2264669 : Blo 892572 2264669 := bbase (se 3 (by rfl) ⟨424625, by rfl⟩ : syracuseStep 2264669 = 849251) (by norm_num)
theorem B1511021 : Blo 892572 1511021 := bbase (se 3 (by rfl) ⟨283316, by rfl⟩ : syracuseStep 1511021 = 566633) (by norm_num)
theorem B3018437 : Blo 892572 3018437 := bbase (se 4 (by rfl) ⟨282978, by rfl⟩ : syracuseStep 3018437 = 565957) (by norm_num)
theorem B1511149 : Blo 892572 1511149 := bbase (se 3 (by rfl) ⟨283340, by rfl⟩ : syracuseStep 1511149 = 566681) (by norm_num)
theorem B954109 : Blo 892572 954109 := bbase (se 3 (by rfl) ⟨178895, by rfl⟩ : syracuseStep 954109 = 357791) (by norm_num)
theorem B954113 : Blo 892572 954113 := bbase (se 2 (by rfl) ⟨357792, by rfl⟩ : syracuseStep 954113 = 715585) (by norm_num)
theorem B2264861 : Blo 892572 2264861 := bbase (se 3 (by rfl) ⟨424661, by rfl⟩ : syracuseStep 2264861 = 849323) (by norm_num)
theorem B1511237 : Blo 892572 1511237 := bbase (se 4 (by rfl) ⟨141678, by rfl⟩ : syracuseStep 1511237 = 283357) (by norm_num)
theorem B2723701 : Blo 892572 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B1511365 : Blo 892572 1511365 := bbase (se 4 (by rfl) ⟨141690, by rfl⟩ : syracuseStep 1511365 = 283381) (by norm_num)
theorem B1511453 : Blo 892572 1511453 := bbase (se 3 (by rfl) ⟨283397, by rfl⟩ : syracuseStep 1511453 = 566795) (by norm_num)
theorem B4526117 : Blo 892572 4526117 := bbase (se 4 (by rfl) ⟨424323, by rfl⟩ : syracuseStep 4526117 = 848647) (by norm_num)
theorem B3018869 : Blo 892572 3018869 := bbase (se 5 (by rfl) ⟨141509, by rfl⟩ : syracuseStep 3018869 = 283019) (by norm_num)
theorem B2265205 : Blo 892572 2265205 := bbase (se 5 (by rfl) ⟨106181, by rfl⟩ : syracuseStep 2265205 = 212363) (by norm_num)
theorem B1511581 : Blo 892572 1511581 := bbase (se 3 (by rfl) ⟨283421, by rfl⟩ : syracuseStep 1511581 = 566843) (by norm_num)
theorem B2265317 : Blo 892572 2265317 := bbase (se 4 (by rfl) ⟨212373, by rfl⟩ : syracuseStep 2265317 = 424747) (by norm_num)
theorem B1511669 : Blo 892572 1511669 := bbase (se 5 (by rfl) ⟨70859, by rfl⟩ : syracuseStep 1511669 = 141719) (by norm_num)
theorem B1937677 : Blo 892572 1937677 := bbase (se 3 (by rfl) ⟨363314, by rfl⟩ : syracuseStep 1937677 = 726629) (by norm_num)
theorem B954677 : Blo 892572 954677 := bbase (se 5 (by rfl) ⟨44750, by rfl⟩ : syracuseStep 954677 = 89501) (by norm_num)
theorem B4297045 : Blo 892572 4297045 := bbase (se 10 (by rfl) ⟨6294, by rfl⟩ : syracuseStep 4297045 = 12589) (by norm_num)
theorem B1511797 : Blo 892572 1511797 := bbase (se 5 (by rfl) ⟨70865, by rfl⟩ : syracuseStep 1511797 = 141731) (by norm_num)
theorem B2265509 : Blo 892572 2265509 := bbase (se 4 (by rfl) ⟨212391, by rfl⟩ : syracuseStep 2265509 = 424783) (by norm_num)
theorem B1511885 : Blo 892572 1511885 := bbase (se 3 (by rfl) ⟨283478, by rfl⟩ : syracuseStep 1511885 = 566957) (by norm_num)
theorem B954865 : Blo 892572 954865 := bbase (se 2 (by rfl) ⟨358074, by rfl⟩ : syracuseStep 954865 = 716149) (by norm_num)
theorem B3019301 : Blo 892572 3019301 := bbase (se 4 (by rfl) ⟨283059, by rfl⟩ : syracuseStep 3019301 = 566119) (by norm_num)
theorem B1512013 : Blo 892572 1512013 := bbase (se 3 (by rfl) ⟨283502, by rfl⟩ : syracuseStep 1512013 = 567005) (by norm_num)
theorem B1512101 : Blo 892572 1512101 := bbase (se 4 (by rfl) ⟨141759, by rfl⟩ : syracuseStep 1512101 = 283519) (by norm_num)
theorem B2265853 : Blo 892572 2265853 := bbase (se 3 (by rfl) ⟨424847, by rfl⟩ : syracuseStep 2265853 = 849695) (by norm_num)
theorem B1512229 : Blo 892572 1512229 := bbase (se 4 (by rfl) ⟨141771, by rfl⟩ : syracuseStep 1512229 = 283543) (by norm_num)
theorem B1020713 : Blo 892572 1020713 := bbase (se 2 (by rfl) ⟨382767, by rfl⟩ : syracuseStep 1020713 = 765535) (by norm_num)
theorem B2265965 : Blo 892572 2265965 := bbase (se 3 (by rfl) ⟨424868, by rfl⟩ : syracuseStep 2265965 = 849737) (by norm_num)
theorem B1512317 : Blo 892572 1512317 := bbase (se 3 (by rfl) ⟨283559, by rfl⟩ : syracuseStep 1512317 = 567119) (by norm_num)
theorem B3019733 : Blo 892572 3019733 := bbase (se 7 (by rfl) ⟨35387, by rfl⟩ : syracuseStep 3019733 = 70775) (by norm_num)
theorem B2331605 : Blo 892572 2331605 := bbase (se 7 (by rfl) ⟨27323, by rfl⟩ : syracuseStep 2331605 = 54647) (by norm_num)
theorem B1512445 : Blo 892572 1512445 := bbase (se 3 (by rfl) ⟨283583, by rfl⟩ : syracuseStep 1512445 = 567167) (by norm_num)
theorem B2266157 : Blo 892572 2266157 := bbase (se 3 (by rfl) ⟨424904, by rfl⟩ : syracuseStep 2266157 = 849809) (by norm_num)
theorem B1512533 : Blo 892572 1512533 := bbase (se 8 (by rfl) ⟨8862, by rfl⟩ : syracuseStep 1512533 = 17725) (by norm_num)
theorem B1512661 : Blo 892572 1512661 := bbase (se 7 (by rfl) ⟨17726, by rfl⟩ : syracuseStep 1512661 = 35453) (by norm_num)
theorem B955685 : Blo 892572 955685 := bbase (se 4 (by rfl) ⟨89595, by rfl⟩ : syracuseStep 955685 = 179191) (by norm_num)
theorem B1512749 : Blo 892572 1512749 := bbase (se 3 (by rfl) ⟨283640, by rfl⟩ : syracuseStep 1512749 = 567281) (by norm_num)
theorem B4527413 : Blo 892572 4527413 := bbase (se 5 (by rfl) ⟨212222, by rfl⟩ : syracuseStep 4527413 = 424445) (by norm_num)
theorem B3020165 : Blo 892572 3020165 := bbase (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) (by norm_num)
theorem B2266501 : Blo 892572 2266501 := bbase (se 4 (by rfl) ⟨212484, by rfl⟩ : syracuseStep 2266501 = 424969) (by norm_num)
theorem B1512877 : Blo 892572 1512877 := bbase (se 3 (by rfl) ⟨283664, by rfl⟩ : syracuseStep 1512877 = 567329) (by norm_num)
theorem B2266613 : Blo 892572 2266613 := bbase (se 5 (by rfl) ⟨106247, by rfl⟩ : syracuseStep 2266613 = 212495) (by norm_num)
theorem B1512965 : Blo 892572 1512965 := bbase (se 4 (by rfl) ⟨141840, by rfl⟩ : syracuseStep 1512965 = 283681) (by norm_num)
theorem B2266805 : Blo 892572 2266805 := bbase (se 5 (by rfl) ⟨106256, by rfl⟩ : syracuseStep 2266805 = 212513) (by norm_num)
theorem B956129 : Blo 892572 956129 := bbase (se 2 (by rfl) ⟨358548, by rfl⟩ : syracuseStep 956129 = 717097) (by norm_num)
theorem B3020597 : Blo 892572 3020597 := bbase (se 5 (by rfl) ⟨141590, by rfl⟩ : syracuseStep 3020597 = 283181) (by norm_num)
theorem B956377 : Blo 892572 956377 := bbase (se 2 (by rfl) ⟨358641, by rfl⟩ : syracuseStep 956377 = 717283) (by norm_num)
theorem B2267149 : Blo 892572 2267149 := bbase (se 3 (by rfl) ⟨425090, by rfl⟩ : syracuseStep 2267149 = 850181) (by norm_num)
theorem B1906757 : Blo 892572 1906757 := bbase (se 4 (by rfl) ⟨178758, by rfl⟩ : syracuseStep 1906757 = 357517) (by norm_num)
theorem B1022041 : Blo 892572 1022041 := bbase (se 2 (by rfl) ⟨383265, by rfl⟩ : syracuseStep 1022041 = 766531) (by norm_num)
theorem B2267261 : Blo 892572 2267261 := bbase (se 3 (by rfl) ⟨425111, by rfl⟩ : syracuseStep 2267261 = 850223) (by norm_num)
theorem B1022077 : Blo 892572 1022077 := bbase (se 3 (by rfl) ⟨191639, by rfl⟩ : syracuseStep 1022077 = 383279) (by norm_num)
theorem B1906877 : Blo 892572 1906877 := bbase (se 3 (by rfl) ⟨357539, by rfl⟩ : syracuseStep 1906877 = 715079) (by norm_num)
theorem B5445845 : Blo 892572 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B3021029 : Blo 892572 3021029 := bbase (se 4 (by rfl) ⟨283221, by rfl⟩ : syracuseStep 3021029 = 566443) (by norm_num)
theorem B1612021 : Blo 892572 1612021 := bbase (se 5 (by rfl) ⟨75563, by rfl⟩ : syracuseStep 1612021 = 151127) (by norm_num)
theorem B2267453 : Blo 892572 2267453 := bbase (se 3 (by rfl) ⟨425147, by rfl⟩ : syracuseStep 2267453 = 850295) (by norm_num)
theorem B956809 : Blo 892572 956809 := bbase (se 2 (by rfl) ⟨358803, by rfl⟩ : syracuseStep 956809 = 717607) (by norm_num)
theorem B14522773 : Blo 892572 14522773 := bbase (se 6 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 14522773 = 680755) (by norm_num)
theorem B1612229 : Blo 892572 1612229 := bbase (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) (by norm_num)
theorem B956881 : Blo 892572 956881 := bbase (se 2 (by rfl) ⟨358830, by rfl⟩ : syracuseStep 956881 = 717661) (by norm_num)
theorem B4528709 : Blo 892572 4528709 := bbase (se 4 (by rfl) ⟨424566, by rfl⟩ : syracuseStep 4528709 = 849133) (by norm_num)
theorem B3054229 : Blo 892572 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B3021461 : Blo 892572 3021461 := bbase (se 6 (by rfl) ⟨70815, by rfl⟩ : syracuseStep 3021461 = 141631) (by norm_num)
theorem B2267797 : Blo 892572 2267797 := bbase (se 6 (by rfl) ⟨53151, by rfl⟩ : syracuseStep 2267797 = 106303) (by norm_num)
theorem B2267909 : Blo 892572 2267909 := bbase (se 4 (by rfl) ⟨212616, by rfl⟩ : syracuseStep 2267909 = 425233) (by norm_num)
theorem B1907509 : Blo 892572 1907509 := bbase (se 5 (by rfl) ⟨89414, by rfl⟩ : syracuseStep 1907509 = 178829) (by norm_num)
theorem B957253 : Blo 892572 957253 := bbase (se 4 (by rfl) ⟨89742, by rfl⟩ : syracuseStep 957253 = 179485) (by norm_num)
theorem B2268101 : Blo 892572 2268101 := bbase (se 4 (by rfl) ⟨212634, by rfl⟩ : syracuseStep 2268101 = 425269) (by norm_num)
theorem B3021893 : Blo 892572 3021893 := bbase (se 4 (by rfl) ⟨283302, by rfl⟩ : syracuseStep 3021893 = 566605) (by norm_num)
theorem B2268445 : Blo 892572 2268445 := bbase (se 3 (by rfl) ⟨425333, by rfl⟩ : syracuseStep 2268445 = 850667) (by norm_num)
theorem B2268557 : Blo 892572 2268557 := bbase (se 3 (by rfl) ⟨425354, by rfl⟩ : syracuseStep 2268557 = 850709) (by norm_num)
theorem B2792933 : Blo 892572 2792933 := bbase (se 4 (by rfl) ⟨261837, by rfl⟩ : syracuseStep 2792933 = 523675) (by norm_num)
theorem B3022325 : Blo 892572 3022325 := bbase (se 5 (by rfl) ⟨141671, by rfl⟩ : syracuseStep 3022325 = 283343) (by norm_num)
theorem B2268749 : Blo 892572 2268749 := bbase (se 3 (by rfl) ⟨425390, by rfl⟩ : syracuseStep 2268749 = 850781) (by norm_num)
theorem B1908397 : Blo 892572 1908397 := bbase (se 3 (by rfl) ⟨357824, by rfl⟩ : syracuseStep 1908397 = 715649) (by norm_num)
theorem B1908517 : Blo 892572 1908517 := bbase (se 4 (by rfl) ⟨178923, by rfl⟩ : syracuseStep 1908517 = 357847) (by norm_num)
theorem B4530005 : Blo 892572 4530005 := bbase (se 9 (by rfl) ⟨13271, by rfl⟩ : syracuseStep 4530005 = 26543) (by norm_num)
theorem B3022757 : Blo 892572 3022757 := bbase (se 4 (by rfl) ⟨283383, by rfl⟩ : syracuseStep 3022757 = 566767) (by norm_num)
theorem B2269093 : Blo 892572 2269093 := bbase (se 4 (by rfl) ⟨212727, by rfl⟩ : syracuseStep 2269093 = 425455) (by norm_num)
theorem B2072573 : Blo 892572 2072573 := bbase (se 3 (by rfl) ⟨388607, by rfl⟩ : syracuseStep 2072573 = 777215) (by norm_num)
theorem B2269205 : Blo 892572 2269205 := bbase (se 6 (by rfl) ⟨53184, by rfl⟩ : syracuseStep 2269205 = 106369) (by norm_num)
theorem B1908773 : Blo 892572 1908773 := bbase (se 4 (by rfl) ⟨178947, by rfl⟩ : syracuseStep 1908773 = 357895) (by norm_num)
theorem B1613981 : Blo 892572 1613981 := bbase (se 3 (by rfl) ⟨302621, by rfl⟩ : syracuseStep 1613981 = 605243) (by norm_num)
theorem B2203829 : Blo 892572 2203829 := bbase (se 5 (by rfl) ⟨103304, by rfl⟩ : syracuseStep 2203829 = 206609) (by norm_num)
theorem B2269397 : Blo 892572 2269397 := bbase (se 7 (by rfl) ⟨26594, by rfl⟩ : syracuseStep 2269397 = 53189) (by norm_num)
theorem B4301045 : Blo 892572 4301045 := bbase (se 5 (by rfl) ⟨201611, by rfl⟩ : syracuseStep 4301045 = 403223) (by norm_num)
theorem B3023189 : Blo 892572 3023189 := bbase (se 10 (by rfl) ⟨4428, by rfl⟩ : syracuseStep 3023189 = 8857) (by norm_num)
theorem B4301237 : Blo 892572 4301237 := bbase (se 5 (by rfl) ⟨201620, by rfl⟩ : syracuseStep 4301237 = 403241) (by norm_num)
theorem B3023621 : Blo 892572 3023621 := bbase (se 4 (by rfl) ⟨283464, by rfl⟩ : syracuseStep 3023621 = 566929) (by norm_num)
theorem B1450853 : Blo 892572 1450853 := bbase (se 4 (by rfl) ⟨136017, by rfl⟩ : syracuseStep 1450853 = 272035) (by norm_num)
theorem B1909661 : Blo 892572 1909661 := bbase (se 3 (by rfl) ⟨358061, by rfl⟩ : syracuseStep 1909661 = 716123) (by norm_num)
theorem B5743541 : Blo 892572 5743541 := bbase (se 5 (by rfl) ⟨269228, by rfl⟩ : syracuseStep 5743541 = 538457) (by norm_num)
theorem B1614925 : Blo 892572 1614925 := bbase (se 3 (by rfl) ⟨302798, by rfl⟩ : syracuseStep 1614925 = 605597) (by norm_num)
theorem B4531301 : Blo 892572 4531301 := bbase (se 4 (by rfl) ⟨424809, by rfl⟩ : syracuseStep 4531301 = 849619) (by norm_num)
theorem B1909901 : Blo 892572 1909901 := bbase (se 3 (by rfl) ⟨358106, by rfl⟩ : syracuseStep 1909901 = 716213) (by norm_num)
theorem B3024053 : Blo 892572 3024053 := bbase (se 5 (by rfl) ⟨141752, by rfl⟩ : syracuseStep 3024053 = 283505) (by norm_num)
theorem B11445461 : Blo 892572 11445461 := bbase (se 7 (by rfl) ⟨134126, by rfl⟩ : syracuseStep 11445461 = 268253) (by norm_num)
theorem B2008349 : Blo 892572 2008349 := bbase (se 3 (by rfl) ⟨376565, by rfl⟩ : syracuseStep 2008349 = 753131) (by norm_num)
theorem B2008421 : Blo 892572 2008421 := bbase (se 4 (by rfl) ⟨188289, by rfl⟩ : syracuseStep 2008421 = 376579) (by norm_num)
theorem B2008493 : Blo 892572 2008493 := bbase (se 3 (by rfl) ⟨376592, by rfl⟩ : syracuseStep 2008493 = 753185) (by norm_num)
theorem B1811909 : Blo 892572 1811909 := bbase (se 4 (by rfl) ⟨169866, by rfl⟩ : syracuseStep 1811909 = 339733) (by norm_num)
theorem B2008565 : Blo 892572 2008565 := bbase (se 5 (by rfl) ⟨94151, by rfl⟩ : syracuseStep 2008565 = 188303) (by norm_num)
theorem B2041381 : Blo 892572 2041381 := bbase (se 4 (by rfl) ⟨191379, by rfl⟩ : syracuseStep 2041381 = 382759) (by norm_num)
theorem B2008637 : Blo 892572 2008637 := bbase (se 3 (by rfl) ⟨376619, by rfl⟩ : syracuseStep 2008637 = 753239) (by norm_num)
theorem B3024485 : Blo 892572 3024485 := bbase (se 4 (by rfl) ⟨283545, by rfl⟩ : syracuseStep 3024485 = 567091) (by norm_num)
theorem B6792821 : Blo 892572 6792821 := bbase (se 5 (by rfl) ⟨318413, by rfl⟩ : syracuseStep 6792821 = 636827) (by norm_num)
theorem B2008709 : Blo 892572 2008709 := bbase (se 4 (by rfl) ⟨188316, by rfl⟩ : syracuseStep 2008709 = 376633) (by norm_num)
theorem B1910405 : Blo 892572 1910405 := bbase (se 4 (by rfl) ⟨179100, by rfl⟩ : syracuseStep 1910405 = 358201) (by norm_num)
theorem B1910413 : Blo 892572 1910413 := bbase (se 3 (by rfl) ⟨358202, by rfl⟩ : syracuseStep 1910413 = 716405) (by norm_num)
theorem B2008781 : Blo 892572 2008781 := bbase (se 3 (by rfl) ⟨376646, by rfl⟩ : syracuseStep 2008781 = 753293) (by norm_num)
theorem B5089013 : Blo 892572 5089013 := bbase (se 5 (by rfl) ⟨238547, by rfl⟩ : syracuseStep 5089013 = 477095) (by norm_num)
theorem B2008853 : Blo 892572 2008853 := bbase (se 6 (by rfl) ⟨47082, by rfl⟩ : syracuseStep 2008853 = 94165) (by norm_num)
theorem B2008925 : Blo 892572 2008925 := bbase (se 3 (by rfl) ⟨376673, by rfl⟩ : syracuseStep 2008925 = 753347) (by norm_num)
theorem B2008997 : Blo 892572 2008997 := bbase (se 4 (by rfl) ⟨188343, by rfl⟩ : syracuseStep 2008997 = 376687) (by norm_num)
theorem B2009069 : Blo 892572 2009069 := bbase (se 3 (by rfl) ⟨376700, by rfl⟩ : syracuseStep 2009069 = 753401) (by norm_num)
theorem B7645205 : Blo 892572 7645205 := bbase (se 6 (by rfl) ⟨179184, by rfl⟩ : syracuseStep 7645205 = 358369) (by norm_num)
theorem B3024917 : Blo 892572 3024917 := bbase (se 6 (by rfl) ⟨70896, by rfl⟩ : syracuseStep 3024917 = 141793) (by norm_num)
theorem B2009141 : Blo 892572 2009141 := bbase (se 5 (by rfl) ⟨94178, by rfl⟩ : syracuseStep 2009141 = 188357) (by norm_num)
theorem B1812557 : Blo 892572 1812557 := bbase (se 3 (by rfl) ⟨339854, by rfl⟩ : syracuseStep 1812557 = 679709) (by norm_num)
theorem B2009213 : Blo 892572 2009213 := bbase (se 3 (by rfl) ⟨376727, by rfl⟩ : syracuseStep 2009213 = 753455) (by norm_num)
theorem B2009285 : Blo 892572 2009285 := bbase (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) (by norm_num)
theorem B2009357 : Blo 892572 2009357 := bbase (se 3 (by rfl) ⟨376754, by rfl⟩ : syracuseStep 2009357 = 753509) (by norm_num)
theorem B2009429 : Blo 892572 2009429 := bbase (se 10 (by rfl) ⟨2943, by rfl⟩ : syracuseStep 2009429 = 5887) (by norm_num)
theorem B3221861 : Blo 892572 3221861 := bbase (se 4 (by rfl) ⟨302049, by rfl⟩ : syracuseStep 3221861 = 604099) (by norm_num)
theorem B4532597 : Blo 892572 4532597 := bbase (se 5 (by rfl) ⟨212465, by rfl⟩ : syracuseStep 4532597 = 424931) (by norm_num)
theorem B2009501 : Blo 892572 2009501 := bbase (se 3 (by rfl) ⟨376781, by rfl⟩ : syracuseStep 2009501 = 753563) (by norm_num)
theorem B1550765 : Blo 892572 1550765 := bbase (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) (by norm_num)
theorem B3025349 : Blo 892572 3025349 := bbase (se 4 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 3025349 = 567253) (by norm_num)
theorem B2009573 : Blo 892572 2009573 := bbase (se 4 (by rfl) ⟨188397, by rfl⟩ : syracuseStep 2009573 = 376795) (by norm_num)
theorem B2009645 : Blo 892572 2009645 := bbase (se 3 (by rfl) ⟨376808, by rfl⟩ : syracuseStep 2009645 = 753617) (by norm_num)
theorem B2009717 : Blo 892572 2009717 := bbase (se 5 (by rfl) ⟨94205, by rfl⟩ : syracuseStep 2009717 = 188411) (by norm_num)
theorem B1813141 : Blo 892572 1813141 := bbase (se 6 (by rfl) ⟨42495, by rfl⟩ : syracuseStep 1813141 = 84991) (by norm_num)
theorem B1288885 : Blo 892572 1288885 := bbase (se 5 (by rfl) ⟨60416, by rfl⟩ : syracuseStep 1288885 = 120833) (by norm_num)
theorem B2009789 : Blo 892572 2009789 := bbase (se 3 (by rfl) ⟨376835, by rfl⟩ : syracuseStep 2009789 = 753671) (by norm_num)
theorem B1911541 : Blo 892572 1911541 := bbase (se 5 (by rfl) ⟨89603, by rfl⟩ : syracuseStep 1911541 = 179207) (by norm_num)
theorem B2009861 : Blo 892572 2009861 := bbase (se 4 (by rfl) ⟨188424, by rfl⟩ : syracuseStep 2009861 = 376849) (by norm_num)
theorem B2009933 : Blo 892572 2009933 := bbase (se 3 (by rfl) ⟨376862, by rfl⟩ : syracuseStep 2009933 = 753725) (by norm_num)
theorem B3025781 : Blo 892572 3025781 := bbase (se 5 (by rfl) ⟨141833, by rfl⟩ : syracuseStep 3025781 = 283667) (by norm_num)
theorem B2010005 : Blo 892572 2010005 := bbase (se 6 (by rfl) ⟨47109, by rfl⟩ : syracuseStep 2010005 = 94219) (by norm_num)
theorem B2010077 : Blo 892572 2010077 := bbase (se 3 (by rfl) ⟨376889, by rfl⟩ : syracuseStep 2010077 = 753779) (by norm_num)
theorem B1289197 : Blo 892572 1289197 := bbase (se 3 (by rfl) ⟨241724, by rfl⟩ : syracuseStep 1289197 = 483449) (by norm_num)
theorem B2173981 : Blo 892572 2173981 := bbase (se 3 (by rfl) ⟨407621, by rfl⟩ : syracuseStep 2173981 = 815243) (by norm_num)
theorem B2010149 : Blo 892572 2010149 := bbase (se 4 (by rfl) ⟨188451, by rfl⟩ : syracuseStep 2010149 = 376903) (by norm_num)
theorem B2010221 : Blo 892572 2010221 := bbase (se 3 (by rfl) ⟨376916, by rfl⟩ : syracuseStep 2010221 = 753833) (by norm_num)
theorem B1911917 : Blo 892572 1911917 := bbase (se 3 (by rfl) ⟨358484, by rfl⟩ : syracuseStep 1911917 = 716969) (by norm_num)
theorem B2010293 : Blo 892572 2010293 := bbase (se 5 (by rfl) ⟨94232, by rfl⟩ : syracuseStep 2010293 = 188465) (by norm_num)
theorem B1289461 : Blo 892572 1289461 := bbase (se 5 (by rfl) ⟨60443, by rfl⟩ : syracuseStep 1289461 = 120887) (by norm_num)
theorem B3222773 : Blo 892572 3222773 := bbase (se 5 (by rfl) ⟨151067, by rfl⟩ : syracuseStep 3222773 = 302135) (by norm_num)
theorem B2010365 : Blo 892572 2010365 := bbase (se 3 (by rfl) ⟨376943, by rfl⟩ : syracuseStep 2010365 = 753887) (by norm_num)
theorem B2010437 : Blo 892572 2010437 := bbase (se 4 (by rfl) ⟨188478, by rfl⟩ : syracuseStep 2010437 = 376957) (by norm_num)
theorem B2010509 : Blo 892572 2010509 := bbase (se 3 (by rfl) ⟨376970, by rfl⟩ : syracuseStep 2010509 = 753941) (by norm_num)
theorem B2862533 : Blo 892572 2862533 := bbase (se 4 (by rfl) ⟨268362, by rfl⟩ : syracuseStep 2862533 = 536725) (by norm_num)
theorem B2010581 : Blo 892572 2010581 := bbase (se 7 (by rfl) ⟨23561, by rfl⟩ : syracuseStep 2010581 = 47123) (by norm_num)
theorem B2010653 : Blo 892572 2010653 := bbase (se 3 (by rfl) ⟨376997, by rfl⟩ : syracuseStep 2010653 = 753995) (by norm_num)
theorem B3812933 : Blo 892572 3812933 := bbase (se 4 (by rfl) ⟨357462, by rfl⟩ : syracuseStep 3812933 = 714925) (by norm_num)
theorem B2010725 : Blo 892572 2010725 := bbase (se 4 (by rfl) ⟨188505, by rfl⟩ : syracuseStep 2010725 = 377011) (by norm_num)
theorem B4533893 : Blo 892572 4533893 := bbase (se 4 (by rfl) ⟨425052, by rfl⟩ : syracuseStep 4533893 = 850105) (by norm_num)
theorem B2010797 : Blo 892572 2010797 := bbase (se 3 (by rfl) ⟨377024, by rfl⟩ : syracuseStep 2010797 = 754049) (by norm_num)
theorem B1814197 : Blo 892572 1814197 := bbase (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) (by norm_num)
theorem B2010869 : Blo 892572 2010869 := bbase (se 5 (by rfl) ⟨94259, by rfl⟩ : syracuseStep 2010869 = 188519) (by norm_num)
theorem B1289981 : Blo 892572 1289981 := bbase (se 3 (by rfl) ⟨241871, by rfl⟩ : syracuseStep 1289981 = 483743) (by norm_num)
theorem B2010941 : Blo 892572 2010941 := bbase (se 3 (by rfl) ⟨377051, by rfl⟩ : syracuseStep 2010941 = 754103) (by norm_num)
theorem B2011013 : Blo 892572 2011013 := bbase (se 4 (by rfl) ⟨188532, by rfl⟩ : syracuseStep 2011013 = 377065) (by norm_num)
theorem B2011085 : Blo 892572 2011085 := bbase (se 3 (by rfl) ⟨377078, by rfl⟩ : syracuseStep 2011085 = 754157) (by norm_num)
theorem B2011157 : Blo 892572 2011157 := bbase (se 6 (by rfl) ⟨47136, by rfl⟩ : syracuseStep 2011157 = 94273) (by norm_num)
theorem B2011229 : Blo 892572 2011229 := bbase (se 3 (by rfl) ⟨377105, by rfl⟩ : syracuseStep 2011229 = 754211) (by norm_num)
theorem B2044037 : Blo 892572 2044037 := bbase (se 4 (by rfl) ⟨191628, by rfl⟩ : syracuseStep 2044037 = 383257) (by norm_num)
theorem B2011301 : Blo 892572 2011301 := bbase (se 4 (by rfl) ⟨188559, by rfl⟩ : syracuseStep 2011301 = 377119) (by norm_num)
theorem B2011373 : Blo 892572 2011373 := bbase (se 3 (by rfl) ⟨377132, by rfl⟩ : syracuseStep 2011373 = 754265) (by norm_num)
theorem B2011445 : Blo 892572 2011445 := bbase (se 5 (by rfl) ⟨94286, by rfl⟩ : syracuseStep 2011445 = 188573) (by norm_num)
theorem B2011517 : Blo 892572 2011517 := bbase (se 3 (by rfl) ⟨377159, by rfl⟩ : syracuseStep 2011517 = 754319) (by norm_num)
theorem B2011589 : Blo 892572 2011589 := bbase (se 4 (by rfl) ⟨188586, by rfl⟩ : syracuseStep 2011589 = 377173) (by norm_num)
theorem B4305349 : Blo 892572 4305349 := bbase (se 4 (by rfl) ⟨403626, by rfl⟩ : syracuseStep 4305349 = 807253) (by norm_num)
theorem B2011661 : Blo 892572 2011661 := bbase (se 3 (by rfl) ⟨377186, by rfl⟩ : syracuseStep 2011661 = 754373) (by norm_num)
theorem B2011733 : Blo 892572 2011733 := bbase (se 8 (by rfl) ⟨11787, by rfl⟩ : syracuseStep 2011733 = 23575) (by norm_num)
theorem B2011805 : Blo 892572 2011805 := bbase (se 3 (by rfl) ⟨377213, by rfl⟩ : syracuseStep 2011805 = 754427) (by norm_num)
theorem B1913557 : Blo 892572 1913557 := bbase (se 7 (by rfl) ⟨22424, by rfl⟩ : syracuseStep 1913557 = 44849) (by norm_num)
theorem B2011877 : Blo 892572 2011877 := bbase (se 4 (by rfl) ⟨188613, by rfl⟩ : syracuseStep 2011877 = 377227) (by norm_num)
theorem B2011949 : Blo 892572 2011949 := bbase (se 3 (by rfl) ⟨377240, by rfl⟩ : syracuseStep 2011949 = 754481) (by norm_num)
theorem B1815365 : Blo 892572 1815365 := bbase (se 4 (by rfl) ⟨170190, by rfl⟩ : syracuseStep 1815365 = 340381) (by norm_num)
theorem B2012021 : Blo 892572 2012021 := bbase (se 5 (by rfl) ⟨94313, by rfl⟩ : syracuseStep 2012021 = 188627) (by norm_num)
theorem B4535189 : Blo 892572 4535189 := bbase (se 6 (by rfl) ⟨106293, by rfl⟩ : syracuseStep 4535189 = 212587) (by norm_num)
theorem B7648181 : Blo 892572 7648181 := bbase (se 5 (by rfl) ⟨358508, by rfl⟩ : syracuseStep 7648181 = 717017) (by norm_num)
theorem B2012093 : Blo 892572 2012093 := bbase (se 3 (by rfl) ⟨377267, by rfl⟩ : syracuseStep 2012093 = 754535) (by norm_num)
theorem B9286613 : Blo 892572 9286613 := bbase (se 7 (by rfl) ⟨108827, by rfl⟩ : syracuseStep 9286613 = 217655) (by norm_num)
theorem B5452757 : Blo 892572 5452757 := bbase (se 7 (by rfl) ⟨63899, by rfl⟩ : syracuseStep 5452757 = 127799) (by norm_num)
theorem B2012165 : Blo 892572 2012165 := bbase (se 4 (by rfl) ⟨188640, by rfl⟩ : syracuseStep 2012165 = 377281) (by norm_num)
theorem B3224629 : Blo 892572 3224629 := bbase (se 5 (by rfl) ⟨151154, by rfl⟩ : syracuseStep 3224629 = 302309) (by norm_num)
theorem B2012237 : Blo 892572 2012237 := bbase (se 3 (by rfl) ⟨377294, by rfl⟩ : syracuseStep 2012237 = 754589) (by norm_num)
theorem B2012309 : Blo 892572 2012309 := bbase (se 6 (by rfl) ⟨47163, by rfl⟩ : syracuseStep 2012309 = 94327) (by norm_num)
theorem B2012381 : Blo 892572 2012381 := bbase (se 3 (by rfl) ⟨377321, by rfl⟩ : syracuseStep 2012381 = 754643) (by norm_num)
theorem B2012453 : Blo 892572 2012453 := bbase (se 4 (by rfl) ⟨188667, by rfl⟩ : syracuseStep 2012453 = 377335) (by norm_num)
theorem B2012525 : Blo 892572 2012525 := bbase (se 3 (by rfl) ⟨377348, by rfl⟩ : syracuseStep 2012525 = 754697) (by norm_num)
theorem B2012597 : Blo 892572 2012597 := bbase (se 5 (by rfl) ⟨94340, by rfl⟩ : syracuseStep 2012597 = 188681) (by norm_num)
theorem B2012669 : Blo 892572 2012669 := bbase (se 3 (by rfl) ⟨377375, by rfl⟩ : syracuseStep 2012669 = 754751) (by norm_num)
theorem B2012741 : Blo 892572 2012741 := bbase (se 4 (by rfl) ⟨188694, by rfl⟩ : syracuseStep 2012741 = 377389) (by norm_num)
theorem B1914445 : Blo 892572 1914445 := bbase (se 3 (by rfl) ⟨358958, by rfl⟩ : syracuseStep 1914445 = 717917) (by norm_num)
theorem B2012813 : Blo 892572 2012813 := bbase (se 3 (by rfl) ⟨377402, by rfl⟩ : syracuseStep 2012813 = 754805) (by norm_num)
theorem B2012885 : Blo 892572 2012885 := bbase (se 7 (by rfl) ⟨23588, by rfl⟩ : syracuseStep 2012885 = 47177) (by norm_num)
theorem B2012957 : Blo 892572 2012957 := bbase (se 3 (by rfl) ⟨377429, by rfl⟩ : syracuseStep 2012957 = 754859) (by norm_num)
theorem B2013029 : Blo 892572 2013029 := bbase (se 4 (by rfl) ⟨188721, by rfl⟩ : syracuseStep 2013029 = 377443) (by norm_num)
theorem B2013101 : Blo 892572 2013101 := bbase (se 3 (by rfl) ⟨377456, by rfl⟩ : syracuseStep 2013101 = 754913) (by norm_num)
theorem B3225541 : Blo 892572 3225541 := bbase (se 4 (by rfl) ⟨302394, by rfl⟩ : syracuseStep 3225541 = 604789) (by norm_num)
theorem B2013173 : Blo 892572 2013173 := bbase (se 5 (by rfl) ⟨94367, by rfl⟩ : syracuseStep 2013173 = 188735) (by norm_num)
theorem B2013245 : Blo 892572 2013245 := bbase (se 3 (by rfl) ⟨377483, by rfl⟩ : syracuseStep 2013245 = 754967) (by norm_num)
theorem B3881029 : Blo 892572 3881029 := bbase (se 4 (by rfl) ⟨363846, by rfl⟩ : syracuseStep 3881029 = 727693) (by norm_num)
theorem B2013317 : Blo 892572 2013317 := bbase (se 4 (by rfl) ⟨188748, by rfl⟩ : syracuseStep 2013317 = 377497) (by norm_num)
theorem B4536485 : Blo 892572 4536485 := bbase (se 4 (by rfl) ⟨425295, by rfl⟩ : syracuseStep 4536485 = 850591) (by norm_num)
theorem B2013389 : Blo 892572 2013389 := bbase (se 3 (by rfl) ⟨377510, by rfl⟩ : syracuseStep 2013389 = 755021) (by norm_num)
theorem B2865365 : Blo 892572 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B2013461 : Blo 892572 2013461 := bbase (se 6 (by rfl) ⟨47190, by rfl⟩ : syracuseStep 2013461 = 94381) (by norm_num)
theorem B2013533 : Blo 892572 2013533 := bbase (se 3 (by rfl) ⟨377537, by rfl⟩ : syracuseStep 2013533 = 755075) (by norm_num)
theorem B2013605 : Blo 892572 2013605 := bbase (se 4 (by rfl) ⟨188775, by rfl⟩ : syracuseStep 2013605 = 377551) (by norm_num)
theorem B2013677 : Blo 892572 2013677 := bbase (se 3 (by rfl) ⟨377564, by rfl⟩ : syracuseStep 2013677 = 755129) (by norm_num)
theorem B3389957 : Blo 892572 3389957 := bbase (se 4 (by rfl) ⟨317808, by rfl⟩ : syracuseStep 3389957 = 635617) (by norm_num)
theorem B1653293 : Blo 892572 1653293 := bbase (se 3 (by rfl) ⟨309992, by rfl⟩ : syracuseStep 1653293 = 619985) (by norm_num)
theorem B2013749 : Blo 892572 2013749 := bbase (se 5 (by rfl) ⟨94394, by rfl⟩ : syracuseStep 2013749 = 188789) (by norm_num)
theorem B2013821 : Blo 892572 2013821 := bbase (se 3 (by rfl) ⟨377591, by rfl⟩ : syracuseStep 2013821 = 755183) (by norm_num)
theorem B2013893 : Blo 892572 2013893 := bbase (se 4 (by rfl) ⟨188802, by rfl⟩ : syracuseStep 2013893 = 377605) (by norm_num)
theorem B2013965 : Blo 892572 2013965 := bbase (se 3 (by rfl) ⟨377618, by rfl⟩ : syracuseStep 2013965 = 755237) (by norm_num)
theorem B3390245 : Blo 892572 3390245 := bbase (se 4 (by rfl) ⟨317835, by rfl⟩ : syracuseStep 3390245 = 635671) (by norm_num)
theorem B2014037 : Blo 892572 2014037 := bbase (se 9 (by rfl) ⟨5900, by rfl⟩ : syracuseStep 2014037 = 11801) (by norm_num)
theorem B2014109 : Blo 892572 2014109 := bbase (se 3 (by rfl) ⟨377645, by rfl⟩ : syracuseStep 2014109 = 755291) (by norm_num)
theorem B2014181 : Blo 892572 2014181 := bbase (se 4 (by rfl) ⟨188829, by rfl⟩ : syracuseStep 2014181 = 377659) (by norm_num)
theorem B2014253 : Blo 892572 2014253 := bbase (se 3 (by rfl) ⟨377672, by rfl⟩ : syracuseStep 2014253 = 755345) (by norm_num)
theorem B2866261 : Blo 892572 2866261 := bbase (se 8 (by rfl) ⟨16794, by rfl⟩ : syracuseStep 2866261 = 33589) (by norm_num)
theorem B2014325 : Blo 892572 2014325 := bbase (se 5 (by rfl) ⟨94421, by rfl⟩ : syracuseStep 2014325 = 188843) (by norm_num)
theorem B16333973 : Blo 892572 16333973 := bbase (se 6 (by rfl) ⟨382827, by rfl⟩ : syracuseStep 16333973 = 765655) (by norm_num)
theorem B2014397 : Blo 892572 2014397 := bbase (se 3 (by rfl) ⟨377699, by rfl⟩ : syracuseStep 2014397 = 755399) (by norm_num)
theorem B1129717 : Blo 892572 1129717 := bbase (se 5 (by rfl) ⟨52955, by rfl⟩ : syracuseStep 1129717 = 105911) (by norm_num)
theorem B2014469 : Blo 892572 2014469 := bbase (se 4 (by rfl) ⟨188856, by rfl⟩ : syracuseStep 2014469 = 377713) (by norm_num)
theorem B2014541 : Blo 892572 2014541 := bbase (se 3 (by rfl) ⟨377726, by rfl⟩ : syracuseStep 2014541 = 755453) (by norm_num)
theorem B2014613 : Blo 892572 2014613 := bbase (se 6 (by rfl) ⟨47217, by rfl⟩ : syracuseStep 2014613 = 94435) (by norm_num)
theorem B1129889 : Blo 892572 1129889 := bbase (se 2 (by rfl) ⟨423708, by rfl⟩ : syracuseStep 1129889 = 847417) (by norm_num)
theorem B4537781 : Blo 892572 4537781 := bbase (se 5 (by rfl) ⟨212708, by rfl⟩ : syracuseStep 4537781 = 425417) (by norm_num)
theorem B1129945 : Blo 892572 1129945 := bbase (se 2 (by rfl) ⟨423729, by rfl⟩ : syracuseStep 1129945 = 847459) (by norm_num)
theorem B2014685 : Blo 892572 2014685 := bbase (se 3 (by rfl) ⟨377753, by rfl⟩ : syracuseStep 2014685 = 755507) (by norm_num)
theorem B2014757 : Blo 892572 2014757 := bbase (se 4 (by rfl) ⟨188883, by rfl⟩ : syracuseStep 2014757 = 377767) (by norm_num)
theorem B1130041 : Blo 892572 1130041 := bbase (se 2 (by rfl) ⟨423765, by rfl⟩ : syracuseStep 1130041 = 847531) (by norm_num)
theorem B2014829 : Blo 892572 2014829 := bbase (se 3 (by rfl) ⟨377780, by rfl⟩ : syracuseStep 2014829 = 755561) (by norm_num)
theorem B2014901 : Blo 892572 2014901 := bbase (se 5 (by rfl) ⟨94448, by rfl⟩ : syracuseStep 2014901 = 188897) (by norm_num)
theorem B1130213 : Blo 892572 1130213 := bbase (se 4 (by rfl) ⟨105957, by rfl⟩ : syracuseStep 1130213 = 211915) (by norm_num)
theorem B1162993 : Blo 892572 1162993 := bbase (se 2 (by rfl) ⟨436122, by rfl⟩ : syracuseStep 1162993 = 872245) (by norm_num)
theorem B3817205 : Blo 892572 3817205 := bbase (se 5 (by rfl) ⟨178931, by rfl⟩ : syracuseStep 3817205 = 357863) (by norm_num)
theorem B2014973 : Blo 892572 2014973 := bbase (se 3 (by rfl) ⟨377807, by rfl⟩ : syracuseStep 2014973 = 755615) (by norm_num)
theorem B1130269 : Blo 892572 1130269 := bbase (se 3 (by rfl) ⟨211925, by rfl⟩ : syracuseStep 1130269 = 423851) (by norm_num)
theorem B2015045 : Blo 892572 2015045 := bbase (se 4 (by rfl) ⟨188910, by rfl⟩ : syracuseStep 2015045 = 377821) (by norm_num)
theorem B1130365 : Blo 892572 1130365 := bbase (se 3 (by rfl) ⟨211943, by rfl⟩ : syracuseStep 1130365 = 423887) (by norm_num)
theorem B2015117 : Blo 892572 2015117 := bbase (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) (by norm_num)
theorem B966577 : Blo 892572 966577 := bbase (se 2 (by rfl) ⟨362466, by rfl⟩ : syracuseStep 966577 = 724933) (by norm_num)
theorem B3391429 : Blo 892572 3391429 := bbase (se 4 (by rfl) ⟨317946, by rfl⟩ : syracuseStep 3391429 = 635893) (by norm_num)
theorem B2015189 : Blo 892572 2015189 := bbase (se 7 (by rfl) ⟨23615, by rfl⟩ : syracuseStep 2015189 = 47231) (by norm_num)
theorem B2015261 : Blo 892572 2015261 := bbase (se 3 (by rfl) ⟨377861, by rfl⟩ : syracuseStep 2015261 = 755723) (by norm_num)
theorem B1130537 : Blo 892572 1130537 := bbase (se 2 (by rfl) ⟨423951, by rfl⟩ : syracuseStep 1130537 = 847903) (by norm_num)
theorem B1130593 : Blo 892572 1130593 := bbase (se 2 (by rfl) ⟨423972, by rfl⟩ : syracuseStep 1130593 = 847945) (by norm_num)
theorem B2015333 : Blo 892572 2015333 := bbase (se 4 (by rfl) ⟨188937, by rfl⟩ : syracuseStep 2015333 = 377875) (by norm_num)
theorem B1720469 : Blo 892572 1720469 := bbase (se 6 (by rfl) ⟨40323, by rfl⟩ : syracuseStep 1720469 = 80647) (by norm_num)
theorem B2015405 : Blo 892572 2015405 := bbase (se 3 (by rfl) ⟨377888, by rfl⟩ : syracuseStep 2015405 = 755777) (by norm_num)
theorem B1130689 : Blo 892572 1130689 := bbase (se 2 (by rfl) ⟨424008, by rfl⟩ : syracuseStep 1130689 = 848017) (by norm_num)
theorem B3391733 : Blo 892572 3391733 := bbase (se 5 (by rfl) ⟨158987, by rfl⟩ : syracuseStep 3391733 = 317975) (by norm_num)
theorem B4079861 : Blo 892572 4079861 := bbase (se 5 (by rfl) ⟨191243, by rfl⟩ : syracuseStep 4079861 = 382487) (by norm_num)
theorem B2015477 : Blo 892572 2015477 := bbase (se 5 (by rfl) ⟨94475, by rfl⟩ : syracuseStep 2015477 = 188951) (by norm_num)
theorem B2146621 : Blo 892572 2146621 := bbase (se 3 (by rfl) ⟨402491, by rfl⟩ : syracuseStep 2146621 = 804983) (by norm_num)
theorem B2015549 : Blo 892572 2015549 := bbase (se 3 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 2015549 = 755831) (by norm_num)
theorem B3228005 : Blo 892572 3228005 := bbase (se 4 (by rfl) ⟨302625, by rfl⟩ : syracuseStep 3228005 = 605251) (by norm_num)
theorem B1130861 : Blo 892572 1130861 := bbase (se 3 (by rfl) ⟨212036, by rfl⟩ : syracuseStep 1130861 = 424073) (by norm_num)
theorem B2015621 : Blo 892572 2015621 := bbase (se 4 (by rfl) ⟨188964, by rfl⟩ : syracuseStep 2015621 = 377929) (by norm_num)
theorem B1130917 : Blo 892572 1130917 := bbase (se 4 (by rfl) ⟨106023, by rfl⟩ : syracuseStep 1130917 = 212047) (by norm_num)
theorem B2015693 : Blo 892572 2015693 := bbase (se 3 (by rfl) ⟨377942, by rfl⟩ : syracuseStep 2015693 = 755885) (by norm_num)
theorem B3228149 : Blo 892572 3228149 := bbase (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) (by norm_num)
theorem B1131013 : Blo 892572 1131013 := bbase (se 4 (by rfl) ⟨106032, by rfl⟩ : syracuseStep 1131013 = 212065) (by norm_num)
theorem B2015765 : Blo 892572 2015765 := bbase (se 6 (by rfl) ⟨47244, by rfl⟩ : syracuseStep 2015765 = 94489) (by norm_num)
theorem B2015837 : Blo 892572 2015837 := bbase (se 3 (by rfl) ⟨377969, by rfl⟩ : syracuseStep 2015837 = 755939) (by norm_num)
theorem B1360549 : Blo 892572 1360549 := bbase (se 4 (by rfl) ⟨127551, by rfl⟩ : syracuseStep 1360549 = 255103) (by norm_num)
theorem B2015909 : Blo 892572 2015909 := bbase (se 4 (by rfl) ⟨188991, by rfl⟩ : syracuseStep 2015909 = 377983) (by norm_num)
theorem B1131185 : Blo 892572 1131185 := bbase (se 2 (by rfl) ⟨424194, by rfl⟩ : syracuseStep 1131185 = 848389) (by norm_num)
theorem B1131241 : Blo 892572 1131241 := bbase (se 2 (by rfl) ⟨424215, by rfl⟩ : syracuseStep 1131241 = 848431) (by norm_num)
theorem B2015981 : Blo 892572 2015981 := bbase (se 3 (by rfl) ⟨377996, by rfl⟩ : syracuseStep 2015981 = 755993) (by norm_num)
theorem B3228437 : Blo 892572 3228437 := bbase (se 6 (by rfl) ⟨75666, by rfl⟩ : syracuseStep 3228437 = 151333) (by norm_num)
theorem B2016053 : Blo 892572 2016053 := bbase (se 5 (by rfl) ⟨94502, by rfl⟩ : syracuseStep 2016053 = 189005) (by norm_num)
theorem B1131337 : Blo 892572 1131337 := bbase (se 2 (by rfl) ⟨424251, by rfl⟩ : syracuseStep 1131337 = 848503) (by norm_num)
theorem B2016125 : Blo 892572 2016125 := bbase (se 3 (by rfl) ⟨378023, by rfl⟩ : syracuseStep 2016125 = 756047) (by norm_num)
theorem B10175381 : Blo 892572 10175381 := bbase (se 6 (by rfl) ⟨238485, by rfl⟩ : syracuseStep 10175381 = 476971) (by norm_num)
theorem B2016197 : Blo 892572 2016197 := bbase (se 4 (by rfl) ⟨189018, by rfl⟩ : syracuseStep 2016197 = 378037) (by norm_num)
theorem B1164241 : Blo 892572 1164241 := bbase (se 2 (by rfl) ⟨436590, by rfl⟩ : syracuseStep 1164241 = 873181) (by norm_num)
theorem B2147285 : Blo 892572 2147285 := bbase (se 7 (by rfl) ⟨25163, by rfl⟩ : syracuseStep 2147285 = 50327) (by norm_num)
theorem B1131509 : Blo 892572 1131509 := bbase (se 5 (by rfl) ⟨53039, by rfl⟩ : syracuseStep 1131509 = 106079) (by norm_num)
theorem B967681 : Blo 892572 967681 := bbase (se 2 (by rfl) ⟨362880, by rfl⟩ : syracuseStep 967681 = 725761) (by norm_num)
theorem B2016269 : Blo 892572 2016269 := bbase (se 3 (by rfl) ⟨378050, by rfl⟩ : syracuseStep 2016269 = 756101) (by norm_num)
theorem B1131565 : Blo 892572 1131565 := bbase (se 3 (by rfl) ⟨212168, by rfl⟩ : syracuseStep 1131565 = 424337) (by norm_num)
theorem B2016341 : Blo 892572 2016341 := bbase (se 8 (by rfl) ⟨11814, by rfl⟩ : syracuseStep 2016341 = 23629) (by norm_num)
theorem B1131661 : Blo 892572 1131661 := bbase (se 3 (by rfl) ⟨212186, by rfl⟩ : syracuseStep 1131661 = 424373) (by norm_num)
theorem B2016413 : Blo 892572 2016413 := bbase (se 3 (by rfl) ⟨378077, by rfl⟩ : syracuseStep 2016413 = 756155) (by norm_num)
theorem B6800597 : Blo 892572 6800597 := bbase (se 7 (by rfl) ⟨79694, by rfl⟩ : syracuseStep 6800597 = 159389) (by norm_num)
theorem B3622117 : Blo 892572 3622117 := bbase (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) (by norm_num)
theorem B2016485 : Blo 892572 2016485 := bbase (se 4 (by rfl) ⟨189045, by rfl⟩ : syracuseStep 2016485 = 378091) (by norm_num)
theorem B7259381 : Blo 892572 7259381 := bbase (se 5 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 7259381 = 680567) (by norm_num)
theorem B2016557 : Blo 892572 2016557 := bbase (se 3 (by rfl) ⟨378104, by rfl⟩ : syracuseStep 2016557 = 756209) (by norm_num)
theorem B1131833 : Blo 892572 1131833 := bbase (se 2 (by rfl) ⟨424437, by rfl⟩ : syracuseStep 1131833 = 848875) (by norm_num)
theorem B1131889 : Blo 892572 1131889 := bbase (se 2 (by rfl) ⟨424458, by rfl⟩ : syracuseStep 1131889 = 848917) (by norm_num)
theorem B2016629 : Blo 892572 2016629 := bbase (se 5 (by rfl) ⟨94529, by rfl⟩ : syracuseStep 2016629 = 189059) (by norm_num)
theorem B2016701 : Blo 892572 2016701 := bbase (se 3 (by rfl) ⟨378131, by rfl⟩ : syracuseStep 2016701 = 756263) (by norm_num)
theorem B1131985 : Blo 892572 1131985 := bbase (se 2 (by rfl) ⟨424494, by rfl⟩ : syracuseStep 1131985 = 848989) (by norm_num)
theorem B3818981 : Blo 892572 3818981 := bbase (se 4 (by rfl) ⟨358029, by rfl⟩ : syracuseStep 3818981 = 716059) (by norm_num)
theorem B2016773 : Blo 892572 2016773 := bbase (se 4 (by rfl) ⟨189072, by rfl⟩ : syracuseStep 2016773 = 378145) (by norm_num)
theorem B2016845 : Blo 892572 2016845 := bbase (se 3 (by rfl) ⟨378158, by rfl⟩ : syracuseStep 2016845 = 756317) (by norm_num)
theorem B5097077 : Blo 892572 5097077 := bbase (se 5 (by rfl) ⟨238925, by rfl⟩ : syracuseStep 5097077 = 477851) (by norm_num)
theorem B1132157 : Blo 892572 1132157 := bbase (se 3 (by rfl) ⟨212279, by rfl⟩ : syracuseStep 1132157 = 424559) (by norm_num)
theorem B2016917 : Blo 892572 2016917 := bbase (se 6 (by rfl) ⟨47271, by rfl⟩ : syracuseStep 2016917 = 94543) (by norm_num)
theorem B1132213 : Blo 892572 1132213 := bbase (se 5 (by rfl) ⟨53072, by rfl⟩ : syracuseStep 1132213 = 106145) (by norm_num)
theorem B3819221 : Blo 892572 3819221 := bbase (se 7 (by rfl) ⟨44756, by rfl⟩ : syracuseStep 3819221 = 89513) (by norm_num)
theorem B2016989 : Blo 892572 2016989 := bbase (se 3 (by rfl) ⟨378185, by rfl⟩ : syracuseStep 2016989 = 756371) (by norm_num)
theorem B1132309 : Blo 892572 1132309 := bbase (se 6 (by rfl) ⟨26538, by rfl⟩ : syracuseStep 1132309 = 53077) (by norm_num)
theorem B2017061 : Blo 892572 2017061 := bbase (se 4 (by rfl) ⟨189099, by rfl⟩ : syracuseStep 2017061 = 378199) (by norm_num)
theorem B2017133 : Blo 892572 2017133 := bbase (se 3 (by rfl) ⟨378212, by rfl⟩ : syracuseStep 2017133 = 756425) (by norm_num)
theorem B2869157 : Blo 892572 2869157 := bbase (se 4 (by rfl) ⟨268983, by rfl⟩ : syracuseStep 2869157 = 537967) (by norm_num)
theorem B2017205 : Blo 892572 2017205 := bbase (se 5 (by rfl) ⟨94556, by rfl⟩ : syracuseStep 2017205 = 189113) (by norm_num)
theorem B1132481 : Blo 892572 1132481 := bbase (se 2 (by rfl) ⟨424680, by rfl⟩ : syracuseStep 1132481 = 849361) (by norm_num)
theorem B1132537 : Blo 892572 1132537 := bbase (se 2 (by rfl) ⟨424701, by rfl⟩ : syracuseStep 1132537 = 849403) (by norm_num)
theorem B2017277 : Blo 892572 2017277 := bbase (se 3 (by rfl) ⟨378239, by rfl⟩ : syracuseStep 2017277 = 756479) (by norm_num)
theorem B6113333 : Blo 892572 6113333 := bbase (se 5 (by rfl) ⟨286562, by rfl⟩ : syracuseStep 6113333 = 573125) (by norm_num)
theorem B1132633 : Blo 892572 1132633 := bbase (se 2 (by rfl) ⟨424737, by rfl⟩ : syracuseStep 1132633 = 849475) (by norm_num)
theorem B1722485 : Blo 892572 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B3262693 : Blo 892572 3262693 := bbase (se 4 (by rfl) ⟨305877, by rfl⟩ : syracuseStep 3262693 = 611755) (by norm_num)
theorem B968941 : Blo 892572 968941 := bbase (se 3 (by rfl) ⟨181676, by rfl⟩ : syracuseStep 968941 = 363353) (by norm_num)
theorem B1132805 : Blo 892572 1132805 := bbase (se 4 (by rfl) ⟨106200, by rfl⟩ : syracuseStep 1132805 = 212401) (by norm_num)
theorem B1362205 : Blo 892572 1362205 := bbase (se 3 (by rfl) ⟨255413, by rfl⟩ : syracuseStep 1362205 = 510827) (by norm_num)
theorem B3393845 : Blo 892572 3393845 := bbase (se 5 (by rfl) ⟨159086, by rfl⟩ : syracuseStep 3393845 = 318173) (by norm_num)
theorem B1132861 : Blo 892572 1132861 := bbase (se 3 (by rfl) ⟨212411, by rfl⟩ : syracuseStep 1132861 = 424823) (by norm_num)
theorem B2148677 : Blo 892572 2148677 := bbase (se 4 (by rfl) ⟨201438, by rfl⟩ : syracuseStep 2148677 = 402877) (by norm_num)
theorem B1132957 : Blo 892572 1132957 := bbase (se 3 (by rfl) ⟨212429, by rfl⟩ : syracuseStep 1132957 = 424859) (by norm_num)
theorem B2148773 : Blo 892572 2148773 := bbase (se 4 (by rfl) ⟨201447, by rfl⟩ : syracuseStep 2148773 = 402895) (by norm_num)
theorem B3230165 : Blo 892572 3230165 := bbase (se 7 (by rfl) ⟨37853, by rfl⟩ : syracuseStep 3230165 = 75707) (by norm_num)
theorem B1133129 : Blo 892572 1133129 := bbase (se 2 (by rfl) ⟨424923, by rfl⟩ : syracuseStep 1133129 = 849847) (by norm_num)
theorem B3394133 : Blo 892572 3394133 := bbase (se 8 (by rfl) ⟨19887, by rfl⟩ : syracuseStep 3394133 = 39775) (by norm_num)
theorem B1133185 : Blo 892572 1133185 := bbase (se 2 (by rfl) ⟨424944, by rfl⟩ : syracuseStep 1133185 = 849889) (by norm_num)
theorem B2542229 : Blo 892572 2542229 := bbase (se 6 (by rfl) ⟨59583, by rfl⟩ : syracuseStep 2542229 = 119167) (by norm_num)
theorem B1133281 : Blo 892572 1133281 := bbase (se 2 (by rfl) ⟨424980, by rfl⟩ : syracuseStep 1133281 = 849961) (by norm_num)
theorem B5098261 : Blo 892572 5098261 := bbase (se 6 (by rfl) ⟨119490, by rfl⟩ : syracuseStep 5098261 = 238981) (by norm_num)
theorem B1035101 : Blo 892572 1035101 := bbase (se 3 (by rfl) ⟨194081, by rfl⟩ : syracuseStep 1035101 = 388163) (by norm_num)
theorem B1133453 : Blo 892572 1133453 := bbase (se 3 (by rfl) ⟨212522, by rfl⟩ : syracuseStep 1133453 = 425045) (by norm_num)
theorem B6441877 : Blo 892572 6441877 := bbase (se 6 (by rfl) ⟨150981, by rfl⟩ : syracuseStep 6441877 = 301963) (by norm_num)
theorem B1133509 : Blo 892572 1133509 := bbase (se 4 (by rfl) ⟨106266, by rfl⟩ : syracuseStep 1133509 = 212533) (by norm_num)
theorem B8604629 : Blo 892572 8604629 := bbase (se 7 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 8604629 = 201671) (by norm_num)
theorem B1133605 : Blo 892572 1133605 := bbase (se 4 (by rfl) ⟨106275, by rfl⟩ : syracuseStep 1133605 = 212551) (by norm_num)
theorem B2542661 : Blo 892572 2542661 := bbase (se 4 (by rfl) ⟨238374, by rfl⟩ : syracuseStep 2542661 = 476749) (by norm_num)
theorem B1526933 : Blo 892572 1526933 := bbase (se 6 (by rfl) ⟨35787, by rfl⟩ : syracuseStep 1526933 = 71575) (by norm_num)
theorem B1133777 : Blo 892572 1133777 := bbase (se 2 (by rfl) ⟨425166, by rfl⟩ : syracuseStep 1133777 = 850333) (by norm_num)
theorem B3067109 : Blo 892572 3067109 := bbase (se 4 (by rfl) ⟨287541, by rfl⟩ : syracuseStep 3067109 = 575083) (by norm_num)
theorem B1133833 : Blo 892572 1133833 := bbase (se 2 (by rfl) ⟨425187, by rfl⟩ : syracuseStep 1133833 = 850375) (by norm_num)
theorem B1723685 : Blo 892572 1723685 := bbase (se 4 (by rfl) ⟨161595, by rfl⟩ : syracuseStep 1723685 = 323191) (by norm_num)
theorem B113397077 : Blo 892572 113397077 := bbase (se 11 (by rfl) ⟨83054, by rfl⟩ : syracuseStep 113397077 = 166109) (by norm_num)
theorem B1133929 : Blo 892572 1133929 := bbase (se 2 (by rfl) ⟨425223, by rfl⟩ : syracuseStep 1133929 = 850447) (by norm_num)
theorem B1134101 : Blo 892572 1134101 := bbase (se 6 (by rfl) ⟨26580, by rfl⟩ : syracuseStep 1134101 = 53161) (by norm_num)
theorem B1134157 : Blo 892572 1134157 := bbase (se 3 (by rfl) ⟨212654, by rfl⟩ : syracuseStep 1134157 = 425309) (by norm_num)
theorem B3624533 : Blo 892572 3624533 := bbase (se 8 (by rfl) ⟨21237, by rfl⟩ : syracuseStep 3624533 = 42475) (by norm_num)
theorem B1134253 : Blo 892572 1134253 := bbase (se 3 (by rfl) ⟨212672, by rfl⟩ : syracuseStep 1134253 = 425345) (by norm_num)
theorem B3395317 : Blo 892572 3395317 := bbase (se 5 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 3395317 = 318311) (by norm_num)
theorem B3624725 : Blo 892572 3624725 := bbase (se 6 (by rfl) ⟨84954, by rfl⟩ : syracuseStep 3624725 = 169909) (by norm_num)
theorem B2543413 : Blo 892572 2543413 := bbase (se 5 (by rfl) ⟨119222, by rfl⟩ : syracuseStep 2543413 = 238445) (by norm_num)
theorem B4083509 : Blo 892572 4083509 := bbase (se 5 (by rfl) ⟨191414, by rfl⟩ : syracuseStep 4083509 = 382829) (by norm_num)
theorem B5820245 : Blo 892572 5820245 := bbase (se 9 (by rfl) ⟨17051, by rfl⟩ : syracuseStep 5820245 = 34103) (by norm_num)
theorem B1134425 : Blo 892572 1134425 := bbase (se 2 (by rfl) ⟨425409, by rfl⟩ : syracuseStep 1134425 = 850819) (by norm_num)
theorem B1134481 : Blo 892572 1134481 := bbase (se 2 (by rfl) ⟨425430, by rfl⟩ : syracuseStep 1134481 = 850861) (by norm_num)
theorem B3821509 : Blo 892572 3821509 := bbase (se 4 (by rfl) ⟨358266, by rfl⟩ : syracuseStep 3821509 = 716533) (by norm_num)
theorem B905185 : Blo 892572 905185 := bbase (se 2 (by rfl) ⟨339444, by rfl⟩ : syracuseStep 905185 = 678889) (by norm_num)
theorem B1134577 : Blo 892572 1134577 := bbase (se 2 (by rfl) ⟨425466, by rfl⟩ : syracuseStep 1134577 = 850933) (by norm_num)
theorem B3395621 : Blo 892572 3395621 := bbase (se 4 (by rfl) ⟨318339, by rfl⟩ : syracuseStep 3395621 = 636679) (by norm_num)
theorem B2871413 : Blo 892572 2871413 := bbase (se 5 (by rfl) ⟨134597, by rfl⟩ : syracuseStep 2871413 = 269195) (by norm_num)
theorem B2412677 : Blo 892572 2412677 := bbase (se 4 (by rfl) ⟨226188, by rfl⟩ : syracuseStep 2412677 = 452377) (by norm_num)
theorem B1101961 : Blo 892572 1101961 := bbase (se 2 (by rfl) ⟨413235, by rfl⟩ : syracuseStep 1101961 = 826471) (by norm_num)
theorem B1528141 : Blo 892572 1528141 := bbase (se 3 (by rfl) ⟨286526, by rfl⟩ : syracuseStep 1528141 = 573053) (by norm_num)
theorem B2150869 : Blo 892572 2150869 := bbase (se 7 (by rfl) ⟨25205, by rfl⟩ : syracuseStep 2150869 = 50411) (by norm_num)
theorem B3494453 : Blo 892572 3494453 := bbase (se 5 (by rfl) ⟨163802, by rfl⟩ : syracuseStep 3494453 = 327605) (by norm_num)
theorem B1430093 : Blo 892572 1430093 := bbase (se 3 (by rfl) ⟨268142, by rfl⟩ : syracuseStep 1430093 = 536285) (by norm_num)
theorem B1004161 : Blo 892572 1004161 := bbase (se 2 (by rfl) ⟨376560, by rfl⟩ : syracuseStep 1004161 = 753121) (by norm_num)
theorem B905873 : Blo 892572 905873 := bbase (se 2 (by rfl) ⟨339702, by rfl⟩ : syracuseStep 905873 = 679405) (by norm_num)
theorem B1004197 : Blo 892572 1004197 := bbase (se 4 (by rfl) ⟨94143, by rfl⟩ : syracuseStep 1004197 = 188287) (by norm_num)
theorem B1004233 : Blo 892572 1004233 := bbase (se 2 (by rfl) ⟨376587, by rfl⟩ : syracuseStep 1004233 = 753175) (by norm_num)
theorem B5100245 : Blo 892572 5100245 := bbase (se 7 (by rfl) ⟨59768, by rfl⟩ : syracuseStep 5100245 = 119537) (by norm_num)
theorem B1004269 : Blo 892572 1004269 := bbase (se 3 (by rfl) ⟨188300, by rfl⟩ : syracuseStep 1004269 = 376601) (by norm_num)
theorem B1004305 : Blo 892572 1004305 := bbase (se 2 (by rfl) ⟨376614, by rfl⟩ : syracuseStep 1004305 = 753229) (by norm_num)
theorem B1430293 : Blo 892572 1430293 := bbase (se 6 (by rfl) ⟨33522, by rfl⟩ : syracuseStep 1430293 = 67045) (by norm_num)
theorem B1004341 : Blo 892572 1004341 := bbase (se 5 (by rfl) ⟨47078, by rfl⟩ : syracuseStep 1004341 = 94157) (by norm_num)
theorem B1004377 : Blo 892572 1004377 := bbase (se 2 (by rfl) ⟨376641, by rfl⟩ : syracuseStep 1004377 = 753283) (by norm_num)
theorem B2872181 : Blo 892572 2872181 := bbase (se 5 (by rfl) ⟨134633, by rfl⟩ : syracuseStep 2872181 = 269267) (by norm_num)
theorem B1004413 : Blo 892572 1004413 := bbase (se 3 (by rfl) ⟨188327, by rfl⟩ : syracuseStep 1004413 = 376655) (by norm_num)
theorem B1004449 : Blo 892572 1004449 := bbase (se 2 (by rfl) ⟨376668, by rfl⟩ : syracuseStep 1004449 = 753337) (by norm_num)
theorem B1004485 : Blo 892572 1004485 := bbase (se 4 (by rfl) ⟨94170, by rfl⟩ : syracuseStep 1004485 = 188341) (by norm_num)
theorem B1004521 : Blo 892572 1004521 := bbase (se 2 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 1004521 = 753391) (by norm_num)
theorem B1004557 : Blo 892572 1004557 := bbase (se 3 (by rfl) ⟨188354, by rfl⟩ : syracuseStep 1004557 = 376709) (by norm_num)
theorem B1430549 : Blo 892572 1430549 := bbase (se 6 (by rfl) ⟨33528, by rfl⟩ : syracuseStep 1430549 = 67057) (by norm_num)
theorem B11457557 : Blo 892572 11457557 := bbase (se 6 (by rfl) ⟨268536, by rfl⟩ : syracuseStep 11457557 = 537073) (by norm_num)
theorem B1004593 : Blo 892572 1004593 := bbase (se 2 (by rfl) ⟨376722, by rfl⟩ : syracuseStep 1004593 = 753445) (by norm_num)
theorem B2151485 : Blo 892572 2151485 := bbase (se 3 (by rfl) ⟨403403, by rfl⟩ : syracuseStep 2151485 = 806807) (by norm_num)
theorem B1004629 : Blo 892572 1004629 := bbase (se 8 (by rfl) ⟨5886, by rfl⟩ : syracuseStep 1004629 = 11773) (by norm_num)
theorem B1004665 : Blo 892572 1004665 := bbase (se 2 (by rfl) ⟨376749, by rfl⟩ : syracuseStep 1004665 = 753499) (by norm_num)
theorem B1004701 : Blo 892572 1004701 := bbase (se 3 (by rfl) ⟨188381, by rfl⟩ : syracuseStep 1004701 = 376763) (by norm_num)
theorem B1004737 : Blo 892572 1004737 := bbase (se 2 (by rfl) ⟨376776, by rfl⟩ : syracuseStep 1004737 = 753553) (by norm_num)
theorem B1004773 : Blo 892572 1004773 := bbase (se 4 (by rfl) ⟨94197, by rfl⟩ : syracuseStep 1004773 = 188395) (by norm_num)
theorem B1004809 : Blo 892572 1004809 := bbase (se 2 (by rfl) ⟨376803, by rfl⟩ : syracuseStep 1004809 = 753607) (by norm_num)
theorem B1004845 : Blo 892572 1004845 := bbase (se 3 (by rfl) ⟨188408, by rfl⟩ : syracuseStep 1004845 = 376817) (by norm_num)
theorem B1004881 : Blo 892572 1004881 := bbase (se 2 (by rfl) ⟨376830, by rfl⟩ : syracuseStep 1004881 = 753661) (by norm_num)
theorem B1004917 : Blo 892572 1004917 := bbase (se 5 (by rfl) ⟨47105, by rfl⟩ : syracuseStep 1004917 = 94211) (by norm_num)
theorem B7853429 : Blo 892572 7853429 := bbase (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) (by norm_num)
theorem B2151821 : Blo 892572 2151821 := bbase (se 3 (by rfl) ⟨403466, by rfl⟩ : syracuseStep 2151821 = 806933) (by norm_num)
theorem B3822997 : Blo 892572 3822997 := bbase (se 6 (by rfl) ⟨89601, by rfl⟩ : syracuseStep 3822997 = 179203) (by norm_num)
theorem B1004953 : Blo 892572 1004953 := bbase (se 2 (by rfl) ⟨376857, by rfl⟩ : syracuseStep 1004953 = 753715) (by norm_num)
theorem B3823013 : Blo 892572 3823013 := bbase (se 4 (by rfl) ⟨358407, by rfl⟩ : syracuseStep 3823013 = 716815) (by norm_num)
theorem B1004989 : Blo 892572 1004989 := bbase (se 3 (by rfl) ⟨188435, by rfl⟩ : syracuseStep 1004989 = 376871) (by norm_num)
theorem B1005025 : Blo 892572 1005025 := bbase (se 2 (by rfl) ⟨376884, by rfl⟩ : syracuseStep 1005025 = 753769) (by norm_num)
theorem B1005061 : Blo 892572 1005061 := bbase (se 4 (by rfl) ⟨94224, by rfl⟩ : syracuseStep 1005061 = 188449) (by norm_num)
theorem B1005097 : Blo 892572 1005097 := bbase (se 2 (by rfl) ⟨376911, by rfl⟩ : syracuseStep 1005097 = 753823) (by norm_num)
theorem B1005133 : Blo 892572 1005133 := bbase (se 3 (by rfl) ⟨188462, by rfl⟩ : syracuseStep 1005133 = 376925) (by norm_num)
theorem B1005169 : Blo 892572 1005169 := bbase (se 2 (by rfl) ⟨376938, by rfl⟩ : syracuseStep 1005169 = 753877) (by norm_num)
theorem B1005205 : Blo 892572 1005205 := bbase (se 6 (by rfl) ⟨23559, by rfl⟩ : syracuseStep 1005205 = 47119) (by norm_num)
theorem B1005241 : Blo 892572 1005241 := bbase (se 2 (by rfl) ⟨376965, by rfl⟩ : syracuseStep 1005241 = 753931) (by norm_num)
theorem B1005277 : Blo 892572 1005277 := bbase (se 3 (by rfl) ⟨188489, by rfl⟩ : syracuseStep 1005277 = 376979) (by norm_num)
theorem B1005313 : Blo 892572 1005313 := bbase (se 2 (by rfl) ⟨376992, by rfl⟩ : syracuseStep 1005313 = 753985) (by norm_num)
theorem B2152213 : Blo 892572 2152213 := bbase (se 6 (by rfl) ⟨50442, by rfl⟩ : syracuseStep 2152213 = 100885) (by norm_num)
theorem B1005349 : Blo 892572 1005349 := bbase (se 4 (by rfl) ⟨94251, by rfl⟩ : syracuseStep 1005349 = 188503) (by norm_num)
theorem B907057 : Blo 892572 907057 := bbase (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) (by norm_num)
theorem B1005385 : Blo 892572 1005385 := bbase (se 2 (by rfl) ⟨377019, by rfl⟩ : syracuseStep 1005385 = 754039) (by norm_num)
theorem B1005421 : Blo 892572 1005421 := bbase (se 3 (by rfl) ⟨188516, by rfl⟩ : syracuseStep 1005421 = 377033) (by norm_num)
theorem B1005457 : Blo 892572 1005457 := bbase (se 2 (by rfl) ⟨377046, by rfl⟩ : syracuseStep 1005457 = 754093) (by norm_num)
theorem B8148917 : Blo 892572 8148917 := bbase (se 5 (by rfl) ⟨381980, by rfl⟩ : syracuseStep 8148917 = 763961) (by norm_num)
theorem B1005493 : Blo 892572 1005493 := bbase (se 5 (by rfl) ⟨47132, by rfl⟩ : syracuseStep 1005493 = 94265) (by norm_num)
theorem B1005529 : Blo 892572 1005529 := bbase (se 2 (by rfl) ⟨377073, by rfl⟩ : syracuseStep 1005529 = 754147) (by norm_num)
theorem B1005565 : Blo 892572 1005565 := bbase (se 3 (by rfl) ⟨188543, by rfl⟩ : syracuseStep 1005565 = 377087) (by norm_num)
theorem B1005601 : Blo 892572 1005601 := bbase (se 2 (by rfl) ⟨377100, by rfl⟩ : syracuseStep 1005601 = 754201) (by norm_num)
theorem B1005637 : Blo 892572 1005637 := bbase (se 4 (by rfl) ⟨94278, by rfl⟩ : syracuseStep 1005637 = 188557) (by norm_num)
theorem B3397733 : Blo 892572 3397733 := bbase (se 4 (by rfl) ⟨318537, by rfl⟩ : syracuseStep 3397733 = 637075) (by norm_num)
theorem B1005673 : Blo 892572 1005673 := bbase (se 2 (by rfl) ⟨377127, by rfl⟩ : syracuseStep 1005673 = 754255) (by norm_num)
theorem B1431677 : Blo 892572 1431677 := bbase (se 3 (by rfl) ⟨268439, by rfl⟩ : syracuseStep 1431677 = 536879) (by norm_num)
theorem B1005709 : Blo 892572 1005709 := bbase (se 3 (by rfl) ⟨188570, by rfl⟩ : syracuseStep 1005709 = 377141) (by norm_num)
theorem B1005745 : Blo 892572 1005745 := bbase (se 2 (by rfl) ⟨377154, by rfl⟩ : syracuseStep 1005745 = 754309) (by norm_num)
theorem B1005781 : Blo 892572 1005781 := bbase (se 7 (by rfl) ⟨11786, by rfl⟩ : syracuseStep 1005781 = 23573) (by norm_num)
theorem B1530085 : Blo 892572 1530085 := bbase (se 4 (by rfl) ⟨143445, by rfl⟩ : syracuseStep 1530085 = 286891) (by norm_num)
theorem B1005817 : Blo 892572 1005817 := bbase (se 2 (by rfl) ⟨377181, by rfl⟩ : syracuseStep 1005817 = 754363) (by norm_num)
theorem B1005853 : Blo 892572 1005853 := bbase (se 3 (by rfl) ⟨188597, by rfl⟩ : syracuseStep 1005853 = 377195) (by norm_num)
theorem B1136941 : Blo 892572 1136941 := bbase (se 3 (by rfl) ⟨213176, by rfl⟩ : syracuseStep 1136941 = 426353) (by norm_num)
theorem B1005889 : Blo 892572 1005889 := bbase (se 2 (by rfl) ⟨377208, by rfl⟩ : syracuseStep 1005889 = 754417) (by norm_num)
theorem B1530181 : Blo 892572 1530181 := bbase (se 4 (by rfl) ⟨143454, by rfl⟩ : syracuseStep 1530181 = 286909) (by norm_num)
theorem B1005925 : Blo 892572 1005925 := bbase (se 4 (by rfl) ⟨94305, by rfl⟩ : syracuseStep 1005925 = 188611) (by norm_num)
theorem B3398021 : Blo 892572 3398021 := bbase (se 4 (by rfl) ⟨318564, by rfl⟩ : syracuseStep 3398021 = 637129) (by norm_num)
theorem B1005961 : Blo 892572 1005961 := bbase (se 2 (by rfl) ⟨377235, by rfl⟩ : syracuseStep 1005961 = 754471) (by norm_num)
theorem B1005997 : Blo 892572 1005997 := bbase (se 3 (by rfl) ⟨188624, by rfl⟩ : syracuseStep 1005997 = 377249) (by norm_num)
theorem B1006033 : Blo 892572 1006033 := bbase (se 2 (by rfl) ⟨377262, by rfl⟩ : syracuseStep 1006033 = 754525) (by norm_num)
theorem B3496405 : Blo 892572 3496405 := bbase (se 7 (by rfl) ⟨40973, by rfl⟩ : syracuseStep 3496405 = 81947) (by norm_num)
theorem B1006069 : Blo 892572 1006069 := bbase (se 5 (by rfl) ⟨47159, by rfl⟩ : syracuseStep 1006069 = 94319) (by norm_num)
theorem B1006105 : Blo 892572 1006105 := bbase (se 2 (by rfl) ⟨377289, by rfl⟩ : syracuseStep 1006105 = 754579) (by norm_num)
theorem B1006141 : Blo 892572 1006141 := bbase (se 3 (by rfl) ⟨188651, by rfl⟩ : syracuseStep 1006141 = 377303) (by norm_num)
theorem B2546261 : Blo 892572 2546261 := bbase (se 8 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 2546261 = 29839) (by norm_num)
theorem B1006177 : Blo 892572 1006177 := bbase (se 2 (by rfl) ⟨377316, by rfl⟩ : syracuseStep 1006177 = 754633) (by norm_num)
theorem B1432189 : Blo 892572 1432189 := bbase (se 3 (by rfl) ⟨268535, by rfl⟩ : syracuseStep 1432189 = 537071) (by norm_num)
theorem B1006213 : Blo 892572 1006213 := bbase (se 4 (by rfl) ⟨94332, by rfl⟩ : syracuseStep 1006213 = 188665) (by norm_num)
theorem B1006249 : Blo 892572 1006249 := bbase (se 2 (by rfl) ⟨377343, by rfl⟩ : syracuseStep 1006249 = 754687) (by norm_num)
theorem B1006285 : Blo 892572 1006285 := bbase (se 3 (by rfl) ⟨188678, by rfl⟩ : syracuseStep 1006285 = 377357) (by norm_num)
theorem B1006321 : Blo 892572 1006321 := bbase (se 2 (by rfl) ⟨377370, by rfl⟩ : syracuseStep 1006321 = 754741) (by norm_num)
theorem B1006357 : Blo 892572 1006357 := bbase (se 6 (by rfl) ⟨23586, by rfl⟩ : syracuseStep 1006357 = 47173) (by norm_num)
theorem B1006393 : Blo 892572 1006393 := bbase (se 2 (by rfl) ⟨377397, by rfl⟩ : syracuseStep 1006393 = 754795) (by norm_num)
theorem B1006429 : Blo 892572 1006429 := bbase (se 3 (by rfl) ⟨188705, by rfl⟩ : syracuseStep 1006429 = 377411) (by norm_num)
theorem B5102453 : Blo 892572 5102453 := bbase (se 5 (by rfl) ⟨239177, by rfl⟩ : syracuseStep 5102453 = 478355) (by norm_num)
theorem B1006465 : Blo 892572 1006465 := bbase (se 2 (by rfl) ⟨377424, by rfl⟩ : syracuseStep 1006465 = 754849) (by norm_num)
theorem B1694621 : Blo 892572 1694621 := bbase (se 3 (by rfl) ⟨317741, by rfl⟩ : syracuseStep 1694621 = 635483) (by norm_num)
theorem B1006501 : Blo 892572 1006501 := bbase (se 4 (by rfl) ⟨94359, by rfl⟩ : syracuseStep 1006501 = 188719) (by norm_num)
theorem B908209 : Blo 892572 908209 := bbase (se 2 (by rfl) ⟨340578, by rfl⟩ : syracuseStep 908209 = 681157) (by norm_num)
theorem B1006537 : Blo 892572 1006537 := bbase (se 2 (by rfl) ⟨377451, by rfl⟩ : syracuseStep 1006537 = 754903) (by norm_num)
theorem B1006573 : Blo 892572 1006573 := bbase (se 3 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 1006573 = 377465) (by norm_num)
theorem B1006609 : Blo 892572 1006609 := bbase (se 2 (by rfl) ⟨377478, by rfl⟩ : syracuseStep 1006609 = 754957) (by norm_num)
theorem B1694773 : Blo 892572 1694773 := bbase (se 5 (by rfl) ⟨79442, by rfl⟩ : syracuseStep 1694773 = 158885) (by norm_num)
theorem B1006645 : Blo 892572 1006645 := bbase (se 5 (by rfl) ⟨47186, by rfl⟩ : syracuseStep 1006645 = 94373) (by norm_num)
theorem B1006681 : Blo 892572 1006681 := bbase (se 2 (by rfl) ⟨377505, by rfl⟩ : syracuseStep 1006681 = 755011) (by norm_num)
theorem B1006717 : Blo 892572 1006717 := bbase (se 3 (by rfl) ⟨188759, by rfl⟩ : syracuseStep 1006717 = 377519) (by norm_num)
theorem B3628165 : Blo 892572 3628165 := bbase (se 4 (by rfl) ⟨340140, by rfl⟩ : syracuseStep 3628165 = 680281) (by norm_num)
theorem B1432733 : Blo 892572 1432733 := bbase (se 3 (by rfl) ⟨268637, by rfl⟩ : syracuseStep 1432733 = 537275) (by norm_num)
theorem B1006753 : Blo 892572 1006753 := bbase (se 2 (by rfl) ⟨377532, by rfl⟩ : syracuseStep 1006753 = 755065) (by norm_num)
theorem B2415781 : Blo 892572 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B1006789 : Blo 892572 1006789 := bbase (se 4 (by rfl) ⟨94386, by rfl⟩ : syracuseStep 1006789 = 188773) (by norm_num)
theorem B15260885 : Blo 892572 15260885 := bbase (se 7 (by rfl) ⟨178838, by rfl⟩ : syracuseStep 15260885 = 357677) (by norm_num)
theorem B1006825 : Blo 892572 1006825 := bbase (se 2 (by rfl) ⟨377559, by rfl⟩ : syracuseStep 1006825 = 755119) (by norm_num)
theorem B1072397 : Blo 892572 1072397 := bbase (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) (by norm_num)
theorem B1006861 : Blo 892572 1006861 := bbase (se 3 (by rfl) ⟨188786, by rfl⟩ : syracuseStep 1006861 = 377573) (by norm_num)
theorem B1006897 : Blo 892572 1006897 := bbase (se 2 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 1006897 = 755173) (by norm_num)
theorem B1989965 : Blo 892572 1989965 := bbase (se 3 (by rfl) ⟨373118, by rfl⟩ : syracuseStep 1989965 = 746237) (by norm_num)
theorem B1006933 : Blo 892572 1006933 := bbase (se 11 (by rfl) ⟨737, by rfl⟩ : syracuseStep 1006933 = 1475) (by norm_num)
theorem B1695077 : Blo 892572 1695077 := bbase (se 4 (by rfl) ⟨158913, by rfl⟩ : syracuseStep 1695077 = 317827) (by norm_num)
theorem B1006969 : Blo 892572 1006969 := bbase (se 2 (by rfl) ⟨377613, by rfl⟩ : syracuseStep 1006969 = 755227) (by norm_num)
theorem B1007005 : Blo 892572 1007005 := bbase (se 3 (by rfl) ⟨188813, by rfl⟩ : syracuseStep 1007005 = 377627) (by norm_num)
theorem B1007041 : Blo 892572 1007041 := bbase (se 2 (by rfl) ⟨377640, by rfl⟩ : syracuseStep 1007041 = 755281) (by norm_num)
theorem B1007077 : Blo 892572 1007077 := bbase (se 4 (by rfl) ⟨94413, by rfl⟩ : syracuseStep 1007077 = 188827) (by norm_num)
theorem B1007113 : Blo 892572 1007113 := bbase (se 2 (by rfl) ⟨377667, by rfl⟩ : syracuseStep 1007113 = 755335) (by norm_num)
theorem B3399205 : Blo 892572 3399205 := bbase (se 4 (by rfl) ⟨318675, by rfl⟩ : syracuseStep 3399205 = 637351) (by norm_num)
theorem B1007149 : Blo 892572 1007149 := bbase (se 3 (by rfl) ⟨188840, by rfl⟩ : syracuseStep 1007149 = 377681) (by norm_num)
theorem B1072705 : Blo 892572 1072705 := bbase (se 2 (by rfl) ⟨402264, by rfl⟩ : syracuseStep 1072705 = 804529) (by norm_num)
theorem B1007185 : Blo 892572 1007185 := bbase (se 2 (by rfl) ⟨377694, by rfl⟩ : syracuseStep 1007185 = 755389) (by norm_num)
theorem B6872693 : Blo 892572 6872693 := bbase (se 5 (by rfl) ⟨322157, by rfl⟩ : syracuseStep 6872693 = 644315) (by norm_num)
theorem B1007221 : Blo 892572 1007221 := bbase (se 5 (by rfl) ⟨47213, by rfl⟩ : syracuseStep 1007221 = 94427) (by norm_num)
theorem B3825269 : Blo 892572 3825269 := bbase (se 5 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 3825269 = 358619) (by norm_num)
theorem B1007257 : Blo 892572 1007257 := bbase (se 2 (by rfl) ⟨377721, by rfl⟩ : syracuseStep 1007257 = 755443) (by norm_num)
theorem B1072801 : Blo 892572 1072801 := bbase (se 2 (by rfl) ⟨402300, by rfl⟩ : syracuseStep 1072801 = 804601) (by norm_num)
theorem B1007293 : Blo 892572 1007293 := bbase (se 3 (by rfl) ⟨188867, by rfl⟩ : syracuseStep 1007293 = 377735) (by norm_num)
theorem B1433285 : Blo 892572 1433285 := bbase (se 4 (by rfl) ⟨134370, by rfl⟩ : syracuseStep 1433285 = 268741) (by norm_num)
theorem B1072849 : Blo 892572 1072849 := bbase (se 2 (by rfl) ⟨402318, by rfl⟩ : syracuseStep 1072849 = 804637) (by norm_num)
theorem B1007329 : Blo 892572 1007329 := bbase (se 2 (by rfl) ⟨377748, by rfl⟩ : syracuseStep 1007329 = 755497) (by norm_num)
theorem B1433317 : Blo 892572 1433317 := bbase (se 4 (by rfl) ⟨134373, by rfl⟩ : syracuseStep 1433317 = 268747) (by norm_num)
theorem B2547445 : Blo 892572 2547445 := bbase (se 5 (by rfl) ⟨119411, by rfl⟩ : syracuseStep 2547445 = 238823) (by norm_num)
theorem B1007365 : Blo 892572 1007365 := bbase (se 4 (by rfl) ⟨94440, by rfl⟩ : syracuseStep 1007365 = 188881) (by norm_num)
theorem B1007401 : Blo 892572 1007401 := bbase (se 2 (by rfl) ⟨377775, by rfl⟩ : syracuseStep 1007401 = 755551) (by norm_num)
theorem B7757621 : Blo 892572 7757621 := bbase (se 5 (by rfl) ⟨363638, by rfl⟩ : syracuseStep 7757621 = 727277) (by norm_num)
theorem B1007437 : Blo 892572 1007437 := bbase (se 3 (by rfl) ⟨188894, by rfl⟩ : syracuseStep 1007437 = 377789) (by norm_num)
theorem B3399509 : Blo 892572 3399509 := bbase (se 9 (by rfl) ⟨9959, by rfl⟩ : syracuseStep 3399509 = 19919) (by norm_num)
theorem B1007473 : Blo 892572 1007473 := bbase (se 2 (by rfl) ⟨377802, by rfl⟩ : syracuseStep 1007473 = 755605) (by norm_num)
theorem B2547605 : Blo 892572 2547605 := bbase (se 6 (by rfl) ⟨59709, by rfl⟩ : syracuseStep 2547605 = 119419) (by norm_num)
theorem B1007509 : Blo 892572 1007509 := bbase (se 6 (by rfl) ⟨23613, by rfl⟩ : syracuseStep 1007509 = 47227) (by norm_num)
theorem B1007545 : Blo 892572 1007545 := bbase (se 2 (by rfl) ⟨377829, by rfl⟩ : syracuseStep 1007545 = 755659) (by norm_num)
theorem B10346453 : Blo 892572 10346453 := bbase (se 7 (by rfl) ⟨121247, by rfl⟩ : syracuseStep 10346453 = 242495) (by norm_num)
theorem B1007581 : Blo 892572 1007581 := bbase (se 3 (by rfl) ⟨188921, by rfl⟩ : syracuseStep 1007581 = 377843) (by norm_num)
theorem B1007617 : Blo 892572 1007617 := bbase (se 2 (by rfl) ⟨377856, by rfl⟩ : syracuseStep 1007617 = 755713) (by norm_num)
theorem B1007653 : Blo 892572 1007653 := bbase (se 4 (by rfl) ⟨94467, by rfl⟩ : syracuseStep 1007653 = 188935) (by norm_num)
theorem B1531973 : Blo 892572 1531973 := bbase (se 4 (by rfl) ⟨143622, by rfl⟩ : syracuseStep 1531973 = 287245) (by norm_num)
theorem B1007689 : Blo 892572 1007689 := bbase (se 2 (by rfl) ⟨377883, by rfl⟩ : syracuseStep 1007689 = 755767) (by norm_num)
theorem B1695829 : Blo 892572 1695829 := bbase (se 8 (by rfl) ⟨9936, by rfl⟩ : syracuseStep 1695829 = 19873) (by norm_num)
theorem B1007725 : Blo 892572 1007725 := bbase (se 3 (by rfl) ⟨188948, by rfl⟩ : syracuseStep 1007725 = 377897) (by norm_num)
theorem B2547845 : Blo 892572 2547845 := bbase (se 4 (by rfl) ⟨238860, by rfl⟩ : syracuseStep 2547845 = 477721) (by norm_num)
theorem B1007761 : Blo 892572 1007761 := bbase (se 2 (by rfl) ⟨377910, by rfl⟩ : syracuseStep 1007761 = 755821) (by norm_num)
theorem B5431445 : Blo 892572 5431445 := bbase (se 6 (by rfl) ⟨127299, by rfl⟩ : syracuseStep 5431445 = 254599) (by norm_num)
theorem B8282293 : Blo 892572 8282293 := bbase (se 5 (by rfl) ⟨388232, by rfl⟩ : syracuseStep 8282293 = 776465) (by norm_num)
theorem B1007797 : Blo 892572 1007797 := bbase (se 5 (by rfl) ⟨47240, by rfl⟩ : syracuseStep 1007797 = 94481) (by norm_num)
theorem B1007833 : Blo 892572 1007833 := bbase (se 2 (by rfl) ⟨377937, by rfl⟩ : syracuseStep 1007833 = 755875) (by norm_num)
theorem B1695973 : Blo 892572 1695973 := bbase (se 4 (by rfl) ⟨158997, by rfl⟩ : syracuseStep 1695973 = 317995) (by norm_num)
theorem B1007869 : Blo 892572 1007869 := bbase (se 3 (by rfl) ⟨188975, by rfl⟩ : syracuseStep 1007869 = 377951) (by norm_num)
theorem B1007905 : Blo 892572 1007905 := bbase (se 2 (by rfl) ⟨377964, by rfl⟩ : syracuseStep 1007905 = 755929) (by norm_num)
theorem B6447413 : Blo 892572 6447413 := bbase (se 5 (by rfl) ⟨302222, by rfl⟩ : syracuseStep 6447413 = 604445) (by norm_num)
theorem B2548037 : Blo 892572 2548037 := bbase (se 4 (by rfl) ⟨238878, by rfl⟩ : syracuseStep 2548037 = 477757) (by norm_num)
theorem B1007941 : Blo 892572 1007941 := bbase (se 4 (by rfl) ⟨94494, by rfl⟩ : syracuseStep 1007941 = 188989) (by norm_num)
theorem B5431637 : Blo 892572 5431637 := bbase (se 10 (by rfl) ⟨7956, by rfl⟩ : syracuseStep 5431637 = 15913) (by norm_num)
theorem B1007977 : Blo 892572 1007977 := bbase (se 2 (by rfl) ⟨377991, by rfl⟩ : syracuseStep 1007977 = 755983) (by norm_num)
theorem B1696133 : Blo 892572 1696133 := bbase (se 4 (by rfl) ⟨159012, by rfl⟩ : syracuseStep 1696133 = 318025) (by norm_num)
theorem B1008013 : Blo 892572 1008013 := bbase (se 3 (by rfl) ⟨189002, by rfl⟩ : syracuseStep 1008013 = 378005) (by norm_num)
theorem B2417045 : Blo 892572 2417045 := bbase (se 6 (by rfl) ⟨56649, by rfl⟩ : syracuseStep 2417045 = 113299) (by norm_num)
theorem B1008049 : Blo 892572 1008049 := bbase (se 2 (by rfl) ⟨378018, by rfl⟩ : syracuseStep 1008049 = 756037) (by norm_num)
theorem B1008085 : Blo 892572 1008085 := bbase (se 7 (by rfl) ⟨11813, by rfl⟩ : syracuseStep 1008085 = 23627) (by norm_num)
theorem B1008121 : Blo 892572 1008121 := bbase (se 2 (by rfl) ⟨378045, by rfl⟩ : syracuseStep 1008121 = 756091) (by norm_num)
theorem B1696277 : Blo 892572 1696277 := bbase (se 6 (by rfl) ⟨39756, by rfl⟩ : syracuseStep 1696277 = 79513) (by norm_num)
theorem B1008157 : Blo 892572 1008157 := bbase (se 3 (by rfl) ⟨189029, by rfl⟩ : syracuseStep 1008157 = 378059) (by norm_num)
theorem B1008193 : Blo 892572 1008193 := bbase (se 2 (by rfl) ⟨378072, by rfl⟩ : syracuseStep 1008193 = 756145) (by norm_num)
theorem B1008229 : Blo 892572 1008229 := bbase (se 4 (by rfl) ⟨94521, by rfl⟩ : syracuseStep 1008229 = 189043) (by norm_num)
theorem B2417285 : Blo 892572 2417285 := bbase (se 4 (by rfl) ⟨226620, by rfl⟩ : syracuseStep 2417285 = 453241) (by norm_num)
theorem B1434245 : Blo 892572 1434245 := bbase (se 4 (by rfl) ⟨134460, by rfl⟩ : syracuseStep 1434245 = 268921) (by norm_num)
theorem B1008265 : Blo 892572 1008265 := bbase (se 2 (by rfl) ⟨378099, by rfl⟩ : syracuseStep 1008265 = 756199) (by norm_num)
theorem B1008301 : Blo 892572 1008301 := bbase (se 3 (by rfl) ⟨189056, by rfl⟩ : syracuseStep 1008301 = 378113) (by norm_num)
theorem B1008337 : Blo 892572 1008337 := bbase (se 2 (by rfl) ⟨378126, by rfl⟩ : syracuseStep 1008337 = 756253) (by norm_num)
theorem B5726933 : Blo 892572 5726933 := bbase (se 7 (by rfl) ⟨67112, by rfl⟩ : syracuseStep 5726933 = 134225) (by norm_num)
theorem B1532629 : Blo 892572 1532629 := bbase (se 7 (by rfl) ⟨17960, by rfl⟩ : syracuseStep 1532629 = 35921) (by norm_num)
theorem B1008373 : Blo 892572 1008373 := bbase (se 5 (by rfl) ⟨47267, by rfl⟩ : syracuseStep 1008373 = 94535) (by norm_num)
theorem B1008409 : Blo 892572 1008409 := bbase (se 2 (by rfl) ⟨378153, by rfl⟩ : syracuseStep 1008409 = 756307) (by norm_num)
theorem B1696565 : Blo 892572 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B1008445 : Blo 892572 1008445 := bbase (se 3 (by rfl) ⟨189083, by rfl⟩ : syracuseStep 1008445 = 378167) (by norm_num)
theorem B1008481 : Blo 892572 1008481 := bbase (se 2 (by rfl) ⟨378180, by rfl⟩ : syracuseStep 1008481 = 756361) (by norm_num)
theorem B1008517 : Blo 892572 1008517 := bbase (se 4 (by rfl) ⟨94548, by rfl⟩ : syracuseStep 1008517 = 189097) (by norm_num)
theorem B1074065 : Blo 892572 1074065 := bbase (se 2 (by rfl) ⟨402774, by rfl⟩ : syracuseStep 1074065 = 805549) (by norm_num)
theorem B1008553 : Blo 892572 1008553 := bbase (se 2 (by rfl) ⟨378207, by rfl⟩ : syracuseStep 1008553 = 756415) (by norm_num)
theorem B1696717 : Blo 892572 1696717 := bbase (se 3 (by rfl) ⟨318134, by rfl⟩ : syracuseStep 1696717 = 636269) (by norm_num)
theorem B1008589 : Blo 892572 1008589 := bbase (se 3 (by rfl) ⟨189110, by rfl⟩ : syracuseStep 1008589 = 378221) (by norm_num)
theorem B1008625 : Blo 892572 1008625 := bbase (se 2 (by rfl) ⟨378234, by rfl⟩ : syracuseStep 1008625 = 756469) (by norm_num)
theorem B2909189 : Blo 892572 2909189 := bbase (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) (by norm_num)
theorem B1074233 : Blo 892572 1074233 := bbase (se 2 (by rfl) ⟨402837, by rfl⟩ : syracuseStep 1074233 = 805675) (by norm_num)
theorem B1008697 : Blo 892572 1008697 := bbase (se 2 (by rfl) ⟨378261, by rfl⟩ : syracuseStep 1008697 = 756523) (by norm_num)
theorem B1697021 : Blo 892572 1697021 := bbase (se 3 (by rfl) ⟨318191, by rfl⟩ : syracuseStep 1697021 = 636383) (by norm_num)
theorem B2549029 : Blo 892572 2549029 := bbase (se 4 (by rfl) ⟨238971, by rfl⟩ : syracuseStep 2549029 = 477943) (by norm_num)
theorem B1434925 : Blo 892572 1434925 := bbase (se 3 (by rfl) ⟨269048, by rfl⟩ : syracuseStep 1434925 = 538097) (by norm_num)
theorem B1074541 : Blo 892572 1074541 := bbase (se 3 (by rfl) ⟨201476, by rfl⟩ : syracuseStep 1074541 = 402953) (by norm_num)
theorem B1434989 : Blo 892572 1434989 := bbase (se 3 (by rfl) ⟨269060, by rfl⟩ : syracuseStep 1434989 = 538121) (by norm_num)
theorem B1860989 : Blo 892572 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B2942453 : Blo 892572 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B1074757 : Blo 892572 1074757 := bbase (se 4 (by rfl) ⟨100758, by rfl⟩ : syracuseStep 1074757 = 201517) (by norm_num)
theorem B4351781 : Blo 892572 4351781 := bbase (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) (by norm_num)
theorem B1075069 : Blo 892572 1075069 := bbase (se 3 (by rfl) ⟨201575, by rfl⟩ : syracuseStep 1075069 = 403151) (by norm_num)
theorem B3401621 : Blo 892572 3401621 := bbase (se 6 (by rfl) ⟨79725, by rfl⟩ : syracuseStep 3401621 = 159451) (by norm_num)
theorem B1697773 : Blo 892572 1697773 := bbase (se 3 (by rfl) ⟨318332, by rfl⟩ : syracuseStep 1697773 = 636665) (by norm_num)
theorem B1960013 : Blo 892572 1960013 := bbase (se 3 (by rfl) ⟨367502, by rfl⟩ : syracuseStep 1960013 = 735005) (by norm_num)
theorem B1697917 : Blo 892572 1697917 := bbase (se 3 (by rfl) ⟨318359, by rfl⟩ : syracuseStep 1697917 = 636719) (by norm_num)
theorem B3401909 : Blo 892572 3401909 := bbase (se 5 (by rfl) ⟨159464, by rfl⟩ : syracuseStep 3401909 = 318929) (by norm_num)
theorem B1272037 : Blo 892572 1272037 := bbase (se 4 (by rfl) ⟨119253, by rfl⟩ : syracuseStep 1272037 = 238507) (by norm_num)
theorem B1698077 : Blo 892572 1698077 := bbase (se 3 (by rfl) ⟨318389, by rfl⟩ : syracuseStep 1698077 = 636779) (by norm_num)
theorem B2550133 : Blo 892572 2550133 := bbase (se 5 (by rfl) ⟨119537, by rfl⟩ : syracuseStep 2550133 = 239075) (by norm_num)
theorem B1206685 : Blo 892572 1206685 := bbase (se 3 (by rfl) ⟨226253, by rfl⟩ : syracuseStep 1206685 = 452507) (by norm_num)
theorem B1698221 : Blo 892572 1698221 := bbase (se 3 (by rfl) ⟨318416, by rfl⟩ : syracuseStep 1698221 = 636833) (by norm_num)
theorem B1698509 : Blo 892572 1698509 := bbase (se 3 (by rfl) ⟨318470, by rfl⟩ : syracuseStep 1698509 = 636941) (by norm_num)
theorem B1272629 : Blo 892572 1272629 := bbase (se 5 (by rfl) ⟨59654, by rfl⟩ : syracuseStep 1272629 = 119309) (by norm_num)
theorem B1698661 : Blo 892572 1698661 := bbase (se 4 (by rfl) ⟨159249, by rfl⟩ : syracuseStep 1698661 = 318499) (by norm_num)
theorem B1272709 : Blo 892572 1272709 := bbase (se 4 (by rfl) ⟨119316, by rfl⟩ : syracuseStep 1272709 = 238633) (by norm_num)
theorem B1272829 : Blo 892572 1272829 := bbase (se 3 (by rfl) ⟨238655, by rfl⟩ : syracuseStep 1272829 = 477311) (by norm_num)
theorem B1272925 : Blo 892572 1272925 := bbase (se 3 (by rfl) ⟨238673, by rfl⟩ : syracuseStep 1272925 = 477347) (by norm_num)
theorem B2419813 : Blo 892572 2419813 := bbase (se 4 (by rfl) ⟨226857, by rfl⟩ : syracuseStep 2419813 = 453715) (by norm_num)
theorem B945265 : Blo 892572 945265 := bbase (se 2 (by rfl) ⟨354474, by rfl⟩ : syracuseStep 945265 = 708949) (by norm_num)
theorem B1961093 : Blo 892572 1961093 := bbase (se 4 (by rfl) ⟨183852, by rfl⟩ : syracuseStep 1961093 = 367705) (by norm_num)
theorem B1698965 : Blo 892572 1698965 := bbase (se 6 (by rfl) ⟨39819, by rfl⟩ : syracuseStep 1698965 = 79639) (by norm_num)
theorem B1076549 : Blo 892572 1076549 := bbase (se 4 (by rfl) ⟨100926, by rfl⟩ : syracuseStep 1076549 = 201853) (by norm_num)
theorem B3403093 : Blo 892572 3403093 := bbase (se 11 (by rfl) ⟨2492, by rfl⟩ : syracuseStep 3403093 = 4985) (by norm_num)
theorem B1076645 : Blo 892572 1076645 := bbase (se 4 (by rfl) ⟨100935, by rfl⟩ : syracuseStep 1076645 = 201871) (by norm_num)
theorem B1076665 : Blo 892572 1076665 := bbase (se 2 (by rfl) ⟨403749, by rfl⟩ : syracuseStep 1076665 = 807499) (by norm_num)
theorem B1338869 : Blo 892572 1338869 := bbase (se 5 (by rfl) ⟨62759, by rfl⟩ : syracuseStep 1338869 = 125519) (by norm_num)
theorem B1338893 : Blo 892572 1338893 := bbase (se 3 (by rfl) ⟨251042, by rfl⟩ : syracuseStep 1338893 = 502085) (by norm_num)
theorem B1338917 : Blo 892572 1338917 := bbase (se 4 (by rfl) ⟨125523, by rfl⟩ : syracuseStep 1338917 = 251047) (by norm_num)
theorem B3829301 : Blo 892572 3829301 := bbase (se 5 (by rfl) ⟨179498, by rfl⟩ : syracuseStep 3829301 = 358997) (by norm_num)
theorem B1338941 : Blo 892572 1338941 := bbase (se 3 (by rfl) ⟨251051, by rfl⟩ : syracuseStep 1338941 = 502103) (by norm_num)
theorem B1076809 : Blo 892572 1076809 := bbase (se 2 (by rfl) ⟨403803, by rfl⟩ : syracuseStep 1076809 = 807607) (by norm_num)
theorem B1273421 : Blo 892572 1273421 := bbase (se 3 (by rfl) ⟨238766, by rfl⟩ : syracuseStep 1273421 = 477533) (by norm_num)
theorem B1338965 : Blo 892572 1338965 := bbase (se 8 (by rfl) ⟨7845, by rfl⟩ : syracuseStep 1338965 = 15691) (by norm_num)
theorem B1338989 : Blo 892572 1338989 := bbase (se 3 (by rfl) ⟨251060, by rfl⟩ : syracuseStep 1338989 = 502121) (by norm_num)
theorem B1339013 : Blo 892572 1339013 := bbase (se 4 (by rfl) ⟨125532, by rfl⟩ : syracuseStep 1339013 = 251065) (by norm_num)
theorem B3403397 : Blo 892572 3403397 := bbase (se 4 (by rfl) ⟨319068, by rfl⟩ : syracuseStep 3403397 = 638137) (by norm_num)
theorem B1339037 : Blo 892572 1339037 := bbase (se 3 (by rfl) ⟨251069, by rfl⟩ : syracuseStep 1339037 = 502139) (by norm_num)
theorem B1339061 : Blo 892572 1339061 := bbase (se 5 (by rfl) ⟨62768, by rfl⟩ : syracuseStep 1339061 = 125537) (by norm_num)
theorem B1339085 : Blo 892572 1339085 := bbase (se 3 (by rfl) ⟨251078, by rfl⟩ : syracuseStep 1339085 = 502157) (by norm_num)
theorem B1339109 : Blo 892572 1339109 := bbase (se 4 (by rfl) ⟨125541, by rfl⟩ : syracuseStep 1339109 = 251083) (by norm_num)
theorem B1339133 : Blo 892572 1339133 := bbase (se 3 (by rfl) ⟨251087, by rfl⟩ : syracuseStep 1339133 = 502175) (by norm_num)
theorem B1339157 : Blo 892572 1339157 := bbase (se 6 (by rfl) ⟨31386, by rfl⟩ : syracuseStep 1339157 = 62773) (by norm_num)
theorem B1339181 : Blo 892572 1339181 := bbase (se 3 (by rfl) ⟨251096, by rfl⟩ : syracuseStep 1339181 = 502193) (by norm_num)
theorem B1339205 : Blo 892572 1339205 := bbase (se 4 (by rfl) ⟨125550, by rfl⟩ : syracuseStep 1339205 = 251101) (by norm_num)
theorem B2551637 : Blo 892572 2551637 := bbase (se 9 (by rfl) ⟨7475, by rfl⟩ : syracuseStep 2551637 = 14951) (by norm_num)
theorem B1339229 : Blo 892572 1339229 := bbase (se 3 (by rfl) ⟨251105, by rfl⟩ : syracuseStep 1339229 = 502211) (by norm_num)
theorem B1339253 : Blo 892572 1339253 := bbase (se 5 (by rfl) ⟨62777, by rfl⟩ : syracuseStep 1339253 = 125555) (by norm_num)
theorem B1699717 : Blo 892572 1699717 := bbase (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) (by norm_num)
theorem B3633029 : Blo 892572 3633029 := bbase (se 4 (by rfl) ⟨340596, by rfl⟩ : syracuseStep 3633029 = 681193) (by norm_num)
theorem B1339277 : Blo 892572 1339277 := bbase (se 3 (by rfl) ⟨251114, by rfl⟩ : syracuseStep 1339277 = 502229) (by norm_num)
theorem B1339301 : Blo 892572 1339301 := bbase (se 4 (by rfl) ⟨125559, by rfl⟩ : syracuseStep 1339301 = 251119) (by norm_num)
theorem B1339325 : Blo 892572 1339325 := bbase (se 3 (by rfl) ⟨251123, by rfl⟩ : syracuseStep 1339325 = 502247) (by norm_num)
theorem B1339349 : Blo 892572 1339349 := bbase (se 7 (by rfl) ⟨15695, by rfl⟩ : syracuseStep 1339349 = 31391) (by norm_num)
theorem B1339373 : Blo 892572 1339373 := bbase (se 3 (by rfl) ⟨251132, by rfl⟩ : syracuseStep 1339373 = 502265) (by norm_num)
theorem B1339397 : Blo 892572 1339397 := bbase (se 4 (by rfl) ⟨125568, by rfl⟩ : syracuseStep 1339397 = 251137) (by norm_num)
theorem B1699861 : Blo 892572 1699861 := bbase (se 6 (by rfl) ⟨39840, by rfl⟩ : syracuseStep 1699861 = 79681) (by norm_num)
theorem B1339421 : Blo 892572 1339421 := bbase (se 3 (by rfl) ⟨251141, by rfl⟩ : syracuseStep 1339421 = 502283) (by norm_num)
theorem B1339445 : Blo 892572 1339445 := bbase (se 5 (by rfl) ⟨62786, by rfl⟩ : syracuseStep 1339445 = 125573) (by norm_num)
theorem B1339469 : Blo 892572 1339469 := bbase (se 3 (by rfl) ⟨251150, by rfl⟩ : syracuseStep 1339469 = 502301) (by norm_num)
theorem B1339493 : Blo 892572 1339493 := bbase (se 4 (by rfl) ⟨125577, by rfl⟩ : syracuseStep 1339493 = 251155) (by norm_num)
theorem B1273973 : Blo 892572 1273973 := bbase (se 5 (by rfl) ⟨59717, by rfl⟩ : syracuseStep 1273973 = 119435) (by norm_num)
theorem B1339517 : Blo 892572 1339517 := bbase (se 3 (by rfl) ⟨251159, by rfl⟩ : syracuseStep 1339517 = 502319) (by norm_num)
theorem B1339541 : Blo 892572 1339541 := bbase (se 6 (by rfl) ⟨31395, by rfl⟩ : syracuseStep 1339541 = 62791) (by norm_num)
theorem B1339565 : Blo 892572 1339565 := bbase (se 3 (by rfl) ⟨251168, by rfl⟩ : syracuseStep 1339565 = 502337) (by norm_num)
theorem B1700021 : Blo 892572 1700021 := bbase (se 5 (by rfl) ⟨79688, by rfl⟩ : syracuseStep 1700021 = 159377) (by norm_num)
theorem B1339589 : Blo 892572 1339589 := bbase (se 4 (by rfl) ⟨125586, by rfl⟩ : syracuseStep 1339589 = 251173) (by norm_num)
theorem B1339613 : Blo 892572 1339613 := bbase (se 3 (by rfl) ⟨251177, by rfl⟩ : syracuseStep 1339613 = 502355) (by norm_num)
theorem B1339637 : Blo 892572 1339637 := bbase (se 5 (by rfl) ⟨62795, by rfl⟩ : syracuseStep 1339637 = 125591) (by norm_num)
theorem B1339661 : Blo 892572 1339661 := bbase (se 3 (by rfl) ⟨251186, by rfl⟩ : syracuseStep 1339661 = 502373) (by norm_num)
theorem B1339685 : Blo 892572 1339685 := bbase (se 4 (by rfl) ⟨125595, by rfl⟩ : syracuseStep 1339685 = 251191) (by norm_num)
theorem B1339709 : Blo 892572 1339709 := bbase (se 3 (by rfl) ⟨251195, by rfl⟩ : syracuseStep 1339709 = 502391) (by norm_num)
theorem B1700165 : Blo 892572 1700165 := bbase (se 4 (by rfl) ⟨159390, by rfl⟩ : syracuseStep 1700165 = 318781) (by norm_num)
theorem B1339733 : Blo 892572 1339733 := bbase (se 10 (by rfl) ⟨1962, by rfl⟩ : syracuseStep 1339733 = 3925) (by norm_num)
theorem B1339757 : Blo 892572 1339757 := bbase (se 3 (by rfl) ⟨251204, by rfl⟩ : syracuseStep 1339757 = 502409) (by norm_num)
theorem B1339781 : Blo 892572 1339781 := bbase (se 4 (by rfl) ⟨125604, by rfl⟩ : syracuseStep 1339781 = 251209) (by norm_num)
theorem B1339805 : Blo 892572 1339805 := bbase (se 3 (by rfl) ⟨251213, by rfl⟩ : syracuseStep 1339805 = 502427) (by norm_num)
theorem B1339829 : Blo 892572 1339829 := bbase (se 5 (by rfl) ⟨62804, by rfl⟩ : syracuseStep 1339829 = 125609) (by norm_num)
theorem B1339853 : Blo 892572 1339853 := bbase (se 3 (by rfl) ⟨251222, by rfl⟩ : syracuseStep 1339853 = 502445) (by norm_num)
theorem B1339877 : Blo 892572 1339877 := bbase (se 4 (by rfl) ⟨125613, by rfl⟩ : syracuseStep 1339877 = 251227) (by norm_num)
theorem B1339901 : Blo 892572 1339901 := bbase (se 3 (by rfl) ⟨251231, by rfl⟩ : syracuseStep 1339901 = 502463) (by norm_num)
theorem B1339925 : Blo 892572 1339925 := bbase (se 6 (by rfl) ⟨31404, by rfl⟩ : syracuseStep 1339925 = 62809) (by norm_num)
theorem B1339949 : Blo 892572 1339949 := bbase (se 3 (by rfl) ⟨251240, by rfl⟩ : syracuseStep 1339949 = 502481) (by norm_num)
theorem B1339973 : Blo 892572 1339973 := bbase (se 4 (by rfl) ⟨125622, by rfl⟩ : syracuseStep 1339973 = 251245) (by norm_num)
theorem B2421317 : Blo 892572 2421317 := bbase (se 4 (by rfl) ⟨226998, by rfl⟩ : syracuseStep 2421317 = 453997) (by norm_num)
theorem B1339997 : Blo 892572 1339997 := bbase (se 3 (by rfl) ⟨251249, by rfl⟩ : syracuseStep 1339997 = 502499) (by norm_num)
theorem B1700453 : Blo 892572 1700453 := bbase (se 4 (by rfl) ⟨159417, by rfl⟩ : syracuseStep 1700453 = 318835) (by norm_num)
theorem B1340021 : Blo 892572 1340021 := bbase (se 5 (by rfl) ⟨62813, by rfl⟩ : syracuseStep 1340021 = 125627) (by norm_num)
theorem B1340045 : Blo 892572 1340045 := bbase (se 3 (by rfl) ⟨251258, by rfl⟩ : syracuseStep 1340045 = 502517) (by norm_num)
theorem B1340069 : Blo 892572 1340069 := bbase (se 4 (by rfl) ⟨125631, by rfl⟩ : syracuseStep 1340069 = 251263) (by norm_num)
theorem B1340093 : Blo 892572 1340093 := bbase (se 3 (by rfl) ⟨251267, by rfl⟩ : syracuseStep 1340093 = 502535) (by norm_num)
theorem B1340117 : Blo 892572 1340117 := bbase (se 7 (by rfl) ⟨15704, by rfl⟩ : syracuseStep 1340117 = 31409) (by norm_num)
theorem B1340141 : Blo 892572 1340141 := bbase (se 3 (by rfl) ⟨251276, by rfl⟩ : syracuseStep 1340141 = 502553) (by norm_num)
theorem B1700605 : Blo 892572 1700605 := bbase (se 3 (by rfl) ⟨318863, by rfl⟩ : syracuseStep 1700605 = 637727) (by norm_num)
theorem B1340165 : Blo 892572 1340165 := bbase (se 4 (by rfl) ⟨125640, by rfl⟩ : syracuseStep 1340165 = 251281) (by norm_num)
theorem B1340189 : Blo 892572 1340189 := bbase (se 3 (by rfl) ⟨251285, by rfl⟩ : syracuseStep 1340189 = 502571) (by norm_num)
theorem B1340213 : Blo 892572 1340213 := bbase (se 5 (by rfl) ⟨62822, by rfl⟩ : syracuseStep 1340213 = 125645) (by norm_num)
theorem B1340237 : Blo 892572 1340237 := bbase (se 3 (by rfl) ⟨251294, by rfl⟩ : syracuseStep 1340237 = 502589) (by norm_num)
theorem B1340261 : Blo 892572 1340261 := bbase (se 4 (by rfl) ⟨125649, by rfl⟩ : syracuseStep 1340261 = 251299) (by norm_num)
theorem B1274725 : Blo 892572 1274725 := bbase (se 4 (by rfl) ⟨119505, by rfl⟩ : syracuseStep 1274725 = 239011) (by norm_num)
theorem B1340285 : Blo 892572 1340285 := bbase (se 3 (by rfl) ⟨251303, by rfl⟩ : syracuseStep 1340285 = 502607) (by norm_num)
theorem B1340309 : Blo 892572 1340309 := bbase (se 6 (by rfl) ⟨31413, by rfl⟩ : syracuseStep 1340309 = 62827) (by norm_num)
theorem B1340333 : Blo 892572 1340333 := bbase (se 3 (by rfl) ⟨251312, by rfl⟩ : syracuseStep 1340333 = 502625) (by norm_num)
theorem B1340357 : Blo 892572 1340357 := bbase (se 4 (by rfl) ⟨125658, by rfl⟩ : syracuseStep 1340357 = 251317) (by norm_num)
theorem B1340381 : Blo 892572 1340381 := bbase (se 3 (by rfl) ⟨251321, by rfl⟩ : syracuseStep 1340381 = 502643) (by norm_num)
theorem B1340405 : Blo 892572 1340405 := bbase (se 5 (by rfl) ⟨62831, by rfl⟩ : syracuseStep 1340405 = 125663) (by norm_num)
theorem B1340429 : Blo 892572 1340429 := bbase (se 3 (by rfl) ⟨251330, by rfl⟩ : syracuseStep 1340429 = 502661) (by norm_num)
theorem B1340453 : Blo 892572 1340453 := bbase (se 4 (by rfl) ⟨125667, by rfl⟩ : syracuseStep 1340453 = 251335) (by norm_num)
theorem B1700909 : Blo 892572 1700909 := bbase (se 3 (by rfl) ⟨318920, by rfl⟩ : syracuseStep 1700909 = 637841) (by norm_num)
theorem B1340477 : Blo 892572 1340477 := bbase (se 3 (by rfl) ⟨251339, by rfl⟩ : syracuseStep 1340477 = 502679) (by norm_num)
theorem B1340501 : Blo 892572 1340501 := bbase (se 8 (by rfl) ⟨7854, by rfl⟩ : syracuseStep 1340501 = 15709) (by norm_num)
theorem B1340525 : Blo 892572 1340525 := bbase (se 3 (by rfl) ⟨251348, by rfl⟩ : syracuseStep 1340525 = 502697) (by norm_num)
theorem B1340549 : Blo 892572 1340549 := bbase (se 4 (by rfl) ⟨125676, by rfl⟩ : syracuseStep 1340549 = 251353) (by norm_num)
theorem B1340573 : Blo 892572 1340573 := bbase (se 3 (by rfl) ⟨251357, by rfl⟩ : syracuseStep 1340573 = 502715) (by norm_num)
theorem B1340597 : Blo 892572 1340597 := bbase (se 5 (by rfl) ⟨62840, by rfl⟩ : syracuseStep 1340597 = 125681) (by norm_num)
theorem B1340621 : Blo 892572 1340621 := bbase (se 3 (by rfl) ⟨251366, by rfl⟩ : syracuseStep 1340621 = 502733) (by norm_num)
theorem B1340645 : Blo 892572 1340645 := bbase (se 4 (by rfl) ⟨125685, by rfl⟩ : syracuseStep 1340645 = 251371) (by norm_num)
theorem B1340669 : Blo 892572 1340669 := bbase (se 3 (by rfl) ⟨251375, by rfl⟩ : syracuseStep 1340669 = 502751) (by norm_num)
theorem B1340693 : Blo 892572 1340693 := bbase (se 6 (by rfl) ⟨31422, by rfl⟩ : syracuseStep 1340693 = 62845) (by norm_num)
theorem B1340717 : Blo 892572 1340717 := bbase (se 3 (by rfl) ⟨251384, by rfl⟩ : syracuseStep 1340717 = 502769) (by norm_num)
theorem B1340741 : Blo 892572 1340741 := bbase (se 4 (by rfl) ⟨125694, by rfl⟩ : syracuseStep 1340741 = 251389) (by norm_num)
theorem B1340765 : Blo 892572 1340765 := bbase (se 3 (by rfl) ⟨251393, by rfl⟩ : syracuseStep 1340765 = 502787) (by norm_num)
theorem B1340789 : Blo 892572 1340789 := bbase (se 5 (by rfl) ⟨62849, by rfl⟩ : syracuseStep 1340789 = 125699) (by norm_num)
theorem B1340813 : Blo 892572 1340813 := bbase (se 3 (by rfl) ⟨251402, by rfl⟩ : syracuseStep 1340813 = 502805) (by norm_num)
theorem B1340837 : Blo 892572 1340837 := bbase (se 4 (by rfl) ⟨125703, by rfl⟩ : syracuseStep 1340837 = 251407) (by norm_num)
theorem B1340861 : Blo 892572 1340861 := bbase (se 3 (by rfl) ⟨251411, by rfl⟩ : syracuseStep 1340861 = 502823) (by norm_num)
theorem B1340885 : Blo 892572 1340885 := bbase (se 7 (by rfl) ⟨15713, by rfl⟩ : syracuseStep 1340885 = 31427) (by norm_num)
theorem B1340909 : Blo 892572 1340909 := bbase (se 3 (by rfl) ⟨251420, by rfl⟩ : syracuseStep 1340909 = 502841) (by norm_num)
theorem B1340933 : Blo 892572 1340933 := bbase (se 4 (by rfl) ⟨125712, by rfl⟩ : syracuseStep 1340933 = 251425) (by norm_num)
theorem B1340957 : Blo 892572 1340957 := bbase (se 3 (by rfl) ⟨251429, by rfl⟩ : syracuseStep 1340957 = 502859) (by norm_num)
theorem B1340981 : Blo 892572 1340981 := bbase (se 5 (by rfl) ⟨62858, by rfl⟩ : syracuseStep 1340981 = 125717) (by norm_num)
theorem B1341005 : Blo 892572 1341005 := bbase (se 3 (by rfl) ⟨251438, by rfl⟩ : syracuseStep 1341005 = 502877) (by norm_num)
theorem B1341029 : Blo 892572 1341029 := bbase (se 4 (by rfl) ⟨125721, by rfl⟩ : syracuseStep 1341029 = 251443) (by norm_num)
theorem B3438197 : Blo 892572 3438197 := bbase (se 5 (by rfl) ⟨161165, by rfl⟩ : syracuseStep 3438197 = 322331) (by norm_num)
theorem B1341053 : Blo 892572 1341053 := bbase (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) (by norm_num)
theorem B1275517 : Blo 892572 1275517 := bbase (se 3 (by rfl) ⟨239159, by rfl⟩ : syracuseStep 1275517 = 478319) (by norm_num)
theorem B1341077 : Blo 892572 1341077 := bbase (se 6 (by rfl) ⟨31431, by rfl⟩ : syracuseStep 1341077 = 62863) (by norm_num)
theorem B1341101 : Blo 892572 1341101 := bbase (se 3 (by rfl) ⟨251456, by rfl⟩ : syracuseStep 1341101 = 502913) (by norm_num)
theorem B1341125 : Blo 892572 1341125 := bbase (se 4 (by rfl) ⟨125730, by rfl⟩ : syracuseStep 1341125 = 251461) (by norm_num)
theorem B4519637 : Blo 892572 4519637 := bbase (se 7 (by rfl) ⟨52964, by rfl⟩ : syracuseStep 4519637 = 105929) (by norm_num)
theorem B1210069 : Blo 892572 1210069 := bbase (se 7 (by rfl) ⟨14180, by rfl⟩ : syracuseStep 1210069 = 28361) (by norm_num)
theorem B1341149 : Blo 892572 1341149 := bbase (se 3 (by rfl) ⟨251465, by rfl⟩ : syracuseStep 1341149 = 502931) (by norm_num)
theorem B1341173 : Blo 892572 1341173 := bbase (se 5 (by rfl) ⟨62867, by rfl⟩ : syracuseStep 1341173 = 125735) (by norm_num)
theorem B1341197 : Blo 892572 1341197 := bbase (se 3 (by rfl) ⟨251474, by rfl⟩ : syracuseStep 1341197 = 502949) (by norm_num)
theorem B1701661 : Blo 892572 1701661 := bbase (se 3 (by rfl) ⟨319061, by rfl⟩ : syracuseStep 1701661 = 638123) (by norm_num)
theorem B1341221 : Blo 892572 1341221 := bbase (se 4 (by rfl) ⟨125739, by rfl⟩ : syracuseStep 1341221 = 251479) (by norm_num)
theorem B1341245 : Blo 892572 1341245 := bbase (se 3 (by rfl) ⟨251483, by rfl⟩ : syracuseStep 1341245 = 502967) (by norm_num)
theorem B1341269 : Blo 892572 1341269 := bbase (se 9 (by rfl) ⟨3929, by rfl⟩ : syracuseStep 1341269 = 7859) (by norm_num)
theorem B1341293 : Blo 892572 1341293 := bbase (se 3 (by rfl) ⟨251492, by rfl⟩ : syracuseStep 1341293 = 502985) (by norm_num)
theorem B1341317 : Blo 892572 1341317 := bbase (se 4 (by rfl) ⟨125748, by rfl⟩ : syracuseStep 1341317 = 251497) (by norm_num)
theorem B1341341 : Blo 892572 1341341 := bbase (se 3 (by rfl) ⟨251501, by rfl⟩ : syracuseStep 1341341 = 503003) (by norm_num)
theorem B1701805 : Blo 892572 1701805 := bbase (se 3 (by rfl) ⟨319088, by rfl⟩ : syracuseStep 1701805 = 638177) (by norm_num)
theorem B1341365 : Blo 892572 1341365 := bbase (se 5 (by rfl) ⟨62876, by rfl⟩ : syracuseStep 1341365 = 125753) (by norm_num)
theorem B1341389 : Blo 892572 1341389 := bbase (se 3 (by rfl) ⟨251510, by rfl⟩ : syracuseStep 1341389 = 503021) (by norm_num)
theorem B1275853 : Blo 892572 1275853 := bbase (se 3 (by rfl) ⟨239222, by rfl⟩ : syracuseStep 1275853 = 478445) (by norm_num)
theorem B2586581 : Blo 892572 2586581 := bbase (se 7 (by rfl) ⟨30311, by rfl⟩ : syracuseStep 2586581 = 60623) (by norm_num)
theorem B1341413 : Blo 892572 1341413 := bbase (se 4 (by rfl) ⟨125757, by rfl⟩ : syracuseStep 1341413 = 251515) (by norm_num)
theorem B1341437 : Blo 892572 1341437 := bbase (se 3 (by rfl) ⟨251519, by rfl⟩ : syracuseStep 1341437 = 503039) (by norm_num)
theorem B1341461 : Blo 892572 1341461 := bbase (se 6 (by rfl) ⟨31440, by rfl⟩ : syracuseStep 1341461 = 62881) (by norm_num)
theorem B1341485 : Blo 892572 1341485 := bbase (se 3 (by rfl) ⟨251528, by rfl⟩ : syracuseStep 1341485 = 503057) (by norm_num)
theorem B1341509 : Blo 892572 1341509 := bbase (se 4 (by rfl) ⟨125766, by rfl⟩ : syracuseStep 1341509 = 251533) (by norm_num)
theorem B1701965 : Blo 892572 1701965 := bbase (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) (by norm_num)
theorem B1341533 : Blo 892572 1341533 := bbase (se 3 (by rfl) ⟨251537, by rfl⟩ : syracuseStep 1341533 = 503075) (by norm_num)
theorem B1341557 : Blo 892572 1341557 := bbase (se 5 (by rfl) ⟨62885, by rfl⟩ : syracuseStep 1341557 = 125771) (by norm_num)
theorem B1341581 : Blo 892572 1341581 := bbase (se 3 (by rfl) ⟨251546, by rfl⟩ : syracuseStep 1341581 = 503093) (by norm_num)
theorem B1341605 : Blo 892572 1341605 := bbase (se 4 (by rfl) ⟨125775, by rfl⟩ : syracuseStep 1341605 = 251551) (by norm_num)
theorem B1276069 : Blo 892572 1276069 := bbase (se 4 (by rfl) ⟨119631, by rfl⟩ : syracuseStep 1276069 = 239263) (by norm_num)
theorem B1341629 : Blo 892572 1341629 := bbase (se 3 (by rfl) ⟨251555, by rfl⟩ : syracuseStep 1341629 = 503111) (by norm_num)
theorem B3012821 : Blo 892572 3012821 := bbase (se 7 (by rfl) ⟨35306, by rfl⟩ : syracuseStep 3012821 = 70613) (by norm_num)
theorem B1341653 : Blo 892572 1341653 := bbase (se 7 (by rfl) ⟨15722, by rfl⟩ : syracuseStep 1341653 = 31445) (by norm_num)
theorem B1341677 : Blo 892572 1341677 := bbase (se 3 (by rfl) ⟨251564, by rfl⟩ : syracuseStep 1341677 = 503129) (by norm_num)
theorem B1341701 : Blo 892572 1341701 := bbase (se 4 (by rfl) ⟨125784, by rfl⟩ : syracuseStep 1341701 = 251569) (by norm_num)
theorem B1341725 : Blo 892572 1341725 := bbase (se 3 (by rfl) ⟨251573, by rfl⟩ : syracuseStep 1341725 = 503147) (by norm_num)
theorem B1341749 : Blo 892572 1341749 := bbase (se 5 (by rfl) ⟨62894, by rfl⟩ : syracuseStep 1341749 = 125789) (by norm_num)
theorem B1341773 : Blo 892572 1341773 := bbase (se 3 (by rfl) ⟨251582, by rfl⟩ : syracuseStep 1341773 = 503165) (by norm_num)
theorem B1341797 : Blo 892572 1341797 := bbase (se 4 (by rfl) ⟨125793, by rfl⟩ : syracuseStep 1341797 = 251587) (by norm_num)
theorem B1341821 : Blo 892572 1341821 := bbase (se 3 (by rfl) ⟨251591, by rfl⟩ : syracuseStep 1341821 = 503183) (by norm_num)
theorem B1341845 : Blo 892572 1341845 := bbase (se 6 (by rfl) ⟨31449, by rfl⟩ : syracuseStep 1341845 = 62899) (by norm_num)
theorem B2423189 : Blo 892572 2423189 := bbase (se 6 (by rfl) ⟨56793, by rfl⟩ : syracuseStep 2423189 = 113587) (by norm_num)
theorem B2259373 : Blo 892572 2259373 := bbase (se 3 (by rfl) ⟨423632, by rfl⟩ : syracuseStep 2259373 = 847265) (by norm_num)
theorem B1341869 : Blo 892572 1341869 := bbase (se 3 (by rfl) ⟨251600, by rfl⟩ : syracuseStep 1341869 = 503201) (by norm_num)
theorem B1341893 : Blo 892572 1341893 := bbase (se 4 (by rfl) ⟨125802, by rfl⟩ : syracuseStep 1341893 = 251605) (by norm_num)
theorem B1341917 : Blo 892572 1341917 := bbase (se 3 (by rfl) ⟨251609, by rfl⟩ : syracuseStep 1341917 = 503219) (by norm_num)
theorem B1341941 : Blo 892572 1341941 := bbase (se 5 (by rfl) ⟨62903, by rfl⟩ : syracuseStep 1341941 = 125807) (by norm_num)
theorem B1341965 : Blo 892572 1341965 := bbase (se 3 (by rfl) ⟨251618, by rfl⟩ : syracuseStep 1341965 = 503237) (by norm_num)
theorem B2259485 : Blo 892572 2259485 := bbase (se 3 (by rfl) ⟨423653, by rfl⟩ : syracuseStep 2259485 = 847307) (by norm_num)
theorem B1276445 : Blo 892572 1276445 := bbase (se 3 (by rfl) ⟨239333, by rfl⟩ : syracuseStep 1276445 = 478667) (by norm_num)
theorem B1341989 : Blo 892572 1341989 := bbase (se 4 (by rfl) ⟨125811, by rfl⟩ : syracuseStep 1341989 = 251623) (by norm_num)
theorem B1342013 : Blo 892572 1342013 := bbase (se 3 (by rfl) ⟨251627, by rfl⟩ : syracuseStep 1342013 = 503255) (by norm_num)
theorem B1342037 : Blo 892572 1342037 := bbase (se 8 (by rfl) ⟨7863, by rfl⟩ : syracuseStep 1342037 = 15727) (by norm_num)
theorem B1342061 : Blo 892572 1342061 := bbase (se 3 (by rfl) ⟨251636, by rfl⟩ : syracuseStep 1342061 = 503273) (by norm_num)
theorem B3013253 : Blo 892572 3013253 := bbase (se 4 (by rfl) ⟨282492, by rfl⟩ : syracuseStep 3013253 = 564985) (by norm_num)
theorem B1342085 : Blo 892572 1342085 := bbase (se 4 (by rfl) ⟨125820, by rfl⟩ : syracuseStep 1342085 = 251641) (by norm_num)
theorem B1342109 : Blo 892572 1342109 := bbase (se 3 (by rfl) ⟨251645, by rfl⟩ : syracuseStep 1342109 = 503291) (by norm_num)
theorem B1342133 : Blo 892572 1342133 := bbase (se 5 (by rfl) ⟨62912, by rfl⟩ : syracuseStep 1342133 = 125825) (by norm_num)
theorem B1342157 : Blo 892572 1342157 := bbase (se 3 (by rfl) ⟨251654, by rfl⟩ : syracuseStep 1342157 = 503309) (by norm_num)
theorem B2259677 : Blo 892572 2259677 := bbase (se 3 (by rfl) ⟨423689, by rfl⟩ : syracuseStep 2259677 = 847379) (by norm_num)
theorem B1342181 : Blo 892572 1342181 := bbase (se 4 (by rfl) ⟨125829, by rfl⟩ : syracuseStep 1342181 = 251659) (by norm_num)
theorem B1342205 : Blo 892572 1342205 := bbase (se 3 (by rfl) ⟨251663, by rfl⟩ : syracuseStep 1342205 = 503327) (by norm_num)
theorem B1342229 : Blo 892572 1342229 := bbase (se 6 (by rfl) ⟨31458, by rfl⟩ : syracuseStep 1342229 = 62917) (by norm_num)
theorem B1342253 : Blo 892572 1342253 := bbase (se 3 (by rfl) ⟨251672, by rfl⟩ : syracuseStep 1342253 = 503345) (by norm_num)
theorem B1342277 : Blo 892572 1342277 := bbase (se 4 (by rfl) ⟨125838, by rfl⟩ : syracuseStep 1342277 = 251677) (by norm_num)
theorem B74316629 : Blo 892572 74316629 := bbase (se 9 (by rfl) ⟨217724, by rfl⟩ : syracuseStep 74316629 = 435449) (by norm_num)
theorem B1342301 : Blo 892572 1342301 := bbase (se 3 (by rfl) ⟨251681, by rfl⟩ : syracuseStep 1342301 = 503363) (by norm_num)
theorem B1342325 : Blo 892572 1342325 := bbase (se 5 (by rfl) ⟨62921, by rfl⟩ : syracuseStep 1342325 = 125843) (by norm_num)
theorem B1342349 : Blo 892572 1342349 := bbase (se 3 (by rfl) ⟨251690, by rfl⟩ : syracuseStep 1342349 = 503381) (by norm_num)
theorem B1342373 : Blo 892572 1342373 := bbase (se 4 (by rfl) ⟨125847, by rfl⟩ : syracuseStep 1342373 = 251695) (by norm_num)
theorem B1342397 : Blo 892572 1342397 := bbase (se 3 (by rfl) ⟨251699, by rfl⟩ : syracuseStep 1342397 = 503399) (by norm_num)
theorem B1342421 : Blo 892572 1342421 := bbase (se 7 (by rfl) ⟨15731, by rfl⟩ : syracuseStep 1342421 = 31463) (by norm_num)
theorem B1506269 : Blo 892572 1506269 := bbase (se 3 (by rfl) ⟨282425, by rfl⟩ : syracuseStep 1506269 = 564851) (by norm_num)
theorem B4520933 : Blo 892572 4520933 := bbase (se 4 (by rfl) ⟨423837, by rfl⟩ : syracuseStep 4520933 = 847675) (by norm_num)
theorem B1342445 : Blo 892572 1342445 := bbase (se 3 (by rfl) ⟨251708, by rfl⟩ : syracuseStep 1342445 = 503417) (by norm_num)
theorem B1342469 : Blo 892572 1342469 := bbase (se 4 (by rfl) ⟨125856, by rfl⟩ : syracuseStep 1342469 = 251713) (by norm_num)
theorem B1342493 : Blo 892572 1342493 := bbase (se 3 (by rfl) ⟨251717, by rfl⟩ : syracuseStep 1342493 = 503435) (by norm_num)
theorem B2260021 : Blo 892572 2260021 := bbase (se 5 (by rfl) ⟨105938, by rfl⟩ : syracuseStep 2260021 = 211877) (by norm_num)
theorem B3013685 : Blo 892572 3013685 := bbase (se 5 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 3013685 = 282533) (by norm_num)
theorem B1342517 : Blo 892572 1342517 := bbase (se 5 (by rfl) ⟨62930, by rfl⟩ : syracuseStep 1342517 = 125861) (by norm_num)
theorem B1342541 : Blo 892572 1342541 := bbase (se 3 (by rfl) ⟨251726, by rfl⟩ : syracuseStep 1342541 = 503453) (by norm_num)
theorem B1506397 : Blo 892572 1506397 := bbase (se 3 (by rfl) ⟨282449, by rfl⟩ : syracuseStep 1506397 = 564899) (by norm_num)
theorem B1342565 : Blo 892572 1342565 := bbase (se 4 (by rfl) ⟨125865, by rfl⟩ : syracuseStep 1342565 = 251731) (by norm_num)
theorem B1342589 : Blo 892572 1342589 := bbase (se 3 (by rfl) ⟨251735, by rfl⟩ : syracuseStep 1342589 = 503471) (by norm_num)
theorem B2292869 : Blo 892572 2292869 := bbase (se 4 (by rfl) ⟨214956, by rfl⟩ : syracuseStep 2292869 = 429913) (by norm_num)
theorem B1342613 : Blo 892572 1342613 := bbase (se 6 (by rfl) ⟨31467, by rfl⟩ : syracuseStep 1342613 = 62935) (by norm_num)
theorem B2260133 : Blo 892572 2260133 := bbase (se 4 (by rfl) ⟨211887, by rfl⟩ : syracuseStep 2260133 = 423775) (by norm_num)
theorem B1342637 : Blo 892572 1342637 := bbase (se 3 (by rfl) ⟨251744, by rfl⟩ : syracuseStep 1342637 = 503489) (by norm_num)
theorem B1506485 : Blo 892572 1506485 := bbase (se 5 (by rfl) ⟨70616, by rfl⟩ : syracuseStep 1506485 = 141233) (by norm_num)
theorem B1342661 : Blo 892572 1342661 := bbase (se 4 (by rfl) ⟨125874, by rfl⟩ : syracuseStep 1342661 = 251749) (by norm_num)
theorem B1342685 : Blo 892572 1342685 := bbase (se 3 (by rfl) ⟨251753, by rfl⟩ : syracuseStep 1342685 = 503507) (by norm_num)
theorem B1342709 : Blo 892572 1342709 := bbase (se 5 (by rfl) ⟨62939, by rfl⟩ : syracuseStep 1342709 = 125879) (by norm_num)
theorem B1342733 : Blo 892572 1342733 := bbase (se 3 (by rfl) ⟨251762, by rfl⟩ : syracuseStep 1342733 = 503525) (by norm_num)
theorem B1342757 : Blo 892572 1342757 := bbase (se 4 (by rfl) ⟨125883, by rfl⟩ : syracuseStep 1342757 = 251767) (by norm_num)
theorem B1506613 : Blo 892572 1506613 := bbase (se 5 (by rfl) ⟨70622, by rfl⟩ : syracuseStep 1506613 = 141245) (by norm_num)
theorem B1342781 : Blo 892572 1342781 := bbase (se 3 (by rfl) ⟨251771, by rfl⟩ : syracuseStep 1342781 = 503543) (by norm_num)
theorem B1342805 : Blo 892572 1342805 := bbase (se 11 (by rfl) ⟨983, by rfl⟩ : syracuseStep 1342805 = 1967) (by norm_num)
theorem B2260325 : Blo 892572 2260325 := bbase (se 4 (by rfl) ⟨211905, by rfl⟩ : syracuseStep 2260325 = 423811) (by norm_num)
theorem B1342829 : Blo 892572 1342829 := bbase (se 3 (by rfl) ⟨251780, by rfl⟩ : syracuseStep 1342829 = 503561) (by norm_num)
theorem B2751877 : Blo 892572 2751877 := bbase (se 4 (by rfl) ⟨257988, by rfl⟩ : syracuseStep 2751877 = 515977) (by norm_num)
theorem B4291973 : Blo 892572 4291973 := bbase (se 4 (by rfl) ⟨402372, by rfl⟩ : syracuseStep 4291973 = 804745) (by norm_num)
theorem B1342853 : Blo 892572 1342853 := bbase (se 4 (by rfl) ⟨125892, by rfl⟩ : syracuseStep 1342853 = 251785) (by norm_num)
theorem B1506701 : Blo 892572 1506701 := bbase (se 3 (by rfl) ⟨282506, by rfl⟩ : syracuseStep 1506701 = 565013) (by norm_num)
theorem B1342877 : Blo 892572 1342877 := bbase (se 3 (by rfl) ⟨251789, by rfl⟩ : syracuseStep 1342877 = 503579) (by norm_num)
theorem B1342901 : Blo 892572 1342901 := bbase (se 5 (by rfl) ⟨62948, by rfl⟩ : syracuseStep 1342901 = 125897) (by norm_num)
theorem B1342925 : Blo 892572 1342925 := bbase (se 3 (by rfl) ⟨251798, by rfl⟩ : syracuseStep 1342925 = 503597) (by norm_num)
theorem B3014117 : Blo 892572 3014117 := bbase (se 4 (by rfl) ⟨282573, by rfl⟩ : syracuseStep 3014117 = 565147) (by norm_num)
theorem B1342949 : Blo 892572 1342949 := bbase (se 4 (by rfl) ⟨125901, by rfl⟩ : syracuseStep 1342949 = 251803) (by norm_num)
theorem B1342973 : Blo 892572 1342973 := bbase (se 3 (by rfl) ⟨251807, by rfl⟩ : syracuseStep 1342973 = 503615) (by norm_num)
theorem B1506829 : Blo 892572 1506829 := bbase (se 3 (by rfl) ⟨282530, by rfl⟩ : syracuseStep 1506829 = 565061) (by norm_num)
theorem B1342997 : Blo 892572 1342997 := bbase (se 6 (by rfl) ⟨31476, by rfl⟩ : syracuseStep 1342997 = 62953) (by norm_num)
theorem B1343021 : Blo 892572 1343021 := bbase (se 3 (by rfl) ⟨251816, by rfl⟩ : syracuseStep 1343021 = 503633) (by norm_num)
theorem B1343045 : Blo 892572 1343045 := bbase (se 4 (by rfl) ⟨125910, by rfl⟩ : syracuseStep 1343045 = 251821) (by norm_num)
theorem B1343069 : Blo 892572 1343069 := bbase (se 3 (by rfl) ⟨251825, by rfl⟩ : syracuseStep 1343069 = 503651) (by norm_num)
theorem B1506917 : Blo 892572 1506917 := bbase (se 4 (by rfl) ⟨141273, by rfl⟩ : syracuseStep 1506917 = 282547) (by norm_num)
theorem B1343093 : Blo 892572 1343093 := bbase (se 5 (by rfl) ⟨62957, by rfl⟩ : syracuseStep 1343093 = 125915) (by norm_num)
theorem B1343117 : Blo 892572 1343117 := bbase (se 3 (by rfl) ⟨251834, by rfl⟩ : syracuseStep 1343117 = 503669) (by norm_num)
theorem B4292261 : Blo 892572 4292261 := bbase (se 4 (by rfl) ⟨402399, by rfl⟩ : syracuseStep 4292261 = 804799) (by norm_num)
theorem B1343141 : Blo 892572 1343141 := bbase (se 4 (by rfl) ⟨125919, by rfl⟩ : syracuseStep 1343141 = 251839) (by norm_num)
theorem B1343165 : Blo 892572 1343165 := bbase (se 3 (by rfl) ⟨251843, by rfl⟩ : syracuseStep 1343165 = 503687) (by norm_num)
theorem B2260669 : Blo 892572 2260669 := bbase (se 3 (by rfl) ⟨423875, by rfl⟩ : syracuseStep 2260669 = 847751) (by norm_num)
theorem B1343189 : Blo 892572 1343189 := bbase (se 7 (by rfl) ⟨15740, by rfl⟩ : syracuseStep 1343189 = 31481) (by norm_num)
theorem B1507045 : Blo 892572 1507045 := bbase (se 4 (by rfl) ⟨141285, by rfl⟩ : syracuseStep 1507045 = 282571) (by norm_num)
theorem B1343213 : Blo 892572 1343213 := bbase (se 3 (by rfl) ⟨251852, by rfl⟩ : syracuseStep 1343213 = 503705) (by norm_num)
theorem B1343237 : Blo 892572 1343237 := bbase (se 4 (by rfl) ⟨125928, by rfl⟩ : syracuseStep 1343237 = 251857) (by norm_num)
theorem B1343261 : Blo 892572 1343261 := bbase (se 3 (by rfl) ⟨251861, by rfl⟩ : syracuseStep 1343261 = 503723) (by norm_num)
theorem B2260781 : Blo 892572 2260781 := bbase (se 3 (by rfl) ⟨423896, by rfl⟩ : syracuseStep 2260781 = 847793) (by norm_num)
theorem B1343285 : Blo 892572 1343285 := bbase (se 5 (by rfl) ⟨62966, by rfl⟩ : syracuseStep 1343285 = 125933) (by norm_num)
theorem B1507133 : Blo 892572 1507133 := bbase (se 3 (by rfl) ⟨282587, by rfl⟩ : syracuseStep 1507133 = 565175) (by norm_num)
theorem B1343309 : Blo 892572 1343309 := bbase (se 3 (by rfl) ⟨251870, by rfl⟩ : syracuseStep 1343309 = 503741) (by norm_num)
theorem B1343333 : Blo 892572 1343333 := bbase (se 4 (by rfl) ⟨125937, by rfl⟩ : syracuseStep 1343333 = 251875) (by norm_num)
theorem B1343357 : Blo 892572 1343357 := bbase (se 3 (by rfl) ⟨251879, by rfl⟩ : syracuseStep 1343357 = 503759) (by norm_num)
theorem B7733141 : Blo 892572 7733141 := bbase (se 6 (by rfl) ⟨181245, by rfl⟩ : syracuseStep 7733141 = 362491) (by norm_num)
theorem B3014549 : Blo 892572 3014549 := bbase (se 6 (by rfl) ⟨70653, by rfl⟩ : syracuseStep 3014549 = 141307) (by norm_num)
theorem B1343381 : Blo 892572 1343381 := bbase (se 6 (by rfl) ⟨31485, by rfl⟩ : syracuseStep 1343381 = 62971) (by norm_num)
theorem B1343405 : Blo 892572 1343405 := bbase (se 3 (by rfl) ⟨251888, by rfl⟩ : syracuseStep 1343405 = 503777) (by norm_num)
theorem B1507261 : Blo 892572 1507261 := bbase (se 3 (by rfl) ⟨282611, by rfl⟩ : syracuseStep 1507261 = 565223) (by norm_num)
theorem B1343429 : Blo 892572 1343429 := bbase (se 4 (by rfl) ⟨125946, by rfl⟩ : syracuseStep 1343429 = 251893) (by norm_num)
theorem B1343453 : Blo 892572 1343453 := bbase (se 3 (by rfl) ⟨251897, by rfl⟩ : syracuseStep 1343453 = 503795) (by norm_num)
theorem B2260973 : Blo 892572 2260973 := bbase (se 3 (by rfl) ⟨423932, by rfl⟩ : syracuseStep 2260973 = 847865) (by norm_num)
theorem B1343477 : Blo 892572 1343477 := bbase (se 5 (by rfl) ⟨62975, by rfl⟩ : syracuseStep 1343477 = 125951) (by norm_num)
theorem B1343489 : Blo 892572 1343489 := bstep (se 2 (by rfl) ⟨503808, by rfl⟩ : syracuseStep 1343489 = 1007617) B1007617
theorem B1343507 : Blo 892572 1343507 := bstep (se 1 (by rfl) ⟨1007630, by rfl⟩ : syracuseStep 1343507 = 2015261) B2015261
theorem B5505059 : Blo 892572 5505059 := bstep (se 1 (by rfl) ⟨4128794, by rfl⟩ : syracuseStep 5505059 = 8257589) B8257589
theorem B1343537 : Blo 892572 1343537 := bstep (se 2 (by rfl) ⟨503826, by rfl⟩ : syracuseStep 1343537 = 1007653) B1007653
theorem B1343555 : Blo 892572 1343555 := bstep (se 1 (by rfl) ⟨1007666, by rfl⟩ : syracuseStep 1343555 = 2015333) B2015333
theorem B1343585 : Blo 892572 1343585 := bstep (se 2 (by rfl) ⟨503844, by rfl⟩ : syracuseStep 1343585 = 1007689) B1007689
theorem B1146979 : Blo 892572 1146979 := bstep (se 1 (by rfl) ⟨860234, by rfl⟩ : syracuseStep 1146979 = 1720469) B1720469
theorem B3014765 : Blo 892572 3014765 := bstep (se 3 (by rfl) ⟨565268, by rfl⟩ : syracuseStep 3014765 = 1130537) B1130537
theorem B2261105 : Blo 892572 2261105 := bstep (se 2 (by rfl) ⟨847914, by rfl⟩ : syracuseStep 2261105 = 1695829) B1695829
theorem B1343603 : Blo 892572 1343603 := bstep (se 1 (by rfl) ⟨1007702, by rfl⟩ : syracuseStep 1343603 = 2015405) B2015405
theorem B1507457 : Blo 892572 1507457 := bstep (se 2 (by rfl) ⟨565296, by rfl⟩ : syracuseStep 1507457 = 1130593) B1130593
theorem B1343633 : Blo 892572 1343633 := bstep (se 2 (by rfl) ⟨503862, by rfl⟩ : syracuseStep 1343633 = 1007725) B1007725
theorem B3014819 : Blo 892572 3014819 := bstep (se 1 (by rfl) ⟨2261114, by rfl⟩ : syracuseStep 3014819 = 4522229) B4522229
theorem B2261155 : Blo 892572 2261155 := bstep (se 1 (by rfl) ⟨1695866, by rfl⟩ : syracuseStep 2261155 = 3391733) B3391733
theorem B2719907 : Blo 892572 2719907 := bstep (se 1 (by rfl) ⟨2039930, by rfl⟩ : syracuseStep 2719907 = 4079861) B4079861
theorem B1343651 : Blo 892572 1343651 := bstep (se 1 (by rfl) ⟨1007738, by rfl⟩ : syracuseStep 1343651 = 2015477) B2015477
theorem B1343681 : Blo 892572 1343681 := bstep (se 2 (by rfl) ⟨503880, by rfl⟩ : syracuseStep 1343681 = 1007761) B1007761
theorem B1343699 : Blo 892572 1343699 := bstep (se 1 (by rfl) ⟨1007774, by rfl⟩ : syracuseStep 1343699 = 2015549) B2015549
theorem B1343729 : Blo 892572 1343729 := bstep (se 2 (by rfl) ⟨503898, by rfl⟩ : syracuseStep 1343729 = 1007797) B1007797
theorem B1507585 : Blo 892572 1507585 := bstep (se 2 (by rfl) ⟨565344, by rfl⟩ : syracuseStep 1507585 = 1130689) B1130689
theorem B1343747 : Blo 892572 1343747 := bstep (se 1 (by rfl) ⟨1007810, by rfl⟩ : syracuseStep 1343747 = 2015621) B2015621
theorem B1343777 : Blo 892572 1343777 := bstep (se 2 (by rfl) ⟨503916, by rfl⟩ : syracuseStep 1343777 = 1007833) B1007833
theorem B1507619 : Blo 892572 1507619 := bstep (se 1 (by rfl) ⟨1130714, by rfl⟩ : syracuseStep 1507619 = 2261429) B2261429
theorem B2261297 : Blo 892572 2261297 := bstep (se 2 (by rfl) ⟨847986, by rfl⟩ : syracuseStep 2261297 = 1695973) B1695973
theorem B1343795 : Blo 892572 1343795 := bstep (se 1 (by rfl) ⟨1007846, by rfl⟩ : syracuseStep 1343795 = 2015693) B2015693
theorem B1343825 : Blo 892572 1343825 := bstep (se 2 (by rfl) ⟨503934, by rfl⟩ : syracuseStep 1343825 = 1007869) B1007869
theorem B1343843 : Blo 892572 1343843 := bstep (se 1 (by rfl) ⟨1007882, by rfl⟩ : syracuseStep 1343843 = 2015765) B2015765
theorem B1343873 : Blo 892572 1343873 := bstep (se 2 (by rfl) ⟨503952, by rfl⟩ : syracuseStep 1343873 = 1007905) B1007905
theorem B1343891 : Blo 892572 1343891 := bstep (se 1 (by rfl) ⟨1007918, by rfl⟩ : syracuseStep 1343891 = 2015837) B2015837
theorem B1507747 : Blo 892572 1507747 := bstep (se 1 (by rfl) ⟨1130810, by rfl⟩ : syracuseStep 1507747 = 2261621) B2261621
theorem B3015089 : Blo 892572 3015089 := bstep (se 2 (by rfl) ⟨1130658, by rfl⟩ : syracuseStep 3015089 = 2261317) B2261317
theorem B1343921 : Blo 892572 1343921 := bstep (se 2 (by rfl) ⟨503970, by rfl⟩ : syracuseStep 1343921 = 1007941) B1007941
theorem B1343939 : Blo 892572 1343939 := bstep (se 1 (by rfl) ⟨1007954, by rfl⟩ : syracuseStep 1343939 = 2015909) B2015909
theorem B1343969 : Blo 892572 1343969 := bstep (se 2 (by rfl) ⟨503988, by rfl⟩ : syracuseStep 1343969 = 1007977) B1007977
theorem B1343987 : Blo 892572 1343987 := bstep (se 1 (by rfl) ⟨1007990, by rfl⟩ : syracuseStep 1343987 = 2015981) B2015981
theorem B1344017 : Blo 892572 1344017 := bstep (se 2 (by rfl) ⟨504006, by rfl⟩ : syracuseStep 1344017 = 1008013) B1008013
theorem B1344035 : Blo 892572 1344035 := bstep (se 1 (by rfl) ⟨1008026, by rfl⟩ : syracuseStep 1344035 = 2016053) B2016053
theorem B1507889 : Blo 892572 1507889 := bstep (se 2 (by rfl) ⟨565458, by rfl⟩ : syracuseStep 1507889 = 1130917) B1130917
theorem B1344065 : Blo 892572 1344065 := bstep (se 2 (by rfl) ⟨504024, by rfl⟩ : syracuseStep 1344065 = 1008049) B1008049
theorem B1344083 : Blo 892572 1344083 := bstep (se 1 (by rfl) ⟨1008062, by rfl⟩ : syracuseStep 1344083 = 2016125) B2016125
theorem B6783587 : Blo 892572 6783587 := bstep (se 1 (by rfl) ⟨5087690, by rfl⟩ : syracuseStep 6783587 = 10175381) B10175381
theorem B1344113 : Blo 892572 1344113 := bstep (se 2 (by rfl) ⟨504042, by rfl⟩ : syracuseStep 1344113 = 1008085) B1008085
theorem B1344131 : Blo 892572 1344131 := bstep (se 1 (by rfl) ⟨1008098, by rfl⟩ : syracuseStep 1344131 = 2016197) B2016197
theorem B1344161 : Blo 892572 1344161 := bstep (se 2 (by rfl) ⟨504060, by rfl⟩ : syracuseStep 1344161 = 1008121) B1008121
theorem B1508017 : Blo 892572 1508017 := bstep (se 2 (by rfl) ⟨565506, by rfl⟩ : syracuseStep 1508017 = 1131013) B1131013
theorem B1344179 : Blo 892572 1344179 := bstep (se 1 (by rfl) ⟨1008134, by rfl⟩ : syracuseStep 1344179 = 2016269) B2016269
theorem B1344209 : Blo 892572 1344209 := bstep (se 2 (by rfl) ⟨504078, by rfl⟩ : syracuseStep 1344209 = 1008157) B1008157
theorem B1508051 : Blo 892572 1508051 := bstep (se 1 (by rfl) ⟨1131038, by rfl⟩ : syracuseStep 1508051 = 2262077) B2262077
theorem B1344227 : Blo 892572 1344227 := bstep (se 1 (by rfl) ⟨1008170, by rfl⟩ : syracuseStep 1344227 = 2016341) B2016341
theorem B1344257 : Blo 892572 1344257 := bstep (se 2 (by rfl) ⟨504096, by rfl⟩ : syracuseStep 1344257 = 1008193) B1008193
theorem B1344275 : Blo 892572 1344275 := bstep (se 1 (by rfl) ⟨1008206, by rfl⟩ : syracuseStep 1344275 = 2016413) B2016413
theorem B1344305 : Blo 892572 1344305 := bstep (se 2 (by rfl) ⟨504114, by rfl⟩ : syracuseStep 1344305 = 1008229) B1008229
theorem B1344323 : Blo 892572 1344323 := bstep (se 1 (by rfl) ⟨1008242, by rfl⟩ : syracuseStep 1344323 = 2016485) B2016485
theorem B1508179 : Blo 892572 1508179 := bstep (se 1 (by rfl) ⟨1131134, by rfl⟩ : syracuseStep 1508179 = 2262269) B2262269
theorem B1344353 : Blo 892572 1344353 := bstep (se 2 (by rfl) ⟨504132, by rfl⟩ : syracuseStep 1344353 = 1008265) B1008265
theorem B1344371 : Blo 892572 1344371 := bstep (se 1 (by rfl) ⟨1008278, by rfl⟩ : syracuseStep 1344371 = 2016557) B2016557
theorem B14484365 : Blo 892572 14484365 := bstep (se 3 (by rfl) ⟨2715818, by rfl⟩ : syracuseStep 14484365 = 5431637) B5431637
theorem B1344401 : Blo 892572 1344401 := bstep (se 2 (by rfl) ⟨504150, by rfl⟩ : syracuseStep 1344401 = 1008301) B1008301
theorem B1344419 : Blo 892572 1344419 := bstep (se 1 (by rfl) ⟨1008314, by rfl⟩ : syracuseStep 1344419 = 2016629) B2016629
theorem B1344449 : Blo 892572 1344449 := bstep (se 2 (by rfl) ⟨504168, by rfl⟩ : syracuseStep 1344449 = 1008337) B1008337
theorem B44172229 : Blo 892572 44172229 := bstep (se 4 (by rfl) ⟨4141146, by rfl⟩ : syracuseStep 44172229 = 8282293) B8282293
theorem B3015629 : Blo 892572 3015629 := bstep (se 3 (by rfl) ⟨565430, by rfl⟩ : syracuseStep 3015629 = 1130861) B1130861
theorem B1344467 : Blo 892572 1344467 := bstep (se 1 (by rfl) ⟨1008350, by rfl⟩ : syracuseStep 1344467 = 2016701) B2016701
theorem B1508321 : Blo 892572 1508321 := bstep (se 2 (by rfl) ⟨565620, by rfl⟩ : syracuseStep 1508321 = 1131241) B1131241
theorem B1344497 : Blo 892572 1344497 := bstep (se 2 (by rfl) ⟨504186, by rfl⟩ : syracuseStep 1344497 = 1008373) B1008373
theorem B3015683 : Blo 892572 3015683 := bstep (se 1 (by rfl) ⟨2261762, by rfl⟩ : syracuseStep 3015683 = 4523525) B4523525
theorem B1344515 : Blo 892572 1344515 := bstep (se 1 (by rfl) ⟨1008386, by rfl⟩ : syracuseStep 1344515 = 2016773) B2016773
theorem B1344545 : Blo 892572 1344545 := bstep (se 2 (by rfl) ⟨504204, by rfl⟩ : syracuseStep 1344545 = 1008409) B1008409
theorem B1344563 : Blo 892572 1344563 := bstep (se 1 (by rfl) ⟨1008422, by rfl⟩ : syracuseStep 1344563 = 2016845) B2016845
theorem B1344593 : Blo 892572 1344593 := bstep (se 2 (by rfl) ⟨504222, by rfl⟩ : syracuseStep 1344593 = 1008445) B1008445
theorem B1508449 : Blo 892572 1508449 := bstep (se 2 (by rfl) ⟨565668, by rfl⟩ : syracuseStep 1508449 = 1131337) B1131337
theorem B1344611 : Blo 892572 1344611 := bstep (se 1 (by rfl) ⟨1008458, by rfl⟩ : syracuseStep 1344611 = 2016917) B2016917
theorem B1344641 : Blo 892572 1344641 := bstep (se 2 (by rfl) ⟨504240, by rfl⟩ : syracuseStep 1344641 = 1008481) B1008481
theorem B1508483 : Blo 892572 1508483 := bstep (se 1 (by rfl) ⟨1131362, by rfl⟩ : syracuseStep 1508483 = 2262725) B2262725
theorem B1344659 : Blo 892572 1344659 := bstep (se 1 (by rfl) ⟨1008494, by rfl⟩ : syracuseStep 1344659 = 2016989) B2016989
theorem B1344689 : Blo 892572 1344689 := bstep (se 2 (by rfl) ⟨504258, by rfl⟩ : syracuseStep 1344689 = 1008517) B1008517
theorem B1344707 : Blo 892572 1344707 := bstep (se 1 (by rfl) ⟨1008530, by rfl⟩ : syracuseStep 1344707 = 2017061) B2017061
theorem B1344737 : Blo 892572 1344737 := bstep (se 2 (by rfl) ⟨504276, by rfl⟩ : syracuseStep 1344737 = 1008553) B1008553
theorem B1344755 : Blo 892572 1344755 := bstep (se 1 (by rfl) ⟨1008566, by rfl⟩ : syracuseStep 1344755 = 2017133) B2017133
theorem B1508611 : Blo 892572 1508611 := bstep (se 1 (by rfl) ⟨1131458, by rfl⟩ : syracuseStep 1508611 = 2262917) B2262917
theorem B3015953 : Blo 892572 3015953 := bstep (se 2 (by rfl) ⟨1130982, by rfl⟩ : syracuseStep 3015953 = 2261965) B2261965
theorem B2262289 : Blo 892572 2262289 := bstep (se 2 (by rfl) ⟨848358, by rfl⟩ : syracuseStep 2262289 = 1696717) B1696717
theorem B1344785 : Blo 892572 1344785 := bstep (se 2 (by rfl) ⟨504294, by rfl⟩ : syracuseStep 1344785 = 1008589) B1008589
theorem B1344803 : Blo 892572 1344803 := bstep (se 1 (by rfl) ⟨1008602, by rfl⟩ : syracuseStep 1344803 = 2017205) B2017205
theorem B1344833 : Blo 892572 1344833 := bstep (se 2 (by rfl) ⟨504312, by rfl⟩ : syracuseStep 1344833 = 1008625) B1008625
theorem B1344851 : Blo 892572 1344851 := bstep (se 1 (by rfl) ⟨1008638, by rfl⟩ : syracuseStep 1344851 = 2017277) B2017277
theorem B4523363 : Blo 892572 4523363 := bstep (se 1 (by rfl) ⟨3392522, by rfl⟩ : syracuseStep 4523363 = 6785045) B6785045
theorem B1508753 : Blo 892572 1508753 := bstep (se 2 (by rfl) ⟨565782, by rfl⟩ : syracuseStep 1508753 = 1131565) B1131565
theorem B1344929 : Blo 892572 1344929 := bstep (se 2 (by rfl) ⟨504348, by rfl⟩ : syracuseStep 1344929 = 1008697) B1008697
theorem B1148323 : Blo 892572 1148323 := bstep (se 1 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 1148323 = 1722485) B1722485
theorem B1508881 : Blo 892572 1508881 := bstep (se 2 (by rfl) ⟨565830, by rfl⟩ : syracuseStep 1508881 = 1131661) B1131661
theorem B2262563 : Blo 892572 2262563 := bstep (se 1 (by rfl) ⟨1696922, by rfl⟩ : syracuseStep 2262563 = 3393845) B3393845
theorem B1508915 : Blo 892572 1508915 := bstep (se 1 (by rfl) ⟨1131686, by rfl⟩ : syracuseStep 1508915 = 2263373) B2263373
theorem B1509043 : Blo 892572 1509043 := bstep (se 1 (by rfl) ⟨1131782, by rfl⟩ : syracuseStep 1509043 = 2263565) B2263565
theorem B2262755 : Blo 892572 2262755 := bstep (se 1 (by rfl) ⟨1697066, by rfl⟩ : syracuseStep 2262755 = 3394133) B3394133
theorem B3016493 : Blo 892572 3016493 := bstep (se 3 (by rfl) ⟨565592, by rfl⟩ : syracuseStep 3016493 = 1131185) B1131185
theorem B1509185 : Blo 892572 1509185 := bstep (se 2 (by rfl) ⟨565944, by rfl⟩ : syracuseStep 1509185 = 1131889) B1131889
theorem B3016547 : Blo 892572 3016547 := bstep (se 1 (by rfl) ⟨2262410, by rfl⟩ : syracuseStep 3016547 = 4524821) B4524821
theorem B1509313 : Blo 892572 1509313 := bstep (se 2 (by rfl) ⟨565992, by rfl⟩ : syracuseStep 1509313 = 1131985) B1131985
theorem B1509347 : Blo 892572 1509347 := bstep (se 1 (by rfl) ⟨1132010, by rfl⟩ : syracuseStep 1509347 = 2264021) B2264021
theorem B5736419 : Blo 892572 5736419 := bstep (se 1 (by rfl) ⟨4302314, by rfl⟩ : syracuseStep 5736419 = 8604629) B8604629
theorem B1017955 : Blo 892572 1017955 := bstep (se 1 (by rfl) ⟨763466, by rfl⟩ : syracuseStep 1017955 = 1526933) B1526933
theorem B1509475 : Blo 892572 1509475 := bstep (se 1 (by rfl) ⟨1132106, by rfl⟩ : syracuseStep 1509475 = 2264213) B2264213
theorem B3016817 : Blo 892572 3016817 := bstep (se 2 (by rfl) ⟨1131306, by rfl⟩ : syracuseStep 3016817 = 2262613) B2262613
theorem B4524173 : Blo 892572 4524173 := bstep (se 3 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 4524173 = 1696565) B1696565
theorem B75598051 : Blo 892572 75598051 := bstep (se 1 (by rfl) ⟨56698538, by rfl⟩ : syracuseStep 75598051 = 113397077) B113397077
theorem B1509617 : Blo 892572 1509617 := bstep (se 2 (by rfl) ⟨566106, by rfl⟩ : syracuseStep 1509617 = 1132213) B1132213
theorem B1509745 : Blo 892572 1509745 := bstep (se 2 (by rfl) ⟨566154, by rfl⟩ : syracuseStep 1509745 = 1132309) B1132309
theorem B1575299 : Blo 892572 1575299 := bstep (se 1 (by rfl) ⟨1181474, by rfl⟩ : syracuseStep 1575299 = 2362949) B2362949
theorem B1509779 : Blo 892572 1509779 := bstep (se 1 (by rfl) ⟨1132334, by rfl⟩ : syracuseStep 1509779 = 2264669) B2264669
theorem B1509907 : Blo 892572 1509907 := bstep (se 1 (by rfl) ⟨1132430, by rfl⟩ : syracuseStep 1509907 = 2264861) B2264861
theorem B2722339 : Blo 892572 2722339 := bstep (se 1 (by rfl) ⟨2041754, by rfl⟩ : syracuseStep 2722339 = 4083509) B4083509
theorem B3017357 : Blo 892572 3017357 := bstep (se 3 (by rfl) ⟨565754, by rfl⟩ : syracuseStep 3017357 = 1131509) B1131509
theorem B2263697 : Blo 892572 2263697 := bstep (se 2 (by rfl) ⟨848886, by rfl⟩ : syracuseStep 2263697 = 1697773) B1697773
theorem B1510049 : Blo 892572 1510049 := bstep (se 2 (by rfl) ⟨566268, by rfl⟩ : syracuseStep 1510049 = 1132537) B1132537
theorem B3017411 : Blo 892572 3017411 := bstep (se 1 (by rfl) ⟨2263058, by rfl⟩ : syracuseStep 3017411 = 4526117) B4526117
theorem B2263747 : Blo 892572 2263747 := bstep (se 1 (by rfl) ⟨1697810, by rfl⟩ : syracuseStep 2263747 = 3395621) B3395621
theorem B1510177 : Blo 892572 1510177 := bstep (se 2 (by rfl) ⟨566316, by rfl⟩ : syracuseStep 1510177 = 1132633) B1132633
theorem B1510211 : Blo 892572 1510211 := bstep (se 1 (by rfl) ⟨1132658, by rfl⟩ : syracuseStep 1510211 = 2265317) B2265317
theorem B2263889 : Blo 892572 2263889 := bstep (se 2 (by rfl) ⟨848958, by rfl⟩ : syracuseStep 2263889 = 1697917) B1697917
theorem B1510339 : Blo 892572 1510339 := bstep (se 1 (by rfl) ⟨1132754, by rfl⟩ : syracuseStep 1510339 = 2265509) B2265509
theorem B3017681 : Blo 892572 3017681 := bstep (se 2 (by rfl) ⟨1131630, by rfl⟩ : syracuseStep 3017681 = 2263261) B2263261
theorem B18385973 : Blo 892572 18385973 := bstep (se 5 (by rfl) ⟨861842, by rfl⟩ : syracuseStep 18385973 = 1723685) B1723685
theorem B1510481 : Blo 892572 1510481 := bstep (se 2 (by rfl) ⟨566430, by rfl⟩ : syracuseStep 1510481 = 1132861) B1132861
theorem B1608913 : Blo 892572 1608913 := bstep (se 2 (by rfl) ⟨603342, by rfl⟩ : syracuseStep 1608913 = 1206685) B1206685
theorem B1510609 : Blo 892572 1510609 := bstep (se 2 (by rfl) ⟨566478, by rfl⟩ : syracuseStep 1510609 = 1132957) B1132957
theorem B1510643 : Blo 892572 1510643 := bstep (se 1 (by rfl) ⟨1132982, by rfl⟩ : syracuseStep 1510643 = 2265965) B2265965
theorem B953699 : Blo 892572 953699 := bstep (se 1 (by rfl) ⟨715274, by rfl⟩ : syracuseStep 953699 = 1430549) B1430549
theorem B7638371 : Blo 892572 7638371 := bstep (se 1 (by rfl) ⟨5728778, by rfl⟩ : syracuseStep 7638371 = 11457557) B11457557
theorem B1510771 : Blo 892572 1510771 := bstep (se 1 (by rfl) ⟨1133078, by rfl⟩ : syracuseStep 1510771 = 2266157) B2266157
theorem B16289221 : Blo 892572 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B3018221 : Blo 892572 3018221 := bstep (se 3 (by rfl) ⟨565916, by rfl⟩ : syracuseStep 3018221 = 1131833) B1131833
theorem B1510913 : Blo 892572 1510913 := bstep (se 2 (by rfl) ⟨566592, by rfl⟩ : syracuseStep 1510913 = 1133185) B1133185
theorem B3018275 : Blo 892572 3018275 := bstep (se 1 (by rfl) ⟨2263706, by rfl⟩ : syracuseStep 3018275 = 4527413) B4527413
theorem B1511041 : Blo 892572 1511041 := bstep (se 2 (by rfl) ⟨566640, by rfl⟩ : syracuseStep 1511041 = 1133281) B1133281
theorem B1511075 : Blo 892572 1511075 := bstep (se 1 (by rfl) ⟨1133306, by rfl⟩ : syracuseStep 1511075 = 2266613) B2266613
theorem B1511203 : Blo 892572 1511203 := bstep (se 1 (by rfl) ⟨1133402, by rfl⟩ : syracuseStep 1511203 = 2266805) B2266805
theorem B3018545 : Blo 892572 3018545 := bstep (se 2 (by rfl) ⟨1131954, by rfl⟩ : syracuseStep 3018545 = 2263909) B2263909
theorem B2264881 : Blo 892572 2264881 := bstep (se 2 (by rfl) ⟨849330, by rfl⟩ : syracuseStep 2264881 = 1698661) B1698661
theorem B8589169 : Blo 892572 8589169 := bstep (se 2 (by rfl) ⟨3220938, by rfl⟩ : syracuseStep 8589169 = 6441877) B6441877
theorem B1511345 : Blo 892572 1511345 := bstep (se 2 (by rfl) ⟨566754, by rfl⟩ : syracuseStep 1511345 = 1133509) B1133509
theorem B1511473 : Blo 892572 1511473 := bstep (se 2 (by rfl) ⟨566802, by rfl⟩ : syracuseStep 1511473 = 1133605) B1133605
theorem B2265155 : Blo 892572 2265155 := bstep (se 1 (by rfl) ⟨1698866, by rfl⟩ : syracuseStep 2265155 = 3397733) B3397733
theorem B954451 : Blo 892572 954451 := bstep (se 1 (by rfl) ⟨715838, by rfl⟩ : syracuseStep 954451 = 1431677) B1431677
theorem B1511507 : Blo 892572 1511507 := bstep (se 1 (by rfl) ⟨1133630, by rfl⟩ : syracuseStep 1511507 = 2267261) B2267261
theorem B1511635 : Blo 892572 1511635 := bstep (se 1 (by rfl) ⟨1133726, by rfl⟩ : syracuseStep 1511635 = 2267453) B2267453
theorem B2265347 : Blo 892572 2265347 := bstep (se 1 (by rfl) ⟨1699010, by rfl⟩ : syracuseStep 2265347 = 3398021) B3398021
theorem B3019085 : Blo 892572 3019085 := bstep (se 3 (by rfl) ⟨566078, by rfl⟩ : syracuseStep 3019085 = 1132157) B1132157
theorem B1511777 : Blo 892572 1511777 := bstep (se 2 (by rfl) ⟨566916, by rfl⟩ : syracuseStep 1511777 = 1133833) B1133833
theorem B3019139 : Blo 892572 3019139 := bstep (se 1 (by rfl) ⟨2264354, by rfl⟩ : syracuseStep 3019139 = 4528709) B4528709
theorem B1511905 : Blo 892572 1511905 := bstep (se 2 (by rfl) ⟨566964, by rfl⟩ : syracuseStep 1511905 = 1133929) B1133929
theorem B1511939 : Blo 892572 1511939 := bstep (se 1 (by rfl) ⟨1133954, by rfl⟩ : syracuseStep 1511939 = 2267909) B2267909
theorem B1512067 : Blo 892572 1512067 := bstep (se 1 (by rfl) ⟨1134050, by rfl⟩ : syracuseStep 1512067 = 2268101) B2268101
theorem B3019409 : Blo 892572 3019409 := bstep (se 2 (by rfl) ⟨1132278, by rfl⟩ : syracuseStep 3019409 = 2264557) B2264557
theorem B1512209 : Blo 892572 1512209 := bstep (se 2 (by rfl) ⟨567078, by rfl⟩ : syracuseStep 1512209 = 1134157) B1134157
theorem B1512337 : Blo 892572 1512337 := bstep (se 2 (by rfl) ⟨567126, by rfl⟩ : syracuseStep 1512337 = 1134253) B1134253
theorem B1512371 : Blo 892572 1512371 := bstep (se 1 (by rfl) ⟨1134278, by rfl⟩ : syracuseStep 1512371 = 2268557) B2268557
theorem B4527089 : Blo 892572 4527089 := bstep (se 2 (by rfl) ⟨1697658, by rfl⟩ : syracuseStep 4527089 = 3395317) B3395317
theorem B1512499 : Blo 892572 1512499 := bstep (se 1 (by rfl) ⟨1134374, by rfl⟩ : syracuseStep 1512499 = 2268749) B2268749
theorem B955523 : Blo 892572 955523 := bstep (se 1 (by rfl) ⟨716642, by rfl⟩ : syracuseStep 955523 = 1433285) B1433285
theorem B3019949 : Blo 892572 3019949 := bstep (se 3 (by rfl) ⟨566240, by rfl⟩ : syracuseStep 3019949 = 1132481) B1132481
theorem B2266289 : Blo 892572 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B1512641 : Blo 892572 1512641 := bstep (se 2 (by rfl) ⟨567240, by rfl⟩ : syracuseStep 1512641 = 1134481) B1134481
theorem B3020003 : Blo 892572 3020003 := bstep (se 1 (by rfl) ⟨2265002, by rfl⟩ : syracuseStep 3020003 = 4530005) B4530005
theorem B2266339 : Blo 892572 2266339 := bstep (se 1 (by rfl) ⟨1699754, by rfl⟩ : syracuseStep 2266339 = 3399509) B3399509
theorem B1512769 : Blo 892572 1512769 := bstep (se 2 (by rfl) ⟨567288, by rfl⟩ : syracuseStep 1512769 = 1134577) B1134577
theorem B1381715 : Blo 892572 1381715 := bstep (se 1 (by rfl) ⟨1036286, by rfl⟩ : syracuseStep 1381715 = 2072573) B2072573
theorem B1512803 : Blo 892572 1512803 := bstep (se 1 (by rfl) ⟨1134602, by rfl⟩ : syracuseStep 1512803 = 2269205) B2269205
theorem B2266481 : Blo 892572 2266481 := bstep (se 2 (by rfl) ⟨849930, by rfl⟩ : syracuseStep 2266481 = 1699861) B1699861
theorem B1512931 : Blo 892572 1512931 := bstep (se 1 (by rfl) ⟨1134698, by rfl⟩ : syracuseStep 1512931 = 2269397) B2269397
theorem B3020273 : Blo 892572 3020273 := bstep (se 2 (by rfl) ⟨1132602, by rfl⟩ : syracuseStep 3020273 = 2265205) B2265205
theorem B4298275 : Blo 892572 4298275 := bstep (se 1 (by rfl) ⟨3223706, by rfl⟩ : syracuseStep 4298275 = 6447413) B6447413
theorem B1611523 : Blo 892572 1611523 := bstep (se 1 (by rfl) ⟨1208642, by rfl⟩ : syracuseStep 1611523 = 2417285) B2417285
theorem B2037521 : Blo 892572 2037521 := bstep (se 2 (by rfl) ⟨764070, by rfl⟩ : syracuseStep 2037521 = 1528141) B1528141
theorem B6788933 : Blo 892572 6788933 := bstep (se 4 (by rfl) ⟨636462, by rfl⟩ : syracuseStep 6788933 = 1272925) B1272925
theorem B5740465 : Blo 892572 5740465 := bstep (se 2 (by rfl) ⟨2152674, by rfl⟩ : syracuseStep 5740465 = 4305349) B4305349
theorem B1939459 : Blo 892572 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B3020813 : Blo 892572 3020813 := bstep (se 3 (by rfl) ⟨566402, by rfl⟩ : syracuseStep 3020813 = 1132805) B1132805
theorem B3020867 : Blo 892572 3020867 := bstep (se 1 (by rfl) ⟨2265650, by rfl⟩ : syracuseStep 3020867 = 4531301) B4531301
theorem B956659 : Blo 892572 956659 := bstep (se 1 (by rfl) ⟨717494, by rfl⟩ : syracuseStep 956659 = 1434989) B1434989
theorem B24254741 : Blo 892572 24254741 := bstep (se 6 (by rfl) ⟨568470, by rfl⟩ : syracuseStep 24254741 = 1136941) B1136941
theorem B3021137 : Blo 892572 3021137 := bstep (se 2 (by rfl) ⟨1132926, by rfl⟩ : syracuseStep 3021137 = 2265853) B2265853
theorem B2267473 : Blo 892572 2267473 := bstep (se 2 (by rfl) ⟨850302, by rfl⟩ : syracuseStep 2267473 = 1700605) B1700605
theorem B1907057 : Blo 892572 1907057 := bstep (se 2 (by rfl) ⟨715146, by rfl⟩ : syracuseStep 1907057 = 1430293) B1430293
theorem B4528547 : Blo 892572 4528547 := bstep (se 1 (by rfl) ⟨3396410, by rfl⟩ : syracuseStep 4528547 = 6792821) B6792821
theorem B4135373 : Blo 892572 4135373 := bstep (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) B1550765
theorem B4299277 : Blo 892572 4299277 := bstep (se 3 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 4299277 = 1612229) B1612229
theorem B2267747 : Blo 892572 2267747 := bstep (se 1 (by rfl) ⟨1700810, by rfl⟩ : syracuseStep 2267747 = 3401621) B3401621
theorem B2267939 : Blo 892572 2267939 := bstep (se 1 (by rfl) ⟨1700954, by rfl⟩ : syracuseStep 2267939 = 3401909) B3401909
theorem B3021677 : Blo 892572 3021677 := bstep (se 3 (by rfl) ⟨566564, by rfl⟩ : syracuseStep 3021677 = 1133129) B1133129
theorem B3021731 : Blo 892572 3021731 := bstep (se 1 (by rfl) ⟨2266298, by rfl⟩ : syracuseStep 3021731 = 4532597) B4532597
theorem B3022001 : Blo 892572 3022001 := bstep (se 2 (by rfl) ⟨1133250, by rfl⟩ : syracuseStep 3022001 = 2266501) B2266501
theorem B4529357 : Blo 892572 4529357 := bstep (se 3 (by rfl) ⟨849254, by rfl⟩ : syracuseStep 4529357 = 1698509) B1698509
theorem B5086597 : Blo 892572 5086597 := bstep (se 4 (by rfl) ⟨476868, by rfl⟩ : syracuseStep 5086597 = 953737) B953737
theorem B2760269 : Blo 892572 2760269 := bstep (se 3 (by rfl) ⟨517550, by rfl⟩ : syracuseStep 2760269 = 1035101) B1035101
theorem B1908355 : Blo 892572 1908355 := bstep (se 1 (by rfl) ⟨1431266, by rfl⟩ : syracuseStep 1908355 = 2862533) B2862533
theorem B892579 : Blo 892572 892579 := bstep (se 1 (by rfl) ⟨669434, by rfl⟩ : syracuseStep 892579 = 1338869) B1338869
theorem B892595 : Blo 892572 892595 := bstep (se 1 (by rfl) ⟨669446, by rfl⟩ : syracuseStep 892595 = 1338893) B1338893
theorem B10198709 : Blo 892572 10198709 := bstep (se 5 (by rfl) ⟨478064, by rfl⟩ : syracuseStep 10198709 = 956129) B956129
theorem B892611 : Blo 892572 892611 := bstep (se 1 (by rfl) ⟨669458, by rfl⟩ : syracuseStep 892611 = 1338917) B1338917
theorem B3022541 : Blo 892572 3022541 := bstep (se 3 (by rfl) ⟨566726, by rfl⟩ : syracuseStep 3022541 = 1133453) B1133453
theorem B2268881 : Blo 892572 2268881 := bstep (se 2 (by rfl) ⟨850830, by rfl⟩ : syracuseStep 2268881 = 1701661) B1701661
theorem B892627 : Blo 892572 892627 := bstep (se 1 (by rfl) ⟨669470, by rfl⟩ : syracuseStep 892627 = 1338941) B1338941
theorem B892643 : Blo 892572 892643 := bstep (se 1 (by rfl) ⟨669482, by rfl⟩ : syracuseStep 892643 = 1338965) B1338965
theorem B892659 : Blo 892572 892659 := bstep (se 1 (by rfl) ⟨669494, by rfl⟩ : syracuseStep 892659 = 1338989) B1338989
theorem B3022595 : Blo 892572 3022595 := bstep (se 1 (by rfl) ⟨2266946, by rfl⟩ : syracuseStep 3022595 = 4533893) B4533893
theorem B892675 : Blo 892572 892675 := bstep (se 1 (by rfl) ⟨669506, by rfl⟩ : syracuseStep 892675 = 1339013) B1339013
theorem B2268931 : Blo 892572 2268931 := bstep (se 1 (by rfl) ⟨1701698, by rfl⟩ : syracuseStep 2268931 = 3403397) B3403397
theorem B892691 : Blo 892572 892691 := bstep (se 1 (by rfl) ⟨669518, by rfl⟩ : syracuseStep 892691 = 1339037) B1339037
theorem B892707 : Blo 892572 892707 := bstep (se 1 (by rfl) ⟨669530, by rfl⟩ : syracuseStep 892707 = 1339061) B1339061
theorem B892723 : Blo 892572 892723 := bstep (se 1 (by rfl) ⟨669542, by rfl⟩ : syracuseStep 892723 = 1339085) B1339085
theorem B892739 : Blo 892572 892739 := bstep (se 1 (by rfl) ⟨669554, by rfl⟩ : syracuseStep 892739 = 1339109) B1339109
theorem B892755 : Blo 892572 892755 := bstep (se 1 (by rfl) ⟨669566, by rfl⟩ : syracuseStep 892755 = 1339133) B1339133
theorem B892771 : Blo 892572 892771 := bstep (se 1 (by rfl) ⟨669578, by rfl⟩ : syracuseStep 892771 = 1339157) B1339157
theorem B892787 : Blo 892572 892787 := bstep (se 1 (by rfl) ⟨669590, by rfl⟩ : syracuseStep 892787 = 1339181) B1339181
theorem B892803 : Blo 892572 892803 := bstep (se 1 (by rfl) ⟨669602, by rfl⟩ : syracuseStep 892803 = 1339205) B1339205
theorem B2269073 : Blo 892572 2269073 := bstep (se 2 (by rfl) ⟨850902, by rfl⟩ : syracuseStep 2269073 = 1701805) B1701805
theorem B892819 : Blo 892572 892819 := bstep (se 1 (by rfl) ⟨669614, by rfl⟩ : syracuseStep 892819 = 1339229) B1339229
theorem B892835 : Blo 892572 892835 := bstep (se 1 (by rfl) ⟨669626, by rfl⟩ : syracuseStep 892835 = 1339253) B1339253
theorem B4300721 : Blo 892572 4300721 := bstep (se 2 (by rfl) ⟨1612770, by rfl⟩ : syracuseStep 4300721 = 3225541) B3225541
theorem B892851 : Blo 892572 892851 := bstep (se 1 (by rfl) ⟨669638, by rfl⟩ : syracuseStep 892851 = 1339277) B1339277
theorem B892867 : Blo 892572 892867 := bstep (se 1 (by rfl) ⟨669650, by rfl⟩ : syracuseStep 892867 = 1339301) B1339301
theorem B892883 : Blo 892572 892883 := bstep (se 1 (by rfl) ⟨669662, by rfl⟩ : syracuseStep 892883 = 1339325) B1339325
theorem B892899 : Blo 892572 892899 := bstep (se 1 (by rfl) ⟨669674, by rfl⟩ : syracuseStep 892899 = 1339349) B1339349
theorem B892915 : Blo 892572 892915 := bstep (se 1 (by rfl) ⟨669686, by rfl⟩ : syracuseStep 892915 = 1339373) B1339373
theorem B892931 : Blo 892572 892931 := bstep (se 1 (by rfl) ⟨669698, by rfl⟩ : syracuseStep 892931 = 1339397) B1339397
theorem B3022865 : Blo 892572 3022865 := bstep (se 2 (by rfl) ⟨1133574, by rfl⟩ : syracuseStep 3022865 = 2267149) B2267149
theorem B892947 : Blo 892572 892947 := bstep (se 1 (by rfl) ⟨669710, by rfl⟩ : syracuseStep 892947 = 1339421) B1339421
theorem B892963 : Blo 892572 892963 := bstep (se 1 (by rfl) ⟨669722, by rfl⟩ : syracuseStep 892963 = 1339445) B1339445
theorem B892979 : Blo 892572 892979 := bstep (se 1 (by rfl) ⟨669734, by rfl⟩ : syracuseStep 892979 = 1339469) B1339469
theorem B892995 : Blo 892572 892995 := bstep (se 1 (by rfl) ⟨669746, by rfl⟩ : syracuseStep 892995 = 1339493) B1339493
theorem B893011 : Blo 892572 893011 := bstep (se 1 (by rfl) ⟨669758, by rfl⟩ : syracuseStep 893011 = 1339517) B1339517
theorem B893027 : Blo 892572 893027 := bstep (se 1 (by rfl) ⟨669770, by rfl⟩ : syracuseStep 893027 = 1339541) B1339541
theorem B893043 : Blo 892572 893043 := bstep (se 1 (by rfl) ⟨669782, by rfl⟩ : syracuseStep 893043 = 1339565) B1339565
theorem B893059 : Blo 892572 893059 := bstep (se 1 (by rfl) ⟨669794, by rfl⟩ : syracuseStep 893059 = 1339589) B1339589
theorem B893075 : Blo 892572 893075 := bstep (se 1 (by rfl) ⟨669806, by rfl⟩ : syracuseStep 893075 = 1339613) B1339613
theorem B893091 : Blo 892572 893091 := bstep (se 1 (by rfl) ⟨669818, by rfl⟩ : syracuseStep 893091 = 1339637) B1339637
theorem B893107 : Blo 892572 893107 := bstep (se 1 (by rfl) ⟨669830, by rfl⟩ : syracuseStep 893107 = 1339661) B1339661
theorem B893123 : Blo 892572 893123 := bstep (se 1 (by rfl) ⟨669842, by rfl⟩ : syracuseStep 893123 = 1339685) B1339685
theorem B10887365 : Blo 892572 10887365 := bstep (se 4 (by rfl) ⟨1020690, by rfl⟩ : syracuseStep 10887365 = 2041381) B2041381
theorem B893139 : Blo 892572 893139 := bstep (se 1 (by rfl) ⟨669854, by rfl⟩ : syracuseStep 893139 = 1339709) B1339709
theorem B893155 : Blo 892572 893155 := bstep (se 1 (by rfl) ⟨669866, by rfl⟩ : syracuseStep 893155 = 1339733) B1339733
theorem B893171 : Blo 892572 893171 := bstep (se 1 (by rfl) ⟨669878, by rfl⟩ : syracuseStep 893171 = 1339757) B1339757
theorem B893187 : Blo 892572 893187 := bstep (se 1 (by rfl) ⟨669890, by rfl⟩ : syracuseStep 893187 = 1339781) B1339781
theorem B893203 : Blo 892572 893203 := bstep (se 1 (by rfl) ⟨669902, by rfl⟩ : syracuseStep 893203 = 1339805) B1339805
theorem B893219 : Blo 892572 893219 := bstep (se 1 (by rfl) ⟨669914, by rfl⟩ : syracuseStep 893219 = 1339829) B1339829
theorem B2040113 : Blo 892572 2040113 := bstep (se 2 (by rfl) ⟨765042, by rfl⟩ : syracuseStep 2040113 = 1530085) B1530085
theorem B893235 : Blo 892572 893235 := bstep (se 1 (by rfl) ⟨669926, by rfl⟩ : syracuseStep 893235 = 1339853) B1339853
theorem B893251 : Blo 892572 893251 := bstep (se 1 (by rfl) ⟨669938, by rfl⟩ : syracuseStep 893251 = 1339877) B1339877
theorem B893267 : Blo 892572 893267 := bstep (se 1 (by rfl) ⟨669950, by rfl⟩ : syracuseStep 893267 = 1339901) B1339901
theorem B893283 : Blo 892572 893283 := bstep (se 1 (by rfl) ⟨669962, by rfl⟩ : syracuseStep 893283 = 1339925) B1339925
theorem B893299 : Blo 892572 893299 := bstep (se 1 (by rfl) ⟨669974, by rfl⟩ : syracuseStep 893299 = 1339949) B1339949
theorem B893315 : Blo 892572 893315 := bstep (se 1 (by rfl) ⟨669986, by rfl⟩ : syracuseStep 893315 = 1339973) B1339973
theorem B1614211 : Blo 892572 1614211 := bstep (se 1 (by rfl) ⟨1210658, by rfl⟩ : syracuseStep 1614211 = 2421317) B2421317
theorem B893331 : Blo 892572 893331 := bstep (se 1 (by rfl) ⟨669998, by rfl⟩ : syracuseStep 893331 = 1339997) B1339997
theorem B893347 : Blo 892572 893347 := bstep (se 1 (by rfl) ⟨670010, by rfl⟩ : syracuseStep 893347 = 1340021) B1340021
theorem B2040241 : Blo 892572 2040241 := bstep (se 2 (by rfl) ⟨765090, by rfl⟩ : syracuseStep 2040241 = 1530181) B1530181
theorem B893363 : Blo 892572 893363 := bstep (se 1 (by rfl) ⟨670022, by rfl⟩ : syracuseStep 893363 = 1340045) B1340045
theorem B10887605 : Blo 892572 10887605 := bstep (se 5 (by rfl) ⟨510356, by rfl⟩ : syracuseStep 10887605 = 1020713) B1020713
theorem B893379 : Blo 892572 893379 := bstep (se 1 (by rfl) ⟨670034, by rfl⟩ : syracuseStep 893379 = 1340069) B1340069
theorem B893395 : Blo 892572 893395 := bstep (se 1 (by rfl) ⟨670046, by rfl⟩ : syracuseStep 893395 = 1340093) B1340093
theorem B893411 : Blo 892572 893411 := bstep (se 1 (by rfl) ⟨670058, by rfl⟩ : syracuseStep 893411 = 1340117) B1340117
theorem B893427 : Blo 892572 893427 := bstep (se 1 (by rfl) ⟨670070, by rfl⟩ : syracuseStep 893427 = 1340141) B1340141
theorem B893443 : Blo 892572 893443 := bstep (se 1 (by rfl) ⟨670082, by rfl⟩ : syracuseStep 893443 = 1340165) B1340165
theorem B893459 : Blo 892572 893459 := bstep (se 1 (by rfl) ⟨670094, by rfl⟩ : syracuseStep 893459 = 1340189) B1340189
theorem B893475 : Blo 892572 893475 := bstep (se 1 (by rfl) ⟨670106, by rfl⟩ : syracuseStep 893475 = 1340213) B1340213
theorem B3023405 : Blo 892572 3023405 := bstep (se 3 (by rfl) ⟨566888, by rfl⟩ : syracuseStep 3023405 = 1133777) B1133777
theorem B893491 : Blo 892572 893491 := bstep (se 1 (by rfl) ⟨670118, by rfl⟩ : syracuseStep 893491 = 1340237) B1340237
theorem B893507 : Blo 892572 893507 := bstep (se 1 (by rfl) ⟨670130, by rfl⟩ : syracuseStep 893507 = 1340261) B1340261
theorem B893523 : Blo 892572 893523 := bstep (se 1 (by rfl) ⟨670142, by rfl⟩ : syracuseStep 893523 = 1340285) B1340285
theorem B893539 : Blo 892572 893539 := bstep (se 1 (by rfl) ⟨670154, by rfl⟩ : syracuseStep 893539 = 1340309) B1340309
theorem B3023459 : Blo 892572 3023459 := bstep (se 1 (by rfl) ⟨2267594, by rfl⟩ : syracuseStep 3023459 = 4535189) B4535189
theorem B4661873 : Blo 892572 4661873 := bstep (se 2 (by rfl) ⟨1748202, by rfl⟩ : syracuseStep 4661873 = 3496405) B3496405
theorem B893555 : Blo 892572 893555 := bstep (se 1 (by rfl) ⟨670166, by rfl⟩ : syracuseStep 893555 = 1340333) B1340333
theorem B893571 : Blo 892572 893571 := bstep (se 1 (by rfl) ⟨670178, by rfl⟩ : syracuseStep 893571 = 1340357) B1340357
theorem B893587 : Blo 892572 893587 := bstep (se 1 (by rfl) ⟨670190, by rfl⟩ : syracuseStep 893587 = 1340381) B1340381
theorem B893603 : Blo 892572 893603 := bstep (se 1 (by rfl) ⟨670202, by rfl⟩ : syracuseStep 893603 = 1340405) B1340405
theorem B893619 : Blo 892572 893619 := bstep (se 1 (by rfl) ⟨670214, by rfl⟩ : syracuseStep 893619 = 1340429) B1340429
theorem B893635 : Blo 892572 893635 := bstep (se 1 (by rfl) ⟨670226, by rfl⟩ : syracuseStep 893635 = 1340453) B1340453
theorem B2859725 : Blo 892572 2859725 := bstep (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) B1072397
theorem B893651 : Blo 892572 893651 := bstep (se 1 (by rfl) ⟨670238, by rfl⟩ : syracuseStep 893651 = 1340477) B1340477
theorem B893667 : Blo 892572 893667 := bstep (se 1 (by rfl) ⟨670250, by rfl⟩ : syracuseStep 893667 = 1340501) B1340501
theorem B893683 : Blo 892572 893683 := bstep (se 1 (by rfl) ⟨670262, by rfl⟩ : syracuseStep 893683 = 1340525) B1340525
theorem B893699 : Blo 892572 893699 := bstep (se 1 (by rfl) ⟨670274, by rfl⟩ : syracuseStep 893699 = 1340549) B1340549
theorem B893715 : Blo 892572 893715 := bstep (se 1 (by rfl) ⟨670286, by rfl⟩ : syracuseStep 893715 = 1340573) B1340573
theorem B893731 : Blo 892572 893731 := bstep (se 1 (by rfl) ⟨670298, by rfl⟩ : syracuseStep 893731 = 1340597) B1340597
theorem B893747 : Blo 892572 893747 := bstep (se 1 (by rfl) ⟨670310, by rfl⟩ : syracuseStep 893747 = 1340621) B1340621
theorem B893763 : Blo 892572 893763 := bstep (se 1 (by rfl) ⟨670322, by rfl⟩ : syracuseStep 893763 = 1340645) B1340645
theorem B1909585 : Blo 892572 1909585 := bstep (se 2 (by rfl) ⟨716094, by rfl⟩ : syracuseStep 1909585 = 1432189) B1432189
theorem B893779 : Blo 892572 893779 := bstep (se 1 (by rfl) ⟨670334, by rfl⟩ : syracuseStep 893779 = 1340669) B1340669
theorem B893795 : Blo 892572 893795 := bstep (se 1 (by rfl) ⟨670346, by rfl⟩ : syracuseStep 893795 = 1340693) B1340693
theorem B3023729 : Blo 892572 3023729 := bstep (se 2 (by rfl) ⟨1133898, by rfl⟩ : syracuseStep 3023729 = 2267797) B2267797
theorem B893811 : Blo 892572 893811 := bstep (se 1 (by rfl) ⟨670358, by rfl⟩ : syracuseStep 893811 = 1340717) B1340717
theorem B893827 : Blo 892572 893827 := bstep (se 1 (by rfl) ⟨670370, by rfl⟩ : syracuseStep 893827 = 1340741) B1340741
theorem B893843 : Blo 892572 893843 := bstep (se 1 (by rfl) ⟨670382, by rfl⟩ : syracuseStep 893843 = 1340765) B1340765
theorem B893859 : Blo 892572 893859 := bstep (se 1 (by rfl) ⟨670394, by rfl⟩ : syracuseStep 893859 = 1340789) B1340789
theorem B893875 : Blo 892572 893875 := bstep (se 1 (by rfl) ⟨670406, by rfl⟩ : syracuseStep 893875 = 1340813) B1340813
theorem B893891 : Blo 892572 893891 := bstep (se 1 (by rfl) ⟨670418, by rfl⟩ : syracuseStep 893891 = 1340837) B1340837
theorem B893907 : Blo 892572 893907 := bstep (se 1 (by rfl) ⟨670430, by rfl⟩ : syracuseStep 893907 = 1340861) B1340861
theorem B893923 : Blo 892572 893923 := bstep (se 1 (by rfl) ⟨670442, by rfl⟩ : syracuseStep 893923 = 1340885) B1340885
theorem B893939 : Blo 892572 893939 := bstep (se 1 (by rfl) ⟨670454, by rfl⟩ : syracuseStep 893939 = 1340909) B1340909
theorem B893955 : Blo 892572 893955 := bstep (se 1 (by rfl) ⟨670466, by rfl⟩ : syracuseStep 893955 = 1340933) B1340933
theorem B893971 : Blo 892572 893971 := bstep (se 1 (by rfl) ⟨670478, by rfl⟩ : syracuseStep 893971 = 1340957) B1340957
theorem B893987 : Blo 892572 893987 := bstep (se 1 (by rfl) ⟨670490, by rfl⟩ : syracuseStep 893987 = 1340981) B1340981
theorem B894003 : Blo 892572 894003 := bstep (se 1 (by rfl) ⟨670502, by rfl⟩ : syracuseStep 894003 = 1341005) B1341005
theorem B894019 : Blo 892572 894019 := bstep (se 1 (by rfl) ⟨670514, by rfl⟩ : syracuseStep 894019 = 1341029) B1341029
theorem B894035 : Blo 892572 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B894051 : Blo 892572 894051 := bstep (se 1 (by rfl) ⟨670538, by rfl⟩ : syracuseStep 894051 = 1341077) B1341077
theorem B894067 : Blo 892572 894067 := bstep (se 1 (by rfl) ⟨670550, by rfl⟩ : syracuseStep 894067 = 1341101) B1341101
theorem B894083 : Blo 892572 894083 := bstep (se 1 (by rfl) ⟨670562, by rfl⟩ : syracuseStep 894083 = 1341125) B1341125
theorem B894099 : Blo 892572 894099 := bstep (se 1 (by rfl) ⟨670574, by rfl⟩ : syracuseStep 894099 = 1341149) B1341149
theorem B894115 : Blo 892572 894115 := bstep (se 1 (by rfl) ⟨670586, by rfl⟩ : syracuseStep 894115 = 1341173) B1341173
theorem B894131 : Blo 892572 894131 := bstep (se 1 (by rfl) ⟨670598, by rfl⟩ : syracuseStep 894131 = 1341197) B1341197
theorem B894147 : Blo 892572 894147 := bstep (se 1 (by rfl) ⟨670610, by rfl⟩ : syracuseStep 894147 = 1341221) B1341221
theorem B894163 : Blo 892572 894163 := bstep (se 1 (by rfl) ⟨670622, by rfl⟩ : syracuseStep 894163 = 1341245) B1341245
theorem B894179 : Blo 892572 894179 := bstep (se 1 (by rfl) ⟨670634, by rfl⟩ : syracuseStep 894179 = 1341269) B1341269
theorem B894195 : Blo 892572 894195 := bstep (se 1 (by rfl) ⟨670646, by rfl⟩ : syracuseStep 894195 = 1341293) B1341293
theorem B894211 : Blo 892572 894211 := bstep (se 1 (by rfl) ⟨670658, by rfl⟩ : syracuseStep 894211 = 1341317) B1341317
theorem B894227 : Blo 892572 894227 := bstep (se 1 (by rfl) ⟨670670, by rfl⟩ : syracuseStep 894227 = 1341341) B1341341
theorem B894243 : Blo 892572 894243 := bstep (se 1 (by rfl) ⟨670682, by rfl⟩ : syracuseStep 894243 = 1341365) B1341365
theorem B894259 : Blo 892572 894259 := bstep (se 1 (by rfl) ⟨670694, by rfl⟩ : syracuseStep 894259 = 1341389) B1341389
theorem B894275 : Blo 892572 894275 := bstep (se 1 (by rfl) ⟨670706, by rfl⟩ : syracuseStep 894275 = 1341413) B1341413
theorem B5088581 : Blo 892572 5088581 := bstep (se 4 (by rfl) ⟨477054, by rfl⟩ : syracuseStep 5088581 = 954109) B954109
theorem B894291 : Blo 892572 894291 := bstep (se 1 (by rfl) ⟨670718, by rfl⟩ : syracuseStep 894291 = 1341437) B1341437
theorem B894307 : Blo 892572 894307 := bstep (se 1 (by rfl) ⟨670730, by rfl⟩ : syracuseStep 894307 = 1341461) B1341461
theorem B894323 : Blo 892572 894323 := bstep (se 1 (by rfl) ⟨670742, by rfl⟩ : syracuseStep 894323 = 1341485) B1341485
theorem B894339 : Blo 892572 894339 := bstep (se 1 (by rfl) ⟨670754, by rfl⟩ : syracuseStep 894339 = 1341509) B1341509
theorem B3024269 : Blo 892572 3024269 := bstep (se 3 (by rfl) ⟨567050, by rfl⟩ : syracuseStep 3024269 = 1134101) B1134101
theorem B894355 : Blo 892572 894355 := bstep (se 1 (by rfl) ⟨670766, by rfl⟩ : syracuseStep 894355 = 1341533) B1341533
theorem B894371 : Blo 892572 894371 := bstep (se 1 (by rfl) ⟨670778, by rfl⟩ : syracuseStep 894371 = 1341557) B1341557
theorem B894387 : Blo 892572 894387 := bstep (se 1 (by rfl) ⟨670790, by rfl⟩ : syracuseStep 894387 = 1341581) B1341581
theorem B894403 : Blo 892572 894403 := bstep (se 1 (by rfl) ⟨670802, by rfl⟩ : syracuseStep 894403 = 1341605) B1341605
theorem B3024323 : Blo 892572 3024323 := bstep (se 1 (by rfl) ⟨2268242, by rfl⟩ : syracuseStep 3024323 = 4536485) B4536485
theorem B11478469 : Blo 892572 11478469 := bstep (se 4 (by rfl) ⟨1076106, by rfl⟩ : syracuseStep 11478469 = 2152213) B2152213
theorem B2008529 : Blo 892572 2008529 := bstep (se 2 (by rfl) ⟨753198, by rfl⟩ : syracuseStep 2008529 = 1506397) B1506397
theorem B894419 : Blo 892572 894419 := bstep (se 1 (by rfl) ⟨670814, by rfl⟩ : syracuseStep 894419 = 1341629) B1341629
theorem B2008547 : Blo 892572 2008547 := bstep (se 1 (by rfl) ⟨1506410, by rfl⟩ : syracuseStep 2008547 = 3012821) B3012821
theorem B1910243 : Blo 892572 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B894435 : Blo 892572 894435 := bstep (se 1 (by rfl) ⟨670826, by rfl⟩ : syracuseStep 894435 = 1341653) B1341653
theorem B894451 : Blo 892572 894451 := bstep (se 1 (by rfl) ⟨670838, by rfl⟩ : syracuseStep 894451 = 1341677) B1341677
theorem B894467 : Blo 892572 894467 := bstep (se 1 (by rfl) ⟨670850, by rfl⟩ : syracuseStep 894467 = 1341701) B1341701
theorem B894483 : Blo 892572 894483 := bstep (se 1 (by rfl) ⟨670862, by rfl⟩ : syracuseStep 894483 = 1341725) B1341725
theorem B894499 : Blo 892572 894499 := bstep (se 1 (by rfl) ⟨670874, by rfl⟩ : syracuseStep 894499 = 1341749) B1341749
theorem B3221041 : Blo 892572 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B894515 : Blo 892572 894515 := bstep (se 1 (by rfl) ⟨670886, by rfl⟩ : syracuseStep 894515 = 1341773) B1341773
theorem B894531 : Blo 892572 894531 := bstep (se 1 (by rfl) ⟨670898, by rfl⟩ : syracuseStep 894531 = 1341797) B1341797
theorem B894547 : Blo 892572 894547 := bstep (se 1 (by rfl) ⟨670910, by rfl⟩ : syracuseStep 894547 = 1341821) B1341821
theorem B894563 : Blo 892572 894563 := bstep (se 1 (by rfl) ⟨670922, by rfl⟩ : syracuseStep 894563 = 1341845) B1341845
theorem B1615459 : Blo 892572 1615459 := bstep (se 1 (by rfl) ⟨1211594, by rfl⟩ : syracuseStep 1615459 = 2423189) B2423189
theorem B894579 : Blo 892572 894579 := bstep (se 1 (by rfl) ⟨670934, by rfl⟩ : syracuseStep 894579 = 1341869) B1341869
theorem B894595 : Blo 892572 894595 := bstep (se 1 (by rfl) ⟨670946, by rfl⟩ : syracuseStep 894595 = 1341893) B1341893
theorem B18327181 : Blo 892572 18327181 := bstep (se 3 (by rfl) ⟨3436346, by rfl⟩ : syracuseStep 18327181 = 6872693) B6872693
theorem B894611 : Blo 892572 894611 := bstep (se 1 (by rfl) ⟨670958, by rfl⟩ : syracuseStep 894611 = 1341917) B1341917
theorem B894627 : Blo 892572 894627 := bstep (se 1 (by rfl) ⟨670970, by rfl⟩ : syracuseStep 894627 = 1341941) B1341941
theorem B894643 : Blo 892572 894643 := bstep (se 1 (by rfl) ⟨670982, by rfl⟩ : syracuseStep 894643 = 1341965) B1341965
theorem B894659 : Blo 892572 894659 := bstep (se 1 (by rfl) ⟨670994, by rfl⟩ : syracuseStep 894659 = 1341989) B1341989
theorem B3024593 : Blo 892572 3024593 := bstep (se 2 (by rfl) ⟨1134222, by rfl⟩ : syracuseStep 3024593 = 2268445) B2268445
theorem B894675 : Blo 892572 894675 := bstep (se 1 (by rfl) ⟨671006, by rfl⟩ : syracuseStep 894675 = 1342013) B1342013
theorem B894691 : Blo 892572 894691 := bstep (se 1 (by rfl) ⟨671018, by rfl⟩ : syracuseStep 894691 = 1342037) B1342037
theorem B2008817 : Blo 892572 2008817 := bstep (se 2 (by rfl) ⟨753306, by rfl⟩ : syracuseStep 2008817 = 1506613) B1506613
theorem B894707 : Blo 892572 894707 := bstep (se 1 (by rfl) ⟨671030, by rfl⟩ : syracuseStep 894707 = 1342061) B1342061
theorem B2008835 : Blo 892572 2008835 := bstep (se 1 (by rfl) ⟨1506626, by rfl⟩ : syracuseStep 2008835 = 3013253) B3013253
theorem B894723 : Blo 892572 894723 := bstep (se 1 (by rfl) ⟨671042, by rfl⟩ : syracuseStep 894723 = 1342085) B1342085
theorem B894739 : Blo 892572 894739 := bstep (se 1 (by rfl) ⟨671054, by rfl⟩ : syracuseStep 894739 = 1342109) B1342109
theorem B894755 : Blo 892572 894755 := bstep (se 1 (by rfl) ⟨671066, by rfl⟩ : syracuseStep 894755 = 1342133) B1342133
theorem B894771 : Blo 892572 894771 := bstep (se 1 (by rfl) ⟨671078, by rfl⟩ : syracuseStep 894771 = 1342157) B1342157
theorem B894787 : Blo 892572 894787 := bstep (se 1 (by rfl) ⟨671090, by rfl⟩ : syracuseStep 894787 = 1342181) B1342181
theorem B894803 : Blo 892572 894803 := bstep (se 1 (by rfl) ⟨671102, by rfl⟩ : syracuseStep 894803 = 1342205) B1342205
theorem B894819 : Blo 892572 894819 := bstep (se 1 (by rfl) ⟨671114, by rfl⟩ : syracuseStep 894819 = 1342229) B1342229
theorem B894835 : Blo 892572 894835 := bstep (se 1 (by rfl) ⟨671126, by rfl⟩ : syracuseStep 894835 = 1342253) B1342253
theorem B894851 : Blo 892572 894851 := bstep (se 1 (by rfl) ⟨671138, by rfl⟩ : syracuseStep 894851 = 1342277) B1342277
theorem B894867 : Blo 892572 894867 := bstep (se 1 (by rfl) ⟨671150, by rfl⟩ : syracuseStep 894867 = 1342301) B1342301
theorem B894883 : Blo 892572 894883 := bstep (se 1 (by rfl) ⟨671162, by rfl⟩ : syracuseStep 894883 = 1342325) B1342325
theorem B894899 : Blo 892572 894899 := bstep (se 1 (by rfl) ⟨671174, by rfl⟩ : syracuseStep 894899 = 1342349) B1342349
theorem B894915 : Blo 892572 894915 := bstep (se 1 (by rfl) ⟨671186, by rfl⟩ : syracuseStep 894915 = 1342373) B1342373
theorem B894931 : Blo 892572 894931 := bstep (se 1 (by rfl) ⟨671198, by rfl⟩ : syracuseStep 894931 = 1342397) B1342397
theorem B894947 : Blo 892572 894947 := bstep (se 1 (by rfl) ⟨671210, by rfl⟩ : syracuseStep 894947 = 1342421) B1342421
theorem B894963 : Blo 892572 894963 := bstep (se 1 (by rfl) ⟨671222, by rfl⟩ : syracuseStep 894963 = 1342445) B1342445
theorem B894979 : Blo 892572 894979 := bstep (se 1 (by rfl) ⟨671234, by rfl⟩ : syracuseStep 894979 = 1342469) B1342469
theorem B2009105 : Blo 892572 2009105 := bstep (se 2 (by rfl) ⟨753414, by rfl⟩ : syracuseStep 2009105 = 1506829) B1506829
theorem B894995 : Blo 892572 894995 := bstep (se 1 (by rfl) ⟨671246, by rfl⟩ : syracuseStep 894995 = 1342493) B1342493
theorem B2009123 : Blo 892572 2009123 := bstep (se 1 (by rfl) ⟨1506842, by rfl⟩ : syracuseStep 2009123 = 3013685) B3013685
theorem B895011 : Blo 892572 895011 := bstep (se 1 (by rfl) ⟨671258, by rfl⟩ : syracuseStep 895011 = 1342517) B1342517
theorem B4532273 : Blo 892572 4532273 := bstep (se 2 (by rfl) ⟨1699602, by rfl⟩ : syracuseStep 4532273 = 3399205) B3399205
theorem B895027 : Blo 892572 895027 := bstep (se 1 (by rfl) ⟨671270, by rfl⟩ : syracuseStep 895027 = 1342541) B1342541
theorem B895043 : Blo 892572 895043 := bstep (se 1 (by rfl) ⟨671282, by rfl⟩ : syracuseStep 895043 = 1342565) B1342565
theorem B895059 : Blo 892572 895059 := bstep (se 1 (by rfl) ⟨671294, by rfl⟩ : syracuseStep 895059 = 1342589) B1342589
theorem B895075 : Blo 892572 895075 := bstep (se 1 (by rfl) ⟨671306, by rfl⟩ : syracuseStep 895075 = 1342613) B1342613
theorem B10889315 : Blo 892572 10889315 := bstep (se 1 (by rfl) ⟨8166986, by rfl⟩ : syracuseStep 10889315 = 16333973) B16333973
theorem B895091 : Blo 892572 895091 := bstep (se 1 (by rfl) ⟨671318, by rfl⟩ : syracuseStep 895091 = 1342637) B1342637
theorem B895107 : Blo 892572 895107 := bstep (se 1 (by rfl) ⟨671330, by rfl⟩ : syracuseStep 895107 = 1342661) B1342661
theorem B895123 : Blo 892572 895123 := bstep (se 1 (by rfl) ⟨671342, by rfl⟩ : syracuseStep 895123 = 1342685) B1342685
theorem B895139 : Blo 892572 895139 := bstep (se 1 (by rfl) ⟨671354, by rfl⟩ : syracuseStep 895139 = 1342709) B1342709
theorem B895155 : Blo 892572 895155 := bstep (se 1 (by rfl) ⟨671366, by rfl⟩ : syracuseStep 895155 = 1342733) B1342733
theorem B895171 : Blo 892572 895171 := bstep (se 1 (by rfl) ⟨671378, by rfl⟩ : syracuseStep 895171 = 1342757) B1342757
theorem B895187 : Blo 892572 895187 := bstep (se 1 (by rfl) ⟨671390, by rfl⟩ : syracuseStep 895187 = 1342781) B1342781
theorem B895203 : Blo 892572 895203 := bstep (se 1 (by rfl) ⟨671402, by rfl⟩ : syracuseStep 895203 = 1342805) B1342805
theorem B3025133 : Blo 892572 3025133 := bstep (se 3 (by rfl) ⟨567212, by rfl⟩ : syracuseStep 3025133 = 1134425) B1134425
theorem B895219 : Blo 892572 895219 := bstep (se 1 (by rfl) ⟨671414, by rfl⟩ : syracuseStep 895219 = 1342829) B1342829
theorem B2861315 : Blo 892572 2861315 := bstep (se 1 (by rfl) ⟨2145986, by rfl⟩ : syracuseStep 2861315 = 4291973) B4291973
theorem B895235 : Blo 892572 895235 := bstep (se 1 (by rfl) ⟨671426, by rfl⟩ : syracuseStep 895235 = 1342853) B1342853
theorem B895251 : Blo 892572 895251 := bstep (se 1 (by rfl) ⟨671438, by rfl⟩ : syracuseStep 895251 = 1342877) B1342877
theorem B895267 : Blo 892572 895267 := bstep (se 1 (by rfl) ⟨671450, by rfl⟩ : syracuseStep 895267 = 1342901) B1342901
theorem B3025187 : Blo 892572 3025187 := bstep (se 1 (by rfl) ⟨2268890, by rfl⟩ : syracuseStep 3025187 = 4537781) B4537781
theorem B2009393 : Blo 892572 2009393 := bstep (se 2 (by rfl) ⟨753522, by rfl⟩ : syracuseStep 2009393 = 1507045) B1507045
theorem B1911089 : Blo 892572 1911089 := bstep (se 2 (by rfl) ⟨716658, by rfl⟩ : syracuseStep 1911089 = 1433317) B1433317
theorem B895283 : Blo 892572 895283 := bstep (se 1 (by rfl) ⟨671462, by rfl⟩ : syracuseStep 895283 = 1342925) B1342925
theorem B1550657 : Blo 892572 1550657 := bstep (se 2 (by rfl) ⟨581496, by rfl⟩ : syracuseStep 1550657 = 1162993) B1162993
theorem B2009411 : Blo 892572 2009411 := bstep (se 1 (by rfl) ⟨1507058, by rfl⟩ : syracuseStep 2009411 = 3014117) B3014117
theorem B895299 : Blo 892572 895299 := bstep (se 1 (by rfl) ⟨671474, by rfl⟩ : syracuseStep 895299 = 1342949) B1342949
theorem B895315 : Blo 892572 895315 := bstep (se 1 (by rfl) ⟨671486, by rfl⟩ : syracuseStep 895315 = 1342973) B1342973
theorem B895331 : Blo 892572 895331 := bstep (se 1 (by rfl) ⟨671498, by rfl⟩ : syracuseStep 895331 = 1342997) B1342997
theorem B895347 : Blo 892572 895347 := bstep (se 1 (by rfl) ⟨671510, by rfl⟩ : syracuseStep 895347 = 1343021) B1343021
theorem B895363 : Blo 892572 895363 := bstep (se 1 (by rfl) ⟨671522, by rfl⟩ : syracuseStep 895363 = 1343045) B1343045
theorem B895379 : Blo 892572 895379 := bstep (se 1 (by rfl) ⟨671534, by rfl⟩ : syracuseStep 895379 = 1343069) B1343069
theorem B895395 : Blo 892572 895395 := bstep (se 1 (by rfl) ⟨671546, by rfl⟩ : syracuseStep 895395 = 1343093) B1343093
theorem B895411 : Blo 892572 895411 := bstep (se 1 (by rfl) ⟨671558, by rfl⟩ : syracuseStep 895411 = 1343117) B1343117
theorem B2861507 : Blo 892572 2861507 := bstep (se 1 (by rfl) ⟨2146130, by rfl⟩ : syracuseStep 2861507 = 4292261) B4292261
theorem B895427 : Blo 892572 895427 := bstep (se 1 (by rfl) ⟨671570, by rfl⟩ : syracuseStep 895427 = 1343141) B1343141
theorem B895443 : Blo 892572 895443 := bstep (se 1 (by rfl) ⟨671582, by rfl⟩ : syracuseStep 895443 = 1343165) B1343165
theorem B895459 : Blo 892572 895459 := bstep (se 1 (by rfl) ⟨671594, by rfl⟩ : syracuseStep 895459 = 1343189) B1343189
theorem B895475 : Blo 892572 895475 := bstep (se 1 (by rfl) ⟨671606, by rfl⟩ : syracuseStep 895475 = 1343213) B1343213
theorem B895491 : Blo 892572 895491 := bstep (se 1 (by rfl) ⟨671618, by rfl⟩ : syracuseStep 895491 = 1343237) B1343237
theorem B895507 : Blo 892572 895507 := bstep (se 1 (by rfl) ⟨671630, by rfl⟩ : syracuseStep 895507 = 1343261) B1343261
theorem B895523 : Blo 892572 895523 := bstep (se 1 (by rfl) ⟨671642, by rfl⟩ : syracuseStep 895523 = 1343285) B1343285
theorem B3025457 : Blo 892572 3025457 := bstep (se 2 (by rfl) ⟨1134546, by rfl⟩ : syracuseStep 3025457 = 2269093) B2269093
theorem B895539 : Blo 892572 895539 := bstep (se 1 (by rfl) ⟨671654, by rfl⟩ : syracuseStep 895539 = 1343309) B1343309
theorem B1288769 : Blo 892572 1288769 := bstep (se 2 (by rfl) ⟨483288, by rfl⟩ : syracuseStep 1288769 = 966577) B966577
theorem B895555 : Blo 892572 895555 := bstep (se 1 (by rfl) ⟨671666, by rfl⟩ : syracuseStep 895555 = 1343333) B1343333
theorem B2009681 : Blo 892572 2009681 := bstep (se 2 (by rfl) ⟨753630, by rfl⟩ : syracuseStep 2009681 = 1507261) B1507261
theorem B895571 : Blo 892572 895571 := bstep (se 1 (by rfl) ⟨671678, by rfl⟩ : syracuseStep 895571 = 1343357) B1343357
theorem B5155427 : Blo 892572 5155427 := bstep (se 1 (by rfl) ⟨3866570, by rfl⟩ : syracuseStep 5155427 = 7733141) B7733141
theorem B2009699 : Blo 892572 2009699 := bstep (se 1 (by rfl) ⟨1507274, by rfl⟩ : syracuseStep 2009699 = 3014549) B3014549
theorem B895587 : Blo 892572 895587 := bstep (se 1 (by rfl) ⟨671690, by rfl⟩ : syracuseStep 895587 = 1343381) B1343381
theorem B895603 : Blo 892572 895603 := bstep (se 1 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 895603 = 1343405) B1343405
theorem B895619 : Blo 892572 895619 := bstep (se 1 (by rfl) ⟨671714, by rfl⟩ : syracuseStep 895619 = 1343429) B1343429
theorem B895635 : Blo 892572 895635 := bstep (se 1 (by rfl) ⟨671726, by rfl⟩ : syracuseStep 895635 = 1343453) B1343453
theorem B895651 : Blo 892572 895651 := bstep (se 1 (by rfl) ⟨671738, by rfl⟩ : syracuseStep 895651 = 1343477) B1343477
theorem B895667 : Blo 892572 895667 := bstep (se 1 (by rfl) ⟨671750, by rfl⟩ : syracuseStep 895667 = 1343501) B1343501
theorem B895683 : Blo 892572 895683 := bstep (se 1 (by rfl) ⟨671762, by rfl⟩ : syracuseStep 895683 = 1343525) B1343525
theorem B895699 : Blo 892572 895699 := bstep (se 1 (by rfl) ⟨671774, by rfl⟩ : syracuseStep 895699 = 1343549) B1343549
theorem B895715 : Blo 892572 895715 := bstep (se 1 (by rfl) ⟨671786, by rfl⟩ : syracuseStep 895715 = 1343573) B1343573
theorem B895731 : Blo 892572 895731 := bstep (se 1 (by rfl) ⟨671798, by rfl⟩ : syracuseStep 895731 = 1343597) B1343597
theorem B895747 : Blo 892572 895747 := bstep (se 1 (by rfl) ⟨671810, by rfl⟩ : syracuseStep 895747 = 1343621) B1343621
theorem B895763 : Blo 892572 895763 := bstep (se 1 (by rfl) ⟨671822, by rfl⟩ : syracuseStep 895763 = 1343645) B1343645
theorem B895779 : Blo 892572 895779 := bstep (se 1 (by rfl) ⟨671834, by rfl⟩ : syracuseStep 895779 = 1343669) B1343669
theorem B895795 : Blo 892572 895795 := bstep (se 1 (by rfl) ⟨671846, by rfl⟩ : syracuseStep 895795 = 1343693) B1343693
theorem B895811 : Blo 892572 895811 := bstep (se 1 (by rfl) ⟨671858, by rfl⟩ : syracuseStep 895811 = 1343717) B1343717
theorem B895827 : Blo 892572 895827 := bstep (se 1 (by rfl) ⟨671870, by rfl⟩ : syracuseStep 895827 = 1343741) B1343741
theorem B895843 : Blo 892572 895843 := bstep (se 1 (by rfl) ⟨671882, by rfl⟩ : syracuseStep 895843 = 1343765) B1343765
theorem B2009969 : Blo 892572 2009969 := bstep (se 2 (by rfl) ⟨753738, by rfl⟩ : syracuseStep 2009969 = 1507477) B1507477
theorem B895859 : Blo 892572 895859 := bstep (se 1 (by rfl) ⟨671894, by rfl⟩ : syracuseStep 895859 = 1343789) B1343789
theorem B2009987 : Blo 892572 2009987 := bstep (se 1 (by rfl) ⟨1507490, by rfl⟩ : syracuseStep 2009987 = 3014981) B3014981
theorem B895875 : Blo 892572 895875 := bstep (se 1 (by rfl) ⟨671906, by rfl⟩ : syracuseStep 895875 = 1343813) B1343813
theorem B895891 : Blo 892572 895891 := bstep (se 1 (by rfl) ⟨671918, by rfl⟩ : syracuseStep 895891 = 1343837) B1343837
theorem B895907 : Blo 892572 895907 := bstep (se 1 (by rfl) ⟨671930, by rfl⟩ : syracuseStep 895907 = 1343861) B1343861
theorem B895923 : Blo 892572 895923 := bstep (se 1 (by rfl) ⟨671942, by rfl⟩ : syracuseStep 895923 = 1343885) B1343885
theorem B895939 : Blo 892572 895939 := bstep (se 1 (by rfl) ⟨671954, by rfl⟩ : syracuseStep 895939 = 1343909) B1343909
theorem B895955 : Blo 892572 895955 := bstep (se 1 (by rfl) ⟨671966, by rfl⟩ : syracuseStep 895955 = 1343933) B1343933
theorem B895971 : Blo 892572 895971 := bstep (se 1 (by rfl) ⟨671978, by rfl⟩ : syracuseStep 895971 = 1343957) B1343957
theorem B895987 : Blo 892572 895987 := bstep (se 1 (by rfl) ⟨671990, by rfl⟩ : syracuseStep 895987 = 1343981) B1343981
theorem B896003 : Blo 892572 896003 := bstep (se 1 (by rfl) ⟨672002, by rfl⟩ : syracuseStep 896003 = 1344005) B1344005
theorem B6433805 : Blo 892572 6433805 := bstep (se 3 (by rfl) ⟨1206338, by rfl⟩ : syracuseStep 6433805 = 2412677) B2412677
theorem B896019 : Blo 892572 896019 := bstep (se 1 (by rfl) ⟨672014, by rfl⟩ : syracuseStep 896019 = 1344029) B1344029
theorem B896035 : Blo 892572 896035 := bstep (se 1 (by rfl) ⟨672026, by rfl⟩ : syracuseStep 896035 = 1344053) B1344053
theorem B896051 : Blo 892572 896051 := bstep (se 1 (by rfl) ⟨672038, by rfl⟩ : syracuseStep 896051 = 1344077) B1344077
theorem B896067 : Blo 892572 896067 := bstep (se 1 (by rfl) ⟨672050, by rfl⟩ : syracuseStep 896067 = 1344101) B1344101
theorem B2862161 : Blo 892572 2862161 := bstep (se 2 (by rfl) ⟨1073310, by rfl⟩ : syracuseStep 2862161 = 2146621) B2146621
theorem B896083 : Blo 892572 896083 := bstep (se 1 (by rfl) ⟨672062, by rfl⟩ : syracuseStep 896083 = 1344125) B1344125
theorem B896099 : Blo 892572 896099 := bstep (se 1 (by rfl) ⟨672074, by rfl⟩ : syracuseStep 896099 = 1344149) B1344149
theorem B896115 : Blo 892572 896115 := bstep (se 1 (by rfl) ⟨672086, by rfl⟩ : syracuseStep 896115 = 1344173) B1344173
theorem B896131 : Blo 892572 896131 := bstep (se 1 (by rfl) ⟨672098, by rfl⟩ : syracuseStep 896131 = 1344197) B1344197
theorem B5450885 : Blo 892572 5450885 := bstep (se 4 (by rfl) ⟨511020, by rfl⟩ : syracuseStep 5450885 = 1022041) B1022041
theorem B2010257 : Blo 892572 2010257 := bstep (se 2 (by rfl) ⟨753846, by rfl⟩ : syracuseStep 2010257 = 1507693) B1507693
theorem B896147 : Blo 892572 896147 := bstep (se 1 (by rfl) ⟨672110, by rfl⟩ : syracuseStep 896147 = 1344221) B1344221
theorem B2010275 : Blo 892572 2010275 := bstep (se 1 (by rfl) ⟨1507706, by rfl⟩ : syracuseStep 2010275 = 3015413) B3015413
theorem B896163 : Blo 892572 896163 := bstep (se 1 (by rfl) ⟨672122, by rfl⟩ : syracuseStep 896163 = 1344245) B1344245
theorem B896179 : Blo 892572 896179 := bstep (se 1 (by rfl) ⟨672134, by rfl⟩ : syracuseStep 896179 = 1344269) B1344269
theorem B896195 : Blo 892572 896195 := bstep (se 1 (by rfl) ⟨672146, by rfl⟩ : syracuseStep 896195 = 1344293) B1344293
theorem B896211 : Blo 892572 896211 := bstep (se 1 (by rfl) ⟨672158, by rfl⟩ : syracuseStep 896211 = 1344317) B1344317
theorem B896227 : Blo 892572 896227 := bstep (se 1 (by rfl) ⟨672170, by rfl⟩ : syracuseStep 896227 = 1344341) B1344341
theorem B896243 : Blo 892572 896243 := bstep (se 1 (by rfl) ⟨672182, by rfl⟩ : syracuseStep 896243 = 1344365) B1344365
theorem B896259 : Blo 892572 896259 := bstep (se 1 (by rfl) ⟨672194, by rfl⟩ : syracuseStep 896259 = 1344389) B1344389
theorem B896275 : Blo 892572 896275 := bstep (se 1 (by rfl) ⟨672206, by rfl⟩ : syracuseStep 896275 = 1344413) B1344413
theorem B896291 : Blo 892572 896291 := bstep (se 1 (by rfl) ⟨672218, by rfl⟩ : syracuseStep 896291 = 1344437) B1344437
theorem B896307 : Blo 892572 896307 := bstep (se 1 (by rfl) ⟨672230, by rfl⟩ : syracuseStep 896307 = 1344461) B1344461
theorem B896323 : Blo 892572 896323 := bstep (se 1 (by rfl) ⟨672242, by rfl⟩ : syracuseStep 896323 = 1344485) B1344485
theorem B5451077 : Blo 892572 5451077 := bstep (se 4 (by rfl) ⟨511038, by rfl⟩ : syracuseStep 5451077 = 1022077) B1022077
theorem B896339 : Blo 892572 896339 := bstep (se 1 (by rfl) ⟨672254, by rfl⟩ : syracuseStep 896339 = 1344509) B1344509
theorem B896355 : Blo 892572 896355 := bstep (se 1 (by rfl) ⟨672266, by rfl⟩ : syracuseStep 896355 = 1344533) B1344533
theorem B896371 : Blo 892572 896371 := bstep (se 1 (by rfl) ⟨672278, by rfl⟩ : syracuseStep 896371 = 1344557) B1344557
theorem B896387 : Blo 892572 896387 := bstep (se 1 (by rfl) ⟨672290, by rfl⟩ : syracuseStep 896387 = 1344581) B1344581
theorem B896403 : Blo 892572 896403 := bstep (se 1 (by rfl) ⟨672302, by rfl⟩ : syracuseStep 896403 = 1344605) B1344605
theorem B896419 : Blo 892572 896419 := bstep (se 1 (by rfl) ⟨672314, by rfl⟩ : syracuseStep 896419 = 1344629) B1344629
theorem B2010545 : Blo 892572 2010545 := bstep (se 2 (by rfl) ⟨753954, by rfl⟩ : syracuseStep 2010545 = 1507909) B1507909
theorem B896435 : Blo 892572 896435 := bstep (se 1 (by rfl) ⟨672326, by rfl⟩ : syracuseStep 896435 = 1344653) B1344653
theorem B2010563 : Blo 892572 2010563 := bstep (se 1 (by rfl) ⟨1507922, by rfl⟩ : syracuseStep 2010563 = 3015845) B3015845
theorem B896451 : Blo 892572 896451 := bstep (se 1 (by rfl) ⟨672338, by rfl⟩ : syracuseStep 896451 = 1344677) B1344677
theorem B896467 : Blo 892572 896467 := bstep (se 1 (by rfl) ⟨672350, by rfl⟩ : syracuseStep 896467 = 1344701) B1344701
theorem B4533731 : Blo 892572 4533731 := bstep (se 1 (by rfl) ⟨3400298, by rfl⟩ : syracuseStep 4533731 = 6800597) B6800597
theorem B896483 : Blo 892572 896483 := bstep (se 1 (by rfl) ⟨672362, by rfl⟩ : syracuseStep 896483 = 1344725) B1344725
theorem B896499 : Blo 892572 896499 := bstep (se 1 (by rfl) ⟨672374, by rfl⟩ : syracuseStep 896499 = 1344749) B1344749
theorem B896515 : Blo 892572 896515 := bstep (se 1 (by rfl) ⟨672386, by rfl⟩ : syracuseStep 896515 = 1344773) B1344773
theorem B6794765 : Blo 892572 6794765 := bstep (se 3 (by rfl) ⟨1274018, by rfl⟩ : syracuseStep 6794765 = 2548037) B2548037
theorem B896531 : Blo 892572 896531 := bstep (se 1 (by rfl) ⟨672398, by rfl⟩ : syracuseStep 896531 = 1344797) B1344797
theorem B896547 : Blo 892572 896547 := bstep (se 1 (by rfl) ⟨672410, by rfl⟩ : syracuseStep 896547 = 1344821) B1344821
theorem B896563 : Blo 892572 896563 := bstep (se 1 (by rfl) ⟨672422, by rfl⟩ : syracuseStep 896563 = 1344845) B1344845
theorem B2043505 : Blo 892572 2043505 := bstep (se 2 (by rfl) ⟨766314, by rfl⟩ : syracuseStep 2043505 = 1532629) B1532629
theorem B2010833 : Blo 892572 2010833 := bstep (se 2 (by rfl) ⟨754062, by rfl⟩ : syracuseStep 2010833 = 1508125) B1508125
theorem B2010851 : Blo 892572 2010851 := bstep (se 1 (by rfl) ⟨1508138, by rfl⟩ : syracuseStep 2010851 = 3016277) B3016277
theorem B1552321 : Blo 892572 1552321 := bstep (se 2 (by rfl) ⟨582120, by rfl⟩ : syracuseStep 1552321 = 1164241) B1164241
theorem B1912771 : Blo 892572 1912771 := bstep (se 1 (by rfl) ⟨1434578, by rfl⟩ : syracuseStep 1912771 = 2869157) B2869157
theorem B14528483 : Blo 892572 14528483 := bstep (se 1 (by rfl) ⟨10896362, by rfl⟩ : syracuseStep 14528483 = 21792725) B21792725
theorem B2011121 : Blo 892572 2011121 := bstep (se 2 (by rfl) ⟨754170, by rfl⟩ : syracuseStep 2011121 = 1508341) B1508341
theorem B1290241 : Blo 892572 1290241 := bstep (se 2 (by rfl) ⟨483840, by rfl⟩ : syracuseStep 1290241 = 967681) B967681
theorem B2011139 : Blo 892572 2011139 := bstep (se 1 (by rfl) ⟨1508354, by rfl⟩ : syracuseStep 2011139 = 3016709) B3016709
theorem B4075555 : Blo 892572 4075555 := bstep (se 1 (by rfl) ⟨3056666, by rfl⟩ : syracuseStep 4075555 = 6113333) B6113333
theorem B3813581 : Blo 892572 3813581 := bstep (se 3 (by rfl) ⟨715046, by rfl⟩ : syracuseStep 3813581 = 1430093) B1430093
theorem B4534541 : Blo 892572 4534541 := bstep (se 3 (by rfl) ⟨850226, by rfl⟩ : syracuseStep 4534541 = 1700453) B1700453
theorem B2011409 : Blo 892572 2011409 := bstep (se 2 (by rfl) ⟨754278, by rfl⟩ : syracuseStep 2011409 = 1508557) B1508557
theorem B2011427 : Blo 892572 2011427 := bstep (se 1 (by rfl) ⟨1508570, by rfl⟩ : syracuseStep 2011427 = 3017141) B3017141
theorem B4829489 : Blo 892572 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B1290611 : Blo 892572 1290611 := bstep (se 1 (by rfl) ⟨967958, by rfl⟩ : syracuseStep 1290611 = 1935917) B1935917
theorem B1913233 : Blo 892572 1913233 := bstep (se 2 (by rfl) ⟨717462, by rfl⟩ : syracuseStep 1913233 = 1434925) B1434925
theorem B2011697 : Blo 892572 2011697 := bstep (se 2 (by rfl) ⟨754386, by rfl⟩ : syracuseStep 2011697 = 1508773) B1508773
theorem B2011715 : Blo 892572 2011715 := bstep (se 1 (by rfl) ⟨1508786, by rfl⟩ : syracuseStep 2011715 = 3017573) B3017573
theorem B2044739 : Blo 892572 2044739 := bstep (se 1 (by rfl) ⟨1533554, by rfl⟩ : syracuseStep 2044739 = 3067109) B3067109
theorem B2011985 : Blo 892572 2011985 := bstep (se 2 (by rfl) ⟨754494, by rfl⟩ : syracuseStep 2011985 = 1508989) B1508989
theorem B2012003 : Blo 892572 2012003 := bstep (se 1 (by rfl) ⟨1509002, by rfl⟩ : syracuseStep 2012003 = 3018005) B3018005
theorem B2864173 : Blo 892572 2864173 := bstep (se 3 (by rfl) ⟨537032, by rfl⟩ : syracuseStep 2864173 = 1074065) B1074065
theorem B5092429 : Blo 892572 5092429 := bstep (se 3 (by rfl) ⟨954830, by rfl⟩ : syracuseStep 5092429 = 1909661) B1909661
theorem B2012273 : Blo 892572 2012273 := bstep (se 2 (by rfl) ⟨754602, by rfl⟩ : syracuseStep 2012273 = 1509205) B1509205
theorem B2012291 : Blo 892572 2012291 := bstep (se 1 (by rfl) ⟨1509218, by rfl⟩ : syracuseStep 2012291 = 3018437) B3018437
theorem B3880163 : Blo 892572 3880163 := bstep (se 1 (by rfl) ⟨2910122, by rfl⟩ : syracuseStep 3880163 = 5820245) B5820245
theorem B2012561 : Blo 892572 2012561 := bstep (se 2 (by rfl) ⟨754710, by rfl⟩ : syracuseStep 2012561 = 1509421) B1509421
theorem B2012579 : Blo 892572 2012579 := bstep (se 1 (by rfl) ⟨1509434, by rfl⟩ : syracuseStep 2012579 = 3018869) B3018869
theorem B1914275 : Blo 892572 1914275 := bstep (se 1 (by rfl) ⟨1435706, by rfl⟩ : syracuseStep 1914275 = 2871413) B2871413
theorem B2864621 : Blo 892572 2864621 := bstep (se 3 (by rfl) ⟨537116, by rfl⟩ : syracuseStep 2864621 = 1074233) B1074233
theorem B1226305 : Blo 892572 1226305 := bstep (se 2 (by rfl) ⟨459864, by rfl⟩ : syracuseStep 1226305 = 919729) B919729
theorem B2012849 : Blo 892572 2012849 := bstep (se 2 (by rfl) ⟨754818, by rfl⟩ : syracuseStep 2012849 = 1509637) B1509637
theorem B2012867 : Blo 892572 2012867 := bstep (se 1 (by rfl) ⟨1509650, by rfl⟩ : syracuseStep 2012867 = 3019301) B3019301
theorem B1816273 : Blo 892572 1816273 := bstep (se 2 (by rfl) ⟨681102, by rfl⟩ : syracuseStep 1816273 = 1362205) B1362205
theorem B1914787 : Blo 892572 1914787 := bstep (se 1 (by rfl) ⟨1436090, by rfl⟩ : syracuseStep 1914787 = 2872181) B2872181
theorem B2013137 : Blo 892572 2013137 := bstep (se 2 (by rfl) ⟨754926, by rfl⟩ : syracuseStep 2013137 = 1509853) B1509853
theorem B2013155 : Blo 892572 2013155 := bstep (se 1 (by rfl) ⟨1509866, by rfl⟩ : syracuseStep 2013155 = 3019733) B3019733
theorem B1554403 : Blo 892572 1554403 := bstep (se 1 (by rfl) ⟨1165802, by rfl⟩ : syracuseStep 1554403 = 2331605) B2331605
theorem B7256261 : Blo 892572 7256261 := bstep (se 4 (by rfl) ⟨680274, by rfl⟩ : syracuseStep 7256261 = 1360549) B1360549
theorem B1718513 : Blo 892572 1718513 := bstep (se 2 (by rfl) ⟨644442, by rfl⟩ : syracuseStep 1718513 = 1288885) B1288885
theorem B2013425 : Blo 892572 2013425 := bstep (se 2 (by rfl) ⟨755034, by rfl⟩ : syracuseStep 2013425 = 1510069) B1510069
theorem B2013443 : Blo 892572 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B4962637 : Blo 892572 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B6797681 : Blo 892572 6797681 := bstep (se 2 (by rfl) ⟨2549130, by rfl⟩ : syracuseStep 6797681 = 5098261) B5098261
theorem B4831757 : Blo 892572 4831757 := bstep (se 3 (by rfl) ⟨905954, by rfl⟩ : syracuseStep 4831757 = 1811909) B1811909
theorem B2013713 : Blo 892572 2013713 := bstep (se 2 (by rfl) ⟨755142, by rfl⟩ : syracuseStep 2013713 = 1510285) B1510285
theorem B2013731 : Blo 892572 2013731 := bstep (se 1 (by rfl) ⟨1510298, by rfl⟩ : syracuseStep 2013731 = 3020597) B3020597
theorem B1718929 : Blo 892572 1718929 := bstep (se 2 (by rfl) ⟨644598, by rfl⟩ : syracuseStep 1718929 = 1289197) B1289197
theorem B2898641 : Blo 892572 2898641 := bstep (se 2 (by rfl) ⟨1086990, by rfl⟩ : syracuseStep 2898641 = 2173981) B2173981
theorem B2014001 : Blo 892572 2014001 := bstep (se 2 (by rfl) ⟨755250, by rfl⟩ : syracuseStep 2014001 = 1510501) B1510501
theorem B1260353 : Blo 892572 1260353 := bstep (se 2 (by rfl) ⟨472632, by rfl⟩ : syracuseStep 1260353 = 945265) B945265
theorem B2014019 : Blo 892572 2014019 := bstep (se 1 (by rfl) ⟨1510514, by rfl⟩ : syracuseStep 2014019 = 3021029) B3021029
theorem B1358689 : Blo 892572 1358689 := bstep (se 2 (by rfl) ⟨509508, by rfl⟩ : syracuseStep 1358689 = 1019017) B1019017
theorem B1719281 : Blo 892572 1719281 := bstep (se 2 (by rfl) ⟨644730, by rfl⟩ : syracuseStep 1719281 = 1289461) B1289461
theorem B5094413 : Blo 892572 5094413 := bstep (se 3 (by rfl) ⟨955202, by rfl⟩ : syracuseStep 5094413 = 1910405) B1910405
theorem B2014289 : Blo 892572 2014289 := bstep (se 2 (by rfl) ⟨755358, by rfl⟩ : syracuseStep 2014289 = 1510717) B1510717
theorem B1358945 : Blo 892572 1358945 := bstep (se 2 (by rfl) ⟨509604, by rfl⟩ : syracuseStep 1358945 = 1019209) B1019209
theorem B2014307 : Blo 892572 2014307 := bstep (se 1 (by rfl) ⟨1510730, by rfl⟩ : syracuseStep 2014307 = 3021461) B3021461
theorem B4537457 : Blo 892572 4537457 := bstep (se 2 (by rfl) ⟨1701546, by rfl⟩ : syracuseStep 4537457 = 3403093) B3403093
theorem B2014577 : Blo 892572 2014577 := bstep (se 2 (by rfl) ⟨755466, by rfl⟩ : syracuseStep 2014577 = 1510933) B1510933
theorem B2014595 : Blo 892572 2014595 := bstep (se 1 (by rfl) ⟨1510946, by rfl⟩ : syracuseStep 2014595 = 3021893) B3021893
theorem B10173923 : Blo 892572 10173923 := bstep (se 1 (by rfl) ⟨7630442, by rfl⟩ : syracuseStep 10173923 = 15260885) B15260885
theorem B1130051 : Blo 892572 1130051 := bstep (se 1 (by rfl) ⟨847538, by rfl⟩ : syracuseStep 1130051 = 1695077) B1695077
theorem B2014865 : Blo 892572 2014865 := bstep (se 2 (by rfl) ⟨755574, by rfl⟩ : syracuseStep 2014865 = 1511149) B1511149
theorem B2014883 : Blo 892572 2014883 := bstep (se 1 (by rfl) ⟨1511162, by rfl⟩ : syracuseStep 2014883 = 3022325) B3022325
theorem B3391217 : Blo 892572 3391217 := bstep (se 2 (by rfl) ⟨1271706, by rfl⟩ : syracuseStep 3391217 = 2543413) B2543413
theorem B2015153 : Blo 892572 2015153 := bstep (se 2 (by rfl) ⟨755682, by rfl⟩ : syracuseStep 2015153 = 1511365) B1511365
theorem B5095345 : Blo 892572 5095345 := bstep (se 2 (by rfl) ⟨1910754, by rfl⟩ : syracuseStep 5095345 = 3821509) B3821509
theorem B2015171 : Blo 892572 2015171 := bstep (se 1 (by rfl) ⟨1511378, by rfl⟩ : syracuseStep 2015171 = 3022757) B3022757
theorem B6897635 : Blo 892572 6897635 := bstep (se 1 (by rfl) ⟨5173226, by rfl⟩ : syracuseStep 6897635 = 10346453) B10346453
theorem B3620963 : Blo 892572 3620963 := bstep (se 1 (by rfl) ⟨2715722, by rfl⟩ : syracuseStep 3620963 = 5431445) B5431445
theorem B2867363 : Blo 892572 2867363 := bstep (se 1 (by rfl) ⟨2150522, by rfl⟩ : syracuseStep 2867363 = 4301045) B4301045
theorem B4833485 : Blo 892572 4833485 := bstep (se 3 (by rfl) ⟨906278, by rfl⟩ : syracuseStep 4833485 = 1812557) B1812557
theorem B2015441 : Blo 892572 2015441 := bstep (se 2 (by rfl) ⟨755790, by rfl⟩ : syracuseStep 2015441 = 1511581) B1511581
theorem B2015459 : Blo 892572 2015459 := bstep (se 1 (by rfl) ⟨1511594, by rfl⟩ : syracuseStep 2015459 = 3023189) B3023189
theorem B1130755 : Blo 892572 1130755 := bstep (se 1 (by rfl) ⟨848066, by rfl⟩ : syracuseStep 1130755 = 1696133) B1696133
theorem B5161229 : Blo 892572 5161229 := bstep (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) B1935461
theorem B2867491 : Blo 892572 2867491 := bstep (se 1 (by rfl) ⟨2150618, by rfl⟩ : syracuseStep 2867491 = 4301237) B4301237
theorem B1130851 : Blo 892572 1130851 := bstep (se 1 (by rfl) ⟨848138, by rfl⟩ : syracuseStep 1130851 = 1696277) B1696277
theorem B3817955 : Blo 892572 3817955 := bstep (se 1 (by rfl) ⟨2863466, by rfl⟩ : syracuseStep 3817955 = 5726933) B5726933
theorem B2015729 : Blo 892572 2015729 := bstep (se 2 (by rfl) ⟨755898, by rfl⟩ : syracuseStep 2015729 = 1511797) B1511797
theorem B2015747 : Blo 892572 2015747 := bstep (se 1 (by rfl) ⟨1511810, by rfl⟩ : syracuseStep 2015747 = 3023621) B3023621
theorem B37274165 : Blo 892572 37274165 := bstep (se 5 (by rfl) ⟨1747226, by rfl⟩ : syracuseStep 37274165 = 3494453) B3494453
theorem B967235 : Blo 892572 967235 := bstep (se 1 (by rfl) ⟨725426, by rfl⟩ : syracuseStep 967235 = 1450853) B1450853
theorem B2867825 : Blo 892572 2867825 := bstep (se 2 (by rfl) ⟨1075434, by rfl⟩ : syracuseStep 2867825 = 2150869) B2150869
theorem B2016017 : Blo 892572 2016017 := bstep (se 2 (by rfl) ⟨756006, by rfl⟩ : syracuseStep 2016017 = 1512013) B1512013
theorem B2016035 : Blo 892572 2016035 := bstep (se 1 (by rfl) ⟨1512026, by rfl⟩ : syracuseStep 2016035 = 3024053) B3024053
theorem B1131347 : Blo 892572 1131347 := bstep (se 1 (by rfl) ⟨848510, by rfl⟩ : syracuseStep 1131347 = 1697021) B1697021
theorem B2016305 : Blo 892572 2016305 := bstep (se 2 (by rfl) ⟨756114, by rfl⟩ : syracuseStep 2016305 = 1512229) B1512229
theorem B2016323 : Blo 892572 2016323 := bstep (se 1 (by rfl) ⟨1512242, by rfl⟩ : syracuseStep 2016323 = 3024485) B3024485
theorem B3392675 : Blo 892572 3392675 := bstep (se 1 (by rfl) ⟨2544506, by rfl⟩ : syracuseStep 3392675 = 5089013) B5089013
theorem B2901187 : Blo 892572 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B2016593 : Blo 892572 2016593 := bstep (se 2 (by rfl) ⟨756222, by rfl⟩ : syracuseStep 2016593 = 1512445) B1512445
theorem B5096803 : Blo 892572 5096803 := bstep (se 1 (by rfl) ⟨3822602, by rfl⟩ : syracuseStep 5096803 = 7645205) B7645205
theorem B2016611 : Blo 892572 2016611 := bstep (se 1 (by rfl) ⟨1512458, by rfl⟩ : syracuseStep 2016611 = 3024917) B3024917
theorem B3065357 : Blo 892572 3065357 := bstep (se 3 (by rfl) ⟨574754, by rfl⟩ : syracuseStep 3065357 = 1149509) B1149509
theorem B1132051 : Blo 892572 1132051 := bstep (se 1 (by rfl) ⟨849038, by rfl⟩ : syracuseStep 1132051 = 1698077) B1698077
theorem B2016881 : Blo 892572 2016881 := bstep (se 2 (by rfl) ⟨756330, by rfl⟩ : syracuseStep 2016881 = 1512661) B1512661
theorem B1132147 : Blo 892572 1132147 := bstep (se 1 (by rfl) ⟨849110, by rfl⟩ : syracuseStep 1132147 = 1698221) B1698221
theorem B2016899 : Blo 892572 2016899 := bstep (se 1 (by rfl) ⟨1512674, by rfl⟩ : syracuseStep 2016899 = 3025349) B3025349
theorem B5097329 : Blo 892572 5097329 := bstep (se 2 (by rfl) ⟨1911498, by rfl⟩ : syracuseStep 5097329 = 3822997) B3822997
theorem B2017169 : Blo 892572 2017169 := bstep (se 2 (by rfl) ⟨756438, by rfl⟩ : syracuseStep 2017169 = 1512877) B1512877
theorem B2017187 : Blo 892572 2017187 := bstep (se 1 (by rfl) ⟨1512890, by rfl⟩ : syracuseStep 2017187 = 3025781) B3025781
theorem B1132643 : Blo 892572 1132643 := bstep (se 1 (by rfl) ⟨849482, by rfl⟩ : syracuseStep 1132643 = 1698965) B1698965
theorem B3393677 : Blo 892572 3393677 := bstep (se 3 (by rfl) ⟨636314, by rfl⟩ : syracuseStep 3393677 = 1272629) B1272629
theorem B2148515 : Blo 892572 2148515 := bstep (se 1 (by rfl) ⟨1611386, by rfl⟩ : syracuseStep 2148515 = 3222773) B3222773
theorem B2541773 : Blo 892572 2541773 := bstep (se 3 (by rfl) ⟨476582, by rfl⟩ : syracuseStep 2541773 = 953165) B953165
theorem B2541955 : Blo 892572 2541955 := bstep (se 1 (by rfl) ⟨1906466, by rfl⟩ : syracuseStep 2541955 = 3812933) B3812933
theorem B1362691 : Blo 892572 1362691 := bstep (se 1 (by rfl) ⟨1022018, by rfl⟩ : syracuseStep 1362691 = 2044037) B2044037
theorem B1133347 : Blo 892572 1133347 := bstep (se 1 (by rfl) ⟨850010, by rfl⟩ : syracuseStep 1133347 = 1700021) B1700021
theorem B1133443 : Blo 892572 1133443 := bstep (se 1 (by rfl) ⟨850082, by rfl⟩ : syracuseStep 1133443 = 1700165) B1700165
theorem B2149361 : Blo 892572 2149361 := bstep (se 2 (by rfl) ⟨806010, by rfl⟩ : syracuseStep 2149361 = 1612021) B1612021
theorem B10210373 : Blo 892572 10210373 := bstep (se 4 (by rfl) ⟨957222, by rfl⟩ : syracuseStep 10210373 = 1914445) B1914445
theorem B3820621 : Blo 892572 3820621 := bstep (se 3 (by rfl) ⟨716366, by rfl⟩ : syracuseStep 3820621 = 1432733) B1432733
theorem B5098787 : Blo 892572 5098787 := bstep (se 1 (by rfl) ⟨3824090, by rfl⟩ : syracuseStep 5098787 = 7648181) B7648181
theorem B1133939 : Blo 892572 1133939 := bstep (se 1 (by rfl) ⟨850454, by rfl⟩ : syracuseStep 1133939 = 1700909) B1700909
theorem B2870797 : Blo 892572 2870797 := bstep (se 3 (by rfl) ⟨538274, by rfl⟩ : syracuseStep 2870797 = 1076549) B1076549
theorem B2543345 : Blo 892572 2543345 := bstep (se 2 (by rfl) ⟨953754, by rfl⟩ : syracuseStep 2543345 = 1907509) B1907509
theorem B2871053 : Blo 892572 2871053 := bstep (se 3 (by rfl) ⟨538322, by rfl⟩ : syracuseStep 2871053 = 1076645) B1076645
theorem B1724387 : Blo 892572 1724387 := bstep (se 1 (by rfl) ⟨1293290, by rfl⟩ : syracuseStep 1724387 = 2586581) B2586581
theorem B1134643 : Blo 892572 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B3821681 : Blo 892572 3821681 := bstep (se 2 (by rfl) ⟨1433130, by rfl⟩ : syracuseStep 3821681 = 2866261) B2866261
theorem B4837553 : Blo 892572 4837553 := bstep (se 2 (by rfl) ⟨1814082, by rfl⟩ : syracuseStep 4837553 = 3628165) B3628165
theorem B3395789 : Blo 892572 3395789 := bstep (se 3 (by rfl) ⟨636710, by rfl⟩ : syracuseStep 3395789 = 1273421) B1273421
theorem B4837637 : Blo 892572 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B1102195 : Blo 892572 1102195 := bstep (se 1 (by rfl) ⟨826646, by rfl⟩ : syracuseStep 1102195 = 1653293) B1653293
theorem B1004179 : Blo 892572 1004179 := bstep (se 1 (by rfl) ⟨753134, by rfl⟩ : syracuseStep 1004179 = 1506269) B1506269
theorem B2544301 : Blo 892572 2544301 := bstep (se 3 (by rfl) ⟨477056, by rfl⟩ : syracuseStep 2544301 = 954113) B954113
theorem B1430273 : Blo 892572 1430273 := bstep (se 2 (by rfl) ⟨536352, by rfl⟩ : syracuseStep 1430273 = 1072705) B1072705
theorem B1528579 : Blo 892572 1528579 := bstep (se 1 (by rfl) ⟨1146434, by rfl⟩ : syracuseStep 1528579 = 2292869) B2292869
theorem B1004323 : Blo 892572 1004323 := bstep (se 1 (by rfl) ⟨753242, by rfl⟩ : syracuseStep 1004323 = 1506485) B1506485
theorem B1430401 : Blo 892572 1430401 := bstep (se 2 (by rfl) ⟨536400, by rfl⟩ : syracuseStep 1430401 = 1072801) B1072801
theorem B2544529 : Blo 892572 2544529 := bstep (se 2 (by rfl) ⟨954198, by rfl⟩ : syracuseStep 2544529 = 1908397) B1908397
theorem B1004467 : Blo 892572 1004467 := bstep (se 1 (by rfl) ⟨753350, by rfl⟩ : syracuseStep 1004467 = 1506701) B1506701
theorem B1430465 : Blo 892572 1430465 := bstep (se 2 (by rfl) ⟨536424, by rfl⟩ : syracuseStep 1430465 = 1072849) B1072849
theorem B3396593 : Blo 892572 3396593 := bstep (se 2 (by rfl) ⟨1273722, by rfl⟩ : syracuseStep 3396593 = 2547445) B2547445
theorem B2544689 : Blo 892572 2544689 := bstep (se 2 (by rfl) ⟨954258, by rfl⟩ : syracuseStep 2544689 = 1908517) B1908517
theorem B1004611 : Blo 892572 1004611 := bstep (se 1 (by rfl) ⟨753458, by rfl⟩ : syracuseStep 1004611 = 1506917) B1506917
theorem B5100677 : Blo 892572 5100677 := bstep (se 4 (by rfl) ⟨478188, by rfl⟩ : syracuseStep 5100677 = 956377) B956377
theorem B2544803 : Blo 892572 2544803 := bstep (se 1 (by rfl) ⟨1908602, by rfl⟩ : syracuseStep 2544803 = 3817205) B3817205
theorem B1004755 : Blo 892572 1004755 := bstep (se 1 (by rfl) ⟨753566, by rfl⟩ : syracuseStep 1004755 = 1507133) B1507133
theorem B1004899 : Blo 892572 1004899 := bstep (se 1 (by rfl) ⟨753674, by rfl⟩ : syracuseStep 1004899 = 1507349) B1507349
theorem B1005043 : Blo 892572 1005043 := bstep (se 1 (by rfl) ⟨753782, by rfl⟩ : syracuseStep 1005043 = 1507565) B1507565
theorem B4085261 : Blo 892572 4085261 := bstep (se 3 (by rfl) ⟨765986, by rfl⟩ : syracuseStep 4085261 = 1531973) B1531973
theorem B2152003 : Blo 892572 2152003 := bstep (se 1 (by rfl) ⟨1614002, by rfl⟩ : syracuseStep 2152003 = 3228005) B3228005
theorem B1005187 : Blo 892572 1005187 := bstep (se 1 (by rfl) ⟨753890, by rfl⟩ : syracuseStep 1005187 = 1507781) B1507781
theorem B3397261 : Blo 892572 3397261 := bstep (se 3 (by rfl) ⟨636986, by rfl⟩ : syracuseStep 3397261 = 1273973) B1273973
theorem B2152099 : Blo 892572 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B1005331 : Blo 892572 1005331 := bstep (se 1 (by rfl) ⟨753998, by rfl⟩ : syracuseStep 1005331 = 1507997) B1507997
theorem B2152291 : Blo 892572 2152291 := bstep (se 1 (by rfl) ⟨1614218, by rfl⟩ : syracuseStep 2152291 = 3228437) B3228437
theorem B1005475 : Blo 892572 1005475 := bstep (se 1 (by rfl) ⟨754106, by rfl⟩ : syracuseStep 1005475 = 1508213) B1508213
theorem B1431523 : Blo 892572 1431523 := bstep (se 1 (by rfl) ⟨1073642, by rfl⟩ : syracuseStep 1431523 = 2147285) B2147285
theorem B1005619 : Blo 892572 1005619 := bstep (se 1 (by rfl) ⟨754214, by rfl⟩ : syracuseStep 1005619 = 1508429) B1508429
theorem B2545805 : Blo 892572 2545805 := bstep (se 3 (by rfl) ⟨477338, by rfl⟩ : syracuseStep 2545805 = 954677) B954677
theorem B2906275 : Blo 892572 2906275 := bstep (se 1 (by rfl) ⟨2179706, by rfl⟩ : syracuseStep 2906275 = 4359413) B4359413
theorem B4839587 : Blo 892572 4839587 := bstep (se 1 (by rfl) ⟨3629690, by rfl⟩ : syracuseStep 4839587 = 7259381) B7259381
theorem B1005763 : Blo 892572 1005763 := bstep (se 1 (by rfl) ⟨754322, by rfl⟩ : syracuseStep 1005763 = 1508645) B1508645
theorem B2545987 : Blo 892572 2545987 := bstep (se 1 (by rfl) ⟨1909490, by rfl⟩ : syracuseStep 2545987 = 3818981) B3818981
theorem B1005907 : Blo 892572 1005907 := bstep (se 1 (by rfl) ⟨754430, by rfl⟩ : syracuseStep 1005907 = 1508861) B1508861
theorem B3398051 : Blo 892572 3398051 := bstep (se 1 (by rfl) ⟨2548538, by rfl⟩ : syracuseStep 3398051 = 5097077) B5097077
theorem B2546147 : Blo 892572 2546147 := bstep (se 1 (by rfl) ⟨1909610, by rfl⟩ : syracuseStep 2546147 = 3819221) B3819221
theorem B1006051 : Blo 892572 1006051 := bstep (se 1 (by rfl) ⟨754538, by rfl⟩ : syracuseStep 1006051 = 1509077) B1509077
theorem B5167685 : Blo 892572 5167685 := bstep (se 4 (by rfl) ⟨484470, by rfl⟩ : syracuseStep 5167685 = 968941) B968941
theorem B1006195 : Blo 892572 1006195 := bstep (se 1 (by rfl) ⟨754646, by rfl⟩ : syracuseStep 1006195 = 1509293) B1509293
theorem B1006339 : Blo 892572 1006339 := bstep (se 1 (by rfl) ⟨754754, by rfl⟩ : syracuseStep 1006339 = 1509509) B1509509
theorem B2153233 : Blo 892572 2153233 := bstep (se 2 (by rfl) ⟨807462, by rfl⟩ : syracuseStep 2153233 = 1614925) B1614925
theorem B8608625 : Blo 892572 8608625 := bstep (se 2 (by rfl) ⟨3228234, by rfl⟩ : syracuseStep 8608625 = 6456469) B6456469
theorem B1432451 : Blo 892572 1432451 := bstep (se 1 (by rfl) ⟨1074338, by rfl⟩ : syracuseStep 1432451 = 2148677) B2148677
theorem B1006483 : Blo 892572 1006483 := bstep (se 1 (by rfl) ⟨754862, by rfl⟩ : syracuseStep 1006483 = 1509725) B1509725
theorem B3824653 : Blo 892572 3824653 := bstep (se 3 (by rfl) ⟨717122, by rfl⟩ : syracuseStep 3824653 = 1434245) B1434245
theorem B1006627 : Blo 892572 1006627 := bstep (se 1 (by rfl) ⟨754970, by rfl⟩ : syracuseStep 1006627 = 1509941) B1509941
theorem B3398705 : Blo 892572 3398705 := bstep (se 2 (by rfl) ⟨1274514, by rfl⟩ : syracuseStep 3398705 = 2549029) B2549029
theorem B1694819 : Blo 892572 1694819 := bstep (se 1 (by rfl) ⟨1271114, by rfl⟩ : syracuseStep 1694819 = 2542229) B2542229
theorem B1432721 : Blo 892572 1432721 := bstep (se 2 (by rfl) ⟨537270, by rfl⟩ : syracuseStep 1432721 = 1074541) B1074541
theorem B1006771 : Blo 892572 1006771 := bstep (se 1 (by rfl) ⟨755078, by rfl⟩ : syracuseStep 1006771 = 1510157) B1510157
theorem B5725475 : Blo 892572 5725475 := bstep (se 1 (by rfl) ⟨4294106, by rfl⟩ : syracuseStep 5725475 = 8588213) B8588213
theorem B1006915 : Blo 892572 1006915 := bstep (se 1 (by rfl) ⟨755186, by rfl⟩ : syracuseStep 1006915 = 1510373) B1510373
theorem B3824995 : Blo 892572 3824995 := bstep (se 1 (by rfl) ⟨2868746, by rfl⟩ : syracuseStep 3824995 = 5737493) B5737493
theorem B1695107 : Blo 892572 1695107 := bstep (se 1 (by rfl) ⟨1271330, by rfl⟩ : syracuseStep 1695107 = 2542661) B2542661
theorem B1433009 : Blo 892572 1433009 := bstep (se 2 (by rfl) ⟨537378, by rfl⟩ : syracuseStep 1433009 = 1074757) B1074757
theorem B9821621 : Blo 892572 9821621 := bstep (se 5 (by rfl) ⟨460388, by rfl⟩ : syracuseStep 9821621 = 920777) B920777
theorem B1007059 : Blo 892572 1007059 := bstep (se 1 (by rfl) ⟨755294, by rfl⟩ : syracuseStep 1007059 = 1510589) B1510589
theorem B2547217 : Blo 892572 2547217 := bstep (se 2 (by rfl) ⟨955206, by rfl⟩ : syracuseStep 2547217 = 1910413) B1910413
theorem B1007203 : Blo 892572 1007203 := bstep (se 1 (by rfl) ⟨755402, by rfl⟩ : syracuseStep 1007203 = 1510805) B1510805
theorem B2416355 : Blo 892572 2416355 := bstep (se 1 (by rfl) ⟨1812266, by rfl⟩ : syracuseStep 2416355 = 3624533) B3624533
theorem B1007347 : Blo 892572 1007347 := bstep (se 1 (by rfl) ⟨755510, by rfl⟩ : syracuseStep 1007347 = 1511021) B1511021
theorem B1433425 : Blo 892572 1433425 := bstep (se 2 (by rfl) ⟨537534, by rfl⟩ : syracuseStep 1433425 = 1075069) B1075069
theorem B2416483 : Blo 892572 2416483 := bstep (se 1 (by rfl) ⟨1812362, by rfl⟩ : syracuseStep 2416483 = 3624725) B3624725
theorem B1007491 : Blo 892572 1007491 := bstep (se 1 (by rfl) ⟨755618, by rfl⟩ : syracuseStep 1007491 = 1511237) B1511237
theorem B1007635 : Blo 892572 1007635 := bstep (se 1 (by rfl) ⟨755726, by rfl⟩ : syracuseStep 1007635 = 1511453) B1511453
theorem B1007779 : Blo 892572 1007779 := bstep (se 1 (by rfl) ⟨755834, by rfl⟩ : syracuseStep 1007779 = 1511669) B1511669
theorem B4350257 : Blo 892572 4350257 := bstep (se 2 (by rfl) ⟨1631346, by rfl⟩ : syracuseStep 4350257 = 3262693) B3262693
theorem B1696049 : Blo 892572 1696049 := bstep (se 2 (by rfl) ⟨636018, by rfl⟩ : syracuseStep 1696049 = 1272037) B1272037
theorem B1007923 : Blo 892572 1007923 := bstep (se 1 (by rfl) ⟨755942, by rfl⟩ : syracuseStep 1007923 = 1511885) B1511885
theorem B1008067 : Blo 892572 1008067 := bstep (se 1 (by rfl) ⟨756050, by rfl⟩ : syracuseStep 1008067 = 1512101) B1512101
theorem B3400163 : Blo 892572 3400163 := bstep (se 1 (by rfl) ⟨2550122, by rfl⟩ : syracuseStep 3400163 = 5100245) B5100245
theorem B3400177 : Blo 892572 3400177 := bstep (se 2 (by rfl) ⟨1275066, by rfl⟩ : syracuseStep 3400177 = 2550133) B2550133
theorem B1008211 : Blo 892572 1008211 := bstep (se 1 (by rfl) ⟨756158, by rfl⟩ : syracuseStep 1008211 = 1512317) B1512317
theorem B1434323 : Blo 892572 1434323 := bstep (se 1 (by rfl) ⟨1075742, by rfl⟩ : syracuseStep 1434323 = 2151485) B2151485
theorem B1008355 : Blo 892572 1008355 := bstep (se 1 (by rfl) ⟨756266, by rfl⟩ : syracuseStep 1008355 = 1512533) B1512533
theorem B2548493 : Blo 892572 2548493 := bstep (se 3 (by rfl) ⟨477842, by rfl⟩ : syracuseStep 2548493 = 955685) B955685
theorem B2417521 : Blo 892572 2417521 := bstep (se 2 (by rfl) ⟨906570, by rfl⟩ : syracuseStep 2417521 = 1813141) B1813141
theorem B1008499 : Blo 892572 1008499 := bstep (se 1 (by rfl) ⟨756374, by rfl⟩ : syracuseStep 1008499 = 1512749) B1512749
theorem B5235619 : Blo 892572 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B1434547 : Blo 892572 1434547 := bstep (se 1 (by rfl) ⟨1075910, by rfl⟩ : syracuseStep 1434547 = 2151821) B2151821
theorem B2548675 : Blo 892572 2548675 := bstep (se 1 (by rfl) ⟨1911506, by rfl⟩ : syracuseStep 2548675 = 3823013) B3823013
theorem B2548721 : Blo 892572 2548721 := bstep (se 2 (by rfl) ⟨955770, by rfl⟩ : syracuseStep 2548721 = 1911541) B1911541
theorem B1008643 : Blo 892572 1008643 := bstep (se 1 (by rfl) ⟨756482, by rfl⟩ : syracuseStep 1008643 = 1512965) B1512965
theorem B34366517 : Blo 892572 34366517 := bstep (se 5 (by rfl) ⟨1610930, by rfl⟩ : syracuseStep 34366517 = 3221861) B3221861
theorem B1696945 : Blo 892572 1696945 := bstep (se 2 (by rfl) ⟨636354, by rfl⟩ : syracuseStep 1696945 = 1272709) B1272709
theorem B1271057 : Blo 892572 1271057 := bstep (se 2 (by rfl) ⟨476646, by rfl⟩ : syracuseStep 1271057 = 953293) B953293
theorem B5432611 : Blo 892572 5432611 := bstep (se 1 (by rfl) ⟨4074458, by rfl⟩ : syracuseStep 5432611 = 8148917) B8148917
theorem B1697105 : Blo 892572 1697105 := bstep (se 2 (by rfl) ⟨636414, by rfl⟩ : syracuseStep 1697105 = 1272829) B1272829
theorem B1271171 : Blo 892572 1271171 := bstep (se 1 (by rfl) ⟨953378, by rfl⟩ : syracuseStep 1271171 = 1906757) B1906757
theorem B1271251 : Blo 892572 1271251 := bstep (se 1 (by rfl) ⟨953438, by rfl⟩ : syracuseStep 1271251 = 1906877) B1906877
theorem B3630563 : Blo 892572 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B25781813 : Blo 892572 25781813 := bstep (se 5 (by rfl) ⟨1208522, by rfl⟩ : syracuseStep 25781813 = 2417045) B2417045
theorem B1697507 : Blo 892572 1697507 := bstep (se 1 (by rfl) ⟨1273130, by rfl⟩ : syracuseStep 1697507 = 2546261) B2546261
theorem B1435553 : Blo 892572 1435553 := bstep (se 2 (by rfl) ⟨538332, by rfl⟩ : syracuseStep 1435553 = 1076665) B1076665
theorem B3401635 : Blo 892572 3401635 := bstep (se 1 (by rfl) ⟨2551226, by rfl⟩ : syracuseStep 3401635 = 5102453) B5102453
theorem B1271809 : Blo 892572 1271809 := bstep (se 2 (by rfl) ⟨476928, by rfl⟩ : syracuseStep 1271809 = 953857) B953857
theorem B1435745 : Blo 892572 1435745 := bstep (se 2 (by rfl) ⟨538404, by rfl⟩ : syracuseStep 1435745 = 1076809) B1076809
theorem B2418929 : Blo 892572 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B1861955 : Blo 892572 1861955 := bstep (se 1 (by rfl) ⟨1396466, by rfl⟩ : syracuseStep 1861955 = 2792933) B2792933
theorem B2550179 : Blo 892572 2550179 := bstep (se 1 (by rfl) ⟨1912634, by rfl⟩ : syracuseStep 2550179 = 3825269) B3825269
theorem B3631601 : Blo 892572 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B5171747 : Blo 892572 5171747 := bstep (se 1 (by rfl) ⟨3878810, by rfl⟩ : syracuseStep 5171747 = 7757621) B7757621
theorem B1698403 : Blo 892572 1698403 := bstep (se 1 (by rfl) ⟨1273802, by rfl⟩ : syracuseStep 1698403 = 2547605) B2547605
theorem B1206913 : Blo 892572 1206913 := bstep (se 2 (by rfl) ⟨452592, by rfl⟩ : syracuseStep 1206913 = 905185) B905185
theorem B1272515 : Blo 892572 1272515 := bstep (se 1 (by rfl) ⟨954386, by rfl⟩ : syracuseStep 1272515 = 1908773) B1908773
theorem B39217877 : Blo 892572 39217877 := bstep (se 7 (by rfl) ⟨459584, by rfl⟩ : syracuseStep 39217877 = 919169) B919169
theorem B1698563 : Blo 892572 1698563 := bstep (se 1 (by rfl) ⟨1273922, by rfl⟩ : syracuseStep 1698563 = 2547845) B2547845
theorem B1075987 : Blo 892572 1075987 := bstep (se 1 (by rfl) ⟨806990, by rfl⟩ : syracuseStep 1075987 = 1613981) B1613981
theorem B1469219 : Blo 892572 1469219 := bstep (se 1 (by rfl) ⟨1101914, by rfl⟩ : syracuseStep 1469219 = 2203829) B2203829
theorem B1469281 : Blo 892572 1469281 := bstep (se 2 (by rfl) ⟨550980, by rfl⟩ : syracuseStep 1469281 = 1101961) B1101961
theorem B17198021 : Blo 892572 17198021 := bstep (se 4 (by rfl) ⟨1612314, by rfl⟩ : syracuseStep 17198021 = 3224629) B3224629
theorem B2583569 : Blo 892572 2583569 := bstep (se 2 (by rfl) ⟨968838, by rfl⟩ : syracuseStep 2583569 = 1937677) B1937677
theorem B5729393 : Blo 892572 5729393 := bstep (se 2 (by rfl) ⟨2148522, by rfl⟩ : syracuseStep 5729393 = 4297045) B4297045
theorem B12905669 : Blo 892572 12905669 := bstep (se 4 (by rfl) ⟨1209906, by rfl⟩ : syracuseStep 12905669 = 2419813) B2419813
theorem B3829027 : Blo 892572 3829027 := bstep (se 1 (by rfl) ⟨2871770, by rfl⟩ : syracuseStep 3829027 = 5743541) B5743541
theorem B1273153 : Blo 892572 1273153 := bstep (se 2 (by rfl) ⟨477432, by rfl⟩ : syracuseStep 1273153 = 954865) B954865
theorem B1273267 : Blo 892572 1273267 := bstep (se 1 (by rfl) ⟨954950, by rfl⟩ : syracuseStep 1273267 = 1909901) B1909901
theorem B7630307 : Blo 892572 7630307 := bstep (se 1 (by rfl) ⟨5722730, by rfl⟩ : syracuseStep 7630307 = 11445461) B11445461
theorem B1338881 : Blo 892572 1338881 := bstep (se 2 (by rfl) ⟨502080, by rfl⟩ : syracuseStep 1338881 = 1004161) B1004161
theorem B1338899 : Blo 892572 1338899 := bstep (se 1 (by rfl) ⟨1004174, by rfl⟩ : syracuseStep 1338899 = 2008349) B2008349
theorem B1338929 : Blo 892572 1338929 := bstep (se 2 (by rfl) ⟨502098, by rfl⟩ : syracuseStep 1338929 = 1004197) B1004197
theorem B1338947 : Blo 892572 1338947 := bstep (se 1 (by rfl) ⟨1004210, by rfl⟩ : syracuseStep 1338947 = 2008421) B2008421
theorem B1338977 : Blo 892572 1338977 := bstep (se 2 (by rfl) ⟨502116, by rfl⟩ : syracuseStep 1338977 = 1004233) B1004233
theorem B2551409 : Blo 892572 2551409 := bstep (se 2 (by rfl) ⟨956778, by rfl⟩ : syracuseStep 2551409 = 1913557) B1913557
theorem B1338995 : Blo 892572 1338995 := bstep (se 1 (by rfl) ⟨1004246, by rfl⟩ : syracuseStep 1338995 = 2008493) B2008493
theorem B1339025 : Blo 892572 1339025 := bstep (se 2 (by rfl) ⟨502134, by rfl⟩ : syracuseStep 1339025 = 1004269) B1004269
theorem B1339043 : Blo 892572 1339043 := bstep (se 1 (by rfl) ⟨1004282, by rfl⟩ : syracuseStep 1339043 = 2008565) B2008565
theorem B1961635 : Blo 892572 1961635 := bstep (se 1 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 1961635 = 2942453) B2942453
theorem B1339073 : Blo 892572 1339073 := bstep (se 2 (by rfl) ⟨502152, by rfl⟩ : syracuseStep 1339073 = 1004305) B1004305
theorem B1339091 : Blo 892572 1339091 := bstep (se 1 (by rfl) ⟨1004318, by rfl⟩ : syracuseStep 1339091 = 2008637) B2008637
theorem B1339121 : Blo 892572 1339121 := bstep (se 2 (by rfl) ⟨502170, by rfl⟩ : syracuseStep 1339121 = 1004341) B1004341
theorem B1339139 : Blo 892572 1339139 := bstep (se 1 (by rfl) ⟨1004354, by rfl⟩ : syracuseStep 1339139 = 2008709) B2008709
theorem B5730061 : Blo 892572 5730061 := bstep (se 3 (by rfl) ⟨1074386, by rfl⟩ : syracuseStep 5730061 = 2148773) B2148773
theorem B1339169 : Blo 892572 1339169 := bstep (se 2 (by rfl) ⟨502188, by rfl⟩ : syracuseStep 1339169 = 1004377) B1004377
theorem B1699633 : Blo 892572 1699633 := bstep (se 2 (by rfl) ⟨637362, by rfl⟩ : syracuseStep 1699633 = 1274725) B1274725
theorem B1339187 : Blo 892572 1339187 := bstep (se 1 (by rfl) ⟨1004390, by rfl⟩ : syracuseStep 1339187 = 2008781) B2008781
theorem B1339217 : Blo 892572 1339217 := bstep (se 2 (by rfl) ⟨502206, by rfl⟩ : syracuseStep 1339217 = 1004413) B1004413
theorem B1339235 : Blo 892572 1339235 := bstep (se 1 (by rfl) ⟨1004426, by rfl⟩ : syracuseStep 1339235 = 2008853) B2008853
theorem B1339265 : Blo 892572 1339265 := bstep (se 2 (by rfl) ⟨502224, by rfl⟩ : syracuseStep 1339265 = 1004449) B1004449
theorem B8613773 : Blo 892572 8613773 := bstep (se 3 (by rfl) ⟨1615082, by rfl⟩ : syracuseStep 8613773 = 3230165) B3230165
theorem B1339283 : Blo 892572 1339283 := bstep (se 1 (by rfl) ⟨1004462, by rfl⟩ : syracuseStep 1339283 = 2008925) B2008925
theorem B1339313 : Blo 892572 1339313 := bstep (se 2 (by rfl) ⟨502242, by rfl⟩ : syracuseStep 1339313 = 1004485) B1004485
theorem B1339331 : Blo 892572 1339331 := bstep (se 1 (by rfl) ⟨1004498, by rfl⟩ : syracuseStep 1339331 = 2008997) B2008997
theorem B1339361 : Blo 892572 1339361 := bstep (se 2 (by rfl) ⟨502260, by rfl⟩ : syracuseStep 1339361 = 1004521) B1004521
theorem B1339379 : Blo 892572 1339379 := bstep (se 1 (by rfl) ⟨1004534, by rfl⟩ : syracuseStep 1339379 = 2009069) B2009069
theorem B1339409 : Blo 892572 1339409 := bstep (se 2 (by rfl) ⟨502278, by rfl⟩ : syracuseStep 1339409 = 1004557) B1004557
theorem B1339427 : Blo 892572 1339427 := bstep (se 1 (by rfl) ⟨1004570, by rfl⟩ : syracuseStep 1339427 = 2009141) B2009141
theorem B1306675 : Blo 892572 1306675 := bstep (se 1 (by rfl) ⟨980006, by rfl⟩ : syracuseStep 1306675 = 1960013) B1960013
theorem B1339457 : Blo 892572 1339457 := bstep (se 2 (by rfl) ⟨502296, by rfl⟩ : syracuseStep 1339457 = 1004593) B1004593
theorem B3403853 : Blo 892572 3403853 := bstep (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) B1276445
theorem B1339475 : Blo 892572 1339475 := bstep (se 1 (by rfl) ⟨1004606, by rfl⟩ : syracuseStep 1339475 = 2009213) B2009213
theorem B1339505 : Blo 892572 1339505 := bstep (se 2 (by rfl) ⟨502314, by rfl⟩ : syracuseStep 1339505 = 1004629) B1004629
theorem B1339523 : Blo 892572 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B1339553 : Blo 892572 1339553 := bstep (se 2 (by rfl) ⟨502332, by rfl⟩ : syracuseStep 1339553 = 1004665) B1004665
theorem B1339571 : Blo 892572 1339571 := bstep (se 1 (by rfl) ⟨1004678, by rfl⟩ : syracuseStep 1339571 = 2009357) B2009357
theorem B9662645 : Blo 892572 9662645 := bstep (se 5 (by rfl) ⟨452936, by rfl⟩ : syracuseStep 9662645 = 905873) B905873
theorem B1339601 : Blo 892572 1339601 := bstep (se 2 (by rfl) ⟨502350, by rfl⟩ : syracuseStep 1339601 = 1004701) B1004701
theorem B1339619 : Blo 892572 1339619 := bstep (se 1 (by rfl) ⟨1004714, by rfl⟩ : syracuseStep 1339619 = 2009429) B2009429
theorem B1339649 : Blo 892572 1339649 := bstep (se 2 (by rfl) ⟨502368, by rfl⟩ : syracuseStep 1339649 = 1004737) B1004737
theorem B1339667 : Blo 892572 1339667 := bstep (se 1 (by rfl) ⟨1004750, by rfl⟩ : syracuseStep 1339667 = 2009501) B2009501
theorem B1339697 : Blo 892572 1339697 := bstep (se 2 (by rfl) ⟨502386, by rfl⟩ : syracuseStep 1339697 = 1004773) B1004773
theorem B1339715 : Blo 892572 1339715 := bstep (se 1 (by rfl) ⟨1004786, by rfl⟩ : syracuseStep 1339715 = 2009573) B2009573
theorem B1339745 : Blo 892572 1339745 := bstep (se 2 (by rfl) ⟨502404, by rfl⟩ : syracuseStep 1339745 = 1004809) B1004809
theorem B1339763 : Blo 892572 1339763 := bstep (se 1 (by rfl) ⟨1004822, by rfl⟩ : syracuseStep 1339763 = 2009645) B2009645
theorem B1339793 : Blo 892572 1339793 := bstep (se 2 (by rfl) ⟨502422, by rfl⟩ : syracuseStep 1339793 = 1004845) B1004845
theorem B1339811 : Blo 892572 1339811 := bstep (se 1 (by rfl) ⟨1004858, by rfl⟩ : syracuseStep 1339811 = 2009717) B2009717
theorem B1339841 : Blo 892572 1339841 := bstep (se 2 (by rfl) ⟨502440, by rfl⟩ : syracuseStep 1339841 = 1004881) B1004881
theorem B1339859 : Blo 892572 1339859 := bstep (se 1 (by rfl) ⟨1004894, by rfl⟩ : syracuseStep 1339859 = 2009789) B2009789
theorem B1339889 : Blo 892572 1339889 := bstep (se 2 (by rfl) ⟨502458, by rfl⟩ : syracuseStep 1339889 = 1004917) B1004917
theorem B1339907 : Blo 892572 1339907 := bstep (se 1 (by rfl) ⟨1004930, by rfl⟩ : syracuseStep 1339907 = 2009861) B2009861
theorem B1339937 : Blo 892572 1339937 := bstep (se 2 (by rfl) ⟨502476, by rfl⟩ : syracuseStep 1339937 = 1004953) B1004953
theorem B1339955 : Blo 892572 1339955 := bstep (se 1 (by rfl) ⟨1004966, by rfl⟩ : syracuseStep 1339955 = 2009933) B2009933
theorem B1339985 : Blo 892572 1339985 := bstep (se 2 (by rfl) ⟨502494, by rfl⟩ : syracuseStep 1339985 = 1004989) B1004989
theorem B1340003 : Blo 892572 1340003 := bstep (se 1 (by rfl) ⟨1005002, by rfl⟩ : syracuseStep 1340003 = 2010005) B2010005
theorem B1340033 : Blo 892572 1340033 := bstep (se 2 (by rfl) ⟨502512, by rfl⟩ : syracuseStep 1340033 = 1005025) B1005025
theorem B1340051 : Blo 892572 1340051 := bstep (se 1 (by rfl) ⟨1005038, by rfl⟩ : syracuseStep 1340051 = 2010077) B2010077
theorem B1340081 : Blo 892572 1340081 := bstep (se 2 (by rfl) ⟨502530, by rfl⟩ : syracuseStep 1340081 = 1005061) B1005061
theorem B1340099 : Blo 892572 1340099 := bstep (se 1 (by rfl) ⟨1005074, by rfl⟩ : syracuseStep 1340099 = 2010149) B2010149
theorem B14676677 : Blo 892572 14676677 := bstep (se 4 (by rfl) ⟨1375938, by rfl⟩ : syracuseStep 14676677 = 2751877) B2751877
theorem B1340129 : Blo 892572 1340129 := bstep (se 2 (by rfl) ⟨502548, by rfl⟩ : syracuseStep 1340129 = 1005097) B1005097
theorem B1340147 : Blo 892572 1340147 := bstep (se 1 (by rfl) ⟨1005110, by rfl⟩ : syracuseStep 1340147 = 2010221) B2010221
theorem B1274611 : Blo 892572 1274611 := bstep (se 1 (by rfl) ⟨955958, by rfl⟩ : syracuseStep 1274611 = 1911917) B1911917
theorem B1307395 : Blo 892572 1307395 := bstep (se 1 (by rfl) ⟨980546, by rfl⟩ : syracuseStep 1307395 = 1961093) B1961093
theorem B2716429 : Blo 892572 2716429 := bstep (se 3 (by rfl) ⟨509330, by rfl⟩ : syracuseStep 2716429 = 1018661) B1018661
theorem B1340177 : Blo 892572 1340177 := bstep (se 2 (by rfl) ⟨502566, by rfl⟩ : syracuseStep 1340177 = 1005133) B1005133
theorem B1340195 : Blo 892572 1340195 := bstep (se 1 (by rfl) ⟨1005146, by rfl⟩ : syracuseStep 1340195 = 2010293) B2010293
theorem B1340225 : Blo 892572 1340225 := bstep (se 2 (by rfl) ⟨502584, by rfl⟩ : syracuseStep 1340225 = 1005169) B1005169
theorem B4289357 : Blo 892572 4289357 := bstep (se 3 (by rfl) ⟨804254, by rfl⟩ : syracuseStep 4289357 = 1608509) B1608509
theorem B1700689 : Blo 892572 1700689 := bstep (se 2 (by rfl) ⟨637758, by rfl⟩ : syracuseStep 1700689 = 1275517) B1275517
theorem B1340243 : Blo 892572 1340243 := bstep (se 1 (by rfl) ⟨1005182, by rfl⟩ : syracuseStep 1340243 = 2010365) B2010365
theorem B1340273 : Blo 892572 1340273 := bstep (se 2 (by rfl) ⟨502602, by rfl⟩ : syracuseStep 1340273 = 1005205) B1005205
theorem B1340291 : Blo 892572 1340291 := bstep (se 1 (by rfl) ⟨1005218, by rfl⟩ : syracuseStep 1340291 = 2010437) B2010437
theorem B1340321 : Blo 892572 1340321 := bstep (se 2 (by rfl) ⟨502620, by rfl⟩ : syracuseStep 1340321 = 1005241) B1005241
theorem B1340339 : Blo 892572 1340339 := bstep (se 1 (by rfl) ⟨1005254, by rfl⟩ : syracuseStep 1340339 = 2010509) B2010509
theorem B1340369 : Blo 892572 1340369 := bstep (se 2 (by rfl) ⟨502638, by rfl⟩ : syracuseStep 1340369 = 1005277) B1005277
theorem B1340387 : Blo 892572 1340387 := bstep (se 1 (by rfl) ⟨1005290, by rfl⟩ : syracuseStep 1340387 = 2010581) B2010581
theorem B1340417 : Blo 892572 1340417 := bstep (se 2 (by rfl) ⟨502656, by rfl⟩ : syracuseStep 1340417 = 1005313) B1005313
theorem B1340435 : Blo 892572 1340435 := bstep (se 1 (by rfl) ⟨1005326, by rfl⟩ : syracuseStep 1340435 = 2010653) B2010653
theorem B2552867 : Blo 892572 2552867 := bstep (se 1 (by rfl) ⟨1914650, by rfl⟩ : syracuseStep 2552867 = 3829301) B3829301
theorem B1340465 : Blo 892572 1340465 := bstep (se 2 (by rfl) ⟨502674, by rfl⟩ : syracuseStep 1340465 = 1005349) B1005349
theorem B1340483 : Blo 892572 1340483 := bstep (se 1 (by rfl) ⟨1005362, by rfl⟩ : syracuseStep 1340483 = 2010725) B2010725
theorem B4518989 : Blo 892572 4518989 := bstep (se 3 (by rfl) ⟨847310, by rfl⟩ : syracuseStep 4518989 = 1694621) B1694621
theorem B1340513 : Blo 892572 1340513 := bstep (se 2 (by rfl) ⟨502692, by rfl⟩ : syracuseStep 1340513 = 1005385) B1005385
theorem B1340531 : Blo 892572 1340531 := bstep (se 1 (by rfl) ⟨1005398, by rfl⟩ : syracuseStep 1340531 = 2010797) B2010797
theorem B1340561 : Blo 892572 1340561 := bstep (se 2 (by rfl) ⟨502710, by rfl⟩ : syracuseStep 1340561 = 1005421) B1005421
theorem B1340579 : Blo 892572 1340579 := bstep (se 1 (by rfl) ⟨1005434, by rfl⟩ : syracuseStep 1340579 = 2010869) B2010869
theorem B1340609 : Blo 892572 1340609 := bstep (se 2 (by rfl) ⟨502728, by rfl⟩ : syracuseStep 1340609 = 1005457) B1005457
theorem B1340627 : Blo 892572 1340627 := bstep (se 1 (by rfl) ⟨1005470, by rfl⟩ : syracuseStep 1340627 = 2010941) B2010941
theorem B1701091 : Blo 892572 1701091 := bstep (se 1 (by rfl) ⟨1275818, by rfl⟩ : syracuseStep 1701091 = 2551637) B2551637
theorem B1340657 : Blo 892572 1340657 := bstep (se 2 (by rfl) ⟨502746, by rfl⟩ : syracuseStep 1340657 = 1005493) B1005493
theorem B1340675 : Blo 892572 1340675 := bstep (se 1 (by rfl) ⟨1005506, by rfl⟩ : syracuseStep 1340675 = 2011013) B2011013
theorem B2422019 : Blo 892572 2422019 := bstep (se 1 (by rfl) ⟨1816514, by rfl⟩ : syracuseStep 2422019 = 3633029) B3633029
theorem B1701137 : Blo 892572 1701137 := bstep (se 2 (by rfl) ⟨637926, by rfl⟩ : syracuseStep 1701137 = 1275853) B1275853
theorem B1340705 : Blo 892572 1340705 := bstep (se 2 (by rfl) ⟨502764, by rfl⟩ : syracuseStep 1340705 = 1005529) B1005529
theorem B1340723 : Blo 892572 1340723 := bstep (se 1 (by rfl) ⟨1005542, by rfl⟩ : syracuseStep 1340723 = 2011085) B2011085
theorem B1340753 : Blo 892572 1340753 := bstep (se 2 (by rfl) ⟨502782, by rfl⟩ : syracuseStep 1340753 = 1005565) B1005565
theorem B1340771 : Blo 892572 1340771 := bstep (se 1 (by rfl) ⟨1005578, by rfl⟩ : syracuseStep 1340771 = 2011157) B2011157
theorem B1340801 : Blo 892572 1340801 := bstep (se 2 (by rfl) ⟨502800, by rfl⟩ : syracuseStep 1340801 = 1005601) B1005601
theorem B1340819 : Blo 892572 1340819 := bstep (se 1 (by rfl) ⟨1005614, by rfl⟩ : syracuseStep 1340819 = 2011229) B2011229
theorem B1340849 : Blo 892572 1340849 := bstep (se 2 (by rfl) ⟨502818, by rfl⟩ : syracuseStep 1340849 = 1005637) B1005637
theorem B5174705 : Blo 892572 5174705 := bstep (se 2 (by rfl) ⟨1940514, by rfl⟩ : syracuseStep 5174705 = 3881029) B3881029
theorem B1340867 : Blo 892572 1340867 := bstep (se 1 (by rfl) ⟨1005650, by rfl⟩ : syracuseStep 1340867 = 2011301) B2011301
theorem B1340897 : Blo 892572 1340897 := bstep (se 2 (by rfl) ⟨502836, by rfl⟩ : syracuseStep 1340897 = 1005673) B1005673
theorem B1340915 : Blo 892572 1340915 := bstep (se 1 (by rfl) ⟨1005686, by rfl⟩ : syracuseStep 1340915 = 2011373) B2011373
theorem B1340945 : Blo 892572 1340945 := bstep (se 2 (by rfl) ⟨502854, by rfl⟩ : syracuseStep 1340945 = 1005709) B1005709
theorem B1340963 : Blo 892572 1340963 := bstep (se 1 (by rfl) ⟨1005722, by rfl⟩ : syracuseStep 1340963 = 2011445) B2011445
theorem B1701425 : Blo 892572 1701425 := bstep (se 2 (by rfl) ⟨638034, by rfl⟩ : syracuseStep 1701425 = 1276069) B1276069
theorem B1340993 : Blo 892572 1340993 := bstep (se 2 (by rfl) ⟨502872, by rfl⟩ : syracuseStep 1340993 = 1005745) B1005745
theorem B1341011 : Blo 892572 1341011 := bstep (se 1 (by rfl) ⟨1005758, by rfl⟩ : syracuseStep 1341011 = 2011517) B2011517
theorem B1341041 : Blo 892572 1341041 := bstep (se 2 (by rfl) ⟨502890, by rfl⟩ : syracuseStep 1341041 = 1005781) B1005781
theorem B1341059 : Blo 892572 1341059 := bstep (se 1 (by rfl) ⟨1005794, by rfl⟩ : syracuseStep 1341059 = 2011589) B2011589
theorem B1341089 : Blo 892572 1341089 := bstep (se 2 (by rfl) ⟨502908, by rfl⟩ : syracuseStep 1341089 = 1005817) B1005817
theorem B1341107 : Blo 892572 1341107 := bstep (se 1 (by rfl) ⟨1005830, by rfl⟩ : syracuseStep 1341107 = 2011661) B2011661
theorem B1341137 : Blo 892572 1341137 := bstep (se 2 (by rfl) ⟨502926, by rfl⟩ : syracuseStep 1341137 = 1005853) B1005853
theorem B1341155 : Blo 892572 1341155 := bstep (se 1 (by rfl) ⟨1005866, by rfl⟩ : syracuseStep 1341155 = 2011733) B2011733
theorem B1341185 : Blo 892572 1341185 := bstep (se 2 (by rfl) ⟨502944, by rfl⟩ : syracuseStep 1341185 = 1005889) B1005889
theorem B1341203 : Blo 892572 1341203 := bstep (se 1 (by rfl) ⟨1005902, by rfl⟩ : syracuseStep 1341203 = 2011805) B2011805
theorem B1341233 : Blo 892572 1341233 := bstep (se 2 (by rfl) ⟨502962, by rfl⟩ : syracuseStep 1341233 = 1005925) B1005925
theorem B1341251 : Blo 892572 1341251 := bstep (se 1 (by rfl) ⟨1005938, by rfl⟩ : syracuseStep 1341251 = 2011877) B2011877
theorem B1341281 : Blo 892572 1341281 := bstep (se 2 (by rfl) ⟨502980, by rfl⟩ : syracuseStep 1341281 = 1005961) B1005961
theorem B1275745 : Blo 892572 1275745 := bstep (se 2 (by rfl) ⟨478404, by rfl⟩ : syracuseStep 1275745 = 956809) B956809
theorem B19363697 : Blo 892572 19363697 := bstep (se 2 (by rfl) ⟨7261386, by rfl⟩ : syracuseStep 19363697 = 14522773) B14522773
theorem B1341299 : Blo 892572 1341299 := bstep (se 1 (by rfl) ⟨1005974, by rfl⟩ : syracuseStep 1341299 = 2011949) B2011949
theorem B1210243 : Blo 892572 1210243 := bstep (se 1 (by rfl) ⟨907682, by rfl⟩ : syracuseStep 1210243 = 1815365) B1815365
theorem B3012497 : Blo 892572 3012497 := bstep (se 2 (by rfl) ⟨1129686, by rfl⟩ : syracuseStep 3012497 = 2259373) B2259373
theorem B1341329 : Blo 892572 1341329 := bstep (se 2 (by rfl) ⟨502998, by rfl⟩ : syracuseStep 1341329 = 1005997) B1005997
theorem B1341347 : Blo 892572 1341347 := bstep (se 1 (by rfl) ⟨1006010, by rfl⟩ : syracuseStep 1341347 = 2012021) B2012021
theorem B1341377 : Blo 892572 1341377 := bstep (se 2 (by rfl) ⟨503016, by rfl⟩ : syracuseStep 1341377 = 1006033) B1006033
theorem B1275841 : Blo 892572 1275841 := bstep (se 2 (by rfl) ⟨478440, by rfl⟩ : syracuseStep 1275841 = 956881) B956881
theorem B1341395 : Blo 892572 1341395 := bstep (se 1 (by rfl) ⟨1006046, by rfl⟩ : syracuseStep 1341395 = 2012093) B2012093
theorem B6191075 : Blo 892572 6191075 := bstep (se 1 (by rfl) ⟨4643306, by rfl⟩ : syracuseStep 6191075 = 9286613) B9286613
theorem B3635171 : Blo 892572 3635171 := bstep (se 1 (by rfl) ⟨2726378, by rfl⟩ : syracuseStep 3635171 = 5452757) B5452757
theorem B1341425 : Blo 892572 1341425 := bstep (se 2 (by rfl) ⟨503034, by rfl⟩ : syracuseStep 1341425 = 1006069) B1006069
theorem B1341443 : Blo 892572 1341443 := bstep (se 1 (by rfl) ⟨1006082, by rfl⟩ : syracuseStep 1341443 = 2012165) B2012165
theorem B1341473 : Blo 892572 1341473 := bstep (se 2 (by rfl) ⟨503052, by rfl⟩ : syracuseStep 1341473 = 1006105) B1006105
theorem B1341491 : Blo 892572 1341491 := bstep (se 1 (by rfl) ⟨1006118, by rfl⟩ : syracuseStep 1341491 = 2012237) B2012237
theorem B1341521 : Blo 892572 1341521 := bstep (se 2 (by rfl) ⟨503070, by rfl⟩ : syracuseStep 1341521 = 1006141) B1006141
theorem B1341539 : Blo 892572 1341539 := bstep (se 1 (by rfl) ⟨1006154, by rfl⟩ : syracuseStep 1341539 = 2012309) B2012309
theorem B1341569 : Blo 892572 1341569 := bstep (se 2 (by rfl) ⟨503088, by rfl⟩ : syracuseStep 1341569 = 1006177) B1006177
theorem B1341587 : Blo 892572 1341587 := bstep (se 1 (by rfl) ⟨1006190, by rfl⟩ : syracuseStep 1341587 = 2012381) B2012381
theorem B1341617 : Blo 892572 1341617 := bstep (se 2 (by rfl) ⟨503106, by rfl⟩ : syracuseStep 1341617 = 1006213) B1006213
theorem B1341635 : Blo 892572 1341635 := bstep (se 1 (by rfl) ⟨1006226, by rfl⟩ : syracuseStep 1341635 = 2012453) B2012453
theorem B5306573 : Blo 892572 5306573 := bstep (se 3 (by rfl) ⟨994982, by rfl⟩ : syracuseStep 5306573 = 1989965) B1989965
theorem B1341665 : Blo 892572 1341665 := bstep (se 2 (by rfl) ⟨503124, by rfl⟩ : syracuseStep 1341665 = 1006249) B1006249
theorem B1341683 : Blo 892572 1341683 := bstep (se 1 (by rfl) ⟨1006262, by rfl⟩ : syracuseStep 1341683 = 2012525) B2012525
theorem B1341713 : Blo 892572 1341713 := bstep (se 2 (by rfl) ⟨503142, by rfl⟩ : syracuseStep 1341713 = 1006285) B1006285
theorem B1341731 : Blo 892572 1341731 := bstep (se 1 (by rfl) ⟨1006298, by rfl⟩ : syracuseStep 1341731 = 2012597) B2012597
theorem B1341761 : Blo 892572 1341761 := bstep (se 2 (by rfl) ⟨503160, by rfl⟩ : syracuseStep 1341761 = 1006321) B1006321
theorem B1341779 : Blo 892572 1341779 := bstep (se 1 (by rfl) ⟨1006334, by rfl⟩ : syracuseStep 1341779 = 2012669) B2012669
theorem B1341809 : Blo 892572 1341809 := bstep (se 2 (by rfl) ⟨503178, by rfl⟩ : syracuseStep 1341809 = 1006357) B1006357
theorem B1341827 : Blo 892572 1341827 := bstep (se 1 (by rfl) ⟨1006370, by rfl⟩ : syracuseStep 1341827 = 2012741) B2012741
theorem B1341857 : Blo 892572 1341857 := bstep (se 2 (by rfl) ⟨503196, by rfl⟩ : syracuseStep 1341857 = 1006393) B1006393
theorem B2292131 : Blo 892572 2292131 := bstep (se 1 (by rfl) ⟨1719098, by rfl⟩ : syracuseStep 2292131 = 3438197) B3438197
theorem B3013037 : Blo 892572 3013037 := bstep (se 3 (by rfl) ⟨564944, by rfl⟩ : syracuseStep 3013037 = 1129889) B1129889
theorem B1276337 : Blo 892572 1276337 := bstep (se 2 (by rfl) ⟨478626, by rfl⟩ : syracuseStep 1276337 = 957253) B957253
theorem B1341875 : Blo 892572 1341875 := bstep (se 1 (by rfl) ⟨1006406, by rfl⟩ : syracuseStep 1341875 = 2012813) B2012813
theorem B6453701 : Blo 892572 6453701 := bstep (se 4 (by rfl) ⟨605034, by rfl⟩ : syracuseStep 6453701 = 1210069) B1210069
theorem B2718157 : Blo 892572 2718157 := bstep (se 3 (by rfl) ⟨509654, by rfl⟩ : syracuseStep 2718157 = 1019309) B1019309
theorem B1341905 : Blo 892572 1341905 := bstep (se 2 (by rfl) ⟨503214, by rfl⟩ : syracuseStep 1341905 = 1006429) B1006429
theorem B3013091 : Blo 892572 3013091 := bstep (se 1 (by rfl) ⟨2259818, by rfl⟩ : syracuseStep 3013091 = 4519637) B4519637
theorem B1341923 : Blo 892572 1341923 := bstep (se 1 (by rfl) ⟨1006442, by rfl⟩ : syracuseStep 1341923 = 2012885) B2012885
theorem B1341953 : Blo 892572 1341953 := bstep (se 2 (by rfl) ⟨503232, by rfl⟩ : syracuseStep 1341953 = 1006465) B1006465
theorem B1341971 : Blo 892572 1341971 := bstep (se 1 (by rfl) ⟨1006478, by rfl⟩ : syracuseStep 1341971 = 2012957) B2012957
theorem B1342001 : Blo 892572 1342001 := bstep (se 2 (by rfl) ⟨503250, by rfl⟩ : syracuseStep 1342001 = 1006501) B1006501
theorem B1210945 : Blo 892572 1210945 := bstep (se 2 (by rfl) ⟨454104, by rfl⟩ : syracuseStep 1210945 = 908209) B908209
theorem B1342019 : Blo 892572 1342019 := bstep (se 1 (by rfl) ⟨1006514, by rfl⟩ : syracuseStep 1342019 = 2013029) B2013029
theorem B1342049 : Blo 892572 1342049 := bstep (se 2 (by rfl) ⟨503268, by rfl⟩ : syracuseStep 1342049 = 1006537) B1006537
theorem B1342067 : Blo 892572 1342067 := bstep (se 1 (by rfl) ⟨1006550, by rfl⟩ : syracuseStep 1342067 = 2013101) B2013101
theorem B1342097 : Blo 892572 1342097 := bstep (se 2 (by rfl) ⟨503286, by rfl⟩ : syracuseStep 1342097 = 1006573) B1006573
theorem B1342115 : Blo 892572 1342115 := bstep (se 1 (by rfl) ⟨1006586, by rfl⟩ : syracuseStep 1342115 = 2013173) B2013173
theorem B1342145 : Blo 892572 1342145 := bstep (se 2 (by rfl) ⟨503304, by rfl⟩ : syracuseStep 1342145 = 1006609) B1006609
theorem B1342163 : Blo 892572 1342163 := bstep (se 1 (by rfl) ⟨1006622, by rfl⟩ : syracuseStep 1342163 = 2013245) B2013245
theorem B2259697 : Blo 892572 2259697 := bstep (se 2 (by rfl) ⟨847386, by rfl⟩ : syracuseStep 2259697 = 1694773) B1694773
theorem B3013361 : Blo 892572 3013361 := bstep (se 2 (by rfl) ⟨1130010, by rfl⟩ : syracuseStep 3013361 = 2260021) B2260021
theorem B1342193 : Blo 892572 1342193 := bstep (se 2 (by rfl) ⟨503322, by rfl⟩ : syracuseStep 1342193 = 1006645) B1006645
theorem B1342211 : Blo 892572 1342211 := bstep (se 1 (by rfl) ⟨1006658, by rfl⟩ : syracuseStep 1342211 = 2013317) B2013317
theorem B1342241 : Blo 892572 1342241 := bstep (se 2 (by rfl) ⟨503340, by rfl⟩ : syracuseStep 1342241 = 1006681) B1006681
theorem B1342259 : Blo 892572 1342259 := bstep (se 1 (by rfl) ⟨1006694, by rfl⟩ : syracuseStep 1342259 = 2013389) B2013389
theorem B1342289 : Blo 892572 1342289 := bstep (se 2 (by rfl) ⟨503358, by rfl⟩ : syracuseStep 1342289 = 1006717) B1006717
theorem B1342307 : Blo 892572 1342307 := bstep (se 1 (by rfl) ⟨1006730, by rfl⟩ : syracuseStep 1342307 = 2013461) B2013461
theorem B1342337 : Blo 892572 1342337 := bstep (se 2 (by rfl) ⟨503376, by rfl⟩ : syracuseStep 1342337 = 1006753) B1006753
theorem B1342355 : Blo 892572 1342355 := bstep (se 1 (by rfl) ⟨1006766, by rfl⟩ : syracuseStep 1342355 = 2013533) B2013533
theorem B1342385 : Blo 892572 1342385 := bstep (se 2 (by rfl) ⟨503394, by rfl⟩ : syracuseStep 1342385 = 1006789) B1006789
theorem B1342403 : Blo 892572 1342403 := bstep (se 1 (by rfl) ⟨1006802, by rfl⟩ : syracuseStep 1342403 = 2013605) B2013605
theorem B1342433 : Blo 892572 1342433 := bstep (se 2 (by rfl) ⟨503412, by rfl⟩ : syracuseStep 1342433 = 1006825) B1006825
theorem B1506289 : Blo 892572 1506289 := bstep (se 2 (by rfl) ⟨564858, by rfl⟩ : syracuseStep 1506289 = 1129717) B1129717
theorem B1342451 : Blo 892572 1342451 := bstep (se 1 (by rfl) ⟨1006838, by rfl⟩ : syracuseStep 1342451 = 2013677) B2013677
theorem B2259971 : Blo 892572 2259971 := bstep (se 1 (by rfl) ⟨1694978, by rfl⟩ : syracuseStep 2259971 = 3389957) B3389957
theorem B1342481 : Blo 892572 1342481 := bstep (se 2 (by rfl) ⟨503430, by rfl⟩ : syracuseStep 1342481 = 1006861) B1006861
theorem B1506323 : Blo 892572 1506323 := bstep (se 1 (by rfl) ⟨1129742, by rfl⟩ : syracuseStep 1506323 = 2259485) B2259485
theorem B1342499 : Blo 892572 1342499 := bstep (se 1 (by rfl) ⟨1006874, by rfl⟩ : syracuseStep 1342499 = 2013749) B2013749
theorem B1342529 : Blo 892572 1342529 := bstep (se 2 (by rfl) ⟨503448, by rfl⟩ : syracuseStep 1342529 = 1006897) B1006897
theorem B1342547 : Blo 892572 1342547 := bstep (se 1 (by rfl) ⟨1006910, by rfl⟩ : syracuseStep 1342547 = 2013821) B2013821
theorem B1342577 : Blo 892572 1342577 := bstep (se 2 (by rfl) ⟨503466, by rfl⟩ : syracuseStep 1342577 = 1006933) B1006933
theorem B1342595 : Blo 892572 1342595 := bstep (se 1 (by rfl) ⟨1006946, by rfl⟩ : syracuseStep 1342595 = 2013893) B2013893
theorem B1506451 : Blo 892572 1506451 := bstep (se 1 (by rfl) ⟨1129838, by rfl⟩ : syracuseStep 1506451 = 2259677) B2259677
theorem B1342625 : Blo 892572 1342625 := bstep (se 2 (by rfl) ⟨503484, by rfl⟩ : syracuseStep 1342625 = 1006969) B1006969
theorem B1342643 : Blo 892572 1342643 := bstep (se 1 (by rfl) ⟨1006982, by rfl⟩ : syracuseStep 1342643 = 2013965) B2013965
theorem B2260163 : Blo 892572 2260163 := bstep (se 1 (by rfl) ⟨1695122, by rfl⟩ : syracuseStep 2260163 = 3390245) B3390245
theorem B1342673 : Blo 892572 1342673 := bstep (se 2 (by rfl) ⟨503502, by rfl⟩ : syracuseStep 1342673 = 1007005) B1007005
theorem B49544419 : Blo 892572 49544419 := bstep (se 1 (by rfl) ⟨37158314, by rfl⟩ : syracuseStep 49544419 = 74316629) B74316629
theorem B1342691 : Blo 892572 1342691 := bstep (se 1 (by rfl) ⟨1007018, by rfl⟩ : syracuseStep 1342691 = 2014037) B2014037
theorem B1342721 : Blo 892572 1342721 := bstep (se 2 (by rfl) ⟨503520, by rfl⟩ : syracuseStep 1342721 = 1007041) B1007041
theorem B3013901 : Blo 892572 3013901 := bstep (se 3 (by rfl) ⟨565106, by rfl⟩ : syracuseStep 3013901 = 1130213) B1130213
theorem B1342739 : Blo 892572 1342739 := bstep (se 1 (by rfl) ⟨1007054, by rfl⟩ : syracuseStep 1342739 = 2014109) B2014109
theorem B1506593 : Blo 892572 1506593 := bstep (se 2 (by rfl) ⟨564972, by rfl⟩ : syracuseStep 1506593 = 1129945) B1129945
theorem B1342769 : Blo 892572 1342769 := bstep (se 2 (by rfl) ⟨503538, by rfl⟩ : syracuseStep 1342769 = 1007077) B1007077
theorem B3013955 : Blo 892572 3013955 := bstep (se 1 (by rfl) ⟨2260466, by rfl⟩ : syracuseStep 3013955 = 4520933) B4520933
theorem B1342787 : Blo 892572 1342787 := bstep (se 1 (by rfl) ⟨1007090, by rfl⟩ : syracuseStep 1342787 = 2014181) B2014181
theorem B3439949 : Blo 892572 3439949 := bstep (se 3 (by rfl) ⟨644990, by rfl⟩ : syracuseStep 3439949 = 1289981) B1289981
theorem B1342817 : Blo 892572 1342817 := bstep (se 2 (by rfl) ⟨503556, by rfl⟩ : syracuseStep 1342817 = 1007113) B1007113
theorem B1342835 : Blo 892572 1342835 := bstep (se 1 (by rfl) ⟨1007126, by rfl⟩ : syracuseStep 1342835 = 2014253) B2014253
theorem B1342865 : Blo 892572 1342865 := bstep (se 2 (by rfl) ⟨503574, by rfl⟩ : syracuseStep 1342865 = 1007149) B1007149
theorem B1506721 : Blo 892572 1506721 := bstep (se 2 (by rfl) ⟨565020, by rfl⟩ : syracuseStep 1506721 = 1130041) B1130041
theorem B1342883 : Blo 892572 1342883 := bstep (se 1 (by rfl) ⟨1007162, by rfl⟩ : syracuseStep 1342883 = 2014325) B2014325
theorem B1342913 : Blo 892572 1342913 := bstep (se 2 (by rfl) ⟨503592, by rfl⟩ : syracuseStep 1342913 = 1007185) B1007185
theorem B1506755 : Blo 892572 1506755 := bstep (se 1 (by rfl) ⟨1130066, by rfl⟩ : syracuseStep 1506755 = 2260133) B2260133
theorem B1342931 : Blo 892572 1342931 := bstep (se 1 (by rfl) ⟨1007198, by rfl⟩ : syracuseStep 1342931 = 2014397) B2014397
theorem B1342961 : Blo 892572 1342961 := bstep (se 2 (by rfl) ⟨503610, by rfl⟩ : syracuseStep 1342961 = 1007221) B1007221
theorem B1342979 : Blo 892572 1342979 := bstep (se 1 (by rfl) ⟨1007234, by rfl⟩ : syracuseStep 1342979 = 2014469) B2014469
theorem B1343009 : Blo 892572 1343009 := bstep (se 2 (by rfl) ⟨503628, by rfl⟩ : syracuseStep 1343009 = 1007257) B1007257
theorem B1343027 : Blo 892572 1343027 := bstep (se 1 (by rfl) ⟨1007270, by rfl⟩ : syracuseStep 1343027 = 2014541) B2014541
theorem B1506883 : Blo 892572 1506883 := bstep (se 1 (by rfl) ⟨1130162, by rfl⟩ : syracuseStep 1506883 = 2260325) B2260325
theorem B3014225 : Blo 892572 3014225 := bstep (se 2 (by rfl) ⟨1130334, by rfl⟩ : syracuseStep 3014225 = 2260669) B2260669
theorem B1343057 : Blo 892572 1343057 := bstep (se 2 (by rfl) ⟨503646, by rfl⟩ : syracuseStep 1343057 = 1007293) B1007293
theorem B1343075 : Blo 892572 1343075 := bstep (se 1 (by rfl) ⟨1007306, by rfl⟩ : syracuseStep 1343075 = 2014613) B2014613
theorem B1343105 : Blo 892572 1343105 := bstep (se 2 (by rfl) ⟨503664, by rfl⟩ : syracuseStep 1343105 = 1007329) B1007329
theorem B1343123 : Blo 892572 1343123 := bstep (se 1 (by rfl) ⟨1007342, by rfl⟩ : syracuseStep 1343123 = 2014685) B2014685
theorem B1343153 : Blo 892572 1343153 := bstep (se 2 (by rfl) ⟨503682, by rfl⟩ : syracuseStep 1343153 = 1007365) B1007365
theorem B1343171 : Blo 892572 1343171 := bstep (se 1 (by rfl) ⟨1007378, by rfl⟩ : syracuseStep 1343171 = 2014757) B2014757
theorem B1507025 : Blo 892572 1507025 := bstep (se 2 (by rfl) ⟨565134, by rfl⟩ : syracuseStep 1507025 = 1130269) B1130269
theorem B1343201 : Blo 892572 1343201 := bstep (se 2 (by rfl) ⟨503700, by rfl⟩ : syracuseStep 1343201 = 1007401) B1007401
theorem B1343219 : Blo 892572 1343219 := bstep (se 1 (by rfl) ⟨1007414, by rfl⟩ : syracuseStep 1343219 = 2014829) B2014829
theorem B1343249 : Blo 892572 1343249 := bstep (se 2 (by rfl) ⟨503718, by rfl⟩ : syracuseStep 1343249 = 1007437) B1007437
theorem B1343267 : Blo 892572 1343267 := bstep (se 1 (by rfl) ⟨1007450, by rfl⟩ : syracuseStep 1343267 = 2014901) B2014901
theorem B1343297 : Blo 892572 1343297 := bstep (se 2 (by rfl) ⟨503736, by rfl⟩ : syracuseStep 1343297 = 1007473) B1007473
theorem B1507153 : Blo 892572 1507153 := bstep (se 2 (by rfl) ⟨565182, by rfl⟩ : syracuseStep 1507153 = 1130365) B1130365
theorem B1343315 : Blo 892572 1343315 := bstep (se 1 (by rfl) ⟨1007486, by rfl⟩ : syracuseStep 1343315 = 2014973) B2014973
theorem B1343345 : Blo 892572 1343345 := bstep (se 2 (by rfl) ⟨503754, by rfl⟩ : syracuseStep 1343345 = 1007509) B1007509
theorem B1507187 : Blo 892572 1507187 := bstep (se 1 (by rfl) ⟨1130390, by rfl⟩ : syracuseStep 1507187 = 2260781) B2260781
theorem B1343363 : Blo 892572 1343363 := bstep (se 1 (by rfl) ⟨1007522, by rfl⟩ : syracuseStep 1343363 = 2015045) B2015045
theorem B1343393 : Blo 892572 1343393 := bstep (se 2 (by rfl) ⟨503772, by rfl⟩ : syracuseStep 1343393 = 1007545) B1007545
theorem B4521905 : Blo 892572 4521905 := bstep (se 2 (by rfl) ⟨1695714, by rfl⟩ : syracuseStep 4521905 = 3391429) B3391429
theorem B1343411 : Blo 892572 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B1343441 : Blo 892572 1343441 := bstep (se 2 (by rfl) ⟨503790, by rfl⟩ : syracuseStep 1343441 = 1007581) B1007581
theorem B1343459 : Blo 892572 1343459 := bstep (se 1 (by rfl) ⟨1007594, by rfl⟩ : syracuseStep 1343459 = 2015189) B2015189
theorem B1507315 : Blo 892572 1507315 := bstep (se 1 (by rfl) ⟨1130486, by rfl⟩ : syracuseStep 1507315 = 2260973) B2260973
theorem B6881285 : Blo 892572 6881285 := bstep (se 4 (by rfl) ⟨645120, by rfl⟩ : syracuseStep 6881285 = 1290241) B1290241
theorem B3670039 : Blo 892572 3670039 := bstep (se 1 (by rfl) ⟨2752529, by rfl⟩ : syracuseStep 3670039 = 5505059) B5505059
theorem B1343513 : Blo 892572 1343513 := bstep (se 2 (by rfl) ⟨503817, by rfl⟩ : syracuseStep 1343513 = 1007635) B1007635
theorem B1507403 : Blo 892572 1507403 := bstep (se 1 (by rfl) ⟨1130552, by rfl⟩ : syracuseStep 1507403 = 2261105) B2261105
theorem B1343627 : Blo 892572 1343627 := bstep (se 1 (by rfl) ⟨1007720, by rfl⟩ : syracuseStep 1343627 = 2015441) B2015441
theorem B1343639 : Blo 892572 1343639 := bstep (se 1 (by rfl) ⟨1007729, by rfl⟩ : syracuseStep 1343639 = 2015459) B2015459
theorem B3440819 : Blo 892572 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B1507531 : Blo 892572 1507531 := bstep (se 1 (by rfl) ⟨1130648, by rfl⟩ : syracuseStep 1507531 = 2261297) B2261297
theorem B3014873 : Blo 892572 3014873 := bstep (se 2 (by rfl) ⟨1130577, by rfl⟩ : syracuseStep 3014873 = 2261155) B2261155
theorem B1343705 : Blo 892572 1343705 := bstep (se 2 (by rfl) ⟨503889, by rfl⟩ : syracuseStep 1343705 = 1007779) B1007779
theorem B1343819 : Blo 892572 1343819 := bstep (se 1 (by rfl) ⟨1007864, by rfl⟩ : syracuseStep 1343819 = 2015729) B2015729
theorem B1343831 : Blo 892572 1343831 := bstep (se 1 (by rfl) ⟨1007873, by rfl⟩ : syracuseStep 1343831 = 2015747) B2015747
theorem B1507673 : Blo 892572 1507673 := bstep (se 2 (by rfl) ⟨565377, by rfl⟩ : syracuseStep 1507673 = 1130755) B1130755
theorem B4522391 : Blo 892572 4522391 := bstep (se 1 (by rfl) ⟨3391793, by rfl⟩ : syracuseStep 4522391 = 6783587) B6783587
theorem B1343897 : Blo 892572 1343897 := bstep (se 2 (by rfl) ⟨503961, by rfl⟩ : syracuseStep 1343897 = 1007923) B1007923
theorem B1507801 : Blo 892572 1507801 := bstep (se 2 (by rfl) ⟨565425, by rfl⟩ : syracuseStep 1507801 = 1130851) B1130851
theorem B1344011 : Blo 892572 1344011 := bstep (se 1 (by rfl) ⟨1008008, by rfl⟩ : syracuseStep 1344011 = 2016017) B2016017
theorem B1344023 : Blo 892572 1344023 := bstep (se 1 (by rfl) ⟨1008017, by rfl⟩ : syracuseStep 1344023 = 2016035) B2016035
theorem B2720321 : Blo 892572 2720321 := bstep (se 2 (by rfl) ⟨1020120, by rfl⟩ : syracuseStep 2720321 = 2040241) B2040241
theorem B1344089 : Blo 892572 1344089 := bstep (se 2 (by rfl) ⟨504033, by rfl⟩ : syracuseStep 1344089 = 1008067) B1008067
theorem B1344203 : Blo 892572 1344203 := bstep (se 1 (by rfl) ⟨1008152, by rfl⟩ : syracuseStep 1344203 = 2016305) B2016305
theorem B1344215 : Blo 892572 1344215 := bstep (se 1 (by rfl) ⟨1008161, by rfl⟩ : syracuseStep 1344215 = 2016323) B2016323
theorem B2261783 : Blo 892572 2261783 := bstep (se 1 (by rfl) ⟨1696337, by rfl⟩ : syracuseStep 2261783 = 3392675) B3392675
theorem B1344281 : Blo 892572 1344281 := bstep (se 2 (by rfl) ⟨504105, by rfl⟩ : syracuseStep 1344281 = 1008211) B1008211
theorem B1344395 : Blo 892572 1344395 := bstep (se 1 (by rfl) ⟨1008296, by rfl⟩ : syracuseStep 1344395 = 2016593) B2016593
theorem B3015575 : Blo 892572 3015575 := bstep (se 1 (by rfl) ⟨2261681, by rfl⟩ : syracuseStep 3015575 = 4523363) B4523363
theorem B1344407 : Blo 892572 1344407 := bstep (se 1 (by rfl) ⟨1008305, by rfl⟩ : syracuseStep 1344407 = 2016611) B2016611
theorem B1344473 : Blo 892572 1344473 := bstep (se 2 (by rfl) ⟨504177, by rfl⟩ : syracuseStep 1344473 = 1008355) B1008355
theorem B3441629 : Blo 892572 3441629 := bstep (se 3 (by rfl) ⟨645305, by rfl⟩ : syracuseStep 3441629 = 1290611) B1290611
theorem B1508375 : Blo 892572 1508375 := bstep (se 1 (by rfl) ⟨1131281, by rfl⟩ : syracuseStep 1508375 = 2262563) B2262563
theorem B1344587 : Blo 892572 1344587 := bstep (se 1 (by rfl) ⟨1008440, by rfl⟩ : syracuseStep 1344587 = 2016881) B2016881
theorem B1344599 : Blo 892572 1344599 := bstep (se 1 (by rfl) ⟨1008449, by rfl⟩ : syracuseStep 1344599 = 2016899) B2016899
theorem B1508503 : Blo 892572 1508503 := bstep (se 1 (by rfl) ⟨1131377, by rfl⟩ : syracuseStep 1508503 = 2262755) B2262755
theorem B1344665 : Blo 892572 1344665 := bstep (se 2 (by rfl) ⟨504249, by rfl⟩ : syracuseStep 1344665 = 1008499) B1008499
theorem B6980825 : Blo 892572 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B1344779 : Blo 892572 1344779 := bstep (se 1 (by rfl) ⟨1008584, by rfl⟩ : syracuseStep 1344779 = 2017169) B2017169
theorem B1344791 : Blo 892572 1344791 := bstep (se 1 (by rfl) ⟨1008593, by rfl⟩ : syracuseStep 1344791 = 2017187) B2017187
theorem B1344857 : Blo 892572 1344857 := bstep (se 2 (by rfl) ⟨504321, by rfl⟩ : syracuseStep 1344857 = 1008643) B1008643
theorem B3016115 : Blo 892572 3016115 := bstep (se 1 (by rfl) ⟨2262086, by rfl⟩ : syracuseStep 3016115 = 4524173) B4524173
theorem B2262451 : Blo 892572 2262451 := bstep (se 1 (by rfl) ⟨1696838, by rfl⟩ : syracuseStep 2262451 = 3393677) B3393677
theorem B2262593 : Blo 892572 2262593 := bstep (se 2 (by rfl) ⟨848472, by rfl⟩ : syracuseStep 2262593 = 1696945) B1696945
theorem B1050199 : Blo 892572 1050199 := bstep (se 1 (by rfl) ⟨787649, by rfl⟩ : syracuseStep 1050199 = 1575299) B1575299
theorem B3868249 : Blo 892572 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B3016385 : Blo 892572 3016385 := bstep (se 2 (by rfl) ⟨1131144, by rfl⟩ : syracuseStep 3016385 = 2262289) B2262289
theorem B7243481 : Blo 892572 7243481 := bstep (se 2 (by rfl) ⟨2716305, by rfl⟩ : syracuseStep 7243481 = 5432611) B5432611
theorem B1509131 : Blo 892572 1509131 := bstep (se 1 (by rfl) ⟨1131848, by rfl⟩ : syracuseStep 1509131 = 2263697) B2263697
theorem B1509259 : Blo 892572 1509259 := bstep (se 1 (by rfl) ⟨1131944, by rfl⟩ : syracuseStep 1509259 = 2263889) B2263889
theorem B15304625 : Blo 892572 15304625 := bstep (se 2 (by rfl) ⟨5739234, by rfl⟩ : syracuseStep 15304625 = 11478469) B11478469
theorem B1509401 : Blo 892572 1509401 := bstep (se 2 (by rfl) ⟨566025, by rfl⟩ : syracuseStep 1509401 = 1132051) B1132051
theorem B12257315 : Blo 892572 12257315 := bstep (se 1 (by rfl) ⟨9192986, by rfl⟩ : syracuseStep 12257315 = 18385973) B18385973
theorem B4294721 : Blo 892572 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B1509529 : Blo 892572 1509529 := bstep (se 2 (by rfl) ⟨566073, by rfl⟩ : syracuseStep 1509529 = 1132147) B1132147
theorem B3016925 : Blo 892572 3016925 := bstep (se 3 (by rfl) ⟨565673, by rfl⟩ : syracuseStep 3016925 = 1131347) B1131347
theorem B1510103 : Blo 892572 1510103 := bstep (se 1 (by rfl) ⟨1132577, by rfl⟩ : syracuseStep 1510103 = 2265155) B2265155
theorem B2263859 : Blo 892572 2263859 := bstep (se 1 (by rfl) ⟨1697894, by rfl⟩ : syracuseStep 2263859 = 3395789) B3395789
theorem B1510231 : Blo 892572 1510231 := bstep (se 1 (by rfl) ⟨1132673, by rfl⟩ : syracuseStep 1510231 = 2265347) B2265347
theorem B100797401 : Blo 892572 100797401 := bstep (se 2 (by rfl) ⟨37799025, by rfl⟩ : syracuseStep 100797401 = 75598051) B75598051
theorem B953515 : Blo 892572 953515 := bstep (se 1 (by rfl) ⟨715136, by rfl⟩ : syracuseStep 953515 = 1430273) B1430273
theorem B46402741 : Blo 892572 46402741 := bstep (se 5 (by rfl) ⟨2175128, by rfl⟩ : syracuseStep 46402741 = 4350257) B4350257
theorem B3018059 : Blo 892572 3018059 := bstep (se 1 (by rfl) ⟨2263544, by rfl⟩ : syracuseStep 3018059 = 4527089) B4527089
theorem B2264395 : Blo 892572 2264395 := bstep (se 1 (by rfl) ⟨1698296, by rfl⟩ : syracuseStep 2264395 = 3396593) B3396593
theorem B6458717 : Blo 892572 6458717 := bstep (se 3 (by rfl) ⟨1211009, by rfl⟩ : syracuseStep 6458717 = 2422019) B2422019
theorem B1510859 : Blo 892572 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B2264537 : Blo 892572 2264537 := bstep (se 2 (by rfl) ⟨849201, by rfl⟩ : syracuseStep 2264537 = 1698403) B1698403
theorem B1609217 : Blo 892572 1609217 := bstep (se 2 (by rfl) ⟨603456, by rfl⟩ : syracuseStep 1609217 = 1206913) B1206913
theorem B921143 : Blo 892572 921143 := bstep (se 1 (by rfl) ⟨690857, by rfl⟩ : syracuseStep 921143 = 1381715) B1381715
theorem B1510987 : Blo 892572 1510987 := bstep (se 1 (by rfl) ⟨1133240, by rfl⟩ : syracuseStep 1510987 = 2266481) B2266481
theorem B3018329 : Blo 892572 3018329 := bstep (se 2 (by rfl) ⟨1131873, by rfl⟩ : syracuseStep 3018329 = 2263747) B2263747
theorem B2723507 : Blo 892572 2723507 := bstep (se 1 (by rfl) ⟨2042630, by rfl⟩ : syracuseStep 2723507 = 4085261) B4085261
theorem B1511129 : Blo 892572 1511129 := bstep (se 2 (by rfl) ⟨566673, by rfl⟩ : syracuseStep 1511129 = 1133347) B1133347
theorem B1511257 : Blo 892572 1511257 := bstep (se 2 (by rfl) ⟨566721, by rfl⟩ : syracuseStep 1511257 = 1133443) B1133443
theorem B4525955 : Blo 892572 4525955 := bstep (se 1 (by rfl) ⟨3394466, by rfl⟩ : syracuseStep 4525955 = 6788933) B6788933
theorem B5738597 : Blo 892572 5738597 := bstep (se 4 (by rfl) ⟨537993, by rfl⟩ : syracuseStep 5738597 = 1075987) B1075987
theorem B3019031 : Blo 892572 3019031 := bstep (se 1 (by rfl) ⟨2264273, by rfl⟩ : syracuseStep 3019031 = 4528547) B4528547
theorem B2265367 : Blo 892572 2265367 := bstep (se 1 (by rfl) ⟨1699025, by rfl⟩ : syracuseStep 2265367 = 3398051) B3398051
theorem B2756915 : Blo 892572 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B1511831 : Blo 892572 1511831 := bstep (se 1 (by rfl) ⟨1133873, by rfl⟩ : syracuseStep 1511831 = 2267747) B2267747
theorem B1511959 : Blo 892572 1511959 := bstep (se 1 (by rfl) ⟨1133969, by rfl⟩ : syracuseStep 1511959 = 2267939) B2267939
theorem B5739083 : Blo 892572 5739083 := bstep (se 1 (by rfl) ⟨4304312, by rfl⟩ : syracuseStep 5739083 = 8608625) B8608625
theorem B2265803 : Blo 892572 2265803 := bstep (se 1 (by rfl) ⟨1699352, by rfl⟩ : syracuseStep 2265803 = 3398705) B3398705
theorem B955147 : Blo 892572 955147 := bstep (se 1 (by rfl) ⟨716360, by rfl⟩ : syracuseStep 955147 = 1432721) B1432721
theorem B3019571 : Blo 892572 3019571 := bstep (se 1 (by rfl) ⟨2264678, by rfl⟩ : syracuseStep 3019571 = 4529357) B4529357
theorem B7640081 : Blo 892572 7640081 := bstep (se 2 (by rfl) ⟨2865030, by rfl⟩ : syracuseStep 7640081 = 5730061) B5730061
theorem B3019841 : Blo 892572 3019841 := bstep (se 2 (by rfl) ⟨1132440, by rfl⟩ : syracuseStep 3019841 = 2264881) B2264881
theorem B2266177 : Blo 892572 2266177 := bstep (se 2 (by rfl) ⟨849816, by rfl⟩ : syracuseStep 2266177 = 1699633) B1699633
theorem B1512587 : Blo 892572 1512587 := bstep (se 1 (by rfl) ⟨1134440, by rfl⟩ : syracuseStep 1512587 = 2268881) B2268881
theorem B1610903 : Blo 892572 1610903 := bstep (se 1 (by rfl) ⟨1208177, by rfl⟩ : syracuseStep 1610903 = 2416355) B2416355
theorem B2069761 : Blo 892572 2069761 := bstep (se 2 (by rfl) ⟨776160, by rfl⟩ : syracuseStep 2069761 = 1552321) B1552321
theorem B1512715 : Blo 892572 1512715 := bstep (se 1 (by rfl) ⟨1134536, by rfl⟩ : syracuseStep 1512715 = 2269073) B2269073
theorem B1512857 : Blo 892572 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B3020381 : Blo 892572 3020381 := bstep (se 3 (by rfl) ⟨566321, by rfl⟩ : syracuseStep 3020381 = 1132643) B1132643
theorem B2266775 : Blo 892572 2266775 := bstep (se 1 (by rfl) ⟨1700081, by rfl⟩ : syracuseStep 2266775 = 3400163) B3400163
theorem B956215 : Blo 892572 956215 := bstep (se 1 (by rfl) ⟨717161, by rfl⟩ : syracuseStep 956215 = 1434323) B1434323
theorem B22911011 : Blo 892572 22911011 := bstep (se 1 (by rfl) ⟨17183258, by rfl⟩ : syracuseStep 22911011 = 34366517) B34366517
theorem B2038105 : Blo 892572 2038105 := bstep (se 2 (by rfl) ⟨764289, by rfl⟩ : syracuseStep 2038105 = 1528579) B1528579
theorem B1743193 : Blo 892572 1743193 := bstep (se 2 (by rfl) ⟨653697, by rfl⟩ : syracuseStep 1743193 = 1307395) B1307395
theorem B2267585 : Blo 892572 2267585 := bstep (se 2 (by rfl) ⟨850344, by rfl⟩ : syracuseStep 2267585 = 1700689) B1700689
theorem B1907201 : Blo 892572 1907201 := bstep (se 2 (by rfl) ⟨715200, by rfl⟩ : syracuseStep 1907201 = 1430401) B1430401
theorem B957035 : Blo 892572 957035 := bstep (se 1 (by rfl) ⟨717776, by rfl⟩ : syracuseStep 957035 = 1435553) B1435553
theorem B3021515 : Blo 892572 3021515 := bstep (se 1 (by rfl) ⟨2266136, by rfl⟩ : syracuseStep 3021515 = 4532273) B4532273
theorem B6789905 : Blo 892572 6789905 := bstep (se 2 (by rfl) ⟨2546214, by rfl⟩ : syracuseStep 6789905 = 5092429) B5092429
theorem B1612619 : Blo 892572 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B1907543 : Blo 892572 1907543 := bstep (se 1 (by rfl) ⟨1430657, by rfl⟩ : syracuseStep 1907543 = 2861315) B2861315
theorem B3021785 : Blo 892572 3021785 := bstep (se 2 (by rfl) ⟨1133169, by rfl⟩ : syracuseStep 3021785 = 2266339) B2266339
theorem B2268121 : Blo 892572 2268121 := bstep (se 2 (by rfl) ⟨850545, by rfl⟩ : syracuseStep 2268121 = 1701091) B1701091
theorem B1908107 : Blo 892572 1908107 := bstep (se 1 (by rfl) ⟨1431080, by rfl⟩ : syracuseStep 1908107 = 2862161) B2862161
theorem B4529681 : Blo 892572 4529681 := bstep (se 2 (by rfl) ⟨1698630, by rfl⟩ : syracuseStep 4529681 = 3397261) B3397261
theorem B5086871 : Blo 892572 5086871 := bstep (se 1 (by rfl) ⟨3815153, by rfl⟩ : syracuseStep 5086871 = 7630307) B7630307
theorem B3022487 : Blo 892572 3022487 := bstep (se 1 (by rfl) ⟨2266865, by rfl⟩ : syracuseStep 3022487 = 4533731) B4533731
theorem B892587 : Blo 892572 892587 := bstep (se 1 (by rfl) ⟨669440, by rfl⟩ : syracuseStep 892587 = 1338881) B1338881
theorem B4529843 : Blo 892572 4529843 := bstep (se 1 (by rfl) ⟨3397382, by rfl⟩ : syracuseStep 4529843 = 6794765) B6794765
theorem B892599 : Blo 892572 892599 := bstep (se 1 (by rfl) ⟨669449, by rfl⟩ : syracuseStep 892599 = 1338899) B1338899
theorem B892619 : Blo 892572 892619 := bstep (se 1 (by rfl) ⟨669464, by rfl⟩ : syracuseStep 892619 = 1338929) B1338929
theorem B892631 : Blo 892572 892631 := bstep (se 1 (by rfl) ⟨669473, by rfl⟩ : syracuseStep 892631 = 1338947) B1338947
theorem B892651 : Blo 892572 892651 := bstep (se 1 (by rfl) ⟨669488, by rfl⟩ : syracuseStep 892651 = 1338977) B1338977
theorem B892663 : Blo 892572 892663 := bstep (se 1 (by rfl) ⟨669497, by rfl⟩ : syracuseStep 892663 = 1338995) B1338995
theorem B892683 : Blo 892572 892683 := bstep (se 1 (by rfl) ⟨669512, by rfl⟩ : syracuseStep 892683 = 1339025) B1339025
theorem B892695 : Blo 892572 892695 := bstep (se 1 (by rfl) ⟨669521, by rfl⟩ : syracuseStep 892695 = 1339043) B1339043
theorem B892715 : Blo 892572 892715 := bstep (se 1 (by rfl) ⟨669536, by rfl⟩ : syracuseStep 892715 = 1339073) B1339073
theorem B892727 : Blo 892572 892727 := bstep (se 1 (by rfl) ⟨669545, by rfl⟩ : syracuseStep 892727 = 1339091) B1339091
theorem B892747 : Blo 892572 892747 := bstep (se 1 (by rfl) ⟨669560, by rfl⟩ : syracuseStep 892747 = 1339121) B1339121
theorem B892759 : Blo 892572 892759 := bstep (se 1 (by rfl) ⟨669569, by rfl⟩ : syracuseStep 892759 = 1339139) B1339139
theorem B1613657 : Blo 892572 1613657 := bstep (se 2 (by rfl) ⟨605121, by rfl⟩ : syracuseStep 1613657 = 1210243) B1210243
theorem B892779 : Blo 892572 892779 := bstep (se 1 (by rfl) ⟨669584, by rfl⟩ : syracuseStep 892779 = 1339169) B1339169
theorem B892791 : Blo 892572 892791 := bstep (se 1 (by rfl) ⟨669593, by rfl⟩ : syracuseStep 892791 = 1339187) B1339187
theorem B892811 : Blo 892572 892811 := bstep (se 1 (by rfl) ⟨669608, by rfl⟩ : syracuseStep 892811 = 1339217) B1339217
theorem B892823 : Blo 892572 892823 := bstep (se 1 (by rfl) ⟨669617, by rfl⟩ : syracuseStep 892823 = 1339235) B1339235
theorem B892843 : Blo 892572 892843 := bstep (se 1 (by rfl) ⟨669632, by rfl⟩ : syracuseStep 892843 = 1339265) B1339265
theorem B5742515 : Blo 892572 5742515 := bstep (se 1 (by rfl) ⟨4306886, by rfl⟩ : syracuseStep 5742515 = 8613773) B8613773
theorem B892855 : Blo 892572 892855 := bstep (se 1 (by rfl) ⟨669641, by rfl⟩ : syracuseStep 892855 = 1339283) B1339283
theorem B892875 : Blo 892572 892875 := bstep (se 1 (by rfl) ⟨669656, by rfl⟩ : syracuseStep 892875 = 1339313) B1339313
theorem B892887 : Blo 892572 892887 := bstep (se 1 (by rfl) ⟨669665, by rfl⟩ : syracuseStep 892887 = 1339331) B1339331
theorem B1908697 : Blo 892572 1908697 := bstep (se 2 (by rfl) ⟨715761, by rfl⟩ : syracuseStep 1908697 = 1431523) B1431523
theorem B2072537 : Blo 892572 2072537 := bstep (se 2 (by rfl) ⟨777201, by rfl⟩ : syracuseStep 2072537 = 1554403) B1554403
theorem B892907 : Blo 892572 892907 := bstep (se 1 (by rfl) ⟨669680, by rfl⟩ : syracuseStep 892907 = 1339361) B1339361
theorem B892919 : Blo 892572 892919 := bstep (se 1 (by rfl) ⟨669689, by rfl⟩ : syracuseStep 892919 = 1339379) B1339379
theorem B892939 : Blo 892572 892939 := bstep (se 1 (by rfl) ⟨669704, by rfl⟩ : syracuseStep 892939 = 1339409) B1339409
theorem B892951 : Blo 892572 892951 := bstep (se 1 (by rfl) ⟨669713, by rfl⟩ : syracuseStep 892951 = 1339427) B1339427
theorem B892971 : Blo 892572 892971 := bstep (se 1 (by rfl) ⟨669728, by rfl⟩ : syracuseStep 892971 = 1339457) B1339457
theorem B2269235 : Blo 892572 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B892983 : Blo 892572 892983 := bstep (se 1 (by rfl) ⟨669737, by rfl⟩ : syracuseStep 892983 = 1339475) B1339475
theorem B893003 : Blo 892572 893003 := bstep (se 1 (by rfl) ⟨669752, by rfl⟩ : syracuseStep 893003 = 1339505) B1339505
theorem B893015 : Blo 892572 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B893035 : Blo 892572 893035 := bstep (se 1 (by rfl) ⟨669776, by rfl⟩ : syracuseStep 893035 = 1339553) B1339553
theorem B893047 : Blo 892572 893047 := bstep (se 1 (by rfl) ⟨669785, by rfl⟩ : syracuseStep 893047 = 1339571) B1339571
theorem B893067 : Blo 892572 893067 := bstep (se 1 (by rfl) ⟨669800, by rfl⟩ : syracuseStep 893067 = 1339601) B1339601
theorem B893079 : Blo 892572 893079 := bstep (se 1 (by rfl) ⟨669809, by rfl⟩ : syracuseStep 893079 = 1339619) B1339619
theorem B893099 : Blo 892572 893099 := bstep (se 1 (by rfl) ⟨669824, by rfl⟩ : syracuseStep 893099 = 1339649) B1339649
theorem B3023027 : Blo 892572 3023027 := bstep (se 1 (by rfl) ⟨2267270, by rfl⟩ : syracuseStep 3023027 = 4534541) B4534541
theorem B893111 : Blo 892572 893111 := bstep (se 1 (by rfl) ⟨669833, by rfl⟩ : syracuseStep 893111 = 1339667) B1339667
theorem B893131 : Blo 892572 893131 := bstep (se 1 (by rfl) ⟨669848, by rfl⟩ : syracuseStep 893131 = 1339697) B1339697
theorem B3219659 : Blo 892572 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B893143 : Blo 892572 893143 := bstep (se 1 (by rfl) ⟨669857, by rfl⟩ : syracuseStep 893143 = 1339715) B1339715
theorem B3875033 : Blo 892572 3875033 := bstep (se 2 (by rfl) ⟨1453137, by rfl⟩ : syracuseStep 3875033 = 2906275) B2906275
theorem B893163 : Blo 892572 893163 := bstep (se 1 (by rfl) ⟨669872, by rfl⟩ : syracuseStep 893163 = 1339745) B1339745
theorem B893175 : Blo 892572 893175 := bstep (se 1 (by rfl) ⟨669881, by rfl⟩ : syracuseStep 893175 = 1339763) B1339763
theorem B893195 : Blo 892572 893195 := bstep (se 1 (by rfl) ⟨669896, by rfl⟩ : syracuseStep 893195 = 1339793) B1339793
theorem B893207 : Blo 892572 893207 := bstep (se 1 (by rfl) ⟨669905, by rfl⟩ : syracuseStep 893207 = 1339811) B1339811
theorem B893227 : Blo 892572 893227 := bstep (se 1 (by rfl) ⟨669920, by rfl⟩ : syracuseStep 893227 = 1339841) B1339841
theorem B15278381 : Blo 892572 15278381 := bstep (se 3 (by rfl) ⟨2864696, by rfl⟩ : syracuseStep 15278381 = 5729393) B5729393
theorem B893239 : Blo 892572 893239 := bstep (se 1 (by rfl) ⟨669929, by rfl⟩ : syracuseStep 893239 = 1339859) B1339859
theorem B893259 : Blo 892572 893259 := bstep (se 1 (by rfl) ⟨669944, by rfl⟩ : syracuseStep 893259 = 1339889) B1339889
theorem B893271 : Blo 892572 893271 := bstep (se 1 (by rfl) ⟨669953, by rfl⟩ : syracuseStep 893271 = 1339907) B1339907
theorem B893291 : Blo 892572 893291 := bstep (se 1 (by rfl) ⟨669968, by rfl⟩ : syracuseStep 893291 = 1339937) B1339937
theorem B893303 : Blo 892572 893303 := bstep (se 1 (by rfl) ⟨669977, by rfl⟩ : syracuseStep 893303 = 1339955) B1339955
theorem B893323 : Blo 892572 893323 := bstep (se 1 (by rfl) ⟨669992, by rfl⟩ : syracuseStep 893323 = 1339985) B1339985
theorem B893335 : Blo 892572 893335 := bstep (se 1 (by rfl) ⟨670001, by rfl⟩ : syracuseStep 893335 = 1340003) B1340003
theorem B893355 : Blo 892572 893355 := bstep (se 1 (by rfl) ⟨670016, by rfl⟩ : syracuseStep 893355 = 1340033) B1340033
theorem B893367 : Blo 892572 893367 := bstep (se 1 (by rfl) ⟨670025, by rfl⟩ : syracuseStep 893367 = 1340051) B1340051
theorem B3023297 : Blo 892572 3023297 := bstep (se 2 (by rfl) ⟨1133736, by rfl⟩ : syracuseStep 3023297 = 2267473) B2267473
theorem B893387 : Blo 892572 893387 := bstep (se 1 (by rfl) ⟨670040, by rfl⟩ : syracuseStep 893387 = 1340081) B1340081
theorem B893399 : Blo 892572 893399 := bstep (se 1 (by rfl) ⟨670049, by rfl⟩ : syracuseStep 893399 = 1340099) B1340099
theorem B893419 : Blo 892572 893419 := bstep (se 1 (by rfl) ⟨670064, by rfl⟩ : syracuseStep 893419 = 1340129) B1340129
theorem B893431 : Blo 892572 893431 := bstep (se 1 (by rfl) ⟨670073, by rfl⟩ : syracuseStep 893431 = 1340147) B1340147
theorem B893451 : Blo 892572 893451 := bstep (se 1 (by rfl) ⟨670088, by rfl⟩ : syracuseStep 893451 = 1340177) B1340177
theorem B893463 : Blo 892572 893463 := bstep (se 1 (by rfl) ⟨670097, by rfl⟩ : syracuseStep 893463 = 1340195) B1340195
theorem B893483 : Blo 892572 893483 := bstep (se 1 (by rfl) ⟨670112, by rfl⟩ : syracuseStep 893483 = 1340225) B1340225
theorem B2859571 : Blo 892572 2859571 := bstep (se 1 (by rfl) ⟨2144678, by rfl⟩ : syracuseStep 2859571 = 4289357) B4289357
theorem B893495 : Blo 892572 893495 := bstep (se 1 (by rfl) ⟨670121, by rfl⟩ : syracuseStep 893495 = 1340243) B1340243
theorem B893515 : Blo 892572 893515 := bstep (se 1 (by rfl) ⟨670136, by rfl⟩ : syracuseStep 893515 = 1340273) B1340273
theorem B893527 : Blo 892572 893527 := bstep (se 1 (by rfl) ⟨670145, by rfl⟩ : syracuseStep 893527 = 1340291) B1340291
theorem B893547 : Blo 892572 893547 := bstep (se 1 (by rfl) ⟨670160, by rfl⟩ : syracuseStep 893547 = 1340321) B1340321
theorem B893559 : Blo 892572 893559 := bstep (se 1 (by rfl) ⟨670169, by rfl⟩ : syracuseStep 893559 = 1340339) B1340339
theorem B893579 : Blo 892572 893579 := bstep (se 1 (by rfl) ⟨670184, by rfl⟩ : syracuseStep 893579 = 1340369) B1340369
theorem B893591 : Blo 892572 893591 := bstep (se 1 (by rfl) ⟨670193, by rfl⟩ : syracuseStep 893591 = 1340387) B1340387
theorem B893611 : Blo 892572 893611 := bstep (se 1 (by rfl) ⟨670208, by rfl⟩ : syracuseStep 893611 = 1340417) B1340417
theorem B893623 : Blo 892572 893623 := bstep (se 1 (by rfl) ⟨670217, by rfl⟩ : syracuseStep 893623 = 1340435) B1340435
theorem B893643 : Blo 892572 893643 := bstep (se 1 (by rfl) ⟨670232, by rfl⟩ : syracuseStep 893643 = 1340465) B1340465
theorem B893655 : Blo 892572 893655 := bstep (se 1 (by rfl) ⟨670241, by rfl⟩ : syracuseStep 893655 = 1340483) B1340483
theorem B893675 : Blo 892572 893675 := bstep (se 1 (by rfl) ⟨670256, by rfl⟩ : syracuseStep 893675 = 1340513) B1340513
theorem B893687 : Blo 892572 893687 := bstep (se 1 (by rfl) ⟨670265, by rfl⟩ : syracuseStep 893687 = 1340531) B1340531
theorem B1614593 : Blo 892572 1614593 := bstep (se 2 (by rfl) ⟨605472, by rfl⟩ : syracuseStep 1614593 = 1210945) B1210945
theorem B893707 : Blo 892572 893707 := bstep (se 1 (by rfl) ⟨670280, by rfl⟩ : syracuseStep 893707 = 1340561) B1340561
theorem B893719 : Blo 892572 893719 := bstep (se 1 (by rfl) ⟨670289, by rfl⟩ : syracuseStep 893719 = 1340579) B1340579
theorem B893739 : Blo 892572 893739 := bstep (se 1 (by rfl) ⟨670304, by rfl⟩ : syracuseStep 893739 = 1340609) B1340609
theorem B893751 : Blo 892572 893751 := bstep (se 1 (by rfl) ⟨670313, by rfl⟩ : syracuseStep 893751 = 1340627) B1340627
theorem B893771 : Blo 892572 893771 := bstep (se 1 (by rfl) ⟨670328, by rfl⟩ : syracuseStep 893771 = 1340657) B1340657
theorem B893783 : Blo 892572 893783 := bstep (se 1 (by rfl) ⟨670337, by rfl⟩ : syracuseStep 893783 = 1340675) B1340675
theorem B893803 : Blo 892572 893803 := bstep (se 1 (by rfl) ⟨670352, by rfl⟩ : syracuseStep 893803 = 1340705) B1340705
theorem B893815 : Blo 892572 893815 := bstep (se 1 (by rfl) ⟨670361, by rfl⟩ : syracuseStep 893815 = 1340723) B1340723
theorem B893835 : Blo 892572 893835 := bstep (se 1 (by rfl) ⟨670376, by rfl⟩ : syracuseStep 893835 = 1340753) B1340753
theorem B893847 : Blo 892572 893847 := bstep (se 1 (by rfl) ⟨670385, by rfl⟩ : syracuseStep 893847 = 1340771) B1340771
theorem B893867 : Blo 892572 893867 := bstep (se 1 (by rfl) ⟨670400, by rfl⟩ : syracuseStep 893867 = 1340801) B1340801
theorem B893879 : Blo 892572 893879 := bstep (se 1 (by rfl) ⟨670409, by rfl⟩ : syracuseStep 893879 = 1340819) B1340819
theorem B893899 : Blo 892572 893899 := bstep (se 1 (by rfl) ⟨670424, by rfl⟩ : syracuseStep 893899 = 1340849) B1340849
theorem B3449803 : Blo 892572 3449803 := bstep (se 1 (by rfl) ⟨2587352, by rfl⟩ : syracuseStep 3449803 = 5174705) B5174705
theorem B893911 : Blo 892572 893911 := bstep (se 1 (by rfl) ⟨670433, by rfl⟩ : syracuseStep 893911 = 1340867) B1340867
theorem B3023837 : Blo 892572 3023837 := bstep (se 3 (by rfl) ⟨566969, by rfl⟩ : syracuseStep 3023837 = 1133939) B1133939
theorem B893931 : Blo 892572 893931 := bstep (se 1 (by rfl) ⟨670448, by rfl⟩ : syracuseStep 893931 = 1340897) B1340897
theorem B1909747 : Blo 892572 1909747 := bstep (se 1 (by rfl) ⟨1432310, by rfl⟩ : syracuseStep 1909747 = 2864621) B2864621
theorem B893943 : Blo 892572 893943 := bstep (se 1 (by rfl) ⟨670457, by rfl⟩ : syracuseStep 893943 = 1340915) B1340915
theorem B893963 : Blo 892572 893963 := bstep (se 1 (by rfl) ⟨670472, by rfl⟩ : syracuseStep 893963 = 1340945) B1340945
theorem B893975 : Blo 892572 893975 := bstep (se 1 (by rfl) ⟨670481, by rfl⟩ : syracuseStep 893975 = 1340963) B1340963
theorem B893995 : Blo 892572 893995 := bstep (se 1 (by rfl) ⟨670496, by rfl⟩ : syracuseStep 893995 = 1340993) B1340993
theorem B894007 : Blo 892572 894007 := bstep (se 1 (by rfl) ⟨670505, by rfl⟩ : syracuseStep 894007 = 1341011) B1341011
theorem B894027 : Blo 892572 894027 := bstep (se 1 (by rfl) ⟨670520, by rfl⟩ : syracuseStep 894027 = 1341041) B1341041
theorem B894039 : Blo 892572 894039 := bstep (se 1 (by rfl) ⟨670529, by rfl⟩ : syracuseStep 894039 = 1341059) B1341059
theorem B894059 : Blo 892572 894059 := bstep (se 1 (by rfl) ⟨670544, by rfl⟩ : syracuseStep 894059 = 1341089) B1341089
theorem B894071 : Blo 892572 894071 := bstep (se 1 (by rfl) ⟨670553, by rfl⟩ : syracuseStep 894071 = 1341107) B1341107
theorem B1811585 : Blo 892572 1811585 := bstep (se 2 (by rfl) ⟨679344, by rfl⟩ : syracuseStep 1811585 = 1358689) B1358689
theorem B894091 : Blo 892572 894091 := bstep (se 1 (by rfl) ⟨670568, by rfl⟩ : syracuseStep 894091 = 1341137) B1341137
theorem B26190989 : Blo 892572 26190989 := bstep (se 3 (by rfl) ⟨4910810, by rfl⟩ : syracuseStep 26190989 = 9821621) B9821621
theorem B894103 : Blo 892572 894103 := bstep (se 1 (by rfl) ⟨670577, by rfl⟩ : syracuseStep 894103 = 1341155) B1341155
theorem B894123 : Blo 892572 894123 := bstep (se 1 (by rfl) ⟨670592, by rfl⟩ : syracuseStep 894123 = 1341185) B1341185
theorem B894135 : Blo 892572 894135 := bstep (se 1 (by rfl) ⟨670601, by rfl⟩ : syracuseStep 894135 = 1341203) B1341203
theorem B894155 : Blo 892572 894155 := bstep (se 1 (by rfl) ⟨670616, by rfl⟩ : syracuseStep 894155 = 1341233) B1341233
theorem B894167 : Blo 892572 894167 := bstep (se 1 (by rfl) ⟨670625, by rfl⟩ : syracuseStep 894167 = 1341251) B1341251
theorem B894187 : Blo 892572 894187 := bstep (se 1 (by rfl) ⟨670640, by rfl⟩ : syracuseStep 894187 = 1341281) B1341281
theorem B894199 : Blo 892572 894199 := bstep (se 1 (by rfl) ⟨670649, by rfl⟩ : syracuseStep 894199 = 1341299) B1341299
theorem B2008331 : Blo 892572 2008331 := bstep (se 1 (by rfl) ⟨1506248, by rfl⟩ : syracuseStep 2008331 = 3012497) B3012497
theorem B894219 : Blo 892572 894219 := bstep (se 1 (by rfl) ⟨670664, by rfl⟩ : syracuseStep 894219 = 1341329) B1341329
theorem B894231 : Blo 892572 894231 := bstep (se 1 (by rfl) ⟨670673, by rfl⟩ : syracuseStep 894231 = 1341347) B1341347
theorem B894251 : Blo 892572 894251 := bstep (se 1 (by rfl) ⟨670688, by rfl⟩ : syracuseStep 894251 = 1341377) B1341377
theorem B894263 : Blo 892572 894263 := bstep (se 1 (by rfl) ⟨670697, by rfl⟩ : syracuseStep 894263 = 1341395) B1341395
theorem B2008385 : Blo 892572 2008385 := bstep (se 2 (by rfl) ⟨753144, by rfl⟩ : syracuseStep 2008385 = 1506289) B1506289
theorem B894283 : Blo 892572 894283 := bstep (se 1 (by rfl) ⟨670712, by rfl⟩ : syracuseStep 894283 = 1341425) B1341425
theorem B894295 : Blo 892572 894295 := bstep (se 1 (by rfl) ⟨670721, by rfl⟩ : syracuseStep 894295 = 1341443) B1341443
theorem B894315 : Blo 892572 894315 := bstep (se 1 (by rfl) ⟨670736, by rfl⟩ : syracuseStep 894315 = 1341473) B1341473
theorem B894327 : Blo 892572 894327 := bstep (se 1 (by rfl) ⟨670745, by rfl⟩ : syracuseStep 894327 = 1341491) B1341491
theorem B894347 : Blo 892572 894347 := bstep (se 1 (by rfl) ⟨670760, by rfl⟩ : syracuseStep 894347 = 1341521) B1341521
theorem B894359 : Blo 892572 894359 := bstep (se 1 (by rfl) ⟨670769, by rfl⟩ : syracuseStep 894359 = 1341539) B1341539
theorem B894379 : Blo 892572 894379 := bstep (se 1 (by rfl) ⟨670784, by rfl⟩ : syracuseStep 894379 = 1341569) B1341569
theorem B894391 : Blo 892572 894391 := bstep (se 1 (by rfl) ⟨670793, by rfl⟩ : syracuseStep 894391 = 1341587) B1341587
theorem B894411 : Blo 892572 894411 := bstep (se 1 (by rfl) ⟨670808, by rfl⟩ : syracuseStep 894411 = 1341617) B1341617
theorem B894423 : Blo 892572 894423 := bstep (se 1 (by rfl) ⟨670817, by rfl⟩ : syracuseStep 894423 = 1341635) B1341635
theorem B894443 : Blo 892572 894443 := bstep (se 1 (by rfl) ⟨670832, by rfl⟩ : syracuseStep 894443 = 1341665) B1341665
theorem B894455 : Blo 892572 894455 := bstep (se 1 (by rfl) ⟨670841, by rfl⟩ : syracuseStep 894455 = 1341683) B1341683
theorem B894475 : Blo 892572 894475 := bstep (se 1 (by rfl) ⟨670856, by rfl⟩ : syracuseStep 894475 = 1341713) B1341713
theorem B894487 : Blo 892572 894487 := bstep (se 1 (by rfl) ⟨670865, by rfl⟩ : syracuseStep 894487 = 1341731) B1341731
theorem B2008601 : Blo 892572 2008601 := bstep (se 2 (by rfl) ⟨753225, by rfl⟩ : syracuseStep 2008601 = 1506451) B1506451
theorem B894507 : Blo 892572 894507 := bstep (se 1 (by rfl) ⟨670880, by rfl⟩ : syracuseStep 894507 = 1341761) B1341761
theorem B894519 : Blo 892572 894519 := bstep (se 1 (by rfl) ⟨670889, by rfl⟩ : syracuseStep 894519 = 1341779) B1341779
theorem B894539 : Blo 892572 894539 := bstep (se 1 (by rfl) ⟨670904, by rfl⟩ : syracuseStep 894539 = 1341809) B1341809
theorem B4531787 : Blo 892572 4531787 := bstep (se 1 (by rfl) ⟨3398840, by rfl⟩ : syracuseStep 4531787 = 6797681) B6797681
theorem B894551 : Blo 892572 894551 := bstep (se 1 (by rfl) ⟨670913, by rfl⟩ : syracuseStep 894551 = 1341827) B1341827
theorem B894571 : Blo 892572 894571 := bstep (se 1 (by rfl) ⟨670928, by rfl⟩ : syracuseStep 894571 = 1341857) B1341857
theorem B2008691 : Blo 892572 2008691 := bstep (se 1 (by rfl) ⟨1506518, by rfl⟩ : syracuseStep 2008691 = 3013037) B3013037
theorem B894583 : Blo 892572 894583 := bstep (se 1 (by rfl) ⟨670937, by rfl⟩ : syracuseStep 894583 = 1341875) B1341875
theorem B4302467 : Blo 892572 4302467 := bstep (se 1 (by rfl) ⟨3226850, by rfl⟩ : syracuseStep 4302467 = 6453701) B6453701
theorem B894603 : Blo 892572 894603 := bstep (se 1 (by rfl) ⟨670952, by rfl⟩ : syracuseStep 894603 = 1341905) B1341905
theorem B2008727 : Blo 892572 2008727 := bstep (se 1 (by rfl) ⟨1506545, by rfl⟩ : syracuseStep 2008727 = 3013091) B3013091
theorem B894615 : Blo 892572 894615 := bstep (se 1 (by rfl) ⟨670961, by rfl⟩ : syracuseStep 894615 = 1341923) B1341923
theorem B894635 : Blo 892572 894635 := bstep (se 1 (by rfl) ⟨670976, by rfl⟩ : syracuseStep 894635 = 1341953) B1341953
theorem B3221171 : Blo 892572 3221171 := bstep (se 1 (by rfl) ⟨2415878, by rfl⟩ : syracuseStep 3221171 = 4831757) B4831757
theorem B894647 : Blo 892572 894647 := bstep (se 1 (by rfl) ⟨670985, by rfl⟩ : syracuseStep 894647 = 1341971) B1341971
theorem B894667 : Blo 892572 894667 := bstep (se 1 (by rfl) ⟨671000, by rfl⟩ : syracuseStep 894667 = 1342001) B1342001
theorem B894679 : Blo 892572 894679 := bstep (se 1 (by rfl) ⟨671009, by rfl⟩ : syracuseStep 894679 = 1342019) B1342019
theorem B894699 : Blo 892572 894699 := bstep (se 1 (by rfl) ⟨671024, by rfl⟩ : syracuseStep 894699 = 1342049) B1342049
theorem B894711 : Blo 892572 894711 := bstep (se 1 (by rfl) ⟨671033, by rfl⟩ : syracuseStep 894711 = 1342067) B1342067
theorem B894731 : Blo 892572 894731 := bstep (se 1 (by rfl) ⟨671048, by rfl⟩ : syracuseStep 894731 = 1342097) B1342097
theorem B894743 : Blo 892572 894743 := bstep (se 1 (by rfl) ⟨671057, by rfl⟩ : syracuseStep 894743 = 1342115) B1342115
theorem B894763 : Blo 892572 894763 := bstep (se 1 (by rfl) ⟨671072, by rfl⟩ : syracuseStep 894763 = 1342145) B1342145
theorem B894775 : Blo 892572 894775 := bstep (se 1 (by rfl) ⟨671081, by rfl⟩ : syracuseStep 894775 = 1342163) B1342163
theorem B2008907 : Blo 892572 2008907 := bstep (se 1 (by rfl) ⟨1506680, by rfl⟩ : syracuseStep 2008907 = 3013361) B3013361
theorem B894795 : Blo 892572 894795 := bstep (se 1 (by rfl) ⟨671096, by rfl⟩ : syracuseStep 894795 = 1342193) B1342193
theorem B894807 : Blo 892572 894807 := bstep (se 1 (by rfl) ⟨671105, by rfl⟩ : syracuseStep 894807 = 1342211) B1342211
theorem B12887909 : Blo 892572 12887909 := bstep (se 4 (by rfl) ⟨1208241, by rfl⟩ : syracuseStep 12887909 = 2416483) B2416483
theorem B894827 : Blo 892572 894827 := bstep (se 1 (by rfl) ⟨671120, by rfl⟩ : syracuseStep 894827 = 1342241) B1342241
theorem B894839 : Blo 892572 894839 := bstep (se 1 (by rfl) ⟨671129, by rfl⟩ : syracuseStep 894839 = 1342259) B1342259
theorem B2008961 : Blo 892572 2008961 := bstep (se 2 (by rfl) ⟨753360, by rfl⟩ : syracuseStep 2008961 = 1506721) B1506721
theorem B894859 : Blo 892572 894859 := bstep (se 1 (by rfl) ⟨671144, by rfl⟩ : syracuseStep 894859 = 1342289) B1342289
theorem B894871 : Blo 892572 894871 := bstep (se 1 (by rfl) ⟨671153, by rfl⟩ : syracuseStep 894871 = 1342307) B1342307
theorem B894891 : Blo 892572 894891 := bstep (se 1 (by rfl) ⟨671168, by rfl⟩ : syracuseStep 894891 = 1342337) B1342337
theorem B894903 : Blo 892572 894903 := bstep (se 1 (by rfl) ⟨671177, by rfl⟩ : syracuseStep 894903 = 1342355) B1342355
theorem B894923 : Blo 892572 894923 := bstep (se 1 (by rfl) ⟨671192, by rfl⟩ : syracuseStep 894923 = 1342385) B1342385
theorem B894935 : Blo 892572 894935 := bstep (se 1 (by rfl) ⟨671201, by rfl⟩ : syracuseStep 894935 = 1342403) B1342403
theorem B894955 : Blo 892572 894955 := bstep (se 1 (by rfl) ⟨671216, by rfl⟩ : syracuseStep 894955 = 1342433) B1342433
theorem B894967 : Blo 892572 894967 := bstep (se 1 (by rfl) ⟨671225, by rfl⟩ : syracuseStep 894967 = 1342451) B1342451
theorem B894987 : Blo 892572 894987 := bstep (se 1 (by rfl) ⟨671240, by rfl⟩ : syracuseStep 894987 = 1342481) B1342481
theorem B894999 : Blo 892572 894999 := bstep (se 1 (by rfl) ⟨671249, by rfl⟩ : syracuseStep 894999 = 1342499) B1342499
theorem B895019 : Blo 892572 895019 := bstep (se 1 (by rfl) ⟨671264, by rfl⟩ : syracuseStep 895019 = 1342529) B1342529
theorem B895031 : Blo 892572 895031 := bstep (se 1 (by rfl) ⟨671273, by rfl⟩ : syracuseStep 895031 = 1342547) B1342547
theorem B895051 : Blo 892572 895051 := bstep (se 1 (by rfl) ⟨671288, by rfl⟩ : syracuseStep 895051 = 1342577) B1342577
theorem B3024971 : Blo 892572 3024971 := bstep (se 1 (by rfl) ⟨2268728, by rfl⟩ : syracuseStep 3024971 = 4537457) B4537457
theorem B895063 : Blo 892572 895063 := bstep (se 1 (by rfl) ⟨671297, by rfl⟩ : syracuseStep 895063 = 1342595) B1342595
theorem B2009177 : Blo 892572 2009177 := bstep (se 2 (by rfl) ⟨753441, by rfl⟩ : syracuseStep 2009177 = 1506883) B1506883
theorem B895083 : Blo 892572 895083 := bstep (se 1 (by rfl) ⟨671312, by rfl⟩ : syracuseStep 895083 = 1342625) B1342625
theorem B895095 : Blo 892572 895095 := bstep (se 1 (by rfl) ⟨671321, by rfl⟩ : syracuseStep 895095 = 1342643) B1342643
theorem B895115 : Blo 892572 895115 := bstep (se 1 (by rfl) ⟨671336, by rfl⟩ : syracuseStep 895115 = 1342673) B1342673
theorem B895127 : Blo 892572 895127 := bstep (se 1 (by rfl) ⟨671345, by rfl⟩ : syracuseStep 895127 = 1342691) B1342691
theorem B895147 : Blo 892572 895147 := bstep (se 1 (by rfl) ⟨671360, by rfl⟩ : syracuseStep 895147 = 1342721) B1342721
theorem B2009267 : Blo 892572 2009267 := bstep (se 1 (by rfl) ⟨1506950, by rfl⟩ : syracuseStep 2009267 = 3013901) B3013901
theorem B895159 : Blo 892572 895159 := bstep (se 1 (by rfl) ⟨671369, by rfl⟩ : syracuseStep 895159 = 1342739) B1342739
theorem B895179 : Blo 892572 895179 := bstep (se 1 (by rfl) ⟨671384, by rfl⟩ : syracuseStep 895179 = 1342769) B1342769
theorem B2009303 : Blo 892572 2009303 := bstep (se 1 (by rfl) ⟨1506977, by rfl⟩ : syracuseStep 2009303 = 3013955) B3013955
theorem B895191 : Blo 892572 895191 := bstep (se 1 (by rfl) ⟨671393, by rfl⟩ : syracuseStep 895191 = 1342787) B1342787
theorem B895211 : Blo 892572 895211 := bstep (se 1 (by rfl) ⟨671408, by rfl⟩ : syracuseStep 895211 = 1342817) B1342817
theorem B895223 : Blo 892572 895223 := bstep (se 1 (by rfl) ⟨671417, by rfl⟩ : syracuseStep 895223 = 1342835) B1342835
theorem B895243 : Blo 892572 895243 := bstep (se 1 (by rfl) ⟨671432, by rfl⟩ : syracuseStep 895243 = 1342865) B1342865
theorem B895255 : Blo 892572 895255 := bstep (se 1 (by rfl) ⟨671441, by rfl⟩ : syracuseStep 895255 = 1342883) B1342883
theorem B895275 : Blo 892572 895275 := bstep (se 1 (by rfl) ⟨671456, by rfl⟩ : syracuseStep 895275 = 1342913) B1342913
theorem B895287 : Blo 892572 895287 := bstep (se 1 (by rfl) ⟨671465, by rfl⟩ : syracuseStep 895287 = 1342931) B1342931
theorem B895307 : Blo 892572 895307 := bstep (se 1 (by rfl) ⟨671480, by rfl⟩ : syracuseStep 895307 = 1342961) B1342961
theorem B895319 : Blo 892572 895319 := bstep (se 1 (by rfl) ⟨671489, by rfl⟩ : syracuseStep 895319 = 1342979) B1342979
theorem B3025241 : Blo 892572 3025241 := bstep (se 2 (by rfl) ⟨1134465, by rfl⟩ : syracuseStep 3025241 = 2268931) B2268931
theorem B895339 : Blo 892572 895339 := bstep (se 1 (by rfl) ⟨671504, by rfl⟩ : syracuseStep 895339 = 1343009) B1343009
theorem B895351 : Blo 892572 895351 := bstep (se 1 (by rfl) ⟨671513, by rfl⟩ : syracuseStep 895351 = 1343027) B1343027
theorem B2009483 : Blo 892572 2009483 := bstep (se 1 (by rfl) ⟨1507112, by rfl⟩ : syracuseStep 2009483 = 3014225) B3014225
theorem B895371 : Blo 892572 895371 := bstep (se 1 (by rfl) ⟨671528, by rfl⟩ : syracuseStep 895371 = 1343057) B1343057
theorem B895383 : Blo 892572 895383 := bstep (se 1 (by rfl) ⟨671537, by rfl⟩ : syracuseStep 895383 = 1343075) B1343075
theorem B895403 : Blo 892572 895403 := bstep (se 1 (by rfl) ⟨671552, by rfl⟩ : syracuseStep 895403 = 1343105) B1343105
theorem B895415 : Blo 892572 895415 := bstep (se 1 (by rfl) ⟨671561, by rfl⟩ : syracuseStep 895415 = 1343123) B1343123
theorem B2009537 : Blo 892572 2009537 := bstep (se 2 (by rfl) ⟨753576, by rfl⟩ : syracuseStep 2009537 = 1507153) B1507153
theorem B1911233 : Blo 892572 1911233 := bstep (se 2 (by rfl) ⟨716712, by rfl⟩ : syracuseStep 1911233 = 1433425) B1433425
theorem B895435 : Blo 892572 895435 := bstep (se 1 (by rfl) ⟨671576, by rfl⟩ : syracuseStep 895435 = 1343153) B1343153
theorem B895447 : Blo 892572 895447 := bstep (se 1 (by rfl) ⟨671585, by rfl⟩ : syracuseStep 895447 = 1343171) B1343171
theorem B895467 : Blo 892572 895467 := bstep (se 1 (by rfl) ⟨671600, by rfl⟩ : syracuseStep 895467 = 1343201) B1343201
theorem B895479 : Blo 892572 895479 := bstep (se 1 (by rfl) ⟨671609, by rfl⟩ : syracuseStep 895479 = 1343219) B1343219
theorem B895499 : Blo 892572 895499 := bstep (se 1 (by rfl) ⟨671624, by rfl⟩ : syracuseStep 895499 = 1343249) B1343249
theorem B895511 : Blo 892572 895511 := bstep (se 1 (by rfl) ⟨671633, by rfl⟩ : syracuseStep 895511 = 1343267) B1343267
theorem B895531 : Blo 892572 895531 := bstep (se 1 (by rfl) ⟨671648, by rfl⟩ : syracuseStep 895531 = 1343297) B1343297
theorem B895543 : Blo 892572 895543 := bstep (se 1 (by rfl) ⟨671657, by rfl⟩ : syracuseStep 895543 = 1343315) B1343315
theorem B6793793 : Blo 892572 6793793 := bstep (se 2 (by rfl) ⟨2547672, by rfl⟩ : syracuseStep 6793793 = 5095345) B5095345
theorem B895563 : Blo 892572 895563 := bstep (se 1 (by rfl) ⟨671672, by rfl⟩ : syracuseStep 895563 = 1343345) B1343345
theorem B895575 : Blo 892572 895575 := bstep (se 1 (by rfl) ⟨671681, by rfl⟩ : syracuseStep 895575 = 1343363) B1343363
theorem B4598365 : Blo 892572 4598365 := bstep (se 3 (by rfl) ⟨862193, by rfl⟩ : syracuseStep 4598365 = 1724387) B1724387
theorem B895595 : Blo 892572 895595 := bstep (se 1 (by rfl) ⟨671696, by rfl⟩ : syracuseStep 895595 = 1343393) B1343393
theorem B895607 : Blo 892572 895607 := bstep (se 1 (by rfl) ⟨671705, by rfl⟩ : syracuseStep 895607 = 1343411) B1343411
theorem B895627 : Blo 892572 895627 := bstep (se 1 (by rfl) ⟨671720, by rfl⟩ : syracuseStep 895627 = 1343441) B1343441
theorem B895639 : Blo 892572 895639 := bstep (se 1 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 895639 = 1343459) B1343459
theorem B4598423 : Blo 892572 4598423 := bstep (se 1 (by rfl) ⟨3448817, by rfl⟩ : syracuseStep 4598423 = 6897635) B6897635
theorem B2009753 : Blo 892572 2009753 := bstep (se 2 (by rfl) ⟨753657, by rfl⟩ : syracuseStep 2009753 = 1507315) B1507315
theorem B895659 : Blo 892572 895659 := bstep (se 1 (by rfl) ⟨671744, by rfl⟩ : syracuseStep 895659 = 1343489) B1343489
theorem B895671 : Blo 892572 895671 := bstep (se 1 (by rfl) ⟨671753, by rfl⟩ : syracuseStep 895671 = 1343507) B1343507
theorem B895691 : Blo 892572 895691 := bstep (se 1 (by rfl) ⟨671768, by rfl⟩ : syracuseStep 895691 = 1343537) B1343537
theorem B895703 : Blo 892572 895703 := bstep (se 1 (by rfl) ⟨671777, by rfl⟩ : syracuseStep 895703 = 1343555) B1343555
theorem B895723 : Blo 892572 895723 := bstep (se 1 (by rfl) ⟨671792, by rfl⟩ : syracuseStep 895723 = 1343585) B1343585
theorem B2009843 : Blo 892572 2009843 := bstep (se 1 (by rfl) ⟨1507382, by rfl⟩ : syracuseStep 2009843 = 3014765) B3014765
theorem B895735 : Blo 892572 895735 := bstep (se 1 (by rfl) ⟨671801, by rfl⟩ : syracuseStep 895735 = 1343603) B1343603
theorem B895755 : Blo 892572 895755 := bstep (se 1 (by rfl) ⟨671816, by rfl⟩ : syracuseStep 895755 = 1343633) B1343633
theorem B2009879 : Blo 892572 2009879 := bstep (se 1 (by rfl) ⟨1507409, by rfl⟩ : syracuseStep 2009879 = 3014819) B3014819
theorem B1813271 : Blo 892572 1813271 := bstep (se 1 (by rfl) ⟨1359953, by rfl⟩ : syracuseStep 1813271 = 2719907) B2719907
theorem B1911575 : Blo 892572 1911575 := bstep (se 1 (by rfl) ⟨1433681, by rfl⟩ : syracuseStep 1911575 = 2867363) B2867363
theorem B895767 : Blo 892572 895767 := bstep (se 1 (by rfl) ⟨671825, by rfl⟩ : syracuseStep 895767 = 1343651) B1343651
theorem B895787 : Blo 892572 895787 := bstep (se 1 (by rfl) ⟨671840, by rfl⟩ : syracuseStep 895787 = 1343681) B1343681
theorem B3222323 : Blo 892572 3222323 := bstep (se 1 (by rfl) ⟨2416742, by rfl⟩ : syracuseStep 3222323 = 4833485) B4833485
theorem B895799 : Blo 892572 895799 := bstep (se 1 (by rfl) ⟨671849, by rfl⟩ : syracuseStep 895799 = 1343699) B1343699
theorem B895819 : Blo 892572 895819 := bstep (se 1 (by rfl) ⟨671864, by rfl⟩ : syracuseStep 895819 = 1343729) B1343729
theorem B895831 : Blo 892572 895831 := bstep (se 1 (by rfl) ⟨671873, by rfl⟩ : syracuseStep 895831 = 1343747) B1343747
theorem B895851 : Blo 892572 895851 := bstep (se 1 (by rfl) ⟨671888, by rfl⟩ : syracuseStep 895851 = 1343777) B1343777
theorem B895863 : Blo 892572 895863 := bstep (se 1 (by rfl) ⟨671897, by rfl⟩ : syracuseStep 895863 = 1343795) B1343795
theorem B895883 : Blo 892572 895883 := bstep (se 1 (by rfl) ⟨671912, by rfl⟩ : syracuseStep 895883 = 1343825) B1343825
theorem B895895 : Blo 892572 895895 := bstep (se 1 (by rfl) ⟨671921, by rfl⟩ : syracuseStep 895895 = 1343843) B1343843
theorem B895915 : Blo 892572 895915 := bstep (se 1 (by rfl) ⟨671936, by rfl⟩ : syracuseStep 895915 = 1343873) B1343873
theorem B895927 : Blo 892572 895927 := bstep (se 1 (by rfl) ⟨671945, by rfl⟩ : syracuseStep 895927 = 1343891) B1343891
theorem B2010059 : Blo 892572 2010059 := bstep (se 1 (by rfl) ⟨1507544, by rfl⟩ : syracuseStep 2010059 = 3015089) B3015089
theorem B895947 : Blo 892572 895947 := bstep (se 1 (by rfl) ⟨671960, by rfl⟩ : syracuseStep 895947 = 1343921) B1343921
theorem B895959 : Blo 892572 895959 := bstep (se 1 (by rfl) ⟨671969, by rfl⟩ : syracuseStep 895959 = 1343939) B1343939
theorem B895979 : Blo 892572 895979 := bstep (se 1 (by rfl) ⟨671984, by rfl⟩ : syracuseStep 895979 = 1343969) B1343969
theorem B895991 : Blo 892572 895991 := bstep (se 1 (by rfl) ⟨671993, by rfl⟩ : syracuseStep 895991 = 1343987) B1343987
theorem B2010113 : Blo 892572 2010113 := bstep (se 2 (by rfl) ⟨753792, by rfl⟩ : syracuseStep 2010113 = 1507585) B1507585
theorem B896011 : Blo 892572 896011 := bstep (se 1 (by rfl) ⟨672008, by rfl⟩ : syracuseStep 896011 = 1344017) B1344017
theorem B896023 : Blo 892572 896023 := bstep (se 1 (by rfl) ⟨672017, by rfl⟩ : syracuseStep 896023 = 1344035) B1344035
theorem B24849443 : Blo 892572 24849443 := bstep (se 1 (by rfl) ⟨18637082, by rfl⟩ : syracuseStep 24849443 = 37274165) B37274165
theorem B896043 : Blo 892572 896043 := bstep (se 1 (by rfl) ⟨672032, by rfl⟩ : syracuseStep 896043 = 1344065) B1344065
theorem B896055 : Blo 892572 896055 := bstep (se 1 (by rfl) ⟨672041, by rfl⟩ : syracuseStep 896055 = 1344083) B1344083
theorem B1911883 : Blo 892572 1911883 := bstep (se 1 (by rfl) ⟨1433912, by rfl⟩ : syracuseStep 1911883 = 2867825) B2867825
theorem B896075 : Blo 892572 896075 := bstep (se 1 (by rfl) ⟨672056, by rfl⟩ : syracuseStep 896075 = 1344113) B1344113
theorem B896087 : Blo 892572 896087 := bstep (se 1 (by rfl) ⟨672065, by rfl⟩ : syracuseStep 896087 = 1344131) B1344131
theorem B896107 : Blo 892572 896107 := bstep (se 1 (by rfl) ⟨672080, by rfl⟩ : syracuseStep 896107 = 1344161) B1344161
theorem B896119 : Blo 892572 896119 := bstep (se 1 (by rfl) ⟨672089, by rfl⟩ : syracuseStep 896119 = 1344179) B1344179
theorem B896139 : Blo 892572 896139 := bstep (se 1 (by rfl) ⟨672104, by rfl⟩ : syracuseStep 896139 = 1344209) B1344209
theorem B896151 : Blo 892572 896151 := bstep (se 1 (by rfl) ⟨672113, by rfl⟩ : syracuseStep 896151 = 1344227) B1344227
theorem B896171 : Blo 892572 896171 := bstep (se 1 (by rfl) ⟨672128, by rfl⟩ : syracuseStep 896171 = 1344257) B1344257
theorem B896183 : Blo 892572 896183 := bstep (se 1 (by rfl) ⟨672137, by rfl⟩ : syracuseStep 896183 = 1344275) B1344275
theorem B896203 : Blo 892572 896203 := bstep (se 1 (by rfl) ⟨672152, by rfl⟩ : syracuseStep 896203 = 1344305) B1344305
theorem B10169549 : Blo 892572 10169549 := bstep (se 3 (by rfl) ⟨1906790, by rfl⟩ : syracuseStep 10169549 = 3813581) B3813581
theorem B896215 : Blo 892572 896215 := bstep (se 1 (by rfl) ⟨672161, by rfl⟩ : syracuseStep 896215 = 1344323) B1344323
theorem B2010329 : Blo 892572 2010329 := bstep (se 2 (by rfl) ⟨753873, by rfl⟩ : syracuseStep 2010329 = 1507747) B1507747
theorem B896235 : Blo 892572 896235 := bstep (se 1 (by rfl) ⟨672176, by rfl⟩ : syracuseStep 896235 = 1344353) B1344353
theorem B896247 : Blo 892572 896247 := bstep (se 1 (by rfl) ⟨672185, by rfl⟩ : syracuseStep 896247 = 1344371) B1344371
theorem B896267 : Blo 892572 896267 := bstep (se 1 (by rfl) ⟨672200, by rfl⟩ : syracuseStep 896267 = 1344401) B1344401
theorem B896279 : Blo 892572 896279 := bstep (se 1 (by rfl) ⟨672209, by rfl⟩ : syracuseStep 896279 = 1344419) B1344419
theorem B896299 : Blo 892572 896299 := bstep (se 1 (by rfl) ⟨672224, by rfl⟩ : syracuseStep 896299 = 1344449) B1344449
theorem B2010419 : Blo 892572 2010419 := bstep (se 1 (by rfl) ⟨1507814, by rfl⟩ : syracuseStep 2010419 = 3015629) B3015629
theorem B896311 : Blo 892572 896311 := bstep (se 1 (by rfl) ⟨672233, by rfl⟩ : syracuseStep 896311 = 1344467) B1344467
theorem B4533569 : Blo 892572 4533569 := bstep (se 2 (by rfl) ⟨1700088, by rfl⟩ : syracuseStep 4533569 = 3400177) B3400177
theorem B896331 : Blo 892572 896331 := bstep (se 1 (by rfl) ⟨672248, by rfl⟩ : syracuseStep 896331 = 1344497) B1344497
theorem B2010455 : Blo 892572 2010455 := bstep (se 1 (by rfl) ⟨1507841, by rfl⟩ : syracuseStep 2010455 = 3015683) B3015683
theorem B896343 : Blo 892572 896343 := bstep (se 1 (by rfl) ⟨672257, by rfl⟩ : syracuseStep 896343 = 1344515) B1344515
theorem B896363 : Blo 892572 896363 := bstep (se 1 (by rfl) ⟨672272, by rfl⟩ : syracuseStep 896363 = 1344545) B1344545
theorem B896375 : Blo 892572 896375 := bstep (se 1 (by rfl) ⟨672281, by rfl⟩ : syracuseStep 896375 = 1344563) B1344563
theorem B896395 : Blo 892572 896395 := bstep (se 1 (by rfl) ⟨672296, by rfl⟩ : syracuseStep 896395 = 1344593) B1344593
theorem B896407 : Blo 892572 896407 := bstep (se 1 (by rfl) ⟨672305, by rfl⟩ : syracuseStep 896407 = 1344611) B1344611
theorem B896427 : Blo 892572 896427 := bstep (se 1 (by rfl) ⟨672320, by rfl⟩ : syracuseStep 896427 = 1344641) B1344641
theorem B896439 : Blo 892572 896439 := bstep (se 1 (by rfl) ⟨672329, by rfl⟩ : syracuseStep 896439 = 1344659) B1344659
theorem B896459 : Blo 892572 896459 := bstep (se 1 (by rfl) ⟨672344, by rfl⟩ : syracuseStep 896459 = 1344689) B1344689
theorem B896471 : Blo 892572 896471 := bstep (se 1 (by rfl) ⟨672353, by rfl⟩ : syracuseStep 896471 = 1344707) B1344707
theorem B896491 : Blo 892572 896491 := bstep (se 1 (by rfl) ⟨672368, by rfl⟩ : syracuseStep 896491 = 1344737) B1344737
theorem B896503 : Blo 892572 896503 := bstep (se 1 (by rfl) ⟨672377, by rfl⟩ : syracuseStep 896503 = 1344755) B1344755
theorem B2010635 : Blo 892572 2010635 := bstep (se 1 (by rfl) ⟨1507976, by rfl⟩ : syracuseStep 2010635 = 3015953) B3015953
theorem B896523 : Blo 892572 896523 := bstep (se 1 (by rfl) ⟨672392, by rfl⟩ : syracuseStep 896523 = 1344785) B1344785
theorem B896535 : Blo 892572 896535 := bstep (se 1 (by rfl) ⟨672401, by rfl⟩ : syracuseStep 896535 = 1344803) B1344803
theorem B896555 : Blo 892572 896555 := bstep (se 1 (by rfl) ⟨672416, by rfl⟩ : syracuseStep 896555 = 1344833) B1344833
theorem B896567 : Blo 892572 896567 := bstep (se 1 (by rfl) ⟨672425, by rfl⟩ : syracuseStep 896567 = 1344851) B1344851
theorem B2010689 : Blo 892572 2010689 := bstep (se 2 (by rfl) ⟨754008, by rfl⟩ : syracuseStep 2010689 = 1508017) B1508017
theorem B2043571 : Blo 892572 2043571 := bstep (se 1 (by rfl) ⟨1532678, by rfl⟩ : syracuseStep 2043571 = 3065357) B3065357
theorem B2010905 : Blo 892572 2010905 := bstep (se 2 (by rfl) ⟨754089, by rfl⟩ : syracuseStep 2010905 = 1508179) B1508179
theorem B3223361 : Blo 892572 3223361 := bstep (se 2 (by rfl) ⟨1208760, by rfl⟩ : syracuseStep 3223361 = 2417521) B2417521
theorem B2010995 : Blo 892572 2010995 := bstep (se 1 (by rfl) ⟨1508246, by rfl⟩ : syracuseStep 2010995 = 3016493) B3016493
theorem B2011031 : Blo 892572 2011031 := bstep (se 1 (by rfl) ⟨1508273, by rfl⟩ : syracuseStep 2011031 = 3016547) B3016547
theorem B1912729 : Blo 892572 1912729 := bstep (se 2 (by rfl) ⟨717273, by rfl⟩ : syracuseStep 1912729 = 1434547) B1434547
theorem B58896305 : Blo 892572 58896305 := bstep (se 2 (by rfl) ⟨22086114, by rfl⟩ : syracuseStep 58896305 = 44172229) B44172229
theorem B2011211 : Blo 892572 2011211 := bstep (se 1 (by rfl) ⟨1508408, by rfl⟩ : syracuseStep 2011211 = 3016817) B3016817
theorem B2011265 : Blo 892572 2011265 := bstep (se 2 (by rfl) ⟨754224, by rfl⟩ : syracuseStep 2011265 = 1508449) B1508449
theorem B2011481 : Blo 892572 2011481 := bstep (se 2 (by rfl) ⟨754305, by rfl⟩ : syracuseStep 2011481 = 1508611) B1508611
theorem B2011571 : Blo 892572 2011571 := bstep (se 1 (by rfl) ⟨1508678, by rfl⟩ : syracuseStep 2011571 = 3017357) B3017357
theorem B2011607 : Blo 892572 2011607 := bstep (se 1 (by rfl) ⟨1508705, by rfl⟩ : syracuseStep 2011607 = 3017411) B3017411
theorem B6795737 : Blo 892572 6795737 := bstep (se 2 (by rfl) ⟨2548401, by rfl⟩ : syracuseStep 6795737 = 5096803) B5096803
theorem B2011787 : Blo 892572 2011787 := bstep (se 1 (by rfl) ⟨1508840, by rfl⟩ : syracuseStep 2011787 = 3017681) B3017681
theorem B2011841 : Blo 892572 2011841 := bstep (se 2 (by rfl) ⟨754440, by rfl⟩ : syracuseStep 2011841 = 1508881) B1508881
theorem B5092247 : Blo 892572 5092247 := bstep (se 1 (by rfl) ⟨3819185, by rfl⟩ : syracuseStep 5092247 = 7638371) B7638371
theorem B2012057 : Blo 892572 2012057 := bstep (se 2 (by rfl) ⟨754521, by rfl⟩ : syracuseStep 2012057 = 1509043) B1509043
theorem B2012147 : Blo 892572 2012147 := bstep (se 1 (by rfl) ⟨1509110, by rfl⟩ : syracuseStep 2012147 = 3018221) B3018221
theorem B2012183 : Blo 892572 2012183 := bstep (se 1 (by rfl) ⟨1509137, by rfl⟩ : syracuseStep 2012183 = 3018275) B3018275
theorem B3814573 : Blo 892572 3814573 := bstep (se 3 (by rfl) ⟨715232, by rfl⟩ : syracuseStep 3814573 = 1430465) B1430465
theorem B1914035 : Blo 892572 1914035 := bstep (se 1 (by rfl) ⟨1435526, by rfl⟩ : syracuseStep 1914035 = 2871053) B2871053
theorem B2012363 : Blo 892572 2012363 := bstep (se 1 (by rfl) ⟨1509272, by rfl⟩ : syracuseStep 2012363 = 3018545) B3018545
theorem B4535513 : Blo 892572 4535513 := bstep (se 2 (by rfl) ⟨1700817, by rfl⟩ : syracuseStep 4535513 = 3401635) B3401635
theorem B2012417 : Blo 892572 2012417 := bstep (se 2 (by rfl) ⟨754656, by rfl⟩ : syracuseStep 2012417 = 1509313) B1509313
theorem B3225035 : Blo 892572 3225035 := bstep (se 1 (by rfl) ⟨2418776, by rfl⟩ : syracuseStep 3225035 = 4837553) B4837553
theorem B1357273 : Blo 892572 1357273 := bstep (se 2 (by rfl) ⟨508977, by rfl⟩ : syracuseStep 1357273 = 1017955) B1017955
theorem B2012633 : Blo 892572 2012633 := bstep (se 2 (by rfl) ⟨754737, by rfl⟩ : syracuseStep 2012633 = 1509475) B1509475
theorem B3225091 : Blo 892572 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B2012723 : Blo 892572 2012723 := bstep (se 1 (by rfl) ⟨1509542, by rfl⟩ : syracuseStep 2012723 = 3019085) B3019085
theorem B2012759 : Blo 892572 2012759 := bstep (se 1 (by rfl) ⟨1509569, by rfl⟩ : syracuseStep 2012759 = 3019139) B3019139
theorem B2012939 : Blo 892572 2012939 := bstep (se 1 (by rfl) ⟨1509704, by rfl⟩ : syracuseStep 2012939 = 3019409) B3019409
theorem B2012993 : Blo 892572 2012993 := bstep (se 2 (by rfl) ⟨754872, by rfl⟩ : syracuseStep 2012993 = 1509745) B1509745
theorem B3389273 : Blo 892572 3389273 := bstep (se 2 (by rfl) ⟨1270977, by rfl⟩ : syracuseStep 3389273 = 2541955) B2541955
theorem B2013209 : Blo 892572 2013209 := bstep (se 2 (by rfl) ⟨754953, by rfl⟩ : syracuseStep 2013209 = 1509907) B1509907
theorem B3389485 : Blo 892572 3389485 := bstep (se 3 (by rfl) ⟨635528, by rfl⟩ : syracuseStep 3389485 = 1271057) B1271057
theorem B2013299 : Blo 892572 2013299 := bstep (se 1 (by rfl) ⟨1509974, by rfl⟩ : syracuseStep 2013299 = 3019949) B3019949
theorem B2013335 : Blo 892572 2013335 := bstep (se 1 (by rfl) ⟨1510001, by rfl⟩ : syracuseStep 2013335 = 3020003) B3020003
theorem B2013515 : Blo 892572 2013515 := bstep (se 1 (by rfl) ⟨1510136, by rfl⟩ : syracuseStep 2013515 = 3020273) B3020273
theorem B1816921 : Blo 892572 1816921 := bstep (se 2 (by rfl) ⟨681345, by rfl⟩ : syracuseStep 1816921 = 1362691) B1362691
theorem B3389789 : Blo 892572 3389789 := bstep (se 3 (by rfl) ⟨635585, by rfl⟩ : syracuseStep 3389789 = 1271171) B1271171
theorem B2013569 : Blo 892572 2013569 := bstep (se 2 (by rfl) ⟨755088, by rfl⟩ : syracuseStep 2013569 = 1510177) B1510177
theorem B2013785 : Blo 892572 2013785 := bstep (se 2 (by rfl) ⟨755169, by rfl⟩ : syracuseStep 2013785 = 1510339) B1510339
theorem B2013875 : Blo 892572 2013875 := bstep (se 1 (by rfl) ⟨1510406, by rfl⟩ : syracuseStep 2013875 = 3020813) B3020813
theorem B2013911 : Blo 892572 2013911 := bstep (se 1 (by rfl) ⟨1510433, by rfl⟩ : syracuseStep 2013911 = 3020867) B3020867
theorem B5094161 : Blo 892572 5094161 := bstep (se 2 (by rfl) ⟨1910310, by rfl⟩ : syracuseStep 5094161 = 3820621) B3820621
theorem B3226391 : Blo 892572 3226391 := bstep (se 1 (by rfl) ⟨2419793, by rfl⟩ : syracuseStep 3226391 = 4839587) B4839587
theorem B4537133 : Blo 892572 4537133 := bstep (se 3 (by rfl) ⟨850712, by rfl⟩ : syracuseStep 4537133 = 1701425) B1701425
theorem B16169827 : Blo 892572 16169827 := bstep (se 1 (by rfl) ⟨12127370, by rfl⟩ : syracuseStep 16169827 = 24254741) B24254741
theorem B2014091 : Blo 892572 2014091 := bstep (se 1 (by rfl) ⟨1510568, by rfl⟩ : syracuseStep 2014091 = 3021137) B3021137
theorem B2145217 : Blo 892572 2145217 := bstep (se 2 (by rfl) ⟨804456, by rfl⟩ : syracuseStep 2145217 = 1608913) B1608913
theorem B2014145 : Blo 892572 2014145 := bstep (se 2 (by rfl) ⟨755304, by rfl⟩ : syracuseStep 2014145 = 1510609) B1510609
theorem B2014361 : Blo 892572 2014361 := bstep (se 2 (by rfl) ⟨755385, by rfl⟩ : syracuseStep 2014361 = 1510771) B1510771
theorem B2014451 : Blo 892572 2014451 := bstep (se 1 (by rfl) ⟨1510838, by rfl⟩ : syracuseStep 2014451 = 3021677) B3021677
theorem B2014487 : Blo 892572 2014487 := bstep (se 1 (by rfl) ⟨1510865, by rfl⟩ : syracuseStep 2014487 = 3021731) B3021731
theorem B1129879 : Blo 892572 1129879 := bstep (se 1 (by rfl) ⟨847409, by rfl⟩ : syracuseStep 1129879 = 1694819) B1694819
theorem B2014667 : Blo 892572 2014667 := bstep (se 1 (by rfl) ⟨1511000, by rfl⟩ : syracuseStep 2014667 = 3022001) B3022001
theorem B2014721 : Blo 892572 2014721 := bstep (se 2 (by rfl) ⟨755520, by rfl⟩ : syracuseStep 2014721 = 1511041) B1511041
theorem B3816983 : Blo 892572 3816983 := bstep (se 1 (by rfl) ⟨2862737, by rfl⟩ : syracuseStep 3816983 = 5725475) B5725475
theorem B2014937 : Blo 892572 2014937 := bstep (se 2 (by rfl) ⟨755601, by rfl⟩ : syracuseStep 2014937 = 1511203) B1511203
theorem B6799139 : Blo 892572 6799139 := bstep (se 1 (by rfl) ⟨5099354, by rfl⟩ : syracuseStep 6799139 = 10198709) B10198709
theorem B2015027 : Blo 892572 2015027 := bstep (se 1 (by rfl) ⟨1511270, by rfl⟩ : syracuseStep 2015027 = 3022541) B3022541
theorem B11452225 : Blo 892572 11452225 := bstep (se 2 (by rfl) ⟨4294584, by rfl⟩ : syracuseStep 11452225 = 8589169) B8589169
theorem B2015063 : Blo 892572 2015063 := bstep (se 1 (by rfl) ⟨1511297, by rfl⟩ : syracuseStep 2015063 = 3022595) B3022595
theorem B2867147 : Blo 892572 2867147 := bstep (se 1 (by rfl) ⟨2150360, by rfl⟩ : syracuseStep 2867147 = 4300721) B4300721
theorem B2015243 : Blo 892572 2015243 := bstep (se 1 (by rfl) ⟨1511432, by rfl⟩ : syracuseStep 2015243 = 3022865) B3022865
theorem B2015297 : Blo 892572 2015297 := bstep (se 2 (by rfl) ⟨755736, by rfl⟩ : syracuseStep 2015297 = 1511473) B1511473
theorem B7258243 : Blo 892572 7258243 := bstep (se 1 (by rfl) ⟨5443682, by rfl⟩ : syracuseStep 7258243 = 10887365) B10887365
theorem B1130699 : Blo 892572 1130699 := bstep (se 1 (by rfl) ⟨848024, by rfl⟩ : syracuseStep 1130699 = 1696049) B1696049
theorem B1360075 : Blo 892572 1360075 := bstep (se 1 (by rfl) ⟨1020056, by rfl⟩ : syracuseStep 1360075 = 2040113) B2040113
theorem B2015513 : Blo 892572 2015513 := bstep (se 2 (by rfl) ⟨755817, by rfl⟩ : syracuseStep 2015513 = 1511635) B1511635
theorem B7258403 : Blo 892572 7258403 := bstep (se 1 (by rfl) ⟨5443802, by rfl⟩ : syracuseStep 7258403 = 10887605) B10887605
theorem B2015603 : Blo 892572 2015603 := bstep (se 1 (by rfl) ⟨1511702, by rfl⟩ : syracuseStep 2015603 = 3023405) B3023405
theorem B2015639 : Blo 892572 2015639 := bstep (se 1 (by rfl) ⟨1511729, by rfl⟩ : syracuseStep 2015639 = 3023459) B3023459
theorem B19350029 : Blo 892572 19350029 := bstep (se 3 (by rfl) ⟨3628130, by rfl⟩ : syracuseStep 19350029 = 7256261) B7256261
theorem B2015819 : Blo 892572 2015819 := bstep (se 1 (by rfl) ⟨1511864, by rfl⟩ : syracuseStep 2015819 = 3023729) B3023729
theorem B2015873 : Blo 892572 2015873 := bstep (se 2 (by rfl) ⟨755952, by rfl⟩ : syracuseStep 2015873 = 1511905) B1511905
theorem B2016089 : Blo 892572 2016089 := bstep (se 2 (by rfl) ⟨756033, by rfl⟩ : syracuseStep 2016089 = 1512067) B1512067
theorem B3392387 : Blo 892572 3392387 := bstep (se 1 (by rfl) ⟨2544290, by rfl⟩ : syracuseStep 3392387 = 5088581) B5088581
theorem B1131403 : Blo 892572 1131403 := bstep (se 1 (by rfl) ⟨848552, by rfl⟩ : syracuseStep 1131403 = 1697105) B1697105
theorem B3392401 : Blo 892572 3392401 := bstep (se 2 (by rfl) ⟨1272150, by rfl⟩ : syracuseStep 3392401 = 2544301) B2544301
theorem B2016179 : Blo 892572 2016179 := bstep (se 1 (by rfl) ⟨1512134, by rfl⟩ : syracuseStep 2016179 = 3024269) B3024269
theorem B2016215 : Blo 892572 2016215 := bstep (se 1 (by rfl) ⟨1512161, by rfl⟩ : syracuseStep 2016215 = 3024323) B3024323
theorem B3621905 : Blo 892572 3621905 := bstep (se 2 (by rfl) ⟨1358214, by rfl⟩ : syracuseStep 3621905 = 2716429) B2716429
theorem B17187875 : Blo 892572 17187875 := bstep (se 1 (by rfl) ⟨12890906, by rfl⟩ : syracuseStep 17187875 = 25781813) B25781813
theorem B2016395 : Blo 892572 2016395 := bstep (se 1 (by rfl) ⟨1512296, by rfl⟩ : syracuseStep 2016395 = 3024593) B3024593
theorem B1131671 : Blo 892572 1131671 := bstep (se 1 (by rfl) ⟨848753, by rfl⟩ : syracuseStep 1131671 = 1697507) B1697507
theorem B3392705 : Blo 892572 3392705 := bstep (se 2 (by rfl) ⟨1272264, by rfl⟩ : syracuseStep 3392705 = 2544529) B2544529
theorem B2016449 : Blo 892572 2016449 := bstep (se 2 (by rfl) ⟨756168, by rfl⟩ : syracuseStep 2016449 = 1512337) B1512337
theorem B9684269 : Blo 892572 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B3818897 : Blo 892572 3818897 := bstep (se 2 (by rfl) ⟨1432086, by rfl⟩ : syracuseStep 3818897 = 2864173) B2864173
theorem B7259543 : Blo 892572 7259543 := bstep (se 1 (by rfl) ⟨5444657, by rfl⟩ : syracuseStep 7259543 = 10889315) B10889315
theorem B2016665 : Blo 892572 2016665 := bstep (se 2 (by rfl) ⟨756249, by rfl⟩ : syracuseStep 2016665 = 1512499) B1512499
theorem B2016755 : Blo 892572 2016755 := bstep (se 1 (by rfl) ⟨1512566, by rfl⟩ : syracuseStep 2016755 = 3025133) B3025133
theorem B13780493 : Blo 892572 13780493 := bstep (se 3 (by rfl) ⟨2583842, by rfl⟩ : syracuseStep 13780493 = 5167685) B5167685
theorem B2016791 : Blo 892572 2016791 := bstep (se 1 (by rfl) ⟨1512593, by rfl⟩ : syracuseStep 2016791 = 3025187) B3025187
theorem B1033771 : Blo 892572 1033771 := bstep (se 1 (by rfl) ⟨775328, by rfl⟩ : syracuseStep 1033771 = 1550657) B1550657
theorem B2016971 : Blo 892572 2016971 := bstep (se 1 (by rfl) ⟨1512728, by rfl⟩ : syracuseStep 2016971 = 3025457) B3025457
theorem B2017025 : Blo 892572 2017025 := bstep (se 2 (by rfl) ⟨756384, by rfl⟩ : syracuseStep 2017025 = 1512769) B1512769
theorem B1132375 : Blo 892572 1132375 := bstep (se 1 (by rfl) ⟨849281, by rfl⟩ : syracuseStep 1132375 = 1698563) B1698563
theorem B3393373 : Blo 892572 3393373 := bstep (se 3 (by rfl) ⟨636257, by rfl⟩ : syracuseStep 3393373 = 1272515) B1272515
theorem B2017241 : Blo 892572 2017241 := bstep (se 2 (by rfl) ⟨756465, by rfl⟩ : syracuseStep 2017241 = 1512931) B1512931
theorem B1722379 : Blo 892572 1722379 := bstep (se 1 (by rfl) ⟨1291784, by rfl⟩ : syracuseStep 1722379 = 2583569) B2583569
theorem B2869337 : Blo 892572 2869337 := bstep (se 2 (by rfl) ⟨1076001, by rfl⟩ : syracuseStep 2869337 = 2152003) B2152003
theorem B3917917 : Blo 892572 3917917 := bstep (se 3 (by rfl) ⟨734609, by rfl⟩ : syracuseStep 3917917 = 1469219) B1469219
theorem B8603779 : Blo 892572 8603779 := bstep (se 1 (by rfl) ⟨6452834, by rfl⟩ : syracuseStep 8603779 = 12905669) B12905669
theorem B3360941 : Blo 892572 3360941 := bstep (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) B1260353
theorem B2869465 : Blo 892572 2869465 := bstep (se 2 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 2869465 = 2152099) B2152099
theorem B2148697 : Blo 892572 2148697 := bstep (se 2 (by rfl) ⟨805761, by rfl⟩ : syracuseStep 2148697 = 1611523) B1611523
theorem B3819869 : Blo 892572 3819869 := bstep (se 3 (by rfl) ⟨716225, by rfl⟩ : syracuseStep 3819869 = 1432451) B1432451
theorem B2869721 : Blo 892572 2869721 := bstep (se 2 (by rfl) ⟨1076145, by rfl⟩ : syracuseStep 2869721 = 2152291) B2152291
theorem B7653953 : Blo 892572 7653953 := bstep (se 2 (by rfl) ⟨2870232, by rfl⟩ : syracuseStep 7653953 = 5740465) B5740465
theorem B9685655 : Blo 892572 9685655 := bstep (se 1 (by rfl) ⟨7264241, by rfl⟩ : syracuseStep 9685655 = 14528483) B14528483
theorem B6441763 : Blo 892572 6441763 := bstep (se 1 (by rfl) ⟨4831322, by rfl⟩ : syracuseStep 6441763 = 9662645) B9662645
theorem B22924133 : Blo 892572 22924133 := bstep (se 4 (by rfl) ⟨2149137, by rfl⟩ : syracuseStep 22924133 = 4298275) B4298275
theorem B3394649 : Blo 892572 3394649 := bstep (se 2 (by rfl) ⟨1272993, by rfl⟩ : syracuseStep 3394649 = 2545987) B2545987
theorem B9784451 : Blo 892572 9784451 := bstep (se 1 (by rfl) ⟨7338338, by rfl⟩ : syracuseStep 9784451 = 14676677) B14676677
theorem B1363159 : Blo 892572 1363159 := bstep (se 1 (by rfl) ⟨1022369, by rfl⟩ : syracuseStep 1363159 = 2044739) B2044739
theorem B10898693 : Blo 892572 10898693 := bstep (se 4 (by rfl) ⟨1021752, by rfl⟩ : syracuseStep 10898693 = 2043505) B2043505
theorem B3624209 : Blo 892572 3624209 := bstep (se 2 (by rfl) ⟨1359078, by rfl⟩ : syracuseStep 3624209 = 2718157) B2718157
theorem B1134091 : Blo 892572 1134091 := bstep (se 1 (by rfl) ⟨850568, by rfl⟩ : syracuseStep 1134091 = 1701137) B1701137
theorem B14536205 : Blo 892572 14536205 := bstep (se 3 (by rfl) ⟨2725538, by rfl⟩ : syracuseStep 14536205 = 5451077) B5451077
theorem B2543197 : Blo 892572 2543197 := bstep (se 3 (by rfl) ⟨476849, by rfl⟩ : syracuseStep 2543197 = 953699) B953699
theorem B2870977 : Blo 892572 2870977 := bstep (se 2 (by rfl) ⟨1076616, by rfl⟩ : syracuseStep 2870977 = 2153233) B2153233
theorem B3821357 : Blo 892572 3821357 := bstep (se 3 (by rfl) ⟨716504, by rfl⟩ : syracuseStep 3821357 = 1433009) B1433009
theorem B5099537 : Blo 892572 5099537 := bstep (se 2 (by rfl) ⟨1912326, by rfl⟩ : syracuseStep 5099537 = 3824653) B3824653
theorem B7360717 : Blo 892572 7360717 := bstep (se 3 (by rfl) ⟨1380134, by rfl⟩ : syracuseStep 7360717 = 2760269) B2760269
theorem B1528087 : Blo 892572 1528087 := bstep (se 1 (by rfl) ⟨1146065, by rfl⟩ : syracuseStep 1528087 = 2292131) B2292131
theorem B5099993 : Blo 892572 5099993 := bstep (se 2 (by rfl) ⟨1912497, by rfl⟩ : syracuseStep 5099993 = 3824995) B3824995
theorem B3396275 : Blo 892572 3396275 := bstep (se 1 (by rfl) ⟨2547206, by rfl⟩ : syracuseStep 3396275 = 5094413) B5094413
theorem B1004215 : Blo 892572 1004215 := bstep (se 1 (by rfl) ⟨753161, by rfl⟩ : syracuseStep 1004215 = 1506323) B1506323
theorem B3396289 : Blo 892572 3396289 := bstep (se 2 (by rfl) ⟨1273608, by rfl⟩ : syracuseStep 3396289 = 2547217) B2547217
theorem B73355989 : Blo 892572 73355989 := bstep (se 7 (by rfl) ⟨859640, by rfl⟩ : syracuseStep 73355989 = 1719281) B1719281
theorem B905963 : Blo 892572 905963 := bstep (se 1 (by rfl) ⟨679472, by rfl⟩ : syracuseStep 905963 = 1358945) B1358945
theorem B2544473 : Blo 892572 2544473 := bstep (se 2 (by rfl) ⟨954177, by rfl⟩ : syracuseStep 2544473 = 1908355) B1908355
theorem B1004395 : Blo 892572 1004395 := bstep (se 1 (by rfl) ⟨753296, by rfl⟩ : syracuseStep 1004395 = 1506593) B1506593
theorem B1004503 : Blo 892572 1004503 := bstep (se 1 (by rfl) ⟨753377, by rfl⟩ : syracuseStep 1004503 = 1506755) B1506755
theorem B6804485 : Blo 892572 6804485 := bstep (se 4 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 6804485 = 1275841) B1275841
theorem B1004683 : Blo 892572 1004683 := bstep (se 1 (by rfl) ⟨753512, by rfl⟩ : syracuseStep 1004683 = 1507025) B1507025
theorem B1004791 : Blo 892572 1004791 := bstep (se 1 (by rfl) ⟨753593, by rfl⟩ : syracuseStep 1004791 = 1507187) B1507187
theorem B2413975 : Blo 892572 2413975 := bstep (se 1 (by rfl) ⟨1810481, by rfl⟩ : syracuseStep 2413975 = 3620963) B3620963
theorem B1004971 : Blo 892572 1004971 := bstep (se 1 (by rfl) ⟨753728, by rfl⟩ : syracuseStep 1004971 = 1507457) B1507457
theorem B1005079 : Blo 892572 1005079 := bstep (se 1 (by rfl) ⟨753809, by rfl⟩ : syracuseStep 1005079 = 1507619) B1507619
theorem B6968933 : Blo 892572 6968933 := bstep (se 4 (by rfl) ⟨653337, by rfl⟩ : syracuseStep 6968933 = 1306675) B1306675
theorem B1005259 : Blo 892572 1005259 := bstep (se 1 (by rfl) ⟨753944, by rfl⟩ : syracuseStep 1005259 = 1507889) B1507889
theorem B3823321 : Blo 892572 3823321 := bstep (se 2 (by rfl) ⟨1433745, by rfl⟩ : syracuseStep 3823321 = 2867491) B2867491
theorem B1005367 : Blo 892572 1005367 := bstep (se 1 (by rfl) ⟨754025, by rfl⟩ : syracuseStep 1005367 = 1508051) B1508051
theorem B6117221 : Blo 892572 6117221 := bstep (se 4 (by rfl) ⟨573489, by rfl⟩ : syracuseStep 6117221 = 1146979) B1146979
theorem B9656243 : Blo 892572 9656243 := bstep (se 1 (by rfl) ⟨7242182, by rfl⟩ : syracuseStep 9656243 = 14484365) B14484365
theorem B1005547 : Blo 892572 1005547 := bstep (se 1 (by rfl) ⟨754160, by rfl⟩ : syracuseStep 1005547 = 1508321) B1508321
theorem B1005655 : Blo 892572 1005655 := bstep (se 1 (by rfl) ⟨754241, by rfl⟩ : syracuseStep 1005655 = 1508483) B1508483
theorem B1005835 : Blo 892572 1005835 := bstep (se 1 (by rfl) ⟨754376, by rfl⟩ : syracuseStep 1005835 = 1508753) B1508753
theorem B1005943 : Blo 892572 1005943 := bstep (se 1 (by rfl) ⟨754457, by rfl⟩ : syracuseStep 1005943 = 1508915) B1508915
theorem B2546113 : Blo 892572 2546113 := bstep (se 2 (by rfl) ⟨954792, by rfl⟩ : syracuseStep 2546113 = 1909585) B1909585
theorem B1006123 : Blo 892572 1006123 := bstep (se 1 (by rfl) ⟨754592, by rfl⟩ : syracuseStep 1006123 = 1509185) B1509185
theorem B3398219 : Blo 892572 3398219 := bstep (se 1 (by rfl) ⟨2548664, by rfl⟩ : syracuseStep 3398219 = 5097329) B5097329
theorem B3398233 : Blo 892572 3398233 := bstep (se 2 (by rfl) ⟨1274337, by rfl⟩ : syracuseStep 3398233 = 2548675) B2548675
theorem B10181213 : Blo 892572 10181213 := bstep (se 3 (by rfl) ⟨1908977, by rfl⟩ : syracuseStep 10181213 = 3817955) B3817955
theorem B1006231 : Blo 892572 1006231 := bstep (se 1 (by rfl) ⟨754673, by rfl⟩ : syracuseStep 1006231 = 1509347) B1509347
theorem B3824279 : Blo 892572 3824279 := bstep (se 1 (by rfl) ⟨2868209, by rfl⟩ : syracuseStep 3824279 = 5736419) B5736419
theorem B1432343 : Blo 892572 1432343 := bstep (se 1 (by rfl) ⟨1074257, by rfl⟩ : syracuseStep 1432343 = 2148515) B2148515
theorem B1694515 : Blo 892572 1694515 := bstep (se 1 (by rfl) ⟨1270886, by rfl⟩ : syracuseStep 1694515 = 2541773) B2541773
theorem B1006411 : Blo 892572 1006411 := bstep (se 1 (by rfl) ⟨754808, by rfl⟩ : syracuseStep 1006411 = 1509617) B1509617
theorem B2579293 : Blo 892572 2579293 := bstep (se 3 (by rfl) ⟨483617, by rfl⟩ : syracuseStep 2579293 = 967235) B967235
theorem B1006519 : Blo 892572 1006519 := bstep (se 1 (by rfl) ⟨754889, by rfl⟩ : syracuseStep 1006519 = 1509779) B1509779
theorem B1006699 : Blo 892572 1006699 := bstep (se 1 (by rfl) ⟨755024, by rfl⟩ : syracuseStep 1006699 = 1510049) B1510049
theorem B7625933 : Blo 892572 7625933 := bstep (se 3 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 7625933 = 2859725) B2859725
theorem B1006807 : Blo 892572 1006807 := bstep (se 1 (by rfl) ⟨755105, by rfl⟩ : syracuseStep 1006807 = 1510211) B1510211
theorem B1531097 : Blo 892572 1531097 := bstep (se 2 (by rfl) ⟨574161, by rfl⟩ : syracuseStep 1531097 = 1148323) B1148323
theorem B1695001 : Blo 892572 1695001 := bstep (se 2 (by rfl) ⟨635625, by rfl⟩ : syracuseStep 1695001 = 1271251) B1271251
theorem B1432907 : Blo 892572 1432907 := bstep (se 1 (by rfl) ⟨1074680, by rfl⟩ : syracuseStep 1432907 = 2149361) B2149361
theorem B8609125 : Blo 892572 8609125 := bstep (se 4 (by rfl) ⟨807105, by rfl⟩ : syracuseStep 8609125 = 1614211) B1614211
theorem B6806915 : Blo 892572 6806915 := bstep (se 1 (by rfl) ⟨5105186, by rfl⟩ : syracuseStep 6806915 = 10210373) B10210373
theorem B1006987 : Blo 892572 1006987 := bstep (se 1 (by rfl) ⟨755240, by rfl⟩ : syracuseStep 1006987 = 1510481) B1510481
theorem B2153945 : Blo 892572 2153945 := bstep (se 2 (by rfl) ⟨807729, by rfl⟩ : syracuseStep 2153945 = 1615459) B1615459
theorem B1007095 : Blo 892572 1007095 := bstep (se 1 (by rfl) ⟨755321, by rfl⟩ : syracuseStep 1007095 = 1510643) B1510643
theorem B24436241 : Blo 892572 24436241 := bstep (se 2 (by rfl) ⟨9163590, by rfl⟩ : syracuseStep 24436241 = 18327181) B18327181
theorem B3399191 : Blo 892572 3399191 := bstep (se 1 (by rfl) ⟨2549393, by rfl⟩ : syracuseStep 3399191 = 5098787) B5098787
theorem B1007275 : Blo 892572 1007275 := bstep (se 1 (by rfl) ⟨755456, by rfl⟩ : syracuseStep 1007275 = 1510913) B1510913
theorem B1007383 : Blo 892572 1007383 := bstep (se 1 (by rfl) ⟨755537, by rfl⟩ : syracuseStep 1007383 = 1511075) B1511075
theorem B1695563 : Blo 892572 1695563 := bstep (se 1 (by rfl) ⟨1271672, by rfl⟩ : syracuseStep 1695563 = 2543345) B2543345
theorem B1007563 : Blo 892572 1007563 := bstep (se 1 (by rfl) ⟨755672, by rfl⟩ : syracuseStep 1007563 = 1511345) B1511345
theorem B1695745 : Blo 892572 1695745 := bstep (se 2 (by rfl) ⟨635904, by rfl⟩ : syracuseStep 1695745 = 1271809) B1271809
theorem B1007671 : Blo 892572 1007671 := bstep (se 1 (by rfl) ⟨755753, by rfl⟩ : syracuseStep 1007671 = 1511507) B1511507
theorem B2547787 : Blo 892572 2547787 := bstep (se 1 (by rfl) ⟨1910840, by rfl⟩ : syracuseStep 2547787 = 3821681) B3821681
theorem B1007851 : Blo 892572 1007851 := bstep (se 1 (by rfl) ⟨755888, by rfl⟩ : syracuseStep 1007851 = 1511777) B1511777
theorem B1007959 : Blo 892572 1007959 := bstep (se 1 (by rfl) ⟨755969, by rfl⟩ : syracuseStep 1007959 = 1511939) B1511939
theorem B2548061 : Blo 892572 2548061 := bstep (se 3 (by rfl) ⟨477761, by rfl⟩ : syracuseStep 2548061 = 955523) B955523
theorem B1008139 : Blo 892572 1008139 := bstep (se 1 (by rfl) ⟨756104, by rfl⟩ : syracuseStep 1008139 = 1512209) B1512209
theorem B1008247 : Blo 892572 1008247 := bstep (se 1 (by rfl) ⟨756185, by rfl⟩ : syracuseStep 1008247 = 1512371) B1512371
theorem B1696459 : Blo 892572 1696459 := bstep (se 1 (by rfl) ⟨1272344, by rfl⟩ : syracuseStep 1696459 = 2544689) B2544689
theorem B3629785 : Blo 892572 3629785 := bstep (se 2 (by rfl) ⟨1361169, by rfl⟩ : syracuseStep 3629785 = 2722339) B2722339
theorem B3400451 : Blo 892572 3400451 := bstep (se 1 (by rfl) ⟨2550338, by rfl⟩ : syracuseStep 3400451 = 5100677) B5100677
theorem B1696535 : Blo 892572 1696535 := bstep (se 1 (by rfl) ⟨1272401, by rfl⟩ : syracuseStep 1696535 = 2544803) B2544803
theorem B1008427 : Blo 892572 1008427 := bstep (se 1 (by rfl) ⟨756320, by rfl⟩ : syracuseStep 1008427 = 1512641) B1512641
theorem B1008535 : Blo 892572 1008535 := bstep (se 1 (by rfl) ⟨756401, by rfl⟩ : syracuseStep 1008535 = 1512803) B1512803
theorem B1959041 : Blo 892572 1959041 := bstep (se 2 (by rfl) ⟨734640, by rfl⟩ : syracuseStep 1959041 = 1469281) B1469281
theorem B1697203 : Blo 892572 1697203 := bstep (se 1 (by rfl) ⟨1272902, by rfl⟩ : syracuseStep 1697203 = 2545805) B2545805
theorem B1271371 : Blo 892572 1271371 := bstep (se 1 (by rfl) ⟨953528, by rfl⟩ : syracuseStep 1271371 = 1907057) B1907057
theorem B1697431 : Blo 892572 1697431 := bstep (se 1 (by rfl) ⟨1273073, by rfl⟩ : syracuseStep 1697431 = 2546147) B2546147
theorem B14345909 : Blo 892572 14345909 := bstep (se 5 (by rfl) ⟨672464, by rfl⟩ : syracuseStep 14345909 = 1344929) B1344929
theorem B5105369 : Blo 892572 5105369 := bstep (se 2 (by rfl) ⟨1914513, by rfl⟩ : syracuseStep 5105369 = 3829027) B3829027
theorem B1697537 : Blo 892572 1697537 := bstep (se 2 (by rfl) ⟨636576, by rfl⟩ : syracuseStep 1697537 = 1273153) B1273153
theorem B1697689 : Blo 892572 1697689 := bstep (se 2 (by rfl) ⟨636633, by rfl⟩ : syracuseStep 1697689 = 1273267) B1273267
theorem B21718961 : Blo 892572 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B3827729 : Blo 892572 3827729 := bstep (se 2 (by rfl) ⟨1435398, by rfl⟩ : syracuseStep 3827729 = 2870797) B2870797
theorem B5433389 : Blo 892572 5433389 := bstep (se 3 (by rfl) ⟨1018760, by rfl⟩ : syracuseStep 5433389 = 2037521) B2037521
theorem B2615513 : Blo 892572 2615513 := bstep (se 2 (by rfl) ⟨980817, by rfl⟩ : syracuseStep 2615513 = 1961635) B1961635
theorem B2550361 : Blo 892572 2550361 := bstep (se 2 (by rfl) ⟨956385, by rfl⟩ : syracuseStep 2550361 = 1912771) B1912771
theorem B5434073 : Blo 892572 5434073 := bstep (se 2 (by rfl) ⟨2037777, by rfl⟩ : syracuseStep 5434073 = 4075555) B4075555
theorem B1272601 : Blo 892572 1272601 := bstep (se 2 (by rfl) ⟨477225, by rfl⟩ : syracuseStep 1272601 = 954451) B954451
theorem B3828653 : Blo 892572 3828653 := bstep (se 3 (by rfl) ⟨717872, by rfl⟩ : syracuseStep 3828653 = 1435745) B1435745
theorem B3107915 : Blo 892572 3107915 := bstep (se 1 (by rfl) ⟨2330936, by rfl⟩ : syracuseStep 3107915 = 4661873) B4661873
theorem B1469593 : Blo 892572 1469593 := bstep (se 2 (by rfl) ⟨551097, by rfl⟩ : syracuseStep 1469593 = 1102195) B1102195
theorem B1698995 : Blo 892572 1698995 := bstep (se 1 (by rfl) ⟨1274246, by rfl⟩ : syracuseStep 1698995 = 2548493) B2548493
theorem B2550977 : Blo 892572 2550977 := bstep (se 2 (by rfl) ⟨956616, by rfl⟩ : syracuseStep 2550977 = 1913233) B1913233
theorem B14150861 : Blo 892572 14150861 := bstep (se 3 (by rfl) ⟨2653286, by rfl⟩ : syracuseStep 14150861 = 5306573) B5306573
theorem B1699147 : Blo 892572 1699147 := bstep (se 1 (by rfl) ⟨1274360, by rfl⟩ : syracuseStep 1699147 = 2548721) B2548721
theorem B1338905 : Blo 892572 1338905 := bstep (se 2 (by rfl) ⟨502089, by rfl⟩ : syracuseStep 1338905 = 1004179) B1004179
theorem B1339019 : Blo 892572 1339019 := bstep (se 1 (by rfl) ⟨1004264, by rfl⟩ : syracuseStep 1339019 = 2008529) B2008529
theorem B1339031 : Blo 892572 1339031 := bstep (se 1 (by rfl) ⟨1004273, by rfl⟩ : syracuseStep 1339031 = 2008547) B2008547
theorem B1273495 : Blo 892572 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B1699481 : Blo 892572 1699481 := bstep (se 2 (by rfl) ⟨637305, by rfl⟩ : syracuseStep 1699481 = 1274611) B1274611
theorem B2420375 : Blo 892572 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B1339097 : Blo 892572 1339097 := bstep (se 2 (by rfl) ⟨502161, by rfl⟩ : syracuseStep 1339097 = 1004323) B1004323
theorem B3403565 : Blo 892572 3403565 := bstep (se 3 (by rfl) ⟨638168, by rfl⟩ : syracuseStep 3403565 = 1276337) B1276337
theorem B1339211 : Blo 892572 1339211 := bstep (se 1 (by rfl) ⟨1004408, by rfl⟩ : syracuseStep 1339211 = 2008817) B2008817
theorem B1339223 : Blo 892572 1339223 := bstep (se 1 (by rfl) ⟨1004417, by rfl⟩ : syracuseStep 1339223 = 2008835) B2008835
theorem B7630685 : Blo 892572 7630685 := bstep (se 3 (by rfl) ⟨1430753, by rfl⟩ : syracuseStep 7630685 = 2861507) B2861507
theorem B1339289 : Blo 892572 1339289 := bstep (se 2 (by rfl) ⟨502233, by rfl⟩ : syracuseStep 1339289 = 1004467) B1004467
theorem B1339403 : Blo 892572 1339403 := bstep (se 1 (by rfl) ⟨1004552, by rfl⟩ : syracuseStep 1339403 = 2009105) B2009105
theorem B1339415 : Blo 892572 1339415 := bstep (se 1 (by rfl) ⟨1004561, by rfl⟩ : syracuseStep 1339415 = 2009123) B2009123
theorem B1339481 : Blo 892572 1339481 := bstep (se 2 (by rfl) ⟨502305, by rfl⟩ : syracuseStep 1339481 = 1004611) B1004611
theorem B13791325 : Blo 892572 13791325 := bstep (se 3 (by rfl) ⟨2585873, by rfl⟩ : syracuseStep 13791325 = 5171747) B5171747
theorem B3436717 : Blo 892572 3436717 := bstep (se 3 (by rfl) ⟨644384, by rfl⟩ : syracuseStep 3436717 = 1288769) B1288769
theorem B1339595 : Blo 892572 1339595 := bstep (se 1 (by rfl) ⟨1004696, by rfl⟩ : syracuseStep 1339595 = 2009393) B2009393
theorem B1274059 : Blo 892572 1274059 := bstep (se 1 (by rfl) ⟨955544, by rfl⟩ : syracuseStep 1274059 = 1911089) B1911089
theorem B1339607 : Blo 892572 1339607 := bstep (se 1 (by rfl) ⟨1004705, by rfl⟩ : syracuseStep 1339607 = 2009411) B2009411
theorem B1241303 : Blo 892572 1241303 := bstep (se 1 (by rfl) ⟨930977, by rfl⟩ : syracuseStep 1241303 = 1861955) B1861955
theorem B1700119 : Blo 892572 1700119 := bstep (se 1 (by rfl) ⟨1275089, by rfl⟩ : syracuseStep 1700119 = 2550179) B2550179
theorem B1339673 : Blo 892572 1339673 := bstep (se 2 (by rfl) ⟨502377, by rfl⟩ : syracuseStep 1339673 = 1004755) B1004755
theorem B1339787 : Blo 892572 1339787 := bstep (se 1 (by rfl) ⟨1004840, by rfl⟩ : syracuseStep 1339787 = 2009681) B2009681
theorem B3436951 : Blo 892572 3436951 := bstep (se 1 (by rfl) ⟨2577713, by rfl⟩ : syracuseStep 3436951 = 5155427) B5155427
theorem B1339799 : Blo 892572 1339799 := bstep (se 1 (by rfl) ⟨1004849, by rfl⟩ : syracuseStep 1339799 = 2009699) B2009699
theorem B1339865 : Blo 892572 1339865 := bstep (se 2 (by rfl) ⟨502449, by rfl⟩ : syracuseStep 1339865 = 1004899) B1004899
theorem B26145251 : Blo 892572 26145251 := bstep (se 1 (by rfl) ⟨19608938, by rfl⟩ : syracuseStep 26145251 = 39217877) B39217877
theorem B1339979 : Blo 892572 1339979 := bstep (se 1 (by rfl) ⟨1004984, by rfl⟩ : syracuseStep 1339979 = 2009969) B2009969
theorem B1339991 : Blo 892572 1339991 := bstep (se 1 (by rfl) ⟨1004993, by rfl⟩ : syracuseStep 1339991 = 2009987) B2009987
theorem B11465347 : Blo 892572 11465347 := bstep (se 1 (by rfl) ⟨8599010, by rfl⟩ : syracuseStep 11465347 = 17198021) B17198021
theorem B1340057 : Blo 892572 1340057 := bstep (se 2 (by rfl) ⟨502521, by rfl⟩ : syracuseStep 1340057 = 1005043) B1005043
theorem B4289203 : Blo 892572 4289203 := bstep (se 1 (by rfl) ⟨3216902, by rfl⟩ : syracuseStep 4289203 = 6433805) B6433805
theorem B1635073 : Blo 892572 1635073 := bstep (se 2 (by rfl) ⟨613152, by rfl⟩ : syracuseStep 1635073 = 1226305) B1226305
theorem B3633923 : Blo 892572 3633923 := bstep (se 1 (by rfl) ⟨2725442, by rfl⟩ : syracuseStep 3633923 = 5450885) B5450885
theorem B1340171 : Blo 892572 1340171 := bstep (se 1 (by rfl) ⟨1005128, by rfl⟩ : syracuseStep 1340171 = 2010257) B2010257
theorem B1340183 : Blo 892572 1340183 := bstep (se 1 (by rfl) ⟨1005137, by rfl⟩ : syracuseStep 1340183 = 2010275) B2010275
theorem B1340249 : Blo 892572 1340249 := bstep (se 2 (by rfl) ⟨502593, by rfl⟩ : syracuseStep 1340249 = 1005187) B1005187
theorem B2421697 : Blo 892572 2421697 := bstep (se 2 (by rfl) ⟨908136, by rfl⟩ : syracuseStep 2421697 = 1816273) B1816273
theorem B1340363 : Blo 892572 1340363 := bstep (se 1 (by rfl) ⟨1005272, by rfl⟩ : syracuseStep 1340363 = 2010545) B2010545
theorem B1340375 : Blo 892572 1340375 := bstep (se 1 (by rfl) ⟨1005281, by rfl⟩ : syracuseStep 1340375 = 2010563) B2010563
theorem B1340441 : Blo 892572 1340441 := bstep (se 2 (by rfl) ⟨502665, by rfl⟩ : syracuseStep 1340441 = 1005331) B1005331
theorem B1700939 : Blo 892572 1700939 := bstep (se 1 (by rfl) ⟨1275704, by rfl⟩ : syracuseStep 1700939 = 2551409) B2551409
theorem B1700993 : Blo 892572 1700993 := bstep (se 2 (by rfl) ⟨637872, by rfl⟩ : syracuseStep 1700993 = 1275745) B1275745
theorem B1340555 : Blo 892572 1340555 := bstep (se 1 (by rfl) ⟨1005416, by rfl⟩ : syracuseStep 1340555 = 2010833) B2010833
theorem B1340567 : Blo 892572 1340567 := bstep (se 1 (by rfl) ⟨1005425, by rfl⟩ : syracuseStep 1340567 = 2010851) B2010851
theorem B1340633 : Blo 892572 1340633 := bstep (se 2 (by rfl) ⟨502737, by rfl⟩ : syracuseStep 1340633 = 1005475) B1005475
theorem B2553049 : Blo 892572 2553049 := bstep (se 2 (by rfl) ⟨957393, by rfl⟩ : syracuseStep 2553049 = 1914787) B1914787
theorem B1340747 : Blo 892572 1340747 := bstep (se 1 (by rfl) ⟨1005560, by rfl⟩ : syracuseStep 1340747 = 2011121) B2011121
theorem B1340759 : Blo 892572 1340759 := bstep (se 1 (by rfl) ⟨1005569, by rfl⟩ : syracuseStep 1340759 = 2011139) B2011139
theorem B2585945 : Blo 892572 2585945 := bstep (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) B1939459
theorem B1340825 : Blo 892572 1340825 := bstep (se 2 (by rfl) ⟨502809, by rfl⟩ : syracuseStep 1340825 = 1005619) B1005619
theorem B1340939 : Blo 892572 1340939 := bstep (se 1 (by rfl) ⟨1005704, by rfl⟩ : syracuseStep 1340939 = 2011409) B2011409
theorem B1340951 : Blo 892572 1340951 := bstep (se 1 (by rfl) ⟨1005713, by rfl⟩ : syracuseStep 1340951 = 2011427) B2011427
theorem B1341017 : Blo 892572 1341017 := bstep (se 2 (by rfl) ⟨502881, by rfl⟩ : syracuseStep 1341017 = 1005763) B1005763
theorem B1275545 : Blo 892572 1275545 := bstep (se 2 (by rfl) ⟨478329, by rfl⟩ : syracuseStep 1275545 = 956659) B956659
theorem B1341131 : Blo 892572 1341131 := bstep (se 1 (by rfl) ⟨1005848, by rfl⟩ : syracuseStep 1341131 = 2011697) B2011697
theorem B1341143 : Blo 892572 1341143 := bstep (se 1 (by rfl) ⟨1005857, by rfl⟩ : syracuseStep 1341143 = 2011715) B2011715
theorem B6616849 : Blo 892572 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B1341209 : Blo 892572 1341209 := bstep (se 2 (by rfl) ⟨502953, by rfl⟩ : syracuseStep 1341209 = 1005907) B1005907
theorem B1341323 : Blo 892572 1341323 := bstep (se 1 (by rfl) ⟨1005992, by rfl⟩ : syracuseStep 1341323 = 2011985) B2011985
theorem B1341335 : Blo 892572 1341335 := bstep (se 1 (by rfl) ⟨1006001, by rfl⟩ : syracuseStep 1341335 = 2012003) B2012003
theorem B1341401 : Blo 892572 1341401 := bstep (se 2 (by rfl) ⟨503025, by rfl⟩ : syracuseStep 1341401 = 1006051) B1006051
theorem B5732369 : Blo 892572 5732369 := bstep (se 2 (by rfl) ⟨2149638, by rfl⟩ : syracuseStep 5732369 = 4299277) B4299277
theorem B1701911 : Blo 892572 1701911 := bstep (se 1 (by rfl) ⟨1276433, by rfl⟩ : syracuseStep 1701911 = 2552867) B2552867
theorem B3012659 : Blo 892572 3012659 := bstep (se 1 (by rfl) ⟨2259494, by rfl⟩ : syracuseStep 3012659 = 4518989) B4518989
theorem B1341515 : Blo 892572 1341515 := bstep (se 1 (by rfl) ⟨1006136, by rfl⟩ : syracuseStep 1341515 = 2012273) B2012273
theorem B1341527 : Blo 892572 1341527 := bstep (se 1 (by rfl) ⟨1006145, by rfl⟩ : syracuseStep 1341527 = 2012291) B2012291
theorem B2586775 : Blo 892572 2586775 := bstep (se 1 (by rfl) ⟨1940081, by rfl⟩ : syracuseStep 2586775 = 3880163) B3880163
theorem B1341593 : Blo 892572 1341593 := bstep (se 2 (by rfl) ⟨503097, by rfl⟩ : syracuseStep 1341593 = 1006195) B1006195
theorem B2291905 : Blo 892572 2291905 := bstep (se 2 (by rfl) ⟨859464, by rfl⟩ : syracuseStep 2291905 = 1718929) B1718929
theorem B9173197 : Blo 892572 9173197 := bstep (se 3 (by rfl) ⟨1719974, by rfl⟩ : syracuseStep 9173197 = 3439949) B3439949
theorem B1341707 : Blo 892572 1341707 := bstep (se 1 (by rfl) ⟨1006280, by rfl⟩ : syracuseStep 1341707 = 2012561) B2012561
theorem B1341719 : Blo 892572 1341719 := bstep (se 1 (by rfl) ⟨1006289, by rfl⟩ : syracuseStep 1341719 = 2012579) B2012579
theorem B1276183 : Blo 892572 1276183 := bstep (se 1 (by rfl) ⟨957137, by rfl⟩ : syracuseStep 1276183 = 1914275) B1914275
theorem B3012929 : Blo 892572 3012929 := bstep (se 2 (by rfl) ⟨1129848, by rfl⟩ : syracuseStep 3012929 = 2259697) B2259697
theorem B1341785 : Blo 892572 1341785 := bstep (se 2 (by rfl) ⟨503169, by rfl⟩ : syracuseStep 1341785 = 1006339) B1006339
theorem B4520285 : Blo 892572 4520285 := bstep (se 3 (by rfl) ⟨847553, by rfl⟩ : syracuseStep 4520285 = 1695107) B1695107
theorem B1341899 : Blo 892572 1341899 := bstep (se 1 (by rfl) ⟨1006424, by rfl⟩ : syracuseStep 1341899 = 2012849) B2012849
theorem B1341911 : Blo 892572 1341911 := bstep (se 1 (by rfl) ⟨1006433, by rfl⟩ : syracuseStep 1341911 = 2012867) B2012867
theorem B1341977 : Blo 892572 1341977 := bstep (se 2 (by rfl) ⟨503241, by rfl⟩ : syracuseStep 1341977 = 1006483) B1006483
theorem B12909131 : Blo 892572 12909131 := bstep (se 1 (by rfl) ⟨9681848, by rfl⟩ : syracuseStep 12909131 = 19363697) B19363697
theorem B1342091 : Blo 892572 1342091 := bstep (se 1 (by rfl) ⟨1006568, by rfl⟩ : syracuseStep 1342091 = 2013137) B2013137
theorem B4127383 : Blo 892572 4127383 := bstep (se 1 (by rfl) ⟨3095537, by rfl⟩ : syracuseStep 4127383 = 6191075) B6191075
theorem B1342103 : Blo 892572 1342103 := bstep (se 1 (by rfl) ⟨1006577, by rfl⟩ : syracuseStep 1342103 = 2013155) B2013155
theorem B2423447 : Blo 892572 2423447 := bstep (se 1 (by rfl) ⟨1817585, by rfl⟩ : syracuseStep 2423447 = 3635171) B3635171
theorem B1342169 : Blo 892572 1342169 := bstep (se 2 (by rfl) ⟨503313, by rfl⟩ : syracuseStep 1342169 = 1006627) B1006627
theorem B1145675 : Blo 892572 1145675 := bstep (se 1 (by rfl) ⟨859256, by rfl⟩ : syracuseStep 1145675 = 1718513) B1718513
theorem B1342283 : Blo 892572 1342283 := bstep (se 1 (by rfl) ⟨1006712, by rfl⟩ : syracuseStep 1342283 = 2013425) B2013425
theorem B1342295 : Blo 892572 1342295 := bstep (se 1 (by rfl) ⟨1006721, by rfl⟩ : syracuseStep 1342295 = 2013443) B2013443
theorem B3013469 : Blo 892572 3013469 := bstep (se 3 (by rfl) ⟨565025, by rfl⟩ : syracuseStep 3013469 = 1130051) B1130051
theorem B1342361 : Blo 892572 1342361 := bstep (se 2 (by rfl) ⟨503385, by rfl⟩ : syracuseStep 1342361 = 1006771) B1006771
theorem B66059225 : Blo 892572 66059225 := bstep (se 2 (by rfl) ⟨24772209, by rfl⟩ : syracuseStep 66059225 = 49544419) B49544419
theorem B1342475 : Blo 892572 1342475 := bstep (se 1 (by rfl) ⟨1006856, by rfl⟩ : syracuseStep 1342475 = 2013713) B2013713
theorem B1342487 : Blo 892572 1342487 := bstep (se 1 (by rfl) ⟨1006865, by rfl⟩ : syracuseStep 1342487 = 2013731) B2013731
theorem B1342553 : Blo 892572 1342553 := bstep (se 2 (by rfl) ⟨503457, by rfl⟩ : syracuseStep 1342553 = 1006915) B1006915
theorem B1932427 : Blo 892572 1932427 := bstep (se 1 (by rfl) ⟨1449320, by rfl⟩ : syracuseStep 1932427 = 2898641) B2898641
theorem B6782129 : Blo 892572 6782129 := bstep (se 2 (by rfl) ⟨2543298, by rfl⟩ : syracuseStep 6782129 = 5086597) B5086597
theorem B1342667 : Blo 892572 1342667 := bstep (se 1 (by rfl) ⟨1007000, by rfl⟩ : syracuseStep 1342667 = 2014001) B2014001
theorem B1342679 : Blo 892572 1342679 := bstep (se 1 (by rfl) ⟨1007009, by rfl⟩ : syracuseStep 1342679 = 2014019) B2014019
theorem B1342745 : Blo 892572 1342745 := bstep (se 2 (by rfl) ⟨503529, by rfl⟩ : syracuseStep 1342745 = 1007059) B1007059
theorem B1506647 : Blo 892572 1506647 := bstep (se 1 (by rfl) ⟨1129985, by rfl⟩ : syracuseStep 1506647 = 2259971) B2259971
theorem B1342859 : Blo 892572 1342859 := bstep (se 1 (by rfl) ⟨1007144, by rfl⟩ : syracuseStep 1342859 = 2014289) B2014289
theorem B1342871 : Blo 892572 1342871 := bstep (se 1 (by rfl) ⟨1007153, by rfl⟩ : syracuseStep 1342871 = 2014307) B2014307
theorem B1506775 : Blo 892572 1506775 := bstep (se 1 (by rfl) ⟨1130081, by rfl⟩ : syracuseStep 1506775 = 2260163) B2260163
theorem B1342937 : Blo 892572 1342937 := bstep (se 2 (by rfl) ⟨503601, by rfl⟩ : syracuseStep 1342937 = 1007203) B1007203
theorem B1343051 : Blo 892572 1343051 := bstep (se 1 (by rfl) ⟨1007288, by rfl⟩ : syracuseStep 1343051 = 2014577) B2014577
theorem B1343063 : Blo 892572 1343063 := bstep (se 1 (by rfl) ⟨1007297, by rfl⟩ : syracuseStep 1343063 = 2014595) B2014595
theorem B6782615 : Blo 892572 6782615 := bstep (se 1 (by rfl) ⟨5086961, by rfl⟩ : syracuseStep 6782615 = 10173923) B10173923
theorem B1343129 : Blo 892572 1343129 := bstep (se 2 (by rfl) ⟨503673, by rfl⟩ : syracuseStep 1343129 = 1007347) B1007347
theorem B1343243 : Blo 892572 1343243 := bstep (se 1 (by rfl) ⟨1007432, by rfl⟩ : syracuseStep 1343243 = 2014865) B2014865
theorem B1343255 : Blo 892572 1343255 := bstep (se 1 (by rfl) ⟨1007441, by rfl⟩ : syracuseStep 1343255 = 2014883) B2014883
theorem B2260811 : Blo 892572 2260811 := bstep (se 1 (by rfl) ⟨1695608, by rfl⟩ : syracuseStep 2260811 = 3391217) B3391217
theorem B1343321 : Blo 892572 1343321 := bstep (se 2 (by rfl) ⟨503745, by rfl⟩ : syracuseStep 1343321 = 1007491) B1007491
theorem B3014603 : Blo 892572 3014603 := bstep (se 1 (by rfl) ⟨2260952, by rfl⟩ : syracuseStep 3014603 = 4521905) B4521905
theorem B1343435 : Blo 892572 1343435 := bstep (se 1 (by rfl) ⟨1007576, by rfl⟩ : syracuseStep 1343435 = 2015153) B2015153
theorem B1343447 : Blo 892572 1343447 := bstep (se 1 (by rfl) ⟨1007585, by rfl⟩ : syracuseStep 1343447 = 2015171) B2015171
theorem B2260993 : Blo 892572 2260993 := bstep (se 2 (by rfl) ⟨847872, by rfl⟩ : syracuseStep 2260993 = 1695745) B1695745
theorem B4587523 : Blo 892572 4587523 := bstep (se 1 (by rfl) ⟨3440642, by rfl⟩ : syracuseStep 4587523 = 6881285) B6881285
theorem B1343495 : Blo 892572 1343495 := bstep (se 1 (by rfl) ⟨1007621, by rfl⟩ : syracuseStep 1343495 = 2015243) B2015243
theorem B1343531 : Blo 892572 1343531 := bstep (se 1 (by rfl) ⟨1007648, by rfl⟩ : syracuseStep 1343531 = 2015297) B2015297
theorem B1343561 : Blo 892572 1343561 := bstep (se 2 (by rfl) ⟨503835, by rfl⟩ : syracuseStep 1343561 = 1007671) B1007671
theorem B2293879 : Blo 892572 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B1343675 : Blo 892572 1343675 := bstep (se 1 (by rfl) ⟨1007756, by rfl⟩ : syracuseStep 1343675 = 2015513) B2015513
theorem B1343735 : Blo 892572 1343735 := bstep (se 1 (by rfl) ⟨1007801, by rfl⟩ : syracuseStep 1343735 = 2015603) B2015603
theorem B3014927 : Blo 892572 3014927 := bstep (se 1 (by rfl) ⟨2261195, by rfl⟩ : syracuseStep 3014927 = 4522391) B4522391
theorem B1343759 : Blo 892572 1343759 := bstep (se 1 (by rfl) ⟨1007819, by rfl⟩ : syracuseStep 1343759 = 2015639) B2015639
theorem B1343801 : Blo 892572 1343801 := bstep (se 2 (by rfl) ⟨503925, by rfl⟩ : syracuseStep 1343801 = 1007851) B1007851
theorem B1343879 : Blo 892572 1343879 := bstep (se 1 (by rfl) ⟨1007909, by rfl⟩ : syracuseStep 1343879 = 2015819) B2015819
theorem B1343915 : Blo 892572 1343915 := bstep (se 1 (by rfl) ⟨1007936, by rfl⟩ : syracuseStep 1343915 = 2015873) B2015873
theorem B1343945 : Blo 892572 1343945 := bstep (se 2 (by rfl) ⟨503979, by rfl⟩ : syracuseStep 1343945 = 1007959) B1007959
theorem B1507855 : Blo 892572 1507855 := bstep (se 1 (by rfl) ⟨1130891, by rfl⟩ : syracuseStep 1507855 = 2261783) B2261783
theorem B3015197 : Blo 892572 3015197 := bstep (se 3 (by rfl) ⟨565349, by rfl⟩ : syracuseStep 3015197 = 1130699) B1130699
theorem B1344059 : Blo 892572 1344059 := bstep (se 1 (by rfl) ⟨1008044, by rfl⟩ : syracuseStep 1344059 = 2016089) B2016089
theorem B3310141 : Blo 892572 3310141 := bstep (se 3 (by rfl) ⟨620651, by rfl⟩ : syracuseStep 3310141 = 1241303) B1241303
theorem B2261591 : Blo 892572 2261591 := bstep (se 1 (by rfl) ⟨1696193, by rfl⟩ : syracuseStep 2261591 = 3392387) B3392387
theorem B1344119 : Blo 892572 1344119 := bstep (se 1 (by rfl) ⟨1008089, by rfl⟩ : syracuseStep 1344119 = 2016179) B2016179
theorem B1344143 : Blo 892572 1344143 := bstep (se 1 (by rfl) ⟨1008107, by rfl⟩ : syracuseStep 1344143 = 2016215) B2016215
theorem B2294419 : Blo 892572 2294419 := bstep (se 1 (by rfl) ⟨1720814, by rfl⟩ : syracuseStep 2294419 = 3441629) B3441629
theorem B1344185 : Blo 892572 1344185 := bstep (se 2 (by rfl) ⟨504069, by rfl⟩ : syracuseStep 1344185 = 1008139) B1008139
theorem B1344263 : Blo 892572 1344263 := bstep (se 1 (by rfl) ⟨1008197, by rfl⟩ : syracuseStep 1344263 = 2016395) B2016395
theorem B2261803 : Blo 892572 2261803 := bstep (se 1 (by rfl) ⟨1696352, by rfl⟩ : syracuseStep 2261803 = 3392705) B3392705
theorem B1344299 : Blo 892572 1344299 := bstep (se 1 (by rfl) ⟨1008224, by rfl⟩ : syracuseStep 1344299 = 2016449) B2016449
theorem B4653883 : Blo 892572 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B1344329 : Blo 892572 1344329 := bstep (se 2 (by rfl) ⟨504123, by rfl⟩ : syracuseStep 1344329 = 1008247) B1008247
theorem B6456179 : Blo 892572 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B2261945 : Blo 892572 2261945 := bstep (se 2 (by rfl) ⟨848229, by rfl⟩ : syracuseStep 2261945 = 1696459) B1696459
theorem B1344443 : Blo 892572 1344443 := bstep (se 1 (by rfl) ⟨1008332, by rfl⟩ : syracuseStep 1344443 = 2016665) B2016665
theorem B1344503 : Blo 892572 1344503 := bstep (se 1 (by rfl) ⟨1008377, by rfl⟩ : syracuseStep 1344503 = 2016755) B2016755
theorem B12223493 : Blo 892572 12223493 := bstep (se 4 (by rfl) ⟨1145952, by rfl⟩ : syracuseStep 12223493 = 2291905) B2291905
theorem B1344527 : Blo 892572 1344527 := bstep (se 1 (by rfl) ⟨1008395, by rfl⟩ : syracuseStep 1344527 = 2016791) B2016791
theorem B1508395 : Blo 892572 1508395 := bstep (se 1 (by rfl) ⟨1131296, by rfl⟩ : syracuseStep 1508395 = 2262593) B2262593
theorem B1344569 : Blo 892572 1344569 := bstep (se 2 (by rfl) ⟨504213, by rfl⟩ : syracuseStep 1344569 = 1008427) B1008427
theorem B1344647 : Blo 892572 1344647 := bstep (se 1 (by rfl) ⟨1008485, by rfl⟩ : syracuseStep 1344647 = 2016971) B2016971
theorem B1344683 : Blo 892572 1344683 := bstep (se 1 (by rfl) ⟨1008512, by rfl⟩ : syracuseStep 1344683 = 2017025) B2017025
theorem B1508537 : Blo 892572 1508537 := bstep (se 2 (by rfl) ⟨565701, by rfl⟩ : syracuseStep 1508537 = 1131403) B1131403
theorem B4523201 : Blo 892572 4523201 := bstep (se 2 (by rfl) ⟨1696200, by rfl⟩ : syracuseStep 4523201 = 3392401) B3392401
theorem B1344713 : Blo 892572 1344713 := bstep (se 2 (by rfl) ⟨504267, by rfl⟩ : syracuseStep 1344713 = 1008535) B1008535
theorem B1344827 : Blo 892572 1344827 := bstep (se 1 (by rfl) ⟨1008620, by rfl⟩ : syracuseStep 1344827 = 2017241) B2017241
theorem B6457103 : Blo 892572 6457103 := bstep (se 1 (by rfl) ⟨4842827, by rfl⟩ : syracuseStep 6457103 = 9685655) B9685655
theorem B1509239 : Blo 892572 1509239 := bstep (se 1 (by rfl) ⟨1131929, by rfl⟩ : syracuseStep 1509239 = 2263859) B2263859
theorem B3016601 : Blo 892572 3016601 := bstep (se 2 (by rfl) ⟨1131225, by rfl⟩ : syracuseStep 3016601 = 2262451) B2262451
theorem B2262937 : Blo 892572 2262937 := bstep (se 2 (by rfl) ⟨848601, by rfl⟩ : syracuseStep 2262937 = 1697203) B1697203
theorem B1378361 : Blo 892572 1378361 := bstep (se 2 (by rfl) ⟨516885, by rfl⟩ : syracuseStep 1378361 = 1033771) B1033771
theorem B2263099 : Blo 892572 2263099 := bstep (se 1 (by rfl) ⟨1697324, by rfl⟩ : syracuseStep 2263099 = 3394649) B3394649
theorem B6522967 : Blo 892572 6522967 := bstep (se 1 (by rfl) ⟨4892225, by rfl⟩ : syracuseStep 6522967 = 9784451) B9784451
theorem B2263241 : Blo 892572 2263241 := bstep (se 2 (by rfl) ⟨848715, by rfl⟩ : syracuseStep 2263241 = 1697431) B1697431
theorem B1509691 : Blo 892572 1509691 := bstep (se 1 (by rfl) ⟨1132268, by rfl⟩ : syracuseStep 1509691 = 2264537) B2264537
theorem B1509833 : Blo 892572 1509833 := bstep (se 2 (by rfl) ⟨566187, by rfl⟩ : syracuseStep 1509833 = 1132375) B1132375
theorem B4524497 : Blo 892572 4524497 := bstep (se 2 (by rfl) ⟨1696686, by rfl⟩ : syracuseStep 4524497 = 3393373) B3393373
theorem B2263585 : Blo 892572 2263585 := bstep (se 2 (by rfl) ⟨848844, by rfl⟩ : syracuseStep 2263585 = 1697689) B1697689
theorem B3017303 : Blo 892572 3017303 := bstep (se 1 (by rfl) ⟨2262977, by rfl⟩ : syracuseStep 3017303 = 4525955) B4525955
theorem B2296505 : Blo 892572 2296505 := bstep (se 2 (by rfl) ⟨861189, by rfl⟩ : syracuseStep 2296505 = 1722379) B1722379
theorem B11471705 : Blo 892572 11471705 := bstep (se 2 (by rfl) ⟨4301889, by rfl⟩ : syracuseStep 11471705 = 8603779) B8603779
theorem B3017789 : Blo 892572 3017789 := bstep (se 3 (by rfl) ⟨565835, by rfl⟩ : syracuseStep 3017789 = 1131671) B1131671
theorem B2264183 : Blo 892572 2264183 := bstep (se 1 (by rfl) ⟨1698137, by rfl⟩ : syracuseStep 2264183 = 3396275) B3396275
theorem B1510535 : Blo 892572 1510535 := bstep (se 1 (by rfl) ⟨1132901, by rfl⟩ : syracuseStep 1510535 = 2265803) B2265803
theorem B6131153 : Blo 892572 6131153 := bstep (se 2 (by rfl) ⟨2299182, by rfl⟩ : syracuseStep 6131153 = 4598365) B4598365
theorem B8589017 : Blo 892572 8589017 := bstep (se 2 (by rfl) ⟨3220881, by rfl⟩ : syracuseStep 8589017 = 6441763) B6441763
theorem B1511183 : Blo 892572 1511183 := bstep (se 1 (by rfl) ⟨1133387, by rfl⟩ : syracuseStep 1511183 = 2266775) B2266775
theorem B8720389 : Blo 892572 8720389 := bstep (se 4 (by rfl) ⟨817536, by rfl⟩ : syracuseStep 8720389 = 1635073) B1635073
theorem B15274007 : Blo 892572 15274007 := bstep (se 1 (by rfl) ⟨11455505, by rfl⟩ : syracuseStep 15274007 = 22911011) B22911011
theorem B61870321 : Blo 892572 61870321 := bstep (se 2 (by rfl) ⟨23201370, by rfl⟩ : syracuseStep 61870321 = 46402741) B46402741
theorem B1511723 : Blo 892572 1511723 := bstep (se 1 (by rfl) ⟨1133792, by rfl⟩ : syracuseStep 1511723 = 2267585) B2267585
theorem B2265479 : Blo 892572 2265479 := bstep (se 1 (by rfl) ⟨1699109, by rfl⟩ : syracuseStep 2265479 = 3398219) B3398219
theorem B6787475 : Blo 892572 6787475 := bstep (se 1 (by rfl) ⟨5090606, by rfl⟩ : syracuseStep 6787475 = 10181213) B10181213
theorem B3019193 : Blo 892572 3019193 := bstep (se 2 (by rfl) ⟨1132197, by rfl⟩ : syracuseStep 3019193 = 2264395) B2264395
theorem B2265529 : Blo 892572 2265529 := bstep (se 2 (by rfl) ⟨849573, by rfl⟩ : syracuseStep 2265529 = 1699147) B1699147
theorem B4526603 : Blo 892572 4526603 := bstep (se 1 (by rfl) ⟨3394952, by rfl⟩ : syracuseStep 4526603 = 6789905) B6789905
theorem B4526765 : Blo 892572 4526765 := bstep (se 3 (by rfl) ⟨848768, by rfl⟩ : syracuseStep 4526765 = 1697537) B1697537
theorem B1512121 : Blo 892572 1512121 := bstep (se 2 (by rfl) ⟨567045, by rfl⟩ : syracuseStep 1512121 = 1134091) B1134091
theorem B5083955 : Blo 892572 5083955 := bstep (se 1 (by rfl) ⟨3812966, by rfl⟩ : syracuseStep 5083955 = 7625933) B7625933
theorem B1020731 : Blo 892572 1020731 := bstep (se 1 (by rfl) ⟨765548, by rfl⟩ : syracuseStep 1020731 = 1531097) B1531097
theorem B955271 : Blo 892572 955271 := bstep (se 1 (by rfl) ⟨716453, by rfl⟩ : syracuseStep 955271 = 1432907) B1432907
theorem B2724761 : Blo 892572 2724761 := bstep (se 2 (by rfl) ⟨1021785, by rfl⟩ : syracuseStep 2724761 = 2043571) B2043571
theorem B16290827 : Blo 892572 16290827 := bstep (se 1 (by rfl) ⟨12218120, by rfl⟩ : syracuseStep 16290827 = 24436241) B24436241
theorem B3019787 : Blo 892572 3019787 := bstep (se 1 (by rfl) ⟨2264840, by rfl⟩ : syracuseStep 3019787 = 4529681) B4529681
theorem B2266127 : Blo 892572 2266127 := bstep (se 1 (by rfl) ⟨1699595, by rfl⟩ : syracuseStep 2266127 = 3399191) B3399191
theorem B3019895 : Blo 892572 3019895 := bstep (se 1 (by rfl) ⟨2264921, by rfl⟩ : syracuseStep 3019895 = 4529843) B4529843
theorem B1381691 : Blo 892572 1381691 := bstep (se 1 (by rfl) ⟨1036268, by rfl⟩ : syracuseStep 1381691 = 2072537) B2072537
theorem B1512823 : Blo 892572 1512823 := bstep (se 1 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 1512823 = 2269235) B2269235
theorem B18388433 : Blo 892572 18388433 := bstep (se 2 (by rfl) ⟨6895662, by rfl⟩ : syracuseStep 18388433 = 13791325) B13791325
theorem B2037449 : Blo 892572 2037449 := bstep (se 2 (by rfl) ⟨764043, by rfl⟩ : syracuseStep 2037449 = 1528087) B1528087
theorem B3020489 : Blo 892572 3020489 := bstep (se 2 (by rfl) ⟨1132683, by rfl⟩ : syracuseStep 3020489 = 2265367) B2265367
theorem B2266825 : Blo 892572 2266825 := bstep (se 2 (by rfl) ⟨850059, by rfl⟩ : syracuseStep 2266825 = 1700119) B1700119
theorem B2266967 : Blo 892572 2266967 := bstep (se 1 (by rfl) ⟨1700225, by rfl⟩ : syracuseStep 2266967 = 3400451) B3400451
theorem B5085413 : Blo 892572 5085413 := bstep (se 4 (by rfl) ⟨476757, by rfl⟩ : syracuseStep 5085413 = 953515) B953515
theorem B4528385 : Blo 892572 4528385 := bstep (se 2 (by rfl) ⟨1698144, by rfl⟩ : syracuseStep 4528385 = 3396289) B3396289
theorem B3021191 : Blo 892572 3021191 := bstep (se 1 (by rfl) ⟨2265893, by rfl⟩ : syracuseStep 3021191 = 4531787) B4531787
theorem B8591939 : Blo 892572 8591939 := bstep (se 1 (by rfl) ⟨6443954, by rfl⟩ : syracuseStep 8591939 = 12887909) B12887909
theorem B3021569 : Blo 892572 3021569 := bstep (se 2 (by rfl) ⟨1133088, by rfl⟩ : syracuseStep 3021569 = 2266177) B2266177
theorem B5086097 : Blo 892572 5086097 := bstep (se 2 (by rfl) ⟨1907286, by rfl⟩ : syracuseStep 5086097 = 3814573) B3814573
theorem B2759681 : Blo 892572 2759681 := bstep (se 2 (by rfl) ⟨1034880, by rfl⟩ : syracuseStep 2759681 = 2069761) B2069761
theorem B4529195 : Blo 892572 4529195 := bstep (se 1 (by rfl) ⟨3396896, by rfl⟩ : syracuseStep 4529195 = 6793793) B6793793
theorem B3218633 : Blo 892572 3218633 := bstep (se 2 (by rfl) ⟨1206987, by rfl⟩ : syracuseStep 3218633 = 2413975) B2413975
theorem B1809697 : Blo 892572 1809697 := bstep (se 2 (by rfl) ⟨678636, by rfl⟩ : syracuseStep 1809697 = 1357273) B1357273
theorem B4300121 : Blo 892572 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B2071943 : Blo 892572 2071943 := bstep (se 1 (by rfl) ⟨1553957, by rfl⟩ : syracuseStep 2071943 = 3107915) B3107915
theorem B3055133 : Blo 892572 3055133 := bstep (se 3 (by rfl) ⟨572837, by rfl⟩ : syracuseStep 3055133 = 1145675) B1145675
theorem B3022379 : Blo 892572 3022379 := bstep (se 1 (by rfl) ⟨2266784, by rfl⟩ : syracuseStep 3022379 = 4533569) B4533569
theorem B892603 : Blo 892572 892603 := bstep (se 1 (by rfl) ⟨669452, by rfl⟩ : syracuseStep 892603 = 1338905) B1338905
theorem B8822465 : Blo 892572 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B892679 : Blo 892572 892679 := bstep (se 1 (by rfl) ⟨669509, by rfl⟩ : syracuseStep 892679 = 1339019) B1339019
theorem B892687 : Blo 892572 892687 := bstep (se 1 (by rfl) ⟨669515, by rfl⟩ : syracuseStep 892687 = 1339031) B1339031
theorem B892731 : Blo 892572 892731 := bstep (se 1 (by rfl) ⟨669548, by rfl⟩ : syracuseStep 892731 = 1339097) B1339097
theorem B2269043 : Blo 892572 2269043 := bstep (se 1 (by rfl) ⟨1701782, by rfl⟩ : syracuseStep 2269043 = 3403565) B3403565
theorem B892807 : Blo 892572 892807 := bstep (se 1 (by rfl) ⟨669605, by rfl⟩ : syracuseStep 892807 = 1339211) B1339211
theorem B892815 : Blo 892572 892815 := bstep (se 1 (by rfl) ⟨669611, by rfl⟩ : syracuseStep 892815 = 1339223) B1339223
theorem B5087123 : Blo 892572 5087123 := bstep (se 1 (by rfl) ⟨3815342, by rfl⟩ : syracuseStep 5087123 = 7630685) B7630685
theorem B892859 : Blo 892572 892859 := bstep (se 1 (by rfl) ⟨669644, by rfl⟩ : syracuseStep 892859 = 1339289) B1339289
theorem B39264203 : Blo 892572 39264203 := bstep (se 1 (by rfl) ⟨29448152, by rfl⟩ : syracuseStep 39264203 = 58896305) B58896305
theorem B892935 : Blo 892572 892935 := bstep (se 1 (by rfl) ⟨669701, by rfl⟩ : syracuseStep 892935 = 1339403) B1339403
theorem B892943 : Blo 892572 892943 := bstep (se 1 (by rfl) ⟨669707, by rfl⟩ : syracuseStep 892943 = 1339415) B1339415
theorem B892987 : Blo 892572 892987 := bstep (se 1 (by rfl) ⟨669740, by rfl⟩ : syracuseStep 892987 = 1339481) B1339481
theorem B893063 : Blo 892572 893063 := bstep (se 1 (by rfl) ⟨669797, by rfl⟩ : syracuseStep 893063 = 1339595) B1339595
theorem B893071 : Blo 892572 893071 := bstep (se 1 (by rfl) ⟨669803, by rfl⟩ : syracuseStep 893071 = 1339607) B1339607
theorem B893115 : Blo 892572 893115 := bstep (se 1 (by rfl) ⟨669836, by rfl⟩ : syracuseStep 893115 = 1339673) B1339673
theorem B3449033 : Blo 892572 3449033 := bstep (se 2 (by rfl) ⟨1293387, by rfl⟩ : syracuseStep 3449033 = 2586775) B2586775
theorem B893191 : Blo 892572 893191 := bstep (se 1 (by rfl) ⟨669893, by rfl⟩ : syracuseStep 893191 = 1339787) B1339787
theorem B893199 : Blo 892572 893199 := bstep (se 1 (by rfl) ⟨669899, by rfl⟩ : syracuseStep 893199 = 1339799) B1339799
theorem B12230929 : Blo 892572 12230929 := bstep (se 2 (by rfl) ⟨4586598, by rfl⟩ : syracuseStep 12230929 = 9173197) B9173197
theorem B893243 : Blo 892572 893243 := bstep (se 1 (by rfl) ⟨669932, by rfl⟩ : syracuseStep 893243 = 1339865) B1339865
theorem B4530491 : Blo 892572 4530491 := bstep (se 1 (by rfl) ⟨3397868, by rfl⟩ : syracuseStep 4530491 = 6795737) B6795737
theorem B893319 : Blo 892572 893319 := bstep (se 1 (by rfl) ⟨669989, by rfl⟩ : syracuseStep 893319 = 1339979) B1339979
theorem B893327 : Blo 892572 893327 := bstep (se 1 (by rfl) ⟨669995, by rfl⟩ : syracuseStep 893327 = 1339991) B1339991
theorem B893371 : Blo 892572 893371 := bstep (se 1 (by rfl) ⟨670028, by rfl⟩ : syracuseStep 893371 = 1340057) B1340057
theorem B4530653 : Blo 892572 4530653 := bstep (se 3 (by rfl) ⟨849497, by rfl⟩ : syracuseStep 4530653 = 1698995) B1698995
theorem B893447 : Blo 892572 893447 := bstep (se 1 (by rfl) ⟨670085, by rfl⟩ : syracuseStep 893447 = 1340171) B1340171
theorem B893455 : Blo 892572 893455 := bstep (se 1 (by rfl) ⟨670091, by rfl⟩ : syracuseStep 893455 = 1340183) B1340183
theorem B893499 : Blo 892572 893499 := bstep (se 1 (by rfl) ⟨670124, by rfl⟩ : syracuseStep 893499 = 1340249) B1340249
theorem B893575 : Blo 892572 893575 := bstep (se 1 (by rfl) ⟨670181, by rfl⟩ : syracuseStep 893575 = 1340363) B1340363
theorem B893583 : Blo 892572 893583 := bstep (se 1 (by rfl) ⟨670187, by rfl⟩ : syracuseStep 893583 = 1340375) B1340375
theorem B893627 : Blo 892572 893627 := bstep (se 1 (by rfl) ⟨670220, by rfl⟩ : syracuseStep 893627 = 1340441) B1340441
theorem B893703 : Blo 892572 893703 := bstep (se 1 (by rfl) ⟨670277, by rfl⟩ : syracuseStep 893703 = 1340555) B1340555
theorem B893711 : Blo 892572 893711 := bstep (se 1 (by rfl) ⟨670283, by rfl⟩ : syracuseStep 893711 = 1340567) B1340567
theorem B4530977 : Blo 892572 4530977 := bstep (se 2 (by rfl) ⟨1699116, by rfl⟩ : syracuseStep 4530977 = 3398233) B3398233
theorem B893755 : Blo 892572 893755 := bstep (se 1 (by rfl) ⟨670316, by rfl⟩ : syracuseStep 893755 = 1340633) B1340633
theorem B3023675 : Blo 892572 3023675 := bstep (se 1 (by rfl) ⟨2267756, by rfl⟩ : syracuseStep 3023675 = 4535513) B4535513
theorem B893831 : Blo 892572 893831 := bstep (se 1 (by rfl) ⟨670373, by rfl⟩ : syracuseStep 893831 = 1340747) B1340747
theorem B893839 : Blo 892572 893839 := bstep (se 1 (by rfl) ⟨670379, by rfl⟩ : syracuseStep 893839 = 1340759) B1340759
theorem B893883 : Blo 892572 893883 := bstep (se 1 (by rfl) ⟨670412, by rfl⟩ : syracuseStep 893883 = 1340825) B1340825
theorem B893959 : Blo 892572 893959 := bstep (se 1 (by rfl) ⟨670469, by rfl⟩ : syracuseStep 893959 = 1340939) B1340939
theorem B893967 : Blo 892572 893967 := bstep (se 1 (by rfl) ⟨670475, by rfl⟩ : syracuseStep 893967 = 1340951) B1340951
theorem B894011 : Blo 892572 894011 := bstep (se 1 (by rfl) ⟨670508, by rfl⟩ : syracuseStep 894011 = 1341017) B1341017
theorem B894087 : Blo 892572 894087 := bstep (se 1 (by rfl) ⟨670565, by rfl⟩ : syracuseStep 894087 = 1341131) B1341131
theorem B894095 : Blo 892572 894095 := bstep (se 1 (by rfl) ⟨670571, by rfl⟩ : syracuseStep 894095 = 1341143) B1341143
theorem B894139 : Blo 892572 894139 := bstep (se 1 (by rfl) ⟨670604, by rfl⟩ : syracuseStep 894139 = 1341209) B1341209
theorem B2860289 : Blo 892572 2860289 := bstep (se 2 (by rfl) ⟨1072608, by rfl⟩ : syracuseStep 2860289 = 2145217) B2145217
theorem B894215 : Blo 892572 894215 := bstep (se 1 (by rfl) ⟨670661, by rfl⟩ : syracuseStep 894215 = 1341323) B1341323
theorem B894223 : Blo 892572 894223 := bstep (se 1 (by rfl) ⟨670667, by rfl⟩ : syracuseStep 894223 = 1341335) B1341335
theorem B3024161 : Blo 892572 3024161 := bstep (se 2 (by rfl) ⟨1134060, by rfl⟩ : syracuseStep 3024161 = 2268121) B2268121
theorem B894267 : Blo 892572 894267 := bstep (se 1 (by rfl) ⟨670700, by rfl⟩ : syracuseStep 894267 = 1341401) B1341401
theorem B2008439 : Blo 892572 2008439 := bstep (se 1 (by rfl) ⟨1506329, by rfl⟩ : syracuseStep 2008439 = 3012659) B3012659
theorem B894343 : Blo 892572 894343 := bstep (se 1 (by rfl) ⟨670757, by rfl⟩ : syracuseStep 894343 = 1341515) B1341515
theorem B894351 : Blo 892572 894351 := bstep (se 1 (by rfl) ⟨670763, by rfl⟩ : syracuseStep 894351 = 1341527) B1341527
theorem B894395 : Blo 892572 894395 := bstep (se 1 (by rfl) ⟨670796, by rfl⟩ : syracuseStep 894395 = 1341593) B1341593
theorem B894471 : Blo 892572 894471 := bstep (se 1 (by rfl) ⟨670853, by rfl⟩ : syracuseStep 894471 = 1341707) B1341707
theorem B894479 : Blo 892572 894479 := bstep (se 1 (by rfl) ⟨670859, by rfl⟩ : syracuseStep 894479 = 1341719) B1341719
theorem B2008619 : Blo 892572 2008619 := bstep (se 1 (by rfl) ⟨1506464, by rfl⟩ : syracuseStep 2008619 = 3012929) B3012929
theorem B894523 : Blo 892572 894523 := bstep (se 1 (by rfl) ⟨670892, by rfl⟩ : syracuseStep 894523 = 1341785) B1341785
theorem B894599 : Blo 892572 894599 := bstep (se 1 (by rfl) ⟨670949, by rfl⟩ : syracuseStep 894599 = 1341899) B1341899
theorem B894607 : Blo 892572 894607 := bstep (se 1 (by rfl) ⟨670955, by rfl⟩ : syracuseStep 894607 = 1341911) B1341911
theorem B894651 : Blo 892572 894651 := bstep (se 1 (by rfl) ⟨670988, by rfl⟩ : syracuseStep 894651 = 1341977) B1341977
theorem B4531949 : Blo 892572 4531949 := bstep (se 3 (by rfl) ⟨849740, by rfl⟩ : syracuseStep 4531949 = 1699481) B1699481
theorem B894727 : Blo 892572 894727 := bstep (se 1 (by rfl) ⟨671045, by rfl⟩ : syracuseStep 894727 = 1342091) B1342091
theorem B894735 : Blo 892572 894735 := bstep (se 1 (by rfl) ⟨671051, by rfl⟩ : syracuseStep 894735 = 1342103) B1342103
theorem B1615631 : Blo 892572 1615631 := bstep (se 1 (by rfl) ⟨1211723, by rfl⟩ : syracuseStep 1615631 = 2423447) B2423447
theorem B11478833 : Blo 892572 11478833 := bstep (se 2 (by rfl) ⟨4304562, by rfl⟩ : syracuseStep 11478833 = 8609125) B8609125
theorem B894779 : Blo 892572 894779 := bstep (se 1 (by rfl) ⟨671084, by rfl⟩ : syracuseStep 894779 = 1342169) B1342169
theorem B3024755 : Blo 892572 3024755 := bstep (se 1 (by rfl) ⟨2268566, by rfl⟩ : syracuseStep 3024755 = 4537133) B4537133
theorem B894855 : Blo 892572 894855 := bstep (se 1 (by rfl) ⟨671141, by rfl⟩ : syracuseStep 894855 = 1342283) B1342283
theorem B894863 : Blo 892572 894863 := bstep (se 1 (by rfl) ⟨671147, by rfl⟩ : syracuseStep 894863 = 1342295) B1342295
theorem B2008979 : Blo 892572 2008979 := bstep (se 1 (by rfl) ⟨1506734, by rfl⟩ : syracuseStep 2008979 = 3013469) B3013469
theorem B894907 : Blo 892572 894907 := bstep (se 1 (by rfl) ⟨671180, by rfl⟩ : syracuseStep 894907 = 1342361) B1342361
theorem B2009033 : Blo 892572 2009033 := bstep (se 2 (by rfl) ⟨753387, by rfl⟩ : syracuseStep 2009033 = 1506775) B1506775
theorem B894983 : Blo 892572 894983 := bstep (se 1 (by rfl) ⟨671237, by rfl⟩ : syracuseStep 894983 = 1342475) B1342475
theorem B894991 : Blo 892572 894991 := bstep (se 1 (by rfl) ⟨671243, by rfl⟩ : syracuseStep 894991 = 1342487) B1342487
theorem B895035 : Blo 892572 895035 := bstep (se 1 (by rfl) ⟨671276, by rfl⟩ : syracuseStep 895035 = 1342553) B1342553
theorem B895111 : Blo 892572 895111 := bstep (se 1 (by rfl) ⟨671333, by rfl⟩ : syracuseStep 895111 = 1342667) B1342667
theorem B895119 : Blo 892572 895119 := bstep (se 1 (by rfl) ⟨671339, by rfl⟩ : syracuseStep 895119 = 1342679) B1342679
theorem B8595629 : Blo 892572 8595629 := bstep (se 3 (by rfl) ⟨1611680, by rfl⟩ : syracuseStep 8595629 = 3223361) B3223361
theorem B895163 : Blo 892572 895163 := bstep (se 1 (by rfl) ⟨671372, by rfl⟩ : syracuseStep 895163 = 1342745) B1342745
theorem B895239 : Blo 892572 895239 := bstep (se 1 (by rfl) ⟨671429, by rfl⟩ : syracuseStep 895239 = 1342859) B1342859
theorem B895247 : Blo 892572 895247 := bstep (se 1 (by rfl) ⟨671435, by rfl⟩ : syracuseStep 895247 = 1342871) B1342871
theorem B895291 : Blo 892572 895291 := bstep (se 1 (by rfl) ⟨671468, by rfl⟩ : syracuseStep 895291 = 1342937) B1342937
theorem B895367 : Blo 892572 895367 := bstep (se 1 (by rfl) ⟨671525, by rfl⟩ : syracuseStep 895367 = 1343051) B1343051
theorem B895375 : Blo 892572 895375 := bstep (se 1 (by rfl) ⟨671531, by rfl⟩ : syracuseStep 895375 = 1343063) B1343063
theorem B895419 : Blo 892572 895419 := bstep (se 1 (by rfl) ⟨671564, by rfl⟩ : syracuseStep 895419 = 1343129) B1343129
theorem B15313373 : Blo 892572 15313373 := bstep (se 3 (by rfl) ⟨2871257, by rfl⟩ : syracuseStep 15313373 = 5742515) B5742515
theorem B895495 : Blo 892572 895495 := bstep (se 1 (by rfl) ⟨671621, by rfl⟩ : syracuseStep 895495 = 1343243) B1343243
theorem B895503 : Blo 892572 895503 := bstep (se 1 (by rfl) ⟨671627, by rfl⟩ : syracuseStep 895503 = 1343255) B1343255
theorem B4532759 : Blo 892572 4532759 := bstep (se 1 (by rfl) ⟨3399569, by rfl⟩ : syracuseStep 4532759 = 6799139) B6799139
theorem B895547 : Blo 892572 895547 := bstep (se 1 (by rfl) ⟨671660, by rfl⟩ : syracuseStep 895547 = 1343321) B1343321
theorem B2009735 : Blo 892572 2009735 := bstep (se 1 (by rfl) ⟨1507301, by rfl⟩ : syracuseStep 2009735 = 3014603) B3014603
theorem B1911431 : Blo 892572 1911431 := bstep (se 1 (by rfl) ⟨1433573, by rfl⟩ : syracuseStep 1911431 = 2867147) B2867147
theorem B895623 : Blo 892572 895623 := bstep (se 1 (by rfl) ⟨671717, by rfl⟩ : syracuseStep 895623 = 1343435) B1343435
theorem B895631 : Blo 892572 895631 := bstep (se 1 (by rfl) ⟨671723, by rfl⟩ : syracuseStep 895631 = 1343447) B1343447
theorem B895675 : Blo 892572 895675 := bstep (se 1 (by rfl) ⟨671756, by rfl⟩ : syracuseStep 895675 = 1343513) B1343513
theorem B4893385 : Blo 892572 4893385 := bstep (se 2 (by rfl) ⟨1835019, by rfl⟩ : syracuseStep 4893385 = 3670039) B3670039
theorem B895751 : Blo 892572 895751 := bstep (se 1 (by rfl) ⟨671813, by rfl⟩ : syracuseStep 895751 = 1343627) B1343627
theorem B895759 : Blo 892572 895759 := bstep (se 1 (by rfl) ⟨671819, by rfl⟩ : syracuseStep 895759 = 1343639) B1343639
theorem B2009915 : Blo 892572 2009915 := bstep (se 1 (by rfl) ⟨1507436, by rfl⟩ : syracuseStep 2009915 = 3014873) B3014873
theorem B895803 : Blo 892572 895803 := bstep (se 1 (by rfl) ⟨671852, by rfl⟩ : syracuseStep 895803 = 1343705) B1343705
theorem B9677657 : Blo 892572 9677657 := bstep (se 2 (by rfl) ⟨3629121, by rfl⟩ : syracuseStep 9677657 = 7258243) B7258243
theorem B895879 : Blo 892572 895879 := bstep (se 1 (by rfl) ⟨671909, by rfl⟩ : syracuseStep 895879 = 1343819) B1343819
theorem B895887 : Blo 892572 895887 := bstep (se 1 (by rfl) ⟨671915, by rfl⟩ : syracuseStep 895887 = 1343831) B1343831
theorem B2010041 : Blo 892572 2010041 := bstep (se 2 (by rfl) ⟨753765, by rfl⟩ : syracuseStep 2010041 = 1507531) B1507531
theorem B1813433 : Blo 892572 1813433 := bstep (se 2 (by rfl) ⟨680037, by rfl⟩ : syracuseStep 1813433 = 1360075) B1360075
theorem B895931 : Blo 892572 895931 := bstep (se 1 (by rfl) ⟨671948, by rfl⟩ : syracuseStep 895931 = 1343897) B1343897
theorem B896007 : Blo 892572 896007 := bstep (se 1 (by rfl) ⟨672005, by rfl⟩ : syracuseStep 896007 = 1344011) B1344011
theorem B896015 : Blo 892572 896015 := bstep (se 1 (by rfl) ⟨672011, by rfl⟩ : syracuseStep 896015 = 1344023) B1344023
theorem B1813547 : Blo 892572 1813547 := bstep (se 1 (by rfl) ⟨1360160, by rfl⟩ : syracuseStep 1813547 = 2720321) B2720321
theorem B896059 : Blo 892572 896059 := bstep (se 1 (by rfl) ⟨672044, by rfl⟩ : syracuseStep 896059 = 1344089) B1344089
theorem B896135 : Blo 892572 896135 := bstep (se 1 (by rfl) ⟨672101, by rfl⟩ : syracuseStep 896135 = 1344203) B1344203
theorem B896143 : Blo 892572 896143 := bstep (se 1 (by rfl) ⟨672107, by rfl⟩ : syracuseStep 896143 = 1344215) B1344215
theorem B896187 : Blo 892572 896187 := bstep (se 1 (by rfl) ⟨672140, by rfl⟩ : syracuseStep 896187 = 1344281) B1344281
theorem B10333421 : Blo 892572 10333421 := bstep (se 3 (by rfl) ⟨1937516, by rfl⟩ : syracuseStep 10333421 = 3875033) B3875033
theorem B896263 : Blo 892572 896263 := bstep (se 1 (by rfl) ⟨672197, by rfl⟩ : syracuseStep 896263 = 1344395) B1344395
theorem B2010383 : Blo 892572 2010383 := bstep (se 1 (by rfl) ⟨1507787, by rfl⟩ : syracuseStep 2010383 = 3015575) B3015575
theorem B896271 : Blo 892572 896271 := bstep (se 1 (by rfl) ⟨672203, by rfl⟩ : syracuseStep 896271 = 1344407) B1344407
theorem B2010401 : Blo 892572 2010401 := bstep (se 2 (by rfl) ⟨753900, by rfl⟩ : syracuseStep 2010401 = 1507801) B1507801
theorem B896315 : Blo 892572 896315 := bstep (se 1 (by rfl) ⟨672236, by rfl⟩ : syracuseStep 896315 = 1344473) B1344473
theorem B896391 : Blo 892572 896391 := bstep (se 1 (by rfl) ⟨672293, by rfl⟩ : syracuseStep 896391 = 1344587) B1344587
theorem B896399 : Blo 892572 896399 := bstep (se 1 (by rfl) ⟨672299, by rfl⟩ : syracuseStep 896399 = 1344599) B1344599
theorem B3812761 : Blo 892572 3812761 := bstep (se 2 (by rfl) ⟨1429785, by rfl⟩ : syracuseStep 3812761 = 2859571) B2859571
theorem B896443 : Blo 892572 896443 := bstep (se 1 (by rfl) ⟨672332, by rfl⟩ : syracuseStep 896443 = 1344665) B1344665
theorem B896519 : Blo 892572 896519 := bstep (se 1 (by rfl) ⟨672389, by rfl⟩ : syracuseStep 896519 = 1344779) B1344779
theorem B896527 : Blo 892572 896527 := bstep (se 1 (by rfl) ⟨672395, by rfl⟩ : syracuseStep 896527 = 1344791) B1344791
theorem B896571 : Blo 892572 896571 := bstep (se 1 (by rfl) ⟨672428, by rfl⟩ : syracuseStep 896571 = 1344857) B1344857
theorem B2010743 : Blo 892572 2010743 := bstep (se 1 (by rfl) ⟨1508057, by rfl⟩ : syracuseStep 2010743 = 3016115) B3016115
theorem B9186995 : Blo 892572 9186995 := bstep (se 1 (by rfl) ⟨6890246, by rfl⟩ : syracuseStep 9186995 = 13780493) B13780493
theorem B2010923 : Blo 892572 2010923 := bstep (se 1 (by rfl) ⟨1508192, by rfl⟩ : syracuseStep 2010923 = 3016385) B3016385
theorem B4828987 : Blo 892572 4828987 := bstep (se 1 (by rfl) ⟨3621740, by rfl⟩ : syracuseStep 4828987 = 7243481) B7243481
theorem B4599737 : Blo 892572 4599737 := bstep (se 2 (by rfl) ⟨1724901, by rfl⟩ : syracuseStep 4599737 = 3449803) B3449803
theorem B10203083 : Blo 892572 10203083 := bstep (se 1 (by rfl) ⟨7652312, by rfl⟩ : syracuseStep 10203083 = 15304625) B15304625
theorem B8171543 : Blo 892572 8171543 := bstep (se 1 (by rfl) ⟨6128657, by rfl⟩ : syracuseStep 8171543 = 12257315) B12257315
theorem B1912891 : Blo 892572 1912891 := bstep (se 1 (by rfl) ⟨1434668, by rfl⟩ : syracuseStep 1912891 = 2869337) B2869337
theorem B2240627 : Blo 892572 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B2011283 : Blo 892572 2011283 := bstep (se 1 (by rfl) ⟨1508462, by rfl⟩ : syracuseStep 2011283 = 3016925) B3016925
theorem B2011337 : Blo 892572 2011337 := bstep (se 2 (by rfl) ⟨754251, by rfl⟩ : syracuseStep 2011337 = 1508503) B1508503
theorem B1913147 : Blo 892572 1913147 := bstep (se 1 (by rfl) ⟨1434860, by rfl⟩ : syracuseStep 1913147 = 2869721) B2869721
theorem B15282755 : Blo 892572 15282755 := bstep (se 1 (by rfl) ⟨11462066, by rfl⟩ : syracuseStep 15282755 = 22924133) B22924133
theorem B4305581 : Blo 892572 4305581 := bstep (se 3 (by rfl) ⟨807296, by rfl⟩ : syracuseStep 4305581 = 1614593) B1614593
theorem B5157665 : Blo 892572 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B2012039 : Blo 892572 2012039 := bstep (se 1 (by rfl) ⟨1509029, by rfl⟩ : syracuseStep 2012039 = 3018059) B3018059
theorem B4305811 : Blo 892572 4305811 := bstep (se 1 (by rfl) ⟨3229358, by rfl⟩ : syracuseStep 4305811 = 6458717) B6458717
theorem B27898805 : Blo 892572 27898805 := bstep (se 5 (by rfl) ⟨1307756, by rfl⟩ : syracuseStep 27898805 = 2615513) B2615513
theorem B2012219 : Blo 892572 2012219 := bstep (se 1 (by rfl) ⟨1509164, by rfl⟩ : syracuseStep 2012219 = 3018329) B3018329
theorem B1815671 : Blo 892572 1815671 := bstep (se 1 (by rfl) ⟨1361753, by rfl⟩ : syracuseStep 1815671 = 2723507) B2723507
theorem B2012345 : Blo 892572 2012345 := bstep (se 2 (by rfl) ⟨754629, by rfl⟩ : syracuseStep 2012345 = 1509259) B1509259
theorem B5223889 : Blo 892572 5223889 := bstep (se 2 (by rfl) ⟨1958958, by rfl⟩ : syracuseStep 5223889 = 3917917) B3917917
theorem B2012687 : Blo 892572 2012687 := bstep (se 1 (by rfl) ⟨1509515, by rfl⟩ : syracuseStep 2012687 = 3019031) B3019031
theorem B4535837 : Blo 892572 4535837 := bstep (se 3 (by rfl) ⟨850469, by rfl⟩ : syracuseStep 4535837 = 1700939) B1700939
theorem B2012705 : Blo 892572 2012705 := bstep (se 2 (by rfl) ⟨754764, by rfl⟩ : syracuseStep 2012705 = 1509529) B1509529
theorem B2864929 : Blo 892572 2864929 := bstep (se 2 (by rfl) ⟨1074348, by rfl⟩ : syracuseStep 2864929 = 2148697) B2148697
theorem B29407093 : Blo 892572 29407093 := bstep (se 5 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 29407093 = 2756915) B2756915
theorem B2013047 : Blo 892572 2013047 := bstep (se 1 (by rfl) ⟨1509785, by rfl⟩ : syracuseStep 2013047 = 3019571) B3019571
theorem B4536323 : Blo 892572 4536323 := bstep (se 1 (by rfl) ⟨3402242, by rfl⟩ : syracuseStep 4536323 = 6804485) B6804485
theorem B5093387 : Blo 892572 5093387 := bstep (se 1 (by rfl) ⟨3820040, by rfl⟩ : syracuseStep 5093387 = 7640081) B7640081
theorem B2013227 : Blo 892572 2013227 := bstep (se 1 (by rfl) ⟨1509920, by rfl⟩ : syracuseStep 2013227 = 3019841) B3019841
theorem B6895853 : Blo 892572 6895853 := bstep (se 3 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 6895853 = 2585945) B2585945
theorem B2013587 : Blo 892572 2013587 := bstep (se 1 (by rfl) ⟨1510190, by rfl⟩ : syracuseStep 2013587 = 3020381) B3020381
theorem B2013641 : Blo 892572 2013641 := bstep (se 2 (by rfl) ⟨755115, by rfl⟩ : syracuseStep 2013641 = 1510231) B1510231
theorem B4078147 : Blo 892572 4078147 := bstep (se 1 (by rfl) ⟨3058610, by rfl⟩ : syracuseStep 4078147 = 6117221) B6117221
theorem B6437495 : Blo 892572 6437495 := bstep (se 1 (by rfl) ⟨4828121, by rfl⟩ : syracuseStep 6437495 = 9656243) B9656243
theorem B2014343 : Blo 892572 2014343 := bstep (se 1 (by rfl) ⟨1510757, by rfl⟩ : syracuseStep 2014343 = 3021515) B3021515
theorem B2014523 : Blo 892572 2014523 := bstep (se 1 (by rfl) ⟨1510892, by rfl⟩ : syracuseStep 2014523 = 3021785) B3021785
theorem B2014649 : Blo 892572 2014649 := bstep (se 2 (by rfl) ⟨755493, by rfl⟩ : syracuseStep 2014649 = 1510987) B1510987
theorem B3390929 : Blo 892572 3390929 := bstep (se 2 (by rfl) ⟨1271598, by rfl⟩ : syracuseStep 3390929 = 2543197) B2543197
theorem B4537943 : Blo 892572 4537943 := bstep (se 1 (by rfl) ⟨3403457, by rfl⟩ : syracuseStep 4537943 = 6806915) B6806915
theorem B3391247 : Blo 892572 3391247 := bstep (se 1 (by rfl) ⟨2543435, by rfl⟩ : syracuseStep 3391247 = 5086871) B5086871
theorem B2014991 : Blo 892572 2014991 := bstep (se 1 (by rfl) ⟨1511243, by rfl⟩ : syracuseStep 2014991 = 3022487) B3022487
theorem B2015009 : Blo 892572 2015009 := bstep (se 2 (by rfl) ⟨755628, by rfl⟩ : syracuseStep 2015009 = 1511257) B1511257
theorem B1130375 : Blo 892572 1130375 := bstep (se 1 (by rfl) ⟨847781, by rfl⟩ : syracuseStep 1130375 = 1695563) B1695563
theorem B4538429 : Blo 892572 4538429 := bstep (se 3 (by rfl) ⟨850955, by rfl⟩ : syracuseStep 4538429 = 1701911) B1701911
theorem B2015351 : Blo 892572 2015351 := bstep (se 1 (by rfl) ⟨1511513, by rfl⟩ : syracuseStep 2015351 = 3023027) B3023027
theorem B2146439 : Blo 892572 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B11452589 : Blo 892572 11452589 := bstep (se 3 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 11452589 = 4294721) B4294721
theorem B9814289 : Blo 892572 9814289 := bstep (se 2 (by rfl) ⟨3680358, by rfl⟩ : syracuseStep 9814289 = 7360717) B7360717
theorem B2015531 : Blo 892572 2015531 := bstep (se 1 (by rfl) ⟨1511648, by rfl⟩ : syracuseStep 2015531 = 3023297) B3023297
theorem B1131023 : Blo 892572 1131023 := bstep (se 1 (by rfl) ⟨848267, by rfl⟩ : syracuseStep 1131023 = 1696535) B1696535
theorem B2015891 : Blo 892572 2015891 := bstep (se 1 (by rfl) ⟨1511918, by rfl⟩ : syracuseStep 2015891 = 3023837) B3023837
theorem B2015945 : Blo 892572 2015945 := bstep (se 2 (by rfl) ⟨755979, by rfl⟩ : syracuseStep 2015945 = 1511959) B1511959
theorem B15287129 : Blo 892572 15287129 := bstep (se 2 (by rfl) ⟨5732673, by rfl⟩ : syracuseStep 15287129 = 11465347) B11465347
theorem B5718937 : Blo 892572 5718937 := bstep (se 2 (by rfl) ⟨2144601, by rfl⟩ : syracuseStep 5718937 = 4289203) B4289203
theorem B2868311 : Blo 892572 2868311 := bstep (se 1 (by rfl) ⟨2151233, by rfl⟩ : syracuseStep 2868311 = 4302467) B4302467
theorem B2147447 : Blo 892572 2147447 := bstep (se 1 (by rfl) ⟨1610585, by rfl⟩ : syracuseStep 2147447 = 3221171) B3221171
theorem B5096621 : Blo 892572 5096621 := bstep (se 3 (by rfl) ⟨955616, by rfl⟩ : syracuseStep 5096621 = 1911233) B1911233
theorem B3228929 : Blo 892572 3228929 := bstep (se 2 (by rfl) ⟨1210848, by rfl⟩ : syracuseStep 3228929 = 2421697) B2421697
theorem B3622259 : Blo 892572 3622259 := bstep (se 1 (by rfl) ⟨2716694, by rfl⟩ : syracuseStep 3622259 = 5433389) B5433389
theorem B2016647 : Blo 892572 2016647 := bstep (se 1 (by rfl) ⟨1512485, by rfl⟩ : syracuseStep 2016647 = 3024971) B3024971
theorem B2016827 : Blo 892572 2016827 := bstep (se 1 (by rfl) ⟨1512620, by rfl⟩ : syracuseStep 2016827 = 3025241) B3025241
theorem B2016953 : Blo 892572 2016953 := bstep (se 2 (by rfl) ⟨756357, by rfl⟩ : syracuseStep 2016953 = 1512715) B1512715
theorem B3065615 : Blo 892572 3065615 := bstep (se 1 (by rfl) ⟨2299211, by rfl⟩ : syracuseStep 3065615 = 4598423) B4598423
theorem B3622715 : Blo 892572 3622715 := bstep (se 1 (by rfl) ⟨2717036, by rfl⟩ : syracuseStep 3622715 = 5434073) B5434073
theorem B2148215 : Blo 892572 2148215 := bstep (se 1 (by rfl) ⟨1611161, by rfl⟩ : syracuseStep 2148215 = 3222323) B3222323
theorem B16566295 : Blo 892572 16566295 := bstep (se 1 (by rfl) ⟨12424721, by rfl⟩ : syracuseStep 16566295 = 24849443) B24849443
theorem B3819581 : Blo 892572 3819581 := bstep (se 3 (by rfl) ⟨716171, by rfl⟩ : syracuseStep 3819581 = 1432343) B1432343
theorem B4835389 : Blo 892572 4835389 := bstep (se 3 (by rfl) ⟨906635, by rfl⟩ : syracuseStep 4835389 = 1813271) B1813271
theorem B5097761 : Blo 892572 5097761 := bstep (se 2 (by rfl) ⟨1911660, by rfl⟩ : syracuseStep 5097761 = 3823321) B3823321
theorem B3394817 : Blo 892572 3394817 := bstep (se 2 (by rfl) ⟨1273056, by rfl⟩ : syracuseStep 3394817 = 2546113) B2546113
theorem B3394831 : Blo 892572 3394831 := bstep (se 1 (by rfl) ⟨2546123, by rfl⟩ : syracuseStep 3394831 = 5092247) B5092247
theorem B1133995 : Blo 892572 1133995 := bstep (se 1 (by rfl) ⟨850496, by rfl⟩ : syracuseStep 1133995 = 1700993) B1700993
theorem B2150023 : Blo 892572 2150023 := bstep (se 1 (by rfl) ⟨1612517, by rfl⟩ : syracuseStep 2150023 = 3225035) B3225035
theorem B3821579 : Blo 892572 3821579 := bstep (se 1 (by rfl) ⟨2866184, by rfl⟩ : syracuseStep 3821579 = 5732369) B5732369
theorem B2576569 : Blo 892572 2576569 := bstep (se 2 (by rfl) ⟨966213, by rfl⟩ : syracuseStep 2576569 = 1932427) B1932427
theorem B8606087 : Blo 892572 8606087 := bstep (se 1 (by rfl) ⟨6454565, by rfl⟩ : syracuseStep 8606087 = 12909131) B12909131
theorem B3396107 : Blo 892572 3396107 := bstep (se 1 (by rfl) ⟨2547080, by rfl⟩ : syracuseStep 3396107 = 5094161) B5094161
theorem B2150927 : Blo 892572 2150927 := bstep (se 1 (by rfl) ⟨1613195, by rfl⟩ : syracuseStep 2150927 = 3226391) B3226391
theorem B1004431 : Blo 892572 1004431 := bstep (se 1 (by rfl) ⟨753323, by rfl⟩ : syracuseStep 1004431 = 1506647) B1506647
theorem B2544655 : Blo 892572 2544655 := bstep (se 1 (by rfl) ⟨1908491, by rfl⟩ : syracuseStep 2544655 = 3816983) B3816983
theorem B2544929 : Blo 892572 2544929 := bstep (se 2 (by rfl) ⟨954348, by rfl⟩ : syracuseStep 2544929 = 1908697) B1908697
theorem B1004935 : Blo 892572 1004935 := bstep (se 1 (by rfl) ⟨753701, by rfl⟩ : syracuseStep 1004935 = 1507403) B1507403
theorem B3397049 : Blo 892572 3397049 := bstep (se 2 (by rfl) ⟨1273893, by rfl⟩ : syracuseStep 3397049 = 2547787) B2547787
theorem B4838935 : Blo 892572 4838935 := bstep (se 1 (by rfl) ⟨3629201, by rfl⟩ : syracuseStep 4838935 = 7258403) B7258403
theorem B1005115 : Blo 892572 1005115 := bstep (se 1 (by rfl) ⟨753836, by rfl⟩ : syracuseStep 1005115 = 1507673) B1507673
theorem B12900019 : Blo 892572 12900019 := bstep (se 1 (by rfl) ⟨9675014, by rfl⟩ : syracuseStep 12900019 = 19350029) B19350029
theorem B2414603 : Blo 892572 2414603 := bstep (se 1 (by rfl) ⟨1810952, by rfl⟩ : syracuseStep 2414603 = 3621905) B3621905
theorem B1005583 : Blo 892572 1005583 := bstep (se 1 (by rfl) ⟨754187, by rfl⟩ : syracuseStep 1005583 = 1508375) B1508375
theorem B11458583 : Blo 892572 11458583 := bstep (se 1 (by rfl) ⟨8593937, by rfl⟩ : syracuseStep 11458583 = 17187875) B17187875
theorem B2545931 : Blo 892572 2545931 := bstep (se 1 (by rfl) ⟨1909448, by rfl⟩ : syracuseStep 2545931 = 3818897) B3818897
theorem B4839695 : Blo 892572 4839695 := bstep (se 1 (by rfl) ⟨3629771, by rfl⟩ : syracuseStep 4839695 = 7259543) B7259543
theorem B4839713 : Blo 892572 4839713 := bstep (se 2 (by rfl) ⟨1814892, by rfl⟩ : syracuseStep 4839713 = 3629785) B3629785
theorem B1006087 : Blo 892572 1006087 := bstep (se 1 (by rfl) ⟨754565, by rfl⟩ : syracuseStep 1006087 = 1509131) B1509131
theorem B2546329 : Blo 892572 2546329 := bstep (se 2 (by rfl) ⟨954873, by rfl⟩ : syracuseStep 2546329 = 1909747) B1909747
theorem B1006267 : Blo 892572 1006267 := bstep (se 1 (by rfl) ⟨754700, by rfl⟩ : syracuseStep 1006267 = 1509401) B1509401
theorem B2546579 : Blo 892572 2546579 := bstep (se 1 (by rfl) ⟨1909934, by rfl⟩ : syracuseStep 2546579 = 3819869) B3819869
theorem B5102635 : Blo 892572 5102635 := bstep (se 1 (by rfl) ⟨3826976, by rfl⟩ : syracuseStep 5102635 = 7653953) B7653953
theorem B1006735 : Blo 892572 1006735 := bstep (se 1 (by rfl) ⟨755051, by rfl⟩ : syracuseStep 1006735 = 1510103) B1510103
theorem B2415901 : Blo 892572 2415901 := bstep (se 3 (by rfl) ⟨452981, by rfl⟩ : syracuseStep 2415901 = 905963) B905963
theorem B67198267 : Blo 892572 67198267 := bstep (se 1 (by rfl) ⟨50398700, by rfl⟩ : syracuseStep 67198267 = 100797401) B100797401
theorem B9690461 : Blo 892572 9690461 := bstep (se 3 (by rfl) ⟨1816961, by rfl⟩ : syracuseStep 9690461 = 3633923) B3633923
theorem B1695161 : Blo 892572 1695161 := bstep (se 2 (by rfl) ⟨635685, by rfl⟩ : syracuseStep 1695161 = 1271371) B1271371
theorem B7265795 : Blo 892572 7265795 := bstep (se 1 (by rfl) ⟨5449346, by rfl⟩ : syracuseStep 7265795 = 10898693) B10898693
theorem B2416139 : Blo 892572 2416139 := bstep (se 1 (by rfl) ⟨1812104, by rfl⟩ : syracuseStep 2416139 = 3624209) B3624209
theorem B1007239 : Blo 892572 1007239 := bstep (se 1 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 1007239 = 1510859) B1510859
theorem B1072811 : Blo 892572 1072811 := bstep (se 1 (by rfl) ⟨804608, by rfl⟩ : syracuseStep 1072811 = 1609217) B1609217
theorem B9690803 : Blo 892572 9690803 := bstep (se 1 (by rfl) ⟨7268102, by rfl⟩ : syracuseStep 9690803 = 14536205) B14536205
theorem B1007419 : Blo 892572 1007419 := bstep (se 1 (by rfl) ⟨755564, by rfl⟩ : syracuseStep 1007419 = 1511129) B1511129
theorem B2547571 : Blo 892572 2547571 := bstep (se 1 (by rfl) ⟨1910678, by rfl⟩ : syracuseStep 2547571 = 3821357) B3821357
theorem B3399691 : Blo 892572 3399691 := bstep (se 1 (by rfl) ⟨2549768, by rfl⟩ : syracuseStep 3399691 = 5099537) B5099537
theorem B3825731 : Blo 892572 3825731 := bstep (se 1 (by rfl) ⟨2869298, by rfl⟩ : syracuseStep 3825731 = 5738597) B5738597
theorem B1007887 : Blo 892572 1007887 := bstep (se 1 (by rfl) ⟨755915, by rfl⟩ : syracuseStep 1007887 = 1511831) B1511831
theorem B3825953 : Blo 892572 3825953 := bstep (se 2 (by rfl) ⟨1434732, by rfl⟩ : syracuseStep 3825953 = 2869465) B2869465
theorem B3399995 : Blo 892572 3399995 := bstep (se 1 (by rfl) ⟨2549996, by rfl⟩ : syracuseStep 3399995 = 5099993) B5099993
theorem B3826055 : Blo 892572 3826055 := bstep (se 1 (by rfl) ⟨2869541, by rfl⟩ : syracuseStep 3826055 = 5739083) B5739083
theorem B5104093 : Blo 892572 5104093 := bstep (se 3 (by rfl) ⟨957017, by rfl⟩ : syracuseStep 5104093 = 1914035) B1914035
theorem B1696315 : Blo 892572 1696315 := bstep (se 1 (by rfl) ⟨1272236, by rfl⟩ : syracuseStep 1696315 = 2544473) B2544473
theorem B1008391 : Blo 892572 1008391 := bstep (se 1 (by rfl) ⟨756293, by rfl⟩ : syracuseStep 1008391 = 1512587) B1512587
theorem B1073935 : Blo 892572 1073935 := bstep (se 1 (by rfl) ⟨805451, by rfl⟩ : syracuseStep 1073935 = 1610903) B1610903
theorem B3400481 : Blo 892572 3400481 := bstep (se 2 (by rfl) ⟨1275180, by rfl⟩ : syracuseStep 3400481 = 2550361) B2550361
theorem B1008571 : Blo 892572 1008571 := bstep (se 1 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 1008571 = 1512857) B1512857
theorem B1696801 : Blo 892572 1696801 := bstep (se 2 (by rfl) ⟨636300, by rfl⟩ : syracuseStep 1696801 = 1272601) B1272601
theorem B4645955 : Blo 892572 4645955 := bstep (se 1 (by rfl) ⟨3484466, by rfl⟩ : syracuseStep 4645955 = 6968933) B6968933
theorem B2549177 : Blo 892572 2549177 := bstep (se 2 (by rfl) ⟨955941, by rfl⟩ : syracuseStep 2549177 = 1911883) B1911883
theorem B1959457 : Blo 892572 1959457 := bstep (se 2 (by rfl) ⟨734796, by rfl⟩ : syracuseStep 1959457 = 1469593) B1469593
theorem B1271467 : Blo 892572 1271467 := bstep (se 1 (by rfl) ⟨953600, by rfl⟩ : syracuseStep 1271467 = 1907201) B1907201
theorem B3401453 : Blo 892572 3401453 := bstep (se 3 (by rfl) ⟨637772, by rfl⟩ : syracuseStep 3401453 = 1275545) B1275545
theorem B2549519 : Blo 892572 2549519 := bstep (se 1 (by rfl) ⟨1912139, by rfl⟩ : syracuseStep 2549519 = 3824279) B3824279
theorem B13756229 : Blo 892572 13756229 := bstep (se 4 (by rfl) ⟨1289646, by rfl⟩ : syracuseStep 13756229 = 2579293) B2579293
theorem B1075079 : Blo 892572 1075079 := bstep (se 1 (by rfl) ⟨806309, by rfl⟩ : syracuseStep 1075079 = 1612619) B1612619
theorem B1271695 : Blo 892572 1271695 := bstep (se 1 (by rfl) ⟨953771, by rfl⟩ : syracuseStep 1271695 = 1907543) B1907543
theorem B1697993 : Blo 892572 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B3827969 : Blo 892572 3827969 := bstep (se 2 (by rfl) ⟨1435488, by rfl⟩ : syracuseStep 3827969 = 2870977) B2870977
theorem B1272071 : Blo 892572 1272071 := bstep (se 1 (by rfl) ⟨954053, by rfl⟩ : syracuseStep 1272071 = 1908107) B1908107
theorem B1435963 : Blo 892572 1435963 := bstep (se 1 (by rfl) ⟨1076972, by rfl⟩ : syracuseStep 1435963 = 2153945) B2153945
theorem B2550305 : Blo 892572 2550305 := bstep (se 2 (by rfl) ⟨956364, by rfl⟩ : syracuseStep 2550305 = 1912729) B1912729
theorem B1075771 : Blo 892572 1075771 := bstep (se 1 (by rfl) ⟨806828, by rfl⟩ : syracuseStep 1075771 = 1613657) B1613657
theorem B10185587 : Blo 892572 10185587 := bstep (se 1 (by rfl) ⟨7639190, by rfl⟩ : syracuseStep 10185587 = 15278381) B15278381
theorem B4582289 : Blo 892572 4582289 := bstep (se 2 (by rfl) ⟨1718358, by rfl⟩ : syracuseStep 4582289 = 3436717) B3436717
theorem B1698707 : Blo 892572 1698707 := bstep (se 1 (by rfl) ⟨1274030, by rfl⟩ : syracuseStep 1698707 = 2548061) B2548061
theorem B1698745 : Blo 892572 1698745 := bstep (se 2 (by rfl) ⟨637029, by rfl⟩ : syracuseStep 1698745 = 1274059) B1274059
theorem B4582601 : Blo 892572 4582601 := bstep (se 2 (by rfl) ⟨1718475, by rfl⟩ : syracuseStep 4582601 = 3436951) B3436951
theorem B1306027 : Blo 892572 1306027 := bstep (se 1 (by rfl) ⟨979520, by rfl⟩ : syracuseStep 1306027 = 1959041) B1959041
theorem B1207723 : Blo 892572 1207723 := bstep (se 1 (by rfl) ⟨905792, by rfl⟩ : syracuseStep 1207723 = 1811585) B1811585
theorem B17460659 : Blo 892572 17460659 := bstep (se 1 (by rfl) ⟨13095494, by rfl⟩ : syracuseStep 17460659 = 26190989) B26190989
theorem B1338887 : Blo 892572 1338887 := bstep (se 1 (by rfl) ⟨1004165, by rfl⟩ : syracuseStep 1338887 = 2008331) B2008331
theorem B1338923 : Blo 892572 1338923 := bstep (se 1 (by rfl) ⟨1004192, by rfl⟩ : syracuseStep 1338923 = 2008385) B2008385
theorem B1338953 : Blo 892572 1338953 := bstep (se 2 (by rfl) ⟨502107, by rfl⟩ : syracuseStep 1338953 = 1004215) B1004215
theorem B97807985 : Blo 892572 97807985 := bstep (se 2 (by rfl) ⟨36677994, by rfl⟩ : syracuseStep 97807985 = 73355989) B73355989
theorem B1273529 : Blo 892572 1273529 := bstep (se 2 (by rfl) ⟨477573, by rfl⟩ : syracuseStep 1273529 = 955147) B955147
theorem B1339067 : Blo 892572 1339067 := bstep (se 1 (by rfl) ⟨1004300, by rfl⟩ : syracuseStep 1339067 = 2008601) B2008601
theorem B1339127 : Blo 892572 1339127 := bstep (se 1 (by rfl) ⟨1004345, by rfl⟩ : syracuseStep 1339127 = 2008691) B2008691
theorem B1339151 : Blo 892572 1339151 := bstep (se 1 (by rfl) ⟨1004363, by rfl⟩ : syracuseStep 1339151 = 2008727) B2008727
theorem B9563939 : Blo 892572 9563939 := bstep (se 1 (by rfl) ⟨7172954, by rfl⟩ : syracuseStep 9563939 = 14345909) B14345909
theorem B7270181 : Blo 892572 7270181 := bstep (se 4 (by rfl) ⟨681579, by rfl⟩ : syracuseStep 7270181 = 1363159) B1363159
theorem B1339193 : Blo 892572 1339193 := bstep (se 2 (by rfl) ⟨502197, by rfl⟩ : syracuseStep 1339193 = 1004395) B1004395
theorem B3403579 : Blo 892572 3403579 := bstep (se 1 (by rfl) ⟨2552684, by rfl⟩ : syracuseStep 3403579 = 5105369) B5105369
theorem B1339271 : Blo 892572 1339271 := bstep (se 1 (by rfl) ⟨1004453, by rfl⟩ : syracuseStep 1339271 = 2008907) B2008907
theorem B1339307 : Blo 892572 1339307 := bstep (se 1 (by rfl) ⟨1004480, by rfl⟩ : syracuseStep 1339307 = 2008961) B2008961
theorem B1339337 : Blo 892572 1339337 := bstep (se 2 (by rfl) ⟨502251, by rfl⟩ : syracuseStep 1339337 = 1004503) B1004503
theorem B14479307 : Blo 892572 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B2551819 : Blo 892572 2551819 := bstep (se 1 (by rfl) ⟨1913864, by rfl⟩ : syracuseStep 2551819 = 3827729) B3827729
theorem B1339451 : Blo 892572 1339451 := bstep (se 1 (by rfl) ⟨1004588, by rfl⟩ : syracuseStep 1339451 = 2009177) B2009177
theorem B1339511 : Blo 892572 1339511 := bstep (se 1 (by rfl) ⟨1004633, by rfl⟩ : syracuseStep 1339511 = 2009267) B2009267
theorem B1339535 : Blo 892572 1339535 := bstep (se 1 (by rfl) ⟨1004651, by rfl⟩ : syracuseStep 1339535 = 2009303) B2009303
theorem B1339577 : Blo 892572 1339577 := bstep (se 2 (by rfl) ⟨502341, by rfl⟩ : syracuseStep 1339577 = 1004683) B1004683
theorem B1339655 : Blo 892572 1339655 := bstep (se 1 (by rfl) ⟨1004741, by rfl⟩ : syracuseStep 1339655 = 2009483) B2009483
theorem B2552093 : Blo 892572 2552093 := bstep (se 3 (by rfl) ⟨478517, by rfl⟩ : syracuseStep 2552093 = 957035) B957035
theorem B3404065 : Blo 892572 3404065 := bstep (se 2 (by rfl) ⟨1276524, by rfl⟩ : syracuseStep 3404065 = 2553049) B2553049
theorem B1339691 : Blo 892572 1339691 := bstep (se 1 (by rfl) ⟨1004768, by rfl⟩ : syracuseStep 1339691 = 2009537) B2009537
theorem B1339721 : Blo 892572 1339721 := bstep (se 2 (by rfl) ⟨502395, by rfl⟩ : syracuseStep 1339721 = 1004791) B1004791
theorem B1339835 : Blo 892572 1339835 := bstep (se 1 (by rfl) ⟨1004876, by rfl⟩ : syracuseStep 1339835 = 2009753) B2009753
theorem B1339895 : Blo 892572 1339895 := bstep (se 1 (by rfl) ⟨1004921, by rfl⟩ : syracuseStep 1339895 = 2009843) B2009843
theorem B1339919 : Blo 892572 1339919 := bstep (se 1 (by rfl) ⟨1004939, by rfl⟩ : syracuseStep 1339919 = 2009879) B2009879
theorem B1274383 : Blo 892572 1274383 := bstep (se 1 (by rfl) ⟨955787, by rfl⟩ : syracuseStep 1274383 = 1911575) B1911575
theorem B1339961 : Blo 892572 1339961 := bstep (se 2 (by rfl) ⟨502485, by rfl⟩ : syracuseStep 1339961 = 1004971) B1004971
theorem B2552435 : Blo 892572 2552435 := bstep (se 1 (by rfl) ⟨1914326, by rfl⟩ : syracuseStep 2552435 = 3828653) B3828653
theorem B1340039 : Blo 892572 1340039 := bstep (se 1 (by rfl) ⟨1005029, by rfl⟩ : syracuseStep 1340039 = 2010059) B2010059
theorem B1340075 : Blo 892572 1340075 := bstep (se 1 (by rfl) ⟨1005056, by rfl⟩ : syracuseStep 1340075 = 2010113) B2010113
theorem B1340105 : Blo 892572 1340105 := bstep (se 2 (by rfl) ⟨502539, by rfl⟩ : syracuseStep 1340105 = 1005079) B1005079
theorem B1700651 : Blo 892572 1700651 := bstep (se 1 (by rfl) ⟨1275488, by rfl⟩ : syracuseStep 1700651 = 2550977) B2550977
theorem B6779699 : Blo 892572 6779699 := bstep (se 1 (by rfl) ⟨5084774, by rfl⟩ : syracuseStep 6779699 = 10169549) B10169549
theorem B9433907 : Blo 892572 9433907 := bstep (se 1 (by rfl) ⟨7075430, by rfl⟩ : syracuseStep 9433907 = 14150861) B14150861
theorem B1340219 : Blo 892572 1340219 := bstep (se 1 (by rfl) ⟨1005164, by rfl⟩ : syracuseStep 1340219 = 2010329) B2010329
theorem B1340279 : Blo 892572 1340279 := bstep (se 1 (by rfl) ⟨1005209, by rfl⟩ : syracuseStep 1340279 = 2010419) B2010419
theorem B1340303 : Blo 892572 1340303 := bstep (se 1 (by rfl) ⟨1005227, by rfl⟩ : syracuseStep 1340303 = 2010455) B2010455
theorem B1340345 : Blo 892572 1340345 := bstep (se 2 (by rfl) ⟨502629, by rfl⟩ : syracuseStep 1340345 = 1005259) B1005259
theorem B1340423 : Blo 892572 1340423 := bstep (se 1 (by rfl) ⟨1005317, by rfl⟩ : syracuseStep 1340423 = 2010635) B2010635
theorem B1340459 : Blo 892572 1340459 := bstep (se 1 (by rfl) ⟨1005344, by rfl⟩ : syracuseStep 1340459 = 2010689) B2010689
theorem B1340489 : Blo 892572 1340489 := bstep (se 2 (by rfl) ⟨502683, by rfl⟩ : syracuseStep 1340489 = 1005367) B1005367
theorem B1274953 : Blo 892572 1274953 := bstep (se 2 (by rfl) ⟨478107, by rfl⟩ : syracuseStep 1274953 = 956215) B956215
theorem B1340603 : Blo 892572 1340603 := bstep (se 1 (by rfl) ⟨1005452, by rfl⟩ : syracuseStep 1340603 = 2010905) B2010905
theorem B1340663 : Blo 892572 1340663 := bstep (se 1 (by rfl) ⟨1005497, by rfl⟩ : syracuseStep 1340663 = 2010995) B2010995
theorem B1340687 : Blo 892572 1340687 := bstep (se 1 (by rfl) ⟨1005515, by rfl⟩ : syracuseStep 1340687 = 2011031) B2011031
theorem B1340729 : Blo 892572 1340729 := bstep (se 2 (by rfl) ⟨502773, by rfl⟩ : syracuseStep 1340729 = 1005547) B1005547
theorem B1340807 : Blo 892572 1340807 := bstep (se 1 (by rfl) ⟨1005605, by rfl⟩ : syracuseStep 1340807 = 2011211) B2011211
theorem B4519313 : Blo 892572 4519313 := bstep (se 2 (by rfl) ⟨1694742, by rfl⟩ : syracuseStep 4519313 = 3389485) B3389485
theorem B1340843 : Blo 892572 1340843 := bstep (se 1 (by rfl) ⟨1005632, by rfl⟩ : syracuseStep 1340843 = 2011265) B2011265
theorem B1340873 : Blo 892572 1340873 := bstep (se 2 (by rfl) ⟨502827, by rfl⟩ : syracuseStep 1340873 = 1005655) B1005655
theorem B1340987 : Blo 892572 1340987 := bstep (se 1 (by rfl) ⟨1005740, by rfl⟩ : syracuseStep 1340987 = 2011481) B2011481
theorem B1341047 : Blo 892572 1341047 := bstep (se 1 (by rfl) ⟨1005785, by rfl⟩ : syracuseStep 1341047 = 2011571) B2011571
theorem B1341071 : Blo 892572 1341071 := bstep (se 1 (by rfl) ⟨1005803, by rfl⟩ : syracuseStep 1341071 = 2011607) B2011607
theorem B17430167 : Blo 892572 17430167 := bstep (se 1 (by rfl) ⟨13072625, by rfl⟩ : syracuseStep 17430167 = 26145251) B26145251
theorem B1341113 : Blo 892572 1341113 := bstep (se 2 (by rfl) ⟨502917, by rfl⟩ : syracuseStep 1341113 = 1005835) B1005835
theorem B1701577 : Blo 892572 1701577 := bstep (se 2 (by rfl) ⟨638091, by rfl⟩ : syracuseStep 1701577 = 1276183) B1276183
theorem B1341191 : Blo 892572 1341191 := bstep (se 1 (by rfl) ⟨1005893, by rfl⟩ : syracuseStep 1341191 = 2011787) B2011787
theorem B2717473 : Blo 892572 2717473 := bstep (se 2 (by rfl) ⟨1019052, by rfl⟩ : syracuseStep 2717473 = 2038105) B2038105
theorem B2324257 : Blo 892572 2324257 := bstep (se 2 (by rfl) ⟨871596, by rfl⟩ : syracuseStep 2324257 = 1743193) B1743193
theorem B2422561 : Blo 892572 2422561 := bstep (se 2 (by rfl) ⟨908460, by rfl⟩ : syracuseStep 2422561 = 1816921) B1816921
theorem B5601061 : Blo 892572 5601061 := bstep (se 4 (by rfl) ⟨525099, by rfl⟩ : syracuseStep 5601061 = 1050199) B1050199
theorem B1341227 : Blo 892572 1341227 := bstep (se 1 (by rfl) ⟨1005920, by rfl⟩ : syracuseStep 1341227 = 2011841) B2011841
theorem B1341257 : Blo 892572 1341257 := bstep (se 2 (by rfl) ⟨502971, by rfl⟩ : syracuseStep 1341257 = 1005943) B1005943
theorem B1341371 : Blo 892572 1341371 := bstep (se 1 (by rfl) ⟨1006028, by rfl⟩ : syracuseStep 1341371 = 2012057) B2012057
theorem B1341431 : Blo 892572 1341431 := bstep (se 1 (by rfl) ⟨1006073, by rfl⟩ : syracuseStep 1341431 = 2012147) B2012147
theorem B1341455 : Blo 892572 1341455 := bstep (se 1 (by rfl) ⟨1006091, by rfl⟩ : syracuseStep 1341455 = 2012183) B2012183
theorem B1341497 : Blo 892572 1341497 := bstep (se 2 (by rfl) ⟨503061, by rfl⟩ : syracuseStep 1341497 = 1006123) B1006123
theorem B1341575 : Blo 892572 1341575 := bstep (se 1 (by rfl) ⟨1006181, by rfl⟩ : syracuseStep 1341575 = 2012363) B2012363
theorem B1341611 : Blo 892572 1341611 := bstep (se 1 (by rfl) ⟨1006208, by rfl⟩ : syracuseStep 1341611 = 2012417) B2012417
theorem B5503177 : Blo 892572 5503177 := bstep (se 2 (by rfl) ⟨2063691, by rfl⟩ : syracuseStep 5503177 = 4127383) B4127383
theorem B1341641 : Blo 892572 1341641 := bstep (se 2 (by rfl) ⟨503115, by rfl⟩ : syracuseStep 1341641 = 1006231) B1006231
theorem B1341755 : Blo 892572 1341755 := bstep (se 1 (by rfl) ⟨1006316, by rfl⟩ : syracuseStep 1341755 = 2012633) B2012633
theorem B1341815 : Blo 892572 1341815 := bstep (se 1 (by rfl) ⟨1006361, by rfl⟩ : syracuseStep 1341815 = 2012723) B2012723
theorem B1341839 : Blo 892572 1341839 := bstep (se 1 (by rfl) ⟨1006379, by rfl⟩ : syracuseStep 1341839 = 2012759) B2012759
theorem B2259353 : Blo 892572 2259353 := bstep (se 2 (by rfl) ⟨847257, by rfl⟩ : syracuseStep 2259353 = 1694515) B1694515
theorem B1341881 : Blo 892572 1341881 := bstep (se 2 (by rfl) ⟨503205, by rfl⟩ : syracuseStep 1341881 = 1006411) B1006411
theorem B21559769 : Blo 892572 21559769 := bstep (se 2 (by rfl) ⟨8084913, by rfl⟩ : syracuseStep 21559769 = 16169827) B16169827
theorem B1341959 : Blo 892572 1341959 := bstep (se 1 (by rfl) ⟨1006469, by rfl⟩ : syracuseStep 1341959 = 2012939) B2012939
theorem B1341995 : Blo 892572 1341995 := bstep (se 1 (by rfl) ⟨1006496, by rfl⟩ : syracuseStep 1341995 = 2012993) B2012993
theorem B2259515 : Blo 892572 2259515 := bstep (se 1 (by rfl) ⟨1694636, by rfl⟩ : syracuseStep 2259515 = 3389273) B3389273
theorem B1342025 : Blo 892572 1342025 := bstep (se 2 (by rfl) ⟨503259, by rfl⟩ : syracuseStep 1342025 = 1006519) B1006519
theorem B1342139 : Blo 892572 1342139 := bstep (se 1 (by rfl) ⟨1006604, by rfl⟩ : syracuseStep 1342139 = 2013209) B2013209
theorem B1342199 : Blo 892572 1342199 := bstep (se 1 (by rfl) ⟨1006649, by rfl⟩ : syracuseStep 1342199 = 2013299) B2013299
theorem B1342223 : Blo 892572 1342223 := bstep (se 1 (by rfl) ⟨1006667, by rfl⟩ : syracuseStep 1342223 = 2013335) B2013335
theorem B1342265 : Blo 892572 1342265 := bstep (se 2 (by rfl) ⟨503349, by rfl⟩ : syracuseStep 1342265 = 1006699) B1006699
theorem B2456381 : Blo 892572 2456381 := bstep (se 3 (by rfl) ⟨460571, by rfl⟩ : syracuseStep 2456381 = 921143) B921143
theorem B1342343 : Blo 892572 1342343 := bstep (se 1 (by rfl) ⟨1006757, by rfl⟩ : syracuseStep 1342343 = 2013515) B2013515
theorem B2259859 : Blo 892572 2259859 := bstep (se 1 (by rfl) ⟨1694894, by rfl⟩ : syracuseStep 2259859 = 3389789) B3389789
theorem B3013523 : Blo 892572 3013523 := bstep (se 1 (by rfl) ⟨2260142, by rfl⟩ : syracuseStep 3013523 = 4520285) B4520285
theorem B1342379 : Blo 892572 1342379 := bstep (se 1 (by rfl) ⟨1006784, by rfl⟩ : syracuseStep 1342379 = 2013569) B2013569
theorem B1342409 : Blo 892572 1342409 := bstep (se 2 (by rfl) ⟨503403, by rfl⟩ : syracuseStep 1342409 = 1006807) B1006807
theorem B2260001 : Blo 892572 2260001 := bstep (se 2 (by rfl) ⟨847500, by rfl⟩ : syracuseStep 2260001 = 1695001) B1695001
theorem B1342523 : Blo 892572 1342523 := bstep (se 1 (by rfl) ⟨1006892, by rfl⟩ : syracuseStep 1342523 = 2013785) B2013785
theorem B6454333 : Blo 892572 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B1342583 : Blo 892572 1342583 := bstep (se 1 (by rfl) ⟨1006937, by rfl⟩ : syracuseStep 1342583 = 2013875) B2013875
theorem B1342607 : Blo 892572 1342607 := bstep (se 1 (by rfl) ⟨1006955, by rfl⟩ : syracuseStep 1342607 = 2013911) B2013911
theorem B1342649 : Blo 892572 1342649 := bstep (se 2 (by rfl) ⟨503493, by rfl⟩ : syracuseStep 1342649 = 1006987) B1006987
theorem B1506505 : Blo 892572 1506505 := bstep (se 2 (by rfl) ⟨564939, by rfl⟩ : syracuseStep 1506505 = 1129879) B1129879
theorem B1342727 : Blo 892572 1342727 := bstep (se 1 (by rfl) ⟨1007045, by rfl⟩ : syracuseStep 1342727 = 2014091) B2014091
theorem B1342763 : Blo 892572 1342763 := bstep (se 1 (by rfl) ⟨1007072, by rfl⟩ : syracuseStep 1342763 = 2014145) B2014145
theorem B44039483 : Blo 892572 44039483 := bstep (se 1 (by rfl) ⟨33029612, by rfl⟩ : syracuseStep 44039483 = 66059225) B66059225
theorem B1342793 : Blo 892572 1342793 := bstep (se 2 (by rfl) ⟨503547, by rfl⟩ : syracuseStep 1342793 = 1007095) B1007095
theorem B1342907 : Blo 892572 1342907 := bstep (se 1 (by rfl) ⟨1007180, by rfl⟩ : syracuseStep 1342907 = 2014361) B2014361
theorem B4521419 : Blo 892572 4521419 := bstep (se 1 (by rfl) ⟨3391064, by rfl⟩ : syracuseStep 4521419 = 6782129) B6782129
theorem B1342967 : Blo 892572 1342967 := bstep (se 1 (by rfl) ⟨1007225, by rfl⟩ : syracuseStep 1342967 = 2014451) B2014451
theorem B1342991 : Blo 892572 1342991 := bstep (se 1 (by rfl) ⟨1007243, by rfl⟩ : syracuseStep 1342991 = 2014487) B2014487
theorem B1343033 : Blo 892572 1343033 := bstep (se 2 (by rfl) ⟨503637, by rfl⟩ : syracuseStep 1343033 = 1007275) B1007275
theorem B1343111 : Blo 892572 1343111 := bstep (se 1 (by rfl) ⟨1007333, by rfl⟩ : syracuseStep 1343111 = 2014667) B2014667
theorem B1343147 : Blo 892572 1343147 := bstep (se 1 (by rfl) ⟨1007360, by rfl⟩ : syracuseStep 1343147 = 2014721) B2014721
theorem B1343177 : Blo 892572 1343177 := bstep (se 2 (by rfl) ⟨503691, by rfl⟩ : syracuseStep 1343177 = 1007383) B1007383
theorem B15269633 : Blo 892572 15269633 := bstep (se 2 (by rfl) ⟨5726112, by rfl⟩ : syracuseStep 15269633 = 11452225) B11452225
theorem B4521743 : Blo 892572 4521743 := bstep (se 1 (by rfl) ⟨3391307, by rfl⟩ : syracuseStep 4521743 = 6782615) B6782615
theorem B1343291 : Blo 892572 1343291 := bstep (se 1 (by rfl) ⟨1007468, by rfl⟩ : syracuseStep 1343291 = 2014937) B2014937
theorem B1343351 : Blo 892572 1343351 := bstep (se 1 (by rfl) ⟨1007513, by rfl⟩ : syracuseStep 1343351 = 2015027) B2015027
theorem B1507207 : Blo 892572 1507207 := bstep (se 1 (by rfl) ⟨1130405, by rfl⟩ : syracuseStep 1507207 = 2260811) B2260811
theorem B1343375 : Blo 892572 1343375 := bstep (se 1 (by rfl) ⟨1007531, by rfl⟩ : syracuseStep 1343375 = 2015063) B2015063
theorem B1343417 : Blo 892572 1343417 := bstep (se 2 (by rfl) ⟨503781, by rfl⟩ : syracuseStep 1343417 = 1007563) B1007563
theorem B3014657 : Blo 892572 3014657 := bstep (se 2 (by rfl) ⟨1130496, by rfl⟩ : syracuseStep 3014657 = 2260993) B2260993
theorem B1343567 : Blo 892572 1343567 := bstep (se 1 (by rfl) ⟨1007675, by rfl⟩ : syracuseStep 1343567 = 2015351) B2015351
theorem B7635059 : Blo 892572 7635059 := bstep (se 1 (by rfl) ⟨5726294, by rfl⟩ : syracuseStep 7635059 = 11452589) B11452589
theorem B1343687 : Blo 892572 1343687 := bstep (se 1 (by rfl) ⟨1007765, by rfl⟩ : syracuseStep 1343687 = 2015531) B2015531
theorem B1343849 : Blo 892572 1343849 := bstep (se 2 (by rfl) ⟨503943, by rfl⟩ : syracuseStep 1343849 = 1007887) B1007887
theorem B1507727 : Blo 892572 1507727 := bstep (se 1 (by rfl) ⟨1130795, by rfl⟩ : syracuseStep 1507727 = 2261591) B2261591
theorem B1343927 : Blo 892572 1343927 := bstep (se 1 (by rfl) ⟨1007945, by rfl⟩ : syracuseStep 1343927 = 2015891) B2015891
theorem B1343963 : Blo 892572 1343963 := bstep (se 1 (by rfl) ⟨1007972, by rfl⟩ : syracuseStep 1343963 = 2015945) B2015945
theorem B10191419 : Blo 892572 10191419 := bstep (se 1 (by rfl) ⟨7643564, by rfl⟩ : syracuseStep 10191419 = 15287129) B15287129
theorem B1507963 : Blo 892572 1507963 := bstep (se 1 (by rfl) ⟨1130972, by rfl⟩ : syracuseStep 1507963 = 2261945) B2261945
theorem B2261753 : Blo 892572 2261753 := bstep (se 2 (by rfl) ⟨848157, by rfl⟩ : syracuseStep 2261753 = 1696315) B1696315
theorem B3015467 : Blo 892572 3015467 := bstep (se 1 (by rfl) ⟨2261600, by rfl⟩ : syracuseStep 3015467 = 4523201) B4523201
theorem B1344431 : Blo 892572 1344431 := bstep (se 1 (by rfl) ⟨1008323, by rfl⟩ : syracuseStep 1344431 = 2016647) B2016647
theorem B1344521 : Blo 892572 1344521 := bstep (se 2 (by rfl) ⟨504195, by rfl⟩ : syracuseStep 1344521 = 1008391) B1008391
theorem B1344551 : Blo 892572 1344551 := bstep (se 1 (by rfl) ⟨1008413, by rfl⟩ : syracuseStep 1344551 = 2016827) B2016827
theorem B3015737 : Blo 892572 3015737 := bstep (se 2 (by rfl) ⟨1130901, by rfl⟩ : syracuseStep 3015737 = 2261803) B2261803
theorem B1344635 : Blo 892572 1344635 := bstep (se 1 (by rfl) ⟨1008476, by rfl⟩ : syracuseStep 1344635 = 2016953) B2016953
theorem B1344761 : Blo 892572 1344761 := bstep (se 2 (by rfl) ⟨504285, by rfl⟩ : syracuseStep 1344761 = 1008571) B1008571
theorem B918907 : Blo 892572 918907 := bstep (se 1 (by rfl) ⟨689180, by rfl⟩ : syracuseStep 918907 = 1378361) B1378361
theorem B3016061 : Blo 892572 3016061 := bstep (se 3 (by rfl) ⟨565511, by rfl⟩ : syracuseStep 3016061 = 1131023) B1131023
theorem B2262401 : Blo 892572 2262401 := bstep (se 2 (by rfl) ⟨848400, by rfl⟩ : syracuseStep 2262401 = 1696801) B1696801
theorem B1508827 : Blo 892572 1508827 := bstep (se 1 (by rfl) ⟨1131620, by rfl⟩ : syracuseStep 1508827 = 2263241) B2263241
theorem B3016331 : Blo 892572 3016331 := bstep (se 1 (by rfl) ⟨2262248, by rfl⟩ : syracuseStep 3016331 = 4524497) B4524497
theorem B1509455 : Blo 892572 1509455 := bstep (se 1 (by rfl) ⟨1132091, by rfl⟩ : syracuseStep 1509455 = 2264183) B2264183
theorem B2263211 : Blo 892572 2263211 := bstep (se 1 (by rfl) ⟨1697408, by rfl⟩ : syracuseStep 2263211 = 3394817) B3394817
theorem B3017249 : Blo 892572 3017249 := bstep (se 2 (by rfl) ⟨1131468, by rfl⟩ : syracuseStep 3017249 = 2262937) B2262937
theorem B22088393 : Blo 892572 22088393 := bstep (se 2 (by rfl) ⟨8283147, by rfl⟩ : syracuseStep 22088393 = 16566295) B16566295
theorem B3017465 : Blo 892572 3017465 := bstep (se 2 (by rfl) ⟨1131549, by rfl⟩ : syracuseStep 3017465 = 2263099) B2263099
theorem B12389213 : Blo 892572 12389213 := bstep (se 3 (by rfl) ⟨2322977, by rfl⟩ : syracuseStep 12389213 = 4645955) B4645955
theorem B1510319 : Blo 892572 1510319 := bstep (se 1 (by rfl) ⟨1132739, by rfl⟩ : syracuseStep 1510319 = 2265479) B2265479
theorem B5737391 : Blo 892572 5737391 := bstep (se 1 (by rfl) ⟨4303043, by rfl⟩ : syracuseStep 5737391 = 8606087) B8606087
theorem B4524983 : Blo 892572 4524983 := bstep (se 1 (by rfl) ⟨3393737, by rfl⟩ : syracuseStep 4524983 = 6787475) B6787475
theorem B3017735 : Blo 892572 3017735 := bstep (se 1 (by rfl) ⟨2263301, by rfl⟩ : syracuseStep 3017735 = 4526603) B4526603
theorem B2264071 : Blo 892572 2264071 := bstep (se 1 (by rfl) ⟨1698053, by rfl⟩ : syracuseStep 2264071 = 3396107) B3396107
theorem B3017843 : Blo 892572 3017843 := bstep (se 1 (by rfl) ⟨2263382, by rfl⟩ : syracuseStep 3017843 = 4526765) B4526765
theorem B1510751 : Blo 892572 1510751 := bstep (se 1 (by rfl) ⟨1133063, by rfl⟩ : syracuseStep 1510751 = 2266127) B2266127
theorem B3018113 : Blo 892572 3018113 := bstep (se 2 (by rfl) ⟨1131792, by rfl⟩ : syracuseStep 3018113 = 2263585) B2263585
theorem B921127 : Blo 892572 921127 := bstep (se 1 (by rfl) ⟨690845, by rfl⟩ : syracuseStep 921127 = 1381691) B1381691
theorem B6524513 : Blo 892572 6524513 := bstep (se 2 (by rfl) ⟨2446692, by rfl⟩ : syracuseStep 6524513 = 4893385) B4893385
theorem B2264699 : Blo 892572 2264699 := bstep (se 1 (by rfl) ⟨1698524, by rfl⟩ : syracuseStep 2264699 = 3397049) B3397049
theorem B12258955 : Blo 892572 12258955 := bstep (se 1 (by rfl) ⟨9194216, by rfl⟩ : syracuseStep 12258955 = 18388433) B18388433
theorem B1511311 : Blo 892572 1511311 := bstep (se 1 (by rfl) ⟨1133483, by rfl⟩ : syracuseStep 1511311 = 2266967) B2266967
theorem B2264993 : Blo 892572 2264993 := bstep (se 2 (by rfl) ⟨849372, by rfl⟩ : syracuseStep 2264993 = 1698745) B1698745
theorem B1609735 : Blo 892572 1609735 := bstep (se 1 (by rfl) ⟨1207301, by rfl⟩ : syracuseStep 1609735 = 2414603) B2414603
theorem B7639055 : Blo 892572 7639055 := bstep (se 1 (by rfl) ⟨5729291, by rfl⟩ : syracuseStep 7639055 = 11458583) B11458583
theorem B3018923 : Blo 892572 3018923 := bstep (se 1 (by rfl) ⟨2264192, by rfl⟩ : syracuseStep 3018923 = 4528385) B4528385
theorem B4526441 : Blo 892572 4526441 := bstep (se 2 (by rfl) ⟨1697415, by rfl⟩ : syracuseStep 4526441 = 3394831) B3394831
theorem B5083681 : Blo 892572 5083681 := bstep (se 2 (by rfl) ⟨1906380, by rfl⟩ : syracuseStep 5083681 = 3812761) B3812761
theorem B1610297 : Blo 892572 1610297 := bstep (se 2 (by rfl) ⟨603861, by rfl⟩ : syracuseStep 1610297 = 1207723) B1207723
theorem B1511993 : Blo 892572 1511993 := bstep (se 2 (by rfl) ⟨566997, by rfl⟩ : syracuseStep 1511993 = 1133995) B1133995
theorem B3019463 : Blo 892572 3019463 := bstep (se 1 (by rfl) ⟨2264597, by rfl⟩ : syracuseStep 3019463 = 4529195) B4529195
theorem B6460307 : Blo 892572 6460307 := bstep (se 1 (by rfl) ⟨4845230, by rfl⟩ : syracuseStep 6460307 = 9690461) B9690461
theorem B1381295 : Blo 892572 1381295 := bstep (se 1 (by rfl) ⟨1035971, by rfl⟩ : syracuseStep 1381295 = 2071943) B2071943
theorem B1610759 : Blo 892572 1610759 := bstep (se 1 (by rfl) ⟨1208069, by rfl⟩ : syracuseStep 1610759 = 2416139) B2416139
theorem B2036755 : Blo 892572 2036755 := bstep (se 1 (by rfl) ⟨1527566, by rfl⟩ : syracuseStep 2036755 = 3055133) B3055133
theorem B6460535 : Blo 892572 6460535 := bstep (se 1 (by rfl) ⟨4845401, by rfl⟩ : syracuseStep 6460535 = 9690803) B9690803
theorem B1512695 : Blo 892572 1512695 := bstep (se 1 (by rfl) ⟨1134521, by rfl⟩ : syracuseStep 1512695 = 2269043) B2269043
theorem B2299355 : Blo 892572 2299355 := bstep (se 1 (by rfl) ⟨1724516, by rfl⟩ : syracuseStep 2299355 = 3449033) B3449033
theorem B3020327 : Blo 892572 3020327 := bstep (se 1 (by rfl) ⟨2265245, by rfl⟩ : syracuseStep 3020327 = 4530491) B4530491
theorem B2266663 : Blo 892572 2266663 := bstep (se 1 (by rfl) ⟨1699997, by rfl⟩ : syracuseStep 2266663 = 3399995) B3399995
theorem B3020435 : Blo 892572 3020435 := bstep (se 1 (by rfl) ⟨2265326, by rfl⟩ : syracuseStep 3020435 = 4530653) B4530653
theorem B3020651 : Blo 892572 3020651 := bstep (se 1 (by rfl) ⟨2265488, by rfl⟩ : syracuseStep 3020651 = 4530977) B4530977
theorem B2266987 : Blo 892572 2266987 := bstep (se 1 (by rfl) ⟨1700240, by rfl⟩ : syracuseStep 2266987 = 3400481) B3400481
theorem B3020705 : Blo 892572 3020705 := bstep (se 2 (by rfl) ⟨1132764, by rfl⟩ : syracuseStep 3020705 = 2265529) B2265529
theorem B1906859 : Blo 892572 1906859 := bstep (se 1 (by rfl) ⟨1430144, by rfl⟩ : syracuseStep 1906859 = 2860289) B2860289
theorem B3021299 : Blo 892572 3021299 := bstep (se 1 (by rfl) ⟨2265974, by rfl⟩ : syracuseStep 3021299 = 4531949) B4531949
theorem B2267635 : Blo 892572 2267635 := bstep (se 1 (by rfl) ⟨1700726, by rfl⟩ : syracuseStep 2267635 = 3401453) B3401453
theorem B5741081 : Blo 892572 5741081 := bstep (se 2 (by rfl) ⟨2152905, by rfl⟩ : syracuseStep 5741081 = 4305811) B4305811
theorem B358390757 : Blo 892572 358390757 := bstep (se 4 (by rfl) ⟨33599133, by rfl⟩ : syracuseStep 358390757 = 67198267) B67198267
theorem B3021839 : Blo 892572 3021839 := bstep (se 1 (by rfl) ⟨2266379, by rfl⟩ : syracuseStep 3021839 = 4532759) B4532759
theorem B6790391 : Blo 892572 6790391 := bstep (se 1 (by rfl) ⟨5092793, by rfl⟩ : syracuseStep 6790391 = 10185587) B10185587
theorem B3055067 : Blo 892572 3055067 := bstep (se 1 (by rfl) ⟨2291300, by rfl⟩ : syracuseStep 3055067 = 4582601) B4582601
theorem B6888947 : Blo 892572 6888947 := bstep (se 1 (by rfl) ⟨5166710, by rfl⟩ : syracuseStep 6888947 = 10333421) B10333421
theorem B3022433 : Blo 892572 3022433 := bstep (se 2 (by rfl) ⟨1133412, by rfl⟩ : syracuseStep 3022433 = 2266825) B2266825
theorem B2268769 : Blo 892572 2268769 := bstep (se 2 (by rfl) ⟨850788, by rfl⟩ : syracuseStep 2268769 = 1701577) B1701577
theorem B11640439 : Blo 892572 11640439 := bstep (se 1 (by rfl) ⟨8730329, by rfl⟩ : syracuseStep 11640439 = 17460659) B17460659
theorem B892591 : Blo 892572 892591 := bstep (se 1 (by rfl) ⟨669443, by rfl⟩ : syracuseStep 892591 = 1338887) B1338887
theorem B892615 : Blo 892572 892615 := bstep (se 1 (by rfl) ⟨669461, by rfl⟩ : syracuseStep 892615 = 1338923) B1338923
theorem B892635 : Blo 892572 892635 := bstep (se 1 (by rfl) ⟨669476, by rfl⟩ : syracuseStep 892635 = 1338953) B1338953
theorem B6790877 : Blo 892572 6790877 := bstep (se 3 (by rfl) ⟨1273289, by rfl⟩ : syracuseStep 6790877 = 2546579) B2546579
theorem B627351317 : Blo 892572 627351317 := bstep (se 6 (by rfl) ⟨14703546, by rfl⟩ : syracuseStep 627351317 = 29407093) B29407093
theorem B892711 : Blo 892572 892711 := bstep (se 1 (by rfl) ⟨669533, by rfl⟩ : syracuseStep 892711 = 1339067) B1339067
theorem B892751 : Blo 892572 892751 := bstep (se 1 (by rfl) ⟨669563, by rfl⟩ : syracuseStep 892751 = 1339127) B1339127
theorem B892767 : Blo 892572 892767 := bstep (se 1 (by rfl) ⟨669575, by rfl⟩ : syracuseStep 892767 = 1339151) B1339151
theorem B892795 : Blo 892572 892795 := bstep (se 1 (by rfl) ⟨669596, by rfl⟩ : syracuseStep 892795 = 1339193) B1339193
theorem B892847 : Blo 892572 892847 := bstep (se 1 (by rfl) ⟨669635, by rfl⟩ : syracuseStep 892847 = 1339271) B1339271
theorem B892871 : Blo 892572 892871 := bstep (se 1 (by rfl) ⟨669653, by rfl⟩ : syracuseStep 892871 = 1339307) B1339307
theorem B892891 : Blo 892572 892891 := bstep (se 1 (by rfl) ⟨669668, by rfl⟩ : syracuseStep 892891 = 1339337) B1339337
theorem B5447695 : Blo 892572 5447695 := bstep (se 1 (by rfl) ⟨4085771, by rfl⟩ : syracuseStep 5447695 = 8171543) B8171543
theorem B892967 : Blo 892572 892967 := bstep (se 1 (by rfl) ⟨669725, by rfl⟩ : syracuseStep 892967 = 1339451) B1339451
theorem B893007 : Blo 892572 893007 := bstep (se 1 (by rfl) ⟨669755, by rfl⟩ : syracuseStep 893007 = 1339511) B1339511
theorem B893023 : Blo 892572 893023 := bstep (se 1 (by rfl) ⟨669767, by rfl⟩ : syracuseStep 893023 = 1339535) B1339535
theorem B893051 : Blo 892572 893051 := bstep (se 1 (by rfl) ⟨669788, by rfl⟩ : syracuseStep 893051 = 1339577) B1339577
theorem B893103 : Blo 892572 893103 := bstep (se 1 (by rfl) ⟨669827, by rfl⟩ : syracuseStep 893103 = 1339655) B1339655
theorem B893127 : Blo 892572 893127 := bstep (se 1 (by rfl) ⟨669845, by rfl⟩ : syracuseStep 893127 = 1339691) B1339691
theorem B893147 : Blo 892572 893147 := bstep (se 1 (by rfl) ⟨669860, by rfl⟩ : syracuseStep 893147 = 1339721) B1339721
theorem B893223 : Blo 892572 893223 := bstep (se 1 (by rfl) ⟨669917, by rfl⟩ : syracuseStep 893223 = 1339835) B1339835
theorem B893263 : Blo 892572 893263 := bstep (se 1 (by rfl) ⟨669947, by rfl⟩ : syracuseStep 893263 = 1339895) B1339895
theorem B893279 : Blo 892572 893279 := bstep (se 1 (by rfl) ⟨669959, by rfl⟩ : syracuseStep 893279 = 1339919) B1339919
theorem B893307 : Blo 892572 893307 := bstep (se 1 (by rfl) ⟨669980, by rfl⟩ : syracuseStep 893307 = 1339961) B1339961
theorem B893359 : Blo 892572 893359 := bstep (se 1 (by rfl) ⟨670019, by rfl⟩ : syracuseStep 893359 = 1340039) B1340039
theorem B893383 : Blo 892572 893383 := bstep (se 1 (by rfl) ⟨670037, by rfl⟩ : syracuseStep 893383 = 1340075) B1340075
theorem B893403 : Blo 892572 893403 := bstep (se 1 (by rfl) ⟨670052, by rfl⟩ : syracuseStep 893403 = 1340105) B1340105
theorem B893479 : Blo 892572 893479 := bstep (se 1 (by rfl) ⟨670109, by rfl⟩ : syracuseStep 893479 = 1340219) B1340219
theorem B893519 : Blo 892572 893519 := bstep (se 1 (by rfl) ⟨670139, by rfl⟩ : syracuseStep 893519 = 1340279) B1340279
theorem B893535 : Blo 892572 893535 := bstep (se 1 (by rfl) ⟨670151, by rfl⟩ : syracuseStep 893535 = 1340303) B1340303
theorem B10887797 : Blo 892572 10887797 := bstep (se 5 (by rfl) ⟨510365, by rfl⟩ : syracuseStep 10887797 = 1020731) B1020731
theorem B893563 : Blo 892572 893563 := bstep (se 1 (by rfl) ⟨670172, by rfl⟩ : syracuseStep 893563 = 1340345) B1340345
theorem B893615 : Blo 892572 893615 := bstep (se 1 (by rfl) ⟨670211, by rfl⟩ : syracuseStep 893615 = 1340423) B1340423
theorem B893639 : Blo 892572 893639 := bstep (se 1 (by rfl) ⟨670229, by rfl⟩ : syracuseStep 893639 = 1340459) B1340459
theorem B893659 : Blo 892572 893659 := bstep (se 1 (by rfl) ⟨670244, by rfl⟩ : syracuseStep 893659 = 1340489) B1340489
theorem B893735 : Blo 892572 893735 := bstep (se 1 (by rfl) ⟨670301, by rfl⟩ : syracuseStep 893735 = 1340603) B1340603
theorem B893775 : Blo 892572 893775 := bstep (se 1 (by rfl) ⟨670331, by rfl⟩ : syracuseStep 893775 = 1340663) B1340663
theorem B893791 : Blo 892572 893791 := bstep (se 1 (by rfl) ⟨670343, by rfl⟩ : syracuseStep 893791 = 1340687) B1340687
theorem B893819 : Blo 892572 893819 := bstep (se 1 (by rfl) ⟨670364, by rfl⟩ : syracuseStep 893819 = 1340729) B1340729
theorem B893871 : Blo 892572 893871 := bstep (se 1 (by rfl) ⟨670403, by rfl⟩ : syracuseStep 893871 = 1340807) B1340807
theorem B893895 : Blo 892572 893895 := bstep (se 1 (by rfl) ⟨670421, by rfl⟩ : syracuseStep 893895 = 1340843) B1340843
theorem B893915 : Blo 892572 893915 := bstep (se 1 (by rfl) ⟨670436, by rfl⟩ : syracuseStep 893915 = 1340873) B1340873
theorem B3023891 : Blo 892572 3023891 := bstep (se 1 (by rfl) ⟨2267918, by rfl⟩ : syracuseStep 3023891 = 4535837) B4535837
theorem B893991 : Blo 892572 893991 := bstep (se 1 (by rfl) ⟨670493, by rfl⟩ : syracuseStep 893991 = 1340987) B1340987
theorem B894031 : Blo 892572 894031 := bstep (se 1 (by rfl) ⟨670523, by rfl⟩ : syracuseStep 894031 = 1341047) B1341047
theorem B894047 : Blo 892572 894047 := bstep (se 1 (by rfl) ⟨670535, by rfl⟩ : syracuseStep 894047 = 1341071) B1341071
theorem B894075 : Blo 892572 894075 := bstep (se 1 (by rfl) ⟨670556, by rfl⟩ : syracuseStep 894075 = 1341113) B1341113
theorem B894127 : Blo 892572 894127 := bstep (se 1 (by rfl) ⟨670595, by rfl⟩ : syracuseStep 894127 = 1341191) B1341191
theorem B894151 : Blo 892572 894151 := bstep (se 1 (by rfl) ⟨670613, by rfl⟩ : syracuseStep 894151 = 1341227) B1341227
theorem B894171 : Blo 892572 894171 := bstep (se 1 (by rfl) ⟨670628, by rfl⟩ : syracuseStep 894171 = 1341257) B1341257
theorem B894247 : Blo 892572 894247 := bstep (se 1 (by rfl) ⟨670685, by rfl⟩ : syracuseStep 894247 = 1341371) B1341371
theorem B894287 : Blo 892572 894287 := bstep (se 1 (by rfl) ⟨670715, by rfl⟩ : syracuseStep 894287 = 1341431) B1341431
theorem B3024215 : Blo 892572 3024215 := bstep (se 1 (by rfl) ⟨2268161, by rfl⟩ : syracuseStep 3024215 = 4536323) B4536323
theorem B19375453 : Blo 892572 19375453 := bstep (se 3 (by rfl) ⟨3632897, by rfl⟩ : syracuseStep 19375453 = 7265795) B7265795
theorem B894303 : Blo 892572 894303 := bstep (se 1 (by rfl) ⟨670727, by rfl⟩ : syracuseStep 894303 = 1341455) B1341455
theorem B894331 : Blo 892572 894331 := bstep (se 1 (by rfl) ⟨670748, by rfl⟩ : syracuseStep 894331 = 1341497) B1341497
theorem B894383 : Blo 892572 894383 := bstep (se 1 (by rfl) ⟨670787, by rfl⟩ : syracuseStep 894383 = 1341575) B1341575
theorem B894407 : Blo 892572 894407 := bstep (se 1 (by rfl) ⟨670805, by rfl⟩ : syracuseStep 894407 = 1341611) B1341611
theorem B894427 : Blo 892572 894427 := bstep (se 1 (by rfl) ⟨670820, by rfl⟩ : syracuseStep 894427 = 1341641) B1341641
theorem B4597235 : Blo 892572 4597235 := bstep (se 1 (by rfl) ⟨3447926, by rfl⟩ : syracuseStep 4597235 = 6895853) B6895853
theorem B12396037 : Blo 892572 12396037 := bstep (se 4 (by rfl) ⟨1162128, by rfl⟩ : syracuseStep 12396037 = 2324257) B2324257
theorem B894503 : Blo 892572 894503 := bstep (se 1 (by rfl) ⟨670877, by rfl⟩ : syracuseStep 894503 = 1341755) B1341755
theorem B894543 : Blo 892572 894543 := bstep (se 1 (by rfl) ⟨670907, by rfl⟩ : syracuseStep 894543 = 1341815) B1341815
theorem B894559 : Blo 892572 894559 := bstep (se 1 (by rfl) ⟨670919, by rfl⟩ : syracuseStep 894559 = 1341839) B1341839
theorem B2008673 : Blo 892572 2008673 := bstep (se 2 (by rfl) ⟨753252, by rfl⟩ : syracuseStep 2008673 = 1506505) B1506505
theorem B894587 : Blo 892572 894587 := bstep (se 1 (by rfl) ⟨670940, by rfl⟩ : syracuseStep 894587 = 1341881) B1341881
theorem B894639 : Blo 892572 894639 := bstep (se 1 (by rfl) ⟨670979, by rfl⟩ : syracuseStep 894639 = 1341959) B1341959
theorem B894663 : Blo 892572 894663 := bstep (se 1 (by rfl) ⟨670997, by rfl⟩ : syracuseStep 894663 = 1341995) B1341995
theorem B3221201 : Blo 892572 3221201 := bstep (se 2 (by rfl) ⟨1207950, by rfl⟩ : syracuseStep 3221201 = 2415901) B2415901
theorem B894683 : Blo 892572 894683 := bstep (se 1 (by rfl) ⟨671012, by rfl⟩ : syracuseStep 894683 = 1342025) B1342025
theorem B2860829 : Blo 892572 2860829 := bstep (se 3 (by rfl) ⟨536405, by rfl⟩ : syracuseStep 2860829 = 1072811) B1072811
theorem B894759 : Blo 892572 894759 := bstep (se 1 (by rfl) ⟨671069, by rfl⟩ : syracuseStep 894759 = 1342139) B1342139
theorem B894799 : Blo 892572 894799 := bstep (se 1 (by rfl) ⟨671099, by rfl⟩ : syracuseStep 894799 = 1342199) B1342199
theorem B894815 : Blo 892572 894815 := bstep (se 1 (by rfl) ⟨671111, by rfl⟩ : syracuseStep 894815 = 1342223) B1342223
theorem B894843 : Blo 892572 894843 := bstep (se 1 (by rfl) ⟨671132, by rfl⟩ : syracuseStep 894843 = 1342265) B1342265
theorem B894895 : Blo 892572 894895 := bstep (se 1 (by rfl) ⟨671171, by rfl⟩ : syracuseStep 894895 = 1342343) B1342343
theorem B19343285 : Blo 892572 19343285 := bstep (se 5 (by rfl) ⟨906716, by rfl⟩ : syracuseStep 19343285 = 1813433) B1813433
theorem B2009015 : Blo 892572 2009015 := bstep (se 1 (by rfl) ⟨1506761, by rfl⟩ : syracuseStep 2009015 = 3013523) B3013523
theorem B894919 : Blo 892572 894919 := bstep (se 1 (by rfl) ⟨671189, by rfl⟩ : syracuseStep 894919 = 1342379) B1342379
theorem B894939 : Blo 892572 894939 := bstep (se 1 (by rfl) ⟨671204, by rfl⟩ : syracuseStep 894939 = 1342409) B1342409
theorem B895015 : Blo 892572 895015 := bstep (se 1 (by rfl) ⟨671261, by rfl⟩ : syracuseStep 895015 = 1342523) B1342523
theorem B895055 : Blo 892572 895055 := bstep (se 1 (by rfl) ⟨671291, by rfl⟩ : syracuseStep 895055 = 1342583) B1342583
theorem B895071 : Blo 892572 895071 := bstep (se 1 (by rfl) ⟨671303, by rfl⟩ : syracuseStep 895071 = 1342607) B1342607
theorem B895099 : Blo 892572 895099 := bstep (se 1 (by rfl) ⟨671324, by rfl⟩ : syracuseStep 895099 = 1342649) B1342649
theorem B895151 : Blo 892572 895151 := bstep (se 1 (by rfl) ⟨671363, by rfl⟩ : syracuseStep 895151 = 1342727) B1342727
theorem B895175 : Blo 892572 895175 := bstep (se 1 (by rfl) ⟨671381, by rfl⟩ : syracuseStep 895175 = 1342763) B1342763
theorem B895195 : Blo 892572 895195 := bstep (se 1 (by rfl) ⟨671396, by rfl⟩ : syracuseStep 895195 = 1342793) B1342793
theorem B895271 : Blo 892572 895271 := bstep (se 1 (by rfl) ⟨671453, by rfl⟩ : syracuseStep 895271 = 1342907) B1342907
theorem B895311 : Blo 892572 895311 := bstep (se 1 (by rfl) ⟨671483, by rfl⟩ : syracuseStep 895311 = 1342967) B1342967
theorem B895327 : Blo 892572 895327 := bstep (se 1 (by rfl) ⟨671495, by rfl⟩ : syracuseStep 895327 = 1342991) B1342991
theorem B895355 : Blo 892572 895355 := bstep (se 1 (by rfl) ⟨671516, by rfl⟩ : syracuseStep 895355 = 1343033) B1343033
theorem B3025295 : Blo 892572 3025295 := bstep (se 1 (by rfl) ⟨2268971, by rfl⟩ : syracuseStep 3025295 = 4537943) B4537943
theorem B895407 : Blo 892572 895407 := bstep (se 1 (by rfl) ⟨671555, by rfl⟩ : syracuseStep 895407 = 1343111) B1343111
theorem B895431 : Blo 892572 895431 := bstep (se 1 (by rfl) ⟨671573, by rfl⟩ : syracuseStep 895431 = 1343147) B1343147
theorem B895451 : Blo 892572 895451 := bstep (se 1 (by rfl) ⟨671588, by rfl⟩ : syracuseStep 895451 = 1343177) B1343177
theorem B2009609 : Blo 892572 2009609 := bstep (se 2 (by rfl) ⟨753603, by rfl⟩ : syracuseStep 2009609 = 1507207) B1507207
theorem B895527 : Blo 892572 895527 := bstep (se 1 (by rfl) ⟨671645, by rfl⟩ : syracuseStep 895527 = 1343291) B1343291
theorem B895567 : Blo 892572 895567 := bstep (se 1 (by rfl) ⟨671675, by rfl⟩ : syracuseStep 895567 = 1343351) B1343351
theorem B895583 : Blo 892572 895583 := bstep (se 1 (by rfl) ⟨671687, by rfl⟩ : syracuseStep 895583 = 1343375) B1343375
theorem B895611 : Blo 892572 895611 := bstep (se 1 (by rfl) ⟨671708, by rfl⟩ : syracuseStep 895611 = 1343417) B1343417
theorem B895663 : Blo 892572 895663 := bstep (se 1 (by rfl) ⟨671747, by rfl⟩ : syracuseStep 895663 = 1343495) B1343495
theorem B4532921 : Blo 892572 4532921 := bstep (se 2 (by rfl) ⟨1699845, by rfl⟩ : syracuseStep 4532921 = 3399691) B3399691
theorem B895687 : Blo 892572 895687 := bstep (se 1 (by rfl) ⟨671765, by rfl⟩ : syracuseStep 895687 = 1343531) B1343531
theorem B3025619 : Blo 892572 3025619 := bstep (se 1 (by rfl) ⟨2269214, by rfl⟩ : syracuseStep 3025619 = 4538429) B4538429
theorem B895707 : Blo 892572 895707 := bstep (se 1 (by rfl) ⟨671780, by rfl⟩ : syracuseStep 895707 = 1343561) B1343561
theorem B895783 : Blo 892572 895783 := bstep (se 1 (by rfl) ⟨671837, by rfl⟩ : syracuseStep 895783 = 1343675) B1343675
theorem B3058505 : Blo 892572 3058505 := bstep (se 2 (by rfl) ⟨1146939, by rfl⟩ : syracuseStep 3058505 = 2293879) B2293879
theorem B895823 : Blo 892572 895823 := bstep (se 1 (by rfl) ⟨671867, by rfl⟩ : syracuseStep 895823 = 1343735) B1343735
theorem B2009951 : Blo 892572 2009951 := bstep (se 1 (by rfl) ⟨1507463, by rfl⟩ : syracuseStep 2009951 = 3014927) B3014927
theorem B895839 : Blo 892572 895839 := bstep (se 1 (by rfl) ⟨671879, by rfl⟩ : syracuseStep 895839 = 1343759) B1343759
theorem B895867 : Blo 892572 895867 := bstep (se 1 (by rfl) ⟨671900, by rfl⟩ : syracuseStep 895867 = 1343801) B1343801
theorem B895919 : Blo 892572 895919 := bstep (se 1 (by rfl) ⟨671939, by rfl⟩ : syracuseStep 895919 = 1343879) B1343879
theorem B895943 : Blo 892572 895943 := bstep (se 1 (by rfl) ⟨671957, by rfl⟩ : syracuseStep 895943 = 1343915) B1343915
theorem B895963 : Blo 892572 895963 := bstep (se 1 (by rfl) ⟨671972, by rfl⟩ : syracuseStep 895963 = 1343945) B1343945
theorem B5975005 : Blo 892572 5975005 := bstep (se 3 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 5975005 = 2240627) B2240627
theorem B2010131 : Blo 892572 2010131 := bstep (se 1 (by rfl) ⟨1507598, by rfl⟩ : syracuseStep 2010131 = 3015197) B3015197
theorem B896039 : Blo 892572 896039 := bstep (se 1 (by rfl) ⟨672029, by rfl⟩ : syracuseStep 896039 = 1344059) B1344059
theorem B896079 : Blo 892572 896079 := bstep (se 1 (by rfl) ⟨672059, by rfl⟩ : syracuseStep 896079 = 1344119) B1344119
theorem B896095 : Blo 892572 896095 := bstep (se 1 (by rfl) ⟨672071, by rfl⟩ : syracuseStep 896095 = 1344143) B1344143
theorem B896123 : Blo 892572 896123 := bstep (se 1 (by rfl) ⟨672092, by rfl⟩ : syracuseStep 896123 = 1344185) B1344185
theorem B896175 : Blo 892572 896175 := bstep (se 1 (by rfl) ⟨672131, by rfl⟩ : syracuseStep 896175 = 1344263) B1344263
theorem B896199 : Blo 892572 896199 := bstep (se 1 (by rfl) ⟨672149, by rfl⟩ : syracuseStep 896199 = 1344299) B1344299
theorem B896219 : Blo 892572 896219 := bstep (se 1 (by rfl) ⟨672164, by rfl⟩ : syracuseStep 896219 = 1344329) B1344329
theorem B4304119 : Blo 892572 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B896295 : Blo 892572 896295 := bstep (se 1 (by rfl) ⟨672221, by rfl⟩ : syracuseStep 896295 = 1344443) B1344443
theorem B896335 : Blo 892572 896335 := bstep (se 1 (by rfl) ⟨672251, by rfl⟩ : syracuseStep 896335 = 1344503) B1344503
theorem B896351 : Blo 892572 896351 := bstep (se 1 (by rfl) ⟨672263, by rfl⟩ : syracuseStep 896351 = 1344527) B1344527
theorem B2010473 : Blo 892572 2010473 := bstep (se 2 (by rfl) ⟨753927, by rfl⟩ : syracuseStep 2010473 = 1507855) B1507855
theorem B896379 : Blo 892572 896379 := bstep (se 1 (by rfl) ⟨672284, by rfl⟩ : syracuseStep 896379 = 1344569) B1344569
theorem B896431 : Blo 892572 896431 := bstep (se 1 (by rfl) ⟨672323, by rfl⟩ : syracuseStep 896431 = 1344647) B1344647
theorem B896455 : Blo 892572 896455 := bstep (se 1 (by rfl) ⟨672341, by rfl⟩ : syracuseStep 896455 = 1344683) B1344683
theorem B896475 : Blo 892572 896475 := bstep (se 1 (by rfl) ⟨672356, by rfl⟩ : syracuseStep 896475 = 1344713) B1344713
theorem B3059225 : Blo 892572 3059225 := bstep (se 2 (by rfl) ⟨1147209, by rfl⟩ : syracuseStep 3059225 = 2294419) B2294419
theorem B896551 : Blo 892572 896551 := bstep (se 1 (by rfl) ⟨672413, by rfl⟩ : syracuseStep 896551 = 1344827) B1344827
theorem B6205177 : Blo 892572 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B4304735 : Blo 892572 4304735 := bstep (se 1 (by rfl) ⟨3228551, by rfl⟩ : syracuseStep 4304735 = 6457103) B6457103
theorem B2043743 : Blo 892572 2043743 := bstep (se 1 (by rfl) ⟨1532807, by rfl⟩ : syracuseStep 2043743 = 3065615) B3065615
theorem B2011067 : Blo 892572 2011067 := bstep (se 1 (by rfl) ⟨1508300, by rfl⟩ : syracuseStep 2011067 = 3016601) B3016601
theorem B2011193 : Blo 892572 2011193 := bstep (se 2 (by rfl) ⟨754197, by rfl⟩ : syracuseStep 2011193 = 1508395) B1508395
theorem B2011535 : Blo 892572 2011535 := bstep (se 1 (by rfl) ⟨1508651, by rfl⟩ : syracuseStep 2011535 = 3017303) B3017303
theorem B7647803 : Blo 892572 7647803 := bstep (se 1 (by rfl) ⟨5735852, by rfl⟩ : syracuseStep 7647803 = 11471705) B11471705
theorem B2011859 : Blo 892572 2011859 := bstep (se 1 (by rfl) ⟨1508894, by rfl⟩ : syracuseStep 2011859 = 3017789) B3017789
theorem B6796709 : Blo 892572 6796709 := bstep (se 4 (by rfl) ⟨637191, by rfl⟩ : syracuseStep 6796709 = 1274383) B1274383
theorem B8697289 : Blo 892572 8697289 := bstep (se 2 (by rfl) ⟨3261483, by rfl⟩ : syracuseStep 8697289 = 6522967) B6522967
theorem B7648829 : Blo 892572 7648829 := bstep (se 3 (by rfl) ⟨1434155, by rfl⟩ : syracuseStep 7648829 = 2868311) B2868311
theorem B2012795 : Blo 892572 2012795 := bstep (se 1 (by rfl) ⟨1509596, by rfl⟩ : syracuseStep 2012795 = 3019193) B3019193
theorem B2012921 : Blo 892572 2012921 := bstep (se 2 (by rfl) ⟨754845, by rfl⟩ : syracuseStep 2012921 = 1509691) B1509691
theorem B1914617 : Blo 892572 1914617 := bstep (se 2 (by rfl) ⟨717981, by rfl⟩ : syracuseStep 1914617 = 1435963) B1435963
theorem B3389303 : Blo 892572 3389303 := bstep (se 1 (by rfl) ⟨2541977, by rfl⟩ : syracuseStep 3389303 = 5083955) B5083955
theorem B1816507 : Blo 892572 1816507 := bstep (se 1 (by rfl) ⟨1362380, by rfl⟩ : syracuseStep 1816507 = 2724761) B2724761
theorem B10860551 : Blo 892572 10860551 := bstep (se 1 (by rfl) ⟨8145413, by rfl⟩ : syracuseStep 10860551 = 16290827) B16290827
theorem B2013191 : Blo 892572 2013191 := bstep (se 1 (by rfl) ⟨1509893, by rfl⟩ : syracuseStep 2013191 = 3019787) B3019787
theorem B2013263 : Blo 892572 2013263 := bstep (se 1 (by rfl) ⟨1509947, by rfl⟩ : syracuseStep 2013263 = 3019895) B3019895
theorem B1358299 : Blo 892572 1358299 := bstep (se 1 (by rfl) ⟨1018724, by rfl⟩ : syracuseStep 1358299 = 2037449) B2037449
theorem B2013659 : Blo 892572 2013659 := bstep (se 1 (by rfl) ⟨1510244, by rfl⟩ : syracuseStep 2013659 = 3020489) B3020489
theorem B3390275 : Blo 892572 3390275 := bstep (se 1 (by rfl) ⟨2542706, by rfl⟩ : syracuseStep 3390275 = 5085413) B5085413
theorem B3226463 : Blo 892572 3226463 := bstep (se 1 (by rfl) ⟨2419847, by rfl⟩ : syracuseStep 3226463 = 4839695) B4839695
theorem B3226475 : Blo 892572 3226475 := bstep (se 1 (by rfl) ⟨2419856, by rfl⟩ : syracuseStep 3226475 = 4839713) B4839713
theorem B2014127 : Blo 892572 2014127 := bstep (se 1 (by rfl) ⟨1510595, by rfl⟩ : syracuseStep 2014127 = 3021191) B3021191
theorem B46480445 : Blo 892572 46480445 := bstep (se 3 (by rfl) ⟨8715083, by rfl⟩ : syracuseStep 46480445 = 17430167) B17430167
theorem B2014379 : Blo 892572 2014379 := bstep (se 1 (by rfl) ⟨1510784, by rfl⟩ : syracuseStep 2014379 = 3021569) B3021569
theorem B3390731 : Blo 892572 3390731 := bstep (se 1 (by rfl) ⟨2543048, by rfl⟩ : syracuseStep 3390731 = 5086097) B5086097
theorem B4308349 : Blo 892572 4308349 := bstep (se 3 (by rfl) ⟨807815, by rfl⟩ : syracuseStep 4308349 = 1615631) B1615631
theorem B2145755 : Blo 892572 2145755 := bstep (se 1 (by rfl) ⟨1609316, by rfl⟩ : syracuseStep 2145755 = 3218633) B3218633
theorem B2866697 : Blo 892572 2866697 := bstep (se 2 (by rfl) ⟨1075011, by rfl⟩ : syracuseStep 2866697 = 2150023) B2150023
theorem B2866747 : Blo 892572 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B1130107 : Blo 892572 1130107 := bstep (se 1 (by rfl) ⟨847580, by rfl⟩ : syracuseStep 1130107 = 1695161) B1695161
theorem B2866877 : Blo 892572 2866877 := bstep (se 3 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 2866877 = 1075079) B1075079
theorem B2014919 : Blo 892572 2014919 := bstep (se 1 (by rfl) ⟨1511189, by rfl⟩ : syracuseStep 2014919 = 3022379) B3022379
theorem B6438649 : Blo 892572 6438649 := bstep (se 2 (by rfl) ⟨2414493, by rfl⟩ : syracuseStep 6438649 = 4828987) B4828987
theorem B4538105 : Blo 892572 4538105 := bstep (se 2 (by rfl) ⟨1701789, by rfl⟩ : syracuseStep 4538105 = 3403579) B3403579
theorem B5881643 : Blo 892572 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B3391415 : Blo 892572 3391415 := bstep (se 1 (by rfl) ⟨2543561, by rfl⟩ : syracuseStep 3391415 = 5087123) B5087123
theorem B82493761 : Blo 892572 82493761 := bstep (se 2 (by rfl) ⟨30935160, by rfl⟩ : syracuseStep 82493761 = 61870321) B61870321
theorem B4538753 : Blo 892572 4538753 := bstep (se 2 (by rfl) ⟨1702032, by rfl⟩ : syracuseStep 4538753 = 3404065) B3404065
theorem B2015783 : Blo 892572 2015783 := bstep (se 1 (by rfl) ⟨1511837, by rfl⟩ : syracuseStep 2015783 = 3023675) B3023675
theorem B3392189 : Blo 892572 3392189 := bstep (se 3 (by rfl) ⟨636035, by rfl⟩ : syracuseStep 3392189 = 1272071) B1272071
theorem B2016107 : Blo 892572 2016107 := bstep (se 1 (by rfl) ⟨1512080, by rfl⟩ : syracuseStep 2016107 = 3024161) B3024161
theorem B2016161 : Blo 892572 2016161 := bstep (se 2 (by rfl) ⟨756060, by rfl⟩ : syracuseStep 2016161 = 1512121) B1512121
theorem B7652555 : Blo 892572 7652555 := bstep (se 1 (by rfl) ⟨5739416, by rfl⟩ : syracuseStep 7652555 = 11478833) B11478833
theorem B2016503 : Blo 892572 2016503 := bstep (se 1 (by rfl) ⟨1512377, by rfl⟩ : syracuseStep 2016503 = 3024755) B3024755
theorem B3392873 : Blo 892572 3392873 := bstep (se 2 (by rfl) ⟨1272327, by rfl⟩ : syracuseStep 3392873 = 2544655) B2544655
theorem B1131995 : Blo 892572 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B10208915 : Blo 892572 10208915 := bstep (se 1 (by rfl) ⟨7656686, by rfl⟩ : syracuseStep 10208915 = 15313373) B15313373
theorem B2017097 : Blo 892572 2017097 := bstep (se 2 (by rfl) ⟨756411, by rfl⟩ : syracuseStep 2017097 = 1512823) B1512823
theorem B1132471 : Blo 892572 1132471 := bstep (se 1 (by rfl) ⟨849353, by rfl⟩ : syracuseStep 1132471 = 1698707) B1698707
theorem B6965185 : Blo 892572 6965185 := bstep (se 2 (by rfl) ⟨2611944, by rfl⟩ : syracuseStep 6965185 = 5223889) B5223889
theorem B6965477 : Blo 892572 6965477 := bstep (se 4 (by rfl) ⟨653013, by rfl⟩ : syracuseStep 6965477 = 1306027) B1306027
theorem B3623297 : Blo 892572 3623297 := bstep (se 2 (by rfl) ⟨1358736, by rfl⟩ : syracuseStep 3623297 = 2717473) B2717473
theorem B3819905 : Blo 892572 3819905 := bstep (se 2 (by rfl) ⟨1432464, by rfl⟩ : syracuseStep 3819905 = 2864929) B2864929
theorem B3230081 : Blo 892572 3230081 := bstep (se 2 (by rfl) ⟨1211280, by rfl⟩ : syracuseStep 3230081 = 2422561) B2422561
theorem B6375959 : Blo 892572 6375959 := bstep (se 1 (by rfl) ⟨4781969, by rfl⟩ : syracuseStep 6375959 = 9563939) B9563939
theorem B3066491 : Blo 892572 3066491 := bstep (se 1 (by rfl) ⟨2299868, by rfl⟩ : syracuseStep 3066491 = 4599737) B4599737
theorem B9652871 : Blo 892572 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B6802055 : Blo 892572 6802055 := bstep (se 1 (by rfl) ⟨5101541, by rfl⟩ : syracuseStep 6802055 = 10203083) B10203083
theorem B7359149 : Blo 892572 7359149 := bstep (se 3 (by rfl) ⟨1379840, by rfl⟩ : syracuseStep 7359149 = 2759681) B2759681
theorem B4836125 : Blo 892572 4836125 := bstep (se 3 (by rfl) ⟨906773, by rfl⟩ : syracuseStep 4836125 = 1813547) B1813547
theorem B2870387 : Blo 892572 2870387 := bstep (se 1 (by rfl) ⟨2152790, by rfl⟩ : syracuseStep 2870387 = 4305581) B4305581
theorem B1133767 : Blo 892572 1133767 := bstep (se 1 (by rfl) ⟨850325, by rfl⟩ : syracuseStep 1133767 = 1700651) B1700651
theorem B18599203 : Blo 892572 18599203 := bstep (se 1 (by rfl) ⟨13949402, by rfl⟩ : syracuseStep 18599203 = 27898805) B27898805
theorem B3395105 : Blo 892572 3395105 := bstep (se 2 (by rfl) ⟨1273164, by rfl⟩ : syracuseStep 3395105 = 2546329) B2546329
theorem B3395591 : Blo 892572 3395591 := bstep (se 1 (by rfl) ⟨2546693, by rfl⟩ : syracuseStep 3395591 = 5093387) B5093387
theorem B6803513 : Blo 892572 6803513 := bstep (se 2 (by rfl) ⟨2551317, by rfl⟩ : syracuseStep 6803513 = 5102635) B5102635
theorem B8605777 : Blo 892572 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B14373179 : Blo 892572 14373179 := bstep (se 1 (by rfl) ⟨10779884, by rfl⟩ : syracuseStep 14373179 = 21559769) B21559769
theorem B2412929 : Blo 892572 2412929 := bstep (se 2 (by rfl) ⟨904848, by rfl⟩ : syracuseStep 2412929 = 1809697) B1809697
theorem B3396077 : Blo 892572 3396077 := bstep (se 3 (by rfl) ⟨636764, by rfl⟩ : syracuseStep 3396077 = 1273529) B1273529
theorem B3396761 : Blo 892572 3396761 := bstep (se 2 (by rfl) ⟨1273785, by rfl⟩ : syracuseStep 3396761 = 2547571) B2547571
theorem B10179755 : Blo 892572 10179755 := bstep (se 1 (by rfl) ⟨7634816, by rfl⟩ : syracuseStep 10179755 = 15269633) B15269633
theorem B24466789 : Blo 892572 24466789 := bstep (se 4 (by rfl) ⟨2293761, by rfl⟩ : syracuseStep 24466789 = 4587523) B4587523
theorem B1430959 : Blo 892572 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B16307905 : Blo 892572 16307905 := bstep (se 2 (by rfl) ⟨6115464, by rfl⟩ : syracuseStep 16307905 = 12230929) B12230929
theorem B6805457 : Blo 892572 6805457 := bstep (se 2 (by rfl) ⟨2552046, by rfl⟩ : syracuseStep 6805457 = 5104093) B5104093
theorem B8148995 : Blo 892572 8148995 := bstep (se 1 (by rfl) ⟨6111746, by rfl⟩ : syracuseStep 8148995 = 12223493) B12223493
theorem B26171437 : Blo 892572 26171437 := bstep (se 3 (by rfl) ⟨4907144, by rfl⟩ : syracuseStep 26171437 = 9814289) B9814289
theorem B1431631 : Blo 892572 1431631 := bstep (se 1 (by rfl) ⟨1073723, by rfl⟩ : syracuseStep 1431631 = 2147447) B2147447
theorem B4413521 : Blo 892572 4413521 := bstep (se 2 (by rfl) ⟨1655070, by rfl⟩ : syracuseStep 4413521 = 3310141) B3310141
theorem B3397747 : Blo 892572 3397747 := bstep (se 1 (by rfl) ⟨2548310, by rfl⟩ : syracuseStep 3397747 = 5096621) B5096621
theorem B1005691 : Blo 892572 1005691 := bstep (se 1 (by rfl) ⟨754268, by rfl⟩ : syracuseStep 1005691 = 1508537) B1508537
theorem B2152619 : Blo 892572 2152619 := bstep (se 1 (by rfl) ⟨1614464, by rfl⟩ : syracuseStep 2152619 = 3228929) B3228929
theorem B1431913 : Blo 892572 1431913 := bstep (se 2 (by rfl) ⟨536967, by rfl⟩ : syracuseStep 1431913 = 1073935) B1073935
theorem B29350277 : Blo 892572 29350277 := bstep (se 4 (by rfl) ⟨2751588, by rfl⟩ : syracuseStep 29350277 = 5503177) B5503177
theorem B7625249 : Blo 892572 7625249 := bstep (se 2 (by rfl) ⟨2859468, by rfl⟩ : syracuseStep 7625249 = 5718937) B5718937
theorem B2415143 : Blo 892572 2415143 := bstep (se 1 (by rfl) ⟨1811357, by rfl⟩ : syracuseStep 2415143 = 3622715) B3622715
theorem B1006159 : Blo 892572 1006159 := bstep (se 1 (by rfl) ⟨754619, by rfl⟩ : syracuseStep 1006159 = 1509239) B1509239
theorem B2546387 : Blo 892572 2546387 := bstep (se 1 (by rfl) ⟨1909790, by rfl⟩ : syracuseStep 2546387 = 3819581) B3819581
theorem B3398507 : Blo 892572 3398507 := bstep (se 1 (by rfl) ⟨2548880, by rfl⟩ : syracuseStep 3398507 = 5097761) B5097761
theorem B1006555 : Blo 892572 1006555 := bstep (se 1 (by rfl) ⟨754916, by rfl⟩ : syracuseStep 1006555 = 1509833) B1509833
theorem B1531003 : Blo 892572 1531003 := bstep (se 1 (by rfl) ⟨1148252, by rfl⟩ : syracuseStep 1531003 = 2296505) B2296505
theorem B2612609 : Blo 892572 2612609 := bstep (se 2 (by rfl) ⟨979728, by rfl⟩ : syracuseStep 2612609 = 1959457) B1959457
theorem B1007023 : Blo 892572 1007023 := bstep (se 1 (by rfl) ⟨755267, by rfl⟩ : syracuseStep 1007023 = 1510535) B1510535
theorem B4087435 : Blo 892572 4087435 := bstep (se 1 (by rfl) ⟨3065576, by rfl⟩ : syracuseStep 4087435 = 6131153) B6131153
theorem B2547389 : Blo 892572 2547389 := bstep (se 3 (by rfl) ⟨477635, by rfl⟩ : syracuseStep 2547389 = 955271) B955271
theorem B5726011 : Blo 892572 5726011 := bstep (se 1 (by rfl) ⟨4294508, by rfl⟩ : syracuseStep 5726011 = 8589017) B8589017
theorem B1007455 : Blo 892572 1007455 := bstep (se 1 (by rfl) ⟨755591, by rfl⟩ : syracuseStep 1007455 = 1511183) B1511183
theorem B1695593 : Blo 892572 1695593 := bstep (se 2 (by rfl) ⟨635847, by rfl⟩ : syracuseStep 1695593 = 1271695) B1271695
theorem B2547719 : Blo 892572 2547719 := bstep (se 1 (by rfl) ⟨1910789, by rfl⟩ : syracuseStep 2547719 = 3821579) B3821579
theorem B10182671 : Blo 892572 10182671 := bstep (se 1 (by rfl) ⟨7637003, by rfl⟩ : syracuseStep 10182671 = 15274007) B15274007
theorem B6447185 : Blo 892572 6447185 := bstep (se 2 (by rfl) ⟨2417694, by rfl⟩ : syracuseStep 6447185 = 4835389) B4835389
theorem B1007815 : Blo 892572 1007815 := bstep (se 1 (by rfl) ⟨755861, by rfl⟩ : syracuseStep 1007815 = 1511723) B1511723
theorem B1433951 : Blo 892572 1433951 := bstep (se 1 (by rfl) ⟨1075463, by rfl⟩ : syracuseStep 1433951 = 2150927) B2150927
theorem B1434361 : Blo 892572 1434361 := bstep (se 2 (by rfl) ⟨537885, by rfl⟩ : syracuseStep 1434361 = 1075771) B1075771
theorem B1696619 : Blo 892572 1696619 := bstep (se 1 (by rfl) ⟨1272464, by rfl⟩ : syracuseStep 1696619 = 2544929) B2544929
theorem B9659357 : Blo 892572 9659357 := bstep (se 3 (by rfl) ⟨1811129, by rfl⟩ : syracuseStep 9659357 = 3622259) B3622259
theorem B1697287 : Blo 892572 1697287 := bstep (se 1 (by rfl) ⟨1272965, by rfl⟩ : syracuseStep 1697287 = 2545931) B2545931
theorem B5727959 : Blo 892572 5727959 := bstep (se 1 (by rfl) ⟨4295969, by rfl⟩ : syracuseStep 5727959 = 8591939) B8591939
theorem B5728573 : Blo 892572 5728573 := bstep (se 3 (by rfl) ⟨1074107, by rfl⟩ : syracuseStep 5728573 = 2148215) B2148215
theorem B26176135 : Blo 892572 26176135 := bstep (se 1 (by rfl) ⟨19632101, by rfl⟩ : syracuseStep 26176135 = 39264203) B39264203
theorem B11627185 : Blo 892572 11627185 := bstep (se 2 (by rfl) ⟨4360194, by rfl⟩ : syracuseStep 11627185 = 8720389) B8720389
theorem B3402425 : Blo 892572 3402425 := bstep (se 2 (by rfl) ⟨1275909, by rfl⟩ : syracuseStep 3402425 = 2551819) B2551819
theorem B2550487 : Blo 892572 2550487 := bstep (se 1 (by rfl) ⟨1912865, by rfl⟩ : syracuseStep 2550487 = 3825731) B3825731
theorem B2550521 : Blo 892572 2550521 := bstep (se 2 (by rfl) ⟨956445, by rfl⟩ : syracuseStep 2550521 = 1912891) B1912891
theorem B2550635 : Blo 892572 2550635 := bstep (se 1 (by rfl) ⟨1912976, by rfl⟩ : syracuseStep 2550635 = 3825953) B3825953
theorem B3435425 : Blo 892572 3435425 := bstep (se 2 (by rfl) ⟨1288284, by rfl⟩ : syracuseStep 3435425 = 2576569) B2576569
theorem B2550703 : Blo 892572 2550703 := bstep (se 1 (by rfl) ⟨1913027, by rfl⟩ : syracuseStep 2550703 = 3826055) B3826055
theorem B1338959 : Blo 892572 1338959 := bstep (se 1 (by rfl) ⟨1004219, by rfl⟩ : syracuseStep 1338959 = 2008439) B2008439
theorem B1699451 : Blo 892572 1699451 := bstep (se 1 (by rfl) ⟨1274588, by rfl⟩ : syracuseStep 1699451 = 2549177) B2549177
theorem B1339079 : Blo 892572 1339079 := bstep (se 1 (by rfl) ⟨1004309, by rfl⟩ : syracuseStep 1339079 = 2008619) B2008619
theorem B1699679 : Blo 892572 1699679 := bstep (se 1 (by rfl) ⟨1274759, by rfl⟩ : syracuseStep 1699679 = 2549519) B2549519
theorem B1339241 : Blo 892572 1339241 := bstep (se 2 (by rfl) ⟨502215, by rfl⟩ : syracuseStep 1339241 = 1004431) B1004431
theorem B9170819 : Blo 892572 9170819 := bstep (se 1 (by rfl) ⟨6878114, by rfl⟩ : syracuseStep 9170819 = 13756229) B13756229
theorem B1339319 : Blo 892572 1339319 := bstep (se 1 (by rfl) ⟨1004489, by rfl⟩ : syracuseStep 1339319 = 2008979) B2008979
theorem B1339355 : Blo 892572 1339355 := bstep (se 1 (by rfl) ⟨1004516, by rfl⟩ : syracuseStep 1339355 = 2009033) B2009033
theorem B1699937 : Blo 892572 1699937 := bstep (se 2 (by rfl) ⟨637476, by rfl⟩ : syracuseStep 1699937 = 1274953) B1274953
theorem B5730419 : Blo 892572 5730419 := bstep (se 1 (by rfl) ⟨4297814, by rfl⟩ : syracuseStep 5730419 = 8595629) B8595629
theorem B2551979 : Blo 892572 2551979 := bstep (se 1 (by rfl) ⟨1913984, by rfl⟩ : syracuseStep 2551979 = 3827969) B3827969
theorem B17166653 : Blo 892572 17166653 := bstep (se 3 (by rfl) ⟨3218747, by rfl⟩ : syracuseStep 17166653 = 6437495) B6437495
theorem B1700203 : Blo 892572 1700203 := bstep (se 1 (by rfl) ⟨1275152, by rfl⟩ : syracuseStep 1700203 = 2550305) B2550305
theorem B1339823 : Blo 892572 1339823 := bstep (se 1 (by rfl) ⟨1004867, by rfl⟩ : syracuseStep 1339823 = 2009735) B2009735
theorem B1274287 : Blo 892572 1274287 := bstep (se 1 (by rfl) ⟨955715, by rfl⟩ : syracuseStep 1274287 = 1911431) B1911431
theorem B1339913 : Blo 892572 1339913 := bstep (se 2 (by rfl) ⟨502467, by rfl⟩ : syracuseStep 1339913 = 1004935) B1004935
theorem B1339943 : Blo 892572 1339943 := bstep (se 1 (by rfl) ⟨1004957, by rfl⟩ : syracuseStep 1339943 = 2009915) B2009915
theorem B6451771 : Blo 892572 6451771 := bstep (se 1 (by rfl) ⟨4838828, by rfl⟩ : syracuseStep 6451771 = 9677657) B9677657
theorem B1340027 : Blo 892572 1340027 := bstep (se 1 (by rfl) ⟨1005020, by rfl⟩ : syracuseStep 1340027 = 2010041) B2010041
theorem B6451913 : Blo 892572 6451913 := bstep (se 2 (by rfl) ⟨2419467, by rfl⟩ : syracuseStep 6451913 = 4838935) B4838935
theorem B1340153 : Blo 892572 1340153 := bstep (se 2 (by rfl) ⟨502557, by rfl⟩ : syracuseStep 1340153 = 1005115) B1005115
theorem B1340255 : Blo 892572 1340255 := bstep (se 1 (by rfl) ⟨1005191, by rfl⟩ : syracuseStep 1340255 = 2010383) B2010383
theorem B1340267 : Blo 892572 1340267 := bstep (se 1 (by rfl) ⟨1005200, by rfl⟩ : syracuseStep 1340267 = 2010401) B2010401
theorem B17200025 : Blo 892572 17200025 := bstep (se 2 (by rfl) ⟨6450009, by rfl⟩ : syracuseStep 17200025 = 12900019) B12900019
theorem B12219437 : Blo 892572 12219437 := bstep (se 3 (by rfl) ⟨2291144, by rfl⟩ : syracuseStep 12219437 = 4582289) B4582289
theorem B7468081 : Blo 892572 7468081 := bstep (se 2 (by rfl) ⟨2800530, by rfl⟩ : syracuseStep 7468081 = 5601061) B5601061
theorem B65205323 : Blo 892572 65205323 := bstep (se 1 (by rfl) ⟨48903992, by rfl⟩ : syracuseStep 65205323 = 97807985) B97807985
theorem B1340495 : Blo 892572 1340495 := bstep (se 1 (by rfl) ⟨1005371, by rfl⟩ : syracuseStep 1340495 = 2010743) B2010743
theorem B6124663 : Blo 892572 6124663 := bstep (se 1 (by rfl) ⟨4593497, by rfl⟩ : syracuseStep 6124663 = 9186995) B9186995
theorem B4846787 : Blo 892572 4846787 := bstep (se 1 (by rfl) ⟨3635090, by rfl⟩ : syracuseStep 4846787 = 7270181) B7270181
theorem B1340615 : Blo 892572 1340615 := bstep (se 1 (by rfl) ⟨1005461, by rfl⟩ : syracuseStep 1340615 = 2010923) B2010923
theorem B1340777 : Blo 892572 1340777 := bstep (se 2 (by rfl) ⟨502791, by rfl⟩ : syracuseStep 1340777 = 1005583) B1005583
theorem B1340855 : Blo 892572 1340855 := bstep (se 1 (by rfl) ⟨1005641, by rfl⟩ : syracuseStep 1340855 = 2011283) B2011283
theorem B1340891 : Blo 892572 1340891 := bstep (se 1 (by rfl) ⟨1005668, by rfl⟩ : syracuseStep 1340891 = 2011337) B2011337
theorem B1701395 : Blo 892572 1701395 := bstep (se 1 (by rfl) ⟨1276046, by rfl⟩ : syracuseStep 1701395 = 2552093) B2552093
theorem B1275431 : Blo 892572 1275431 := bstep (se 1 (by rfl) ⟨956573, by rfl⟩ : syracuseStep 1275431 = 1913147) B1913147
theorem B10188503 : Blo 892572 10188503 := bstep (se 1 (by rfl) ⟨7641377, by rfl⟩ : syracuseStep 10188503 = 15282755) B15282755
theorem B1701623 : Blo 892572 1701623 := bstep (se 1 (by rfl) ⟨1276217, by rfl⟩ : syracuseStep 1701623 = 2552435) B2552435
theorem B3438443 : Blo 892572 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B4519799 : Blo 892572 4519799 := bstep (se 1 (by rfl) ⟨3389849, by rfl⟩ : syracuseStep 4519799 = 6779699) B6779699
theorem B6289271 : Blo 892572 6289271 := bstep (se 1 (by rfl) ⟨4716953, by rfl⟩ : syracuseStep 6289271 = 9433907) B9433907
theorem B1341359 : Blo 892572 1341359 := bstep (se 1 (by rfl) ⟨1006019, by rfl⟩ : syracuseStep 1341359 = 2012039) B2012039
theorem B1341449 : Blo 892572 1341449 := bstep (se 2 (by rfl) ⟨503043, by rfl⟩ : syracuseStep 1341449 = 1006087) B1006087
theorem B1341479 : Blo 892572 1341479 := bstep (se 1 (by rfl) ⟨1006109, by rfl⟩ : syracuseStep 1341479 = 2012219) B2012219
theorem B1210447 : Blo 892572 1210447 := bstep (se 1 (by rfl) ⟨907835, by rfl⟩ : syracuseStep 1210447 = 1815671) B1815671
theorem B5437529 : Blo 892572 5437529 := bstep (se 2 (by rfl) ⟨2039073, by rfl⟩ : syracuseStep 5437529 = 4078147) B4078147
theorem B1341563 : Blo 892572 1341563 := bstep (se 1 (by rfl) ⟨1006172, by rfl⟩ : syracuseStep 1341563 = 2012345) B2012345
theorem B6781157 : Blo 892572 6781157 := bstep (se 4 (by rfl) ⟨635733, by rfl⟩ : syracuseStep 6781157 = 1271467) B1271467
theorem B1341689 : Blo 892572 1341689 := bstep (se 2 (by rfl) ⟨503133, by rfl⟩ : syracuseStep 1341689 = 1006267) B1006267
theorem B3012875 : Blo 892572 3012875 := bstep (se 1 (by rfl) ⟨2259656, by rfl⟩ : syracuseStep 3012875 = 4519313) B4519313
theorem B1341791 : Blo 892572 1341791 := bstep (se 1 (by rfl) ⟨1006343, by rfl⟩ : syracuseStep 1341791 = 2012687) B2012687
theorem B1341803 : Blo 892572 1341803 := bstep (se 1 (by rfl) ⟨1006352, by rfl⟩ : syracuseStep 1341803 = 2012705) B2012705
theorem B3013145 : Blo 892572 3013145 := bstep (se 2 (by rfl) ⟨1129929, by rfl⟩ : syracuseStep 3013145 = 2259859) B2259859
theorem B1342031 : Blo 892572 1342031 := bstep (se 1 (by rfl) ⟨1006523, by rfl⟩ : syracuseStep 1342031 = 2013047) B2013047
theorem B1342151 : Blo 892572 1342151 := bstep (se 1 (by rfl) ⟨1006613, by rfl⟩ : syracuseStep 1342151 = 2013227) B2013227
theorem B1342313 : Blo 892572 1342313 := bstep (se 2 (by rfl) ⟨503367, by rfl⟩ : syracuseStep 1342313 = 1006735) B1006735
theorem B1342391 : Blo 892572 1342391 := bstep (se 1 (by rfl) ⟨1006793, by rfl⟩ : syracuseStep 1342391 = 2013587) B2013587
theorem B1506235 : Blo 892572 1506235 := bstep (se 1 (by rfl) ⟨1129676, by rfl⟩ : syracuseStep 1506235 = 2259353) B2259353
theorem B1342427 : Blo 892572 1342427 := bstep (se 1 (by rfl) ⟨1006820, by rfl⟩ : syracuseStep 1342427 = 2013641) B2013641
theorem B1506343 : Blo 892572 1506343 := bstep (se 1 (by rfl) ⟨1129757, by rfl⟩ : syracuseStep 1506343 = 2259515) B2259515
theorem B1637587 : Blo 892572 1637587 := bstep (se 1 (by rfl) ⟨1228190, by rfl⟩ : syracuseStep 1637587 = 2456381) B2456381
theorem B1506667 : Blo 892572 1506667 := bstep (se 1 (by rfl) ⟨1130000, by rfl⟩ : syracuseStep 1506667 = 2260001) B2260001
theorem B1342895 : Blo 892572 1342895 := bstep (se 1 (by rfl) ⟨1007171, by rfl⟩ : syracuseStep 1342895 = 2014343) B2014343
theorem B1342985 : Blo 892572 1342985 := bstep (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) B1007239
theorem B29359655 : Blo 892572 29359655 := bstep (se 1 (by rfl) ⟨22019741, by rfl⟩ : syracuseStep 29359655 = 44039483) B44039483
theorem B1343015 : Blo 892572 1343015 := bstep (se 1 (by rfl) ⟨1007261, by rfl⟩ : syracuseStep 1343015 = 2014523) B2014523
theorem B1343099 : Blo 892572 1343099 := bstep (se 1 (by rfl) ⟨1007324, by rfl⟩ : syracuseStep 1343099 = 2014649) B2014649
theorem B3014279 : Blo 892572 3014279 := bstep (se 1 (by rfl) ⟨2260709, by rfl⟩ : syracuseStep 3014279 = 4521419) B4521419
theorem B2260619 : Blo 892572 2260619 := bstep (se 1 (by rfl) ⟨1695464, by rfl⟩ : syracuseStep 2260619 = 3390929) B3390929
theorem B3014333 : Blo 892572 3014333 := bstep (se 3 (by rfl) ⟨565187, by rfl⟩ : syracuseStep 3014333 = 1130375) B1130375
theorem B1343225 : Blo 892572 1343225 := bstep (se 2 (by rfl) ⟨503709, by rfl⟩ : syracuseStep 1343225 = 1007419) B1007419
theorem B2260831 : Blo 892572 2260831 := bstep (se 1 (by rfl) ⟨1695623, by rfl⟩ : syracuseStep 2260831 = 3391247) B3391247
theorem B3014495 : Blo 892572 3014495 := bstep (se 1 (by rfl) ⟨2260871, by rfl⟩ : syracuseStep 3014495 = 4521743) B4521743
theorem B1343327 : Blo 892572 1343327 := bstep (se 1 (by rfl) ⟨1007495, by rfl⟩ : syracuseStep 1343327 = 2014991) B2014991
theorem B1343339 : Blo 892572 1343339 := bstep (se 1 (by rfl) ⟨1007504, by rfl⟩ : syracuseStep 1343339 = 2015009) B2015009
theorem B1343753 : Blo 892572 1343753 := bstep (se 2 (by rfl) ⟨503907, by rfl⟩ : syracuseStep 1343753 = 1007815) B1007815
theorem B1343855 : Blo 892572 1343855 := bstep (se 1 (by rfl) ⟨1007891, by rfl⟩ : syracuseStep 1343855 = 2015783) B2015783
theorem B6455717 : Blo 892572 6455717 := bstep (se 4 (by rfl) ⟨605223, by rfl⟩ : syracuseStep 6455717 = 1210447) B1210447
theorem B2261459 : Blo 892572 2261459 := bstep (se 1 (by rfl) ⟨1696094, by rfl⟩ : syracuseStep 2261459 = 3392189) B3392189
theorem B1507835 : Blo 892572 1507835 := bstep (se 1 (by rfl) ⟨1130876, by rfl⟩ : syracuseStep 1507835 = 2261753) B2261753
theorem B1344071 : Blo 892572 1344071 := bstep (se 1 (by rfl) ⟨1008053, by rfl⟩ : syracuseStep 1344071 = 2016107) B2016107
theorem B1344107 : Blo 892572 1344107 := bstep (se 1 (by rfl) ⟨1008080, by rfl⟩ : syracuseStep 1344107 = 2016161) B2016161
theorem B1344335 : Blo 892572 1344335 := bstep (se 1 (by rfl) ⟨1008251, by rfl⟩ : syracuseStep 1344335 = 2016503) B2016503
theorem B2261915 : Blo 892572 2261915 := bstep (se 1 (by rfl) ⟨1696436, by rfl⟩ : syracuseStep 2261915 = 3392873) B3392873
theorem B1508267 : Blo 892572 1508267 := bstep (se 1 (by rfl) ⟨1131200, by rfl⟩ : syracuseStep 1508267 = 2262401) B2262401
theorem B1344731 : Blo 892572 1344731 := bstep (se 1 (by rfl) ⟨1008548, by rfl⟩ : syracuseStep 1344731 = 2017097) B2017097
theorem B1508807 : Blo 892572 1508807 := bstep (se 1 (by rfl) ⟨1131605, by rfl⟩ : syracuseStep 1508807 = 2263211) B2263211
theorem B3016655 : Blo 892572 3016655 := bstep (se 1 (by rfl) ⟨2262491, by rfl⟩ : syracuseStep 3016655 = 4524983) B4524983
theorem B2263049 : Blo 892572 2263049 := bstep (se 2 (by rfl) ⟨848643, by rfl⟩ : syracuseStep 2263049 = 1697287) B1697287
theorem B2263403 : Blo 892572 2263403 := bstep (se 1 (by rfl) ⟨1697552, by rfl⟩ : syracuseStep 2263403 = 3395105) B3395105
theorem B1509799 : Blo 892572 1509799 := bstep (se 1 (by rfl) ⟨1132349, by rfl⟩ : syracuseStep 1509799 = 2264699) B2264699
theorem B7244261 : Blo 892572 7244261 := bstep (se 4 (by rfl) ⟨679149, by rfl⟩ : syracuseStep 7244261 = 1358299) B1358299
theorem B1509961 : Blo 892572 1509961 := bstep (se 2 (by rfl) ⟨566235, by rfl⟩ : syracuseStep 1509961 = 1132471) B1132471
theorem B1509995 : Blo 892572 1509995 := bstep (se 1 (by rfl) ⟨1132496, by rfl⟩ : syracuseStep 1509995 = 2264993) B2264993
theorem B2263727 : Blo 892572 2263727 := bstep (se 1 (by rfl) ⟨1697795, by rfl⟩ : syracuseStep 2263727 = 3395591) B3395591
theorem B3017627 : Blo 892572 3017627 := bstep (se 1 (by rfl) ⟨2263220, by rfl⟩ : syracuseStep 3017627 = 4526441) B4526441
theorem B1608619 : Blo 892572 1608619 := bstep (se 1 (by rfl) ⟨1206464, by rfl⟩ : syracuseStep 1608619 = 2412929) B2412929
theorem B2264051 : Blo 892572 2264051 := bstep (se 1 (by rfl) ⟨1698038, by rfl⟩ : syracuseStep 2264051 = 3396077) B3396077
theorem B7638097 : Blo 892572 7638097 := bstep (se 2 (by rfl) ⟨2864286, by rfl⟩ : syracuseStep 7638097 = 5728573) B5728573
theorem B920863 : Blo 892572 920863 := bstep (se 1 (by rfl) ⟨690647, by rfl⟩ : syracuseStep 920863 = 1381295) B1381295
theorem B2264507 : Blo 892572 2264507 := bstep (se 1 (by rfl) ⟨1698380, by rfl⟩ : syracuseStep 2264507 = 3396761) B3396761
theorem B6786503 : Blo 892572 6786503 := bstep (se 1 (by rfl) ⟨5089877, by rfl⟩ : syracuseStep 6786503 = 10179755) B10179755
theorem B34901513 : Blo 892572 34901513 := bstep (se 2 (by rfl) ⟨13088067, by rfl⟩ : syracuseStep 34901513 = 26176135) B26176135
theorem B15502913 : Blo 892572 15502913 := bstep (se 2 (by rfl) ⟨5813592, by rfl⟩ : syracuseStep 15502913 = 11627185) B11627185
theorem B3018653 : Blo 892572 3018653 := bstep (se 3 (by rfl) ⟨565997, by rfl⟩ : syracuseStep 3018653 = 1131995) B1131995
theorem B7966673 : Blo 892572 7966673 := bstep (se 2 (by rfl) ⟨2987502, by rfl⟩ : syracuseStep 7966673 = 5975005) B5975005
theorem B3018761 : Blo 892572 3018761 := bstep (se 2 (by rfl) ⟨1132035, by rfl⟩ : syracuseStep 3018761 = 2264071) B2264071
theorem B19566851 : Blo 892572 19566851 := bstep (se 1 (by rfl) ⟨14675138, by rfl⟩ : syracuseStep 19566851 = 29350277) B29350277
theorem B1511689 : Blo 892572 1511689 := bstep (se 2 (by rfl) ⟨566883, by rfl⟩ : syracuseStep 1511689 = 1133767) B1133767
theorem B5738825 : Blo 892572 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B5083499 : Blo 892572 5083499 := bstep (se 1 (by rfl) ⟨3812624, by rfl⟩ : syracuseStep 5083499 = 7625249) B7625249
theorem B2265671 : Blo 892572 2265671 := bstep (se 1 (by rfl) ⟨1699253, by rfl⟩ : syracuseStep 2265671 = 3398507) B3398507
theorem B4526927 : Blo 892572 4526927 := bstep (se 1 (by rfl) ⟨3395195, by rfl⟩ : syracuseStep 4526927 = 6790391) B6790391
theorem B1741739 : Blo 892572 1741739 := bstep (se 1 (by rfl) ⟨1306304, by rfl⟩ : syracuseStep 1741739 = 2612609) B2612609
theorem B2036711 : Blo 892572 2036711 := bstep (se 1 (by rfl) ⟨1527533, by rfl⟩ : syracuseStep 2036711 = 3055067) B3055067
theorem B4527251 : Blo 892572 4527251 := bstep (se 1 (by rfl) ⟨3395438, by rfl⟩ : syracuseStep 4527251 = 6790877) B6790877
theorem B6788447 : Blo 892572 6788447 := bstep (se 1 (by rfl) ⟨5091335, by rfl⟩ : syracuseStep 6788447 = 10182671) B10182671
theorem B4298123 : Blo 892572 4298123 := bstep (se 1 (by rfl) ⟨3223592, by rfl⟩ : syracuseStep 4298123 = 6447185) B6447185
theorem B11474369 : Blo 892572 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B955967 : Blo 892572 955967 := bstep (se 1 (by rfl) ⟨716975, by rfl⟩ : syracuseStep 955967 = 1433951) B1433951
theorem B5084957 : Blo 892572 5084957 := bstep (se 3 (by rfl) ⟨953429, by rfl⟩ : syracuseStep 5084957 = 1906859) B1906859
theorem B2266937 : Blo 892572 2266937 := bstep (se 2 (by rfl) ⟨850101, by rfl⟩ : syracuseStep 2266937 = 1700203) B1700203
theorem B1907219 : Blo 892572 1907219 := bstep (se 1 (by rfl) ⟨1430414, by rfl⟩ : syracuseStep 1907219 = 2860829) B2860829
theorem B8166217 : Blo 892572 8166217 := bstep (se 2 (by rfl) ⟨3062331, by rfl⟩ : syracuseStep 8166217 = 6124663) B6124663
theorem B99195749 : Blo 892572 99195749 := bstep (se 4 (by rfl) ⟨9299601, by rfl⟩ : syracuseStep 99195749 = 18599203) B18599203
theorem B3021947 : Blo 892572 3021947 := bstep (se 1 (by rfl) ⟨2266460, by rfl⟩ : syracuseStep 3021947 = 4532921) B4532921
theorem B2268283 : Blo 892572 2268283 := bstep (se 1 (by rfl) ⟨1701212, by rfl⟩ : syracuseStep 2268283 = 3402425) B3402425
theorem B2039003 : Blo 892572 2039003 := bstep (se 1 (by rfl) ⟨1529252, by rfl⟩ : syracuseStep 2039003 = 3058505) B3058505
theorem B1907945 : Blo 892572 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B3022217 : Blo 892572 3022217 := bstep (se 2 (by rfl) ⟨1133331, by rfl⟩ : syracuseStep 3022217 = 2266663) B2266663
theorem B33037901 : Blo 892572 33037901 := bstep (se 3 (by rfl) ⟨6194606, by rfl⟩ : syracuseStep 33037901 = 12389213) B12389213
theorem B2039483 : Blo 892572 2039483 := bstep (se 1 (by rfl) ⟨1529612, by rfl⟩ : syracuseStep 2039483 = 3059225) B3059225
theorem B892639 : Blo 892572 892639 := bstep (se 1 (by rfl) ⟨669479, by rfl⟩ : syracuseStep 892639 = 1338959) B1338959
theorem B892719 : Blo 892572 892719 := bstep (se 1 (by rfl) ⟨669539, by rfl⟩ : syracuseStep 892719 = 1339079) B1339079
theorem B3022649 : Blo 892572 3022649 := bstep (se 2 (by rfl) ⟨1133493, by rfl⟩ : syracuseStep 3022649 = 2266987) B2266987
theorem B892827 : Blo 892572 892827 := bstep (se 1 (by rfl) ⟨669620, by rfl⟩ : syracuseStep 892827 = 1339241) B1339241
theorem B892879 : Blo 892572 892879 := bstep (se 1 (by rfl) ⟨669659, by rfl⟩ : syracuseStep 892879 = 1339319) B1339319
theorem B892903 : Blo 892572 892903 := bstep (se 1 (by rfl) ⟨669677, by rfl⟩ : syracuseStep 892903 = 1339355) B1339355
theorem B1908841 : Blo 892572 1908841 := bstep (se 2 (by rfl) ⟨715815, by rfl⟩ : syracuseStep 1908841 = 1431631) B1431631
theorem B4530329 : Blo 892572 4530329 := bstep (se 2 (by rfl) ⟨1698873, by rfl⟩ : syracuseStep 4530329 = 3397747) B3397747
theorem B11444435 : Blo 892572 11444435 := bstep (se 1 (by rfl) ⟨8583326, by rfl⟩ : syracuseStep 11444435 = 17166653) B17166653
theorem B893215 : Blo 892572 893215 := bstep (se 1 (by rfl) ⟨669911, by rfl⟩ : syracuseStep 893215 = 1339823) B1339823
theorem B893275 : Blo 892572 893275 := bstep (se 1 (by rfl) ⟨669956, by rfl⟩ : syracuseStep 893275 = 1339913) B1339913
theorem B893295 : Blo 892572 893295 := bstep (se 1 (by rfl) ⟨669971, by rfl⟩ : syracuseStep 893295 = 1339943) B1339943
theorem B893351 : Blo 892572 893351 := bstep (se 1 (by rfl) ⟨670013, by rfl⟩ : syracuseStep 893351 = 1340027) B1340027
theorem B4301275 : Blo 892572 4301275 := bstep (se 1 (by rfl) ⟨3225956, by rfl⟩ : syracuseStep 4301275 = 6451913) B6451913
theorem B1909217 : Blo 892572 1909217 := bstep (se 2 (by rfl) ⟨715956, by rfl⟩ : syracuseStep 1909217 = 1431913) B1431913
theorem B893435 : Blo 892572 893435 := bstep (se 1 (by rfl) ⟨670076, by rfl⟩ : syracuseStep 893435 = 1340153) B1340153
theorem B893503 : Blo 892572 893503 := bstep (se 1 (by rfl) ⟨670127, by rfl⟩ : syracuseStep 893503 = 1340255) B1340255
theorem B893511 : Blo 892572 893511 := bstep (se 1 (by rfl) ⟨670133, by rfl⟩ : syracuseStep 893511 = 1340267) B1340267
theorem B3023513 : Blo 892572 3023513 := bstep (se 2 (by rfl) ⟨1133817, by rfl⟩ : syracuseStep 3023513 = 2267635) B2267635
theorem B893663 : Blo 892572 893663 := bstep (se 1 (by rfl) ⟨670247, by rfl⟩ : syracuseStep 893663 = 1340495) B1340495
theorem B893743 : Blo 892572 893743 := bstep (se 1 (by rfl) ⟨670307, by rfl⟩ : syracuseStep 893743 = 1340615) B1340615
theorem B893851 : Blo 892572 893851 := bstep (se 1 (by rfl) ⟨670388, by rfl⟩ : syracuseStep 893851 = 1340777) B1340777
theorem B4531139 : Blo 892572 4531139 := bstep (se 1 (by rfl) ⟨3398354, by rfl⟩ : syracuseStep 4531139 = 6796709) B6796709
theorem B893903 : Blo 892572 893903 := bstep (se 1 (by rfl) ⟨670427, by rfl⟩ : syracuseStep 893903 = 1340855) B1340855
theorem B893927 : Blo 892572 893927 := bstep (se 1 (by rfl) ⟨670445, by rfl⟩ : syracuseStep 893927 = 1340891) B1340891
theorem B21799925 : Blo 892572 21799925 := bstep (se 5 (by rfl) ⟨1021871, by rfl⟩ : syracuseStep 21799925 = 2043743) B2043743
theorem B6792335 : Blo 892572 6792335 := bstep (se 1 (by rfl) ⟨5094251, by rfl⟩ : syracuseStep 6792335 = 10188503) B10188503
theorem B2008313 : Blo 892572 2008313 := bstep (se 2 (by rfl) ⟨753117, by rfl⟩ : syracuseStep 2008313 = 1506235) B1506235
theorem B894239 : Blo 892572 894239 := bstep (se 1 (by rfl) ⟨670679, by rfl⟩ : syracuseStep 894239 = 1341359) B1341359
theorem B894299 : Blo 892572 894299 := bstep (se 1 (by rfl) ⟨670724, by rfl⟩ : syracuseStep 894299 = 1341449) B1341449
theorem B894319 : Blo 892572 894319 := bstep (se 1 (by rfl) ⟨670739, by rfl⟩ : syracuseStep 894319 = 1341479) B1341479
theorem B2008457 : Blo 892572 2008457 := bstep (se 2 (by rfl) ⟨753171, by rfl⟩ : syracuseStep 2008457 = 1506343) B1506343
theorem B894375 : Blo 892572 894375 := bstep (se 1 (by rfl) ⟨670781, by rfl⟩ : syracuseStep 894375 = 1341563) B1341563
theorem B2041337 : Blo 892572 2041337 := bstep (se 2 (by rfl) ⟨765501, by rfl⟩ : syracuseStep 2041337 = 1531003) B1531003
theorem B894459 : Blo 892572 894459 := bstep (se 1 (by rfl) ⟨670844, by rfl⟩ : syracuseStep 894459 = 1341689) B1341689
theorem B2008583 : Blo 892572 2008583 := bstep (se 1 (by rfl) ⟨1506437, by rfl⟩ : syracuseStep 2008583 = 3012875) B3012875
theorem B894527 : Blo 892572 894527 := bstep (se 1 (by rfl) ⟨670895, by rfl⟩ : syracuseStep 894527 = 1341791) B1341791
theorem B894535 : Blo 892572 894535 := bstep (se 1 (by rfl) ⟨670901, by rfl⟩ : syracuseStep 894535 = 1341803) B1341803
theorem B2008763 : Blo 892572 2008763 := bstep (se 1 (by rfl) ⟨1506572, by rfl⟩ : syracuseStep 2008763 = 3013145) B3013145
theorem B894687 : Blo 892572 894687 := bstep (se 1 (by rfl) ⟨671015, by rfl⟩ : syracuseStep 894687 = 1342031) B1342031
theorem B894767 : Blo 892572 894767 := bstep (se 1 (by rfl) ⟨671075, by rfl⟩ : syracuseStep 894767 = 1342151) B1342151
theorem B2008889 : Blo 892572 2008889 := bstep (se 2 (by rfl) ⟨753333, by rfl⟩ : syracuseStep 2008889 = 1506667) B1506667
theorem B5744465 : Blo 892572 5744465 := bstep (se 2 (by rfl) ⟨2154174, by rfl⟩ : syracuseStep 5744465 = 4308349) B4308349
theorem B894875 : Blo 892572 894875 := bstep (se 1 (by rfl) ⟨671156, by rfl⟩ : syracuseStep 894875 = 1342313) B1342313
theorem B894927 : Blo 892572 894927 := bstep (se 1 (by rfl) ⟨671195, by rfl⟩ : syracuseStep 894927 = 1342391) B1342391
theorem B894951 : Blo 892572 894951 := bstep (se 1 (by rfl) ⟨671213, by rfl⟩ : syracuseStep 894951 = 1342427) B1342427
theorem B3025025 : Blo 892572 3025025 := bstep (se 2 (by rfl) ⟨1134384, by rfl⟩ : syracuseStep 3025025 = 2268769) B2268769
theorem B5449913 : Blo 892572 5449913 := bstep (se 2 (by rfl) ⟨2043717, by rfl⟩ : syracuseStep 5449913 = 4087435) B4087435
theorem B895263 : Blo 892572 895263 := bstep (se 1 (by rfl) ⟨671447, by rfl⟩ : syracuseStep 895263 = 1342895) B1342895
theorem B1911131 : Blo 892572 1911131 := bstep (se 1 (by rfl) ⟨1433348, by rfl⟩ : syracuseStep 1911131 = 2866697) B2866697
theorem B895323 : Blo 892572 895323 := bstep (se 1 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 895323 = 1342985) B1342985
theorem B19573103 : Blo 892572 19573103 := bstep (se 1 (by rfl) ⟨14679827, by rfl⟩ : syracuseStep 19573103 = 29359655) B29359655
theorem B895343 : Blo 892572 895343 := bstep (se 1 (by rfl) ⟨671507, by rfl⟩ : syracuseStep 895343 = 1343015) B1343015
theorem B895399 : Blo 892572 895399 := bstep (se 1 (by rfl) ⟨671549, by rfl⟩ : syracuseStep 895399 = 1343099) B1343099
theorem B2009519 : Blo 892572 2009519 := bstep (se 1 (by rfl) ⟨1507139, by rfl⟩ : syracuseStep 2009519 = 3014279) B3014279
theorem B2009555 : Blo 892572 2009555 := bstep (se 1 (by rfl) ⟨1507166, by rfl⟩ : syracuseStep 2009555 = 3014333) B3014333
theorem B1911251 : Blo 892572 1911251 := bstep (se 1 (by rfl) ⟨1433438, by rfl⟩ : syracuseStep 1911251 = 2866877) B2866877
theorem B895483 : Blo 892572 895483 := bstep (se 1 (by rfl) ⟨671612, by rfl⟩ : syracuseStep 895483 = 1343225) B1343225
theorem B3025403 : Blo 892572 3025403 := bstep (se 1 (by rfl) ⟨2269052, by rfl⟩ : syracuseStep 3025403 = 4538105) B4538105
theorem B2009663 : Blo 892572 2009663 := bstep (se 1 (by rfl) ⟨1507247, by rfl⟩ : syracuseStep 2009663 = 3014495) B3014495
theorem B895551 : Blo 892572 895551 := bstep (se 1 (by rfl) ⟨671663, by rfl⟩ : syracuseStep 895551 = 1343327) B1343327
theorem B895559 : Blo 892572 895559 := bstep (se 1 (by rfl) ⟨671669, by rfl⟩ : syracuseStep 895559 = 1343339) B1343339
theorem B2009771 : Blo 892572 2009771 := bstep (se 1 (by rfl) ⟨1507328, by rfl⟩ : syracuseStep 2009771 = 3014657) B3014657
theorem B895711 : Blo 892572 895711 := bstep (se 1 (by rfl) ⟨671783, by rfl⟩ : syracuseStep 895711 = 1343567) B1343567
theorem B5090039 : Blo 892572 5090039 := bstep (se 1 (by rfl) ⟨3817529, by rfl⟩ : syracuseStep 5090039 = 7635059) B7635059
theorem B895791 : Blo 892572 895791 := bstep (se 1 (by rfl) ⟨671843, by rfl⟩ : syracuseStep 895791 = 1343687) B1343687
theorem B895899 : Blo 892572 895899 := bstep (se 1 (by rfl) ⟨671924, by rfl⟩ : syracuseStep 895899 = 1343849) B1343849
theorem B3025835 : Blo 892572 3025835 := bstep (se 1 (by rfl) ⟨2269376, by rfl⟩ : syracuseStep 3025835 = 4538753) B4538753
theorem B895951 : Blo 892572 895951 := bstep (se 1 (by rfl) ⟨671963, by rfl⟩ : syracuseStep 895951 = 1343927) B1343927
theorem B895975 : Blo 892572 895975 := bstep (se 1 (by rfl) ⟨671981, by rfl⟩ : syracuseStep 895975 = 1343963) B1343963
theorem B6794279 : Blo 892572 6794279 := bstep (se 1 (by rfl) ⟨5095709, by rfl⟩ : syracuseStep 6794279 = 10191419) B10191419
theorem B2010311 : Blo 892572 2010311 := bstep (se 1 (by rfl) ⟨1507733, by rfl⟩ : syracuseStep 2010311 = 3015467) B3015467
theorem B896287 : Blo 892572 896287 := bstep (se 1 (by rfl) ⟨672215, by rfl⟩ : syracuseStep 896287 = 1344431) B1344431
theorem B896347 : Blo 892572 896347 := bstep (se 1 (by rfl) ⟨672260, by rfl⟩ : syracuseStep 896347 = 1344521) B1344521
theorem B896367 : Blo 892572 896367 := bstep (se 1 (by rfl) ⟨672275, by rfl⟩ : syracuseStep 896367 = 1344551) B1344551
theorem B2010491 : Blo 892572 2010491 := bstep (se 1 (by rfl) ⟨1507868, by rfl⟩ : syracuseStep 2010491 = 3015737) B3015737
theorem B896423 : Blo 892572 896423 := bstep (se 1 (by rfl) ⟨672317, by rfl⟩ : syracuseStep 896423 = 1344635) B1344635
theorem B2010617 : Blo 892572 2010617 := bstep (se 2 (by rfl) ⟨753981, by rfl⟩ : syracuseStep 2010617 = 1507963) B1507963
theorem B896507 : Blo 892572 896507 := bstep (se 1 (by rfl) ⟨672380, by rfl⟩ : syracuseStep 896507 = 1344761) B1344761
theorem B2010707 : Blo 892572 2010707 := bstep (se 1 (by rfl) ⟨1508030, by rfl⟩ : syracuseStep 2010707 = 3016061) B3016061
theorem B1912481 : Blo 892572 1912481 := bstep (se 2 (by rfl) ⟨717180, by rfl⟩ : syracuseStep 1912481 = 1434361) B1434361
theorem B2010887 : Blo 892572 2010887 := bstep (se 1 (by rfl) ⟨1508165, by rfl⟩ : syracuseStep 2010887 = 3016331) B3016331
theorem B2011499 : Blo 892572 2011499 := bstep (se 1 (by rfl) ⟨1508624, by rfl⟩ : syracuseStep 2011499 = 3017249) B3017249
theorem B2044327 : Blo 892572 2044327 := bstep (se 1 (by rfl) ⟨1533245, by rfl⟩ : syracuseStep 2044327 = 3066491) B3066491
theorem B4534703 : Blo 892572 4534703 := bstep (se 1 (by rfl) ⟨3401027, by rfl⟩ : syracuseStep 4534703 = 6802055) B6802055
theorem B25833937 : Blo 892572 25833937 := bstep (se 2 (by rfl) ⟨9687726, by rfl⟩ : syracuseStep 25833937 = 19375453) B19375453
theorem B14725595 : Blo 892572 14725595 := bstep (se 1 (by rfl) ⟨11044196, by rfl⟩ : syracuseStep 14725595 = 22088393) B22088393
theorem B2011643 : Blo 892572 2011643 := bstep (se 1 (by rfl) ⟨1508732, by rfl⟩ : syracuseStep 2011643 = 3017465) B3017465
theorem B3224083 : Blo 892572 3224083 := bstep (se 1 (by rfl) ⟨2418062, by rfl⟩ : syracuseStep 3224083 = 4836125) B4836125
theorem B2011769 : Blo 892572 2011769 := bstep (se 2 (by rfl) ⟨754413, by rfl⟩ : syracuseStep 2011769 = 1508827) B1508827
theorem B2011823 : Blo 892572 2011823 := bstep (se 1 (by rfl) ⟨1508867, by rfl⟩ : syracuseStep 2011823 = 3017735) B3017735
theorem B16528049 : Blo 892572 16528049 := bstep (se 2 (by rfl) ⟨6198018, by rfl⟩ : syracuseStep 16528049 = 12396037) B12396037
theorem B2011895 : Blo 892572 2011895 := bstep (se 1 (by rfl) ⟨1508921, by rfl⟩ : syracuseStep 2011895 = 3017843) B3017843
theorem B1913591 : Blo 892572 1913591 := bstep (se 1 (by rfl) ⟨1435193, by rfl⟩ : syracuseStep 1913591 = 2870387) B2870387
theorem B2012075 : Blo 892572 2012075 := bstep (se 1 (by rfl) ⟨1509056, by rfl⟩ : syracuseStep 2012075 = 3018113) B3018113
theorem B9286913 : Blo 892572 9286913 := bstep (se 2 (by rfl) ⟨3482592, by rfl⟩ : syracuseStep 9286913 = 6965185) B6965185
theorem B5092703 : Blo 892572 5092703 := bstep (se 1 (by rfl) ⟨3819527, by rfl⟩ : syracuseStep 5092703 = 7639055) B7639055
theorem B4535675 : Blo 892572 4535675 := bstep (se 1 (by rfl) ⟨3401756, by rfl⟩ : syracuseStep 4535675 = 6803513) B6803513
theorem B2012615 : Blo 892572 2012615 := bstep (se 1 (by rfl) ⟨1509461, by rfl⟩ : syracuseStep 2012615 = 3018923) B3018923
theorem B9582119 : Blo 892572 9582119 := bstep (se 1 (by rfl) ⟨7186589, by rfl⟩ : syracuseStep 9582119 = 14373179) B14373179
theorem B2012975 : Blo 892572 2012975 := bstep (se 1 (by rfl) ⟨1509731, by rfl⟩ : syracuseStep 2012975 = 3019463) B3019463
theorem B4306871 : Blo 892572 4306871 := bstep (se 1 (by rfl) ⟨3230153, by rfl⟩ : syracuseStep 4306871 = 6460307) B6460307
theorem B4307023 : Blo 892572 4307023 := bstep (se 1 (by rfl) ⟨3230267, by rfl⟩ : syracuseStep 4307023 = 6460535) B6460535
theorem B2013551 : Blo 892572 2013551 := bstep (se 1 (by rfl) ⟨1510163, by rfl⟩ : syracuseStep 2013551 = 3020327) B3020327
theorem B2013623 : Blo 892572 2013623 := bstep (se 1 (by rfl) ⟨1510217, by rfl⟩ : syracuseStep 2013623 = 3020435) B3020435
theorem B2013767 : Blo 892572 2013767 := bstep (se 1 (by rfl) ⟨1510325, by rfl⟩ : syracuseStep 2013767 = 3020651) B3020651
theorem B2013803 : Blo 892572 2013803 := bstep (se 1 (by rfl) ⟨1510352, by rfl⟩ : syracuseStep 2013803 = 3020705) B3020705
theorem B4536971 : Blo 892572 4536971 := bstep (se 1 (by rfl) ⟨3402728, by rfl⟩ : syracuseStep 4536971 = 6805457) B6805457
theorem B2014199 : Blo 892572 2014199 := bstep (se 1 (by rfl) ⟨1510649, by rfl⟩ : syracuseStep 2014199 = 3021299) B3021299
theorem B238927171 : Blo 892572 238927171 := bstep (se 1 (by rfl) ⟨179195378, by rfl⟩ : syracuseStep 238927171 = 358390757) B358390757
theorem B2014559 : Blo 892572 2014559 := bstep (se 1 (by rfl) ⟨1510919, by rfl⟩ : syracuseStep 2014559 = 3021839) B3021839
theorem B1228169 : Blo 892572 1228169 := bstep (se 2 (by rfl) ⟨460563, by rfl⟩ : syracuseStep 1228169 = 921127) B921127
theorem B2014955 : Blo 892572 2014955 := bstep (se 1 (by rfl) ⟨1511216, by rfl⟩ : syracuseStep 2014955 = 3022433) B3022433
theorem B418234211 : Blo 892572 418234211 := bstep (se 1 (by rfl) ⟨313675658, by rfl⟩ : syracuseStep 418234211 = 627351317) B627351317
theorem B2015081 : Blo 892572 2015081 := bstep (se 2 (by rfl) ⟨755655, by rfl⟩ : syracuseStep 2015081 = 1511311) B1511311
theorem B2146313 : Blo 892572 2146313 := bstep (se 2 (by rfl) ⟨804867, by rfl⟩ : syracuseStep 2146313 = 1609735) B1609735
theorem B10862693 : Blo 892572 10862693 := bstep (se 4 (by rfl) ⟨1018377, by rfl⟩ : syracuseStep 10862693 = 2036755) B2036755
theorem B39829765 : Blo 892572 39829765 := bstep (se 4 (by rfl) ⟨3734040, by rfl⟩ : syracuseStep 39829765 = 7468081) B7468081
theorem B7258531 : Blo 892572 7258531 := bstep (se 1 (by rfl) ⟨5443898, by rfl⟩ : syracuseStep 7258531 = 10887797) B10887797
theorem B1131079 : Blo 892572 1131079 := bstep (se 1 (by rfl) ⟨848309, by rfl⟩ : syracuseStep 1131079 = 1696619) B1696619
theorem B6439571 : Blo 892572 6439571 := bstep (se 1 (by rfl) ⟨4829678, by rfl⟩ : syracuseStep 6439571 = 9659357) B9659357
theorem B2015927 : Blo 892572 2015927 := bstep (se 1 (by rfl) ⟨1511945, by rfl⟩ : syracuseStep 2015927 = 3023891) B3023891
theorem B8602361 : Blo 892572 8602361 := bstep (se 2 (by rfl) ⟨3225885, by rfl⟩ : syracuseStep 8602361 = 6451771) B6451771
theorem B2016143 : Blo 892572 2016143 := bstep (se 1 (by rfl) ⟨1512107, by rfl⟩ : syracuseStep 2016143 = 3024215) B3024215
theorem B3064823 : Blo 892572 3064823 := bstep (se 1 (by rfl) ⟨2298617, by rfl⟩ : syracuseStep 3064823 = 4597235) B4597235
theorem B2147467 : Blo 892572 2147467 := bstep (se 1 (by rfl) ⟨1610600, by rfl⟩ : syracuseStep 2147467 = 3221201) B3221201
theorem B3818639 : Blo 892572 3818639 := bstep (se 1 (by rfl) ⟨2863979, by rfl⟩ : syracuseStep 3818639 = 5727959) B5727959
theorem B12895523 : Blo 892572 12895523 := bstep (se 1 (by rfl) ⟨9671642, by rfl⟩ : syracuseStep 12895523 = 19343285) B19343285
theorem B6440381 : Blo 892572 6440381 := bstep (se 3 (by rfl) ⟨1207571, by rfl⟩ : syracuseStep 6440381 = 2415143) B2415143
theorem B2016863 : Blo 892572 2016863 := bstep (se 1 (by rfl) ⟨1512647, by rfl⟩ : syracuseStep 2016863 = 3025295) B3025295
theorem B25740989 : Blo 892572 25740989 := bstep (se 3 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 25740989 = 9652871) B9652871
theorem B32622385 : Blo 892572 32622385 := bstep (se 2 (by rfl) ⟨12233394, by rfl⟩ : syracuseStep 32622385 = 24466789) B24466789
theorem B2017079 : Blo 892572 2017079 := bstep (se 1 (by rfl) ⟨1512809, by rfl⟩ : syracuseStep 2017079 = 3025619) B3025619
theorem B4900837 : Blo 892572 4900837 := bstep (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) B918907
theorem B21743873 : Blo 892572 21743873 := bstep (se 2 (by rfl) ⟨8153952, by rfl⟩ : syracuseStep 21743873 = 16307905) B16307905
theorem B1132967 : Blo 892572 1132967 := bstep (se 1 (by rfl) ⟨849725, by rfl⟩ : syracuseStep 1132967 = 1699451) B1699451
theorem B1133119 : Blo 892572 1133119 := bstep (se 1 (by rfl) ⟨849839, by rfl⟩ : syracuseStep 1133119 = 1699679) B1699679
theorem B2869823 : Blo 892572 2869823 := bstep (se 1 (by rfl) ⟨2152367, by rfl⟩ : syracuseStep 2869823 = 4304735) B4304735
theorem B6113879 : Blo 892572 6113879 := bstep (se 1 (by rfl) ⟨4585409, by rfl⟩ : syracuseStep 6113879 = 9170819) B9170819
theorem B1133291 : Blo 892572 1133291 := bstep (se 1 (by rfl) ⟨849968, by rfl⟩ : syracuseStep 1133291 = 1699937) B1699937
theorem B3820279 : Blo 892572 3820279 := bstep (se 1 (by rfl) ⟨2865209, by rfl⟩ : syracuseStep 3820279 = 5730419) B5730419
theorem B5098535 : Blo 892572 5098535 := bstep (se 1 (by rfl) ⟨3823901, by rfl⟩ : syracuseStep 5098535 = 7647803) B7647803
theorem B8146291 : Blo 892572 8146291 := bstep (se 1 (by rfl) ⟨6109718, by rfl⟩ : syracuseStep 8146291 = 12219437) B12219437
theorem B43470215 : Blo 892572 43470215 := bstep (se 1 (by rfl) ⟨32602661, by rfl⟩ : syracuseStep 43470215 = 65205323) B65205323
theorem B3231191 : Blo 892572 3231191 := bstep (se 1 (by rfl) ⟨2423393, by rfl⟩ : syracuseStep 3231191 = 4846787) B4846787
theorem B1134263 : Blo 892572 1134263 := bstep (se 1 (by rfl) ⟨850697, by rfl⟩ : syracuseStep 1134263 = 1701395) B1701395
theorem B5099219 : Blo 892572 5099219 := bstep (se 1 (by rfl) ⟨3824414, by rfl⟩ : syracuseStep 5099219 = 7648829) B7648829
theorem B1134415 : Blo 892572 1134415 := bstep (se 1 (by rfl) ⟨850811, by rfl⟩ : syracuseStep 1134415 = 1701623) B1701623
theorem B18370525 : Blo 892572 18370525 := bstep (se 3 (by rfl) ⟨3444473, by rfl⟩ : syracuseStep 18370525 = 6888947) B6888947
theorem B3625019 : Blo 892572 3625019 := bstep (se 1 (by rfl) ⟨2718764, by rfl⟩ : syracuseStep 3625019 = 5437529) B5437529
theorem B2183449 : Blo 892572 2183449 := bstep (se 2 (by rfl) ⟨818793, by rfl⟩ : syracuseStep 2183449 = 1637587) B1637587
theorem B2150975 : Blo 892572 2150975 := bstep (se 1 (by rfl) ⟨1613231, by rfl⟩ : syracuseStep 2150975 = 3226463) B3226463
theorem B2150983 : Blo 892572 2150983 := bstep (se 1 (by rfl) ⟨1613237, by rfl⟩ : syracuseStep 2150983 = 3226475) B3226475
theorem B30986963 : Blo 892572 30986963 := bstep (se 1 (by rfl) ⟨23240222, by rfl⟩ : syracuseStep 30986963 = 46480445) B46480445
theorem B3822329 : Blo 892572 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B15520585 : Blo 892572 15520585 := bstep (se 2 (by rfl) ⟨5820219, by rfl⟩ : syracuseStep 15520585 = 11640439) B11640439
theorem B1430503 : Blo 892572 1430503 := bstep (se 1 (by rfl) ⟨1072877, by rfl⟩ : syracuseStep 1430503 = 2145755) B2145755
theorem B3921095 : Blo 892572 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B7263593 : Blo 892572 7263593 := bstep (se 2 (by rfl) ⟨2723847, by rfl⟩ : syracuseStep 7263593 = 5447695) B5447695
theorem B1005151 : Blo 892572 1005151 := bstep (se 1 (by rfl) ⟨753863, by rfl⟩ : syracuseStep 1005151 = 1507727) B1507727
theorem B109991681 : Blo 892572 109991681 := bstep (se 2 (by rfl) ⟨41246880, by rfl⟩ : syracuseStep 109991681 = 82493761) B82493761
theorem B5101703 : Blo 892572 5101703 := bstep (se 1 (by rfl) ⟨3826277, by rfl⟩ : syracuseStep 5101703 = 7652555) B7652555
theorem B6805943 : Blo 892572 6805943 := bstep (se 1 (by rfl) ⟨5104457, by rfl⟩ : syracuseStep 6805943 = 10208915) B10208915
theorem B1006303 : Blo 892572 1006303 := bstep (se 1 (by rfl) ⟨754727, by rfl⟩ : syracuseStep 1006303 = 1509455) B1509455
theorem B4643651 : Blo 892572 4643651 := bstep (se 1 (by rfl) ⟨3482738, by rfl⟩ : syracuseStep 4643651 = 6965477) B6965477
theorem B2546603 : Blo 892572 2546603 := bstep (se 1 (by rfl) ⟨1909952, by rfl⟩ : syracuseStep 2546603 = 3819905) B3819905
theorem B2153387 : Blo 892572 2153387 := bstep (se 1 (by rfl) ⟨1615040, by rfl⟩ : syracuseStep 2153387 = 3230081) B3230081
theorem B4250639 : Blo 892572 4250639 := bstep (se 1 (by rfl) ⟨3187979, by rfl⟩ : syracuseStep 4250639 = 6375959) B6375959
theorem B4906099 : Blo 892572 4906099 := bstep (se 1 (by rfl) ⟨3679574, by rfl⟩ : syracuseStep 4906099 = 7359149) B7359149
theorem B1006879 : Blo 892572 1006879 := bstep (se 1 (by rfl) ⟨755159, by rfl⟩ : syracuseStep 1006879 = 1510319) B1510319
theorem B3824927 : Blo 892572 3824927 := bstep (se 1 (by rfl) ⟨2868695, by rfl⟩ : syracuseStep 3824927 = 5737391) B5737391
theorem B1007167 : Blo 892572 1007167 := bstep (se 1 (by rfl) ⟨755375, by rfl⟩ : syracuseStep 1007167 = 1510751) B1510751
theorem B4349675 : Blo 892572 4349675 := bstep (se 1 (by rfl) ⟨3262256, by rfl⟩ : syracuseStep 4349675 = 6524513) B6524513
theorem B1073531 : Blo 892572 1073531 := bstep (se 1 (by rfl) ⟨805148, by rfl⟩ : syracuseStep 1073531 = 1610297) B1610297
theorem B1007995 : Blo 892572 1007995 := bstep (se 1 (by rfl) ⟨755996, by rfl⟩ : syracuseStep 1007995 = 1511993) B1511993
theorem B1073839 : Blo 892572 1073839 := bstep (se 1 (by rfl) ⟨805379, by rfl⟩ : syracuseStep 1073839 = 1610759) B1610759
theorem B1008463 : Blo 892572 1008463 := bstep (se 1 (by rfl) ⟨756347, by rfl⟩ : syracuseStep 1008463 = 1512695) B1512695
theorem B3400649 : Blo 892572 3400649 := bstep (se 2 (by rfl) ⟨1275243, by rfl⟩ : syracuseStep 3400649 = 2550487) B2550487
theorem B1532903 : Blo 892572 1532903 := bstep (se 1 (by rfl) ⟨1149677, by rfl⟩ : syracuseStep 1532903 = 2299355) B2299355
theorem B3400937 : Blo 892572 3400937 := bstep (se 2 (by rfl) ⟨1275351, by rfl⟩ : syracuseStep 3400937 = 2550703) B2550703
theorem B5432663 : Blo 892572 5432663 := bstep (se 1 (by rfl) ⟨4074497, by rfl⟩ : syracuseStep 5432663 = 8148995) B8148995
theorem B2942347 : Blo 892572 2942347 := bstep (se 1 (by rfl) ⟨2206760, by rfl⟩ : syracuseStep 2942347 = 4413521) B4413521
theorem B3401149 : Blo 892572 3401149 := bstep (se 3 (by rfl) ⟨637715, by rfl⟩ : syracuseStep 3401149 = 1275431) B1275431
theorem B1435079 : Blo 892572 1435079 := bstep (se 1 (by rfl) ⟨1076309, by rfl⟩ : syracuseStep 1435079 = 2152619) B2152619
theorem B3827387 : Blo 892572 3827387 := bstep (se 1 (by rfl) ⟨2870540, by rfl⟩ : syracuseStep 3827387 = 5741081) B5741081
theorem B1697591 : Blo 892572 1697591 := bstep (se 1 (by rfl) ⟨1273193, by rfl⟩ : syracuseStep 1697591 = 2546387) B2546387
theorem B16345273 : Blo 892572 16345273 := bstep (se 2 (by rfl) ⟨6129477, by rfl⟩ : syracuseStep 16345273 = 12258955) B12258955
theorem B1698259 : Blo 892572 1698259 := bstep (se 1 (by rfl) ⟨1273694, by rfl⟩ : syracuseStep 1698259 = 2547389) B2547389
theorem B1698479 : Blo 892572 1698479 := bstep (se 1 (by rfl) ⟨1273859, by rfl⟩ : syracuseStep 1698479 = 2547719) B2547719
theorem B1699049 : Blo 892572 1699049 := bstep (se 2 (by rfl) ⟨637143, by rfl⟩ : syracuseStep 1699049 = 1274287) B1274287
theorem B6778241 : Blo 892572 6778241 := bstep (se 2 (by rfl) ⟨2541840, by rfl⟩ : syracuseStep 6778241 = 5083681) B5083681
theorem B9662125 : Blo 892572 9662125 := bstep (se 3 (by rfl) ⟨1811648, by rfl⟩ : syracuseStep 9662125 = 3623297) B3623297
theorem B1339115 : Blo 892572 1339115 := bstep (se 1 (by rfl) ⟨1004336, by rfl⟩ : syracuseStep 1339115 = 2008673) B2008673
theorem B1339343 : Blo 892572 1339343 := bstep (se 1 (by rfl) ⟨1004507, by rfl⟩ : syracuseStep 1339343 = 2009015) B2009015
theorem B1339739 : Blo 892572 1339739 := bstep (se 1 (by rfl) ⟨1004804, by rfl⟩ : syracuseStep 1339739 = 2009609) B2009609
theorem B1700347 : Blo 892572 1700347 := bstep (se 1 (by rfl) ⟨1275260, by rfl⟩ : syracuseStep 1700347 = 2550521) B2550521
theorem B1339967 : Blo 892572 1339967 := bstep (se 1 (by rfl) ⟨1004975, by rfl⟩ : syracuseStep 1339967 = 2009951) B2009951
theorem B1700423 : Blo 892572 1700423 := bstep (se 1 (by rfl) ⟨1275317, by rfl⟩ : syracuseStep 1700423 = 2550635) B2550635
theorem B11596385 : Blo 892572 11596385 := bstep (se 2 (by rfl) ⟨4348644, by rfl⟩ : syracuseStep 11596385 = 8697289) B8697289
theorem B2290283 : Blo 892572 2290283 := bstep (se 1 (by rfl) ⟨1717712, by rfl⟩ : syracuseStep 2290283 = 3435425) B3435425
theorem B1340087 : Blo 892572 1340087 := bstep (se 1 (by rfl) ⟨1005065, by rfl⟩ : syracuseStep 1340087 = 2010131) B2010131
theorem B1340315 : Blo 892572 1340315 := bstep (se 1 (by rfl) ⟨1005236, by rfl⟩ : syracuseStep 1340315 = 2010473) B2010473
theorem B2422009 : Blo 892572 2422009 := bstep (se 2 (by rfl) ⟨908253, by rfl⟩ : syracuseStep 2422009 = 1816507) B1816507
theorem B1340711 : Blo 892572 1340711 := bstep (se 1 (by rfl) ⟨1005533, by rfl⟩ : syracuseStep 1340711 = 2011067) B2011067
theorem B1340795 : Blo 892572 1340795 := bstep (se 1 (by rfl) ⟨1005596, by rfl⟩ : syracuseStep 1340795 = 2011193) B2011193
theorem B34895249 : Blo 892572 34895249 := bstep (se 2 (by rfl) ⟨13085718, by rfl⟩ : syracuseStep 34895249 = 26171437) B26171437
theorem B1701319 : Blo 892572 1701319 := bstep (se 1 (by rfl) ⟨1275989, by rfl⟩ : syracuseStep 1701319 = 2551979) B2551979
theorem B1340921 : Blo 892572 1340921 := bstep (se 2 (by rfl) ⟨502845, by rfl⟩ : syracuseStep 1340921 = 1005691) B1005691
theorem B1341023 : Blo 892572 1341023 := bstep (se 1 (by rfl) ⟨1005767, by rfl⟩ : syracuseStep 1341023 = 2011535) B2011535
theorem B1341239 : Blo 892572 1341239 := bstep (se 1 (by rfl) ⟨1005929, by rfl⟩ : syracuseStep 1341239 = 2011859) B2011859
theorem B11466683 : Blo 892572 11466683 := bstep (se 1 (by rfl) ⟨8600012, by rfl⟩ : syracuseStep 11466683 = 17200025) B17200025
theorem B1341545 : Blo 892572 1341545 := bstep (se 2 (by rfl) ⟨503079, by rfl⟩ : syracuseStep 1341545 = 1006159) B1006159
theorem B1341863 : Blo 892572 1341863 := bstep (se 1 (by rfl) ⟨1006397, by rfl⟩ : syracuseStep 1341863 = 2012795) B2012795
theorem B1341947 : Blo 892572 1341947 := bstep (se 1 (by rfl) ⟨1006460, by rfl⟩ : syracuseStep 1341947 = 2012921) B2012921
theorem B1276411 : Blo 892572 1276411 := bstep (se 1 (by rfl) ⟨957308, by rfl⟩ : syracuseStep 1276411 = 1914617) B1914617
theorem B2292295 : Blo 892572 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B2259535 : Blo 892572 2259535 := bstep (se 1 (by rfl) ⟨1694651, by rfl⟩ : syracuseStep 2259535 = 3389303) B3389303
theorem B3013199 : Blo 892572 3013199 := bstep (se 1 (by rfl) ⟨2259899, by rfl⟩ : syracuseStep 3013199 = 4519799) B4519799
theorem B4192847 : Blo 892572 4192847 := bstep (se 1 (by rfl) ⟨3144635, by rfl⟩ : syracuseStep 4192847 = 6289271) B6289271
theorem B1342073 : Blo 892572 1342073 := bstep (se 2 (by rfl) ⟨503277, by rfl⟩ : syracuseStep 1342073 = 1006555) B1006555
theorem B33094277 : Blo 892572 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B7240367 : Blo 892572 7240367 := bstep (se 1 (by rfl) ⟨5430275, by rfl⟩ : syracuseStep 7240367 = 10860551) B10860551
theorem B1342127 : Blo 892572 1342127 := bstep (se 1 (by rfl) ⟨1006595, by rfl⟩ : syracuseStep 1342127 = 2013191) B2013191
theorem B1342175 : Blo 892572 1342175 := bstep (se 1 (by rfl) ⟨1006631, by rfl⟩ : syracuseStep 1342175 = 2013263) B2013263
theorem B4520771 : Blo 892572 4520771 := bstep (se 1 (by rfl) ⟨3390578, by rfl⟩ : syracuseStep 4520771 = 6781157) B6781157
theorem B1342439 : Blo 892572 1342439 := bstep (se 1 (by rfl) ⟨1006829, by rfl⟩ : syracuseStep 1342439 = 2013659) B2013659
theorem B2260183 : Blo 892572 2260183 := bstep (se 1 (by rfl) ⟨1695137, by rfl⟩ : syracuseStep 2260183 = 3390275) B3390275
theorem B1342697 : Blo 892572 1342697 := bstep (se 2 (by rfl) ⟨503511, by rfl⟩ : syracuseStep 1342697 = 1007023) B1007023
theorem B1342751 : Blo 892572 1342751 := bstep (se 1 (by rfl) ⟨1007063, by rfl⟩ : syracuseStep 1342751 = 2014127) B2014127
theorem B1342919 : Blo 892572 1342919 := bstep (se 1 (by rfl) ⟨1007189, by rfl⟩ : syracuseStep 1342919 = 2014379) B2014379
theorem B1506809 : Blo 892572 1506809 := bstep (se 2 (by rfl) ⟨565053, by rfl⟩ : syracuseStep 1506809 = 1130107) B1130107
theorem B2260487 : Blo 892572 2260487 := bstep (se 1 (by rfl) ⟨1695365, by rfl⟩ : syracuseStep 2260487 = 3390731) B3390731
theorem B4521581 : Blo 892572 4521581 := bstep (se 3 (by rfl) ⟨847796, by rfl⟩ : syracuseStep 4521581 = 1695593) B1695593
theorem B8584865 : Blo 892572 8584865 := bstep (se 2 (by rfl) ⟨3219324, by rfl⟩ : syracuseStep 8584865 = 6438649) B6438649
theorem B7634681 : Blo 892572 7634681 := bstep (se 2 (by rfl) ⟨2863005, by rfl⟩ : syracuseStep 7634681 = 5726011) B5726011
theorem B1507079 : Blo 892572 1507079 := bstep (se 1 (by rfl) ⟨1130309, by rfl⟩ : syracuseStep 1507079 = 2260619) B2260619
theorem B3014441 : Blo 892572 3014441 := bstep (se 2 (by rfl) ⟨1130415, by rfl⟩ : syracuseStep 3014441 = 2260831) B2260831
theorem B1343273 : Blo 892572 1343273 := bstep (se 2 (by rfl) ⟨503727, by rfl⟩ : syracuseStep 1343273 = 1007455) B1007455
theorem B1343279 : Blo 892572 1343279 := bstep (se 1 (by rfl) ⟨1007459, by rfl⟩ : syracuseStep 1343279 = 2014919) B2014919
theorem B2260943 : Blo 892572 2260943 := bstep (se 1 (by rfl) ⟨1695707, by rfl⟩ : syracuseStep 2260943 = 3391415) B3391415
theorem B7241795 : Blo 892572 7241795 := bstep (se 1 (by rfl) ⟨5431346, by rfl⟩ : syracuseStep 7241795 = 10862693) B10862693
theorem B1507639 : Blo 892572 1507639 := bstep (se 1 (by rfl) ⟨1130729, by rfl⟩ : syracuseStep 1507639 = 2261459) B2261459
theorem B4293047 : Blo 892572 4293047 := bstep (se 1 (by rfl) ⟨3219785, by rfl⟩ : syracuseStep 4293047 = 6439571) B6439571
theorem B1343951 : Blo 892572 1343951 := bstep (se 1 (by rfl) ⟨1007963, by rfl⟩ : syracuseStep 1343951 = 2015927) B2015927
theorem B1343993 : Blo 892572 1343993 := bstep (se 2 (by rfl) ⟨503997, by rfl⟩ : syracuseStep 1343993 = 1007995) B1007995
theorem B5734907 : Blo 892572 5734907 := bstep (se 1 (by rfl) ⟨4301180, by rfl⟩ : syracuseStep 5734907 = 8602361) B8602361
theorem B1344095 : Blo 892572 1344095 := bstep (se 1 (by rfl) ⟨1008071, by rfl⟩ : syracuseStep 1344095 = 2016143) B2016143
theorem B1507943 : Blo 892572 1507943 := bstep (se 1 (by rfl) ⟨1130957, by rfl⟩ : syracuseStep 1507943 = 2261915) B2261915
theorem B5735033 : Blo 892572 5735033 := bstep (se 2 (by rfl) ⟨2150637, by rfl⟩ : syracuseStep 5735033 = 4301275) B4301275
theorem B1508105 : Blo 892572 1508105 := bstep (se 2 (by rfl) ⟨565539, by rfl⟩ : syracuseStep 1508105 = 1131079) B1131079
theorem B4293587 : Blo 892572 4293587 := bstep (se 1 (by rfl) ⟨3220190, by rfl⟩ : syracuseStep 4293587 = 6440381) B6440381
theorem B1344575 : Blo 892572 1344575 := bstep (se 1 (by rfl) ⟨1008431, by rfl⟩ : syracuseStep 1344575 = 2016863) B2016863
theorem B1344617 : Blo 892572 1344617 := bstep (se 2 (by rfl) ⟨504231, by rfl⟩ : syracuseStep 1344617 = 1008463) B1008463
theorem B1344719 : Blo 892572 1344719 := bstep (se 1 (by rfl) ⟨1008539, by rfl⟩ : syracuseStep 1344719 = 2017079) B2017079
theorem B1508699 : Blo 892572 1508699 := bstep (se 1 (by rfl) ⟨1131524, by rfl⟩ : syracuseStep 1508699 = 2263049) B2263049
theorem B5735933 : Blo 892572 5735933 := bstep (se 3 (by rfl) ⟨1075487, by rfl⟩ : syracuseStep 5735933 = 2150975) B2150975
theorem B1508935 : Blo 892572 1508935 := bstep (se 1 (by rfl) ⟨1131701, by rfl⟩ : syracuseStep 1508935 = 2263403) B2263403
theorem B1509151 : Blo 892572 1509151 := bstep (se 1 (by rfl) ⟨1131863, by rfl⟩ : syracuseStep 1509151 = 2263727) B2263727
theorem B10192877 : Blo 892572 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B1509367 : Blo 892572 1509367 := bstep (se 1 (by rfl) ⟨1132025, by rfl⟩ : syracuseStep 1509367 = 2264051) B2264051
theorem B1509671 : Blo 892572 1509671 := bstep (se 1 (by rfl) ⟨1132253, by rfl⟩ : syracuseStep 1509671 = 2264507) B2264507
theorem B4524335 : Blo 892572 4524335 := bstep (se 1 (by rfl) ⟨3393251, by rfl⟩ : syracuseStep 4524335 = 6786503) B6786503
theorem B23267675 : Blo 892572 23267675 := bstep (se 1 (by rfl) ⟨17450756, by rfl⟩ : syracuseStep 23267675 = 34901513) B34901513
theorem B5311115 : Blo 892572 5311115 := bstep (se 1 (by rfl) ⟨3983336, by rfl⟩ : syracuseStep 5311115 = 7966673) B7966673
theorem B21793697 : Blo 892572 21793697 := bstep (se 2 (by rfl) ⟨8172636, by rfl⟩ : syracuseStep 21793697 = 16345273) B16345273
theorem B1510447 : Blo 892572 1510447 := bstep (se 1 (by rfl) ⟨1132835, by rfl⟩ : syracuseStep 1510447 = 2265671) B2265671
theorem B10456253 : Blo 892572 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B3017951 : Blo 892572 3017951 := bstep (se 1 (by rfl) ⟨2263463, by rfl⟩ : syracuseStep 3017951 = 4526927) B4526927
theorem B2264345 : Blo 892572 2264345 := bstep (se 2 (by rfl) ⟨849129, by rfl⟩ : syracuseStep 2264345 = 1698259) B1698259
theorem B1510825 : Blo 892572 1510825 := bstep (se 2 (by rfl) ⟨566559, by rfl⟩ : syracuseStep 1510825 = 1133119) B1133119
theorem B3018167 : Blo 892572 3018167 := bstep (se 1 (by rfl) ⟨2263625, by rfl⟩ : syracuseStep 3018167 = 4527251) B4527251
theorem B4525631 : Blo 892572 4525631 := bstep (se 1 (by rfl) ⟨3394223, by rfl⟩ : syracuseStep 4525631 = 6788447) B6788447
theorem B1511291 : Blo 892572 1511291 := bstep (se 1 (by rfl) ⟨1133468, by rfl⟩ : syracuseStep 1511291 = 2266937) B2266937
theorem B66130499 : Blo 892572 66130499 := bstep (se 1 (by rfl) ⟨49597874, by rfl⟩ : syracuseStep 66130499 = 99195749) B99195749
theorem B12882833 : Blo 892572 12882833 := bstep (se 2 (by rfl) ⟨4831062, by rfl⟩ : syracuseStep 12882833 = 9662125) B9662125
theorem B22025267 : Blo 892572 22025267 := bstep (se 1 (by rfl) ⟨16518950, by rfl⟩ : syracuseStep 22025267 = 33037901) B33037901
theorem B1512553 : Blo 892572 1512553 := bstep (se 2 (by rfl) ⟨567207, by rfl⟩ : syracuseStep 1512553 = 1134415) B1134415
theorem B3020219 : Blo 892572 3020219 := bstep (se 1 (by rfl) ⟨2265164, by rfl⟩ : syracuseStep 3020219 = 4530329) B4530329
theorem B2725769 : Blo 892572 2725769 := bstep (se 2 (by rfl) ⟨1022163, by rfl⟩ : syracuseStep 2725769 = 2044327) B2044327
theorem B34445249 : Blo 892572 34445249 := bstep (se 2 (by rfl) ⟨12916968, by rfl⟩ : syracuseStep 34445249 = 25833937) B25833937
theorem B3020759 : Blo 892572 3020759 := bstep (se 1 (by rfl) ⟨2265569, by rfl⟩ : syracuseStep 3020759 = 4531139) B4531139
theorem B2267099 : Blo 892572 2267099 := bstep (se 1 (by rfl) ⟨1700324, by rfl⟩ : syracuseStep 2267099 = 3400649) B3400649
theorem B2267129 : Blo 892572 2267129 := bstep (se 2 (by rfl) ⟨850173, by rfl⟩ : syracuseStep 2267129 = 1700347) B1700347
theorem B4298777 : Blo 892572 4298777 := bstep (se 2 (by rfl) ⟨1612041, by rfl⟩ : syracuseStep 4298777 = 3224083) B3224083
theorem B4528223 : Blo 892572 4528223 := bstep (se 1 (by rfl) ⟨3396167, by rfl⟩ : syracuseStep 4528223 = 6792335) B6792335
theorem B2267291 : Blo 892572 2267291 := bstep (se 1 (by rfl) ⟨1700468, by rfl⟩ : syracuseStep 2267291 = 3400937) B3400937
theorem B956719 : Blo 892572 956719 := bstep (se 1 (by rfl) ⟨717539, by rfl⟩ : syracuseStep 956719 = 1435079) B1435079
theorem B3021245 : Blo 892572 3021245 := bstep (se 3 (by rfl) ⟨566483, by rfl⟩ : syracuseStep 3021245 = 1132967) B1132967
theorem B2268425 : Blo 892572 2268425 := bstep (se 2 (by rfl) ⟨850659, by rfl⟩ : syracuseStep 2268425 = 1701319) B1701319
theorem B3022109 : Blo 892572 3022109 := bstep (se 3 (by rfl) ⟨566645, by rfl⟩ : syracuseStep 3022109 = 1133291) B1133291
theorem B4529519 : Blo 892572 4529519 := bstep (se 1 (by rfl) ⟨3397139, by rfl⟩ : syracuseStep 4529519 = 6794279) B6794279
theorem B892743 : Blo 892572 892743 := bstep (se 1 (by rfl) ⟨669557, by rfl⟩ : syracuseStep 892743 = 1339115) B1339115
theorem B892895 : Blo 892572 892895 := bstep (se 1 (by rfl) ⟨669671, by rfl⟩ : syracuseStep 892895 = 1339343) B1339343
theorem B5742697 : Blo 892572 5742697 := bstep (se 2 (by rfl) ⟨2153511, by rfl⟩ : syracuseStep 5742697 = 4307023) B4307023
theorem B893159 : Blo 892572 893159 := bstep (se 1 (by rfl) ⟨669869, by rfl⟩ : syracuseStep 893159 = 1339739) B1339739
theorem B3023135 : Blo 892572 3023135 := bstep (se 1 (by rfl) ⟨2267351, by rfl⟩ : syracuseStep 3023135 = 4534703) B4534703
theorem B893311 : Blo 892572 893311 := bstep (se 1 (by rfl) ⟨669983, by rfl⟩ : syracuseStep 893311 = 1339967) B1339967
theorem B11018699 : Blo 892572 11018699 := bstep (se 1 (by rfl) ⟨8264024, by rfl⟩ : syracuseStep 11018699 = 16528049) B16528049
theorem B893391 : Blo 892572 893391 := bstep (se 1 (by rfl) ⟨670043, by rfl⟩ : syracuseStep 893391 = 1340087) B1340087
theorem B893543 : Blo 892572 893543 := bstep (se 1 (by rfl) ⟨670157, by rfl⟩ : syracuseStep 893543 = 1340315) B1340315
theorem B3056393 : Blo 892572 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B893807 : Blo 892572 893807 := bstep (se 1 (by rfl) ⟨670355, by rfl⟩ : syracuseStep 893807 = 1340711) B1340711
theorem B893863 : Blo 892572 893863 := bstep (se 1 (by rfl) ⟨670397, by rfl⟩ : syracuseStep 893863 = 1340795) B1340795
theorem B3023783 : Blo 892572 3023783 := bstep (se 1 (by rfl) ⟨2267837, by rfl⟩ : syracuseStep 3023783 = 4535675) B4535675
theorem B893947 : Blo 892572 893947 := bstep (se 1 (by rfl) ⟨670460, by rfl⟩ : syracuseStep 893947 = 1340921) B1340921
theorem B894015 : Blo 892572 894015 := bstep (se 1 (by rfl) ⟨670511, by rfl⟩ : syracuseStep 894015 = 1341023) B1341023
theorem B10888289 : Blo 892572 10888289 := bstep (se 2 (by rfl) ⟨4083108, by rfl⟩ : syracuseStep 10888289 = 8166217) B8166217
theorem B894159 : Blo 892572 894159 := bstep (se 1 (by rfl) ⟨670619, by rfl⟩ : syracuseStep 894159 = 1341239) B1341239
theorem B7644455 : Blo 892572 7644455 := bstep (se 1 (by rfl) ⟨5733341, by rfl⟩ : syracuseStep 7644455 = 11466683) B11466683
theorem B894363 : Blo 892572 894363 := bstep (se 1 (by rfl) ⟨670772, by rfl⟩ : syracuseStep 894363 = 1341545) B1341545
theorem B3024377 : Blo 892572 3024377 := bstep (se 2 (by rfl) ⟨1134141, by rfl⟩ : syracuseStep 3024377 = 2268283) B2268283
theorem B894575 : Blo 892572 894575 := bstep (se 1 (by rfl) ⟨670931, by rfl⟩ : syracuseStep 894575 = 1341863) B1341863
theorem B894631 : Blo 892572 894631 := bstep (se 1 (by rfl) ⟨670973, by rfl⟩ : syracuseStep 894631 = 1341947) B1341947
theorem B2008799 : Blo 892572 2008799 := bstep (se 1 (by rfl) ⟨1506599, by rfl⟩ : syracuseStep 2008799 = 3013199) B3013199
theorem B2795231 : Blo 892572 2795231 := bstep (se 1 (by rfl) ⟨2096423, by rfl⟩ : syracuseStep 2795231 = 4192847) B4192847
theorem B894715 : Blo 892572 894715 := bstep (se 1 (by rfl) ⟨671036, by rfl⟩ : syracuseStep 894715 = 1342073) B1342073
theorem B22062851 : Blo 892572 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B3024647 : Blo 892572 3024647 := bstep (se 1 (by rfl) ⟨2268485, by rfl⟩ : syracuseStep 3024647 = 4536971) B4536971
theorem B4826911 : Blo 892572 4826911 := bstep (se 1 (by rfl) ⟨3620183, by rfl⟩ : syracuseStep 4826911 = 7240367) B7240367
theorem B894751 : Blo 892572 894751 := bstep (se 1 (by rfl) ⟨671063, by rfl⟩ : syracuseStep 894751 = 1342127) B1342127
theorem B3024701 : Blo 892572 3024701 := bstep (se 3 (by rfl) ⟨567131, by rfl⟩ : syracuseStep 3024701 = 1134263) B1134263
theorem B894783 : Blo 892572 894783 := bstep (se 1 (by rfl) ⟨671087, by rfl⟩ : syracuseStep 894783 = 1342175) B1342175
theorem B894959 : Blo 892572 894959 := bstep (se 1 (by rfl) ⟨671219, by rfl⟩ : syracuseStep 894959 = 1342439) B1342439
theorem B895131 : Blo 892572 895131 := bstep (se 1 (by rfl) ⟨671348, by rfl⟩ : syracuseStep 895131 = 1342697) B1342697
theorem B895167 : Blo 892572 895167 := bstep (se 1 (by rfl) ⟨671375, by rfl⟩ : syracuseStep 895167 = 1342751) B1342751
theorem B895279 : Blo 892572 895279 := bstep (se 1 (by rfl) ⟨671459, by rfl⟩ : syracuseStep 895279 = 1342919) B1342919
theorem B5089787 : Blo 892572 5089787 := bstep (se 1 (by rfl) ⟨3817340, by rfl⟩ : syracuseStep 5089787 = 7634681) B7634681
theorem B2009627 : Blo 892572 2009627 := bstep (se 1 (by rfl) ⟨1507220, by rfl⟩ : syracuseStep 2009627 = 3014441) B3014441
theorem B895515 : Blo 892572 895515 := bstep (se 1 (by rfl) ⟨671636, by rfl⟩ : syracuseStep 895515 = 1343273) B1343273
theorem B895519 : Blo 892572 895519 := bstep (se 1 (by rfl) ⟨671639, by rfl⟩ : syracuseStep 895519 = 1343279) B1343279
theorem B895835 : Blo 892572 895835 := bstep (se 1 (by rfl) ⟨671876, by rfl⟩ : syracuseStep 895835 = 1343753) B1343753
theorem B895903 : Blo 892572 895903 := bstep (se 1 (by rfl) ⟨671927, by rfl⟩ : syracuseStep 895903 = 1343855) B1343855
theorem B4303811 : Blo 892572 4303811 := bstep (se 1 (by rfl) ⟨3227858, by rfl⟩ : syracuseStep 4303811 = 6455717) B6455717
theorem B896047 : Blo 892572 896047 := bstep (se 1 (by rfl) ⟨672035, by rfl⟩ : syracuseStep 896047 = 1344071) B1344071
theorem B896071 : Blo 892572 896071 := bstep (se 1 (by rfl) ⟨672053, by rfl⟩ : syracuseStep 896071 = 1344107) B1344107
theorem B9678041 : Blo 892572 9678041 := bstep (se 2 (by rfl) ⟨3629265, by rfl⟩ : syracuseStep 9678041 = 7258531) B7258531
theorem B896223 : Blo 892572 896223 := bstep (se 1 (by rfl) ⟨672167, by rfl⟩ : syracuseStep 896223 = 1344335) B1344335
theorem B2043215 : Blo 892572 2043215 := bstep (se 1 (by rfl) ⟨1532411, by rfl⟩ : syracuseStep 2043215 = 3064823) B3064823
theorem B52178269 : Blo 892572 52178269 := bstep (se 3 (by rfl) ⟨9783425, by rfl⟩ : syracuseStep 52178269 = 19566851) B19566851
theorem B896487 : Blo 892572 896487 := bstep (se 1 (by rfl) ⟨672365, by rfl⟩ : syracuseStep 896487 = 1344731) B1344731
theorem B8597015 : Blo 892572 8597015 := bstep (se 1 (by rfl) ⟨6447761, by rfl⟩ : syracuseStep 8597015 = 12895523) B12895523
theorem B2862749 : Blo 892572 2862749 := bstep (se 3 (by rfl) ⟨536765, by rfl⟩ : syracuseStep 2862749 = 1073531) B1073531
theorem B39268253 : Blo 892572 39268253 := bstep (se 3 (by rfl) ⟨7362797, by rfl⟩ : syracuseStep 39268253 = 14725595) B14725595
theorem B5091245 : Blo 892572 5091245 := bstep (se 3 (by rfl) ⟨954608, by rfl⟩ : syracuseStep 5091245 = 1909217) B1909217
theorem B2011103 : Blo 892572 2011103 := bstep (se 1 (by rfl) ⟨1508327, by rfl⟩ : syracuseStep 2011103 = 3016655) B3016655
theorem B14495915 : Blo 892572 14495915 := bstep (se 1 (by rfl) ⟨10871936, by rfl⟩ : syracuseStep 14495915 = 21743873) B21743873
theorem B2863289 : Blo 892572 2863289 := bstep (se 2 (by rfl) ⟨1073733, by rfl⟩ : syracuseStep 2863289 = 2147467) B2147467
theorem B4829507 : Blo 892572 4829507 := bstep (se 1 (by rfl) ⟨3622130, by rfl⟩ : syracuseStep 4829507 = 7244261) B7244261
theorem B1913215 : Blo 892572 1913215 := bstep (se 1 (by rfl) ⟨1434911, by rfl⟩ : syracuseStep 1913215 = 2869823) B2869823
theorem B4075919 : Blo 892572 4075919 := bstep (se 1 (by rfl) ⟨3056939, by rfl⟩ : syracuseStep 4075919 = 6113879) B6113879
theorem B4534865 : Blo 892572 4534865 := bstep (se 2 (by rfl) ⟨1700574, by rfl⟩ : syracuseStep 4534865 = 3401149) B3401149
theorem B2011751 : Blo 892572 2011751 := bstep (se 1 (by rfl) ⟨1508813, by rfl⟩ : syracuseStep 2011751 = 3017627) B3017627
theorem B28980143 : Blo 892572 28980143 := bstep (se 1 (by rfl) ⟨21735107, by rfl⟩ : syracuseStep 28980143 = 43470215) B43470215
theorem B10335275 : Blo 892572 10335275 := bstep (se 1 (by rfl) ⟨7751456, by rfl⟩ : syracuseStep 10335275 = 15502913) B15502913
theorem B43496513 : Blo 892572 43496513 := bstep (se 2 (by rfl) ⟨16311192, by rfl⟩ : syracuseStep 43496513 = 32622385) B32622385
theorem B2012435 : Blo 892572 2012435 := bstep (se 1 (by rfl) ⟨1509326, by rfl⟩ : syracuseStep 2012435 = 3018653) B3018653
theorem B6534449 : Blo 892572 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B2012507 : Blo 892572 2012507 := bstep (se 1 (by rfl) ⟨1509380, by rfl⟩ : syracuseStep 2012507 = 3018761) B3018761
theorem B3388999 : Blo 892572 3388999 := bstep (se 1 (by rfl) ⟨2541749, by rfl⟩ : syracuseStep 3388999 = 5083499) B5083499
theorem B20657975 : Blo 892572 20657975 := bstep (se 1 (by rfl) ⟨15493481, by rfl⟩ : syracuseStep 20657975 = 30986963) B30986963
theorem B2013065 : Blo 892572 2013065 := bstep (se 2 (by rfl) ⟨754899, by rfl⟩ : syracuseStep 2013065 = 1509799) B1509799
theorem B1357807 : Blo 892572 1357807 := bstep (se 1 (by rfl) ⟨1018355, by rfl⟩ : syracuseStep 1357807 = 2036711) B2036711
theorem B2013281 : Blo 892572 2013281 := bstep (se 2 (by rfl) ⟨754980, by rfl⟩ : syracuseStep 2013281 = 1509961) B1509961
theorem B2865415 : Blo 892572 2865415 := bstep (se 1 (by rfl) ⟨2149061, by rfl⟩ : syracuseStep 2865415 = 4298123) B4298123
theorem B7649579 : Blo 892572 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B5093705 : Blo 892572 5093705 := bstep (se 2 (by rfl) ⟨1910139, by rfl⟩ : syracuseStep 5093705 = 3820279) B3820279
theorem B3389971 : Blo 892572 3389971 := bstep (se 1 (by rfl) ⟨2542478, by rfl⟩ : syracuseStep 3389971 = 5084957) B5084957
theorem B2144825 : Blo 892572 2144825 := bstep (se 2 (by rfl) ⟨804309, by rfl⟩ : syracuseStep 2144825 = 1608619) B1608619
theorem B4537295 : Blo 892572 4537295 := bstep (se 1 (by rfl) ⟨3402971, by rfl⟩ : syracuseStep 4537295 = 6805943) B6805943
theorem B1227817 : Blo 892572 1227817 := bstep (se 2 (by rfl) ⟨460431, by rfl⟩ : syracuseStep 1227817 = 920863) B920863
theorem B10861721 : Blo 892572 10861721 := bstep (se 2 (by rfl) ⟨4073145, by rfl⟩ : syracuseStep 10861721 = 8146291) B8146291
theorem B3095767 : Blo 892572 3095767 := bstep (se 1 (by rfl) ⟨2321825, by rfl⟩ : syracuseStep 3095767 = 4643651) B4643651
theorem B2833759 : Blo 892572 2833759 := bstep (se 1 (by rfl) ⟨2125319, by rfl⟩ : syracuseStep 2833759 = 4250639) B4250639
theorem B2014631 : Blo 892572 2014631 := bstep (se 1 (by rfl) ⟨1510973, by rfl⟩ : syracuseStep 2014631 = 3021947) B3021947
theorem B1359335 : Blo 892572 1359335 := bstep (se 1 (by rfl) ⟨1019501, by rfl⟩ : syracuseStep 1359335 = 2039003) B2039003
theorem B2014811 : Blo 892572 2014811 := bstep (se 1 (by rfl) ⟨1511108, by rfl⟩ : syracuseStep 2014811 = 3022217) B3022217
theorem B2899783 : Blo 892572 2899783 := bstep (se 1 (by rfl) ⟨2174837, by rfl⟩ : syracuseStep 2899783 = 4349675) B4349675
theorem B2015099 : Blo 892572 2015099 := bstep (se 1 (by rfl) ⟨1511324, by rfl⟩ : syracuseStep 2015099 = 3022649) B3022649
theorem B24494033 : Blo 892572 24494033 := bstep (se 2 (by rfl) ⟨9185262, by rfl⟩ : syracuseStep 24494033 = 18370525) B18370525
theorem B2015585 : Blo 892572 2015585 := bstep (se 2 (by rfl) ⟨755844, by rfl⟩ : syracuseStep 2015585 = 1511689) B1511689
theorem B2015675 : Blo 892572 2015675 := bstep (se 1 (by rfl) ⟨1511756, by rfl⟩ : syracuseStep 2015675 = 3023513) B3023513
theorem B26165861 : Blo 892572 26165861 := bstep (se 4 (by rfl) ⟨2453049, by rfl⟩ : syracuseStep 26165861 = 4906099) B4906099
theorem B14533283 : Blo 892572 14533283 := bstep (se 1 (by rfl) ⟨10899962, by rfl⟩ : syracuseStep 14533283 = 21799925) B21799925
theorem B2867977 : Blo 892572 2867977 := bstep (se 2 (by rfl) ⟨1075491, by rfl⟩ : syracuseStep 2867977 = 2150983) B2150983
theorem B3621775 : Blo 892572 3621775 := bstep (se 1 (by rfl) ⟨2716331, by rfl⟩ : syracuseStep 3621775 = 5432663) B5432663
theorem B1360891 : Blo 892572 1360891 := bstep (se 1 (by rfl) ⟨1020668, by rfl⟩ : syracuseStep 1360891 = 2041337) B2041337
theorem B20694113 : Blo 892572 20694113 := bstep (se 2 (by rfl) ⟨7760292, by rfl⟩ : syracuseStep 20694113 = 15520585) B15520585
theorem B1131727 : Blo 892572 1131727 := bstep (se 1 (by rfl) ⟨848795, by rfl⟩ : syracuseStep 1131727 = 1697591) B1697591
theorem B2016683 : Blo 892572 2016683 := bstep (se 1 (by rfl) ⟨1512512, by rfl⟩ : syracuseStep 2016683 = 3025025) B3025025
theorem B3229345 : Blo 892572 3229345 := bstep (se 2 (by rfl) ⟨1211004, by rfl⟩ : syracuseStep 3229345 = 2422009) B2422009
theorem B2016935 : Blo 892572 2016935 := bstep (se 1 (by rfl) ⟨1512701, by rfl⟩ : syracuseStep 2016935 = 3025403) B3025403
theorem B1132319 : Blo 892572 1132319 := bstep (se 1 (by rfl) ⟨849239, by rfl⟩ : syracuseStep 1132319 = 1698479) B1698479
theorem B3393359 : Blo 892572 3393359 := bstep (se 1 (by rfl) ⟨2545019, by rfl⟩ : syracuseStep 3393359 = 5090039) B5090039
theorem B2017223 : Blo 892572 2017223 := bstep (se 1 (by rfl) ⟨1512917, by rfl⟩ : syracuseStep 2017223 = 3025835) B3025835
theorem B1132699 : Blo 892572 1132699 := bstep (se 1 (by rfl) ⟨849524, by rfl⟩ : syracuseStep 1132699 = 1699049) B1699049
theorem B1133615 : Blo 892572 1133615 := bstep (se 1 (by rfl) ⟨850211, by rfl⟩ : syracuseStep 1133615 = 1700423) B1700423
theorem B1526855 : Blo 892572 1526855 := bstep (se 1 (by rfl) ⟨1145141, by rfl⟩ : syracuseStep 1526855 = 2290283) B2290283
theorem B3395135 : Blo 892572 3395135 := bstep (se 1 (by rfl) ⟨2546351, by rfl⟩ : syracuseStep 3395135 = 5092703) B5092703
theorem B2871247 : Blo 892572 2871247 := bstep (se 1 (by rfl) ⟨2153435, by rfl⟩ : syracuseStep 2871247 = 4306871) B4306871
theorem B1004539 : Blo 892572 1004539 := bstep (se 1 (by rfl) ⟨753404, by rfl⟩ : syracuseStep 1004539 = 1506809) B1506809
theorem B5723243 : Blo 892572 5723243 := bstep (se 1 (by rfl) ⟨4292432, by rfl⟩ : syracuseStep 5723243 = 8584865) B8584865
theorem B1004719 : Blo 892572 1004719 := bstep (se 1 (by rfl) ⟨753539, by rfl⟩ : syracuseStep 1004719 = 1507079) B1507079
theorem B1430875 : Blo 892572 1430875 := bstep (se 1 (by rfl) ⟨1073156, by rfl⟩ : syracuseStep 1430875 = 2146313) B2146313
theorem B2545121 : Blo 892572 2545121 := bstep (se 2 (by rfl) ⟨954420, by rfl⟩ : syracuseStep 2545121 = 1908841) B1908841
theorem B1005223 : Blo 892572 1005223 := bstep (se 1 (by rfl) ⟨753917, by rfl⟩ : syracuseStep 1005223 = 1507835) B1507835
theorem B53106353 : Blo 892572 53106353 := bstep (se 2 (by rfl) ⟨19914882, by rfl⟩ : syracuseStep 53106353 = 39829765) B39829765
theorem B1005511 : Blo 892572 1005511 := bstep (se 1 (by rfl) ⟨754133, by rfl⟩ : syracuseStep 1005511 = 1508267) B1508267
theorem B2545759 : Blo 892572 2545759 := bstep (se 1 (by rfl) ⟨1909319, by rfl⟩ : syracuseStep 2545759 = 3818639) B3818639
theorem B1431785 : Blo 892572 1431785 := bstep (se 2 (by rfl) ⟨536919, by rfl⟩ : syracuseStep 1431785 = 1073839) B1073839
theorem B1005871 : Blo 892572 1005871 := bstep (se 1 (by rfl) ⟨754403, by rfl⟩ : syracuseStep 1005871 = 1508807) B1508807
theorem B17160659 : Blo 892572 17160659 := bstep (se 1 (by rfl) ⟨12870494, by rfl⟩ : syracuseStep 17160659 = 25740989) B25740989
theorem B1006663 : Blo 892572 1006663 := bstep (se 1 (by rfl) ⟨754997, by rfl⟩ : syracuseStep 1006663 = 1509995) B1509995
theorem B3923129 : Blo 892572 3923129 := bstep (se 2 (by rfl) ⟨1471173, by rfl⟩ : syracuseStep 3923129 = 2942347) B2942347
theorem B5102909 : Blo 892572 5102909 := bstep (se 3 (by rfl) ⟨956795, by rfl⟩ : syracuseStep 5102909 = 1913591) B1913591
theorem B3399023 : Blo 892572 3399023 := bstep (se 1 (by rfl) ⟨2549267, by rfl⟩ : syracuseStep 3399023 = 5098535) B5098535
theorem B2154127 : Blo 892572 2154127 := bstep (se 1 (by rfl) ⟨1615595, by rfl⟩ : syracuseStep 2154127 = 3231191) B3231191
theorem B4644637 : Blo 892572 4644637 := bstep (se 3 (by rfl) ⟨870869, by rfl⟩ : syracuseStep 4644637 = 1741739) B1741739
theorem B3399479 : Blo 892572 3399479 := bstep (se 1 (by rfl) ⟨2549609, by rfl⟩ : syracuseStep 3399479 = 5099219) B5099219
theorem B4087741 : Blo 892572 4087741 := bstep (se 3 (by rfl) ⟨766451, by rfl⟩ : syracuseStep 4087741 = 1532903) B1532903
theorem B2416679 : Blo 892572 2416679 := bstep (se 1 (by rfl) ⟨1812509, by rfl⟩ : syracuseStep 2416679 = 3625019) B3625019
theorem B3825883 : Blo 892572 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B4842395 : Blo 892572 4842395 := bstep (se 1 (by rfl) ⟨3631796, by rfl⟩ : syracuseStep 4842395 = 7263593) B7263593
theorem B73327787 : Blo 892572 73327787 := bstep (se 1 (by rfl) ⟨54995840, by rfl⟩ : syracuseStep 73327787 = 109991681) B109991681
theorem B3401135 : Blo 892572 3401135 := bstep (se 1 (by rfl) ⟨2550851, by rfl⟩ : syracuseStep 3401135 = 5101703) B5101703
theorem B10184129 : Blo 892572 10184129 := bstep (se 2 (by rfl) ⟨3819048, by rfl⟩ : syracuseStep 10184129 = 7638097) B7638097
theorem B2549245 : Blo 892572 2549245 := bstep (se 3 (by rfl) ⟨477983, by rfl⟩ : syracuseStep 2549245 = 955967) B955967
theorem B1271479 : Blo 892572 1271479 := bstep (se 1 (by rfl) ⟨953609, by rfl⟩ : syracuseStep 1271479 = 1907219) B1907219
theorem B1697735 : Blo 892572 1697735 := bstep (se 1 (by rfl) ⟨1273301, by rfl⟩ : syracuseStep 1697735 = 2546603) B2546603
theorem B1435591 : Blo 892572 1435591 := bstep (se 1 (by rfl) ⟨1076693, by rfl⟩ : syracuseStep 1435591 = 2153387) B2153387
theorem B1271963 : Blo 892572 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B2549951 : Blo 892572 2549951 := bstep (se 1 (by rfl) ⟨1912463, by rfl⟩ : syracuseStep 2549951 = 3824927) B3824927
theorem B7629349 : Blo 892572 7629349 := bstep (se 4 (by rfl) ⟨715251, by rfl⟩ : syracuseStep 7629349 = 1430503) B1430503
theorem B7629623 : Blo 892572 7629623 := bstep (se 1 (by rfl) ⟨5722217, by rfl⟩ : syracuseStep 7629623 = 11444435) B11444435
theorem B2911265 : Blo 892572 2911265 := bstep (se 2 (by rfl) ⟨1091724, by rfl⟩ : syracuseStep 2911265 = 2183449) B2183449
theorem B1338875 : Blo 892572 1338875 := bstep (se 1 (by rfl) ⟨1004156, by rfl⟩ : syracuseStep 1338875 = 2008313) B2008313
theorem B1338971 : Blo 892572 1338971 := bstep (se 1 (by rfl) ⟨1004228, by rfl⟩ : syracuseStep 1338971 = 2008457) B2008457
theorem B52194941 : Blo 892572 52194941 := bstep (se 3 (by rfl) ⟨9786551, by rfl⟩ : syracuseStep 52194941 = 19573103) B19573103
theorem B1339055 : Blo 892572 1339055 := bstep (se 1 (by rfl) ⟨1004291, by rfl⟩ : syracuseStep 1339055 = 2008583) B2008583
theorem B1339175 : Blo 892572 1339175 := bstep (se 1 (by rfl) ⟨1004381, by rfl⟩ : syracuseStep 1339175 = 2008763) B2008763
theorem B2551591 : Blo 892572 2551591 := bstep (se 1 (by rfl) ⟨1913693, by rfl⟩ : syracuseStep 2551591 = 3827387) B3827387
theorem B1339259 : Blo 892572 1339259 := bstep (se 1 (by rfl) ⟨1004444, by rfl⟩ : syracuseStep 1339259 = 2008889) B2008889
theorem B3829643 : Blo 892572 3829643 := bstep (se 1 (by rfl) ⟨2872232, by rfl⟩ : syracuseStep 3829643 = 5744465) B5744465
theorem B3633275 : Blo 892572 3633275 := bstep (se 1 (by rfl) ⟨2724956, by rfl⟩ : syracuseStep 3633275 = 5449913) B5449913
theorem B1274087 : Blo 892572 1274087 := bstep (se 1 (by rfl) ⟨955565, by rfl⟩ : syracuseStep 1274087 = 1911131) B1911131
theorem B1339679 : Blo 892572 1339679 := bstep (se 1 (by rfl) ⟨1004759, by rfl⟩ : syracuseStep 1339679 = 2009519) B2009519
theorem B1339703 : Blo 892572 1339703 := bstep (se 1 (by rfl) ⟨1004777, by rfl⟩ : syracuseStep 1339703 = 2009555) B2009555
theorem B1274167 : Blo 892572 1274167 := bstep (se 1 (by rfl) ⟨955625, by rfl⟩ : syracuseStep 1274167 = 1911251) B1911251
theorem B1339775 : Blo 892572 1339775 := bstep (se 1 (by rfl) ⟨1004831, by rfl⟩ : syracuseStep 1339775 = 2009663) B2009663
theorem B1339847 : Blo 892572 1339847 := bstep (se 1 (by rfl) ⟨1004885, by rfl⟩ : syracuseStep 1339847 = 2009771) B2009771
theorem B1340201 : Blo 892572 1340201 := bstep (se 2 (by rfl) ⟨502575, by rfl⟩ : syracuseStep 1340201 = 1005151) B1005151
theorem B1340207 : Blo 892572 1340207 := bstep (se 1 (by rfl) ⟨1005155, by rfl⟩ : syracuseStep 1340207 = 2010311) B2010311
theorem B1340327 : Blo 892572 1340327 := bstep (se 1 (by rfl) ⟨1005245, by rfl⟩ : syracuseStep 1340327 = 2010491) B2010491
theorem B4518827 : Blo 892572 4518827 := bstep (se 1 (by rfl) ⟨3389120, by rfl⟩ : syracuseStep 4518827 = 6778241) B6778241
theorem B1340411 : Blo 892572 1340411 := bstep (se 1 (by rfl) ⟨1005308, by rfl⟩ : syracuseStep 1340411 = 2010617) B2010617
theorem B1340471 : Blo 892572 1340471 := bstep (se 1 (by rfl) ⟨1005353, by rfl⟩ : syracuseStep 1340471 = 2010707) B2010707
theorem B1274987 : Blo 892572 1274987 := bstep (se 1 (by rfl) ⟨956240, by rfl⟩ : syracuseStep 1274987 = 1912481) B1912481
theorem B1340591 : Blo 892572 1340591 := bstep (se 1 (by rfl) ⟨1005443, by rfl⟩ : syracuseStep 1340591 = 2010887) B2010887
theorem B1340999 : Blo 892572 1340999 := bstep (se 1 (by rfl) ⟨1005749, by rfl⟩ : syracuseStep 1340999 = 2011499) B2011499
theorem B1341095 : Blo 892572 1341095 := bstep (se 1 (by rfl) ⟨1005821, by rfl⟩ : syracuseStep 1341095 = 2011643) B2011643
theorem B7730923 : Blo 892572 7730923 := bstep (se 1 (by rfl) ⟨5798192, by rfl⟩ : syracuseStep 7730923 = 11596385) B11596385
theorem B1341179 : Blo 892572 1341179 := bstep (se 1 (by rfl) ⟨1005884, by rfl⟩ : syracuseStep 1341179 = 2011769) B2011769
theorem B1341215 : Blo 892572 1341215 := bstep (se 1 (by rfl) ⟨1005911, by rfl⟩ : syracuseStep 1341215 = 2011823) B2011823
theorem B1341263 : Blo 892572 1341263 := bstep (se 1 (by rfl) ⟨1005947, by rfl⟩ : syracuseStep 1341263 = 2011895) B2011895
theorem B1341383 : Blo 892572 1341383 := bstep (se 1 (by rfl) ⟨1006037, by rfl⟩ : syracuseStep 1341383 = 2012075) B2012075
theorem B1701881 : Blo 892572 1701881 := bstep (se 2 (by rfl) ⟨638205, by rfl⟩ : syracuseStep 1701881 = 1276411) B1276411
theorem B3012713 : Blo 892572 3012713 := bstep (se 2 (by rfl) ⟨1129767, by rfl⟩ : syracuseStep 3012713 = 2259535) B2259535
theorem B6191275 : Blo 892572 6191275 := bstep (se 1 (by rfl) ⟨4643456, by rfl⟩ : syracuseStep 6191275 = 9286913) B9286913
theorem B23263499 : Blo 892572 23263499 := bstep (se 1 (by rfl) ⟨17447624, by rfl⟩ : syracuseStep 23263499 = 34895249) B34895249
theorem B1341737 : Blo 892572 1341737 := bstep (se 2 (by rfl) ⟨503151, by rfl⟩ : syracuseStep 1341737 = 1006303) B1006303
theorem B1341743 : Blo 892572 1341743 := bstep (se 1 (by rfl) ⟨1006307, by rfl⟩ : syracuseStep 1341743 = 2012615) B2012615
theorem B3275117 : Blo 892572 3275117 := bstep (se 3 (by rfl) ⟨614084, by rfl⟩ : syracuseStep 3275117 = 1228169) B1228169
theorem B6388079 : Blo 892572 6388079 := bstep (se 1 (by rfl) ⟨4791059, by rfl⟩ : syracuseStep 6388079 = 9582119) B9582119
theorem B1341983 : Blo 892572 1341983 := bstep (se 1 (by rfl) ⟨1006487, by rfl⟩ : syracuseStep 1341983 = 2012975) B2012975
theorem B1342367 : Blo 892572 1342367 := bstep (se 1 (by rfl) ⟨1006775, by rfl⟩ : syracuseStep 1342367 = 2013551) B2013551
theorem B3013577 : Blo 892572 3013577 := bstep (se 2 (by rfl) ⟨1130091, by rfl⟩ : syracuseStep 3013577 = 2260183) B2260183
theorem B1342415 : Blo 892572 1342415 := bstep (se 1 (by rfl) ⟨1006811, by rfl⟩ : syracuseStep 1342415 = 2013623) B2013623
theorem B1342505 : Blo 892572 1342505 := bstep (se 2 (by rfl) ⟨503439, by rfl⟩ : syracuseStep 1342505 = 1006879) B1006879
theorem B1342511 : Blo 892572 1342511 := bstep (se 1 (by rfl) ⟨1006883, by rfl⟩ : syracuseStep 1342511 = 2013767) B2013767
theorem B1342535 : Blo 892572 1342535 := bstep (se 1 (by rfl) ⟨1006901, by rfl⟩ : syracuseStep 1342535 = 2013803) B2013803
theorem B318569561 : Blo 892572 318569561 := bstep (se 2 (by rfl) ⟨119463585, by rfl⟩ : syracuseStep 318569561 = 238927171) B238927171
theorem B5438621 : Blo 892572 5438621 := bstep (se 3 (by rfl) ⟨1019741, by rfl⟩ : syracuseStep 5438621 = 2039483) B2039483
theorem B3013847 : Blo 892572 3013847 := bstep (se 1 (by rfl) ⟨2260385, by rfl⟩ : syracuseStep 3013847 = 4520771) B4520771
theorem B1342799 : Blo 892572 1342799 := bstep (se 1 (by rfl) ⟨1007099, by rfl⟩ : syracuseStep 1342799 = 2014199) B2014199
theorem B1342889 : Blo 892572 1342889 := bstep (se 2 (by rfl) ⟨503583, by rfl⟩ : syracuseStep 1342889 = 1007167) B1007167
theorem B1343039 : Blo 892572 1343039 := bstep (se 1 (by rfl) ⟨1007279, by rfl⟩ : syracuseStep 1343039 = 2014559) B2014559
theorem B1506991 : Blo 892572 1506991 := bstep (se 1 (by rfl) ⟨1130243, by rfl⟩ : syracuseStep 1506991 = 2260487) B2260487
theorem B3014387 : Blo 892572 3014387 := bstep (se 1 (by rfl) ⟨2260790, by rfl⟩ : syracuseStep 3014387 = 4521581) B4521581
theorem B1343303 : Blo 892572 1343303 := bstep (se 1 (by rfl) ⟨1007477, by rfl⟩ : syracuseStep 1343303 = 2014955) B2014955
theorem B278822807 : Blo 892572 278822807 := bstep (se 1 (by rfl) ⟨209117105, by rfl⟩ : syracuseStep 278822807 = 418234211) B418234211
theorem B1343387 : Blo 892572 1343387 := bstep (se 1 (by rfl) ⟨1007540, by rfl⟩ : syracuseStep 1343387 = 2015081) B2015081
theorem B1507295 : Blo 892572 1507295 := bstep (se 1 (by rfl) ⟨1130471, by rfl⟩ : syracuseStep 1507295 = 2260943) B2260943
theorem B1343723 : Blo 892572 1343723 := bstep (se 1 (by rfl) ⟨1007792, by rfl⟩ : syracuseStep 1343723 = 2015585) B2015585
theorem B1343783 : Blo 892572 1343783 := bstep (se 1 (by rfl) ⟨1007837, by rfl⟩ : syracuseStep 1343783 = 2015675) B2015675
theorem B13796075 : Blo 892572 13796075 := bstep (se 1 (by rfl) ⟨10347056, by rfl⟩ : syracuseStep 13796075 = 20694113) B20694113
theorem B16286453 : Blo 892572 16286453 := bstep (se 5 (by rfl) ⟨763427, by rfl⟩ : syracuseStep 16286453 = 1526855) B1526855
theorem B1344455 : Blo 892572 1344455 := bstep (se 1 (by rfl) ⟨1008341, by rfl⟩ : syracuseStep 1344455 = 2016683) B2016683
theorem B1344623 : Blo 892572 1344623 := bstep (se 1 (by rfl) ⟨1008467, by rfl⟩ : syracuseStep 1344623 = 2016935) B2016935
theorem B2262239 : Blo 892572 2262239 := bstep (se 1 (by rfl) ⟨1696679, by rfl⟩ : syracuseStep 2262239 = 3393359) B3393359
theorem B1344815 : Blo 892572 1344815 := bstep (se 1 (by rfl) ⟨1008611, by rfl⟩ : syracuseStep 1344815 = 2017223) B2017223
theorem B3016223 : Blo 892572 3016223 := bstep (se 1 (by rfl) ⟨2262167, by rfl⟩ : syracuseStep 3016223 = 4524335) B4524335
theorem B1508969 : Blo 892572 1508969 := bstep (se 2 (by rfl) ⟨565863, by rfl⟩ : syracuseStep 1508969 = 1131727) B1131727
theorem B3540743 : Blo 892572 3540743 := bstep (se 1 (by rfl) ⟨2655557, by rfl⟩ : syracuseStep 3540743 = 5311115) B5311115
theorem B1509563 : Blo 892572 1509563 := bstep (se 1 (by rfl) ⟨1132172, by rfl⟩ : syracuseStep 1509563 = 2264345) B2264345
theorem B3017087 : Blo 892572 3017087 := bstep (se 1 (by rfl) ⟨2262815, by rfl⟩ : syracuseStep 3017087 = 4525631) B4525631
theorem B2263423 : Blo 892572 2263423 := bstep (se 1 (by rfl) ⟨1697567, by rfl⟩ : syracuseStep 2263423 = 3395135) B3395135
theorem B1510265 : Blo 892572 1510265 := bstep (se 2 (by rfl) ⟨566349, by rfl⟩ : syracuseStep 1510265 = 1132699) B1132699
theorem B8588555 : Blo 892572 8588555 := bstep (se 1 (by rfl) ⟨6441416, by rfl⟩ : syracuseStep 8588555 = 12882833) B12882833
theorem B14683511 : Blo 892572 14683511 := bstep (se 1 (by rfl) ⟨11012633, by rfl⟩ : syracuseStep 14683511 = 22025267) B22025267
theorem B6786989 : Blo 892572 6786989 := bstep (se 3 (by rfl) ⟨1272560, by rfl⟩ : syracuseStep 6786989 = 2545121) B2545121
theorem B1511399 : Blo 892572 1511399 := bstep (se 1 (by rfl) ⟨1133549, by rfl⟩ : syracuseStep 1511399 = 2267099) B2267099
theorem B1511419 : Blo 892572 1511419 := bstep (se 1 (by rfl) ⟨1133564, by rfl⟩ : syracuseStep 1511419 = 2267129) B2267129
theorem B3018815 : Blo 892572 3018815 := bstep (se 1 (by rfl) ⟨2264111, by rfl⟩ : syracuseStep 3018815 = 4528223) B4528223
theorem B1511527 : Blo 892572 1511527 := bstep (se 1 (by rfl) ⟨1133645, by rfl⟩ : syracuseStep 1511527 = 2267291) B2267291
theorem B954523 : Blo 892572 954523 := bstep (se 1 (by rfl) ⟨715892, by rfl⟩ : syracuseStep 954523 = 1431785) B1431785
theorem B11440439 : Blo 892572 11440439 := bstep (se 1 (by rfl) ⟨8580329, by rfl⟩ : syracuseStep 11440439 = 17160659) B17160659
theorem B69571025 : Blo 892572 69571025 := bstep (se 2 (by rfl) ⟨26089134, by rfl⟩ : syracuseStep 69571025 = 52178269) B52178269
theorem B3019517 : Blo 892572 3019517 := bstep (se 3 (by rfl) ⟨566159, by rfl⟩ : syracuseStep 3019517 = 1132319) B1132319
theorem B55087933 : Blo 892572 55087933 := bstep (se 3 (by rfl) ⟨10328987, by rfl⟩ : syracuseStep 55087933 = 20657975) B20657975
theorem B1512283 : Blo 892572 1512283 := bstep (se 1 (by rfl) ⟨1134212, by rfl⟩ : syracuseStep 1512283 = 2268425) B2268425
theorem B3019679 : Blo 892572 3019679 := bstep (se 1 (by rfl) ⟨2264759, by rfl⟩ : syracuseStep 3019679 = 4529519) B4529519
theorem B2266015 : Blo 892572 2266015 := bstep (se 1 (by rfl) ⟨1699511, by rfl⟩ : syracuseStep 2266015 = 3399023) B3399023
theorem B2266319 : Blo 892572 2266319 := bstep (se 1 (by rfl) ⟨1699739, by rfl⟩ : syracuseStep 2266319 = 3399479) B3399479
theorem B1611119 : Blo 892572 1611119 := bstep (se 1 (by rfl) ⟨1208339, by rfl⟩ : syracuseStep 1611119 = 2416679) B2416679
theorem B7345799 : Blo 892572 7345799 := bstep (se 1 (by rfl) ⟨5509349, by rfl⟩ : syracuseStep 7345799 = 11018699) B11018699
theorem B2267423 : Blo 892572 2267423 := bstep (se 1 (by rfl) ⟨1700567, by rfl⟩ : syracuseStep 2267423 = 3401135) B3401135
theorem B6789419 : Blo 892572 6789419 := bstep (se 1 (by rfl) ⟨5092064, by rfl⟩ : syracuseStep 6789419 = 10184129) B10184129
theorem B5086415 : Blo 892572 5086415 := bstep (se 1 (by rfl) ⟨3814811, by rfl⟩ : syracuseStep 5086415 = 7629623) B7629623
theorem B1940843 : Blo 892572 1940843 := bstep (se 1 (by rfl) ⟨1455632, by rfl⟩ : syracuseStep 1940843 = 2911265) B2911265
theorem B892583 : Blo 892572 892583 := bstep (se 1 (by rfl) ⟨669437, by rfl⟩ : syracuseStep 892583 = 1338875) B1338875
theorem B892647 : Blo 892572 892647 := bstep (se 1 (by rfl) ⟨669485, by rfl⟩ : syracuseStep 892647 = 1338971) B1338971
theorem B892703 : Blo 892572 892703 := bstep (se 1 (by rfl) ⟨669527, by rfl⟩ : syracuseStep 892703 = 1339055) B1339055
theorem B11476829 : Blo 892572 11476829 := bstep (se 3 (by rfl) ⟨2151905, by rfl⟩ : syracuseStep 11476829 = 4303811) B4303811
theorem B892783 : Blo 892572 892783 := bstep (se 1 (by rfl) ⟨669587, by rfl⟩ : syracuseStep 892783 = 1339175) B1339175
theorem B892839 : Blo 892572 892839 := bstep (se 1 (by rfl) ⟨669629, by rfl⟩ : syracuseStep 892839 = 1339259) B1339259
theorem B1810409 : Blo 892572 1810409 := bstep (se 2 (by rfl) ⟨678903, by rfl⟩ : syracuseStep 1810409 = 1357807) B1357807
theorem B1908859 : Blo 892572 1908859 := bstep (se 1 (by rfl) ⟨1431644, by rfl⟩ : syracuseStep 1908859 = 2863289) B2863289
theorem B3022973 : Blo 892572 3022973 := bstep (se 3 (by rfl) ⟨566807, by rfl⟩ : syracuseStep 3022973 = 1133615) B1133615
theorem B893119 : Blo 892572 893119 := bstep (se 1 (by rfl) ⟨669839, by rfl⟩ : syracuseStep 893119 = 1339679) B1339679
theorem B893135 : Blo 892572 893135 := bstep (se 1 (by rfl) ⟨669851, by rfl⟩ : syracuseStep 893135 = 1339703) B1339703
theorem B3219671 : Blo 892572 3219671 := bstep (se 1 (by rfl) ⟨2414753, by rfl⟩ : syracuseStep 3219671 = 4829507) B4829507
theorem B893183 : Blo 892572 893183 := bstep (se 1 (by rfl) ⟨669887, by rfl⟩ : syracuseStep 893183 = 1339775) B1339775
theorem B893231 : Blo 892572 893231 := bstep (se 1 (by rfl) ⟨669923, by rfl⟩ : syracuseStep 893231 = 1339847) B1339847
theorem B3023243 : Blo 892572 3023243 := bstep (se 1 (by rfl) ⟨2267432, by rfl⟩ : syracuseStep 3023243 = 4534865) B4534865
theorem B893467 : Blo 892572 893467 := bstep (se 1 (by rfl) ⟨670100, by rfl⟩ : syracuseStep 893467 = 1340201) B1340201
theorem B893471 : Blo 892572 893471 := bstep (se 1 (by rfl) ⟨670103, by rfl⟩ : syracuseStep 893471 = 1340207) B1340207
theorem B893551 : Blo 892572 893551 := bstep (se 1 (by rfl) ⟨670163, by rfl⟩ : syracuseStep 893551 = 1340327) B1340327
theorem B893607 : Blo 892572 893607 := bstep (se 1 (by rfl) ⟨670205, by rfl⟩ : syracuseStep 893607 = 1340411) B1340411
theorem B6890183 : Blo 892572 6890183 := bstep (se 1 (by rfl) ⟨5167637, by rfl⟩ : syracuseStep 6890183 = 10335275) B10335275
theorem B893647 : Blo 892572 893647 := bstep (se 1 (by rfl) ⟨670235, by rfl⟩ : syracuseStep 893647 = 1340471) B1340471
theorem B893727 : Blo 892572 893727 := bstep (se 1 (by rfl) ⟨670295, by rfl⟩ : syracuseStep 893727 = 1340591) B1340591
theorem B893999 : Blo 892572 893999 := bstep (se 1 (by rfl) ⟨670499, by rfl⟩ : syracuseStep 893999 = 1340999) B1340999
theorem B894063 : Blo 892572 894063 := bstep (se 1 (by rfl) ⟨670547, by rfl⟩ : syracuseStep 894063 = 1341095) B1341095
theorem B894119 : Blo 892572 894119 := bstep (se 1 (by rfl) ⟨670589, by rfl⟩ : syracuseStep 894119 = 1341179) B1341179
theorem B894143 : Blo 892572 894143 := bstep (se 1 (by rfl) ⟨670607, by rfl⟩ : syracuseStep 894143 = 1341215) B1341215
theorem B894175 : Blo 892572 894175 := bstep (se 1 (by rfl) ⟨670631, by rfl⟩ : syracuseStep 894175 = 1341263) B1341263
theorem B894255 : Blo 892572 894255 := bstep (se 1 (by rfl) ⟨670691, by rfl⟩ : syracuseStep 894255 = 1341383) B1341383
theorem B2008475 : Blo 892572 2008475 := bstep (se 1 (by rfl) ⟨1506356, by rfl⟩ : syracuseStep 2008475 = 3012713) B3012713
theorem B15508999 : Blo 892572 15508999 := bstep (se 1 (by rfl) ⟨11631749, by rfl⟩ : syracuseStep 15508999 = 23263499) B23263499
theorem B894491 : Blo 892572 894491 := bstep (se 1 (by rfl) ⟨670868, by rfl⟩ : syracuseStep 894491 = 1341737) B1341737
theorem B894495 : Blo 892572 894495 := bstep (se 1 (by rfl) ⟨670871, by rfl⟩ : syracuseStep 894495 = 1341743) B1341743
theorem B894655 : Blo 892572 894655 := bstep (se 1 (by rfl) ⟨670991, by rfl⟩ : syracuseStep 894655 = 1341983) B1341983
theorem B3778345 : Blo 892572 3778345 := bstep (se 2 (by rfl) ⟨1416879, by rfl⟩ : syracuseStep 3778345 = 2833759) B2833759
theorem B894911 : Blo 892572 894911 := bstep (se 1 (by rfl) ⟨671183, by rfl⟩ : syracuseStep 894911 = 1342367) B1342367
theorem B2009051 : Blo 892572 2009051 := bstep (se 1 (by rfl) ⟨1506788, by rfl⟩ : syracuseStep 2009051 = 3013577) B3013577
theorem B894943 : Blo 892572 894943 := bstep (se 1 (by rfl) ⟨671207, by rfl⟩ : syracuseStep 894943 = 1342415) B1342415
theorem B3024863 : Blo 892572 3024863 := bstep (se 1 (by rfl) ⟨2268647, by rfl⟩ : syracuseStep 3024863 = 4537295) B4537295
theorem B895003 : Blo 892572 895003 := bstep (se 1 (by rfl) ⟨671252, by rfl⟩ : syracuseStep 895003 = 1342505) B1342505
theorem B895007 : Blo 892572 895007 := bstep (se 1 (by rfl) ⟨671255, by rfl⟩ : syracuseStep 895007 = 1342511) B1342511
theorem B895023 : Blo 892572 895023 := bstep (se 1 (by rfl) ⟨671267, by rfl⟩ : syracuseStep 895023 = 1342535) B1342535
theorem B212379707 : Blo 892572 212379707 := bstep (se 1 (by rfl) ⟨159284780, by rfl⟩ : syracuseStep 212379707 = 318569561) B318569561
theorem B2009231 : Blo 892572 2009231 := bstep (se 1 (by rfl) ⟨1506923, by rfl⟩ : syracuseStep 2009231 = 3013847) B3013847
theorem B895199 : Blo 892572 895199 := bstep (se 1 (by rfl) ⟨671399, by rfl⟩ : syracuseStep 895199 = 1342799) B1342799
theorem B2009321 : Blo 892572 2009321 := bstep (se 2 (by rfl) ⟨753495, by rfl⟩ : syracuseStep 2009321 = 1506991) B1506991
theorem B895259 : Blo 892572 895259 := bstep (se 1 (by rfl) ⟨671444, by rfl⟩ : syracuseStep 895259 = 1342889) B1342889
theorem B895359 : Blo 892572 895359 := bstep (se 1 (by rfl) ⟨671519, by rfl⟩ : syracuseStep 895359 = 1343039) B1343039
theorem B2009591 : Blo 892572 2009591 := bstep (se 1 (by rfl) ⟨1507193, by rfl⟩ : syracuseStep 2009591 = 3014387) B3014387
theorem B65317421 : Blo 892572 65317421 := bstep (se 3 (by rfl) ⟨12247016, by rfl⟩ : syracuseStep 65317421 = 24494033) B24494033
theorem B895535 : Blo 892572 895535 := bstep (se 1 (by rfl) ⟨671651, by rfl⟩ : syracuseStep 895535 = 1343303) B1343303
theorem B5450321 : Blo 892572 5450321 := bstep (se 2 (by rfl) ⟨2043870, by rfl⟩ : syracuseStep 5450321 = 4087741) B4087741
theorem B895591 : Blo 892572 895591 := bstep (se 1 (by rfl) ⟨671693, by rfl⟩ : syracuseStep 895591 = 1343387) B1343387
theorem B4827863 : Blo 892572 4827863 := bstep (se 1 (by rfl) ⟨3620897, by rfl⟩ : syracuseStep 4827863 = 7241795) B7241795
theorem B895967 : Blo 892572 895967 := bstep (se 1 (by rfl) ⟨671975, by rfl⟩ : syracuseStep 895967 = 1343951) B1343951
theorem B895995 : Blo 892572 895995 := bstep (se 1 (by rfl) ⟨671996, by rfl⟩ : syracuseStep 895995 = 1343993) B1343993
theorem B896063 : Blo 892572 896063 := bstep (se 1 (by rfl) ⟨672047, by rfl⟩ : syracuseStep 896063 = 1344095) B1344095
theorem B17443907 : Blo 892572 17443907 := bstep (se 1 (by rfl) ⟨13082930, by rfl⟩ : syracuseStep 17443907 = 26165861) B26165861
theorem B2010185 : Blo 892572 2010185 := bstep (se 2 (by rfl) ⟨753819, by rfl⟩ : syracuseStep 2010185 = 1507639) B1507639
theorem B2862391 : Blo 892572 2862391 := bstep (se 1 (by rfl) ⟨2146793, by rfl⟩ : syracuseStep 2862391 = 4293587) B4293587
theorem B896383 : Blo 892572 896383 := bstep (se 1 (by rfl) ⟨672287, by rfl⟩ : syracuseStep 896383 = 1344575) B1344575
theorem B896411 : Blo 892572 896411 := bstep (se 1 (by rfl) ⟨672308, by rfl⟩ : syracuseStep 896411 = 1344617) B1344617
theorem B896479 : Blo 892572 896479 := bstep (se 1 (by rfl) ⟨672359, by rfl⟩ : syracuseStep 896479 = 1344719) B1344719
theorem B11448125 : Blo 892572 11448125 := bstep (se 3 (by rfl) ⟨2146523, by rfl⟩ : syracuseStep 11448125 = 4293047) B4293047
theorem B4829033 : Blo 892572 4829033 := bstep (se 2 (by rfl) ⟨1810887, by rfl⟩ : syracuseStep 4829033 = 3621775) B3621775
theorem B6795251 : Blo 892572 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B15511783 : Blo 892572 15511783 := bstep (se 1 (by rfl) ⟨11633837, by rfl⟩ : syracuseStep 15511783 = 23267675) B23267675
theorem B14529131 : Blo 892572 14529131 := bstep (se 1 (by rfl) ⟨10896848, by rfl⟩ : syracuseStep 14529131 = 21793697) B21793697
theorem B2011913 : Blo 892572 2011913 := bstep (se 2 (by rfl) ⟨754467, by rfl⟩ : syracuseStep 2011913 = 1508935) B1508935
theorem B2011967 : Blo 892572 2011967 := bstep (se 1 (by rfl) ⟨1508975, by rfl⟩ : syracuseStep 2011967 = 3017951) B3017951
theorem B4305793 : Blo 892572 4305793 := bstep (se 2 (by rfl) ⟨1614672, by rfl⟩ : syracuseStep 4305793 = 3229345) B3229345
theorem B2012111 : Blo 892572 2012111 := bstep (se 1 (by rfl) ⟨1509083, by rfl⟩ : syracuseStep 2012111 = 3018167) B3018167
theorem B6435881 : Blo 892572 6435881 := bstep (se 2 (by rfl) ⟨2413455, by rfl⟩ : syracuseStep 6435881 = 4826911) B4826911
theorem B2012201 : Blo 892572 2012201 := bstep (se 2 (by rfl) ⟨754575, by rfl⟩ : syracuseStep 2012201 = 1509151) B1509151
theorem B1914121 : Blo 892572 1914121 := bstep (se 2 (by rfl) ⟨717795, by rfl⟩ : syracuseStep 1914121 = 1435591) B1435591
theorem B2012489 : Blo 892572 2012489 := bstep (se 2 (by rfl) ⟨754683, by rfl⟩ : syracuseStep 2012489 = 1509367) B1509367
theorem B44086999 : Blo 892572 44086999 := bstep (se 1 (by rfl) ⟨33065249, by rfl⟩ : syracuseStep 44086999 = 66130499) B66130499
theorem B10172465 : Blo 892572 10172465 := bstep (se 2 (by rfl) ⟨3814674, by rfl⟩ : syracuseStep 10172465 = 7629349) B7629349
theorem B3815495 : Blo 892572 3815495 := bstep (se 1 (by rfl) ⟨2861621, by rfl⟩ : syracuseStep 3815495 = 5723243) B5723243
theorem B2013479 : Blo 892572 2013479 := bstep (se 1 (by rfl) ⟨1510109, by rfl⟩ : syracuseStep 2013479 = 3020219) B3020219
theorem B35404235 : Blo 892572 35404235 := bstep (se 1 (by rfl) ⟨26553176, by rfl⟩ : syracuseStep 35404235 = 53106353) B53106353
theorem B2013839 : Blo 892572 2013839 := bstep (se 1 (by rfl) ⟨1510379, by rfl⟩ : syracuseStep 2013839 = 3020759) B3020759
theorem B2865851 : Blo 892572 2865851 := bstep (se 1 (by rfl) ⟨2149388, by rfl⟩ : syracuseStep 2865851 = 4298777) B4298777
theorem B2013929 : Blo 892572 2013929 := bstep (se 2 (by rfl) ⟨755223, by rfl⟩ : syracuseStep 2013929 = 1510447) B1510447
theorem B2014163 : Blo 892572 2014163 := bstep (se 1 (by rfl) ⟨1510622, by rfl⟩ : syracuseStep 2014163 = 3021245) B3021245
theorem B2014433 : Blo 892572 2014433 := bstep (se 2 (by rfl) ⟨755412, by rfl⟩ : syracuseStep 2014433 = 1510825) B1510825
theorem B7453949 : Blo 892572 7453949 := bstep (se 3 (by rfl) ⟨1397615, by rfl⟩ : syracuseStep 7453949 = 2795231) B2795231
theorem B2014739 : Blo 892572 2014739 := bstep (se 1 (by rfl) ⟨1511054, by rfl⟩ : syracuseStep 2014739 = 3022109) B3022109
theorem B7258085 : Blo 892572 7258085 := bstep (se 4 (by rfl) ⟨680445, by rfl⟩ : syracuseStep 7258085 = 1360891) B1360891
theorem B2015423 : Blo 892572 2015423 := bstep (se 1 (by rfl) ⟨1511567, by rfl⟩ : syracuseStep 2015423 = 3023135) B3023135
theorem B3391901 : Blo 892572 3391901 := bstep (se 3 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 3391901 = 1271963) B1271963
theorem B3228263 : Blo 892572 3228263 := bstep (se 1 (by rfl) ⟨2421197, by rfl⟩ : syracuseStep 3228263 = 4842395) B4842395
theorem B2015855 : Blo 892572 2015855 := bstep (se 1 (by rfl) ⟨1511891, by rfl⟩ : syracuseStep 2015855 = 3023783) B3023783
theorem B7258859 : Blo 892572 7258859 := bstep (se 1 (by rfl) ⟨5444144, by rfl⟩ : syracuseStep 7258859 = 10888289) B10888289
theorem B5096303 : Blo 892572 5096303 := bstep (se 1 (by rfl) ⟨3822227, by rfl⟩ : syracuseStep 5096303 = 7644455) B7644455
theorem B2016251 : Blo 892572 2016251 := bstep (se 1 (by rfl) ⟨1512188, by rfl⟩ : syracuseStep 2016251 = 3024377) B3024377
theorem B2016431 : Blo 892572 2016431 := bstep (se 1 (by rfl) ⟨1512323, by rfl⟩ : syracuseStep 2016431 = 3024647) B3024647
theorem B2016467 : Blo 892572 2016467 := bstep (se 1 (by rfl) ⟨1512350, by rfl⟩ : syracuseStep 2016467 = 3024701) B3024701
theorem B1131823 : Blo 892572 1131823 := bstep (se 1 (by rfl) ⟨848867, by rfl⟩ : syracuseStep 1131823 = 1697735) B1697735
theorem B2016737 : Blo 892572 2016737 := bstep (se 2 (by rfl) ⟨756276, by rfl⟩ : syracuseStep 2016737 = 1512553) B1512553
theorem B3393191 : Blo 892572 3393191 := bstep (se 1 (by rfl) ⟨2544893, by rfl⟩ : syracuseStep 3393191 = 5089787) B5089787
theorem B1362143 : Blo 892572 1362143 := bstep (se 1 (by rfl) ⟨1021607, by rfl⟩ : syracuseStep 1362143 = 2043215) B2043215
theorem B10307897 : Blo 892572 10307897 := bstep (se 2 (by rfl) ⟨3865461, by rfl⟩ : syracuseStep 10307897 = 7730923) B7730923
theorem B3394163 : Blo 892572 3394163 := bstep (se 1 (by rfl) ⟨2545622, by rfl⟩ : syracuseStep 3394163 = 5091245) B5091245
theorem B3394345 : Blo 892572 3394345 := bstep (se 2 (by rfl) ⟨1272879, by rfl⟩ : syracuseStep 3394345 = 2545759) B2545759
theorem B3820553 : Blo 892572 3820553 := bstep (se 2 (by rfl) ⟨1432707, by rfl⟩ : syracuseStep 3820553 = 2865415) B2865415
theorem B14502989 : Blo 892572 14502989 := bstep (se 3 (by rfl) ⟨2719310, by rfl⟩ : syracuseStep 14502989 = 5438621) B5438621
theorem B19320095 : Blo 892572 19320095 := bstep (se 1 (by rfl) ⟨14490071, by rfl⟩ : syracuseStep 19320095 = 28980143) B28980143
theorem B1134587 : Blo 892572 1134587 := bstep (se 1 (by rfl) ⟨850940, by rfl⟩ : syracuseStep 1134587 = 1701881) B1701881
theorem B5099719 : Blo 892572 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B3395803 : Blo 892572 3395803 := bstep (se 1 (by rfl) ⟨2546852, by rfl⟩ : syracuseStep 3395803 = 5093705) B5093705
theorem B2183411 : Blo 892572 2183411 := bstep (se 1 (by rfl) ⟨1637558, by rfl⟩ : syracuseStep 2183411 = 3275117) B3275117
theorem B1429883 : Blo 892572 1429883 := bstep (se 1 (by rfl) ⟨1072412, by rfl⟩ : syracuseStep 1429883 = 2144825) B2144825
theorem B2872169 : Blo 892572 2872169 := bstep (se 2 (by rfl) ⟨1077063, by rfl⟩ : syracuseStep 2872169 = 2154127) B2154127
theorem B906223 : Blo 892572 906223 := bstep (se 1 (by rfl) ⟨679667, by rfl⟩ : syracuseStep 906223 = 1359335) B1359335
theorem B185881871 : Blo 892572 185881871 := bstep (se 1 (by rfl) ⟨139411403, by rfl⟩ : syracuseStep 185881871 = 278822807) B278822807
theorem B1004863 : Blo 892572 1004863 := bstep (se 1 (by rfl) ⟨753647, by rfl⟩ : syracuseStep 1004863 = 1507295) B1507295
theorem B7656929 : Blo 892572 7656929 := bstep (se 2 (by rfl) ⟨2871348, by rfl⟩ : syracuseStep 7656929 = 5742697) B5742697
theorem B5101177 : Blo 892572 5101177 := bstep (se 2 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 5101177 = 3825883) B3825883
theorem B3823271 : Blo 892572 3823271 := bstep (se 1 (by rfl) ⟨2867453, by rfl⟩ : syracuseStep 3823271 = 5734907) B5734907
theorem B1005295 : Blo 892572 1005295 := bstep (se 1 (by rfl) ⟨753971, by rfl⟩ : syracuseStep 1005295 = 1507943) B1507943
theorem B3823355 : Blo 892572 3823355 := bstep (se 1 (by rfl) ⟨2867516, by rfl⟩ : syracuseStep 3823355 = 5735033) B5735033
theorem B9688855 : Blo 892572 9688855 := bstep (se 1 (by rfl) ⟨7266641, by rfl⟩ : syracuseStep 9688855 = 14533283) B14533283
theorem B1005403 : Blo 892572 1005403 := bstep (se 1 (by rfl) ⟨754052, by rfl⟩ : syracuseStep 1005403 = 1508105) B1508105
theorem B3397565 : Blo 892572 3397565 := bstep (se 3 (by rfl) ⟨637043, by rfl⟩ : syracuseStep 3397565 = 1274087) B1274087
theorem B1005799 : Blo 892572 1005799 := bstep (se 1 (by rfl) ⟨754349, by rfl⟩ : syracuseStep 1005799 = 1508699) B1508699
theorem B3823955 : Blo 892572 3823955 := bstep (se 1 (by rfl) ⟨2867966, by rfl⟩ : syracuseStep 3823955 = 5735933) B5735933
theorem B1006447 : Blo 892572 1006447 := bstep (se 1 (by rfl) ⟨754835, by rfl⟩ : syracuseStep 1006447 = 1509671) B1509671
theorem B3398993 : Blo 892572 3398993 := bstep (se 2 (by rfl) ⟨1274622, by rfl⟩ : syracuseStep 3398993 = 2549245) B2549245
theorem B8150381 : Blo 892572 8150381 := bstep (se 3 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 8150381 = 3056393) B3056393
theorem B6970835 : Blo 892572 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B1695305 : Blo 892572 1695305 := bstep (se 2 (by rfl) ⟨635739, by rfl⟩ : syracuseStep 1695305 = 1271479) B1271479
theorem B1007527 : Blo 892572 1007527 := bstep (se 1 (by rfl) ⟨755645, by rfl⟩ : syracuseStep 1007527 = 1511291) B1511291
theorem B3399965 : Blo 892572 3399965 := bstep (se 3 (by rfl) ⟨637493, by rfl⟩ : syracuseStep 3399965 = 1274987) B1274987
theorem B22963499 : Blo 892572 22963499 := bstep (se 1 (by rfl) ⟨17222624, by rfl⟩ : syracuseStep 22963499 = 34445249) B34445249
theorem B15295877 : Blo 892572 15295877 := bstep (se 4 (by rfl) ⟨1433988, by rfl⟩ : syracuseStep 15295877 = 2867977) B2867977
theorem B2615419 : Blo 892572 2615419 := bstep (se 1 (by rfl) ⟨1961564, by rfl⟩ : syracuseStep 2615419 = 3923129) B3923129
theorem B3401939 : Blo 892572 3401939 := bstep (se 1 (by rfl) ⟨2551454, by rfl⟩ : syracuseStep 3401939 = 5102909) B5102909
theorem B7268717 : Blo 892572 7268717 := bstep (se 3 (by rfl) ⟨1362884, by rfl⟩ : syracuseStep 7268717 = 2725769) B2725769
theorem B3402121 : Blo 892572 3402121 := bstep (se 2 (by rfl) ⟨1275795, by rfl⟩ : syracuseStep 3402121 = 2551591) B2551591
theorem B3828329 : Blo 892572 3828329 := bstep (se 2 (by rfl) ⟨1435623, by rfl⟩ : syracuseStep 3828329 = 2871247) B2871247
theorem B6548357 : Blo 892572 6548357 := bstep (se 4 (by rfl) ⟨613908, by rfl⟩ : syracuseStep 6548357 = 1227817) B1227817
theorem B1698889 : Blo 892572 1698889 := bstep (se 2 (by rfl) ⟨637083, by rfl⟩ : syracuseStep 1698889 = 1274167) B1274167
theorem B2550953 : Blo 892572 2550953 := bstep (se 2 (by rfl) ⟨956607, by rfl⟩ : syracuseStep 2550953 = 1913215) B1913215
theorem B48885191 : Blo 892572 48885191 := bstep (se 1 (by rfl) ⟨36663893, by rfl⟩ : syracuseStep 48885191 = 73327787) B73327787
theorem B17034877 : Blo 892572 17034877 := bstep (se 3 (by rfl) ⟨3194039, by rfl⟩ : syracuseStep 17034877 = 6388079) B6388079
theorem B1339199 : Blo 892572 1339199 := bstep (se 1 (by rfl) ⟨1004399, by rfl⟩ : syracuseStep 1339199 = 2008799) B2008799
theorem B14708567 : Blo 892572 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B1339385 : Blo 892572 1339385 := bstep (se 2 (by rfl) ⟨502269, by rfl⟩ : syracuseStep 1339385 = 1004539) B1004539
theorem B1699967 : Blo 892572 1699967 := bstep (se 1 (by rfl) ⟨1274975, by rfl⟩ : syracuseStep 1699967 = 2549951) B2549951
theorem B1339625 : Blo 892572 1339625 := bstep (se 2 (by rfl) ⟨502359, by rfl⟩ : syracuseStep 1339625 = 1004719) B1004719
theorem B1339751 : Blo 892572 1339751 := bstep (se 1 (by rfl) ⟨1004813, by rfl⟩ : syracuseStep 1339751 = 2009627) B2009627
theorem B7631333 : Blo 892572 7631333 := bstep (se 4 (by rfl) ⟨715437, by rfl⟩ : syracuseStep 7631333 = 1430875) B1430875
theorem B4518665 : Blo 892572 4518665 := bstep (se 2 (by rfl) ⟨1694499, by rfl⟩ : syracuseStep 4518665 = 3388999) B3388999
theorem B6452027 : Blo 892572 6452027 := bstep (se 1 (by rfl) ⟨4839020, by rfl⟩ : syracuseStep 6452027 = 9678041) B9678041
theorem B1340297 : Blo 892572 1340297 := bstep (se 2 (by rfl) ⟨502611, by rfl⟩ : syracuseStep 1340297 = 1005223) B1005223
theorem B5731343 : Blo 892572 5731343 := bstep (se 1 (by rfl) ⟨4298507, by rfl⟩ : syracuseStep 5731343 = 8597015) B8597015
theorem B34796627 : Blo 892572 34796627 := bstep (se 1 (by rfl) ⟨26097470, by rfl⟩ : syracuseStep 34796627 = 52194941) B52194941
theorem B2553095 : Blo 892572 2553095 := bstep (se 1 (by rfl) ⟨1914821, by rfl⟩ : syracuseStep 2553095 = 3829643) B3829643
theorem B1340681 : Blo 892572 1340681 := bstep (se 2 (by rfl) ⟨502755, by rfl⟩ : syracuseStep 1340681 = 1005511) B1005511
theorem B26178835 : Blo 892572 26178835 := bstep (se 1 (by rfl) ⟨19634126, by rfl⟩ : syracuseStep 26178835 = 39268253) B39268253
theorem B1340735 : Blo 892572 1340735 := bstep (se 1 (by rfl) ⟨1005551, by rfl⟩ : syracuseStep 1340735 = 2011103) B2011103
theorem B2422183 : Blo 892572 2422183 := bstep (se 1 (by rfl) ⟨1816637, by rfl⟩ : syracuseStep 2422183 = 3633275) B3633275
theorem B9663943 : Blo 892572 9663943 := bstep (se 1 (by rfl) ⟨7247957, by rfl⟩ : syracuseStep 9663943 = 14495915) B14495915
theorem B8255033 : Blo 892572 8255033 := bstep (se 2 (by rfl) ⟨3095637, by rfl⟩ : syracuseStep 8255033 = 6191275) B6191275
theorem B2717279 : Blo 892572 2717279 := bstep (se 1 (by rfl) ⟨2037959, by rfl⟩ : syracuseStep 2717279 = 4075919) B4075919
theorem B1341161 : Blo 892572 1341161 := bstep (se 2 (by rfl) ⟨502935, by rfl⟩ : syracuseStep 1341161 = 1005871) B1005871
theorem B1275625 : Blo 892572 1275625 := bstep (se 2 (by rfl) ⟨478359, by rfl⟩ : syracuseStep 1275625 = 956719) B956719
theorem B1341167 : Blo 892572 1341167 := bstep (se 1 (by rfl) ⟨1005875, by rfl⟩ : syracuseStep 1341167 = 2011751) B2011751
theorem B3012551 : Blo 892572 3012551 := bstep (se 1 (by rfl) ⟨2259413, by rfl⟩ : syracuseStep 3012551 = 4518827) B4518827
theorem B4519961 : Blo 892572 4519961 := bstep (se 2 (by rfl) ⟨1694985, by rfl⟩ : syracuseStep 4519961 = 3389971) B3389971
theorem B28997675 : Blo 892572 28997675 := bstep (se 1 (by rfl) ⟨21748256, by rfl⟩ : syracuseStep 28997675 = 43496513) B43496513
theorem B1341623 : Blo 892572 1341623 := bstep (se 1 (by rfl) ⟨1006217, by rfl⟩ : syracuseStep 1341623 = 2012435) B2012435
theorem B4356299 : Blo 892572 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B1341671 : Blo 892572 1341671 := bstep (se 1 (by rfl) ⟨1006253, by rfl⟩ : syracuseStep 1341671 = 2012507) B2012507
theorem B1342043 : Blo 892572 1342043 := bstep (se 1 (by rfl) ⟨1006532, by rfl⟩ : syracuseStep 1342043 = 2013065) B2013065
theorem B1342187 : Blo 892572 1342187 := bstep (se 1 (by rfl) ⟨1006640, by rfl⟩ : syracuseStep 1342187 = 2013281) B2013281
theorem B1342217 : Blo 892572 1342217 := bstep (se 2 (by rfl) ⟨503331, by rfl⟩ : syracuseStep 1342217 = 1006663) B1006663
theorem B24771397 : Blo 892572 24771397 := bstep (se 4 (by rfl) ⟨2322318, by rfl⟩ : syracuseStep 24771397 = 4644637) B4644637
theorem B4127689 : Blo 892572 4127689 := bstep (se 2 (by rfl) ⟨1547883, by rfl⟩ : syracuseStep 4127689 = 3095767) B3095767
theorem B7633997 : Blo 892572 7633997 := bstep (se 3 (by rfl) ⟨1431374, by rfl⟩ : syracuseStep 7633997 = 2862749) B2862749
theorem B7241147 : Blo 892572 7241147 := bstep (se 1 (by rfl) ⟨5430860, by rfl⟩ : syracuseStep 7241147 = 10861721) B10861721
theorem B1343087 : Blo 892572 1343087 := bstep (se 1 (by rfl) ⟨1007315, by rfl⟩ : syracuseStep 1343087 = 2014631) B2014631
theorem B1343207 : Blo 892572 1343207 := bstep (se 1 (by rfl) ⟨1007405, by rfl⟩ : syracuseStep 1343207 = 2014811) B2014811
theorem B3866377 : Blo 892572 3866377 := bstep (se 2 (by rfl) ⟨1449891, by rfl⟩ : syracuseStep 3866377 = 2899783) B2899783
theorem B1343399 : Blo 892572 1343399 := bstep (se 1 (by rfl) ⟨1007549, by rfl⟩ : syracuseStep 1343399 = 2015099) B2015099
theorem B1343615 : Blo 892572 1343615 := bstep (se 1 (by rfl) ⟨1007711, by rfl⟩ : syracuseStep 1343615 = 2015423) B2015423
theorem B2261267 : Blo 892572 2261267 := bstep (se 1 (by rfl) ⟨1695950, by rfl⟩ : syracuseStep 2261267 = 3391901) B3391901
theorem B1343903 : Blo 892572 1343903 := bstep (se 1 (by rfl) ⟨1007927, by rfl⟩ : syracuseStep 1343903 = 2015855) B2015855
theorem B1344167 : Blo 892572 1344167 := bstep (se 1 (by rfl) ⟨1008125, by rfl⟩ : syracuseStep 1344167 = 2016251) B2016251
theorem B1344287 : Blo 892572 1344287 := bstep (se 1 (by rfl) ⟨1008215, by rfl⟩ : syracuseStep 1344287 = 2016431) B2016431
theorem B1344311 : Blo 892572 1344311 := bstep (se 1 (by rfl) ⟨1008233, by rfl⟩ : syracuseStep 1344311 = 2016467) B2016467
theorem B1508159 : Blo 892572 1508159 := bstep (se 1 (by rfl) ⟨1131119, by rfl⟩ : syracuseStep 1508159 = 2262239) B2262239
theorem B1344491 : Blo 892572 1344491 := bstep (se 1 (by rfl) ⟨1008368, by rfl⟩ : syracuseStep 1344491 = 2016737) B2016737
theorem B2262127 : Blo 892572 2262127 := bstep (se 1 (by rfl) ⟨1696595, by rfl⟩ : syracuseStep 2262127 = 3393191) B3393191
theorem B2360495 : Blo 892572 2360495 := bstep (se 1 (by rfl) ⟨1770371, by rfl⟩ : syracuseStep 2360495 = 3540743) B3540743
theorem B1509097 : Blo 892572 1509097 := bstep (se 2 (by rfl) ⟨565911, by rfl⟩ : syracuseStep 1509097 = 1131823) B1131823
theorem B2262775 : Blo 892572 2262775 := bstep (se 1 (by rfl) ⟨1697081, by rfl⟩ : syracuseStep 2262775 = 3394163) B3394163
theorem B20678665 : Blo 892572 20678665 := bstep (se 2 (by rfl) ⟨7754499, by rfl⟩ : syracuseStep 20678665 = 15508999) B15508999
theorem B9668659 : Blo 892572 9668659 := bstep (se 1 (by rfl) ⟨7251494, by rfl⟩ : syracuseStep 9668659 = 14502989) B14502989
theorem B12880063 : Blo 892572 12880063 := bstep (se 1 (by rfl) ⟨9660047, by rfl⟩ : syracuseStep 12880063 = 19320095) B19320095
theorem B4524659 : Blo 892572 4524659 := bstep (se 1 (by rfl) ⟨3393494, by rfl⟩ : syracuseStep 4524659 = 6786989) B6786989
theorem B953255 : Blo 892572 953255 := bstep (se 1 (by rfl) ⟨714941, by rfl⟩ : syracuseStep 953255 = 1429883) B1429883
theorem B3017897 : Blo 892572 3017897 := bstep (se 2 (by rfl) ⟨1131711, by rfl⟩ : syracuseStep 3017897 = 2263423) B2263423
theorem B1510879 : Blo 892572 1510879 := bstep (se 1 (by rfl) ⟨1133159, by rfl⟩ : syracuseStep 1510879 = 2266319) B2266319
theorem B4525793 : Blo 892572 4525793 := bstep (se 2 (by rfl) ⟨1697172, by rfl⟩ : syracuseStep 4525793 = 3394345) B3394345
theorem B2265043 : Blo 892572 2265043 := bstep (se 1 (by rfl) ⟨1698782, by rfl⟩ : syracuseStep 2265043 = 3397565) B3397565
theorem B2265185 : Blo 892572 2265185 := bstep (se 2 (by rfl) ⟨849444, by rfl⟩ : syracuseStep 2265185 = 1698889) B1698889
theorem B1511615 : Blo 892572 1511615 := bstep (se 1 (by rfl) ⟨1133711, by rfl⟩ : syracuseStep 1511615 = 2267423) B2267423
theorem B4526279 : Blo 892572 4526279 := bstep (se 1 (by rfl) ⟨3394709, by rfl⟩ : syracuseStep 4526279 = 6789419) B6789419
theorem B22713169 : Blo 892572 22713169 := bstep (se 2 (by rfl) ⟨8517438, by rfl⟩ : syracuseStep 22713169 = 17034877) B17034877
theorem B2265995 : Blo 892572 2265995 := bstep (se 1 (by rfl) ⟨1699496, by rfl⟩ : syracuseStep 2265995 = 3398993) B3398993
theorem B2266643 : Blo 892572 2266643 := bstep (se 1 (by rfl) ⟨1699982, by rfl⟩ : syracuseStep 2266643 = 3399965) B3399965
theorem B4527737 : Blo 892572 4527737 := bstep (se 2 (by rfl) ⟨1697901, by rfl⟩ : syracuseStep 4527737 = 3395803) B3395803
theorem B20682377 : Blo 892572 20682377 := bstep (se 2 (by rfl) ⟨7755891, by rfl⟩ : syracuseStep 20682377 = 15511783) B15511783
theorem B4593455 : Blo 892572 4593455 := bstep (se 1 (by rfl) ⟨3445091, by rfl⟩ : syracuseStep 4593455 = 6890183) B6890183
theorem B15308999 : Blo 892572 15308999 := bstep (se 1 (by rfl) ⟨11481749, by rfl⟩ : syracuseStep 15308999 = 22963499) B22963499
theorem B10197251 : Blo 892572 10197251 := bstep (se 1 (by rfl) ⟨7647938, by rfl⟩ : syracuseStep 10197251 = 15295877) B15295877
theorem B5741057 : Blo 892572 5741057 := bstep (se 2 (by rfl) ⟨2152896, by rfl⟩ : syracuseStep 5741057 = 4305793) B4305793
theorem B3021353 : Blo 892572 3021353 := bstep (se 2 (by rfl) ⟨1133007, by rfl⟩ : syracuseStep 3021353 = 2266015) B2266015
theorem B2267959 : Blo 892572 2267959 := bstep (se 1 (by rfl) ⟨1700969, by rfl⟩ : syracuseStep 2267959 = 3401939) B3401939
theorem B34905113 : Blo 892572 34905113 := bstep (se 2 (by rfl) ⟨13089417, by rfl⟩ : syracuseStep 34905113 = 26178835) B26178835
theorem B4365571 : Blo 892572 4365571 := bstep (se 1 (by rfl) ⟨3274178, by rfl⟩ : syracuseStep 4365571 = 6548357) B6548357
theorem B12885257 : Blo 892572 12885257 := bstep (se 2 (by rfl) ⟨4831971, by rfl⟩ : syracuseStep 12885257 = 9663943) B9663943
theorem B12918473 : Blo 892572 12918473 := bstep (se 2 (by rfl) ⟨4844427, by rfl⟩ : syracuseStep 12918473 = 9688855) B9688855
theorem B892799 : Blo 892572 892799 := bstep (se 1 (by rfl) ⟨669599, by rfl⟩ : syracuseStep 892799 = 1339199) B1339199
theorem B9805711 : Blo 892572 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B3219355 : Blo 892572 3219355 := bstep (se 1 (by rfl) ⟨2414516, by rfl⟩ : syracuseStep 3219355 = 4829033) B4829033
theorem B4530167 : Blo 892572 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B892923 : Blo 892572 892923 := bstep (se 1 (by rfl) ⟨669692, by rfl⟩ : syracuseStep 892923 = 1339385) B1339385
theorem B893083 : Blo 892572 893083 := bstep (se 1 (by rfl) ⟨669812, by rfl⟩ : syracuseStep 893083 = 1339625) B1339625
theorem B893167 : Blo 892572 893167 := bstep (se 1 (by rfl) ⟨669875, by rfl⟩ : syracuseStep 893167 = 1339751) B1339751
theorem B5087555 : Blo 892572 5087555 := bstep (se 1 (by rfl) ⟨3815666, by rfl⟩ : syracuseStep 5087555 = 7631333) B7631333
theorem B4301351 : Blo 892572 4301351 := bstep (se 1 (by rfl) ⟨3226013, by rfl⟩ : syracuseStep 4301351 = 6452027) B6452027
theorem B893531 : Blo 892572 893531 := bstep (se 1 (by rfl) ⟨670148, by rfl⟩ : syracuseStep 893531 = 1340297) B1340297
theorem B893787 : Blo 892572 893787 := bstep (se 1 (by rfl) ⟨670340, by rfl⟩ : syracuseStep 893787 = 1340681) B1340681
theorem B893823 : Blo 892572 893823 := bstep (se 1 (by rfl) ⟨670367, by rfl⟩ : syracuseStep 893823 = 1340735) B1340735
theorem B1811519 : Blo 892572 1811519 := bstep (se 1 (by rfl) ⟨1358639, by rfl⟩ : syracuseStep 1811519 = 2717279) B2717279
theorem B894107 : Blo 892572 894107 := bstep (se 1 (by rfl) ⟨670580, by rfl⟩ : syracuseStep 894107 = 1341161) B1341161
theorem B894111 : Blo 892572 894111 := bstep (se 1 (by rfl) ⟨670583, by rfl⟩ : syracuseStep 894111 = 1341167) B1341167
theorem B2008367 : Blo 892572 2008367 := bstep (se 1 (by rfl) ⟨1506275, by rfl⟩ : syracuseStep 2008367 = 3012551) B3012551
theorem B894415 : Blo 892572 894415 := bstep (se 1 (by rfl) ⟨670811, by rfl⟩ : syracuseStep 894415 = 1341623) B1341623
theorem B894447 : Blo 892572 894447 := bstep (se 1 (by rfl) ⟨670835, by rfl⟩ : syracuseStep 894447 = 1341671) B1341671
theorem B23602823 : Blo 892572 23602823 := bstep (se 1 (by rfl) ⟨17702117, by rfl⟩ : syracuseStep 23602823 = 35404235) B35404235
theorem B894695 : Blo 892572 894695 := bstep (se 1 (by rfl) ⟨671021, by rfl⟩ : syracuseStep 894695 = 1342043) B1342043
theorem B1910567 : Blo 892572 1910567 := bstep (se 1 (by rfl) ⟨1432925, by rfl⟩ : syracuseStep 1910567 = 2865851) B2865851
theorem B894791 : Blo 892572 894791 := bstep (se 1 (by rfl) ⟨671093, by rfl⟩ : syracuseStep 894791 = 1342187) B1342187
theorem B894811 : Blo 892572 894811 := bstep (se 1 (by rfl) ⟨671108, by rfl⟩ : syracuseStep 894811 = 1342217) B1342217
theorem B5089331 : Blo 892572 5089331 := bstep (se 1 (by rfl) ⟨3816998, by rfl⟩ : syracuseStep 5089331 = 7633997) B7633997
theorem B4827431 : Blo 892572 4827431 := bstep (se 1 (by rfl) ⟨3620573, by rfl⟩ : syracuseStep 4827431 = 7241147) B7241147
theorem B5155169 : Blo 892572 5155169 := bstep (se 2 (by rfl) ⟨1933188, by rfl⟩ : syracuseStep 5155169 = 3866377) B3866377
theorem B895391 : Blo 892572 895391 := bstep (se 1 (by rfl) ⟨671543, by rfl⟩ : syracuseStep 895391 = 1343087) B1343087
theorem B895471 : Blo 892572 895471 := bstep (se 1 (by rfl) ⟨671603, by rfl⟩ : syracuseStep 895471 = 1343207) B1343207
theorem B4827757 : Blo 892572 4827757 := bstep (se 3 (by rfl) ⟨905204, by rfl⟩ : syracuseStep 4827757 = 1810409) B1810409
theorem B895599 : Blo 892572 895599 := bstep (se 1 (by rfl) ⟨671699, by rfl⟩ : syracuseStep 895599 = 1343399) B1343399
theorem B3025565 : Blo 892572 3025565 := bstep (se 3 (by rfl) ⟨567293, by rfl⟩ : syracuseStep 3025565 = 1134587) B1134587
theorem B895815 : Blo 892572 895815 := bstep (se 1 (by rfl) ⟨671861, by rfl⟩ : syracuseStep 895815 = 1343723) B1343723
theorem B895855 : Blo 892572 895855 := bstep (se 1 (by rfl) ⟨671891, by rfl⟩ : syracuseStep 895855 = 1343783) B1343783
theorem B4533245 : Blo 892572 4533245 := bstep (se 3 (by rfl) ⟨849983, by rfl⟩ : syracuseStep 4533245 = 1699967) B1699967
theorem B10857635 : Blo 892572 10857635 := bstep (se 1 (by rfl) ⟨8143226, by rfl⟩ : syracuseStep 10857635 = 16286453) B16286453
theorem B896303 : Blo 892572 896303 := bstep (se 1 (by rfl) ⟨672227, by rfl⟩ : syracuseStep 896303 = 1344455) B1344455
theorem B896415 : Blo 892572 896415 := bstep (se 1 (by rfl) ⟨672311, by rfl⟩ : syracuseStep 896415 = 1344623) B1344623
theorem B5090789 : Blo 892572 5090789 := bstep (se 4 (by rfl) ⟨477261, by rfl⟩ : syracuseStep 5090789 = 954523) B954523
theorem B896543 : Blo 892572 896543 := bstep (se 1 (by rfl) ⟨672407, by rfl⟩ : syracuseStep 896543 = 1344815) B1344815
theorem B2010815 : Blo 892572 2010815 := bstep (se 1 (by rfl) ⟨1508111, by rfl⟩ : syracuseStep 2010815 = 3016223) B3016223
theorem B2011391 : Blo 892572 2011391 := bstep (se 1 (by rfl) ⟨1508543, by rfl⟩ : syracuseStep 2011391 = 3017087) B3017087
theorem B79508789 : Blo 892572 79508789 := bstep (se 5 (by rfl) ⟨3726974, by rfl⟩ : syracuseStep 79508789 = 7453949) B7453949
theorem B2012543 : Blo 892572 2012543 := bstep (se 1 (by rfl) ⟨1509407, by rfl⟩ : syracuseStep 2012543 = 3018815) B3018815
theorem B1455607 : Blo 892572 1455607 := bstep (se 1 (by rfl) ⟨1091705, by rfl⟩ : syracuseStep 1455607 = 2183411) B2183411
theorem B46380683 : Blo 892572 46380683 := bstep (se 1 (by rfl) ⟨34785512, by rfl⟩ : syracuseStep 46380683 = 69571025) B69571025
theorem B2013011 : Blo 892572 2013011 := bstep (se 1 (by rfl) ⟨1509758, by rfl⟩ : syracuseStep 2013011 = 3019517) B3019517
theorem B4536161 : Blo 892572 4536161 := bstep (se 2 (by rfl) ⟨1701060, by rfl⟩ : syracuseStep 4536161 = 3402121) B3402121
theorem B1914779 : Blo 892572 1914779 := bstep (se 1 (by rfl) ⟨1436084, by rfl⟩ : syracuseStep 1914779 = 2872169) B2872169
theorem B2013119 : Blo 892572 2013119 := bstep (se 1 (by rfl) ⟨1509839, by rfl⟩ : syracuseStep 2013119 = 3019679) B3019679
theorem B4897199 : Blo 892572 4897199 := bstep (se 1 (by rfl) ⟨3672899, by rfl⟩ : syracuseStep 4897199 = 7345799) B7345799
theorem B3816521 : Blo 892572 3816521 := bstep (se 2 (by rfl) ⟨1431195, by rfl⟩ : syracuseStep 3816521 = 2862391) B2862391
theorem B3390943 : Blo 892572 3390943 := bstep (se 1 (by rfl) ⟨2543207, by rfl⟩ : syracuseStep 3390943 = 5086415) B5086415
theorem B1293895 : Blo 892572 1293895 := bstep (se 1 (by rfl) ⟨970421, by rfl⟩ : syracuseStep 1293895 = 1940843) B1940843
theorem B1130203 : Blo 892572 1130203 := bstep (se 1 (by rfl) ⟨847652, by rfl⟩ : syracuseStep 1130203 = 1695305) B1695305
theorem B7651219 : Blo 892572 7651219 := bstep (se 1 (by rfl) ⟨5738414, by rfl⟩ : syracuseStep 7651219 = 11476829) B11476829
theorem B2015225 : Blo 892572 2015225 := bstep (se 2 (by rfl) ⟨755709, by rfl⟩ : syracuseStep 2015225 = 1511419) B1511419
theorem B2015315 : Blo 892572 2015315 := bstep (se 1 (by rfl) ⟨1511486, by rfl⟩ : syracuseStep 2015315 = 3022973) B3022973
theorem B2015369 : Blo 892572 2015369 := bstep (se 2 (by rfl) ⟨755763, by rfl⟩ : syracuseStep 2015369 = 1511527) B1511527
theorem B2146447 : Blo 892572 2146447 := bstep (se 1 (by rfl) ⟨1609835, by rfl⟩ : syracuseStep 2146447 = 3219671) B3219671
theorem B2015495 : Blo 892572 2015495 := bstep (se 1 (by rfl) ⟨1511621, by rfl⟩ : syracuseStep 2015495 = 3023243) B3023243
theorem B6799625 : Blo 892572 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B11616797 : Blo 892572 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B19383245 : Blo 892572 19383245 := bstep (se 3 (by rfl) ⟨3634358, by rfl⟩ : syracuseStep 19383245 = 7268717) B7268717
theorem B73450577 : Blo 892572 73450577 := bstep (se 2 (by rfl) ⟨27543966, by rfl⟩ : syracuseStep 73450577 = 55087933) B55087933
theorem B2016377 : Blo 892572 2016377 := bstep (se 2 (by rfl) ⟨756141, by rfl⟩ : syracuseStep 2016377 = 1512283) B1512283
theorem B2016575 : Blo 892572 2016575 := bstep (se 1 (by rfl) ⟨1512431, by rfl⟩ : syracuseStep 2016575 = 3024863) B3024863
theorem B3229577 : Blo 892572 3229577 := bstep (se 2 (by rfl) ⟨1211091, by rfl⟩ : syracuseStep 3229577 = 2422183) B2422183
theorem B6801569 : Blo 892572 6801569 := bstep (se 2 (by rfl) ⟨2550588, by rfl⟩ : syracuseStep 6801569 = 5101177) B5101177
theorem B32590127 : Blo 892572 32590127 := bstep (se 1 (by rfl) ⟨24442595, by rfl⟩ : syracuseStep 32590127 = 48885191) B48885191
theorem B9686087 : Blo 892572 9686087 := bstep (se 1 (by rfl) ⟨7264565, by rfl⟩ : syracuseStep 9686087 = 14529131) B14529131
theorem B6802541 : Blo 892572 6802541 := bstep (se 3 (by rfl) ⟨1275476, by rfl⟩ : syracuseStep 6802541 = 2550953) B2550953
theorem B3820895 : Blo 892572 3820895 := bstep (se 1 (by rfl) ⟨2865671, by rfl⟩ : syracuseStep 3820895 = 5731343) B5731343
theorem B2543663 : Blo 892572 2543663 := bstep (se 1 (by rfl) ⟨1907747, by rfl⟩ : syracuseStep 2543663 = 3815495) B3815495
theorem B4838723 : Blo 892572 4838723 := bstep (se 1 (by rfl) ⟨3629042, by rfl⟩ : syracuseStep 4838723 = 7258085) B7258085
theorem B2545145 : Blo 892572 2545145 := bstep (se 2 (by rfl) ⟨954429, by rfl⟩ : syracuseStep 2545145 = 1908859) B1908859
theorem B2152175 : Blo 892572 2152175 := bstep (se 1 (by rfl) ⟨1614131, by rfl⟩ : syracuseStep 2152175 = 3228263) B3228263
theorem B4839239 : Blo 892572 4839239 := bstep (se 1 (by rfl) ⟨3629429, by rfl⟩ : syracuseStep 4839239 = 7258859) B7258859
theorem B9197383 : Blo 892572 9197383 := bstep (se 1 (by rfl) ⟨6898037, by rfl⟩ : syracuseStep 9197383 = 13796075) B13796075
theorem B3397535 : Blo 892572 3397535 := bstep (se 1 (by rfl) ⟨2548151, by rfl⟩ : syracuseStep 3397535 = 5096303) B5096303
theorem B13948901 : Blo 892572 13948901 := bstep (se 4 (by rfl) ⟨1307709, by rfl⟩ : syracuseStep 13948901 = 2615419) B2615419
theorem B1005979 : Blo 892572 1005979 := bstep (se 1 (by rfl) ⟨754484, by rfl⟩ : syracuseStep 1005979 = 1508969) B1508969
theorem B1006375 : Blo 892572 1006375 := bstep (se 1 (by rfl) ⟨754781, by rfl⟩ : syracuseStep 1006375 = 1509563) B1509563
theorem B908095 : Blo 892572 908095 := bstep (se 1 (by rfl) ⟨681071, by rfl⟩ : syracuseStep 908095 = 1362143) B1362143
theorem B6871931 : Blo 892572 6871931 := bstep (se 1 (by rfl) ⟨5153948, by rfl⟩ : syracuseStep 6871931 = 10307897) B10307897
theorem B1006843 : Blo 892572 1006843 := bstep (se 1 (by rfl) ⟨755132, by rfl⟩ : syracuseStep 1006843 = 1510265) B1510265
theorem B2547035 : Blo 892572 2547035 := bstep (se 1 (by rfl) ⟨1910276, by rfl⟩ : syracuseStep 2547035 = 3820553) B3820553
theorem B5725703 : Blo 892572 5725703 := bstep (se 1 (by rfl) ⟨4294277, by rfl⟩ : syracuseStep 5725703 = 8588555) B8588555
theorem B9789007 : Blo 892572 9789007 := bstep (se 1 (by rfl) ⟨7341755, by rfl⟩ : syracuseStep 9789007 = 14683511) B14683511
theorem B1007599 : Blo 892572 1007599 := bstep (se 1 (by rfl) ⟨755699, by rfl⟩ : syracuseStep 1007599 = 1511399) B1511399
theorem B7626959 : Blo 892572 7626959 := bstep (se 1 (by rfl) ⟨5720219, by rfl⟩ : syracuseStep 7626959 = 11440439) B11440439
theorem B123921247 : Blo 892572 123921247 := bstep (se 1 (by rfl) ⟨92940935, by rfl⟩ : syracuseStep 123921247 = 185881871) B185881871
theorem B1074079 : Blo 892572 1074079 := bstep (se 1 (by rfl) ⟨805559, by rfl⟩ : syracuseStep 1074079 = 1611119) B1611119
theorem B5104619 : Blo 892572 5104619 := bstep (se 1 (by rfl) ⟨3828464, by rfl⟩ : syracuseStep 5104619 = 7656929) B7656929
theorem B2548847 : Blo 892572 2548847 := bstep (se 1 (by rfl) ⟨1911635, by rfl⟩ : syracuseStep 2548847 = 3823271) B3823271
theorem B2548903 : Blo 892572 2548903 := bstep (se 1 (by rfl) ⟨1911677, by rfl⟩ : syracuseStep 2548903 = 3823355) B3823355
theorem B2549303 : Blo 892572 2549303 := bstep (se 1 (by rfl) ⟨1911977, by rfl⟩ : syracuseStep 2549303 = 3823955) B3823955
theorem B5433587 : Blo 892572 5433587 := bstep (se 1 (by rfl) ⟨4075190, by rfl⟩ : syracuseStep 5433587 = 8150381) B8150381
theorem B4647223 : Blo 892572 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B1338983 : Blo 892572 1338983 := bstep (se 1 (by rfl) ⟨1004237, by rfl⟩ : syracuseStep 1338983 = 2008475) B2008475
theorem B1339367 : Blo 892572 1339367 := bstep (se 1 (by rfl) ⟨1004525, by rfl⟩ : syracuseStep 1339367 = 2009051) B2009051
theorem B1208297 : Blo 892572 1208297 := bstep (se 2 (by rfl) ⟨453111, by rfl⟩ : syracuseStep 1208297 = 906223) B906223
theorem B141586471 : Blo 892572 141586471 := bstep (se 1 (by rfl) ⟨106189853, by rfl⟩ : syracuseStep 141586471 = 212379707) B212379707
theorem B1339487 : Blo 892572 1339487 := bstep (se 1 (by rfl) ⟨1004615, by rfl⟩ : syracuseStep 1339487 = 2009231) B2009231
theorem B1339547 : Blo 892572 1339547 := bstep (se 1 (by rfl) ⟨1004660, by rfl⟩ : syracuseStep 1339547 = 2009321) B2009321
theorem B1339727 : Blo 892572 1339727 := bstep (se 1 (by rfl) ⟨1004795, by rfl⟩ : syracuseStep 1339727 = 2009591) B2009591
theorem B2552161 : Blo 892572 2552161 := bstep (se 2 (by rfl) ⟨957060, by rfl⟩ : syracuseStep 2552161 = 1914121) B1914121
theorem B43544947 : Blo 892572 43544947 := bstep (se 1 (by rfl) ⟨32658710, by rfl⟩ : syracuseStep 43544947 = 65317421) B65317421
theorem B3633547 : Blo 892572 3633547 := bstep (se 1 (by rfl) ⟨2725160, by rfl⟩ : syracuseStep 3633547 = 5450321) B5450321
theorem B2552219 : Blo 892572 2552219 := bstep (se 1 (by rfl) ⟨1914164, by rfl⟩ : syracuseStep 2552219 = 3828329) B3828329
theorem B1339817 : Blo 892572 1339817 := bstep (se 2 (by rfl) ⟨502431, by rfl⟩ : syracuseStep 1339817 = 1004863) B1004863
theorem B12874301 : Blo 892572 12874301 := bstep (se 3 (by rfl) ⟨2413931, by rfl⟩ : syracuseStep 12874301 = 4827863) B4827863
theorem B11629271 : Blo 892572 11629271 := bstep (se 1 (by rfl) ⟨8721953, by rfl⟩ : syracuseStep 11629271 = 17443907) B17443907
theorem B1340123 : Blo 892572 1340123 := bstep (se 1 (by rfl) ⟨1005092, by rfl⟩ : syracuseStep 1340123 = 2010185) B2010185
theorem B58782665 : Blo 892572 58782665 := bstep (se 2 (by rfl) ⟨22043499, by rfl⟩ : syracuseStep 58782665 = 44086999) B44086999
theorem B1700833 : Blo 892572 1700833 := bstep (se 2 (by rfl) ⟨637812, by rfl⟩ : syracuseStep 1700833 = 1275625) B1275625
theorem B1340393 : Blo 892572 1340393 := bstep (se 2 (by rfl) ⟨502647, by rfl⟩ : syracuseStep 1340393 = 1005295) B1005295
theorem B1340537 : Blo 892572 1340537 := bstep (se 2 (by rfl) ⟨502701, by rfl⟩ : syracuseStep 1340537 = 1005403) B1005403
theorem B7632083 : Blo 892572 7632083 := bstep (se 1 (by rfl) ⟨5724062, by rfl⟩ : syracuseStep 7632083 = 11448125) B11448125
theorem B1341065 : Blo 892572 1341065 := bstep (se 2 (by rfl) ⟨502899, by rfl⟩ : syracuseStep 1341065 = 1005799) B1005799
theorem B3012443 : Blo 892572 3012443 := bstep (se 1 (by rfl) ⟨2259332, by rfl⟩ : syracuseStep 3012443 = 4518665) B4518665
theorem B1341275 : Blo 892572 1341275 := bstep (se 1 (by rfl) ⟨1005956, by rfl⟩ : syracuseStep 1341275 = 2011913) B2011913
theorem B1341311 : Blo 892572 1341311 := bstep (se 1 (by rfl) ⟨1005983, by rfl⟩ : syracuseStep 1341311 = 2011967) B2011967
theorem B1341407 : Blo 892572 1341407 := bstep (se 1 (by rfl) ⟨1006055, by rfl⟩ : syracuseStep 1341407 = 2012111) B2012111
theorem B4290587 : Blo 892572 4290587 := bstep (se 1 (by rfl) ⟨3217940, by rfl⟩ : syracuseStep 4290587 = 6435881) B6435881
theorem B1341467 : Blo 892572 1341467 := bstep (se 1 (by rfl) ⟨1006100, by rfl⟩ : syracuseStep 1341467 = 2012201) B2012201
theorem B23197751 : Blo 892572 23197751 := bstep (se 1 (by rfl) ⟨17398313, by rfl⟩ : syracuseStep 23197751 = 34796627) B34796627
theorem B1702063 : Blo 892572 1702063 := bstep (se 1 (by rfl) ⟨1276547, by rfl⟩ : syracuseStep 1702063 = 2553095) B2553095
theorem B1341659 : Blo 892572 1341659 := bstep (se 1 (by rfl) ⟨1006244, by rfl⟩ : syracuseStep 1341659 = 2012489) B2012489
theorem B5503355 : Blo 892572 5503355 := bstep (se 1 (by rfl) ⟨4127516, by rfl⟩ : syracuseStep 5503355 = 8255033) B8255033
theorem B33028529 : Blo 892572 33028529 := bstep (se 2 (by rfl) ⟨12385698, by rfl⟩ : syracuseStep 33028529 = 24771397) B24771397
theorem B1341929 : Blo 892572 1341929 := bstep (se 2 (by rfl) ⟨503223, by rfl⟩ : syracuseStep 1341929 = 1006447) B1006447
theorem B5503585 : Blo 892572 5503585 := bstep (se 2 (by rfl) ⟨2063844, by rfl⟩ : syracuseStep 5503585 = 4127689) B4127689
theorem B3013307 : Blo 892572 3013307 := bstep (se 1 (by rfl) ⟨2259980, by rfl⟩ : syracuseStep 3013307 = 4519961) B4519961
theorem B19331783 : Blo 892572 19331783 := bstep (se 1 (by rfl) ⟨14498837, by rfl⟩ : syracuseStep 19331783 = 28997675) B28997675
theorem B6781643 : Blo 892572 6781643 := bstep (se 1 (by rfl) ⟨5086232, by rfl⟩ : syracuseStep 6781643 = 10172465) B10172465
theorem B1342319 : Blo 892572 1342319 := bstep (se 1 (by rfl) ⟨1006739, by rfl⟩ : syracuseStep 1342319 = 2013479) B2013479
theorem B20151173 : Blo 892572 20151173 := bstep (se 4 (by rfl) ⟨1889172, by rfl⟩ : syracuseStep 20151173 = 3778345) B3778345
theorem B1342559 : Blo 892572 1342559 := bstep (se 1 (by rfl) ⟨1006919, by rfl⟩ : syracuseStep 1342559 = 2013839) B2013839
theorem B1342619 : Blo 892572 1342619 := bstep (se 1 (by rfl) ⟨1006964, by rfl⟩ : syracuseStep 1342619 = 2013929) B2013929
theorem B1342775 : Blo 892572 1342775 := bstep (se 1 (by rfl) ⟨1007081, by rfl⟩ : syracuseStep 1342775 = 2014163) B2014163
theorem B1342955 : Blo 892572 1342955 := bstep (se 1 (by rfl) ⟨1007216, by rfl⟩ : syracuseStep 1342955 = 2014433) B2014433
theorem B1343159 : Blo 892572 1343159 := bstep (se 1 (by rfl) ⟨1007369, by rfl⟩ : syracuseStep 1343159 = 2014739) B2014739
theorem B1343369 : Blo 892572 1343369 := bstep (se 2 (by rfl) ⟨503763, by rfl⟩ : syracuseStep 1343369 = 1007527) B1007527
theorem B1343543 : Blo 892572 1343543 := bstep (se 1 (by rfl) ⟨1007657, by rfl⟩ : syracuseStep 1343543 = 2015315) B2015315
theorem B1343579 : Blo 892572 1343579 := bstep (se 1 (by rfl) ⟨1007684, by rfl⟩ : syracuseStep 1343579 = 2015369) B2015369
theorem B6783101 : Blo 892572 6783101 := bstep (se 3 (by rfl) ⟨1271831, by rfl⟩ : syracuseStep 6783101 = 2543663) B2543663
theorem B1343663 : Blo 892572 1343663 := bstep (se 1 (by rfl) ⟨1007747, by rfl⟩ : syracuseStep 1343663 = 2015495) B2015495
theorem B1507511 : Blo 892572 1507511 := bstep (se 1 (by rfl) ⟨1130633, by rfl⟩ : syracuseStep 1507511 = 2261267) B2261267
theorem B1344251 : Blo 892572 1344251 := bstep (se 1 (by rfl) ⟨1008188, by rfl⟩ : syracuseStep 1344251 = 2016377) B2016377
theorem B1573663 : Blo 892572 1573663 := bstep (se 1 (by rfl) ⟨1180247, by rfl⟩ : syracuseStep 1573663 = 2360495) B2360495
theorem B1344383 : Blo 892572 1344383 := bstep (se 1 (by rfl) ⟨1008287, by rfl⟩ : syracuseStep 1344383 = 2016575) B2016575
theorem B3016169 : Blo 892572 3016169 := bstep (se 2 (by rfl) ⟨1131063, by rfl⟩ : syracuseStep 3016169 = 2262127) B2262127
theorem B21726751 : Blo 892572 21726751 := bstep (se 1 (by rfl) ⟨16295063, by rfl⟩ : syracuseStep 21726751 = 32590127) B32590127
theorem B3016439 : Blo 892572 3016439 := bstep (se 1 (by rfl) ⟨2262329, by rfl⟩ : syracuseStep 3016439 = 4524659) B4524659
theorem B6457391 : Blo 892572 6457391 := bstep (se 1 (by rfl) ⟨4843043, by rfl⟩ : syracuseStep 6457391 = 9686087) B9686087
theorem B3017033 : Blo 892572 3017033 := bstep (se 2 (by rfl) ⟨1131387, by rfl⟩ : syracuseStep 3017033 = 2262775) B2262775
theorem B3017195 : Blo 892572 3017195 := bstep (se 1 (by rfl) ⟨2262896, by rfl⟩ : syracuseStep 3017195 = 4525793) B4525793
theorem B1510123 : Blo 892572 1510123 := bstep (se 1 (by rfl) ⟨1132592, by rfl⟩ : syracuseStep 1510123 = 2265185) B2265185
theorem B3017519 : Blo 892572 3017519 := bstep (se 1 (by rfl) ⟨2263139, by rfl⟩ : syracuseStep 3017519 = 4526279) B4526279
theorem B17173417 : Blo 892572 17173417 := bstep (se 2 (by rfl) ⟨6440031, by rfl⟩ : syracuseStep 17173417 = 12880063) B12880063
theorem B1510663 : Blo 892572 1510663 := bstep (se 1 (by rfl) ⟨1132997, by rfl⟩ : syracuseStep 1510663 = 2265995) B2265995
theorem B1511095 : Blo 892572 1511095 := bstep (se 1 (by rfl) ⟨1133321, by rfl⟩ : syracuseStep 1511095 = 2266643) B2266643
theorem B3018491 : Blo 892572 3018491 := bstep (se 1 (by rfl) ⟨2263868, by rfl⟩ : syracuseStep 3018491 = 4527737) B4527737
theorem B2265023 : Blo 892572 2265023 := bstep (se 1 (by rfl) ⟨1698767, by rfl⟩ : syracuseStep 2265023 = 3397535) B3397535
theorem B5739133 : Blo 892572 5739133 := bstep (se 3 (by rfl) ⟨1076087, by rfl⟩ : syracuseStep 5739133 = 2152175) B2152175
theorem B23270075 : Blo 892572 23270075 := bstep (se 1 (by rfl) ⟨17452556, by rfl⟩ : syracuseStep 23270075 = 34905113) B34905113
theorem B8590171 : Blo 892572 8590171 := bstep (se 1 (by rfl) ⟨6442628, by rfl⟩ : syracuseStep 8590171 = 12885257) B12885257
theorem B3020057 : Blo 892572 3020057 := bstep (se 2 (by rfl) ⟨1132521, by rfl⟩ : syracuseStep 3020057 = 2265043) B2265043
theorem B3020111 : Blo 892572 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B188781961 : Blo 892572 188781961 := bstep (se 2 (by rfl) ⟨70793235, by rfl⟩ : syracuseStep 188781961 = 141586471) B141586471
theorem B5084639 : Blo 892572 5084639 := bstep (se 1 (by rfl) ⟨3813479, by rfl⟩ : syracuseStep 5084639 = 7626959) B7626959
theorem B15735215 : Blo 892572 15735215 := bstep (se 1 (by rfl) ⟨11801411, by rfl⟩ : syracuseStep 15735215 = 23602823) B23602823
theorem B30284225 : Blo 892572 30284225 := bstep (se 2 (by rfl) ⟨11356584, by rfl⟩ : syracuseStep 30284225 = 22713169) B22713169
theorem B2267777 : Blo 892572 2267777 := bstep (se 2 (by rfl) ⟨850416, by rfl⟩ : syracuseStep 2267777 = 1700833) B1700833
theorem B3218287 : Blo 892572 3218287 := bstep (se 1 (by rfl) ⟨2413715, by rfl⟩ : syracuseStep 3218287 = 4827431) B4827431
theorem B1940809 : Blo 892572 1940809 := bstep (se 2 (by rfl) ⟨727803, by rfl⟩ : syracuseStep 1940809 = 1455607) B1455607
theorem B3022163 : Blo 892572 3022163 := bstep (se 1 (by rfl) ⟨2266622, by rfl⟩ : syracuseStep 3022163 = 4533245) B4533245
theorem B892655 : Blo 892572 892655 := bstep (se 1 (by rfl) ⟨669491, by rfl⟩ : syracuseStep 892655 = 1338983) B1338983
theorem B12263177 : Blo 892572 12263177 := bstep (se 2 (by rfl) ⟨4598691, by rfl⟩ : syracuseStep 12263177 = 9197383) B9197383
theorem B892911 : Blo 892572 892911 := bstep (se 1 (by rfl) ⟨669683, by rfl⟩ : syracuseStep 892911 = 1339367) B1339367
theorem B892991 : Blo 892572 892991 := bstep (se 1 (by rfl) ⟨669743, by rfl⟩ : syracuseStep 892991 = 1339487) B1339487
theorem B893031 : Blo 892572 893031 := bstep (se 1 (by rfl) ⟨669773, by rfl⟩ : syracuseStep 893031 = 1339547) B1339547
theorem B893151 : Blo 892572 893151 := bstep (se 1 (by rfl) ⟨669863, by rfl⟩ : syracuseStep 893151 = 1339727) B1339727
theorem B2269417 : Blo 892572 2269417 := bstep (se 2 (by rfl) ⟨851031, by rfl⟩ : syracuseStep 2269417 = 1702063) B1702063
theorem B893211 : Blo 892572 893211 := bstep (se 1 (by rfl) ⟨669908, by rfl⟩ : syracuseStep 893211 = 1339817) B1339817
theorem B893415 : Blo 892572 893415 := bstep (se 1 (by rfl) ⟨670061, by rfl⟩ : syracuseStep 893415 = 1340123) B1340123
theorem B893595 : Blo 892572 893595 := bstep (se 1 (by rfl) ⟨670196, by rfl⟩ : syracuseStep 893595 = 1340393) B1340393
theorem B893691 : Blo 892572 893691 := bstep (se 1 (by rfl) ⟨670268, by rfl⟩ : syracuseStep 893691 = 1340537) B1340537
theorem B5088055 : Blo 892572 5088055 := bstep (se 1 (by rfl) ⟨3816041, by rfl⟩ : syracuseStep 5088055 = 7632083) B7632083
theorem B3023945 : Blo 892572 3023945 := bstep (se 2 (by rfl) ⟨1133979, by rfl⟩ : syracuseStep 3023945 = 2267959) B2267959
theorem B894043 : Blo 892572 894043 := bstep (se 1 (by rfl) ⟨670532, by rfl⟩ : syracuseStep 894043 = 1341065) B1341065
theorem B2008295 : Blo 892572 2008295 := bstep (se 1 (by rfl) ⟨1506221, by rfl⟩ : syracuseStep 2008295 = 3012443) B3012443
theorem B894183 : Blo 892572 894183 := bstep (se 1 (by rfl) ⟨670637, by rfl⟩ : syracuseStep 894183 = 1341275) B1341275
theorem B3024107 : Blo 892572 3024107 := bstep (se 1 (by rfl) ⟨2268080, by rfl⟩ : syracuseStep 3024107 = 4536161) B4536161
theorem B894207 : Blo 892572 894207 := bstep (se 1 (by rfl) ⟨670655, by rfl⟩ : syracuseStep 894207 = 1341311) B1341311
theorem B894271 : Blo 892572 894271 := bstep (se 1 (by rfl) ⟨670703, by rfl⟩ : syracuseStep 894271 = 1341407) B1341407
theorem B2860391 : Blo 892572 2860391 := bstep (se 1 (by rfl) ⟨2145293, by rfl⟩ : syracuseStep 2860391 = 4290587) B4290587
theorem B894311 : Blo 892572 894311 := bstep (se 1 (by rfl) ⟨670733, by rfl⟩ : syracuseStep 894311 = 1341467) B1341467
theorem B894439 : Blo 892572 894439 := bstep (se 1 (by rfl) ⟨670829, by rfl⟩ : syracuseStep 894439 = 1341659) B1341659
theorem B894619 : Blo 892572 894619 := bstep (se 1 (by rfl) ⟨670964, by rfl⟩ : syracuseStep 894619 = 1341929) B1341929
theorem B2008871 : Blo 892572 2008871 := bstep (se 1 (by rfl) ⟨1506653, by rfl⟩ : syracuseStep 2008871 = 3013307) B3013307
theorem B12887855 : Blo 892572 12887855 := bstep (se 1 (by rfl) ⟨9665891, by rfl⟩ : syracuseStep 12887855 = 19331783) B19331783
theorem B894879 : Blo 892572 894879 := bstep (se 1 (by rfl) ⟨671159, by rfl⟩ : syracuseStep 894879 = 1342319) B1342319
theorem B895039 : Blo 892572 895039 := bstep (se 1 (by rfl) ⟨671279, by rfl⟩ : syracuseStep 895039 = 1342559) B1342559
theorem B895079 : Blo 892572 895079 := bstep (se 1 (by rfl) ⟨671309, by rfl⟩ : syracuseStep 895079 = 1342619) B1342619
theorem B13052009 : Blo 892572 13052009 := bstep (se 2 (by rfl) ⟨4894503, by rfl⟩ : syracuseStep 13052009 = 9789007) B9789007
theorem B895183 : Blo 892572 895183 := bstep (se 1 (by rfl) ⟨671387, by rfl⟩ : syracuseStep 895183 = 1342775) B1342775
theorem B895303 : Blo 892572 895303 := bstep (se 1 (by rfl) ⟨671477, by rfl⟩ : syracuseStep 895303 = 1342955) B1342955
theorem B895439 : Blo 892572 895439 := bstep (se 1 (by rfl) ⟨671579, by rfl⟩ : syracuseStep 895439 = 1343159) B1343159
theorem B10201625 : Blo 892572 10201625 := bstep (se 2 (by rfl) ⟨3825609, by rfl⟩ : syracuseStep 10201625 = 7651219) B7651219
theorem B895579 : Blo 892572 895579 := bstep (se 1 (by rfl) ⟨671684, by rfl⟩ : syracuseStep 895579 = 1343369) B1343369
theorem B3222125 : Blo 892572 3222125 := bstep (se 3 (by rfl) ⟨604148, by rfl⟩ : syracuseStep 3222125 = 1208297) B1208297
theorem B895743 : Blo 892572 895743 := bstep (se 1 (by rfl) ⟨671807, by rfl⟩ : syracuseStep 895743 = 1343615) B1343615
theorem B4533083 : Blo 892572 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B2861929 : Blo 892572 2861929 := bstep (se 2 (by rfl) ⟨1073223, by rfl⟩ : syracuseStep 2861929 = 2146447) B2146447
theorem B895935 : Blo 892572 895935 := bstep (se 1 (by rfl) ⟨671951, by rfl⟩ : syracuseStep 895935 = 1343903) B1343903
theorem B896111 : Blo 892572 896111 := bstep (se 1 (by rfl) ⟨672083, by rfl⟩ : syracuseStep 896111 = 1344167) B1344167
theorem B896191 : Blo 892572 896191 := bstep (se 1 (by rfl) ⟨672143, by rfl⟩ : syracuseStep 896191 = 1344287) B1344287
theorem B896207 : Blo 892572 896207 := bstep (se 1 (by rfl) ⟨672155, by rfl⟩ : syracuseStep 896207 = 1344311) B1344311
theorem B12922163 : Blo 892572 12922163 := bstep (se 1 (by rfl) ⟨9691622, by rfl⟩ : syracuseStep 12922163 = 19383245) B19383245
theorem B896327 : Blo 892572 896327 := bstep (se 1 (by rfl) ⟨672245, by rfl⟩ : syracuseStep 896327 = 1344491) B1344491
theorem B48967051 : Blo 892572 48967051 := bstep (se 1 (by rfl) ⟨36725288, by rfl⟩ : syracuseStep 48967051 = 73450577) B73450577
theorem B165228329 : Blo 892572 165228329 := bstep (se 2 (by rfl) ⟨61960623, by rfl⟩ : syracuseStep 165228329 = 123921247) B123921247
theorem B30978125 : Blo 892572 30978125 := bstep (se 3 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 30978125 = 11616797) B11616797
theorem B4534379 : Blo 892572 4534379 := bstep (se 1 (by rfl) ⟨3400784, by rfl⟩ : syracuseStep 4534379 = 6801569) B6801569
theorem B24785189 : Blo 892572 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B4535027 : Blo 892572 4535027 := bstep (se 1 (by rfl) ⟨3401270, by rfl⟩ : syracuseStep 4535027 = 6802541) B6802541
theorem B2011931 : Blo 892572 2011931 := bstep (se 1 (by rfl) ⟨1508948, by rfl⟩ : syracuseStep 2011931 = 3017897) B3017897
theorem B2012129 : Blo 892572 2012129 := bstep (se 2 (by rfl) ⟨754548, by rfl⟩ : syracuseStep 2012129 = 1509097) B1509097
theorem B27571553 : Blo 892572 27571553 := bstep (se 2 (by rfl) ⟨10339332, by rfl⟩ : syracuseStep 27571553 = 20678665) B20678665
theorem B12891545 : Blo 892572 12891545 := bstep (se 2 (by rfl) ⟨4834329, by rfl⟩ : syracuseStep 12891545 = 9668659) B9668659
theorem B6437009 : Blo 892572 6437009 := bstep (se 2 (by rfl) ⟨2413878, by rfl⟩ : syracuseStep 6437009 = 4827757) B4827757
theorem B3225815 : Blo 892572 3225815 := bstep (se 1 (by rfl) ⟨2419361, by rfl⟩ : syracuseStep 3225815 = 4838723) B4838723
theorem B3062303 : Blo 892572 3062303 := bstep (se 1 (by rfl) ⟨2296727, by rfl⟩ : syracuseStep 3062303 = 4593455) B4593455
theorem B3226159 : Blo 892572 3226159 := bstep (se 1 (by rfl) ⟨2419619, by rfl⟩ : syracuseStep 3226159 = 4839239) B4839239
theorem B10205999 : Blo 892572 10205999 := bstep (se 1 (by rfl) ⟨7654499, by rfl⟩ : syracuseStep 10205999 = 15308999) B15308999
theorem B6798167 : Blo 892572 6798167 := bstep (se 1 (by rfl) ⟨5098625, by rfl⟩ : syracuseStep 6798167 = 10197251) B10197251
theorem B2014235 : Blo 892572 2014235 := bstep (se 1 (by rfl) ⟨1510676, by rfl⟩ : syracuseStep 2014235 = 3021353) B3021353
theorem B123681821 : Blo 892572 123681821 := bstep (se 3 (by rfl) ⟨23190341, by rfl⟩ : syracuseStep 123681821 = 46380683) B46380683
theorem B352304309 : Blo 892572 352304309 := bstep (se 5 (by rfl) ⟨16514264, by rfl⟩ : syracuseStep 352304309 = 33028529) B33028529
theorem B2014505 : Blo 892572 2014505 := bstep (se 2 (by rfl) ⟨755439, by rfl⟩ : syracuseStep 2014505 = 1510879) B1510879
theorem B5094845 : Blo 892572 5094845 := bstep (se 3 (by rfl) ⟨955283, by rfl⟩ : syracuseStep 5094845 = 1910567) B1910567
theorem B3817135 : Blo 892572 3817135 := bstep (se 1 (by rfl) ⟨2862851, by rfl⟩ : syracuseStep 3817135 = 5725703) B5725703
theorem B3391703 : Blo 892572 3391703 := bstep (se 1 (by rfl) ⟨2543777, by rfl⟩ : syracuseStep 3391703 = 5087555) B5087555
theorem B2867567 : Blo 892572 2867567 := bstep (se 1 (by rfl) ⟨2150675, by rfl⟩ : syracuseStep 2867567 = 4301351) B4301351
theorem B13747117 : Blo 892572 13747117 := bstep (se 3 (by rfl) ⟨2577584, by rfl⟩ : syracuseStep 13747117 = 5155169) B5155169
theorem B3392887 : Blo 892572 3392887 := bstep (se 1 (by rfl) ⟨2544665, by rfl⟩ : syracuseStep 3392887 = 5089331) B5089331
theorem B3622391 : Blo 892572 3622391 := bstep (se 1 (by rfl) ⟨2716793, by rfl⟩ : syracuseStep 3622391 = 5433587) B5433587
theorem B2017043 : Blo 892572 2017043 := bstep (se 1 (by rfl) ⟨1512782, by rfl⟩ : syracuseStep 2017043 = 3025565) B3025565
theorem B3393859 : Blo 892572 3393859 := bstep (se 1 (by rfl) ⟨2545394, by rfl⟩ : syracuseStep 3393859 = 5090789) B5090789
theorem B2542013 : Blo 892572 2542013 := bstep (se 3 (by rfl) ⟨476627, by rfl⟩ : syracuseStep 2542013 = 953255) B953255
theorem B7752847 : Blo 892572 7752847 := bstep (se 1 (by rfl) ⟨5814635, by rfl⟩ : syracuseStep 7752847 = 11629271) B11629271
theorem B53005859 : Blo 892572 53005859 := bstep (se 1 (by rfl) ⟨39754394, by rfl⟩ : syracuseStep 53005859 = 79508789) B79508789
theorem B3264799 : Blo 892572 3264799 := bstep (se 1 (by rfl) ⟨2448599, by rfl⟩ : syracuseStep 3264799 = 4897199) B4897199
theorem B5820761 : Blo 892572 5820761 := bstep (se 2 (by rfl) ⟨2182785, by rfl⟩ : syracuseStep 5820761 = 4365571) B4365571
theorem B2544347 : Blo 892572 2544347 := bstep (se 1 (by rfl) ⟨1908260, by rfl⟩ : syracuseStep 2544347 = 3816521) B3816521
theorem B1725193 : Blo 892572 1725193 := bstep (se 2 (by rfl) ⟨646947, by rfl⟩ : syracuseStep 1725193 = 1293895) B1293895
theorem B1005439 : Blo 892572 1005439 := bstep (se 1 (by rfl) ⟨754079, by rfl⟩ : syracuseStep 1005439 = 1508159) B1508159
theorem B2153051 : Blo 892572 2153051 := bstep (se 1 (by rfl) ⟨1614788, by rfl⟩ : syracuseStep 2153051 = 3229577) B3229577
theorem B3398537 : Blo 892572 3398537 := bstep (se 2 (by rfl) ⟨1274451, by rfl⟩ : syracuseStep 3398537 = 2548903) B2548903
theorem B2547263 : Blo 892572 2547263 := bstep (se 1 (by rfl) ⟨1910447, by rfl⟩ : syracuseStep 2547263 = 3820895) B3820895
theorem B1007743 : Blo 892572 1007743 := bstep (se 1 (by rfl) ⟨755807, by rfl⟩ : syracuseStep 1007743 = 1511615) B1511615
theorem B1696763 : Blo 892572 1696763 := bstep (se 1 (by rfl) ⟨1272572, by rfl⟩ : syracuseStep 1696763 = 2545145) B2545145
theorem B13788251 : Blo 892572 13788251 := bstep (se 1 (by rfl) ⟨10341188, by rfl⟩ : syracuseStep 13788251 = 20682377) B20682377
theorem B9299267 : Blo 892572 9299267 := bstep (se 1 (by rfl) ⟨6974450, by rfl⟩ : syracuseStep 9299267 = 13948901) B13948901
theorem B3827371 : Blo 892572 3827371 := bstep (se 1 (by rfl) ⟨2870528, by rfl⟩ : syracuseStep 3827371 = 5741057) B5741057
theorem B4581287 : Blo 892572 4581287 := bstep (se 1 (by rfl) ⟨3435965, by rfl⟩ : syracuseStep 4581287 = 6871931) B6871931
theorem B5728421 : Blo 892572 5728421 := bstep (se 4 (by rfl) ⟨537039, by rfl⟩ : syracuseStep 5728421 = 1074079) B1074079
theorem B1698023 : Blo 892572 1698023 := bstep (se 1 (by rfl) ⟨1273517, by rfl⟩ : syracuseStep 1698023 = 2547035) B2547035
theorem B5106077 : Blo 892572 5106077 := bstep (se 3 (by rfl) ⟨957389, by rfl⟩ : syracuseStep 5106077 = 1914779) B1914779
theorem B8612315 : Blo 892572 8612315 := bstep (se 1 (by rfl) ⟨6459236, by rfl⟩ : syracuseStep 8612315 = 12918473) B12918473
theorem B3402881 : Blo 892572 3402881 := bstep (se 2 (by rfl) ⟨1276080, by rfl⟩ : syracuseStep 3402881 = 2552161) B2552161
theorem B58059929 : Blo 892572 58059929 := bstep (se 2 (by rfl) ⟨21772473, by rfl⟩ : syracuseStep 58059929 = 43544947) B43544947
theorem B4844729 : Blo 892572 4844729 := bstep (se 2 (by rfl) ⟨1816773, by rfl⟩ : syracuseStep 4844729 = 3633547) B3633547
theorem B3403079 : Blo 892572 3403079 := bstep (se 1 (by rfl) ⟨2552309, by rfl⟩ : syracuseStep 3403079 = 5104619) B5104619
theorem B1207679 : Blo 892572 1207679 := bstep (se 1 (by rfl) ⟨905759, by rfl⟩ : syracuseStep 1207679 = 1811519) B1811519
theorem B1699231 : Blo 892572 1699231 := bstep (se 1 (by rfl) ⟨1274423, by rfl⟩ : syracuseStep 1699231 = 2548847) B2548847
theorem B1338911 : Blo 892572 1338911 := bstep (se 1 (by rfl) ⟨1004183, by rfl⟩ : syracuseStep 1338911 = 2008367) B2008367
theorem B1699535 : Blo 892572 1699535 := bstep (se 1 (by rfl) ⟨1274651, by rfl⟩ : syracuseStep 1699535 = 2549303) B2549303
theorem B7238423 : Blo 892572 7238423 := bstep (se 1 (by rfl) ⟨5428817, by rfl⟩ : syracuseStep 7238423 = 10857635) B10857635
theorem B1340543 : Blo 892572 1340543 := bstep (se 1 (by rfl) ⟨1005407, by rfl⟩ : syracuseStep 1340543 = 2010815) B2010815
theorem B1340927 : Blo 892572 1340927 := bstep (se 1 (by rfl) ⟨1005695, by rfl⟩ : syracuseStep 1340927 = 2011391) B2011391
theorem B1701479 : Blo 892572 1701479 := bstep (se 1 (by rfl) ⟨1276109, by rfl⟩ : syracuseStep 1701479 = 2552219) B2552219
theorem B8582867 : Blo 892572 8582867 := bstep (se 1 (by rfl) ⟨6437150, by rfl⟩ : syracuseStep 8582867 = 12874301) B12874301
theorem B1341305 : Blo 892572 1341305 := bstep (se 2 (by rfl) ⟨502989, by rfl⟩ : syracuseStep 1341305 = 1005979) B1005979
theorem B39188443 : Blo 892572 39188443 := bstep (se 1 (by rfl) ⟨29391332, by rfl⟩ : syracuseStep 39188443 = 58782665) B58782665
theorem B7338113 : Blo 892572 7338113 := bstep (se 2 (by rfl) ⟨2751792, by rfl⟩ : syracuseStep 7338113 = 5503585) B5503585
theorem B1341695 : Blo 892572 1341695 := bstep (se 1 (by rfl) ⟨1006271, by rfl⟩ : syracuseStep 1341695 = 2012543) B2012543
theorem B1341833 : Blo 892572 1341833 := bstep (se 2 (by rfl) ⟨503187, by rfl⟩ : syracuseStep 1341833 = 1006375) B1006375
theorem B1210793 : Blo 892572 1210793 := bstep (se 2 (by rfl) ⟨454047, by rfl⟩ : syracuseStep 1210793 = 908095) B908095
theorem B1342007 : Blo 892572 1342007 := bstep (se 1 (by rfl) ⟨1006505, by rfl⟩ : syracuseStep 1342007 = 2013011) B2013011
theorem B1342079 : Blo 892572 1342079 := bstep (se 1 (by rfl) ⟨1006559, by rfl⟩ : syracuseStep 1342079 = 2013119) B2013119
theorem B15465167 : Blo 892572 15465167 := bstep (se 1 (by rfl) ⟨11598875, by rfl⟩ : syracuseStep 15465167 = 23197751) B23197751
theorem B3668903 : Blo 892572 3668903 := bstep (se 1 (by rfl) ⟨2751677, by rfl⟩ : syracuseStep 3668903 = 5503355) B5503355
theorem B1342457 : Blo 892572 1342457 := bstep (se 2 (by rfl) ⟨503421, by rfl⟩ : syracuseStep 1342457 = 1006843) B1006843
theorem B4521095 : Blo 892572 4521095 := bstep (se 1 (by rfl) ⟨3390821, by rfl⟩ : syracuseStep 4521095 = 6781643) B6781643
theorem B13434115 : Blo 892572 13434115 := bstep (se 1 (by rfl) ⟨10075586, by rfl⟩ : syracuseStep 13434115 = 20151173) B20151173
theorem B4521257 : Blo 892572 4521257 := bstep (se 2 (by rfl) ⟨1695471, by rfl⟩ : syracuseStep 4521257 = 3390943) B3390943
theorem B1506937 : Blo 892572 1506937 := bstep (se 2 (by rfl) ⟨565101, by rfl⟩ : syracuseStep 1506937 = 1130203) B1130203
theorem B13074281 : Blo 892572 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B4292473 : Blo 892572 4292473 := bstep (se 2 (by rfl) ⟨1609677, by rfl⟩ : syracuseStep 4292473 = 3219355) B3219355
theorem B1343465 : Blo 892572 1343465 := bstep (se 2 (by rfl) ⟨503799, by rfl⟩ : syracuseStep 1343465 = 1007599) B1007599
theorem B1343483 : Blo 892572 1343483 := bstep (se 1 (by rfl) ⟨1007612, by rfl⟩ : syracuseStep 1343483 = 2015225) B2015225
theorem B4522067 : Blo 892572 4522067 := bstep (se 1 (by rfl) ⟨3391550, by rfl⟩ : syracuseStep 4522067 = 6783101) B6783101
theorem B2261135 : Blo 892572 2261135 := bstep (se 1 (by rfl) ⟨1695851, by rfl⟩ : syracuseStep 2261135 = 3391703) B3391703
theorem B1343657 : Blo 892572 1343657 := bstep (se 2 (by rfl) ⟨503871, by rfl⟩ : syracuseStep 1343657 = 1007743) B1007743
theorem B2098217 : Blo 892572 2098217 := bstep (se 2 (by rfl) ⟨786831, by rfl⟩ : syracuseStep 2098217 = 1573663) B1573663
theorem B6784073 : Blo 892572 6784073 := bstep (se 2 (by rfl) ⟨2544027, by rfl⟩ : syracuseStep 6784073 = 5088055) B5088055
theorem B1344695 : Blo 892572 1344695 := bstep (se 1 (by rfl) ⟨1008521, by rfl⟩ : syracuseStep 1344695 = 2017043) B2017043
theorem B4523849 : Blo 892572 4523849 := bstep (se 2 (by rfl) ⟨1696443, by rfl⟩ : syracuseStep 4523849 = 3392887) B3392887
theorem B28969001 : Blo 892572 28969001 := bstep (se 2 (by rfl) ⟨10863375, by rfl⟩ : syracuseStep 28969001 = 21726751) B21726751
theorem B19302461 : Blo 892572 19302461 := bstep (se 3 (by rfl) ⟨3619211, by rfl⟩ : syracuseStep 19302461 = 7238423) B7238423
theorem B1510015 : Blo 892572 1510015 := bstep (se 1 (by rfl) ⟨1132511, by rfl⟩ : syracuseStep 1510015 = 2265023) B2265023
theorem B4525145 : Blo 892572 4525145 := bstep (se 2 (by rfl) ⟨1696929, by rfl⟩ : syracuseStep 4525145 = 3393859) B3393859
theorem B12881909 : Blo 892572 12881909 := bstep (se 5 (by rfl) ⟨603839, by rfl⟩ : syracuseStep 12881909 = 1207679) B1207679
theorem B10490143 : Blo 892572 10490143 := bstep (se 1 (by rfl) ⟨7867607, by rfl⟩ : syracuseStep 10490143 = 15735215) B15735215
theorem B20189483 : Blo 892572 20189483 := bstep (se 1 (by rfl) ⟨15142112, by rfl⟩ : syracuseStep 20189483 = 30284225) B30284225
theorem B1511851 : Blo 892572 1511851 := bstep (se 1 (by rfl) ⟨1133888, by rfl⟩ : syracuseStep 1511851 = 2267777) B2267777
theorem B12915125 : Blo 892572 12915125 := bstep (se 5 (by rfl) ⟨605396, by rfl⟩ : syracuseStep 12915125 = 1210793) B1210793
theorem B2265641 : Blo 892572 2265641 := bstep (se 2 (by rfl) ⟨849615, by rfl⟩ : syracuseStep 2265641 = 1699231) B1699231
theorem B2265691 : Blo 892572 2265691 := bstep (se 1 (by rfl) ⟨1699268, by rfl⟩ : syracuseStep 2265691 = 3398537) B3398537
theorem B286594453 : Blo 892572 286594453 := bstep (se 6 (by rfl) ⟨6717057, by rfl⟩ : syracuseStep 286594453 = 13434115) B13434115
theorem B4528061 : Blo 892572 4528061 := bstep (se 3 (by rfl) ⟨849011, by rfl⟩ : syracuseStep 4528061 = 1698023) B1698023
theorem B6199511 : Blo 892572 6199511 := bstep (se 1 (by rfl) ⟨4649633, by rfl⟩ : syracuseStep 6199511 = 9299267) B9299267
theorem B2300257 : Blo 892572 2300257 := bstep (se 2 (by rfl) ⟨862596, by rfl⟩ : syracuseStep 2300257 = 1725193) B1725193
theorem B8591903 : Blo 892572 8591903 := bstep (se 1 (by rfl) ⟨6443927, by rfl⟩ : syracuseStep 8591903 = 12887855) B12887855
theorem B3054191 : Blo 892572 3054191 := bstep (se 1 (by rfl) ⟨2290643, by rfl⟩ : syracuseStep 3054191 = 4581287) B4581287
theorem B5741543 : Blo 892572 5741543 := bstep (se 1 (by rfl) ⟨4306157, by rfl⟩ : syracuseStep 5741543 = 8612315) B8612315
theorem B3022055 : Blo 892572 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B2268587 : Blo 892572 2268587 := bstep (se 1 (by rfl) ⟨1701440, by rfl⟩ : syracuseStep 2268587 = 3402881) B3402881
theorem B38706619 : Blo 892572 38706619 := bstep (se 1 (by rfl) ⟨29029964, by rfl⟩ : syracuseStep 38706619 = 58059929) B58059929
theorem B2268719 : Blo 892572 2268719 := bstep (se 1 (by rfl) ⟨1701539, by rfl⟩ : syracuseStep 2268719 = 3403079) B3403079
theorem B892607 : Blo 892572 892607 := bstep (se 1 (by rfl) ⟨669455, by rfl⟩ : syracuseStep 892607 = 1338911) B1338911
theorem B20652083 : Blo 892572 20652083 := bstep (se 1 (by rfl) ⟨15489062, by rfl⟩ : syracuseStep 20652083 = 30978125) B30978125
theorem B3022919 : Blo 892572 3022919 := bstep (se 1 (by rfl) ⟨2267189, by rfl⟩ : syracuseStep 3022919 = 4534379) B4534379
theorem B329818189 : Blo 892572 329818189 := bstep (se 3 (by rfl) ⟨61840910, by rfl⟩ : syracuseStep 329818189 = 123681821) B123681821
theorem B16523459 : Blo 892572 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B12919277 : Blo 892572 12919277 := bstep (se 3 (by rfl) ⟨2422364, by rfl⟩ : syracuseStep 12919277 = 4844729) B4844729
theorem B3023351 : Blo 892572 3023351 := bstep (se 1 (by rfl) ⟨2267513, by rfl⟩ : syracuseStep 3023351 = 4535027) B4535027
theorem B4301545 : Blo 892572 4301545 := bstep (se 2 (by rfl) ⟨1613079, by rfl⟩ : syracuseStep 4301545 = 3226159) B3226159
theorem B893695 : Blo 892572 893695 := bstep (se 1 (by rfl) ⟨670271, by rfl⟩ : syracuseStep 893695 = 1340543) B1340543
theorem B8594363 : Blo 892572 8594363 := bstep (se 1 (by rfl) ⟨6445772, by rfl⟩ : syracuseStep 8594363 = 12891545) B12891545
theorem B893951 : Blo 892572 893951 := bstep (se 1 (by rfl) ⟨670463, by rfl⟩ : syracuseStep 893951 = 1340927) B1340927
theorem B894203 : Blo 892572 894203 := bstep (se 1 (by rfl) ⟨670652, by rfl⟩ : syracuseStep 894203 = 1341305) B1341305
theorem B4892075 : Blo 892572 4892075 := bstep (se 1 (by rfl) ⟨3669056, by rfl⟩ : syracuseStep 4892075 = 7338113) B7338113
theorem B894463 : Blo 892572 894463 := bstep (se 1 (by rfl) ⟨670847, by rfl⟩ : syracuseStep 894463 = 1341695) B1341695
theorem B894555 : Blo 892572 894555 := bstep (se 1 (by rfl) ⟨670916, by rfl⟩ : syracuseStep 894555 = 1341833) B1341833
theorem B2041535 : Blo 892572 2041535 := bstep (se 1 (by rfl) ⟨1531151, by rfl⟩ : syracuseStep 2041535 = 3062303) B3062303
theorem B894671 : Blo 892572 894671 := bstep (se 1 (by rfl) ⟨671003, by rfl⟩ : syracuseStep 894671 = 1342007) B1342007
theorem B894719 : Blo 892572 894719 := bstep (se 1 (by rfl) ⟨671039, by rfl⟩ : syracuseStep 894719 = 1342079) B1342079
theorem B4532111 : Blo 892572 4532111 := bstep (se 1 (by rfl) ⟨3399083, by rfl⟩ : syracuseStep 4532111 = 6798167) B6798167
theorem B894971 : Blo 892572 894971 := bstep (se 1 (by rfl) ⟨671228, by rfl⟩ : syracuseStep 894971 = 1342457) B1342457
theorem B2009249 : Blo 892572 2009249 := bstep (se 2 (by rfl) ⟨753468, by rfl⟩ : syracuseStep 2009249 = 1506937) B1506937
theorem B5089513 : Blo 892572 5089513 := bstep (se 2 (by rfl) ⟨1908567, by rfl⟩ : syracuseStep 5089513 = 3817135) B3817135
theorem B895643 : Blo 892572 895643 := bstep (se 1 (by rfl) ⟨671732, by rfl⟩ : syracuseStep 895643 = 1343465) B1343465
theorem B895655 : Blo 892572 895655 := bstep (se 1 (by rfl) ⟨671741, by rfl⟩ : syracuseStep 895655 = 1343483) B1343483
theorem B895695 : Blo 892572 895695 := bstep (se 1 (by rfl) ⟨671771, by rfl⟩ : syracuseStep 895695 = 1343543) B1343543
theorem B895719 : Blo 892572 895719 := bstep (se 1 (by rfl) ⟨671789, by rfl⟩ : syracuseStep 895719 = 1343579) B1343579
theorem B895775 : Blo 892572 895775 := bstep (se 1 (by rfl) ⟨671831, by rfl⟩ : syracuseStep 895775 = 1343663) B1343663
theorem B3025889 : Blo 892572 3025889 := bstep (se 2 (by rfl) ⟨1134708, by rfl⟩ : syracuseStep 3025889 = 2269417) B2269417
theorem B896167 : Blo 892572 896167 := bstep (se 1 (by rfl) ⟨672125, by rfl⟩ : syracuseStep 896167 = 1344251) B1344251
theorem B896255 : Blo 892572 896255 := bstep (se 1 (by rfl) ⟨672191, by rfl⟩ : syracuseStep 896255 = 1344383) B1344383
theorem B7646845 : Blo 892572 7646845 := bstep (se 3 (by rfl) ⟨1433783, by rfl⟩ : syracuseStep 7646845 = 2867567) B2867567
theorem B2010779 : Blo 892572 2010779 := bstep (se 1 (by rfl) ⟨1508084, by rfl⟩ : syracuseStep 2010779 = 3016169) B3016169
theorem B2010959 : Blo 892572 2010959 := bstep (se 1 (by rfl) ⟨1508219, by rfl⟩ : syracuseStep 2010959 = 3016439) B3016439
theorem B18329489 : Blo 892572 18329489 := bstep (se 2 (by rfl) ⟨6873558, by rfl⟩ : syracuseStep 18329489 = 13747117) B13747117
theorem B4304927 : Blo 892572 4304927 := bstep (se 1 (by rfl) ⟨3228695, by rfl⟩ : syracuseStep 4304927 = 6457391) B6457391
theorem B2011355 : Blo 892572 2011355 := bstep (se 1 (by rfl) ⟨1508516, by rfl⟩ : syracuseStep 2011355 = 3017033) B3017033
theorem B2011463 : Blo 892572 2011463 := bstep (se 1 (by rfl) ⟨1508597, by rfl⟩ : syracuseStep 2011463 = 3017195) B3017195
theorem B2011679 : Blo 892572 2011679 := bstep (se 1 (by rfl) ⟨1508759, by rfl⟩ : syracuseStep 2011679 = 3017519) B3017519
theorem B35337239 : Blo 892572 35337239 := bstep (se 1 (by rfl) ⟨26502929, by rfl⟩ : syracuseStep 35337239 = 53005859) B53005859
theorem B2012327 : Blo 892572 2012327 := bstep (se 1 (by rfl) ⟨1509245, by rfl⟩ : syracuseStep 2012327 = 3018491) B3018491
theorem B3880507 : Blo 892572 3880507 := bstep (se 1 (by rfl) ⟨2910380, by rfl⟩ : syracuseStep 3880507 = 5820761) B5820761
theorem B15513383 : Blo 892572 15513383 := bstep (se 1 (by rfl) ⟨11635037, by rfl⟩ : syracuseStep 15513383 = 23270075) B23270075
theorem B2013371 : Blo 892572 2013371 := bstep (se 1 (by rfl) ⟨1510028, by rfl⟩ : syracuseStep 2013371 = 3020057) B3020057
theorem B2013407 : Blo 892572 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B2013497 : Blo 892572 2013497 := bstep (se 2 (by rfl) ⟨755061, by rfl⟩ : syracuseStep 2013497 = 1510123) B1510123
theorem B3389759 : Blo 892572 3389759 := bstep (se 1 (by rfl) ⟨2542319, by rfl⟩ : syracuseStep 3389759 = 5084639) B5084639
theorem B3815905 : Blo 892572 3815905 := bstep (se 2 (by rfl) ⟨1430964, by rfl⟩ : syracuseStep 3815905 = 2861929) B2861929
theorem B10337129 : Blo 892572 10337129 := bstep (se 2 (by rfl) ⟨3876423, by rfl⟩ : syracuseStep 10337129 = 7752847) B7752847
theorem B2014217 : Blo 892572 2014217 := bstep (se 2 (by rfl) ⟨755331, by rfl⟩ : syracuseStep 2014217 = 1510663) B1510663
theorem B65289401 : Blo 892572 65289401 := bstep (se 2 (by rfl) ⟨24483525, by rfl⟩ : syracuseStep 65289401 = 48967051) B48967051
theorem B2014775 : Blo 892572 2014775 := bstep (se 1 (by rfl) ⟨1511081, by rfl⟩ : syracuseStep 2014775 = 3022163) B3022163
theorem B2014793 : Blo 892572 2014793 := bstep (se 2 (by rfl) ⟨755547, by rfl⟩ : syracuseStep 2014793 = 1511095) B1511095
theorem B8175451 : Blo 892572 8175451 := bstep (se 1 (by rfl) ⟨6131588, by rfl⟩ : syracuseStep 8175451 = 12263177) B12263177
theorem B1131175 : Blo 892572 1131175 := bstep (se 1 (by rfl) ⟨848381, by rfl⟩ : syracuseStep 1131175 = 1696763) B1696763
theorem B2015963 : Blo 892572 2015963 := bstep (se 1 (by rfl) ⟨1511972, by rfl⟩ : syracuseStep 2015963 = 3023945) B3023945
theorem B9192167 : Blo 892572 9192167 := bstep (se 1 (by rfl) ⟨6894125, by rfl⟩ : syracuseStep 9192167 = 13788251) B13788251
theorem B2016071 : Blo 892572 2016071 := bstep (se 1 (by rfl) ⟨1512053, by rfl⟩ : syracuseStep 2016071 = 3024107) B3024107
theorem B7652177 : Blo 892572 7652177 := bstep (se 2 (by rfl) ⟨2869566, by rfl⟩ : syracuseStep 7652177 = 5739133) B5739133
theorem B11453561 : Blo 892572 11453561 := bstep (se 2 (by rfl) ⟨4295085, by rfl⟩ : syracuseStep 11453561 = 8590171) B8590171
theorem B8701339 : Blo 892572 8701339 := bstep (se 1 (by rfl) ⟨6526004, by rfl⟩ : syracuseStep 8701339 = 13052009) B13052009
theorem B3818947 : Blo 892572 3818947 := bstep (se 1 (by rfl) ⟨2864210, by rfl⟩ : syracuseStep 3818947 = 5728421) B5728421
theorem B6801083 : Blo 892572 6801083 := bstep (se 1 (by rfl) ⟨5100812, by rfl⟩ : syracuseStep 6801083 = 10201625) B10201625
theorem B2148083 : Blo 892572 2148083 := bstep (se 1 (by rfl) ⟨1611062, by rfl⟩ : syracuseStep 2148083 = 3222125) B3222125
theorem B251709281 : Blo 892572 251709281 := bstep (se 2 (by rfl) ⟨94390980, by rfl⟩ : syracuseStep 251709281 = 188781961) B188781961
theorem B1133023 : Blo 892572 1133023 := bstep (se 1 (by rfl) ⟨849767, by rfl⟩ : syracuseStep 1133023 = 1699535) B1699535
theorem B110152219 : Blo 892572 110152219 := bstep (se 1 (by rfl) ⟨82614164, by rfl⟩ : syracuseStep 110152219 = 165228329) B165228329
theorem B52251257 : Blo 892572 52251257 := bstep (se 2 (by rfl) ⟨19594221, by rfl⟩ : syracuseStep 52251257 = 39188443) B39188443
theorem B1134319 : Blo 892572 1134319 := bstep (se 1 (by rfl) ⟨850739, by rfl⟩ : syracuseStep 1134319 = 1701479) B1701479
theorem B5721911 : Blo 892572 5721911 := bstep (se 1 (by rfl) ⟨4291433, by rfl⟩ : syracuseStep 5721911 = 8582867) B8582867
theorem B2150543 : Blo 892572 2150543 := bstep (se 1 (by rfl) ⟨1612907, by rfl⟩ : syracuseStep 2150543 = 3225815) B3225815
theorem B10310111 : Blo 892572 10310111 := bstep (se 1 (by rfl) ⟨7732583, by rfl⟩ : syracuseStep 10310111 = 15465167) B15465167
theorem B6803999 : Blo 892572 6803999 := bstep (se 1 (by rfl) ⟨5102999, by rfl⟩ : syracuseStep 6803999 = 10205999) B10205999
theorem B2445935 : Blo 892572 2445935 := bstep (se 1 (by rfl) ⟨1834451, by rfl⟩ : syracuseStep 2445935 = 3668903) B3668903
theorem B234869539 : Blo 892572 234869539 := bstep (se 1 (by rfl) ⟨176152154, by rfl⟩ : syracuseStep 234869539 = 352304309) B352304309
theorem B3396563 : Blo 892572 3396563 := bstep (se 1 (by rfl) ⟨2547422, by rfl⟩ : syracuseStep 3396563 = 5094845) B5094845
theorem B5723297 : Blo 892572 5723297 := bstep (se 2 (by rfl) ⟨2146236, by rfl⟩ : syracuseStep 5723297 = 4292473) B4292473
theorem B1005007 : Blo 892572 1005007 := bstep (se 1 (by rfl) ⟨753755, by rfl⟩ : syracuseStep 1005007 = 1507511) B1507511
theorem B2414927 : Blo 892572 2414927 := bstep (se 1 (by rfl) ⟨1811195, by rfl⟩ : syracuseStep 2414927 = 3622391) B3622391
theorem B1694675 : Blo 892572 1694675 := bstep (se 1 (by rfl) ⟨1271006, by rfl⟩ : syracuseStep 1694675 = 2542013) B2542013
theorem B5103161 : Blo 892572 5103161 := bstep (se 2 (by rfl) ⟨1913685, by rfl⟩ : syracuseStep 5103161 = 3827371) B3827371
theorem B1696231 : Blo 892572 1696231 := bstep (se 1 (by rfl) ⟨1272173, by rfl⟩ : syracuseStep 1696231 = 2544347) B2544347
theorem B7627709 : Blo 892572 7627709 := bstep (se 3 (by rfl) ⟨1430195, by rfl⟩ : syracuseStep 7627709 = 2860391) B2860391
theorem B22897889 : Blo 892572 22897889 := bstep (se 2 (by rfl) ⟨8586708, by rfl⟩ : syracuseStep 22897889 = 17173417) B17173417
theorem B1435367 : Blo 892572 1435367 := bstep (se 1 (by rfl) ⟨1076525, by rfl⟩ : syracuseStep 1435367 = 2153051) B2153051
theorem B1698175 : Blo 892572 1698175 := bstep (se 1 (by rfl) ⟨1273631, by rfl⟩ : syracuseStep 1698175 = 2547263) B2547263
theorem B4353065 : Blo 892572 4353065 := bstep (se 2 (by rfl) ⟨1632399, by rfl⟩ : syracuseStep 4353065 = 3264799) B3264799
theorem B1338863 : Blo 892572 1338863 := bstep (se 1 (by rfl) ⟨1004147, by rfl⟩ : syracuseStep 1338863 = 2008295) B2008295
theorem B1339247 : Blo 892572 1339247 := bstep (se 1 (by rfl) ⟨1004435, by rfl⟩ : syracuseStep 1339247 = 2008871) B2008871
theorem B3404051 : Blo 892572 3404051 := bstep (se 1 (by rfl) ⟨2553038, by rfl⟩ : syracuseStep 3404051 = 5106077) B5106077
theorem B8614775 : Blo 892572 8614775 := bstep (se 1 (by rfl) ⟨6461081, by rfl⟩ : syracuseStep 8614775 = 12922163) B12922163
theorem B1340585 : Blo 892572 1340585 := bstep (se 2 (by rfl) ⟨502719, by rfl⟩ : syracuseStep 1340585 = 1005439) B1005439
theorem B1341287 : Blo 892572 1341287 := bstep (se 1 (by rfl) ⟨1005965, by rfl⟩ : syracuseStep 1341287 = 2011931) B2011931
theorem B1341419 : Blo 892572 1341419 := bstep (se 1 (by rfl) ⟨1006064, by rfl⟩ : syracuseStep 1341419 = 2012129) B2012129
theorem B18381035 : Blo 892572 18381035 := bstep (se 1 (by rfl) ⟨13785776, by rfl⟩ : syracuseStep 18381035 = 27571553) B27571553
theorem B4291049 : Blo 892572 4291049 := bstep (se 2 (by rfl) ⟨1609143, by rfl⟩ : syracuseStep 4291049 = 3218287) B3218287
theorem B4291339 : Blo 892572 4291339 := bstep (se 1 (by rfl) ⟨3218504, by rfl⟩ : syracuseStep 4291339 = 6437009) B6437009
theorem B2587745 : Blo 892572 2587745 := bstep (se 2 (by rfl) ⟨970404, by rfl⟩ : syracuseStep 2587745 = 1940809) B1940809
theorem B1342823 : Blo 892572 1342823 := bstep (se 1 (by rfl) ⟨1007117, by rfl⟩ : syracuseStep 1342823 = 2014235) B2014235
theorem B3014063 : Blo 892572 3014063 := bstep (se 1 (by rfl) ⟨2260547, by rfl⟩ : syracuseStep 3014063 = 4521095) B4521095
theorem B3014171 : Blo 892572 3014171 := bstep (se 1 (by rfl) ⟨2260628, by rfl⟩ : syracuseStep 3014171 = 4521257) B4521257
theorem B1343003 : Blo 892572 1343003 := bstep (se 1 (by rfl) ⟨1007252, by rfl⟩ : syracuseStep 1343003 = 2014505) B2014505
theorem B8716187 : Blo 892572 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B3014711 : Blo 892572 3014711 := bstep (se 1 (by rfl) ⟨2261033, by rfl⟩ : syracuseStep 3014711 = 4522067) B4522067
theorem B1507423 : Blo 892572 1507423 := bstep (se 1 (by rfl) ⟨1130567, by rfl⟩ : syracuseStep 1507423 = 2261135) B2261135
theorem B1343975 : Blo 892572 1343975 := bstep (se 1 (by rfl) ⟨1007981, by rfl⟩ : syracuseStep 1343975 = 2015963) B2015963
theorem B6128111 : Blo 892572 6128111 := bstep (se 1 (by rfl) ⟨4596083, by rfl⟩ : syracuseStep 6128111 = 9192167) B9192167
theorem B1344047 : Blo 892572 1344047 := bstep (se 1 (by rfl) ⟨1008035, by rfl⟩ : syracuseStep 1344047 = 2016071) B2016071
theorem B2261641 : Blo 892572 2261641 := bstep (se 2 (by rfl) ⟨848115, by rfl⟩ : syracuseStep 2261641 = 1696231) B1696231
theorem B4522715 : Blo 892572 4522715 := bstep (se 1 (by rfl) ⟨3392036, by rfl⟩ : syracuseStep 4522715 = 6784073) B6784073
theorem B7635707 : Blo 892572 7635707 := bstep (se 1 (by rfl) ⟨5726780, by rfl⟩ : syracuseStep 7635707 = 11453561) B11453561
theorem B1508233 : Blo 892572 1508233 := bstep (se 2 (by rfl) ⟨565587, by rfl⟩ : syracuseStep 1508233 = 1131175) B1131175
theorem B5735393 : Blo 892572 5735393 := bstep (se 2 (by rfl) ⟨2150772, by rfl⟩ : syracuseStep 5735393 = 4301545) B4301545
theorem B3015899 : Blo 892572 3015899 := bstep (se 1 (by rfl) ⟨2261924, by rfl⟩ : syracuseStep 3015899 = 4523849) B4523849
theorem B167806187 : Blo 892572 167806187 := bstep (se 1 (by rfl) ⟨125854640, by rfl⟩ : syracuseStep 167806187 = 251709281) B251709281
theorem B6522493 : Blo 892572 6522493 := bstep (se 3 (by rfl) ⟨1222967, by rfl⟩ : syracuseStep 6522493 = 2445935) B2445935
theorem B34834171 : Blo 892572 34834171 := bstep (se 1 (by rfl) ⟨26125628, by rfl⟩ : syracuseStep 34834171 = 52251257) B52251257
theorem B11601785 : Blo 892572 11601785 := bstep (se 2 (by rfl) ⟨4350669, by rfl⟩ : syracuseStep 11601785 = 8701339) B8701339
theorem B3016763 : Blo 892572 3016763 := bstep (se 1 (by rfl) ⟨2262572, by rfl⟩ : syracuseStep 3016763 = 4525145) B4525145
theorem B8587939 : Blo 892572 8587939 := bstep (se 1 (by rfl) ⟨6440954, by rfl⟩ : syracuseStep 8587939 = 12881909) B12881909
theorem B6786017 : Blo 892572 6786017 := bstep (se 2 (by rfl) ⟨2544756, by rfl⟩ : syracuseStep 6786017 = 5089513) B5089513
theorem B1510427 : Blo 892572 1510427 := bstep (se 1 (by rfl) ⟨1132820, by rfl⟩ : syracuseStep 1510427 = 2265641) B2265641
theorem B2264233 : Blo 892572 2264233 := bstep (se 2 (by rfl) ⟨849087, by rfl⟩ : syracuseStep 2264233 = 1698175) B1698175
theorem B1510697 : Blo 892572 1510697 := bstep (se 2 (by rfl) ⟨566511, by rfl⟩ : syracuseStep 1510697 = 1133023) B1133023
theorem B2264375 : Blo 892572 2264375 := bstep (se 1 (by rfl) ⟨1698281, by rfl⟩ : syracuseStep 2264375 = 3396563) B3396563
theorem B146869625 : Blo 892572 146869625 := bstep (se 2 (by rfl) ⟨55076109, by rfl⟩ : syracuseStep 146869625 = 110152219) B110152219
theorem B3018707 : Blo 892572 3018707 := bstep (se 1 (by rfl) ⟨2264030, by rfl⟩ : syracuseStep 3018707 = 4528061) B4528061
theorem B1609951 : Blo 892572 1609951 := bstep (se 1 (by rfl) ⟨1207463, by rfl⟩ : syracuseStep 1609951 = 2414927) B2414927
theorem B5444093 : Blo 892572 5444093 := bstep (se 3 (by rfl) ⟨1020767, by rfl⟩ : syracuseStep 5444093 = 2041535) B2041535
theorem B10195793 : Blo 892572 10195793 := bstep (se 2 (by rfl) ⟨3823422, by rfl⟩ : syracuseStep 10195793 = 7646845) B7646845
theorem B1512391 : Blo 892572 1512391 := bstep (se 1 (by rfl) ⟨1134293, by rfl⟩ : syracuseStep 1512391 = 2268587) B2268587
theorem B1512425 : Blo 892572 1512425 := bstep (se 2 (by rfl) ⟨567159, by rfl⟩ : syracuseStep 1512425 = 1134319) B1134319
theorem B1512479 : Blo 892572 1512479 := bstep (se 1 (by rfl) ⟨1134359, by rfl⟩ : syracuseStep 1512479 = 2268719) B2268719
theorem B13768055 : Blo 892572 13768055 := bstep (se 1 (by rfl) ⟨10326041, by rfl⟩ : syracuseStep 13768055 = 20652083) B20652083
theorem B11015639 : Blo 892572 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B5085139 : Blo 892572 5085139 := bstep (se 1 (by rfl) ⟨3813854, by rfl⟩ : syracuseStep 5085139 = 7627709) B7627709
theorem B3020921 : Blo 892572 3020921 := bstep (se 2 (by rfl) ⟨1132845, by rfl⟩ : syracuseStep 3020921 = 2265691) B2265691
theorem B3021407 : Blo 892572 3021407 := bstep (se 1 (by rfl) ⟨2266055, by rfl⟩ : syracuseStep 3021407 = 4532111) B4532111
theorem B892575 : Blo 892572 892575 := bstep (se 1 (by rfl) ⟨669431, by rfl⟩ : syracuseStep 892575 = 1338863) B1338863
theorem B892831 : Blo 892572 892831 := bstep (se 1 (by rfl) ⟨669623, by rfl⟩ : syracuseStep 892831 = 1339247) B1339247
theorem B2269367 : Blo 892572 2269367 := bstep (se 1 (by rfl) ⟨1702025, by rfl⟩ : syracuseStep 2269367 = 3404051) B3404051
theorem B5743183 : Blo 892572 5743183 := bstep (se 1 (by rfl) ⟨4307387, by rfl⟩ : syracuseStep 5743183 = 8614775) B8614775
theorem B5087873 : Blo 892572 5087873 := bstep (se 2 (by rfl) ⟨1907952, by rfl⟩ : syracuseStep 5087873 = 3815905) B3815905
theorem B893723 : Blo 892572 893723 := bstep (se 1 (by rfl) ⟨670292, by rfl⟩ : syracuseStep 893723 = 1340585) B1340585
theorem B894191 : Blo 892572 894191 := bstep (se 1 (by rfl) ⟨670643, by rfl⟩ : syracuseStep 894191 = 1341287) B1341287
theorem B894279 : Blo 892572 894279 := bstep (se 1 (by rfl) ⟨670709, by rfl⟩ : syracuseStep 894279 = 1341419) B1341419
theorem B2860699 : Blo 892572 2860699 := bstep (se 1 (by rfl) ⟨2145524, by rfl⟩ : syracuseStep 2860699 = 4291049) B4291049
theorem B6891419 : Blo 892572 6891419 := bstep (se 1 (by rfl) ⟨5168564, by rfl⟩ : syracuseStep 6891419 = 10337129) B10337129
theorem B43526267 : Blo 892572 43526267 := bstep (se 1 (by rfl) ⟨32644700, by rfl⟩ : syracuseStep 43526267 = 65289401) B65289401
theorem B895215 : Blo 892572 895215 := bstep (se 1 (by rfl) ⟨671411, by rfl⟩ : syracuseStep 895215 = 1342823) B1342823
theorem B2009375 : Blo 892572 2009375 := bstep (se 1 (by rfl) ⟨1507031, by rfl⟩ : syracuseStep 2009375 = 3014063) B3014063
theorem B2009447 : Blo 892572 2009447 := bstep (se 1 (by rfl) ⟨1507085, by rfl⟩ : syracuseStep 2009447 = 3014171) B3014171
theorem B895335 : Blo 892572 895335 := bstep (se 1 (by rfl) ⟨671501, by rfl⟩ : syracuseStep 895335 = 1343003) B1343003
theorem B5810791 : Blo 892572 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B11479805 : Blo 892572 11479805 := bstep (se 3 (by rfl) ⟨2152463, by rfl⟩ : syracuseStep 11479805 = 4304927) B4304927
theorem B439757585 : Blo 892572 439757585 := bstep (se 2 (by rfl) ⟨164909094, by rfl⟩ : syracuseStep 439757585 = 329818189) B329818189
theorem B895771 : Blo 892572 895771 := bstep (se 1 (by rfl) ⟨671828, by rfl⟩ : syracuseStep 895771 = 1343657) B1343657
theorem B896463 : Blo 892572 896463 := bstep (se 1 (by rfl) ⟨672347, by rfl⟩ : syracuseStep 896463 = 1344695) B1344695
theorem B4534055 : Blo 892572 4534055 := bstep (se 1 (by rfl) ⟨3400541, by rfl⟩ : syracuseStep 4534055 = 6801083) B6801083
theorem B19312667 : Blo 892572 19312667 := bstep (se 1 (by rfl) ⟨14484500, by rfl⟩ : syracuseStep 19312667 = 28969001) B28969001
theorem B12268037 : Blo 892572 12268037 := bstep (se 4 (by rfl) ⟨1150128, by rfl⟩ : syracuseStep 12268037 = 2300257) B2300257
theorem B5091929 : Blo 892572 5091929 := bstep (se 2 (by rfl) ⟨1909473, by rfl⟩ : syracuseStep 5091929 = 3818947) B3818947
theorem B3814607 : Blo 892572 3814607 := bstep (se 1 (by rfl) ⟨2860955, by rfl⟩ : syracuseStep 3814607 = 5721911) B5721911
theorem B4535999 : Blo 892572 4535999 := bstep (se 1 (by rfl) ⟨3401999, by rfl⟩ : syracuseStep 4535999 = 6803999) B6803999
theorem B3815531 : Blo 892572 3815531 := bstep (se 1 (by rfl) ⟨2861648, by rfl⟩ : syracuseStep 3815531 = 5723297) B5723297
theorem B2013353 : Blo 892572 2013353 := bstep (se 2 (by rfl) ⟨755007, by rfl⟩ : syracuseStep 2013353 = 1510015) B1510015
theorem B1129783 : Blo 892572 1129783 := bstep (se 1 (by rfl) ⟨847337, by rfl⟩ : syracuseStep 1129783 = 1694675) B1694675
theorem B2014703 : Blo 892572 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B2015279 : Blo 892572 2015279 := bstep (se 1 (by rfl) ⟨1511459, by rfl⟩ : syracuseStep 2015279 = 3022919) B3022919
theorem B2015567 : Blo 892572 2015567 := bstep (se 1 (by rfl) ⟨1511675, by rfl⟩ : syracuseStep 2015567 = 3023351) B3023351
theorem B2015801 : Blo 892572 2015801 := bstep (se 2 (by rfl) ⟨755925, by rfl⟩ : syracuseStep 2015801 = 1511851) B1511851
theorem B16532029 : Blo 892572 16532029 := bstep (se 3 (by rfl) ⟨3099755, by rfl⟩ : syracuseStep 16532029 = 6199511) B6199511
theorem B3261383 : Blo 892572 3261383 := bstep (se 1 (by rfl) ⟨2446037, by rfl⟩ : syracuseStep 3261383 = 4892075) B4892075
theorem B8144509 : Blo 892572 8144509 := bstep (se 3 (by rfl) ⟨1527095, by rfl⟩ : syracuseStep 8144509 = 3054191) B3054191
theorem B382125937 : Blo 892572 382125937 := bstep (se 2 (by rfl) ⟨143297226, by rfl⟩ : syracuseStep 382125937 = 286594453) B286594453
theorem B2017259 : Blo 892572 2017259 := bstep (se 1 (by rfl) ⟨1512944, by rfl⟩ : syracuseStep 2017259 = 3025889) B3025889
theorem B2902043 : Blo 892572 2902043 := bstep (se 1 (by rfl) ⟨2176532, by rfl⟩ : syracuseStep 2902043 = 4353065) B4353065
theorem B6900653 : Blo 892572 6900653 := bstep (se 3 (by rfl) ⟨1293872, by rfl⟩ : syracuseStep 6900653 = 2587745) B2587745
theorem B5721785 : Blo 892572 5721785 := bstep (se 2 (by rfl) ⟨2145669, by rfl⟩ : syracuseStep 5721785 = 4291339) B4291339
theorem B10342255 : Blo 892572 10342255 := bstep (se 1 (by rfl) ⟨7756691, by rfl⟩ : syracuseStep 10342255 = 15513383) B15513383
theorem B10900601 : Blo 892572 10900601 := bstep (se 2 (by rfl) ⟨4087725, by rfl⟩ : syracuseStep 10900601 = 8175451) B8175451
theorem B5101451 : Blo 892572 5101451 := bstep (se 1 (by rfl) ⟨3826088, by rfl⟩ : syracuseStep 5101451 = 7652177) B7652177
theorem B1398811 : Blo 892572 1398811 := bstep (se 1 (by rfl) ⟨1049108, by rfl⟩ : syracuseStep 1398811 = 2098217) B2098217
theorem B1432055 : Blo 892572 1432055 := bstep (se 1 (by rfl) ⟨1074041, by rfl⟩ : syracuseStep 1432055 = 2148083) B2148083
theorem B12868307 : Blo 892572 12868307 := bstep (se 1 (by rfl) ⟨9651230, by rfl⟩ : syracuseStep 12868307 = 19302461) B19302461
theorem B1433695 : Blo 892572 1433695 := bstep (se 1 (by rfl) ⟨1075271, by rfl⟩ : syracuseStep 1433695 = 2150543) B2150543
theorem B13459655 : Blo 892572 13459655 := bstep (se 1 (by rfl) ⟨10094741, by rfl⟩ : syracuseStep 13459655 = 20189483) B20189483
theorem B8610083 : Blo 892572 8610083 := bstep (se 1 (by rfl) ⟨6457562, by rfl⟩ : syracuseStep 8610083 = 12915125) B12915125
theorem B6873407 : Blo 892572 6873407 := bstep (se 1 (by rfl) ⟨5155055, by rfl⟩ : syracuseStep 6873407 = 10310111) B10310111
theorem B5727935 : Blo 892572 5727935 := bstep (se 1 (by rfl) ⟨4295951, by rfl⟩ : syracuseStep 5727935 = 8591903) B8591903
theorem B3827645 : Blo 892572 3827645 := bstep (se 3 (by rfl) ⟨717683, by rfl⟩ : syracuseStep 3827645 = 1435367) B1435367
theorem B3827695 : Blo 892572 3827695 := bstep (se 1 (by rfl) ⟨2870771, by rfl⟩ : syracuseStep 3827695 = 5741543) B5741543
theorem B3402107 : Blo 892572 3402107 := bstep (se 1 (by rfl) ⟨2551580, by rfl⟩ : syracuseStep 3402107 = 5103161) B5103161
theorem B8612851 : Blo 892572 8612851 := bstep (se 1 (by rfl) ⟨6459638, by rfl⟩ : syracuseStep 8612851 = 12919277) B12919277
theorem B13986857 : Blo 892572 13986857 := bstep (se 2 (by rfl) ⟨5245071, by rfl⟩ : syracuseStep 13986857 = 10490143) B10490143
theorem B5729575 : Blo 892572 5729575 := bstep (se 1 (by rfl) ⟨4297181, by rfl⟩ : syracuseStep 5729575 = 8594363) B8594363
theorem B15265259 : Blo 892572 15265259 := bstep (se 1 (by rfl) ⟨11448944, by rfl⟩ : syracuseStep 15265259 = 22897889) B22897889
theorem B313159385 : Blo 892572 313159385 := bstep (se 2 (by rfl) ⟨117434769, by rfl⟩ : syracuseStep 313159385 = 234869539) B234869539
theorem B1339499 : Blo 892572 1339499 := bstep (se 1 (by rfl) ⟨1004624, by rfl⟩ : syracuseStep 1339499 = 2009249) B2009249
theorem B1340009 : Blo 892572 1340009 := bstep (se 2 (by rfl) ⟨502503, by rfl⟩ : syracuseStep 1340009 = 1005007) B1005007
theorem B5174009 : Blo 892572 5174009 := bstep (se 2 (by rfl) ⟨1940253, by rfl⟩ : syracuseStep 5174009 = 3880507) B3880507
theorem B1340519 : Blo 892572 1340519 := bstep (se 1 (by rfl) ⟨1005389, by rfl⟩ : syracuseStep 1340519 = 2010779) B2010779
theorem B1340639 : Blo 892572 1340639 := bstep (se 1 (by rfl) ⟨1005479, by rfl⟩ : syracuseStep 1340639 = 2010959) B2010959
theorem B12219659 : Blo 892572 12219659 := bstep (se 1 (by rfl) ⟨9164744, by rfl⟩ : syracuseStep 12219659 = 18329489) B18329489
theorem B1340903 : Blo 892572 1340903 := bstep (se 1 (by rfl) ⟨1005677, by rfl⟩ : syracuseStep 1340903 = 2011355) B2011355
theorem B1340975 : Blo 892572 1340975 := bstep (se 1 (by rfl) ⟨1005731, by rfl⟩ : syracuseStep 1340975 = 2011463) B2011463
theorem B1341119 : Blo 892572 1341119 := bstep (se 1 (by rfl) ⟨1005839, by rfl⟩ : syracuseStep 1341119 = 2011679) B2011679
theorem B23558159 : Blo 892572 23558159 := bstep (se 1 (by rfl) ⟨17668619, by rfl⟩ : syracuseStep 23558159 = 35337239) B35337239
theorem B1341551 : Blo 892572 1341551 := bstep (se 1 (by rfl) ⟨1006163, by rfl⟩ : syracuseStep 1341551 = 2012327) B2012327
theorem B1342247 : Blo 892572 1342247 := bstep (se 1 (by rfl) ⟨1006685, by rfl⟩ : syracuseStep 1342247 = 2013371) B2013371
theorem B1342271 : Blo 892572 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B12254023 : Blo 892572 12254023 := bstep (se 1 (by rfl) ⟨9190517, by rfl⟩ : syracuseStep 12254023 = 18381035) B18381035
theorem B1342331 : Blo 892572 1342331 := bstep (se 1 (by rfl) ⟨1006748, by rfl⟩ : syracuseStep 1342331 = 2013497) B2013497
theorem B2259839 : Blo 892572 2259839 := bstep (se 1 (by rfl) ⟨1694879, by rfl⟩ : syracuseStep 2259839 = 3389759) B3389759
theorem B51608825 : Blo 892572 51608825 := bstep (se 2 (by rfl) ⟨19353309, by rfl⟩ : syracuseStep 51608825 = 38706619) B38706619
theorem B1342811 : Blo 892572 1342811 := bstep (se 1 (by rfl) ⟨1007108, by rfl⟩ : syracuseStep 1342811 = 2014217) B2014217
theorem B1343183 : Blo 892572 1343183 := bstep (se 1 (by rfl) ⟨1007387, by rfl⟩ : syracuseStep 1343183 = 2014775) B2014775
theorem B1343195 : Blo 892572 1343195 := bstep (se 1 (by rfl) ⟨1007396, by rfl⟩ : syracuseStep 1343195 = 2014793) B2014793
theorem B1343519 : Blo 892572 1343519 := bstep (se 1 (by rfl) ⟨1007639, by rfl⟩ : syracuseStep 1343519 = 2015279) B2015279
theorem B1343711 : Blo 892572 1343711 := bstep (se 1 (by rfl) ⟨1007783, by rfl⟩ : syracuseStep 1343711 = 2015567) B2015567
theorem B1343867 : Blo 892572 1343867 := bstep (se 1 (by rfl) ⟨1007900, by rfl⟩ : syracuseStep 1343867 = 2015801) B2015801
theorem B3015143 : Blo 892572 3015143 := bstep (se 1 (by rfl) ⟨2261357, by rfl⟩ : syracuseStep 3015143 = 4522715) B4522715
theorem B111870791 : Blo 892572 111870791 := bstep (se 1 (by rfl) ⟨83903093, by rfl⟩ : syracuseStep 111870791 = 167806187) B167806187
theorem B3015521 : Blo 892572 3015521 := bstep (se 2 (by rfl) ⟨1130820, by rfl⟩ : syracuseStep 3015521 = 2261641) B2261641
theorem B7734523 : Blo 892572 7734523 := bstep (se 1 (by rfl) ⟨5800892, by rfl⟩ : syracuseStep 7734523 = 11601785) B11601785
theorem B1344839 : Blo 892572 1344839 := bstep (se 1 (by rfl) ⟨1008629, by rfl⟩ : syracuseStep 1344839 = 2017259) B2017259
theorem B1934695 : Blo 892572 1934695 := bstep (se 1 (by rfl) ⟨1451021, by rfl⟩ : syracuseStep 1934695 = 2902043) B2902043
theorem B4524011 : Blo 892572 4524011 := bstep (se 1 (by rfl) ⟨3393008, by rfl⟩ : syracuseStep 4524011 = 6786017) B6786017
theorem B1509583 : Blo 892572 1509583 := bstep (se 1 (by rfl) ⟨1132187, by rfl⟩ : syracuseStep 1509583 = 2264375) B2264375
theorem B97913083 : Blo 892572 97913083 := bstep (se 1 (by rfl) ⟨73434812, by rfl⟩ : syracuseStep 97913083 = 146869625) B146869625
theorem B9178703 : Blo 892572 9178703 := bstep (se 1 (by rfl) ⟨6884027, by rfl⟩ : syracuseStep 9178703 = 13768055) B13768055
theorem B7343759 : Blo 892572 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B3018977 : Blo 892572 3018977 := bstep (se 2 (by rfl) ⟨1132116, by rfl⟩ : syracuseStep 3018977 = 2264233) B2264233
theorem B954703 : Blo 892572 954703 := bstep (se 1 (by rfl) ⟨716027, by rfl⟩ : syracuseStep 954703 = 1432055) B1432055
theorem B7639433 : Blo 892572 7639433 := bstep (se 2 (by rfl) ⟨2864787, by rfl⟩ : syracuseStep 7639433 = 5729575) B5729575
theorem B62821757 : Blo 892572 62821757 := bstep (se 3 (by rfl) ⟨11779079, by rfl⟩ : syracuseStep 62821757 = 23558159) B23558159
theorem B1512911 : Blo 892572 1512911 := bstep (se 1 (by rfl) ⟨1134683, by rfl⟩ : syracuseStep 1512911 = 2269367) B2269367
theorem B5740055 : Blo 892572 5740055 := bstep (se 1 (by rfl) ⟨4305041, by rfl⟩ : syracuseStep 5740055 = 8610083) B8610083
theorem B4594279 : Blo 892572 4594279 := bstep (se 1 (by rfl) ⟨3445709, by rfl⟩ : syracuseStep 4594279 = 6891419) B6891419
theorem B2268071 : Blo 892572 2268071 := bstep (se 1 (by rfl) ⟨1701053, by rfl⟩ : syracuseStep 2268071 = 3402107) B3402107
theorem B208772923 : Blo 892572 208772923 := bstep (se 1 (by rfl) ⟨156579692, by rfl⟩ : syracuseStep 208772923 = 313159385) B313159385
theorem B3022703 : Blo 892572 3022703 := bstep (se 1 (by rfl) ⟨2267027, by rfl⟩ : syracuseStep 3022703 = 4534055) B4534055
theorem B892999 : Blo 892572 892999 := bstep (se 1 (by rfl) ⟨669749, by rfl⟩ : syracuseStep 892999 = 1339499) B1339499
theorem B893339 : Blo 892572 893339 := bstep (se 1 (by rfl) ⟨670004, by rfl⟩ : syracuseStep 893339 = 1340009) B1340009
theorem B3449339 : Blo 892572 3449339 := bstep (se 1 (by rfl) ⟨2587004, by rfl⟩ : syracuseStep 3449339 = 5174009) B5174009
theorem B893679 : Blo 892572 893679 := bstep (se 1 (by rfl) ⟨670259, by rfl⟩ : syracuseStep 893679 = 1340519) B1340519
theorem B893759 : Blo 892572 893759 := bstep (se 1 (by rfl) ⟨670319, by rfl⟩ : syracuseStep 893759 = 1340639) B1340639
theorem B893935 : Blo 892572 893935 := bstep (se 1 (by rfl) ⟨670451, by rfl⟩ : syracuseStep 893935 = 1340903) B1340903
theorem B893983 : Blo 892572 893983 := bstep (se 1 (by rfl) ⟨670487, by rfl⟩ : syracuseStep 893983 = 1340975) B1340975
theorem B894079 : Blo 892572 894079 := bstep (se 1 (by rfl) ⟨670559, by rfl⟩ : syracuseStep 894079 = 1341119) B1341119
theorem B3023999 : Blo 892572 3023999 := bstep (se 1 (by rfl) ⟨2267999, by rfl⟩ : syracuseStep 3023999 = 4535999) B4535999
theorem B894367 : Blo 892572 894367 := bstep (se 1 (by rfl) ⟨670775, by rfl⟩ : syracuseStep 894367 = 1341551) B1341551
theorem B894831 : Blo 892572 894831 := bstep (se 1 (by rfl) ⟨671123, by rfl⟩ : syracuseStep 894831 = 1342247) B1342247
theorem B894847 : Blo 892572 894847 := bstep (se 1 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 894847 = 1342271) B1342271
theorem B894887 : Blo 892572 894887 := bstep (se 1 (by rfl) ⟨671165, by rfl⟩ : syracuseStep 894887 = 1342331) B1342331
theorem B895207 : Blo 892572 895207 := bstep (se 1 (by rfl) ⟨671405, by rfl⟩ : syracuseStep 895207 = 1342811) B1342811
theorem B895455 : Blo 892572 895455 := bstep (se 1 (by rfl) ⟨671591, by rfl⟩ : syracuseStep 895455 = 1343183) B1343183
theorem B895463 : Blo 892572 895463 := bstep (se 1 (by rfl) ⟨671597, by rfl⟩ : syracuseStep 895463 = 1343195) B1343195
theorem B2009807 : Blo 892572 2009807 := bstep (se 1 (by rfl) ⟨1507355, by rfl⟩ : syracuseStep 2009807 = 3014711) B3014711
theorem B2009897 : Blo 892572 2009897 := bstep (se 2 (by rfl) ⟨753711, by rfl⟩ : syracuseStep 2009897 = 1507423) B1507423
theorem B1911593 : Blo 892572 1911593 := bstep (se 2 (by rfl) ⟨716847, by rfl⟩ : syracuseStep 1911593 = 1433695) B1433695
theorem B895983 : Blo 892572 895983 := bstep (se 1 (by rfl) ⟨671987, by rfl⟩ : syracuseStep 895983 = 1343975) B1343975
theorem B896031 : Blo 892572 896031 := bstep (se 1 (by rfl) ⟨672023, by rfl⟩ : syracuseStep 896031 = 1344047) B1344047
theorem B5090471 : Blo 892572 5090471 := bstep (se 1 (by rfl) ⟨3817853, by rfl⟩ : syracuseStep 5090471 = 7635707) B7635707
theorem B35892413 : Blo 892572 35892413 := bstep (se 3 (by rfl) ⟨6729827, by rfl⟩ : syracuseStep 35892413 = 13459655) B13459655
theorem B2174255 : Blo 892572 2174255 := bstep (se 1 (by rfl) ⟨1630691, by rfl⟩ : syracuseStep 2174255 = 3261383) B3261383
theorem B2010599 : Blo 892572 2010599 := bstep (se 1 (by rfl) ⟨1507949, by rfl⟩ : syracuseStep 2010599 = 3015899) B3015899
theorem B2010977 : Blo 892572 2010977 := bstep (se 2 (by rfl) ⟨754116, by rfl⟩ : syracuseStep 2010977 = 1508233) B1508233
theorem B32714765 : Blo 892572 32714765 := bstep (se 3 (by rfl) ⟨6134018, by rfl⟩ : syracuseStep 32714765 = 12268037) B12268037
theorem B2011175 : Blo 892572 2011175 := bstep (se 1 (by rfl) ⟨1508381, by rfl⟩ : syracuseStep 2011175 = 3016763) B3016763
theorem B4600435 : Blo 892572 4600435 := bstep (se 1 (by rfl) ⟨3450326, by rfl⟩ : syracuseStep 4600435 = 6900653) B6900653
theorem B8696657 : Blo 892572 8696657 := bstep (se 2 (by rfl) ⟨3261246, by rfl⟩ : syracuseStep 8696657 = 6522493) B6522493
theorem B10859345 : Blo 892572 10859345 := bstep (se 2 (by rfl) ⟨4072254, by rfl⟩ : syracuseStep 10859345 = 8144509) B8144509
theorem B3814265 : Blo 892572 3814265 := bstep (se 2 (by rfl) ⟨1430349, by rfl⟩ : syracuseStep 3814265 = 2860699) B2860699
theorem B46445561 : Blo 892572 46445561 := bstep (se 2 (by rfl) ⟨17417085, by rfl⟩ : syracuseStep 46445561 = 34834171) B34834171
theorem B3814523 : Blo 892572 3814523 := bstep (se 1 (by rfl) ⟨2860892, by rfl⟩ : syracuseStep 3814523 = 5721785) B5721785
theorem B2012471 : Blo 892572 2012471 := bstep (se 1 (by rfl) ⟨1509353, by rfl⟩ : syracuseStep 2012471 = 3018707) B3018707
theorem B6797195 : Blo 892572 6797195 := bstep (se 1 (by rfl) ⟨5097896, by rfl⟩ : syracuseStep 6797195 = 10195793) B10195793
theorem B7747721 : Blo 892572 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B11450585 : Blo 892572 11450585 := bstep (se 2 (by rfl) ⟨4293969, by rfl⟩ : syracuseStep 11450585 = 8587939) B8587939
theorem B11483801 : Blo 892572 11483801 := bstep (se 2 (by rfl) ⟨4306425, by rfl⟩ : syracuseStep 11483801 = 8612851) B8612851
theorem B2013947 : Blo 892572 2013947 := bstep (se 1 (by rfl) ⟨1510460, by rfl⟩ : syracuseStep 2013947 = 3020921) B3020921
theorem B65354789 : Blo 892572 65354789 := bstep (se 4 (by rfl) ⟨6127011, by rfl⟩ : syracuseStep 65354789 = 12254023) B12254023
theorem B2014271 : Blo 892572 2014271 := bstep (se 1 (by rfl) ⟨1510703, by rfl⟩ : syracuseStep 2014271 = 3021407) B3021407
theorem B2146601 : Blo 892572 2146601 := bstep (se 2 (by rfl) ⟨804975, by rfl⟩ : syracuseStep 2146601 = 1609951) B1609951
theorem B3391915 : Blo 892572 3391915 := bstep (se 1 (by rfl) ⟨2543936, by rfl⟩ : syracuseStep 3391915 = 5087873) B5087873
theorem B3818623 : Blo 892572 3818623 := bstep (se 1 (by rfl) ⟨2863967, by rfl⟩ : syracuseStep 3818623 = 5727935) B5727935
theorem B2016521 : Blo 892572 2016521 := bstep (se 2 (by rfl) ⟨756195, by rfl⟩ : syracuseStep 2016521 = 1512391) B1512391
theorem B29017511 : Blo 892572 29017511 := bstep (se 1 (by rfl) ⟨21763133, by rfl⟩ : syracuseStep 29017511 = 43526267) B43526267
theorem B7653203 : Blo 892572 7653203 := bstep (se 1 (by rfl) ⟨5739902, by rfl⟩ : syracuseStep 7653203 = 11479805) B11479805
theorem B9324571 : Blo 892572 9324571 := bstep (se 1 (by rfl) ⟨6993428, by rfl⟩ : syracuseStep 9324571 = 13986857) B13986857
theorem B10176839 : Blo 892572 10176839 := bstep (se 1 (by rfl) ⟨7632629, by rfl⟩ : syracuseStep 10176839 = 15265259) B15265259
theorem B3394619 : Blo 892572 3394619 := bstep (se 1 (by rfl) ⟨2545964, by rfl⟩ : syracuseStep 3394619 = 5091929) B5091929
theorem B2543071 : Blo 892572 2543071 := bstep (se 1 (by rfl) ⟨1907303, by rfl⟩ : syracuseStep 2543071 = 3814607) B3814607
theorem B8146439 : Blo 892572 8146439 := bstep (se 1 (by rfl) ⟨6109829, by rfl⟩ : syracuseStep 8146439 = 12219659) B12219659
theorem B2543687 : Blo 892572 2543687 := bstep (se 1 (by rfl) ⟨1907765, by rfl⟩ : syracuseStep 2543687 = 3815531) B3815531
theorem B4085407 : Blo 892572 4085407 := bstep (se 1 (by rfl) ⟨3064055, by rfl⟩ : syracuseStep 4085407 = 6128111) B6128111
theorem B3823595 : Blo 892572 3823595 := bstep (se 1 (by rfl) ⟨2867696, by rfl⟩ : syracuseStep 3823595 = 5735393) B5735393
theorem B22042705 : Blo 892572 22042705 := bstep (se 2 (by rfl) ⟨8266014, by rfl⟩ : syracuseStep 22042705 = 16532029) B16532029
theorem B7657577 : Blo 892572 7657577 := bstep (se 2 (by rfl) ⟨2871591, by rfl⟩ : syracuseStep 7657577 = 5743183) B5743183
theorem B1006951 : Blo 892572 1006951 := bstep (se 1 (by rfl) ⟨755213, by rfl⟩ : syracuseStep 1006951 = 1510427) B1510427
theorem B1007131 : Blo 892572 1007131 := bstep (se 1 (by rfl) ⟨755348, by rfl⟩ : syracuseStep 1007131 = 1510697) B1510697
theorem B509501249 : Blo 892572 509501249 := bstep (se 2 (by rfl) ⟨191062968, by rfl⟩ : syracuseStep 509501249 = 382125937) B382125937
theorem B5103593 : Blo 892572 5103593 := bstep (se 2 (by rfl) ⟨1913847, by rfl⟩ : syracuseStep 5103593 = 3827695) B3827695
theorem B3629395 : Blo 892572 3629395 := bstep (se 1 (by rfl) ⟨2722046, by rfl⟩ : syracuseStep 3629395 = 5444093) B5444093
theorem B1008283 : Blo 892572 1008283 := bstep (se 1 (by rfl) ⟨756212, by rfl⟩ : syracuseStep 1008283 = 1512425) B1512425
theorem B1008319 : Blo 892572 1008319 := bstep (se 1 (by rfl) ⟨756239, by rfl⟩ : syracuseStep 1008319 = 1512479) B1512479
theorem B7267067 : Blo 892572 7267067 := bstep (se 1 (by rfl) ⟨5450300, by rfl⟩ : syracuseStep 7267067 = 10900601) B10900601
theorem B3400967 : Blo 892572 3400967 := bstep (se 1 (by rfl) ⟨2550725, by rfl⟩ : syracuseStep 3400967 = 5101451) B5101451
theorem B8578871 : Blo 892572 8578871 := bstep (se 1 (by rfl) ⟨6434153, by rfl⟩ : syracuseStep 8578871 = 12868307) B12868307
theorem B13789673 : Blo 892572 13789673 := bstep (se 2 (by rfl) ⟨5171127, by rfl⟩ : syracuseStep 13789673 = 10342255) B10342255
theorem B4582271 : Blo 892572 4582271 := bstep (se 1 (by rfl) ⟨3436703, by rfl⟩ : syracuseStep 4582271 = 6873407) B6873407
theorem B2551763 : Blo 892572 2551763 := bstep (se 1 (by rfl) ⟨1913822, by rfl⟩ : syracuseStep 2551763 = 3827645) B3827645
theorem B1339583 : Blo 892572 1339583 := bstep (se 1 (by rfl) ⟨1004687, by rfl⟩ : syracuseStep 1339583 = 2009375) B2009375
theorem B1339631 : Blo 892572 1339631 := bstep (se 1 (by rfl) ⟨1004723, by rfl⟩ : syracuseStep 1339631 = 2009447) B2009447
theorem B293171723 : Blo 892572 293171723 := bstep (se 1 (by rfl) ⟨219878792, by rfl⟩ : syracuseStep 293171723 = 439757585) B439757585
theorem B6780185 : Blo 892572 6780185 := bstep (se 2 (by rfl) ⟨2542569, by rfl⟩ : syracuseStep 6780185 = 5085139) B5085139
theorem B12875111 : Blo 892572 12875111 := bstep (se 1 (by rfl) ⟨9656333, by rfl⟩ : syracuseStep 12875111 = 19312667) B19312667
theorem B1865081 : Blo 892572 1865081 := bstep (se 2 (by rfl) ⟨699405, by rfl⟩ : syracuseStep 1865081 = 1398811) B1398811
theorem B1342235 : Blo 892572 1342235 := bstep (se 1 (by rfl) ⟨1006676, by rfl⟩ : syracuseStep 1342235 = 2013353) B2013353
theorem B1506377 : Blo 892572 1506377 := bstep (se 2 (by rfl) ⟨564891, by rfl⟩ : syracuseStep 1506377 = 1129783) B1129783
theorem B1506559 : Blo 892572 1506559 := bstep (se 1 (by rfl) ⟨1129919, by rfl⟩ : syracuseStep 1506559 = 2259839) B2259839
theorem B34405883 : Blo 892572 34405883 := bstep (se 1 (by rfl) ⟨25804412, by rfl⟩ : syracuseStep 34405883 = 51608825) B51608825
theorem B1343135 : Blo 892572 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B74580527 : Blo 892572 74580527 := bstep (se 1 (by rfl) ⟨55935395, by rfl⟩ : syracuseStep 74580527 = 111870791) B111870791
theorem B4522553 : Blo 892572 4522553 := bstep (se 2 (by rfl) ⟨1695957, by rfl⟩ : syracuseStep 4522553 = 3391915) B3391915
theorem B1344347 : Blo 892572 1344347 := bstep (se 1 (by rfl) ⟨1008260, by rfl⟩ : syracuseStep 1344347 = 2016521) B2016521
theorem B1344377 : Blo 892572 1344377 := bstep (se 2 (by rfl) ⟨504141, by rfl⟩ : syracuseStep 1344377 = 1008283) B1008283
theorem B1344425 : Blo 892572 1344425 := bstep (se 2 (by rfl) ⟨504159, by rfl⟩ : syracuseStep 1344425 = 1008319) B1008319
theorem B3016007 : Blo 892572 3016007 := bstep (se 1 (by rfl) ⟨2262005, by rfl⟩ : syracuseStep 3016007 = 4524011) B4524011
theorem B6784559 : Blo 892572 6784559 := bstep (se 1 (by rfl) ⟨5088419, by rfl⟩ : syracuseStep 6784559 = 10176839) B10176839
theorem B2263079 : Blo 892572 2263079 := bstep (se 1 (by rfl) ⟨1697309, by rfl⟩ : syracuseStep 2263079 = 3394619) B3394619
theorem B130550777 : Blo 892572 130550777 := bstep (se 2 (by rfl) ⟨48956541, by rfl⟩ : syracuseStep 130550777 = 97913083) B97913083
theorem B41881171 : Blo 892572 41881171 := bstep (se 1 (by rfl) ⟨31410878, by rfl⟩ : syracuseStep 41881171 = 62821757) B62821757
theorem B1512047 : Blo 892572 1512047 := bstep (se 1 (by rfl) ⟨1134035, by rfl⟩ : syracuseStep 1512047 = 2268071) B2268071
theorem B6133913 : Blo 892572 6133913 := bstep (se 2 (by rfl) ⟨2300217, by rfl⟩ : syracuseStep 6133913 = 4600435) B4600435
theorem B2267311 : Blo 892572 2267311 := bstep (se 1 (by rfl) ⟨1700483, by rfl⟩ : syracuseStep 2267311 = 3400967) B3400967
theorem B3054847 : Blo 892572 3054847 := bstep (se 1 (by rfl) ⟨2291135, by rfl⟩ : syracuseStep 3054847 = 4582271) B4582271
theorem B23928275 : Blo 892572 23928275 := bstep (se 1 (by rfl) ⟨17946206, by rfl⟩ : syracuseStep 23928275 = 35892413) B35892413
theorem B1449503 : Blo 892572 1449503 := bstep (se 1 (by rfl) ⟨1087127, by rfl⟩ : syracuseStep 1449503 = 2174255) B2174255
theorem B5447209 : Blo 892572 5447209 := bstep (se 2 (by rfl) ⟨2042703, by rfl⟩ : syracuseStep 5447209 = 4085407) B4085407
theorem B893055 : Blo 892572 893055 := bstep (se 1 (by rfl) ⟨669791, by rfl⟩ : syracuseStep 893055 = 1339583) B1339583
theorem B893087 : Blo 892572 893087 := bstep (se 1 (by rfl) ⟨669815, by rfl⟩ : syracuseStep 893087 = 1339631) B1339631
theorem B4531463 : Blo 892572 4531463 := bstep (se 1 (by rfl) ⟨3398597, by rfl⟩ : syracuseStep 4531463 = 6797195) B6797195
theorem B2008745 : Blo 892572 2008745 := bstep (se 2 (by rfl) ⟨753279, by rfl⟩ : syracuseStep 2008745 = 1506559) B1506559
theorem B894823 : Blo 892572 894823 := bstep (se 1 (by rfl) ⟨671117, by rfl⟩ : syracuseStep 894823 = 1342235) B1342235
theorem B895423 : Blo 892572 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B895679 : Blo 892572 895679 := bstep (se 1 (by rfl) ⟨671759, by rfl⟩ : syracuseStep 895679 = 1343519) B1343519
theorem B895807 : Blo 892572 895807 := bstep (se 1 (by rfl) ⟨671855, by rfl⟩ : syracuseStep 895807 = 1343711) B1343711
theorem B895911 : Blo 892572 895911 := bstep (se 1 (by rfl) ⟨671933, by rfl⟩ : syracuseStep 895911 = 1343867) B1343867
theorem B2010095 : Blo 892572 2010095 := bstep (se 1 (by rfl) ⟨1507571, by rfl⟩ : syracuseStep 2010095 = 3015143) B3015143
theorem B2010347 : Blo 892572 2010347 := bstep (se 1 (by rfl) ⟨1507760, by rfl⟩ : syracuseStep 2010347 = 3015521) B3015521
theorem B896559 : Blo 892572 896559 := bstep (se 1 (by rfl) ⟨672419, by rfl⟩ : syracuseStep 896559 = 1344839) B1344839
theorem B19345007 : Blo 892572 19345007 := bstep (se 1 (by rfl) ⟨14508755, by rfl⟩ : syracuseStep 19345007 = 29017511) B29017511
theorem B5091497 : Blo 892572 5091497 := bstep (se 2 (by rfl) ⟨1909311, by rfl⟩ : syracuseStep 5091497 = 3818623) B3818623
theorem B4895839 : Blo 892572 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B12432761 : Blo 892572 12432761 := bstep (se 2 (by rfl) ⟨4662285, by rfl⟩ : syracuseStep 12432761 = 9324571) B9324571
theorem B2012651 : Blo 892572 2012651 := bstep (se 1 (by rfl) ⟨1509488, by rfl⟩ : syracuseStep 2012651 = 3018977) B3018977
theorem B5092955 : Blo 892572 5092955 := bstep (se 1 (by rfl) ⟨3819716, by rfl⟩ : syracuseStep 5092955 = 7639433) B7639433
theorem B2012777 : Blo 892572 2012777 := bstep (se 2 (by rfl) ⟨754791, by rfl⟩ : syracuseStep 2012777 = 1509583) B1509583
theorem B3390761 : Blo 892572 3390761 := bstep (se 2 (by rfl) ⟨1271535, by rfl⟩ : syracuseStep 3390761 = 2543071) B2543071
theorem B2015135 : Blo 892572 2015135 := bstep (se 1 (by rfl) ⟨1511351, by rfl⟩ : syracuseStep 2015135 = 3022703) B3022703
theorem B2015999 : Blo 892572 2015999 := bstep (se 1 (by rfl) ⟨1511999, by rfl⟩ : syracuseStep 2015999 = 3023999) B3023999
theorem B5719247 : Blo 892572 5719247 := bstep (se 1 (by rfl) ⟨4289435, by rfl⟩ : syracuseStep 5719247 = 8578871) B8578871
theorem B9193115 : Blo 892572 9193115 := bstep (se 1 (by rfl) ⟨6894836, by rfl⟩ : syracuseStep 9193115 = 13789673) B13789673
theorem B3393647 : Blo 892572 3393647 := bstep (se 1 (by rfl) ⟨2545235, by rfl⟩ : syracuseStep 3393647 = 5090471) B5090471
theorem B21809843 : Blo 892572 21809843 := bstep (se 1 (by rfl) ⟨16357382, by rfl⟩ : syracuseStep 21809843 = 32714765) B32714765
theorem B195447815 : Blo 892572 195447815 := bstep (se 1 (by rfl) ⟨146585861, by rfl⟩ : syracuseStep 195447815 = 293171723) B293171723
theorem B2542843 : Blo 892572 2542843 := bstep (se 1 (by rfl) ⟨1907132, by rfl⟩ : syracuseStep 2542843 = 3814265) B3814265
theorem B2543015 : Blo 892572 2543015 := bstep (se 1 (by rfl) ⟨1907261, by rfl⟩ : syracuseStep 2543015 = 3814523) B3814523
theorem B5165147 : Blo 892572 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B7655867 : Blo 892572 7655867 := bstep (se 1 (by rfl) ⟨5741900, by rfl⟩ : syracuseStep 7655867 = 11483801) B11483801
theorem B43569859 : Blo 892572 43569859 := bstep (se 1 (by rfl) ⟨32677394, by rfl⟩ : syracuseStep 43569859 = 65354789) B65354789
theorem B1004251 : Blo 892572 1004251 := bstep (se 1 (by rfl) ⟨753188, by rfl⟩ : syracuseStep 1004251 = 1506377) B1506377
theorem B4839193 : Blo 892572 4839193 := bstep (se 2 (by rfl) ⟨1814697, by rfl⟩ : syracuseStep 4839193 = 3629395) B3629395
theorem B5724269 : Blo 892572 5724269 := bstep (se 3 (by rfl) ⟨1073300, by rfl⟩ : syracuseStep 5724269 = 2146601) B2146601
theorem B5102135 : Blo 892572 5102135 := bstep (se 1 (by rfl) ⟨3826601, by rfl⟩ : syracuseStep 5102135 = 7653203) B7653203
theorem B10312697 : Blo 892572 10312697 := bstep (se 2 (by rfl) ⟨3867261, by rfl⟩ : syracuseStep 10312697 = 7734523) B7734523
theorem B23191085 : Blo 892572 23191085 := bstep (se 3 (by rfl) ⟨4348328, by rfl⟩ : syracuseStep 23191085 = 8696657) B8696657
theorem B5430959 : Blo 892572 5430959 := bstep (se 1 (by rfl) ⟨4073219, by rfl⟩ : syracuseStep 5430959 = 8146439) B8146439
theorem B6119135 : Blo 892572 6119135 := bstep (se 1 (by rfl) ⟨4589351, by rfl⟩ : syracuseStep 6119135 = 9178703) B9178703
theorem B1695791 : Blo 892572 1695791 := bstep (se 1 (by rfl) ⟨1271843, by rfl⟩ : syracuseStep 1695791 = 2543687) B2543687
theorem B1008607 : Blo 892572 1008607 := bstep (se 1 (by rfl) ⟨756455, by rfl⟩ : syracuseStep 1008607 = 1512911) B1512911
theorem B3826703 : Blo 892572 3826703 := bstep (se 1 (by rfl) ⟨2870027, by rfl⟩ : syracuseStep 3826703 = 5740055) B5740055
theorem B2549063 : Blo 892572 2549063 := bstep (se 1 (by rfl) ⟨1911797, by rfl⟩ : syracuseStep 2549063 = 3823595) B3823595
theorem B5105051 : Blo 892572 5105051 := bstep (se 1 (by rfl) ⟨3828788, by rfl⟩ : syracuseStep 5105051 = 7657577) B7657577
theorem B339667499 : Blo 892572 339667499 := bstep (se 1 (by rfl) ⟨254750624, by rfl⟩ : syracuseStep 339667499 = 509501249) B509501249
theorem B36792949 : Blo 892572 36792949 := bstep (se 5 (by rfl) ⟨1724669, by rfl⟩ : syracuseStep 36792949 = 3449339) B3449339
theorem B3402395 : Blo 892572 3402395 := bstep (se 1 (by rfl) ⟨2551796, by rfl⟩ : syracuseStep 3402395 = 5103593) B5103593
theorem B1272937 : Blo 892572 1272937 := bstep (se 2 (by rfl) ⟨477351, by rfl⟩ : syracuseStep 1272937 = 954703) B954703
theorem B4844711 : Blo 892572 4844711 := bstep (se 1 (by rfl) ⟨3633533, by rfl⟩ : syracuseStep 4844711 = 7267067) B7267067
theorem B1339871 : Blo 892572 1339871 := bstep (se 1 (by rfl) ⟨1004903, by rfl⟩ : syracuseStep 1339871 = 2009807) B2009807
theorem B1339931 : Blo 892572 1339931 := bstep (se 1 (by rfl) ⟨1004948, by rfl⟩ : syracuseStep 1339931 = 2009897) B2009897
theorem B1274395 : Blo 892572 1274395 := bstep (se 1 (by rfl) ⟨955796, by rfl⟩ : syracuseStep 1274395 = 1911593) B1911593
theorem B10318373 : Blo 892572 10318373 := bstep (se 4 (by rfl) ⟨967347, by rfl⟩ : syracuseStep 10318373 = 1934695) B1934695
theorem B1340399 : Blo 892572 1340399 := bstep (se 1 (by rfl) ⟨1005299, by rfl⟩ : syracuseStep 1340399 = 2010599) B2010599
theorem B1340651 : Blo 892572 1340651 := bstep (se 1 (by rfl) ⟨1005488, by rfl⟩ : syracuseStep 1340651 = 2010977) B2010977
theorem B1701175 : Blo 892572 1701175 := bstep (se 1 (by rfl) ⟨1275881, by rfl⟩ : syracuseStep 1701175 = 2551763) B2551763
theorem B1340783 : Blo 892572 1340783 := bstep (se 1 (by rfl) ⟨1005587, by rfl⟩ : syracuseStep 1340783 = 2011175) B2011175
theorem B29390273 : Blo 892572 29390273 := bstep (se 2 (by rfl) ⟨11021352, by rfl⟩ : syracuseStep 29390273 = 22042705) B22042705
theorem B7239563 : Blo 892572 7239563 := bstep (se 1 (by rfl) ⟨5429672, by rfl⟩ : syracuseStep 7239563 = 10859345) B10859345
theorem B30963707 : Blo 892572 30963707 := bstep (se 1 (by rfl) ⟨23222780, by rfl⟩ : syracuseStep 30963707 = 46445561) B46445561
theorem B6125705 : Blo 892572 6125705 := bstep (se 2 (by rfl) ⟨2297139, by rfl⟩ : syracuseStep 6125705 = 4594279) B4594279
theorem B4520123 : Blo 892572 4520123 := bstep (se 1 (by rfl) ⟨3390092, by rfl⟩ : syracuseStep 4520123 = 6780185) B6780185
theorem B1341647 : Blo 892572 1341647 := bstep (se 1 (by rfl) ⟨1006235, by rfl⟩ : syracuseStep 1341647 = 2012471) B2012471
theorem B8583407 : Blo 892572 8583407 := bstep (se 1 (by rfl) ⟨6437555, by rfl⟩ : syracuseStep 8583407 = 12875111) B12875111
theorem B1243387 : Blo 892572 1243387 := bstep (se 1 (by rfl) ⟨932540, by rfl⟩ : syracuseStep 1243387 = 1865081) B1865081
theorem B7633723 : Blo 892572 7633723 := bstep (se 1 (by rfl) ⟨5725292, by rfl⟩ : syracuseStep 7633723 = 11450585) B11450585
theorem B1342601 : Blo 892572 1342601 := bstep (se 2 (by rfl) ⟨503475, by rfl⟩ : syracuseStep 1342601 = 1006951) B1006951
theorem B1342631 : Blo 892572 1342631 := bstep (se 1 (by rfl) ⟨1006973, by rfl⟩ : syracuseStep 1342631 = 2013947) B2013947
theorem B1342841 : Blo 892572 1342841 := bstep (se 2 (by rfl) ⟨503565, by rfl⟩ : syracuseStep 1342841 = 1007131) B1007131
theorem B1342847 : Blo 892572 1342847 := bstep (se 1 (by rfl) ⟨1007135, by rfl⟩ : syracuseStep 1342847 = 2014271) B2014271
theorem B22937255 : Blo 892572 22937255 := bstep (se 1 (by rfl) ⟨17202941, by rfl⟩ : syracuseStep 22937255 = 34405883) B34405883
theorem B278363897 : Blo 892572 278363897 := bstep (se 2 (by rfl) ⟨104386461, by rfl⟩ : syracuseStep 278363897 = 208772923) B208772923
theorem B3015035 : Blo 892572 3015035 := bstep (se 1 (by rfl) ⟨2261276, by rfl⟩ : syracuseStep 3015035 = 4522553) B4522553
theorem B1343999 : Blo 892572 1343999 := bstep (se 1 (by rfl) ⟨1007999, by rfl⟩ : syracuseStep 1343999 = 2015999) B2015999
theorem B4523039 : Blo 892572 4523039 := bstep (se 1 (by rfl) ⟨3392279, by rfl⟩ : syracuseStep 4523039 = 6784559) B6784559
theorem B1344809 : Blo 892572 1344809 := bstep (se 2 (by rfl) ⟨504303, by rfl⟩ : syracuseStep 1344809 = 1008607) B1008607
theorem B1508719 : Blo 892572 1508719 := bstep (se 1 (by rfl) ⟨1131539, by rfl⟩ : syracuseStep 1508719 = 2263079) B2263079
theorem B2262431 : Blo 892572 2262431 := bstep (se 1 (by rfl) ⟨1696823, by rfl⟩ : syracuseStep 2262431 = 3393647) B3393647
theorem B87033851 : Blo 892572 87033851 := bstep (se 1 (by rfl) ⟨65275388, by rfl⟩ : syracuseStep 87033851 = 130550777) B130550777
theorem B49057265 : Blo 892572 49057265 := bstep (se 2 (by rfl) ⟨18396474, by rfl⟩ : syracuseStep 49057265 = 36792949) B36792949
theorem B24514973 : Blo 892572 24514973 := bstep (se 3 (by rfl) ⟨4596557, by rfl⟩ : syracuseStep 24514973 = 9193115) B9193115
theorem B55841561 : Blo 892572 55841561 := bstep (se 2 (by rfl) ⟨20940585, by rfl⟩ : syracuseStep 55841561 = 41881171) B41881171
theorem B3020975 : Blo 892572 3020975 := bstep (se 1 (by rfl) ⟨2265731, by rfl⟩ : syracuseStep 3020975 = 4531463) B4531463
theorem B6527785 : Blo 892572 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B2268233 : Blo 892572 2268233 := bstep (se 2 (by rfl) ⟨850587, by rfl⟩ : syracuseStep 2268233 = 1701175) B1701175
theorem B2268263 : Blo 892572 2268263 := bstep (se 1 (by rfl) ⟨1701197, by rfl⟩ : syracuseStep 2268263 = 3402395) B3402395
theorem B3023081 : Blo 892572 3023081 := bstep (se 2 (by rfl) ⟨1133655, by rfl⟩ : syracuseStep 3023081 = 2267311) B2267311
theorem B893247 : Blo 892572 893247 := bstep (se 1 (by rfl) ⟨669935, by rfl⟩ : syracuseStep 893247 = 1339871) B1339871
theorem B893287 : Blo 892572 893287 := bstep (se 1 (by rfl) ⟨669965, by rfl⟩ : syracuseStep 893287 = 1339931) B1339931
theorem B893599 : Blo 892572 893599 := bstep (se 1 (by rfl) ⟨670199, by rfl⟩ : syracuseStep 893599 = 1340399) B1340399
theorem B893767 : Blo 892572 893767 := bstep (se 1 (by rfl) ⟨670325, by rfl⟩ : syracuseStep 893767 = 1340651) B1340651
theorem B893855 : Blo 892572 893855 := bstep (se 1 (by rfl) ⟨670391, by rfl⟩ : syracuseStep 893855 = 1340783) B1340783
theorem B4826375 : Blo 892572 4826375 := bstep (se 1 (by rfl) ⟨3619781, by rfl⟩ : syracuseStep 4826375 = 7239563) B7239563
theorem B894431 : Blo 892572 894431 := bstep (se 1 (by rfl) ⟨670823, by rfl⟩ : syracuseStep 894431 = 1341647) B1341647
theorem B4073129 : Blo 892572 4073129 := bstep (se 2 (by rfl) ⟨1527423, by rfl⟩ : syracuseStep 4073129 = 3054847) B3054847
theorem B895067 : Blo 892572 895067 := bstep (se 1 (by rfl) ⟨671300, by rfl⟩ : syracuseStep 895067 = 1342601) B1342601
theorem B895087 : Blo 892572 895087 := bstep (se 1 (by rfl) ⟨671315, by rfl⟩ : syracuseStep 895087 = 1342631) B1342631
theorem B895227 : Blo 892572 895227 := bstep (se 1 (by rfl) ⟨671420, by rfl⟩ : syracuseStep 895227 = 1342841) B1342841
theorem B895231 : Blo 892572 895231 := bstep (se 1 (by rfl) ⟨671423, by rfl⟩ : syracuseStep 895231 = 1342847) B1342847
theorem B185575931 : Blo 892572 185575931 := bstep (se 1 (by rfl) ⟨139181948, by rfl⟩ : syracuseStep 185575931 = 278363897) B278363897
theorem B13773725 : Blo 892572 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B896231 : Blo 892572 896231 := bstep (se 1 (by rfl) ⟨672173, by rfl⟩ : syracuseStep 896231 = 1344347) B1344347
theorem B896251 : Blo 892572 896251 := bstep (se 1 (by rfl) ⟨672188, by rfl⟩ : syracuseStep 896251 = 1344377) B1344377
theorem B896283 : Blo 892572 896283 := bstep (se 1 (by rfl) ⟨672212, by rfl⟩ : syracuseStep 896283 = 1344425) B1344425
theorem B3812831 : Blo 892572 3812831 := bstep (se 1 (by rfl) ⟨2859623, by rfl⟩ : syracuseStep 3812831 = 5719247) B5719247
theorem B2010671 : Blo 892572 2010671 := bstep (se 1 (by rfl) ⟨1508003, by rfl⟩ : syracuseStep 2010671 = 3016007) B3016007
theorem B198881405 : Blo 892572 198881405 := bstep (se 3 (by rfl) ⟨37290263, by rfl⟩ : syracuseStep 198881405 = 74580527) B74580527
theorem B130298543 : Blo 892572 130298543 := bstep (se 1 (by rfl) ⟨97723907, by rfl⟩ : syracuseStep 130298543 = 195447815) B195447815
theorem B10204541 : Blo 892572 10204541 := bstep (se 3 (by rfl) ⟨1913351, by rfl⟩ : syracuseStep 10204541 = 3826703) B3826703
theorem B3816179 : Blo 892572 3816179 := bstep (se 1 (by rfl) ⟨2862134, by rfl⟩ : syracuseStep 3816179 = 5724269) B5724269
theorem B3390457 : Blo 892572 3390457 := bstep (se 2 (by rfl) ⟨1271421, by rfl⟩ : syracuseStep 3390457 = 2542843) B2542843
theorem B966335 : Blo 892572 966335 := bstep (se 1 (by rfl) ⟨724751, by rfl⟩ : syracuseStep 966335 = 1449503) B1449503
theorem B3620639 : Blo 892572 3620639 := bstep (se 1 (by rfl) ⟨2715479, by rfl⟩ : syracuseStep 3620639 = 5430959) B5430959
theorem B4079423 : Blo 892572 4079423 := bstep (se 1 (by rfl) ⟨3059567, by rfl⟩ : syracuseStep 4079423 = 6119135) B6119135
theorem B1130527 : Blo 892572 1130527 := bstep (se 1 (by rfl) ⟨847895, by rfl⟩ : syracuseStep 1130527 = 1695791) B1695791
theorem B226444999 : Blo 892572 226444999 := bstep (se 1 (by rfl) ⟨169833749, by rfl⟩ : syracuseStep 226444999 = 339667499) B339667499
theorem B3229807 : Blo 892572 3229807 := bstep (se 1 (by rfl) ⟨2422355, by rfl⟩ : syracuseStep 3229807 = 4844711) B4844711
theorem B12896671 : Blo 892572 12896671 := bstep (se 1 (by rfl) ⟨9672503, by rfl⟩ : syracuseStep 12896671 = 19345007) B19345007
theorem B3394331 : Blo 892572 3394331 := bstep (se 1 (by rfl) ⟨2545748, by rfl⟩ : syracuseStep 3394331 = 5091497) B5091497
theorem B1657849 : Blo 892572 1657849 := bstep (se 2 (by rfl) ⟨621693, by rfl⟩ : syracuseStep 1657849 = 1243387) B1243387
theorem B3395303 : Blo 892572 3395303 := bstep (se 1 (by rfl) ⟨2546477, by rfl⟩ : syracuseStep 3395303 = 5092955) B5092955
theorem B10178297 : Blo 892572 10178297 := bstep (se 2 (by rfl) ⟨3816861, by rfl⟩ : syracuseStep 10178297 = 7633723) B7633723
theorem B4083803 : Blo 892572 4083803 := bstep (se 1 (by rfl) ⟨3062852, by rfl⟩ : syracuseStep 4083803 = 6125705) B6125705
theorem B25809029 : Blo 892572 25809029 := bstep (se 4 (by rfl) ⟨2419596, by rfl⟩ : syracuseStep 25809029 = 4839193) B4839193
theorem B5722271 : Blo 892572 5722271 := bstep (se 1 (by rfl) ⟨4291703, by rfl⟩ : syracuseStep 5722271 = 8583407) B8583407
theorem B7262945 : Blo 892572 7262945 := bstep (se 2 (by rfl) ⟨2723604, by rfl⟩ : syracuseStep 7262945 = 5447209) B5447209
theorem B15291503 : Blo 892572 15291503 := bstep (se 1 (by rfl) ⟨11468627, by rfl⟩ : syracuseStep 15291503 = 22937255) B22937255
theorem B14539895 : Blo 892572 14539895 := bstep (se 1 (by rfl) ⟨10904921, by rfl⟩ : syracuseStep 14539895 = 21809843) B21809843
theorem B1695343 : Blo 892572 1695343 := bstep (se 1 (by rfl) ⟨1271507, by rfl⟩ : syracuseStep 1695343 = 2543015) B2543015
theorem B5103911 : Blo 892572 5103911 := bstep (se 1 (by rfl) ⟨3827933, by rfl⟩ : syracuseStep 5103911 = 7655867) B7655867
theorem B1008031 : Blo 892572 1008031 := bstep (se 1 (by rfl) ⟨756023, by rfl⟩ : syracuseStep 1008031 = 1512047) B1512047
theorem B4089275 : Blo 892572 4089275 := bstep (se 1 (by rfl) ⟨3066956, by rfl⟩ : syracuseStep 4089275 = 6133913) B6133913
theorem B1697249 : Blo 892572 1697249 := bstep (se 2 (by rfl) ⟨636468, by rfl⟩ : syracuseStep 1697249 = 1272937) B1272937
theorem B3401423 : Blo 892572 3401423 := bstep (se 1 (by rfl) ⟨2551067, by rfl⟩ : syracuseStep 3401423 = 5102135) B5102135
theorem B6875131 : Blo 892572 6875131 := bstep (se 1 (by rfl) ⟨5156348, by rfl⟩ : syracuseStep 6875131 = 10312697) B10312697
theorem B15952183 : Blo 892572 15952183 := bstep (se 1 (by rfl) ⟨11964137, by rfl⟩ : syracuseStep 15952183 = 23928275) B23928275
theorem B15460723 : Blo 892572 15460723 := bstep (se 1 (by rfl) ⟨11595542, by rfl⟩ : syracuseStep 15460723 = 23191085) B23191085
theorem B1699193 : Blo 892572 1699193 := bstep (se 2 (by rfl) ⟨637197, by rfl⟩ : syracuseStep 1699193 = 1274395) B1274395
theorem B1699375 : Blo 892572 1699375 := bstep (se 1 (by rfl) ⟨1274531, by rfl⟩ : syracuseStep 1699375 = 2549063) B2549063
theorem B58093145 : Blo 892572 58093145 := bstep (se 2 (by rfl) ⟨21784929, by rfl⟩ : syracuseStep 58093145 = 43569859) B43569859
theorem B3403367 : Blo 892572 3403367 := bstep (se 1 (by rfl) ⟨2552525, by rfl⟩ : syracuseStep 3403367 = 5105051) B5105051
theorem B1339001 : Blo 892572 1339001 := bstep (se 2 (by rfl) ⟨502125, by rfl⟩ : syracuseStep 1339001 = 1004251) B1004251
theorem B1339163 : Blo 892572 1339163 := bstep (se 1 (by rfl) ⟨1004372, by rfl⟩ : syracuseStep 1339163 = 2008745) B2008745
theorem B1340063 : Blo 892572 1340063 := bstep (se 1 (by rfl) ⟨1005047, by rfl⟩ : syracuseStep 1340063 = 2010095) B2010095
theorem B1340231 : Blo 892572 1340231 := bstep (se 1 (by rfl) ⟨1005173, by rfl⟩ : syracuseStep 1340231 = 2010347) B2010347
theorem B6878915 : Blo 892572 6878915 := bstep (se 1 (by rfl) ⟨5159186, by rfl⟩ : syracuseStep 6878915 = 10318373) B10318373
theorem B8288507 : Blo 892572 8288507 := bstep (se 1 (by rfl) ⟨6216380, by rfl⟩ : syracuseStep 8288507 = 12432761) B12432761
theorem B19593515 : Blo 892572 19593515 := bstep (se 1 (by rfl) ⟨14695136, by rfl⟩ : syracuseStep 19593515 = 29390273) B29390273
theorem B1341767 : Blo 892572 1341767 := bstep (se 1 (by rfl) ⟨1006325, by rfl⟩ : syracuseStep 1341767 = 2012651) B2012651
theorem B1341851 : Blo 892572 1341851 := bstep (se 1 (by rfl) ⟨1006388, by rfl⟩ : syracuseStep 1341851 = 2012777) B2012777
theorem B20642471 : Blo 892572 20642471 := bstep (se 1 (by rfl) ⟨15481853, by rfl⟩ : syracuseStep 20642471 = 30963707) B30963707
theorem B3013415 : Blo 892572 3013415 := bstep (se 1 (by rfl) ⟨2260061, by rfl⟩ : syracuseStep 3013415 = 4520123) B4520123
theorem B2260507 : Blo 892572 2260507 := bstep (se 1 (by rfl) ⟨1695380, by rfl⟩ : syracuseStep 2260507 = 3390761) B3390761
theorem B1343423 : Blo 892572 1343423 := bstep (se 1 (by rfl) ⟨1007567, by rfl⟩ : syracuseStep 1343423 = 2015135) B2015135
theorem B1507369 : Blo 892572 1507369 := bstep (se 2 (by rfl) ⟨565263, by rfl⟩ : syracuseStep 1507369 = 1130527) B1130527
theorem B1344041 : Blo 892572 1344041 := bstep (se 2 (by rfl) ⟨504015, by rfl⟩ : syracuseStep 1344041 = 1008031) B1008031
theorem B3015359 : Blo 892572 3015359 := bstep (se 1 (by rfl) ⟨2261519, by rfl⟩ : syracuseStep 3015359 = 4523039) B4523039
theorem B1508287 : Blo 892572 1508287 := bstep (se 1 (by rfl) ⟨1131215, by rfl⟩ : syracuseStep 1508287 = 2262431) B2262431
theorem B2262887 : Blo 892572 2262887 := bstep (se 1 (by rfl) ⟨1697165, by rfl⟩ : syracuseStep 2262887 = 3394331) B3394331
theorem B301926665 : Blo 892572 301926665 := bstep (se 2 (by rfl) ⟨113222499, by rfl⟩ : syracuseStep 301926665 = 226444999) B226444999
theorem B32704843 : Blo 892572 32704843 := bstep (se 1 (by rfl) ⟨24528632, by rfl⟩ : syracuseStep 32704843 = 49057265) B49057265
theorem B2263535 : Blo 892572 2263535 := bstep (se 1 (by rfl) ⟨1697651, by rfl⟩ : syracuseStep 2263535 = 3395303) B3395303
theorem B6785531 : Blo 892572 6785531 := bstep (se 1 (by rfl) ⟨5089148, by rfl⟩ : syracuseStep 6785531 = 10178297) B10178297
theorem B2722535 : Blo 892572 2722535 := bstep (se 1 (by rfl) ⟨2041901, by rfl⟩ : syracuseStep 2722535 = 4083803) B4083803
theorem B17206019 : Blo 892572 17206019 := bstep (se 1 (by rfl) ⟨12904514, by rfl⟩ : syracuseStep 17206019 = 25809029) B25809029
theorem B20614297 : Blo 892572 20614297 := bstep (se 2 (by rfl) ⟨7730361, by rfl⟩ : syracuseStep 20614297 = 15460723) B15460723
theorem B37227707 : Blo 892572 37227707 := bstep (se 1 (by rfl) ⟨27920780, by rfl⟩ : syracuseStep 37227707 = 55841561) B55841561
theorem B10194335 : Blo 892572 10194335 := bstep (se 1 (by rfl) ⟨7645751, by rfl⟩ : syracuseStep 10194335 = 15291503) B15291503
theorem B1512155 : Blo 892572 1512155 := bstep (se 1 (by rfl) ⟨1134116, by rfl⟩ : syracuseStep 1512155 = 2268233) B2268233
theorem B2265833 : Blo 892572 2265833 := bstep (se 2 (by rfl) ⟨849687, by rfl⟩ : syracuseStep 2265833 = 1699375) B1699375
theorem B1512175 : Blo 892572 1512175 := bstep (se 1 (by rfl) ⟨1134131, by rfl⟩ : syracuseStep 1512175 = 2268263) B2268263
theorem B3217583 : Blo 892572 3217583 := bstep (se 1 (by rfl) ⟨2413187, by rfl⟩ : syracuseStep 3217583 = 4826375) B4826375
theorem B2726183 : Blo 892572 2726183 := bstep (se 1 (by rfl) ⟨2044637, by rfl⟩ : syracuseStep 2726183 = 4089275) B4089275
theorem B2267615 : Blo 892572 2267615 := bstep (se 1 (by rfl) ⟨1700711, by rfl⟩ : syracuseStep 2267615 = 3401423) B3401423
theorem B9182483 : Blo 892572 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B2268911 : Blo 892572 2268911 := bstep (se 1 (by rfl) ⟨1701683, by rfl⟩ : syracuseStep 2268911 = 3403367) B3403367
theorem B892667 : Blo 892572 892667 := bstep (se 1 (by rfl) ⟨669500, by rfl⟩ : syracuseStep 892667 = 1339001) B1339001
theorem B892775 : Blo 892572 892775 := bstep (se 1 (by rfl) ⟨669581, by rfl⟩ : syracuseStep 892775 = 1339163) B1339163
theorem B132587603 : Blo 892572 132587603 := bstep (se 1 (by rfl) ⟨99440702, by rfl⟩ : syracuseStep 132587603 = 198881405) B198881405
theorem B893375 : Blo 892572 893375 := bstep (se 1 (by rfl) ⟨670031, by rfl⟩ : syracuseStep 893375 = 1340063) B1340063
theorem B893487 : Blo 892572 893487 := bstep (se 1 (by rfl) ⟨670115, by rfl⟩ : syracuseStep 893487 = 1340231) B1340231
theorem B894511 : Blo 892572 894511 := bstep (se 1 (by rfl) ⟨670883, by rfl⟩ : syracuseStep 894511 = 1341767) B1341767
theorem B894567 : Blo 892572 894567 := bstep (se 1 (by rfl) ⟨670925, by rfl⟩ : syracuseStep 894567 = 1341851) B1341851
theorem B2008943 : Blo 892572 2008943 := bstep (se 1 (by rfl) ⟨1506707, by rfl⟩ : syracuseStep 2008943 = 3013415) B3013415
theorem B895615 : Blo 892572 895615 := bstep (se 1 (by rfl) ⟨671711, by rfl⟩ : syracuseStep 895615 = 1343423) B1343423
theorem B2010023 : Blo 892572 2010023 := bstep (se 1 (by rfl) ⟨1507517, by rfl⟩ : syracuseStep 2010023 = 3015035) B3015035
theorem B895999 : Blo 892572 895999 := bstep (se 1 (by rfl) ⟨671999, by rfl⟩ : syracuseStep 895999 = 1343999) B1343999
theorem B896539 : Blo 892572 896539 := bstep (se 1 (by rfl) ⟨672404, by rfl⟩ : syracuseStep 896539 = 1344809) B1344809
theorem B85078309 : Blo 892572 85078309 := bstep (se 4 (by rfl) ⟨7976091, by rfl⟩ : syracuseStep 85078309 = 15952183) B15952183
theorem B2011625 : Blo 892572 2011625 := bstep (se 2 (by rfl) ⟨754359, by rfl⟩ : syracuseStep 2011625 = 1508719) B1508719
theorem B3814847 : Blo 892572 3814847 := bstep (se 1 (by rfl) ⟨2861135, by rfl⟩ : syracuseStep 3814847 = 5722271) B5722271
theorem B4306409 : Blo 892572 4306409 := bstep (se 2 (by rfl) ⟨1614903, by rfl⟩ : syracuseStep 4306409 = 3229807) B3229807
theorem B2210465 : Blo 892572 2210465 := bstep (se 2 (by rfl) ⟨828924, by rfl⟩ : syracuseStep 2210465 = 1657849) B1657849
theorem B2013983 : Blo 892572 2013983 := bstep (se 1 (by rfl) ⟨1510487, by rfl⟩ : syracuseStep 2013983 = 3020975) B3020975
theorem B2015387 : Blo 892572 2015387 := bstep (se 1 (by rfl) ⟨1511540, by rfl⟩ : syracuseStep 2015387 = 3023081) B3023081
theorem B1131499 : Blo 892572 1131499 := bstep (se 1 (by rfl) ⟨848624, by rfl⟩ : syracuseStep 1131499 = 1697249) B1697249
theorem B123717287 : Blo 892572 123717287 := bstep (se 1 (by rfl) ⟨92787965, by rfl⟩ : syracuseStep 123717287 = 185575931) B185575931
theorem B10307573 : Blo 892572 10307573 := bstep (se 5 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 10307573 = 966335) B966335
theorem B1132795 : Blo 892572 1132795 := bstep (se 1 (by rfl) ⟨849596, by rfl⟩ : syracuseStep 1132795 = 1699193) B1699193
theorem B2541887 : Blo 892572 2541887 := bstep (se 1 (by rfl) ⟨1906415, by rfl⟩ : syracuseStep 2541887 = 3812831) B3812831
theorem B6803027 : Blo 892572 6803027 := bstep (se 1 (by rfl) ⟨5102270, by rfl⟩ : syracuseStep 6803027 = 10204541) B10204541
theorem B8703713 : Blo 892572 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B5525671 : Blo 892572 5525671 := bstep (se 1 (by rfl) ⟨4144253, by rfl⟩ : syracuseStep 5525671 = 8288507) B8288507
theorem B13062343 : Blo 892572 13062343 := bstep (se 1 (by rfl) ⟨9796757, by rfl⟩ : syracuseStep 13062343 = 19593515) B19593515
theorem B2544119 : Blo 892572 2544119 := bstep (se 1 (by rfl) ⟨1908089, by rfl⟩ : syracuseStep 2544119 = 3816179) B3816179
theorem B9655037 : Blo 892572 9655037 := bstep (se 3 (by rfl) ⟨1810319, by rfl⟩ : syracuseStep 9655037 = 3620639) B3620639
theorem B58022567 : Blo 892572 58022567 := bstep (se 1 (by rfl) ⟨43516925, by rfl⟩ : syracuseStep 58022567 = 87033851) B87033851
theorem B9166841 : Blo 892572 9166841 := bstep (se 2 (by rfl) ⟨3437565, by rfl⟩ : syracuseStep 9166841 = 6875131) B6875131
theorem B16343315 : Blo 892572 16343315 := bstep (se 1 (by rfl) ⟨12257486, by rfl⟩ : syracuseStep 16343315 = 24514973) B24514973
theorem B4841963 : Blo 892572 4841963 := bstep (se 1 (by rfl) ⟨3631472, by rfl⟩ : syracuseStep 4841963 = 7262945) B7262945
theorem B17195561 : Blo 892572 17195561 := bstep (se 2 (by rfl) ⟨6448335, by rfl⟩ : syracuseStep 17195561 = 12896671) B12896671
theorem B9693263 : Blo 892572 9693263 := bstep (se 1 (by rfl) ⟨7269947, by rfl⟩ : syracuseStep 9693263 = 14539895) B14539895
theorem B3402607 : Blo 892572 3402607 := bstep (se 1 (by rfl) ⟨2551955, by rfl⟩ : syracuseStep 3402607 = 5103911) B5103911
theorem B2715419 : Blo 892572 2715419 := bstep (se 1 (by rfl) ⟨2036564, by rfl⟩ : syracuseStep 2715419 = 4073129) B4073129
theorem B1340447 : Blo 892572 1340447 := bstep (se 1 (by rfl) ⟨1005335, by rfl⟩ : syracuseStep 1340447 = 2010671) B2010671
theorem B38728763 : Blo 892572 38728763 := bstep (se 1 (by rfl) ⟨29046572, by rfl⟩ : syracuseStep 38728763 = 58093145) B58093145
theorem B86865695 : Blo 892572 86865695 := bstep (se 1 (by rfl) ⟨65149271, by rfl⟩ : syracuseStep 86865695 = 130298543) B130298543
theorem B4585943 : Blo 892572 4585943 := bstep (se 1 (by rfl) ⟨3439457, by rfl⟩ : syracuseStep 4585943 = 6878915) B6878915
theorem B4520609 : Blo 892572 4520609 := bstep (se 2 (by rfl) ⟨1695228, by rfl⟩ : syracuseStep 4520609 = 3390457) B3390457
theorem B13761647 : Blo 892572 13761647 := bstep (se 1 (by rfl) ⟨10321235, by rfl⟩ : syracuseStep 13761647 = 20642471) B20642471
theorem B3014009 : Blo 892572 3014009 := bstep (se 2 (by rfl) ⟨1130253, by rfl⟩ : syracuseStep 3014009 = 2260507) B2260507
theorem B2260457 : Blo 892572 2260457 := bstep (se 2 (by rfl) ⟨847671, by rfl⟩ : syracuseStep 2260457 = 1695343) B1695343
theorem B2719615 : Blo 892572 2719615 := bstep (se 1 (by rfl) ⟨2039711, by rfl⟩ : syracuseStep 2719615 = 4079423) B4079423
theorem B1343591 : Blo 892572 1343591 := bstep (se 1 (by rfl) ⟨1007693, by rfl⟩ : syracuseStep 1343591 = 2015387) B2015387
theorem B82478191 : Blo 892572 82478191 := bstep (se 1 (by rfl) ⟨61858643, by rfl⟩ : syracuseStep 82478191 = 123717287) B123717287
theorem B1508591 : Blo 892572 1508591 := bstep (se 1 (by rfl) ⟨1131443, by rfl⟩ : syracuseStep 1508591 = 2262887) B2262887
theorem B1508665 : Blo 892572 1508665 := bstep (se 2 (by rfl) ⟨565749, by rfl⟩ : syracuseStep 1508665 = 1131499) B1131499
theorem B1509023 : Blo 892572 1509023 := bstep (se 1 (by rfl) ⟨1131767, by rfl⟩ : syracuseStep 1509023 = 2263535) B2263535
theorem B4523687 : Blo 892572 4523687 := bstep (se 1 (by rfl) ⟨3392765, by rfl⟩ : syracuseStep 4523687 = 6785531) B6785531
theorem B11470679 : Blo 892572 11470679 := bstep (se 1 (by rfl) ⟨8603009, by rfl⟩ : syracuseStep 11470679 = 17206019) B17206019
theorem B1510393 : Blo 892572 1510393 := bstep (se 2 (by rfl) ⟨566397, by rfl⟩ : syracuseStep 1510393 = 1132795) B1132795
theorem B1510555 : Blo 892572 1510555 := bstep (se 1 (by rfl) ⟨1132916, by rfl⟩ : syracuseStep 1510555 = 2265833) B2265833
theorem B1511743 : Blo 892572 1511743 := bstep (se 1 (by rfl) ⟨1133807, by rfl⟩ : syracuseStep 1511743 = 2267615) B2267615
theorem B1512607 : Blo 892572 1512607 := bstep (se 1 (by rfl) ⟨1134455, by rfl⟩ : syracuseStep 1512607 = 2268911) B2268911
theorem B12229181 : Blo 892572 12229181 := bstep (se 3 (by rfl) ⟨2292971, by rfl⟩ : syracuseStep 12229181 = 4585943) B4585943
theorem B6462175 : Blo 892572 6462175 := bstep (se 1 (by rfl) ⟨4846631, by rfl⟩ : syracuseStep 6462175 = 9693263) B9693263
theorem B1810279 : Blo 892572 1810279 := bstep (se 1 (by rfl) ⟨1357709, by rfl⟩ : syracuseStep 1810279 = 2715419) B2715419
theorem B893631 : Blo 892572 893631 := bstep (se 1 (by rfl) ⟨670223, by rfl⟩ : syracuseStep 893631 = 1340447) B1340447
theorem B57910463 : Blo 892572 57910463 := bstep (se 1 (by rfl) ⟨43432847, by rfl⟩ : syracuseStep 57910463 = 86865695) B86865695
theorem B23209901 : Blo 892572 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B2009339 : Blo 892572 2009339 := bstep (se 1 (by rfl) ⟨1507004, by rfl⟩ : syracuseStep 2009339 = 3014009) B3014009
theorem B2009825 : Blo 892572 2009825 := bstep (se 2 (by rfl) ⟨753684, by rfl⟩ : syracuseStep 2009825 = 1507369) B1507369
theorem B896027 : Blo 892572 896027 := bstep (se 1 (by rfl) ⟨672020, by rfl⟩ : syracuseStep 896027 = 1344041) B1344041
theorem B2010239 : Blo 892572 2010239 := bstep (se 1 (by rfl) ⟨1507679, by rfl⟩ : syracuseStep 2010239 = 3015359) B3015359
theorem B2011049 : Blo 892572 2011049 := bstep (se 2 (by rfl) ⟨754143, by rfl⟩ : syracuseStep 2011049 = 1508287) B1508287
theorem B1815023 : Blo 892572 1815023 := bstep (se 1 (by rfl) ⟨1361267, by rfl⟩ : syracuseStep 1815023 = 2722535) B2722535
theorem B24818471 : Blo 892572 24818471 := bstep (se 1 (by rfl) ⟨18613853, by rfl⟩ : syracuseStep 24818471 = 37227707) B37227707
theorem B6796223 : Blo 892572 6796223 := bstep (se 1 (by rfl) ⟨5097167, by rfl⟩ : syracuseStep 6796223 = 10194335) B10194335
theorem B4535351 : Blo 892572 4535351 := bstep (se 1 (by rfl) ⟨3401513, by rfl⟩ : syracuseStep 4535351 = 6803027) B6803027
theorem B6436691 : Blo 892572 6436691 := bstep (se 1 (by rfl) ⟨4827518, by rfl⟩ : syracuseStep 6436691 = 9655037) B9655037
theorem B4536809 : Blo 892572 4536809 := bstep (se 2 (by rfl) ⟨1701303, by rfl⟩ : syracuseStep 4536809 = 3402607) B3402607
theorem B2145055 : Blo 892572 2145055 := bstep (se 1 (by rfl) ⟨1608791, by rfl⟩ : syracuseStep 2145055 = 3217583) B3217583
theorem B38681711 : Blo 892572 38681711 := bstep (se 1 (by rfl) ⟨29011283, by rfl⟩ : syracuseStep 38681711 = 58022567) B58022567
theorem B6111227 : Blo 892572 6111227 := bstep (se 1 (by rfl) ⟨4583420, by rfl⟩ : syracuseStep 6111227 = 9166841) B9166841
theorem B88391735 : Blo 892572 88391735 := bstep (se 1 (by rfl) ⟨66293801, by rfl⟩ : syracuseStep 88391735 = 132587603) B132587603
theorem B10895543 : Blo 892572 10895543 := bstep (se 1 (by rfl) ⟨8171657, by rfl⟩ : syracuseStep 10895543 = 16343315) B16343315
theorem B17416457 : Blo 892572 17416457 := bstep (se 2 (by rfl) ⟨6531171, by rfl⟩ : syracuseStep 17416457 = 13062343) B13062343
theorem B3227975 : Blo 892572 3227975 := bstep (se 1 (by rfl) ⟨2420981, by rfl⟩ : syracuseStep 3227975 = 4841963) B4841963
theorem B2016233 : Blo 892572 2016233 := bstep (se 2 (by rfl) ⟨756087, by rfl⟩ : syracuseStep 2016233 = 1512175) B1512175
theorem B2543231 : Blo 892572 2543231 := bstep (se 1 (by rfl) ⟨1907423, by rfl⟩ : syracuseStep 2543231 = 3814847) B3814847
theorem B2870939 : Blo 892572 2870939 := bstep (se 1 (by rfl) ⟨2153204, by rfl⟩ : syracuseStep 2870939 = 4306409) B4306409
theorem B3626153 : Blo 892572 3626153 := bstep (se 2 (by rfl) ⟨1359807, by rfl⟩ : syracuseStep 3626153 = 2719615) B2719615
theorem B6871715 : Blo 892572 6871715 := bstep (se 1 (by rfl) ⟨5153786, by rfl⟩ : syracuseStep 6871715 = 10307573) B10307573
theorem B201284443 : Blo 892572 201284443 := bstep (se 1 (by rfl) ⟨150963332, by rfl⟩ : syracuseStep 201284443 = 301926665) B301926665
theorem B1694591 : Blo 892572 1694591 := bstep (se 1 (by rfl) ⟨1270943, by rfl⟩ : syracuseStep 1694591 = 2541887) B2541887
theorem B1696079 : Blo 892572 1696079 := bstep (se 1 (by rfl) ⟨1272059, by rfl⟩ : syracuseStep 1696079 = 2544119) B2544119
theorem B43606457 : Blo 892572 43606457 := bstep (se 2 (by rfl) ⟨16352421, by rfl⟩ : syracuseStep 43606457 = 32704843) B32704843
theorem B1008103 : Blo 892572 1008103 := bstep (se 1 (by rfl) ⟨756077, by rfl⟩ : syracuseStep 1008103 = 1512155) B1512155
theorem B27485729 : Blo 892572 27485729 := bstep (se 2 (by rfl) ⟨10307148, by rfl⟩ : syracuseStep 27485729 = 20614297) B20614297
theorem B6121655 : Blo 892572 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B7367561 : Blo 892572 7367561 := bstep (se 2 (by rfl) ⟨2762835, by rfl⟩ : syracuseStep 7367561 = 5525671) B5525671
theorem B11463707 : Blo 892572 11463707 := bstep (se 1 (by rfl) ⟨8597780, by rfl⟩ : syracuseStep 11463707 = 17195561) B17195561
theorem B113437745 : Blo 892572 113437745 := bstep (se 2 (by rfl) ⟨42539154, by rfl⟩ : syracuseStep 113437745 = 85078309) B85078309
theorem B7269821 : Blo 892572 7269821 := bstep (se 3 (by rfl) ⟨1363091, by rfl⟩ : syracuseStep 7269821 = 2726183) B2726183
theorem B1339295 : Blo 892572 1339295 := bstep (se 1 (by rfl) ⟨1004471, by rfl⟩ : syracuseStep 1339295 = 2008943) B2008943
theorem B1340015 : Blo 892572 1340015 := bstep (se 1 (by rfl) ⟨1005011, by rfl⟩ : syracuseStep 1340015 = 2010023) B2010023
theorem B1341083 : Blo 892572 1341083 := bstep (se 1 (by rfl) ⟨1005812, by rfl⟩ : syracuseStep 1341083 = 2011625) B2011625
theorem B25819175 : Blo 892572 25819175 := bstep (se 1 (by rfl) ⟨19364381, by rfl⟩ : syracuseStep 25819175 = 38728763) B38728763
theorem B3013739 : Blo 892572 3013739 := bstep (se 1 (by rfl) ⟨2260304, by rfl⟩ : syracuseStep 3013739 = 4520609) B4520609
theorem B1473643 : Blo 892572 1473643 := bstep (se 1 (by rfl) ⟨1105232, by rfl⟩ : syracuseStep 1473643 = 2210465) B2210465
theorem B1342655 : Blo 892572 1342655 := bstep (se 1 (by rfl) ⟨1006991, by rfl⟩ : syracuseStep 1342655 = 2013983) B2013983
theorem B9174431 : Blo 892572 9174431 := bstep (se 1 (by rfl) ⟨6880823, by rfl⟩ : syracuseStep 9174431 = 13761647) B13761647
theorem B1506971 : Blo 892572 1506971 := bstep (se 1 (by rfl) ⟨1130228, by rfl⟩ : syracuseStep 1506971 = 2260457) B2260457
theorem B1344137 : Blo 892572 1344137 := bstep (se 2 (by rfl) ⟨504051, by rfl⟩ : syracuseStep 1344137 = 1008103) B1008103
theorem B1344155 : Blo 892572 1344155 := bstep (se 1 (by rfl) ⟨1008116, by rfl⟩ : syracuseStep 1344155 = 2016233) B2016233
theorem B4522877 : Blo 892572 4522877 := bstep (se 3 (by rfl) ⟨848039, by rfl⟩ : syracuseStep 4522877 = 1696079) B1696079
theorem B3015791 : Blo 892572 3015791 := bstep (se 1 (by rfl) ⟨2261843, by rfl⟩ : syracuseStep 3015791 = 4523687) B4523687
theorem B109970921 : Blo 892572 109970921 := bstep (se 2 (by rfl) ⟨41239095, by rfl⟩ : syracuseStep 109970921 = 82478191) B82478191
theorem B29070971 : Blo 892572 29070971 := bstep (se 1 (by rfl) ⟨21803228, by rfl⟩ : syracuseStep 29070971 = 43606457) B43606457
theorem B38606975 : Blo 892572 38606975 := bstep (se 1 (by rfl) ⟨28955231, by rfl⟩ : syracuseStep 38606975 = 57910463) B57910463
theorem B18323819 : Blo 892572 18323819 := bstep (se 1 (by rfl) ⟨13742864, by rfl⟩ : syracuseStep 18323819 = 27485729) B27485729
theorem B15473267 : Blo 892572 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B7642471 : Blo 892572 7642471 := bstep (se 1 (by rfl) ⟨5731853, by rfl⟩ : syracuseStep 7642471 = 11463707) B11463707
theorem B892863 : Blo 892572 892863 := bstep (se 1 (by rfl) ⟨669647, by rfl⟩ : syracuseStep 892863 = 1339295) B1339295
theorem B893343 : Blo 892572 893343 := bstep (se 1 (by rfl) ⟨670007, by rfl⟩ : syracuseStep 893343 = 1340015) B1340015
theorem B4530815 : Blo 892572 4530815 := bstep (se 1 (by rfl) ⟨3398111, by rfl⟩ : syracuseStep 4530815 = 6796223) B6796223
theorem B3023567 : Blo 892572 3023567 := bstep (se 1 (by rfl) ⟨2267675, by rfl⟩ : syracuseStep 3023567 = 4535351) B4535351
theorem B2860073 : Blo 892572 2860073 := bstep (se 2 (by rfl) ⟨1072527, by rfl⟩ : syracuseStep 2860073 = 2145055) B2145055
theorem B894055 : Blo 892572 894055 := bstep (se 1 (by rfl) ⟨670541, by rfl⟩ : syracuseStep 894055 = 1341083) B1341083
theorem B268379257 : Blo 892572 268379257 := bstep (se 2 (by rfl) ⟨100642221, by rfl⟩ : syracuseStep 268379257 = 201284443) B201284443
theorem B17212783 : Blo 892572 17212783 := bstep (se 1 (by rfl) ⟨12909587, by rfl⟩ : syracuseStep 17212783 = 25819175) B25819175
theorem B3024539 : Blo 892572 3024539 := bstep (se 1 (by rfl) ⟨2268404, by rfl⟩ : syracuseStep 3024539 = 4536809) B4536809
theorem B2009159 : Blo 892572 2009159 := bstep (se 1 (by rfl) ⟨1506869, by rfl⟩ : syracuseStep 2009159 = 3013739) B3013739
theorem B895103 : Blo 892572 895103 := bstep (se 1 (by rfl) ⟨671327, by rfl⟩ : syracuseStep 895103 = 1342655) B1342655
theorem B4074151 : Blo 892572 4074151 := bstep (se 1 (by rfl) ⟨3055613, by rfl⟩ : syracuseStep 4074151 = 6111227) B6111227
theorem B58927823 : Blo 892572 58927823 := bstep (se 1 (by rfl) ⟨44195867, by rfl⟩ : syracuseStep 58927823 = 88391735) B88391735
theorem B895727 : Blo 892572 895727 := bstep (se 1 (by rfl) ⟨671795, by rfl⟩ : syracuseStep 895727 = 1343591) B1343591
theorem B11610971 : Blo 892572 11610971 := bstep (se 1 (by rfl) ⟨8708228, by rfl⟩ : syracuseStep 11610971 = 17416457) B17416457
theorem B7647119 : Blo 892572 7647119 := bstep (se 1 (by rfl) ⟨5735339, by rfl⟩ : syracuseStep 7647119 = 11470679) B11470679
theorem B2011553 : Blo 892572 2011553 := bstep (se 2 (by rfl) ⟨754332, by rfl⟩ : syracuseStep 2011553 = 1508665) B1508665
theorem B1913959 : Blo 892572 1913959 := bstep (se 1 (by rfl) ⟨1435469, by rfl⟩ : syracuseStep 1913959 = 2870939) B2870939
theorem B2013857 : Blo 892572 2013857 := bstep (se 2 (by rfl) ⟨755196, by rfl⟩ : syracuseStep 2013857 = 1510393) B1510393
theorem B2014073 : Blo 892572 2014073 := bstep (se 2 (by rfl) ⟨755277, by rfl⟩ : syracuseStep 2014073 = 1510555) B1510555
theorem B1129727 : Blo 892572 1129727 := bstep (se 1 (by rfl) ⟨847295, by rfl⟩ : syracuseStep 1129727 = 1694591) B1694591
theorem B2015657 : Blo 892572 2015657 := bstep (se 2 (by rfl) ⟨755871, by rfl⟩ : syracuseStep 2015657 = 1511743) B1511743
theorem B4081103 : Blo 892572 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B2016809 : Blo 892572 2016809 := bstep (se 2 (by rfl) ⟨756303, by rfl⟩ : syracuseStep 2016809 = 1512607) B1512607
theorem B24465149 : Blo 892572 24465149 := bstep (se 3 (by rfl) ⟨4587215, by rfl⟩ : syracuseStep 24465149 = 9174431) B9174431
theorem B9654821 : Blo 892572 9654821 := bstep (se 4 (by rfl) ⟨905139, by rfl⟩ : syracuseStep 9654821 = 1810279) B1810279
theorem B1004647 : Blo 892572 1004647 := bstep (se 1 (by rfl) ⟨753485, by rfl⟩ : syracuseStep 1004647 = 1506971) B1506971
theorem B7263695 : Blo 892572 7263695 := bstep (se 1 (by rfl) ⟨5447771, by rfl⟩ : syracuseStep 7263695 = 10895543) B10895543
theorem B2151983 : Blo 892572 2151983 := bstep (se 1 (by rfl) ⟨1613987, by rfl⟩ : syracuseStep 2151983 = 3227975) B3227975
theorem B1005727 : Blo 892572 1005727 := bstep (se 1 (by rfl) ⟨754295, by rfl⟩ : syracuseStep 1005727 = 1508591) B1508591
theorem B1006015 : Blo 892572 1006015 := bstep (se 1 (by rfl) ⟨754511, by rfl⟩ : syracuseStep 1006015 = 1509023) B1509023
theorem B1695487 : Blo 892572 1695487 := bstep (se 1 (by rfl) ⟨1271615, by rfl⟩ : syracuseStep 1695487 = 2543231) B2543231
theorem B2417435 : Blo 892572 2417435 := bstep (se 1 (by rfl) ⟨1813076, by rfl⟩ : syracuseStep 2417435 = 3626153) B3626153
theorem B8152787 : Blo 892572 8152787 := bstep (se 1 (by rfl) ⟨6114590, by rfl⟩ : syracuseStep 8152787 = 12229181) B12229181
theorem B4581143 : Blo 892572 4581143 := bstep (se 1 (by rfl) ⟨3435857, by rfl⟩ : syracuseStep 4581143 = 6871715) B6871715
theorem B7859429 : Blo 892572 7859429 := bstep (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) B1473643
theorem B1339559 : Blo 892572 1339559 := bstep (se 1 (by rfl) ⟨1004669, by rfl⟩ : syracuseStep 1339559 = 2009339) B2009339
theorem B1339883 : Blo 892572 1339883 := bstep (se 1 (by rfl) ⟨1004912, by rfl⟩ : syracuseStep 1339883 = 2009825) B2009825
theorem B4911707 : Blo 892572 4911707 := bstep (se 1 (by rfl) ⟨3683780, by rfl⟩ : syracuseStep 4911707 = 7367561) B7367561
theorem B75625163 : Blo 892572 75625163 := bstep (se 1 (by rfl) ⟨56718872, by rfl⟩ : syracuseStep 75625163 = 113437745) B113437745
theorem B1340159 : Blo 892572 1340159 := bstep (se 1 (by rfl) ⟨1005119, by rfl⟩ : syracuseStep 1340159 = 2010239) B2010239
theorem B4846547 : Blo 892572 4846547 := bstep (se 1 (by rfl) ⟨3634910, by rfl⟩ : syracuseStep 4846547 = 7269821) B7269821
theorem B1340699 : Blo 892572 1340699 := bstep (se 1 (by rfl) ⟨1005524, by rfl⟩ : syracuseStep 1340699 = 2011049) B2011049
theorem B1210015 : Blo 892572 1210015 := bstep (se 1 (by rfl) ⟨907511, by rfl⟩ : syracuseStep 1210015 = 1815023) B1815023
theorem B16545647 : Blo 892572 16545647 := bstep (se 1 (by rfl) ⟨12409235, by rfl⟩ : syracuseStep 16545647 = 24818471) B24818471
theorem B8616233 : Blo 892572 8616233 := bstep (se 2 (by rfl) ⟨3231087, by rfl⟩ : syracuseStep 8616233 = 6462175) B6462175
theorem B4291127 : Blo 892572 4291127 := bstep (se 1 (by rfl) ⟨3218345, by rfl⟩ : syracuseStep 4291127 = 6436691) B6436691
theorem B25787807 : Blo 892572 25787807 := bstep (se 1 (by rfl) ⟨19340855, by rfl⟩ : syracuseStep 25787807 = 38681711) B38681711
theorem B1343771 : Blo 892572 1343771 := bstep (se 1 (by rfl) ⟨1007828, by rfl⟩ : syracuseStep 1343771 = 2015657) B2015657
theorem B3015251 : Blo 892572 3015251 := bstep (se 1 (by rfl) ⟨2261438, by rfl⟩ : syracuseStep 3015251 = 4522877) B4522877
theorem B2720735 : Blo 892572 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B1344539 : Blo 892572 1344539 := bstep (se 1 (by rfl) ⟨1008404, by rfl⟩ : syracuseStep 1344539 = 2016809) B2016809
theorem B3020543 : Blo 892572 3020543 := bstep (se 1 (by rfl) ⟨2265407, by rfl⟩ : syracuseStep 3020543 = 4530815) B4530815
theorem B1611623 : Blo 892572 1611623 := bstep (se 1 (by rfl) ⟨1208717, by rfl⟩ : syracuseStep 1611623 = 2417435) B2417435
theorem B1906715 : Blo 892572 1906715 := bstep (se 1 (by rfl) ⟨1430036, by rfl⟩ : syracuseStep 1906715 = 2860073) B2860073
theorem B22976621 : Blo 892572 22976621 := bstep (se 3 (by rfl) ⟨4308116, by rfl⟩ : syracuseStep 22976621 = 8616233) B8616233
theorem B3054095 : Blo 892572 3054095 := bstep (se 1 (by rfl) ⟨2290571, by rfl⟩ : syracuseStep 3054095 = 4581143) B4581143
theorem B7740647 : Blo 892572 7740647 := bstep (se 1 (by rfl) ⟨5805485, by rfl⟩ : syracuseStep 7740647 = 11610971) B11610971
theorem B1613353 : Blo 892572 1613353 := bstep (se 2 (by rfl) ⟨605007, by rfl⟩ : syracuseStep 1613353 = 1210015) B1210015
theorem B893039 : Blo 892572 893039 := bstep (se 1 (by rfl) ⟨669779, by rfl⟩ : syracuseStep 893039 = 1339559) B1339559
theorem B893255 : Blo 892572 893255 := bstep (se 1 (by rfl) ⟨669941, by rfl⟩ : syracuseStep 893255 = 1339883) B1339883
theorem B893439 : Blo 892572 893439 := bstep (se 1 (by rfl) ⟨670079, by rfl⟩ : syracuseStep 893439 = 1340159) B1340159
theorem B893799 : Blo 892572 893799 := bstep (se 1 (by rfl) ⟨670349, by rfl⟩ : syracuseStep 893799 = 1340699) B1340699
theorem B2860751 : Blo 892572 2860751 := bstep (se 1 (by rfl) ⟨2145563, by rfl⟩ : syracuseStep 2860751 = 4291127) B4291127
theorem B896091 : Blo 892572 896091 := bstep (se 1 (by rfl) ⟨672068, by rfl⟩ : syracuseStep 896091 = 1344137) B1344137
theorem B896103 : Blo 892572 896103 := bstep (se 1 (by rfl) ⟨672077, by rfl⟩ : syracuseStep 896103 = 1344155) B1344155
theorem B2010527 : Blo 892572 2010527 := bstep (se 1 (by rfl) ⟨1507895, by rfl⟩ : syracuseStep 2010527 = 3015791) B3015791
theorem B73313947 : Blo 892572 73313947 := bstep (se 1 (by rfl) ⟨54985460, by rfl⟩ : syracuseStep 73313947 = 109970921) B109970921
theorem B357839009 : Blo 892572 357839009 := bstep (se 2 (by rfl) ⟨134189628, by rfl⟩ : syracuseStep 357839009 = 268379257) B268379257
theorem B22950377 : Blo 892572 22950377 := bstep (se 2 (by rfl) ⟨8606391, by rfl⟩ : syracuseStep 22950377 = 17212783) B17212783
theorem B6436547 : Blo 892572 6436547 := bstep (se 1 (by rfl) ⟨4827410, by rfl⟩ : syracuseStep 6436547 = 9654821) B9654821
theorem B19380647 : Blo 892572 19380647 := bstep (se 1 (by rfl) ⟨14535485, by rfl⟩ : syracuseStep 19380647 = 29070971) B29070971
theorem B25737983 : Blo 892572 25737983 := bstep (se 1 (by rfl) ⟨19303487, by rfl⟩ : syracuseStep 25737983 = 38606975) B38606975
theorem B2015711 : Blo 892572 2015711 := bstep (se 1 (by rfl) ⟨1511783, by rfl⟩ : syracuseStep 2015711 = 3023567) B3023567
theorem B2016359 : Blo 892572 2016359 := bstep (se 1 (by rfl) ⟨1512269, by rfl⟩ : syracuseStep 2016359 = 3024539) B3024539
theorem B5098079 : Blo 892572 5098079 := bstep (se 1 (by rfl) ⟨3823559, by rfl⟩ : syracuseStep 5098079 = 7647119) B7647119
theorem B50416775 : Blo 892572 50416775 := bstep (se 1 (by rfl) ⟨37812581, by rfl⟩ : syracuseStep 50416775 = 75625163) B75625163
theorem B3231031 : Blo 892572 3231031 := bstep (se 1 (by rfl) ⟨2423273, by rfl⟩ : syracuseStep 3231031 = 4846547) B4846547
theorem B11030431 : Blo 892572 11030431 := bstep (se 1 (by rfl) ⟨8272823, by rfl⟩ : syracuseStep 11030431 = 16545647) B16545647
theorem B17191871 : Blo 892572 17191871 := bstep (se 1 (by rfl) ⟨12893903, by rfl⟩ : syracuseStep 17191871 = 25787807) B25787807
theorem B16310099 : Blo 892572 16310099 := bstep (se 1 (by rfl) ⟨12232574, by rfl⟩ : syracuseStep 16310099 = 24465149) B24465149
theorem B5432201 : Blo 892572 5432201 := bstep (se 2 (by rfl) ⟨2037075, by rfl⟩ : syracuseStep 5432201 = 4074151) B4074151
theorem B4842463 : Blo 892572 4842463 := bstep (se 1 (by rfl) ⟨3631847, by rfl⟩ : syracuseStep 4842463 = 7263695) B7263695
theorem B1434655 : Blo 892572 1434655 := bstep (se 1 (by rfl) ⟨1075991, by rfl⟩ : syracuseStep 1434655 = 2151983) B2151983
theorem B12215879 : Blo 892572 12215879 := bstep (se 1 (by rfl) ⟨9161909, by rfl⟩ : syracuseStep 12215879 = 18323819) B18323819
theorem B10315511 : Blo 892572 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B5435191 : Blo 892572 5435191 := bstep (se 1 (by rfl) ⟨4076393, by rfl⟩ : syracuseStep 5435191 = 8152787) B8152787
theorem B1339439 : Blo 892572 1339439 := bstep (se 1 (by rfl) ⟨1004579, by rfl⟩ : syracuseStep 1339439 = 2009159) B2009159
theorem B1339529 : Blo 892572 1339529 := bstep (se 2 (by rfl) ⟨502323, by rfl⟩ : syracuseStep 1339529 = 1004647) B1004647
theorem B2551945 : Blo 892572 2551945 := bstep (se 2 (by rfl) ⟨956979, by rfl⟩ : syracuseStep 2551945 = 1913959) B1913959
theorem B39285215 : Blo 892572 39285215 := bstep (se 1 (by rfl) ⟨29463911, by rfl⟩ : syracuseStep 39285215 = 58927823) B58927823
theorem B5239619 : Blo 892572 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B1340969 : Blo 892572 1340969 := bstep (se 2 (by rfl) ⟨502863, by rfl⟩ : syracuseStep 1340969 = 1005727) B1005727
theorem B1341035 : Blo 892572 1341035 := bstep (se 1 (by rfl) ⟨1005776, by rfl⟩ : syracuseStep 1341035 = 2011553) B2011553
theorem B3274471 : Blo 892572 3274471 := bstep (se 1 (by rfl) ⟨2455853, by rfl⟩ : syracuseStep 3274471 = 4911707) B4911707
theorem B1341353 : Blo 892572 1341353 := bstep (se 2 (by rfl) ⟨503007, by rfl⟩ : syracuseStep 1341353 = 1006015) B1006015
theorem B3012605 : Blo 892572 3012605 := bstep (se 3 (by rfl) ⟨564863, by rfl⟩ : syracuseStep 3012605 = 1129727) B1129727
theorem B1342571 : Blo 892572 1342571 := bstep (se 1 (by rfl) ⟨1006928, by rfl⟩ : syracuseStep 1342571 = 2013857) B2013857
theorem B10189961 : Blo 892572 10189961 := bstep (se 2 (by rfl) ⟨3821235, by rfl⟩ : syracuseStep 10189961 = 7642471) B7642471
theorem B1342715 : Blo 892572 1342715 := bstep (se 1 (by rfl) ⟨1007036, by rfl⟩ : syracuseStep 1342715 = 2014073) B2014073
theorem B2260649 : Blo 892572 2260649 := bstep (se 2 (by rfl) ⟨847743, by rfl⟩ : syracuseStep 2260649 = 1695487) B1695487
theorem B1343807 : Blo 892572 1343807 := bstep (se 1 (by rfl) ⟨1007855, by rfl⟩ : syracuseStep 1343807 = 2015711) B2015711
theorem B1344239 : Blo 892572 1344239 := bstep (se 1 (by rfl) ⟨1008179, by rfl⟩ : syracuseStep 1344239 = 2016359) B2016359
theorem B6456617 : Blo 892572 6456617 := bstep (se 2 (by rfl) ⟨2421231, by rfl⟩ : syracuseStep 6456617 = 4842463) B4842463
theorem B2036063 : Blo 892572 2036063 := bstep (se 1 (by rfl) ⟨1527047, by rfl⟩ : syracuseStep 2036063 = 3054095) B3054095
theorem B97751929 : Blo 892572 97751929 := bstep (se 2 (by rfl) ⟨36656973, by rfl⟩ : syracuseStep 97751929 = 73313947) B73313947
theorem B4297661 : Blo 892572 4297661 := bstep (se 3 (by rfl) ⟨805811, by rfl⟩ : syracuseStep 4297661 = 1611623) B1611623
theorem B7246921 : Blo 892572 7246921 := bstep (se 2 (by rfl) ⟨2717595, by rfl⟩ : syracuseStep 7246921 = 5435191) B5435191
theorem B1907167 : Blo 892572 1907167 := bstep (se 1 (by rfl) ⟨1430375, by rfl⟩ : syracuseStep 1907167 = 2860751) B2860751
theorem B892959 : Blo 892572 892959 := bstep (se 1 (by rfl) ⟨669719, by rfl⟩ : syracuseStep 892959 = 1339439) B1339439
theorem B893019 : Blo 892572 893019 := bstep (se 1 (by rfl) ⟨669764, by rfl⟩ : syracuseStep 893019 = 1339529) B1339529
theorem B238559339 : Blo 892572 238559339 := bstep (se 1 (by rfl) ⟨178919504, by rfl⟩ : syracuseStep 238559339 = 357839009) B357839009
theorem B26190143 : Blo 892572 26190143 := bstep (se 1 (by rfl) ⟨19642607, by rfl⟩ : syracuseStep 26190143 = 39285215) B39285215
theorem B893979 : Blo 892572 893979 := bstep (se 1 (by rfl) ⟨670484, by rfl⟩ : syracuseStep 893979 = 1340969) B1340969
theorem B894023 : Blo 892572 894023 := bstep (se 1 (by rfl) ⟨670517, by rfl⟩ : syracuseStep 894023 = 1341035) B1341035
theorem B894235 : Blo 892572 894235 := bstep (se 1 (by rfl) ⟨670676, by rfl⟩ : syracuseStep 894235 = 1341353) B1341353
theorem B2008403 : Blo 892572 2008403 := bstep (se 1 (by rfl) ⟨1506302, by rfl⟩ : syracuseStep 2008403 = 3012605) B3012605
theorem B12920431 : Blo 892572 12920431 := bstep (se 1 (by rfl) ⟨9690323, by rfl⟩ : syracuseStep 12920431 = 19380647) B19380647
theorem B895047 : Blo 892572 895047 := bstep (se 1 (by rfl) ⟨671285, by rfl⟩ : syracuseStep 895047 = 1342571) B1342571
theorem B6793307 : Blo 892572 6793307 := bstep (se 1 (by rfl) ⟨5094980, by rfl⟩ : syracuseStep 6793307 = 10189961) B10189961
theorem B895143 : Blo 892572 895143 := bstep (se 1 (by rfl) ⟨671357, by rfl⟩ : syracuseStep 895143 = 1342715) B1342715
theorem B895847 : Blo 892572 895847 := bstep (se 1 (by rfl) ⟨671885, by rfl⟩ : syracuseStep 895847 = 1343771) B1343771
theorem B2010167 : Blo 892572 2010167 := bstep (se 1 (by rfl) ⟨1507625, by rfl⟩ : syracuseStep 2010167 = 3015251) B3015251
theorem B1813823 : Blo 892572 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B896359 : Blo 892572 896359 := bstep (se 1 (by rfl) ⟨672269, by rfl⟩ : syracuseStep 896359 = 1344539) B1344539
theorem B2013695 : Blo 892572 2013695 := bstep (se 1 (by rfl) ⟨1510271, by rfl⟩ : syracuseStep 2013695 = 3020543) B3020543
theorem B15317747 : Blo 892572 15317747 := bstep (se 1 (by rfl) ⟨11488310, by rfl⟩ : syracuseStep 15317747 = 22976621) B22976621
theorem B4308041 : Blo 892572 4308041 := bstep (se 2 (by rfl) ⟨1615515, by rfl⟩ : syracuseStep 4308041 = 3231031) B3231031
theorem B5160431 : Blo 892572 5160431 := bstep (se 1 (by rfl) ⟨3870323, by rfl⟩ : syracuseStep 5160431 = 7740647) B7740647
theorem B7651493 : Blo 892572 7651493 := bstep (se 4 (by rfl) ⟨717327, by rfl⟩ : syracuseStep 7651493 = 1434655) B1434655
theorem B3621467 : Blo 892572 3621467 := bstep (se 1 (by rfl) ⟨2716100, by rfl⟩ : syracuseStep 3621467 = 5432201) B5432201
theorem B8143919 : Blo 892572 8143919 := bstep (se 1 (by rfl) ⟨6107939, by rfl⟩ : syracuseStep 8143919 = 12215879) B12215879
theorem B3493079 : Blo 892572 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B17158655 : Blo 892572 17158655 := bstep (se 1 (by rfl) ⟨12868991, by rfl⟩ : syracuseStep 17158655 = 25737983) B25737983
theorem B2151137 : Blo 892572 2151137 := bstep (se 2 (by rfl) ⟨806676, by rfl⟩ : syracuseStep 2151137 = 1613353) B1613353
theorem B3398719 : Blo 892572 3398719 := bstep (se 1 (by rfl) ⟨2549039, by rfl⟩ : syracuseStep 3398719 = 5098079) B5098079
theorem B33611183 : Blo 892572 33611183 := bstep (se 1 (by rfl) ⟨25208387, by rfl⟩ : syracuseStep 33611183 = 50416775) B50416775
theorem B11461247 : Blo 892572 11461247 := bstep (se 1 (by rfl) ⟨8595935, by rfl⟩ : syracuseStep 11461247 = 17191871) B17191871
theorem B1271143 : Blo 892572 1271143 := bstep (se 1 (by rfl) ⟨953357, by rfl⟩ : syracuseStep 1271143 = 1906715) B1906715
theorem B14707241 : Blo 892572 14707241 := bstep (se 2 (by rfl) ⟨5515215, by rfl⟩ : syracuseStep 14707241 = 11030431) B11030431
theorem B10873399 : Blo 892572 10873399 := bstep (se 1 (by rfl) ⟨8155049, by rfl⟩ : syracuseStep 10873399 = 16310099) B16310099
theorem B3402593 : Blo 892572 3402593 := bstep (se 2 (by rfl) ⟨1275972, by rfl⟩ : syracuseStep 3402593 = 2551945) B2551945
theorem B6877007 : Blo 892572 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B1340351 : Blo 892572 1340351 := bstep (se 1 (by rfl) ⟨1005263, by rfl⟩ : syracuseStep 1340351 = 2010527) B2010527
theorem B15300251 : Blo 892572 15300251 := bstep (se 1 (by rfl) ⟨11475188, by rfl⟩ : syracuseStep 15300251 = 22950377) B22950377
theorem B4291031 : Blo 892572 4291031 := bstep (se 1 (by rfl) ⟨3218273, by rfl⟩ : syracuseStep 4291031 = 6436547) B6436547
theorem B17463845 : Blo 892572 17463845 := bstep (se 4 (by rfl) ⟨1637235, by rfl⟩ : syracuseStep 17463845 = 3274471) B3274471
theorem B1507099 : Blo 892572 1507099 := bstep (se 1 (by rfl) ⟨1130324, by rfl⟩ : syracuseStep 1507099 = 2260649) B2260649
theorem B5736365 : Blo 892572 5736365 := bstep (se 3 (by rfl) ⟨1075568, by rfl⟩ : syracuseStep 5736365 = 2151137) B2151137
theorem B37259509 : Blo 892572 37259509 := bstep (se 5 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 37259509 = 3493079) B3493079
theorem B11439103 : Blo 892572 11439103 := bstep (se 1 (by rfl) ⟨8579327, by rfl⟩ : syracuseStep 11439103 = 17158655) B17158655
theorem B7640831 : Blo 892572 7640831 := bstep (se 1 (by rfl) ⟨5730623, by rfl⟩ : syracuseStep 7640831 = 11461247) B11461247
theorem B4528871 : Blo 892572 4528871 := bstep (se 1 (by rfl) ⟨3396653, by rfl⟩ : syracuseStep 4528871 = 6793307) B6793307
theorem B9804827 : Blo 892572 9804827 := bstep (se 1 (by rfl) ⟨7353620, by rfl⟩ : syracuseStep 9804827 = 14707241) B14707241
theorem B2268395 : Blo 892572 2268395 := bstep (se 1 (by rfl) ⟨1701296, by rfl⟩ : syracuseStep 2268395 = 3402593) B3402593
theorem B893567 : Blo 892572 893567 := bstep (se 1 (by rfl) ⟨670175, by rfl⟩ : syracuseStep 893567 = 1340351) B1340351
theorem B10200167 : Blo 892572 10200167 := bstep (se 1 (by rfl) ⟨7650125, by rfl⟩ : syracuseStep 10200167 = 15300251) B15300251
theorem B4531625 : Blo 892572 4531625 := bstep (se 2 (by rfl) ⟨1699359, by rfl⟩ : syracuseStep 4531625 = 3398719) B3398719
theorem B2860687 : Blo 892572 2860687 := bstep (se 1 (by rfl) ⟨2145515, by rfl⟩ : syracuseStep 2860687 = 4291031) B4291031
theorem B11642563 : Blo 892572 11642563 := bstep (se 1 (by rfl) ⟨8731922, by rfl⟩ : syracuseStep 11642563 = 17463845) B17463845
theorem B2009465 : Blo 892572 2009465 := bstep (se 2 (by rfl) ⟨753549, by rfl⟩ : syracuseStep 2009465 = 1507099) B1507099
theorem B895871 : Blo 892572 895871 := bstep (se 1 (by rfl) ⟨671903, by rfl⟩ : syracuseStep 895871 = 1343807) B1343807
theorem B896159 : Blo 892572 896159 := bstep (se 1 (by rfl) ⟨672119, by rfl⟩ : syracuseStep 896159 = 1344239) B1344239
theorem B4304411 : Blo 892572 4304411 := bstep (se 1 (by rfl) ⟨3228308, by rfl⟩ : syracuseStep 4304411 = 6456617) B6456617
theorem B2865107 : Blo 892572 2865107 := bstep (se 1 (by rfl) ⟨2148830, by rfl⟩ : syracuseStep 2865107 = 4297661) B4297661
theorem B14497865 : Blo 892572 14497865 := bstep (se 2 (by rfl) ⟨5436699, by rfl⟩ : syracuseStep 14497865 = 10873399) B10873399
theorem B159039559 : Blo 892572 159039559 := bstep (se 1 (by rfl) ⟨119279669, by rfl⟩ : syracuseStep 159039559 = 238559339) B238559339
theorem B130335905 : Blo 892572 130335905 := bstep (se 2 (by rfl) ⟨48875964, by rfl⟩ : syracuseStep 130335905 = 97751929) B97751929
theorem B2542889 : Blo 892572 2542889 := bstep (se 2 (by rfl) ⟨953583, by rfl⟩ : syracuseStep 2542889 = 1907167) B1907167
theorem B10211831 : Blo 892572 10211831 := bstep (se 1 (by rfl) ⟨7658873, by rfl⟩ : syracuseStep 10211831 = 15317747) B15317747
theorem B2872027 : Blo 892572 2872027 := bstep (se 1 (by rfl) ⟨2154020, by rfl⟩ : syracuseStep 2872027 = 4308041) B4308041
theorem B5100995 : Blo 892572 5100995 := bstep (se 1 (by rfl) ⟨3825746, by rfl⟩ : syracuseStep 5100995 = 7651493) B7651493
theorem B5429279 : Blo 892572 5429279 := bstep (se 1 (by rfl) ⟨4071959, by rfl⟩ : syracuseStep 5429279 = 8143919) B8143919
theorem B5429501 : Blo 892572 5429501 := bstep (se 3 (by rfl) ⟨1018031, by rfl⟩ : syracuseStep 5429501 = 2036063) B2036063
theorem B9657245 : Blo 892572 9657245 := bstep (se 3 (by rfl) ⟨1810733, by rfl⟩ : syracuseStep 9657245 = 3621467) B3621467
theorem B1694857 : Blo 892572 1694857 := bstep (se 2 (by rfl) ⟨635571, by rfl⟩ : syracuseStep 1694857 = 1271143) B1271143
theorem B17227241 : Blo 892572 17227241 := bstep (se 2 (by rfl) ⟨6460215, by rfl⟩ : syracuseStep 17227241 = 12920431) B12920431
theorem B22407455 : Blo 892572 22407455 := bstep (se 1 (by rfl) ⟨16805591, by rfl⟩ : syracuseStep 22407455 = 33611183) B33611183
theorem B17460095 : Blo 892572 17460095 := bstep (se 1 (by rfl) ⟨13095071, by rfl⟩ : syracuseStep 17460095 = 26190143) B26190143
theorem B1338935 : Blo 892572 1338935 := bstep (se 1 (by rfl) ⟨1004201, by rfl⟩ : syracuseStep 1338935 = 2008403) B2008403
theorem B9662561 : Blo 892572 9662561 := bstep (se 2 (by rfl) ⟨3623460, by rfl⟩ : syracuseStep 9662561 = 7246921) B7246921
theorem B1340111 : Blo 892572 1340111 := bstep (se 1 (by rfl) ⟨1005083, by rfl⟩ : syracuseStep 1340111 = 2010167) B2010167
theorem B1209215 : Blo 892572 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B4584671 : Blo 892572 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B1342463 : Blo 892572 1342463 := bstep (se 1 (by rfl) ⟨1006847, by rfl⟩ : syracuseStep 1342463 = 2013695) B2013695
theorem B3440287 : Blo 892572 3440287 := bstep (se 1 (by rfl) ⟨2580215, by rfl⟩ : syracuseStep 3440287 = 5160431) B5160431
theorem B49679345 : Blo 892572 49679345 := bstep (se 2 (by rfl) ⟨18629754, by rfl⟩ : syracuseStep 49679345 = 37259509) B37259509
theorem B3019247 : Blo 892572 3019247 := bstep (se 1 (by rfl) ⟨2264435, by rfl⟩ : syracuseStep 3019247 = 4528871) B4528871
theorem B1512263 : Blo 892572 1512263 := bstep (se 1 (by rfl) ⟨1134197, by rfl⟩ : syracuseStep 1512263 = 2268395) B2268395
theorem B3021083 : Blo 892572 3021083 := bstep (se 1 (by rfl) ⟨2265812, by rfl⟩ : syracuseStep 3021083 = 4531625) B4531625
theorem B892623 : Blo 892572 892623 := bstep (se 1 (by rfl) ⟨669467, by rfl⟩ : syracuseStep 892623 = 1338935) B1338935
theorem B893407 : Blo 892572 893407 := bstep (se 1 (by rfl) ⟨670055, by rfl⟩ : syracuseStep 893407 = 1340111) B1340111
theorem B3056447 : Blo 892572 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B1910071 : Blo 892572 1910071 := bstep (se 1 (by rfl) ⟨1432553, by rfl⟩ : syracuseStep 1910071 = 2865107) B2865107
theorem B894975 : Blo 892572 894975 := bstep (se 1 (by rfl) ⟨671231, by rfl⟩ : syracuseStep 894975 = 1342463) B1342463
theorem B212052745 : Blo 892572 212052745 := bstep (se 2 (by rfl) ⟨79519779, by rfl⟩ : syracuseStep 212052745 = 159039559) B159039559
theorem B3814249 : Blo 892572 3814249 := bstep (se 2 (by rfl) ⟨1430343, by rfl⟩ : syracuseStep 3814249 = 2860687) B2860687
theorem B3224573 : Blo 892572 3224573 := bstep (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) B1209215
theorem B5093887 : Blo 892572 5093887 := bstep (se 1 (by rfl) ⟨3820415, by rfl⟩ : syracuseStep 5093887 = 7640831) B7640831
theorem B15252137 : Blo 892572 15252137 := bstep (se 2 (by rfl) ⟨5719551, by rfl⟩ : syracuseStep 15252137 = 11439103) B11439103
theorem B3619667 : Blo 892572 3619667 := bstep (se 1 (by rfl) ⟨2714750, by rfl⟩ : syracuseStep 3619667 = 5429501) B5429501
theorem B6438163 : Blo 892572 6438163 := bstep (se 1 (by rfl) ⟨4828622, by rfl⟩ : syracuseStep 6438163 = 9657245) B9657245
theorem B6536551 : Blo 892572 6536551 := bstep (se 1 (by rfl) ⟨4902413, by rfl⟩ : syracuseStep 6536551 = 9804827) B9804827
theorem B11484827 : Blo 892572 11484827 := bstep (se 1 (by rfl) ⟨8613620, by rfl⟩ : syracuseStep 11484827 = 17227241) B17227241
theorem B6800111 : Blo 892572 6800111 := bstep (se 1 (by rfl) ⟨5100083, by rfl⟩ : syracuseStep 6800111 = 10200167) B10200167
theorem B59753213 : Blo 892572 59753213 := bstep (se 3 (by rfl) ⟨11203727, by rfl⟩ : syracuseStep 59753213 = 22407455) B22407455
theorem B2869607 : Blo 892572 2869607 := bstep (se 1 (by rfl) ⟨2152205, by rfl⟩ : syracuseStep 2869607 = 4304411) B4304411
theorem B6441707 : Blo 892572 6441707 := bstep (se 1 (by rfl) ⟨4831280, by rfl⟩ : syracuseStep 6441707 = 9662561) B9662561
theorem B86890603 : Blo 892572 86890603 := bstep (se 1 (by rfl) ⟨65167952, by rfl⟩ : syracuseStep 86890603 = 130335905) B130335905
theorem B3824243 : Blo 892572 3824243 := bstep (se 1 (by rfl) ⟨2868182, by rfl⟩ : syracuseStep 3824243 = 5736365) B5736365
theorem B1695259 : Blo 892572 1695259 := bstep (se 1 (by rfl) ⟨1271444, by rfl⟩ : syracuseStep 1695259 = 2542889) B2542889
theorem B15523417 : Blo 892572 15523417 := bstep (se 2 (by rfl) ⟨5821281, by rfl⟩ : syracuseStep 15523417 = 11642563) B11642563
theorem B6807887 : Blo 892572 6807887 := bstep (se 1 (by rfl) ⟨5105915, by rfl⟩ : syracuseStep 6807887 = 10211831) B10211831
theorem B3400663 : Blo 892572 3400663 := bstep (se 1 (by rfl) ⟨2550497, by rfl⟩ : syracuseStep 3400663 = 5100995) B5100995
theorem B14478077 : Blo 892572 14478077 := bstep (se 3 (by rfl) ⟨2714639, by rfl⟩ : syracuseStep 14478077 = 5429279) B5429279
theorem B3829369 : Blo 892572 3829369 := bstep (se 2 (by rfl) ⟨1436013, by rfl⟩ : syracuseStep 3829369 = 2872027) B2872027
theorem B1339643 : Blo 892572 1339643 := bstep (se 1 (by rfl) ⟨1004732, by rfl⟩ : syracuseStep 1339643 = 2009465) B2009465
theorem B46560253 : Blo 892572 46560253 := bstep (se 3 (by rfl) ⟨8730047, by rfl⟩ : syracuseStep 46560253 = 17460095) B17460095
theorem B9665243 : Blo 892572 9665243 := bstep (se 1 (by rfl) ⟨7248932, by rfl⟩ : syracuseStep 9665243 = 14497865) B14497865
theorem B2259809 : Blo 892572 2259809 := bstep (se 2 (by rfl) ⟨847428, by rfl⟩ : syracuseStep 2259809 = 1694857) B1694857
theorem B4587049 : Blo 892572 4587049 := bstep (se 2 (by rfl) ⟨1720143, by rfl⟩ : syracuseStep 4587049 = 3440287) B3440287
theorem B4294471 : Blo 892572 4294471 := bstep (se 1 (by rfl) ⟨3220853, by rfl⟩ : syracuseStep 4294471 = 6441707) B6441707
theorem B2037631 : Blo 892572 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B5085665 : Blo 892572 5085665 := bstep (se 2 (by rfl) ⟨1907124, by rfl⟩ : syracuseStep 5085665 = 3814249) B3814249
theorem B893095 : Blo 892572 893095 := bstep (se 1 (by rfl) ⟨669821, by rfl⟩ : syracuseStep 893095 = 1339643) B1339643
theorem B6791849 : Blo 892572 6791849 := bstep (se 2 (by rfl) ⟨2546943, by rfl⟩ : syracuseStep 6791849 = 5093887) B5093887
theorem B10168091 : Blo 892572 10168091 := bstep (se 1 (by rfl) ⟨7626068, by rfl⟩ : syracuseStep 10168091 = 15252137) B15252137
theorem B4533407 : Blo 892572 4533407 := bstep (se 1 (by rfl) ⟨3400055, by rfl⟩ : syracuseStep 4533407 = 6800111) B6800111
theorem B4534217 : Blo 892572 4534217 := bstep (se 2 (by rfl) ⟨1700331, by rfl⟩ : syracuseStep 4534217 = 3400663) B3400663
theorem B1913071 : Blo 892572 1913071 := bstep (se 1 (by rfl) ⟨1434803, by rfl⟩ : syracuseStep 1913071 = 2869607) B2869607
theorem B2012831 : Blo 892572 2012831 := bstep (se 1 (by rfl) ⟨1509623, by rfl⟩ : syracuseStep 2012831 = 3019247) B3019247
theorem B282736993 : Blo 892572 282736993 := bstep (se 2 (by rfl) ⟨106026372, by rfl⟩ : syracuseStep 282736993 = 212052745) B212052745
theorem B2014055 : Blo 892572 2014055 := bstep (se 1 (by rfl) ⟨1510541, by rfl⟩ : syracuseStep 2014055 = 3021083) B3021083
theorem B4538591 : Blo 892572 4538591 := bstep (se 1 (by rfl) ⟨3403943, by rfl⟩ : syracuseStep 4538591 = 6807887) B6807887
theorem B62080337 : Blo 892572 62080337 := bstep (se 2 (by rfl) ⟨23280126, by rfl⟩ : syracuseStep 62080337 = 46560253) B46560253
theorem B9652051 : Blo 892572 9652051 := bstep (se 1 (by rfl) ⟨7239038, by rfl⟩ : syracuseStep 9652051 = 14478077) B14478077
theorem B115854137 : Blo 892572 115854137 := bstep (se 2 (by rfl) ⟨43445301, by rfl⟩ : syracuseStep 115854137 = 86890603) B86890603
theorem B24464261 : Blo 892572 24464261 := bstep (se 4 (by rfl) ⟨2293524, by rfl⟩ : syracuseStep 24464261 = 4587049) B4587049
theorem B2149715 : Blo 892572 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B6443495 : Blo 892572 6443495 := bstep (se 1 (by rfl) ⟨4832621, by rfl⟩ : syracuseStep 6443495 = 9665243) B9665243
theorem B2413111 : Blo 892572 2413111 := bstep (se 1 (by rfl) ⟨1809833, by rfl⟩ : syracuseStep 2413111 = 3619667) B3619667
theorem B20697889 : Blo 892572 20697889 := bstep (se 2 (by rfl) ⟨7761708, by rfl⟩ : syracuseStep 20697889 = 15523417) B15523417
theorem B7656551 : Blo 892572 7656551 := bstep (se 1 (by rfl) ⟨5742413, by rfl⟩ : syracuseStep 7656551 = 11484827) B11484827
theorem B39835475 : Blo 892572 39835475 := bstep (se 1 (by rfl) ⟨29876606, by rfl⟩ : syracuseStep 39835475 = 59753213) B59753213
theorem B33119563 : Blo 892572 33119563 := bstep (se 1 (by rfl) ⟨24839672, by rfl⟩ : syracuseStep 33119563 = 49679345) B49679345
theorem B1008175 : Blo 892572 1008175 := bstep (se 1 (by rfl) ⟨756131, by rfl⟩ : syracuseStep 1008175 = 1512263) B1512263
theorem B2549495 : Blo 892572 2549495 := bstep (se 1 (by rfl) ⟨1912121, by rfl⟩ : syracuseStep 2549495 = 3824243) B3824243
theorem B5105825 : Blo 892572 5105825 := bstep (se 2 (by rfl) ⟨1914684, by rfl⟩ : syracuseStep 5105825 = 3829369) B3829369
theorem B10187045 : Blo 892572 10187045 := bstep (se 4 (by rfl) ⟨955035, by rfl⟩ : syracuseStep 10187045 = 1910071) B1910071
theorem B8584217 : Blo 892572 8584217 := bstep (se 2 (by rfl) ⟨3219081, by rfl⟩ : syracuseStep 8584217 = 6438163) B6438163
theorem B8715401 : Blo 892572 8715401 := bstep (se 2 (by rfl) ⟨3268275, by rfl⟩ : syracuseStep 8715401 = 6536551) B6536551
theorem B1506539 : Blo 892572 1506539 := bstep (se 1 (by rfl) ⟨1129904, by rfl⟩ : syracuseStep 1506539 = 2259809) B2259809
theorem B2260345 : Blo 892572 2260345 := bstep (se 2 (by rfl) ⟨847629, by rfl⟩ : syracuseStep 2260345 = 1695259) B1695259
theorem B1344233 : Blo 892572 1344233 := bstep (se 2 (by rfl) ⟨504087, by rfl⟩ : syracuseStep 1344233 = 1008175) B1008175
theorem B41386891 : Blo 892572 41386891 := bstep (se 1 (by rfl) ⟨31040168, by rfl⟩ : syracuseStep 41386891 = 62080337) B62080337
theorem B77236091 : Blo 892572 77236091 := bstep (se 1 (by rfl) ⟨57927068, by rfl⟩ : syracuseStep 77236091 = 115854137) B115854137
theorem B4295663 : Blo 892572 4295663 := bstep (se 1 (by rfl) ⟨3221747, by rfl⟩ : syracuseStep 4295663 = 6443495) B6443495
theorem B4527899 : Blo 892572 4527899 := bstep (se 1 (by rfl) ⟨3395924, by rfl⟩ : syracuseStep 4527899 = 6791849) B6791849
theorem B3217481 : Blo 892572 3217481 := bstep (se 2 (by rfl) ⟨1206555, by rfl⟩ : syracuseStep 3217481 = 2413111) B2413111
theorem B27597185 : Blo 892572 27597185 := bstep (se 2 (by rfl) ⟨10348944, by rfl⟩ : syracuseStep 27597185 = 20697889) B20697889
theorem B3022271 : Blo 892572 3022271 := bstep (se 1 (by rfl) ⟨2266703, by rfl⟩ : syracuseStep 3022271 = 4533407) B4533407
theorem B3022811 : Blo 892572 3022811 := bstep (se 1 (by rfl) ⟨2267108, by rfl⟩ : syracuseStep 3022811 = 4534217) B4534217
theorem B6791363 : Blo 892572 6791363 := bstep (se 1 (by rfl) ⟨5093522, by rfl⟩ : syracuseStep 6791363 = 10187045) B10187045
theorem B5810267 : Blo 892572 5810267 := bstep (se 1 (by rfl) ⟨4357700, by rfl⟩ : syracuseStep 5810267 = 8715401) B8715401
theorem B3025727 : Blo 892572 3025727 := bstep (se 1 (by rfl) ⟨2269295, by rfl⟩ : syracuseStep 3025727 = 4538591) B4538591
theorem B26556983 : Blo 892572 26556983 := bstep (se 1 (by rfl) ⟨19917737, by rfl⟩ : syracuseStep 26556983 = 39835475) B39835475
theorem B3390443 : Blo 892572 3390443 := bstep (se 1 (by rfl) ⟨2542832, by rfl⟩ : syracuseStep 3390443 = 5085665) B5085665
theorem B6798653 : Blo 892572 6798653 := bstep (se 3 (by rfl) ⟨1274747, by rfl⟩ : syracuseStep 6798653 = 2549495) B2549495
theorem B376982657 : Blo 892572 376982657 := bstep (se 2 (by rfl) ⟨141368496, by rfl⟩ : syracuseStep 376982657 = 282736993) B282736993
theorem B44159417 : Blo 892572 44159417 := bstep (se 2 (by rfl) ⟨16559781, by rfl⟩ : syracuseStep 44159417 = 33119563) B33119563
theorem B5722811 : Blo 892572 5722811 := bstep (se 1 (by rfl) ⟨4292108, by rfl⟩ : syracuseStep 5722811 = 8584217) B8584217
theorem B1004359 : Blo 892572 1004359 := bstep (se 1 (by rfl) ⟨753269, by rfl⟩ : syracuseStep 1004359 = 1506539) B1506539
theorem B16309507 : Blo 892572 16309507 := bstep (se 1 (by rfl) ⟨12232130, by rfl⟩ : syracuseStep 16309507 = 24464261) B24464261
theorem B1433143 : Blo 892572 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B5725961 : Blo 892572 5725961 := bstep (se 2 (by rfl) ⟨2147235, by rfl⟩ : syracuseStep 5725961 = 4294471) B4294471
theorem B12869401 : Blo 892572 12869401 := bstep (se 2 (by rfl) ⟨4826025, by rfl⟩ : syracuseStep 12869401 = 9652051) B9652051
theorem B5104367 : Blo 892572 5104367 := bstep (se 1 (by rfl) ⟨3828275, by rfl⟩ : syracuseStep 5104367 = 7656551) B7656551
theorem B2550761 : Blo 892572 2550761 := bstep (se 2 (by rfl) ⟨956535, by rfl⟩ : syracuseStep 2550761 = 1913071) B1913071
theorem B6778727 : Blo 892572 6778727 := bstep (se 1 (by rfl) ⟨5084045, by rfl⟩ : syracuseStep 6778727 = 10168091) B10168091
theorem B3403883 : Blo 892572 3403883 := bstep (se 1 (by rfl) ⟨2552912, by rfl⟩ : syracuseStep 3403883 = 5105825) B5105825
theorem B2716841 : Blo 892572 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B1341887 : Blo 892572 1341887 := bstep (se 1 (by rfl) ⟨1006415, by rfl⟩ : syracuseStep 1341887 = 2012831) B2012831
theorem B3013793 : Blo 892572 3013793 := bstep (se 2 (by rfl) ⟨1130172, by rfl⟩ : syracuseStep 3013793 = 2260345) B2260345
theorem B1342703 : Blo 892572 1342703 := bstep (se 1 (by rfl) ⟨1007027, by rfl⟩ : syracuseStep 1342703 = 2014055) B2014055
theorem B55182521 : Blo 892572 55182521 := bstep (se 2 (by rfl) ⟨20693445, by rfl⟩ : syracuseStep 55182521 = 41386891) B41386891
theorem B7244909 : Blo 892572 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B3018599 : Blo 892572 3018599 := bstep (se 1 (by rfl) ⟨2263949, by rfl⟩ : syracuseStep 3018599 = 4527899) B4527899
theorem B4527575 : Blo 892572 4527575 := bstep (se 1 (by rfl) ⟨3395681, by rfl⟩ : syracuseStep 4527575 = 6791363) B6791363
theorem B3873511 : Blo 892572 3873511 := bstep (se 1 (by rfl) ⟨2905133, by rfl⟩ : syracuseStep 3873511 = 5810267) B5810267
theorem B2269255 : Blo 892572 2269255 := bstep (se 1 (by rfl) ⟨1701941, by rfl⟩ : syracuseStep 2269255 = 3403883) B3403883
theorem B7643429 : Blo 892572 7643429 := bstep (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) B1433143
theorem B894591 : Blo 892572 894591 := bstep (se 1 (by rfl) ⟨670943, by rfl⟩ : syracuseStep 894591 = 1341887) B1341887
theorem B17704655 : Blo 892572 17704655 := bstep (se 1 (by rfl) ⟨13278491, by rfl⟩ : syracuseStep 17704655 = 26556983) B26556983
theorem B2009195 : Blo 892572 2009195 := bstep (se 1 (by rfl) ⟨1506896, by rfl⟩ : syracuseStep 2009195 = 3013793) B3013793
theorem B895135 : Blo 892572 895135 := bstep (se 1 (by rfl) ⟨671351, by rfl⟩ : syracuseStep 895135 = 1342703) B1342703
theorem B4532435 : Blo 892572 4532435 := bstep (se 1 (by rfl) ⟨3399326, by rfl⟩ : syracuseStep 4532435 = 6798653) B6798653
theorem B896155 : Blo 892572 896155 := bstep (se 1 (by rfl) ⟨672116, by rfl⟩ : syracuseStep 896155 = 1344233) B1344233
theorem B51490727 : Blo 892572 51490727 := bstep (se 1 (by rfl) ⟨38618045, by rfl⟩ : syracuseStep 51490727 = 77236091) B77236091
theorem B2863775 : Blo 892572 2863775 := bstep (se 1 (by rfl) ⟨2147831, by rfl⟩ : syracuseStep 2863775 = 4295663) B4295663
theorem B29439611 : Blo 892572 29439611 := bstep (se 1 (by rfl) ⟨22079708, by rfl⟩ : syracuseStep 29439611 = 44159417) B44159417
theorem B3815207 : Blo 892572 3815207 := bstep (se 1 (by rfl) ⟨2861405, by rfl⟩ : syracuseStep 3815207 = 5722811) B5722811
theorem B2144987 : Blo 892572 2144987 := bstep (se 1 (by rfl) ⟨1608740, by rfl⟩ : syracuseStep 2144987 = 3217481) B3217481
theorem B18398123 : Blo 892572 18398123 := bstep (se 1 (by rfl) ⟨13798592, by rfl⟩ : syracuseStep 18398123 = 27597185) B27597185
theorem B2014847 : Blo 892572 2014847 := bstep (se 1 (by rfl) ⟨1511135, by rfl⟩ : syracuseStep 2014847 = 3022271) B3022271
theorem B3817307 : Blo 892572 3817307 := bstep (se 1 (by rfl) ⟨2862980, by rfl⟩ : syracuseStep 3817307 = 5725961) B5725961
theorem B2015207 : Blo 892572 2015207 := bstep (se 1 (by rfl) ⟨1511405, by rfl⟩ : syracuseStep 2015207 = 3022811) B3022811
theorem B2017151 : Blo 892572 2017151 := bstep (se 1 (by rfl) ⟨1512863, by rfl⟩ : syracuseStep 2017151 = 3025727) B3025727
theorem B21746009 : Blo 892572 21746009 := bstep (se 2 (by rfl) ⟨8154753, by rfl⟩ : syracuseStep 21746009 = 16309507) B16309507
theorem B17159201 : Blo 892572 17159201 := bstep (se 2 (by rfl) ⟨6434700, by rfl⟩ : syracuseStep 17159201 = 12869401) B12869401
theorem B251321771 : Blo 892572 251321771 := bstep (se 1 (by rfl) ⟨188491328, by rfl⟩ : syracuseStep 251321771 = 376982657) B376982657
theorem B3402911 : Blo 892572 3402911 := bstep (se 1 (by rfl) ⟨2552183, by rfl⟩ : syracuseStep 3402911 = 5104367) B5104367
theorem B1339145 : Blo 892572 1339145 := bstep (se 2 (by rfl) ⟨502179, by rfl⟩ : syracuseStep 1339145 = 1004359) B1004359
theorem B1700507 : Blo 892572 1700507 := bstep (se 1 (by rfl) ⟨1275380, by rfl⟩ : syracuseStep 1700507 = 2550761) B2550761
theorem B4519151 : Blo 892572 4519151 := bstep (se 1 (by rfl) ⟨3389363, by rfl⟩ : syracuseStep 4519151 = 6778727) B6778727
theorem B2260295 : Blo 892572 2260295 := bstep (se 1 (by rfl) ⟨1695221, by rfl⟩ : syracuseStep 2260295 = 3390443) B3390443
theorem B1344767 : Blo 892572 1344767 := bstep (se 1 (by rfl) ⟨1008575, by rfl⟩ : syracuseStep 1344767 = 2017151) B2017151
theorem B11439467 : Blo 892572 11439467 := bstep (se 1 (by rfl) ⟨8579600, by rfl⟩ : syracuseStep 11439467 = 17159201) B17159201
theorem B3018383 : Blo 892572 3018383 := bstep (se 1 (by rfl) ⟨2263787, by rfl⟩ : syracuseStep 3018383 = 4527575) B4527575
theorem B167547847 : Blo 892572 167547847 := bstep (se 1 (by rfl) ⟨125660885, by rfl⟩ : syracuseStep 167547847 = 251321771) B251321771
theorem B11803103 : Blo 892572 11803103 := bstep (se 1 (by rfl) ⟨8852327, by rfl⟩ : syracuseStep 11803103 = 17704655) B17704655
theorem B3021623 : Blo 892572 3021623 := bstep (se 1 (by rfl) ⟨2266217, by rfl⟩ : syracuseStep 3021623 = 4532435) B4532435
theorem B2268607 : Blo 892572 2268607 := bstep (se 1 (by rfl) ⟨1701455, by rfl⟩ : syracuseStep 2268607 = 3402911) B3402911
theorem B892763 : Blo 892572 892763 := bstep (se 1 (by rfl) ⟨669572, by rfl⟩ : syracuseStep 892763 = 1339145) B1339145
theorem B1909183 : Blo 892572 1909183 := bstep (se 1 (by rfl) ⟨1431887, by rfl⟩ : syracuseStep 1909183 = 2863775) B2863775
theorem B12265415 : Blo 892572 12265415 := bstep (se 1 (by rfl) ⟨9199061, by rfl⟩ : syracuseStep 12265415 = 18398123) B18398123
theorem B3025673 : Blo 892572 3025673 := bstep (se 2 (by rfl) ⟨1134627, by rfl⟩ : syracuseStep 3025673 = 2269255) B2269255
theorem B4829939 : Blo 892572 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B2012399 : Blo 892572 2012399 := bstep (se 1 (by rfl) ⟨1509299, by rfl⟩ : syracuseStep 2012399 = 3018599) B3018599
theorem B14497339 : Blo 892572 14497339 := bstep (se 1 (by rfl) ⟨10873004, by rfl⟩ : syracuseStep 14497339 = 21746009) B21746009
theorem B5095619 : Blo 892572 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B34327151 : Blo 892572 34327151 := bstep (se 1 (by rfl) ⟨25745363, by rfl⟩ : syracuseStep 34327151 = 51490727) B51490727
theorem B1133671 : Blo 892572 1133671 := bstep (se 1 (by rfl) ⟨850253, by rfl⟩ : syracuseStep 1133671 = 1700507) B1700507
theorem B5164681 : Blo 892572 5164681 := bstep (se 2 (by rfl) ⟨1936755, by rfl⟩ : syracuseStep 5164681 = 3873511) B3873511
theorem B2543471 : Blo 892572 2543471 := bstep (se 1 (by rfl) ⟨1907603, by rfl⟩ : syracuseStep 2543471 = 3815207) B3815207
theorem B1429991 : Blo 892572 1429991 := bstep (se 1 (by rfl) ⟨1072493, by rfl⟩ : syracuseStep 1429991 = 2144987) B2144987
theorem B2544871 : Blo 892572 2544871 := bstep (se 1 (by rfl) ⟨1908653, by rfl⟩ : syracuseStep 2544871 = 3817307) B3817307
theorem B36788347 : Blo 892572 36788347 := bstep (se 1 (by rfl) ⟨27591260, by rfl⟩ : syracuseStep 36788347 = 55182521) B55182521
theorem B1339463 : Blo 892572 1339463 := bstep (se 1 (by rfl) ⟨1004597, by rfl⟩ : syracuseStep 1339463 = 2009195) B2009195
theorem B3012767 : Blo 892572 3012767 := bstep (se 1 (by rfl) ⟨2259575, by rfl⟩ : syracuseStep 3012767 = 4519151) B4519151
theorem B19626407 : Blo 892572 19626407 := bstep (se 1 (by rfl) ⟨14719805, by rfl⟩ : syracuseStep 19626407 = 29439611) B29439611
theorem B1506863 : Blo 892572 1506863 := bstep (se 1 (by rfl) ⟨1130147, by rfl⟩ : syracuseStep 1506863 = 2260295) B2260295
theorem B1343231 : Blo 892572 1343231 := bstep (se 1 (by rfl) ⟨1007423, by rfl⟩ : syracuseStep 1343231 = 2014847) B2014847
theorem B1343471 : Blo 892572 1343471 := bstep (se 1 (by rfl) ⟨1007603, by rfl⟩ : syracuseStep 1343471 = 2015207) B2015207
theorem B953327 : Blo 892572 953327 := bstep (se 1 (by rfl) ⟨714995, by rfl⟩ : syracuseStep 953327 = 1429991) B1429991
theorem B1511561 : Blo 892572 1511561 := bstep (se 2 (by rfl) ⟨566835, by rfl⟩ : syracuseStep 1511561 = 1133671) B1133671
theorem B7868735 : Blo 892572 7868735 := bstep (se 1 (by rfl) ⟨5901551, by rfl⟩ : syracuseStep 7868735 = 11803103) B11803103
theorem B6886241 : Blo 892572 6886241 := bstep (se 2 (by rfl) ⟨2582340, by rfl⟩ : syracuseStep 6886241 = 5164681) B5164681
theorem B892975 : Blo 892572 892975 := bstep (se 1 (by rfl) ⟨669731, by rfl⟩ : syracuseStep 892975 = 1339463) B1339463
theorem B3219959 : Blo 892572 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B2008511 : Blo 892572 2008511 := bstep (se 1 (by rfl) ⟨1506383, by rfl⟩ : syracuseStep 2008511 = 3012767) B3012767
theorem B13084271 : Blo 892572 13084271 := bstep (se 1 (by rfl) ⟨9813203, by rfl⟩ : syracuseStep 13084271 = 19626407) B19626407
theorem B3024809 : Blo 892572 3024809 := bstep (se 2 (by rfl) ⟨1134303, by rfl⟩ : syracuseStep 3024809 = 2268607) B2268607
theorem B895487 : Blo 892572 895487 := bstep (se 1 (by rfl) ⟨671615, by rfl⟩ : syracuseStep 895487 = 1343231) B1343231
theorem B895647 : Blo 892572 895647 := bstep (se 1 (by rfl) ⟨671735, by rfl⟩ : syracuseStep 895647 = 1343471) B1343471
theorem B896511 : Blo 892572 896511 := bstep (se 1 (by rfl) ⟨672383, by rfl⟩ : syracuseStep 896511 = 1344767) B1344767
theorem B22884767 : Blo 892572 22884767 := bstep (se 1 (by rfl) ⟨17163575, by rfl⟩ : syracuseStep 22884767 = 34327151) B34327151
theorem B2012255 : Blo 892572 2012255 := bstep (se 1 (by rfl) ⟨1509191, by rfl⟩ : syracuseStep 2012255 = 3018383) B3018383
theorem B2014415 : Blo 892572 2014415 := bstep (se 1 (by rfl) ⟨1510811, by rfl⟩ : syracuseStep 2014415 = 3021623) B3021623
theorem B223397129 : Blo 892572 223397129 := bstep (se 2 (by rfl) ⟨83773923, by rfl⟩ : syracuseStep 223397129 = 167547847) B167547847
theorem B8176943 : Blo 892572 8176943 := bstep (se 1 (by rfl) ⟨6132707, by rfl⟩ : syracuseStep 8176943 = 12265415) B12265415
theorem B3393161 : Blo 892572 3393161 := bstep (se 2 (by rfl) ⟨1272435, by rfl⟩ : syracuseStep 3393161 = 2544871) B2544871
theorem B2017115 : Blo 892572 2017115 := bstep (se 1 (by rfl) ⟨1512836, by rfl⟩ : syracuseStep 2017115 = 3025673) B3025673
theorem B1004575 : Blo 892572 1004575 := bstep (se 1 (by rfl) ⟨753431, by rfl⟩ : syracuseStep 1004575 = 1506863) B1506863
theorem B3397079 : Blo 892572 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B2545577 : Blo 892572 2545577 := bstep (se 2 (by rfl) ⟨954591, by rfl⟩ : syracuseStep 2545577 = 1909183) B1909183
theorem B7626311 : Blo 892572 7626311 := bstep (se 1 (by rfl) ⟨5719733, by rfl⟩ : syracuseStep 7626311 = 11439467) B11439467
theorem B1695647 : Blo 892572 1695647 := bstep (se 1 (by rfl) ⟨1271735, by rfl⟩ : syracuseStep 1695647 = 2543471) B2543471
theorem B19329785 : Blo 892572 19329785 := bstep (se 2 (by rfl) ⟨7248669, by rfl⟩ : syracuseStep 19329785 = 14497339) B14497339
theorem B49051129 : Blo 892572 49051129 := bstep (se 2 (by rfl) ⟨18394173, by rfl⟩ : syracuseStep 49051129 = 36788347) B36788347
theorem B1341599 : Blo 892572 1341599 := bstep (se 1 (by rfl) ⟨1006199, by rfl⟩ : syracuseStep 1341599 = 2012399) B2012399
theorem B148931419 : Blo 892572 148931419 := bstep (se 1 (by rfl) ⟨111698564, by rfl⟩ : syracuseStep 148931419 = 223397129) B223397129
theorem B2262107 : Blo 892572 2262107 := bstep (se 1 (by rfl) ⟨1696580, by rfl⟩ : syracuseStep 2262107 = 3393161) B3393161
theorem B1344743 : Blo 892572 1344743 := bstep (se 1 (by rfl) ⟨1008557, by rfl⟩ : syracuseStep 1344743 = 2017115) B2017115
theorem B8586557 : Blo 892572 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B5245823 : Blo 892572 5245823 := bstep (se 1 (by rfl) ⟨3934367, by rfl⟩ : syracuseStep 5245823 = 7868735) B7868735
theorem B4590827 : Blo 892572 4590827 := bstep (se 1 (by rfl) ⟨3443120, by rfl⟩ : syracuseStep 4590827 = 6886241) B6886241
theorem B2264719 : Blo 892572 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B5084207 : Blo 892572 5084207 := bstep (se 1 (by rfl) ⟨3813155, by rfl⟩ : syracuseStep 5084207 = 7626311) B7626311
theorem B8722847 : Blo 892572 8722847 := bstep (se 1 (by rfl) ⟨6542135, by rfl⟩ : syracuseStep 8722847 = 13084271) B13084271
theorem B12886523 : Blo 892572 12886523 := bstep (se 1 (by rfl) ⟨9664892, by rfl⟩ : syracuseStep 12886523 = 19329785) B19329785
theorem B894399 : Blo 892572 894399 := bstep (se 1 (by rfl) ⟨670799, by rfl⟩ : syracuseStep 894399 = 1341599) B1341599
theorem B5451295 : Blo 892572 5451295 := bstep (se 1 (by rfl) ⟨4088471, by rfl⟩ : syracuseStep 5451295 = 8176943) B8176943
theorem B1130431 : Blo 892572 1130431 := bstep (se 1 (by rfl) ⟨847823, by rfl⟩ : syracuseStep 1130431 = 1695647) B1695647
theorem B2016539 : Blo 892572 2016539 := bstep (se 1 (by rfl) ⟨1512404, by rfl⟩ : syracuseStep 2016539 = 3024809) B3024809
theorem B2542205 : Blo 892572 2542205 := bstep (se 3 (by rfl) ⟨476663, by rfl⟩ : syracuseStep 2542205 = 953327) B953327
theorem B15256511 : Blo 892572 15256511 := bstep (se 1 (by rfl) ⟨11442383, by rfl⟩ : syracuseStep 15256511 = 22884767) B22884767
theorem B1007707 : Blo 892572 1007707 := bstep (se 1 (by rfl) ⟨755780, by rfl⟩ : syracuseStep 1007707 = 1511561) B1511561
theorem B1697051 : Blo 892572 1697051 := bstep (se 1 (by rfl) ⟨1272788, by rfl⟩ : syracuseStep 1697051 = 2545577) B2545577
theorem B1339007 : Blo 892572 1339007 := bstep (se 1 (by rfl) ⟨1004255, by rfl⟩ : syracuseStep 1339007 = 2008511) B2008511
theorem B1339433 : Blo 892572 1339433 := bstep (se 2 (by rfl) ⟨502287, by rfl⟩ : syracuseStep 1339433 = 1004575) B1004575
theorem B65401505 : Blo 892572 65401505 := bstep (se 2 (by rfl) ⟨24525564, by rfl⟩ : syracuseStep 65401505 = 49051129) B49051129
theorem B1341503 : Blo 892572 1341503 := bstep (se 1 (by rfl) ⟨1006127, by rfl⟩ : syracuseStep 1341503 = 2012255) B2012255
theorem B1342943 : Blo 892572 1342943 := bstep (se 1 (by rfl) ⟨1007207, by rfl⟩ : syracuseStep 1342943 = 2014415) B2014415
theorem B1343609 : Blo 892572 1343609 := bstep (se 2 (by rfl) ⟨503853, by rfl⟩ : syracuseStep 1343609 = 1007707) B1007707
theorem B1508071 : Blo 892572 1508071 := bstep (se 1 (by rfl) ⟨1131053, by rfl⟩ : syracuseStep 1508071 = 2262107) B2262107
theorem B1344359 : Blo 892572 1344359 := bstep (se 1 (by rfl) ⟨1008269, by rfl⟩ : syracuseStep 1344359 = 2016539) B2016539
theorem B198575225 : Blo 892572 198575225 := bstep (se 2 (by rfl) ⟨74465709, by rfl⟩ : syracuseStep 198575225 = 148931419) B148931419
theorem B4525469 : Blo 892572 4525469 := bstep (se 3 (by rfl) ⟨848525, by rfl⟩ : syracuseStep 4525469 = 1697051) B1697051
theorem B3019625 : Blo 892572 3019625 := bstep (se 2 (by rfl) ⟨1132359, by rfl⟩ : syracuseStep 3019625 = 2264719) B2264719
theorem B8591015 : Blo 892572 8591015 := bstep (se 1 (by rfl) ⟨6443261, by rfl⟩ : syracuseStep 8591015 = 12886523) B12886523
theorem B892671 : Blo 892572 892671 := bstep (se 1 (by rfl) ⟨669503, by rfl⟩ : syracuseStep 892671 = 1339007) B1339007
theorem B892955 : Blo 892572 892955 := bstep (se 1 (by rfl) ⟨669716, by rfl⟩ : syracuseStep 892955 = 1339433) B1339433
theorem B894335 : Blo 892572 894335 := bstep (se 1 (by rfl) ⟨670751, by rfl⟩ : syracuseStep 894335 = 1341503) B1341503
theorem B895295 : Blo 892572 895295 := bstep (se 1 (by rfl) ⟨671471, by rfl⟩ : syracuseStep 895295 = 1342943) B1342943
theorem B896495 : Blo 892572 896495 := bstep (se 1 (by rfl) ⟨672371, by rfl⟩ : syracuseStep 896495 = 1344743) B1344743
theorem B10171007 : Blo 892572 10171007 := bstep (se 1 (by rfl) ⟨7628255, by rfl⟩ : syracuseStep 10171007 = 15256511) B15256511
theorem B3060551 : Blo 892572 3060551 := bstep (se 1 (by rfl) ⟨2295413, by rfl⟩ : syracuseStep 3060551 = 4590827) B4590827
theorem B3389471 : Blo 892572 3389471 := bstep (se 1 (by rfl) ⟨2542103, by rfl⟩ : syracuseStep 3389471 = 5084207) B5084207
theorem B43601003 : Blo 892572 43601003 := bstep (se 1 (by rfl) ⟨32700752, by rfl⟩ : syracuseStep 43601003 = 65401505) B65401505
theorem B5724371 : Blo 892572 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B3497215 : Blo 892572 3497215 := bstep (se 1 (by rfl) ⟨2622911, by rfl⟩ : syracuseStep 3497215 = 5245823) B5245823
theorem B7268393 : Blo 892572 7268393 := bstep (se 2 (by rfl) ⟨2725647, by rfl⟩ : syracuseStep 7268393 = 5451295) B5451295
theorem B23260925 : Blo 892572 23260925 := bstep (se 3 (by rfl) ⟨4361423, by rfl⟩ : syracuseStep 23260925 = 8722847) B8722847
theorem B6779213 : Blo 892572 6779213 := bstep (se 3 (by rfl) ⟨1271102, by rfl⟩ : syracuseStep 6779213 = 2542205) B2542205
theorem B1507241 : Blo 892572 1507241 := bstep (se 2 (by rfl) ⟨565215, by rfl⟩ : syracuseStep 1507241 = 1130431) B1130431
theorem B132383483 : Blo 892572 132383483 := bstep (se 1 (by rfl) ⟨99287612, by rfl⟩ : syracuseStep 132383483 = 198575225) B198575225
theorem B29067335 : Blo 892572 29067335 := bstep (se 1 (by rfl) ⟨21800501, by rfl⟩ : syracuseStep 29067335 = 43601003) B43601003
theorem B8161469 : Blo 892572 8161469 := bstep (se 3 (by rfl) ⟨1530275, by rfl⟩ : syracuseStep 8161469 = 3060551) B3060551
theorem B3016979 : Blo 892572 3016979 := bstep (se 1 (by rfl) ⟨2262734, by rfl⟩ : syracuseStep 3016979 = 4525469) B4525469
theorem B15507283 : Blo 892572 15507283 := bstep (se 1 (by rfl) ⟨11630462, by rfl⟩ : syracuseStep 15507283 = 23260925) B23260925
theorem B4662953 : Blo 892572 4662953 := bstep (se 2 (by rfl) ⟨1748607, by rfl⟩ : syracuseStep 4662953 = 3497215) B3497215
theorem B895739 : Blo 892572 895739 := bstep (se 1 (by rfl) ⟨671804, by rfl⟩ : syracuseStep 895739 = 1343609) B1343609
theorem B896239 : Blo 892572 896239 := bstep (se 1 (by rfl) ⟨672179, by rfl⟩ : syracuseStep 896239 = 1344359) B1344359
theorem B2010761 : Blo 892572 2010761 := bstep (se 2 (by rfl) ⟨754035, by rfl⟩ : syracuseStep 2010761 = 1508071) B1508071
theorem B2013083 : Blo 892572 2013083 := bstep (se 1 (by rfl) ⟨1509812, by rfl⟩ : syracuseStep 2013083 = 3019625) B3019625
theorem B3816247 : Blo 892572 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B1004827 : Blo 892572 1004827 := bstep (se 1 (by rfl) ⟨753620, by rfl⟩ : syracuseStep 1004827 = 1507241) B1507241
theorem B5727343 : Blo 892572 5727343 := bstep (se 1 (by rfl) ⟨4295507, by rfl⟩ : syracuseStep 5727343 = 8591015) B8591015
theorem B4845595 : Blo 892572 4845595 := bstep (se 1 (by rfl) ⟨3634196, by rfl⟩ : syracuseStep 4845595 = 7268393) B7268393
theorem B4519475 : Blo 892572 4519475 := bstep (se 1 (by rfl) ⟨3389606, by rfl⟩ : syracuseStep 4519475 = 6779213) B6779213
theorem B6780671 : Blo 892572 6780671 := bstep (se 1 (by rfl) ⟨5085503, by rfl⟩ : syracuseStep 6780671 = 10171007) B10171007
theorem B2259647 : Blo 892572 2259647 := bstep (se 1 (by rfl) ⟨1694735, by rfl⟩ : syracuseStep 2259647 = 3389471) B3389471
theorem B5440979 : Blo 892572 5440979 := bstep (se 1 (by rfl) ⟨4080734, by rfl⟩ : syracuseStep 5440979 = 8161469) B8161469
theorem B7636457 : Blo 892572 7636457 := bstep (se 2 (by rfl) ⟨2863671, by rfl⟩ : syracuseStep 7636457 = 5727343) B5727343
theorem B6460793 : Blo 892572 6460793 := bstep (se 2 (by rfl) ⟨2422797, by rfl⟩ : syracuseStep 6460793 = 4845595) B4845595
theorem B5088329 : Blo 892572 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B88255655 : Blo 892572 88255655 := bstep (se 1 (by rfl) ⟨66191741, by rfl⟩ : syracuseStep 88255655 = 132383483) B132383483
theorem B19378223 : Blo 892572 19378223 := bstep (se 1 (by rfl) ⟨14533667, by rfl⟩ : syracuseStep 19378223 = 29067335) B29067335
theorem B2011319 : Blo 892572 2011319 := bstep (se 1 (by rfl) ⟨1508489, by rfl⟩ : syracuseStep 2011319 = 3016979) B3016979
theorem B3108635 : Blo 892572 3108635 := bstep (se 1 (by rfl) ⟨2331476, by rfl⟩ : syracuseStep 3108635 = 4662953) B4662953
theorem B1339769 : Blo 892572 1339769 := bstep (se 2 (by rfl) ⟨502413, by rfl⟩ : syracuseStep 1339769 = 1004827) B1004827
theorem B1340507 : Blo 892572 1340507 := bstep (se 1 (by rfl) ⟨1005380, by rfl⟩ : syracuseStep 1340507 = 2010761) B2010761
theorem B3012983 : Blo 892572 3012983 := bstep (se 1 (by rfl) ⟨2259737, by rfl⟩ : syracuseStep 3012983 = 4519475) B4519475
theorem B4520447 : Blo 892572 4520447 := bstep (se 1 (by rfl) ⟨3390335, by rfl⟩ : syracuseStep 4520447 = 6780671) B6780671
theorem B1342055 : Blo 892572 1342055 := bstep (se 1 (by rfl) ⟨1006541, by rfl⟩ : syracuseStep 1342055 = 2013083) B2013083
theorem B1506431 : Blo 892572 1506431 := bstep (se 1 (by rfl) ⟨1129823, by rfl⟩ : syracuseStep 1506431 = 2259647) B2259647
theorem B20676377 : Blo 892572 20676377 := bstep (se 2 (by rfl) ⟨7753641, by rfl⟩ : syracuseStep 20676377 = 15507283) B15507283
theorem B2072423 : Blo 892572 2072423 := bstep (se 1 (by rfl) ⟨1554317, by rfl⟩ : syracuseStep 2072423 = 3108635) B3108635
theorem B12918815 : Blo 892572 12918815 := bstep (se 1 (by rfl) ⟨9689111, by rfl⟩ : syracuseStep 12918815 = 19378223) B19378223
theorem B893179 : Blo 892572 893179 := bstep (se 1 (by rfl) ⟨669884, by rfl⟩ : syracuseStep 893179 = 1339769) B1339769
theorem B893671 : Blo 892572 893671 := bstep (se 1 (by rfl) ⟨670253, by rfl⟩ : syracuseStep 893671 = 1340507) B1340507
theorem B2008655 : Blo 892572 2008655 := bstep (se 1 (by rfl) ⟨1506491, by rfl⟩ : syracuseStep 2008655 = 3012983) B3012983
theorem B894703 : Blo 892572 894703 := bstep (se 1 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 894703 = 1342055) B1342055
theorem B5090971 : Blo 892572 5090971 := bstep (se 1 (by rfl) ⟨3818228, by rfl⟩ : syracuseStep 5090971 = 7636457) B7636457
theorem B4307195 : Blo 892572 4307195 := bstep (se 1 (by rfl) ⟨3230396, by rfl⟩ : syracuseStep 4307195 = 6460793) B6460793
theorem B3392219 : Blo 892572 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B58837103 : Blo 892572 58837103 := bstep (se 1 (by rfl) ⟨44127827, by rfl⟩ : syracuseStep 58837103 = 88255655) B88255655
theorem B1004287 : Blo 892572 1004287 := bstep (se 1 (by rfl) ⟨753215, by rfl⟩ : syracuseStep 1004287 = 1506431) B1506431
theorem B13784251 : Blo 892572 13784251 := bstep (se 1 (by rfl) ⟨10338188, by rfl⟩ : syracuseStep 13784251 = 20676377) B20676377
theorem B14509277 : Blo 892572 14509277 := bstep (se 3 (by rfl) ⟨2720489, by rfl⟩ : syracuseStep 14509277 = 5440979) B5440979
theorem B1340879 : Blo 892572 1340879 := bstep (se 1 (by rfl) ⟨1005659, by rfl⟩ : syracuseStep 1340879 = 2011319) B2011319
theorem B3013631 : Blo 892572 3013631 := bstep (se 1 (by rfl) ⟨2260223, by rfl⟩ : syracuseStep 3013631 = 4520447) B4520447
theorem B2261479 : Blo 892572 2261479 := bstep (se 1 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 2261479 = 3392219) B3392219
theorem B39224735 : Blo 892572 39224735 := bstep (se 1 (by rfl) ⟨29418551, by rfl⟩ : syracuseStep 39224735 = 58837103) B58837103
theorem B6787961 : Blo 892572 6787961 := bstep (se 2 (by rfl) ⟨2545485, by rfl⟩ : syracuseStep 6787961 = 5090971) B5090971
theorem B9672851 : Blo 892572 9672851 := bstep (se 1 (by rfl) ⟨7254638, by rfl⟩ : syracuseStep 9672851 = 14509277) B14509277
theorem B893919 : Blo 892572 893919 := bstep (se 1 (by rfl) ⟨670439, by rfl⟩ : syracuseStep 893919 = 1340879) B1340879
theorem B2009087 : Blo 892572 2009087 := bstep (se 1 (by rfl) ⟨1506815, by rfl⟩ : syracuseStep 2009087 = 3013631) B3013631
theorem B2871463 : Blo 892572 2871463 := bstep (se 1 (by rfl) ⟨2153597, by rfl⟩ : syracuseStep 2871463 = 4307195) B4307195
theorem B5526461 : Blo 892572 5526461 := bstep (se 3 (by rfl) ⟨1036211, by rfl⟩ : syracuseStep 5526461 = 2072423) B2072423
theorem B8612543 : Blo 892572 8612543 := bstep (se 1 (by rfl) ⟨6459407, by rfl⟩ : syracuseStep 8612543 = 12918815) B12918815
theorem B1339049 : Blo 892572 1339049 := bstep (se 2 (by rfl) ⟨502143, by rfl⟩ : syracuseStep 1339049 = 1004287) B1004287
theorem B1339103 : Blo 892572 1339103 := bstep (se 1 (by rfl) ⟨1004327, by rfl⟩ : syracuseStep 1339103 = 2008655) B2008655
theorem B18379001 : Blo 892572 18379001 := bstep (se 2 (by rfl) ⟨6892125, by rfl⟩ : syracuseStep 18379001 = 13784251) B13784251
theorem B3015305 : Blo 892572 3015305 := bstep (se 2 (by rfl) ⟨1130739, by rfl⟩ : syracuseStep 3015305 = 2261479) B2261479
theorem B26149823 : Blo 892572 26149823 := bstep (se 1 (by rfl) ⟨19612367, by rfl⟩ : syracuseStep 26149823 = 39224735) B39224735
theorem B4525307 : Blo 892572 4525307 := bstep (se 1 (by rfl) ⟨3393980, by rfl⟩ : syracuseStep 4525307 = 6787961) B6787961
theorem B5741695 : Blo 892572 5741695 := bstep (se 1 (by rfl) ⟨4306271, by rfl⟩ : syracuseStep 5741695 = 8612543) B8612543
theorem B892699 : Blo 892572 892699 := bstep (se 1 (by rfl) ⟨669524, by rfl⟩ : syracuseStep 892699 = 1339049) B1339049
theorem B892735 : Blo 892572 892735 := bstep (se 1 (by rfl) ⟨669551, by rfl⟩ : syracuseStep 892735 = 1339103) B1339103
theorem B3684307 : Blo 892572 3684307 := bstep (se 1 (by rfl) ⟨2763230, by rfl⟩ : syracuseStep 3684307 = 5526461) B5526461
theorem B49010669 : Blo 892572 49010669 := bstep (se 3 (by rfl) ⟨9189500, by rfl⟩ : syracuseStep 49010669 = 18379001) B18379001
theorem B6448567 : Blo 892572 6448567 := bstep (se 1 (by rfl) ⟨4836425, by rfl⟩ : syracuseStep 6448567 = 9672851) B9672851
theorem B3828617 : Blo 892572 3828617 := bstep (se 2 (by rfl) ⟨1435731, by rfl⟩ : syracuseStep 3828617 = 2871463) B2871463
theorem B1339391 : Blo 892572 1339391 := bstep (se 1 (by rfl) ⟨1004543, by rfl⟩ : syracuseStep 1339391 = 2009087) B2009087
theorem B17433215 : Blo 892572 17433215 := bstep (se 1 (by rfl) ⟨13074911, by rfl⟩ : syracuseStep 17433215 = 26149823) B26149823
theorem B3016871 : Blo 892572 3016871 := bstep (se 1 (by rfl) ⟨2262653, by rfl⟩ : syracuseStep 3016871 = 4525307) B4525307
theorem B32673779 : Blo 892572 32673779 := bstep (se 1 (by rfl) ⟨24505334, by rfl⟩ : syracuseStep 32673779 = 49010669) B49010669
theorem B892927 : Blo 892572 892927 := bstep (se 1 (by rfl) ⟨669695, by rfl⟩ : syracuseStep 892927 = 1339391) B1339391
theorem B2010203 : Blo 892572 2010203 := bstep (se 1 (by rfl) ⟨1507652, by rfl⟩ : syracuseStep 2010203 = 3015305) B3015305
theorem B8598089 : Blo 892572 8598089 := bstep (se 2 (by rfl) ⟨3224283, by rfl⟩ : syracuseStep 8598089 = 6448567) B6448567
theorem B7655593 : Blo 892572 7655593 := bstep (se 2 (by rfl) ⟨2870847, by rfl⟩ : syracuseStep 7655593 = 5741695) B5741695
theorem B2552411 : Blo 892572 2552411 := bstep (se 1 (by rfl) ⟨1914308, by rfl⟩ : syracuseStep 2552411 = 3828617) B3828617
theorem B4912409 : Blo 892572 4912409 := bstep (se 2 (by rfl) ⟨1842153, by rfl⟩ : syracuseStep 4912409 = 3684307) B3684307
theorem B2011247 : Blo 892572 2011247 := bstep (se 1 (by rfl) ⟨1508435, by rfl⟩ : syracuseStep 2011247 = 3016871) B3016871
theorem B10207457 : Blo 892572 10207457 := bstep (se 2 (by rfl) ⟨3827796, by rfl⟩ : syracuseStep 10207457 = 7655593) B7655593
theorem B11622143 : Blo 892572 11622143 := bstep (se 1 (by rfl) ⟨8716607, by rfl⟩ : syracuseStep 11622143 = 17433215) B17433215
theorem B6806429 : Blo 892572 6806429 := bstep (se 3 (by rfl) ⟨1276205, by rfl⟩ : syracuseStep 6806429 = 2552411) B2552411
theorem B21782519 : Blo 892572 21782519 := bstep (se 1 (by rfl) ⟨16336889, by rfl⟩ : syracuseStep 21782519 = 32673779) B32673779
theorem B1340135 : Blo 892572 1340135 := bstep (se 1 (by rfl) ⟨1005101, by rfl⟩ : syracuseStep 1340135 = 2010203) B2010203
theorem B5732059 : Blo 892572 5732059 := bstep (se 1 (by rfl) ⟨4299044, by rfl⟩ : syracuseStep 5732059 = 8598089) B8598089
theorem B3274939 : Blo 892572 3274939 := bstep (se 1 (by rfl) ⟨2456204, by rfl⟩ : syracuseStep 3274939 = 4912409) B4912409
theorem B14521679 : Blo 892572 14521679 := bstep (se 1 (by rfl) ⟨10891259, by rfl⟩ : syracuseStep 14521679 = 21782519) B21782519
theorem B7642745 : Blo 892572 7642745 := bstep (se 2 (by rfl) ⟨2866029, by rfl⟩ : syracuseStep 7642745 = 5732059) B5732059
theorem B4366585 : Blo 892572 4366585 := bstep (se 2 (by rfl) ⟨1637469, by rfl⟩ : syracuseStep 4366585 = 3274939) B3274939
theorem B893423 : Blo 892572 893423 := bstep (se 1 (by rfl) ⟨670067, by rfl⟩ : syracuseStep 893423 = 1340135) B1340135
theorem B4537619 : Blo 892572 4537619 := bstep (se 1 (by rfl) ⟨3403214, by rfl⟩ : syracuseStep 4537619 = 6806429) B6806429
theorem B6804971 : Blo 892572 6804971 := bstep (se 1 (by rfl) ⟨5103728, by rfl⟩ : syracuseStep 6804971 = 10207457) B10207457
theorem B30992381 : Blo 892572 30992381 := bstep (se 3 (by rfl) ⟨5811071, by rfl⟩ : syracuseStep 30992381 = 11622143) B11622143
theorem B1340831 : Blo 892572 1340831 := bstep (se 1 (by rfl) ⟨1005623, by rfl⟩ : syracuseStep 1340831 = 2011247) B2011247
theorem B893887 : Blo 892572 893887 := bstep (se 1 (by rfl) ⟨670415, by rfl⟩ : syracuseStep 893887 = 1340831) B1340831
theorem B3025079 : Blo 892572 3025079 := bstep (se 1 (by rfl) ⟨2268809, by rfl⟩ : syracuseStep 3025079 = 4537619) B4537619
theorem B9681119 : Blo 892572 9681119 := bstep (se 1 (by rfl) ⟨7260839, by rfl⟩ : syracuseStep 9681119 = 14521679) B14521679
theorem B4536647 : Blo 892572 4536647 := bstep (se 1 (by rfl) ⟨3402485, by rfl⟩ : syracuseStep 4536647 = 6804971) B6804971
theorem B5095163 : Blo 892572 5095163 := bstep (se 1 (by rfl) ⟨3821372, by rfl⟩ : syracuseStep 5095163 = 7642745) B7642745
theorem B20661587 : Blo 892572 20661587 := bstep (se 1 (by rfl) ⟨15496190, by rfl⟩ : syracuseStep 20661587 = 30992381) B30992381
theorem B5822113 : Blo 892572 5822113 := bstep (se 2 (by rfl) ⟨2183292, by rfl⟩ : syracuseStep 5822113 = 4366585) B4366585
theorem B3024431 : Blo 892572 3024431 := bstep (se 1 (by rfl) ⟨2268323, by rfl⟩ : syracuseStep 3024431 = 4536647) B4536647
theorem B13774391 : Blo 892572 13774391 := bstep (se 1 (by rfl) ⟨10330793, by rfl⟩ : syracuseStep 13774391 = 20661587) B20661587
theorem B2016719 : Blo 892572 2016719 := bstep (se 1 (by rfl) ⟨1512539, by rfl⟩ : syracuseStep 2016719 = 3025079) B3025079
theorem B3396775 : Blo 892572 3396775 := bstep (se 1 (by rfl) ⟨2547581, by rfl⟩ : syracuseStep 3396775 = 5095163) B5095163
theorem B7762817 : Blo 892572 7762817 := bstep (se 2 (by rfl) ⟨2911056, by rfl⟩ : syracuseStep 7762817 = 5822113) B5822113
theorem B6454079 : Blo 892572 6454079 := bstep (se 1 (by rfl) ⟨4840559, by rfl⟩ : syracuseStep 6454079 = 9681119) B9681119
theorem B1344479 : Blo 892572 1344479 := bstep (se 1 (by rfl) ⟨1008359, by rfl⟩ : syracuseStep 1344479 = 2016719) B2016719
theorem B4529033 : Blo 892572 4529033 := bstep (se 2 (by rfl) ⟨1698387, by rfl⟩ : syracuseStep 4529033 = 3396775) B3396775
theorem B9182927 : Blo 892572 9182927 := bstep (se 1 (by rfl) ⟨6887195, by rfl⟩ : syracuseStep 9182927 = 13774391) B13774391
theorem B4302719 : Blo 892572 4302719 := bstep (se 1 (by rfl) ⟨3227039, by rfl⟩ : syracuseStep 4302719 = 6454079) B6454079
theorem B2016287 : Blo 892572 2016287 := bstep (se 1 (by rfl) ⟨1512215, by rfl⟩ : syracuseStep 2016287 = 3024431) B3024431
theorem B20700845 : Blo 892572 20700845 := bstep (se 3 (by rfl) ⟨3881408, by rfl⟩ : syracuseStep 20700845 = 7762817) B7762817
theorem B1344191 : Blo 892572 1344191 := bstep (se 1 (by rfl) ⟨1008143, by rfl⟩ : syracuseStep 1344191 = 2016287) B2016287
theorem B3019355 : Blo 892572 3019355 := bstep (se 1 (by rfl) ⟨2264516, by rfl⟩ : syracuseStep 3019355 = 4529033) B4529033
theorem B13800563 : Blo 892572 13800563 := bstep (se 1 (by rfl) ⟨10350422, by rfl⟩ : syracuseStep 13800563 = 20700845) B20700845
theorem B24487805 : Blo 892572 24487805 := bstep (se 3 (by rfl) ⟨4591463, by rfl⟩ : syracuseStep 24487805 = 9182927) B9182927
theorem B896319 : Blo 892572 896319 := bstep (se 1 (by rfl) ⟨672239, by rfl⟩ : syracuseStep 896319 = 1344479) B1344479
theorem B2868479 : Blo 892572 2868479 := bstep (se 1 (by rfl) ⟨2151359, by rfl⟩ : syracuseStep 2868479 = 4302719) B4302719
theorem B896127 : Blo 892572 896127 := bstep (se 1 (by rfl) ⟨672095, by rfl⟩ : syracuseStep 896127 = 1344191) B1344191
theorem B1912319 : Blo 892572 1912319 := bstep (se 1 (by rfl) ⟨1434239, by rfl⟩ : syracuseStep 1912319 = 2868479) B2868479
theorem B2012903 : Blo 892572 2012903 := bstep (se 1 (by rfl) ⟨1509677, by rfl⟩ : syracuseStep 2012903 = 3019355) B3019355
theorem B9200375 : Blo 892572 9200375 := bstep (se 1 (by rfl) ⟨6900281, by rfl⟩ : syracuseStep 9200375 = 13800563) B13800563
theorem B65300813 : Blo 892572 65300813 := bstep (se 3 (by rfl) ⟨12243902, by rfl⟩ : syracuseStep 65300813 = 24487805) B24487805
theorem B6133583 : Blo 892572 6133583 := bstep (se 1 (by rfl) ⟨4600187, by rfl⟩ : syracuseStep 6133583 = 9200375) B9200375
theorem B43533875 : Blo 892572 43533875 := bstep (se 1 (by rfl) ⟨32650406, by rfl⟩ : syracuseStep 43533875 = 65300813) B65300813
theorem B1274879 : Blo 892572 1274879 := bstep (se 1 (by rfl) ⟨956159, by rfl⟩ : syracuseStep 1274879 = 1912319) B1912319
theorem B1341935 : Blo 892572 1341935 := bstep (se 1 (by rfl) ⟨1006451, by rfl⟩ : syracuseStep 1341935 = 2012903) B2012903
theorem B894623 : Blo 892572 894623 := bstep (se 1 (by rfl) ⟨670967, by rfl⟩ : syracuseStep 894623 = 1341935) B1341935
theorem B29022583 : Blo 892572 29022583 := bstep (se 1 (by rfl) ⟨21766937, by rfl⟩ : syracuseStep 29022583 = 43533875) B43533875
theorem B3399677 : Blo 892572 3399677 := bstep (se 3 (by rfl) ⟨637439, by rfl⟩ : syracuseStep 3399677 = 1274879) B1274879
theorem B4089055 : Blo 892572 4089055 := bstep (se 1 (by rfl) ⟨3066791, by rfl⟩ : syracuseStep 4089055 = 6133583) B6133583
theorem B2266451 : Blo 892572 2266451 := bstep (se 1 (by rfl) ⟨1699838, by rfl⟩ : syracuseStep 2266451 = 3399677) B3399677
theorem B5452073 : Blo 892572 5452073 := bstep (se 2 (by rfl) ⟨2044527, by rfl⟩ : syracuseStep 5452073 = 4089055) B4089055
theorem B38696777 : Blo 892572 38696777 := bstep (se 2 (by rfl) ⟨14511291, by rfl⟩ : syracuseStep 38696777 = 29022583) B29022583
theorem B1510967 : Blo 892572 1510967 := bstep (se 1 (by rfl) ⟨1133225, by rfl⟩ : syracuseStep 1510967 = 2266451) B2266451
theorem B25797851 : Blo 892572 25797851 := bstep (se 1 (by rfl) ⟨19348388, by rfl⟩ : syracuseStep 25797851 = 38696777) B38696777
theorem B3634715 : Blo 892572 3634715 := bstep (se 1 (by rfl) ⟨2726036, by rfl⟩ : syracuseStep 3634715 = 5452073) B5452073
theorem B1007311 : Blo 892572 1007311 := bstep (se 1 (by rfl) ⟨755483, by rfl⟩ : syracuseStep 1007311 = 1510967) B1510967
theorem B17198567 : Blo 892572 17198567 := bstep (se 1 (by rfl) ⟨12898925, by rfl⟩ : syracuseStep 17198567 = 25797851) B25797851
theorem B2423143 : Blo 892572 2423143 := bstep (se 1 (by rfl) ⟨1817357, by rfl⟩ : syracuseStep 2423143 = 3634715) B3634715
theorem B3230857 : Blo 892572 3230857 := bstep (se 2 (by rfl) ⟨1211571, by rfl⟩ : syracuseStep 3230857 = 2423143) B2423143
theorem B11465711 : Blo 892572 11465711 := bstep (se 1 (by rfl) ⟨8599283, by rfl⟩ : syracuseStep 11465711 = 17198567) B17198567
theorem B1343081 : Blo 892572 1343081 := bstep (se 2 (by rfl) ⟨503655, by rfl⟩ : syracuseStep 1343081 = 1007311) B1007311
theorem B7643807 : Blo 892572 7643807 := bstep (se 1 (by rfl) ⟨5732855, by rfl⟩ : syracuseStep 7643807 = 11465711) B11465711
theorem B895387 : Blo 892572 895387 := bstep (se 1 (by rfl) ⟨671540, by rfl⟩ : syracuseStep 895387 = 1343081) B1343081
theorem B17231237 : Blo 892572 17231237 := bstep (se 4 (by rfl) ⟨1615428, by rfl⟩ : syracuseStep 17231237 = 3230857) B3230857
theorem B5095871 : Blo 892572 5095871 := bstep (se 1 (by rfl) ⟨3821903, by rfl⟩ : syracuseStep 5095871 = 7643807) B7643807
theorem B11487491 : Blo 892572 11487491 := bstep (se 1 (by rfl) ⟨8615618, by rfl⟩ : syracuseStep 11487491 = 17231237) B17231237
theorem B3397247 : Blo 892572 3397247 := bstep (se 1 (by rfl) ⟨2547935, by rfl⟩ : syracuseStep 3397247 = 5095871) B5095871
theorem B7658327 : Blo 892572 7658327 := bstep (se 1 (by rfl) ⟨5743745, by rfl⟩ : syracuseStep 7658327 = 11487491) B11487491
theorem B2264831 : Blo 892572 2264831 := bstep (se 1 (by rfl) ⟨1698623, by rfl⟩ : syracuseStep 2264831 = 3397247) B3397247
theorem B5105551 : Blo 892572 5105551 := bstep (se 1 (by rfl) ⟨3829163, by rfl⟩ : syracuseStep 5105551 = 7658327) B7658327
theorem B1509887 : Blo 892572 1509887 := bstep (se 1 (by rfl) ⟨1132415, by rfl⟩ : syracuseStep 1509887 = 2264831) B2264831
theorem B6807401 : Blo 892572 6807401 := bstep (se 2 (by rfl) ⟨2552775, by rfl⟩ : syracuseStep 6807401 = 5105551) B5105551
theorem B4538267 : Blo 892572 4538267 := bstep (se 1 (by rfl) ⟨3403700, by rfl⟩ : syracuseStep 4538267 = 6807401) B6807401
theorem B1006591 : Blo 892572 1006591 := bstep (se 1 (by rfl) ⟨754943, by rfl⟩ : syracuseStep 1006591 = 1509887) B1509887
theorem B3025511 : Blo 892572 3025511 := bstep (se 1 (by rfl) ⟨2269133, by rfl⟩ : syracuseStep 3025511 = 4538267) B4538267
theorem B1342121 : Blo 892572 1342121 := bstep (se 2 (by rfl) ⟨503295, by rfl⟩ : syracuseStep 1342121 = 1006591) B1006591
theorem B894747 : Blo 892572 894747 := bstep (se 1 (by rfl) ⟨671060, by rfl⟩ : syracuseStep 894747 = 1342121) B1342121
theorem B2017007 : Blo 892572 2017007 := bstep (se 1 (by rfl) ⟨1512755, by rfl⟩ : syracuseStep 2017007 = 3025511) B3025511
theorem B1344671 : Blo 892572 1344671 := bstep (se 1 (by rfl) ⟨1008503, by rfl⟩ : syracuseStep 1344671 = 2017007) B2017007
theorem B896447 : Blo 892572 896447 := bstep (se 1 (by rfl) ⟨672335, by rfl⟩ : syracuseStep 896447 = 1344671) B1344671

theorem C0 (j : ℕ) (h1 : 223143 ≤ j) (h2 : j ≤ 223842) : Blo 892572 (4 * j + 3) := by
  interval_cases j
  · exact B892575
  · exact B892579
  · exact B892583
  · exact B892587
  · exact B892591
  · exact B892595
  · exact B892599
  · exact B892603
  · exact B892607
  · exact B892611
  · exact B892615
  · exact B892619
  · exact B892623
  · exact B892627
  · exact B892631
  · exact B892635
  · exact B892639
  · exact B892643
  · exact B892647
  · exact B892651
  · exact B892655
  · exact B892659
  · exact B892663
  · exact B892667
  · exact B892671
  · exact B892675
  · exact B892679
  · exact B892683
  · exact B892687
  · exact B892691
  · exact B892695
  · exact B892699
  · exact B892703
  · exact B892707
  · exact B892711
  · exact B892715
  · exact B892719
  · exact B892723
  · exact B892727
  · exact B892731
  · exact B892735
  · exact B892739
  · exact B892743
  · exact B892747
  · exact B892751
  · exact B892755
  · exact B892759
  · exact B892763
  · exact B892767
  · exact B892771
  · exact B892775
  · exact B892779
  · exact B892783
  · exact B892787
  · exact B892791
  · exact B892795
  · exact B892799
  · exact B892803
  · exact B892807
  · exact B892811
  · exact B892815
  · exact B892819
  · exact B892823
  · exact B892827
  · exact B892831
  · exact B892835
  · exact B892839
  · exact B892843
  · exact B892847
  · exact B892851
  · exact B892855
  · exact B892859
  · exact B892863
  · exact B892867
  · exact B892871
  · exact B892875
  · exact B892879
  · exact B892883
  · exact B892887
  · exact B892891
  · exact B892895
  · exact B892899
  · exact B892903
  · exact B892907
  · exact B892911
  · exact B892915
  · exact B892919
  · exact B892923
  · exact B892927
  · exact B892931
  · exact B892935
  · exact B892939
  · exact B892943
  · exact B892947
  · exact B892951
  · exact B892955
  · exact B892959
  · exact B892963
  · exact B892967
  · exact B892971
  · exact B892975
  · exact B892979
  · exact B892983
  · exact B892987
  · exact B892991
  · exact B892995
  · exact B892999
  · exact B893003
  · exact B893007
  · exact B893011
  · exact B893015
  · exact B893019
  · exact B893023
  · exact B893027
  · exact B893031
  · exact B893035
  · exact B893039
  · exact B893043
  · exact B893047
  · exact B893051
  · exact B893055
  · exact B893059
  · exact B893063
  · exact B893067
  · exact B893071
  · exact B893075
  · exact B893079
  · exact B893083
  · exact B893087
  · exact B893091
  · exact B893095
  · exact B893099
  · exact B893103
  · exact B893107
  · exact B893111
  · exact B893115
  · exact B893119
  · exact B893123
  · exact B893127
  · exact B893131
  · exact B893135
  · exact B893139
  · exact B893143
  · exact B893147
  · exact B893151
  · exact B893155
  · exact B893159
  · exact B893163
  · exact B893167
  · exact B893171
  · exact B893175
  · exact B893179
  · exact B893183
  · exact B893187
  · exact B893191
  · exact B893195
  · exact B893199
  · exact B893203
  · exact B893207
  · exact B893211
  · exact B893215
  · exact B893219
  · exact B893223
  · exact B893227
  · exact B893231
  · exact B893235
  · exact B893239
  · exact B893243
  · exact B893247
  · exact B893251
  · exact B893255
  · exact B893259
  · exact B893263
  · exact B893267
  · exact B893271
  · exact B893275
  · exact B893279
  · exact B893283
  · exact B893287
  · exact B893291
  · exact B893295
  · exact B893299
  · exact B893303
  · exact B893307
  · exact B893311
  · exact B893315
  · exact B893319
  · exact B893323
  · exact B893327
  · exact B893331
  · exact B893335
  · exact B893339
  · exact B893343
  · exact B893347
  · exact B893351
  · exact B893355
  · exact B893359
  · exact B893363
  · exact B893367
  · exact B893371
  · exact B893375
  · exact B893379
  · exact B893383
  · exact B893387
  · exact B893391
  · exact B893395
  · exact B893399
  · exact B893403
  · exact B893407
  · exact B893411
  · exact B893415
  · exact B893419
  · exact B893423
  · exact B893427
  · exact B893431
  · exact B893435
  · exact B893439
  · exact B893443
  · exact B893447
  · exact B893451
  · exact B893455
  · exact B893459
  · exact B893463
  · exact B893467
  · exact B893471
  · exact B893475
  · exact B893479
  · exact B893483
  · exact B893487
  · exact B893491
  · exact B893495
  · exact B893499
  · exact B893503
  · exact B893507
  · exact B893511
  · exact B893515
  · exact B893519
  · exact B893523
  · exact B893527
  · exact B893531
  · exact B893535
  · exact B893539
  · exact B893543
  · exact B893547
  · exact B893551
  · exact B893555
  · exact B893559
  · exact B893563
  · exact B893567
  · exact B893571
  · exact B893575
  · exact B893579
  · exact B893583
  · exact B893587
  · exact B893591
  · exact B893595
  · exact B893599
  · exact B893603
  · exact B893607
  · exact B893611
  · exact B893615
  · exact B893619
  · exact B893623
  · exact B893627
  · exact B893631
  · exact B893635
  · exact B893639
  · exact B893643
  · exact B893647
  · exact B893651
  · exact B893655
  · exact B893659
  · exact B893663
  · exact B893667
  · exact B893671
  · exact B893675
  · exact B893679
  · exact B893683
  · exact B893687
  · exact B893691
  · exact B893695
  · exact B893699
  · exact B893703
  · exact B893707
  · exact B893711
  · exact B893715
  · exact B893719
  · exact B893723
  · exact B893727
  · exact B893731
  · exact B893735
  · exact B893739
  · exact B893743
  · exact B893747
  · exact B893751
  · exact B893755
  · exact B893759
  · exact B893763
  · exact B893767
  · exact B893771
  · exact B893775
  · exact B893779
  · exact B893783
  · exact B893787
  · exact B893791
  · exact B893795
  · exact B893799
  · exact B893803
  · exact B893807
  · exact B893811
  · exact B893815
  · exact B893819
  · exact B893823
  · exact B893827
  · exact B893831
  · exact B893835
  · exact B893839
  · exact B893843
  · exact B893847
  · exact B893851
  · exact B893855
  · exact B893859
  · exact B893863
  · exact B893867
  · exact B893871
  · exact B893875
  · exact B893879
  · exact B893883
  · exact B893887
  · exact B893891
  · exact B893895
  · exact B893899
  · exact B893903
  · exact B893907
  · exact B893911
  · exact B893915
  · exact B893919
  · exact B893923
  · exact B893927
  · exact B893931
  · exact B893935
  · exact B893939
  · exact B893943
  · exact B893947
  · exact B893951
  · exact B893955
  · exact B893959
  · exact B893963
  · exact B893967
  · exact B893971
  · exact B893975
  · exact B893979
  · exact B893983
  · exact B893987
  · exact B893991
  · exact B893995
  · exact B893999
  · exact B894003
  · exact B894007
  · exact B894011
  · exact B894015
  · exact B894019
  · exact B894023
  · exact B894027
  · exact B894031
  · exact B894035
  · exact B894039
  · exact B894043
  · exact B894047
  · exact B894051
  · exact B894055
  · exact B894059
  · exact B894063
  · exact B894067
  · exact B894071
  · exact B894075
  · exact B894079
  · exact B894083
  · exact B894087
  · exact B894091
  · exact B894095
  · exact B894099
  · exact B894103
  · exact B894107
  · exact B894111
  · exact B894115
  · exact B894119
  · exact B894123
  · exact B894127
  · exact B894131
  · exact B894135
  · exact B894139
  · exact B894143
  · exact B894147
  · exact B894151
  · exact B894155
  · exact B894159
  · exact B894163
  · exact B894167
  · exact B894171
  · exact B894175
  · exact B894179
  · exact B894183
  · exact B894187
  · exact B894191
  · exact B894195
  · exact B894199
  · exact B894203
  · exact B894207
  · exact B894211
  · exact B894215
  · exact B894219
  · exact B894223
  · exact B894227
  · exact B894231
  · exact B894235
  · exact B894239
  · exact B894243
  · exact B894247
  · exact B894251
  · exact B894255
  · exact B894259
  · exact B894263
  · exact B894267
  · exact B894271
  · exact B894275
  · exact B894279
  · exact B894283
  · exact B894287
  · exact B894291
  · exact B894295
  · exact B894299
  · exact B894303
  · exact B894307
  · exact B894311
  · exact B894315
  · exact B894319
  · exact B894323
  · exact B894327
  · exact B894331
  · exact B894335
  · exact B894339
  · exact B894343
  · exact B894347
  · exact B894351
  · exact B894355
  · exact B894359
  · exact B894363
  · exact B894367
  · exact B894371
  · exact B894375
  · exact B894379
  · exact B894383
  · exact B894387
  · exact B894391
  · exact B894395
  · exact B894399
  · exact B894403
  · exact B894407
  · exact B894411
  · exact B894415
  · exact B894419
  · exact B894423
  · exact B894427
  · exact B894431
  · exact B894435
  · exact B894439
  · exact B894443
  · exact B894447
  · exact B894451
  · exact B894455
  · exact B894459
  · exact B894463
  · exact B894467
  · exact B894471
  · exact B894475
  · exact B894479
  · exact B894483
  · exact B894487
  · exact B894491
  · exact B894495
  · exact B894499
  · exact B894503
  · exact B894507
  · exact B894511
  · exact B894515
  · exact B894519
  · exact B894523
  · exact B894527
  · exact B894531
  · exact B894535
  · exact B894539
  · exact B894543
  · exact B894547
  · exact B894551
  · exact B894555
  · exact B894559
  · exact B894563
  · exact B894567
  · exact B894571
  · exact B894575
  · exact B894579
  · exact B894583
  · exact B894587
  · exact B894591
  · exact B894595
  · exact B894599
  · exact B894603
  · exact B894607
  · exact B894611
  · exact B894615
  · exact B894619
  · exact B894623
  · exact B894627
  · exact B894631
  · exact B894635
  · exact B894639
  · exact B894643
  · exact B894647
  · exact B894651
  · exact B894655
  · exact B894659
  · exact B894663
  · exact B894667
  · exact B894671
  · exact B894675
  · exact B894679
  · exact B894683
  · exact B894687
  · exact B894691
  · exact B894695
  · exact B894699
  · exact B894703
  · exact B894707
  · exact B894711
  · exact B894715
  · exact B894719
  · exact B894723
  · exact B894727
  · exact B894731
  · exact B894735
  · exact B894739
  · exact B894743
  · exact B894747
  · exact B894751
  · exact B894755
  · exact B894759
  · exact B894763
  · exact B894767
  · exact B894771
  · exact B894775
  · exact B894779
  · exact B894783
  · exact B894787
  · exact B894791
  · exact B894795
  · exact B894799
  · exact B894803
  · exact B894807
  · exact B894811
  · exact B894815
  · exact B894819
  · exact B894823
  · exact B894827
  · exact B894831
  · exact B894835
  · exact B894839
  · exact B894843
  · exact B894847
  · exact B894851
  · exact B894855
  · exact B894859
  · exact B894863
  · exact B894867
  · exact B894871
  · exact B894875
  · exact B894879
  · exact B894883
  · exact B894887
  · exact B894891
  · exact B894895
  · exact B894899
  · exact B894903
  · exact B894907
  · exact B894911
  · exact B894915
  · exact B894919
  · exact B894923
  · exact B894927
  · exact B894931
  · exact B894935
  · exact B894939
  · exact B894943
  · exact B894947
  · exact B894951
  · exact B894955
  · exact B894959
  · exact B894963
  · exact B894967
  · exact B894971
  · exact B894975
  · exact B894979
  · exact B894983
  · exact B894987
  · exact B894991
  · exact B894995
  · exact B894999
  · exact B895003
  · exact B895007
  · exact B895011
  · exact B895015
  · exact B895019
  · exact B895023
  · exact B895027
  · exact B895031
  · exact B895035
  · exact B895039
  · exact B895043
  · exact B895047
  · exact B895051
  · exact B895055
  · exact B895059
  · exact B895063
  · exact B895067
  · exact B895071
  · exact B895075
  · exact B895079
  · exact B895083
  · exact B895087
  · exact B895091
  · exact B895095
  · exact B895099
  · exact B895103
  · exact B895107
  · exact B895111
  · exact B895115
  · exact B895119
  · exact B895123
  · exact B895127
  · exact B895131
  · exact B895135
  · exact B895139
  · exact B895143
  · exact B895147
  · exact B895151
  · exact B895155
  · exact B895159
  · exact B895163
  · exact B895167
  · exact B895171
  · exact B895175
  · exact B895179
  · exact B895183
  · exact B895187
  · exact B895191
  · exact B895195
  · exact B895199
  · exact B895203
  · exact B895207
  · exact B895211
  · exact B895215
  · exact B895219
  · exact B895223
  · exact B895227
  · exact B895231
  · exact B895235
  · exact B895239
  · exact B895243
  · exact B895247
  · exact B895251
  · exact B895255
  · exact B895259
  · exact B895263
  · exact B895267
  · exact B895271
  · exact B895275
  · exact B895279
  · exact B895283
  · exact B895287
  · exact B895291
  · exact B895295
  · exact B895299
  · exact B895303
  · exact B895307
  · exact B895311
  · exact B895315
  · exact B895319
  · exact B895323
  · exact B895327
  · exact B895331
  · exact B895335
  · exact B895339
  · exact B895343
  · exact B895347
  · exact B895351
  · exact B895355
  · exact B895359
  · exact B895363
  · exact B895367
  · exact B895371

theorem C1 (j : ℕ) (h1 : 223843 ≤ j) (h2 : j ≤ 224142) : Blo 892572 (4 * j + 3) := by
  interval_cases j
  · exact B895375
  · exact B895379
  · exact B895383
  · exact B895387
  · exact B895391
  · exact B895395
  · exact B895399
  · exact B895403
  · exact B895407
  · exact B895411
  · exact B895415
  · exact B895419
  · exact B895423
  · exact B895427
  · exact B895431
  · exact B895435
  · exact B895439
  · exact B895443
  · exact B895447
  · exact B895451
  · exact B895455
  · exact B895459
  · exact B895463
  · exact B895467
  · exact B895471
  · exact B895475
  · exact B895479
  · exact B895483
  · exact B895487
  · exact B895491
  · exact B895495
  · exact B895499
  · exact B895503
  · exact B895507
  · exact B895511
  · exact B895515
  · exact B895519
  · exact B895523
  · exact B895527
  · exact B895531
  · exact B895535
  · exact B895539
  · exact B895543
  · exact B895547
  · exact B895551
  · exact B895555
  · exact B895559
  · exact B895563
  · exact B895567
  · exact B895571
  · exact B895575
  · exact B895579
  · exact B895583
  · exact B895587
  · exact B895591
  · exact B895595
  · exact B895599
  · exact B895603
  · exact B895607
  · exact B895611
  · exact B895615
  · exact B895619
  · exact B895623
  · exact B895627
  · exact B895631
  · exact B895635
  · exact B895639
  · exact B895643
  · exact B895647
  · exact B895651
  · exact B895655
  · exact B895659
  · exact B895663
  · exact B895667
  · exact B895671
  · exact B895675
  · exact B895679
  · exact B895683
  · exact B895687
  · exact B895691
  · exact B895695
  · exact B895699
  · exact B895703
  · exact B895707
  · exact B895711
  · exact B895715
  · exact B895719
  · exact B895723
  · exact B895727
  · exact B895731
  · exact B895735
  · exact B895739
  · exact B895743
  · exact B895747
  · exact B895751
  · exact B895755
  · exact B895759
  · exact B895763
  · exact B895767
  · exact B895771
  · exact B895775
  · exact B895779
  · exact B895783
  · exact B895787
  · exact B895791
  · exact B895795
  · exact B895799
  · exact B895803
  · exact B895807
  · exact B895811
  · exact B895815
  · exact B895819
  · exact B895823
  · exact B895827
  · exact B895831
  · exact B895835
  · exact B895839
  · exact B895843
  · exact B895847
  · exact B895851
  · exact B895855
  · exact B895859
  · exact B895863
  · exact B895867
  · exact B895871
  · exact B895875
  · exact B895879
  · exact B895883
  · exact B895887
  · exact B895891
  · exact B895895
  · exact B895899
  · exact B895903
  · exact B895907
  · exact B895911
  · exact B895915
  · exact B895919
  · exact B895923
  · exact B895927
  · exact B895931
  · exact B895935
  · exact B895939
  · exact B895943
  · exact B895947
  · exact B895951
  · exact B895955
  · exact B895959
  · exact B895963
  · exact B895967
  · exact B895971
  · exact B895975
  · exact B895979
  · exact B895983
  · exact B895987
  · exact B895991
  · exact B895995
  · exact B895999
  · exact B896003
  · exact B896007
  · exact B896011
  · exact B896015
  · exact B896019
  · exact B896023
  · exact B896027
  · exact B896031
  · exact B896035
  · exact B896039
  · exact B896043
  · exact B896047
  · exact B896051
  · exact B896055
  · exact B896059
  · exact B896063
  · exact B896067
  · exact B896071
  · exact B896075
  · exact B896079
  · exact B896083
  · exact B896087
  · exact B896091
  · exact B896095
  · exact B896099
  · exact B896103
  · exact B896107
  · exact B896111
  · exact B896115
  · exact B896119
  · exact B896123
  · exact B896127
  · exact B896131
  · exact B896135
  · exact B896139
  · exact B896143
  · exact B896147
  · exact B896151
  · exact B896155
  · exact B896159
  · exact B896163
  · exact B896167
  · exact B896171
  · exact B896175
  · exact B896179
  · exact B896183
  · exact B896187
  · exact B896191
  · exact B896195
  · exact B896199
  · exact B896203
  · exact B896207
  · exact B896211
  · exact B896215
  · exact B896219
  · exact B896223
  · exact B896227
  · exact B896231
  · exact B896235
  · exact B896239
  · exact B896243
  · exact B896247
  · exact B896251
  · exact B896255
  · exact B896259
  · exact B896263
  · exact B896267
  · exact B896271
  · exact B896275
  · exact B896279
  · exact B896283
  · exact B896287
  · exact B896291
  · exact B896295
  · exact B896299
  · exact B896303
  · exact B896307
  · exact B896311
  · exact B896315
  · exact B896319
  · exact B896323
  · exact B896327
  · exact B896331
  · exact B896335
  · exact B896339
  · exact B896343
  · exact B896347
  · exact B896351
  · exact B896355
  · exact B896359
  · exact B896363
  · exact B896367
  · exact B896371
  · exact B896375
  · exact B896379
  · exact B896383
  · exact B896387
  · exact B896391
  · exact B896395
  · exact B896399
  · exact B896403
  · exact B896407
  · exact B896411
  · exact B896415
  · exact B896419
  · exact B896423
  · exact B896427
  · exact B896431
  · exact B896435
  · exact B896439
  · exact B896443
  · exact B896447
  · exact B896451
  · exact B896455
  · exact B896459
  · exact B896463
  · exact B896467
  · exact B896471
  · exact B896475
  · exact B896479
  · exact B896483
  · exact B896487
  · exact B896491
  · exact B896495
  · exact B896499
  · exact B896503
  · exact B896507
  · exact B896511
  · exact B896515
  · exact B896519
  · exact B896523
  · exact B896527
  · exact B896531
  · exact B896535
  · exact B896539
  · exact B896543
  · exact B896547
  · exact B896551
  · exact B896555
  · exact B896559
  · exact B896563
  · exact B896567
  · exact B896571

theorem solution (m : ℕ) (hlo : 892572 ≤ m) (hhi : m ≤ 896572) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 223143 ≤ j := by omega
    have hj2 : j ≤ 224142 := by omega
    have hb : Blo 892572 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 223843 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
