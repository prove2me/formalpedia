-- Prove2me | solution 1 for syracuse_descends_range_1299968_1301968
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:26.867442+00:00
-- url     : https://prove2.me/submissions/fc7bb5d8-c49b-4578-b647-5f1a3e4229dc

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


theorem B12501013 : Blo 1299968 12501013 := bbase (se 6 (by rfl) ⟨292992, by rfl⟩ : syracuseStep 12501013 = 585985) (by norm_num)
theorem B2777141 : Blo 1299968 2777141 := bbase (se 5 (by rfl) ⟨130178, by rfl⟩ : syracuseStep 2777141 = 260357) (by norm_num)
theorem B3293237 : Blo 1299968 3293237 := bbase (se 5 (by rfl) ⟨154370, by rfl⟩ : syracuseStep 3293237 = 308741) (by norm_num)
theorem B2195525 : Blo 1299968 2195525 := bbase (se 4 (by rfl) ⟨205830, by rfl⟩ : syracuseStep 2195525 = 411661) (by norm_num)
theorem B1646669 : Blo 1299968 1646669 := bbase (se 3 (by rfl) ⟨308750, by rfl⟩ : syracuseStep 1646669 = 617501) (by norm_num)
theorem B1646725 : Blo 1299968 1646725 := bbase (se 4 (by rfl) ⟨154380, by rfl⟩ : syracuseStep 1646725 = 308761) (by norm_num)
theorem B2777285 : Blo 1299968 2777285 := bbase (se 4 (by rfl) ⟨260370, by rfl⟩ : syracuseStep 2777285 = 520741) (by norm_num)
theorem B2195653 : Blo 1299968 2195653 := bbase (se 4 (by rfl) ⟨205842, by rfl⟩ : syracuseStep 2195653 = 411685) (by norm_num)
theorem B3956933 : Blo 1299968 3956933 := bbase (se 4 (by rfl) ⟨370962, by rfl⟩ : syracuseStep 3956933 = 741925) (by norm_num)
theorem B1646821 : Blo 1299968 1646821 := bbase (se 4 (by rfl) ⟨154389, by rfl⟩ : syracuseStep 1646821 = 308779) (by norm_num)
theorem B1949957 : Blo 1299968 1949957 := bbase (se 4 (by rfl) ⟨182808, by rfl⟩ : syracuseStep 1949957 = 365617) (by norm_num)
theorem B1949981 : Blo 1299968 1949981 := bbase (se 3 (by rfl) ⟨365621, by rfl⟩ : syracuseStep 1949981 = 731243) (by norm_num)
theorem B2195741 : Blo 1299968 2195741 := bbase (se 3 (by rfl) ⟨411701, by rfl⟩ : syracuseStep 2195741 = 823403) (by norm_num)
theorem B1483057 : Blo 1299968 1483057 := bbase (se 2 (by rfl) ⟨556146, by rfl⟩ : syracuseStep 1483057 = 1112293) (by norm_num)
theorem B1950005 : Blo 1299968 1950005 := bbase (se 5 (by rfl) ⟨91406, by rfl⟩ : syracuseStep 1950005 = 182813) (by norm_num)
theorem B1950029 : Blo 1299968 1950029 := bbase (se 3 (by rfl) ⟨365630, by rfl⟩ : syracuseStep 1950029 = 731261) (by norm_num)
theorem B9879893 : Blo 1299968 9879893 := bbase (se 10 (by rfl) ⟨14472, by rfl⟩ : syracuseStep 9879893 = 28945) (by norm_num)
theorem B1950053 : Blo 1299968 1950053 := bbase (se 4 (by rfl) ⟨182817, by rfl⟩ : syracuseStep 1950053 = 365635) (by norm_num)
theorem B2343277 : Blo 1299968 2343277 := bbase (se 3 (by rfl) ⟨439364, by rfl⟩ : syracuseStep 2343277 = 878729) (by norm_num)
theorem B1950077 : Blo 1299968 1950077 := bbase (se 3 (by rfl) ⟨365639, by rfl⟩ : syracuseStep 1950077 = 731279) (by norm_num)
theorem B6586757 : Blo 1299968 6586757 := bbase (se 4 (by rfl) ⟨617508, by rfl⟩ : syracuseStep 6586757 = 1235017) (by norm_num)
theorem B3293581 : Blo 1299968 3293581 := bbase (se 3 (by rfl) ⟨617546, by rfl⟩ : syracuseStep 3293581 = 1235093) (by norm_num)
theorem B1646993 : Blo 1299968 1646993 := bbase (se 2 (by rfl) ⟨617622, by rfl⟩ : syracuseStep 1646993 = 1235245) (by norm_num)
theorem B1950101 : Blo 1299968 1950101 := bbase (se 6 (by rfl) ⟨45705, by rfl⟩ : syracuseStep 1950101 = 91411) (by norm_num)
theorem B2195869 : Blo 1299968 2195869 := bbase (se 3 (by rfl) ⟨411725, by rfl⟩ : syracuseStep 2195869 = 823451) (by norm_num)
theorem B4391333 : Blo 1299968 4391333 := bbase (se 4 (by rfl) ⟨411687, by rfl⟩ : syracuseStep 4391333 = 823375) (by norm_num)
theorem B1950125 : Blo 1299968 1950125 := bbase (se 3 (by rfl) ⟨365648, by rfl⟩ : syracuseStep 1950125 = 731297) (by norm_num)
theorem B2924981 : Blo 1299968 2924981 := bbase (se 5 (by rfl) ⟨137108, by rfl⟩ : syracuseStep 2924981 = 274217) (by norm_num)
theorem B10011061 : Blo 1299968 10011061 := bbase (se 5 (by rfl) ⟨469268, by rfl⟩ : syracuseStep 10011061 = 938537) (by norm_num)
theorem B1950149 : Blo 1299968 1950149 := bbase (se 4 (by rfl) ⟨182826, by rfl⟩ : syracuseStep 1950149 = 365653) (by norm_num)
theorem B1647049 : Blo 1299968 1647049 := bbase (se 2 (by rfl) ⟨617643, by rfl⟩ : syracuseStep 1647049 = 1235287) (by norm_num)
theorem B1950173 : Blo 1299968 1950173 := bbase (se 3 (by rfl) ⟨365657, by rfl⟩ : syracuseStep 1950173 = 731315) (by norm_num)
theorem B1950197 : Blo 1299968 1950197 := bbase (se 5 (by rfl) ⟨91415, by rfl⟩ : syracuseStep 1950197 = 182831) (by norm_num)
theorem B2195957 : Blo 1299968 2195957 := bbase (se 5 (by rfl) ⟨102935, by rfl⟩ : syracuseStep 2195957 = 205871) (by norm_num)
theorem B2925053 : Blo 1299968 2925053 := bbase (se 3 (by rfl) ⟨548447, by rfl⟩ : syracuseStep 2925053 = 1096895) (by norm_num)
theorem B3293693 : Blo 1299968 3293693 := bbase (se 3 (by rfl) ⟨617567, by rfl⟩ : syracuseStep 3293693 = 1235135) (by norm_num)
theorem B1950221 : Blo 1299968 1950221 := bbase (se 3 (by rfl) ⟨365666, by rfl⟩ : syracuseStep 1950221 = 731333) (by norm_num)
theorem B1950245 : Blo 1299968 1950245 := bbase (se 4 (by rfl) ⟨182835, by rfl⟩ : syracuseStep 1950245 = 365671) (by norm_num)
theorem B1647145 : Blo 1299968 1647145 := bbase (se 2 (by rfl) ⟨617679, by rfl⟩ : syracuseStep 1647145 = 1235359) (by norm_num)
theorem B2777645 : Blo 1299968 2777645 := bbase (se 3 (by rfl) ⟨520808, by rfl⟩ : syracuseStep 2777645 = 1041617) (by norm_num)
theorem B1950269 : Blo 1299968 1950269 := bbase (se 3 (by rfl) ⟨365675, by rfl⟩ : syracuseStep 1950269 = 731351) (by norm_num)
theorem B2925125 : Blo 1299968 2925125 := bbase (se 4 (by rfl) ⟨274230, by rfl⟩ : syracuseStep 2925125 = 548461) (by norm_num)
theorem B1950293 : Blo 1299968 1950293 := bbase (se 8 (by rfl) ⟨11427, by rfl⟩ : syracuseStep 1950293 = 22855) (by norm_num)
theorem B4170325 : Blo 1299968 4170325 := bbase (se 8 (by rfl) ⟨24435, by rfl⟩ : syracuseStep 4170325 = 48871) (by norm_num)
theorem B1950317 : Blo 1299968 1950317 := bbase (se 3 (by rfl) ⟨365684, by rfl⟩ : syracuseStep 1950317 = 731369) (by norm_num)
theorem B2196085 : Blo 1299968 2196085 := bbase (se 5 (by rfl) ⟨102941, by rfl⟩ : syracuseStep 2196085 = 205883) (by norm_num)
theorem B1950341 : Blo 1299968 1950341 := bbase (se 4 (by rfl) ⟨182844, by rfl⟩ : syracuseStep 1950341 = 365689) (by norm_num)
theorem B2966149 : Blo 1299968 2966149 := bbase (se 4 (by rfl) ⟨278076, by rfl⟩ : syracuseStep 2966149 = 556153) (by norm_num)
theorem B2171525 : Blo 1299968 2171525 := bbase (se 4 (by rfl) ⟨203580, by rfl⟩ : syracuseStep 2171525 = 407161) (by norm_num)
theorem B2925197 : Blo 1299968 2925197 := bbase (se 3 (by rfl) ⟨548474, by rfl⟩ : syracuseStep 2925197 = 1096949) (by norm_num)
theorem B21103253 : Blo 1299968 21103253 := bbase (se 6 (by rfl) ⟨494607, by rfl⟩ : syracuseStep 21103253 = 989215) (by norm_num)
theorem B11870869 : Blo 1299968 11870869 := bbase (se 6 (by rfl) ⟨278223, by rfl⟩ : syracuseStep 11870869 = 556447) (by norm_num)
theorem B1950365 : Blo 1299968 1950365 := bbase (se 3 (by rfl) ⟨365693, by rfl⟩ : syracuseStep 1950365 = 731387) (by norm_num)
theorem B1950389 : Blo 1299968 1950389 := bbase (se 5 (by rfl) ⟨91424, by rfl⟩ : syracuseStep 1950389 = 182849) (by norm_num)
theorem B1852093 : Blo 1299968 1852093 := bbase (se 3 (by rfl) ⟨347267, by rfl⟩ : syracuseStep 1852093 = 694535) (by norm_num)
theorem B3293885 : Blo 1299968 3293885 := bbase (se 3 (by rfl) ⟨617603, by rfl⟩ : syracuseStep 3293885 = 1235207) (by norm_num)
theorem B2966213 : Blo 1299968 2966213 := bbase (se 4 (by rfl) ⟨278082, by rfl⟩ : syracuseStep 2966213 = 556165) (by norm_num)
theorem B1950413 : Blo 1299968 1950413 := bbase (se 3 (by rfl) ⟨365702, by rfl⟩ : syracuseStep 1950413 = 731405) (by norm_num)
theorem B2196173 : Blo 1299968 2196173 := bbase (se 3 (by rfl) ⟨411782, by rfl⟩ : syracuseStep 2196173 = 823565) (by norm_num)
theorem B2925269 : Blo 1299968 2925269 := bbase (se 7 (by rfl) ⟨34280, by rfl⟩ : syracuseStep 2925269 = 68561) (by norm_num)
theorem B1647317 : Blo 1299968 1647317 := bbase (se 7 (by rfl) ⟨19304, by rfl⟩ : syracuseStep 1647317 = 38609) (by norm_num)
theorem B1950437 : Blo 1299968 1950437 := bbase (se 4 (by rfl) ⟨182853, by rfl⟩ : syracuseStep 1950437 = 365707) (by norm_num)
theorem B1876717 : Blo 1299968 1876717 := bbase (se 3 (by rfl) ⟨351884, by rfl⟩ : syracuseStep 1876717 = 703769) (by norm_num)
theorem B9872117 : Blo 1299968 9872117 := bbase (se 5 (by rfl) ⟨462755, by rfl⟩ : syracuseStep 9872117 = 925511) (by norm_num)
theorem B1950461 : Blo 1299968 1950461 := bbase (se 3 (by rfl) ⟨365711, by rfl⟩ : syracuseStep 1950461 = 731423) (by norm_num)
theorem B1647373 : Blo 1299968 1647373 := bbase (se 3 (by rfl) ⟨308882, by rfl⟩ : syracuseStep 1647373 = 617765) (by norm_num)
theorem B1950485 : Blo 1299968 1950485 := bbase (se 6 (by rfl) ⟨45714, by rfl⟩ : syracuseStep 1950485 = 91429) (by norm_num)
theorem B2925341 : Blo 1299968 2925341 := bbase (se 3 (by rfl) ⟨548501, by rfl⟩ : syracuseStep 2925341 = 1097003) (by norm_num)
theorem B1950509 : Blo 1299968 1950509 := bbase (se 3 (by rfl) ⟨365720, by rfl⟩ : syracuseStep 1950509 = 731441) (by norm_num)
theorem B1950533 : Blo 1299968 1950533 := bbase (se 4 (by rfl) ⟨182862, by rfl⟩ : syracuseStep 1950533 = 365725) (by norm_num)
theorem B2196301 : Blo 1299968 2196301 := bbase (se 3 (by rfl) ⟨411806, by rfl⟩ : syracuseStep 2196301 = 823613) (by norm_num)
theorem B4391765 : Blo 1299968 4391765 := bbase (se 9 (by rfl) ⟨12866, by rfl⟩ : syracuseStep 4391765 = 25733) (by norm_num)
theorem B3957589 : Blo 1299968 3957589 := bbase (se 9 (by rfl) ⟨11594, by rfl⟩ : syracuseStep 3957589 = 23189) (by norm_num)
theorem B1950557 : Blo 1299968 1950557 := bbase (se 3 (by rfl) ⟨365729, by rfl⟩ : syracuseStep 1950557 = 731459) (by norm_num)
theorem B2925413 : Blo 1299968 2925413 := bbase (se 4 (by rfl) ⟨274257, by rfl⟩ : syracuseStep 2925413 = 548515) (by norm_num)
theorem B1647469 : Blo 1299968 1647469 := bbase (se 3 (by rfl) ⟨308900, by rfl⟩ : syracuseStep 1647469 = 617801) (by norm_num)
theorem B1950581 : Blo 1299968 1950581 := bbase (se 5 (by rfl) ⟨91433, by rfl⟩ : syracuseStep 1950581 = 182867) (by norm_num)
theorem B1950605 : Blo 1299968 1950605 := bbase (se 3 (by rfl) ⟨365738, by rfl⟩ : syracuseStep 1950605 = 731477) (by norm_num)
theorem B1950629 : Blo 1299968 1950629 := bbase (se 4 (by rfl) ⟨182871, by rfl⟩ : syracuseStep 1950629 = 365743) (by norm_num)
theorem B2196389 : Blo 1299968 2196389 := bbase (se 4 (by rfl) ⟨205911, by rfl⟩ : syracuseStep 2196389 = 411823) (by norm_num)
theorem B2925485 : Blo 1299968 2925485 := bbase (se 3 (by rfl) ⟨548528, by rfl⟩ : syracuseStep 2925485 = 1097057) (by norm_num)
theorem B1483705 : Blo 1299968 1483705 := bbase (se 2 (by rfl) ⟨556389, by rfl⟩ : syracuseStep 1483705 = 1112779) (by norm_num)
theorem B1950653 : Blo 1299968 1950653 := bbase (se 3 (by rfl) ⟨365747, by rfl⟩ : syracuseStep 1950653 = 731495) (by norm_num)
theorem B1950677 : Blo 1299968 1950677 := bbase (se 7 (by rfl) ⟨22859, by rfl⟩ : syracuseStep 1950677 = 45719) (by norm_num)
theorem B7406549 : Blo 1299968 7406549 := bbase (se 7 (by rfl) ⟨86795, by rfl⟩ : syracuseStep 7406549 = 173591) (by norm_num)
theorem B3703765 : Blo 1299968 3703765 := bbase (se 7 (by rfl) ⟨43403, by rfl⟩ : syracuseStep 3703765 = 86807) (by norm_num)
theorem B1950701 : Blo 1299968 1950701 := bbase (se 3 (by rfl) ⟨365756, by rfl⟩ : syracuseStep 1950701 = 731513) (by norm_num)
theorem B2925557 : Blo 1299968 2925557 := bbase (se 5 (by rfl) ⟨137135, by rfl⟩ : syracuseStep 2925557 = 274271) (by norm_num)
theorem B1483777 : Blo 1299968 1483777 := bbase (se 2 (by rfl) ⟨556416, by rfl⟩ : syracuseStep 1483777 = 1112833) (by norm_num)
theorem B1950725 : Blo 1299968 1950725 := bbase (se 4 (by rfl) ⟨182880, by rfl⟩ : syracuseStep 1950725 = 365761) (by norm_num)
theorem B3294229 : Blo 1299968 3294229 := bbase (se 6 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 3294229 = 154417) (by norm_num)
theorem B1647641 : Blo 1299968 1647641 := bbase (se 2 (by rfl) ⟨617865, by rfl⟩ : syracuseStep 1647641 = 1235731) (by norm_num)
theorem B1950749 : Blo 1299968 1950749 := bbase (se 3 (by rfl) ⟨365765, by rfl⟩ : syracuseStep 1950749 = 731531) (by norm_num)
theorem B2196517 : Blo 1299968 2196517 := bbase (se 4 (by rfl) ⟨205923, by rfl⟩ : syracuseStep 2196517 = 411847) (by norm_num)
theorem B1950773 : Blo 1299968 1950773 := bbase (se 5 (by rfl) ⟨91442, by rfl⟩ : syracuseStep 1950773 = 182885) (by norm_num)
theorem B2925629 : Blo 1299968 2925629 := bbase (se 3 (by rfl) ⟨548555, by rfl⟩ : syracuseStep 2925629 = 1097111) (by norm_num)
theorem B1950797 : Blo 1299968 1950797 := bbase (se 3 (by rfl) ⟨365774, by rfl⟩ : syracuseStep 1950797 = 731549) (by norm_num)
theorem B1647697 : Blo 1299968 1647697 := bbase (se 2 (by rfl) ⟨617886, by rfl⟩ : syracuseStep 1647697 = 1235773) (by norm_num)
theorem B1410133 : Blo 1299968 1410133 := bbase (se 8 (by rfl) ⟨8262, by rfl⟩ : syracuseStep 1410133 = 16525) (by norm_num)
theorem B1950821 : Blo 1299968 1950821 := bbase (se 4 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 1950821 = 365779) (by norm_num)
theorem B1483877 : Blo 1299968 1483877 := bbase (se 4 (by rfl) ⟨139113, by rfl⟩ : syracuseStep 1483877 = 278227) (by norm_num)
theorem B4285541 : Blo 1299968 4285541 := bbase (se 4 (by rfl) ⟨401769, by rfl⟩ : syracuseStep 4285541 = 803539) (by norm_num)
theorem B1950845 : Blo 1299968 1950845 := bbase (se 3 (by rfl) ⟨365783, by rfl⟩ : syracuseStep 1950845 = 731567) (by norm_num)
theorem B2196605 : Blo 1299968 2196605 := bbase (se 3 (by rfl) ⟨411863, by rfl⟩ : syracuseStep 2196605 = 823727) (by norm_num)
theorem B2925701 : Blo 1299968 2925701 := bbase (se 4 (by rfl) ⟨274284, by rfl⟩ : syracuseStep 2925701 = 548569) (by norm_num)
theorem B1483909 : Blo 1299968 1483909 := bbase (se 4 (by rfl) ⟨139116, by rfl⟩ : syracuseStep 1483909 = 278233) (by norm_num)
theorem B3294341 : Blo 1299968 3294341 := bbase (se 4 (by rfl) ⟨308844, by rfl⟩ : syracuseStep 3294341 = 617689) (by norm_num)
theorem B1950869 : Blo 1299968 1950869 := bbase (se 6 (by rfl) ⟨45723, by rfl⟩ : syracuseStep 1950869 = 91447) (by norm_num)
theorem B1950893 : Blo 1299968 1950893 := bbase (se 3 (by rfl) ⟨365792, by rfl⟩ : syracuseStep 1950893 = 731585) (by norm_num)
theorem B1647793 : Blo 1299968 1647793 := bbase (se 2 (by rfl) ⟨617922, by rfl⟩ : syracuseStep 1647793 = 1235845) (by norm_num)
theorem B1950917 : Blo 1299968 1950917 := bbase (se 4 (by rfl) ⟨182898, by rfl⟩ : syracuseStep 1950917 = 365797) (by norm_num)
theorem B2925773 : Blo 1299968 2925773 := bbase (se 3 (by rfl) ⟨548582, by rfl⟩ : syracuseStep 2925773 = 1097165) (by norm_num)
theorem B1950941 : Blo 1299968 1950941 := bbase (se 3 (by rfl) ⟨365801, by rfl⟩ : syracuseStep 1950941 = 731603) (by norm_num)
theorem B2344157 : Blo 1299968 2344157 := bbase (se 3 (by rfl) ⟨439529, by rfl⟩ : syracuseStep 2344157 = 879059) (by norm_num)
theorem B1950965 : Blo 1299968 1950965 := bbase (se 5 (by rfl) ⟨91451, by rfl⟩ : syracuseStep 1950965 = 182903) (by norm_num)
theorem B2196733 : Blo 1299968 2196733 := bbase (se 3 (by rfl) ⟨411887, by rfl⟩ : syracuseStep 2196733 = 823775) (by norm_num)
theorem B4392197 : Blo 1299968 4392197 := bbase (se 4 (by rfl) ⟨411768, by rfl⟩ : syracuseStep 4392197 = 823537) (by norm_num)
theorem B1950989 : Blo 1299968 1950989 := bbase (se 3 (by rfl) ⟨365810, by rfl⟩ : syracuseStep 1950989 = 731621) (by norm_num)
theorem B2925845 : Blo 1299968 2925845 := bbase (se 6 (by rfl) ⟨68574, by rfl⟩ : syracuseStep 2925845 = 137149) (by norm_num)
theorem B1951013 : Blo 1299968 1951013 := bbase (se 4 (by rfl) ⟨182907, by rfl⟩ : syracuseStep 1951013 = 365815) (by norm_num)
theorem B5276981 : Blo 1299968 5276981 := bbase (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) (by norm_num)
theorem B1951037 : Blo 1299968 1951037 := bbase (se 3 (by rfl) ⟨365819, by rfl⟩ : syracuseStep 1951037 = 731639) (by norm_num)
theorem B3515717 : Blo 1299968 3515717 := bbase (se 4 (by rfl) ⟨329598, by rfl⟩ : syracuseStep 3515717 = 659197) (by norm_num)
theorem B3294533 : Blo 1299968 3294533 := bbase (se 4 (by rfl) ⟨308862, by rfl⟩ : syracuseStep 3294533 = 617725) (by norm_num)
theorem B1951061 : Blo 1299968 1951061 := bbase (se 12 (by rfl) ⟨714, by rfl⟩ : syracuseStep 1951061 = 1429) (by norm_num)
theorem B2196821 : Blo 1299968 2196821 := bbase (se 12 (by rfl) ⟨804, by rfl⟩ : syracuseStep 2196821 = 1609) (by norm_num)
theorem B2925917 : Blo 1299968 2925917 := bbase (se 3 (by rfl) ⟨548609, by rfl⟩ : syracuseStep 2925917 = 1097219) (by norm_num)
theorem B1951085 : Blo 1299968 1951085 := bbase (se 3 (by rfl) ⟨365828, by rfl⟩ : syracuseStep 1951085 = 731657) (by norm_num)
theorem B8340853 : Blo 1299968 8340853 := bbase (se 5 (by rfl) ⟨390977, by rfl⟩ : syracuseStep 8340853 = 781955) (by norm_num)
theorem B1951109 : Blo 1299968 1951109 := bbase (se 4 (by rfl) ⟨182916, by rfl⟩ : syracuseStep 1951109 = 365833) (by norm_num)
theorem B1951133 : Blo 1299968 1951133 := bbase (se 3 (by rfl) ⟨365837, by rfl⟩ : syracuseStep 1951133 = 731675) (by norm_num)
theorem B2925989 : Blo 1299968 2925989 := bbase (se 4 (by rfl) ⟨274311, by rfl⟩ : syracuseStep 2925989 = 548623) (by norm_num)
theorem B2778533 : Blo 1299968 2778533 := bbase (se 4 (by rfl) ⟨260487, by rfl⟩ : syracuseStep 2778533 = 520975) (by norm_num)
theorem B6333877 : Blo 1299968 6333877 := bbase (se 5 (by rfl) ⟨296900, by rfl⟩ : syracuseStep 6333877 = 593801) (by norm_num)
theorem B1951157 : Blo 1299968 1951157 := bbase (se 5 (by rfl) ⟨91460, by rfl⟩ : syracuseStep 1951157 = 182921) (by norm_num)
theorem B1951181 : Blo 1299968 1951181 := bbase (se 3 (by rfl) ⟨365846, by rfl⟩ : syracuseStep 1951181 = 731693) (by norm_num)
theorem B8898005 : Blo 1299968 8898005 := bbase (se 7 (by rfl) ⟨104273, by rfl⟩ : syracuseStep 8898005 = 208547) (by norm_num)
theorem B1852885 : Blo 1299968 1852885 := bbase (se 7 (by rfl) ⟨21713, by rfl⟩ : syracuseStep 1852885 = 43427) (by norm_num)
theorem B4941269 : Blo 1299968 4941269 := bbase (se 7 (by rfl) ⟨57905, by rfl⟩ : syracuseStep 4941269 = 115811) (by norm_num)
theorem B2196949 : Blo 1299968 2196949 := bbase (se 7 (by rfl) ⟨25745, by rfl⟩ : syracuseStep 2196949 = 51491) (by norm_num)
theorem B1951205 : Blo 1299968 1951205 := bbase (se 4 (by rfl) ⟨182925, by rfl⟩ : syracuseStep 1951205 = 365851) (by norm_num)
theorem B2926061 : Blo 1299968 2926061 := bbase (se 3 (by rfl) ⟨548636, by rfl⟩ : syracuseStep 2926061 = 1097273) (by norm_num)
theorem B1951229 : Blo 1299968 1951229 := bbase (se 3 (by rfl) ⟨365855, by rfl⟩ : syracuseStep 1951229 = 731711) (by norm_num)
theorem B1951253 : Blo 1299968 1951253 := bbase (se 6 (by rfl) ⟨45732, by rfl⟩ : syracuseStep 1951253 = 91465) (by norm_num)
theorem B2082349 : Blo 1299968 2082349 := bbase (se 3 (by rfl) ⟨390440, by rfl⟩ : syracuseStep 2082349 = 780881) (by norm_num)
theorem B1951277 : Blo 1299968 1951277 := bbase (se 3 (by rfl) ⟨365864, by rfl⟩ : syracuseStep 1951277 = 731729) (by norm_num)
theorem B2197037 : Blo 1299968 2197037 := bbase (se 3 (by rfl) ⟨411944, by rfl⟩ : syracuseStep 2197037 = 823889) (by norm_num)
theorem B2926133 : Blo 1299968 2926133 := bbase (se 5 (by rfl) ⟨137162, by rfl⟩ : syracuseStep 2926133 = 274325) (by norm_num)
theorem B1951301 : Blo 1299968 1951301 := bbase (se 4 (by rfl) ⟨182934, by rfl⟩ : syracuseStep 1951301 = 365869) (by norm_num)
theorem B1951325 : Blo 1299968 1951325 := bbase (se 3 (by rfl) ⟨365873, by rfl⟩ : syracuseStep 1951325 = 731747) (by norm_num)
theorem B1951349 : Blo 1299968 1951349 := bbase (se 5 (by rfl) ⟨91469, by rfl⟩ : syracuseStep 1951349 = 182939) (by norm_num)
theorem B2926205 : Blo 1299968 2926205 := bbase (se 3 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 2926205 = 1097327) (by norm_num)
theorem B1951373 : Blo 1299968 1951373 := bbase (se 3 (by rfl) ⟨365882, by rfl⟩ : syracuseStep 1951373 = 731765) (by norm_num)
theorem B6588053 : Blo 1299968 6588053 := bbase (se 6 (by rfl) ⟨154407, by rfl⟩ : syracuseStep 6588053 = 308815) (by norm_num)
theorem B2778781 : Blo 1299968 2778781 := bbase (se 3 (by rfl) ⟨521021, by rfl⟩ : syracuseStep 2778781 = 1042043) (by norm_num)
theorem B3294877 : Blo 1299968 3294877 := bbase (se 3 (by rfl) ⟨617789, by rfl⟩ : syracuseStep 3294877 = 1235579) (by norm_num)
theorem B1951397 : Blo 1299968 1951397 := bbase (se 4 (by rfl) ⟨182943, by rfl⟩ : syracuseStep 1951397 = 365887) (by norm_num)
theorem B4392629 : Blo 1299968 4392629 := bbase (se 5 (by rfl) ⟨205904, by rfl⟩ : syracuseStep 4392629 = 411809) (by norm_num)
theorem B1951421 : Blo 1299968 1951421 := bbase (se 3 (by rfl) ⟨365891, by rfl⟩ : syracuseStep 1951421 = 731783) (by norm_num)
theorem B2926277 : Blo 1299968 2926277 := bbase (se 4 (by rfl) ⟨274338, by rfl⟩ : syracuseStep 2926277 = 548677) (by norm_num)
theorem B1951445 : Blo 1299968 1951445 := bbase (se 7 (by rfl) ⟨22868, by rfl⟩ : syracuseStep 1951445 = 45737) (by norm_num)
theorem B2344661 : Blo 1299968 2344661 := bbase (se 7 (by rfl) ⟨27476, by rfl⟩ : syracuseStep 2344661 = 54953) (by norm_num)
theorem B1951469 : Blo 1299968 1951469 := bbase (se 3 (by rfl) ⟨365900, by rfl⟩ : syracuseStep 1951469 = 731801) (by norm_num)
theorem B4941557 : Blo 1299968 4941557 := bbase (se 5 (by rfl) ⟨231635, by rfl⟩ : syracuseStep 4941557 = 463271) (by norm_num)
theorem B1951493 : Blo 1299968 1951493 := bbase (se 4 (by rfl) ⟨182952, by rfl⟩ : syracuseStep 1951493 = 365905) (by norm_num)
theorem B2926349 : Blo 1299968 2926349 := bbase (se 3 (by rfl) ⟨548690, by rfl⟩ : syracuseStep 2926349 = 1097381) (by norm_num)
theorem B3294989 : Blo 1299968 3294989 := bbase (se 3 (by rfl) ⟨617810, by rfl⟩ : syracuseStep 3294989 = 1235621) (by norm_num)
theorem B1951517 : Blo 1299968 1951517 := bbase (se 3 (by rfl) ⟨365909, by rfl⟩ : syracuseStep 1951517 = 731819) (by norm_num)
theorem B1853221 : Blo 1299968 1853221 := bbase (se 4 (by rfl) ⟨173739, by rfl⟩ : syracuseStep 1853221 = 347479) (by norm_num)
theorem B2082605 : Blo 1299968 2082605 := bbase (se 3 (by rfl) ⟨390488, by rfl⟩ : syracuseStep 2082605 = 780977) (by norm_num)
theorem B1951541 : Blo 1299968 1951541 := bbase (se 5 (by rfl) ⟨91478, by rfl⟩ : syracuseStep 1951541 = 182957) (by norm_num)
theorem B1951565 : Blo 1299968 1951565 := bbase (se 3 (by rfl) ⟨365918, by rfl⟩ : syracuseStep 1951565 = 731837) (by norm_num)
theorem B2926421 : Blo 1299968 2926421 := bbase (se 9 (by rfl) ⟨8573, by rfl⟩ : syracuseStep 2926421 = 17147) (by norm_num)
theorem B1951589 : Blo 1299968 1951589 := bbase (se 4 (by rfl) ⟨182961, by rfl⟩ : syracuseStep 1951589 = 365923) (by norm_num)
theorem B1951613 : Blo 1299968 1951613 := bbase (se 3 (by rfl) ⟨365927, by rfl⟩ : syracuseStep 1951613 = 731855) (by norm_num)
theorem B1951637 : Blo 1299968 1951637 := bbase (se 6 (by rfl) ⟨45741, by rfl⟩ : syracuseStep 1951637 = 91483) (by norm_num)
theorem B2926493 : Blo 1299968 2926493 := bbase (se 3 (by rfl) ⟨548717, by rfl⟩ : syracuseStep 2926493 = 1097435) (by norm_num)
theorem B1951661 : Blo 1299968 1951661 := bbase (se 3 (by rfl) ⟨365936, by rfl⟩ : syracuseStep 1951661 = 731873) (by norm_num)
theorem B1951685 : Blo 1299968 1951685 := bbase (se 4 (by rfl) ⟨182970, by rfl⟩ : syracuseStep 1951685 = 365941) (by norm_num)
theorem B3295181 : Blo 1299968 3295181 := bbase (se 3 (by rfl) ⟨617846, by rfl⟩ : syracuseStep 3295181 = 1235693) (by norm_num)
theorem B1951709 : Blo 1299968 1951709 := bbase (se 3 (by rfl) ⟨365945, by rfl⟩ : syracuseStep 1951709 = 731891) (by norm_num)
theorem B2926565 : Blo 1299968 2926565 := bbase (se 4 (by rfl) ⟨274365, by rfl⟩ : syracuseStep 2926565 = 548731) (by norm_num)
theorem B1951733 : Blo 1299968 1951733 := bbase (se 5 (by rfl) ⟨91487, by rfl⟩ : syracuseStep 1951733 = 182975) (by norm_num)
theorem B1853437 : Blo 1299968 1853437 := bbase (se 3 (by rfl) ⟨347519, by rfl⟩ : syracuseStep 1853437 = 695039) (by norm_num)
theorem B6334469 : Blo 1299968 6334469 := bbase (se 4 (by rfl) ⟨593856, by rfl⟩ : syracuseStep 6334469 = 1187713) (by norm_num)
theorem B1951757 : Blo 1299968 1951757 := bbase (se 3 (by rfl) ⟨365954, by rfl⟩ : syracuseStep 1951757 = 731909) (by norm_num)
theorem B6252565 : Blo 1299968 6252565 := bbase (se 6 (by rfl) ⟨146544, by rfl⟩ : syracuseStep 6252565 = 293089) (by norm_num)
theorem B3704869 : Blo 1299968 3704869 := bbase (se 4 (by rfl) ⟨347331, by rfl⟩ : syracuseStep 3704869 = 694663) (by norm_num)
theorem B1951781 : Blo 1299968 1951781 := bbase (se 4 (by rfl) ⟨182979, by rfl⟩ : syracuseStep 1951781 = 365959) (by norm_num)
theorem B2926637 : Blo 1299968 2926637 := bbase (se 3 (by rfl) ⟨548744, by rfl⟩ : syracuseStep 2926637 = 1097489) (by norm_num)
theorem B1951805 : Blo 1299968 1951805 := bbase (se 3 (by rfl) ⟨365963, by rfl⟩ : syracuseStep 1951805 = 731927) (by norm_num)
theorem B1951829 : Blo 1299968 1951829 := bbase (se 8 (by rfl) ⟨11436, by rfl⟩ : syracuseStep 1951829 = 22873) (by norm_num)
theorem B4393061 : Blo 1299968 4393061 := bbase (se 4 (by rfl) ⟨411849, by rfl⟩ : syracuseStep 4393061 = 823699) (by norm_num)
theorem B1951853 : Blo 1299968 1951853 := bbase (se 3 (by rfl) ⟨365972, by rfl⟩ : syracuseStep 1951853 = 731945) (by norm_num)
theorem B7407733 : Blo 1299968 7407733 := bbase (se 5 (by rfl) ⟨347237, by rfl⟩ : syracuseStep 7407733 = 694475) (by norm_num)
theorem B2926709 : Blo 1299968 2926709 := bbase (se 5 (by rfl) ⟨137189, by rfl⟩ : syracuseStep 2926709 = 274379) (by norm_num)
theorem B1951877 : Blo 1299968 1951877 := bbase (se 4 (by rfl) ⟨182988, by rfl⟩ : syracuseStep 1951877 = 365977) (by norm_num)
theorem B2779285 : Blo 1299968 2779285 := bbase (se 6 (by rfl) ⟨65139, by rfl⟩ : syracuseStep 2779285 = 130279) (by norm_num)
theorem B1951901 : Blo 1299968 1951901 := bbase (se 3 (by rfl) ⟨365981, by rfl⟩ : syracuseStep 1951901 = 731963) (by norm_num)
theorem B1337509 : Blo 1299968 1337509 := bbase (se 4 (by rfl) ⟨125391, by rfl⟩ : syracuseStep 1337509 = 250783) (by norm_num)
theorem B1951925 : Blo 1299968 1951925 := bbase (se 5 (by rfl) ⟨91496, by rfl⟩ : syracuseStep 1951925 = 182993) (by norm_num)
theorem B2926781 : Blo 1299968 2926781 := bbase (se 3 (by rfl) ⟨548771, by rfl⟩ : syracuseStep 2926781 = 1097543) (by norm_num)
theorem B2468045 : Blo 1299968 2468045 := bbase (se 3 (by rfl) ⟨462758, by rfl⟩ : syracuseStep 2468045 = 925517) (by norm_num)
theorem B1951949 : Blo 1299968 1951949 := bbase (se 3 (by rfl) ⟨365990, by rfl⟩ : syracuseStep 1951949 = 731981) (by norm_num)
theorem B1951973 : Blo 1299968 1951973 := bbase (se 4 (by rfl) ⟨182997, by rfl⟩ : syracuseStep 1951973 = 365995) (by norm_num)
theorem B1951997 : Blo 1299968 1951997 := bbase (se 3 (by rfl) ⟨365999, by rfl⟩ : syracuseStep 1951997 = 731999) (by norm_num)
theorem B2926853 : Blo 1299968 2926853 := bbase (se 4 (by rfl) ⟨274392, by rfl⟩ : syracuseStep 2926853 = 548785) (by norm_num)
theorem B1952021 : Blo 1299968 1952021 := bbase (se 6 (by rfl) ⟨45750, by rfl⟩ : syracuseStep 1952021 = 91501) (by norm_num)
theorem B3295525 : Blo 1299968 3295525 := bbase (se 4 (by rfl) ⟨308955, by rfl⟩ : syracuseStep 3295525 = 617911) (by norm_num)
theorem B1952045 : Blo 1299968 1952045 := bbase (se 3 (by rfl) ⟨366008, by rfl⟩ : syracuseStep 1952045 = 732017) (by norm_num)
theorem B3754309 : Blo 1299968 3754309 := bbase (se 4 (by rfl) ⟨351966, by rfl⟩ : syracuseStep 3754309 = 703933) (by norm_num)
theorem B1952069 : Blo 1299968 1952069 := bbase (se 4 (by rfl) ⟨183006, by rfl⟩ : syracuseStep 1952069 = 366013) (by norm_num)
theorem B2926925 : Blo 1299968 2926925 := bbase (se 3 (by rfl) ⟨548798, by rfl⟩ : syracuseStep 2926925 = 1097597) (by norm_num)
theorem B1952093 : Blo 1299968 1952093 := bbase (se 3 (by rfl) ⟨366017, by rfl⟩ : syracuseStep 1952093 = 732035) (by norm_num)
theorem B1952117 : Blo 1299968 1952117 := bbase (se 5 (by rfl) ⟨91505, by rfl⟩ : syracuseStep 1952117 = 183011) (by norm_num)
theorem B1952141 : Blo 1299968 1952141 := bbase (se 3 (by rfl) ⟨366026, by rfl⟩ : syracuseStep 1952141 = 732053) (by norm_num)
theorem B2926997 : Blo 1299968 2926997 := bbase (se 6 (by rfl) ⟨68601, by rfl⟩ : syracuseStep 2926997 = 137203) (by norm_num)
theorem B1952165 : Blo 1299968 1952165 := bbase (se 4 (by rfl) ⟨183015, by rfl⟩ : syracuseStep 1952165 = 366031) (by norm_num)
theorem B1952189 : Blo 1299968 1952189 := bbase (se 3 (by rfl) ⟨366035, by rfl⟩ : syracuseStep 1952189 = 732071) (by norm_num)
theorem B1952213 : Blo 1299968 1952213 := bbase (se 7 (by rfl) ⟨22877, by rfl⟩ : syracuseStep 1952213 = 45755) (by norm_num)
theorem B2927069 : Blo 1299968 2927069 := bbase (se 3 (by rfl) ⟨548825, by rfl⟩ : syracuseStep 2927069 = 1097651) (by norm_num)
theorem B2468333 : Blo 1299968 2468333 := bbase (se 3 (by rfl) ⟨462812, by rfl⟩ : syracuseStep 2468333 = 925625) (by norm_num)
theorem B1952237 : Blo 1299968 1952237 := bbase (se 3 (by rfl) ⟨366044, by rfl⟩ : syracuseStep 1952237 = 732089) (by norm_num)
theorem B1952261 : Blo 1299968 1952261 := bbase (se 4 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 1952261 = 366049) (by norm_num)
theorem B5556757 : Blo 1299968 5556757 := bbase (se 6 (by rfl) ⟨130236, by rfl⟩ : syracuseStep 5556757 = 260473) (by norm_num)
theorem B3516949 : Blo 1299968 3516949 := bbase (se 6 (by rfl) ⟨82428, by rfl⟩ : syracuseStep 3516949 = 164857) (by norm_num)
theorem B4393493 : Blo 1299968 4393493 := bbase (se 6 (by rfl) ⟨102972, by rfl⟩ : syracuseStep 4393493 = 205945) (by norm_num)
theorem B1952285 : Blo 1299968 1952285 := bbase (se 3 (by rfl) ⟨366053, by rfl⟩ : syracuseStep 1952285 = 732107) (by norm_num)
theorem B2927141 : Blo 1299968 2927141 := bbase (se 4 (by rfl) ⟨274419, by rfl⟩ : syracuseStep 2927141 = 548839) (by norm_num)
theorem B1878565 : Blo 1299968 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B1952309 : Blo 1299968 1952309 := bbase (se 5 (by rfl) ⟨91514, by rfl⟩ : syracuseStep 1952309 = 183029) (by norm_num)
theorem B1952333 : Blo 1299968 1952333 := bbase (se 3 (by rfl) ⟨366062, by rfl⟩ : syracuseStep 1952333 = 732125) (by norm_num)
theorem B1952357 : Blo 1299968 1952357 := bbase (se 4 (by rfl) ⟨183033, by rfl⟩ : syracuseStep 1952357 = 366067) (by norm_num)
theorem B2927213 : Blo 1299968 2927213 := bbase (se 3 (by rfl) ⟨548852, by rfl⟩ : syracuseStep 2927213 = 1097705) (by norm_num)
theorem B3009133 : Blo 1299968 3009133 := bbase (se 3 (by rfl) ⟨564212, by rfl⟩ : syracuseStep 3009133 = 1128425) (by norm_num)
theorem B1952381 : Blo 1299968 1952381 := bbase (se 3 (by rfl) ⟨366071, by rfl⟩ : syracuseStep 1952381 = 732143) (by norm_num)
theorem B2468485 : Blo 1299968 2468485 := bbase (se 4 (by rfl) ⟨231420, by rfl⟩ : syracuseStep 2468485 = 462841) (by norm_num)
theorem B2083477 : Blo 1299968 2083477 := bbase (se 6 (by rfl) ⟨48831, by rfl⟩ : syracuseStep 2083477 = 97663) (by norm_num)
theorem B1952405 : Blo 1299968 1952405 := bbase (se 6 (by rfl) ⟨45759, by rfl⟩ : syracuseStep 1952405 = 91519) (by norm_num)
theorem B1952429 : Blo 1299968 1952429 := bbase (se 3 (by rfl) ⟨366080, by rfl⟩ : syracuseStep 1952429 = 732161) (by norm_num)
theorem B2927285 : Blo 1299968 2927285 := bbase (se 5 (by rfl) ⟨137216, by rfl⟩ : syracuseStep 2927285 = 274433) (by norm_num)
theorem B1952453 : Blo 1299968 1952453 := bbase (se 4 (by rfl) ⟨183042, by rfl⟩ : syracuseStep 1952453 = 366085) (by norm_num)
theorem B1952477 : Blo 1299968 1952477 := bbase (se 3 (by rfl) ⟨366089, by rfl⟩ : syracuseStep 1952477 = 732179) (by norm_num)
theorem B2083573 : Blo 1299968 2083573 := bbase (se 5 (by rfl) ⟨97667, by rfl⟩ : syracuseStep 2083573 = 195335) (by norm_num)
theorem B1952501 : Blo 1299968 1952501 := bbase (se 5 (by rfl) ⟨91523, by rfl⟩ : syracuseStep 1952501 = 183047) (by norm_num)
theorem B2927357 : Blo 1299968 2927357 := bbase (se 3 (by rfl) ⟨548879, by rfl⟩ : syracuseStep 2927357 = 1097759) (by norm_num)
theorem B1952525 : Blo 1299968 1952525 := bbase (se 3 (by rfl) ⟨366098, by rfl⟩ : syracuseStep 1952525 = 732197) (by norm_num)
theorem B1952549 : Blo 1299968 1952549 := bbase (se 4 (by rfl) ⟨183051, by rfl⟩ : syracuseStep 1952549 = 366103) (by norm_num)
theorem B1952573 : Blo 1299968 1952573 := bbase (se 3 (by rfl) ⟨366107, by rfl⟩ : syracuseStep 1952573 = 732215) (by norm_num)
theorem B2927429 : Blo 1299968 2927429 := bbase (se 4 (by rfl) ⟨274446, by rfl⟩ : syracuseStep 2927429 = 548893) (by norm_num)
theorem B1952597 : Blo 1299968 1952597 := bbase (se 9 (by rfl) ⟨5720, by rfl⟩ : syracuseStep 1952597 = 11441) (by norm_num)
theorem B1952621 : Blo 1299968 1952621 := bbase (se 3 (by rfl) ⟨366116, by rfl⟩ : syracuseStep 1952621 = 732233) (by norm_num)
theorem B1952645 : Blo 1299968 1952645 := bbase (se 4 (by rfl) ⟨183060, by rfl⟩ : syracuseStep 1952645 = 366121) (by norm_num)
theorem B2927501 : Blo 1299968 2927501 := bbase (se 3 (by rfl) ⟨548906, by rfl⟩ : syracuseStep 2927501 = 1097813) (by norm_num)
theorem B2083733 : Blo 1299968 2083733 := bbase (se 6 (by rfl) ⟨48837, by rfl⟩ : syracuseStep 2083733 = 97675) (by norm_num)
theorem B4942741 : Blo 1299968 4942741 := bbase (se 6 (by rfl) ⟨115845, by rfl⟩ : syracuseStep 4942741 = 231691) (by norm_num)
theorem B1952669 : Blo 1299968 1952669 := bbase (se 3 (by rfl) ⟨366125, by rfl⟩ : syracuseStep 1952669 = 732251) (by norm_num)
theorem B6589349 : Blo 1299968 6589349 := bbase (se 4 (by rfl) ⟨617751, by rfl⟩ : syracuseStep 6589349 = 1235503) (by norm_num)
theorem B2468789 : Blo 1299968 2468789 := bbase (se 5 (by rfl) ⟨115724, by rfl⟩ : syracuseStep 2468789 = 231449) (by norm_num)
theorem B1952693 : Blo 1299968 1952693 := bbase (se 5 (by rfl) ⟨91532, by rfl⟩ : syracuseStep 1952693 = 183065) (by norm_num)
theorem B4393925 : Blo 1299968 4393925 := bbase (se 4 (by rfl) ⟨411930, by rfl⟩ : syracuseStep 4393925 = 823861) (by norm_num)
theorem B1952717 : Blo 1299968 1952717 := bbase (se 3 (by rfl) ⟨366134, by rfl⟩ : syracuseStep 1952717 = 732269) (by norm_num)
theorem B18754517 : Blo 1299968 18754517 := bbase (se 7 (by rfl) ⟨219779, by rfl⟩ : syracuseStep 18754517 = 439559) (by norm_num)
theorem B2927573 : Blo 1299968 2927573 := bbase (se 7 (by rfl) ⟨34307, by rfl⟩ : syracuseStep 2927573 = 68615) (by norm_num)
theorem B1952741 : Blo 1299968 1952741 := bbase (se 4 (by rfl) ⟨183069, by rfl⟩ : syracuseStep 1952741 = 366139) (by norm_num)
theorem B1952765 : Blo 1299968 1952765 := bbase (se 3 (by rfl) ⟨366143, by rfl⟩ : syracuseStep 1952765 = 732287) (by norm_num)
theorem B2780173 : Blo 1299968 2780173 := bbase (se 3 (by rfl) ⟨521282, by rfl⟩ : syracuseStep 2780173 = 1042565) (by norm_num)
theorem B1952789 : Blo 1299968 1952789 := bbase (se 6 (by rfl) ⟨45768, by rfl⟩ : syracuseStep 1952789 = 91537) (by norm_num)
theorem B2927645 : Blo 1299968 2927645 := bbase (se 3 (by rfl) ⟨548933, by rfl⟩ : syracuseStep 2927645 = 1097867) (by norm_num)
theorem B1952813 : Blo 1299968 1952813 := bbase (se 3 (by rfl) ⟨366152, by rfl⟩ : syracuseStep 1952813 = 732305) (by norm_num)
theorem B1952837 : Blo 1299968 1952837 := bbase (se 4 (by rfl) ⟨183078, by rfl⟩ : syracuseStep 1952837 = 366157) (by norm_num)
theorem B20024405 : Blo 1299968 20024405 := bbase (se 8 (by rfl) ⟨117330, by rfl⟩ : syracuseStep 20024405 = 234661) (by norm_num)
theorem B1952861 : Blo 1299968 1952861 := bbase (se 3 (by rfl) ⟨366161, by rfl⟩ : syracuseStep 1952861 = 732323) (by norm_num)
theorem B2927717 : Blo 1299968 2927717 := bbase (se 4 (by rfl) ⟨274473, by rfl⟩ : syracuseStep 2927717 = 548947) (by norm_num)
theorem B1952885 : Blo 1299968 1952885 := bbase (se 5 (by rfl) ⟨91541, by rfl⟩ : syracuseStep 1952885 = 183083) (by norm_num)
theorem B1952909 : Blo 1299968 1952909 := bbase (se 3 (by rfl) ⟨366170, by rfl⟩ : syracuseStep 1952909 = 732341) (by norm_num)
theorem B1952933 : Blo 1299968 1952933 := bbase (se 4 (by rfl) ⟨183087, by rfl⟩ : syracuseStep 1952933 = 366175) (by norm_num)
theorem B2927789 : Blo 1299968 2927789 := bbase (se 3 (by rfl) ⟨548960, by rfl⟩ : syracuseStep 2927789 = 1097921) (by norm_num)
theorem B4943045 : Blo 1299968 4943045 := bbase (se 4 (by rfl) ⟨463410, by rfl⟩ : syracuseStep 4943045 = 926821) (by norm_num)
theorem B2927861 : Blo 1299968 2927861 := bbase (se 5 (by rfl) ⟨137243, by rfl⟩ : syracuseStep 2927861 = 274487) (by norm_num)
theorem B2927933 : Blo 1299968 2927933 := bbase (se 3 (by rfl) ⟨548987, by rfl⟩ : syracuseStep 2927933 = 1097975) (by norm_num)
theorem B6581573 : Blo 1299968 6581573 := bbase (se 4 (by rfl) ⟨617022, by rfl⟩ : syracuseStep 6581573 = 1234045) (by norm_num)
theorem B2928005 : Blo 1299968 2928005 := bbase (se 4 (by rfl) ⟨274500, by rfl⟩ : syracuseStep 2928005 = 549001) (by norm_num)
theorem B5270933 : Blo 1299968 5270933 := bbase (se 6 (by rfl) ⟨123537, by rfl⟩ : syracuseStep 5270933 = 247075) (by norm_num)
theorem B3124669 : Blo 1299968 3124669 := bbase (se 3 (by rfl) ⟨585875, by rfl⟩ : syracuseStep 3124669 = 1171751) (by norm_num)
theorem B2928077 : Blo 1299968 2928077 := bbase (se 3 (by rfl) ⟨549014, by rfl⟩ : syracuseStep 2928077 = 1098029) (by norm_num)
theorem B2780669 : Blo 1299968 2780669 := bbase (se 3 (by rfl) ⟨521375, by rfl⟩ : syracuseStep 2780669 = 1042751) (by norm_num)
theorem B3706373 : Blo 1299968 3706373 := bbase (se 4 (by rfl) ⟨347472, by rfl⟩ : syracuseStep 3706373 = 694945) (by norm_num)
theorem B2928149 : Blo 1299968 2928149 := bbase (se 6 (by rfl) ⟨68628, by rfl⟩ : syracuseStep 2928149 = 137257) (by norm_num)
theorem B2928221 : Blo 1299968 2928221 := bbase (se 3 (by rfl) ⟨549041, by rfl⟩ : syracuseStep 2928221 = 1098083) (by norm_num)
theorem B1502885 : Blo 1299968 1502885 := bbase (se 4 (by rfl) ⟨140895, by rfl⟩ : syracuseStep 1502885 = 281791) (by norm_num)
theorem B2469541 : Blo 1299968 2469541 := bbase (se 4 (by rfl) ⟨231519, by rfl⟩ : syracuseStep 2469541 = 463039) (by norm_num)
theorem B2928293 : Blo 1299968 2928293 := bbase (se 4 (by rfl) ⟨274527, by rfl⟩ : syracuseStep 2928293 = 549055) (by norm_num)
theorem B3518117 : Blo 1299968 3518117 := bbase (se 4 (by rfl) ⟨329823, by rfl⟩ : syracuseStep 3518117 = 659647) (by norm_num)
theorem B2928365 : Blo 1299968 2928365 := bbase (se 3 (by rfl) ⟨549068, by rfl⟩ : syracuseStep 2928365 = 1098137) (by norm_num)
theorem B5713669 : Blo 1299968 5713669 := bbase (se 4 (by rfl) ⟨535656, by rfl⟩ : syracuseStep 5713669 = 1071313) (by norm_num)
theorem B1388297 : Blo 1299968 1388297 := bbase (se 2 (by rfl) ⟨520611, by rfl⟩ : syracuseStep 1388297 = 1041223) (by norm_num)
theorem B2469685 : Blo 1299968 2469685 := bbase (se 5 (by rfl) ⟨115766, by rfl⟩ : syracuseStep 2469685 = 231533) (by norm_num)
theorem B2928437 : Blo 1299968 2928437 := bbase (se 5 (by rfl) ⟨137270, by rfl⟩ : syracuseStep 2928437 = 274541) (by norm_num)
theorem B2928509 : Blo 1299968 2928509 := bbase (se 3 (by rfl) ⟨549095, by rfl⟩ : syracuseStep 2928509 = 1098191) (by norm_num)
theorem B2928581 : Blo 1299968 2928581 := bbase (se 4 (by rfl) ⟨274554, by rfl⟩ : syracuseStep 2928581 = 549109) (by norm_num)
theorem B2469845 : Blo 1299968 2469845 := bbase (se 7 (by rfl) ⟨28943, by rfl⟩ : syracuseStep 2469845 = 57887) (by norm_num)
theorem B3518453 : Blo 1299968 3518453 := bbase (se 5 (by rfl) ⟨164927, by rfl⟩ : syracuseStep 3518453 = 329855) (by norm_num)
theorem B2084861 : Blo 1299968 2084861 := bbase (se 3 (by rfl) ⟨390911, by rfl⟩ : syracuseStep 2084861 = 781823) (by norm_num)
theorem B1388549 : Blo 1299968 1388549 := bbase (se 4 (by rfl) ⟨130176, by rfl⟩ : syracuseStep 1388549 = 260353) (by norm_num)
theorem B2928653 : Blo 1299968 2928653 := bbase (se 3 (by rfl) ⟨549122, by rfl⟩ : syracuseStep 2928653 = 1098245) (by norm_num)
theorem B17813525 : Blo 1299968 17813525 := bbase (se 6 (by rfl) ⟨417504, by rfl⟩ : syracuseStep 17813525 = 835009) (by norm_num)
theorem B7409717 : Blo 1299968 7409717 := bbase (se 5 (by rfl) ⟨347330, by rfl⟩ : syracuseStep 7409717 = 694661) (by norm_num)
theorem B2928725 : Blo 1299968 2928725 := bbase (se 8 (by rfl) ⟨17160, by rfl⟩ : syracuseStep 2928725 = 34321) (by norm_num)
theorem B3518549 : Blo 1299968 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B2469989 : Blo 1299968 2469989 := bbase (se 4 (by rfl) ⟨231561, by rfl⟩ : syracuseStep 2469989 = 463123) (by norm_num)
theorem B1585273 : Blo 1299968 1585273 := bbase (se 2 (by rfl) ⟨594477, by rfl⟩ : syracuseStep 1585273 = 1188955) (by norm_num)
theorem B2928797 : Blo 1299968 2928797 := bbase (se 3 (by rfl) ⟨549149, by rfl⟩ : syracuseStep 2928797 = 1098299) (by norm_num)
theorem B6590645 : Blo 1299968 6590645 := bbase (se 5 (by rfl) ⟨308936, by rfl⟩ : syracuseStep 6590645 = 617873) (by norm_num)
theorem B1462477 : Blo 1299968 1462477 := bbase (se 3 (by rfl) ⟨274214, by rfl⟩ : syracuseStep 1462477 = 548429) (by norm_num)
theorem B2928869 : Blo 1299968 2928869 := bbase (se 4 (by rfl) ⟨274581, by rfl⟩ : syracuseStep 2928869 = 549163) (by norm_num)
theorem B1462513 : Blo 1299968 1462513 := bbase (se 2 (by rfl) ⟨548442, by rfl⟩ : syracuseStep 1462513 = 1096885) (by norm_num)
theorem B1462549 : Blo 1299968 1462549 := bbase (se 6 (by rfl) ⟨34278, by rfl⟩ : syracuseStep 1462549 = 68557) (by norm_num)
theorem B2928941 : Blo 1299968 2928941 := bbase (se 3 (by rfl) ⟨549176, by rfl⟩ : syracuseStep 2928941 = 1098353) (by norm_num)
theorem B1462585 : Blo 1299968 1462585 := bbase (se 2 (by rfl) ⟨548469, by rfl⟩ : syracuseStep 1462585 = 1096939) (by norm_num)
theorem B1462621 : Blo 1299968 1462621 := bbase (se 3 (by rfl) ⟨274241, by rfl⟩ : syracuseStep 1462621 = 548483) (by norm_num)
theorem B7033205 : Blo 1299968 7033205 := bbase (se 5 (by rfl) ⟨329681, by rfl⟩ : syracuseStep 7033205 = 659363) (by norm_num)
theorem B2929013 : Blo 1299968 2929013 := bbase (se 5 (by rfl) ⟨137297, by rfl⟩ : syracuseStep 2929013 = 274595) (by norm_num)
theorem B1462657 : Blo 1299968 1462657 := bbase (se 2 (by rfl) ⟨548496, by rfl⟩ : syracuseStep 1462657 = 1096993) (by norm_num)
theorem B2470277 : Blo 1299968 2470277 := bbase (se 4 (by rfl) ⟨231588, by rfl⟩ : syracuseStep 2470277 = 463177) (by norm_num)
theorem B1462693 : Blo 1299968 1462693 := bbase (se 4 (by rfl) ⟨137127, by rfl⟩ : syracuseStep 1462693 = 274255) (by norm_num)
theorem B2929085 : Blo 1299968 2929085 := bbase (se 3 (by rfl) ⟨549203, by rfl⟩ : syracuseStep 2929085 = 1098407) (by norm_num)
theorem B1388993 : Blo 1299968 1388993 := bbase (se 2 (by rfl) ⟨520872, by rfl⟩ : syracuseStep 1388993 = 1041745) (by norm_num)
theorem B1462729 : Blo 1299968 1462729 := bbase (se 2 (by rfl) ⟨548523, by rfl⟩ : syracuseStep 1462729 = 1097047) (by norm_num)
theorem B1462765 : Blo 1299968 1462765 := bbase (se 3 (by rfl) ⟨274268, by rfl⟩ : syracuseStep 1462765 = 548537) (by norm_num)
theorem B2085373 : Blo 1299968 2085373 := bbase (se 3 (by rfl) ⟨391007, by rfl⟩ : syracuseStep 2085373 = 782015) (by norm_num)
theorem B2929157 : Blo 1299968 2929157 := bbase (se 4 (by rfl) ⟨274608, by rfl⟩ : syracuseStep 2929157 = 549217) (by norm_num)
theorem B2503181 : Blo 1299968 2503181 := bbase (se 3 (by rfl) ⟨469346, by rfl⟩ : syracuseStep 2503181 = 938693) (by norm_num)
theorem B1462801 : Blo 1299968 1462801 := bbase (se 2 (by rfl) ⟨548550, by rfl⟩ : syracuseStep 1462801 = 1097101) (by norm_num)
theorem B1692181 : Blo 1299968 1692181 := bbase (se 6 (by rfl) ⟨39660, by rfl⟩ : syracuseStep 1692181 = 79321) (by norm_num)
theorem B2470429 : Blo 1299968 2470429 := bbase (se 3 (by rfl) ⟨463205, by rfl⟩ : syracuseStep 2470429 = 926411) (by norm_num)
theorem B1462837 : Blo 1299968 1462837 := bbase (se 5 (by rfl) ⟨68570, by rfl⟩ : syracuseStep 1462837 = 137141) (by norm_num)
theorem B2929229 : Blo 1299968 2929229 := bbase (se 3 (by rfl) ⟨549230, by rfl⟩ : syracuseStep 2929229 = 1098461) (by norm_num)
theorem B6582869 : Blo 1299968 6582869 := bbase (se 8 (by rfl) ⟨38571, by rfl⟩ : syracuseStep 6582869 = 77143) (by norm_num)
theorem B1462873 : Blo 1299968 1462873 := bbase (se 2 (by rfl) ⟨548577, by rfl⟩ : syracuseStep 1462873 = 1097155) (by norm_num)
theorem B4387445 : Blo 1299968 4387445 := bbase (se 5 (by rfl) ⟨205661, by rfl⟩ : syracuseStep 4387445 = 411323) (by norm_num)
theorem B1462909 : Blo 1299968 1462909 := bbase (se 3 (by rfl) ⟨274295, by rfl⟩ : syracuseStep 1462909 = 548591) (by norm_num)
theorem B2929301 : Blo 1299968 2929301 := bbase (se 6 (by rfl) ⟨68655, by rfl⟩ : syracuseStep 2929301 = 137311) (by norm_num)
theorem B1462945 : Blo 1299968 1462945 := bbase (se 2 (by rfl) ⟨548604, by rfl⟩ : syracuseStep 1462945 = 1097209) (by norm_num)
theorem B1389241 : Blo 1299968 1389241 := bbase (se 2 (by rfl) ⟨520965, by rfl⟩ : syracuseStep 1389241 = 1041931) (by norm_num)
theorem B1462981 : Blo 1299968 1462981 := bbase (se 4 (by rfl) ⟨137154, by rfl⟩ : syracuseStep 1462981 = 274309) (by norm_num)
theorem B2929373 : Blo 1299968 2929373 := bbase (se 3 (by rfl) ⟨549257, by rfl⟩ : syracuseStep 2929373 = 1098515) (by norm_num)
theorem B1463017 : Blo 1299968 1463017 := bbase (se 2 (by rfl) ⟨548631, by rfl⟩ : syracuseStep 1463017 = 1097263) (by norm_num)
theorem B1463053 : Blo 1299968 1463053 := bbase (se 3 (by rfl) ⟨274322, by rfl⟩ : syracuseStep 1463053 = 548645) (by norm_num)
theorem B1463089 : Blo 1299968 1463089 := bbase (se 2 (by rfl) ⟨548658, by rfl⟩ : syracuseStep 1463089 = 1097317) (by norm_num)
theorem B2470733 : Blo 1299968 2470733 := bbase (se 3 (by rfl) ⟨463262, by rfl⟩ : syracuseStep 2470733 = 926525) (by norm_num)
theorem B1463125 : Blo 1299968 1463125 := bbase (se 9 (by rfl) ⟨4286, by rfl⟩ : syracuseStep 1463125 = 8573) (by norm_num)
theorem B1463161 : Blo 1299968 1463161 := bbase (se 2 (by rfl) ⟨548685, by rfl⟩ : syracuseStep 1463161 = 1097371) (by norm_num)
theorem B1463197 : Blo 1299968 1463197 := bbase (se 3 (by rfl) ⟨274349, by rfl⟩ : syracuseStep 1463197 = 548699) (by norm_num)
theorem B1463233 : Blo 1299968 1463233 := bbase (se 2 (by rfl) ⟨548712, by rfl⟩ : syracuseStep 1463233 = 1097425) (by norm_num)
theorem B1463269 : Blo 1299968 1463269 := bbase (se 4 (by rfl) ⟨137181, by rfl⟩ : syracuseStep 1463269 = 274363) (by norm_num)
theorem B4166645 : Blo 1299968 4166645 := bbase (se 5 (by rfl) ⟨195311, by rfl⟩ : syracuseStep 4166645 = 390623) (by norm_num)
theorem B1463305 : Blo 1299968 1463305 := bbase (se 2 (by rfl) ⟨548739, by rfl⟩ : syracuseStep 1463305 = 1097479) (by norm_num)
theorem B4387877 : Blo 1299968 4387877 := bbase (se 4 (by rfl) ⟨411363, by rfl⟩ : syracuseStep 4387877 = 822727) (by norm_num)
theorem B1463341 : Blo 1299968 1463341 := bbase (se 3 (by rfl) ⟨274376, by rfl⟩ : syracuseStep 1463341 = 548753) (by norm_num)
theorem B1463377 : Blo 1299968 1463377 := bbase (se 2 (by rfl) ⟨548766, by rfl⟩ : syracuseStep 1463377 = 1097533) (by norm_num)
theorem B1463413 : Blo 1299968 1463413 := bbase (se 5 (by rfl) ⟨68597, by rfl⟩ : syracuseStep 1463413 = 137195) (by norm_num)
theorem B1389685 : Blo 1299968 1389685 := bbase (se 5 (by rfl) ⟨65141, by rfl⟩ : syracuseStep 1389685 = 130283) (by norm_num)
theorem B1979525 : Blo 1299968 1979525 := bbase (se 4 (by rfl) ⟨185580, by rfl⟩ : syracuseStep 1979525 = 371161) (by norm_num)
theorem B16888981 : Blo 1299968 16888981 := bbase (se 6 (by rfl) ⟨395835, by rfl⟩ : syracuseStep 16888981 = 791671) (by norm_num)
theorem B1463449 : Blo 1299968 1463449 := bbase (se 2 (by rfl) ⟨548793, by rfl⟩ : syracuseStep 1463449 = 1097587) (by norm_num)
theorem B1389745 : Blo 1299968 1389745 := bbase (se 2 (by rfl) ⟨521154, by rfl⟩ : syracuseStep 1389745 = 1042309) (by norm_num)
theorem B1463485 : Blo 1299968 1463485 := bbase (se 3 (by rfl) ⟨274403, by rfl⟩ : syracuseStep 1463485 = 548807) (by norm_num)
theorem B1463521 : Blo 1299968 1463521 := bbase (se 2 (by rfl) ⟨548820, by rfl⟩ : syracuseStep 1463521 = 1097641) (by norm_num)
theorem B1463557 : Blo 1299968 1463557 := bbase (se 4 (by rfl) ⟨137208, by rfl⟩ : syracuseStep 1463557 = 274417) (by norm_num)
theorem B16676117 : Blo 1299968 16676117 := bbase (se 6 (by rfl) ⟨390846, by rfl⟩ : syracuseStep 16676117 = 781693) (by norm_num)
theorem B1463593 : Blo 1299968 1463593 := bbase (se 2 (by rfl) ⟨548847, by rfl⟩ : syracuseStep 1463593 = 1097695) (by norm_num)
theorem B2225461 : Blo 1299968 2225461 := bbase (se 5 (by rfl) ⟨104318, by rfl⟩ : syracuseStep 2225461 = 208637) (by norm_num)
theorem B1463629 : Blo 1299968 1463629 := bbase (se 3 (by rfl) ⟨274430, by rfl⟩ : syracuseStep 1463629 = 548861) (by norm_num)
theorem B1463665 : Blo 1299968 1463665 := bbase (se 2 (by rfl) ⟨548874, by rfl⟩ : syracuseStep 1463665 = 1097749) (by norm_num)
theorem B1463701 : Blo 1299968 1463701 := bbase (se 6 (by rfl) ⟨34305, by rfl⟩ : syracuseStep 1463701 = 68611) (by norm_num)
theorem B1463737 : Blo 1299968 1463737 := bbase (se 2 (by rfl) ⟨548901, by rfl⟩ : syracuseStep 1463737 = 1097803) (by norm_num)
theorem B5559749 : Blo 1299968 5559749 := bbase (se 4 (by rfl) ⟨521226, by rfl⟩ : syracuseStep 5559749 = 1042453) (by norm_num)
theorem B4388309 : Blo 1299968 4388309 := bbase (se 7 (by rfl) ⟨51425, by rfl⟩ : syracuseStep 4388309 = 102851) (by norm_num)
theorem B1463773 : Blo 1299968 1463773 := bbase (se 3 (by rfl) ⟨274457, by rfl⟩ : syracuseStep 1463773 = 548915) (by norm_num)
theorem B1390061 : Blo 1299968 1390061 := bbase (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) (by norm_num)
theorem B1463809 : Blo 1299968 1463809 := bbase (se 2 (by rfl) ⟨548928, by rfl⟩ : syracuseStep 1463809 = 1097857) (by norm_num)
theorem B3290645 : Blo 1299968 3290645 := bbase (se 6 (by rfl) ⟨77124, by rfl⟩ : syracuseStep 3290645 = 154249) (by norm_num)
theorem B1463845 : Blo 1299968 1463845 := bbase (se 4 (by rfl) ⟨137235, by rfl⟩ : syracuseStep 1463845 = 274471) (by norm_num)
theorem B2471485 : Blo 1299968 2471485 := bbase (se 3 (by rfl) ⟨463403, by rfl⟩ : syracuseStep 2471485 = 926807) (by norm_num)
theorem B1463881 : Blo 1299968 1463881 := bbase (se 2 (by rfl) ⟨548955, by rfl⟩ : syracuseStep 1463881 = 1097911) (by norm_num)
theorem B8336981 : Blo 1299968 8336981 := bbase (se 8 (by rfl) ⟨48849, by rfl⟩ : syracuseStep 8336981 = 97699) (by norm_num)
theorem B1463917 : Blo 1299968 1463917 := bbase (se 3 (by rfl) ⟨274484, by rfl⟩ : syracuseStep 1463917 = 548969) (by norm_num)
theorem B1463953 : Blo 1299968 1463953 := bbase (se 2 (by rfl) ⟨548982, by rfl⟩ : syracuseStep 1463953 = 1097965) (by norm_num)
theorem B4937381 : Blo 1299968 4937381 := bbase (se 4 (by rfl) ⟨462879, by rfl⟩ : syracuseStep 4937381 = 925759) (by norm_num)
theorem B1463989 : Blo 1299968 1463989 := bbase (se 5 (by rfl) ⟨68624, by rfl⟩ : syracuseStep 1463989 = 137249) (by norm_num)
theorem B1447621 : Blo 1299968 1447621 := bbase (se 4 (by rfl) ⟨135714, by rfl⟩ : syracuseStep 1447621 = 271429) (by norm_num)
theorem B2471629 : Blo 1299968 2471629 := bbase (se 3 (by rfl) ⟨463430, by rfl⟩ : syracuseStep 2471629 = 926861) (by norm_num)
theorem B1464025 : Blo 1299968 1464025 := bbase (se 2 (by rfl) ⟨549009, by rfl⟩ : syracuseStep 1464025 = 1098019) (by norm_num)
theorem B1464061 : Blo 1299968 1464061 := bbase (se 3 (by rfl) ⟨274511, by rfl⟩ : syracuseStep 1464061 = 549023) (by norm_num)
theorem B1562377 : Blo 1299968 1562377 := bbase (se 2 (by rfl) ⟨585891, by rfl⟩ : syracuseStep 1562377 = 1171783) (by norm_num)
theorem B3127061 : Blo 1299968 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B1464097 : Blo 1299968 1464097 := bbase (se 2 (by rfl) ⟨549036, by rfl⟩ : syracuseStep 1464097 = 1098073) (by norm_num)
theorem B1464133 : Blo 1299968 1464133 := bbase (se 4 (by rfl) ⟨137262, by rfl⟩ : syracuseStep 1464133 = 274525) (by norm_num)
theorem B6584165 : Blo 1299968 6584165 := bbase (se 4 (by rfl) ⟨617265, by rfl⟩ : syracuseStep 6584165 = 1234531) (by norm_num)
theorem B1562473 : Blo 1299968 1562473 := bbase (se 2 (by rfl) ⟨585927, by rfl⟩ : syracuseStep 1562473 = 1171855) (by norm_num)
theorem B1464169 : Blo 1299968 1464169 := bbase (se 2 (by rfl) ⟨549063, by rfl⟩ : syracuseStep 1464169 = 1098127) (by norm_num)
theorem B3290989 : Blo 1299968 3290989 := bbase (se 3 (by rfl) ⟨617060, by rfl⟩ : syracuseStep 3290989 = 1234121) (by norm_num)
theorem B4388741 : Blo 1299968 4388741 := bbase (se 4 (by rfl) ⟨411444, by rfl⟩ : syracuseStep 4388741 = 822889) (by norm_num)
theorem B4167557 : Blo 1299968 4167557 := bbase (se 4 (by rfl) ⟨390708, by rfl⟩ : syracuseStep 4167557 = 781417) (by norm_num)
theorem B1464205 : Blo 1299968 1464205 := bbase (se 3 (by rfl) ⟨274538, by rfl⟩ : syracuseStep 1464205 = 549077) (by norm_num)
theorem B3127205 : Blo 1299968 3127205 := bbase (se 4 (by rfl) ⟨293175, by rfl⟩ : syracuseStep 3127205 = 586351) (by norm_num)
theorem B1669033 : Blo 1299968 1669033 := bbase (se 2 (by rfl) ⟨625887, by rfl⟩ : syracuseStep 1669033 = 1251775) (by norm_num)
theorem B1464241 : Blo 1299968 1464241 := bbase (se 2 (by rfl) ⟨549090, by rfl⟩ : syracuseStep 1464241 = 1098181) (by norm_num)
theorem B4937669 : Blo 1299968 4937669 := bbase (se 4 (by rfl) ⟨462906, by rfl⟩ : syracuseStep 4937669 = 925813) (by norm_num)
theorem B1464277 : Blo 1299968 1464277 := bbase (se 7 (by rfl) ⟨17159, by rfl⟩ : syracuseStep 1464277 = 34319) (by norm_num)
theorem B3291101 : Blo 1299968 3291101 := bbase (se 3 (by rfl) ⟨617081, by rfl⟩ : syracuseStep 3291101 = 1234163) (by norm_num)
theorem B1464313 : Blo 1299968 1464313 := bbase (se 2 (by rfl) ⟨549117, by rfl⟩ : syracuseStep 1464313 = 1098235) (by norm_num)
theorem B1464349 : Blo 1299968 1464349 := bbase (se 3 (by rfl) ⟨274565, by rfl⟩ : syracuseStep 1464349 = 549131) (by norm_num)
theorem B1464385 : Blo 1299968 1464385 := bbase (se 2 (by rfl) ⟨549144, by rfl⟩ : syracuseStep 1464385 = 1098289) (by norm_num)
theorem B3954757 : Blo 1299968 3954757 := bbase (se 4 (by rfl) ⟨370758, by rfl⟩ : syracuseStep 3954757 = 741517) (by norm_num)
theorem B1464421 : Blo 1299968 1464421 := bbase (se 4 (by rfl) ⟨137289, by rfl⟩ : syracuseStep 1464421 = 274579) (by norm_num)
theorem B1464457 : Blo 1299968 1464457 := bbase (se 2 (by rfl) ⟨549171, by rfl⟩ : syracuseStep 1464457 = 1098343) (by norm_num)
theorem B3291293 : Blo 1299968 3291293 := bbase (se 3 (by rfl) ⟨617117, by rfl⟩ : syracuseStep 3291293 = 1234235) (by norm_num)
theorem B1464493 : Blo 1299968 1464493 := bbase (se 3 (by rfl) ⟨274592, by rfl⟩ : syracuseStep 1464493 = 549185) (by norm_num)
theorem B12507317 : Blo 1299968 12507317 := bbase (se 5 (by rfl) ⟨586280, by rfl⟩ : syracuseStep 12507317 = 1172561) (by norm_num)
theorem B1464529 : Blo 1299968 1464529 := bbase (se 2 (by rfl) ⟨549198, by rfl⟩ : syracuseStep 1464529 = 1098397) (by norm_num)
theorem B7411925 : Blo 1299968 7411925 := bbase (se 7 (by rfl) ⟨86858, by rfl⟩ : syracuseStep 7411925 = 173717) (by norm_num)
theorem B3299557 : Blo 1299968 3299557 := bbase (se 4 (by rfl) ⟨309333, by rfl⟩ : syracuseStep 3299557 = 618667) (by norm_num)
theorem B1464565 : Blo 1299968 1464565 := bbase (se 5 (by rfl) ⟨68651, by rfl⟩ : syracuseStep 1464565 = 137303) (by norm_num)
theorem B1464601 : Blo 1299968 1464601 := bbase (se 2 (by rfl) ⟨549225, by rfl⟩ : syracuseStep 1464601 = 1098451) (by norm_num)
theorem B2193709 : Blo 1299968 2193709 := bbase (se 3 (by rfl) ⟨411320, by rfl⟩ : syracuseStep 2193709 = 822641) (by norm_num)
theorem B1407277 : Blo 1299968 1407277 := bbase (se 3 (by rfl) ⟨263864, by rfl⟩ : syracuseStep 1407277 = 527729) (by norm_num)
theorem B4389173 : Blo 1299968 4389173 := bbase (se 5 (by rfl) ⟨205742, by rfl⟩ : syracuseStep 4389173 = 411485) (by norm_num)
theorem B1464637 : Blo 1299968 1464637 := bbase (se 3 (by rfl) ⟨274619, by rfl⟩ : syracuseStep 1464637 = 549239) (by norm_num)
theorem B1759573 : Blo 1299968 1759573 := bbase (se 10 (by rfl) ⟨2577, by rfl⟩ : syracuseStep 1759573 = 5155) (by norm_num)
theorem B1464673 : Blo 1299968 1464673 := bbase (se 2 (by rfl) ⟨549252, by rfl⟩ : syracuseStep 1464673 = 1098505) (by norm_num)
theorem B2193797 : Blo 1299968 2193797 := bbase (se 4 (by rfl) ⟨205668, by rfl⟩ : syracuseStep 2193797 = 411337) (by norm_num)
theorem B1464709 : Blo 1299968 1464709 := bbase (se 4 (by rfl) ⟨137316, by rfl⟩ : syracuseStep 1464709 = 274633) (by norm_num)
theorem B8444341 : Blo 1299968 8444341 := bbase (se 5 (by rfl) ⟨395828, by rfl⟩ : syracuseStep 8444341 = 791657) (by norm_num)
theorem B5560757 : Blo 1299968 5560757 := bbase (se 5 (by rfl) ⟨260660, by rfl⟩ : syracuseStep 5560757 = 521321) (by norm_num)
theorem B6248933 : Blo 1299968 6248933 := bbase (se 4 (by rfl) ⟨585837, by rfl⟩ : syracuseStep 6248933 = 1171675) (by norm_num)
theorem B3291637 : Blo 1299968 3291637 := bbase (se 5 (by rfl) ⟨154295, by rfl⟩ : syracuseStep 3291637 = 308591) (by norm_num)
theorem B2193925 : Blo 1299968 2193925 := bbase (se 4 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 2193925 = 411361) (by norm_num)
theorem B2636317 : Blo 1299968 2636317 := bbase (se 3 (by rfl) ⟨494309, by rfl⟩ : syracuseStep 2636317 = 988619) (by norm_num)
theorem B2194013 : Blo 1299968 2194013 := bbase (se 3 (by rfl) ⟨411377, by rfl⟩ : syracuseStep 2194013 = 822755) (by norm_num)
theorem B3291749 : Blo 1299968 3291749 := bbase (se 4 (by rfl) ⟨308601, by rfl⟩ : syracuseStep 3291749 = 617203) (by norm_num)
theorem B1563257 : Blo 1299968 1563257 := bbase (se 2 (by rfl) ⟨586221, by rfl⟩ : syracuseStep 1563257 = 1172443) (by norm_num)
theorem B2194141 : Blo 1299968 2194141 := bbase (se 3 (by rfl) ⟨411401, by rfl⟩ : syracuseStep 2194141 = 822803) (by norm_num)
theorem B4389605 : Blo 1299968 4389605 := bbase (se 4 (by rfl) ⟨411525, by rfl⟩ : syracuseStep 4389605 = 823051) (by norm_num)
theorem B3291941 : Blo 1299968 3291941 := bbase (se 4 (by rfl) ⟨308619, by rfl⟩ : syracuseStep 3291941 = 617239) (by norm_num)
theorem B2194229 : Blo 1299968 2194229 := bbase (se 5 (by rfl) ⟨102854, by rfl⟩ : syracuseStep 2194229 = 205709) (by norm_num)
theorem B1645373 : Blo 1299968 1645373 := bbase (se 3 (by rfl) ⟨308507, by rfl⟩ : syracuseStep 1645373 = 617015) (by norm_num)
theorem B1645429 : Blo 1299968 1645429 := bbase (se 5 (by rfl) ⟨77129, by rfl⟩ : syracuseStep 1645429 = 154259) (by norm_num)
theorem B1563565 : Blo 1299968 1563565 := bbase (se 3 (by rfl) ⟨293168, by rfl⟩ : syracuseStep 1563565 = 586337) (by norm_num)
theorem B2194357 : Blo 1299968 2194357 := bbase (se 5 (by rfl) ⟨102860, by rfl⟩ : syracuseStep 2194357 = 205721) (by norm_num)
theorem B1645525 : Blo 1299968 1645525 := bbase (se 7 (by rfl) ⟨19283, by rfl⟩ : syracuseStep 1645525 = 38567) (by norm_num)
theorem B2194445 : Blo 1299968 2194445 := bbase (se 3 (by rfl) ⟨411458, by rfl⟩ : syracuseStep 2194445 = 822917) (by norm_num)
theorem B2636869 : Blo 1299968 2636869 := bbase (se 4 (by rfl) ⟨247206, by rfl⟩ : syracuseStep 2636869 = 494413) (by norm_num)
theorem B4938853 : Blo 1299968 4938853 := bbase (se 4 (by rfl) ⟨463017, by rfl⟩ : syracuseStep 4938853 = 926035) (by norm_num)
theorem B6585461 : Blo 1299968 6585461 := bbase (se 5 (by rfl) ⟨308693, by rfl⟩ : syracuseStep 6585461 = 617387) (by norm_num)
theorem B3292285 : Blo 1299968 3292285 := bbase (se 3 (by rfl) ⟨617303, by rfl⟩ : syracuseStep 3292285 = 1234607) (by norm_num)
theorem B1645697 : Blo 1299968 1645697 := bbase (se 2 (by rfl) ⟨617136, by rfl⟩ : syracuseStep 1645697 = 1234273) (by norm_num)
theorem B2194573 : Blo 1299968 2194573 := bbase (se 3 (by rfl) ⟨411482, by rfl⟩ : syracuseStep 2194573 = 822965) (by norm_num)
theorem B4390037 : Blo 1299968 4390037 := bbase (se 6 (by rfl) ⟨102891, by rfl⟩ : syracuseStep 4390037 = 205783) (by norm_num)
theorem B2636965 : Blo 1299968 2636965 := bbase (se 4 (by rfl) ⟨247215, by rfl⟩ : syracuseStep 2636965 = 494431) (by norm_num)
theorem B11115701 : Blo 1299968 11115701 := bbase (se 5 (by rfl) ⟨521048, by rfl⟩ : syracuseStep 11115701 = 1042097) (by norm_num)
theorem B1645753 : Blo 1299968 1645753 := bbase (se 2 (by rfl) ⟨617157, by rfl⟩ : syracuseStep 1645753 = 1234315) (by norm_num)
theorem B4168901 : Blo 1299968 4168901 := bbase (se 4 (by rfl) ⟨390834, by rfl⟩ : syracuseStep 4168901 = 781669) (by norm_num)
theorem B1408213 : Blo 1299968 1408213 := bbase (se 7 (by rfl) ⟨16502, by rfl⟩ : syracuseStep 1408213 = 33005) (by norm_num)
theorem B2194661 : Blo 1299968 2194661 := bbase (se 4 (by rfl) ⟨205749, by rfl⟩ : syracuseStep 2194661 = 411499) (by norm_num)
theorem B3292397 : Blo 1299968 3292397 := bbase (se 3 (by rfl) ⟨617324, by rfl⟩ : syracuseStep 3292397 = 1234649) (by norm_num)
theorem B1645849 : Blo 1299968 1645849 := bbase (se 2 (by rfl) ⟨617193, by rfl⟩ : syracuseStep 1645849 = 1234387) (by norm_num)
theorem B1563953 : Blo 1299968 1563953 := bbase (se 2 (by rfl) ⟨586482, by rfl⟩ : syracuseStep 1563953 = 1172965) (by norm_num)
theorem B5553461 : Blo 1299968 5553461 := bbase (se 5 (by rfl) ⟨260318, by rfl⟩ : syracuseStep 5553461 = 520637) (by norm_num)
theorem B11107637 : Blo 1299968 11107637 := bbase (se 5 (by rfl) ⟨520670, by rfl⟩ : syracuseStep 11107637 = 1041341) (by norm_num)
theorem B2194789 : Blo 1299968 2194789 := bbase (se 4 (by rfl) ⟨205761, by rfl⟩ : syracuseStep 2194789 = 411523) (by norm_num)
theorem B4939157 : Blo 1299968 4939157 := bbase (se 6 (by rfl) ⟨115761, by rfl⟩ : syracuseStep 4939157 = 231523) (by norm_num)
theorem B3702181 : Blo 1299968 3702181 := bbase (se 4 (by rfl) ⟨347079, by rfl⟩ : syracuseStep 3702181 = 694159) (by norm_num)
theorem B3292589 : Blo 1299968 3292589 := bbase (se 3 (by rfl) ⟨617360, by rfl⟩ : syracuseStep 3292589 = 1234721) (by norm_num)
theorem B2194877 : Blo 1299968 2194877 := bbase (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) (by norm_num)
theorem B1646021 : Blo 1299968 1646021 := bbase (se 4 (by rfl) ⟨154314, by rfl⟩ : syracuseStep 1646021 = 308629) (by norm_num)
theorem B1646077 : Blo 1299968 1646077 := bbase (se 3 (by rfl) ⟨308639, by rfl⟩ : syracuseStep 1646077 = 617279) (by norm_num)
theorem B2195005 : Blo 1299968 2195005 := bbase (se 3 (by rfl) ⟨411563, by rfl⟩ : syracuseStep 2195005 = 823127) (by norm_num)
theorem B3702341 : Blo 1299968 3702341 := bbase (se 4 (by rfl) ⟨347094, by rfl⟩ : syracuseStep 3702341 = 694189) (by norm_num)
theorem B4390469 : Blo 1299968 4390469 := bbase (se 4 (by rfl) ⟨411606, by rfl⟩ : syracuseStep 4390469 = 823213) (by norm_num)
theorem B1646173 : Blo 1299968 1646173 := bbase (se 3 (by rfl) ⟨308657, by rfl⟩ : syracuseStep 1646173 = 617315) (by norm_num)
theorem B1523333 : Blo 1299968 1523333 := bbase (se 4 (by rfl) ⟨142812, by rfl⟩ : syracuseStep 1523333 = 285625) (by norm_num)
theorem B2195093 : Blo 1299968 2195093 := bbase (se 6 (by rfl) ⟨51447, by rfl⟩ : syracuseStep 2195093 = 102895) (by norm_num)
theorem B3292933 : Blo 1299968 3292933 := bbase (se 4 (by rfl) ⟨308712, by rfl⟩ : syracuseStep 3292933 = 617425) (by norm_num)
theorem B1646345 : Blo 1299968 1646345 := bbase (se 2 (by rfl) ⟨617379, by rfl⟩ : syracuseStep 1646345 = 1234759) (by norm_num)
theorem B2195221 : Blo 1299968 2195221 := bbase (se 6 (by rfl) ⟨51450, by rfl⟩ : syracuseStep 2195221 = 102901) (by norm_num)
theorem B1408801 : Blo 1299968 1408801 := bbase (se 2 (by rfl) ⟨528300, by rfl⟩ : syracuseStep 1408801 = 1056601) (by norm_num)
theorem B3702581 : Blo 1299968 3702581 := bbase (se 5 (by rfl) ⟨173558, by rfl⟩ : syracuseStep 3702581 = 347117) (by norm_num)
theorem B1646401 : Blo 1299968 1646401 := bbase (se 2 (by rfl) ⟨617400, by rfl⟩ : syracuseStep 1646401 = 1234801) (by norm_num)
theorem B2195309 : Blo 1299968 2195309 := bbase (se 3 (by rfl) ⟨411620, by rfl⟩ : syracuseStep 2195309 = 823241) (by norm_num)
theorem B2342773 : Blo 1299968 2342773 := bbase (se 5 (by rfl) ⟨109817, by rfl⟩ : syracuseStep 2342773 = 219635) (by norm_num)
theorem B3293045 : Blo 1299968 3293045 := bbase (se 5 (by rfl) ⟨154361, by rfl⟩ : syracuseStep 3293045 = 308723) (by norm_num)
theorem B1646497 : Blo 1299968 1646497 := bbase (se 2 (by rfl) ⟨617436, by rfl⟩ : syracuseStep 1646497 = 1234873) (by norm_num)
theorem B3170213 : Blo 1299968 3170213 := bbase (se 4 (by rfl) ⟨297207, by rfl⟩ : syracuseStep 3170213 = 594415) (by norm_num)
theorem B1851341 : Blo 1299968 1851341 := bbase (se 3 (by rfl) ⟨347126, by rfl⟩ : syracuseStep 1851341 = 694253) (by norm_num)
theorem B5930965 : Blo 1299968 5930965 := bbase (se 7 (by rfl) ⟨69503, by rfl⟩ : syracuseStep 5930965 = 139007) (by norm_num)
theorem B2195437 : Blo 1299968 2195437 := bbase (se 3 (by rfl) ⟨411644, by rfl⟩ : syracuseStep 2195437 = 823289) (by norm_num)
theorem B3702773 : Blo 1299968 3702773 := bbase (se 5 (by rfl) ⟨173567, by rfl⟩ : syracuseStep 3702773 = 347135) (by norm_num)
theorem B4390901 : Blo 1299968 4390901 := bbase (se 5 (by rfl) ⟨205823, by rfl⟩ : syracuseStep 4390901 = 411647) (by norm_num)
theorem B7913477 : Blo 1299968 7913477 := bstep (se 4 (by rfl) ⟨741888, by rfl⟩ : syracuseStep 7913477 = 1483777) B1483777
theorem B3702797 : Blo 1299968 3702797 := bstep (se 3 (by rfl) ⟨694274, by rfl⟩ : syracuseStep 3702797 = 1388549) B1388549
theorem B1851427 : Blo 1299968 1851427 := bstep (se 1 (by rfl) ⟨1388570, by rfl⟩ : syracuseStep 1851427 = 2777141) B2777141
theorem B4939811 : Blo 1299968 4939811 := bstep (se 1 (by rfl) ⟨3704858, by rfl⟩ : syracuseStep 4939811 = 7409717) B7409717
theorem B2195491 : Blo 1299968 2195491 := bstep (se 1 (by rfl) ⟨1646618, by rfl⟩ : syracuseStep 2195491 = 3293237) B3293237
theorem B4939825 : Blo 1299968 4939825 := bstep (se 2 (by rfl) ⟨1852434, by rfl⟩ : syracuseStep 4939825 = 3704869) B3704869
theorem B1646659 : Blo 1299968 1646659 := bstep (se 1 (by rfl) ⟨1234994, by rfl⟩ : syracuseStep 1646659 = 2469989) B2469989
theorem B2637955 : Blo 1299968 2637955 := bstep (se 1 (by rfl) ⟨1978466, by rfl⟩ : syracuseStep 2637955 = 3956933) B3956933
theorem B2113697 : Blo 1299968 2113697 := bstep (se 2 (by rfl) ⟨792636, by rfl⟩ : syracuseStep 2113697 = 1585273) B1585273
theorem B2195633 : Blo 1299968 2195633 := bstep (se 2 (by rfl) ⟨823362, by rfl⟩ : syracuseStep 2195633 = 1646725) B1646725
theorem B4391117 : Blo 1299968 4391117 := bstep (se 3 (by rfl) ⟨823334, by rfl⟩ : syracuseStep 4391117 = 1646669) B1646669
theorem B6586595 : Blo 1299968 6586595 := bstep (se 1 (by rfl) ⟨4939946, by rfl⟩ : syracuseStep 6586595 = 9879893) B9879893
theorem B4391171 : Blo 1299968 4391171 := bstep (se 1 (by rfl) ⟨3293378, by rfl⟩ : syracuseStep 4391171 = 6586757) B6586757
theorem B3957005 : Blo 1299968 3957005 := bstep (se 3 (by rfl) ⟨741938, by rfl⟩ : syracuseStep 3957005 = 1483877) B1483877
theorem B1949969 : Blo 1299968 1949969 := bstep (se 2 (by rfl) ⟨731238, by rfl⟩ : syracuseStep 1949969 = 1462477) B1462477
theorem B1949987 : Blo 1299968 1949987 := bstep (se 1 (by rfl) ⟨1462490, by rfl⟩ : syracuseStep 1949987 = 2924981) B2924981
theorem B4399409 : Blo 1299968 4399409 := bstep (se 2 (by rfl) ⟨1649778, by rfl⟩ : syracuseStep 4399409 = 3299557) B3299557
theorem B2195761 : Blo 1299968 2195761 := bstep (se 2 (by rfl) ⟨823410, by rfl⟩ : syracuseStep 2195761 = 1646821) B1646821
theorem B1950017 : Blo 1299968 1950017 := bstep (se 2 (by rfl) ⟨731256, by rfl⟩ : syracuseStep 1950017 = 1462513) B1462513
theorem B1950035 : Blo 1299968 1950035 := bstep (se 1 (by rfl) ⟨1462526, by rfl⟩ : syracuseStep 1950035 = 2925053) B2925053
theorem B2195795 : Blo 1299968 2195795 := bstep (se 1 (by rfl) ⟨1646846, by rfl⟩ : syracuseStep 2195795 = 3293693) B3293693
theorem B1950065 : Blo 1299968 1950065 := bstep (se 2 (by rfl) ⟨731274, by rfl⟩ : syracuseStep 1950065 = 1462549) B1462549
theorem B1851763 : Blo 1299968 1851763 := bstep (se 1 (by rfl) ⟨1388822, by rfl⟩ : syracuseStep 1851763 = 2777645) B2777645
theorem B1950083 : Blo 1299968 1950083 := bstep (se 1 (by rfl) ⟨1462562, by rfl⟩ : syracuseStep 1950083 = 2925125) B2925125
theorem B2924945 : Blo 1299968 2924945 := bstep (se 2 (by rfl) ⟨1096854, by rfl⟩ : syracuseStep 2924945 = 2193709) B2193709
theorem B1950113 : Blo 1299968 1950113 := bstep (se 2 (by rfl) ⟨731292, by rfl⟩ : syracuseStep 1950113 = 1462585) B1462585
theorem B2924963 : Blo 1299968 2924963 := bstep (se 1 (by rfl) ⟨2193722, by rfl⟩ : syracuseStep 2924963 = 4387445) B4387445
theorem B5005745 : Blo 1299968 5005745 := bstep (se 2 (by rfl) ⟨1877154, by rfl⟩ : syracuseStep 5005745 = 3754309) B3754309
theorem B1950131 : Blo 1299968 1950131 := bstep (se 1 (by rfl) ⟨1462598, by rfl⟩ : syracuseStep 1950131 = 2925197) B2925197
theorem B1950161 : Blo 1299968 1950161 := bstep (se 2 (by rfl) ⟨731310, by rfl⟩ : syracuseStep 1950161 = 1462621) B1462621
theorem B2195923 : Blo 1299968 2195923 := bstep (se 1 (by rfl) ⟨1646942, by rfl⟩ : syracuseStep 2195923 = 3293885) B3293885
theorem B1950179 : Blo 1299968 1950179 := bstep (se 1 (by rfl) ⟨1462634, by rfl⟩ : syracuseStep 1950179 = 2925269) B2925269
theorem B1950209 : Blo 1299968 1950209 := bstep (se 2 (by rfl) ⟨731328, by rfl⟩ : syracuseStep 1950209 = 1462657) B1462657
theorem B7406093 : Blo 1299968 7406093 := bstep (se 3 (by rfl) ⟨1388642, by rfl⟩ : syracuseStep 7406093 = 2777285) B2777285
theorem B4391441 : Blo 1299968 4391441 := bstep (se 2 (by rfl) ⟨1646790, by rfl⟩ : syracuseStep 4391441 = 3293581) B3293581
theorem B1950227 : Blo 1299968 1950227 := bstep (se 1 (by rfl) ⟨1462670, by rfl⟩ : syracuseStep 1950227 = 2925341) B2925341
theorem B1950257 : Blo 1299968 1950257 := bstep (se 2 (by rfl) ⟨731346, by rfl⟩ : syracuseStep 1950257 = 1462693) B1462693
theorem B1647155 : Blo 1299968 1647155 := bstep (se 1 (by rfl) ⟨1235366, by rfl⟩ : syracuseStep 1647155 = 2470733) B2470733
theorem B1950275 : Blo 1299968 1950275 := bstep (se 1 (by rfl) ⟨1462706, by rfl⟩ : syracuseStep 1950275 = 2925413) B2925413
theorem B1950305 : Blo 1299968 1950305 := bstep (se 2 (by rfl) ⟨731364, by rfl⟩ : syracuseStep 1950305 = 1462729) B1462729
theorem B2196065 : Blo 1299968 2196065 := bstep (se 2 (by rfl) ⟨823524, by rfl⟩ : syracuseStep 2196065 = 1647049) B1647049
theorem B1950323 : Blo 1299968 1950323 := bstep (se 1 (by rfl) ⟨1462742, by rfl⟩ : syracuseStep 1950323 = 2925485) B2925485
theorem B1950353 : Blo 1299968 1950353 := bstep (se 2 (by rfl) ⟨731382, by rfl⟩ : syracuseStep 1950353 = 1462765) B1462765
theorem B1950371 : Blo 1299968 1950371 := bstep (se 1 (by rfl) ⟨1462778, by rfl⟩ : syracuseStep 1950371 = 2925557) B2925557
theorem B2925233 : Blo 1299968 2925233 := bstep (se 2 (by rfl) ⟨1096962, by rfl⟩ : syracuseStep 2925233 = 2193925) B2193925
theorem B1950401 : Blo 1299968 1950401 := bstep (se 2 (by rfl) ⟨731400, by rfl⟩ : syracuseStep 1950401 = 1462801) B1462801
theorem B2925251 : Blo 1299968 2925251 := bstep (se 1 (by rfl) ⟨2193938, by rfl⟩ : syracuseStep 2925251 = 4387877) B4387877
theorem B15819461 : Blo 1299968 15819461 := bstep (se 4 (by rfl) ⟨1483074, by rfl⟩ : syracuseStep 15819461 = 2966149) B2966149
theorem B7914181 : Blo 1299968 7914181 := bstep (se 4 (by rfl) ⟨741954, by rfl⟩ : syracuseStep 7914181 = 1483909) B1483909
theorem B3515089 : Blo 1299968 3515089 := bstep (se 2 (by rfl) ⟨1318158, by rfl⟩ : syracuseStep 3515089 = 2636317) B2636317
theorem B3293905 : Blo 1299968 3293905 := bstep (se 2 (by rfl) ⟨1235214, by rfl⟩ : syracuseStep 3293905 = 2470429) B2470429
theorem B1950419 : Blo 1299968 1950419 := bstep (se 1 (by rfl) ⟨1462814, by rfl⟩ : syracuseStep 1950419 = 2925629) B2925629
theorem B2196193 : Blo 1299968 2196193 := bstep (se 2 (by rfl) ⟨823572, by rfl⟩ : syracuseStep 2196193 = 1647145) B1647145
theorem B1950449 : Blo 1299968 1950449 := bstep (se 2 (by rfl) ⟨731418, by rfl⟩ : syracuseStep 1950449 = 1462837) B1462837
theorem B1950467 : Blo 1299968 1950467 := bstep (se 1 (by rfl) ⟨1462850, by rfl⟩ : syracuseStep 1950467 = 2925701) B2925701
theorem B2196227 : Blo 1299968 2196227 := bstep (se 1 (by rfl) ⟨1647170, by rfl⟩ : syracuseStep 2196227 = 3294341) B3294341
theorem B1319683 : Blo 1299968 1319683 := bstep (se 1 (by rfl) ⟨989762, by rfl⟩ : syracuseStep 1319683 = 1979525) B1979525
theorem B1950497 : Blo 1299968 1950497 := bstep (se 2 (by rfl) ⟨731436, by rfl⟩ : syracuseStep 1950497 = 1462873) B1462873
theorem B4170541 : Blo 1299968 4170541 := bstep (se 3 (by rfl) ⟨781976, by rfl⟩ : syracuseStep 4170541 = 1563953) B1563953
theorem B1950515 : Blo 1299968 1950515 := bstep (se 1 (by rfl) ⟨1462886, by rfl⟩ : syracuseStep 1950515 = 2925773) B2925773
theorem B1950545 : Blo 1299968 1950545 := bstep (se 2 (by rfl) ⟨731454, by rfl⟩ : syracuseStep 1950545 = 1462909) B1462909
theorem B1950563 : Blo 1299968 1950563 := bstep (se 1 (by rfl) ⟨1462922, by rfl⟩ : syracuseStep 1950563 = 2925845) B2925845
theorem B11117411 : Blo 1299968 11117411 := bstep (se 1 (by rfl) ⟨8338058, by rfl⟩ : syracuseStep 11117411 = 16676117) B16676117
theorem B2777969 : Blo 1299968 2777969 := bstep (se 2 (by rfl) ⟨1041738, by rfl⟩ : syracuseStep 2777969 = 2083477) B2083477
theorem B15827825 : Blo 1299968 15827825 := bstep (se 2 (by rfl) ⟨5935434, by rfl⟩ : syracuseStep 15827825 = 11870869) B11870869
theorem B1950593 : Blo 1299968 1950593 := bstep (se 2 (by rfl) ⟨731472, by rfl⟩ : syracuseStep 1950593 = 1462945) B1462945
theorem B2343811 : Blo 1299968 2343811 := bstep (se 1 (by rfl) ⟨1757858, by rfl⟩ : syracuseStep 2343811 = 3515717) B3515717
theorem B2196355 : Blo 1299968 2196355 := bstep (se 1 (by rfl) ⟨1647266, by rfl⟩ : syracuseStep 2196355 = 3294533) B3294533
theorem B1950611 : Blo 1299968 1950611 := bstep (se 1 (by rfl) ⟨1462958, by rfl⟩ : syracuseStep 1950611 = 2925917) B2925917
theorem B1852321 : Blo 1299968 1852321 := bstep (se 2 (by rfl) ⟨694620, by rfl⟩ : syracuseStep 1852321 = 1389241) B1389241
theorem B1950641 : Blo 1299968 1950641 := bstep (se 2 (by rfl) ⟨731490, by rfl⟩ : syracuseStep 1950641 = 1462981) B1462981
theorem B1950659 : Blo 1299968 1950659 := bstep (se 1 (by rfl) ⟨1462994, by rfl⟩ : syracuseStep 1950659 = 2925989) B2925989
theorem B1852355 : Blo 1299968 1852355 := bstep (se 1 (by rfl) ⟨1389266, by rfl⟩ : syracuseStep 1852355 = 2778533) B2778533
theorem B2925521 : Blo 1299968 2925521 := bstep (se 2 (by rfl) ⟨1097070, by rfl⟩ : syracuseStep 2925521 = 2194141) B2194141
theorem B1950689 : Blo 1299968 1950689 := bstep (se 2 (by rfl) ⟨731508, by rfl⟩ : syracuseStep 1950689 = 1463017) B1463017
theorem B2925539 : Blo 1299968 2925539 := bstep (se 1 (by rfl) ⟨2194154, by rfl⟩ : syracuseStep 2925539 = 4388309) B4388309
theorem B5932003 : Blo 1299968 5932003 := bstep (se 1 (by rfl) ⟨4449002, by rfl⟩ : syracuseStep 5932003 = 8898005) B8898005
theorem B3294179 : Blo 1299968 3294179 := bstep (se 1 (by rfl) ⟨2470634, by rfl⟩ : syracuseStep 3294179 = 4941269) B4941269
theorem B1950707 : Blo 1299968 1950707 := bstep (se 1 (by rfl) ⟨1463030, by rfl⟩ : syracuseStep 1950707 = 2926061) B2926061
theorem B6587405 : Blo 1299968 6587405 := bstep (se 3 (by rfl) ⟨1235138, by rfl⟩ : syracuseStep 6587405 = 2470277) B2470277
theorem B1950737 : Blo 1299968 1950737 := bstep (se 2 (by rfl) ⟨731526, by rfl⟩ : syracuseStep 1950737 = 1463053) B1463053
theorem B2196497 : Blo 1299968 2196497 := bstep (se 2 (by rfl) ⟨823686, by rfl⟩ : syracuseStep 2196497 = 1647373) B1647373
theorem B1950755 : Blo 1299968 1950755 := bstep (se 1 (by rfl) ⟨1463066, by rfl⟩ : syracuseStep 1950755 = 2926133) B2926133
theorem B4391981 : Blo 1299968 4391981 := bstep (se 3 (by rfl) ⟨823496, by rfl⟩ : syracuseStep 4391981 = 1646993) B1646993
theorem B1950785 : Blo 1299968 1950785 := bstep (se 2 (by rfl) ⟨731544, by rfl⟩ : syracuseStep 1950785 = 1463089) B1463089
theorem B1950803 : Blo 1299968 1950803 := bstep (se 1 (by rfl) ⟨1463102, by rfl⟩ : syracuseStep 1950803 = 2926205) B2926205
theorem B4392035 : Blo 1299968 4392035 := bstep (se 1 (by rfl) ⟨3294026, by rfl⟩ : syracuseStep 4392035 = 6588053) B6588053
theorem B1950833 : Blo 1299968 1950833 := bstep (se 2 (by rfl) ⟨731562, by rfl⟩ : syracuseStep 1950833 = 1463125) B1463125
theorem B5276785 : Blo 1299968 5276785 := bstep (se 2 (by rfl) ⟨1978794, by rfl⟩ : syracuseStep 5276785 = 3957589) B3957589
theorem B1950851 : Blo 1299968 1950851 := bstep (se 1 (by rfl) ⟨1463138, by rfl⟩ : syracuseStep 1950851 = 2926277) B2926277
theorem B2196625 : Blo 1299968 2196625 := bstep (se 2 (by rfl) ⟨823734, by rfl⟩ : syracuseStep 2196625 = 1647469) B1647469
theorem B1950881 : Blo 1299968 1950881 := bstep (se 2 (by rfl) ⟨731580, by rfl⟩ : syracuseStep 1950881 = 1463161) B1463161
theorem B3294371 : Blo 1299968 3294371 := bstep (se 1 (by rfl) ⟨2470778, by rfl⟩ : syracuseStep 3294371 = 4941557) B4941557
theorem B3703981 : Blo 1299968 3703981 := bstep (se 3 (by rfl) ⟨694496, by rfl⟩ : syracuseStep 3703981 = 1388993) B1388993
theorem B1950899 : Blo 1299968 1950899 := bstep (se 1 (by rfl) ⟨1463174, by rfl⟩ : syracuseStep 1950899 = 2926349) B2926349
theorem B2196659 : Blo 1299968 2196659 := bstep (se 1 (by rfl) ⟨1647494, by rfl⟩ : syracuseStep 2196659 = 3294989) B3294989
theorem B1950929 : Blo 1299968 1950929 := bstep (se 2 (by rfl) ⟨731598, by rfl⟩ : syracuseStep 1950929 = 1463197) B1463197
theorem B1950947 : Blo 1299968 1950947 := bstep (se 1 (by rfl) ⟨1463210, by rfl⟩ : syracuseStep 1950947 = 2926421) B2926421
theorem B2925809 : Blo 1299968 2925809 := bstep (se 2 (by rfl) ⟨1097178, by rfl⟩ : syracuseStep 2925809 = 2194357) B2194357
theorem B1950977 : Blo 1299968 1950977 := bstep (se 2 (by rfl) ⟨731616, by rfl⟩ : syracuseStep 1950977 = 1463233) B1463233
theorem B2925827 : Blo 1299968 2925827 := bstep (se 1 (by rfl) ⟨2194370, by rfl⟩ : syracuseStep 2925827 = 4388741) B4388741
theorem B2778371 : Blo 1299968 2778371 := bstep (se 1 (by rfl) ⟨2083778, by rfl⟩ : syracuseStep 2778371 = 4167557) B4167557
theorem B1950995 : Blo 1299968 1950995 := bstep (se 1 (by rfl) ⟨1463246, by rfl⟩ : syracuseStep 1950995 = 2926493) B2926493
theorem B1951025 : Blo 1299968 1951025 := bstep (se 2 (by rfl) ⟨731634, by rfl⟩ : syracuseStep 1951025 = 1463269) B1463269
theorem B2196787 : Blo 1299968 2196787 := bstep (se 1 (by rfl) ⟨1647590, by rfl⟩ : syracuseStep 2196787 = 3295181) B3295181
theorem B1951043 : Blo 1299968 1951043 := bstep (se 1 (by rfl) ⟨1463282, by rfl⟩ : syracuseStep 1951043 = 2926565) B2926565
theorem B1951073 : Blo 1299968 1951073 := bstep (se 2 (by rfl) ⟨731652, by rfl⟩ : syracuseStep 1951073 = 1463305) B1463305
theorem B4392305 : Blo 1299968 4392305 := bstep (se 2 (by rfl) ⟨1647114, by rfl⟩ : syracuseStep 4392305 = 3294229) B3294229
theorem B1951091 : Blo 1299968 1951091 := bstep (se 1 (by rfl) ⟨1463318, by rfl⟩ : syracuseStep 1951091 = 2926637) B2926637
theorem B1951121 : Blo 1299968 1951121 := bstep (se 2 (by rfl) ⟨731670, by rfl⟩ : syracuseStep 1951121 = 1463341) B1463341
theorem B1951139 : Blo 1299968 1951139 := bstep (se 1 (by rfl) ⟨1463354, by rfl⟩ : syracuseStep 1951139 = 2926709) B2926709
theorem B3515825 : Blo 1299968 3515825 := bstep (se 2 (by rfl) ⟨1318434, by rfl⟩ : syracuseStep 3515825 = 2636869) B2636869
theorem B1951169 : Blo 1299968 1951169 := bstep (se 2 (by rfl) ⟨731688, by rfl⟩ : syracuseStep 1951169 = 1463377) B1463377
theorem B2196929 : Blo 1299968 2196929 := bstep (se 2 (by rfl) ⟨823848, by rfl⟩ : syracuseStep 2196929 = 1647697) B1647697
theorem B1951187 : Blo 1299968 1951187 := bstep (se 1 (by rfl) ⟨1463390, by rfl⟩ : syracuseStep 1951187 = 2926781) B2926781
theorem B4941283 : Blo 1299968 4941283 := bstep (se 1 (by rfl) ⟨3705962, by rfl⟩ : syracuseStep 4941283 = 7411925) B7411925
theorem B1951217 : Blo 1299968 1951217 := bstep (se 2 (by rfl) ⟨731706, by rfl⟩ : syracuseStep 1951217 = 1463413) B1463413
theorem B1852913 : Blo 1299968 1852913 := bstep (se 2 (by rfl) ⟨694842, by rfl⟩ : syracuseStep 1852913 = 1389685) B1389685
theorem B1951235 : Blo 1299968 1951235 := bstep (se 1 (by rfl) ⟨1463426, by rfl⟩ : syracuseStep 1951235 = 2926853) B2926853
theorem B2926097 : Blo 1299968 2926097 := bstep (se 2 (by rfl) ⟨1097286, by rfl⟩ : syracuseStep 2926097 = 2194573) B2194573
theorem B1951265 : Blo 1299968 1951265 := bstep (se 2 (by rfl) ⟨731724, by rfl⟩ : syracuseStep 1951265 = 1463449) B1463449
theorem B2926115 : Blo 1299968 2926115 := bstep (se 1 (by rfl) ⟨2194586, by rfl⟩ : syracuseStep 2926115 = 4389173) B4389173
theorem B1951283 : Blo 1299968 1951283 := bstep (se 1 (by rfl) ⟨1463462, by rfl⟩ : syracuseStep 1951283 = 2926925) B2926925
theorem B1852993 : Blo 1299968 1852993 := bstep (se 2 (by rfl) ⟨694872, by rfl⟩ : syracuseStep 1852993 = 1389745) B1389745
theorem B2197057 : Blo 1299968 2197057 := bstep (se 2 (by rfl) ⟨823896, by rfl⟩ : syracuseStep 2197057 = 1647793) B1647793
theorem B7505477 : Blo 1299968 7505477 := bstep (se 4 (by rfl) ⟨703638, by rfl⟩ : syracuseStep 7505477 = 1407277) B1407277
theorem B1951313 : Blo 1299968 1951313 := bstep (se 2 (by rfl) ⟨731742, by rfl⟩ : syracuseStep 1951313 = 1463485) B1463485
theorem B1951331 : Blo 1299968 1951331 := bstep (se 1 (by rfl) ⟨1463498, by rfl⟩ : syracuseStep 1951331 = 2926997) B2926997
theorem B1877617 : Blo 1299968 1877617 := bstep (se 2 (by rfl) ⟨704106, by rfl⟩ : syracuseStep 1877617 = 1408213) B1408213
theorem B1951361 : Blo 1299968 1951361 := bstep (se 2 (by rfl) ⟨731760, by rfl⟩ : syracuseStep 1951361 = 1463521) B1463521
theorem B1951379 : Blo 1299968 1951379 := bstep (se 1 (by rfl) ⟨1463534, by rfl⟩ : syracuseStep 1951379 = 2927069) B2927069
theorem B1951409 : Blo 1299968 1951409 := bstep (se 2 (by rfl) ⟨731778, by rfl⟩ : syracuseStep 1951409 = 1463557) B1463557
theorem B1951427 : Blo 1299968 1951427 := bstep (se 1 (by rfl) ⟨1463570, by rfl⟩ : syracuseStep 1951427 = 2927141) B2927141
theorem B1951457 : Blo 1299968 1951457 := bstep (se 2 (by rfl) ⟨731796, by rfl⟩ : syracuseStep 1951457 = 1463593) B1463593
theorem B2967281 : Blo 1299968 2967281 := bstep (se 2 (by rfl) ⟨1112730, by rfl⟩ : syracuseStep 2967281 = 2225461) B2225461
theorem B1951475 : Blo 1299968 1951475 := bstep (se 1 (by rfl) ⟨1463606, by rfl⟩ : syracuseStep 1951475 = 2927213) B2927213
theorem B4007693 : Blo 1299968 4007693 := bstep (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) B1502885
theorem B1951505 : Blo 1299968 1951505 := bstep (se 2 (by rfl) ⟨731814, by rfl⟩ : syracuseStep 1951505 = 1463629) B1463629
theorem B1951523 : Blo 1299968 1951523 := bstep (se 1 (by rfl) ⟨1463642, by rfl⟩ : syracuseStep 1951523 = 2927285) B2927285
theorem B2926385 : Blo 1299968 2926385 := bstep (se 2 (by rfl) ⟨1097394, by rfl⟩ : syracuseStep 2926385 = 2194789) B2194789
theorem B1951553 : Blo 1299968 1951553 := bstep (se 2 (by rfl) ⟨731832, by rfl⟩ : syracuseStep 1951553 = 1463665) B1463665
theorem B2926403 : Blo 1299968 2926403 := bstep (se 1 (by rfl) ⟨2194802, by rfl⟩ : syracuseStep 2926403 = 4389605) B4389605
theorem B1951571 : Blo 1299968 1951571 := bstep (se 1 (by rfl) ⟨1463678, by rfl⟩ : syracuseStep 1951571 = 2927357) B2927357
theorem B1951601 : Blo 1299968 1951601 := bstep (se 2 (by rfl) ⟨731850, by rfl⟩ : syracuseStep 1951601 = 1463701) B1463701
theorem B1951619 : Blo 1299968 1951619 := bstep (se 1 (by rfl) ⟨1463714, by rfl⟩ : syracuseStep 1951619 = 2927429) B2927429
theorem B8333189 : Blo 1299968 8333189 := bstep (se 4 (by rfl) ⟨781236, by rfl⟩ : syracuseStep 8333189 = 1562473) B1562473
theorem B4392845 : Blo 1299968 4392845 := bstep (se 3 (by rfl) ⟨823658, by rfl⟩ : syracuseStep 4392845 = 1647317) B1647317
theorem B1951649 : Blo 1299968 1951649 := bstep (se 2 (by rfl) ⟨731868, by rfl⟩ : syracuseStep 1951649 = 1463737) B1463737
theorem B1951667 : Blo 1299968 1951667 := bstep (se 1 (by rfl) ⟨1463750, by rfl⟩ : syracuseStep 1951667 = 2927501) B2927501
theorem B4392899 : Blo 1299968 4392899 := bstep (se 1 (by rfl) ⟨3294674, by rfl⟩ : syracuseStep 4392899 = 6589349) B6589349
theorem B1951697 : Blo 1299968 1951697 := bstep (se 2 (by rfl) ⟨731886, by rfl⟩ : syracuseStep 1951697 = 1463773) B1463773
theorem B12503011 : Blo 1299968 12503011 := bstep (se 1 (by rfl) ⟨9377258, by rfl⟩ : syracuseStep 12503011 = 18754517) B18754517
theorem B1951715 : Blo 1299968 1951715 := bstep (se 1 (by rfl) ⟨1463786, by rfl⟩ : syracuseStep 1951715 = 2927573) B2927573
theorem B1951745 : Blo 1299968 1951745 := bstep (se 2 (by rfl) ⟨731904, by rfl⟩ : syracuseStep 1951745 = 1463809) B1463809
theorem B1951763 : Blo 1299968 1951763 := bstep (se 1 (by rfl) ⟨1463822, by rfl⟩ : syracuseStep 1951763 = 2927645) B2927645
theorem B1951793 : Blo 1299968 1951793 := bstep (se 2 (by rfl) ⟨731922, by rfl⟩ : syracuseStep 1951793 = 1463845) B1463845
theorem B1951811 : Blo 1299968 1951811 := bstep (se 1 (by rfl) ⟨1463858, by rfl⟩ : syracuseStep 1951811 = 2927717) B2927717
theorem B2926673 : Blo 1299968 2926673 := bstep (se 2 (by rfl) ⟨1097502, by rfl⟩ : syracuseStep 2926673 = 2195005) B2195005
theorem B3295313 : Blo 1299968 3295313 := bstep (se 2 (by rfl) ⟨1235742, by rfl⟩ : syracuseStep 3295313 = 2471485) B2471485
theorem B1951841 : Blo 1299968 1951841 := bstep (se 2 (by rfl) ⟨731940, by rfl⟩ : syracuseStep 1951841 = 1463881) B1463881
theorem B2926691 : Blo 1299968 2926691 := bstep (se 1 (by rfl) ⟨2195018, by rfl⟩ : syracuseStep 2926691 = 4390037) B4390037
theorem B1951859 : Blo 1299968 1951859 := bstep (se 1 (by rfl) ⟨1463894, by rfl⟩ : syracuseStep 1951859 = 2927789) B2927789
theorem B2779267 : Blo 1299968 2779267 := bstep (se 1 (by rfl) ⟨2084450, by rfl⟩ : syracuseStep 2779267 = 4168901) B4168901
theorem B3295363 : Blo 1299968 3295363 := bstep (se 1 (by rfl) ⟨2471522, by rfl⟩ : syracuseStep 3295363 = 4943045) B4943045
theorem B1951889 : Blo 1299968 1951889 := bstep (se 2 (by rfl) ⟨731958, by rfl⟩ : syracuseStep 1951889 = 1463917) B1463917
theorem B1951907 : Blo 1299968 1951907 := bstep (se 1 (by rfl) ⟨1463930, by rfl⟩ : syracuseStep 1951907 = 2927861) B2927861
theorem B1951937 : Blo 1299968 1951937 := bstep (se 2 (by rfl) ⟨731976, by rfl⟩ : syracuseStep 1951937 = 1463953) B1463953
theorem B3705041 : Blo 1299968 3705041 := bstep (se 2 (by rfl) ⟨1389390, by rfl⟩ : syracuseStep 3705041 = 2778781) B2778781
theorem B4393169 : Blo 1299968 4393169 := bstep (se 2 (by rfl) ⟨1647438, by rfl⟩ : syracuseStep 4393169 = 3294877) B3294877
theorem B1951955 : Blo 1299968 1951955 := bstep (se 1 (by rfl) ⟨1463966, by rfl⟩ : syracuseStep 1951955 = 2927933) B2927933
theorem B1951985 : Blo 1299968 1951985 := bstep (se 2 (by rfl) ⟨731994, by rfl⟩ : syracuseStep 1951985 = 1463989) B1463989
theorem B1952003 : Blo 1299968 1952003 := bstep (se 1 (by rfl) ⟨1464002, by rfl⟩ : syracuseStep 1952003 = 2928005) B2928005
theorem B3295505 : Blo 1299968 3295505 := bstep (se 2 (by rfl) ⟨1235814, by rfl⟩ : syracuseStep 3295505 = 2471629) B2471629
theorem B1952033 : Blo 1299968 1952033 := bstep (se 2 (by rfl) ⟨732012, by rfl⟩ : syracuseStep 1952033 = 1464025) B1464025
theorem B1952051 : Blo 1299968 1952051 := bstep (se 1 (by rfl) ⟨1464038, by rfl⟩ : syracuseStep 1952051 = 2928077) B2928077
theorem B1952081 : Blo 1299968 1952081 := bstep (se 2 (by rfl) ⟨732030, by rfl⟩ : syracuseStep 1952081 = 1464061) B1464061
theorem B1853779 : Blo 1299968 1853779 := bstep (se 1 (by rfl) ⟨1390334, by rfl⟩ : syracuseStep 1853779 = 2780669) B2780669
theorem B2083169 : Blo 1299968 2083169 := bstep (se 2 (by rfl) ⟨781188, by rfl⟩ : syracuseStep 2083169 = 1562377) B1562377
theorem B1952099 : Blo 1299968 1952099 := bstep (se 1 (by rfl) ⟨1464074, by rfl⟩ : syracuseStep 1952099 = 2928149) B2928149
theorem B2926961 : Blo 1299968 2926961 := bstep (se 2 (by rfl) ⟨1097610, by rfl⟩ : syracuseStep 2926961 = 2195221) B2195221
theorem B1952129 : Blo 1299968 1952129 := bstep (se 2 (by rfl) ⟨732048, by rfl⟩ : syracuseStep 1952129 = 1464097) B1464097
theorem B1878401 : Blo 1299968 1878401 := bstep (se 2 (by rfl) ⟨704400, by rfl⟩ : syracuseStep 1878401 = 1408801) B1408801
theorem B2468227 : Blo 1299968 2468227 := bstep (se 1 (by rfl) ⟨1851170, by rfl⟩ : syracuseStep 2468227 = 3702341) B3702341
theorem B2926979 : Blo 1299968 2926979 := bstep (se 1 (by rfl) ⟨2195234, by rfl⟩ : syracuseStep 2926979 = 4390469) B4390469
theorem B1952147 : Blo 1299968 1952147 := bstep (se 1 (by rfl) ⟨1464110, by rfl⟩ : syracuseStep 1952147 = 2928221) B2928221
theorem B1952177 : Blo 1299968 1952177 := bstep (se 2 (by rfl) ⟨732066, by rfl⟩ : syracuseStep 1952177 = 1464133) B1464133
theorem B1952195 : Blo 1299968 1952195 := bstep (se 1 (by rfl) ⟨1464146, by rfl⟩ : syracuseStep 1952195 = 2928293) B2928293
theorem B2345411 : Blo 1299968 2345411 := bstep (se 1 (by rfl) ⟨1759058, by rfl⟩ : syracuseStep 2345411 = 3518117) B3518117
theorem B1952225 : Blo 1299968 1952225 := bstep (se 2 (by rfl) ⟨732084, by rfl⟩ : syracuseStep 1952225 = 1464169) B1464169
theorem B3123697 : Blo 1299968 3123697 := bstep (se 2 (by rfl) ⟨1171386, by rfl⟩ : syracuseStep 3123697 = 2342773) B2342773
theorem B1952243 : Blo 1299968 1952243 := bstep (se 1 (by rfl) ⟨1464182, by rfl⟩ : syracuseStep 1952243 = 2928365) B2928365
theorem B1952273 : Blo 1299968 1952273 := bstep (se 2 (by rfl) ⟨732102, by rfl⟩ : syracuseStep 1952273 = 1464205) B1464205
theorem B2468387 : Blo 1299968 2468387 := bstep (se 1 (by rfl) ⟨1851290, by rfl⟩ : syracuseStep 2468387 = 3702581) B3702581
theorem B1952291 : Blo 1299968 1952291 := bstep (se 1 (by rfl) ⟨1464218, by rfl⟩ : syracuseStep 1952291 = 2928437) B2928437
theorem B1952321 : Blo 1299968 1952321 := bstep (se 2 (by rfl) ⟨732120, by rfl⟩ : syracuseStep 1952321 = 1464241) B1464241
theorem B1952339 : Blo 1299968 1952339 := bstep (se 1 (by rfl) ⟨1464254, by rfl⟩ : syracuseStep 1952339 = 2928509) B2928509
theorem B7907953 : Blo 1299968 7907953 := bstep (se 2 (by rfl) ⟨2965482, by rfl⟩ : syracuseStep 7907953 = 5930965) B5930965
theorem B1952369 : Blo 1299968 1952369 := bstep (se 2 (by rfl) ⟨732138, by rfl⟩ : syracuseStep 1952369 = 1464277) B1464277
theorem B1952387 : Blo 1299968 1952387 := bstep (se 1 (by rfl) ⟨1464290, by rfl⟩ : syracuseStep 1952387 = 2928581) B2928581
theorem B9874061 : Blo 1299968 9874061 := bstep (se 3 (by rfl) ⟨1851386, by rfl⟩ : syracuseStep 9874061 = 3702773) B3702773
theorem B11111053 : Blo 1299968 11111053 := bstep (se 3 (by rfl) ⟨2083322, by rfl⟩ : syracuseStep 11111053 = 4166645) B4166645
theorem B2927249 : Blo 1299968 2927249 := bstep (se 2 (by rfl) ⟨1097718, by rfl⟩ : syracuseStep 2927249 = 2195437) B2195437
theorem B1952417 : Blo 1299968 1952417 := bstep (se 2 (by rfl) ⟨732156, by rfl⟩ : syracuseStep 1952417 = 1464313) B1464313
theorem B2927267 : Blo 1299968 2927267 := bstep (se 1 (by rfl) ⟨2195450, by rfl⟩ : syracuseStep 2927267 = 4390901) B4390901
theorem B2345635 : Blo 1299968 2345635 := bstep (se 1 (by rfl) ⟨1759226, by rfl⟩ : syracuseStep 2345635 = 3518453) B3518453
theorem B1952435 : Blo 1299968 1952435 := bstep (se 1 (by rfl) ⟨1464326, by rfl⟩ : syracuseStep 1952435 = 2928653) B2928653
theorem B1952465 : Blo 1299968 1952465 := bstep (se 2 (by rfl) ⟨732174, by rfl⟩ : syracuseStep 1952465 = 1464349) B1464349
theorem B1952483 : Blo 1299968 1952483 := bstep (se 1 (by rfl) ⟨1464362, by rfl⟩ : syracuseStep 1952483 = 2928725) B2928725
theorem B2345699 : Blo 1299968 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B4393709 : Blo 1299968 4393709 := bstep (se 3 (by rfl) ⟨823820, by rfl⟩ : syracuseStep 4393709 = 1647641) B1647641
theorem B1952513 : Blo 1299968 1952513 := bstep (se 2 (by rfl) ⟨732192, by rfl⟩ : syracuseStep 1952513 = 1464385) B1464385
theorem B1952531 : Blo 1299968 1952531 := bstep (se 1 (by rfl) ⟨1464398, by rfl⟩ : syracuseStep 1952531 = 2928797) B2928797
theorem B4393763 : Blo 1299968 4393763 := bstep (se 1 (by rfl) ⟨3295322, by rfl⟩ : syracuseStep 4393763 = 6590645) B6590645
theorem B1952561 : Blo 1299968 1952561 := bstep (se 2 (by rfl) ⟨732210, by rfl⟩ : syracuseStep 1952561 = 1464421) B1464421
theorem B1952579 : Blo 1299968 1952579 := bstep (se 1 (by rfl) ⟨1464434, by rfl⟩ : syracuseStep 1952579 = 2928869) B2928869
theorem B1952609 : Blo 1299968 1952609 := bstep (se 2 (by rfl) ⟨732228, by rfl⟩ : syracuseStep 1952609 = 1464457) B1464457
theorem B3705713 : Blo 1299968 3705713 := bstep (se 2 (by rfl) ⟨1389642, by rfl⟩ : syracuseStep 3705713 = 2779285) B2779285
theorem B1952627 : Blo 1299968 1952627 := bstep (se 1 (by rfl) ⟨1464470, by rfl⟩ : syracuseStep 1952627 = 2928941) B2928941
theorem B1952657 : Blo 1299968 1952657 := bstep (se 2 (by rfl) ⟨732246, by rfl⟩ : syracuseStep 1952657 = 1464493) B1464493
theorem B4688803 : Blo 1299968 4688803 := bstep (se 1 (by rfl) ⟨3516602, by rfl⟩ : syracuseStep 4688803 = 7033205) B7033205
theorem B1952675 : Blo 1299968 1952675 := bstep (se 1 (by rfl) ⟨1464506, by rfl⟩ : syracuseStep 1952675 = 2929013) B2929013
theorem B2927537 : Blo 1299968 2927537 := bstep (se 2 (by rfl) ⟨1097826, by rfl⟩ : syracuseStep 2927537 = 2195653) B2195653
theorem B1952705 : Blo 1299968 1952705 := bstep (se 2 (by rfl) ⟨732264, by rfl⟩ : syracuseStep 1952705 = 1464529) B1464529
theorem B2927555 : Blo 1299968 2927555 := bstep (se 1 (by rfl) ⟨2195666, by rfl⟩ : syracuseStep 2927555 = 4391333) B4391333
theorem B1952723 : Blo 1299968 1952723 := bstep (se 1 (by rfl) ⟨1464542, by rfl⟩ : syracuseStep 1952723 = 2929085) B2929085
theorem B1952753 : Blo 1299968 1952753 := bstep (se 2 (by rfl) ⟨732282, by rfl⟩ : syracuseStep 1952753 = 1464565) B1464565
theorem B1952771 : Blo 1299968 1952771 := bstep (se 1 (by rfl) ⟨1464578, by rfl⟩ : syracuseStep 1952771 = 2929157) B2929157
theorem B1952801 : Blo 1299968 1952801 := bstep (se 2 (by rfl) ⟨732300, by rfl⟩ : syracuseStep 1952801 = 1464601) B1464601
theorem B4394033 : Blo 1299968 4394033 := bstep (se 2 (by rfl) ⟨1647762, by rfl⟩ : syracuseStep 4394033 = 3295525) B3295525
theorem B1952819 : Blo 1299968 1952819 := bstep (se 1 (by rfl) ⟨1464614, by rfl⟩ : syracuseStep 1952819 = 2929229) B2929229
theorem B1977409 : Blo 1299968 1977409 := bstep (se 2 (by rfl) ⟨741528, by rfl⟩ : syracuseStep 1977409 = 1483057) B1483057
theorem B1952849 : Blo 1299968 1952849 := bstep (se 2 (by rfl) ⟨732318, by rfl⟩ : syracuseStep 1952849 = 1464637) B1464637
theorem B14068835 : Blo 1299968 14068835 := bstep (se 1 (by rfl) ⟨10551626, by rfl⟩ : syracuseStep 14068835 = 21103253) B21103253
theorem B1952867 : Blo 1299968 1952867 := bstep (se 1 (by rfl) ⟨1464650, by rfl⟩ : syracuseStep 1952867 = 2929301) B2929301
theorem B2346097 : Blo 1299968 2346097 := bstep (se 2 (by rfl) ⟨879786, by rfl⟩ : syracuseStep 2346097 = 1759573) B1759573
theorem B1952897 : Blo 1299968 1952897 := bstep (se 2 (by rfl) ⟨732336, by rfl⟩ : syracuseStep 1952897 = 1464673) B1464673
theorem B3124369 : Blo 1299968 3124369 := bstep (se 2 (by rfl) ⟨1171638, by rfl⟩ : syracuseStep 3124369 = 2343277) B2343277
theorem B1952915 : Blo 1299968 1952915 := bstep (se 1 (by rfl) ⟨1464686, by rfl⟩ : syracuseStep 1952915 = 2929373) B2929373
theorem B6581411 : Blo 1299968 6581411 := bstep (se 1 (by rfl) ⟨4936058, by rfl⟩ : syracuseStep 6581411 = 9872117) B9872117
theorem B1952945 : Blo 1299968 1952945 := bstep (se 2 (by rfl) ⟨732354, by rfl⟩ : syracuseStep 1952945 = 1464709) B1464709
theorem B2927825 : Blo 1299968 2927825 := bstep (se 2 (by rfl) ⟨1097934, by rfl⟩ : syracuseStep 2927825 = 2195869) B2195869
theorem B2927843 : Blo 1299968 2927843 := bstep (se 1 (by rfl) ⟨2195882, by rfl⟩ : syracuseStep 2927843 = 4391765) B4391765
theorem B11259121 : Blo 1299968 11259121 := bstep (se 2 (by rfl) ⟨4222170, by rfl⟩ : syracuseStep 11259121 = 8444341) B8444341
theorem B13348081 : Blo 1299968 13348081 := bstep (se 2 (by rfl) ⟨5005530, by rfl⟩ : syracuseStep 13348081 = 10011061) B10011061
theorem B2780497 : Blo 1299968 2780497 := bstep (se 2 (by rfl) ⟨1042686, by rfl⟩ : syracuseStep 2780497 = 2085373) B2085373
theorem B7409009 : Blo 1299968 7409009 := bstep (se 2 (by rfl) ⟨2778378, by rfl⟩ : syracuseStep 7409009 = 5556757) B5556757
theorem B4689265 : Blo 1299968 4689265 := bstep (se 2 (by rfl) ⟨1758474, by rfl⟩ : syracuseStep 4689265 = 3516949) B3516949
theorem B2928113 : Blo 1299968 2928113 := bstep (se 2 (by rfl) ⟨1098042, by rfl⟩ : syracuseStep 2928113 = 2196085) B2196085
theorem B2928131 : Blo 1299968 2928131 := bstep (se 1 (by rfl) ⟨2196098, by rfl⟩ : syracuseStep 2928131 = 4392197) B4392197
theorem B3517987 : Blo 1299968 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B2469457 : Blo 1299968 2469457 := bstep (se 2 (by rfl) ⟨926046, by rfl⟩ : syracuseStep 2469457 = 1852093) B1852093
theorem B3706499 : Blo 1299968 3706499 := bstep (se 1 (by rfl) ⟨2779874, by rfl⟩ : syracuseStep 3706499 = 5559749) B5559749
theorem B2502289 : Blo 1299968 2502289 := bstep (se 2 (by rfl) ⟨938358, by rfl⟩ : syracuseStep 2502289 = 1876717) B1876717
theorem B7720645 : Blo 1299968 7720645 := bstep (se 4 (by rfl) ⟨723810, by rfl⟩ : syracuseStep 7720645 = 1447621) B1447621
theorem B5557987 : Blo 1299968 5557987 := bstep (se 1 (by rfl) ⟨4168490, by rfl⟩ : syracuseStep 5557987 = 8336981) B8336981
theorem B2928401 : Blo 1299968 2928401 := bstep (se 2 (by rfl) ⟨1098150, by rfl⟩ : syracuseStep 2928401 = 2196301) B2196301
theorem B2928419 : Blo 1299968 2928419 := bstep (se 1 (by rfl) ⟨2196314, by rfl⟩ : syracuseStep 2928419 = 4392629) B4392629
theorem B2084707 : Blo 1299968 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B6590321 : Blo 1299968 6590321 := bstep (se 2 (by rfl) ⟨2471370, by rfl⟩ : syracuseStep 6590321 = 4942741) B4942741
theorem B2084753 : Blo 1299968 2084753 := bstep (se 2 (by rfl) ⟨781782, by rfl⟩ : syracuseStep 2084753 = 1563565) B1563565
theorem B1978273 : Blo 1299968 1978273 := bstep (se 2 (by rfl) ⟨741852, by rfl⟩ : syracuseStep 1978273 = 1483705) B1483705
theorem B11112389 : Blo 1299968 11112389 := bstep (se 4 (by rfl) ⟨1041786, by rfl⟩ : syracuseStep 11112389 = 2083573) B2083573
theorem B6582221 : Blo 1299968 6582221 := bstep (se 3 (by rfl) ⟨1234166, by rfl⟩ : syracuseStep 6582221 = 2468333) B2468333
theorem B3706829 : Blo 1299968 3706829 := bstep (se 3 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 3706829 = 1390061) B1390061
theorem B4222979 : Blo 1299968 4222979 := bstep (se 1 (by rfl) ⟨3167234, by rfl⟩ : syracuseStep 4222979 = 6334469) B6334469
theorem B3706897 : Blo 1299968 3706897 := bstep (se 2 (by rfl) ⟨1390086, by rfl⟩ : syracuseStep 3706897 = 2780173) B2780173
theorem B2928689 : Blo 1299968 2928689 := bstep (se 2 (by rfl) ⟨1098258, by rfl⟩ : syracuseStep 2928689 = 2196517) B2196517
theorem B2928707 : Blo 1299968 2928707 := bstep (se 1 (by rfl) ⟨2196530, by rfl⟩ : syracuseStep 2928707 = 4393061) B4393061
theorem B1880177 : Blo 1299968 1880177 := bstep (se 2 (by rfl) ⟨705066, by rfl⟩ : syracuseStep 1880177 = 1410133) B1410133
theorem B1462531 : Blo 1299968 1462531 := bstep (se 1 (by rfl) ⟨1096898, by rfl⟩ : syracuseStep 1462531 = 2193797) B2193797
theorem B3707171 : Blo 1299968 3707171 := bstep (se 1 (by rfl) ⟨2780378, by rfl⟩ : syracuseStep 3707171 = 5560757) B5560757
theorem B4165955 : Blo 1299968 4165955 := bstep (se 1 (by rfl) ⟨3124466, by rfl⟩ : syracuseStep 4165955 = 6248933) B6248933
theorem B2928977 : Blo 1299968 2928977 := bstep (se 2 (by rfl) ⟨1098366, by rfl⟩ : syracuseStep 2928977 = 2196733) B2196733
theorem B2928995 : Blo 1299968 2928995 := bstep (se 1 (by rfl) ⟨2196746, by rfl⟩ : syracuseStep 2928995 = 4393493) B4393493
theorem B1462675 : Blo 1299968 1462675 := bstep (se 1 (by rfl) ⟨1097006, by rfl⟩ : syracuseStep 1462675 = 2194013) B2194013
theorem B11121137 : Blo 1299968 11121137 := bstep (se 2 (by rfl) ⟨4170426, by rfl⟩ : syracuseStep 11121137 = 8340853) B8340853
theorem B7909901 : Blo 1299968 7909901 := bstep (se 3 (by rfl) ⟨1483106, by rfl⟩ : syracuseStep 7909901 = 2966213) B2966213
theorem B1462819 : Blo 1299968 1462819 := bstep (se 1 (by rfl) ⟨1097114, by rfl⟩ : syracuseStep 1462819 = 2194229) B2194229
theorem B4936241 : Blo 1299968 4936241 := bstep (se 2 (by rfl) ⟨1851090, by rfl⟩ : syracuseStep 4936241 = 3702181) B3702181
theorem B4166225 : Blo 1299968 4166225 := bstep (se 2 (by rfl) ⟨1562334, by rfl⟩ : syracuseStep 4166225 = 3124669) B3124669
theorem B1389155 : Blo 1299968 1389155 := bstep (se 1 (by rfl) ⟨1041866, by rfl⟩ : syracuseStep 1389155 = 2083733) B2083733
theorem B2470513 : Blo 1299968 2470513 := bstep (se 2 (by rfl) ⟨926442, by rfl⟩ : syracuseStep 2470513 = 1852885) B1852885
theorem B2929265 : Blo 1299968 2929265 := bstep (se 2 (by rfl) ⟨1098474, by rfl⟩ : syracuseStep 2929265 = 2196949) B2196949
theorem B2929283 : Blo 1299968 2929283 := bstep (se 1 (by rfl) ⟨2196962, by rfl⟩ : syracuseStep 2929283 = 4393925) B4393925
theorem B1462963 : Blo 1299968 1462963 := bstep (se 1 (by rfl) ⟨1097222, by rfl⟩ : syracuseStep 1462963 = 2194445) B2194445
theorem B13349603 : Blo 1299968 13349603 := bstep (se 1 (by rfl) ⟨10012202, by rfl⟩ : syracuseStep 13349603 = 20024405) B20024405
theorem B7410467 : Blo 1299968 7410467 := bstep (se 1 (by rfl) ⟨5557850, by rfl⟩ : syracuseStep 7410467 = 11115701) B11115701
theorem B1463107 : Blo 1299968 1463107 := bstep (se 1 (by rfl) ⟨1097330, by rfl⟩ : syracuseStep 1463107 = 2194661) B2194661
theorem B4387661 : Blo 1299968 4387661 := bstep (se 3 (by rfl) ⟨822686, by rfl⟩ : syracuseStep 4387661 = 1645373) B1645373
theorem B4387715 : Blo 1299968 4387715 := bstep (se 1 (by rfl) ⟨3290786, by rfl⟩ : syracuseStep 4387715 = 6581573) B6581573
theorem B1463251 : Blo 1299968 1463251 := bstep (se 1 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 1463251 = 2194877) B2194877
theorem B2470915 : Blo 1299968 2470915 := bstep (se 1 (by rfl) ⟨1853186, by rfl⟩ : syracuseStep 2470915 = 3706373) B3706373
theorem B2470961 : Blo 1299968 2470961 := bstep (se 2 (by rfl) ⟨926610, by rfl⟩ : syracuseStep 2470961 = 1853221) B1853221
theorem B1463395 : Blo 1299968 1463395 := bstep (se 1 (by rfl) ⟨1097546, by rfl⟩ : syracuseStep 1463395 = 2195093) B2195093
theorem B4387985 : Blo 1299968 4387985 := bstep (se 2 (by rfl) ⟨1645494, by rfl⟩ : syracuseStep 4387985 = 3290989) B3290989
theorem B4936909 : Blo 1299968 4936909 := bstep (se 3 (by rfl) ⟨925670, by rfl⟩ : syracuseStep 4936909 = 1851341) B1851341
theorem B2225377 : Blo 1299968 2225377 := bstep (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) B1669033
theorem B1463539 : Blo 1299968 1463539 := bstep (se 1 (by rfl) ⟨1097654, by rfl⟩ : syracuseStep 1463539 = 2195309) B2195309
theorem B2471249 : Blo 1299968 2471249 := bstep (se 2 (by rfl) ⟨926718, by rfl⟩ : syracuseStep 2471249 = 1853437) B1853437
theorem B1389907 : Blo 1299968 1389907 := bstep (se 1 (by rfl) ⟨1042430, by rfl⟩ : syracuseStep 1389907 = 2084861) B2084861
theorem B16668017 : Blo 1299968 16668017 := bstep (se 2 (by rfl) ⟨6250506, by rfl⟩ : syracuseStep 16668017 = 12501013) B12501013
theorem B8336753 : Blo 1299968 8336753 := bstep (se 2 (by rfl) ⟨3126282, by rfl⟩ : syracuseStep 8336753 = 6252565) B6252565
theorem B1463683 : Blo 1299968 1463683 := bstep (se 1 (by rfl) ⟨1097762, by rfl⟩ : syracuseStep 1463683 = 2195525) B2195525
theorem B47502733 : Blo 1299968 47502733 := bstep (se 3 (by rfl) ⟨8906762, by rfl⟩ : syracuseStep 47502733 = 17813525) B17813525
theorem B5273009 : Blo 1299968 5273009 := bstep (se 2 (by rfl) ⟨1977378, by rfl⟩ : syracuseStep 5273009 = 3954757) B3954757
theorem B9024965 : Blo 1299968 9024965 := bstep (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) B1692181
theorem B9876977 : Blo 1299968 9876977 := bstep (se 2 (by rfl) ⟨3703866, by rfl⟩ : syracuseStep 9876977 = 7407733) B7407733
theorem B1299971 : Blo 1299968 1299971 := bstep (se 1 (by rfl) ⟨974978, by rfl⟩ : syracuseStep 1299971 = 1949957) B1949957
theorem B1299987 : Blo 1299968 1299987 := bstep (se 1 (by rfl) ⟨974990, by rfl⟩ : syracuseStep 1299987 = 1949981) B1949981
theorem B1463827 : Blo 1299968 1463827 := bstep (se 1 (by rfl) ⟨1097870, by rfl⟩ : syracuseStep 1463827 = 2195741) B2195741
theorem B1300003 : Blo 1299968 1300003 := bstep (se 1 (by rfl) ⟨975002, by rfl⟩ : syracuseStep 1300003 = 1950005) B1950005
theorem B1783345 : Blo 1299968 1783345 := bstep (se 2 (by rfl) ⟨668754, by rfl⟩ : syracuseStep 1783345 = 1337509) B1337509
theorem B1300019 : Blo 1299968 1300019 := bstep (se 1 (by rfl) ⟨975014, by rfl⟩ : syracuseStep 1300019 = 1950029) B1950029
theorem B1300035 : Blo 1299968 1300035 := bstep (se 1 (by rfl) ⟨975026, by rfl⟩ : syracuseStep 1300035 = 1950053) B1950053
theorem B1300051 : Blo 1299968 1300051 := bstep (se 1 (by rfl) ⟨975038, by rfl⟩ : syracuseStep 1300051 = 1950077) B1950077
theorem B1300067 : Blo 1299968 1300067 := bstep (se 1 (by rfl) ⟨975050, by rfl⟩ : syracuseStep 1300067 = 1950101) B1950101
theorem B1300083 : Blo 1299968 1300083 := bstep (se 1 (by rfl) ⟨975062, by rfl⟩ : syracuseStep 1300083 = 1950125) B1950125
theorem B1300099 : Blo 1299968 1300099 := bstep (se 1 (by rfl) ⟨975074, by rfl⟩ : syracuseStep 1300099 = 1950149) B1950149
theorem B1300115 : Blo 1299968 1300115 := bstep (se 1 (by rfl) ⟨975086, by rfl⟩ : syracuseStep 1300115 = 1950173) B1950173
theorem B1300131 : Blo 1299968 1300131 := bstep (se 1 (by rfl) ⟨975098, by rfl⟩ : syracuseStep 1300131 = 1950197) B1950197
theorem B1463971 : Blo 1299968 1463971 := bstep (se 1 (by rfl) ⟨1097978, by rfl⟩ : syracuseStep 1463971 = 2195957) B2195957
theorem B4388525 : Blo 1299968 4388525 := bstep (se 3 (by rfl) ⟨822848, by rfl⟩ : syracuseStep 4388525 = 1645697) B1645697
theorem B1300147 : Blo 1299968 1300147 := bstep (se 1 (by rfl) ⟨975110, by rfl⟩ : syracuseStep 1300147 = 1950221) B1950221
theorem B1300163 : Blo 1299968 1300163 := bstep (se 1 (by rfl) ⟨975122, by rfl⟩ : syracuseStep 1300163 = 1950245) B1950245
theorem B1300179 : Blo 1299968 1300179 := bstep (se 1 (by rfl) ⟨975134, by rfl⟩ : syracuseStep 1300179 = 1950269) B1950269
theorem B1300195 : Blo 1299968 1300195 := bstep (se 1 (by rfl) ⟨975146, by rfl⟩ : syracuseStep 1300195 = 1950293) B1950293
theorem B4388579 : Blo 1299968 4388579 := bstep (se 1 (by rfl) ⟨3291434, by rfl⟩ : syracuseStep 4388579 = 6582869) B6582869
theorem B1300211 : Blo 1299968 1300211 := bstep (se 1 (by rfl) ⟨975158, by rfl⟩ : syracuseStep 1300211 = 1950317) B1950317
theorem B1300227 : Blo 1299968 1300227 := bstep (se 1 (by rfl) ⟨975170, by rfl⟩ : syracuseStep 1300227 = 1950341) B1950341
theorem B1300243 : Blo 1299968 1300243 := bstep (se 1 (by rfl) ⟨975182, by rfl⟩ : syracuseStep 1300243 = 1950365) B1950365
theorem B1300259 : Blo 1299968 1300259 := bstep (se 1 (by rfl) ⟨975194, by rfl⟩ : syracuseStep 1300259 = 1950389) B1950389
theorem B1300275 : Blo 1299968 1300275 := bstep (se 1 (by rfl) ⟨975206, by rfl⟩ : syracuseStep 1300275 = 1950413) B1950413
theorem B1464115 : Blo 1299968 1464115 := bstep (se 1 (by rfl) ⟨1098086, by rfl⟩ : syracuseStep 1464115 = 2196173) B2196173
theorem B1300291 : Blo 1299968 1300291 := bstep (se 1 (by rfl) ⟨975218, by rfl⟩ : syracuseStep 1300291 = 1950437) B1950437
theorem B1300307 : Blo 1299968 1300307 := bstep (se 1 (by rfl) ⟨975230, by rfl⟩ : syracuseStep 1300307 = 1950461) B1950461
theorem B1300323 : Blo 1299968 1300323 := bstep (se 1 (by rfl) ⟨975242, by rfl⟩ : syracuseStep 1300323 = 1950485) B1950485
theorem B1300339 : Blo 1299968 1300339 := bstep (se 1 (by rfl) ⟨975254, by rfl⟩ : syracuseStep 1300339 = 1950509) B1950509
theorem B1300355 : Blo 1299968 1300355 := bstep (se 1 (by rfl) ⟨975266, by rfl⟩ : syracuseStep 1300355 = 1950533) B1950533
theorem B1300371 : Blo 1299968 1300371 := bstep (se 1 (by rfl) ⟨975278, by rfl⟩ : syracuseStep 1300371 = 1950557) B1950557
theorem B1300387 : Blo 1299968 1300387 := bstep (se 1 (by rfl) ⟨975290, by rfl⟩ : syracuseStep 1300387 = 1950581) B1950581
theorem B1300403 : Blo 1299968 1300403 := bstep (se 1 (by rfl) ⟨975302, by rfl⟩ : syracuseStep 1300403 = 1950605) B1950605
theorem B1300419 : Blo 1299968 1300419 := bstep (se 1 (by rfl) ⟨975314, by rfl⟩ : syracuseStep 1300419 = 1950629) B1950629
theorem B1464259 : Blo 1299968 1464259 := bstep (se 1 (by rfl) ⟨1098194, by rfl⟩ : syracuseStep 1464259 = 2196389) B2196389
theorem B1300435 : Blo 1299968 1300435 := bstep (se 1 (by rfl) ⟨975326, by rfl⟩ : syracuseStep 1300435 = 1950653) B1950653
theorem B1300451 : Blo 1299968 1300451 := bstep (se 1 (by rfl) ⟨975338, by rfl⟩ : syracuseStep 1300451 = 1950677) B1950677
theorem B4937699 : Blo 1299968 4937699 := bstep (se 1 (by rfl) ⟨3703274, by rfl⟩ : syracuseStep 4937699 = 7406549) B7406549
theorem B4388849 : Blo 1299968 4388849 := bstep (se 2 (by rfl) ⟨1645818, by rfl⟩ : syracuseStep 4388849 = 3291637) B3291637
theorem B1300467 : Blo 1299968 1300467 := bstep (se 1 (by rfl) ⟨975350, by rfl⟩ : syracuseStep 1300467 = 1950701) B1950701
theorem B1300483 : Blo 1299968 1300483 := bstep (se 1 (by rfl) ⟨975362, by rfl⟩ : syracuseStep 1300483 = 1950725) B1950725
theorem B1300499 : Blo 1299968 1300499 := bstep (se 1 (by rfl) ⟨975374, by rfl⟩ : syracuseStep 1300499 = 1950749) B1950749
theorem B1300515 : Blo 1299968 1300515 := bstep (se 1 (by rfl) ⟨975386, by rfl⟩ : syracuseStep 1300515 = 1950773) B1950773
theorem B2504753 : Blo 1299968 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B1300531 : Blo 1299968 1300531 := bstep (se 1 (by rfl) ⟨975398, by rfl⟩ : syracuseStep 1300531 = 1950797) B1950797
theorem B1300547 : Blo 1299968 1300547 := bstep (se 1 (by rfl) ⟨975410, by rfl⟩ : syracuseStep 1300547 = 1950821) B1950821
theorem B2857027 : Blo 1299968 2857027 := bstep (se 1 (by rfl) ⟨2142770, by rfl⟩ : syracuseStep 2857027 = 4285541) B4285541
theorem B1300563 : Blo 1299968 1300563 := bstep (se 1 (by rfl) ⟨975422, by rfl⟩ : syracuseStep 1300563 = 1950845) B1950845
theorem B1464403 : Blo 1299968 1464403 := bstep (se 1 (by rfl) ⟨1098302, by rfl⟩ : syracuseStep 1464403 = 2196605) B2196605
theorem B1300579 : Blo 1299968 1300579 := bstep (se 1 (by rfl) ⟨975434, by rfl⟩ : syracuseStep 1300579 = 1950869) B1950869
theorem B5560433 : Blo 1299968 5560433 := bstep (se 2 (by rfl) ⟨2085162, by rfl⟩ : syracuseStep 5560433 = 4170325) B4170325
theorem B1300595 : Blo 1299968 1300595 := bstep (se 1 (by rfl) ⟨975446, by rfl⟩ : syracuseStep 1300595 = 1950893) B1950893
theorem B1300611 : Blo 1299968 1300611 := bstep (se 1 (by rfl) ⟨975458, by rfl⟩ : syracuseStep 1300611 = 1950917) B1950917
theorem B4012177 : Blo 1299968 4012177 := bstep (se 2 (by rfl) ⟨1504566, by rfl⟩ : syracuseStep 4012177 = 3009133) B3009133
theorem B1300627 : Blo 1299968 1300627 := bstep (se 1 (by rfl) ⟨975470, by rfl⟩ : syracuseStep 1300627 = 1950941) B1950941
theorem B1562771 : Blo 1299968 1562771 := bstep (se 1 (by rfl) ⟨1172078, by rfl⟩ : syracuseStep 1562771 = 2344157) B2344157
theorem B1300643 : Blo 1299968 1300643 := bstep (se 1 (by rfl) ⟨975482, by rfl⟩ : syracuseStep 1300643 = 1950965) B1950965
theorem B3291313 : Blo 1299968 3291313 := bstep (se 2 (by rfl) ⟨1234242, by rfl⟩ : syracuseStep 3291313 = 2468485) B2468485
theorem B1300659 : Blo 1299968 1300659 := bstep (se 1 (by rfl) ⟨975494, by rfl⟩ : syracuseStep 1300659 = 1950989) B1950989
theorem B1300675 : Blo 1299968 1300675 := bstep (se 1 (by rfl) ⟨975506, by rfl⟩ : syracuseStep 1300675 = 1951013) B1951013
theorem B14063813 : Blo 1299968 14063813 := bstep (se 4 (by rfl) ⟨1318482, by rfl⟩ : syracuseStep 14063813 = 2636965) B2636965
theorem B1300691 : Blo 1299968 1300691 := bstep (se 1 (by rfl) ⟨975518, by rfl⟩ : syracuseStep 1300691 = 1951037) B1951037
theorem B1300707 : Blo 1299968 1300707 := bstep (se 1 (by rfl) ⟨975530, by rfl⟩ : syracuseStep 1300707 = 1951061) B1951061
theorem B1464547 : Blo 1299968 1464547 := bstep (se 1 (by rfl) ⟨1098410, by rfl⟩ : syracuseStep 1464547 = 2196821) B2196821
theorem B1300723 : Blo 1299968 1300723 := bstep (se 1 (by rfl) ⟨975542, by rfl⟩ : syracuseStep 1300723 = 1951085) B1951085
theorem B1300739 : Blo 1299968 1300739 := bstep (se 1 (by rfl) ⟨975554, by rfl⟩ : syracuseStep 1300739 = 1951109) B1951109
theorem B1300755 : Blo 1299968 1300755 := bstep (se 1 (by rfl) ⟨975566, by rfl⟩ : syracuseStep 1300755 = 1951133) B1951133
theorem B1300771 : Blo 1299968 1300771 := bstep (se 1 (by rfl) ⟨975578, by rfl⟩ : syracuseStep 1300771 = 1951157) B1951157
theorem B1300787 : Blo 1299968 1300787 := bstep (se 1 (by rfl) ⟨975590, by rfl⟩ : syracuseStep 1300787 = 1951181) B1951181
theorem B1300803 : Blo 1299968 1300803 := bstep (se 1 (by rfl) ⟨975602, by rfl⟩ : syracuseStep 1300803 = 1951205) B1951205
theorem B1300819 : Blo 1299968 1300819 := bstep (se 1 (by rfl) ⟨975614, by rfl⟩ : syracuseStep 1300819 = 1951229) B1951229
theorem B2193763 : Blo 1299968 2193763 := bstep (se 1 (by rfl) ⟨1645322, by rfl⟩ : syracuseStep 2193763 = 3290645) B3290645
theorem B1300835 : Blo 1299968 1300835 := bstep (se 1 (by rfl) ⟨975626, by rfl⟩ : syracuseStep 1300835 = 1951253) B1951253
theorem B1300851 : Blo 1299968 1300851 := bstep (se 1 (by rfl) ⟨975638, by rfl⟩ : syracuseStep 1300851 = 1951277) B1951277
theorem B1464691 : Blo 1299968 1464691 := bstep (se 1 (by rfl) ⟨1098518, by rfl⟩ : syracuseStep 1464691 = 2197037) B2197037
theorem B1300867 : Blo 1299968 1300867 := bstep (se 1 (by rfl) ⟨975650, by rfl⟩ : syracuseStep 1300867 = 1951301) B1951301
theorem B1300883 : Blo 1299968 1300883 := bstep (se 1 (by rfl) ⟨975662, by rfl⟩ : syracuseStep 1300883 = 1951325) B1951325
theorem B1300899 : Blo 1299968 1300899 := bstep (se 1 (by rfl) ⟨975674, by rfl⟩ : syracuseStep 1300899 = 1951349) B1951349
theorem B1300915 : Blo 1299968 1300915 := bstep (se 1 (by rfl) ⟨975686, by rfl⟩ : syracuseStep 1300915 = 1951373) B1951373
theorem B3291587 : Blo 1299968 3291587 := bstep (se 1 (by rfl) ⟨2468690, by rfl⟩ : syracuseStep 3291587 = 4937381) B4937381
theorem B1300931 : Blo 1299968 1300931 := bstep (se 1 (by rfl) ⟨975698, by rfl⟩ : syracuseStep 1300931 = 1951397) B1951397
theorem B1300947 : Blo 1299968 1300947 := bstep (se 1 (by rfl) ⟨975710, by rfl⟩ : syracuseStep 1300947 = 1951421) B1951421
theorem B1300963 : Blo 1299968 1300963 := bstep (se 1 (by rfl) ⟨975722, by rfl⟩ : syracuseStep 1300963 = 1951445) B1951445
theorem B1563107 : Blo 1299968 1563107 := bstep (se 1 (by rfl) ⟨1172330, by rfl⟩ : syracuseStep 1563107 = 2344661) B2344661
theorem B2193905 : Blo 1299968 2193905 := bstep (se 2 (by rfl) ⟨822714, by rfl⟩ : syracuseStep 2193905 = 1645429) B1645429
theorem B1300979 : Blo 1299968 1300979 := bstep (se 1 (by rfl) ⟨975734, by rfl⟩ : syracuseStep 1300979 = 1951469) B1951469
theorem B1300995 : Blo 1299968 1300995 := bstep (se 1 (by rfl) ⟨975746, by rfl⟩ : syracuseStep 1300995 = 1951493) B1951493
theorem B4389389 : Blo 1299968 4389389 := bstep (se 3 (by rfl) ⟨823010, by rfl⟩ : syracuseStep 4389389 = 1646021) B1646021
theorem B1301011 : Blo 1299968 1301011 := bstep (se 1 (by rfl) ⟨975758, by rfl⟩ : syracuseStep 1301011 = 1951517) B1951517
theorem B1301027 : Blo 1299968 1301027 := bstep (se 1 (by rfl) ⟨975770, by rfl⟩ : syracuseStep 1301027 = 1951541) B1951541
theorem B1301043 : Blo 1299968 1301043 := bstep (se 1 (by rfl) ⟨975782, by rfl⟩ : syracuseStep 1301043 = 1951565) B1951565
theorem B4389443 : Blo 1299968 4389443 := bstep (se 1 (by rfl) ⟨3292082, by rfl⟩ : syracuseStep 4389443 = 6584165) B6584165
theorem B1301059 : Blo 1299968 1301059 := bstep (se 1 (by rfl) ⟨975794, by rfl⟩ : syracuseStep 1301059 = 1951589) B1951589
theorem B1301075 : Blo 1299968 1301075 := bstep (se 1 (by rfl) ⟨975806, by rfl⟩ : syracuseStep 1301075 = 1951613) B1951613
theorem B1301091 : Blo 1299968 1301091 := bstep (se 1 (by rfl) ⟨975818, by rfl⟩ : syracuseStep 1301091 = 1951637) B1951637
theorem B2194033 : Blo 1299968 2194033 := bstep (se 2 (by rfl) ⟨822762, by rfl⟩ : syracuseStep 2194033 = 1645525) B1645525
theorem B4938353 : Blo 1299968 4938353 := bstep (se 2 (by rfl) ⟨1851882, by rfl⟩ : syracuseStep 4938353 = 3703765) B3703765
theorem B1301107 : Blo 1299968 1301107 := bstep (se 1 (by rfl) ⟨975830, by rfl⟩ : syracuseStep 1301107 = 1951661) B1951661
theorem B3291779 : Blo 1299968 3291779 := bstep (se 1 (by rfl) ⟨2468834, by rfl⟩ : syracuseStep 3291779 = 4937669) B4937669
theorem B1301123 : Blo 1299968 1301123 := bstep (se 1 (by rfl) ⟨975842, by rfl⟩ : syracuseStep 1301123 = 1951685) B1951685
theorem B2194067 : Blo 1299968 2194067 := bstep (se 1 (by rfl) ⟨1645550, by rfl⟩ : syracuseStep 2194067 = 3291101) B3291101
theorem B1301139 : Blo 1299968 1301139 := bstep (se 1 (by rfl) ⟨975854, by rfl⟩ : syracuseStep 1301139 = 1951709) B1951709
theorem B1301155 : Blo 1299968 1301155 := bstep (se 1 (by rfl) ⟨975866, by rfl⟩ : syracuseStep 1301155 = 1951733) B1951733
theorem B1301171 : Blo 1299968 1301171 := bstep (se 1 (by rfl) ⟨975878, by rfl⟩ : syracuseStep 1301171 = 1951757) B1951757
theorem B1301187 : Blo 1299968 1301187 := bstep (se 1 (by rfl) ⟨975890, by rfl⟩ : syracuseStep 1301187 = 1951781) B1951781
theorem B6675149 : Blo 1299968 6675149 := bstep (se 3 (by rfl) ⟨1251590, by rfl⟩ : syracuseStep 6675149 = 2503181) B2503181
theorem B1301203 : Blo 1299968 1301203 := bstep (se 1 (by rfl) ⟨975902, by rfl⟩ : syracuseStep 1301203 = 1951805) B1951805
theorem B1301219 : Blo 1299968 1301219 := bstep (se 1 (by rfl) ⟨975914, by rfl⟩ : syracuseStep 1301219 = 1951829) B1951829
theorem B1301235 : Blo 1299968 1301235 := bstep (se 1 (by rfl) ⟨975926, by rfl⟩ : syracuseStep 1301235 = 1951853) B1951853
theorem B1301251 : Blo 1299968 1301251 := bstep (se 1 (by rfl) ⟨975938, by rfl⟩ : syracuseStep 1301251 = 1951877) B1951877
theorem B2194195 : Blo 1299968 2194195 := bstep (se 1 (by rfl) ⟨1645646, by rfl⟩ : syracuseStep 2194195 = 3291293) B3291293
theorem B1301267 : Blo 1299968 1301267 := bstep (se 1 (by rfl) ⟨975950, by rfl⟩ : syracuseStep 1301267 = 1951901) B1951901
theorem B1301283 : Blo 1299968 1301283 := bstep (se 1 (by rfl) ⟨975962, by rfl⟩ : syracuseStep 1301283 = 1951925) B1951925
theorem B8338211 : Blo 1299968 8338211 := bstep (se 1 (by rfl) ⟨6253658, by rfl⟩ : syracuseStep 8338211 = 12507317) B12507317
theorem B6585137 : Blo 1299968 6585137 := bstep (se 2 (by rfl) ⟨2469426, by rfl⟩ : syracuseStep 6585137 = 4938853) B4938853
theorem B1645363 : Blo 1299968 1645363 := bstep (se 1 (by rfl) ⟨1234022, by rfl⟩ : syracuseStep 1645363 = 2468045) B2468045
theorem B1301299 : Blo 1299968 1301299 := bstep (se 1 (by rfl) ⟨975974, by rfl⟩ : syracuseStep 1301299 = 1951949) B1951949
theorem B1301315 : Blo 1299968 1301315 := bstep (se 1 (by rfl) ⟨975986, by rfl⟩ : syracuseStep 1301315 = 1951973) B1951973
theorem B4389713 : Blo 1299968 4389713 := bstep (se 2 (by rfl) ⟨1646142, by rfl⟩ : syracuseStep 4389713 = 3292285) B3292285
theorem B1301331 : Blo 1299968 1301331 := bstep (se 1 (by rfl) ⟨975998, by rfl⟩ : syracuseStep 1301331 = 1951997) B1951997
theorem B1301347 : Blo 1299968 1301347 := bstep (se 1 (by rfl) ⟨976010, by rfl⟩ : syracuseStep 1301347 = 1952021) B1952021
theorem B22518641 : Blo 1299968 22518641 := bstep (se 2 (by rfl) ⟨8444490, by rfl⟩ : syracuseStep 22518641 = 16888981) B16888981
theorem B1301363 : Blo 1299968 1301363 := bstep (se 1 (by rfl) ⟨976022, by rfl⟩ : syracuseStep 1301363 = 1952045) B1952045
theorem B1301379 : Blo 1299968 1301379 := bstep (se 1 (by rfl) ⟨976034, by rfl⟩ : syracuseStep 1301379 = 1952069) B1952069
theorem B1301395 : Blo 1299968 1301395 := bstep (se 1 (by rfl) ⟨976046, by rfl⟩ : syracuseStep 1301395 = 1952093) B1952093
theorem B2194337 : Blo 1299968 2194337 := bstep (se 2 (by rfl) ⟨822876, by rfl⟩ : syracuseStep 2194337 = 1645753) B1645753
theorem B1301411 : Blo 1299968 1301411 := bstep (se 1 (by rfl) ⟨976058, by rfl⟩ : syracuseStep 1301411 = 1952117) B1952117
theorem B1301427 : Blo 1299968 1301427 := bstep (se 1 (by rfl) ⟨976070, by rfl⟩ : syracuseStep 1301427 = 1952141) B1952141
theorem B1301443 : Blo 1299968 1301443 := bstep (se 1 (by rfl) ⟨976082, by rfl⟩ : syracuseStep 1301443 = 1952165) B1952165
theorem B1301459 : Blo 1299968 1301459 := bstep (se 1 (by rfl) ⟨976094, by rfl⟩ : syracuseStep 1301459 = 1952189) B1952189
theorem B1301475 : Blo 1299968 1301475 := bstep (se 1 (by rfl) ⟨976106, by rfl⟩ : syracuseStep 1301475 = 1952213) B1952213
theorem B4168685 : Blo 1299968 4168685 := bstep (se 3 (by rfl) ⟨781628, by rfl⟩ : syracuseStep 4168685 = 1563257) B1563257
theorem B1301491 : Blo 1299968 1301491 := bstep (se 1 (by rfl) ⟨976118, by rfl⟩ : syracuseStep 1301491 = 1952237) B1952237
theorem B1301507 : Blo 1299968 1301507 := bstep (se 1 (by rfl) ⟨976130, by rfl⟩ : syracuseStep 1301507 = 1952261) B1952261
theorem B4062221 : Blo 1299968 4062221 := bstep (se 3 (by rfl) ⟨761666, by rfl⟩ : syracuseStep 4062221 = 1523333) B1523333
theorem B5790733 : Blo 1299968 5790733 := bstep (se 3 (by rfl) ⟨1085762, by rfl⟩ : syracuseStep 5790733 = 2171525) B2171525
theorem B1301523 : Blo 1299968 1301523 := bstep (se 1 (by rfl) ⟨976142, by rfl⟩ : syracuseStep 1301523 = 1952285) B1952285
theorem B2194465 : Blo 1299968 2194465 := bstep (se 2 (by rfl) ⟨822924, by rfl⟩ : syracuseStep 2194465 = 1645849) B1645849
theorem B1301539 : Blo 1299968 1301539 := bstep (se 1 (by rfl) ⟨976154, by rfl⟩ : syracuseStep 1301539 = 1952309) B1952309
theorem B1301555 : Blo 1299968 1301555 := bstep (se 1 (by rfl) ⟨976166, by rfl⟩ : syracuseStep 1301555 = 1952333) B1952333
theorem B2194499 : Blo 1299968 2194499 := bstep (se 1 (by rfl) ⟨1645874, by rfl⟩ : syracuseStep 2194499 = 3291749) B3291749
theorem B1301571 : Blo 1299968 1301571 := bstep (se 1 (by rfl) ⟨976178, by rfl⟩ : syracuseStep 1301571 = 1952357) B1952357
theorem B1301587 : Blo 1299968 1301587 := bstep (se 1 (by rfl) ⟨976190, by rfl⟩ : syracuseStep 1301587 = 1952381) B1952381
theorem B1301603 : Blo 1299968 1301603 := bstep (se 1 (by rfl) ⟨976202, by rfl⟩ : syracuseStep 1301603 = 1952405) B1952405
theorem B1301619 : Blo 1299968 1301619 := bstep (se 1 (by rfl) ⟨976214, by rfl⟩ : syracuseStep 1301619 = 1952429) B1952429
theorem B1301635 : Blo 1299968 1301635 := bstep (se 1 (by rfl) ⟨976226, by rfl⟩ : syracuseStep 1301635 = 1952453) B1952453
theorem B1301651 : Blo 1299968 1301651 := bstep (se 1 (by rfl) ⟨976238, by rfl⟩ : syracuseStep 1301651 = 1952477) B1952477
theorem B1301667 : Blo 1299968 1301667 := bstep (se 1 (by rfl) ⟨976250, by rfl⟩ : syracuseStep 1301667 = 1952501) B1952501
theorem B1301683 : Blo 1299968 1301683 := bstep (se 1 (by rfl) ⟨976262, by rfl⟩ : syracuseStep 1301683 = 1952525) B1952525
theorem B2194627 : Blo 1299968 2194627 := bstep (se 1 (by rfl) ⟨1645970, by rfl⟩ : syracuseStep 2194627 = 3291941) B3291941
theorem B1301699 : Blo 1299968 1301699 := bstep (se 1 (by rfl) ⟨976274, by rfl⟩ : syracuseStep 1301699 = 1952549) B1952549
theorem B1301715 : Blo 1299968 1301715 := bstep (se 1 (by rfl) ⟨976286, by rfl⟩ : syracuseStep 1301715 = 1952573) B1952573
theorem B1301731 : Blo 1299968 1301731 := bstep (se 1 (by rfl) ⟨976298, by rfl⟩ : syracuseStep 1301731 = 1952597) B1952597
theorem B8445169 : Blo 1299968 8445169 := bstep (se 2 (by rfl) ⟨3166938, by rfl⟩ : syracuseStep 8445169 = 6333877) B6333877
theorem B1301747 : Blo 1299968 1301747 := bstep (se 1 (by rfl) ⟨976310, by rfl⟩ : syracuseStep 1301747 = 1952621) B1952621
theorem B1301763 : Blo 1299968 1301763 := bstep (se 1 (by rfl) ⟨976322, by rfl⟩ : syracuseStep 1301763 = 1952645) B1952645
theorem B1301779 : Blo 1299968 1301779 := bstep (se 1 (by rfl) ⟨976334, by rfl⟩ : syracuseStep 1301779 = 1952669) B1952669
theorem B1645859 : Blo 1299968 1645859 := bstep (se 1 (by rfl) ⟨1234394, by rfl⟩ : syracuseStep 1645859 = 2468789) B2468789
theorem B1301795 : Blo 1299968 1301795 := bstep (se 1 (by rfl) ⟨976346, by rfl⟩ : syracuseStep 1301795 = 1952693) B1952693
theorem B1301811 : Blo 1299968 1301811 := bstep (se 1 (by rfl) ⟨976358, by rfl⟩ : syracuseStep 1301811 = 1952717) B1952717
theorem B1301827 : Blo 1299968 1301827 := bstep (se 1 (by rfl) ⟨976370, by rfl⟩ : syracuseStep 1301827 = 1952741) B1952741
theorem B2194769 : Blo 1299968 2194769 := bstep (se 2 (by rfl) ⟨823038, by rfl⟩ : syracuseStep 2194769 = 1646077) B1646077
theorem B1301843 : Blo 1299968 1301843 := bstep (se 1 (by rfl) ⟨976382, by rfl⟩ : syracuseStep 1301843 = 1952765) B1952765
theorem B1301859 : Blo 1299968 1301859 := bstep (se 1 (by rfl) ⟨976394, by rfl⟩ : syracuseStep 1301859 = 1952789) B1952789
theorem B3702125 : Blo 1299968 3702125 := bstep (se 3 (by rfl) ⟨694148, by rfl⟩ : syracuseStep 3702125 = 1388297) B1388297
theorem B4390253 : Blo 1299968 4390253 := bstep (se 3 (by rfl) ⟨823172, by rfl⟩ : syracuseStep 4390253 = 1646345) B1646345
theorem B1301875 : Blo 1299968 1301875 := bstep (se 1 (by rfl) ⟨976406, by rfl⟩ : syracuseStep 1301875 = 1952813) B1952813
theorem B1301891 : Blo 1299968 1301891 := bstep (se 1 (by rfl) ⟨976418, by rfl⟩ : syracuseStep 1301891 = 1952837) B1952837
theorem B2776465 : Blo 1299968 2776465 := bstep (se 2 (by rfl) ⟨1041174, by rfl⟩ : syracuseStep 2776465 = 2082349) B2082349
theorem B1301907 : Blo 1299968 1301907 := bstep (se 1 (by rfl) ⟨976430, by rfl⟩ : syracuseStep 1301907 = 1952861) B1952861
theorem B4390307 : Blo 1299968 4390307 := bstep (se 1 (by rfl) ⟨3292730, by rfl⟩ : syracuseStep 4390307 = 6585461) B6585461
theorem B1301923 : Blo 1299968 1301923 := bstep (se 1 (by rfl) ⟨976442, by rfl⟩ : syracuseStep 1301923 = 1952885) B1952885
theorem B1301939 : Blo 1299968 1301939 := bstep (se 1 (by rfl) ⟨976454, by rfl⟩ : syracuseStep 1301939 = 1952909) B1952909
theorem B1301955 : Blo 1299968 1301955 := bstep (se 1 (by rfl) ⟨976466, by rfl⟩ : syracuseStep 1301955 = 1952933) B1952933
theorem B5553613 : Blo 1299968 5553613 := bstep (se 3 (by rfl) ⟨1041302, by rfl⟩ : syracuseStep 5553613 = 2082605) B2082605
theorem B2194897 : Blo 1299968 2194897 := bstep (se 2 (by rfl) ⟨823086, by rfl⟩ : syracuseStep 2194897 = 1646173) B1646173
theorem B2194931 : Blo 1299968 2194931 := bstep (se 1 (by rfl) ⟨1646198, by rfl⟩ : syracuseStep 2194931 = 3292397) B3292397
theorem B3702307 : Blo 1299968 3702307 := bstep (se 1 (by rfl) ⟨2776730, by rfl⟩ : syracuseStep 3702307 = 5553461) B5553461
theorem B7405091 : Blo 1299968 7405091 := bstep (se 1 (by rfl) ⟨5553818, by rfl⟩ : syracuseStep 7405091 = 11107637) B11107637
theorem B3292721 : Blo 1299968 3292721 := bstep (se 2 (by rfl) ⟨1234770, by rfl⟩ : syracuseStep 3292721 = 2469541) B2469541
theorem B3513955 : Blo 1299968 3513955 := bstep (se 1 (by rfl) ⟨2635466, by rfl⟩ : syracuseStep 3513955 = 5270933) B5270933
theorem B3292771 : Blo 1299968 3292771 := bstep (se 1 (by rfl) ⟨2469578, by rfl⟩ : syracuseStep 3292771 = 4939157) B4939157
theorem B2195059 : Blo 1299968 2195059 := bstep (se 1 (by rfl) ⟨1646294, by rfl⟩ : syracuseStep 2195059 = 3292589) B3292589
theorem B4390577 : Blo 1299968 4390577 := bstep (se 2 (by rfl) ⟨1646466, by rfl⟩ : syracuseStep 4390577 = 3292933) B3292933
theorem B7618225 : Blo 1299968 7618225 := bstep (se 2 (by rfl) ⟨2856834, by rfl⟩ : syracuseStep 7618225 = 5713669) B5713669
theorem B3292913 : Blo 1299968 3292913 := bstep (se 2 (by rfl) ⟨1234842, by rfl⟩ : syracuseStep 3292913 = 2469685) B2469685
theorem B2195201 : Blo 1299968 2195201 := bstep (se 2 (by rfl) ⟨823200, by rfl⟩ : syracuseStep 2195201 = 1646401) B1646401
theorem B8339213 : Blo 1299968 8339213 := bstep (se 3 (by rfl) ⟨1563602, by rfl⟩ : syracuseStep 8339213 = 3127205) B3127205
theorem B2195329 : Blo 1299968 2195329 := bstep (se 2 (by rfl) ⟨823248, by rfl⟩ : syracuseStep 2195329 = 1646497) B1646497
theorem B2195363 : Blo 1299968 2195363 := bstep (se 1 (by rfl) ⟨1646522, by rfl⟩ : syracuseStep 2195363 = 3293045) B3293045
theorem B2113475 : Blo 1299968 2113475 := bstep (se 1 (by rfl) ⟨1585106, by rfl⟩ : syracuseStep 2113475 = 3170213) B3170213
theorem B1646563 : Blo 1299968 1646563 := bstep (se 1 (by rfl) ⟨1234922, by rfl⟩ : syracuseStep 1646563 = 2469845) B2469845
theorem B21102605 : Blo 1299968 21102605 := bstep (se 3 (by rfl) ⟨3956738, by rfl⟩ : syracuseStep 21102605 = 7913477) B7913477
theorem B3293207 : Blo 1299968 3293207 := bstep (se 1 (by rfl) ⟨2469905, by rfl⟩ : syracuseStep 3293207 = 4939811) B4939811
theorem B6586433 : Blo 1299968 6586433 := bstep (se 2 (by rfl) ⟨2469912, by rfl⟩ : syracuseStep 6586433 = 4939825) B4939825
theorem B30883909 : Blo 1299968 30883909 := bstep (se 4 (by rfl) ⟨2895366, by rfl⟩ : syracuseStep 30883909 = 5790733) B5790733
theorem B2195545 : Blo 1299968 2195545 := bstep (se 2 (by rfl) ⟨823329, by rfl⟩ : syracuseStep 2195545 = 1646659) B1646659
theorem B3809369 : Blo 1299968 3809369 := bstep (se 2 (by rfl) ⟨1428513, by rfl⟩ : syracuseStep 3809369 = 2857027) B2857027
theorem B1409131 : Blo 1299968 1409131 := bstep (se 1 (by rfl) ⟨1056848, by rfl⟩ : syracuseStep 1409131 = 2113697) B2113697
theorem B4391063 : Blo 1299968 4391063 := bstep (se 1 (by rfl) ⟨3293297, by rfl⟩ : syracuseStep 4391063 = 6586595) B6586595
theorem B2638003 : Blo 1299968 2638003 := bstep (se 1 (by rfl) ⟨1978502, by rfl⟩ : syracuseStep 2638003 = 3957005) B3957005
theorem B5349569 : Blo 1299968 5349569 := bstep (se 2 (by rfl) ⟨2006088, by rfl⟩ : syracuseStep 5349569 = 4012177) B4012177
theorem B2932939 : Blo 1299968 2932939 := bstep (se 1 (by rfl) ⟨2199704, by rfl⟩ : syracuseStep 2932939 = 4399409) B4399409
theorem B2777303 : Blo 1299968 2777303 := bstep (se 1 (by rfl) ⟨2082977, by rfl⟩ : syracuseStep 2777303 = 4165955) B4165955
theorem B1949963 : Blo 1299968 1949963 := bstep (se 1 (by rfl) ⟨1462472, by rfl⟩ : syracuseStep 1949963 = 2924945) B2924945
theorem B1949975 : Blo 1299968 1949975 := bstep (se 1 (by rfl) ⟨1462481, by rfl⟩ : syracuseStep 1949975 = 2924963) B2924963
theorem B5013805 : Blo 1299968 5013805 := bstep (se 3 (by rfl) ⟨940088, by rfl⟩ : syracuseStep 5013805 = 1880177) B1880177
theorem B7414091 : Blo 1299968 7414091 := bstep (se 1 (by rfl) ⟨5560568, by rfl⟩ : syracuseStep 7414091 = 11121137) B11121137
theorem B1950041 : Blo 1299968 1950041 := bstep (se 2 (by rfl) ⟨731265, by rfl⟩ : syracuseStep 1950041 = 1462531) B1462531
theorem B2777483 : Blo 1299968 2777483 := bstep (se 1 (by rfl) ⟨2083112, by rfl⟩ : syracuseStep 2777483 = 4166225) B4166225
theorem B1950155 : Blo 1299968 1950155 := bstep (se 1 (by rfl) ⟨1462616, by rfl⟩ : syracuseStep 1950155 = 2925233) B2925233
theorem B1950167 : Blo 1299968 1950167 := bstep (se 1 (by rfl) ⟨1462625, by rfl⟩ : syracuseStep 1950167 = 2925251) B2925251
theorem B2925017 : Blo 1299968 2925017 := bstep (se 2 (by rfl) ⟨1096881, by rfl⟩ : syracuseStep 2925017 = 2193763) B2193763
theorem B4940311 : Blo 1299968 4940311 := bstep (se 1 (by rfl) ⟨3705233, by rfl⟩ : syracuseStep 4940311 = 7410467) B7410467
theorem B1950233 : Blo 1299968 1950233 := bstep (se 2 (by rfl) ⟨731337, by rfl⟩ : syracuseStep 1950233 = 1462675) B1462675
theorem B2925107 : Blo 1299968 2925107 := bstep (se 1 (by rfl) ⟨2193830, by rfl⟩ : syracuseStep 2925107 = 4387661) B4387661
theorem B1851979 : Blo 1299968 1851979 := bstep (se 1 (by rfl) ⟨1388984, by rfl⟩ : syracuseStep 1851979 = 2777969) B2777969
theorem B10551883 : Blo 1299968 10551883 := bstep (se 1 (by rfl) ⟨7913912, by rfl⟩ : syracuseStep 10551883 = 15827825) B15827825
theorem B2925143 : Blo 1299968 2925143 := bstep (se 1 (by rfl) ⟨2193857, by rfl⟩ : syracuseStep 2925143 = 4387715) B4387715
theorem B1950347 : Blo 1299968 1950347 := bstep (se 1 (by rfl) ⟨1462760, by rfl⟩ : syracuseStep 1950347 = 2925521) B2925521
theorem B1950359 : Blo 1299968 1950359 := bstep (se 1 (by rfl) ⟨1462769, by rfl⟩ : syracuseStep 1950359 = 2925539) B2925539
theorem B2196119 : Blo 1299968 2196119 := bstep (se 1 (by rfl) ⟨1647089, by rfl⟩ : syracuseStep 2196119 = 3294179) B3294179
theorem B4391603 : Blo 1299968 4391603 := bstep (se 1 (by rfl) ⟨3293702, by rfl⟩ : syracuseStep 4391603 = 6587405) B6587405
theorem B1647307 : Blo 1299968 1647307 := bstep (se 1 (by rfl) ⟨1235480, by rfl⟩ : syracuseStep 1647307 = 2470961) B2470961
theorem B1950425 : Blo 1299968 1950425 := bstep (se 2 (by rfl) ⟨731409, by rfl⟩ : syracuseStep 1950425 = 1462819) B1462819
theorem B2925323 : Blo 1299968 2925323 := bstep (se 1 (by rfl) ⟨2193992, by rfl⟩ : syracuseStep 2925323 = 4387985) B4387985
theorem B2196247 : Blo 1299968 2196247 := bstep (se 1 (by rfl) ⟨1647185, by rfl⟩ : syracuseStep 2196247 = 3294371) B3294371
theorem B2925377 : Blo 1299968 2925377 := bstep (se 2 (by rfl) ⟨1097016, by rfl⟩ : syracuseStep 2925377 = 2194033) B2194033
theorem B10543937 : Blo 1299968 10543937 := bstep (se 2 (by rfl) ⟨3953976, by rfl⟩ : syracuseStep 10543937 = 7907953) B7907953
theorem B3294017 : Blo 1299968 3294017 := bstep (se 2 (by rfl) ⟨1235256, by rfl⟩ : syracuseStep 3294017 = 2470513) B2470513
theorem B1950539 : Blo 1299968 1950539 := bstep (se 1 (by rfl) ⟨1462904, by rfl⟩ : syracuseStep 1950539 = 2925809) B2925809
theorem B1950551 : Blo 1299968 1950551 := bstep (se 1 (by rfl) ⟨1462913, by rfl⟩ : syracuseStep 1950551 = 2925827) B2925827
theorem B1852247 : Blo 1299968 1852247 := bstep (se 1 (by rfl) ⟨1389185, by rfl⟩ : syracuseStep 1852247 = 2778371) B2778371
theorem B1950617 : Blo 1299968 1950617 := bstep (se 2 (by rfl) ⟨731481, by rfl⟩ : syracuseStep 1950617 = 1462963) B1462963
theorem B5555117 : Blo 1299968 5555117 := bstep (se 3 (by rfl) ⟨1041584, by rfl⟩ : syracuseStep 5555117 = 2083169) B2083169
theorem B10552241 : Blo 1299968 10552241 := bstep (se 2 (by rfl) ⟨3957090, by rfl⟩ : syracuseStep 10552241 = 7914181) B7914181
theorem B4686785 : Blo 1299968 4686785 := bstep (se 2 (by rfl) ⟨1757544, by rfl⟩ : syracuseStep 4686785 = 3515089) B3515089
theorem B4391873 : Blo 1299968 4391873 := bstep (se 2 (by rfl) ⟨1646952, by rfl⟩ : syracuseStep 4391873 = 3293905) B3293905
theorem B3515339 : Blo 1299968 3515339 := bstep (se 1 (by rfl) ⟨2636504, by rfl⟩ : syracuseStep 3515339 = 5273009) B5273009
theorem B1950731 : Blo 1299968 1950731 := bstep (se 1 (by rfl) ⟨1463048, by rfl⟩ : syracuseStep 1950731 = 2926097) B2926097
theorem B1950743 : Blo 1299968 1950743 := bstep (se 1 (by rfl) ⟨1463057, by rfl⟩ : syracuseStep 1950743 = 2926115) B2926115
theorem B2925593 : Blo 1299968 2925593 := bstep (se 2 (by rfl) ⟨1097097, by rfl⟩ : syracuseStep 2925593 = 2194195) B2194195
theorem B1950809 : Blo 1299968 1950809 := bstep (se 2 (by rfl) ⟨731553, by rfl⟩ : syracuseStep 1950809 = 1463107) B1463107
theorem B2925683 : Blo 1299968 2925683 := bstep (se 1 (by rfl) ⟨2194262, by rfl⟩ : syracuseStep 2925683 = 4388525) B4388525
theorem B2925719 : Blo 1299968 2925719 := bstep (se 1 (by rfl) ⟨2194289, by rfl⟩ : syracuseStep 2925719 = 4388579) B4388579
theorem B2671795 : Blo 1299968 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B1950923 : Blo 1299968 1950923 := bstep (se 1 (by rfl) ⟨1463192, by rfl⟩ : syracuseStep 1950923 = 2926385) B2926385
theorem B1950935 : Blo 1299968 1950935 := bstep (se 1 (by rfl) ⟨1463201, by rfl⟩ : syracuseStep 1950935 = 2926403) B2926403
theorem B6251737 : Blo 1299968 6251737 := bstep (se 2 (by rfl) ⟨2344401, by rfl⟩ : syracuseStep 6251737 = 4688803) B4688803
theorem B5555459 : Blo 1299968 5555459 := bstep (se 1 (by rfl) ⟨4166594, by rfl⟩ : syracuseStep 5555459 = 8333189) B8333189
theorem B1951001 : Blo 1299968 1951001 := bstep (se 2 (by rfl) ⟨731625, by rfl⟩ : syracuseStep 1951001 = 1463251) B1463251
theorem B4941101 : Blo 1299968 4941101 := bstep (se 3 (by rfl) ⟨926456, by rfl⟩ : syracuseStep 4941101 = 1852913) B1852913
theorem B2925899 : Blo 1299968 2925899 := bstep (se 1 (by rfl) ⟨2194424, by rfl⟩ : syracuseStep 2925899 = 4388849) B4388849
theorem B3294553 : Blo 1299968 3294553 := bstep (se 2 (by rfl) ⟨1235457, by rfl⟩ : syracuseStep 3294553 = 2470915) B2470915
theorem B2925953 : Blo 1299968 2925953 := bstep (se 2 (by rfl) ⟨1097232, by rfl⟩ : syracuseStep 2925953 = 2194465) B2194465
theorem B1951115 : Blo 1299968 1951115 := bstep (se 1 (by rfl) ⟨1463336, by rfl⟩ : syracuseStep 1951115 = 2926673) B2926673
theorem B2196875 : Blo 1299968 2196875 := bstep (se 1 (by rfl) ⟨1647656, by rfl⟩ : syracuseStep 2196875 = 3295313) B3295313
theorem B1951127 : Blo 1299968 1951127 := bstep (se 1 (by rfl) ⟨1463345, by rfl⟩ : syracuseStep 1951127 = 2926691) B2926691
theorem B1951193 : Blo 1299968 1951193 := bstep (se 2 (by rfl) ⟨731697, by rfl⟩ : syracuseStep 1951193 = 1463395) B1463395
theorem B4392413 : Blo 1299968 4392413 := bstep (se 3 (by rfl) ⟨823577, by rfl⟩ : syracuseStep 4392413 = 1647155) B1647155
theorem B2197003 : Blo 1299968 2197003 := bstep (se 1 (by rfl) ⟨1647752, by rfl⟩ : syracuseStep 2197003 = 3295505) B3295505
theorem B1951307 : Blo 1299968 1951307 := bstep (se 1 (by rfl) ⟨1463480, by rfl⟩ : syracuseStep 1951307 = 2926961) B2926961
theorem B1951319 : Blo 1299968 1951319 := bstep (se 1 (by rfl) ⟨1463489, by rfl⟩ : syracuseStep 1951319 = 2926979) B2926979
theorem B2926169 : Blo 1299968 2926169 := bstep (se 2 (by rfl) ⟨1097313, by rfl⟩ : syracuseStep 2926169 = 2194627) B2194627
theorem B1951385 : Blo 1299968 1951385 := bstep (se 2 (by rfl) ⟨731769, by rfl⟩ : syracuseStep 1951385 = 1463539) B1463539
theorem B2926259 : Blo 1299968 2926259 := bstep (se 1 (by rfl) ⟨2194694, by rfl⟩ : syracuseStep 2926259 = 4389389) B4389389
theorem B2926295 : Blo 1299968 2926295 := bstep (se 1 (by rfl) ⟨2194721, by rfl⟩ : syracuseStep 2926295 = 4389443) B4389443
theorem B14829317 : Blo 1299968 14829317 := bstep (se 4 (by rfl) ⟨1390248, by rfl⟩ : syracuseStep 14829317 = 2780497) B2780497
theorem B1951499 : Blo 1299968 1951499 := bstep (se 1 (by rfl) ⟨1463624, by rfl⟩ : syracuseStep 1951499 = 2927249) B2927249
theorem B1951511 : Blo 1299968 1951511 := bstep (se 1 (by rfl) ⟨1463633, by rfl⟩ : syracuseStep 1951511 = 2927267) B2927267
theorem B1853209 : Blo 1299968 1853209 := bstep (se 2 (by rfl) ⟨694953, by rfl⟩ : syracuseStep 1853209 = 1389907) B1389907
theorem B4450099 : Blo 1299968 4450099 := bstep (se 1 (by rfl) ⟨3337574, by rfl⟩ : syracuseStep 4450099 = 6675149) B6675149
theorem B6252353 : Blo 1299968 6252353 := bstep (se 2 (by rfl) ⟨2344632, by rfl⟩ : syracuseStep 6252353 = 4689265) B4689265
theorem B1951577 : Blo 1299968 1951577 := bstep (se 2 (by rfl) ⟨731841, by rfl⟩ : syracuseStep 1951577 = 1463683) B1463683
theorem B2926475 : Blo 1299968 2926475 := bstep (se 1 (by rfl) ⟨2194856, by rfl⟩ : syracuseStep 2926475 = 4389713) B4389713
theorem B2926529 : Blo 1299968 2926529 := bstep (se 2 (by rfl) ⟨1097448, by rfl⟩ : syracuseStep 2926529 = 2194897) B2194897
theorem B1951691 : Blo 1299968 1951691 := bstep (se 1 (by rfl) ⟨1463768, by rfl⟩ : syracuseStep 1951691 = 2927537) B2927537
theorem B1951703 : Blo 1299968 1951703 := bstep (se 1 (by rfl) ⟨1463777, by rfl⟩ : syracuseStep 1951703 = 2927555) B2927555
theorem B6588377 : Blo 1299968 6588377 := bstep (se 2 (by rfl) ⟨2470641, by rfl⟩ : syracuseStep 6588377 = 4941283) B4941283
theorem B2779123 : Blo 1299968 2779123 := bstep (se 1 (by rfl) ⟨2084342, by rfl⟩ : syracuseStep 2779123 = 4168685) B4168685
theorem B1951769 : Blo 1299968 1951769 := bstep (se 2 (by rfl) ⟨731913, by rfl⟩ : syracuseStep 1951769 = 1463827) B1463827
theorem B2377793 : Blo 1299968 2377793 := bstep (se 2 (by rfl) ⟨891672, by rfl⟩ : syracuseStep 2377793 = 1783345) B1783345
theorem B1951883 : Blo 1299968 1951883 := bstep (se 1 (by rfl) ⟨1463912, by rfl⟩ : syracuseStep 1951883 = 2927825) B2927825
theorem B1951895 : Blo 1299968 1951895 := bstep (se 1 (by rfl) ⟨1463921, by rfl⟩ : syracuseStep 1951895 = 2927843) B2927843
theorem B2926745 : Blo 1299968 2926745 := bstep (se 2 (by rfl) ⟨1097529, by rfl⟩ : syracuseStep 2926745 = 2195059) B2195059
theorem B3336385 : Blo 1299968 3336385 := bstep (se 2 (by rfl) ⟨1251144, by rfl⟩ : syracuseStep 3336385 = 2502289) B2502289
theorem B1951961 : Blo 1299968 1951961 := bstep (se 2 (by rfl) ⟨731985, by rfl⟩ : syracuseStep 1951961 = 1463971) B1463971
theorem B2468083 : Blo 1299968 2468083 := bstep (se 1 (by rfl) ⟨1851062, by rfl⟩ : syracuseStep 2468083 = 3702125) B3702125
theorem B2926835 : Blo 1299968 2926835 := bstep (se 1 (by rfl) ⟨2195126, by rfl⟩ : syracuseStep 2926835 = 4390253) B4390253
theorem B2926871 : Blo 1299968 2926871 := bstep (se 1 (by rfl) ⟨2195153, by rfl⟩ : syracuseStep 2926871 = 4390307) B4390307
theorem B1952075 : Blo 1299968 1952075 := bstep (se 1 (by rfl) ⟨1464056, by rfl⟩ : syracuseStep 1952075 = 2928113) B2928113
theorem B1952087 : Blo 1299968 1952087 := bstep (se 1 (by rfl) ⟨1464065, by rfl⟩ : syracuseStep 1952087 = 2928131) B2928131
theorem B16673141 : Blo 1299968 16673141 := bstep (se 5 (by rfl) ⟨781553, by rfl⟩ : syracuseStep 16673141 = 1563107) B1563107
theorem B1952153 : Blo 1299968 1952153 := bstep (se 2 (by rfl) ⟨732057, by rfl⟩ : syracuseStep 1952153 = 1464115) B1464115
theorem B2927051 : Blo 1299968 2927051 := bstep (se 1 (by rfl) ⟨2195288, by rfl⟩ : syracuseStep 2927051 = 4390577) B4390577
theorem B2779609 : Blo 1299968 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B2927105 : Blo 1299968 2927105 := bstep (se 2 (by rfl) ⟨1097664, by rfl⟩ : syracuseStep 2927105 = 2195329) B2195329
theorem B1952267 : Blo 1299968 1952267 := bstep (se 1 (by rfl) ⟨1464200, by rfl⟩ : syracuseStep 1952267 = 2928401) B2928401
theorem B1952279 : Blo 1299968 1952279 := bstep (se 1 (by rfl) ⟨1464209, by rfl⟩ : syracuseStep 1952279 = 2928419) B2928419
theorem B4393547 : Blo 1299968 4393547 := bstep (se 1 (by rfl) ⟨3295160, by rfl⟩ : syracuseStep 4393547 = 6590321) B6590321
theorem B1952345 : Blo 1299968 1952345 := bstep (se 2 (by rfl) ⟨732129, by rfl⟩ : syracuseStep 1952345 = 1464259) B1464259
theorem B7408259 : Blo 1299968 7408259 := bstep (se 1 (by rfl) ⟨5556194, by rfl⟩ : syracuseStep 7408259 = 11112389) B11112389
theorem B2468531 : Blo 1299968 2468531 := bstep (se 1 (by rfl) ⟨1851398, by rfl⟩ : syracuseStep 2468531 = 3702797) B3702797
theorem B4942529 : Blo 1299968 4942529 := bstep (se 2 (by rfl) ⟨1853448, by rfl⟩ : syracuseStep 4942529 = 3706897) B3706897
theorem B1952459 : Blo 1299968 1952459 := bstep (se 1 (by rfl) ⟨1464344, by rfl⟩ : syracuseStep 1952459 = 2928689) B2928689
theorem B1952471 : Blo 1299968 1952471 := bstep (se 1 (by rfl) ⟨1464353, by rfl⟩ : syracuseStep 1952471 = 2928707) B2928707
theorem B2468569 : Blo 1299968 2468569 := bstep (se 2 (by rfl) ⟨925713, by rfl⟩ : syracuseStep 2468569 = 1851427) B1851427
theorem B2927321 : Blo 1299968 2927321 := bstep (se 2 (by rfl) ⟨1097745, by rfl⟩ : syracuseStep 2927321 = 2195491) B2195491
theorem B1952537 : Blo 1299968 1952537 := bstep (se 2 (by rfl) ⟨732201, by rfl⟩ : syracuseStep 1952537 = 1464403) B1464403
theorem B2927411 : Blo 1299968 2927411 := bstep (se 1 (by rfl) ⟨2195558, by rfl⟩ : syracuseStep 2927411 = 4391117) B4391117
theorem B2927447 : Blo 1299968 2927447 := bstep (se 1 (by rfl) ⟨2195585, by rfl⟩ : syracuseStep 2927447 = 4391171) B4391171
theorem B3517273 : Blo 1299968 3517273 := bstep (se 2 (by rfl) ⟨1318977, by rfl⟩ : syracuseStep 3517273 = 2637955) B2637955
theorem B3705689 : Blo 1299968 3705689 := bstep (se 2 (by rfl) ⟨1389633, by rfl⟩ : syracuseStep 3705689 = 2779267) B2779267
theorem B4393817 : Blo 1299968 4393817 := bstep (se 2 (by rfl) ⟨1647681, by rfl⟩ : syracuseStep 4393817 = 3295363) B3295363
theorem B1952651 : Blo 1299968 1952651 := bstep (se 1 (by rfl) ⟨1464488, by rfl⟩ : syracuseStep 1952651 = 2928977) B2928977
theorem B1952663 : Blo 1299968 1952663 := bstep (se 1 (by rfl) ⟨1464497, by rfl⟩ : syracuseStep 1952663 = 2928995) B2928995
theorem B3337163 : Blo 1299968 3337163 := bstep (se 1 (by rfl) ⟨2502872, by rfl⟩ : syracuseStep 3337163 = 5005745) B5005745
theorem B1952729 : Blo 1299968 1952729 := bstep (se 2 (by rfl) ⟨732273, by rfl⟩ : syracuseStep 1952729 = 1464547) B1464547
theorem B2927627 : Blo 1299968 2927627 := bstep (se 1 (by rfl) ⟨2195720, by rfl⟩ : syracuseStep 2927627 = 4391441) B4391441
theorem B2927681 : Blo 1299968 2927681 := bstep (se 2 (by rfl) ⟨1097880, by rfl⟩ : syracuseStep 2927681 = 2195761) B2195761
theorem B1952843 : Blo 1299968 1952843 := bstep (se 1 (by rfl) ⟨1464632, by rfl⟩ : syracuseStep 1952843 = 2929265) B2929265
theorem B1952855 : Blo 1299968 1952855 := bstep (se 1 (by rfl) ⟨1464641, by rfl⟩ : syracuseStep 1952855 = 2929283) B2929283
theorem B10546307 : Blo 1299968 10546307 := bstep (se 1 (by rfl) ⟨7909730, by rfl⟩ : syracuseStep 10546307 = 15819461) B15819461
theorem B8899735 : Blo 1299968 8899735 := bstep (se 1 (by rfl) ⟨6674801, by rfl⟩ : syracuseStep 8899735 = 13349603) B13349603
theorem B2469017 : Blo 1299968 2469017 := bstep (se 2 (by rfl) ⟨925881, by rfl⟩ : syracuseStep 2469017 = 1851763) B1851763
theorem B1952921 : Blo 1299968 1952921 := bstep (se 2 (by rfl) ⟨732345, by rfl⟩ : syracuseStep 1952921 = 1464691) B1464691
theorem B2927897 : Blo 1299968 2927897 := bstep (se 2 (by rfl) ⟨1097961, by rfl⟩ : syracuseStep 2927897 = 2195923) B2195923
theorem B4164929 : Blo 1299968 4164929 := bstep (se 2 (by rfl) ⟨1561848, by rfl⟩ : syracuseStep 4164929 = 3123697) B3123697
theorem B2927987 : Blo 1299968 2927987 := bstep (se 1 (by rfl) ⟨2195990, by rfl⟩ : syracuseStep 2927987 = 4391981) B4391981
theorem B2928023 : Blo 1299968 2928023 := bstep (se 1 (by rfl) ⟨2196017, by rfl⟩ : syracuseStep 2928023 = 4392035) B4392035
theorem B14814737 : Blo 1299968 14814737 := bstep (se 2 (by rfl) ⟨5555526, by rfl⟩ : syracuseStep 14814737 = 11111053) B11111053
theorem B6589997 : Blo 1299968 6589997 := bstep (se 3 (by rfl) ⟨1235624, by rfl⟩ : syracuseStep 6589997 = 2471249) B2471249
theorem B11112011 : Blo 1299968 11112011 := bstep (se 1 (by rfl) ⟨8334008, by rfl⟩ : syracuseStep 11112011 = 16668017) B16668017
theorem B5557835 : Blo 1299968 5557835 := bstep (se 1 (by rfl) ⟨4168376, by rfl⟩ : syracuseStep 5557835 = 8336753) B8336753
theorem B2928203 : Blo 1299968 2928203 := bstep (se 1 (by rfl) ⟨2196152, by rfl⟩ : syracuseStep 2928203 = 4392305) B4392305
theorem B2928257 : Blo 1299968 2928257 := bstep (se 2 (by rfl) ⟨1098096, by rfl⟩ : syracuseStep 2928257 = 2196193) B2196193
theorem B6016643 : Blo 1299968 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B5009069 : Blo 1299968 5009069 := bstep (se 3 (by rfl) ⟨939200, by rfl⟩ : syracuseStep 5009069 = 1878401) B1878401
theorem B9375533 : Blo 1299968 9375533 := bstep (se 3 (by rfl) ⟨1757912, by rfl⟩ : syracuseStep 9375533 = 3515825) B3515825
theorem B1978187 : Blo 1299968 1978187 := bstep (se 1 (by rfl) ⟨1483640, by rfl⟩ : syracuseStep 1978187 = 2967281) B2967281
theorem B3125081 : Blo 1299968 3125081 := bstep (se 2 (by rfl) ⟨1171905, by rfl⟩ : syracuseStep 3125081 = 2343811) B2343811
theorem B2928473 : Blo 1299968 2928473 := bstep (se 2 (by rfl) ⟨1098177, by rfl⟩ : syracuseStep 2928473 = 2196355) B2196355
theorem B2469761 : Blo 1299968 2469761 := bstep (se 2 (by rfl) ⟨926160, by rfl⟩ : syracuseStep 2469761 = 1852321) B1852321
theorem B2928563 : Blo 1299968 2928563 := bstep (se 1 (by rfl) ⟨2196422, by rfl⟩ : syracuseStep 2928563 = 4392845) B4392845
theorem B2928599 : Blo 1299968 2928599 := bstep (se 1 (by rfl) ⟨2196449, by rfl⟩ : syracuseStep 2928599 = 4392899) B4392899
theorem B7909337 : Blo 1299968 7909337 := bstep (se 2 (by rfl) ⟨2966001, by rfl⟩ : syracuseStep 7909337 = 5932003) B5932003
theorem B3706955 : Blo 1299968 3706955 := bstep (se 1 (by rfl) ⟨2780216, by rfl⟩ : syracuseStep 3706955 = 5560433) B5560433
theorem B9375875 : Blo 1299968 9375875 := bstep (se 1 (by rfl) ⟨7031906, by rfl⟩ : syracuseStep 9375875 = 14063813) B14063813
theorem B2470027 : Blo 1299968 2470027 := bstep (se 1 (by rfl) ⟨1852520, by rfl⟩ : syracuseStep 2470027 = 3705041) B3705041
theorem B2928779 : Blo 1299968 2928779 := bstep (se 1 (by rfl) ⟨2196584, by rfl⟩ : syracuseStep 2928779 = 4393169) B4393169
theorem B4165825 : Blo 1299968 4165825 := bstep (se 2 (by rfl) ⟨1562184, by rfl⟩ : syracuseStep 4165825 = 3124369) B3124369
theorem B2928833 : Blo 1299968 2928833 := bstep (se 2 (by rfl) ⟨1098312, by rfl⟩ : syracuseStep 2928833 = 2196625) B2196625
theorem B6582545 : Blo 1299968 6582545 := bstep (se 2 (by rfl) ⟨2468454, by rfl⟩ : syracuseStep 6582545 = 4936909) B4936909
theorem B15012161 : Blo 1299968 15012161 := bstep (se 2 (by rfl) ⟨5629560, by rfl⟩ : syracuseStep 15012161 = 11259121) B11259121
theorem B11260225 : Blo 1299968 11260225 := bstep (se 2 (by rfl) ⟨4222584, by rfl⟩ : syracuseStep 11260225 = 8445169) B8445169
theorem B17797441 : Blo 1299968 17797441 := bstep (se 2 (by rfl) ⟨6674040, by rfl⟩ : syracuseStep 17797441 = 13348081) B13348081
theorem B1462603 : Blo 1299968 1462603 := bstep (se 1 (by rfl) ⟨1096952, by rfl⟩ : syracuseStep 1462603 = 2193905) B2193905
theorem B2929049 : Blo 1299968 2929049 := bstep (se 2 (by rfl) ⟨1098393, by rfl⟩ : syracuseStep 2929049 = 2196787) B2196787
theorem B6582707 : Blo 1299968 6582707 := bstep (se 1 (by rfl) ⟨4937030, by rfl⟩ : syracuseStep 6582707 = 9874061) B9874061
theorem B1462711 : Blo 1299968 1462711 := bstep (se 1 (by rfl) ⟨1097033, by rfl⟩ : syracuseStep 1462711 = 2194067) B2194067
theorem B2929139 : Blo 1299968 2929139 := bstep (se 1 (by rfl) ⟨2196854, by rfl⟩ : syracuseStep 2929139 = 4393709) B4393709
theorem B63336977 : Blo 1299968 63336977 := bstep (se 2 (by rfl) ⟨23751366, by rfl⟩ : syracuseStep 63336977 = 47502733) B47502733
theorem B5558807 : Blo 1299968 5558807 := bstep (se 1 (by rfl) ⟨4169105, by rfl⟩ : syracuseStep 5558807 = 8338211) B8338211
theorem B2929175 : Blo 1299968 2929175 := bstep (se 1 (by rfl) ⟨2196881, by rfl⟩ : syracuseStep 2929175 = 4393763) B4393763
theorem B15012427 : Blo 1299968 15012427 := bstep (se 1 (by rfl) ⟨11259320, by rfl⟩ : syracuseStep 15012427 = 22518641) B22518641
theorem B2470475 : Blo 1299968 2470475 := bstep (se 1 (by rfl) ⟨1852856, by rfl⟩ : syracuseStep 2470475 = 3705713) B3705713
theorem B6255197 : Blo 1299968 6255197 := bstep (se 3 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 6255197 = 2345699) B2345699
theorem B1462891 : Blo 1299968 1462891 := bstep (se 1 (by rfl) ⟨1097168, by rfl⟩ : syracuseStep 1462891 = 2194337) B2194337
theorem B2708147 : Blo 1299968 2708147 := bstep (se 1 (by rfl) ⟨2031110, by rfl⟩ : syracuseStep 2708147 = 4062221) B4062221
theorem B2929355 : Blo 1299968 2929355 := bstep (se 1 (by rfl) ⟨2197016, by rfl⟩ : syracuseStep 2929355 = 4394033) B4394033
theorem B1462999 : Blo 1299968 1462999 := bstep (se 1 (by rfl) ⟨1097249, by rfl⟩ : syracuseStep 1462999 = 2194499) B2194499
theorem B4936409 : Blo 1299968 4936409 := bstep (se 2 (by rfl) ⟨1851153, by rfl⟩ : syracuseStep 4936409 = 3702307) B3702307
theorem B4690649 : Blo 1299968 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B2470657 : Blo 1299968 2470657 := bstep (se 2 (by rfl) ⟨926496, by rfl⟩ : syracuseStep 2470657 = 1852993) B1852993
theorem B2929409 : Blo 1299968 2929409 := bstep (se 2 (by rfl) ⟨1098528, by rfl⟩ : syracuseStep 2929409 = 2197057) B2197057
theorem B4387607 : Blo 1299968 4387607 := bstep (se 1 (by rfl) ⟨3290705, by rfl⟩ : syracuseStep 4387607 = 6581411) B6581411
theorem B2503489 : Blo 1299968 2503489 := bstep (se 2 (by rfl) ⟨938808, by rfl⟩ : syracuseStep 2503489 = 1877617) B1877617
theorem B1463179 : Blo 1299968 1463179 := bstep (se 1 (by rfl) ⟨1097384, by rfl⟩ : syracuseStep 1463179 = 2194769) B2194769
theorem B10294193 : Blo 1299968 10294193 := bstep (se 2 (by rfl) ⟨3860322, by rfl⟩ : syracuseStep 10294193 = 7720645) B7720645
theorem B7410649 : Blo 1299968 7410649 := bstep (se 2 (by rfl) ⟨2778993, by rfl⟩ : syracuseStep 7410649 = 5557987) B5557987
theorem B1463287 : Blo 1299968 1463287 := bstep (se 1 (by rfl) ⟨1097465, by rfl⟩ : syracuseStep 1463287 = 2194931) B2194931
theorem B4936727 : Blo 1299968 4936727 := bstep (se 1 (by rfl) ⟨3702545, by rfl⟩ : syracuseStep 4936727 = 7405091) B7405091
theorem B2470999 : Blo 1299968 2470999 := bstep (se 1 (by rfl) ⟨1853249, by rfl⟩ : syracuseStep 2470999 = 3706499) B3706499
theorem B1463467 : Blo 1299968 1463467 := bstep (se 1 (by rfl) ⟨1097600, by rfl⟩ : syracuseStep 1463467 = 2195201) B2195201
theorem B5559475 : Blo 1299968 5559475 := bstep (se 1 (by rfl) ⟨4169606, by rfl⟩ : syracuseStep 5559475 = 8339213) B8339213
theorem B1389835 : Blo 1299968 1389835 := bstep (se 1 (by rfl) ⟨1042376, by rfl⟩ : syracuseStep 1389835 = 2084753) B2084753
theorem B1463575 : Blo 1299968 1463575 := bstep (se 1 (by rfl) ⟨1097681, by rfl⟩ : syracuseStep 1463575 = 2195363) B2195363
theorem B4388147 : Blo 1299968 4388147 := bstep (se 1 (by rfl) ⟨3291110, by rfl⟩ : syracuseStep 4388147 = 6582221) B6582221
theorem B2471219 : Blo 1299968 2471219 := bstep (se 1 (by rfl) ⟨1853414, by rfl⟩ : syracuseStep 2471219 = 3706829) B3706829
theorem B2815319 : Blo 1299968 2815319 := bstep (se 1 (by rfl) ⟨2111489, by rfl⟩ : syracuseStep 2815319 = 4222979) B4222979
theorem B1463755 : Blo 1299968 1463755 := bstep (se 1 (by rfl) ⟨1097816, by rfl⟩ : syracuseStep 1463755 = 2195633) B2195633
theorem B1299979 : Blo 1299968 1299979 := bstep (se 1 (by rfl) ⟨974984, by rfl⟩ : syracuseStep 1299979 = 1949969) B1949969
theorem B1299991 : Blo 1299968 1299991 := bstep (se 1 (by rfl) ⟨974993, by rfl⟩ : syracuseStep 1299991 = 1949987) B1949987
theorem B2471447 : Blo 1299968 2471447 := bstep (se 1 (by rfl) ⟨1853585, by rfl⟩ : syracuseStep 2471447 = 3707171) B3707171
theorem B1300011 : Blo 1299968 1300011 := bstep (se 1 (by rfl) ⟨975008, by rfl⟩ : syracuseStep 1300011 = 1950017) B1950017
theorem B1300023 : Blo 1299968 1300023 := bstep (se 1 (by rfl) ⟨975017, by rfl⟩ : syracuseStep 1300023 = 1950035) B1950035
theorem B1463863 : Blo 1299968 1463863 := bstep (se 1 (by rfl) ⟨1097897, by rfl⟩ : syracuseStep 1463863 = 2195795) B2195795
theorem B4388417 : Blo 1299968 4388417 := bstep (se 2 (by rfl) ⟨1645656, by rfl⟩ : syracuseStep 4388417 = 3291313) B3291313
theorem B1300043 : Blo 1299968 1300043 := bstep (se 1 (by rfl) ⟨975032, by rfl⟩ : syracuseStep 1300043 = 1950065) B1950065
theorem B1300055 : Blo 1299968 1300055 := bstep (se 1 (by rfl) ⟨975041, by rfl⟩ : syracuseStep 1300055 = 1950083) B1950083
theorem B1300075 : Blo 1299968 1300075 := bstep (se 1 (by rfl) ⟨975056, by rfl⟩ : syracuseStep 1300075 = 1950113) B1950113
theorem B1300087 : Blo 1299968 1300087 := bstep (se 1 (by rfl) ⟨975065, by rfl⟩ : syracuseStep 1300087 = 1950131) B1950131
theorem B1300107 : Blo 1299968 1300107 := bstep (se 1 (by rfl) ⟨975080, by rfl⟩ : syracuseStep 1300107 = 1950161) B1950161
theorem B1300119 : Blo 1299968 1300119 := bstep (se 1 (by rfl) ⟨975089, by rfl⟩ : syracuseStep 1300119 = 1950179) B1950179
theorem B1300139 : Blo 1299968 1300139 := bstep (se 1 (by rfl) ⟨975104, by rfl⟩ : syracuseStep 1300139 = 1950209) B1950209
theorem B4937395 : Blo 1299968 4937395 := bstep (se 1 (by rfl) ⟨3703046, by rfl⟩ : syracuseStep 4937395 = 7406093) B7406093
theorem B5273267 : Blo 1299968 5273267 := bstep (se 1 (by rfl) ⟨3954950, by rfl⟩ : syracuseStep 5273267 = 7909901) B7909901
theorem B1300151 : Blo 1299968 1300151 := bstep (se 1 (by rfl) ⟨975113, by rfl⟩ : syracuseStep 1300151 = 1950227) B1950227
theorem B3290827 : Blo 1299968 3290827 := bstep (se 1 (by rfl) ⟨2468120, by rfl⟩ : syracuseStep 3290827 = 4936241) B4936241
theorem B1300171 : Blo 1299968 1300171 := bstep (se 1 (by rfl) ⟨975128, by rfl⟩ : syracuseStep 1300171 = 1950257) B1950257
theorem B1300183 : Blo 1299968 1300183 := bstep (se 1 (by rfl) ⟨975137, by rfl⟩ : syracuseStep 1300183 = 1950275) B1950275
theorem B4167389 : Blo 1299968 4167389 := bstep (se 3 (by rfl) ⟨781385, by rfl⟩ : syracuseStep 4167389 = 1562771) B1562771
theorem B1300203 : Blo 1299968 1300203 := bstep (se 1 (by rfl) ⟨975152, by rfl⟩ : syracuseStep 1300203 = 1950305) B1950305
theorem B1464043 : Blo 1299968 1464043 := bstep (se 1 (by rfl) ⟨1098032, by rfl⟩ : syracuseStep 1464043 = 2196065) B2196065
theorem B1300215 : Blo 1299968 1300215 := bstep (se 1 (by rfl) ⟨975161, by rfl⟩ : syracuseStep 1300215 = 1950323) B1950323
theorem B1300235 : Blo 1299968 1300235 := bstep (se 1 (by rfl) ⟨975176, by rfl⟩ : syracuseStep 1300235 = 1950353) B1950353
theorem B1300247 : Blo 1299968 1300247 := bstep (se 1 (by rfl) ⟨975185, by rfl⟩ : syracuseStep 1300247 = 1950371) B1950371
theorem B2471705 : Blo 1299968 2471705 := bstep (se 2 (by rfl) ⟨926889, by rfl⟩ : syracuseStep 2471705 = 1853779) B1853779
theorem B1300267 : Blo 1299968 1300267 := bstep (se 1 (by rfl) ⟨975200, by rfl⟩ : syracuseStep 1300267 = 1950401) B1950401
theorem B1300279 : Blo 1299968 1300279 := bstep (se 1 (by rfl) ⟨975209, by rfl⟩ : syracuseStep 1300279 = 1950419) B1950419
theorem B1300299 : Blo 1299968 1300299 := bstep (se 1 (by rfl) ⟨975224, by rfl⟩ : syracuseStep 1300299 = 1950449) B1950449
theorem B1300311 : Blo 1299968 1300311 := bstep (se 1 (by rfl) ⟨975233, by rfl⟩ : syracuseStep 1300311 = 1950467) B1950467
theorem B3290969 : Blo 1299968 3290969 := bstep (se 2 (by rfl) ⟨1234113, by rfl⟩ : syracuseStep 3290969 = 2468227) B2468227
theorem B1464151 : Blo 1299968 1464151 := bstep (se 1 (by rfl) ⟨1098113, by rfl⟩ : syracuseStep 1464151 = 2196227) B2196227
theorem B1300331 : Blo 1299968 1300331 := bstep (se 1 (by rfl) ⟨975248, by rfl⟩ : syracuseStep 1300331 = 1950497) B1950497
theorem B1300343 : Blo 1299968 1300343 := bstep (se 1 (by rfl) ⟨975257, by rfl⟩ : syracuseStep 1300343 = 1950515) B1950515
theorem B1300363 : Blo 1299968 1300363 := bstep (se 1 (by rfl) ⟨975272, by rfl⟩ : syracuseStep 1300363 = 1950545) B1950545
theorem B1300375 : Blo 1299968 1300375 := bstep (se 1 (by rfl) ⟨975281, by rfl⟩ : syracuseStep 1300375 = 1950563) B1950563
theorem B7411607 : Blo 1299968 7411607 := bstep (se 1 (by rfl) ⟨5558705, by rfl⟩ : syracuseStep 7411607 = 11117411) B11117411
theorem B1300395 : Blo 1299968 1300395 := bstep (se 1 (by rfl) ⟨975296, by rfl⟩ : syracuseStep 1300395 = 1950593) B1950593
theorem B1300407 : Blo 1299968 1300407 := bstep (se 1 (by rfl) ⟨975305, by rfl⟩ : syracuseStep 1300407 = 1950611) B1950611
theorem B1300427 : Blo 1299968 1300427 := bstep (se 1 (by rfl) ⟨975320, by rfl⟩ : syracuseStep 1300427 = 1950641) B1950641
theorem B1300439 : Blo 1299968 1300439 := bstep (se 1 (by rfl) ⟨975329, by rfl⟩ : syracuseStep 1300439 = 1950659) B1950659
theorem B1300459 : Blo 1299968 1300459 := bstep (se 1 (by rfl) ⟨975344, by rfl⟩ : syracuseStep 1300459 = 1950689) B1950689
theorem B1300471 : Blo 1299968 1300471 := bstep (se 1 (by rfl) ⟨975353, by rfl⟩ : syracuseStep 1300471 = 1950707) B1950707
theorem B1300491 : Blo 1299968 1300491 := bstep (se 1 (by rfl) ⟨975368, by rfl⟩ : syracuseStep 1300491 = 1950737) B1950737
theorem B1464331 : Blo 1299968 1464331 := bstep (se 1 (by rfl) ⟨1098248, by rfl⟩ : syracuseStep 1464331 = 2196497) B2196497
theorem B1300503 : Blo 1299968 1300503 := bstep (se 1 (by rfl) ⟨975377, by rfl⟩ : syracuseStep 1300503 = 1950755) B1950755
theorem B1300523 : Blo 1299968 1300523 := bstep (se 1 (by rfl) ⟨975392, by rfl⟩ : syracuseStep 1300523 = 1950785) B1950785
theorem B1300535 : Blo 1299968 1300535 := bstep (se 1 (by rfl) ⟨975401, by rfl⟩ : syracuseStep 1300535 = 1950803) B1950803
theorem B1300555 : Blo 1299968 1300555 := bstep (se 1 (by rfl) ⟨975416, by rfl⟩ : syracuseStep 1300555 = 1950833) B1950833
theorem B1300567 : Blo 1299968 1300567 := bstep (se 1 (by rfl) ⟨975425, by rfl⟩ : syracuseStep 1300567 = 1950851) B1950851
theorem B4388957 : Blo 1299968 4388957 := bstep (se 3 (by rfl) ⟨822929, by rfl⟩ : syracuseStep 4388957 = 1645859) B1645859
theorem B1300587 : Blo 1299968 1300587 := bstep (se 1 (by rfl) ⟨975440, by rfl⟩ : syracuseStep 1300587 = 1950881) B1950881
theorem B1300599 : Blo 1299968 1300599 := bstep (se 1 (by rfl) ⟨975449, by rfl⟩ : syracuseStep 1300599 = 1950899) B1950899
theorem B1464439 : Blo 1299968 1464439 := bstep (se 1 (by rfl) ⟨1098329, by rfl⟩ : syracuseStep 1464439 = 2196659) B2196659
theorem B1300619 : Blo 1299968 1300619 := bstep (se 1 (by rfl) ⟨975464, by rfl⟩ : syracuseStep 1300619 = 1950929) B1950929
theorem B1300631 : Blo 1299968 1300631 := bstep (se 1 (by rfl) ⟨975473, by rfl⟩ : syracuseStep 1300631 = 1950947) B1950947
theorem B1300651 : Blo 1299968 1300651 := bstep (se 1 (by rfl) ⟨975488, by rfl⟩ : syracuseStep 1300651 = 1950977) B1950977
theorem B1300663 : Blo 1299968 1300663 := bstep (se 1 (by rfl) ⟨975497, by rfl⟩ : syracuseStep 1300663 = 1950995) B1950995
theorem B1300683 : Blo 1299968 1300683 := bstep (se 1 (by rfl) ⟨975512, by rfl⟩ : syracuseStep 1300683 = 1951025) B1951025
theorem B1300695 : Blo 1299968 1300695 := bstep (se 1 (by rfl) ⟨975521, by rfl⟩ : syracuseStep 1300695 = 1951043) B1951043
theorem B3127513 : Blo 1299968 3127513 := bstep (se 2 (by rfl) ⟨1172817, by rfl⟩ : syracuseStep 3127513 = 2345635) B2345635
theorem B1300715 : Blo 1299968 1300715 := bstep (se 1 (by rfl) ⟨975536, by rfl⟩ : syracuseStep 1300715 = 1951073) B1951073
theorem B1300727 : Blo 1299968 1300727 := bstep (se 1 (by rfl) ⟨975545, by rfl⟩ : syracuseStep 1300727 = 1951091) B1951091
theorem B1300747 : Blo 1299968 1300747 := bstep (se 1 (by rfl) ⟨975560, by rfl⟩ : syracuseStep 1300747 = 1951121) B1951121
theorem B1300759 : Blo 1299968 1300759 := bstep (se 1 (by rfl) ⟨975569, by rfl⟩ : syracuseStep 1300759 = 1951139) B1951139
theorem B1300779 : Blo 1299968 1300779 := bstep (se 1 (by rfl) ⟨975584, by rfl⟩ : syracuseStep 1300779 = 1951169) B1951169
theorem B1464619 : Blo 1299968 1464619 := bstep (se 1 (by rfl) ⟨1098464, by rfl⟩ : syracuseStep 1464619 = 2196929) B2196929
theorem B1300791 : Blo 1299968 1300791 := bstep (se 1 (by rfl) ⟨975593, by rfl⟩ : syracuseStep 1300791 = 1951187) B1951187
theorem B6584651 : Blo 1299968 6584651 := bstep (se 1 (by rfl) ⟨4938488, by rfl⟩ : syracuseStep 6584651 = 9876977) B9876977
theorem B1300811 : Blo 1299968 1300811 := bstep (se 1 (by rfl) ⟨975608, by rfl⟩ : syracuseStep 1300811 = 1951217) B1951217
theorem B1300823 : Blo 1299968 1300823 := bstep (se 1 (by rfl) ⟨975617, by rfl⟩ : syracuseStep 1300823 = 1951235) B1951235
theorem B1759577 : Blo 1299968 1759577 := bstep (se 2 (by rfl) ⟨659841, by rfl⟩ : syracuseStep 1759577 = 1319683) B1319683
theorem B1300843 : Blo 1299968 1300843 := bstep (se 1 (by rfl) ⟨975632, by rfl⟩ : syracuseStep 1300843 = 1951265) B1951265
theorem B14817653 : Blo 1299968 14817653 := bstep (se 5 (by rfl) ⟨694577, by rfl⟩ : syracuseStep 14817653 = 1389155) B1389155
theorem B1300855 : Blo 1299968 1300855 := bstep (se 1 (by rfl) ⟨975641, by rfl⟩ : syracuseStep 1300855 = 1951283) B1951283
theorem B5003651 : Blo 1299968 5003651 := bstep (se 1 (by rfl) ⟨3752738, by rfl⟩ : syracuseStep 5003651 = 7505477) B7505477
theorem B1300875 : Blo 1299968 1300875 := bstep (se 1 (by rfl) ⟨975656, by rfl⟩ : syracuseStep 1300875 = 1951313) B1951313
theorem B5560721 : Blo 1299968 5560721 := bstep (se 2 (by rfl) ⟨2085270, by rfl⟩ : syracuseStep 5560721 = 4170541) B4170541
theorem B1300887 : Blo 1299968 1300887 := bstep (se 1 (by rfl) ⟨975665, by rfl⟩ : syracuseStep 1300887 = 1951331) B1951331
theorem B2193817 : Blo 1299968 2193817 := bstep (se 2 (by rfl) ⟨822681, by rfl⟩ : syracuseStep 2193817 = 1645363) B1645363
theorem B1300907 : Blo 1299968 1300907 := bstep (se 1 (by rfl) ⟨975680, by rfl⟩ : syracuseStep 1300907 = 1951361) B1951361
theorem B1300919 : Blo 1299968 1300919 := bstep (se 1 (by rfl) ⟨975689, by rfl⟩ : syracuseStep 1300919 = 1951379) B1951379
theorem B1300939 : Blo 1299968 1300939 := bstep (se 1 (by rfl) ⟨975704, by rfl⟩ : syracuseStep 1300939 = 1951409) B1951409
theorem B1300951 : Blo 1299968 1300951 := bstep (se 1 (by rfl) ⟨975713, by rfl⟩ : syracuseStep 1300951 = 1951427) B1951427
theorem B1300971 : Blo 1299968 1300971 := bstep (se 1 (by rfl) ⟨975728, by rfl⟩ : syracuseStep 1300971 = 1951457) B1951457
theorem B1300983 : Blo 1299968 1300983 := bstep (se 1 (by rfl) ⟨975737, by rfl⟩ : syracuseStep 1300983 = 1951475) B1951475
theorem B11868677 : Blo 1299968 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B1301003 : Blo 1299968 1301003 := bstep (se 1 (by rfl) ⟨975752, by rfl⟩ : syracuseStep 1301003 = 1951505) B1951505
theorem B1301015 : Blo 1299968 1301015 := bstep (se 1 (by rfl) ⟨975761, by rfl⟩ : syracuseStep 1301015 = 1951523) B1951523
theorem B1301035 : Blo 1299968 1301035 := bstep (se 1 (by rfl) ⟨975776, by rfl⟩ : syracuseStep 1301035 = 1951553) B1951553
theorem B1301047 : Blo 1299968 1301047 := bstep (se 1 (by rfl) ⟨975785, by rfl⟩ : syracuseStep 1301047 = 1951571) B1951571
theorem B1301067 : Blo 1299968 1301067 := bstep (se 1 (by rfl) ⟨975800, by rfl⟩ : syracuseStep 1301067 = 1951601) B1951601
theorem B1301079 : Blo 1299968 1301079 := bstep (se 1 (by rfl) ⟨975809, by rfl⟩ : syracuseStep 1301079 = 1951619) B1951619
theorem B1301099 : Blo 1299968 1301099 := bstep (se 1 (by rfl) ⟨975824, by rfl⟩ : syracuseStep 1301099 = 1951649) B1951649
theorem B1301111 : Blo 1299968 1301111 := bstep (se 1 (by rfl) ⟨975833, by rfl⟩ : syracuseStep 1301111 = 1951667) B1951667
theorem B1301131 : Blo 1299968 1301131 := bstep (se 1 (by rfl) ⟨975848, by rfl⟩ : syracuseStep 1301131 = 1951697) B1951697
theorem B3291799 : Blo 1299968 3291799 := bstep (se 1 (by rfl) ⟨2468849, by rfl⟩ : syracuseStep 3291799 = 4937699) B4937699
theorem B1301143 : Blo 1299968 1301143 := bstep (se 1 (by rfl) ⟨975857, by rfl⟩ : syracuseStep 1301143 = 1951715) B1951715
theorem B1301163 : Blo 1299968 1301163 := bstep (se 1 (by rfl) ⟨975872, by rfl⟩ : syracuseStep 1301163 = 1951745) B1951745
theorem B1301175 : Blo 1299968 1301175 := bstep (se 1 (by rfl) ⟨975881, by rfl⟩ : syracuseStep 1301175 = 1951763) B1951763
theorem B1301195 : Blo 1299968 1301195 := bstep (se 1 (by rfl) ⟨975896, by rfl⟩ : syracuseStep 1301195 = 1951793) B1951793
theorem B1669835 : Blo 1299968 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B1301207 : Blo 1299968 1301207 := bstep (se 1 (by rfl) ⟨975905, by rfl⟩ : syracuseStep 1301207 = 1951811) B1951811
theorem B1301227 : Blo 1299968 1301227 := bstep (se 1 (by rfl) ⟨975920, by rfl⟩ : syracuseStep 1301227 = 1951841) B1951841
theorem B1301239 : Blo 1299968 1301239 := bstep (se 1 (by rfl) ⟨975929, by rfl⟩ : syracuseStep 1301239 = 1951859) B1951859
theorem B2636545 : Blo 1299968 2636545 := bstep (se 2 (by rfl) ⟨988704, by rfl⟩ : syracuseStep 2636545 = 1977409) B1977409
theorem B1301259 : Blo 1299968 1301259 := bstep (se 1 (by rfl) ⟨975944, by rfl⟩ : syracuseStep 1301259 = 1951889) B1951889
theorem B1301271 : Blo 1299968 1301271 := bstep (se 1 (by rfl) ⟨975953, by rfl⟩ : syracuseStep 1301271 = 1951907) B1951907
theorem B1301291 : Blo 1299968 1301291 := bstep (se 1 (by rfl) ⟨975968, by rfl⟩ : syracuseStep 1301291 = 1951937) B1951937
theorem B1301303 : Blo 1299968 1301303 := bstep (se 1 (by rfl) ⟨975977, by rfl⟩ : syracuseStep 1301303 = 1951955) B1951955
theorem B7035713 : Blo 1299968 7035713 := bstep (se 2 (by rfl) ⟨2638392, by rfl⟩ : syracuseStep 7035713 = 5276785) B5276785
theorem B3128129 : Blo 1299968 3128129 := bstep (se 2 (by rfl) ⟨1173048, by rfl⟩ : syracuseStep 3128129 = 2346097) B2346097
theorem B1301323 : Blo 1299968 1301323 := bstep (se 1 (by rfl) ⟨975992, by rfl⟩ : syracuseStep 1301323 = 1951985) B1951985
theorem B1301335 : Blo 1299968 1301335 := bstep (se 1 (by rfl) ⟨976001, by rfl⟩ : syracuseStep 1301335 = 1952003) B1952003
theorem B1301355 : Blo 1299968 1301355 := bstep (se 1 (by rfl) ⟨976016, by rfl⟩ : syracuseStep 1301355 = 1952033) B1952033
theorem B1301367 : Blo 1299968 1301367 := bstep (se 1 (by rfl) ⟨976025, by rfl⟩ : syracuseStep 1301367 = 1952051) B1952051
theorem B1301387 : Blo 1299968 1301387 := bstep (se 1 (by rfl) ⟨976040, by rfl⟩ : syracuseStep 1301387 = 1952081) B1952081
theorem B4938641 : Blo 1299968 4938641 := bstep (se 2 (by rfl) ⟨1851990, by rfl⟩ : syracuseStep 4938641 = 3703981) B3703981
theorem B1301399 : Blo 1299968 1301399 := bstep (se 1 (by rfl) ⟨976049, by rfl⟩ : syracuseStep 1301399 = 1952099) B1952099
theorem B1301419 : Blo 1299968 1301419 := bstep (se 1 (by rfl) ⟨976064, by rfl⟩ : syracuseStep 1301419 = 1952129) B1952129
theorem B1301431 : Blo 1299968 1301431 := bstep (se 1 (by rfl) ⟨976073, by rfl⟩ : syracuseStep 1301431 = 1952147) B1952147
theorem B1301451 : Blo 1299968 1301451 := bstep (se 1 (by rfl) ⟨976088, by rfl⟩ : syracuseStep 1301451 = 1952177) B1952177
theorem B2194391 : Blo 1299968 2194391 := bstep (se 1 (by rfl) ⟨1645793, by rfl⟩ : syracuseStep 2194391 = 3291587) B3291587
theorem B1301463 : Blo 1299968 1301463 := bstep (se 1 (by rfl) ⟨976097, by rfl⟩ : syracuseStep 1301463 = 1952195) B1952195
theorem B1563607 : Blo 1299968 1563607 := bstep (se 1 (by rfl) ⟨1172705, by rfl⟩ : syracuseStep 1563607 = 2345411) B2345411
theorem B1301483 : Blo 1299968 1301483 := bstep (se 1 (by rfl) ⟨976112, by rfl⟩ : syracuseStep 1301483 = 1952225) B1952225
theorem B1301495 : Blo 1299968 1301495 := bstep (se 1 (by rfl) ⟨976121, by rfl⟩ : syracuseStep 1301495 = 1952243) B1952243
theorem B1301515 : Blo 1299968 1301515 := bstep (se 1 (by rfl) ⟨976136, by rfl⟩ : syracuseStep 1301515 = 1952273) B1952273
theorem B1645591 : Blo 1299968 1645591 := bstep (se 1 (by rfl) ⟨1234193, by rfl⟩ : syracuseStep 1645591 = 2468387) B2468387
theorem B1301527 : Blo 1299968 1301527 := bstep (se 1 (by rfl) ⟨976145, by rfl⟩ : syracuseStep 1301527 = 1952291) B1952291
theorem B1301547 : Blo 1299968 1301547 := bstep (se 1 (by rfl) ⟨976160, by rfl⟩ : syracuseStep 1301547 = 1952321) B1952321
theorem B1301559 : Blo 1299968 1301559 := bstep (se 1 (by rfl) ⟨976169, by rfl⟩ : syracuseStep 1301559 = 1952339) B1952339
theorem B3292235 : Blo 1299968 3292235 := bstep (se 1 (by rfl) ⟨2469176, by rfl⟩ : syracuseStep 3292235 = 4938353) B4938353
theorem B1301579 : Blo 1299968 1301579 := bstep (se 1 (by rfl) ⟨976184, by rfl⟩ : syracuseStep 1301579 = 1952369) B1952369
theorem B2194519 : Blo 1299968 2194519 := bstep (se 1 (by rfl) ⟨1645889, by rfl⟩ : syracuseStep 2194519 = 3291779) B3291779
theorem B1301591 : Blo 1299968 1301591 := bstep (se 1 (by rfl) ⟨976193, by rfl⟩ : syracuseStep 1301591 = 1952387) B1952387
theorem B1301611 : Blo 1299968 1301611 := bstep (se 1 (by rfl) ⟨976208, by rfl⟩ : syracuseStep 1301611 = 1952417) B1952417
theorem B1301623 : Blo 1299968 1301623 := bstep (se 1 (by rfl) ⟨976217, by rfl⟩ : syracuseStep 1301623 = 1952435) B1952435
theorem B1301643 : Blo 1299968 1301643 := bstep (se 1 (by rfl) ⟨976232, by rfl⟩ : syracuseStep 1301643 = 1952465) B1952465
theorem B1301655 : Blo 1299968 1301655 := bstep (se 1 (by rfl) ⟨976241, by rfl⟩ : syracuseStep 1301655 = 1952483) B1952483
theorem B1301675 : Blo 1299968 1301675 := bstep (se 1 (by rfl) ⟨976256, by rfl⟩ : syracuseStep 1301675 = 1952513) B1952513
theorem B1301687 : Blo 1299968 1301687 := bstep (se 1 (by rfl) ⟨976265, by rfl⟩ : syracuseStep 1301687 = 1952531) B1952531
theorem B3701953 : Blo 1299968 3701953 := bstep (se 2 (by rfl) ⟨1388232, by rfl⟩ : syracuseStep 3701953 = 2776465) B2776465
theorem B4390091 : Blo 1299968 4390091 := bstep (se 1 (by rfl) ⟨3292568, by rfl⟩ : syracuseStep 4390091 = 6585137) B6585137
theorem B1301707 : Blo 1299968 1301707 := bstep (se 1 (by rfl) ⟨976280, by rfl⟩ : syracuseStep 1301707 = 1952561) B1952561
theorem B1301719 : Blo 1299968 1301719 := bstep (se 1 (by rfl) ⟨976289, by rfl⟩ : syracuseStep 1301719 = 1952579) B1952579
theorem B1301739 : Blo 1299968 1301739 := bstep (se 1 (by rfl) ⟨976304, by rfl⟩ : syracuseStep 1301739 = 1952609) B1952609
theorem B1301751 : Blo 1299968 1301751 := bstep (se 1 (by rfl) ⟨976313, by rfl⟩ : syracuseStep 1301751 = 1952627) B1952627
theorem B1301771 : Blo 1299968 1301771 := bstep (se 1 (by rfl) ⟨976328, by rfl⟩ : syracuseStep 1301771 = 1952657) B1952657
theorem B7404817 : Blo 1299968 7404817 := bstep (se 2 (by rfl) ⟨2776806, by rfl⟩ : syracuseStep 7404817 = 5553613) B5553613
theorem B1301783 : Blo 1299968 1301783 := bstep (se 1 (by rfl) ⟨976337, by rfl⟩ : syracuseStep 1301783 = 1952675) B1952675
theorem B1301803 : Blo 1299968 1301803 := bstep (se 1 (by rfl) ⟨976352, by rfl⟩ : syracuseStep 1301803 = 1952705) B1952705
theorem B1301815 : Blo 1299968 1301815 := bstep (se 1 (by rfl) ⟨976361, by rfl⟩ : syracuseStep 1301815 = 1952723) B1952723
theorem B1301835 : Blo 1299968 1301835 := bstep (se 1 (by rfl) ⟨976376, by rfl⟩ : syracuseStep 1301835 = 1952753) B1952753
theorem B1301847 : Blo 1299968 1301847 := bstep (se 1 (by rfl) ⟨976385, by rfl⟩ : syracuseStep 1301847 = 1952771) B1952771
theorem B1301867 : Blo 1299968 1301867 := bstep (se 1 (by rfl) ⟨976400, by rfl⟩ : syracuseStep 1301867 = 1952801) B1952801
theorem B22543733 : Blo 1299968 22543733 := bstep (se 5 (by rfl) ⟨1056737, by rfl⟩ : syracuseStep 22543733 = 2113475) B2113475
theorem B1301879 : Blo 1299968 1301879 := bstep (se 1 (by rfl) ⟨976409, by rfl⟩ : syracuseStep 1301879 = 1952819) B1952819
theorem B1301899 : Blo 1299968 1301899 := bstep (se 1 (by rfl) ⟨976424, by rfl⟩ : syracuseStep 1301899 = 1952849) B1952849
theorem B9379223 : Blo 1299968 9379223 := bstep (se 1 (by rfl) ⟨7034417, by rfl⟩ : syracuseStep 9379223 = 14068835) B14068835
theorem B1301911 : Blo 1299968 1301911 := bstep (se 1 (by rfl) ⟨976433, by rfl⟩ : syracuseStep 1301911 = 1952867) B1952867
theorem B1301931 : Blo 1299968 1301931 := bstep (se 1 (by rfl) ⟨976448, by rfl⟩ : syracuseStep 1301931 = 1952897) B1952897
theorem B1301943 : Blo 1299968 1301943 := bstep (se 1 (by rfl) ⟨976457, by rfl⟩ : syracuseStep 1301943 = 1952915) B1952915
theorem B3292609 : Blo 1299968 3292609 := bstep (se 2 (by rfl) ⟨1234728, by rfl⟩ : syracuseStep 3292609 = 2469457) B2469457
theorem B1301963 : Blo 1299968 1301963 := bstep (se 1 (by rfl) ⟨976472, by rfl⟩ : syracuseStep 1301963 = 1952945) B1952945
theorem B4685273 : Blo 1299968 4685273 := bstep (se 2 (by rfl) ⟨1756977, by rfl⟩ : syracuseStep 4685273 = 3513955) B3513955
theorem B4390361 : Blo 1299968 4390361 := bstep (se 2 (by rfl) ⟨1646385, by rfl⟩ : syracuseStep 4390361 = 3292771) B3292771
theorem B10157633 : Blo 1299968 10157633 := bstep (se 2 (by rfl) ⟨3809112, by rfl⟩ : syracuseStep 10157633 = 7618225) B7618225
theorem B4939339 : Blo 1299968 4939339 := bstep (se 1 (by rfl) ⟨3704504, by rfl⟩ : syracuseStep 4939339 = 7409009) B7409009
theorem B2195147 : Blo 1299968 2195147 := bstep (se 1 (by rfl) ⟨1646360, by rfl⟩ : syracuseStep 2195147 = 3292721) B3292721
theorem B2195275 : Blo 1299968 2195275 := bstep (se 1 (by rfl) ⟨1646456, by rfl⟩ : syracuseStep 2195275 = 3292913) B3292913
theorem B4939613 : Blo 1299968 4939613 := bstep (se 3 (by rfl) ⟨926177, by rfl⟩ : syracuseStep 4939613 = 1852355) B1852355
theorem B2637697 : Blo 1299968 2637697 := bstep (se 2 (by rfl) ⟨989136, by rfl⟩ : syracuseStep 2637697 = 1978273) B1978273
theorem B16670681 : Blo 1299968 16670681 := bstep (se 2 (by rfl) ⟨6251505, by rfl⟩ : syracuseStep 16670681 = 12503011) B12503011
theorem B2195417 : Blo 1299968 2195417 := bstep (se 2 (by rfl) ⟨823281, by rfl⟩ : syracuseStep 2195417 = 1646563) B1646563
theorem B2195471 : Blo 1299968 2195471 := bstep (se 1 (by rfl) ⟨1646603, by rfl⟩ : syracuseStep 2195471 = 3293207) B3293207
theorem B4390955 : Blo 1299968 4390955 := bstep (se 1 (by rfl) ⟨3293216, by rfl⟩ : syracuseStep 4390955 = 6586433) B6586433
theorem B2539579 : Blo 1299968 2539579 := bstep (se 1 (by rfl) ⟨1904684, by rfl⟩ : syracuseStep 2539579 = 3809369) B3809369
theorem B6250583 : Blo 1299968 6250583 := bstep (se 1 (by rfl) ⟨4687937, by rfl⟩ : syracuseStep 6250583 = 9375875) B9375875
theorem B1851535 : Blo 1299968 1851535 := bstep (se 1 (by rfl) ⟨1388651, by rfl⟩ : syracuseStep 1851535 = 2777303) B2777303
theorem B6340781 : Blo 1299968 6340781 := bstep (se 3 (by rfl) ⟨1188896, by rfl⟩ : syracuseStep 6340781 = 2377793) B2377793
theorem B3293369 : Blo 1299968 3293369 := bstep (se 2 (by rfl) ⟨1235013, by rfl⟩ : syracuseStep 3293369 = 2470027) B2470027
theorem B4448513 : Blo 1299968 4448513 := bstep (se 2 (by rfl) ⟨1668192, by rfl⟩ : syracuseStep 4448513 = 3336385) B3336385
theorem B5554433 : Blo 1299968 5554433 := bstep (se 2 (by rfl) ⟨2082912, by rfl⟩ : syracuseStep 5554433 = 4165825) B4165825
theorem B1851655 : Blo 1299968 1851655 := bstep (se 1 (by rfl) ⟨1388741, by rfl⟩ : syracuseStep 1851655 = 2777483) B2777483
theorem B4170017 : Blo 1299968 4170017 := bstep (se 2 (by rfl) ⟨1563756, by rfl⟩ : syracuseStep 4170017 = 3127513) B3127513
theorem B1950011 : Blo 1299968 1950011 := bstep (se 1 (by rfl) ⟨1462508, by rfl⟩ : syracuseStep 1950011 = 2925017) B2925017
theorem B1950071 : Blo 1299968 1950071 := bstep (se 1 (by rfl) ⟨1462553, by rfl⟩ : syracuseStep 1950071 = 2925107) B2925107
theorem B1646983 : Blo 1299968 1646983 := bstep (se 1 (by rfl) ⟨1235237, by rfl⟩ : syracuseStep 1646983 = 2470475) B2470475
theorem B1950095 : Blo 1299968 1950095 := bstep (se 1 (by rfl) ⟨1462571, by rfl⟩ : syracuseStep 1950095 = 2925143) B2925143
theorem B6685073 : Blo 1299968 6685073 := bstep (se 2 (by rfl) ⟨2506902, by rfl⟩ : syracuseStep 6685073 = 5013805) B5013805
theorem B4170131 : Blo 1299968 4170131 := bstep (se 1 (by rfl) ⟨3127598, by rfl⟩ : syracuseStep 4170131 = 6255197) B6255197
theorem B1950137 : Blo 1299968 1950137 := bstep (se 2 (by rfl) ⟨731301, by rfl⟩ : syracuseStep 1950137 = 1462603) B1462603
theorem B1950215 : Blo 1299968 1950215 := bstep (se 1 (by rfl) ⟨1462661, by rfl⟩ : syracuseStep 1950215 = 2925323) B2925323
theorem B2925071 : Blo 1299968 2925071 := bstep (se 1 (by rfl) ⟨2193803, by rfl⟩ : syracuseStep 2925071 = 4387607) B4387607
theorem B2925089 : Blo 1299968 2925089 := bstep (se 2 (by rfl) ⟨1096908, by rfl⟩ : syracuseStep 2925089 = 2193817) B2193817
theorem B1950251 : Blo 1299968 1950251 := bstep (se 1 (by rfl) ⟨1462688, by rfl⟩ : syracuseStep 1950251 = 2925377) B2925377
theorem B2196011 : Blo 1299968 2196011 := bstep (se 1 (by rfl) ⟨1647008, by rfl⟩ : syracuseStep 2196011 = 3294017) B3294017
theorem B1950281 : Blo 1299968 1950281 := bstep (se 2 (by rfl) ⟨731355, by rfl⟩ : syracuseStep 1950281 = 1462711) B1462711
theorem B3703411 : Blo 1299968 3703411 := bstep (se 1 (by rfl) ⟨2777558, by rfl⟩ : syracuseStep 3703411 = 5555117) B5555117
theorem B2343559 : Blo 1299968 2343559 := bstep (se 1 (by rfl) ⟨1757669, by rfl⟩ : syracuseStep 2343559 = 3515339) B3515339
theorem B1950395 : Blo 1299968 1950395 := bstep (se 1 (by rfl) ⟨1462796, by rfl⟩ : syracuseStep 1950395 = 2925593) B2925593
theorem B6587081 : Blo 1299968 6587081 := bstep (se 2 (by rfl) ⟨2470155, by rfl⟩ : syracuseStep 6587081 = 4940311) B4940311
theorem B1950455 : Blo 1299968 1950455 := bstep (se 1 (by rfl) ⟨1462841, by rfl⟩ : syracuseStep 1950455 = 2925683) B2925683
theorem B1950479 : Blo 1299968 1950479 := bstep (se 1 (by rfl) ⟨1462859, by rfl⟩ : syracuseStep 1950479 = 2925719) B2925719
theorem B1950521 : Blo 1299968 1950521 := bstep (se 2 (by rfl) ⟨731445, by rfl⟩ : syracuseStep 1950521 = 1462891) B1462891
theorem B3703639 : Blo 1299968 3703639 := bstep (se 1 (by rfl) ⟨2777729, by rfl⟩ : syracuseStep 3703639 = 5555459) B5555459
theorem B3294067 : Blo 1299968 3294067 := bstep (se 1 (by rfl) ⟨2470550, by rfl⟩ : syracuseStep 3294067 = 4941101) B4941101
theorem B2925431 : Blo 1299968 2925431 := bstep (se 1 (by rfl) ⟨2194073, by rfl⟩ : syracuseStep 2925431 = 4388147) B4388147
theorem B1647479 : Blo 1299968 1647479 := bstep (se 1 (by rfl) ⟨1235609, by rfl⟩ : syracuseStep 1647479 = 2471219) B2471219
theorem B1950599 : Blo 1299968 1950599 := bstep (se 1 (by rfl) ⟨1462949, by rfl⟩ : syracuseStep 1950599 = 2925899) B2925899
theorem B1876879 : Blo 1299968 1876879 := bstep (se 1 (by rfl) ⟨1407659, by rfl⟩ : syracuseStep 1876879 = 2815319) B2815319
theorem B1950635 : Blo 1299968 1950635 := bstep (se 1 (by rfl) ⟨1462976, by rfl⟩ : syracuseStep 1950635 = 2925953) B2925953
theorem B2196409 : Blo 1299968 2196409 := bstep (se 2 (by rfl) ⟨823653, by rfl⟩ : syracuseStep 2196409 = 1647307) B1647307
theorem B1950665 : Blo 1299968 1950665 := bstep (se 2 (by rfl) ⟨731499, by rfl⟩ : syracuseStep 1950665 = 1462999) B1462999
theorem B3515393 : Blo 1299968 3515393 := bstep (se 2 (by rfl) ⟨1318272, by rfl⟩ : syracuseStep 3515393 = 2636545) B2636545
theorem B3294209 : Blo 1299968 3294209 := bstep (se 2 (by rfl) ⟨1235328, by rfl⟩ : syracuseStep 3294209 = 2470657) B2470657
theorem B1647631 : Blo 1299968 1647631 := bstep (se 1 (by rfl) ⟨1235723, by rfl⟩ : syracuseStep 1647631 = 2471447) B2471447
theorem B2925611 : Blo 1299968 2925611 := bstep (se 1 (by rfl) ⟨2194208, by rfl⟩ : syracuseStep 2925611 = 4388417) B4388417
theorem B1950779 : Blo 1299968 1950779 := bstep (se 1 (by rfl) ⟨1463084, by rfl⟩ : syracuseStep 1950779 = 2926169) B2926169
theorem B1950839 : Blo 1299968 1950839 := bstep (se 1 (by rfl) ⟨1463129, by rfl⟩ : syracuseStep 1950839 = 2926259) B2926259
theorem B1950863 : Blo 1299968 1950863 := bstep (se 1 (by rfl) ⟨1463147, by rfl⟩ : syracuseStep 1950863 = 2926295) B2926295
theorem B1950905 : Blo 1299968 1950905 := bstep (se 2 (by rfl) ⟨731589, by rfl⟩ : syracuseStep 1950905 = 1463179) B1463179
theorem B1647803 : Blo 1299968 1647803 := bstep (se 1 (by rfl) ⟨1235852, by rfl⟩ : syracuseStep 1647803 = 2471705) B2471705
theorem B1950983 : Blo 1299968 1950983 := bstep (se 1 (by rfl) ⟨1463237, by rfl⟩ : syracuseStep 1950983 = 2926475) B2926475
theorem B4941071 : Blo 1299968 4941071 := bstep (se 1 (by rfl) ⟨3705803, by rfl⟩ : syracuseStep 4941071 = 7411607) B7411607
theorem B9880865 : Blo 1299968 9880865 := bstep (se 2 (by rfl) ⟨3705324, by rfl⟩ : syracuseStep 9880865 = 7410649) B7410649
theorem B1951019 : Blo 1299968 1951019 := bstep (se 1 (by rfl) ⟨1463264, by rfl⟩ : syracuseStep 1951019 = 2926529) B2926529
theorem B4392251 : Blo 1299968 4392251 := bstep (se 1 (by rfl) ⟨3294188, by rfl⟩ : syracuseStep 4392251 = 6588377) B6588377
theorem B1951049 : Blo 1299968 1951049 := bstep (se 2 (by rfl) ⟨731643, by rfl⟩ : syracuseStep 1951049 = 1463287) B1463287
theorem B2925971 : Blo 1299968 2925971 := bstep (se 1 (by rfl) ⟨2194478, by rfl⟩ : syracuseStep 2925971 = 4388957) B4388957
theorem B1951163 : Blo 1299968 1951163 := bstep (se 1 (by rfl) ⟨1463372, by rfl⟩ : syracuseStep 1951163 = 2926745) B2926745
theorem B2926025 : Blo 1299968 2926025 := bstep (se 2 (by rfl) ⟨1097259, by rfl⟩ : syracuseStep 2926025 = 2194519) B2194519
theorem B3294665 : Blo 1299968 3294665 := bstep (se 2 (by rfl) ⟨1235499, by rfl⟩ : syracuseStep 3294665 = 2470999) B2470999
theorem B1951223 : Blo 1299968 1951223 := bstep (se 1 (by rfl) ⟨1463417, by rfl⟩ : syracuseStep 1951223 = 2926835) B2926835
theorem B1951247 : Blo 1299968 1951247 := bstep (se 1 (by rfl) ⟨1463435, by rfl⟩ : syracuseStep 1951247 = 2926871) B2926871
theorem B1951289 : Blo 1299968 1951289 := bstep (se 2 (by rfl) ⟨731733, by rfl⟩ : syracuseStep 1951289 = 1463467) B1463467
theorem B1951367 : Blo 1299968 1951367 := bstep (se 1 (by rfl) ⟨1463525, by rfl⟩ : syracuseStep 1951367 = 2927051) B2927051
theorem B1951403 : Blo 1299968 1951403 := bstep (se 1 (by rfl) ⟨1463552, by rfl⟩ : syracuseStep 1951403 = 2927105) B2927105
theorem B1853113 : Blo 1299968 1853113 := bstep (se 2 (by rfl) ⟨694917, by rfl⟩ : syracuseStep 1853113 = 1389835) B1389835
theorem B9873089 : Blo 1299968 9873089 := bstep (se 2 (by rfl) ⟨3702408, by rfl⟩ : syracuseStep 9873089 = 7404817) B7404817
theorem B1951433 : Blo 1299968 1951433 := bstep (se 2 (by rfl) ⟨731787, by rfl⟩ : syracuseStep 1951433 = 1463575) B1463575
theorem B4392737 : Blo 1299968 4392737 := bstep (se 2 (by rfl) ⟨1647276, by rfl⟩ : syracuseStep 4392737 = 3294553) B3294553
theorem B3295019 : Blo 1299968 3295019 := bstep (se 1 (by rfl) ⟨2471264, by rfl⟩ : syracuseStep 3295019 = 4942529) B4942529
theorem B1951547 : Blo 1299968 1951547 := bstep (se 1 (by rfl) ⟨1463660, by rfl⟩ : syracuseStep 1951547 = 2927321) B2927321
theorem B1951607 : Blo 1299968 1951607 := bstep (se 1 (by rfl) ⟨1463705, by rfl⟩ : syracuseStep 1951607 = 2927411) B2927411
theorem B1951631 : Blo 1299968 1951631 := bstep (se 1 (by rfl) ⟨1463723, by rfl⟩ : syracuseStep 1951631 = 2927447) B2927447
theorem B1951673 : Blo 1299968 1951673 := bstep (se 2 (by rfl) ⟨731877, by rfl⟩ : syracuseStep 1951673 = 1463755) B1463755
theorem B1951751 : Blo 1299968 1951751 := bstep (se 1 (by rfl) ⟨1463813, by rfl⟩ : syracuseStep 1951751 = 2927627) B2927627
theorem B1951787 : Blo 1299968 1951787 := bstep (se 1 (by rfl) ⟨1463840, by rfl⟩ : syracuseStep 1951787 = 2927681) B2927681
theorem B1951817 : Blo 1299968 1951817 := bstep (se 2 (by rfl) ⟨731931, by rfl⟩ : syracuseStep 1951817 = 1463863) B1463863
theorem B7030871 : Blo 1299968 7030871 := bstep (se 1 (by rfl) ⟨5273153, by rfl⟩ : syracuseStep 7030871 = 10546307) B10546307
theorem B2926727 : Blo 1299968 2926727 := bstep (se 1 (by rfl) ⟨2195045, by rfl⟩ : syracuseStep 2926727 = 4390091) B4390091
theorem B28117165 : Blo 1299968 28117165 := bstep (se 3 (by rfl) ⟨5271968, by rfl⟩ : syracuseStep 28117165 = 10543937) B10543937
theorem B1951931 : Blo 1299968 1951931 := bstep (se 1 (by rfl) ⟨1463948, by rfl⟩ : syracuseStep 1951931 = 2927897) B2927897
theorem B8333549 : Blo 1299968 8333549 := bstep (se 3 (by rfl) ⟨1562540, by rfl⟩ : syracuseStep 8333549 = 3125081) B3125081
theorem B9881837 : Blo 1299968 9881837 := bstep (se 3 (by rfl) ⟨1852844, by rfl⟩ : syracuseStep 9881837 = 3705689) B3705689
theorem B1951991 : Blo 1299968 1951991 := bstep (se 1 (by rfl) ⟨1463993, by rfl⟩ : syracuseStep 1951991 = 2927987) B2927987
theorem B6252815 : Blo 1299968 6252815 := bstep (se 1 (by rfl) ⟨4689611, by rfl⟩ : syracuseStep 6252815 = 9379223) B9379223
theorem B1952015 : Blo 1299968 1952015 := bstep (se 1 (by rfl) ⟨1464011, by rfl⟩ : syracuseStep 1952015 = 2928023) B2928023
theorem B1952057 : Blo 1299968 1952057 := bstep (se 2 (by rfl) ⟨732021, by rfl⟩ : syracuseStep 1952057 = 1464043) B1464043
theorem B3123515 : Blo 1299968 3123515 := bstep (se 1 (by rfl) ⟨2342636, by rfl⟩ : syracuseStep 3123515 = 4685273) B4685273
theorem B2926907 : Blo 1299968 2926907 := bstep (se 1 (by rfl) ⟨2195180, by rfl⟩ : syracuseStep 2926907 = 4390361) B4390361
theorem B4393331 : Blo 1299968 4393331 := bstep (se 1 (by rfl) ⟨3294998, by rfl⟩ : syracuseStep 4393331 = 6589997) B6589997
theorem B7408007 : Blo 1299968 7408007 := bstep (se 1 (by rfl) ⟨5556005, by rfl⟩ : syracuseStep 7408007 = 11112011) B11112011
theorem B3705223 : Blo 1299968 3705223 := bstep (se 1 (by rfl) ⟨2778917, by rfl⟩ : syracuseStep 3705223 = 5557835) B5557835
theorem B1952135 : Blo 1299968 1952135 := bstep (se 1 (by rfl) ⟨1464101, by rfl⟩ : syracuseStep 1952135 = 2928203) B2928203
theorem B5933465 : Blo 1299968 5933465 := bstep (se 2 (by rfl) ⟨2225049, by rfl⟩ : syracuseStep 5933465 = 4450099) B4450099
theorem B1952171 : Blo 1299968 1952171 := bstep (se 1 (by rfl) ⟨1464128, by rfl⟩ : syracuseStep 1952171 = 2928257) B2928257
theorem B2927033 : Blo 1299968 2927033 := bstep (se 2 (by rfl) ⟨1097637, by rfl⟩ : syracuseStep 2927033 = 2195275) B2195275
theorem B1952201 : Blo 1299968 1952201 := bstep (se 2 (by rfl) ⟨732075, by rfl⟩ : syracuseStep 1952201 = 1464151) B1464151
theorem B3516929 : Blo 1299968 3516929 := bstep (se 2 (by rfl) ⟨1318848, by rfl⟩ : syracuseStep 3516929 = 2637697) B2637697
theorem B1952315 : Blo 1299968 1952315 := bstep (se 1 (by rfl) ⟨1464236, by rfl⟩ : syracuseStep 1952315 = 2928473) B2928473
theorem B1952375 : Blo 1299968 1952375 := bstep (se 1 (by rfl) ⟨1464281, by rfl⟩ : syracuseStep 1952375 = 2928563) B2928563
theorem B1952399 : Blo 1299968 1952399 := bstep (se 1 (by rfl) ⟨1464299, by rfl⟩ : syracuseStep 1952399 = 2928599) B2928599
theorem B3705497 : Blo 1299968 3705497 := bstep (se 2 (by rfl) ⟨1389561, by rfl⟩ : syracuseStep 3705497 = 2779123) B2779123
theorem B14068403 : Blo 1299968 14068403 := bstep (se 1 (by rfl) ⟨10551302, by rfl⟩ : syracuseStep 14068403 = 21102605) B21102605
theorem B1952441 : Blo 1299968 1952441 := bstep (se 2 (by rfl) ⟨732165, by rfl⟩ : syracuseStep 1952441 = 1464331) B1464331
theorem B1952519 : Blo 1299968 1952519 := bstep (se 1 (by rfl) ⟨1464389, by rfl⟩ : syracuseStep 1952519 = 2928779) B2928779
theorem B2927375 : Blo 1299968 2927375 := bstep (se 1 (by rfl) ⟨2195531, by rfl⟩ : syracuseStep 2927375 = 4391063) B4391063
theorem B2927393 : Blo 1299968 2927393 := bstep (se 2 (by rfl) ⟨1097772, by rfl⟩ : syracuseStep 2927393 = 2195545) B2195545
theorem B1952555 : Blo 1299968 1952555 := bstep (se 1 (by rfl) ⟨1464416, by rfl⟩ : syracuseStep 1952555 = 2928833) B2928833
theorem B1878841 : Blo 1299968 1878841 := bstep (se 2 (by rfl) ⟨704565, by rfl⟩ : syracuseStep 1878841 = 1409131) B1409131
theorem B1952585 : Blo 1299968 1952585 := bstep (se 2 (by rfl) ⟨732219, by rfl⟩ : syracuseStep 1952585 = 1464439) B1464439
theorem B4942727 : Blo 1299968 4942727 := bstep (se 1 (by rfl) ⟨3707045, by rfl⟩ : syracuseStep 4942727 = 7414091) B7414091
theorem B3517337 : Blo 1299968 3517337 := bstep (se 2 (by rfl) ⟨1319001, by rfl⟩ : syracuseStep 3517337 = 2638003) B2638003
theorem B1952699 : Blo 1299968 1952699 := bstep (se 1 (by rfl) ⟨1464524, by rfl⟩ : syracuseStep 1952699 = 2929049) B2929049
theorem B1952759 : Blo 1299968 1952759 := bstep (se 1 (by rfl) ⟨1464569, by rfl⟩ : syracuseStep 1952759 = 2929139) B2929139
theorem B42224651 : Blo 1299968 42224651 := bstep (se 1 (by rfl) ⟨31668488, by rfl⟩ : syracuseStep 42224651 = 63336977) B63336977
theorem B1952783 : Blo 1299968 1952783 := bstep (se 1 (by rfl) ⟨1464587, by rfl⟩ : syracuseStep 1952783 = 2929175) B2929175
theorem B1952825 : Blo 1299968 1952825 := bstep (se 2 (by rfl) ⟨732309, by rfl⟩ : syracuseStep 1952825 = 1464619) B1464619
theorem B1805431 : Blo 1299968 1805431 := bstep (se 1 (by rfl) ⟨1354073, by rfl⟩ : syracuseStep 1805431 = 2708147) B2708147
theorem B2927735 : Blo 1299968 2927735 := bstep (se 1 (by rfl) ⟨2195801, by rfl⟩ : syracuseStep 2927735 = 4391603) B4391603
theorem B1952903 : Blo 1299968 1952903 := bstep (se 1 (by rfl) ⟨1464677, by rfl⟩ : syracuseStep 1952903 = 2929355) B2929355
theorem B1952939 : Blo 1299968 1952939 := bstep (se 1 (by rfl) ⟨1464704, by rfl⟩ : syracuseStep 1952939 = 2929409) B2929409
theorem B14265517 : Blo 1299968 14265517 := bstep (se 3 (by rfl) ⟨2674784, by rfl⟩ : syracuseStep 14265517 = 5349569) B5349569
theorem B3706145 : Blo 1299968 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B3124523 : Blo 1299968 3124523 := bstep (se 1 (by rfl) ⟨2343392, by rfl⟩ : syracuseStep 3124523 = 4686785) B4686785
theorem B2927915 : Blo 1299968 2927915 := bstep (se 1 (by rfl) ⟨2195936, by rfl⟩ : syracuseStep 2927915 = 4391873) B4391873
theorem B20016569 : Blo 1299968 20016569 := bstep (se 2 (by rfl) ⟨7506213, by rfl⟩ : syracuseStep 20016569 = 15012427) B15012427
theorem B2469305 : Blo 1299968 2469305 := bstep (se 2 (by rfl) ⟨925989, by rfl⟩ : syracuseStep 2469305 = 1851979) B1851979
theorem B14069177 : Blo 1299968 14069177 := bstep (se 2 (by rfl) ⟨5275941, by rfl⟩ : syracuseStep 14069177 = 10551883) B10551883
theorem B2928275 : Blo 1299968 2928275 := bstep (se 1 (by rfl) ⟨2196206, by rfl⟩ : syracuseStep 2928275 = 4392413) B4392413
theorem B2928329 : Blo 1299968 2928329 := bstep (se 2 (by rfl) ⟨1098123, by rfl⟩ : syracuseStep 2928329 = 2196247) B2196247
theorem B15642341 : Blo 1299968 15642341 := bstep (se 4 (by rfl) ⟨1466469, by rfl⟩ : syracuseStep 15642341 = 2932939) B2932939
theorem B3337985 : Blo 1299968 3337985 := bstep (se 2 (by rfl) ⟨1251744, by rfl⟩ : syracuseStep 3337985 = 2503489) B2503489
theorem B14823485 : Blo 1299968 14823485 := bstep (se 3 (by rfl) ⟨2779403, by rfl⟩ : syracuseStep 14823485 = 5558807) B5558807
theorem B9883781 : Blo 1299968 9883781 := bstep (se 4 (by rfl) ⟨926604, by rfl⟩ : syracuseStep 9883781 = 1853209) B1853209
theorem B11866313 : Blo 1299968 11866313 := bstep (se 2 (by rfl) ⟨4449867, by rfl⟩ : syracuseStep 11866313 = 8899735) B8899735
theorem B4935937 : Blo 1299968 4935937 := bstep (se 2 (by rfl) ⟨1850976, by rfl⟩ : syracuseStep 4935937 = 3701953) B3701953
theorem B3707147 : Blo 1299968 3707147 := bstep (se 1 (by rfl) ⟨2780360, by rfl⟩ : syracuseStep 3707147 = 5560721) B5560721
theorem B8335649 : Blo 1299968 8335649 := bstep (se 2 (by rfl) ⟨3125868, by rfl⟩ : syracuseStep 8335649 = 6251737) B6251737
theorem B2929031 : Blo 1299968 2929031 := bstep (se 1 (by rfl) ⟨2196773, by rfl⟩ : syracuseStep 2929031 = 4393547) B4393547
theorem B14062045 : Blo 1299968 14062045 := bstep (se 3 (by rfl) ⟨2636633, by rfl⟩ : syracuseStep 14062045 = 5273267) B5273267
theorem B4452893 : Blo 1299968 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B4690475 : Blo 1299968 4690475 := bstep (se 1 (by rfl) ⟨3517856, by rfl⟩ : syracuseStep 4690475 = 7035713) B7035713
theorem B2085419 : Blo 1299968 2085419 := bstep (se 1 (by rfl) ⟨1564064, by rfl⟩ : syracuseStep 2085419 = 3128129) B3128129
theorem B2929211 : Blo 1299968 2929211 := bstep (se 1 (by rfl) ⟨2196908, by rfl⟩ : syracuseStep 2929211 = 4393817) B4393817
theorem B11113037 : Blo 1299968 11113037 := bstep (se 3 (by rfl) ⟨2083694, by rfl⟩ : syracuseStep 11113037 = 4167389) B4167389
theorem B2224775 : Blo 1299968 2224775 := bstep (se 1 (by rfl) ⟨1668581, by rfl⟩ : syracuseStep 2224775 = 3337163) B3337163
theorem B1462927 : Blo 1299968 1462927 := bstep (se 1 (by rfl) ⟨1097195, by rfl⟩ : syracuseStep 1462927 = 2194391) B2194391
theorem B2929337 : Blo 1299968 2929337 := bstep (se 2 (by rfl) ⟨1098501, by rfl⟩ : syracuseStep 2929337 = 2197003) B2197003
theorem B6583193 : Blo 1299968 6583193 := bstep (se 2 (by rfl) ⟨2468697, by rfl⟩ : syracuseStep 6583193 = 4937395) B4937395
theorem B15029155 : Blo 1299968 15029155 := bstep (se 1 (by rfl) ⟨11271866, by rfl⟩ : syracuseStep 15029155 = 22543733) B22543733
theorem B4387769 : Blo 1299968 4387769 := bstep (se 2 (by rfl) ⟨1645413, by rfl⟩ : syracuseStep 4387769 = 3290827) B3290827
theorem B9876491 : Blo 1299968 9876491 := bstep (se 1 (by rfl) ⟨7407368, by rfl⟩ : syracuseStep 9876491 = 14814737) B14814737
theorem B6771755 : Blo 1299968 6771755 := bstep (se 1 (by rfl) ⟨5078816, by rfl⟩ : syracuseStep 6771755 = 10157633) B10157633
theorem B4011095 : Blo 1299968 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B3339379 : Blo 1299968 3339379 := bstep (se 1 (by rfl) ⟨2504534, by rfl⟩ : syracuseStep 3339379 = 5009069) B5009069
theorem B1463431 : Blo 1299968 1463431 := bstep (se 1 (by rfl) ⟨1097573, by rfl⟩ : syracuseStep 1463431 = 2195147) B2195147
theorem B21091565 : Blo 1299968 21091565 := bstep (se 3 (by rfl) ⟨3954668, by rfl⟩ : syracuseStep 21091565 = 7909337) B7909337
theorem B11113787 : Blo 1299968 11113787 := bstep (se 1 (by rfl) ⟨8335340, by rfl⟩ : syracuseStep 11113787 = 16670681) B16670681
theorem B1463611 : Blo 1299968 1463611 := bstep (se 1 (by rfl) ⟨1097708, by rfl⟩ : syracuseStep 1463611 = 2195417) B2195417
theorem B2471303 : Blo 1299968 2471303 := bstep (se 1 (by rfl) ⟨1853477, by rfl⟩ : syracuseStep 2471303 = 3706955) B3706955
theorem B41178545 : Blo 1299968 41178545 := bstep (se 2 (by rfl) ⟨15441954, by rfl⟩ : syracuseStep 41178545 = 30883909) B30883909
theorem B1299975 : Blo 1299968 1299975 := bstep (se 1 (by rfl) ⟨974981, by rfl⟩ : syracuseStep 1299975 = 1949963) B1949963
theorem B4388363 : Blo 1299968 4388363 := bstep (se 1 (by rfl) ⟨3291272, by rfl⟩ : syracuseStep 4388363 = 6582545) B6582545
theorem B1299983 : Blo 1299968 1299983 := bstep (se 1 (by rfl) ⟨974987, by rfl⟩ : syracuseStep 1299983 = 1949975) B1949975
theorem B10008107 : Blo 1299968 10008107 := bstep (se 1 (by rfl) ⟨7506080, by rfl⟩ : syracuseStep 10008107 = 15012161) B15012161
theorem B1300027 : Blo 1299968 1300027 := bstep (se 1 (by rfl) ⟨975020, by rfl⟩ : syracuseStep 1300027 = 1950041) B1950041
theorem B4388471 : Blo 1299968 4388471 := bstep (se 1 (by rfl) ⟨3291353, by rfl⟩ : syracuseStep 4388471 = 6582707) B6582707
theorem B1300103 : Blo 1299968 1300103 := bstep (se 1 (by rfl) ⟨975077, by rfl⟩ : syracuseStep 1300103 = 1950155) B1950155
theorem B1300111 : Blo 1299968 1300111 := bstep (se 1 (by rfl) ⟨975083, by rfl⟩ : syracuseStep 1300111 = 1950167) B1950167
theorem B3290777 : Blo 1299968 3290777 := bstep (se 2 (by rfl) ⟨1234041, by rfl⟩ : syracuseStep 3290777 = 2468083) B2468083
theorem B1300155 : Blo 1299968 1300155 := bstep (se 1 (by rfl) ⟨975116, by rfl⟩ : syracuseStep 1300155 = 1950233) B1950233
theorem B15013633 : Blo 1299968 15013633 := bstep (se 2 (by rfl) ⟨5630112, by rfl⟩ : syracuseStep 15013633 = 11260225) B11260225
theorem B23729921 : Blo 1299968 23729921 := bstep (se 2 (by rfl) ⟨8898720, by rfl⟩ : syracuseStep 23729921 = 17797441) B17797441
theorem B1300231 : Blo 1299968 1300231 := bstep (se 1 (by rfl) ⟨975173, by rfl⟩ : syracuseStep 1300231 = 1950347) B1950347
theorem B1300239 : Blo 1299968 1300239 := bstep (se 1 (by rfl) ⟨975179, by rfl⟩ : syracuseStep 1300239 = 1950359) B1950359
theorem B1464079 : Blo 1299968 1464079 := bstep (se 1 (by rfl) ⟨1098059, by rfl⟩ : syracuseStep 1464079 = 2196119) B2196119
theorem B3290939 : Blo 1299968 3290939 := bstep (se 1 (by rfl) ⟨2468204, by rfl⟩ : syracuseStep 3290939 = 4936409) B4936409
theorem B1300283 : Blo 1299968 1300283 := bstep (se 1 (by rfl) ⟨975212, by rfl⟩ : syracuseStep 1300283 = 1950425) B1950425
theorem B3127099 : Blo 1299968 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B1300359 : Blo 1299968 1300359 := bstep (se 1 (by rfl) ⟨975269, by rfl⟩ : syracuseStep 1300359 = 1950539) B1950539
theorem B1300367 : Blo 1299968 1300367 := bstep (se 1 (by rfl) ⟨975275, by rfl⟩ : syracuseStep 1300367 = 1950551) B1950551
theorem B1300411 : Blo 1299968 1300411 := bstep (se 1 (by rfl) ⟨975308, by rfl⟩ : syracuseStep 1300411 = 1950617) B1950617
theorem B6862795 : Blo 1299968 6862795 := bstep (se 1 (by rfl) ⟨5147096, by rfl⟩ : syracuseStep 6862795 = 10294193) B10294193
theorem B1300487 : Blo 1299968 1300487 := bstep (se 1 (by rfl) ⟨975365, by rfl⟩ : syracuseStep 1300487 = 1950731) B1950731
theorem B3291151 : Blo 1299968 3291151 := bstep (se 1 (by rfl) ⟨2468363, by rfl⟩ : syracuseStep 3291151 = 4936727) B4936727
theorem B1300495 : Blo 1299968 1300495 := bstep (se 1 (by rfl) ⟨975371, by rfl⟩ : syracuseStep 1300495 = 1950743) B1950743
theorem B1300539 : Blo 1299968 1300539 := bstep (se 1 (by rfl) ⟨975404, by rfl⟩ : syracuseStep 1300539 = 1950809) B1950809
theorem B1300615 : Blo 1299968 1300615 := bstep (se 1 (by rfl) ⟨975461, by rfl⟩ : syracuseStep 1300615 = 1950923) B1950923
theorem B1300623 : Blo 1299968 1300623 := bstep (se 1 (by rfl) ⟨975467, by rfl⟩ : syracuseStep 1300623 = 1950935) B1950935
theorem B1300667 : Blo 1299968 1300667 := bstep (se 1 (by rfl) ⟨975500, by rfl⟩ : syracuseStep 1300667 = 1951001) B1951001
theorem B4389065 : Blo 1299968 4389065 := bstep (se 2 (by rfl) ⟨1645899, by rfl⟩ : syracuseStep 4389065 = 3291799) B3291799
theorem B4692205 : Blo 1299968 4692205 := bstep (se 3 (by rfl) ⟨879788, by rfl⟩ : syracuseStep 4692205 = 1759577) B1759577
theorem B1300743 : Blo 1299968 1300743 := bstep (se 1 (by rfl) ⟨975557, by rfl⟩ : syracuseStep 1300743 = 1951115) B1951115
theorem B1464583 : Blo 1299968 1464583 := bstep (se 1 (by rfl) ⟨1098437, by rfl⟩ : syracuseStep 1464583 = 2196875) B2196875
theorem B1300751 : Blo 1299968 1300751 := bstep (se 1 (by rfl) ⟨975563, by rfl⟩ : syracuseStep 1300751 = 1951127) B1951127
theorem B3291425 : Blo 1299968 3291425 := bstep (se 2 (by rfl) ⟨1234284, by rfl⟩ : syracuseStep 3291425 = 2468569) B2468569
theorem B1300795 : Blo 1299968 1300795 := bstep (se 1 (by rfl) ⟨975596, by rfl⟩ : syracuseStep 1300795 = 1951193) B1951193
theorem B13343069 : Blo 1299968 13343069 := bstep (se 3 (by rfl) ⟨2501825, by rfl⟩ : syracuseStep 13343069 = 5003651) B5003651
theorem B1300871 : Blo 1299968 1300871 := bstep (se 1 (by rfl) ⟨975653, by rfl⟩ : syracuseStep 1300871 = 1951307) B1951307
theorem B1300879 : Blo 1299968 1300879 := bstep (se 1 (by rfl) ⟨975659, by rfl⟩ : syracuseStep 1300879 = 1951319) B1951319
theorem B1300923 : Blo 1299968 1300923 := bstep (se 1 (by rfl) ⟨975692, by rfl⟩ : syracuseStep 1300923 = 1951385) B1951385
theorem B9886211 : Blo 1299968 9886211 := bstep (se 1 (by rfl) ⟨7414658, by rfl⟩ : syracuseStep 9886211 = 14829317) B14829317
theorem B1300999 : Blo 1299968 1300999 := bstep (se 1 (by rfl) ⟨975749, by rfl⟩ : syracuseStep 1300999 = 1951499) B1951499
theorem B1301007 : Blo 1299968 1301007 := bstep (se 1 (by rfl) ⟨975755, by rfl⟩ : syracuseStep 1301007 = 1951511) B1951511
theorem B4168235 : Blo 1299968 4168235 := bstep (se 1 (by rfl) ⟨3126176, by rfl⟩ : syracuseStep 4168235 = 6252353) B6252353
theorem B2193979 : Blo 1299968 2193979 := bstep (se 1 (by rfl) ⟨1645484, by rfl⟩ : syracuseStep 2193979 = 3290969) B3290969
theorem B1301051 : Blo 1299968 1301051 := bstep (se 1 (by rfl) ⟨975788, by rfl⟩ : syracuseStep 1301051 = 1951577) B1951577
theorem B1301127 : Blo 1299968 1301127 := bstep (se 1 (by rfl) ⟨975845, by rfl⟩ : syracuseStep 1301127 = 1951691) B1951691
theorem B1301135 : Blo 1299968 1301135 := bstep (se 1 (by rfl) ⟨975851, by rfl⟩ : syracuseStep 1301135 = 1951703) B1951703
theorem B1301179 : Blo 1299968 1301179 := bstep (se 1 (by rfl) ⟨975884, by rfl⟩ : syracuseStep 1301179 = 1951769) B1951769
theorem B2194121 : Blo 1299968 2194121 := bstep (se 2 (by rfl) ⟨822795, by rfl⟩ : syracuseStep 2194121 = 1645591) B1645591
theorem B1301255 : Blo 1299968 1301255 := bstep (se 1 (by rfl) ⟨975941, by rfl⟩ : syracuseStep 1301255 = 1951883) B1951883
theorem B1301263 : Blo 1299968 1301263 := bstep (se 1 (by rfl) ⟨975947, by rfl⟩ : syracuseStep 1301263 = 1951895) B1951895
theorem B1301307 : Blo 1299968 1301307 := bstep (se 1 (by rfl) ⟨975980, by rfl⟩ : syracuseStep 1301307 = 1951961) B1951961
theorem B4389767 : Blo 1299968 4389767 := bstep (se 1 (by rfl) ⟨3292325, by rfl⟩ : syracuseStep 4389767 = 6584651) B6584651
theorem B1301383 : Blo 1299968 1301383 := bstep (se 1 (by rfl) ⟨976037, by rfl⟩ : syracuseStep 1301383 = 1952075) B1952075
theorem B1301391 : Blo 1299968 1301391 := bstep (se 1 (by rfl) ⟨976043, by rfl⟩ : syracuseStep 1301391 = 1952087) B1952087
theorem B3562393 : Blo 1299968 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B7412633 : Blo 1299968 7412633 := bstep (se 2 (by rfl) ⟨2779737, by rfl⟩ : syracuseStep 7412633 = 5559475) B5559475
theorem B9878435 : Blo 1299968 9878435 := bstep (se 1 (by rfl) ⟨7408826, by rfl⟩ : syracuseStep 9878435 = 14817653) B14817653
theorem B11115427 : Blo 1299968 11115427 := bstep (se 1 (by rfl) ⟨8336570, by rfl⟩ : syracuseStep 11115427 = 16673141) B16673141
theorem B1301435 : Blo 1299968 1301435 := bstep (se 1 (by rfl) ⟨976076, by rfl⟩ : syracuseStep 1301435 = 1952153) B1952153
theorem B7912451 : Blo 1299968 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B1301511 : Blo 1299968 1301511 := bstep (se 1 (by rfl) ⟨976133, by rfl⟩ : syracuseStep 1301511 = 1952267) B1952267
theorem B1301519 : Blo 1299968 1301519 := bstep (se 1 (by rfl) ⟨976139, by rfl⟩ : syracuseStep 1301519 = 1952279) B1952279
theorem B1301563 : Blo 1299968 1301563 := bstep (se 1 (by rfl) ⟨976172, by rfl⟩ : syracuseStep 1301563 = 1952345) B1952345
theorem B4938839 : Blo 1299968 4938839 := bstep (se 1 (by rfl) ⟨3704129, by rfl⟩ : syracuseStep 4938839 = 7408259) B7408259
theorem B1645687 : Blo 1299968 1645687 := bstep (se 1 (by rfl) ⟨1234265, by rfl⟩ : syracuseStep 1645687 = 2468531) B2468531
theorem B18758789 : Blo 1299968 18758789 := bstep (se 4 (by rfl) ⟨1758636, by rfl⟩ : syracuseStep 18758789 = 3517273) B3517273
theorem B1301639 : Blo 1299968 1301639 := bstep (se 1 (by rfl) ⟨976229, by rfl⟩ : syracuseStep 1301639 = 1952459) B1952459
theorem B1301647 : Blo 1299968 1301647 := bstep (se 1 (by rfl) ⟨976235, by rfl⟩ : syracuseStep 1301647 = 1952471) B1952471
theorem B1301691 : Blo 1299968 1301691 := bstep (se 1 (by rfl) ⟨976268, by rfl⟩ : syracuseStep 1301691 = 1952537) B1952537
theorem B4390145 : Blo 1299968 4390145 := bstep (se 2 (by rfl) ⟨1646304, by rfl⟩ : syracuseStep 4390145 = 3292609) B3292609
theorem B1301767 : Blo 1299968 1301767 := bstep (se 1 (by rfl) ⟨976325, by rfl⟩ : syracuseStep 1301767 = 1952651) B1952651
theorem B3292427 : Blo 1299968 3292427 := bstep (se 1 (by rfl) ⟨2469320, by rfl⟩ : syracuseStep 3292427 = 4938641) B4938641
theorem B1301775 : Blo 1299968 1301775 := bstep (se 1 (by rfl) ⟨976331, by rfl⟩ : syracuseStep 1301775 = 1952663) B1952663
theorem B1301819 : Blo 1299968 1301819 := bstep (se 1 (by rfl) ⟨976364, by rfl⟩ : syracuseStep 1301819 = 1952729) B1952729
theorem B2194823 : Blo 1299968 2194823 := bstep (se 1 (by rfl) ⟨1646117, by rfl⟩ : syracuseStep 2194823 = 3292235) B3292235
theorem B1301895 : Blo 1299968 1301895 := bstep (se 1 (by rfl) ⟨976421, by rfl⟩ : syracuseStep 1301895 = 1952843) B1952843
theorem B1301903 : Blo 1299968 1301903 := bstep (se 1 (by rfl) ⟨976427, by rfl⟩ : syracuseStep 1301903 = 1952855) B1952855
theorem B6585785 : Blo 1299968 6585785 := bstep (se 2 (by rfl) ⟨2469669, by rfl⟩ : syracuseStep 6585785 = 4939339) B4939339
theorem B1646011 : Blo 1299968 1646011 := bstep (se 1 (by rfl) ⟨1234508, by rfl⟩ : syracuseStep 1646011 = 2469017) B2469017
theorem B1301947 : Blo 1299968 1301947 := bstep (se 1 (by rfl) ⟨976460, by rfl⟩ : syracuseStep 1301947 = 1952921) B1952921
theorem B5275165 : Blo 1299968 5275165 := bstep (se 3 (by rfl) ⟨989093, by rfl⟩ : syracuseStep 5275165 = 1978187) B1978187
theorem B2776619 : Blo 1299968 2776619 := bstep (se 1 (by rfl) ⟨2082464, by rfl⟩ : syracuseStep 2776619 = 4164929) B4164929
theorem B4939325 : Blo 1299968 4939325 := bstep (se 3 (by rfl) ⟨926123, by rfl⟩ : syracuseStep 4939325 = 1852247) B1852247
theorem B8339237 : Blo 1299968 8339237 := bstep (se 4 (by rfl) ⟨781803, by rfl⟩ : syracuseStep 8339237 = 1563607) B1563607
theorem B28139309 : Blo 1299968 28139309 := bstep (se 3 (by rfl) ⟨5276120, by rfl⟩ : syracuseStep 28139309 = 10552241) B10552241
theorem B6250355 : Blo 1299968 6250355 := bstep (se 1 (by rfl) ⟨4687766, by rfl⟩ : syracuseStep 6250355 = 9375533) B9375533
theorem B3293075 : Blo 1299968 3293075 := bstep (se 1 (by rfl) ⟨2469806, by rfl⟩ : syracuseStep 3293075 = 4939613) B4939613
theorem B1646507 : Blo 1299968 1646507 := bstep (se 1 (by rfl) ⟨1234880, by rfl⟩ : syracuseStep 1646507 = 2469761) B2469761
theorem B4227187 : Blo 1299968 4227187 := bstep (se 1 (by rfl) ⟨3170390, by rfl⟩ : syracuseStep 4227187 = 6340781) B6340781
theorem B2195579 : Blo 1299968 2195579 := bstep (se 1 (by rfl) ⟨1646684, by rfl⟩ : syracuseStep 2195579 = 3293369) B3293369
theorem B2965675 : Blo 1299968 2965675 := bstep (se 1 (by rfl) ⟨2224256, by rfl⟩ : syracuseStep 2965675 = 4448513) B4448513
theorem B4456715 : Blo 1299968 4456715 := bstep (se 1 (by rfl) ⟨3342536, by rfl⟩ : syracuseStep 4456715 = 6685073) B6685073
theorem B1950047 : Blo 1299968 1950047 := bstep (se 1 (by rfl) ⟨1462535, by rfl⟩ : syracuseStep 1950047 = 2925071) B2925071
theorem B1950059 : Blo 1299968 1950059 := bstep (se 1 (by rfl) ⟨1462544, by rfl⟩ : syracuseStep 1950059 = 2925089) B2925089
theorem B4391387 : Blo 1299968 4391387 := bstep (se 1 (by rfl) ⟨3293540, by rfl⟩ : syracuseStep 4391387 = 6587081) B6587081
theorem B4940297 : Blo 1299968 4940297 := bstep (se 2 (by rfl) ⟨1852611, by rfl⟩ : syracuseStep 4940297 = 3705223) B3705223
theorem B2195977 : Blo 1299968 2195977 := bstep (se 2 (by rfl) ⟨823491, by rfl⟩ : syracuseStep 2195977 = 1646983) B1646983
theorem B1950287 : Blo 1299968 1950287 := bstep (se 1 (by rfl) ⟨1462715, by rfl⟩ : syracuseStep 1950287 = 2925431) B2925431
theorem B17810021 : Blo 1299968 17810021 := bstep (se 4 (by rfl) ⟨1669689, by rfl⟩ : syracuseStep 17810021 = 3339379) B3339379
theorem B2925179 : Blo 1299968 2925179 := bstep (se 1 (by rfl) ⟨2193884, by rfl⟩ : syracuseStep 2925179 = 4387769) B4387769
theorem B2343595 : Blo 1299968 2343595 := bstep (se 1 (by rfl) ⟨1757696, by rfl⟩ : syracuseStep 2343595 = 3515393) B3515393
theorem B14811821 : Blo 1299968 14811821 := bstep (se 3 (by rfl) ⟨2777216, by rfl⟩ : syracuseStep 14811821 = 5554433) B5554433
theorem B2196139 : Blo 1299968 2196139 := bstep (se 1 (by rfl) ⟨1647104, by rfl⟩ : syracuseStep 2196139 = 3294209) B3294209
theorem B1950407 : Blo 1299968 1950407 := bstep (se 1 (by rfl) ⟨1462805, by rfl⟩ : syracuseStep 1950407 = 2925611) B2925611
theorem B4514503 : Blo 1299968 4514503 := bstep (se 1 (by rfl) ⟨3385877, by rfl⟩ : syracuseStep 4514503 = 6771755) B6771755
theorem B2925305 : Blo 1299968 2925305 := bstep (se 2 (by rfl) ⟨1096989, by rfl⟩ : syracuseStep 2925305 = 2193979) B2193979
theorem B3294047 : Blo 1299968 3294047 := bstep (se 1 (by rfl) ⟨2470535, by rfl⟩ : syracuseStep 3294047 = 4941071) B4941071
theorem B1950569 : Blo 1299968 1950569 := bstep (se 2 (by rfl) ⟨731463, by rfl⟩ : syracuseStep 1950569 = 1462927) B1462927
theorem B6587243 : Blo 1299968 6587243 := bstep (se 1 (by rfl) ⟨4940432, by rfl⟩ : syracuseStep 6587243 = 9880865) B9880865
theorem B1647535 : Blo 1299968 1647535 := bstep (se 1 (by rfl) ⟨1235651, by rfl⟩ : syracuseStep 1647535 = 2471303) B2471303
theorem B1950647 : Blo 1299968 1950647 := bstep (se 1 (by rfl) ⟨1462985, by rfl⟩ : syracuseStep 1950647 = 2925971) B2925971
theorem B27452363 : Blo 1299968 27452363 := bstep (se 1 (by rfl) ⟨20589272, by rfl⟩ : syracuseStep 27452363 = 41178545) B41178545
theorem B1950683 : Blo 1299968 1950683 := bstep (se 1 (by rfl) ⟨1463012, by rfl⟩ : syracuseStep 1950683 = 2926025) B2926025
theorem B2196443 : Blo 1299968 2196443 := bstep (se 1 (by rfl) ⟨1647332, by rfl⟩ : syracuseStep 2196443 = 3294665) B3294665
theorem B2925575 : Blo 1299968 2925575 := bstep (se 1 (by rfl) ⟨2194181, by rfl⟩ : syracuseStep 2925575 = 4388363) B4388363
theorem B2925647 : Blo 1299968 2925647 := bstep (se 1 (by rfl) ⟨2194235, by rfl⟩ : syracuseStep 2925647 = 4388471) B4388471
theorem B4392089 : Blo 1299968 4392089 := bstep (se 2 (by rfl) ⟨1647033, by rfl⟩ : syracuseStep 4392089 = 3294067) B3294067
theorem B15819947 : Blo 1299968 15819947 := bstep (se 1 (by rfl) ⟨11864960, by rfl⟩ : syracuseStep 15819947 = 23729921) B23729921
theorem B2196679 : Blo 1299968 2196679 := bstep (se 1 (by rfl) ⟨1647509, by rfl⟩ : syracuseStep 2196679 = 3295019) B3295019
theorem B14820569 : Blo 1299968 14820569 := bstep (se 2 (by rfl) ⟨5557713, by rfl⟩ : syracuseStep 14820569 = 11115427) B11115427
theorem B20038873 : Blo 1299968 20038873 := bstep (se 2 (by rfl) ⟨7514577, by rfl⟩ : syracuseStep 20038873 = 15029155) B15029155
theorem B2196841 : Blo 1299968 2196841 := bstep (se 2 (by rfl) ⟨823815, by rfl⟩ : syracuseStep 2196841 = 1647631) B1647631
theorem B4687247 : Blo 1299968 4687247 := bstep (se 1 (by rfl) ⟨3515435, by rfl⟩ : syracuseStep 4687247 = 7030871) B7030871
theorem B1951151 : Blo 1299968 1951151 := bstep (se 1 (by rfl) ⟨1463363, by rfl⟩ : syracuseStep 1951151 = 2926727) B2926727
theorem B2926043 : Blo 1299968 2926043 := bstep (se 1 (by rfl) ⟨2194532, by rfl⟩ : syracuseStep 2926043 = 4389065) B4389065
theorem B5555699 : Blo 1299968 5555699 := bstep (se 1 (by rfl) ⟨4166774, by rfl⟩ : syracuseStep 5555699 = 8333549) B8333549
theorem B6587891 : Blo 1299968 6587891 := bstep (se 1 (by rfl) ⟨4940918, by rfl⟩ : syracuseStep 6587891 = 9881837) B9881837
theorem B1951241 : Blo 1299968 1951241 := bstep (se 2 (by rfl) ⟨731715, by rfl⟩ : syracuseStep 1951241 = 1463431) B1463431
theorem B2082343 : Blo 1299968 2082343 := bstep (se 1 (by rfl) ⟨1561757, by rfl⟩ : syracuseStep 2082343 = 3123515) B3123515
theorem B1951271 : Blo 1299968 1951271 := bstep (se 1 (by rfl) ⟨1463453, by rfl⟩ : syracuseStep 1951271 = 2926907) B2926907
theorem B1951355 : Blo 1299968 1951355 := bstep (se 1 (by rfl) ⟨1463516, by rfl⟩ : syracuseStep 1951355 = 2927033) B2927033
theorem B10020485 : Blo 1299968 10020485 := bstep (se 4 (by rfl) ⟨939420, by rfl⟩ : syracuseStep 10020485 = 1878841) B1878841
theorem B2344619 : Blo 1299968 2344619 := bstep (se 1 (by rfl) ⟨1758464, by rfl⟩ : syracuseStep 2344619 = 3516929) B3516929
theorem B5932733 : Blo 1299968 5932733 := bstep (se 3 (by rfl) ⟨1112387, by rfl⟩ : syracuseStep 5932733 = 2224775) B2224775
theorem B2778823 : Blo 1299968 2778823 := bstep (se 1 (by rfl) ⟨2084117, by rfl⟩ : syracuseStep 2778823 = 4168235) B4168235
theorem B1951481 : Blo 1299968 1951481 := bstep (se 2 (by rfl) ⟨731805, by rfl⟩ : syracuseStep 1951481 = 1463611) B1463611
theorem B1951583 : Blo 1299968 1951583 := bstep (se 1 (by rfl) ⟨1463687, by rfl⟩ : syracuseStep 1951583 = 2927375) B2927375
theorem B1951595 : Blo 1299968 1951595 := bstep (se 1 (by rfl) ⟨1463696, by rfl⟩ : syracuseStep 1951595 = 2927393) B2927393
theorem B2926511 : Blo 1299968 2926511 := bstep (se 1 (by rfl) ⟨2194883, by rfl⟩ : syracuseStep 2926511 = 4389767) B4389767
theorem B3295151 : Blo 1299968 3295151 := bstep (se 1 (by rfl) ⟨2471363, by rfl⟩ : syracuseStep 3295151 = 4942727) B4942727
theorem B4941755 : Blo 1299968 4941755 := bstep (se 1 (by rfl) ⟨3706316, by rfl⟩ : syracuseStep 4941755 = 7412633) B7412633
theorem B28149767 : Blo 1299968 28149767 := bstep (se 1 (by rfl) ⟨21112325, by rfl⟩ : syracuseStep 28149767 = 42224651) B42224651
theorem B1951823 : Blo 1299968 1951823 := bstep (se 1 (by rfl) ⟨1463867, by rfl⟩ : syracuseStep 1951823 = 2927735) B2927735
theorem B2926763 : Blo 1299968 2926763 := bstep (se 1 (by rfl) ⟨2195072, by rfl⟩ : syracuseStep 2926763 = 4390145) B4390145
theorem B2083015 : Blo 1299968 2083015 := bstep (se 1 (by rfl) ⟨1562261, by rfl⟩ : syracuseStep 2083015 = 3124523) B3124523
theorem B1951943 : Blo 1299968 1951943 := bstep (se 1 (by rfl) ⟨1463957, by rfl⟩ : syracuseStep 1951943 = 2927915) B2927915
theorem B4393277 : Blo 1299968 4393277 := bstep (se 3 (by rfl) ⟨823739, by rfl⟩ : syracuseStep 4393277 = 1647479) B1647479
theorem B1952105 : Blo 1299968 1952105 := bstep (se 2 (by rfl) ⟨732039, by rfl⟩ : syracuseStep 1952105 = 1464079) B1464079
theorem B1952183 : Blo 1299968 1952183 := bstep (se 1 (by rfl) ⟨1464137, by rfl⟩ : syracuseStep 1952183 = 2928275) B2928275
theorem B1952219 : Blo 1299968 1952219 := bstep (se 1 (by rfl) ⟨1464164, by rfl⟩ : syracuseStep 1952219 = 2928329) B2928329
theorem B2927303 : Blo 1299968 2927303 := bstep (se 1 (by rfl) ⟨2195477, by rfl⟩ : syracuseStep 2927303 = 4390955) B4390955
theorem B9882323 : Blo 1299968 9882323 := bstep (se 1 (by rfl) ⟨7411742, by rfl⟩ : syracuseStep 9882323 = 14823485) B14823485
theorem B3386105 : Blo 1299968 3386105 := bstep (se 2 (by rfl) ⟨1269789, by rfl⟩ : syracuseStep 3386105 = 2539579) B2539579
theorem B6589187 : Blo 1299968 6589187 := bstep (se 1 (by rfl) ⟨4941890, by rfl⟩ : syracuseStep 6589187 = 9883781) B9883781
theorem B2468713 : Blo 1299968 2468713 := bstep (se 2 (by rfl) ⟨925767, by rfl⟩ : syracuseStep 2468713 = 1851535) B1851535
theorem B5557099 : Blo 1299968 5557099 := bstep (se 1 (by rfl) ⟨4167824, by rfl⟩ : syracuseStep 5557099 = 8335649) B8335649
theorem B2780011 : Blo 1299968 2780011 := bstep (se 1 (by rfl) ⟨2085008, by rfl⟩ : syracuseStep 2780011 = 4170017) B4170017
theorem B37489553 : Blo 1299968 37489553 := bstep (se 2 (by rfl) ⟨14058582, by rfl⟩ : syracuseStep 37489553 = 28117165) B28117165
theorem B1952687 : Blo 1299968 1952687 := bstep (se 1 (by rfl) ⟨1464515, by rfl⟩ : syracuseStep 1952687 = 2929031) B2929031
theorem B2780087 : Blo 1299968 2780087 := bstep (se 1 (by rfl) ⟨2085065, by rfl⟩ : syracuseStep 2780087 = 4170131) B4170131
theorem B6581249 : Blo 1299968 6581249 := bstep (se 2 (by rfl) ⟨2467968, by rfl⟩ : syracuseStep 6581249 = 4935937) B4935937
theorem B2468873 : Blo 1299968 2468873 := bstep (se 2 (by rfl) ⟨925827, by rfl⟩ : syracuseStep 2468873 = 1851655) B1851655
theorem B1952777 : Blo 1299968 1952777 := bstep (se 2 (by rfl) ⟨732291, by rfl⟩ : syracuseStep 1952777 = 1464583) B1464583
theorem B2968595 : Blo 1299968 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B1952807 : Blo 1299968 1952807 := bstep (se 1 (by rfl) ⟨1464605, by rfl⟩ : syracuseStep 1952807 = 2929211) B2929211
theorem B7408691 : Blo 1299968 7408691 := bstep (se 1 (by rfl) ⟨5556518, by rfl⟩ : syracuseStep 7408691 = 11113037) B11113037
theorem B1952891 : Blo 1299968 1952891 := bstep (se 1 (by rfl) ⟨1464668, by rfl⟩ : syracuseStep 1952891 = 2929337) B2929337
theorem B4394141 : Blo 1299968 4394141 := bstep (se 3 (by rfl) ⟨823901, by rfl⟩ : syracuseStep 4394141 = 1647803) B1647803
theorem B2674063 : Blo 1299968 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B14061043 : Blo 1299968 14061043 := bstep (se 1 (by rfl) ⟨10545782, by rfl⟩ : syracuseStep 14061043 = 21091565) B21091565
theorem B3124745 : Blo 1299968 3124745 := bstep (se 2 (by rfl) ⟨1171779, by rfl⟩ : syracuseStep 3124745 = 2343559) B2343559
theorem B7409191 : Blo 1299968 7409191 := bstep (se 1 (by rfl) ⟨5556893, by rfl⟩ : syracuseStep 7409191 = 11113787) B11113787
theorem B2928167 : Blo 1299968 2928167 := bstep (se 1 (by rfl) ⟨2196125, by rfl⟩ : syracuseStep 2928167 = 4392251) B4392251
theorem B6672071 : Blo 1299968 6672071 := bstep (se 1 (by rfl) ⟨5004053, by rfl⟩ : syracuseStep 6672071 = 10008107) B10008107
theorem B6582059 : Blo 1299968 6582059 := bstep (se 1 (by rfl) ⟨4936544, by rfl⟩ : syracuseStep 6582059 = 9873089) B9873089
theorem B2502505 : Blo 1299968 2502505 := bstep (se 2 (by rfl) ⟨938439, by rfl⟩ : syracuseStep 2502505 = 1876879) B1876879
theorem B2928491 : Blo 1299968 2928491 := bstep (se 1 (by rfl) ⟨2196368, by rfl⟩ : syracuseStep 2928491 = 4392737) B4392737
theorem B2928545 : Blo 1299968 2928545 := bstep (se 2 (by rfl) ⟨1098204, by rfl⟩ : syracuseStep 2928545 = 2196409) B2196409
theorem B2928887 : Blo 1299968 2928887 := bstep (se 1 (by rfl) ⟨2196665, by rfl⟩ : syracuseStep 2928887 = 4393331) B4393331
theorem B6590807 : Blo 1299968 6590807 := bstep (se 1 (by rfl) ⟨4943105, by rfl⟩ : syracuseStep 6590807 = 9886211) B9886211
theorem B2470331 : Blo 1299968 2470331 := bstep (se 1 (by rfl) ⟨1852748, by rfl⟩ : syracuseStep 2470331 = 3705497) B3705497
theorem B1462747 : Blo 1299968 1462747 := bstep (se 1 (by rfl) ⟨1097060, by rfl⟩ : syracuseStep 1462747 = 2194121) B2194121
theorem B7033553 : Blo 1299968 7033553 := bstep (se 2 (by rfl) ⟨2637582, by rfl⟩ : syracuseStep 7033553 = 5275165) B5275165
theorem B12505859 : Blo 1299968 12505859 := bstep (se 1 (by rfl) ⟨9379394, by rfl⟩ : syracuseStep 12505859 = 18758789) B18758789
theorem B2470763 : Blo 1299968 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B2470817 : Blo 1299968 2470817 := bstep (se 2 (by rfl) ⟨926556, by rfl⟩ : syracuseStep 2470817 = 1853113) B1853113
theorem B1463215 : Blo 1299968 1463215 := bstep (se 1 (by rfl) ⟨1097411, by rfl⟩ : syracuseStep 1463215 = 2194823) B2194823
theorem B20018177 : Blo 1299968 20018177 := bstep (se 2 (by rfl) ⟨7506816, by rfl⟩ : syracuseStep 20018177 = 15013633) B15013633
theorem B2225323 : Blo 1299968 2225323 := bstep (se 1 (by rfl) ⟨1668992, by rfl⟩ : syracuseStep 2225323 = 3337985) B3337985
theorem B5559491 : Blo 1299968 5559491 := bstep (se 1 (by rfl) ⟨4169618, by rfl⟩ : syracuseStep 5559491 = 8339237) B8339237
theorem B4166903 : Blo 1299968 4166903 := bstep (se 1 (by rfl) ⟨3125177, by rfl⟩ : syracuseStep 4166903 = 6250355) B6250355
theorem B21099869 : Blo 1299968 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B1463647 : Blo 1299968 1463647 := bstep (se 1 (by rfl) ⟨1097735, by rfl⟩ : syracuseStep 1463647 = 2195471) B2195471
theorem B4388201 : Blo 1299968 4388201 := bstep (se 2 (by rfl) ⟨1645575, by rfl⟩ : syracuseStep 4388201 = 3291151) B3291151
theorem B4167055 : Blo 1299968 4167055 := bstep (se 1 (by rfl) ⟨3125291, by rfl⟩ : syracuseStep 4167055 = 6250583) B6250583
theorem B7910875 : Blo 1299968 7910875 := bstep (se 1 (by rfl) ⟨5933156, by rfl⟩ : syracuseStep 7910875 = 11866313) B11866313
theorem B1300007 : Blo 1299968 1300007 := bstep (se 1 (by rfl) ⟨975005, by rfl⟩ : syracuseStep 1300007 = 1950011) B1950011
theorem B1300047 : Blo 1299968 1300047 := bstep (se 1 (by rfl) ⟨975035, by rfl⟩ : syracuseStep 1300047 = 1950071) B1950071
theorem B1300063 : Blo 1299968 1300063 := bstep (se 1 (by rfl) ⟨975047, by rfl⟩ : syracuseStep 1300063 = 1950095) B1950095
theorem B1300091 : Blo 1299968 1300091 := bstep (se 1 (by rfl) ⟨975068, by rfl⟩ : syracuseStep 1300091 = 1950137) B1950137
theorem B6256273 : Blo 1299968 6256273 := bstep (se 2 (by rfl) ⟨2346102, by rfl⟩ : syracuseStep 6256273 = 4692205) B4692205
theorem B1300143 : Blo 1299968 1300143 := bstep (se 1 (by rfl) ⟨975107, by rfl⟩ : syracuseStep 1300143 = 1950215) B1950215
theorem B1300167 : Blo 1299968 1300167 := bstep (se 1 (by rfl) ⟨975125, by rfl⟩ : syracuseStep 1300167 = 1950251) B1950251
theorem B1464007 : Blo 1299968 1464007 := bstep (se 1 (by rfl) ⟨1098005, by rfl⟩ : syracuseStep 1464007 = 2196011) B2196011
theorem B3126983 : Blo 1299968 3126983 := bstep (se 1 (by rfl) ⟨2345237, by rfl⟩ : syracuseStep 3126983 = 4690475) B4690475
theorem B1390279 : Blo 1299968 1390279 := bstep (se 1 (by rfl) ⟨1042709, by rfl⟩ : syracuseStep 1390279 = 2085419) B2085419
theorem B1300187 : Blo 1299968 1300187 := bstep (se 1 (by rfl) ⟨975140, by rfl⟩ : syracuseStep 1300187 = 1950281) B1950281
theorem B1300263 : Blo 1299968 1300263 := bstep (se 1 (by rfl) ⟨975197, by rfl⟩ : syracuseStep 1300263 = 1950395) B1950395
theorem B1300303 : Blo 1299968 1300303 := bstep (se 1 (by rfl) ⟨975227, by rfl⟩ : syracuseStep 1300303 = 1950455) B1950455
theorem B1300319 : Blo 1299968 1300319 := bstep (se 1 (by rfl) ⟨975239, by rfl⟩ : syracuseStep 1300319 = 1950479) B1950479
theorem B1300347 : Blo 1299968 1300347 := bstep (se 1 (by rfl) ⟨975260, by rfl⟩ : syracuseStep 1300347 = 1950521) B1950521
theorem B1300399 : Blo 1299968 1300399 := bstep (se 1 (by rfl) ⟨975299, by rfl⟩ : syracuseStep 1300399 = 1950599) B1950599
theorem B4388795 : Blo 1299968 4388795 := bstep (se 1 (by rfl) ⟨3291596, by rfl⟩ : syracuseStep 4388795 = 6583193) B6583193
theorem B1300423 : Blo 1299968 1300423 := bstep (se 1 (by rfl) ⟨975317, by rfl⟩ : syracuseStep 1300423 = 1950635) B1950635
theorem B18749393 : Blo 1299968 18749393 := bstep (se 2 (by rfl) ⟨7031022, by rfl⟩ : syracuseStep 18749393 = 14062045) B14062045
theorem B1300443 : Blo 1299968 1300443 := bstep (se 1 (by rfl) ⟨975332, by rfl⟩ : syracuseStep 1300443 = 1950665) B1950665
theorem B6584327 : Blo 1299968 6584327 := bstep (se 1 (by rfl) ⟨4938245, by rfl⟩ : syracuseStep 6584327 = 9876491) B9876491
theorem B9885725 : Blo 1299968 9885725 := bstep (se 3 (by rfl) ⟨1853573, by rfl⟩ : syracuseStep 9885725 = 3707147) B3707147
theorem B1300519 : Blo 1299968 1300519 := bstep (se 1 (by rfl) ⟨975389, by rfl⟩ : syracuseStep 1300519 = 1950779) B1950779
theorem B1300559 : Blo 1299968 1300559 := bstep (se 1 (by rfl) ⟨975419, by rfl⟩ : syracuseStep 1300559 = 1950839) B1950839
theorem B1300575 : Blo 1299968 1300575 := bstep (se 1 (by rfl) ⟨975431, by rfl⟩ : syracuseStep 1300575 = 1950863) B1950863
theorem B1300603 : Blo 1299968 1300603 := bstep (se 1 (by rfl) ⟨975452, by rfl⟩ : syracuseStep 1300603 = 1950905) B1950905
theorem B4937881 : Blo 1299968 4937881 := bstep (se 2 (by rfl) ⟨1851705, by rfl⟩ : syracuseStep 4937881 = 3703411) B3703411
theorem B1300655 : Blo 1299968 1300655 := bstep (se 1 (by rfl) ⟨975491, by rfl⟩ : syracuseStep 1300655 = 1950983) B1950983
theorem B1300679 : Blo 1299968 1300679 := bstep (se 1 (by rfl) ⟨975509, by rfl⟩ : syracuseStep 1300679 = 1951019) B1951019
theorem B1300699 : Blo 1299968 1300699 := bstep (se 1 (by rfl) ⟨975524, by rfl⟩ : syracuseStep 1300699 = 1951049) B1951049
theorem B1300775 : Blo 1299968 1300775 := bstep (se 1 (by rfl) ⟨975581, by rfl⟩ : syracuseStep 1300775 = 1951163) B1951163
theorem B1300815 : Blo 1299968 1300815 := bstep (se 1 (by rfl) ⟨975611, by rfl⟩ : syracuseStep 1300815 = 1951223) B1951223
theorem B1300831 : Blo 1299968 1300831 := bstep (se 1 (by rfl) ⟨975623, by rfl⟩ : syracuseStep 1300831 = 1951247) B1951247
theorem B1300859 : Blo 1299968 1300859 := bstep (se 1 (by rfl) ⟨975644, by rfl⟩ : syracuseStep 1300859 = 1951289) B1951289
theorem B1300911 : Blo 1299968 1300911 := bstep (se 1 (by rfl) ⟨975683, by rfl⟩ : syracuseStep 1300911 = 1951367) B1951367
theorem B2193851 : Blo 1299968 2193851 := bstep (se 1 (by rfl) ⟨1645388, by rfl⟩ : syracuseStep 2193851 = 3290777) B3290777
theorem B1300935 : Blo 1299968 1300935 := bstep (se 1 (by rfl) ⟨975701, by rfl⟩ : syracuseStep 1300935 = 1951403) B1951403
theorem B4938185 : Blo 1299968 4938185 := bstep (se 2 (by rfl) ⟨1851819, by rfl⟩ : syracuseStep 4938185 = 3703639) B3703639
theorem B1300955 : Blo 1299968 1300955 := bstep (se 1 (by rfl) ⟨975716, by rfl⟩ : syracuseStep 1300955 = 1951433) B1951433
theorem B53377517 : Blo 1299968 53377517 := bstep (se 3 (by rfl) ⟨10008284, by rfl⟩ : syracuseStep 53377517 = 20016569) B20016569
theorem B6584813 : Blo 1299968 6584813 := bstep (se 3 (by rfl) ⟨1234652, by rfl⟩ : syracuseStep 6584813 = 2469305) B2469305
theorem B4749857 : Blo 1299968 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B2193959 : Blo 1299968 2193959 := bstep (se 1 (by rfl) ⟨1645469, by rfl⟩ : syracuseStep 2193959 = 3290939) B3290939
theorem B1301031 : Blo 1299968 1301031 := bstep (se 1 (by rfl) ⟨975773, by rfl⟩ : syracuseStep 1301031 = 1951547) B1951547
theorem B1301071 : Blo 1299968 1301071 := bstep (se 1 (by rfl) ⟨975803, by rfl⟩ : syracuseStep 1301071 = 1951607) B1951607
theorem B1301087 : Blo 1299968 1301087 := bstep (se 1 (by rfl) ⟨975815, by rfl⟩ : syracuseStep 1301087 = 1951631) B1951631
theorem B1301115 : Blo 1299968 1301115 := bstep (se 1 (by rfl) ⟨975836, by rfl⟩ : syracuseStep 1301115 = 1951673) B1951673
theorem B1301167 : Blo 1299968 1301167 := bstep (se 1 (by rfl) ⟨975875, by rfl⟩ : syracuseStep 1301167 = 1951751) B1951751
theorem B1301191 : Blo 1299968 1301191 := bstep (se 1 (by rfl) ⟨975893, by rfl⟩ : syracuseStep 1301191 = 1951787) B1951787
theorem B1301211 : Blo 1299968 1301211 := bstep (se 1 (by rfl) ⟨975908, by rfl⟩ : syracuseStep 1301211 = 1951817) B1951817
theorem B7404317 : Blo 1299968 7404317 := bstep (se 3 (by rfl) ⟨1388309, by rfl⟩ : syracuseStep 7404317 = 2776619) B2776619
theorem B1301287 : Blo 1299968 1301287 := bstep (se 1 (by rfl) ⟨975965, by rfl⟩ : syracuseStep 1301287 = 1951931) B1951931
theorem B2407241 : Blo 1299968 2407241 := bstep (se 2 (by rfl) ⟨902715, by rfl⟩ : syracuseStep 2407241 = 1805431) B1805431
theorem B2194249 : Blo 1299968 2194249 := bstep (se 2 (by rfl) ⟨822843, by rfl⟩ : syracuseStep 2194249 = 1645687) B1645687
theorem B1301327 : Blo 1299968 1301327 := bstep (se 1 (by rfl) ⟨975995, by rfl⟩ : syracuseStep 1301327 = 1951991) B1951991
theorem B4168543 : Blo 1299968 4168543 := bstep (se 1 (by rfl) ⟨3126407, by rfl⟩ : syracuseStep 4168543 = 6252815) B6252815
theorem B1301343 : Blo 1299968 1301343 := bstep (se 1 (by rfl) ⟨976007, by rfl⟩ : syracuseStep 1301343 = 1952015) B1952015
theorem B2194283 : Blo 1299968 2194283 := bstep (se 1 (by rfl) ⟨1645712, by rfl⟩ : syracuseStep 2194283 = 3291425) B3291425
theorem B1301371 : Blo 1299968 1301371 := bstep (se 1 (by rfl) ⟨976028, by rfl⟩ : syracuseStep 1301371 = 1952057) B1952057
theorem B19020689 : Blo 1299968 19020689 := bstep (se 2 (by rfl) ⟨7132758, by rfl⟩ : syracuseStep 19020689 = 14265517) B14265517
theorem B8895379 : Blo 1299968 8895379 := bstep (se 1 (by rfl) ⟨6671534, by rfl⟩ : syracuseStep 8895379 = 13343069) B13343069
theorem B4938671 : Blo 1299968 4938671 := bstep (se 1 (by rfl) ⟨3704003, by rfl⟩ : syracuseStep 4938671 = 7408007) B7408007
theorem B1301423 : Blo 1299968 1301423 := bstep (se 1 (by rfl) ⟨976067, by rfl⟩ : syracuseStep 1301423 = 1952135) B1952135
theorem B3955643 : Blo 1299968 3955643 := bstep (se 1 (by rfl) ⟨2966732, by rfl⟩ : syracuseStep 3955643 = 5933465) B5933465
theorem B1301447 : Blo 1299968 1301447 := bstep (se 1 (by rfl) ⟨976085, by rfl⟩ : syracuseStep 1301447 = 1952171) B1952171
theorem B1301467 : Blo 1299968 1301467 := bstep (se 1 (by rfl) ⟨976100, by rfl⟩ : syracuseStep 1301467 = 1952201) B1952201
theorem B1301543 : Blo 1299968 1301543 := bstep (se 1 (by rfl) ⟨976157, by rfl⟩ : syracuseStep 1301543 = 1952315) B1952315
theorem B1301583 : Blo 1299968 1301583 := bstep (se 1 (by rfl) ⟨976187, by rfl⟩ : syracuseStep 1301583 = 1952375) B1952375
theorem B1301599 : Blo 1299968 1301599 := bstep (se 1 (by rfl) ⟨976199, by rfl⟩ : syracuseStep 1301599 = 1952399) B1952399
theorem B9378935 : Blo 1299968 9378935 := bstep (se 1 (by rfl) ⟨7034201, by rfl⟩ : syracuseStep 9378935 = 14068403) B14068403
theorem B1301627 : Blo 1299968 1301627 := bstep (se 1 (by rfl) ⟨976220, by rfl⟩ : syracuseStep 1301627 = 1952441) B1952441
theorem B1301679 : Blo 1299968 1301679 := bstep (se 1 (by rfl) ⟨976259, by rfl⟩ : syracuseStep 1301679 = 1952519) B1952519
theorem B1301703 : Blo 1299968 1301703 := bstep (se 1 (by rfl) ⟨976277, by rfl⟩ : syracuseStep 1301703 = 1952555) B1952555
theorem B1301723 : Blo 1299968 1301723 := bstep (se 1 (by rfl) ⟨976292, by rfl⟩ : syracuseStep 1301723 = 1952585) B1952585
theorem B2194681 : Blo 1299968 2194681 := bstep (se 2 (by rfl) ⟨823005, by rfl⟩ : syracuseStep 2194681 = 1646011) B1646011
theorem B6585623 : Blo 1299968 6585623 := bstep (se 1 (by rfl) ⟨4939217, by rfl⟩ : syracuseStep 6585623 = 9878435) B9878435
theorem B1301799 : Blo 1299968 1301799 := bstep (se 1 (by rfl) ⟨976349, by rfl⟩ : syracuseStep 1301799 = 1952699) B1952699
theorem B1301839 : Blo 1299968 1301839 := bstep (se 1 (by rfl) ⟨976379, by rfl⟩ : syracuseStep 1301839 = 1952759) B1952759
theorem B1301855 : Blo 1299968 1301855 := bstep (se 1 (by rfl) ⟨976391, by rfl⟩ : syracuseStep 1301855 = 1952783) B1952783
theorem B1301883 : Blo 1299968 1301883 := bstep (se 1 (by rfl) ⟨976412, by rfl⟩ : syracuseStep 1301883 = 1952825) B1952825
theorem B3292559 : Blo 1299968 3292559 := bstep (se 1 (by rfl) ⟨2469419, by rfl⟩ : syracuseStep 3292559 = 4938839) B4938839
theorem B1301935 : Blo 1299968 1301935 := bstep (se 1 (by rfl) ⟨976451, by rfl⟩ : syracuseStep 1301935 = 1952903) B1952903
theorem B1301959 : Blo 1299968 1301959 := bstep (se 1 (by rfl) ⟨976469, by rfl⟩ : syracuseStep 1301959 = 1952939) B1952939
theorem B2194951 : Blo 1299968 2194951 := bstep (se 1 (by rfl) ⟨1646213, by rfl⟩ : syracuseStep 2194951 = 3292427) B3292427
theorem B4390523 : Blo 1299968 4390523 := bstep (se 1 (by rfl) ⟨3292892, by rfl⟩ : syracuseStep 4390523 = 6585785) B6585785
theorem B9379451 : Blo 1299968 9379451 := bstep (se 1 (by rfl) ⟨7034588, by rfl⟩ : syracuseStep 9379451 = 14069177) B14069177
theorem B3292883 : Blo 1299968 3292883 := bstep (se 1 (by rfl) ⟨2469662, by rfl⟩ : syracuseStep 3292883 = 4939325) B4939325
theorem B36601573 : Blo 1299968 36601573 := bstep (se 4 (by rfl) ⟨3431397, by rfl⟩ : syracuseStep 36601573 = 6862795) B6862795
theorem B9379565 : Blo 1299968 9379565 := bstep (se 3 (by rfl) ⟨1758668, by rfl⟩ : syracuseStep 9379565 = 3517337) B3517337
theorem B4169465 : Blo 1299968 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B4390685 : Blo 1299968 4390685 := bstep (se 3 (by rfl) ⟨823253, by rfl⟩ : syracuseStep 4390685 = 1646507) B1646507
theorem B10428227 : Blo 1299968 10428227 := bstep (se 1 (by rfl) ⟨7821170, by rfl⟩ : syracuseStep 10428227 = 15642341) B15642341
theorem B18759539 : Blo 1299968 18759539 := bstep (se 1 (by rfl) ⟨14069654, by rfl⟩ : syracuseStep 18759539 = 28139309) B28139309
theorem B2195383 : Blo 1299968 2195383 := bstep (se 1 (by rfl) ⟨1646537, by rfl⟩ : syracuseStep 2195383 = 3293075) B3293075
theorem B5636249 : Blo 1299968 5636249 := bstep (se 2 (by rfl) ⟨2113593, by rfl⟩ : syracuseStep 5636249 = 4227187) B4227187
theorem B1646887 : Blo 1299968 1646887 := bstep (se 1 (by rfl) ⟨1235165, by rfl⟩ : syracuseStep 1646887 = 2470331) B2470331
theorem B3293531 : Blo 1299968 3293531 := bstep (se 1 (by rfl) ⟨2470148, by rfl⟩ : syracuseStep 3293531 = 4940297) B4940297
theorem B1950119 : Blo 1299968 1950119 := bstep (se 1 (by rfl) ⟨1462589, by rfl⟩ : syracuseStep 1950119 = 2925179) B2925179
theorem B1950203 : Blo 1299968 1950203 := bstep (se 1 (by rfl) ⟨1462652, by rfl⟩ : syracuseStep 1950203 = 2925305) B2925305
theorem B2196031 : Blo 1299968 2196031 := bstep (se 1 (by rfl) ⟨1647023, by rfl⟩ : syracuseStep 2196031 = 3294047) B3294047
theorem B4391495 : Blo 1299968 4391495 := bstep (se 1 (by rfl) ⟨3293621, by rfl⟩ : syracuseStep 4391495 = 6587243) B6587243
theorem B1647211 : Blo 1299968 1647211 := bstep (se 1 (by rfl) ⟨1235408, by rfl⟩ : syracuseStep 1647211 = 2470817) B2470817
theorem B1950329 : Blo 1299968 1950329 := bstep (se 2 (by rfl) ⟨731373, by rfl⟩ : syracuseStep 1950329 = 1462747) B1462747
theorem B13345451 : Blo 1299968 13345451 := bstep (se 1 (by rfl) ⟨10009088, by rfl⟩ : syracuseStep 13345451 = 20018177) B20018177
theorem B1950383 : Blo 1299968 1950383 := bstep (se 1 (by rfl) ⟨1462787, by rfl⟩ : syracuseStep 1950383 = 2925575) B2925575
theorem B1950431 : Blo 1299968 1950431 := bstep (se 1 (by rfl) ⟨1462823, by rfl⟩ : syracuseStep 1950431 = 2925647) B2925647
theorem B9880379 : Blo 1299968 9880379 := bstep (se 1 (by rfl) ⟨7410284, by rfl⟩ : syracuseStep 9880379 = 14820569) B14820569
theorem B2777935 : Blo 1299968 2777935 := bstep (se 1 (by rfl) ⟨2083451, by rfl⟩ : syracuseStep 2777935 = 4166903) B4166903
theorem B14066579 : Blo 1299968 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B2925467 : Blo 1299968 2925467 := bstep (se 1 (by rfl) ⟨2194100, by rfl⟩ : syracuseStep 2925467 = 4388201) B4388201
theorem B1950695 : Blo 1299968 1950695 := bstep (se 1 (by rfl) ⟨1463021, by rfl⟩ : syracuseStep 1950695 = 2926043) B2926043
theorem B3703799 : Blo 1299968 3703799 := bstep (se 1 (by rfl) ⟨2777849, by rfl⟩ : syracuseStep 3703799 = 5555699) B5555699
theorem B4391927 : Blo 1299968 4391927 := bstep (se 1 (by rfl) ⟨3293945, by rfl⟩ : syracuseStep 4391927 = 6587891) B6587891
theorem B11109413 : Blo 1299968 11109413 := bstep (se 4 (by rfl) ⟨1041507, by rfl⟩ : syracuseStep 11109413 = 2083015) B2083015
theorem B2925665 : Blo 1299968 2925665 := bstep (se 2 (by rfl) ⟨1097124, by rfl⟩ : syracuseStep 2925665 = 2194249) B2194249
theorem B1950953 : Blo 1299968 1950953 := bstep (se 2 (by rfl) ⟨731607, by rfl⟩ : syracuseStep 1950953 = 1463215) B1463215
theorem B2196713 : Blo 1299968 2196713 := bstep (se 2 (by rfl) ⟨823767, by rfl⟩ : syracuseStep 2196713 = 1647535) B1647535
theorem B1951007 : Blo 1299968 1951007 := bstep (se 1 (by rfl) ⟨1463255, by rfl⟩ : syracuseStep 1951007 = 2926511) B2926511
theorem B2196767 : Blo 1299968 2196767 := bstep (se 1 (by rfl) ⟨1647575, by rfl⟩ : syracuseStep 2196767 = 3295151) B3295151
theorem B2925863 : Blo 1299968 2925863 := bstep (se 1 (by rfl) ⟨2194397, by rfl⟩ : syracuseStep 2925863 = 4388795) B4388795
theorem B3294503 : Blo 1299968 3294503 := bstep (se 1 (by rfl) ⟨2470877, by rfl⟩ : syracuseStep 3294503 = 4941755) B4941755
theorem B1951175 : Blo 1299968 1951175 := bstep (se 1 (by rfl) ⟨1463381, by rfl⟩ : syracuseStep 1951175 = 2926763) B2926763
theorem B2926241 : Blo 1299968 2926241 := bstep (se 2 (by rfl) ⟨1097340, by rfl⟩ : syracuseStep 2926241 = 2194681) B2194681
theorem B1951529 : Blo 1299968 1951529 := bstep (se 2 (by rfl) ⟨731823, by rfl⟩ : syracuseStep 1951529 = 1463647) B1463647
theorem B1951535 : Blo 1299968 1951535 := bstep (se 1 (by rfl) ⟨1463651, by rfl⟩ : syracuseStep 1951535 = 2927303) B2927303
theorem B6588215 : Blo 1299968 6588215 := bstep (se 1 (by rfl) ⟨4941161, by rfl⟩ : syracuseStep 6588215 = 9882323) B9882323
theorem B4392791 : Blo 1299968 4392791 := bstep (se 1 (by rfl) ⟨3294593, by rfl⟩ : syracuseStep 4392791 = 6589187) B6589187
theorem B3565417 : Blo 1299968 3565417 := bstep (se 2 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 3565417 = 2674063) B2674063
theorem B13346693 : Blo 1299968 13346693 := bstep (se 4 (by rfl) ⟨1251252, by rfl⟩ : syracuseStep 13346693 = 2502505) B2502505
theorem B2926601 : Blo 1299968 2926601 := bstep (se 2 (by rfl) ⟨1097475, by rfl⟩ : syracuseStep 2926601 = 2194951) B2194951
theorem B6252623 : Blo 1299968 6252623 := bstep (se 1 (by rfl) ⟨4689467, by rfl⟩ : syracuseStep 6252623 = 9378935) B9378935
theorem B8341697 : Blo 1299968 8341697 := bstep (se 2 (by rfl) ⟨3128136, by rfl⟩ : syracuseStep 8341697 = 6256273) B6256273
theorem B3705097 : Blo 1299968 3705097 := bstep (se 2 (by rfl) ⟨1389411, by rfl⟩ : syracuseStep 3705097 = 2778823) B2778823
theorem B1952009 : Blo 1299968 1952009 := bstep (se 2 (by rfl) ⟨732003, by rfl⟩ : syracuseStep 1952009 = 1464007) B1464007
theorem B1853705 : Blo 1299968 1853705 := bstep (se 2 (by rfl) ⟨695139, by rfl⟩ : syracuseStep 1853705 = 1390279) B1390279
theorem B6588701 : Blo 1299968 6588701 := bstep (se 3 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 6588701 = 2470763) B2470763
theorem B48802097 : Blo 1299968 48802097 := bstep (se 2 (by rfl) ⟨18300786, by rfl⟩ : syracuseStep 48802097 = 36601573) B36601573
theorem B2083163 : Blo 1299968 2083163 := bstep (se 1 (by rfl) ⟨1562372, by rfl⟩ : syracuseStep 2083163 = 3124745) B3124745
theorem B1952111 : Blo 1299968 1952111 := bstep (se 1 (by rfl) ⟨1464083, by rfl⟩ : syracuseStep 1952111 = 2928167) B2928167
theorem B2927015 : Blo 1299968 2927015 := bstep (se 1 (by rfl) ⟨2195261, by rfl⟩ : syracuseStep 2927015 = 4390523) B4390523
theorem B6252967 : Blo 1299968 6252967 := bstep (se 1 (by rfl) ⟨4689725, by rfl⟩ : syracuseStep 6252967 = 9379451) B9379451
theorem B6253043 : Blo 1299968 6253043 := bstep (se 1 (by rfl) ⟨4689782, by rfl⟩ : syracuseStep 6253043 = 9379565) B9379565
theorem B2779643 : Blo 1299968 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B2927123 : Blo 1299968 2927123 := bstep (se 1 (by rfl) ⟨2195342, by rfl⟩ : syracuseStep 2927123 = 4390685) B4390685
theorem B73206301 : Blo 1299968 73206301 := bstep (se 3 (by rfl) ⟨13726181, by rfl⟩ : syracuseStep 73206301 = 27452363) B27452363
theorem B1952327 : Blo 1299968 1952327 := bstep (se 1 (by rfl) ⟨1464245, by rfl⟩ : syracuseStep 1952327 = 2928491) B2928491
theorem B2927177 : Blo 1299968 2927177 := bstep (se 2 (by rfl) ⟨1097691, by rfl⟩ : syracuseStep 2927177 = 2195383) B2195383
theorem B74992229 : Blo 1299968 74992229 := bstep (se 4 (by rfl) ⟨7030521, by rfl⟩ : syracuseStep 74992229 = 14061043) B14061043
theorem B1952363 : Blo 1299968 1952363 := bstep (se 1 (by rfl) ⟨1464272, by rfl⟩ : syracuseStep 1952363 = 2928545) B2928545
theorem B1952591 : Blo 1299968 1952591 := bstep (se 1 (by rfl) ⟨1464443, by rfl⟩ : syracuseStep 1952591 = 2928887) B2928887
theorem B4393871 : Blo 1299968 4393871 := bstep (se 1 (by rfl) ⟨3295403, by rfl⟩ : syracuseStep 4393871 = 6590807) B6590807
theorem B2927591 : Blo 1299968 2927591 := bstep (se 1 (by rfl) ⟨2195693, by rfl⟩ : syracuseStep 2927591 = 4391387) B4391387
theorem B11873347 : Blo 1299968 11873347 := bstep (se 1 (by rfl) ⟨8905010, by rfl⟩ : syracuseStep 11873347 = 17810021) B17810021
theorem B9874547 : Blo 1299968 9874547 := bstep (se 1 (by rfl) ⟨7405910, by rfl⟩ : syracuseStep 9874547 = 14811821) B14811821
theorem B4689035 : Blo 1299968 4689035 := bstep (se 1 (by rfl) ⟨3516776, by rfl⟩ : syracuseStep 4689035 = 7033553) B7033553
theorem B2927969 : Blo 1299968 2927969 := bstep (se 2 (by rfl) ⟨1097988, by rfl⟩ : syracuseStep 2927969 = 2195977) B2195977
theorem B2928059 : Blo 1299968 2928059 := bstep (se 1 (by rfl) ⟨2196044, by rfl⟩ : syracuseStep 2928059 = 4392089) B4392089
theorem B10546631 : Blo 1299968 10546631 := bstep (se 1 (by rfl) ⟨7909973, by rfl⟩ : syracuseStep 10546631 = 15819947) B15819947
theorem B3706327 : Blo 1299968 3706327 := bstep (se 1 (by rfl) ⟨2779745, by rfl⟩ : syracuseStep 3706327 = 5559491) B5559491
theorem B3124793 : Blo 1299968 3124793 := bstep (se 2 (by rfl) ⟨1171797, by rfl⟩ : syracuseStep 3124793 = 2343595) B2343595
theorem B2928185 : Blo 1299968 2928185 := bstep (se 2 (by rfl) ⟨1098069, by rfl⟩ : syracuseStep 2928185 = 2196139) B2196139
theorem B3124831 : Blo 1299968 3124831 := bstep (se 1 (by rfl) ⟨2343623, by rfl⟩ : syracuseStep 3124831 = 4687247) B4687247
theorem B6680323 : Blo 1299968 6680323 := bstep (se 1 (by rfl) ⟨5010242, by rfl⟩ : syracuseStep 6680323 = 10020485) B10020485
theorem B5558057 : Blo 1299968 5558057 := bstep (se 2 (by rfl) ⟨2084271, by rfl⟩ : syracuseStep 5558057 = 4168543) B4168543
theorem B7409465 : Blo 1299968 7409465 := bstep (se 2 (by rfl) ⟨2778549, by rfl⟩ : syracuseStep 7409465 = 5557099) B5557099
theorem B3706681 : Blo 1299968 3706681 := bstep (se 2 (by rfl) ⟨1390005, by rfl⟩ : syracuseStep 3706681 = 2780011) B2780011
theorem B6590483 : Blo 1299968 6590483 := bstep (se 1 (by rfl) ⟨4942862, by rfl⟩ : syracuseStep 6590483 = 9885725) B9885725
theorem B2928851 : Blo 1299968 2928851 := bstep (se 1 (by rfl) ⟨2196638, by rfl⟩ : syracuseStep 2928851 = 4393277) B4393277
theorem B2928905 : Blo 1299968 2928905 := bstep (se 2 (by rfl) ⟨1098339, by rfl⟩ : syracuseStep 2928905 = 2196679) B2196679
theorem B26718497 : Blo 1299968 26718497 := bstep (se 2 (by rfl) ⟨10019436, by rfl⟩ : syracuseStep 26718497 = 20038873) B20038873
theorem B1462567 : Blo 1299968 1462567 := bstep (se 1 (by rfl) ⟨1096925, by rfl⟩ : syracuseStep 1462567 = 2193851) B2193851
theorem B3166571 : Blo 1299968 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B1462639 : Blo 1299968 1462639 := bstep (se 1 (by rfl) ⟨1096979, by rfl⟩ : syracuseStep 1462639 = 2193959) B2193959
theorem B2929121 : Blo 1299968 2929121 := bstep (se 2 (by rfl) ⟨1098420, by rfl⟩ : syracuseStep 2929121 = 2196841) B2196841
theorem B2257403 : Blo 1299968 2257403 := bstep (se 1 (by rfl) ⟨1693052, by rfl⟩ : syracuseStep 2257403 = 3386105) B3386105
theorem B4936211 : Blo 1299968 4936211 := bstep (se 1 (by rfl) ⟨3702158, by rfl⟩ : syracuseStep 4936211 = 7404317) B7404317
theorem B1462855 : Blo 1299968 1462855 := bstep (se 1 (by rfl) ⟨1097141, by rfl⟩ : syracuseStep 1462855 = 2194283) B2194283
theorem B10547833 : Blo 1299968 10547833 := bstep (se 2 (by rfl) ⟨3955437, by rfl⟩ : syracuseStep 10547833 = 7910875) B7910875
theorem B4387499 : Blo 1299968 4387499 := bstep (se 1 (by rfl) ⟨3290624, by rfl⟩ : syracuseStep 4387499 = 6581249) B6581249
theorem B1979063 : Blo 1299968 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B2929427 : Blo 1299968 2929427 := bstep (se 1 (by rfl) ⟨2197070, by rfl⟩ : syracuseStep 2929427 = 4394141) B4394141
theorem B4388039 : Blo 1299968 4388039 := bstep (se 1 (by rfl) ⟨3291029, by rfl⟩ : syracuseStep 4388039 = 6582059) B6582059
theorem B6952151 : Blo 1299968 6952151 := bstep (se 1 (by rfl) ⟨5214113, by rfl⟩ : syracuseStep 6952151 = 10428227) B10428227
theorem B12506359 : Blo 1299968 12506359 := bstep (se 1 (by rfl) ⟨9379769, by rfl⟩ : syracuseStep 12506359 = 18759539) B18759539
theorem B1463719 : Blo 1299968 1463719 := bstep (se 1 (by rfl) ⟨1097789, by rfl⟩ : syracuseStep 1463719 = 2195579) B2195579
theorem B6583841 : Blo 1299968 6583841 := bstep (se 2 (by rfl) ⟨2468940, by rfl⟩ : syracuseStep 6583841 = 4937881) B4937881
theorem B3954233 : Blo 1299968 3954233 := bstep (se 2 (by rfl) ⟨1482837, by rfl⟩ : syracuseStep 3954233 = 2965675) B2965675
theorem B1300031 : Blo 1299968 1300031 := bstep (se 1 (by rfl) ⟨975023, by rfl⟩ : syracuseStep 1300031 = 1950047) B1950047
theorem B1300039 : Blo 1299968 1300039 := bstep (se 1 (by rfl) ⟨975029, by rfl⟩ : syracuseStep 1300039 = 1950059) B1950059
theorem B1300191 : Blo 1299968 1300191 := bstep (se 1 (by rfl) ⟨975143, by rfl⟩ : syracuseStep 1300191 = 1950287) B1950287
theorem B1300271 : Blo 1299968 1300271 := bstep (se 1 (by rfl) ⟨975203, by rfl⟩ : syracuseStep 1300271 = 1950407) B1950407
theorem B8337239 : Blo 1299968 8337239 := bstep (se 1 (by rfl) ⟨6252929, by rfl⟩ : syracuseStep 8337239 = 12505859) B12505859
theorem B1300379 : Blo 1299968 1300379 := bstep (se 1 (by rfl) ⟨975284, by rfl⟩ : syracuseStep 1300379 = 1950569) B1950569
theorem B1300431 : Blo 1299968 1300431 := bstep (se 1 (by rfl) ⟨975323, by rfl⟩ : syracuseStep 1300431 = 1950647) B1950647
theorem B1300455 : Blo 1299968 1300455 := bstep (se 1 (by rfl) ⟨975341, by rfl⟩ : syracuseStep 1300455 = 1950683) B1950683
theorem B1464295 : Blo 1299968 1464295 := bstep (se 1 (by rfl) ⟨1098221, by rfl⟩ : syracuseStep 1464295 = 2196443) B2196443
theorem B11884573 : Blo 1299968 11884573 := bstep (se 3 (by rfl) ⟨2228357, by rfl⟩ : syracuseStep 11884573 = 4456715) B4456715
theorem B11868389 : Blo 1299968 11868389 := bstep (se 4 (by rfl) ⟨1112661, by rfl⟩ : syracuseStep 11868389 = 2225323) B2225323
theorem B6019337 : Blo 1299968 6019337 := bstep (se 2 (by rfl) ⟨2257251, by rfl⟩ : syracuseStep 6019337 = 4514503) B4514503
theorem B1300767 : Blo 1299968 1300767 := bstep (se 1 (by rfl) ⟨975575, by rfl⟩ : syracuseStep 1300767 = 1951151) B1951151
theorem B1300827 : Blo 1299968 1300827 := bstep (se 1 (by rfl) ⟨975620, by rfl⟩ : syracuseStep 1300827 = 1951241) B1951241
theorem B1300847 : Blo 1299968 1300847 := bstep (se 1 (by rfl) ⟨975635, by rfl⟩ : syracuseStep 1300847 = 1951271) B1951271
theorem B1300903 : Blo 1299968 1300903 := bstep (se 1 (by rfl) ⟨975677, by rfl⟩ : syracuseStep 1300903 = 1951355) B1951355
theorem B1563079 : Blo 1299968 1563079 := bstep (se 1 (by rfl) ⟨1172309, by rfl⟩ : syracuseStep 1563079 = 2344619) B2344619
theorem B3291617 : Blo 1299968 3291617 := bstep (se 2 (by rfl) ⟨1234356, by rfl⟩ : syracuseStep 3291617 = 2468713) B2468713
theorem B1300987 : Blo 1299968 1300987 := bstep (se 1 (by rfl) ⟨975740, by rfl⟩ : syracuseStep 1300987 = 1951481) B1951481
theorem B11860505 : Blo 1299968 11860505 := bstep (se 2 (by rfl) ⟨4447689, by rfl⟩ : syracuseStep 11860505 = 8895379) B8895379
theorem B1301055 : Blo 1299968 1301055 := bstep (se 1 (by rfl) ⟨975791, by rfl⟩ : syracuseStep 1301055 = 1951583) B1951583
theorem B1301063 : Blo 1299968 1301063 := bstep (se 1 (by rfl) ⟨975797, by rfl⟩ : syracuseStep 1301063 = 1951595) B1951595
theorem B12499595 : Blo 1299968 12499595 := bstep (se 1 (by rfl) ⟨9374696, by rfl⟩ : syracuseStep 12499595 = 18749393) B18749393
theorem B4389551 : Blo 1299968 4389551 := bstep (se 1 (by rfl) ⟨3292163, by rfl⟩ : syracuseStep 4389551 = 6584327) B6584327
theorem B18766511 : Blo 1299968 18766511 := bstep (se 1 (by rfl) ⟨14074883, by rfl⟩ : syracuseStep 18766511 = 28149767) B28149767
theorem B1301215 : Blo 1299968 1301215 := bstep (se 1 (by rfl) ⟨975911, by rfl⟩ : syracuseStep 1301215 = 1951823) B1951823
theorem B1301295 : Blo 1299968 1301295 := bstep (se 1 (by rfl) ⟨975971, by rfl⟩ : syracuseStep 1301295 = 1951943) B1951943
theorem B1301403 : Blo 1299968 1301403 := bstep (se 1 (by rfl) ⟨976052, by rfl⟩ : syracuseStep 1301403 = 1952105) B1952105
theorem B1301455 : Blo 1299968 1301455 := bstep (se 1 (by rfl) ⟨976091, by rfl⟩ : syracuseStep 1301455 = 1952183) B1952183
theorem B3292123 : Blo 1299968 3292123 := bstep (se 1 (by rfl) ⟨2469092, by rfl⟩ : syracuseStep 3292123 = 4938185) B4938185
theorem B1301479 : Blo 1299968 1301479 := bstep (se 1 (by rfl) ⟨976109, by rfl⟩ : syracuseStep 1301479 = 1952219) B1952219
theorem B35585011 : Blo 1299968 35585011 := bstep (se 1 (by rfl) ⟨26688758, by rfl⟩ : syracuseStep 35585011 = 53377517) B53377517
theorem B4389875 : Blo 1299968 4389875 := bstep (se 1 (by rfl) ⟨3292406, by rfl⟩ : syracuseStep 4389875 = 6584813) B6584813
theorem B8338621 : Blo 1299968 8338621 := bstep (se 3 (by rfl) ⟨1563491, by rfl⟩ : syracuseStep 8338621 = 3126983) B3126983
theorem B1604827 : Blo 1299968 1604827 := bstep (se 1 (by rfl) ⟨1203620, by rfl⟩ : syracuseStep 1604827 = 2407241) B2407241
theorem B24993035 : Blo 1299968 24993035 := bstep (se 1 (by rfl) ⟨18744776, by rfl⟩ : syracuseStep 24993035 = 37489553) B37489553
theorem B12680459 : Blo 1299968 12680459 := bstep (se 1 (by rfl) ⟨9510344, by rfl⟩ : syracuseStep 12680459 = 19020689) B19020689
theorem B3292447 : Blo 1299968 3292447 := bstep (se 1 (by rfl) ⟨2469335, by rfl⟩ : syracuseStep 3292447 = 4938671) B4938671
theorem B1301791 : Blo 1299968 1301791 := bstep (se 1 (by rfl) ⟨976343, by rfl⟩ : syracuseStep 1301791 = 1952687) B1952687
theorem B2637095 : Blo 1299968 2637095 := bstep (se 1 (by rfl) ⟨1977821, by rfl⟩ : syracuseStep 2637095 = 3955643) B3955643
theorem B63282485 : Blo 1299968 63282485 := bstep (se 5 (by rfl) ⟨2966366, by rfl⟩ : syracuseStep 63282485 = 5932733) B5932733
theorem B1645915 : Blo 1299968 1645915 := bstep (se 1 (by rfl) ⟨1234436, by rfl⟩ : syracuseStep 1645915 = 2468873) B2468873
theorem B1301851 : Blo 1299968 1301851 := bstep (se 1 (by rfl) ⟨976388, by rfl⟩ : syracuseStep 1301851 = 1952777) B1952777
theorem B1301871 : Blo 1299968 1301871 := bstep (se 1 (by rfl) ⟨976403, by rfl⟩ : syracuseStep 1301871 = 1952807) B1952807
theorem B4939127 : Blo 1299968 4939127 := bstep (se 1 (by rfl) ⟨3704345, by rfl⟩ : syracuseStep 4939127 = 7408691) B7408691
theorem B2776457 : Blo 1299968 2776457 := bstep (se 2 (by rfl) ⟨1041171, by rfl⟩ : syracuseStep 2776457 = 2082343) B2082343
theorem B9878921 : Blo 1299968 9878921 := bstep (se 2 (by rfl) ⟨3704595, by rfl⟩ : syracuseStep 9878921 = 7409191) B7409191
theorem B22224293 : Blo 1299968 22224293 := bstep (se 4 (by rfl) ⟨2083527, by rfl⟩ : syracuseStep 22224293 = 4167055) B4167055
theorem B1301927 : Blo 1299968 1301927 := bstep (se 1 (by rfl) ⟨976445, by rfl⟩ : syracuseStep 1301927 = 1952891) B1952891
theorem B4390415 : Blo 1299968 4390415 := bstep (se 1 (by rfl) ⟨3292811, by rfl⟩ : syracuseStep 4390415 = 6585623) B6585623
theorem B2195039 : Blo 1299968 2195039 := bstep (se 1 (by rfl) ⟨1646279, by rfl⟩ : syracuseStep 2195039 = 3292559) B3292559
theorem B4448047 : Blo 1299968 4448047 := bstep (se 1 (by rfl) ⟨3336035, by rfl⟩ : syracuseStep 4448047 = 6672071) B6672071
theorem B2195255 : Blo 1299968 2195255 := bstep (se 1 (by rfl) ⟨1646441, by rfl⟩ : syracuseStep 2195255 = 3292883) B3292883
theorem B7413565 : Blo 1299968 7413565 := bstep (se 3 (by rfl) ⟨1390043, by rfl⟩ : syracuseStep 7413565 = 2780087) B2780087
theorem B2195687 : Blo 1299968 2195687 := bstep (se 1 (by rfl) ⟨1646765, by rfl⟩ : syracuseStep 2195687 = 3293531) B3293531
theorem B4940129 : Blo 1299968 4940129 := bstep (se 2 (by rfl) ⟨1852548, by rfl⟩ : syracuseStep 4940129 = 3705097) B3705097
theorem B63324517 : Blo 1299968 63324517 := bstep (se 4 (by rfl) ⟨5936673, by rfl⟩ : syracuseStep 63324517 = 11873347) B11873347
theorem B1950089 : Blo 1299968 1950089 := bstep (se 2 (by rfl) ⟨731283, by rfl⟩ : syracuseStep 1950089 = 1462567) B1462567
theorem B2195849 : Blo 1299968 2195849 := bstep (se 2 (by rfl) ⟨823443, by rfl⟩ : syracuseStep 2195849 = 1646887) B1646887
theorem B2924999 : Blo 1299968 2924999 := bstep (se 1 (by rfl) ⟨2193749, by rfl⟩ : syracuseStep 2924999 = 4387499) B4387499
theorem B8896967 : Blo 1299968 8896967 := bstep (se 1 (by rfl) ⟨6672725, by rfl⟩ : syracuseStep 8896967 = 13345451) B13345451
theorem B1319375 : Blo 1299968 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B1950185 : Blo 1299968 1950185 := bstep (se 2 (by rfl) ⟨731319, by rfl⟩ : syracuseStep 1950185 = 1462639) B1462639
theorem B6586919 : Blo 1299968 6586919 := bstep (se 1 (by rfl) ⟨4940189, by rfl⟩ : syracuseStep 6586919 = 9880379) B9880379
theorem B1950311 : Blo 1299968 1950311 := bstep (se 1 (by rfl) ⟨1462733, by rfl⟩ : syracuseStep 1950311 = 2925467) B2925467
theorem B7406275 : Blo 1299968 7406275 := bstep (se 1 (by rfl) ⟨5554706, by rfl⟩ : syracuseStep 7406275 = 11109413) B11109413
theorem B97608401 : Blo 1299968 97608401 := bstep (se 2 (by rfl) ⟨36603150, by rfl⟩ : syracuseStep 97608401 = 73206301) B73206301
theorem B1950443 : Blo 1299968 1950443 := bstep (se 1 (by rfl) ⟨1462832, by rfl⟩ : syracuseStep 1950443 = 2925665) B2925665
theorem B1950473 : Blo 1299968 1950473 := bstep (se 2 (by rfl) ⟨731427, by rfl⟩ : syracuseStep 1950473 = 1462855) B1462855
theorem B2925359 : Blo 1299968 2925359 := bstep (se 1 (by rfl) ⟨2194019, by rfl⟩ : syracuseStep 2925359 = 4388039) B4388039
theorem B2196281 : Blo 1299968 2196281 := bstep (se 2 (by rfl) ⟨823605, by rfl⟩ : syracuseStep 2196281 = 1647211) B1647211
theorem B1950575 : Blo 1299968 1950575 := bstep (se 1 (by rfl) ⟨1462931, by rfl⟩ : syracuseStep 1950575 = 2925863) B2925863
theorem B2196335 : Blo 1299968 2196335 := bstep (se 1 (by rfl) ⟨1647251, by rfl⟩ : syracuseStep 2196335 = 3294503) B3294503
theorem B5555101 : Blo 1299968 5555101 := bstep (se 3 (by rfl) ⟨1041581, by rfl⟩ : syracuseStep 5555101 = 2083163) B2083163
theorem B3703913 : Blo 1299968 3703913 := bstep (se 2 (by rfl) ⟨1388967, by rfl⟩ : syracuseStep 3703913 = 2777935) B2777935
theorem B1950827 : Blo 1299968 1950827 := bstep (se 1 (by rfl) ⟨1463120, by rfl⟩ : syracuseStep 1950827 = 2926241) B2926241
theorem B4392143 : Blo 1299968 4392143 := bstep (se 1 (by rfl) ⟨3294107, by rfl⟩ : syracuseStep 4392143 = 6588215) B6588215
theorem B8897795 : Blo 1299968 8897795 := bstep (se 1 (by rfl) ⟨6673346, by rfl⟩ : syracuseStep 8897795 = 13346693) B13346693
theorem B1951067 : Blo 1299968 1951067 := bstep (se 1 (by rfl) ⟨1463300, by rfl⟩ : syracuseStep 1951067 = 2926601) B2926601
theorem B4392467 : Blo 1299968 4392467 := bstep (se 1 (by rfl) ⟨3294350, by rfl⟩ : syracuseStep 4392467 = 6588701) B6588701
theorem B11118161 : Blo 1299968 11118161 := bstep (se 2 (by rfl) ⟨4169310, by rfl⟩ : syracuseStep 11118161 = 8338621) B8338621
theorem B1951343 : Blo 1299968 1951343 := bstep (se 1 (by rfl) ⟨1463507, by rfl⟩ : syracuseStep 1951343 = 2927015) B2927015
theorem B2139769 : Blo 1299968 2139769 := bstep (se 2 (by rfl) ⟨802413, by rfl⟩ : syracuseStep 2139769 = 1604827) B1604827
theorem B1951415 : Blo 1299968 1951415 := bstep (se 1 (by rfl) ⟨1463561, by rfl⟩ : syracuseStep 1951415 = 2927123) B2927123
theorem B7907003 : Blo 1299968 7907003 := bstep (se 1 (by rfl) ⟨5930252, by rfl⟩ : syracuseStep 7907003 = 11860505) B11860505
theorem B1951451 : Blo 1299968 1951451 := bstep (se 1 (by rfl) ⟨1463588, by rfl⟩ : syracuseStep 1951451 = 2927177) B2927177
theorem B8333063 : Blo 1299968 8333063 := bstep (se 1 (by rfl) ⟨6249797, by rfl⟩ : syracuseStep 8333063 = 12499595) B12499595
theorem B2926367 : Blo 1299968 2926367 := bstep (se 1 (by rfl) ⟨2194775, by rfl⟩ : syracuseStep 2926367 = 4389551) B4389551
theorem B12511007 : Blo 1299968 12511007 := bstep (se 1 (by rfl) ⟨9383255, by rfl⟩ : syracuseStep 12511007 = 18766511) B18766511
theorem B1951625 : Blo 1299968 1951625 := bstep (se 2 (by rfl) ⟨731859, by rfl⟩ : syracuseStep 1951625 = 1463719) B1463719
theorem B4941769 : Blo 1299968 4941769 := bstep (se 2 (by rfl) ⟨1853163, by rfl⟩ : syracuseStep 4941769 = 3706327) B3706327
theorem B1951727 : Blo 1299968 1951727 := bstep (se 1 (by rfl) ⟨1463795, by rfl⟩ : syracuseStep 1951727 = 2927591) B2927591
theorem B2926583 : Blo 1299968 2926583 := bstep (se 1 (by rfl) ⟨2194937, by rfl⟩ : syracuseStep 2926583 = 4389875) B4389875
theorem B1951979 : Blo 1299968 1951979 := bstep (se 1 (by rfl) ⟨1463984, by rfl⟩ : syracuseStep 1951979 = 2927969) B2927969
theorem B1952039 : Blo 1299968 1952039 := bstep (se 1 (by rfl) ⟨1464029, by rfl⟩ : syracuseStep 1952039 = 2928059) B2928059
theorem B7031087 : Blo 1299968 7031087 := bstep (se 1 (by rfl) ⟨5273315, by rfl⟩ : syracuseStep 7031087 = 10546631) B10546631
theorem B8907097 : Blo 1299968 8907097 := bstep (se 2 (by rfl) ⟨3340161, by rfl⟩ : syracuseStep 8907097 = 6680323) B6680323
theorem B2926943 : Blo 1299968 2926943 := bstep (se 1 (by rfl) ⟨2195207, by rfl⟩ : syracuseStep 2926943 = 4390415) B4390415
theorem B2083195 : Blo 1299968 2083195 := bstep (se 1 (by rfl) ⟨1562396, by rfl⟩ : syracuseStep 2083195 = 3124793) B3124793
theorem B1952123 : Blo 1299968 1952123 := bstep (se 1 (by rfl) ⟨1464092, by rfl⟩ : syracuseStep 1952123 = 2928185) B2928185
theorem B4942241 : Blo 1299968 4942241 := bstep (se 2 (by rfl) ⟨1853340, by rfl⟩ : syracuseStep 4942241 = 3706681) B3706681
theorem B4753889 : Blo 1299968 4753889 := bstep (se 2 (by rfl) ⟨1782708, by rfl⟩ : syracuseStep 4753889 = 3565417) B3565417
theorem B3705371 : Blo 1299968 3705371 := bstep (se 1 (by rfl) ⟨2779028, by rfl⟩ : syracuseStep 3705371 = 5558057) B5558057
theorem B24078965 : Blo 1299968 24078965 := bstep (se 5 (by rfl) ⟨1128701, by rfl⟩ : syracuseStep 24078965 = 2257403) B2257403
theorem B1952393 : Blo 1299968 1952393 := bstep (se 2 (by rfl) ⟨732147, by rfl⟩ : syracuseStep 1952393 = 1464295) B1464295
theorem B4393655 : Blo 1299968 4393655 := bstep (se 1 (by rfl) ⟨3295241, by rfl⟩ : syracuseStep 4393655 = 6590483) B6590483
theorem B15846097 : Blo 1299968 15846097 := bstep (se 2 (by rfl) ⟨5942286, by rfl⟩ : syracuseStep 15846097 = 11884573) B11884573
theorem B1952567 : Blo 1299968 1952567 := bstep (se 1 (by rfl) ⟨1464425, by rfl⟩ : syracuseStep 1952567 = 2928851) B2928851
theorem B1952603 : Blo 1299968 1952603 := bstep (se 1 (by rfl) ⟨1464452, by rfl⟩ : syracuseStep 1952603 = 2928905) B2928905
theorem B17812331 : Blo 1299968 17812331 := bstep (se 1 (by rfl) ⟨13359248, by rfl⟩ : syracuseStep 17812331 = 26718497) B26718497
theorem B1952747 : Blo 1299968 1952747 := bstep (se 1 (by rfl) ⟨1464560, by rfl⟩ : syracuseStep 1952747 = 2929121) B2929121
theorem B2927663 : Blo 1299968 2927663 := bstep (se 1 (by rfl) ⟨2195747, by rfl⟩ : syracuseStep 2927663 = 4391495) B4391495
theorem B1952951 : Blo 1299968 1952951 := bstep (se 1 (by rfl) ⟨1464713, by rfl⟩ : syracuseStep 1952951 = 2929427) B2929427
theorem B2084105 : Blo 1299968 2084105 := bstep (se 2 (by rfl) ⟨781539, by rfl⟩ : syracuseStep 2084105 = 1563079) B1563079
theorem B2469199 : Blo 1299968 2469199 := bstep (se 1 (by rfl) ⟨1851899, by rfl⟩ : syracuseStep 2469199 = 3703799) B3703799
theorem B2927951 : Blo 1299968 2927951 := bstep (se 1 (by rfl) ⟨2195963, by rfl⟩ : syracuseStep 2927951 = 4391927) B4391927
theorem B4943213 : Blo 1299968 4943213 := bstep (se 3 (by rfl) ⟨926852, by rfl⟩ : syracuseStep 4943213 = 1853705) B1853705
theorem B2928041 : Blo 1299968 2928041 := bstep (se 2 (by rfl) ⟨1098015, by rfl⟩ : syracuseStep 2928041 = 2196031) B2196031
theorem B7032253 : Blo 1299968 7032253 := bstep (se 3 (by rfl) ⟨1318547, by rfl⟩ : syracuseStep 7032253 = 2637095) B2637095
theorem B5558159 : Blo 1299968 5558159 := bstep (se 1 (by rfl) ⟨4168619, by rfl⟩ : syracuseStep 5558159 = 8337239) B8337239
theorem B2928527 : Blo 1299968 2928527 := bstep (se 1 (by rfl) ⟨2196395, by rfl⟩ : syracuseStep 2928527 = 4392791) B4392791
theorem B16674781 : Blo 1299968 16674781 := bstep (se 3 (by rfl) ⟨3126521, by rfl⟩ : syracuseStep 16674781 = 6253043) B6253043
theorem B32534731 : Blo 1299968 32534731 := bstep (se 1 (by rfl) ⟨24401048, by rfl⟩ : syracuseStep 32534731 = 48802097) B48802097
theorem B16675145 : Blo 1299968 16675145 := bstep (se 2 (by rfl) ⟨6253179, by rfl⟩ : syracuseStep 16675145 = 12506359) B12506359
theorem B2929247 : Blo 1299968 2929247 := bstep (se 1 (by rfl) ⟨2196935, by rfl⟩ : syracuseStep 2929247 = 4393871) B4393871
theorem B6583031 : Blo 1299968 6583031 := bstep (se 1 (by rfl) ⟨4937273, by rfl⟩ : syracuseStep 6583031 = 9874547) B9874547
theorem B3126023 : Blo 1299968 3126023 := bstep (se 1 (by rfl) ⟨2344517, by rfl⟩ : syracuseStep 3126023 = 4689035) B4689035
theorem B4166441 : Blo 1299968 4166441 := bstep (se 2 (by rfl) ⟨1562415, by rfl⟩ : syracuseStep 4166441 = 3124831) B3124831
theorem B14816195 : Blo 1299968 14816195 := bstep (se 1 (by rfl) ⟨11112146, by rfl⟩ : syracuseStep 14816195 = 22224293) B22224293
theorem B1463359 : Blo 1299968 1463359 := bstep (se 1 (by rfl) ⟨1097519, by rfl⟩ : syracuseStep 1463359 = 2195039) B2195039
theorem B9884753 : Blo 1299968 9884753 := bstep (se 2 (by rfl) ⟨3706782, by rfl⟩ : syracuseStep 9884753 = 7413565) B7413565
theorem B1463503 : Blo 1299968 1463503 := bstep (se 1 (by rfl) ⟨1097627, by rfl⟩ : syracuseStep 1463503 = 2195255) B2195255
theorem B3757499 : Blo 1299968 3757499 := bstep (se 1 (by rfl) ⟨2818124, by rfl⟩ : syracuseStep 3757499 = 5636249) B5636249
theorem B1300079 : Blo 1299968 1300079 := bstep (se 1 (by rfl) ⟨975059, by rfl⟩ : syracuseStep 1300079 = 1950119) B1950119
theorem B1300135 : Blo 1299968 1300135 := bstep (se 1 (by rfl) ⟨975101, by rfl⟩ : syracuseStep 1300135 = 1950203) B1950203
theorem B3290807 : Blo 1299968 3290807 := bstep (se 1 (by rfl) ⟨2468105, by rfl⟩ : syracuseStep 3290807 = 4936211) B4936211
theorem B1300219 : Blo 1299968 1300219 := bstep (se 1 (by rfl) ⟨975164, by rfl⟩ : syracuseStep 1300219 = 1950329) B1950329
theorem B1300255 : Blo 1299968 1300255 := bstep (se 1 (by rfl) ⟨975191, by rfl⟩ : syracuseStep 1300255 = 1950383) B1950383
theorem B1300287 : Blo 1299968 1300287 := bstep (se 1 (by rfl) ⟨975215, by rfl⟩ : syracuseStep 1300287 = 1950431) B1950431
theorem B8337289 : Blo 1299968 8337289 := bstep (se 2 (by rfl) ⟨3126483, by rfl⟩ : syracuseStep 8337289 = 6252967) B6252967
theorem B1300463 : Blo 1299968 1300463 := bstep (se 1 (by rfl) ⟨975347, by rfl⟩ : syracuseStep 1300463 = 1950695) B1950695
theorem B4634767 : Blo 1299968 4634767 := bstep (se 1 (by rfl) ⟨3476075, by rfl⟩ : syracuseStep 4634767 = 6952151) B6952151
theorem B1300635 : Blo 1299968 1300635 := bstep (se 1 (by rfl) ⟨975476, by rfl⟩ : syracuseStep 1300635 = 1950953) B1950953
theorem B1464475 : Blo 1299968 1464475 := bstep (se 1 (by rfl) ⟨1098356, by rfl⟩ : syracuseStep 1464475 = 2196713) B2196713
theorem B14063777 : Blo 1299968 14063777 := bstep (se 2 (by rfl) ⟨5273916, by rfl⟩ : syracuseStep 14063777 = 10547833) B10547833
theorem B1300671 : Blo 1299968 1300671 := bstep (se 1 (by rfl) ⟨975503, by rfl⟩ : syracuseStep 1300671 = 1951007) B1951007
theorem B1464511 : Blo 1299968 1464511 := bstep (se 1 (by rfl) ⟨1098383, by rfl⟩ : syracuseStep 1464511 = 2196767) B2196767
theorem B8444189 : Blo 1299968 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B1300783 : Blo 1299968 1300783 := bstep (se 1 (by rfl) ⟨975587, by rfl⟩ : syracuseStep 1300783 = 1951175) B1951175
theorem B4389227 : Blo 1299968 4389227 := bstep (se 1 (by rfl) ⟨3291920, by rfl⟩ : syracuseStep 4389227 = 6583841) B6583841
theorem B7403885 : Blo 1299968 7403885 := bstep (se 3 (by rfl) ⟨1388228, by rfl⟩ : syracuseStep 7403885 = 2776457) B2776457
theorem B2636155 : Blo 1299968 2636155 := bstep (se 1 (by rfl) ⟨1977116, by rfl⟩ : syracuseStep 2636155 = 3954233) B3954233
theorem B1301019 : Blo 1299968 1301019 := bstep (se 1 (by rfl) ⟨975764, by rfl⟩ : syracuseStep 1301019 = 1951529) B1951529
theorem B1301023 : Blo 1299968 1301023 := bstep (se 1 (by rfl) ⟨975767, by rfl⟩ : syracuseStep 1301023 = 1951535) B1951535
theorem B4389497 : Blo 1299968 4389497 := bstep (se 2 (by rfl) ⟨1646061, by rfl⟩ : syracuseStep 4389497 = 3292123) B3292123
theorem B47446681 : Blo 1299968 47446681 := bstep (se 2 (by rfl) ⟨17792505, by rfl⟩ : syracuseStep 47446681 = 35585011) B35585011
theorem B7412381 : Blo 1299968 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B4168415 : Blo 1299968 4168415 := bstep (se 1 (by rfl) ⟨3126311, by rfl⟩ : syracuseStep 4168415 = 6252623) B6252623
theorem B5561131 : Blo 1299968 5561131 := bstep (se 1 (by rfl) ⟨4170848, by rfl⟩ : syracuseStep 5561131 = 8341697) B8341697
theorem B7912259 : Blo 1299968 7912259 := bstep (se 1 (by rfl) ⟨5934194, by rfl⟩ : syracuseStep 7912259 = 11868389) B11868389
theorem B1301339 : Blo 1299968 1301339 := bstep (se 1 (by rfl) ⟨976004, by rfl⟩ : syracuseStep 1301339 = 1952009) B1952009
theorem B4012891 : Blo 1299968 4012891 := bstep (se 1 (by rfl) ⟨3009668, by rfl⟩ : syracuseStep 4012891 = 6019337) B6019337
theorem B1301407 : Blo 1299968 1301407 := bstep (se 1 (by rfl) ⟨976055, by rfl⟩ : syracuseStep 1301407 = 1952111) B1952111
theorem B2194411 : Blo 1299968 2194411 := bstep (se 1 (by rfl) ⟨1645808, by rfl⟩ : syracuseStep 2194411 = 3291617) B3291617
theorem B4389929 : Blo 1299968 4389929 := bstep (se 2 (by rfl) ⟨1646223, by rfl⟩ : syracuseStep 4389929 = 3292447) B3292447
theorem B1301551 : Blo 1299968 1301551 := bstep (se 1 (by rfl) ⟨976163, by rfl⟩ : syracuseStep 1301551 = 1952327) B1952327
theorem B49994819 : Blo 1299968 49994819 := bstep (se 1 (by rfl) ⟨37496114, by rfl⟩ : syracuseStep 49994819 = 74992229) B74992229
theorem B1301575 : Blo 1299968 1301575 := bstep (se 1 (by rfl) ⟨976181, by rfl⟩ : syracuseStep 1301575 = 1952363) B1952363
theorem B2194553 : Blo 1299968 2194553 := bstep (se 2 (by rfl) ⟨822957, by rfl⟩ : syracuseStep 2194553 = 1645915) B1645915
theorem B1301727 : Blo 1299968 1301727 := bstep (se 1 (by rfl) ⟨976295, by rfl⟩ : syracuseStep 1301727 = 1952591) B1952591
theorem B16662023 : Blo 1299968 16662023 := bstep (se 1 (by rfl) ⟨12496517, by rfl⟩ : syracuseStep 16662023 = 24993035) B24993035
theorem B8453639 : Blo 1299968 8453639 := bstep (se 1 (by rfl) ⟨6340229, by rfl⟩ : syracuseStep 8453639 = 12680459) B12680459
theorem B42188323 : Blo 1299968 42188323 := bstep (se 1 (by rfl) ⟨31641242, by rfl⟩ : syracuseStep 42188323 = 63282485) B63282485
theorem B3292751 : Blo 1299968 3292751 := bstep (se 1 (by rfl) ⟨2469563, by rfl⟩ : syracuseStep 3292751 = 4939127) B4939127
theorem B6585947 : Blo 1299968 6585947 := bstep (se 1 (by rfl) ⟨4939460, by rfl⟩ : syracuseStep 6585947 = 9878921) B9878921
theorem B37510877 : Blo 1299968 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B5930729 : Blo 1299968 5930729 := bstep (se 2 (by rfl) ⟨2224023, by rfl⟩ : syracuseStep 5930729 = 4448047) B4448047
theorem B4939643 : Blo 1299968 4939643 := bstep (se 1 (by rfl) ⟨3704732, by rfl⟩ : syracuseStep 4939643 = 7409465) B7409465
theorem B11116763 : Blo 1299968 11116763 := bstep (se 1 (by rfl) ⟨8337572, by rfl⟩ : syracuseStep 11116763 = 16675145) B16675145
theorem B3293419 : Blo 1299968 3293419 := bstep (se 1 (by rfl) ⟨2470064, by rfl⟩ : syracuseStep 3293419 = 4940129) B4940129
theorem B1949999 : Blo 1299968 1949999 := bstep (se 1 (by rfl) ⟨1462499, by rfl⟩ : syracuseStep 1949999 = 2924999) B2924999
theorem B5931311 : Blo 1299968 5931311 := bstep (se 1 (by rfl) ⟨4448483, by rfl⟩ : syracuseStep 5931311 = 8896967) B8896967
theorem B4391279 : Blo 1299968 4391279 := bstep (se 1 (by rfl) ⟨3293459, by rfl⟩ : syracuseStep 4391279 = 6586919) B6586919
theorem B2777593 : Blo 1299968 2777593 := bstep (se 2 (by rfl) ⟨1041597, by rfl⟩ : syracuseStep 2777593 = 2083195) B2083195
theorem B2777627 : Blo 1299968 2777627 := bstep (se 1 (by rfl) ⟨2083220, by rfl⟩ : syracuseStep 2777627 = 4166441) B4166441
theorem B1950239 : Blo 1299968 1950239 := bstep (se 1 (by rfl) ⟨1462679, by rfl⟩ : syracuseStep 1950239 = 2925359) B2925359
theorem B5931863 : Blo 1299968 5931863 := bstep (se 1 (by rfl) ⟨4448897, by rfl⟩ : syracuseStep 5931863 = 8897795) B8897795
theorem B21128129 : Blo 1299968 21128129 := bstep (se 2 (by rfl) ⟨7923048, by rfl⟩ : syracuseStep 21128129 = 15846097) B15846097
theorem B7414841 : Blo 1299968 7414841 := bstep (se 2 (by rfl) ⟨2780565, by rfl⟩ : syracuseStep 7414841 = 5561131) B5561131
theorem B5555375 : Blo 1299968 5555375 := bstep (se 1 (by rfl) ⟨4166531, by rfl⟩ : syracuseStep 5555375 = 8333063) B8333063
theorem B1950911 : Blo 1299968 1950911 := bstep (se 1 (by rfl) ⟨1463183, by rfl⟩ : syracuseStep 1950911 = 2926367) B2926367
theorem B8340671 : Blo 1299968 8340671 := bstep (se 1 (by rfl) ⟨6255503, by rfl⟩ : syracuseStep 8340671 = 12511007) B12511007
theorem B7406801 : Blo 1299968 7406801 := bstep (se 2 (by rfl) ⟨2777550, by rfl⟩ : syracuseStep 7406801 = 5555101) B5555101
theorem B2925881 : Blo 1299968 2925881 := bstep (se 2 (by rfl) ⟨1097205, by rfl⟩ : syracuseStep 2925881 = 2194411) B2194411
theorem B1951055 : Blo 1299968 1951055 := bstep (se 1 (by rfl) ⟨1463291, by rfl⟩ : syracuseStep 1951055 = 2926583) B2926583
theorem B1951145 : Blo 1299968 1951145 := bstep (se 2 (by rfl) ⟨731679, by rfl⟩ : syracuseStep 1951145 = 1463359) B1463359
theorem B5629459 : Blo 1299968 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B4687391 : Blo 1299968 4687391 := bstep (se 1 (by rfl) ⟨3515543, by rfl⟩ : syracuseStep 4687391 = 7031087) B7031087
theorem B1951295 : Blo 1299968 1951295 := bstep (se 1 (by rfl) ⟨1463471, by rfl⟩ : syracuseStep 1951295 = 2926943) B2926943
theorem B2926151 : Blo 1299968 2926151 := bstep (se 1 (by rfl) ⟨2194613, by rfl⟩ : syracuseStep 2926151 = 4389227) B4389227
theorem B1951337 : Blo 1299968 1951337 := bstep (se 2 (by rfl) ⟨731751, by rfl⟩ : syracuseStep 1951337 = 1463503) B1463503
theorem B3294827 : Blo 1299968 3294827 := bstep (se 1 (by rfl) ⟨2471120, by rfl⟩ : syracuseStep 3294827 = 4942241) B4942241
theorem B64210573 : Blo 1299968 64210573 := bstep (se 3 (by rfl) ⟨12039482, by rfl⟩ : syracuseStep 64210573 = 24078965) B24078965
theorem B2926331 : Blo 1299968 2926331 := bstep (se 1 (by rfl) ⟨2194748, by rfl⟩ : syracuseStep 2926331 = 4389497) B4389497
theorem B4941587 : Blo 1299968 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B2778943 : Blo 1299968 2778943 := bstep (se 1 (by rfl) ⟨2084207, by rfl⟩ : syracuseStep 2778943 = 4168415) B4168415
theorem B14059493 : Blo 1299968 14059493 := bstep (se 4 (by rfl) ⟨1318077, by rfl⟩ : syracuseStep 14059493 = 2636155) B2636155
theorem B2926619 : Blo 1299968 2926619 := bstep (se 1 (by rfl) ⟨2194964, by rfl⟩ : syracuseStep 2926619 = 4389929) B4389929
theorem B1951775 : Blo 1299968 1951775 := bstep (se 1 (by rfl) ⟨1463831, by rfl⟩ : syracuseStep 1951775 = 2927663) B2927663
theorem B2853025 : Blo 1299968 2853025 := bstep (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) B2139769
theorem B1951967 : Blo 1299968 1951967 := bstep (se 1 (by rfl) ⟨1463975, by rfl⟩ : syracuseStep 1951967 = 2927951) B2927951
theorem B3295475 : Blo 1299968 3295475 := bstep (se 1 (by rfl) ⟨2471606, by rfl⟩ : syracuseStep 3295475 = 4943213) B4943213
theorem B1952027 : Blo 1299968 1952027 := bstep (se 1 (by rfl) ⟨1464020, by rfl⟩ : syracuseStep 1952027 = 2928041) B2928041
theorem B3705439 : Blo 1299968 3705439 := bstep (se 1 (by rfl) ⟨2779079, by rfl⟩ : syracuseStep 3705439 = 5558159) B5558159
theorem B1952351 : Blo 1299968 1952351 := bstep (se 1 (by rfl) ⟨1464263, by rfl⟩ : syracuseStep 1952351 = 2928527) B2928527
theorem B6589025 : Blo 1299968 6589025 := bstep (se 2 (by rfl) ⟨2470884, by rfl⟩ : syracuseStep 6589025 = 4941769) B4941769
theorem B6179689 : Blo 1299968 6179689 := bstep (se 2 (by rfl) ⟨2317383, by rfl⟩ : syracuseStep 6179689 = 4634767) B4634767
theorem B1952633 : Blo 1299968 1952633 := bstep (se 2 (by rfl) ⟨732237, by rfl⟩ : syracuseStep 1952633 = 1464475) B1464475
theorem B1952681 : Blo 1299968 1952681 := bstep (se 2 (by rfl) ⟨732255, by rfl⟩ : syracuseStep 1952681 = 1464511) B1464511
theorem B43379641 : Blo 1299968 43379641 := bstep (se 2 (by rfl) ⟨16267365, by rfl⟩ : syracuseStep 43379641 = 32534731) B32534731
theorem B1952831 : Blo 1299968 1952831 := bstep (se 1 (by rfl) ⟨1464623, by rfl⟩ : syracuseStep 1952831 = 2929247) B2929247
theorem B65072267 : Blo 1299968 65072267 := bstep (se 1 (by rfl) ⟨48804200, by rfl⟩ : syracuseStep 65072267 = 97608401) B97608401
theorem B2084015 : Blo 1299968 2084015 := bstep (se 1 (by rfl) ⟨1563011, by rfl⟩ : syracuseStep 2084015 = 3126023) B3126023
theorem B6589835 : Blo 1299968 6589835 := bstep (se 1 (by rfl) ⟨4942376, by rfl⟩ : syracuseStep 6589835 = 9884753) B9884753
theorem B2469275 : Blo 1299968 2469275 := bstep (se 1 (by rfl) ⟨1851956, by rfl⟩ : syracuseStep 2469275 = 3703913) B3703913
theorem B2928095 : Blo 1299968 2928095 := bstep (se 1 (by rfl) ⟨2196071, by rfl⟩ : syracuseStep 2928095 = 4392143) B4392143
theorem B63262241 : Blo 1299968 63262241 := bstep (se 2 (by rfl) ⟨23723340, by rfl⟩ : syracuseStep 63262241 = 47446681) B47446681
theorem B9875033 : Blo 1299968 9875033 := bstep (se 2 (by rfl) ⟨3703137, by rfl⟩ : syracuseStep 9875033 = 7406275) B7406275
theorem B2928311 : Blo 1299968 2928311 := bstep (se 1 (by rfl) ⟨2196233, by rfl⟩ : syracuseStep 2928311 = 4392467) B4392467
theorem B5271335 : Blo 1299968 5271335 := bstep (se 1 (by rfl) ⟨3953501, by rfl⟩ : syracuseStep 5271335 = 7907003) B7907003
theorem B3518333 : Blo 1299968 3518333 := bstep (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) B1319375
theorem B9375851 : Blo 1299968 9375851 := bstep (se 1 (by rfl) ⟨7031888, by rfl⟩ : syracuseStep 9375851 = 14063777) B14063777
theorem B4935923 : Blo 1299968 4935923 := bstep (se 1 (by rfl) ⟨3701942, by rfl⟩ : syracuseStep 4935923 = 7403885) B7403885
theorem B2470247 : Blo 1299968 2470247 := bstep (se 1 (by rfl) ⟨1852685, by rfl⟩ : syracuseStep 2470247 = 3705371) B3705371
theorem B2929103 : Blo 1299968 2929103 := bstep (se 1 (by rfl) ⟨2196827, by rfl⟩ : syracuseStep 2929103 = 4393655) B4393655
theorem B21402085 : Blo 1299968 21402085 := bstep (se 4 (by rfl) ⟨2006445, by rfl⟩ : syracuseStep 21402085 = 4012891) B4012891
theorem B11874887 : Blo 1299968 11874887 := bstep (se 1 (by rfl) ⟨8906165, by rfl⟩ : syracuseStep 11874887 = 17812331) B17812331
theorem B9376337 : Blo 1299968 9376337 := bstep (se 2 (by rfl) ⟨3516126, by rfl⟩ : syracuseStep 9376337 = 7032253) B7032253
theorem B33329879 : Blo 1299968 33329879 := bstep (se 1 (by rfl) ⟨24997409, by rfl⟩ : syracuseStep 33329879 = 49994819) B49994819
theorem B56251097 : Blo 1299968 56251097 := bstep (se 2 (by rfl) ⟨21094161, by rfl⟩ : syracuseStep 56251097 = 42188323) B42188323
theorem B1463035 : Blo 1299968 1463035 := bstep (se 1 (by rfl) ⟨1097276, by rfl⟩ : syracuseStep 1463035 = 2194553) B2194553
theorem B1389403 : Blo 1299968 1389403 := bstep (se 1 (by rfl) ⟨1042052, by rfl⟩ : syracuseStep 1389403 = 2084105) B2084105
theorem B25007251 : Blo 1299968 25007251 := bstep (se 1 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 25007251 = 37510877) B37510877
theorem B3953819 : Blo 1299968 3953819 := bstep (se 1 (by rfl) ⟨2965364, by rfl⟩ : syracuseStep 3953819 = 5930729) B5930729
theorem B1463791 : Blo 1299968 1463791 := bstep (se 1 (by rfl) ⟨1097843, by rfl⟩ : syracuseStep 1463791 = 2195687) B2195687
theorem B1300059 : Blo 1299968 1300059 := bstep (se 1 (by rfl) ⟨975044, by rfl⟩ : syracuseStep 1300059 = 1950089) B1950089
theorem B1463899 : Blo 1299968 1463899 := bstep (se 1 (by rfl) ⟨1097924, by rfl⟩ : syracuseStep 1463899 = 2195849) B2195849
theorem B1300123 : Blo 1299968 1300123 := bstep (se 1 (by rfl) ⟨975092, by rfl⟩ : syracuseStep 1300123 = 1950185) B1950185
theorem B1300207 : Blo 1299968 1300207 := bstep (se 1 (by rfl) ⟨975155, by rfl⟩ : syracuseStep 1300207 = 1950311) B1950311
theorem B11876129 : Blo 1299968 11876129 := bstep (se 2 (by rfl) ⟨4453548, by rfl⟩ : syracuseStep 11876129 = 8907097) B8907097
theorem B84432689 : Blo 1299968 84432689 := bstep (se 2 (by rfl) ⟨31662258, by rfl⟩ : syracuseStep 84432689 = 63324517) B63324517
theorem B1300295 : Blo 1299968 1300295 := bstep (se 1 (by rfl) ⟨975221, by rfl⟩ : syracuseStep 1300295 = 1950443) B1950443
theorem B4388687 : Blo 1299968 4388687 := bstep (se 1 (by rfl) ⟨3291515, by rfl⟩ : syracuseStep 4388687 = 6583031) B6583031
theorem B1300315 : Blo 1299968 1300315 := bstep (se 1 (by rfl) ⟨975236, by rfl⟩ : syracuseStep 1300315 = 1950473) B1950473
theorem B1464187 : Blo 1299968 1464187 := bstep (se 1 (by rfl) ⟨1098140, by rfl⟩ : syracuseStep 1464187 = 2196281) B2196281
theorem B1300383 : Blo 1299968 1300383 := bstep (se 1 (by rfl) ⟨975287, by rfl⟩ : syracuseStep 1300383 = 1950575) B1950575
theorem B1464223 : Blo 1299968 1464223 := bstep (se 1 (by rfl) ⟨1098167, by rfl⟩ : syracuseStep 1464223 = 2196335) B2196335
theorem B9877463 : Blo 1299968 9877463 := bstep (se 1 (by rfl) ⟨7408097, by rfl⟩ : syracuseStep 9877463 = 14816195) B14816195
theorem B1300551 : Blo 1299968 1300551 := bstep (se 1 (by rfl) ⟨975413, by rfl⟩ : syracuseStep 1300551 = 1950827) B1950827
theorem B1300711 : Blo 1299968 1300711 := bstep (se 1 (by rfl) ⟨975533, by rfl⟩ : syracuseStep 1300711 = 1951067) B1951067
theorem B2504999 : Blo 1299968 2504999 := bstep (se 1 (by rfl) ⟨1878749, by rfl⟩ : syracuseStep 2504999 = 3757499) B3757499
theorem B7412107 : Blo 1299968 7412107 := bstep (se 1 (by rfl) ⟨5559080, by rfl⟩ : syracuseStep 7412107 = 11118161) B11118161
theorem B1300895 : Blo 1299968 1300895 := bstep (se 1 (by rfl) ⟨975671, by rfl⟩ : syracuseStep 1300895 = 1951343) B1951343
theorem B2193871 : Blo 1299968 2193871 := bstep (se 1 (by rfl) ⟨1645403, by rfl⟩ : syracuseStep 2193871 = 3290807) B3290807
theorem B1300943 : Blo 1299968 1300943 := bstep (se 1 (by rfl) ⟨975707, by rfl⟩ : syracuseStep 1300943 = 1951415) B1951415
theorem B1300967 : Blo 1299968 1300967 := bstep (se 1 (by rfl) ⟨975725, by rfl⟩ : syracuseStep 1300967 = 1951451) B1951451
theorem B1301083 : Blo 1299968 1301083 := bstep (se 1 (by rfl) ⟨975812, by rfl⟩ : syracuseStep 1301083 = 1951625) B1951625
theorem B1301151 : Blo 1299968 1301151 := bstep (se 1 (by rfl) ⟨975863, by rfl⟩ : syracuseStep 1301151 = 1951727) B1951727
theorem B1301319 : Blo 1299968 1301319 := bstep (se 1 (by rfl) ⟨975989, by rfl⟩ : syracuseStep 1301319 = 1951979) B1951979
theorem B1301359 : Blo 1299968 1301359 := bstep (se 1 (by rfl) ⟨976019, by rfl⟩ : syracuseStep 1301359 = 1952039) B1952039
theorem B1301415 : Blo 1299968 1301415 := bstep (se 1 (by rfl) ⟨976061, by rfl⟩ : syracuseStep 1301415 = 1952123) B1952123
theorem B3169259 : Blo 1299968 3169259 := bstep (se 1 (by rfl) ⟨2376944, by rfl⟩ : syracuseStep 3169259 = 4753889) B4753889
theorem B1301595 : Blo 1299968 1301595 := bstep (se 1 (by rfl) ⟨976196, by rfl⟩ : syracuseStep 1301595 = 1952393) B1952393
theorem B3292265 : Blo 1299968 3292265 := bstep (se 2 (by rfl) ⟨1234599, by rfl⟩ : syracuseStep 3292265 = 2469199) B2469199
theorem B1301711 : Blo 1299968 1301711 := bstep (se 1 (by rfl) ⟨976283, by rfl⟩ : syracuseStep 1301711 = 1952567) B1952567
theorem B5274839 : Blo 1299968 5274839 := bstep (se 1 (by rfl) ⟨3956129, by rfl⟩ : syracuseStep 5274839 = 7912259) B7912259
theorem B1301735 : Blo 1299968 1301735 := bstep (se 1 (by rfl) ⟨976301, by rfl⟩ : syracuseStep 1301735 = 1952603) B1952603
theorem B1301831 : Blo 1299968 1301831 := bstep (se 1 (by rfl) ⟨976373, by rfl⟩ : syracuseStep 1301831 = 1952747) B1952747
theorem B1301967 : Blo 1299968 1301967 := bstep (se 1 (by rfl) ⟨976475, by rfl⟩ : syracuseStep 1301967 = 1952951) B1952951
theorem B11108015 : Blo 1299968 11108015 := bstep (se 1 (by rfl) ⟨8331011, by rfl⟩ : syracuseStep 11108015 = 16662023) B16662023
theorem B5635759 : Blo 1299968 5635759 := bstep (se 1 (by rfl) ⟨4226819, by rfl⟩ : syracuseStep 5635759 = 8453639) B8453639
theorem B2195167 : Blo 1299968 2195167 := bstep (se 1 (by rfl) ⟨1646375, by rfl⟩ : syracuseStep 2195167 = 3292751) B3292751
theorem B4390631 : Blo 1299968 4390631 := bstep (se 1 (by rfl) ⟨3292973, by rfl⟩ : syracuseStep 4390631 = 6585947) B6585947
theorem B11116385 : Blo 1299968 11116385 := bstep (se 2 (by rfl) ⟨4168644, by rfl⟩ : syracuseStep 11116385 = 8337289) B8337289
theorem B3293095 : Blo 1299968 3293095 := bstep (se 1 (by rfl) ⟨2469821, by rfl⟩ : syracuseStep 3293095 = 4939643) B4939643
theorem B22233041 : Blo 1299968 22233041 := bstep (se 2 (by rfl) ⟨8337390, by rfl⟩ : syracuseStep 22233041 = 16674781) B16674781
theorem B6250567 : Blo 1299968 6250567 := bstep (se 1 (by rfl) ⟨4687925, by rfl⟩ : syracuseStep 6250567 = 9375851) B9375851
theorem B1646831 : Blo 1299968 1646831 := bstep (se 1 (by rfl) ⟨1235123, by rfl⟩ : syracuseStep 1646831 = 2470247) B2470247
theorem B4391225 : Blo 1299968 4391225 := bstep (se 2 (by rfl) ⟨1646709, by rfl⟩ : syracuseStep 4391225 = 3293419) B3293419
theorem B1851751 : Blo 1299968 1851751 := bstep (se 1 (by rfl) ⟨1388813, by rfl⟩ : syracuseStep 1851751 = 2777627) B2777627
theorem B6250891 : Blo 1299968 6250891 := bstep (se 1 (by rfl) ⟨4688168, by rfl⟩ : syracuseStep 6250891 = 9376337) B9376337
theorem B10543517 : Blo 1299968 10543517 := bstep (se 3 (by rfl) ⟨1976909, by rfl⟩ : syracuseStep 10543517 = 3953819) B3953819
theorem B22241789 : Blo 1299968 22241789 := bstep (se 3 (by rfl) ⟨4170335, by rfl⟩ : syracuseStep 22241789 = 8340671) B8340671
theorem B14066237 : Blo 1299968 14066237 := bstep (se 3 (by rfl) ⟨2637419, by rfl⟩ : syracuseStep 14066237 = 5274839) B5274839
theorem B2925161 : Blo 1299968 2925161 := bstep (se 2 (by rfl) ⟨1096935, by rfl⟩ : syracuseStep 2925161 = 2193871) B2193871
theorem B3703457 : Blo 1299968 3703457 := bstep (se 2 (by rfl) ⟨1388796, by rfl⟩ : syracuseStep 3703457 = 2777593) B2777593
theorem B3703583 : Blo 1299968 3703583 := bstep (se 1 (by rfl) ⟨2777687, by rfl⟩ : syracuseStep 3703583 = 5555375) B5555375
theorem B4940585 : Blo 1299968 4940585 := bstep (se 2 (by rfl) ⟨1852719, by rfl⟩ : syracuseStep 4940585 = 3705439) B3705439
theorem B1950587 : Blo 1299968 1950587 := bstep (se 1 (by rfl) ⟨1462940, by rfl⟩ : syracuseStep 1950587 = 2925881) B2925881
theorem B1950713 : Blo 1299968 1950713 := bstep (se 2 (by rfl) ⟨731517, by rfl⟩ : syracuseStep 1950713 = 1463035) B1463035
theorem B1950767 : Blo 1299968 1950767 := bstep (se 1 (by rfl) ⟨1463075, by rfl⟩ : syracuseStep 1950767 = 2926151) B2926151
theorem B2196551 : Blo 1299968 2196551 := bstep (se 1 (by rfl) ⟨1647413, by rfl⟩ : syracuseStep 2196551 = 3294827) B3294827
theorem B1950887 : Blo 1299968 1950887 := bstep (se 1 (by rfl) ⟨1463165, by rfl⟩ : syracuseStep 1950887 = 2926331) B2926331
theorem B3294391 : Blo 1299968 3294391 := bstep (se 1 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 3294391 = 4941587) B4941587
theorem B56288459 : Blo 1299968 56288459 := bstep (se 1 (by rfl) ⟨42216344, by rfl⟩ : syracuseStep 56288459 = 84432689) B84432689
theorem B2925791 : Blo 1299968 2925791 := bstep (se 1 (by rfl) ⟨2194343, by rfl⟩ : syracuseStep 2925791 = 4388687) B4388687
theorem B9372995 : Blo 1299968 9372995 := bstep (se 1 (by rfl) ⟨7029746, by rfl⟩ : syracuseStep 9372995 = 14059493) B14059493
theorem B1951079 : Blo 1299968 1951079 := bstep (se 1 (by rfl) ⟨1463309, by rfl⟩ : syracuseStep 1951079 = 2926619) B2926619
theorem B2196983 : Blo 1299968 2196983 := bstep (se 1 (by rfl) ⟨1647737, by rfl⟩ : syracuseStep 2196983 = 3295475) B3295475
theorem B33343001 : Blo 1299968 33343001 := bstep (se 2 (by rfl) ⟨12503625, by rfl⟩ : syracuseStep 33343001 = 25007251) B25007251
theorem B4392683 : Blo 1299968 4392683 := bstep (se 1 (by rfl) ⟨3294512, by rfl⟩ : syracuseStep 4392683 = 6589025) B6589025
theorem B1951721 : Blo 1299968 1951721 := bstep (se 2 (by rfl) ⟨731895, by rfl⟩ : syracuseStep 1951721 = 1463791) B1463791
theorem B7505945 : Blo 1299968 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B1951865 : Blo 1299968 1951865 := bstep (se 2 (by rfl) ⟨731949, by rfl⟩ : syracuseStep 1951865 = 1463899) B1463899
theorem B7514345 : Blo 1299968 7514345 := bstep (se 2 (by rfl) ⟨2817879, by rfl⟩ : syracuseStep 7514345 = 5635759) B5635759
theorem B4393223 : Blo 1299968 4393223 := bstep (se 1 (by rfl) ⟨3294917, by rfl⟩ : syracuseStep 4393223 = 6589835) B6589835
theorem B2926889 : Blo 1299968 2926889 := bstep (se 2 (by rfl) ⟨1097583, by rfl⟩ : syracuseStep 2926889 = 2195167) B2195167
theorem B1952063 : Blo 1299968 1952063 := bstep (se 1 (by rfl) ⟨1464047, by rfl⟩ : syracuseStep 1952063 = 2928095) B2928095
theorem B42174827 : Blo 1299968 42174827 := bstep (se 1 (by rfl) ⟨31631120, by rfl⟩ : syracuseStep 42174827 = 63262241) B63262241
theorem B3705257 : Blo 1299968 3705257 := bstep (se 2 (by rfl) ⟨1389471, by rfl⟩ : syracuseStep 3705257 = 2778943) B2778943
theorem B1952207 : Blo 1299968 1952207 := bstep (se 1 (by rfl) ⟨1464155, by rfl⟩ : syracuseStep 1952207 = 2928311) B2928311
theorem B2927087 : Blo 1299968 2927087 := bstep (se 1 (by rfl) ⟨2195315, by rfl⟩ : syracuseStep 2927087 = 4390631) B4390631
theorem B1952249 : Blo 1299968 1952249 := bstep (se 2 (by rfl) ⟨732093, by rfl⟩ : syracuseStep 1952249 = 1464187) B1464187
theorem B1952297 : Blo 1299968 1952297 := bstep (se 2 (by rfl) ⟨732111, by rfl⟩ : syracuseStep 1952297 = 1464223) B1464223
theorem B2345555 : Blo 1299968 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B14822027 : Blo 1299968 14822027 := bstep (se 1 (by rfl) ⟨11116520, by rfl⟩ : syracuseStep 14822027 = 22233041) B22233041
theorem B2927519 : Blo 1299968 2927519 := bstep (se 1 (by rfl) ⟨2195639, by rfl⟩ : syracuseStep 2927519 = 4391279) B4391279
theorem B1952735 : Blo 1299968 1952735 := bstep (se 1 (by rfl) ⟨1464551, by rfl⟩ : syracuseStep 1952735 = 2929103) B2929103
theorem B7916591 : Blo 1299968 7916591 := bstep (se 1 (by rfl) ⟨5937443, by rfl⟩ : syracuseStep 7916591 = 11874887) B11874887
theorem B5557373 : Blo 1299968 5557373 := bstep (se 3 (by rfl) ⟨1042007, by rfl⟩ : syracuseStep 5557373 = 2084015) B2084015
theorem B22219919 : Blo 1299968 22219919 := bstep (se 1 (by rfl) ⟨16664939, by rfl⟩ : syracuseStep 22219919 = 33329879) B33329879
theorem B9882809 : Blo 1299968 9882809 := bstep (se 2 (by rfl) ⟨3706053, by rfl⟩ : syracuseStep 9882809 = 7412107) B7412107
theorem B14085419 : Blo 1299968 14085419 := bstep (se 1 (by rfl) ⟨10564064, by rfl⟩ : syracuseStep 14085419 = 21128129) B21128129
theorem B28536113 : Blo 1299968 28536113 := bstep (se 2 (by rfl) ⟨10701042, by rfl⟩ : syracuseStep 28536113 = 21402085) B21402085
theorem B4943227 : Blo 1299968 4943227 := bstep (se 1 (by rfl) ⟨3707420, by rfl⟩ : syracuseStep 4943227 = 7414841) B7414841
theorem B15216133 : Blo 1299968 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B3124927 : Blo 1299968 3124927 := bstep (se 1 (by rfl) ⟨2343695, by rfl⟩ : syracuseStep 3124927 = 4687391) B4687391
theorem B7917419 : Blo 1299968 7917419 := bstep (se 1 (by rfl) ⟨5938064, by rfl⟩ : syracuseStep 7917419 = 11876129) B11876129
theorem B57839521 : Blo 1299968 57839521 := bstep (se 2 (by rfl) ⟨21689820, by rfl⟩ : syracuseStep 57839521 = 43379641) B43379641
theorem B7410149 : Blo 1299968 7410149 := bstep (se 4 (by rfl) ⟨694701, by rfl⟩ : syracuseStep 7410149 = 1389403) B1389403
theorem B43381511 : Blo 1299968 43381511 := bstep (se 1 (by rfl) ⟨32536133, by rfl⟩ : syracuseStep 43381511 = 65072267) B65072267
theorem B6583355 : Blo 1299968 6583355 := bstep (se 1 (by rfl) ⟨4937516, by rfl⟩ : syracuseStep 6583355 = 9875033) B9875033
theorem B7410923 : Blo 1299968 7410923 := bstep (se 1 (by rfl) ⟨5558192, by rfl⟩ : syracuseStep 7410923 = 11116385) B11116385
theorem B7411175 : Blo 1299968 7411175 := bstep (se 1 (by rfl) ⟨5558381, by rfl⟩ : syracuseStep 7411175 = 11116763) B11116763
theorem B3290615 : Blo 1299968 3290615 := bstep (se 1 (by rfl) ⟨2467961, by rfl⟩ : syracuseStep 3290615 = 4935923) B4935923
theorem B1299999 : Blo 1299968 1299999 := bstep (se 1 (by rfl) ⟨974999, by rfl⟩ : syracuseStep 1299999 = 1949999) B1949999
theorem B1300159 : Blo 1299968 1300159 := bstep (se 1 (by rfl) ⟨975119, by rfl⟩ : syracuseStep 1300159 = 1950239) B1950239
theorem B37500731 : Blo 1299968 37500731 := bstep (se 1 (by rfl) ⟨28125548, by rfl⟩ : syracuseStep 37500731 = 56251097) B56251097
theorem B3954575 : Blo 1299968 3954575 := bstep (se 1 (by rfl) ⟨2965931, by rfl⟩ : syracuseStep 3954575 = 5931863) B5931863
theorem B15816829 : Blo 1299968 15816829 := bstep (se 3 (by rfl) ⟨2965655, by rfl⟩ : syracuseStep 15816829 = 5931311) B5931311
theorem B1300607 : Blo 1299968 1300607 := bstep (se 1 (by rfl) ⟨975455, by rfl⟩ : syracuseStep 1300607 = 1950911) B1950911
theorem B4937867 : Blo 1299968 4937867 := bstep (se 1 (by rfl) ⟨3703400, by rfl⟩ : syracuseStep 4937867 = 7406801) B7406801
theorem B1300703 : Blo 1299968 1300703 := bstep (se 1 (by rfl) ⟨975527, by rfl⟩ : syracuseStep 1300703 = 1951055) B1951055
theorem B1300763 : Blo 1299968 1300763 := bstep (se 1 (by rfl) ⟨975572, by rfl⟩ : syracuseStep 1300763 = 1951145) B1951145
theorem B1300863 : Blo 1299968 1300863 := bstep (se 1 (by rfl) ⟨975647, by rfl⟩ : syracuseStep 1300863 = 1951295) B1951295
theorem B1300891 : Blo 1299968 1300891 := bstep (se 1 (by rfl) ⟨975668, by rfl⟩ : syracuseStep 1300891 = 1951337) B1951337
theorem B8239585 : Blo 1299968 8239585 := bstep (se 2 (by rfl) ⟨3089844, by rfl⟩ : syracuseStep 8239585 = 6179689) B6179689
theorem B6584975 : Blo 1299968 6584975 := bstep (se 1 (by rfl) ⟨4938731, by rfl⟩ : syracuseStep 6584975 = 9877463) B9877463
theorem B1301183 : Blo 1299968 1301183 := bstep (se 1 (by rfl) ⟨975887, by rfl⟩ : syracuseStep 1301183 = 1951775) B1951775
theorem B1301311 : Blo 1299968 1301311 := bstep (se 1 (by rfl) ⟨975983, by rfl⟩ : syracuseStep 1301311 = 1951967) B1951967
theorem B1301351 : Blo 1299968 1301351 := bstep (se 1 (by rfl) ⟨976013, by rfl⟩ : syracuseStep 1301351 = 1952027) B1952027
theorem B1669999 : Blo 1299968 1669999 := bstep (se 1 (by rfl) ⟨1252499, by rfl⟩ : syracuseStep 1669999 = 2504999) B2504999
theorem B1301567 : Blo 1299968 1301567 := bstep (se 1 (by rfl) ⟨976175, by rfl⟩ : syracuseStep 1301567 = 1952351) B1952351
theorem B1301755 : Blo 1299968 1301755 := bstep (se 1 (by rfl) ⟨976316, by rfl⟩ : syracuseStep 1301755 = 1952633) B1952633
theorem B1301787 : Blo 1299968 1301787 := bstep (se 1 (by rfl) ⟨976340, by rfl⟩ : syracuseStep 1301787 = 1952681) B1952681
theorem B2112839 : Blo 1299968 2112839 := bstep (se 1 (by rfl) ⟨1584629, by rfl⟩ : syracuseStep 2112839 = 3169259) B3169259
theorem B1301887 : Blo 1299968 1301887 := bstep (se 1 (by rfl) ⟨976415, by rfl⟩ : syracuseStep 1301887 = 1952831) B1952831
theorem B2194843 : Blo 1299968 2194843 := bstep (se 1 (by rfl) ⟨1646132, by rfl⟩ : syracuseStep 2194843 = 3292265) B3292265
theorem B85614097 : Blo 1299968 85614097 := bstep (se 2 (by rfl) ⟨32105286, by rfl⟩ : syracuseStep 85614097 = 64210573) B64210573
theorem B1646183 : Blo 1299968 1646183 := bstep (se 1 (by rfl) ⟨1234637, by rfl⟩ : syracuseStep 1646183 = 2469275) B2469275
theorem B7405343 : Blo 1299968 7405343 := bstep (se 1 (by rfl) ⟨5554007, by rfl⟩ : syracuseStep 7405343 = 11108015) B11108015
theorem B3514223 : Blo 1299968 3514223 := bstep (se 1 (by rfl) ⟨2635667, by rfl⟩ : syracuseStep 3514223 = 5271335) B5271335
theorem B4390793 : Blo 1299968 4390793 := bstep (se 2 (by rfl) ⟨1646547, by rfl⟩ : syracuseStep 4390793 = 3293095) B3293095
theorem B7029011 : Blo 1299968 7029011 := bstep (se 1 (by rfl) ⟨5271758, by rfl⟩ : syracuseStep 7029011 = 10543517) B10543517
theorem B4940099 : Blo 1299968 4940099 := bstep (se 1 (by rfl) ⟨3705074, by rfl⟩ : syracuseStep 4940099 = 7410149) B7410149
theorem B14827859 : Blo 1299968 14827859 := bstep (se 1 (by rfl) ⟨11120894, by rfl⟩ : syracuseStep 14827859 = 22241789) B22241789
theorem B1950107 : Blo 1299968 1950107 := bstep (se 1 (by rfl) ⟨1462580, by rfl⟩ : syracuseStep 1950107 = 2925161) B2925161
theorem B3293723 : Blo 1299968 3293723 := bstep (se 1 (by rfl) ⟨2470292, by rfl⟩ : syracuseStep 3293723 = 4940585) B4940585
theorem B4391549 : Blo 1299968 4391549 := bstep (se 3 (by rfl) ⟨823415, by rfl⟩ : syracuseStep 4391549 = 1646831) B1646831
theorem B10986113 : Blo 1299968 10986113 := bstep (se 2 (by rfl) ⟨4119792, by rfl⟩ : syracuseStep 10986113 = 8239585) B8239585
theorem B37561117 : Blo 1299968 37561117 := bstep (se 3 (by rfl) ⟨7042709, by rfl⟩ : syracuseStep 37561117 = 14085419) B14085419
theorem B1950527 : Blo 1299968 1950527 := bstep (se 1 (by rfl) ⟨1462895, by rfl⟩ : syracuseStep 1950527 = 2925791) B2925791
theorem B4940615 : Blo 1299968 4940615 := bstep (se 1 (by rfl) ⟨3705461, by rfl⟩ : syracuseStep 4940615 = 7410923) B7410923
theorem B4940783 : Blo 1299968 4940783 := bstep (se 1 (by rfl) ⟨3705587, by rfl⟩ : syracuseStep 4940783 = 7411175) B7411175
theorem B1951259 : Blo 1299968 1951259 := bstep (se 1 (by rfl) ⟨1463444, by rfl⟩ : syracuseStep 1951259 = 2926889) B2926889
theorem B28116551 : Blo 1299968 28116551 := bstep (se 1 (by rfl) ⟨21087413, by rfl⟩ : syracuseStep 28116551 = 42174827) B42174827
theorem B4392521 : Blo 1299968 4392521 := bstep (se 2 (by rfl) ⟨1647195, by rfl⟩ : syracuseStep 4392521 = 3294391) B3294391
theorem B1951391 : Blo 1299968 1951391 := bstep (se 1 (by rfl) ⟨1463543, by rfl⟩ : syracuseStep 1951391 = 2927087) B2927087
theorem B9881351 : Blo 1299968 9881351 := bstep (se 1 (by rfl) ⟨7411013, by rfl⟩ : syracuseStep 9881351 = 14822027) B14822027
theorem B2926457 : Blo 1299968 2926457 := bstep (se 2 (by rfl) ⟨1097421, by rfl⟩ : syracuseStep 2926457 = 2194843) B2194843
theorem B1951679 : Blo 1299968 1951679 := bstep (se 1 (by rfl) ⟨1463759, by rfl⟩ : syracuseStep 1951679 = 2927519) B2927519
theorem B5277727 : Blo 1299968 5277727 := bstep (se 1 (by rfl) ⟨3958295, by rfl⟩ : syracuseStep 5277727 = 7916591) B7916591
theorem B3704915 : Blo 1299968 3704915 := bstep (se 1 (by rfl) ⟨2778686, by rfl⟩ : syracuseStep 3704915 = 5557373) B5557373
theorem B14813279 : Blo 1299968 14813279 := bstep (se 1 (by rfl) ⟨11109959, by rfl⟩ : syracuseStep 14813279 = 22219919) B22219919
theorem B6588539 : Blo 1299968 6588539 := bstep (se 1 (by rfl) ⟨4941404, by rfl⟩ : syracuseStep 6588539 = 9882809) B9882809
theorem B19024075 : Blo 1299968 19024075 := bstep (se 1 (by rfl) ⟨14268056, by rfl⟩ : syracuseStep 19024075 = 28536113) B28536113
theorem B5278279 : Blo 1299968 5278279 := bstep (se 1 (by rfl) ⟨3958709, by rfl⟩ : syracuseStep 5278279 = 7917419) B7917419
theorem B2927195 : Blo 1299968 2927195 := bstep (se 1 (by rfl) ⟨2195396, by rfl⟩ : syracuseStep 2927195 = 4390793) B4390793
theorem B8334089 : Blo 1299968 8334089 := bstep (se 2 (by rfl) ⟨3125283, by rfl⟩ : syracuseStep 8334089 = 6250567) B6250567
theorem B21089105 : Blo 1299968 21089105 := bstep (se 2 (by rfl) ⟨7908414, by rfl⟩ : syracuseStep 21089105 = 15816829) B15816829
theorem B2927483 : Blo 1299968 2927483 := bstep (se 1 (by rfl) ⟨2195612, by rfl⟩ : syracuseStep 2927483 = 4391225) B4391225
theorem B2468971 : Blo 1299968 2468971 := bstep (se 1 (by rfl) ⟨1851728, by rfl⟩ : syracuseStep 2468971 = 3703457) B3703457
theorem B28921007 : Blo 1299968 28921007 := bstep (se 1 (by rfl) ⟨21690755, by rfl⟩ : syracuseStep 28921007 = 43381511) B43381511
theorem B8334521 : Blo 1299968 8334521 := bstep (se 2 (by rfl) ⟨3125445, by rfl⟩ : syracuseStep 8334521 = 6250891) B6250891
theorem B2469055 : Blo 1299968 2469055 := bstep (se 1 (by rfl) ⟨1851791, by rfl⟩ : syracuseStep 2469055 = 3703583) B3703583
theorem B22228667 : Blo 1299968 22228667 := bstep (se 1 (by rfl) ⟨16671500, by rfl⟩ : syracuseStep 22228667 = 33343001) B33343001
theorem B2928455 : Blo 1299968 2928455 := bstep (se 1 (by rfl) ⟨2196341, by rfl⟩ : syracuseStep 2928455 = 4392683) B4392683
theorem B5009563 : Blo 1299968 5009563 := bstep (se 1 (by rfl) ⟨3757172, by rfl⟩ : syracuseStep 5009563 = 7514345) B7514345
theorem B2928815 : Blo 1299968 2928815 := bstep (se 1 (by rfl) ⟨2196611, by rfl⟩ : syracuseStep 2928815 = 4393223) B4393223
theorem B6254813 : Blo 1299968 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B2470171 : Blo 1299968 2470171 := bstep (se 1 (by rfl) ⟨1852628, by rfl⟩ : syracuseStep 2470171 = 3705257) B3705257
theorem B6590969 : Blo 1299968 6590969 := bstep (se 2 (by rfl) ⟨2471613, by rfl⟩ : syracuseStep 6590969 = 4943227) B4943227
theorem B9876005 : Blo 1299968 9876005 := bstep (se 4 (by rfl) ⟨925875, by rfl⟩ : syracuseStep 9876005 = 1851751) B1851751
theorem B20288177 : Blo 1299968 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B114152129 : Blo 1299968 114152129 := bstep (se 2 (by rfl) ⟨42807048, by rfl⟩ : syracuseStep 114152129 = 85614097) B85614097
theorem B4166569 : Blo 1299968 4166569 := bstep (se 2 (by rfl) ⟨1562463, by rfl⟩ : syracuseStep 4166569 = 3124927) B3124927
theorem B4936895 : Blo 1299968 4936895 := bstep (se 1 (by rfl) ⟨3702671, by rfl⟩ : syracuseStep 4936895 = 7405343) B7405343
theorem B9377491 : Blo 1299968 9377491 := bstep (se 1 (by rfl) ⟨7033118, by rfl⟩ : syracuseStep 9377491 = 14066237) B14066237
theorem B1300391 : Blo 1299968 1300391 := bstep (se 1 (by rfl) ⟨975293, by rfl⟩ : syracuseStep 1300391 = 1950587) B1950587
theorem B1300475 : Blo 1299968 1300475 := bstep (se 1 (by rfl) ⟨975356, by rfl⟩ : syracuseStep 1300475 = 1950713) B1950713
theorem B1300511 : Blo 1299968 1300511 := bstep (se 1 (by rfl) ⟨975383, by rfl⟩ : syracuseStep 1300511 = 1950767) B1950767
theorem B4388903 : Blo 1299968 4388903 := bstep (se 1 (by rfl) ⟨3291677, by rfl⟩ : syracuseStep 4388903 = 6583355) B6583355
theorem B1464367 : Blo 1299968 1464367 := bstep (se 1 (by rfl) ⟨1098275, by rfl⟩ : syracuseStep 1464367 = 2196551) B2196551
theorem B1300591 : Blo 1299968 1300591 := bstep (se 1 (by rfl) ⟨975443, by rfl⟩ : syracuseStep 1300591 = 1950887) B1950887
theorem B37525639 : Blo 1299968 37525639 := bstep (se 1 (by rfl) ⟨28144229, by rfl⟩ : syracuseStep 37525639 = 56288459) B56288459
theorem B6248663 : Blo 1299968 6248663 := bstep (se 1 (by rfl) ⟨4686497, by rfl⟩ : syracuseStep 6248663 = 9372995) B9372995
theorem B1300719 : Blo 1299968 1300719 := bstep (se 1 (by rfl) ⟨975539, by rfl⟩ : syracuseStep 1300719 = 1951079) B1951079
theorem B2193743 : Blo 1299968 2193743 := bstep (se 1 (by rfl) ⟨1645307, by rfl⟩ : syracuseStep 2193743 = 3290615) B3290615
theorem B1464655 : Blo 1299968 1464655 := bstep (se 1 (by rfl) ⟨1098491, by rfl⟩ : syracuseStep 1464655 = 2196983) B2196983
theorem B2226665 : Blo 1299968 2226665 := bstep (se 2 (by rfl) ⟨834999, by rfl⟩ : syracuseStep 2226665 = 1669999) B1669999
theorem B25000487 : Blo 1299968 25000487 := bstep (se 1 (by rfl) ⟨18750365, by rfl⟩ : syracuseStep 25000487 = 37500731) B37500731
theorem B2636383 : Blo 1299968 2636383 := bstep (se 1 (by rfl) ⟨1977287, by rfl⟩ : syracuseStep 2636383 = 3954575) B3954575
theorem B1301147 : Blo 1299968 1301147 := bstep (se 1 (by rfl) ⟨975860, by rfl⟩ : syracuseStep 1301147 = 1951721) B1951721
theorem B5003963 : Blo 1299968 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B1301243 : Blo 1299968 1301243 := bstep (se 1 (by rfl) ⟨975932, by rfl⟩ : syracuseStep 1301243 = 1951865) B1951865
theorem B3291911 : Blo 1299968 3291911 := bstep (se 1 (by rfl) ⟨2468933, by rfl⟩ : syracuseStep 3291911 = 4937867) B4937867
theorem B1301375 : Blo 1299968 1301375 := bstep (se 1 (by rfl) ⟨976031, by rfl⟩ : syracuseStep 1301375 = 1952063) B1952063
theorem B4389821 : Blo 1299968 4389821 := bstep (se 3 (by rfl) ⟨823091, by rfl⟩ : syracuseStep 4389821 = 1646183) B1646183
theorem B1301471 : Blo 1299968 1301471 := bstep (se 1 (by rfl) ⟨976103, by rfl⟩ : syracuseStep 1301471 = 1952207) B1952207
theorem B1301499 : Blo 1299968 1301499 := bstep (se 1 (by rfl) ⟨976124, by rfl⟩ : syracuseStep 1301499 = 1952249) B1952249
theorem B1301531 : Blo 1299968 1301531 := bstep (se 1 (by rfl) ⟨976148, by rfl⟩ : syracuseStep 1301531 = 1952297) B1952297
theorem B4389983 : Blo 1299968 4389983 := bstep (se 1 (by rfl) ⟨3292487, by rfl⟩ : syracuseStep 4389983 = 6584975) B6584975
theorem B1301823 : Blo 1299968 1301823 := bstep (se 1 (by rfl) ⟨976367, by rfl⟩ : syracuseStep 1301823 = 1952735) B1952735
theorem B1408559 : Blo 1299968 1408559 := bstep (se 1 (by rfl) ⟨1056419, by rfl⟩ : syracuseStep 1408559 = 2112839) B2112839
theorem B9371261 : Blo 1299968 9371261 := bstep (se 3 (by rfl) ⟨1757111, by rfl⟩ : syracuseStep 9371261 = 3514223) B3514223
theorem B77119361 : Blo 1299968 77119361 := bstep (se 2 (by rfl) ⟨28919760, by rfl⟩ : syracuseStep 77119361 = 57839521) B57839521
theorem B7036969 : Blo 1299968 7036969 := bstep (se 2 (by rfl) ⟨2638863, by rfl⟩ : syracuseStep 7036969 = 5277727) B5277727
theorem B4169875 : Blo 1299968 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B4686007 : Blo 1299968 4686007 := bstep (se 1 (by rfl) ⟨3514505, by rfl⟩ : syracuseStep 4686007 = 7029011) B7029011
theorem B3293399 : Blo 1299968 3293399 := bstep (se 1 (by rfl) ⟨2470049, by rfl⟩ : syracuseStep 3293399 = 4940099) B4940099
theorem B2195815 : Blo 1299968 2195815 := bstep (se 1 (by rfl) ⟨1646861, by rfl⟩ : syracuseStep 2195815 = 3293723) B3293723
theorem B3293561 : Blo 1299968 3293561 := bstep (se 2 (by rfl) ⟨1235085, by rfl⟩ : syracuseStep 3293561 = 2470171) B2470171
theorem B7324075 : Blo 1299968 7324075 := bstep (se 1 (by rfl) ⟨5493056, by rfl⟩ : syracuseStep 7324075 = 10986113) B10986113
theorem B13525451 : Blo 1299968 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B15024629 : Blo 1299968 15024629 := bstep (se 5 (by rfl) ⟨704279, by rfl⟩ : syracuseStep 15024629 = 1408559) B1408559
theorem B3293743 : Blo 1299968 3293743 := bstep (se 1 (by rfl) ⟨2470307, by rfl⟩ : syracuseStep 3293743 = 4940615) B4940615
theorem B3293855 : Blo 1299968 3293855 := bstep (se 1 (by rfl) ⟨2470391, by rfl⟩ : syracuseStep 3293855 = 4940783) B4940783
theorem B7037705 : Blo 1299968 7037705 := bstep (se 2 (by rfl) ⟨2639139, by rfl⟩ : syracuseStep 7037705 = 5278279) B5278279
theorem B3515177 : Blo 1299968 3515177 := bstep (se 2 (by rfl) ⟨1318191, by rfl⟩ : syracuseStep 3515177 = 2636383) B2636383
theorem B18744367 : Blo 1299968 18744367 := bstep (se 1 (by rfl) ⟨14058275, by rfl⟩ : syracuseStep 18744367 = 28116551) B28116551
theorem B6587567 : Blo 1299968 6587567 := bstep (se 1 (by rfl) ⟨4940675, by rfl⟩ : syracuseStep 6587567 = 9881351) B9881351
theorem B5555425 : Blo 1299968 5555425 := bstep (se 2 (by rfl) ⟨2083284, by rfl⟩ : syracuseStep 5555425 = 4166569) B4166569
theorem B1950971 : Blo 1299968 1950971 := bstep (se 1 (by rfl) ⟨1463228, by rfl⟩ : syracuseStep 1950971 = 2926457) B2926457
theorem B2925935 : Blo 1299968 2925935 := bstep (se 1 (by rfl) ⟨2194451, by rfl⟩ : syracuseStep 2925935 = 4388903) B4388903
theorem B4392359 : Blo 1299968 4392359 := bstep (se 1 (by rfl) ⟨3294269, by rfl⟩ : syracuseStep 4392359 = 6588539) B6588539
theorem B1484443 : Blo 1299968 1484443 := bstep (se 1 (by rfl) ⟨1113332, by rfl⟩ : syracuseStep 1484443 = 2226665) B2226665
theorem B1951463 : Blo 1299968 1951463 := bstep (se 1 (by rfl) ⟨1463597, by rfl⟩ : syracuseStep 1951463 = 2927195) B2927195
theorem B3335975 : Blo 1299968 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B5556059 : Blo 1299968 5556059 := bstep (se 1 (by rfl) ⟨4167044, by rfl⟩ : syracuseStep 5556059 = 8334089) B8334089
theorem B14059403 : Blo 1299968 14059403 := bstep (se 1 (by rfl) ⟨10544552, by rfl⟩ : syracuseStep 14059403 = 21089105) B21089105
theorem B1951655 : Blo 1299968 1951655 := bstep (se 1 (by rfl) ⟨1463741, by rfl⟩ : syracuseStep 1951655 = 2927483) B2927483
theorem B2926547 : Blo 1299968 2926547 := bstep (se 1 (by rfl) ⟨2194910, by rfl⟩ : syracuseStep 2926547 = 4389821) B4389821
theorem B2926655 : Blo 1299968 2926655 := bstep (se 1 (by rfl) ⟨2194991, by rfl⟩ : syracuseStep 2926655 = 4389983) B4389983
theorem B5556347 : Blo 1299968 5556347 := bstep (se 1 (by rfl) ⟨4167260, by rfl⟩ : syracuseStep 5556347 = 8334521) B8334521
theorem B12503321 : Blo 1299968 12503321 := bstep (se 2 (by rfl) ⟨4688745, by rfl⟩ : syracuseStep 12503321 = 9377491) B9377491
theorem B1952303 : Blo 1299968 1952303 := bstep (se 1 (by rfl) ⟨1464227, by rfl⟩ : syracuseStep 1952303 = 2928455) B2928455
theorem B1952489 : Blo 1299968 1952489 := bstep (se 2 (by rfl) ⟨732183, by rfl⟩ : syracuseStep 1952489 = 1464367) B1464367
theorem B1952543 : Blo 1299968 1952543 := bstep (se 1 (by rfl) ⟨1464407, by rfl⟩ : syracuseStep 1952543 = 2928815) B2928815
theorem B6679417 : Blo 1299968 6679417 := bstep (se 2 (by rfl) ⟨2504781, by rfl⟩ : syracuseStep 6679417 = 5009563) B5009563
theorem B4393979 : Blo 1299968 4393979 := bstep (se 1 (by rfl) ⟨3295484, by rfl⟩ : syracuseStep 4393979 = 6590969) B6590969
theorem B2927699 : Blo 1299968 2927699 := bstep (se 1 (by rfl) ⟨2195774, by rfl⟩ : syracuseStep 2927699 = 4391549) B4391549
theorem B1952873 : Blo 1299968 1952873 := bstep (se 2 (by rfl) ⟨732327, by rfl⟩ : syracuseStep 1952873 = 1464655) B1464655
theorem B77122685 : Blo 1299968 77122685 := bstep (se 3 (by rfl) ⟨14460503, by rfl⟩ : syracuseStep 77122685 = 28921007) B28921007
theorem B50081489 : Blo 1299968 50081489 := bstep (se 2 (by rfl) ⟨18780558, by rfl⟩ : syracuseStep 50081489 = 37561117) B37561117
theorem B2928347 : Blo 1299968 2928347 := bstep (se 1 (by rfl) ⟨2196260, by rfl⟩ : syracuseStep 2928347 = 4392521) B4392521
theorem B101461733 : Blo 1299968 101461733 := bstep (se 4 (by rfl) ⟨9512037, by rfl⟩ : syracuseStep 101461733 = 19024075) B19024075
theorem B2469943 : Blo 1299968 2469943 := bstep (se 1 (by rfl) ⟨1852457, by rfl⟩ : syracuseStep 2469943 = 3704915) B3704915
theorem B9875519 : Blo 1299968 9875519 := bstep (se 1 (by rfl) ⟨7406639, by rfl⟩ : syracuseStep 9875519 = 14813279) B14813279
theorem B4165775 : Blo 1299968 4165775 := bstep (se 1 (by rfl) ⟨3124331, by rfl⟩ : syracuseStep 4165775 = 6248663) B6248663
theorem B1462495 : Blo 1299968 1462495 := bstep (se 1 (by rfl) ⟨1096871, by rfl⟩ : syracuseStep 1462495 = 2193743) B2193743
theorem B24990029 : Blo 1299968 24990029 := bstep (se 3 (by rfl) ⟨4685630, by rfl⟩ : syracuseStep 24990029 = 9371261) B9371261
theorem B16666991 : Blo 1299968 16666991 := bstep (se 1 (by rfl) ⟨12500243, by rfl⟩ : syracuseStep 16666991 = 25000487) B25000487
theorem B50034185 : Blo 1299968 50034185 := bstep (se 2 (by rfl) ⟨18762819, by rfl⟩ : syracuseStep 50034185 = 37525639) B37525639
theorem B9885239 : Blo 1299968 9885239 := bstep (se 1 (by rfl) ⟨7413929, by rfl⟩ : syracuseStep 9885239 = 14827859) B14827859
theorem B1300071 : Blo 1299968 1300071 := bstep (se 1 (by rfl) ⟨975053, by rfl⟩ : syracuseStep 1300071 = 1950107) B1950107
theorem B6584003 : Blo 1299968 6584003 := bstep (se 1 (by rfl) ⟨4938002, by rfl⟩ : syracuseStep 6584003 = 9876005) B9876005
theorem B76101419 : Blo 1299968 76101419 := bstep (se 1 (by rfl) ⟨57076064, by rfl⟩ : syracuseStep 76101419 = 114152129) B114152129
theorem B1300351 : Blo 1299968 1300351 := bstep (se 1 (by rfl) ⟨975263, by rfl⟩ : syracuseStep 1300351 = 1950527) B1950527
theorem B3291263 : Blo 1299968 3291263 := bstep (se 1 (by rfl) ⟨2468447, by rfl⟩ : syracuseStep 3291263 = 4936895) B4936895
theorem B1300839 : Blo 1299968 1300839 := bstep (se 1 (by rfl) ⟨975629, by rfl⟩ : syracuseStep 1300839 = 1951259) B1951259
theorem B1300927 : Blo 1299968 1300927 := bstep (se 1 (by rfl) ⟨975695, by rfl⟩ : syracuseStep 1300927 = 1951391) B1951391
theorem B1301119 : Blo 1299968 1301119 := bstep (se 1 (by rfl) ⟨975839, by rfl⟩ : syracuseStep 1301119 = 1951679) B1951679
theorem B3291961 : Blo 1299968 3291961 := bstep (se 2 (by rfl) ⟨1234485, by rfl⟩ : syracuseStep 3291961 = 2468971) B2468971
theorem B3292073 : Blo 1299968 3292073 := bstep (se 2 (by rfl) ⟨1234527, by rfl⟩ : syracuseStep 3292073 = 2469055) B2469055
theorem B2194607 : Blo 1299968 2194607 := bstep (se 1 (by rfl) ⟨1645955, by rfl⟩ : syracuseStep 2194607 = 3291911) B3291911
theorem B14819111 : Blo 1299968 14819111 := bstep (se 1 (by rfl) ⟨11114333, by rfl⟩ : syracuseStep 14819111 = 22228667) B22228667
theorem B51412907 : Blo 1299968 51412907 := bstep (se 1 (by rfl) ⟨38559680, by rfl⟩ : syracuseStep 51412907 = 77119361) B77119361
theorem B3293257 : Blo 1299968 3293257 := bstep (se 2 (by rfl) ⟨1234971, by rfl⟩ : syracuseStep 3293257 = 2469943) B2469943
theorem B2777183 : Blo 1299968 2777183 := bstep (se 1 (by rfl) ⟨2082887, by rfl⟩ : syracuseStep 2777183 = 4165775) B4165775
theorem B2195599 : Blo 1299968 2195599 := bstep (se 1 (by rfl) ⟨1646699, by rfl⟩ : syracuseStep 2195599 = 3293399) B3293399
theorem B2195707 : Blo 1299968 2195707 := bstep (se 1 (by rfl) ⟨1646780, by rfl⟩ : syracuseStep 2195707 = 3293561) B3293561
theorem B1949993 : Blo 1299968 1949993 := bstep (se 2 (by rfl) ⟨731247, by rfl⟩ : syracuseStep 1949993 = 1462495) B1462495
theorem B2195903 : Blo 1299968 2195903 := bstep (se 1 (by rfl) ⟨1646927, by rfl⟩ : syracuseStep 2195903 = 3293855) B3293855
theorem B2343451 : Blo 1299968 2343451 := bstep (se 1 (by rfl) ⟨1757588, by rfl⟩ : syracuseStep 2343451 = 3515177) B3515177
theorem B9765433 : Blo 1299968 9765433 := bstep (se 2 (by rfl) ⟨3662037, by rfl⟩ : syracuseStep 9765433 = 7324075) B7324075
theorem B4391657 : Blo 1299968 4391657 := bstep (se 2 (by rfl) ⟨1646871, by rfl⟩ : syracuseStep 4391657 = 3293743) B3293743
theorem B4391711 : Blo 1299968 4391711 := bstep (se 1 (by rfl) ⟨3293783, by rfl⟩ : syracuseStep 4391711 = 6587567) B6587567
theorem B1950623 : Blo 1299968 1950623 := bstep (se 1 (by rfl) ⟨1462967, by rfl⟩ : syracuseStep 1950623 = 2925935) B2925935
theorem B8905889 : Blo 1299968 8905889 := bstep (se 2 (by rfl) ⟨3339708, by rfl⟩ : syracuseStep 8905889 = 6679417) B6679417
theorem B50734279 : Blo 1299968 50734279 := bstep (se 1 (by rfl) ⟨38050709, by rfl⟩ : syracuseStep 50734279 = 76101419) B76101419
theorem B3704039 : Blo 1299968 3704039 := bstep (se 1 (by rfl) ⟨2778029, by rfl⟩ : syracuseStep 3704039 = 5556059) B5556059
theorem B9372935 : Blo 1299968 9372935 := bstep (se 1 (by rfl) ⟨7029701, by rfl⟩ : syracuseStep 9372935 = 14059403) B14059403
theorem B1951031 : Blo 1299968 1951031 := bstep (se 1 (by rfl) ⟨1463273, by rfl⟩ : syracuseStep 1951031 = 2926547) B2926547
theorem B1951103 : Blo 1299968 1951103 := bstep (se 1 (by rfl) ⟨1463327, by rfl⟩ : syracuseStep 1951103 = 2926655) B2926655
theorem B3704231 : Blo 1299968 3704231 := bstep (se 1 (by rfl) ⟨2778173, by rfl⟩ : syracuseStep 3704231 = 5556347) B5556347
theorem B7407233 : Blo 1299968 7407233 := bstep (se 2 (by rfl) ⟨2777712, by rfl⟩ : syracuseStep 7407233 = 5555425) B5555425
theorem B1951799 : Blo 1299968 1951799 := bstep (se 1 (by rfl) ⟨1463849, by rfl⟩ : syracuseStep 1951799 = 2927699) B2927699
theorem B51415123 : Blo 1299968 51415123 := bstep (se 1 (by rfl) ⟨38561342, by rfl⟩ : syracuseStep 51415123 = 77122685) B77122685
theorem B1952231 : Blo 1299968 1952231 := bstep (se 1 (by rfl) ⟨1464173, by rfl⟩ : syracuseStep 1952231 = 2928347) B2928347
theorem B9382625 : Blo 1299968 9382625 := bstep (se 2 (by rfl) ⟨3518484, by rfl⟩ : syracuseStep 9382625 = 7036969) B7036969
theorem B11111327 : Blo 1299968 11111327 := bstep (se 1 (by rfl) ⟨8333495, by rfl⟩ : syracuseStep 11111327 = 16666991) B16666991
theorem B2927753 : Blo 1299968 2927753 := bstep (se 2 (by rfl) ⟨1097907, by rfl⟩ : syracuseStep 2927753 = 2195815) B2195815
theorem B2928239 : Blo 1299968 2928239 := bstep (se 1 (by rfl) ⟨2196179, by rfl⟩ : syracuseStep 2928239 = 4392359) B4392359
theorem B6590159 : Blo 1299968 6590159 := bstep (se 1 (by rfl) ⟨4942619, by rfl⟩ : syracuseStep 6590159 = 9885239) B9885239
theorem B2223983 : Blo 1299968 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B8335547 : Blo 1299968 8335547 := bstep (se 1 (by rfl) ⟨6251660, by rfl⟩ : syracuseStep 8335547 = 12503321) B12503321
theorem B2929319 : Blo 1299968 2929319 := bstep (se 1 (by rfl) ⟨2196989, by rfl⟩ : syracuseStep 2929319 = 4393979) B4393979
theorem B1463071 : Blo 1299968 1463071 := bstep (se 1 (by rfl) ⟨1097303, by rfl⟩ : syracuseStep 1463071 = 2194607) B2194607
theorem B1979257 : Blo 1299968 1979257 := bstep (se 2 (by rfl) ⟨742221, by rfl⟩ : syracuseStep 1979257 = 1484443) B1484443
theorem B33387659 : Blo 1299968 33387659 := bstep (se 1 (by rfl) ⟨25040744, by rfl⟩ : syracuseStep 33387659 = 50081489) B50081489
theorem B6583679 : Blo 1299968 6583679 := bstep (se 1 (by rfl) ⟨4937759, by rfl⟩ : syracuseStep 6583679 = 9875519) B9875519
theorem B5559833 : Blo 1299968 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B16660019 : Blo 1299968 16660019 := bstep (se 1 (by rfl) ⟨12495014, by rfl⟩ : syracuseStep 16660019 = 24990029) B24990029
theorem B6248009 : Blo 1299968 6248009 := bstep (se 2 (by rfl) ⟨2343003, by rfl⟩ : syracuseStep 6248009 = 4686007) B4686007
theorem B9016967 : Blo 1299968 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B10016419 : Blo 1299968 10016419 := bstep (se 1 (by rfl) ⟨7512314, by rfl⟩ : syracuseStep 10016419 = 15024629) B15024629
theorem B4691803 : Blo 1299968 4691803 := bstep (se 1 (by rfl) ⟨3518852, by rfl⟩ : syracuseStep 4691803 = 7037705) B7037705
theorem B1300647 : Blo 1299968 1300647 := bstep (se 1 (by rfl) ⟨975485, by rfl⟩ : syracuseStep 1300647 = 1950971) B1950971
theorem B33356123 : Blo 1299968 33356123 := bstep (se 1 (by rfl) ⟨25017092, by rfl⟩ : syracuseStep 33356123 = 50034185) B50034185
theorem B4389281 : Blo 1299968 4389281 := bstep (se 2 (by rfl) ⟨1645980, by rfl⟩ : syracuseStep 4389281 = 3291961) B3291961
theorem B4389335 : Blo 1299968 4389335 := bstep (se 1 (by rfl) ⟨3292001, by rfl⟩ : syracuseStep 4389335 = 6584003) B6584003
theorem B1300975 : Blo 1299968 1300975 := bstep (se 1 (by rfl) ⟨975731, by rfl⟩ : syracuseStep 1300975 = 1951463) B1951463
theorem B1301103 : Blo 1299968 1301103 := bstep (se 1 (by rfl) ⟨975827, by rfl⟩ : syracuseStep 1301103 = 1951655) B1951655
theorem B24992489 : Blo 1299968 24992489 := bstep (se 2 (by rfl) ⟨9372183, by rfl⟩ : syracuseStep 24992489 = 18744367) B18744367
theorem B2194175 : Blo 1299968 2194175 := bstep (se 1 (by rfl) ⟨1645631, by rfl⟩ : syracuseStep 2194175 = 3291263) B3291263
theorem B1301535 : Blo 1299968 1301535 := bstep (se 1 (by rfl) ⟨976151, by rfl⟩ : syracuseStep 1301535 = 1952303) B1952303
theorem B1301659 : Blo 1299968 1301659 := bstep (se 1 (by rfl) ⟨976244, by rfl⟩ : syracuseStep 1301659 = 1952489) B1952489
theorem B1301695 : Blo 1299968 1301695 := bstep (se 1 (by rfl) ⟨976271, by rfl⟩ : syracuseStep 1301695 = 1952543) B1952543
theorem B2194715 : Blo 1299968 2194715 := bstep (se 1 (by rfl) ⟨1646036, by rfl⟩ : syracuseStep 2194715 = 3292073) B3292073
theorem B1301915 : Blo 1299968 1301915 := bstep (se 1 (by rfl) ⟨976436, by rfl⟩ : syracuseStep 1301915 = 1952873) B1952873
theorem B137101085 : Blo 1299968 137101085 := bstep (se 3 (by rfl) ⟨25706453, by rfl⟩ : syracuseStep 137101085 = 51412907) B51412907
theorem B67641155 : Blo 1299968 67641155 := bstep (se 1 (by rfl) ⟨50730866, by rfl⟩ : syracuseStep 67641155 = 101461733) B101461733
theorem B9879407 : Blo 1299968 9879407 := bstep (se 1 (by rfl) ⟨7409555, by rfl⟩ : syracuseStep 9879407 = 14819111) B14819111
theorem B1851455 : Blo 1299968 1851455 := bstep (se 1 (by rfl) ⟨1388591, by rfl⟩ : syracuseStep 1851455 = 2777183) B2777183
theorem B4391009 : Blo 1299968 4391009 := bstep (se 2 (by rfl) ⟨1646628, by rfl⟩ : syracuseStep 4391009 = 3293257) B3293257
theorem B24994493 : Blo 1299968 24994493 := bstep (se 3 (by rfl) ⟨4686467, by rfl⟩ : syracuseStep 24994493 = 9372935) B9372935
theorem B22258439 : Blo 1299968 22258439 := bstep (se 1 (by rfl) ⟨16693829, by rfl⟩ : syracuseStep 22258439 = 33387659) B33387659
theorem B1950761 : Blo 1299968 1950761 := bstep (se 2 (by rfl) ⟨731535, by rfl⟩ : syracuseStep 1950761 = 1463071) B1463071
theorem B2639009 : Blo 1299968 2639009 := bstep (se 2 (by rfl) ⟨989628, by rfl⟩ : syracuseStep 2639009 = 1979257) B1979257
theorem B2926187 : Blo 1299968 2926187 := bstep (se 1 (by rfl) ⟨2194640, by rfl⟩ : syracuseStep 2926187 = 4389281) B4389281
theorem B2926223 : Blo 1299968 2926223 := bstep (se 1 (by rfl) ⟨2194667, by rfl⟩ : syracuseStep 2926223 = 4389335) B4389335
theorem B24045245 : Blo 1299968 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B7407551 : Blo 1299968 7407551 := bstep (se 1 (by rfl) ⟨5555663, by rfl⟩ : syracuseStep 7407551 = 11111327) B11111327
theorem B1951835 : Blo 1299968 1951835 := bstep (se 1 (by rfl) ⟨1463876, by rfl⟩ : syracuseStep 1951835 = 2927753) B2927753
theorem B13355225 : Blo 1299968 13355225 := bstep (se 2 (by rfl) ⟨5008209, by rfl⟩ : syracuseStep 13355225 = 10016419) B10016419
theorem B1952159 : Blo 1299968 1952159 := bstep (se 1 (by rfl) ⟨1464119, by rfl⟩ : syracuseStep 1952159 = 2928239) B2928239
theorem B4393439 : Blo 1299968 4393439 := bstep (se 1 (by rfl) ⟨3295079, by rfl⟩ : syracuseStep 4393439 = 6590159) B6590159
theorem B91400723 : Blo 1299968 91400723 := bstep (se 1 (by rfl) ⟨68550542, by rfl⟩ : syracuseStep 91400723 = 137101085) B137101085
theorem B68553497 : Blo 1299968 68553497 := bstep (se 2 (by rfl) ⟨25707561, by rfl⟩ : syracuseStep 68553497 = 51415123) B51415123
theorem B5557031 : Blo 1299968 5557031 := bstep (se 1 (by rfl) ⟨4167773, by rfl⟩ : syracuseStep 5557031 = 8335547) B8335547
theorem B2927465 : Blo 1299968 2927465 := bstep (se 2 (by rfl) ⟨1097799, by rfl⟩ : syracuseStep 2927465 = 2195599) B2195599
theorem B2927609 : Blo 1299968 2927609 := bstep (se 2 (by rfl) ⟨1097853, by rfl⟩ : syracuseStep 2927609 = 2195707) B2195707
theorem B1952879 : Blo 1299968 1952879 := bstep (se 1 (by rfl) ⟨1464659, by rfl⟩ : syracuseStep 1952879 = 2929319) B2929319
theorem B2927771 : Blo 1299968 2927771 := bstep (se 1 (by rfl) ⟨2195828, by rfl⟩ : syracuseStep 2927771 = 4391657) B4391657
theorem B2927807 : Blo 1299968 2927807 := bstep (se 1 (by rfl) ⟨2195855, by rfl⟩ : syracuseStep 2927807 = 4391711) B4391711
theorem B3124601 : Blo 1299968 3124601 := bstep (se 2 (by rfl) ⟨1171725, by rfl⟩ : syracuseStep 3124601 = 2343451) B2343451
theorem B13020577 : Blo 1299968 13020577 := bstep (se 2 (by rfl) ⟨4882716, by rfl⟩ : syracuseStep 13020577 = 9765433) B9765433
theorem B2469359 : Blo 1299968 2469359 := bstep (se 1 (by rfl) ⟨1852019, by rfl⟩ : syracuseStep 2469359 = 3704039) B3704039
theorem B3706555 : Blo 1299968 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B4165339 : Blo 1299968 4165339 := bstep (se 1 (by rfl) ⟨3124004, by rfl⟩ : syracuseStep 4165339 = 6248009) B6248009
theorem B22237415 : Blo 1299968 22237415 := bstep (se 1 (by rfl) ⟨16678061, by rfl⟩ : syracuseStep 22237415 = 33356123) B33356123
theorem B67645705 : Blo 1299968 67645705 := bstep (se 2 (by rfl) ⟨25367139, by rfl⟩ : syracuseStep 67645705 = 50734279) B50734279
theorem B6255083 : Blo 1299968 6255083 := bstep (se 1 (by rfl) ⟨4691312, by rfl⟩ : syracuseStep 6255083 = 9382625) B9382625
theorem B1462783 : Blo 1299968 1462783 := bstep (se 1 (by rfl) ⟨1097087, by rfl⟩ : syracuseStep 1462783 = 2194175) B2194175
theorem B1463143 : Blo 1299968 1463143 := bstep (se 1 (by rfl) ⟨1097357, by rfl⟩ : syracuseStep 1463143 = 2194715) B2194715
theorem B6255737 : Blo 1299968 6255737 := bstep (se 2 (by rfl) ⟨2345901, by rfl⟩ : syracuseStep 6255737 = 4691803) B4691803
theorem B45094103 : Blo 1299968 45094103 := bstep (se 1 (by rfl) ⟨33820577, by rfl⟩ : syracuseStep 45094103 = 67641155) B67641155
theorem B1299995 : Blo 1299968 1299995 := bstep (se 1 (by rfl) ⟨974996, by rfl⟩ : syracuseStep 1299995 = 1949993) B1949993
theorem B1463935 : Blo 1299968 1463935 := bstep (se 1 (by rfl) ⟨1097951, by rfl⟩ : syracuseStep 1463935 = 2195903) B2195903
theorem B1300415 : Blo 1299968 1300415 := bstep (se 1 (by rfl) ⟨975311, by rfl⟩ : syracuseStep 1300415 = 1950623) B1950623
theorem B5937259 : Blo 1299968 5937259 := bstep (se 1 (by rfl) ⟨4452944, by rfl⟩ : syracuseStep 5937259 = 8905889) B8905889
theorem B1300687 : Blo 1299968 1300687 := bstep (se 1 (by rfl) ⟨975515, by rfl⟩ : syracuseStep 1300687 = 1951031) B1951031
theorem B4389119 : Blo 1299968 4389119 := bstep (se 1 (by rfl) ⟨3291839, by rfl⟩ : syracuseStep 4389119 = 6583679) B6583679
theorem B1300735 : Blo 1299968 1300735 := bstep (se 1 (by rfl) ⟨975551, by rfl⟩ : syracuseStep 1300735 = 1951103) B1951103
theorem B11106679 : Blo 1299968 11106679 := bstep (se 1 (by rfl) ⟨8330009, by rfl⟩ : syracuseStep 11106679 = 16660019) B16660019
theorem B4938155 : Blo 1299968 4938155 := bstep (se 1 (by rfl) ⟨3703616, by rfl⟩ : syracuseStep 4938155 = 7407233) B7407233
theorem B9877949 : Blo 1299968 9877949 := bstep (se 3 (by rfl) ⟨1852115, by rfl⟩ : syracuseStep 9877949 = 3704231) B3704231
theorem B1301199 : Blo 1299968 1301199 := bstep (se 1 (by rfl) ⟨975899, by rfl⟩ : syracuseStep 1301199 = 1951799) B1951799
theorem B1301487 : Blo 1299968 1301487 := bstep (se 1 (by rfl) ⟨976115, by rfl⟩ : syracuseStep 1301487 = 1952231) B1952231
theorem B16661659 : Blo 1299968 16661659 := bstep (se 1 (by rfl) ⟨12496244, by rfl⟩ : syracuseStep 16661659 = 24992489) B24992489
theorem B5930621 : Blo 1299968 5930621 := bstep (se 3 (by rfl) ⟨1111991, by rfl⟩ : syracuseStep 5930621 = 2223983) B2223983
theorem B6586271 : Blo 1299968 6586271 := bstep (se 1 (by rfl) ⟨4939703, by rfl⟩ : syracuseStep 6586271 = 9879407) B9879407
theorem B4170055 : Blo 1299968 4170055 := bstep (se 1 (by rfl) ⟨3127541, by rfl⟩ : syracuseStep 4170055 = 6255083) B6255083
theorem B90194273 : Blo 1299968 90194273 := bstep (se 2 (by rfl) ⟨33822852, by rfl⟩ : syracuseStep 90194273 = 67645705) B67645705
theorem B16662995 : Blo 1299968 16662995 := bstep (se 1 (by rfl) ⟨12497246, by rfl⟩ : syracuseStep 16662995 = 24994493) B24994493
theorem B1950377 : Blo 1299968 1950377 := bstep (se 2 (by rfl) ⟨731391, by rfl⟩ : syracuseStep 1950377 = 1462783) B1462783
theorem B4170491 : Blo 1299968 4170491 := bstep (se 1 (by rfl) ⟨3127868, by rfl⟩ : syracuseStep 4170491 = 6255737) B6255737
theorem B1950791 : Blo 1299968 1950791 := bstep (se 1 (by rfl) ⟨1463093, by rfl⟩ : syracuseStep 1950791 = 2926187) B2926187
theorem B1950815 : Blo 1299968 1950815 := bstep (se 1 (by rfl) ⟨1463111, by rfl⟩ : syracuseStep 1950815 = 2926223) B2926223
theorem B1950857 : Blo 1299968 1950857 := bstep (se 2 (by rfl) ⟨731571, by rfl⟩ : syracuseStep 1950857 = 1463143) B1463143
theorem B2926079 : Blo 1299968 2926079 := bstep (se 1 (by rfl) ⟨2194559, by rfl⟩ : syracuseStep 2926079 = 4389119) B4389119
theorem B60933815 : Blo 1299968 60933815 := bstep (se 1 (by rfl) ⟨45700361, by rfl⟩ : syracuseStep 60933815 = 91400723) B91400723
theorem B3704687 : Blo 1299968 3704687 := bstep (se 1 (by rfl) ⟨2778515, by rfl⟩ : syracuseStep 3704687 = 5557031) B5557031
theorem B1951643 : Blo 1299968 1951643 := bstep (se 1 (by rfl) ⟨1463732, by rfl⟩ : syracuseStep 1951643 = 2927465) B2927465
theorem B1951739 : Blo 1299968 1951739 := bstep (se 1 (by rfl) ⟨1463804, by rfl⟩ : syracuseStep 1951739 = 2927609) B2927609
theorem B1951847 : Blo 1299968 1951847 := bstep (se 1 (by rfl) ⟨1463885, by rfl⟩ : syracuseStep 1951847 = 2927771) B2927771
theorem B1951871 : Blo 1299968 1951871 := bstep (se 1 (by rfl) ⟨1463903, by rfl⟩ : syracuseStep 1951871 = 2927807) B2927807
theorem B1951913 : Blo 1299968 1951913 := bstep (se 2 (by rfl) ⟨731967, by rfl⟩ : syracuseStep 1951913 = 1463935) B1463935
theorem B4942073 : Blo 1299968 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B2083067 : Blo 1299968 2083067 := bstep (se 1 (by rfl) ⟨1562300, by rfl⟩ : syracuseStep 2083067 = 3124601) B3124601
theorem B2927339 : Blo 1299968 2927339 := bstep (se 1 (by rfl) ⟨2195504, by rfl⟩ : syracuseStep 2927339 = 4391009) B4391009
theorem B7916345 : Blo 1299968 7916345 := bstep (se 2 (by rfl) ⟨2968629, by rfl⟩ : syracuseStep 7916345 = 5937259) B5937259
theorem B14838959 : Blo 1299968 14838959 := bstep (se 1 (by rfl) ⟨11129219, by rfl⟩ : syracuseStep 14838959 = 22258439) B22258439
theorem B2928959 : Blo 1299968 2928959 := bstep (se 1 (by rfl) ⟨2196719, by rfl⟩ : syracuseStep 2928959 = 4393439) B4393439
theorem B182809325 : Blo 1299968 182809325 := bstep (se 3 (by rfl) ⟨34276748, by rfl⟩ : syracuseStep 182809325 = 68553497) B68553497
theorem B3953747 : Blo 1299968 3953747 := bstep (se 1 (by rfl) ⟨2965310, by rfl⟩ : syracuseStep 3953747 = 5930621) B5930621
theorem B14824943 : Blo 1299968 14824943 := bstep (se 1 (by rfl) ⟨11118707, by rfl⟩ : syracuseStep 14824943 = 22237415) B22237415
theorem B4937213 : Blo 1299968 4937213 := bstep (se 3 (by rfl) ⟨925727, by rfl⟩ : syracuseStep 4937213 = 1851455) B1851455
theorem B14808905 : Blo 1299968 14808905 := bstep (se 2 (by rfl) ⟨5553339, by rfl⟩ : syracuseStep 14808905 = 11106679) B11106679
theorem B1300507 : Blo 1299968 1300507 := bstep (se 1 (by rfl) ⟨975380, by rfl⟩ : syracuseStep 1300507 = 1950761) B1950761
theorem B1759339 : Blo 1299968 1759339 := bstep (se 1 (by rfl) ⟨1319504, by rfl⟩ : syracuseStep 1759339 = 2639009) B2639009
theorem B30062735 : Blo 1299968 30062735 := bstep (se 1 (by rfl) ⟨22547051, by rfl⟩ : syracuseStep 30062735 = 45094103) B45094103
theorem B16030163 : Blo 1299968 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B4938367 : Blo 1299968 4938367 := bstep (se 1 (by rfl) ⟨3703775, by rfl⟩ : syracuseStep 4938367 = 7407551) B7407551
theorem B1301223 : Blo 1299968 1301223 := bstep (se 1 (by rfl) ⟨975917, by rfl⟩ : syracuseStep 1301223 = 1951835) B1951835
theorem B8903483 : Blo 1299968 8903483 := bstep (se 1 (by rfl) ⟨6677612, by rfl⟩ : syracuseStep 8903483 = 13355225) B13355225
theorem B22215545 : Blo 1299968 22215545 := bstep (se 2 (by rfl) ⟨8330829, by rfl⟩ : syracuseStep 22215545 = 16661659) B16661659
theorem B1301439 : Blo 1299968 1301439 := bstep (se 1 (by rfl) ⟨976079, by rfl⟩ : syracuseStep 1301439 = 1952159) B1952159
theorem B3292103 : Blo 1299968 3292103 := bstep (se 1 (by rfl) ⟨2469077, by rfl⟩ : syracuseStep 3292103 = 4938155) B4938155
theorem B6585299 : Blo 1299968 6585299 := bstep (se 1 (by rfl) ⟨4938974, by rfl⟩ : syracuseStep 6585299 = 9877949) B9877949
theorem B1301919 : Blo 1299968 1301919 := bstep (se 1 (by rfl) ⟨976439, by rfl⟩ : syracuseStep 1301919 = 1952879) B1952879
theorem B69443077 : Blo 1299968 69443077 := bstep (se 4 (by rfl) ⟨6510288, by rfl⟩ : syracuseStep 69443077 = 13020577) B13020577
theorem B5553785 : Blo 1299968 5553785 := bstep (se 2 (by rfl) ⟨2082669, by rfl⟩ : syracuseStep 5553785 = 4165339) B4165339
theorem B1646239 : Blo 1299968 1646239 := bstep (se 1 (by rfl) ⟨1234679, by rfl⟩ : syracuseStep 1646239 = 2469359) B2469359
theorem B4390847 : Blo 1299968 4390847 := bstep (se 1 (by rfl) ⟨3293135, by rfl⟩ : syracuseStep 4390847 = 6586271) B6586271
theorem B60129515 : Blo 1299968 60129515 := bstep (se 1 (by rfl) ⟨45097136, by rfl⟩ : syracuseStep 60129515 = 90194273) B90194273
theorem B11108663 : Blo 1299968 11108663 := bstep (se 1 (by rfl) ⟨8331497, by rfl⟩ : syracuseStep 11108663 = 16662995) B16662995
theorem B121872883 : Blo 1299968 121872883 := bstep (se 1 (by rfl) ⟨91404662, by rfl⟩ : syracuseStep 121872883 = 182809325) B182809325
theorem B1950719 : Blo 1299968 1950719 := bstep (se 1 (by rfl) ⟨1463039, by rfl⟩ : syracuseStep 1950719 = 2926079) B2926079
theorem B9872603 : Blo 1299968 9872603 := bstep (se 1 (by rfl) ⟨7404452, by rfl⟩ : syracuseStep 9872603 = 14808905) B14808905
theorem B42747101 : Blo 1299968 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B3294715 : Blo 1299968 3294715 := bstep (se 1 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 3294715 = 4942073) B4942073
theorem B1951559 : Blo 1299968 1951559 := bstep (se 1 (by rfl) ⟨1463669, by rfl⟩ : syracuseStep 1951559 = 2927339) B2927339
theorem B5277563 : Blo 1299968 5277563 := bstep (se 1 (by rfl) ⟨3958172, by rfl⟩ : syracuseStep 5277563 = 7916345) B7916345
theorem B2927231 : Blo 1299968 2927231 := bstep (se 1 (by rfl) ⟨2195423, by rfl⟩ : syracuseStep 2927231 = 4390847) B4390847
theorem B1952639 : Blo 1299968 1952639 := bstep (se 1 (by rfl) ⟨1464479, by rfl⟩ : syracuseStep 1952639 = 2928959) B2928959
theorem B2780327 : Blo 1299968 2780327 := bstep (se 1 (by rfl) ⟨2085245, by rfl⟩ : syracuseStep 2780327 = 4170491) B4170491
theorem B9383141 : Blo 1299968 9383141 := bstep (se 4 (by rfl) ⟨879669, by rfl⟩ : syracuseStep 9383141 = 1759339) B1759339
theorem B9883295 : Blo 1299968 9883295 := bstep (se 1 (by rfl) ⟨7412471, by rfl⟩ : syracuseStep 9883295 = 14824943) B14824943
theorem B2469791 : Blo 1299968 2469791 := bstep (se 1 (by rfl) ⟨1852343, by rfl⟩ : syracuseStep 2469791 = 3704687) B3704687
theorem B20041823 : Blo 1299968 20041823 := bstep (se 1 (by rfl) ⟨15031367, by rfl⟩ : syracuseStep 20041823 = 30062735) B30062735
theorem B1388711 : Blo 1299968 1388711 := bstep (se 1 (by rfl) ⟨1041533, by rfl⟩ : syracuseStep 1388711 = 2083067) B2083067
theorem B5935655 : Blo 1299968 5935655 := bstep (se 1 (by rfl) ⟨4451741, by rfl⟩ : syracuseStep 5935655 = 8903483) B8903483
theorem B92590769 : Blo 1299968 92590769 := bstep (se 2 (by rfl) ⟨34721538, by rfl⟩ : syracuseStep 92590769 = 69443077) B69443077
theorem B9892639 : Blo 1299968 9892639 := bstep (se 1 (by rfl) ⟨7419479, by rfl⟩ : syracuseStep 9892639 = 14838959) B14838959
theorem B5560073 : Blo 1299968 5560073 := bstep (se 2 (by rfl) ⟨2085027, by rfl⟩ : syracuseStep 5560073 = 4170055) B4170055
theorem B1300251 : Blo 1299968 1300251 := bstep (se 1 (by rfl) ⟨975188, by rfl⟩ : syracuseStep 1300251 = 1950377) B1950377
theorem B1300527 : Blo 1299968 1300527 := bstep (se 1 (by rfl) ⟨975395, by rfl⟩ : syracuseStep 1300527 = 1950791) B1950791
theorem B2635831 : Blo 1299968 2635831 := bstep (se 1 (by rfl) ⟨1976873, by rfl⟩ : syracuseStep 2635831 = 3953747) B3953747
theorem B1300543 : Blo 1299968 1300543 := bstep (se 1 (by rfl) ⟨975407, by rfl⟩ : syracuseStep 1300543 = 1950815) B1950815
theorem B1300571 : Blo 1299968 1300571 := bstep (se 1 (by rfl) ⟨975428, by rfl⟩ : syracuseStep 1300571 = 1950857) B1950857
theorem B6584489 : Blo 1299968 6584489 := bstep (se 2 (by rfl) ⟨2469183, by rfl⟩ : syracuseStep 6584489 = 4938367) B4938367
theorem B3291475 : Blo 1299968 3291475 := bstep (se 1 (by rfl) ⟨2468606, by rfl⟩ : syracuseStep 3291475 = 4937213) B4937213
theorem B40622543 : Blo 1299968 40622543 := bstep (se 1 (by rfl) ⟨30466907, by rfl⟩ : syracuseStep 40622543 = 60933815) B60933815
theorem B1301095 : Blo 1299968 1301095 := bstep (se 1 (by rfl) ⟨975821, by rfl⟩ : syracuseStep 1301095 = 1951643) B1951643
theorem B1301159 : Blo 1299968 1301159 := bstep (se 1 (by rfl) ⟨975869, by rfl⟩ : syracuseStep 1301159 = 1951739) B1951739
theorem B1301231 : Blo 1299968 1301231 := bstep (se 1 (by rfl) ⟨975923, by rfl⟩ : syracuseStep 1301231 = 1951847) B1951847
theorem B1301247 : Blo 1299968 1301247 := bstep (se 1 (by rfl) ⟨975935, by rfl⟩ : syracuseStep 1301247 = 1951871) B1951871
theorem B1301275 : Blo 1299968 1301275 := bstep (se 1 (by rfl) ⟨975956, by rfl⟩ : syracuseStep 1301275 = 1951913) B1951913
theorem B14810363 : Blo 1299968 14810363 := bstep (se 1 (by rfl) ⟨11107772, by rfl⟩ : syracuseStep 14810363 = 22215545) B22215545
theorem B2194735 : Blo 1299968 2194735 := bstep (se 1 (by rfl) ⟨1646051, by rfl⟩ : syracuseStep 2194735 = 3292103) B3292103
theorem B4390199 : Blo 1299968 4390199 := bstep (se 1 (by rfl) ⟨3292649, by rfl⟩ : syracuseStep 4390199 = 6585299) B6585299
theorem B2194985 : Blo 1299968 2194985 := bstep (se 2 (by rfl) ⟨823119, by rfl⟩ : syracuseStep 2194985 = 1646239) B1646239
theorem B3702523 : Blo 1299968 3702523 := bstep (se 1 (by rfl) ⟨2776892, by rfl⟩ : syracuseStep 3702523 = 5553785) B5553785
theorem B13361215 : Blo 1299968 13361215 := bstep (se 1 (by rfl) ⟨10020911, by rfl⟩ : syracuseStep 13361215 = 20041823) B20041823
theorem B3514441 : Blo 1299968 3514441 := bstep (se 2 (by rfl) ⟨1317915, by rfl⟩ : syracuseStep 3514441 = 2635831) B2635831
theorem B7405775 : Blo 1299968 7405775 := bstep (se 1 (by rfl) ⟨5554331, by rfl⟩ : syracuseStep 7405775 = 11108663) B11108663
theorem B3957103 : Blo 1299968 3957103 := bstep (se 1 (by rfl) ⟨2967827, by rfl⟩ : syracuseStep 3957103 = 5935655) B5935655
theorem B3703229 : Blo 1299968 3703229 := bstep (se 3 (by rfl) ⟨694355, by rfl⟩ : syracuseStep 3703229 = 1388711) B1388711
theorem B61727179 : Blo 1299968 61727179 := bstep (se 1 (by rfl) ⟨46295384, by rfl⟩ : syracuseStep 61727179 = 92590769) B92590769
theorem B162497177 : Blo 1299968 162497177 := bstep (se 2 (by rfl) ⟨60936441, by rfl⟩ : syracuseStep 162497177 = 121872883) B121872883
theorem B2926313 : Blo 1299968 2926313 := bstep (se 2 (by rfl) ⟨1097367, by rfl⟩ : syracuseStep 2926313 = 2194735) B2194735
theorem B1951487 : Blo 1299968 1951487 := bstep (se 1 (by rfl) ⟨1463615, by rfl⟩ : syracuseStep 1951487 = 2927231) B2927231
theorem B4392953 : Blo 1299968 4392953 := bstep (se 2 (by rfl) ⟨1647357, by rfl⟩ : syracuseStep 4392953 = 3294715) B3294715
theorem B1853551 : Blo 1299968 1853551 := bstep (se 1 (by rfl) ⟨1390163, by rfl⟩ : syracuseStep 1853551 = 2780327) B2780327
theorem B9873575 : Blo 1299968 9873575 := bstep (se 1 (by rfl) ⟨7405181, by rfl⟩ : syracuseStep 9873575 = 14810363) B14810363
theorem B2926799 : Blo 1299968 2926799 := bstep (se 1 (by rfl) ⟨2195099, by rfl⟩ : syracuseStep 2926799 = 4390199) B4390199
theorem B6588863 : Blo 1299968 6588863 := bstep (se 1 (by rfl) ⟨4941647, by rfl⟩ : syracuseStep 6588863 = 9883295) B9883295
theorem B40086343 : Blo 1299968 40086343 := bstep (se 1 (by rfl) ⟨30064757, by rfl⟩ : syracuseStep 40086343 = 60129515) B60129515
theorem B25021709 : Blo 1299968 25021709 := bstep (se 3 (by rfl) ⟨4691570, by rfl⟩ : syracuseStep 25021709 = 9383141) B9383141
theorem B6581735 : Blo 1299968 6581735 := bstep (se 1 (by rfl) ⟨4936301, by rfl⟩ : syracuseStep 6581735 = 9872603) B9872603
theorem B3706715 : Blo 1299968 3706715 := bstep (se 1 (by rfl) ⟨2780036, by rfl⟩ : syracuseStep 3706715 = 5560073) B5560073
theorem B3518375 : Blo 1299968 3518375 := bstep (se 1 (by rfl) ⟨2638781, by rfl⟩ : syracuseStep 3518375 = 5277563) B5277563
theorem B52760741 : Blo 1299968 52760741 := bstep (se 4 (by rfl) ⟨4946319, by rfl⟩ : syracuseStep 52760741 = 9892639) B9892639
theorem B4936697 : Blo 1299968 4936697 := bstep (se 2 (by rfl) ⟨1851261, by rfl⟩ : syracuseStep 4936697 = 3702523) B3702523
theorem B1463323 : Blo 1299968 1463323 := bstep (se 1 (by rfl) ⟨1097492, by rfl⟩ : syracuseStep 1463323 = 2194985) B2194985
theorem B4388633 : Blo 1299968 4388633 := bstep (se 2 (by rfl) ⟨1645737, by rfl⟩ : syracuseStep 4388633 = 3291475) B3291475
theorem B1300479 : Blo 1299968 1300479 := bstep (se 1 (by rfl) ⟨975359, by rfl⟩ : syracuseStep 1300479 = 1950719) B1950719
theorem B28498067 : Blo 1299968 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B1301039 : Blo 1299968 1301039 := bstep (se 1 (by rfl) ⟨975779, by rfl⟩ : syracuseStep 1301039 = 1951559) B1951559
theorem B4389659 : Blo 1299968 4389659 := bstep (se 1 (by rfl) ⟨3292244, by rfl⟩ : syracuseStep 4389659 = 6584489) B6584489
theorem B27081695 : Blo 1299968 27081695 := bstep (se 1 (by rfl) ⟨20311271, by rfl⟩ : syracuseStep 27081695 = 40622543) B40622543
theorem B1301759 : Blo 1299968 1301759 := bstep (se 1 (by rfl) ⟨976319, by rfl⟩ : syracuseStep 1301759 = 1952639) B1952639
theorem B6586109 : Blo 1299968 6586109 := bstep (se 3 (by rfl) ⟨1234895, by rfl⟩ : syracuseStep 6586109 = 2469791) B2469791
theorem B4685921 : Blo 1299968 4685921 := bstep (se 2 (by rfl) ⟨1757220, by rfl⟩ : syracuseStep 4685921 = 3514441) B3514441
theorem B108331451 : Blo 1299968 108331451 := bstep (se 1 (by rfl) ⟨81248588, by rfl⟩ : syracuseStep 108331451 = 162497177) B162497177
theorem B1950875 : Blo 1299968 1950875 := bstep (se 1 (by rfl) ⟨1463156, by rfl⟩ : syracuseStep 1950875 = 2926313) B2926313
theorem B2925755 : Blo 1299968 2925755 := bstep (se 1 (by rfl) ⟨2194316, by rfl⟩ : syracuseStep 2925755 = 4388633) B4388633
theorem B1951097 : Blo 1299968 1951097 := bstep (se 2 (by rfl) ⟨731661, by rfl⟩ : syracuseStep 1951097 = 1463323) B1463323
theorem B18998711 : Blo 1299968 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B1951199 : Blo 1299968 1951199 := bstep (se 1 (by rfl) ⟨1463399, by rfl⟩ : syracuseStep 1951199 = 2926799) B2926799
theorem B4392575 : Blo 1299968 4392575 := bstep (se 1 (by rfl) ⟨3294431, by rfl⟩ : syracuseStep 4392575 = 6588863) B6588863
theorem B2926439 : Blo 1299968 2926439 := bstep (se 1 (by rfl) ⟨2194829, by rfl⟩ : syracuseStep 2926439 = 4389659) B4389659
theorem B21104549 : Blo 1299968 21104549 := bstep (se 4 (by rfl) ⟨1978551, by rfl⟩ : syracuseStep 21104549 = 3957103) B3957103
theorem B16681139 : Blo 1299968 16681139 := bstep (se 1 (by rfl) ⟨12510854, by rfl⟩ : syracuseStep 16681139 = 25021709) B25021709
theorem B9382333 : Blo 1299968 9382333 := bstep (se 3 (by rfl) ⟨1759187, by rfl⟩ : syracuseStep 9382333 = 3518375) B3518375
theorem B2468819 : Blo 1299968 2468819 := bstep (se 1 (by rfl) ⟨1851614, by rfl⟩ : syracuseStep 2468819 = 3703229) B3703229
theorem B2928635 : Blo 1299968 2928635 := bstep (se 1 (by rfl) ⟨2196476, by rfl⟩ : syracuseStep 2928635 = 4392953) B4392953
theorem B6582383 : Blo 1299968 6582383 := bstep (se 1 (by rfl) ⟨4936787, by rfl⟩ : syracuseStep 6582383 = 9873575) B9873575
theorem B4387823 : Blo 1299968 4387823 := bstep (se 1 (by rfl) ⟨3290867, by rfl⟩ : syracuseStep 4387823 = 6581735) B6581735
theorem B2471143 : Blo 1299968 2471143 := bstep (se 1 (by rfl) ⟨1853357, by rfl⟩ : syracuseStep 2471143 = 3706715) B3706715
theorem B17814953 : Blo 1299968 17814953 := bstep (se 2 (by rfl) ⟨6680607, by rfl⟩ : syracuseStep 17814953 = 13361215) B13361215
theorem B4937183 : Blo 1299968 4937183 := bstep (se 1 (by rfl) ⟨3702887, by rfl⟩ : syracuseStep 4937183 = 7405775) B7405775
theorem B2471401 : Blo 1299968 2471401 := bstep (se 2 (by rfl) ⟨926775, by rfl⟩ : syracuseStep 2471401 = 1853551) B1853551
theorem B140695309 : Blo 1299968 140695309 := bstep (se 3 (by rfl) ⟨26380370, by rfl⟩ : syracuseStep 140695309 = 52760741) B52760741
theorem B82302905 : Blo 1299968 82302905 := bstep (se 2 (by rfl) ⟨30863589, by rfl⟩ : syracuseStep 82302905 = 61727179) B61727179
theorem B3291131 : Blo 1299968 3291131 := bstep (se 1 (by rfl) ⟨2468348, by rfl⟩ : syracuseStep 3291131 = 4936697) B4936697
theorem B1300991 : Blo 1299968 1300991 := bstep (se 1 (by rfl) ⟨975743, by rfl⟩ : syracuseStep 1300991 = 1951487) B1951487
theorem B213793829 : Blo 1299968 213793829 := bstep (se 4 (by rfl) ⟨20043171, by rfl⟩ : syracuseStep 213793829 = 40086343) B40086343
theorem B18054463 : Blo 1299968 18054463 := bstep (se 1 (by rfl) ⟨13540847, by rfl⟩ : syracuseStep 18054463 = 27081695) B27081695
theorem B4390739 : Blo 1299968 4390739 := bstep (se 1 (by rfl) ⟨3293054, by rfl⟩ : syracuseStep 4390739 = 6586109) B6586109
theorem B72220967 : Blo 1299968 72220967 := bstep (se 1 (by rfl) ⟨54165725, by rfl⟩ : syracuseStep 72220967 = 108331451) B108331451
theorem B12509777 : Blo 1299968 12509777 := bstep (se 2 (by rfl) ⟨4691166, by rfl⟩ : syracuseStep 12509777 = 9382333) B9382333
theorem B2925215 : Blo 1299968 2925215 := bstep (se 1 (by rfl) ⟨2193911, by rfl⟩ : syracuseStep 2925215 = 4387823) B4387823
theorem B1950503 : Blo 1299968 1950503 := bstep (se 1 (by rfl) ⟨1462877, by rfl⟩ : syracuseStep 1950503 = 2925755) B2925755
theorem B12665807 : Blo 1299968 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B1950959 : Blo 1299968 1950959 := bstep (se 1 (by rfl) ⟨1463219, by rfl⟩ : syracuseStep 1950959 = 2926439) B2926439
theorem B3294857 : Blo 1299968 3294857 := bstep (se 2 (by rfl) ⟨1235571, by rfl⟩ : syracuseStep 3294857 = 2471143) B2471143
theorem B3295201 : Blo 1299968 3295201 := bstep (se 2 (by rfl) ⟨1235700, by rfl⟩ : syracuseStep 3295201 = 2471401) B2471401
theorem B2927159 : Blo 1299968 2927159 := bstep (se 1 (by rfl) ⟨2195369, by rfl⟩ : syracuseStep 2927159 = 4390739) B4390739
theorem B1952423 : Blo 1299968 1952423 := bstep (se 1 (by rfl) ⟨1464317, by rfl⟩ : syracuseStep 1952423 = 2928635) B2928635
theorem B3123947 : Blo 1299968 3123947 := bstep (se 1 (by rfl) ⟨2342960, by rfl⟩ : syracuseStep 3123947 = 4685921) B4685921
theorem B2928383 : Blo 1299968 2928383 := bstep (se 1 (by rfl) ⟨2196287, by rfl⟩ : syracuseStep 2928383 = 4392575) B4392575
theorem B14069699 : Blo 1299968 14069699 := bstep (se 1 (by rfl) ⟨10552274, by rfl⟩ : syracuseStep 14069699 = 21104549) B21104549
theorem B11120759 : Blo 1299968 11120759 := bstep (se 1 (by rfl) ⟨8340569, by rfl⟩ : syracuseStep 11120759 = 16681139) B16681139
theorem B24072617 : Blo 1299968 24072617 := bstep (se 2 (by rfl) ⟨9027231, by rfl⟩ : syracuseStep 24072617 = 18054463) B18054463
theorem B142529219 : Blo 1299968 142529219 := bstep (se 1 (by rfl) ⟨106896914, by rfl⟩ : syracuseStep 142529219 = 213793829) B213793829
theorem B187593745 : Blo 1299968 187593745 := bstep (se 2 (by rfl) ⟨70347654, by rfl⟩ : syracuseStep 187593745 = 140695309) B140695309
theorem B6583517 : Blo 1299968 6583517 := bstep (se 3 (by rfl) ⟨1234409, by rfl⟩ : syracuseStep 6583517 = 2468819) B2468819
theorem B4388255 : Blo 1299968 4388255 := bstep (se 1 (by rfl) ⟨3291191, by rfl⟩ : syracuseStep 4388255 = 6582383) B6582383
theorem B1300583 : Blo 1299968 1300583 := bstep (se 1 (by rfl) ⟨975437, by rfl⟩ : syracuseStep 1300583 = 1950875) B1950875
theorem B1300731 : Blo 1299968 1300731 := bstep (se 1 (by rfl) ⟨975548, by rfl⟩ : syracuseStep 1300731 = 1951097) B1951097
theorem B11876635 : Blo 1299968 11876635 := bstep (se 1 (by rfl) ⟨8907476, by rfl⟩ : syracuseStep 11876635 = 17814953) B17814953
theorem B3291455 : Blo 1299968 3291455 := bstep (se 1 (by rfl) ⟨2468591, by rfl⟩ : syracuseStep 3291455 = 4937183) B4937183
theorem B1300799 : Blo 1299968 1300799 := bstep (se 1 (by rfl) ⟨975599, by rfl⟩ : syracuseStep 1300799 = 1951199) B1951199
theorem B54868603 : Blo 1299968 54868603 := bstep (se 1 (by rfl) ⟨41151452, by rfl⟩ : syracuseStep 54868603 = 82302905) B82302905
theorem B2194087 : Blo 1299968 2194087 := bstep (se 1 (by rfl) ⟨1645565, by rfl⟩ : syracuseStep 2194087 = 3291131) B3291131
theorem B7413839 : Blo 1299968 7413839 := bstep (se 1 (by rfl) ⟨5560379, by rfl⟩ : syracuseStep 7413839 = 11120759) B11120759
theorem B16048411 : Blo 1299968 16048411 := bstep (se 1 (by rfl) ⟨12036308, by rfl⟩ : syracuseStep 16048411 = 24072617) B24072617
theorem B15835513 : Blo 1299968 15835513 := bstep (se 2 (by rfl) ⟨5938317, by rfl⟩ : syracuseStep 15835513 = 11876635) B11876635
theorem B8339851 : Blo 1299968 8339851 := bstep (se 1 (by rfl) ⟨6254888, by rfl⟩ : syracuseStep 8339851 = 12509777) B12509777
theorem B1950143 : Blo 1299968 1950143 := bstep (se 1 (by rfl) ⟨1462607, by rfl⟩ : syracuseStep 1950143 = 2925215) B2925215
theorem B95019479 : Blo 1299968 95019479 := bstep (se 1 (by rfl) ⟨71264609, by rfl⟩ : syracuseStep 95019479 = 142529219) B142529219
theorem B2925449 : Blo 1299968 2925449 := bstep (se 2 (by rfl) ⟨1097043, by rfl⟩ : syracuseStep 2925449 = 2194087) B2194087
theorem B2925503 : Blo 1299968 2925503 := bstep (se 1 (by rfl) ⟨2194127, by rfl⟩ : syracuseStep 2925503 = 4388255) B4388255
theorem B2196571 : Blo 1299968 2196571 := bstep (se 1 (by rfl) ⟨1647428, by rfl⟩ : syracuseStep 2196571 = 3294857) B3294857
theorem B1951439 : Blo 1299968 1951439 := bstep (se 1 (by rfl) ⟨1463579, by rfl⟩ : syracuseStep 1951439 = 2927159) B2927159
theorem B1952255 : Blo 1299968 1952255 := bstep (se 1 (by rfl) ⟨1464191, by rfl⟩ : syracuseStep 1952255 = 2928383) B2928383
theorem B4393601 : Blo 1299968 4393601 := bstep (se 2 (by rfl) ⟨1647600, by rfl⟩ : syracuseStep 4393601 = 3295201) B3295201
theorem B48147311 : Blo 1299968 48147311 := bstep (se 1 (by rfl) ⟨36110483, by rfl⟩ : syracuseStep 48147311 = 72220967) B72220967
theorem B73158137 : Blo 1299968 73158137 := bstep (se 2 (by rfl) ⟨27434301, by rfl⟩ : syracuseStep 73158137 = 54868603) B54868603
theorem B1300335 : Blo 1299968 1300335 := bstep (se 1 (by rfl) ⟨975251, by rfl⟩ : syracuseStep 1300335 = 1950503) B1950503
theorem B8443871 : Blo 1299968 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B4389011 : Blo 1299968 4389011 := bstep (se 1 (by rfl) ⟨3291758, by rfl⟩ : syracuseStep 4389011 = 6583517) B6583517
theorem B1300639 : Blo 1299968 1300639 := bstep (se 1 (by rfl) ⟨975479, by rfl⟩ : syracuseStep 1300639 = 1950959) B1950959
theorem B250124993 : Blo 1299968 250124993 := bstep (se 2 (by rfl) ⟨93796872, by rfl⟩ : syracuseStep 250124993 = 187593745) B187593745
theorem B2194303 : Blo 1299968 2194303 := bstep (se 1 (by rfl) ⟨1645727, by rfl⟩ : syracuseStep 2194303 = 3291455) B3291455
theorem B1301615 : Blo 1299968 1301615 := bstep (se 1 (by rfl) ⟨976211, by rfl⟩ : syracuseStep 1301615 = 1952423) B1952423
theorem B8330525 : Blo 1299968 8330525 := bstep (se 3 (by rfl) ⟨1561973, by rfl⟩ : syracuseStep 8330525 = 3123947) B3123947
theorem B9379799 : Blo 1299968 9379799 := bstep (se 1 (by rfl) ⟨7034849, by rfl⟩ : syracuseStep 9379799 = 14069699) B14069699
theorem B1950299 : Blo 1299968 1950299 := bstep (se 1 (by rfl) ⟨1462724, by rfl⟩ : syracuseStep 1950299 = 2925449) B2925449
theorem B1950335 : Blo 1299968 1950335 := bstep (se 1 (by rfl) ⟨1462751, by rfl⟩ : syracuseStep 1950335 = 2925503) B2925503
theorem B2925737 : Blo 1299968 2925737 := bstep (se 2 (by rfl) ⟨1097151, by rfl⟩ : syracuseStep 2925737 = 2194303) B2194303
theorem B5629247 : Blo 1299968 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B2926007 : Blo 1299968 2926007 := bstep (se 1 (by rfl) ⟨2194505, by rfl⟩ : syracuseStep 2926007 = 4389011) B4389011
theorem B166749995 : Blo 1299968 166749995 := bstep (se 1 (by rfl) ⟨125062496, by rfl⟩ : syracuseStep 166749995 = 250124993) B250124993
theorem B32098207 : Blo 1299968 32098207 := bstep (se 1 (by rfl) ⟨24073655, by rfl⟩ : syracuseStep 32098207 = 48147311) B48147311
theorem B6253199 : Blo 1299968 6253199 := bstep (se 1 (by rfl) ⟨4689899, by rfl⟩ : syracuseStep 6253199 = 9379799) B9379799
theorem B4942559 : Blo 1299968 4942559 := bstep (se 1 (by rfl) ⟨3706919, by rfl⟩ : syracuseStep 4942559 = 7413839) B7413839
theorem B21114017 : Blo 1299968 21114017 := bstep (se 2 (by rfl) ⟨7917756, by rfl⟩ : syracuseStep 21114017 = 15835513) B15835513
theorem B11119801 : Blo 1299968 11119801 := bstep (se 2 (by rfl) ⟨4169925, by rfl⟩ : syracuseStep 11119801 = 8339851) B8339851
theorem B2928761 : Blo 1299968 2928761 := bstep (se 2 (by rfl) ⟨1098285, by rfl⟩ : syracuseStep 2928761 = 2196571) B2196571
theorem B2929067 : Blo 1299968 2929067 := bstep (se 1 (by rfl) ⟨2196800, by rfl⟩ : syracuseStep 2929067 = 4393601) B4393601
theorem B48772091 : Blo 1299968 48772091 := bstep (se 1 (by rfl) ⟨36579068, by rfl⟩ : syracuseStep 48772091 = 73158137) B73158137
theorem B1300095 : Blo 1299968 1300095 := bstep (se 1 (by rfl) ⟨975071, by rfl⟩ : syracuseStep 1300095 = 1950143) B1950143
theorem B63346319 : Blo 1299968 63346319 := bstep (se 1 (by rfl) ⟨47509739, by rfl⟩ : syracuseStep 63346319 = 95019479) B95019479
theorem B342366101 : Blo 1299968 342366101 := bstep (se 6 (by rfl) ⟨8024205, by rfl⟩ : syracuseStep 342366101 = 16048411) B16048411
theorem B1300959 : Blo 1299968 1300959 := bstep (se 1 (by rfl) ⟨975719, by rfl⟩ : syracuseStep 1300959 = 1951439) B1951439
theorem B1301503 : Blo 1299968 1301503 := bstep (se 1 (by rfl) ⟨976127, by rfl⟩ : syracuseStep 1301503 = 1952255) B1952255
theorem B5553683 : Blo 1299968 5553683 := bstep (se 1 (by rfl) ⟨4165262, by rfl⟩ : syracuseStep 5553683 = 8330525) B8330525
theorem B1950491 : Blo 1299968 1950491 := bstep (se 1 (by rfl) ⟨1462868, by rfl⟩ : syracuseStep 1950491 = 2925737) B2925737
theorem B3752831 : Blo 1299968 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B1950671 : Blo 1299968 1950671 := bstep (se 1 (by rfl) ⟨1463003, by rfl⟩ : syracuseStep 1950671 = 2926007) B2926007
theorem B42230879 : Blo 1299968 42230879 := bstep (se 1 (by rfl) ⟨31673159, by rfl⟩ : syracuseStep 42230879 = 63346319) B63346319
theorem B111166663 : Blo 1299968 111166663 := bstep (se 1 (by rfl) ⟨83374997, by rfl⟩ : syracuseStep 111166663 = 166749995) B166749995
theorem B3295039 : Blo 1299968 3295039 := bstep (se 1 (by rfl) ⟨2471279, by rfl⟩ : syracuseStep 3295039 = 4942559) B4942559
theorem B14076011 : Blo 1299968 14076011 := bstep (se 1 (by rfl) ⟨10557008, by rfl⟩ : syracuseStep 14076011 = 21114017) B21114017
theorem B42797609 : Blo 1299968 42797609 := bstep (se 2 (by rfl) ⟨16049103, by rfl⟩ : syracuseStep 42797609 = 32098207) B32098207
theorem B130058909 : Blo 1299968 130058909 := bstep (se 3 (by rfl) ⟨24386045, by rfl⟩ : syracuseStep 130058909 = 48772091) B48772091
theorem B1952507 : Blo 1299968 1952507 := bstep (se 1 (by rfl) ⟨1464380, by rfl⟩ : syracuseStep 1952507 = 2928761) B2928761
theorem B1952711 : Blo 1299968 1952711 := bstep (se 1 (by rfl) ⟨1464533, by rfl⟩ : syracuseStep 1952711 = 2929067) B2929067
theorem B1300199 : Blo 1299968 1300199 := bstep (se 1 (by rfl) ⟨975149, by rfl⟩ : syracuseStep 1300199 = 1950299) B1950299
theorem B1300223 : Blo 1299968 1300223 := bstep (se 1 (by rfl) ⟨975167, by rfl⟩ : syracuseStep 1300223 = 1950335) B1950335
theorem B228244067 : Blo 1299968 228244067 := bstep (se 1 (by rfl) ⟨171183050, by rfl⟩ : syracuseStep 228244067 = 342366101) B342366101
theorem B14826401 : Blo 1299968 14826401 := bstep (se 2 (by rfl) ⟨5559900, by rfl⟩ : syracuseStep 14826401 = 11119801) B11119801
theorem B4168799 : Blo 1299968 4168799 := bstep (se 1 (by rfl) ⟨3126599, by rfl⟩ : syracuseStep 4168799 = 6253199) B6253199
theorem B3702455 : Blo 1299968 3702455 := bstep (se 1 (by rfl) ⟨2776841, by rfl⟩ : syracuseStep 3702455 = 5553683) B5553683
theorem B86705939 : Blo 1299968 86705939 := bstep (se 1 (by rfl) ⟨65029454, by rfl⟩ : syracuseStep 86705939 = 130058909) B130058909
theorem B2779199 : Blo 1299968 2779199 := bstep (se 1 (by rfl) ⟨2084399, by rfl⟩ : syracuseStep 2779199 = 4168799) B4168799
theorem B4393385 : Blo 1299968 4393385 := bstep (se 2 (by rfl) ⟨1647519, by rfl⟩ : syracuseStep 4393385 = 3295039) B3295039
theorem B2468303 : Blo 1299968 2468303 := bstep (se 1 (by rfl) ⟨1851227, by rfl⟩ : syracuseStep 2468303 = 3702455) B3702455
theorem B9384007 : Blo 1299968 9384007 := bstep (se 1 (by rfl) ⟨7038005, by rfl⟩ : syracuseStep 9384007 = 14076011) B14076011
theorem B148222217 : Blo 1299968 148222217 := bstep (se 2 (by rfl) ⟨55583331, by rfl⟩ : syracuseStep 148222217 = 111166663) B111166663
theorem B152162711 : Blo 1299968 152162711 := bstep (se 1 (by rfl) ⟨114122033, by rfl⟩ : syracuseStep 152162711 = 228244067) B228244067
theorem B9884267 : Blo 1299968 9884267 := bstep (se 1 (by rfl) ⟨7413200, by rfl⟩ : syracuseStep 9884267 = 14826401) B14826401
theorem B10007549 : Blo 1299968 10007549 := bstep (se 3 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 10007549 = 3752831) B3752831
theorem B1300327 : Blo 1299968 1300327 := bstep (se 1 (by rfl) ⟨975245, by rfl⟩ : syracuseStep 1300327 = 1950491) B1950491
theorem B1300447 : Blo 1299968 1300447 := bstep (se 1 (by rfl) ⟨975335, by rfl⟩ : syracuseStep 1300447 = 1950671) B1950671
theorem B28153919 : Blo 1299968 28153919 := bstep (se 1 (by rfl) ⟨21115439, by rfl⟩ : syracuseStep 28153919 = 42230879) B42230879
theorem B28531739 : Blo 1299968 28531739 := bstep (se 1 (by rfl) ⟨21398804, by rfl⟩ : syracuseStep 28531739 = 42797609) B42797609
theorem B1301671 : Blo 1299968 1301671 := bstep (se 1 (by rfl) ⟨976253, by rfl⟩ : syracuseStep 1301671 = 1952507) B1952507
theorem B1301807 : Blo 1299968 1301807 := bstep (se 1 (by rfl) ⟨976355, by rfl⟩ : syracuseStep 1301807 = 1952711) B1952711
theorem B101441807 : Blo 1299968 101441807 := bstep (se 1 (by rfl) ⟨76081355, by rfl⟩ : syracuseStep 101441807 = 152162711) B152162711
theorem B57803959 : Blo 1299968 57803959 := bstep (se 1 (by rfl) ⟨43352969, by rfl⟩ : syracuseStep 57803959 = 86705939) B86705939
theorem B1852799 : Blo 1299968 1852799 := bstep (se 1 (by rfl) ⟨1389599, by rfl⟩ : syracuseStep 1852799 = 2779199) B2779199
theorem B18769279 : Blo 1299968 18769279 := bstep (se 1 (by rfl) ⟨14076959, by rfl⟩ : syracuseStep 18769279 = 28153919) B28153919
theorem B12512009 : Blo 1299968 12512009 := bstep (se 2 (by rfl) ⟨4692003, by rfl⟩ : syracuseStep 12512009 = 9384007) B9384007
theorem B98814811 : Blo 1299968 98814811 := bstep (se 1 (by rfl) ⟨74111108, by rfl⟩ : syracuseStep 98814811 = 148222217) B148222217
theorem B6589511 : Blo 1299968 6589511 := bstep (se 1 (by rfl) ⟨4942133, by rfl⟩ : syracuseStep 6589511 = 9884267) B9884267
theorem B6671699 : Blo 1299968 6671699 := bstep (se 1 (by rfl) ⟨5003774, by rfl⟩ : syracuseStep 6671699 = 10007549) B10007549
theorem B2928923 : Blo 1299968 2928923 := bstep (se 1 (by rfl) ⟨2196692, by rfl⟩ : syracuseStep 2928923 = 4393385) B4393385
theorem B1645535 : Blo 1299968 1645535 := bstep (se 1 (by rfl) ⟨1234151, by rfl⟩ : syracuseStep 1645535 = 2468303) B2468303
theorem B19021159 : Blo 1299968 19021159 := bstep (se 1 (by rfl) ⟨14265869, by rfl⟩ : syracuseStep 19021159 = 28531739) B28531739
theorem B4940797 : Blo 1299968 4940797 := bstep (se 3 (by rfl) ⟨926399, by rfl⟩ : syracuseStep 4940797 = 1852799) B1852799
theorem B131753081 : Blo 1299968 131753081 := bstep (se 2 (by rfl) ⟨49407405, by rfl⟩ : syracuseStep 131753081 = 98814811) B98814811
theorem B8341339 : Blo 1299968 8341339 := bstep (se 1 (by rfl) ⟨6256004, by rfl⟩ : syracuseStep 8341339 = 12512009) B12512009
theorem B4393007 : Blo 1299968 4393007 := bstep (se 1 (by rfl) ⟨3294755, by rfl⟩ : syracuseStep 4393007 = 6589511) B6589511
theorem B67627871 : Blo 1299968 67627871 := bstep (se 1 (by rfl) ⟨50720903, by rfl⟩ : syracuseStep 67627871 = 101441807) B101441807
theorem B1952615 : Blo 1299968 1952615 := bstep (se 1 (by rfl) ⟨1464461, by rfl⟩ : syracuseStep 1952615 = 2928923) B2928923
theorem B101446181 : Blo 1299968 101446181 := bstep (se 4 (by rfl) ⟨9510579, by rfl⟩ : syracuseStep 101446181 = 19021159) B19021159
theorem B4388093 : Blo 1299968 4388093 := bstep (se 3 (by rfl) ⟨822767, by rfl⟩ : syracuseStep 4388093 = 1645535) B1645535
theorem B308287781 : Blo 1299968 308287781 := bstep (se 4 (by rfl) ⟨28901979, by rfl⟩ : syracuseStep 308287781 = 57803959) B57803959
theorem B25025705 : Blo 1299968 25025705 := bstep (se 2 (by rfl) ⟨9384639, by rfl⟩ : syracuseStep 25025705 = 18769279) B18769279
theorem B4447799 : Blo 1299968 4447799 := bstep (se 1 (by rfl) ⟨3335849, by rfl⟩ : syracuseStep 4447799 = 6671699) B6671699
theorem B2925395 : Blo 1299968 2925395 := bstep (se 1 (by rfl) ⟨2194046, by rfl⟩ : syracuseStep 2925395 = 4388093) B4388093
theorem B6587729 : Blo 1299968 6587729 := bstep (se 2 (by rfl) ⟨2470398, by rfl⟩ : syracuseStep 6587729 = 4940797) B4940797
theorem B351341549 : Blo 1299968 351341549 := bstep (se 3 (by rfl) ⟨65876540, by rfl⟩ : syracuseStep 351341549 = 131753081) B131753081
theorem B2928671 : Blo 1299968 2928671 := bstep (se 1 (by rfl) ⟨2196503, by rfl⟩ : syracuseStep 2928671 = 4393007) B4393007
theorem B205525187 : Blo 1299968 205525187 := bstep (se 1 (by rfl) ⟨154143890, by rfl⟩ : syracuseStep 205525187 = 308287781) B308287781
theorem B45085247 : Blo 1299968 45085247 := bstep (se 1 (by rfl) ⟨33813935, by rfl⟩ : syracuseStep 45085247 = 67627871) B67627871
theorem B16683803 : Blo 1299968 16683803 := bstep (se 1 (by rfl) ⟨12512852, by rfl⟩ : syracuseStep 16683803 = 25025705) B25025705
theorem B11121785 : Blo 1299968 11121785 := bstep (se 2 (by rfl) ⟨4170669, by rfl⟩ : syracuseStep 11121785 = 8341339) B8341339
theorem B67630787 : Blo 1299968 67630787 := bstep (se 1 (by rfl) ⟨50723090, by rfl⟩ : syracuseStep 67630787 = 101446181) B101446181
theorem B1301743 : Blo 1299968 1301743 := bstep (se 1 (by rfl) ⟨976307, by rfl⟩ : syracuseStep 1301743 = 1952615) B1952615
theorem B2965199 : Blo 1299968 2965199 := bstep (se 1 (by rfl) ⟨2223899, by rfl⟩ : syracuseStep 2965199 = 4447799) B4447799
theorem B30056831 : Blo 1299968 30056831 := bstep (se 1 (by rfl) ⟨22542623, by rfl⟩ : syracuseStep 30056831 = 45085247) B45085247
theorem B1950263 : Blo 1299968 1950263 := bstep (se 1 (by rfl) ⟨1462697, by rfl⟩ : syracuseStep 1950263 = 2925395) B2925395
theorem B7414523 : Blo 1299968 7414523 := bstep (se 1 (by rfl) ⟨5560892, by rfl⟩ : syracuseStep 7414523 = 11121785) B11121785
theorem B4391819 : Blo 1299968 4391819 := bstep (se 1 (by rfl) ⟨3293864, by rfl⟩ : syracuseStep 4391819 = 6587729) B6587729
theorem B234227699 : Blo 1299968 234227699 := bstep (se 1 (by rfl) ⟨175670774, by rfl⟩ : syracuseStep 234227699 = 351341549) B351341549
theorem B1952447 : Blo 1299968 1952447 := bstep (se 1 (by rfl) ⟨1464335, by rfl⟩ : syracuseStep 1952447 = 2928671) B2928671
theorem B137016791 : Blo 1299968 137016791 := bstep (se 1 (by rfl) ⟨102762593, by rfl⟩ : syracuseStep 137016791 = 205525187) B205525187
theorem B11122535 : Blo 1299968 11122535 := bstep (se 1 (by rfl) ⟨8341901, by rfl⟩ : syracuseStep 11122535 = 16683803) B16683803
theorem B45087191 : Blo 1299968 45087191 := bstep (se 1 (by rfl) ⟨33815393, by rfl⟩ : syracuseStep 45087191 = 67630787) B67630787
theorem B31628789 : Blo 1299968 31628789 := bstep (se 5 (by rfl) ⟨1482599, by rfl⟩ : syracuseStep 31628789 = 2965199) B2965199
theorem B20037887 : Blo 1299968 20037887 := bstep (se 1 (by rfl) ⟨15028415, by rfl⟩ : syracuseStep 20037887 = 30056831) B30056831
theorem B7415023 : Blo 1299968 7415023 := bstep (se 1 (by rfl) ⟨5561267, by rfl⟩ : syracuseStep 7415023 = 11122535) B11122535
theorem B30058127 : Blo 1299968 30058127 := bstep (se 1 (by rfl) ⟨22543595, by rfl⟩ : syracuseStep 30058127 = 45087191) B45087191
theorem B4943015 : Blo 1299968 4943015 := bstep (se 1 (by rfl) ⟨3707261, by rfl⟩ : syracuseStep 4943015 = 7414523) B7414523
theorem B2927879 : Blo 1299968 2927879 := bstep (se 1 (by rfl) ⟨2195909, by rfl⟩ : syracuseStep 2927879 = 4391819) B4391819
theorem B91344527 : Blo 1299968 91344527 := bstep (se 1 (by rfl) ⟨68508395, by rfl⟩ : syracuseStep 91344527 = 137016791) B137016791
theorem B156151799 : Blo 1299968 156151799 := bstep (se 1 (by rfl) ⟨117113849, by rfl⟩ : syracuseStep 156151799 = 234227699) B234227699
theorem B1300175 : Blo 1299968 1300175 := bstep (se 1 (by rfl) ⟨975131, by rfl⟩ : syracuseStep 1300175 = 1950263) B1950263
theorem B1301631 : Blo 1299968 1301631 := bstep (se 1 (by rfl) ⟨976223, by rfl⟩ : syracuseStep 1301631 = 1952447) B1952447
theorem B21085859 : Blo 1299968 21085859 := bstep (se 1 (by rfl) ⟨15814394, by rfl⟩ : syracuseStep 21085859 = 31628789) B31628789
theorem B20038751 : Blo 1299968 20038751 := bstep (se 1 (by rfl) ⟨15029063, by rfl⟩ : syracuseStep 20038751 = 30058127) B30058127
theorem B3295343 : Blo 1299968 3295343 := bstep (se 1 (by rfl) ⟨2471507, by rfl⟩ : syracuseStep 3295343 = 4943015) B4943015
theorem B1951919 : Blo 1299968 1951919 := bstep (se 1 (by rfl) ⟨1463939, by rfl⟩ : syracuseStep 1951919 = 2927879) B2927879
theorem B60896351 : Blo 1299968 60896351 := bstep (se 1 (by rfl) ⟨45672263, by rfl⟩ : syracuseStep 60896351 = 91344527) B91344527
theorem B104101199 : Blo 1299968 104101199 := bstep (se 1 (by rfl) ⟨78075899, by rfl⟩ : syracuseStep 104101199 = 156151799) B156151799
theorem B13358591 : Blo 1299968 13358591 := bstep (se 1 (by rfl) ⟨10018943, by rfl⟩ : syracuseStep 13358591 = 20037887) B20037887
theorem B9886697 : Blo 1299968 9886697 := bstep (se 2 (by rfl) ⟨3707511, by rfl⟩ : syracuseStep 9886697 = 7415023) B7415023
theorem B14057239 : Blo 1299968 14057239 := bstep (se 1 (by rfl) ⟨10542929, by rfl⟩ : syracuseStep 14057239 = 21085859) B21085859
theorem B162390269 : Blo 1299968 162390269 := bstep (se 3 (by rfl) ⟨30448175, by rfl⟩ : syracuseStep 162390269 = 60896351) B60896351
theorem B8905727 : Blo 1299968 8905727 := bstep (se 1 (by rfl) ⟨6679295, by rfl⟩ : syracuseStep 8905727 = 13358591) B13358591
theorem B2196895 : Blo 1299968 2196895 := bstep (se 1 (by rfl) ⟨1647671, by rfl⟩ : syracuseStep 2196895 = 3295343) B3295343
theorem B6591131 : Blo 1299968 6591131 := bstep (se 1 (by rfl) ⟨4943348, by rfl⟩ : syracuseStep 6591131 = 9886697) B9886697
theorem B13359167 : Blo 1299968 13359167 := bstep (se 1 (by rfl) ⟨10019375, by rfl⟩ : syracuseStep 13359167 = 20038751) B20038751
theorem B69400799 : Blo 1299968 69400799 := bstep (se 1 (by rfl) ⟨52050599, by rfl⟩ : syracuseStep 69400799 = 104101199) B104101199
theorem B1301279 : Blo 1299968 1301279 := bstep (se 1 (by rfl) ⟨975959, by rfl⟩ : syracuseStep 1301279 = 1951919) B1951919
theorem B18742985 : Blo 1299968 18742985 := bstep (se 2 (by rfl) ⟨7028619, by rfl⟩ : syracuseStep 18742985 = 14057239) B14057239
theorem B8906111 : Blo 1299968 8906111 := bstep (se 1 (by rfl) ⟨6679583, by rfl⟩ : syracuseStep 8906111 = 13359167) B13359167
theorem B12495323 : Blo 1299968 12495323 := bstep (se 1 (by rfl) ⟨9371492, by rfl⟩ : syracuseStep 12495323 = 18742985) B18742985
theorem B4394087 : Blo 1299968 4394087 := bstep (se 1 (by rfl) ⟨3295565, by rfl⟩ : syracuseStep 4394087 = 6591131) B6591131
theorem B433040717 : Blo 1299968 433040717 := bstep (se 3 (by rfl) ⟨81195134, by rfl⟩ : syracuseStep 433040717 = 162390269) B162390269
theorem B2929193 : Blo 1299968 2929193 := bstep (se 2 (by rfl) ⟨1098447, by rfl⟩ : syracuseStep 2929193 = 2196895) B2196895
theorem B5937151 : Blo 1299968 5937151 := bstep (se 1 (by rfl) ⟨4452863, by rfl⟩ : syracuseStep 5937151 = 8905727) B8905727
theorem B46267199 : Blo 1299968 46267199 := bstep (se 1 (by rfl) ⟨34700399, by rfl⟩ : syracuseStep 46267199 = 69400799) B69400799
theorem B30844799 : Blo 1299968 30844799 := bstep (se 1 (by rfl) ⟨23133599, by rfl⟩ : syracuseStep 30844799 = 46267199) B46267199
theorem B7916201 : Blo 1299968 7916201 := bstep (se 2 (by rfl) ⟨2968575, by rfl⟩ : syracuseStep 7916201 = 5937151) B5937151
theorem B1952795 : Blo 1299968 1952795 := bstep (se 1 (by rfl) ⟨1464596, by rfl⟩ : syracuseStep 1952795 = 2929193) B2929193
theorem B2929391 : Blo 1299968 2929391 := bstep (se 1 (by rfl) ⟨2197043, by rfl⟩ : syracuseStep 2929391 = 4394087) B4394087
theorem B5937407 : Blo 1299968 5937407 := bstep (se 1 (by rfl) ⟨4453055, by rfl⟩ : syracuseStep 5937407 = 8906111) B8906111
theorem B8330215 : Blo 1299968 8330215 := bstep (se 1 (by rfl) ⟨6247661, by rfl⟩ : syracuseStep 8330215 = 12495323) B12495323
theorem B288693811 : Blo 1299968 288693811 := bstep (se 1 (by rfl) ⟨216520358, by rfl⟩ : syracuseStep 288693811 = 433040717) B433040717
theorem B20563199 : Blo 1299968 20563199 := bstep (se 1 (by rfl) ⟨15422399, by rfl⟩ : syracuseStep 20563199 = 30844799) B30844799
theorem B3958271 : Blo 1299968 3958271 := bstep (se 1 (by rfl) ⟨2968703, by rfl⟩ : syracuseStep 3958271 = 5937407) B5937407
theorem B5277467 : Blo 1299968 5277467 := bstep (se 1 (by rfl) ⟨3958100, by rfl⟩ : syracuseStep 5277467 = 7916201) B7916201
theorem B1952927 : Blo 1299968 1952927 := bstep (se 1 (by rfl) ⟨1464695, by rfl⟩ : syracuseStep 1952927 = 2929391) B2929391
theorem B11106953 : Blo 1299968 11106953 := bstep (se 2 (by rfl) ⟨4165107, by rfl⟩ : syracuseStep 11106953 = 8330215) B8330215
theorem B1301863 : Blo 1299968 1301863 := bstep (se 1 (by rfl) ⟨976397, by rfl⟩ : syracuseStep 1301863 = 1952795) B1952795
theorem B384925081 : Blo 1299968 384925081 := bstep (se 2 (by rfl) ⟨144346905, by rfl⟩ : syracuseStep 384925081 = 288693811) B288693811
theorem B2638847 : Blo 1299968 2638847 := bstep (se 1 (by rfl) ⟨1979135, by rfl⟩ : syracuseStep 2638847 = 3958271) B3958271
theorem B13708799 : Blo 1299968 13708799 := bstep (se 1 (by rfl) ⟨10281599, by rfl⟩ : syracuseStep 13708799 = 20563199) B20563199
theorem B3518311 : Blo 1299968 3518311 := bstep (se 1 (by rfl) ⟨2638733, by rfl⟩ : syracuseStep 3518311 = 5277467) B5277467
theorem B513233441 : Blo 1299968 513233441 := bstep (se 2 (by rfl) ⟨192462540, by rfl⟩ : syracuseStep 513233441 = 384925081) B384925081
theorem B7404635 : Blo 1299968 7404635 := bstep (se 1 (by rfl) ⟨5553476, by rfl⟩ : syracuseStep 7404635 = 11106953) B11106953
theorem B1301951 : Blo 1299968 1301951 := bstep (se 1 (by rfl) ⟨976463, by rfl⟩ : syracuseStep 1301951 = 1952927) B1952927
theorem B342155627 : Blo 1299968 342155627 := bstep (se 1 (by rfl) ⟨256616720, by rfl⟩ : syracuseStep 342155627 = 513233441) B513233441
theorem B4936423 : Blo 1299968 4936423 := bstep (se 1 (by rfl) ⟨3702317, by rfl⟩ : syracuseStep 4936423 = 7404635) B7404635
theorem B9139199 : Blo 1299968 9139199 := bstep (se 1 (by rfl) ⟨6854399, by rfl⟩ : syracuseStep 9139199 = 13708799) B13708799
theorem B4691081 : Blo 1299968 4691081 := bstep (se 2 (by rfl) ⟨1759155, by rfl⟩ : syracuseStep 4691081 = 3518311) B3518311
theorem B1759231 : Blo 1299968 1759231 := bstep (se 1 (by rfl) ⟨1319423, by rfl⟩ : syracuseStep 1759231 = 2638847) B2638847
theorem B12509549 : Blo 1299968 12509549 := bstep (se 3 (by rfl) ⟨2345540, by rfl⟩ : syracuseStep 12509549 = 4691081) B4691081
theorem B2345641 : Blo 1299968 2345641 := bstep (se 2 (by rfl) ⟨879615, by rfl⟩ : syracuseStep 2345641 = 1759231) B1759231
theorem B6581897 : Blo 1299968 6581897 := bstep (se 2 (by rfl) ⟨2468211, by rfl⟩ : syracuseStep 6581897 = 4936423) B4936423
theorem B228103751 : Blo 1299968 228103751 := bstep (se 1 (by rfl) ⟨171077813, by rfl⟩ : syracuseStep 228103751 = 342155627) B342155627
theorem B97484789 : Blo 1299968 97484789 := bstep (se 5 (by rfl) ⟨4569599, by rfl⟩ : syracuseStep 97484789 = 9139199) B9139199
theorem B8339699 : Blo 1299968 8339699 := bstep (se 1 (by rfl) ⟨6254774, by rfl⟩ : syracuseStep 8339699 = 12509549) B12509549
theorem B12510085 : Blo 1299968 12510085 := bstep (se 4 (by rfl) ⟨1172820, by rfl⟩ : syracuseStep 12510085 = 2345641) B2345641
theorem B152069167 : Blo 1299968 152069167 := bstep (se 1 (by rfl) ⟨114051875, by rfl⟩ : syracuseStep 152069167 = 228103751) B228103751
theorem B64989859 : Blo 1299968 64989859 := bstep (se 1 (by rfl) ⟨48742394, by rfl⟩ : syracuseStep 64989859 = 97484789) B97484789
theorem B4387931 : Blo 1299968 4387931 := bstep (se 1 (by rfl) ⟨3290948, by rfl⟩ : syracuseStep 4387931 = 6581897) B6581897
theorem B2925287 : Blo 1299968 2925287 := bstep (se 1 (by rfl) ⟨2193965, by rfl⟩ : syracuseStep 2925287 = 4387931) B4387931
theorem B16680113 : Blo 1299968 16680113 := bstep (se 2 (by rfl) ⟨6255042, by rfl⟩ : syracuseStep 16680113 = 12510085) B12510085
theorem B5559799 : Blo 1299968 5559799 := bstep (se 1 (by rfl) ⟨4169849, by rfl⟩ : syracuseStep 5559799 = 8339699) B8339699
theorem B86653145 : Blo 1299968 86653145 := bstep (se 2 (by rfl) ⟨32494929, by rfl⟩ : syracuseStep 86653145 = 64989859) B64989859
theorem B202758889 : Blo 1299968 202758889 := bstep (se 2 (by rfl) ⟨76034583, by rfl⟩ : syracuseStep 202758889 = 152069167) B152069167
theorem B1950191 : Blo 1299968 1950191 := bstep (se 1 (by rfl) ⟨1462643, by rfl⟩ : syracuseStep 1950191 = 2925287) B2925287
theorem B270345185 : Blo 1299968 270345185 := bstep (se 2 (by rfl) ⟨101379444, by rfl⟩ : syracuseStep 270345185 = 202758889) B202758889
theorem B11120075 : Blo 1299968 11120075 := bstep (se 1 (by rfl) ⟨8340056, by rfl⟩ : syracuseStep 11120075 = 16680113) B16680113
theorem B57768763 : Blo 1299968 57768763 := bstep (se 1 (by rfl) ⟨43326572, by rfl⟩ : syracuseStep 57768763 = 86653145) B86653145
theorem B7413065 : Blo 1299968 7413065 := bstep (se 2 (by rfl) ⟨2779899, by rfl⟩ : syracuseStep 7413065 = 5559799) B5559799
theorem B4942043 : Blo 1299968 4942043 := bstep (se 1 (by rfl) ⟨3706532, by rfl⟩ : syracuseStep 4942043 = 7413065) B7413065
theorem B77025017 : Blo 1299968 77025017 := bstep (se 2 (by rfl) ⟨28884381, by rfl⟩ : syracuseStep 77025017 = 57768763) B57768763
theorem B1300127 : Blo 1299968 1300127 := bstep (se 1 (by rfl) ⟨975095, by rfl⟩ : syracuseStep 1300127 = 1950191) B1950191
theorem B180230123 : Blo 1299968 180230123 := bstep (se 1 (by rfl) ⟨135172592, by rfl⟩ : syracuseStep 180230123 = 270345185) B270345185
theorem B7413383 : Blo 1299968 7413383 := bstep (se 1 (by rfl) ⟨5560037, by rfl⟩ : syracuseStep 7413383 = 11120075) B11120075
theorem B120153415 : Blo 1299968 120153415 := bstep (se 1 (by rfl) ⟨90115061, by rfl⟩ : syracuseStep 120153415 = 180230123) B180230123
theorem B3294695 : Blo 1299968 3294695 := bstep (se 1 (by rfl) ⟨2471021, by rfl⟩ : syracuseStep 3294695 = 4942043) B4942043
theorem B205400045 : Blo 1299968 205400045 := bstep (se 3 (by rfl) ⟨38512508, by rfl⟩ : syracuseStep 205400045 = 77025017) B77025017
theorem B4942255 : Blo 1299968 4942255 := bstep (se 1 (by rfl) ⟨3706691, by rfl⟩ : syracuseStep 4942255 = 7413383) B7413383
theorem B2196463 : Blo 1299968 2196463 := bstep (se 1 (by rfl) ⟨1647347, by rfl⟩ : syracuseStep 2196463 = 3294695) B3294695
theorem B160204553 : Blo 1299968 160204553 := bstep (se 2 (by rfl) ⟨60076707, by rfl⟩ : syracuseStep 160204553 = 120153415) B120153415
theorem B6589673 : Blo 1299968 6589673 := bstep (se 2 (by rfl) ⟨2471127, by rfl⟩ : syracuseStep 6589673 = 4942255) B4942255
theorem B136933363 : Blo 1299968 136933363 := bstep (se 1 (by rfl) ⟨102700022, by rfl⟩ : syracuseStep 136933363 = 205400045) B205400045
theorem B4393115 : Blo 1299968 4393115 := bstep (se 1 (by rfl) ⟨3294836, by rfl⟩ : syracuseStep 4393115 = 6589673) B6589673
theorem B182577817 : Blo 1299968 182577817 := bstep (se 2 (by rfl) ⟨68466681, by rfl⟩ : syracuseStep 182577817 = 136933363) B136933363
theorem B106803035 : Blo 1299968 106803035 := bstep (se 1 (by rfl) ⟨80102276, by rfl⟩ : syracuseStep 106803035 = 160204553) B160204553
theorem B2928617 : Blo 1299968 2928617 := bstep (se 2 (by rfl) ⟨1098231, by rfl⟩ : syracuseStep 2928617 = 2196463) B2196463
theorem B1952411 : Blo 1299968 1952411 := bstep (se 1 (by rfl) ⟨1464308, by rfl⟩ : syracuseStep 1952411 = 2928617) B2928617
theorem B243437089 : Blo 1299968 243437089 := bstep (se 2 (by rfl) ⟨91288908, by rfl⟩ : syracuseStep 243437089 = 182577817) B182577817
theorem B2928743 : Blo 1299968 2928743 := bstep (se 1 (by rfl) ⟨2196557, by rfl⟩ : syracuseStep 2928743 = 4393115) B4393115
theorem B71202023 : Blo 1299968 71202023 := bstep (se 1 (by rfl) ⟨53401517, by rfl⟩ : syracuseStep 71202023 = 106803035) B106803035
theorem B1952495 : Blo 1299968 1952495 := bstep (se 1 (by rfl) ⟨1464371, by rfl⟩ : syracuseStep 1952495 = 2928743) B2928743
theorem B47468015 : Blo 1299968 47468015 := bstep (se 1 (by rfl) ⟨35601011, by rfl⟩ : syracuseStep 47468015 = 71202023) B71202023
theorem B1301607 : Blo 1299968 1301607 := bstep (se 1 (by rfl) ⟨976205, by rfl⟩ : syracuseStep 1301607 = 1952411) B1952411
theorem B324582785 : Blo 1299968 324582785 := bstep (se 2 (by rfl) ⟨121718544, by rfl⟩ : syracuseStep 324582785 = 243437089) B243437089
theorem B216388523 : Blo 1299968 216388523 := bstep (se 1 (by rfl) ⟨162291392, by rfl⟩ : syracuseStep 216388523 = 324582785) B324582785
theorem B1301663 : Blo 1299968 1301663 := bstep (se 1 (by rfl) ⟨976247, by rfl⟩ : syracuseStep 1301663 = 1952495) B1952495
theorem B31645343 : Blo 1299968 31645343 := bstep (se 1 (by rfl) ⟨23734007, by rfl⟩ : syracuseStep 31645343 = 47468015) B47468015
theorem B21096895 : Blo 1299968 21096895 := bstep (se 1 (by rfl) ⟨15822671, by rfl⟩ : syracuseStep 21096895 = 31645343) B31645343
theorem B144259015 : Blo 1299968 144259015 := bstep (se 1 (by rfl) ⟨108194261, by rfl⟩ : syracuseStep 144259015 = 216388523) B216388523
theorem B192345353 : Blo 1299968 192345353 := bstep (se 2 (by rfl) ⟨72129507, by rfl⟩ : syracuseStep 192345353 = 144259015) B144259015
theorem B28129193 : Blo 1299968 28129193 := bstep (se 2 (by rfl) ⟨10548447, by rfl⟩ : syracuseStep 28129193 = 21096895) B21096895
theorem B128230235 : Blo 1299968 128230235 := bstep (se 1 (by rfl) ⟨96172676, by rfl⟩ : syracuseStep 128230235 = 192345353) B192345353
theorem B18752795 : Blo 1299968 18752795 := bstep (se 1 (by rfl) ⟨14064596, by rfl⟩ : syracuseStep 18752795 = 28129193) B28129193
theorem B12501863 : Blo 1299968 12501863 := bstep (se 1 (by rfl) ⟨9376397, by rfl⟩ : syracuseStep 12501863 = 18752795) B18752795
theorem B85486823 : Blo 1299968 85486823 := bstep (se 1 (by rfl) ⟨64115117, by rfl⟩ : syracuseStep 85486823 = 128230235) B128230235
theorem B8334575 : Blo 1299968 8334575 := bstep (se 1 (by rfl) ⟨6250931, by rfl⟩ : syracuseStep 8334575 = 12501863) B12501863
theorem B56991215 : Blo 1299968 56991215 := bstep (se 1 (by rfl) ⟨42743411, by rfl⟩ : syracuseStep 56991215 = 85486823) B85486823
theorem B5556383 : Blo 1299968 5556383 := bstep (se 1 (by rfl) ⟨4167287, by rfl⟩ : syracuseStep 5556383 = 8334575) B8334575
theorem B37994143 : Blo 1299968 37994143 := bstep (se 1 (by rfl) ⟨28495607, by rfl⟩ : syracuseStep 37994143 = 56991215) B56991215
theorem B3704255 : Blo 1299968 3704255 := bstep (se 1 (by rfl) ⟨2778191, by rfl⟩ : syracuseStep 3704255 = 5556383) B5556383
theorem B50658857 : Blo 1299968 50658857 := bstep (se 2 (by rfl) ⟨18997071, by rfl⟩ : syracuseStep 50658857 = 37994143) B37994143
theorem B2469503 : Blo 1299968 2469503 := bstep (se 1 (by rfl) ⟨1852127, by rfl⟩ : syracuseStep 2469503 = 3704255) B3704255
theorem B33772571 : Blo 1299968 33772571 := bstep (se 1 (by rfl) ⟨25329428, by rfl⟩ : syracuseStep 33772571 = 50658857) B50658857
theorem B22515047 : Blo 1299968 22515047 := bstep (se 1 (by rfl) ⟨16886285, by rfl⟩ : syracuseStep 22515047 = 33772571) B33772571
theorem B1646335 : Blo 1299968 1646335 := bstep (se 1 (by rfl) ⟨1234751, by rfl⟩ : syracuseStep 1646335 = 2469503) B2469503
theorem B15010031 : Blo 1299968 15010031 := bstep (se 1 (by rfl) ⟨11257523, by rfl⟩ : syracuseStep 15010031 = 22515047) B22515047
theorem B2195113 : Blo 1299968 2195113 := bstep (se 2 (by rfl) ⟨823167, by rfl⟩ : syracuseStep 2195113 = 1646335) B1646335
theorem B2926817 : Blo 1299968 2926817 := bstep (se 2 (by rfl) ⟨1097556, by rfl⟩ : syracuseStep 2926817 = 2195113) B2195113
theorem B10006687 : Blo 1299968 10006687 := bstep (se 1 (by rfl) ⟨7505015, by rfl⟩ : syracuseStep 10006687 = 15010031) B15010031
theorem B1951211 : Blo 1299968 1951211 := bstep (se 1 (by rfl) ⟨1463408, by rfl⟩ : syracuseStep 1951211 = 2926817) B2926817
theorem B13342249 : Blo 1299968 13342249 := bstep (se 2 (by rfl) ⟨5003343, by rfl⟩ : syracuseStep 13342249 = 10006687) B10006687
theorem B71158661 : Blo 1299968 71158661 := bstep (se 4 (by rfl) ⟨6671124, by rfl⟩ : syracuseStep 71158661 = 13342249) B13342249
theorem B1300807 : Blo 1299968 1300807 := bstep (se 1 (by rfl) ⟨975605, by rfl⟩ : syracuseStep 1300807 = 1951211) B1951211
theorem B47439107 : Blo 1299968 47439107 := bstep (se 1 (by rfl) ⟨35579330, by rfl⟩ : syracuseStep 47439107 = 71158661) B71158661
theorem B31626071 : Blo 1299968 31626071 := bstep (se 1 (by rfl) ⟨23719553, by rfl⟩ : syracuseStep 31626071 = 47439107) B47439107
theorem B21084047 : Blo 1299968 21084047 := bstep (se 1 (by rfl) ⟨15813035, by rfl⟩ : syracuseStep 21084047 = 31626071) B31626071
theorem B14056031 : Blo 1299968 14056031 := bstep (se 1 (by rfl) ⟨10542023, by rfl⟩ : syracuseStep 14056031 = 21084047) B21084047
theorem B9370687 : Blo 1299968 9370687 := bstep (se 1 (by rfl) ⟨7028015, by rfl⟩ : syracuseStep 9370687 = 14056031) B14056031
theorem B12494249 : Blo 1299968 12494249 := bstep (se 2 (by rfl) ⟨4685343, by rfl⟩ : syracuseStep 12494249 = 9370687) B9370687
theorem B8329499 : Blo 1299968 8329499 := bstep (se 1 (by rfl) ⟨6247124, by rfl⟩ : syracuseStep 8329499 = 12494249) B12494249
theorem B5552999 : Blo 1299968 5552999 := bstep (se 1 (by rfl) ⟨4164749, by rfl⟩ : syracuseStep 5552999 = 8329499) B8329499
theorem B3701999 : Blo 1299968 3701999 := bstep (se 1 (by rfl) ⟨2776499, by rfl⟩ : syracuseStep 3701999 = 5552999) B5552999
theorem B2467999 : Blo 1299968 2467999 := bstep (se 1 (by rfl) ⟨1850999, by rfl⟩ : syracuseStep 2467999 = 3701999) B3701999
theorem B3290665 : Blo 1299968 3290665 := bstep (se 2 (by rfl) ⟨1233999, by rfl⟩ : syracuseStep 3290665 = 2467999) B2467999
theorem B4387553 : Blo 1299968 4387553 := bstep (se 2 (by rfl) ⟨1645332, by rfl⟩ : syracuseStep 4387553 = 3290665) B3290665
theorem B2925035 : Blo 1299968 2925035 := bstep (se 1 (by rfl) ⟨2193776, by rfl⟩ : syracuseStep 2925035 = 4387553) B4387553
theorem B1950023 : Blo 1299968 1950023 := bstep (se 1 (by rfl) ⟨1462517, by rfl⟩ : syracuseStep 1950023 = 2925035) B2925035
theorem B1300015 : Blo 1299968 1300015 := bstep (se 1 (by rfl) ⟨975011, by rfl⟩ : syracuseStep 1300015 = 1950023) B1950023

theorem C0 (j : ℕ) (h1 : 324992 ≤ j) (h2 : j ≤ 325491) : Blo 1299968 (4 * j + 3) := by
  interval_cases j
  · exact B1299971
  · exact B1299975
  · exact B1299979
  · exact B1299983
  · exact B1299987
  · exact B1299991
  · exact B1299995
  · exact B1299999
  · exact B1300003
  · exact B1300007
  · exact B1300011
  · exact B1300015
  · exact B1300019
  · exact B1300023
  · exact B1300027
  · exact B1300031
  · exact B1300035
  · exact B1300039
  · exact B1300043
  · exact B1300047
  · exact B1300051
  · exact B1300055
  · exact B1300059
  · exact B1300063
  · exact B1300067
  · exact B1300071
  · exact B1300075
  · exact B1300079
  · exact B1300083
  · exact B1300087
  · exact B1300091
  · exact B1300095
  · exact B1300099
  · exact B1300103
  · exact B1300107
  · exact B1300111
  · exact B1300115
  · exact B1300119
  · exact B1300123
  · exact B1300127
  · exact B1300131
  · exact B1300135
  · exact B1300139
  · exact B1300143
  · exact B1300147
  · exact B1300151
  · exact B1300155
  · exact B1300159
  · exact B1300163
  · exact B1300167
  · exact B1300171
  · exact B1300175
  · exact B1300179
  · exact B1300183
  · exact B1300187
  · exact B1300191
  · exact B1300195
  · exact B1300199
  · exact B1300203
  · exact B1300207
  · exact B1300211
  · exact B1300215
  · exact B1300219
  · exact B1300223
  · exact B1300227
  · exact B1300231
  · exact B1300235
  · exact B1300239
  · exact B1300243
  · exact B1300247
  · exact B1300251
  · exact B1300255
  · exact B1300259
  · exact B1300263
  · exact B1300267
  · exact B1300271
  · exact B1300275
  · exact B1300279
  · exact B1300283
  · exact B1300287
  · exact B1300291
  · exact B1300295
  · exact B1300299
  · exact B1300303
  · exact B1300307
  · exact B1300311
  · exact B1300315
  · exact B1300319
  · exact B1300323
  · exact B1300327
  · exact B1300331
  · exact B1300335
  · exact B1300339
  · exact B1300343
  · exact B1300347
  · exact B1300351
  · exact B1300355
  · exact B1300359
  · exact B1300363
  · exact B1300367
  · exact B1300371
  · exact B1300375
  · exact B1300379
  · exact B1300383
  · exact B1300387
  · exact B1300391
  · exact B1300395
  · exact B1300399
  · exact B1300403
  · exact B1300407
  · exact B1300411
  · exact B1300415
  · exact B1300419
  · exact B1300423
  · exact B1300427
  · exact B1300431
  · exact B1300435
  · exact B1300439
  · exact B1300443
  · exact B1300447
  · exact B1300451
  · exact B1300455
  · exact B1300459
  · exact B1300463
  · exact B1300467
  · exact B1300471
  · exact B1300475
  · exact B1300479
  · exact B1300483
  · exact B1300487
  · exact B1300491
  · exact B1300495
  · exact B1300499
  · exact B1300503
  · exact B1300507
  · exact B1300511
  · exact B1300515
  · exact B1300519
  · exact B1300523
  · exact B1300527
  · exact B1300531
  · exact B1300535
  · exact B1300539
  · exact B1300543
  · exact B1300547
  · exact B1300551
  · exact B1300555
  · exact B1300559
  · exact B1300563
  · exact B1300567
  · exact B1300571
  · exact B1300575
  · exact B1300579
  · exact B1300583
  · exact B1300587
  · exact B1300591
  · exact B1300595
  · exact B1300599
  · exact B1300603
  · exact B1300607
  · exact B1300611
  · exact B1300615
  · exact B1300619
  · exact B1300623
  · exact B1300627
  · exact B1300631
  · exact B1300635
  · exact B1300639
  · exact B1300643
  · exact B1300647
  · exact B1300651
  · exact B1300655
  · exact B1300659
  · exact B1300663
  · exact B1300667
  · exact B1300671
  · exact B1300675
  · exact B1300679
  · exact B1300683
  · exact B1300687
  · exact B1300691
  · exact B1300695
  · exact B1300699
  · exact B1300703
  · exact B1300707
  · exact B1300711
  · exact B1300715
  · exact B1300719
  · exact B1300723
  · exact B1300727
  · exact B1300731
  · exact B1300735
  · exact B1300739
  · exact B1300743
  · exact B1300747
  · exact B1300751
  · exact B1300755
  · exact B1300759
  · exact B1300763
  · exact B1300767
  · exact B1300771
  · exact B1300775
  · exact B1300779
  · exact B1300783
  · exact B1300787
  · exact B1300791
  · exact B1300795
  · exact B1300799
  · exact B1300803
  · exact B1300807
  · exact B1300811
  · exact B1300815
  · exact B1300819
  · exact B1300823
  · exact B1300827
  · exact B1300831
  · exact B1300835
  · exact B1300839
  · exact B1300843
  · exact B1300847
  · exact B1300851
  · exact B1300855
  · exact B1300859
  · exact B1300863
  · exact B1300867
  · exact B1300871
  · exact B1300875
  · exact B1300879
  · exact B1300883
  · exact B1300887
  · exact B1300891
  · exact B1300895
  · exact B1300899
  · exact B1300903
  · exact B1300907
  · exact B1300911
  · exact B1300915
  · exact B1300919
  · exact B1300923
  · exact B1300927
  · exact B1300931
  · exact B1300935
  · exact B1300939
  · exact B1300943
  · exact B1300947
  · exact B1300951
  · exact B1300955
  · exact B1300959
  · exact B1300963
  · exact B1300967
  · exact B1300971
  · exact B1300975
  · exact B1300979
  · exact B1300983
  · exact B1300987
  · exact B1300991
  · exact B1300995
  · exact B1300999
  · exact B1301003
  · exact B1301007
  · exact B1301011
  · exact B1301015
  · exact B1301019
  · exact B1301023
  · exact B1301027
  · exact B1301031
  · exact B1301035
  · exact B1301039
  · exact B1301043
  · exact B1301047
  · exact B1301051
  · exact B1301055
  · exact B1301059
  · exact B1301063
  · exact B1301067
  · exact B1301071
  · exact B1301075
  · exact B1301079
  · exact B1301083
  · exact B1301087
  · exact B1301091
  · exact B1301095
  · exact B1301099
  · exact B1301103
  · exact B1301107
  · exact B1301111
  · exact B1301115
  · exact B1301119
  · exact B1301123
  · exact B1301127
  · exact B1301131
  · exact B1301135
  · exact B1301139
  · exact B1301143
  · exact B1301147
  · exact B1301151
  · exact B1301155
  · exact B1301159
  · exact B1301163
  · exact B1301167
  · exact B1301171
  · exact B1301175
  · exact B1301179
  · exact B1301183
  · exact B1301187
  · exact B1301191
  · exact B1301195
  · exact B1301199
  · exact B1301203
  · exact B1301207
  · exact B1301211
  · exact B1301215
  · exact B1301219
  · exact B1301223
  · exact B1301227
  · exact B1301231
  · exact B1301235
  · exact B1301239
  · exact B1301243
  · exact B1301247
  · exact B1301251
  · exact B1301255
  · exact B1301259
  · exact B1301263
  · exact B1301267
  · exact B1301271
  · exact B1301275
  · exact B1301279
  · exact B1301283
  · exact B1301287
  · exact B1301291
  · exact B1301295
  · exact B1301299
  · exact B1301303
  · exact B1301307
  · exact B1301311
  · exact B1301315
  · exact B1301319
  · exact B1301323
  · exact B1301327
  · exact B1301331
  · exact B1301335
  · exact B1301339
  · exact B1301343
  · exact B1301347
  · exact B1301351
  · exact B1301355
  · exact B1301359
  · exact B1301363
  · exact B1301367
  · exact B1301371
  · exact B1301375
  · exact B1301379
  · exact B1301383
  · exact B1301387
  · exact B1301391
  · exact B1301395
  · exact B1301399
  · exact B1301403
  · exact B1301407
  · exact B1301411
  · exact B1301415
  · exact B1301419
  · exact B1301423
  · exact B1301427
  · exact B1301431
  · exact B1301435
  · exact B1301439
  · exact B1301443
  · exact B1301447
  · exact B1301451
  · exact B1301455
  · exact B1301459
  · exact B1301463
  · exact B1301467
  · exact B1301471
  · exact B1301475
  · exact B1301479
  · exact B1301483
  · exact B1301487
  · exact B1301491
  · exact B1301495
  · exact B1301499
  · exact B1301503
  · exact B1301507
  · exact B1301511
  · exact B1301515
  · exact B1301519
  · exact B1301523
  · exact B1301527
  · exact B1301531
  · exact B1301535
  · exact B1301539
  · exact B1301543
  · exact B1301547
  · exact B1301551
  · exact B1301555
  · exact B1301559
  · exact B1301563
  · exact B1301567
  · exact B1301571
  · exact B1301575
  · exact B1301579
  · exact B1301583
  · exact B1301587
  · exact B1301591
  · exact B1301595
  · exact B1301599
  · exact B1301603
  · exact B1301607
  · exact B1301611
  · exact B1301615
  · exact B1301619
  · exact B1301623
  · exact B1301627
  · exact B1301631
  · exact B1301635
  · exact B1301639
  · exact B1301643
  · exact B1301647
  · exact B1301651
  · exact B1301655
  · exact B1301659
  · exact B1301663
  · exact B1301667
  · exact B1301671
  · exact B1301675
  · exact B1301679
  · exact B1301683
  · exact B1301687
  · exact B1301691
  · exact B1301695
  · exact B1301699
  · exact B1301703
  · exact B1301707
  · exact B1301711
  · exact B1301715
  · exact B1301719
  · exact B1301723
  · exact B1301727
  · exact B1301731
  · exact B1301735
  · exact B1301739
  · exact B1301743
  · exact B1301747
  · exact B1301751
  · exact B1301755
  · exact B1301759
  · exact B1301763
  · exact B1301767
  · exact B1301771
  · exact B1301775
  · exact B1301779
  · exact B1301783
  · exact B1301787
  · exact B1301791
  · exact B1301795
  · exact B1301799
  · exact B1301803
  · exact B1301807
  · exact B1301811
  · exact B1301815
  · exact B1301819
  · exact B1301823
  · exact B1301827
  · exact B1301831
  · exact B1301835
  · exact B1301839
  · exact B1301843
  · exact B1301847
  · exact B1301851
  · exact B1301855
  · exact B1301859
  · exact B1301863
  · exact B1301867
  · exact B1301871
  · exact B1301875
  · exact B1301879
  · exact B1301883
  · exact B1301887
  · exact B1301891
  · exact B1301895
  · exact B1301899
  · exact B1301903
  · exact B1301907
  · exact B1301911
  · exact B1301915
  · exact B1301919
  · exact B1301923
  · exact B1301927
  · exact B1301931
  · exact B1301935
  · exact B1301939
  · exact B1301943
  · exact B1301947
  · exact B1301951
  · exact B1301955
  · exact B1301959
  · exact B1301963
  · exact B1301967

theorem solution (m : ℕ) (hlo : 1299968 ≤ m) (hhi : m ≤ 1301968) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 324992 ≤ j := by omega
    have hj2 : j ≤ 325491 := by omega
    have hb : Blo 1299968 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
