-- Prove2me | solution 1 for syracuse_descends_range_1636017_1638017
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:15:28.237127+00:00
-- url     : https://prove2.me/submissions/5c74745e-6c98-4cec-98f4-3702a8f48aaa

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


theorem B3784717 : Blo 1636017 3784717 := bbase (se 3 (by rfl) ⟨709634, by rfl⟩ : syracuseStep 3784717 = 1419269) (by norm_num)
theorem B4145165 : Blo 1636017 4145165 := bbase (se 3 (by rfl) ⟨777218, by rfl⟩ : syracuseStep 4145165 = 1554437) (by norm_num)
theorem B3498005 : Blo 1636017 3498005 := bbase (se 6 (by rfl) ⟨81984, by rfl⟩ : syracuseStep 3498005 = 163969) (by norm_num)
theorem B2801701 : Blo 1636017 2801701 := bbase (se 4 (by rfl) ⟨262659, by rfl⟩ : syracuseStep 2801701 = 525319) (by norm_num)
theorem B4661317 : Blo 1636017 4661317 := bbase (se 4 (by rfl) ⟨436998, by rfl⟩ : syracuseStep 4661317 = 873997) (by norm_num)
theorem B2760797 : Blo 1636017 2760797 := bbase (se 3 (by rfl) ⟨517649, by rfl⟩ : syracuseStep 2760797 = 1035299) (by norm_num)
theorem B6635621 : Blo 1636017 6635621 := bbase (se 4 (by rfl) ⟨622089, by rfl⟩ : syracuseStep 6635621 = 1244179) (by norm_num)
theorem B2949221 : Blo 1636017 2949221 := bbase (se 4 (by rfl) ⟨276489, by rfl⟩ : syracuseStep 2949221 = 552979) (by norm_num)
theorem B9322613 : Blo 1636017 9322613 := bbase (se 5 (by rfl) ⟨436997, by rfl⟩ : syracuseStep 9322613 = 873995) (by norm_num)
theorem B2072729 : Blo 1636017 2072729 := bbase (se 2 (by rfl) ⟨777273, by rfl⟩ : syracuseStep 2072729 = 1554547) (by norm_num)
theorem B4145357 : Blo 1636017 4145357 := bbase (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) (by norm_num)
theorem B2072785 : Blo 1636017 2072785 := bbase (se 2 (by rfl) ⟨777294, by rfl⟩ : syracuseStep 2072785 = 1554589) (by norm_num)
theorem B2760925 : Blo 1636017 2760925 := bbase (se 3 (by rfl) ⟨517673, by rfl⟩ : syracuseStep 2760925 = 1035347) (by norm_num)
theorem B4423909 : Blo 1636017 4423909 := bbase (se 4 (by rfl) ⟨414741, by rfl⟩ : syracuseStep 4423909 = 829483) (by norm_num)
theorem B9953525 : Blo 1636017 9953525 := bbase (se 5 (by rfl) ⟨466571, by rfl⟩ : syracuseStep 9953525 = 933143) (by norm_num)
theorem B6218005 : Blo 1636017 6218005 := bbase (se 6 (by rfl) ⟨145734, by rfl⟩ : syracuseStep 6218005 = 291469) (by norm_num)
theorem B2105633 : Blo 1636017 2105633 := bbase (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) (by norm_num)
theorem B2072881 : Blo 1636017 2072881 := bbase (se 2 (by rfl) ⟨777330, by rfl⟩ : syracuseStep 2072881 = 1554661) (by norm_num)
theorem B2761013 : Blo 1636017 2761013 := bbase (se 5 (by rfl) ⟨129422, by rfl⟩ : syracuseStep 2761013 = 258845) (by norm_num)
theorem B4424005 : Blo 1636017 4424005 := bbase (se 4 (by rfl) ⟨414750, by rfl⟩ : syracuseStep 4424005 = 829501) (by norm_num)
theorem B23601557 : Blo 1636017 23601557 := bbase (se 6 (by rfl) ⟨553161, by rfl⟩ : syracuseStep 23601557 = 1106323) (by norm_num)
theorem B1966513 : Blo 1636017 1966513 := bbase (se 2 (by rfl) ⟨737442, by rfl⟩ : syracuseStep 1966513 = 1474885) (by norm_num)
theorem B2761141 : Blo 1636017 2761141 := bbase (se 5 (by rfl) ⟨129428, by rfl⟩ : syracuseStep 2761141 = 258857) (by norm_num)
theorem B5521877 : Blo 1636017 5521877 := bbase (se 7 (by rfl) ⟨64709, by rfl⟩ : syracuseStep 5521877 = 129419) (by norm_num)
theorem B2073053 : Blo 1636017 2073053 := bbase (se 3 (by rfl) ⟨388697, by rfl⟩ : syracuseStep 2073053 = 777395) (by norm_num)
theorem B2761229 : Blo 1636017 2761229 := bbase (se 3 (by rfl) ⟨517730, by rfl⟩ : syracuseStep 2761229 = 1035461) (by norm_num)
theorem B2073109 : Blo 1636017 2073109 := bbase (se 6 (by rfl) ⟨48588, by rfl⟩ : syracuseStep 2073109 = 97177) (by norm_num)
theorem B4145701 : Blo 1636017 4145701 := bbase (se 4 (by rfl) ⟨388659, by rfl⟩ : syracuseStep 4145701 = 777319) (by norm_num)
theorem B6218309 : Blo 1636017 6218309 := bbase (se 4 (by rfl) ⟨582966, by rfl⟩ : syracuseStep 6218309 = 1165933) (by norm_num)
theorem B2761357 : Blo 1636017 2761357 := bbase (se 3 (by rfl) ⟨517754, by rfl⟩ : syracuseStep 2761357 = 1035509) (by norm_num)
theorem B4145813 : Blo 1636017 4145813 := bbase (se 6 (by rfl) ⟨97167, by rfl⟩ : syracuseStep 4145813 = 194335) (by norm_num)
theorem B8290997 : Blo 1636017 8290997 := bbase (se 5 (by rfl) ⟨388640, by rfl⟩ : syracuseStep 8290997 = 777281) (by norm_num)
theorem B2761445 : Blo 1636017 2761445 := bbase (se 4 (by rfl) ⟨258885, by rfl⟩ : syracuseStep 2761445 = 517771) (by norm_num)
theorem B9454357 : Blo 1636017 9454357 := bbase (se 6 (by rfl) ⟨221586, by rfl⟩ : syracuseStep 9454357 = 443173) (by norm_num)
theorem B4146005 : Blo 1636017 4146005 := bbase (se 9 (by rfl) ⟨12146, by rfl⟩ : syracuseStep 4146005 = 24293) (by norm_num)
theorem B2761573 : Blo 1636017 2761573 := bbase (se 4 (by rfl) ⟨258897, by rfl⟩ : syracuseStep 2761573 = 517795) (by norm_num)
theorem B3318653 : Blo 1636017 3318653 := bbase (se 3 (by rfl) ⟨622247, by rfl⟩ : syracuseStep 3318653 = 1244495) (by norm_num)
theorem B5522309 : Blo 1636017 5522309 := bbase (se 4 (by rfl) ⟨517716, by rfl⟩ : syracuseStep 5522309 = 1035433) (by norm_num)
theorem B1966993 : Blo 1636017 1966993 := bbase (se 2 (by rfl) ⟨737622, by rfl⟩ : syracuseStep 1966993 = 1475245) (by norm_num)
theorem B2761661 : Blo 1636017 2761661 := bbase (se 3 (by rfl) ⟨517811, by rfl⟩ : syracuseStep 2761661 = 1035623) (by norm_num)
theorem B2761789 : Blo 1636017 2761789 := bbase (se 3 (by rfl) ⟨517835, by rfl⟩ : syracuseStep 2761789 = 1035671) (by norm_num)
theorem B2212933 : Blo 1636017 2212933 := bbase (se 4 (by rfl) ⟨207462, by rfl⟩ : syracuseStep 2212933 = 414925) (by norm_num)
theorem B8283221 : Blo 1636017 8283221 := bbase (se 8 (by rfl) ⟨48534, by rfl⟩ : syracuseStep 8283221 = 97069) (by norm_num)
theorem B2761877 : Blo 1636017 2761877 := bbase (se 6 (by rfl) ⟨64731, by rfl⟩ : syracuseStep 2761877 = 129463) (by norm_num)
theorem B3105965 : Blo 1636017 3105965 := bbase (se 3 (by rfl) ⟨582368, by rfl⟩ : syracuseStep 3105965 = 1164737) (by norm_num)
theorem B2622709 : Blo 1636017 2622709 := bbase (se 5 (by rfl) ⟨122939, by rfl⟩ : syracuseStep 2622709 = 245879) (by norm_num)
theorem B2762005 : Blo 1636017 2762005 := bbase (se 6 (by rfl) ⟨64734, by rfl⟩ : syracuseStep 2762005 = 129469) (by norm_num)
theorem B13985045 : Blo 1636017 13985045 := bbase (se 6 (by rfl) ⟨327774, by rfl⟩ : syracuseStep 13985045 = 655549) (by norm_num)
theorem B5522741 : Blo 1636017 5522741 := bbase (se 5 (by rfl) ⟨258878, by rfl⟩ : syracuseStep 5522741 = 517757) (by norm_num)
theorem B3106117 : Blo 1636017 3106117 := bbase (se 4 (by rfl) ⟨291198, by rfl⟩ : syracuseStep 3106117 = 582397) (by norm_num)
theorem B3933517 : Blo 1636017 3933517 := bbase (se 3 (by rfl) ⟨737534, by rfl⟩ : syracuseStep 3933517 = 1475069) (by norm_num)
theorem B2762093 : Blo 1636017 2762093 := bbase (se 3 (by rfl) ⟨517892, by rfl⟩ : syracuseStep 2762093 = 1035785) (by norm_num)
theorem B13976981 : Blo 1636017 13976981 := bbase (se 6 (by rfl) ⟨327585, by rfl⟩ : syracuseStep 13976981 = 655171) (by norm_num)
theorem B31450517 : Blo 1636017 31450517 := bbase (se 6 (by rfl) ⟨737121, by rfl⟩ : syracuseStep 31450517 = 1474243) (by norm_num)
theorem B4425173 : Blo 1636017 4425173 := bbase (se 7 (by rfl) ⟨51857, by rfl⟩ : syracuseStep 4425173 = 103715) (by norm_num)
theorem B1770977 : Blo 1636017 1770977 := bbase (se 2 (by rfl) ⟨664116, by rfl⟩ : syracuseStep 1770977 = 1328233) (by norm_num)
theorem B2762221 : Blo 1636017 2762221 := bbase (se 3 (by rfl) ⟨517916, by rfl⟩ : syracuseStep 2762221 = 1035833) (by norm_num)
theorem B4662821 : Blo 1636017 4662821 := bbase (se 4 (by rfl) ⟨437139, by rfl⟩ : syracuseStep 4662821 = 874279) (by norm_num)
theorem B1795649 : Blo 1636017 1795649 := bbase (se 2 (by rfl) ⟨673368, by rfl⟩ : syracuseStep 1795649 = 1346737) (by norm_num)
theorem B2762309 : Blo 1636017 2762309 := bbase (se 4 (by rfl) ⟨258966, by rfl⟩ : syracuseStep 2762309 = 517933) (by norm_num)
theorem B3106421 : Blo 1636017 3106421 := bbase (se 5 (by rfl) ⟨145613, by rfl⟩ : syracuseStep 3106421 = 291227) (by norm_num)
theorem B2393765 : Blo 1636017 2393765 := bbase (se 4 (by rfl) ⟨224415, by rfl⟩ : syracuseStep 2393765 = 448831) (by norm_num)
theorem B2762437 : Blo 1636017 2762437 := bbase (se 4 (by rfl) ⟨258978, by rfl⟩ : syracuseStep 2762437 = 517957) (by norm_num)
theorem B5523173 : Blo 1636017 5523173 := bbase (se 4 (by rfl) ⟨517797, by rfl⟩ : syracuseStep 5523173 = 1035595) (by norm_num)
theorem B2762525 : Blo 1636017 2762525 := bbase (se 3 (by rfl) ⟨517973, by rfl⟩ : syracuseStep 2762525 = 1035947) (by norm_num)
theorem B8398741 : Blo 1636017 8398741 := bbase (se 6 (by rfl) ⟨196845, by rfl⟩ : syracuseStep 8398741 = 393691) (by norm_num)
theorem B2762653 : Blo 1636017 2762653 := bbase (se 3 (by rfl) ⟨517997, by rfl⟩ : syracuseStep 2762653 = 1035995) (by norm_num)
theorem B3934133 : Blo 1636017 3934133 := bbase (se 5 (by rfl) ⟨184412, by rfl⟩ : syracuseStep 3934133 = 368825) (by norm_num)
theorem B2623421 : Blo 1636017 2623421 := bbase (se 3 (by rfl) ⟨491891, by rfl⟩ : syracuseStep 2623421 = 983783) (by norm_num)
theorem B8292293 : Blo 1636017 8292293 := bbase (se 4 (by rfl) ⟨777402, by rfl⟩ : syracuseStep 8292293 = 1554805) (by norm_num)
theorem B2762741 : Blo 1636017 2762741 := bbase (se 5 (by rfl) ⟨129503, by rfl⟩ : syracuseStep 2762741 = 259007) (by norm_num)
theorem B6383717 : Blo 1636017 6383717 := bbase (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) (by norm_num)
theorem B2762869 : Blo 1636017 2762869 := bbase (se 5 (by rfl) ⟨129509, by rfl⟩ : syracuseStep 2762869 = 259019) (by norm_num)
theorem B5523605 : Blo 1636017 5523605 := bbase (se 6 (by rfl) ⟨129459, by rfl⟩ : syracuseStep 5523605 = 258919) (by norm_num)
theorem B2762957 : Blo 1636017 2762957 := bbase (se 3 (by rfl) ⟨518054, by rfl⟩ : syracuseStep 2762957 = 1036109) (by norm_num)
theorem B7866629 : Blo 1636017 7866629 := bbase (se 4 (by rfl) ⟨737496, by rfl⟩ : syracuseStep 7866629 = 1474993) (by norm_num)
theorem B1747217 : Blo 1636017 1747217 := bbase (se 2 (by rfl) ⟨655206, by rfl⟩ : syracuseStep 1747217 = 1310413) (by norm_num)
theorem B9324821 : Blo 1636017 9324821 := bbase (se 6 (by rfl) ⟨218550, by rfl⟩ : syracuseStep 9324821 = 437101) (by norm_num)
theorem B2763085 : Blo 1636017 2763085 := bbase (se 3 (by rfl) ⟨518078, by rfl⟩ : syracuseStep 2763085 = 1036157) (by norm_num)
theorem B8284517 : Blo 1636017 8284517 := bbase (se 4 (by rfl) ⟨776673, by rfl⟩ : syracuseStep 8284517 = 1553347) (by norm_num)
theorem B3107173 : Blo 1636017 3107173 := bbase (se 4 (by rfl) ⟨291297, by rfl⟩ : syracuseStep 3107173 = 582595) (by norm_num)
theorem B12954005 : Blo 1636017 12954005 := bbase (se 6 (by rfl) ⟨303609, by rfl⟩ : syracuseStep 12954005 = 607219) (by norm_num)
theorem B2763173 : Blo 1636017 2763173 := bbase (se 4 (by rfl) ⟨259047, by rfl⟩ : syracuseStep 2763173 = 518095) (by norm_num)
theorem B7866821 : Blo 1636017 7866821 := bbase (se 4 (by rfl) ⟨737514, by rfl⟩ : syracuseStep 7866821 = 1475029) (by norm_num)
theorem B3107317 : Blo 1636017 3107317 := bbase (se 5 (by rfl) ⟨145655, by rfl⟩ : syracuseStep 3107317 = 291311) (by norm_num)
theorem B2763301 : Blo 1636017 2763301 := bbase (se 4 (by rfl) ⟨259059, by rfl⟩ : syracuseStep 2763301 = 518119) (by norm_num)
theorem B5524037 : Blo 1636017 5524037 := bbase (se 4 (by rfl) ⟨517878, by rfl⟩ : syracuseStep 5524037 = 1035757) (by norm_num)
theorem B2763389 : Blo 1636017 2763389 := bbase (se 3 (by rfl) ⟨518135, by rfl⟩ : syracuseStep 2763389 = 1036271) (by norm_num)
theorem B3107477 : Blo 1636017 3107477 := bbase (se 6 (by rfl) ⟨72831, by rfl⟩ : syracuseStep 3107477 = 145663) (by norm_num)
theorem B2099881 : Blo 1636017 2099881 := bbase (se 2 (by rfl) ⟨787455, by rfl⟩ : syracuseStep 2099881 = 1574911) (by norm_num)
theorem B12438197 : Blo 1636017 12438197 := bbase (se 5 (by rfl) ⟨583040, by rfl⟩ : syracuseStep 12438197 = 1166081) (by norm_num)
theorem B3934909 : Blo 1636017 3934909 := bbase (se 3 (by rfl) ⟨737795, by rfl⟩ : syracuseStep 3934909 = 1475591) (by norm_num)
theorem B1747661 : Blo 1636017 1747661 := bbase (se 3 (by rfl) ⟨327686, by rfl⟩ : syracuseStep 1747661 = 655373) (by norm_num)
theorem B2763517 : Blo 1636017 2763517 := bbase (se 3 (by rfl) ⟨518159, by rfl⟩ : syracuseStep 2763517 = 1036319) (by norm_num)
theorem B3681053 : Blo 1636017 3681053 := bbase (se 3 (by rfl) ⟨690197, by rfl⟩ : syracuseStep 3681053 = 1380395) (by norm_num)
theorem B3107621 : Blo 1636017 3107621 := bbase (se 4 (by rfl) ⟨291339, by rfl⟩ : syracuseStep 3107621 = 582679) (by norm_num)
theorem B7867205 : Blo 1636017 7867205 := bbase (se 4 (by rfl) ⟨737550, by rfl⟩ : syracuseStep 7867205 = 1475101) (by norm_num)
theorem B2763605 : Blo 1636017 2763605 := bbase (se 9 (by rfl) ⟨8096, by rfl⟩ : syracuseStep 2763605 = 16193) (by norm_num)
theorem B2100065 : Blo 1636017 2100065 := bbase (se 2 (by rfl) ⟨787524, by rfl⟩ : syracuseStep 2100065 = 1575049) (by norm_num)
theorem B3681125 : Blo 1636017 3681125 := bbase (se 4 (by rfl) ⟨345105, by rfl⟩ : syracuseStep 3681125 = 690211) (by norm_num)
theorem B3681197 : Blo 1636017 3681197 := bbase (se 3 (by rfl) ⟨690224, by rfl⟩ : syracuseStep 3681197 = 1380449) (by norm_num)
theorem B1747909 : Blo 1636017 1747909 := bbase (se 4 (by rfl) ⟨163866, by rfl⟩ : syracuseStep 1747909 = 327733) (by norm_num)
theorem B2763733 : Blo 1636017 2763733 := bbase (se 7 (by rfl) ⟨32387, by rfl⟩ : syracuseStep 2763733 = 64775) (by norm_num)
theorem B2329565 : Blo 1636017 2329565 := bbase (se 3 (by rfl) ⟨436793, by rfl⟩ : syracuseStep 2329565 = 873587) (by norm_num)
theorem B3681269 : Blo 1636017 3681269 := bbase (se 5 (by rfl) ⟨172559, by rfl⟩ : syracuseStep 3681269 = 345119) (by norm_num)
theorem B5524469 : Blo 1636017 5524469 := bbase (se 5 (by rfl) ⟨258959, by rfl⟩ : syracuseStep 5524469 = 517919) (by norm_num)
theorem B6212645 : Blo 1636017 6212645 := bbase (se 4 (by rfl) ⟨582435, by rfl⟩ : syracuseStep 6212645 = 1164871) (by norm_num)
theorem B2763821 : Blo 1636017 2763821 := bbase (se 3 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 2763821 = 1036433) (by norm_num)
theorem B3681341 : Blo 1636017 3681341 := bbase (se 3 (by rfl) ⟨690251, by rfl⟩ : syracuseStep 3681341 = 1380503) (by norm_num)
theorem B3107909 : Blo 1636017 3107909 := bbase (se 4 (by rfl) ⟨291366, by rfl⟩ : syracuseStep 3107909 = 582733) (by norm_num)
theorem B5246021 : Blo 1636017 5246021 := bbase (se 4 (by rfl) ⟨491814, by rfl⟩ : syracuseStep 5246021 = 983629) (by norm_num)
theorem B12430421 : Blo 1636017 12430421 := bbase (se 8 (by rfl) ⟨72834, by rfl⟩ : syracuseStep 12430421 = 145669) (by norm_num)
theorem B4664405 : Blo 1636017 4664405 := bbase (se 8 (by rfl) ⟨27330, by rfl⟩ : syracuseStep 4664405 = 54661) (by norm_num)
theorem B15740021 : Blo 1636017 15740021 := bbase (se 5 (by rfl) ⟨737813, by rfl⟩ : syracuseStep 15740021 = 1475627) (by norm_num)
theorem B3681413 : Blo 1636017 3681413 := bbase (se 4 (by rfl) ⟨345132, by rfl⟩ : syracuseStep 3681413 = 690265) (by norm_num)
theorem B2763949 : Blo 1636017 2763949 := bbase (se 3 (by rfl) ⟨518240, by rfl⟩ : syracuseStep 2763949 = 1036481) (by norm_num)
theorem B3681485 : Blo 1636017 3681485 := bbase (se 3 (by rfl) ⟨690278, by rfl⟩ : syracuseStep 3681485 = 1380557) (by norm_num)
theorem B3108061 : Blo 1636017 3108061 := bbase (se 3 (by rfl) ⟨582761, by rfl⟩ : syracuseStep 3108061 = 1165523) (by norm_num)
theorem B2764037 : Blo 1636017 2764037 := bbase (se 4 (by rfl) ⟨259128, by rfl⟩ : syracuseStep 2764037 = 518257) (by norm_num)
theorem B1772813 : Blo 1636017 1772813 := bbase (se 3 (by rfl) ⟨332402, by rfl⟩ : syracuseStep 1772813 = 664805) (by norm_num)
theorem B3681557 : Blo 1636017 3681557 := bbase (se 6 (by rfl) ⟨86286, by rfl⟩ : syracuseStep 3681557 = 172573) (by norm_num)
theorem B6212933 : Blo 1636017 6212933 := bbase (se 4 (by rfl) ⟨582462, by rfl⟩ : syracuseStep 6212933 = 1164925) (by norm_num)
theorem B3681629 : Blo 1636017 3681629 := bbase (se 3 (by rfl) ⟨690305, by rfl⟩ : syracuseStep 3681629 = 1380611) (by norm_num)
theorem B1748353 : Blo 1636017 1748353 := bbase (se 2 (by rfl) ⟨655632, by rfl⟩ : syracuseStep 1748353 = 1311265) (by norm_num)
theorem B3935621 : Blo 1636017 3935621 := bbase (se 4 (by rfl) ⟨368964, by rfl⟩ : syracuseStep 3935621 = 737929) (by norm_num)
theorem B3681701 : Blo 1636017 3681701 := bbase (se 4 (by rfl) ⟨345159, by rfl⟩ : syracuseStep 3681701 = 690319) (by norm_num)
theorem B5524901 : Blo 1636017 5524901 := bbase (se 4 (by rfl) ⟨517959, by rfl⟩ : syracuseStep 5524901 = 1035919) (by norm_num)
theorem B1748413 : Blo 1636017 1748413 := bbase (se 3 (by rfl) ⟨327827, by rfl⟩ : syracuseStep 1748413 = 655655) (by norm_num)
theorem B3681773 : Blo 1636017 3681773 := bbase (se 3 (by rfl) ⟨690332, by rfl⟩ : syracuseStep 3681773 = 1380665) (by norm_num)
theorem B3108365 : Blo 1636017 3108365 := bbase (se 3 (by rfl) ⟨582818, by rfl⟩ : syracuseStep 3108365 = 1165637) (by norm_num)
theorem B2428453 : Blo 1636017 2428453 := bbase (se 4 (by rfl) ⟨227667, by rfl⟩ : syracuseStep 2428453 = 455335) (by norm_num)
theorem B3681845 : Blo 1636017 3681845 := bbase (se 5 (by rfl) ⟨172586, by rfl⟩ : syracuseStep 3681845 = 345173) (by norm_num)
theorem B6991429 : Blo 1636017 6991429 := bbase (se 4 (by rfl) ⟨655446, by rfl⟩ : syracuseStep 6991429 = 1310893) (by norm_num)
theorem B8285813 : Blo 1636017 8285813 := bbase (se 5 (by rfl) ⟨388397, by rfl⟩ : syracuseStep 8285813 = 776795) (by norm_num)
theorem B3681917 : Blo 1636017 3681917 := bbase (se 3 (by rfl) ⟨690359, by rfl⟩ : syracuseStep 3681917 = 1380719) (by norm_num)
theorem B3681989 : Blo 1636017 3681989 := bbase (se 4 (by rfl) ⟨345186, by rfl⟩ : syracuseStep 3681989 = 690373) (by norm_num)
theorem B2330317 : Blo 1636017 2330317 := bbase (se 3 (by rfl) ⟨436934, by rfl⟩ : syracuseStep 2330317 = 873869) (by norm_num)
theorem B6639317 : Blo 1636017 6639317 := bbase (se 7 (by rfl) ⟨77804, by rfl⟩ : syracuseStep 6639317 = 155609) (by norm_num)
theorem B1748729 : Blo 1636017 1748729 := bbase (se 2 (by rfl) ⟨655773, by rfl⟩ : syracuseStep 1748729 = 1311547) (by norm_num)
theorem B2838277 : Blo 1636017 2838277 := bbase (se 4 (by rfl) ⟨266088, by rfl⟩ : syracuseStep 2838277 = 532177) (by norm_num)
theorem B3682061 : Blo 1636017 3682061 := bbase (se 3 (by rfl) ⟨690386, by rfl⟩ : syracuseStep 3682061 = 1380773) (by norm_num)
theorem B3682133 : Blo 1636017 3682133 := bbase (se 9 (by rfl) ⟨10787, by rfl⟩ : syracuseStep 3682133 = 21575) (by norm_num)
theorem B5525333 : Blo 1636017 5525333 := bbase (se 9 (by rfl) ⟨16187, by rfl⟩ : syracuseStep 5525333 = 32375) (by norm_num)
theorem B3682205 : Blo 1636017 3682205 := bbase (se 3 (by rfl) ⟨690413, by rfl⟩ : syracuseStep 3682205 = 1380827) (by norm_num)
theorem B47173589 : Blo 1636017 47173589 := bbase (se 7 (by rfl) ⟨552815, by rfl⟩ : syracuseStep 47173589 = 1105631) (by norm_num)
theorem B3682277 : Blo 1636017 3682277 := bbase (se 4 (by rfl) ⟨345213, by rfl⟩ : syracuseStep 3682277 = 690427) (by norm_num)
theorem B3682349 : Blo 1636017 3682349 := bbase (se 3 (by rfl) ⟨690440, by rfl⟩ : syracuseStep 3682349 = 1380881) (by norm_num)
theorem B3682421 : Blo 1636017 3682421 := bbase (se 5 (by rfl) ⟨172613, by rfl⟩ : syracuseStep 3682421 = 345227) (by norm_num)
theorem B5247109 : Blo 1636017 5247109 := bbase (se 4 (by rfl) ⟨491916, by rfl⟩ : syracuseStep 5247109 = 983833) (by norm_num)
theorem B1749173 : Blo 1636017 1749173 := bbase (se 5 (by rfl) ⟨81992, by rfl⟩ : syracuseStep 1749173 = 163985) (by norm_num)
theorem B3682493 : Blo 1636017 3682493 := bbase (se 3 (by rfl) ⟨690467, by rfl⟩ : syracuseStep 3682493 = 1380935) (by norm_num)
theorem B4141277 : Blo 1636017 4141277 := bbase (se 3 (by rfl) ⟨776489, by rfl⟩ : syracuseStep 4141277 = 1552979) (by norm_num)
theorem B3109117 : Blo 1636017 3109117 := bbase (se 3 (by rfl) ⟨582959, by rfl⟩ : syracuseStep 3109117 = 1165919) (by norm_num)
theorem B3682565 : Blo 1636017 3682565 := bbase (se 4 (by rfl) ⟨345240, by rfl⟩ : syracuseStep 3682565 = 690481) (by norm_num)
theorem B5525765 : Blo 1636017 5525765 := bbase (se 4 (by rfl) ⟨518040, by rfl⟩ : syracuseStep 5525765 = 1036081) (by norm_num)
theorem B3682637 : Blo 1636017 3682637 := bbase (se 3 (by rfl) ⟨690494, by rfl⟩ : syracuseStep 3682637 = 1380989) (by norm_num)
theorem B4198765 : Blo 1636017 4198765 := bbase (se 3 (by rfl) ⟨787268, by rfl⟩ : syracuseStep 4198765 = 1574537) (by norm_num)
theorem B3109261 : Blo 1636017 3109261 := bbase (se 3 (by rfl) ⟨582986, by rfl⟩ : syracuseStep 3109261 = 1165973) (by norm_num)
theorem B3682709 : Blo 1636017 3682709 := bbase (se 6 (by rfl) ⟨86313, by rfl⟩ : syracuseStep 3682709 = 172627) (by norm_num)
theorem B22409621 : Blo 1636017 22409621 := bbase (se 6 (by rfl) ⟨525225, by rfl⟩ : syracuseStep 22409621 = 1050451) (by norm_num)
theorem B4141469 : Blo 1636017 4141469 := bbase (se 3 (by rfl) ⟨776525, by rfl⟩ : syracuseStep 4141469 = 1553051) (by norm_num)
theorem B3682781 : Blo 1636017 3682781 := bbase (se 3 (by rfl) ⟨690521, by rfl⟩ : syracuseStep 3682781 = 1381043) (by norm_num)
theorem B6214117 : Blo 1636017 6214117 := bbase (se 4 (by rfl) ⟨582573, by rfl⟩ : syracuseStep 6214117 = 1165147) (by norm_num)
theorem B2331109 : Blo 1636017 2331109 := bbase (se 4 (by rfl) ⟨218541, by rfl⟩ : syracuseStep 2331109 = 437083) (by norm_num)
theorem B2454029 : Blo 1636017 2454029 := bbase (se 3 (by rfl) ⟨460130, by rfl⟩ : syracuseStep 2454029 = 920261) (by norm_num)
theorem B2454053 : Blo 1636017 2454053 := bbase (se 4 (by rfl) ⟨230067, by rfl⟩ : syracuseStep 2454053 = 460135) (by norm_num)
theorem B3682853 : Blo 1636017 3682853 := bbase (se 4 (by rfl) ⟨345267, by rfl⟩ : syracuseStep 3682853 = 690535) (by norm_num)
theorem B3109421 : Blo 1636017 3109421 := bbase (se 3 (by rfl) ⟨583016, by rfl⟩ : syracuseStep 3109421 = 1166033) (by norm_num)
theorem B2454077 : Blo 1636017 2454077 := bbase (se 3 (by rfl) ⟨460139, by rfl⟩ : syracuseStep 2454077 = 920279) (by norm_num)
theorem B3494477 : Blo 1636017 3494477 := bbase (se 3 (by rfl) ⟨655214, by rfl⟩ : syracuseStep 3494477 = 1310429) (by norm_num)
theorem B2454101 : Blo 1636017 2454101 := bbase (se 8 (by rfl) ⟨14379, by rfl⟩ : syracuseStep 2454101 = 28759) (by norm_num)
theorem B2454125 : Blo 1636017 2454125 := bbase (se 3 (by rfl) ⟨460148, by rfl⟩ : syracuseStep 2454125 = 920297) (by norm_num)
theorem B3682925 : Blo 1636017 3682925 := bbase (se 3 (by rfl) ⟨690548, by rfl⟩ : syracuseStep 3682925 = 1381097) (by norm_num)
theorem B2454149 : Blo 1636017 2454149 := bbase (se 4 (by rfl) ⟨230076, by rfl⟩ : syracuseStep 2454149 = 460153) (by norm_num)
theorem B2454173 : Blo 1636017 2454173 := bbase (se 3 (by rfl) ⟨460157, by rfl⟩ : syracuseStep 2454173 = 920315) (by norm_num)
theorem B2454197 : Blo 1636017 2454197 := bbase (se 5 (by rfl) ⟨115040, by rfl⟩ : syracuseStep 2454197 = 230081) (by norm_num)
theorem B3682997 : Blo 1636017 3682997 := bbase (se 5 (by rfl) ⟨172640, by rfl⟩ : syracuseStep 3682997 = 345281) (by norm_num)
theorem B5526197 : Blo 1636017 5526197 := bbase (se 5 (by rfl) ⟨259040, by rfl⟩ : syracuseStep 5526197 = 518081) (by norm_num)
theorem B3109565 : Blo 1636017 3109565 := bbase (se 3 (by rfl) ⟨583043, by rfl⟩ : syracuseStep 3109565 = 1166087) (by norm_num)
theorem B2454221 : Blo 1636017 2454221 := bbase (se 3 (by rfl) ⟨460166, by rfl⟩ : syracuseStep 2454221 = 920333) (by norm_num)
theorem B3494621 : Blo 1636017 3494621 := bbase (se 3 (by rfl) ⟨655241, by rfl⟩ : syracuseStep 3494621 = 1310483) (by norm_num)
theorem B2454245 : Blo 1636017 2454245 := bbase (se 4 (by rfl) ⟨230085, by rfl⟩ : syracuseStep 2454245 = 460171) (by norm_num)
theorem B4141813 : Blo 1636017 4141813 := bbase (se 5 (by rfl) ⟨194147, by rfl⟩ : syracuseStep 4141813 = 388295) (by norm_num)
theorem B2454269 : Blo 1636017 2454269 := bbase (se 3 (by rfl) ⟨460175, by rfl⟩ : syracuseStep 2454269 = 920351) (by norm_num)
theorem B3683069 : Blo 1636017 3683069 := bbase (se 3 (by rfl) ⟨690575, by rfl⟩ : syracuseStep 3683069 = 1381151) (by norm_num)
theorem B2454293 : Blo 1636017 2454293 := bbase (se 6 (by rfl) ⟨57522, by rfl⟩ : syracuseStep 2454293 = 115045) (by norm_num)
theorem B6214421 : Blo 1636017 6214421 := bbase (se 6 (by rfl) ⟨145650, by rfl⟩ : syracuseStep 6214421 = 291301) (by norm_num)
theorem B2454317 : Blo 1636017 2454317 := bbase (se 3 (by rfl) ⟨460184, by rfl⟩ : syracuseStep 2454317 = 920369) (by norm_num)
theorem B2331445 : Blo 1636017 2331445 := bbase (se 5 (by rfl) ⟨109286, by rfl⟩ : syracuseStep 2331445 = 218573) (by norm_num)
theorem B2454341 : Blo 1636017 2454341 := bbase (se 4 (by rfl) ⟨230094, by rfl⟩ : syracuseStep 2454341 = 460189) (by norm_num)
theorem B3683141 : Blo 1636017 3683141 := bbase (se 4 (by rfl) ⟨345294, by rfl⟩ : syracuseStep 3683141 = 690589) (by norm_num)
theorem B2454365 : Blo 1636017 2454365 := bbase (se 3 (by rfl) ⟨460193, by rfl⟩ : syracuseStep 2454365 = 920387) (by norm_num)
theorem B4141925 : Blo 1636017 4141925 := bbase (se 4 (by rfl) ⟨388305, by rfl⟩ : syracuseStep 4141925 = 776611) (by norm_num)
theorem B2454389 : Blo 1636017 2454389 := bbase (se 5 (by rfl) ⟨115049, by rfl⟩ : syracuseStep 2454389 = 230099) (by norm_num)
theorem B4977541 : Blo 1636017 4977541 := bbase (se 4 (by rfl) ⟨466644, by rfl⟩ : syracuseStep 4977541 = 933289) (by norm_num)
theorem B8287109 : Blo 1636017 8287109 := bbase (se 4 (by rfl) ⟨776916, by rfl⟩ : syracuseStep 8287109 = 1553833) (by norm_num)
theorem B1659781 : Blo 1636017 1659781 := bbase (se 4 (by rfl) ⟨155604, by rfl⟩ : syracuseStep 1659781 = 311209) (by norm_num)
theorem B2454413 : Blo 1636017 2454413 := bbase (se 3 (by rfl) ⟨460202, by rfl⟩ : syracuseStep 2454413 = 920405) (by norm_num)
theorem B3683213 : Blo 1636017 3683213 := bbase (se 3 (by rfl) ⟨690602, by rfl⟩ : syracuseStep 3683213 = 1381205) (by norm_num)
theorem B2454437 : Blo 1636017 2454437 := bbase (se 4 (by rfl) ⟨230103, by rfl⟩ : syracuseStep 2454437 = 460207) (by norm_num)
theorem B1659821 : Blo 1636017 1659821 := bbase (se 3 (by rfl) ⟨311216, by rfl⟩ : syracuseStep 1659821 = 622433) (by norm_num)
theorem B2454461 : Blo 1636017 2454461 := bbase (se 3 (by rfl) ⟨460211, by rfl⟩ : syracuseStep 2454461 = 920423) (by norm_num)
theorem B2454485 : Blo 1636017 2454485 := bbase (se 7 (by rfl) ⟨28763, by rfl⟩ : syracuseStep 2454485 = 57527) (by norm_num)
theorem B3683285 : Blo 1636017 3683285 := bbase (se 7 (by rfl) ⟨43163, by rfl⟩ : syracuseStep 3683285 = 86327) (by norm_num)
theorem B2454509 : Blo 1636017 2454509 := bbase (se 3 (by rfl) ⟨460220, by rfl⟩ : syracuseStep 2454509 = 920441) (by norm_num)
theorem B2454533 : Blo 1636017 2454533 := bbase (se 4 (by rfl) ⟨230112, by rfl⟩ : syracuseStep 2454533 = 460225) (by norm_num)
theorem B2331661 : Blo 1636017 2331661 := bbase (se 3 (by rfl) ⟨437186, by rfl⟩ : syracuseStep 2331661 = 874373) (by norm_num)
theorem B9319445 : Blo 1636017 9319445 := bbase (se 6 (by rfl) ⟨218424, by rfl⟩ : syracuseStep 9319445 = 436849) (by norm_num)
theorem B2454557 : Blo 1636017 2454557 := bbase (se 3 (by rfl) ⟨460229, by rfl⟩ : syracuseStep 2454557 = 920459) (by norm_num)
theorem B3683357 : Blo 1636017 3683357 := bbase (se 3 (by rfl) ⟨690629, by rfl⟩ : syracuseStep 3683357 = 1381259) (by norm_num)
theorem B4142117 : Blo 1636017 4142117 := bbase (se 4 (by rfl) ⟨388323, by rfl⟩ : syracuseStep 4142117 = 776647) (by norm_num)
theorem B2454581 : Blo 1636017 2454581 := bbase (se 5 (by rfl) ⟨115058, by rfl⟩ : syracuseStep 2454581 = 230117) (by norm_num)
theorem B3494981 : Blo 1636017 3494981 := bbase (se 4 (by rfl) ⟨327654, by rfl⟩ : syracuseStep 3494981 = 655309) (by norm_num)
theorem B2454605 : Blo 1636017 2454605 := bbase (se 3 (by rfl) ⟨460238, by rfl⟩ : syracuseStep 2454605 = 920477) (by norm_num)
theorem B2593885 : Blo 1636017 2593885 := bbase (se 3 (by rfl) ⟨486353, by rfl⟩ : syracuseStep 2593885 = 972707) (by norm_num)
theorem B2454629 : Blo 1636017 2454629 := bbase (se 4 (by rfl) ⟨230121, by rfl⟩ : syracuseStep 2454629 = 460243) (by norm_num)
theorem B3683429 : Blo 1636017 3683429 := bbase (se 4 (by rfl) ⟨345321, by rfl⟩ : syracuseStep 3683429 = 690643) (by norm_num)
theorem B5526629 : Blo 1636017 5526629 := bbase (se 4 (by rfl) ⟨518121, by rfl⟩ : syracuseStep 5526629 = 1036243) (by norm_num)
theorem B2454653 : Blo 1636017 2454653 := bbase (se 3 (by rfl) ⟨460247, by rfl⟩ : syracuseStep 2454653 = 920495) (by norm_num)
theorem B2454677 : Blo 1636017 2454677 := bbase (se 6 (by rfl) ⟨57531, by rfl⟩ : syracuseStep 2454677 = 115063) (by norm_num)
theorem B2454701 : Blo 1636017 2454701 := bbase (se 3 (by rfl) ⟨460256, by rfl⟩ : syracuseStep 2454701 = 920513) (by norm_num)
theorem B3683501 : Blo 1636017 3683501 := bbase (se 3 (by rfl) ⟨690656, by rfl⟩ : syracuseStep 3683501 = 1381313) (by norm_num)
theorem B2454725 : Blo 1636017 2454725 := bbase (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) (by norm_num)
theorem B1660105 : Blo 1636017 1660105 := bbase (se 2 (by rfl) ⟨622539, by rfl⟩ : syracuseStep 1660105 = 1245079) (by norm_num)
theorem B2454749 : Blo 1636017 2454749 := bbase (se 3 (by rfl) ⟨460265, by rfl⟩ : syracuseStep 2454749 = 920531) (by norm_num)
theorem B2454773 : Blo 1636017 2454773 := bbase (se 5 (by rfl) ⟨115067, by rfl⟩ : syracuseStep 2454773 = 230135) (by norm_num)
theorem B3683573 : Blo 1636017 3683573 := bbase (se 5 (by rfl) ⟨172667, by rfl⟩ : syracuseStep 3683573 = 345335) (by norm_num)
theorem B2454797 : Blo 1636017 2454797 := bbase (se 3 (by rfl) ⟨460274, by rfl⟩ : syracuseStep 2454797 = 920549) (by norm_num)
theorem B2454821 : Blo 1636017 2454821 := bbase (se 4 (by rfl) ⟨230139, by rfl⟩ : syracuseStep 2454821 = 460279) (by norm_num)
theorem B2454845 : Blo 1636017 2454845 := bbase (se 3 (by rfl) ⟨460283, by rfl⟩ : syracuseStep 2454845 = 920567) (by norm_num)
theorem B3683645 : Blo 1636017 3683645 := bbase (se 3 (by rfl) ⟨690683, by rfl⟩ : syracuseStep 3683645 = 1381367) (by norm_num)
theorem B2454869 : Blo 1636017 2454869 := bbase (se 13 (by rfl) ⟨449, by rfl⟩ : syracuseStep 2454869 = 899) (by norm_num)
theorem B10491221 : Blo 1636017 10491221 := bbase (se 14 (by rfl) ⟨960, by rfl⟩ : syracuseStep 10491221 = 1921) (by norm_num)
theorem B2454893 : Blo 1636017 2454893 := bbase (se 3 (by rfl) ⟨460292, by rfl⟩ : syracuseStep 2454893 = 920585) (by norm_num)
theorem B4142461 : Blo 1636017 4142461 := bbase (se 3 (by rfl) ⟨776711, by rfl⟩ : syracuseStep 4142461 = 1553423) (by norm_num)
theorem B2454917 : Blo 1636017 2454917 := bbase (se 4 (by rfl) ⟨230148, by rfl⟩ : syracuseStep 2454917 = 460297) (by norm_num)
theorem B3683717 : Blo 1636017 3683717 := bbase (se 4 (by rfl) ⟨345348, by rfl⟩ : syracuseStep 3683717 = 690697) (by norm_num)
theorem B8402309 : Blo 1636017 8402309 := bbase (se 4 (by rfl) ⟨787716, by rfl⟩ : syracuseStep 8402309 = 1575433) (by norm_num)
theorem B3151237 : Blo 1636017 3151237 := bbase (se 4 (by rfl) ⟨295428, by rfl⟩ : syracuseStep 3151237 = 590857) (by norm_num)
theorem B2332037 : Blo 1636017 2332037 := bbase (se 4 (by rfl) ⟨218628, by rfl⟩ : syracuseStep 2332037 = 437257) (by norm_num)
theorem B2454941 : Blo 1636017 2454941 := bbase (se 3 (by rfl) ⟨460301, by rfl⟩ : syracuseStep 2454941 = 920603) (by norm_num)
theorem B1840549 : Blo 1636017 1840549 := bbase (se 4 (by rfl) ⟨172551, by rfl⟩ : syracuseStep 1840549 = 345103) (by norm_num)
theorem B2454965 : Blo 1636017 2454965 := bbase (se 5 (by rfl) ⟨115076, by rfl⟩ : syracuseStep 2454965 = 230153) (by norm_num)
theorem B1840585 : Blo 1636017 1840585 := bbase (se 2 (by rfl) ⟨690219, by rfl⟩ : syracuseStep 1840585 = 1380439) (by norm_num)
theorem B2454989 : Blo 1636017 2454989 := bbase (se 3 (by rfl) ⟨460310, by rfl⟩ : syracuseStep 2454989 = 920621) (by norm_num)
theorem B3683789 : Blo 1636017 3683789 := bbase (se 3 (by rfl) ⟨690710, by rfl⟩ : syracuseStep 3683789 = 1381421) (by norm_num)
theorem B2455013 : Blo 1636017 2455013 := bbase (se 4 (by rfl) ⟨230157, by rfl⟩ : syracuseStep 2455013 = 460315) (by norm_num)
theorem B1840621 : Blo 1636017 1840621 := bbase (se 3 (by rfl) ⟨345116, by rfl⟩ : syracuseStep 1840621 = 690233) (by norm_num)
theorem B4142573 : Blo 1636017 4142573 := bbase (se 3 (by rfl) ⟨776732, by rfl⟩ : syracuseStep 4142573 = 1553465) (by norm_num)
theorem B2455037 : Blo 1636017 2455037 := bbase (se 3 (by rfl) ⟨460319, by rfl⟩ : syracuseStep 2455037 = 920639) (by norm_num)
theorem B1840657 : Blo 1636017 1840657 := bbase (se 2 (by rfl) ⟨690246, by rfl⟩ : syracuseStep 1840657 = 1380493) (by norm_num)
theorem B2455061 : Blo 1636017 2455061 := bbase (se 6 (by rfl) ⟨57540, by rfl⟩ : syracuseStep 2455061 = 115081) (by norm_num)
theorem B3683861 : Blo 1636017 3683861 := bbase (se 6 (by rfl) ⟨86340, by rfl⟩ : syracuseStep 3683861 = 172681) (by norm_num)
theorem B5527061 : Blo 1636017 5527061 := bbase (se 6 (by rfl) ⟨129540, by rfl⟩ : syracuseStep 5527061 = 259081) (by norm_num)
theorem B2455085 : Blo 1636017 2455085 := bbase (se 3 (by rfl) ⟨460328, by rfl⟩ : syracuseStep 2455085 = 920657) (by norm_num)
theorem B1840693 : Blo 1636017 1840693 := bbase (se 5 (by rfl) ⟨86282, by rfl⟩ : syracuseStep 1840693 = 172565) (by norm_num)
theorem B2692669 : Blo 1636017 2692669 := bbase (se 3 (by rfl) ⟨504875, by rfl⟩ : syracuseStep 2692669 = 1009751) (by norm_num)
theorem B2455109 : Blo 1636017 2455109 := bbase (se 4 (by rfl) ⟨230166, by rfl⟩ : syracuseStep 2455109 = 460333) (by norm_num)
theorem B1840729 : Blo 1636017 1840729 := bbase (se 2 (by rfl) ⟨690273, by rfl⟩ : syracuseStep 1840729 = 1380547) (by norm_num)
theorem B2455133 : Blo 1636017 2455133 := bbase (se 3 (by rfl) ⟨460337, by rfl⟩ : syracuseStep 2455133 = 920675) (by norm_num)
theorem B3683933 : Blo 1636017 3683933 := bbase (se 3 (by rfl) ⟨690737, by rfl⟩ : syracuseStep 3683933 = 1381475) (by norm_num)
theorem B2455157 : Blo 1636017 2455157 := bbase (se 5 (by rfl) ⟨115085, by rfl⟩ : syracuseStep 2455157 = 230171) (by norm_num)
theorem B1840765 : Blo 1636017 1840765 := bbase (se 3 (by rfl) ⟨345143, by rfl⟩ : syracuseStep 1840765 = 690287) (by norm_num)
theorem B2455181 : Blo 1636017 2455181 := bbase (se 3 (by rfl) ⟨460346, by rfl⟩ : syracuseStep 2455181 = 920693) (by norm_num)
theorem B1840801 : Blo 1636017 1840801 := bbase (se 2 (by rfl) ⟨690300, by rfl⟩ : syracuseStep 1840801 = 1380601) (by norm_num)
theorem B2455205 : Blo 1636017 2455205 := bbase (se 4 (by rfl) ⟨230175, by rfl⟩ : syracuseStep 2455205 = 460351) (by norm_num)
theorem B3684005 : Blo 1636017 3684005 := bbase (se 4 (by rfl) ⟨345375, by rfl⟩ : syracuseStep 3684005 = 690751) (by norm_num)
theorem B4142765 : Blo 1636017 4142765 := bbase (se 3 (by rfl) ⟨776768, by rfl⟩ : syracuseStep 4142765 = 1553537) (by norm_num)
theorem B2455229 : Blo 1636017 2455229 := bbase (se 3 (by rfl) ⟨460355, by rfl⟩ : syracuseStep 2455229 = 920711) (by norm_num)
theorem B1840837 : Blo 1636017 1840837 := bbase (se 4 (by rfl) ⟨172578, by rfl⟩ : syracuseStep 1840837 = 345157) (by norm_num)
theorem B2455253 : Blo 1636017 2455253 := bbase (se 7 (by rfl) ⟨28772, by rfl⟩ : syracuseStep 2455253 = 57545) (by norm_num)
theorem B1840873 : Blo 1636017 1840873 := bbase (se 2 (by rfl) ⟨690327, by rfl⟩ : syracuseStep 1840873 = 1380655) (by norm_num)
theorem B2455277 : Blo 1636017 2455277 := bbase (se 3 (by rfl) ⟨460364, by rfl⟩ : syracuseStep 2455277 = 920729) (by norm_num)
theorem B3684077 : Blo 1636017 3684077 := bbase (se 3 (by rfl) ⟨690764, by rfl⟩ : syracuseStep 3684077 = 1381529) (by norm_num)
theorem B2455301 : Blo 1636017 2455301 := bbase (se 4 (by rfl) ⟨230184, by rfl⟩ : syracuseStep 2455301 = 460369) (by norm_num)
theorem B1840909 : Blo 1636017 1840909 := bbase (se 3 (by rfl) ⟨345170, by rfl⟩ : syracuseStep 1840909 = 690341) (by norm_num)
theorem B2455325 : Blo 1636017 2455325 := bbase (se 3 (by rfl) ⟨460373, by rfl⟩ : syracuseStep 2455325 = 920747) (by norm_num)
theorem B1840945 : Blo 1636017 1840945 := bbase (se 2 (by rfl) ⟨690354, by rfl⟩ : syracuseStep 1840945 = 1380709) (by norm_num)
theorem B2455349 : Blo 1636017 2455349 := bbase (se 5 (by rfl) ⟨115094, by rfl⟩ : syracuseStep 2455349 = 230189) (by norm_num)
theorem B4200245 : Blo 1636017 4200245 := bbase (se 5 (by rfl) ⟨196886, by rfl⟩ : syracuseStep 4200245 = 393773) (by norm_num)
theorem B3684149 : Blo 1636017 3684149 := bbase (se 5 (by rfl) ⟨172694, by rfl⟩ : syracuseStep 3684149 = 345389) (by norm_num)
theorem B2455373 : Blo 1636017 2455373 := bbase (se 3 (by rfl) ⟨460382, by rfl⟩ : syracuseStep 2455373 = 920765) (by norm_num)
theorem B4659029 : Blo 1636017 4659029 := bbase (se 9 (by rfl) ⟨13649, by rfl⟩ : syracuseStep 4659029 = 27299) (by norm_num)
theorem B1840981 : Blo 1636017 1840981 := bbase (se 9 (by rfl) ⟨5393, by rfl⟩ : syracuseStep 1840981 = 10787) (by norm_num)
theorem B2455397 : Blo 1636017 2455397 := bbase (se 4 (by rfl) ⟨230193, by rfl⟩ : syracuseStep 2455397 = 460387) (by norm_num)
theorem B1841017 : Blo 1636017 1841017 := bbase (se 2 (by rfl) ⟨690381, by rfl⟩ : syracuseStep 1841017 = 1380763) (by norm_num)
theorem B2455421 : Blo 1636017 2455421 := bbase (se 3 (by rfl) ⟨460391, by rfl⟩ : syracuseStep 2455421 = 920783) (by norm_num)
theorem B3684221 : Blo 1636017 3684221 := bbase (se 3 (by rfl) ⟨690791, by rfl⟩ : syracuseStep 3684221 = 1381583) (by norm_num)
theorem B2455445 : Blo 1636017 2455445 := bbase (se 6 (by rfl) ⟨57549, by rfl⟩ : syracuseStep 2455445 = 115099) (by norm_num)
theorem B1841053 : Blo 1636017 1841053 := bbase (se 3 (by rfl) ⟨345197, by rfl⟩ : syracuseStep 1841053 = 690395) (by norm_num)
theorem B2455469 : Blo 1636017 2455469 := bbase (se 3 (by rfl) ⟨460400, by rfl⟩ : syracuseStep 2455469 = 920801) (by norm_num)
theorem B3495869 : Blo 1636017 3495869 := bbase (se 3 (by rfl) ⟨655475, by rfl⟩ : syracuseStep 3495869 = 1310951) (by norm_num)
theorem B1841089 : Blo 1636017 1841089 := bbase (se 2 (by rfl) ⟨690408, by rfl⟩ : syracuseStep 1841089 = 1380817) (by norm_num)
theorem B2455493 : Blo 1636017 2455493 := bbase (se 4 (by rfl) ⟨230202, by rfl⟩ : syracuseStep 2455493 = 460405) (by norm_num)
theorem B3684293 : Blo 1636017 3684293 := bbase (se 4 (by rfl) ⟨345402, by rfl⟩ : syracuseStep 3684293 = 690805) (by norm_num)
theorem B5527493 : Blo 1636017 5527493 := bbase (se 4 (by rfl) ⟨518202, by rfl⟩ : syracuseStep 5527493 = 1036405) (by norm_num)
theorem B2455517 : Blo 1636017 2455517 := bbase (se 3 (by rfl) ⟨460409, by rfl⟩ : syracuseStep 2455517 = 920819) (by norm_num)
theorem B1841125 : Blo 1636017 1841125 := bbase (se 4 (by rfl) ⟨172605, by rfl⟩ : syracuseStep 1841125 = 345211) (by norm_num)
theorem B2455541 : Blo 1636017 2455541 := bbase (se 5 (by rfl) ⟨115103, by rfl⟩ : syracuseStep 2455541 = 230207) (by norm_num)
theorem B4143109 : Blo 1636017 4143109 := bbase (se 4 (by rfl) ⟨388416, by rfl⟩ : syracuseStep 4143109 = 776833) (by norm_num)
theorem B1841161 : Blo 1636017 1841161 := bbase (se 2 (by rfl) ⟨690435, by rfl⟩ : syracuseStep 1841161 = 1380871) (by norm_num)
theorem B2455565 : Blo 1636017 2455565 := bbase (se 3 (by rfl) ⟨460418, by rfl⟩ : syracuseStep 2455565 = 920837) (by norm_num)
theorem B3684365 : Blo 1636017 3684365 := bbase (se 3 (by rfl) ⟨690818, by rfl⟩ : syracuseStep 3684365 = 1381637) (by norm_num)
theorem B4659221 : Blo 1636017 4659221 := bbase (se 6 (by rfl) ⟨109200, by rfl⟩ : syracuseStep 4659221 = 218401) (by norm_num)
theorem B2455589 : Blo 1636017 2455589 := bbase (se 4 (by rfl) ⟨230211, by rfl⟩ : syracuseStep 2455589 = 460423) (by norm_num)
theorem B1841197 : Blo 1636017 1841197 := bbase (se 3 (by rfl) ⟨345224, by rfl⟩ : syracuseStep 1841197 = 690449) (by norm_num)
theorem B2799677 : Blo 1636017 2799677 := bbase (se 3 (by rfl) ⟨524939, by rfl⟩ : syracuseStep 2799677 = 1049879) (by norm_num)
theorem B2455613 : Blo 1636017 2455613 := bbase (se 3 (by rfl) ⟨460427, by rfl⟩ : syracuseStep 2455613 = 920855) (by norm_num)
theorem B4790341 : Blo 1636017 4790341 := bbase (se 4 (by rfl) ⟨449094, by rfl⟩ : syracuseStep 4790341 = 898189) (by norm_num)
theorem B4978757 : Blo 1636017 4978757 := bbase (se 4 (by rfl) ⟨466758, by rfl⟩ : syracuseStep 4978757 = 933517) (by norm_num)
theorem B1841233 : Blo 1636017 1841233 := bbase (se 2 (by rfl) ⟨690462, by rfl⟩ : syracuseStep 1841233 = 1380925) (by norm_num)
theorem B2070613 : Blo 1636017 2070613 := bbase (se 8 (by rfl) ⟨12132, by rfl⟩ : syracuseStep 2070613 = 24265) (by norm_num)
theorem B4724821 : Blo 1636017 4724821 := bbase (se 8 (by rfl) ⟨27684, by rfl⟩ : syracuseStep 4724821 = 55369) (by norm_num)
theorem B2455637 : Blo 1636017 2455637 := bbase (se 8 (by rfl) ⟨14388, by rfl⟩ : syracuseStep 2455637 = 28777) (by norm_num)
theorem B3684437 : Blo 1636017 3684437 := bbase (se 8 (by rfl) ⟨21588, by rfl⟩ : syracuseStep 3684437 = 43177) (by norm_num)
theorem B2455661 : Blo 1636017 2455661 := bbase (se 3 (by rfl) ⟨460436, by rfl⟩ : syracuseStep 2455661 = 920873) (by norm_num)
theorem B1841269 : Blo 1636017 1841269 := bbase (se 5 (by rfl) ⟨86309, by rfl⟩ : syracuseStep 1841269 = 172619) (by norm_num)
theorem B4143221 : Blo 1636017 4143221 := bbase (se 5 (by rfl) ⟨194213, by rfl⟩ : syracuseStep 4143221 = 388427) (by norm_num)
theorem B2455685 : Blo 1636017 2455685 := bbase (se 4 (by rfl) ⟨230220, by rfl⟩ : syracuseStep 2455685 = 460441) (by norm_num)
theorem B8288405 : Blo 1636017 8288405 := bbase (se 6 (by rfl) ⟨194259, by rfl⟩ : syracuseStep 8288405 = 388519) (by norm_num)
theorem B1841305 : Blo 1636017 1841305 := bbase (se 2 (by rfl) ⟨690489, by rfl⟩ : syracuseStep 1841305 = 1380979) (by norm_num)
theorem B2455709 : Blo 1636017 2455709 := bbase (se 3 (by rfl) ⟨460445, by rfl⟩ : syracuseStep 2455709 = 920891) (by norm_num)
theorem B3684509 : Blo 1636017 3684509 := bbase (se 3 (by rfl) ⟨690845, by rfl⟩ : syracuseStep 3684509 = 1381691) (by norm_num)
theorem B3545245 : Blo 1636017 3545245 := bbase (se 3 (by rfl) ⟨664733, by rfl⟩ : syracuseStep 3545245 = 1329467) (by norm_num)
theorem B9320629 : Blo 1636017 9320629 := bbase (se 5 (by rfl) ⟨436904, by rfl⟩ : syracuseStep 9320629 = 873809) (by norm_num)
theorem B3496117 : Blo 1636017 3496117 := bbase (se 5 (by rfl) ⟨163880, by rfl⟩ : syracuseStep 3496117 = 327761) (by norm_num)
theorem B2455733 : Blo 1636017 2455733 := bbase (se 5 (by rfl) ⟨115112, by rfl⟩ : syracuseStep 2455733 = 230225) (by norm_num)
theorem B1841341 : Blo 1636017 1841341 := bbase (se 3 (by rfl) ⟨345251, by rfl⟩ : syracuseStep 1841341 = 690503) (by norm_num)
theorem B2455757 : Blo 1636017 2455757 := bbase (se 3 (by rfl) ⟨460454, by rfl⟩ : syracuseStep 2455757 = 920909) (by norm_num)
theorem B1841377 : Blo 1636017 1841377 := bbase (se 2 (by rfl) ⟨690516, by rfl⟩ : syracuseStep 1841377 = 1381033) (by norm_num)
theorem B2455781 : Blo 1636017 2455781 := bbase (se 4 (by rfl) ⟨230229, by rfl⟩ : syracuseStep 2455781 = 460459) (by norm_num)
theorem B3684581 : Blo 1636017 3684581 := bbase (se 4 (by rfl) ⟨345429, by rfl⟩ : syracuseStep 3684581 = 690859) (by norm_num)
theorem B2488565 : Blo 1636017 2488565 := bbase (se 5 (by rfl) ⟨116651, by rfl⟩ : syracuseStep 2488565 = 233303) (by norm_num)
theorem B2455805 : Blo 1636017 2455805 := bbase (se 3 (by rfl) ⟨460463, by rfl⟩ : syracuseStep 2455805 = 920927) (by norm_num)
theorem B2070785 : Blo 1636017 2070785 := bbase (se 2 (by rfl) ⟨776544, by rfl⟩ : syracuseStep 2070785 = 1553089) (by norm_num)
theorem B1841413 : Blo 1636017 1841413 := bbase (se 4 (by rfl) ⟨172632, by rfl⟩ : syracuseStep 1841413 = 345265) (by norm_num)
theorem B2455829 : Blo 1636017 2455829 := bbase (se 6 (by rfl) ⟨57558, by rfl⟩ : syracuseStep 2455829 = 115117) (by norm_num)
theorem B5388581 : Blo 1636017 5388581 := bbase (se 4 (by rfl) ⟨505179, by rfl⟩ : syracuseStep 5388581 = 1010359) (by norm_num)
theorem B1841449 : Blo 1636017 1841449 := bbase (se 2 (by rfl) ⟨690543, by rfl⟩ : syracuseStep 1841449 = 1381087) (by norm_num)
theorem B2455853 : Blo 1636017 2455853 := bbase (se 3 (by rfl) ⟨460472, by rfl⟩ : syracuseStep 2455853 = 920945) (by norm_num)
theorem B3684653 : Blo 1636017 3684653 := bbase (se 3 (by rfl) ⟨690872, by rfl⟩ : syracuseStep 3684653 = 1381745) (by norm_num)
theorem B4143413 : Blo 1636017 4143413 := bbase (se 5 (by rfl) ⟨194222, by rfl⟩ : syracuseStep 4143413 = 388445) (by norm_num)
theorem B2070841 : Blo 1636017 2070841 := bbase (se 2 (by rfl) ⟨776565, by rfl⟩ : syracuseStep 2070841 = 1553131) (by norm_num)
theorem B2242885 : Blo 1636017 2242885 := bbase (se 4 (by rfl) ⟨210270, by rfl⟩ : syracuseStep 2242885 = 420541) (by norm_num)
theorem B2455877 : Blo 1636017 2455877 := bbase (se 4 (by rfl) ⟨230238, by rfl⟩ : syracuseStep 2455877 = 460477) (by norm_num)
theorem B1841485 : Blo 1636017 1841485 := bbase (se 3 (by rfl) ⟨345278, by rfl⟩ : syracuseStep 1841485 = 690557) (by norm_num)
theorem B2455901 : Blo 1636017 2455901 := bbase (se 3 (by rfl) ⟨460481, by rfl⟩ : syracuseStep 2455901 = 920963) (by norm_num)
theorem B1841521 : Blo 1636017 1841521 := bbase (se 2 (by rfl) ⟨690570, by rfl⟩ : syracuseStep 1841521 = 1381141) (by norm_num)
theorem B2455925 : Blo 1636017 2455925 := bbase (se 5 (by rfl) ⟨115121, by rfl⟩ : syracuseStep 2455925 = 230243) (by norm_num)
theorem B3684725 : Blo 1636017 3684725 := bbase (se 5 (by rfl) ⟨172721, by rfl⟩ : syracuseStep 3684725 = 345443) (by norm_num)
theorem B5527925 : Blo 1636017 5527925 := bbase (se 5 (by rfl) ⟨259121, by rfl⟩ : syracuseStep 5527925 = 518243) (by norm_num)
theorem B2455949 : Blo 1636017 2455949 := bbase (se 3 (by rfl) ⟨460490, by rfl⟩ : syracuseStep 2455949 = 920981) (by norm_num)
theorem B1841557 : Blo 1636017 1841557 := bbase (se 6 (by rfl) ⟨43161, by rfl⟩ : syracuseStep 1841557 = 86323) (by norm_num)
theorem B2070937 : Blo 1636017 2070937 := bbase (se 2 (by rfl) ⟨776601, by rfl⟩ : syracuseStep 2070937 = 1553203) (by norm_num)
theorem B2455973 : Blo 1636017 2455973 := bbase (se 4 (by rfl) ⟨230247, by rfl⟩ : syracuseStep 2455973 = 460495) (by norm_num)
theorem B1841593 : Blo 1636017 1841593 := bbase (se 2 (by rfl) ⟨690597, by rfl⟩ : syracuseStep 1841593 = 1381195) (by norm_num)
theorem B2455997 : Blo 1636017 2455997 := bbase (se 3 (by rfl) ⟨460499, by rfl⟩ : syracuseStep 2455997 = 920999) (by norm_num)
theorem B3684797 : Blo 1636017 3684797 := bbase (se 3 (by rfl) ⟨690899, by rfl⟩ : syracuseStep 3684797 = 1381799) (by norm_num)
theorem B2456021 : Blo 1636017 2456021 := bbase (se 7 (by rfl) ⟨28781, by rfl⟩ : syracuseStep 2456021 = 57563) (by norm_num)
theorem B1841629 : Blo 1636017 1841629 := bbase (se 3 (by rfl) ⟨345305, by rfl⟩ : syracuseStep 1841629 = 690611) (by norm_num)
theorem B2456045 : Blo 1636017 2456045 := bbase (se 3 (by rfl) ⟨460508, by rfl⟩ : syracuseStep 2456045 = 921017) (by norm_num)
theorem B6994421 : Blo 1636017 6994421 := bbase (se 5 (by rfl) ⟨327863, by rfl⟩ : syracuseStep 6994421 = 655727) (by norm_num)
theorem B1841665 : Blo 1636017 1841665 := bbase (se 2 (by rfl) ⟨690624, by rfl⟩ : syracuseStep 1841665 = 1381249) (by norm_num)
theorem B2456069 : Blo 1636017 2456069 := bbase (se 4 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 2456069 = 460513) (by norm_num)
theorem B3684869 : Blo 1636017 3684869 := bbase (se 4 (by rfl) ⟨345456, by rfl⟩ : syracuseStep 3684869 = 690913) (by norm_num)
theorem B2456093 : Blo 1636017 2456093 := bbase (se 3 (by rfl) ⟨460517, by rfl⟩ : syracuseStep 2456093 = 921035) (by norm_num)
theorem B1841701 : Blo 1636017 1841701 := bbase (se 4 (by rfl) ⟨172659, by rfl⟩ : syracuseStep 1841701 = 345319) (by norm_num)
theorem B2456117 : Blo 1636017 2456117 := bbase (se 5 (by rfl) ⟨115130, by rfl⟩ : syracuseStep 2456117 = 230261) (by norm_num)
theorem B2071109 : Blo 1636017 2071109 := bbase (se 4 (by rfl) ⟨194166, by rfl⟩ : syracuseStep 2071109 = 388333) (by norm_num)
theorem B1841737 : Blo 1636017 1841737 := bbase (se 2 (by rfl) ⟨690651, by rfl⟩ : syracuseStep 1841737 = 1381303) (by norm_num)
theorem B2456141 : Blo 1636017 2456141 := bbase (se 3 (by rfl) ⟨460526, by rfl⟩ : syracuseStep 2456141 = 921053) (by norm_num)
theorem B3684941 : Blo 1636017 3684941 := bbase (se 3 (by rfl) ⟨690926, by rfl⟩ : syracuseStep 3684941 = 1381853) (by norm_num)
theorem B2456165 : Blo 1636017 2456165 := bbase (se 4 (by rfl) ⟨230265, by rfl⟩ : syracuseStep 2456165 = 460531) (by norm_num)
theorem B1841773 : Blo 1636017 1841773 := bbase (se 3 (by rfl) ⟨345332, by rfl⟩ : syracuseStep 1841773 = 690665) (by norm_num)
theorem B2071165 : Blo 1636017 2071165 := bbase (se 3 (by rfl) ⟨388343, by rfl⟩ : syracuseStep 2071165 = 776687) (by norm_num)
theorem B2456189 : Blo 1636017 2456189 := bbase (se 3 (by rfl) ⟨460535, by rfl⟩ : syracuseStep 2456189 = 921071) (by norm_num)
theorem B4143757 : Blo 1636017 4143757 := bbase (se 3 (by rfl) ⟨776954, by rfl⟩ : syracuseStep 4143757 = 1553909) (by norm_num)
theorem B1841809 : Blo 1636017 1841809 := bbase (se 2 (by rfl) ⟨690678, by rfl⟩ : syracuseStep 1841809 = 1381357) (by norm_num)
theorem B2456213 : Blo 1636017 2456213 := bbase (se 6 (by rfl) ⟨57567, by rfl⟩ : syracuseStep 2456213 = 115135) (by norm_num)
theorem B3685013 : Blo 1636017 3685013 := bbase (se 6 (by rfl) ⟨86367, by rfl⟩ : syracuseStep 3685013 = 172735) (by norm_num)
theorem B28367509 : Blo 1636017 28367509 := bbase (se 6 (by rfl) ⟨664863, by rfl⟩ : syracuseStep 28367509 = 1329727) (by norm_num)
theorem B3496621 : Blo 1636017 3496621 := bbase (se 3 (by rfl) ⟨655616, by rfl⟩ : syracuseStep 3496621 = 1311233) (by norm_num)
theorem B2456237 : Blo 1636017 2456237 := bbase (se 3 (by rfl) ⟨460544, by rfl⟩ : syracuseStep 2456237 = 921089) (by norm_num)
theorem B1841845 : Blo 1636017 1841845 := bbase (se 5 (by rfl) ⟨86336, by rfl⟩ : syracuseStep 1841845 = 172673) (by norm_num)
theorem B2456261 : Blo 1636017 2456261 := bbase (se 4 (by rfl) ⟨230274, by rfl⟩ : syracuseStep 2456261 = 460549) (by norm_num)
theorem B1841881 : Blo 1636017 1841881 := bbase (se 2 (by rfl) ⟨690705, by rfl⟩ : syracuseStep 1841881 = 1381411) (by norm_num)
theorem B2071261 : Blo 1636017 2071261 := bbase (se 3 (by rfl) ⟨388361, by rfl⟩ : syracuseStep 2071261 = 776723) (by norm_num)
theorem B2456285 : Blo 1636017 2456285 := bbase (se 3 (by rfl) ⟨460553, by rfl⟩ : syracuseStep 2456285 = 921107) (by norm_num)
theorem B3685085 : Blo 1636017 3685085 := bbase (se 3 (by rfl) ⟨690953, by rfl⟩ : syracuseStep 3685085 = 1381907) (by norm_num)
theorem B2456309 : Blo 1636017 2456309 := bbase (se 5 (by rfl) ⟨115139, by rfl⟩ : syracuseStep 2456309 = 230279) (by norm_num)
theorem B4143869 : Blo 1636017 4143869 := bbase (se 3 (by rfl) ⟨776975, by rfl⟩ : syracuseStep 4143869 = 1553951) (by norm_num)
theorem B1841917 : Blo 1636017 1841917 := bbase (se 3 (by rfl) ⟨345359, by rfl⟩ : syracuseStep 1841917 = 690719) (by norm_num)
theorem B2456333 : Blo 1636017 2456333 := bbase (se 3 (by rfl) ⟨460562, by rfl⟩ : syracuseStep 2456333 = 921125) (by norm_num)
theorem B1841953 : Blo 1636017 1841953 := bbase (se 2 (by rfl) ⟨690732, by rfl⟩ : syracuseStep 1841953 = 1381465) (by norm_num)
theorem B2456357 : Blo 1636017 2456357 := bbase (se 4 (by rfl) ⟨230283, by rfl⟩ : syracuseStep 2456357 = 460567) (by norm_num)
theorem B3685157 : Blo 1636017 3685157 := bbase (se 4 (by rfl) ⟨345483, by rfl⟩ : syracuseStep 3685157 = 690967) (by norm_num)
theorem B2456381 : Blo 1636017 2456381 := bbase (se 3 (by rfl) ⟨460571, by rfl⟩ : syracuseStep 2456381 = 921143) (by norm_num)
theorem B1841989 : Blo 1636017 1841989 := bbase (se 4 (by rfl) ⟨172686, by rfl⟩ : syracuseStep 1841989 = 345373) (by norm_num)
theorem B5602117 : Blo 1636017 5602117 := bbase (se 4 (by rfl) ⟨525198, by rfl⟩ : syracuseStep 5602117 = 1050397) (by norm_num)
theorem B6216533 : Blo 1636017 6216533 := bbase (se 9 (by rfl) ⟨18212, by rfl⟩ : syracuseStep 6216533 = 36425) (by norm_num)
theorem B2456405 : Blo 1636017 2456405 := bbase (se 9 (by rfl) ⟨7196, by rfl⟩ : syracuseStep 2456405 = 14393) (by norm_num)
theorem B1842025 : Blo 1636017 1842025 := bbase (se 2 (by rfl) ⟨690759, by rfl⟩ : syracuseStep 1842025 = 1381519) (by norm_num)
theorem B2456429 : Blo 1636017 2456429 := bbase (se 3 (by rfl) ⟨460580, by rfl⟩ : syracuseStep 2456429 = 921161) (by norm_num)
theorem B3685229 : Blo 1636017 3685229 := bbase (se 3 (by rfl) ⟨690980, by rfl⟩ : syracuseStep 3685229 = 1381961) (by norm_num)
theorem B2456453 : Blo 1636017 2456453 := bbase (se 4 (by rfl) ⟨230292, by rfl⟩ : syracuseStep 2456453 = 460585) (by norm_num)
theorem B2071433 : Blo 1636017 2071433 := bbase (se 2 (by rfl) ⟨776787, by rfl⟩ : syracuseStep 2071433 = 1553575) (by norm_num)
theorem B1842061 : Blo 1636017 1842061 := bbase (se 3 (by rfl) ⟨345386, by rfl⟩ : syracuseStep 1842061 = 690773) (by norm_num)
theorem B2456477 : Blo 1636017 2456477 := bbase (se 3 (by rfl) ⟨460589, by rfl⟩ : syracuseStep 2456477 = 921179) (by norm_num)
theorem B1842097 : Blo 1636017 1842097 := bbase (se 2 (by rfl) ⟨690786, by rfl⟩ : syracuseStep 1842097 = 1381573) (by norm_num)
theorem B11803573 : Blo 1636017 11803573 := bbase (se 5 (by rfl) ⟨553292, by rfl⟩ : syracuseStep 11803573 = 1106585) (by norm_num)
theorem B2456501 : Blo 1636017 2456501 := bbase (se 5 (by rfl) ⟨115148, by rfl⟩ : syracuseStep 2456501 = 230297) (by norm_num)
theorem B3685301 : Blo 1636017 3685301 := bbase (se 5 (by rfl) ⟨172748, by rfl⟩ : syracuseStep 3685301 = 345497) (by norm_num)
theorem B4144061 : Blo 1636017 4144061 := bbase (se 3 (by rfl) ⟨777011, by rfl⟩ : syracuseStep 4144061 = 1554023) (by norm_num)
theorem B2071489 : Blo 1636017 2071489 := bbase (se 2 (by rfl) ⟨776808, by rfl⟩ : syracuseStep 2071489 = 1553617) (by norm_num)
theorem B2456525 : Blo 1636017 2456525 := bbase (se 3 (by rfl) ⟨460598, by rfl⟩ : syracuseStep 2456525 = 921197) (by norm_num)
theorem B18889685 : Blo 1636017 18889685 := bbase (se 7 (by rfl) ⟨221363, by rfl⟩ : syracuseStep 18889685 = 442727) (by norm_num)
theorem B1842133 : Blo 1636017 1842133 := bbase (se 7 (by rfl) ⟨21587, by rfl⟩ : syracuseStep 1842133 = 43175) (by norm_num)
theorem B5241829 : Blo 1636017 5241829 := bbase (se 4 (by rfl) ⟨491421, by rfl⟩ : syracuseStep 5241829 = 982843) (by norm_num)
theorem B2456549 : Blo 1636017 2456549 := bbase (se 4 (by rfl) ⟨230301, by rfl⟩ : syracuseStep 2456549 = 460603) (by norm_num)
theorem B2128873 : Blo 1636017 2128873 := bbase (se 2 (by rfl) ⟨798327, by rfl⟩ : syracuseStep 2128873 = 1596655) (by norm_num)
theorem B4660213 : Blo 1636017 4660213 := bbase (se 5 (by rfl) ⟨218447, by rfl⟩ : syracuseStep 4660213 = 436895) (by norm_num)
theorem B1842169 : Blo 1636017 1842169 := bbase (se 2 (by rfl) ⟨690813, by rfl⟩ : syracuseStep 1842169 = 1381627) (by norm_num)
theorem B2456573 : Blo 1636017 2456573 := bbase (se 3 (by rfl) ⟨460607, by rfl⟩ : syracuseStep 2456573 = 921215) (by norm_num)
theorem B3685373 : Blo 1636017 3685373 := bbase (se 3 (by rfl) ⟨691007, by rfl⟩ : syracuseStep 3685373 = 1382015) (by norm_num)
theorem B8969237 : Blo 1636017 8969237 := bbase (se 6 (by rfl) ⟨210216, by rfl⟩ : syracuseStep 8969237 = 420433) (by norm_num)
theorem B2456597 : Blo 1636017 2456597 := bbase (se 6 (by rfl) ⟨57576, by rfl⟩ : syracuseStep 2456597 = 115153) (by norm_num)
theorem B1842205 : Blo 1636017 1842205 := bbase (se 3 (by rfl) ⟨345413, by rfl⟩ : syracuseStep 1842205 = 690827) (by norm_num)
theorem B2071585 : Blo 1636017 2071585 := bbase (se 2 (by rfl) ⟨776844, by rfl⟩ : syracuseStep 2071585 = 1553689) (by norm_num)
theorem B2456621 : Blo 1636017 2456621 := bbase (se 3 (by rfl) ⟨460616, by rfl⟩ : syracuseStep 2456621 = 921233) (by norm_num)
theorem B1842241 : Blo 1636017 1842241 := bbase (se 2 (by rfl) ⟨690840, by rfl⟩ : syracuseStep 1842241 = 1381681) (by norm_num)
theorem B2456645 : Blo 1636017 2456645 := bbase (se 4 (by rfl) ⟨230310, by rfl⟩ : syracuseStep 2456645 = 460621) (by norm_num)
theorem B3685445 : Blo 1636017 3685445 := bbase (se 4 (by rfl) ⟨345510, by rfl⟩ : syracuseStep 3685445 = 691021) (by norm_num)
theorem B95657045 : Blo 1636017 95657045 := bbase (se 8 (by rfl) ⟨560490, by rfl⟩ : syracuseStep 95657045 = 1120981) (by norm_num)
theorem B2456669 : Blo 1636017 2456669 := bbase (se 3 (by rfl) ⟨460625, by rfl⟩ : syracuseStep 2456669 = 921251) (by norm_num)
theorem B1842277 : Blo 1636017 1842277 := bbase (se 4 (by rfl) ⟨172713, by rfl⟩ : syracuseStep 1842277 = 345427) (by norm_num)
theorem B2948213 : Blo 1636017 2948213 := bbase (se 5 (by rfl) ⟨138197, by rfl⟩ : syracuseStep 2948213 = 276395) (by norm_num)
theorem B6216821 : Blo 1636017 6216821 := bbase (se 5 (by rfl) ⟨291413, by rfl⟩ : syracuseStep 6216821 = 582827) (by norm_num)
theorem B2456693 : Blo 1636017 2456693 := bbase (se 5 (by rfl) ⟨115157, by rfl⟩ : syracuseStep 2456693 = 230315) (by norm_num)
theorem B1842313 : Blo 1636017 1842313 := bbase (se 2 (by rfl) ⟨690867, by rfl⟩ : syracuseStep 1842313 = 1381735) (by norm_num)
theorem B2456717 : Blo 1636017 2456717 := bbase (se 3 (by rfl) ⟨460634, by rfl⟩ : syracuseStep 2456717 = 921269) (by norm_num)
theorem B3685517 : Blo 1636017 3685517 := bbase (se 3 (by rfl) ⟨691034, by rfl⟩ : syracuseStep 3685517 = 1382069) (by norm_num)
theorem B2456741 : Blo 1636017 2456741 := bbase (se 4 (by rfl) ⟨230319, by rfl⟩ : syracuseStep 2456741 = 460639) (by norm_num)
theorem B1842349 : Blo 1636017 1842349 := bbase (se 3 (by rfl) ⟨345440, by rfl⟩ : syracuseStep 1842349 = 690881) (by norm_num)
theorem B2456765 : Blo 1636017 2456765 := bbase (se 3 (by rfl) ⟨460643, by rfl⟩ : syracuseStep 2456765 = 921287) (by norm_num)
theorem B2071757 : Blo 1636017 2071757 := bbase (se 3 (by rfl) ⟨388454, by rfl⟩ : syracuseStep 2071757 = 776909) (by norm_num)
theorem B1842385 : Blo 1636017 1842385 := bbase (se 2 (by rfl) ⟨690894, by rfl⟩ : syracuseStep 1842385 = 1381789) (by norm_num)
theorem B8969429 : Blo 1636017 8969429 := bbase (se 7 (by rfl) ⟨105110, by rfl⟩ : syracuseStep 8969429 = 210221) (by norm_num)
theorem B2456789 : Blo 1636017 2456789 := bbase (se 7 (by rfl) ⟨28790, by rfl⟩ : syracuseStep 2456789 = 57581) (by norm_num)
theorem B2456813 : Blo 1636017 2456813 := bbase (se 3 (by rfl) ⟨460652, by rfl⟩ : syracuseStep 2456813 = 921305) (by norm_num)
theorem B1842421 : Blo 1636017 1842421 := bbase (se 5 (by rfl) ⟨86363, by rfl⟩ : syracuseStep 1842421 = 172727) (by norm_num)
theorem B2071813 : Blo 1636017 2071813 := bbase (se 4 (by rfl) ⟨194232, by rfl⟩ : syracuseStep 2071813 = 388465) (by norm_num)
theorem B2456837 : Blo 1636017 2456837 := bbase (se 4 (by rfl) ⟨230328, by rfl⟩ : syracuseStep 2456837 = 460657) (by norm_num)
theorem B4144405 : Blo 1636017 4144405 := bbase (se 6 (by rfl) ⟨97134, by rfl⟩ : syracuseStep 4144405 = 194269) (by norm_num)
theorem B1842457 : Blo 1636017 1842457 := bbase (se 2 (by rfl) ⟨690921, by rfl⟩ : syracuseStep 1842457 = 1381843) (by norm_num)
theorem B2456861 : Blo 1636017 2456861 := bbase (se 3 (by rfl) ⟨460661, by rfl⟩ : syracuseStep 2456861 = 921323) (by norm_num)
theorem B2456885 : Blo 1636017 2456885 := bbase (se 5 (by rfl) ⟨115166, by rfl⟩ : syracuseStep 2456885 = 230333) (by norm_num)
theorem B1842493 : Blo 1636017 1842493 := bbase (se 3 (by rfl) ⟨345467, by rfl⟩ : syracuseStep 1842493 = 690935) (by norm_num)
theorem B2456909 : Blo 1636017 2456909 := bbase (se 3 (by rfl) ⟨460670, by rfl⟩ : syracuseStep 2456909 = 921341) (by norm_num)
theorem B14941525 : Blo 1636017 14941525 := bbase (se 11 (by rfl) ⟨10943, by rfl⟩ : syracuseStep 14941525 = 21887) (by norm_num)
theorem B1842529 : Blo 1636017 1842529 := bbase (se 2 (by rfl) ⟨690948, by rfl⟩ : syracuseStep 1842529 = 1381897) (by norm_num)
theorem B2071909 : Blo 1636017 2071909 := bbase (se 4 (by rfl) ⟨194241, by rfl⟩ : syracuseStep 2071909 = 388483) (by norm_num)
theorem B2456933 : Blo 1636017 2456933 := bbase (se 4 (by rfl) ⟨230337, by rfl⟩ : syracuseStep 2456933 = 460675) (by norm_num)
theorem B5242229 : Blo 1636017 5242229 := bbase (se 5 (by rfl) ⟨245729, by rfl⟩ : syracuseStep 5242229 = 491459) (by norm_num)
theorem B2456957 : Blo 1636017 2456957 := bbase (se 3 (by rfl) ⟨460679, by rfl⟩ : syracuseStep 2456957 = 921359) (by norm_num)
theorem B4144517 : Blo 1636017 4144517 := bbase (se 4 (by rfl) ⟨388548, by rfl⟩ : syracuseStep 4144517 = 777097) (by norm_num)
theorem B1842565 : Blo 1636017 1842565 := bbase (se 4 (by rfl) ⟨172740, by rfl⟩ : syracuseStep 1842565 = 345481) (by norm_num)
theorem B2948501 : Blo 1636017 2948501 := bbase (se 6 (by rfl) ⟨69105, by rfl⟩ : syracuseStep 2948501 = 138211) (by norm_num)
theorem B2456981 : Blo 1636017 2456981 := bbase (se 6 (by rfl) ⟨57585, by rfl⟩ : syracuseStep 2456981 = 115171) (by norm_num)
theorem B4201885 : Blo 1636017 4201885 := bbase (se 3 (by rfl) ⟨787853, by rfl⟩ : syracuseStep 4201885 = 1575707) (by norm_num)
theorem B8289701 : Blo 1636017 8289701 := bbase (se 4 (by rfl) ⟨777159, by rfl⟩ : syracuseStep 8289701 = 1554319) (by norm_num)
theorem B1842601 : Blo 1636017 1842601 := bbase (se 2 (by rfl) ⟨690975, by rfl⟩ : syracuseStep 1842601 = 1381951) (by norm_num)
theorem B2457005 : Blo 1636017 2457005 := bbase (se 3 (by rfl) ⟨460688, by rfl⟩ : syracuseStep 2457005 = 921377) (by norm_num)
theorem B1891765 : Blo 1636017 1891765 := bbase (se 5 (by rfl) ⟨88676, by rfl⟩ : syracuseStep 1891765 = 177353) (by norm_num)
theorem B1842637 : Blo 1636017 1842637 := bbase (se 3 (by rfl) ⟨345494, by rfl⟩ : syracuseStep 1842637 = 690989) (by norm_num)
theorem B1867217 : Blo 1636017 1867217 := bbase (se 2 (by rfl) ⟨700206, by rfl⟩ : syracuseStep 1867217 = 1400413) (by norm_num)
theorem B6995429 : Blo 1636017 6995429 := bbase (se 4 (by rfl) ⟨655821, by rfl⟩ : syracuseStep 6995429 = 1311643) (by norm_num)
theorem B1842673 : Blo 1636017 1842673 := bbase (se 2 (by rfl) ⟨691002, by rfl⟩ : syracuseStep 1842673 = 1382005) (by norm_num)
theorem B7085573 : Blo 1636017 7085573 := bbase (se 4 (by rfl) ⟨664272, by rfl⟩ : syracuseStep 7085573 = 1328545) (by norm_num)
theorem B2072081 : Blo 1636017 2072081 := bbase (se 2 (by rfl) ⟨777030, by rfl⟩ : syracuseStep 2072081 = 1554061) (by norm_num)
theorem B1842709 : Blo 1636017 1842709 := bbase (se 6 (by rfl) ⟨43188, by rfl⟩ : syracuseStep 1842709 = 86377) (by norm_num)
theorem B2948645 : Blo 1636017 2948645 := bbase (se 4 (by rfl) ⟨276435, by rfl⟩ : syracuseStep 2948645 = 552871) (by norm_num)
theorem B3497509 : Blo 1636017 3497509 := bbase (se 4 (by rfl) ⟨327891, by rfl⟩ : syracuseStep 3497509 = 655783) (by norm_num)
theorem B1842745 : Blo 1636017 1842745 := bbase (se 2 (by rfl) ⟨691029, by rfl⟩ : syracuseStep 1842745 = 1382059) (by norm_num)
theorem B4144709 : Blo 1636017 4144709 := bbase (se 4 (by rfl) ⟨388566, by rfl⟩ : syracuseStep 4144709 = 777133) (by norm_num)
theorem B2072137 : Blo 1636017 2072137 := bbase (se 2 (by rfl) ⟨777051, by rfl⟩ : syracuseStep 2072137 = 1554103) (by norm_num)
theorem B8085077 : Blo 1636017 8085077 := bbase (se 8 (by rfl) ⟨47373, by rfl⟩ : syracuseStep 8085077 = 94747) (by norm_num)
theorem B3931757 : Blo 1636017 3931757 := bbase (se 3 (by rfl) ⟨737204, by rfl⟩ : syracuseStep 3931757 = 1474409) (by norm_num)
theorem B2621069 : Blo 1636017 2621069 := bbase (se 3 (by rfl) ⟨491450, by rfl⟩ : syracuseStep 2621069 = 982901) (by norm_num)
theorem B2072233 : Blo 1636017 2072233 := bbase (se 2 (by rfl) ⟨777087, by rfl⟩ : syracuseStep 2072233 = 1554175) (by norm_num)
theorem B2621165 : Blo 1636017 2621165 := bbase (se 3 (by rfl) ⟨491468, by rfl⟩ : syracuseStep 2621165 = 982937) (by norm_num)
theorem B2621197 : Blo 1636017 2621197 := bbase (se 3 (by rfl) ⟨491474, by rfl⟩ : syracuseStep 2621197 = 982949) (by norm_num)
theorem B3931949 : Blo 1636017 3931949 := bbase (se 3 (by rfl) ⟨737240, by rfl⟩ : syracuseStep 3931949 = 1474481) (by norm_num)
theorem B10485557 : Blo 1636017 10485557 := bbase (se 5 (by rfl) ⟨491510, by rfl⟩ : syracuseStep 10485557 = 983021) (by norm_num)
theorem B2072405 : Blo 1636017 2072405 := bbase (se 9 (by rfl) ⟨6071, by rfl⟩ : syracuseStep 2072405 = 12143) (by norm_num)
theorem B1965917 : Blo 1636017 1965917 := bbase (se 3 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 1965917 = 737219) (by norm_num)
theorem B1965965 : Blo 1636017 1965965 := bbase (se 3 (by rfl) ⟨368618, by rfl⟩ : syracuseStep 1965965 = 737237) (by norm_num)
theorem B2072461 : Blo 1636017 2072461 := bbase (se 3 (by rfl) ⟨388586, by rfl⟩ : syracuseStep 2072461 = 777173) (by norm_num)
theorem B4202389 : Blo 1636017 4202389 := bbase (se 6 (by rfl) ⟨98493, by rfl⟩ : syracuseStep 4202389 = 196987) (by norm_num)
theorem B4145053 : Blo 1636017 4145053 := bbase (se 3 (by rfl) ⟨777197, by rfl⟩ : syracuseStep 4145053 = 1554395) (by norm_num)
theorem B2072557 : Blo 1636017 2072557 := bbase (se 3 (by rfl) ⟨388604, by rfl⟩ : syracuseStep 2072557 = 777209) (by norm_num)
theorem B3735601 : Blo 1636017 3735601 := bstep (se 2 (by rfl) ⟨1400850, by rfl⟩ : syracuseStep 3735601 = 2801701) B2801701
theorem B4423747 : Blo 1636017 4423747 := bstep (se 1 (by rfl) ⟨3317810, by rfl⟩ : syracuseStep 4423747 = 6635621) B6635621
theorem B20185157 : Blo 1636017 20185157 := bstep (se 4 (by rfl) ⟨1892358, by rfl⟩ : syracuseStep 20185157 = 3784717) B3784717
theorem B2760817 : Blo 1636017 2760817 := bstep (se 2 (by rfl) ⟨1035306, by rfl⟩ : syracuseStep 2760817 = 2070613) B2070613
theorem B2760851 : Blo 1636017 2760851 := bstep (se 1 (by rfl) ⟨2070638, by rfl⟩ : syracuseStep 2760851 = 4141277) B4141277
theorem B6635683 : Blo 1636017 6635683 := bstep (se 1 (by rfl) ⟨4976762, by rfl⟩ : syracuseStep 6635683 = 9953525) B9953525
theorem B6996145 : Blo 1636017 6996145 := bstep (se 2 (by rfl) ⟨2623554, by rfl⟩ : syracuseStep 6996145 = 5247109) B5247109
theorem B4726993 : Blo 1636017 4726993 := bstep (se 2 (by rfl) ⟨1772622, by rfl⟩ : syracuseStep 4726993 = 3545245) B3545245
theorem B12427505 : Blo 1636017 12427505 := bstep (se 2 (by rfl) ⟨4660314, by rfl⟩ : syracuseStep 12427505 = 9320629) B9320629
theorem B4661489 : Blo 1636017 4661489 := bstep (se 2 (by rfl) ⟨1748058, by rfl⟩ : syracuseStep 4661489 = 3496117) B3496117
theorem B7864589 : Blo 1636017 7864589 := bstep (se 3 (by rfl) ⟨1474610, by rfl⟩ : syracuseStep 7864589 = 2949221) B2949221
theorem B2760979 : Blo 1636017 2760979 := bstep (se 1 (by rfl) ⟨2070734, by rfl⟩ : syracuseStep 2760979 = 4141469) B4141469
theorem B5898545 : Blo 1636017 5898545 := bstep (se 2 (by rfl) ⟨2211954, by rfl⟩ : syracuseStep 5898545 = 4423909) B4423909
theorem B4145489 : Blo 1636017 4145489 := bstep (se 2 (by rfl) ⟨1554558, by rfl⟩ : syracuseStep 4145489 = 3109117) B3109117
theorem B8290673 : Blo 1636017 8290673 := bstep (se 2 (by rfl) ⟨3109002, by rfl⟩ : syracuseStep 8290673 = 6218005) B6218005
theorem B2072947 : Blo 1636017 2072947 := bstep (se 1 (by rfl) ⟨1554710, by rfl⟩ : syracuseStep 2072947 = 3109421) B3109421
theorem B4145539 : Blo 1636017 4145539 := bstep (se 1 (by rfl) ⟨3109154, by rfl⟩ : syracuseStep 4145539 = 6218309) B6218309
theorem B2761121 : Blo 1636017 2761121 := bstep (se 2 (by rfl) ⟨1035420, by rfl⟩ : syracuseStep 2761121 = 2070841) B2070841
theorem B5898673 : Blo 1636017 5898673 := bstep (se 2 (by rfl) ⟨2212002, by rfl⟩ : syracuseStep 5898673 = 4424005) B4424005
theorem B2990513 : Blo 1636017 2990513 := bstep (se 2 (by rfl) ⟨1121442, by rfl⟩ : syracuseStep 2990513 = 2242885) B2242885
theorem B25199045 : Blo 1636017 25199045 := bstep (se 4 (by rfl) ⟨2362410, by rfl⟩ : syracuseStep 25199045 = 4724821) B4724821
theorem B8282573 : Blo 1636017 8282573 := bstep (se 3 (by rfl) ⟨1552982, by rfl⟩ : syracuseStep 8282573 = 3105965) B3105965
theorem B2073043 : Blo 1636017 2073043 := bstep (se 1 (by rfl) ⟨1554782, by rfl⟩ : syracuseStep 2073043 = 3109565) B3109565
theorem B4145681 : Blo 1636017 4145681 := bstep (se 2 (by rfl) ⟨1554630, by rfl⟩ : syracuseStep 4145681 = 3109261) B3109261
theorem B2761249 : Blo 1636017 2761249 := bstep (se 2 (by rfl) ⟨1035468, by rfl⟩ : syracuseStep 2761249 = 2070937) B2070937
theorem B2761283 : Blo 1636017 2761283 := bstep (se 1 (by rfl) ⟨2070962, by rfl⟩ : syracuseStep 2761283 = 4141925) B4141925
theorem B2622017 : Blo 1636017 2622017 := bstep (se 2 (by rfl) ⟨983256, by rfl⟩ : syracuseStep 2622017 = 1966513) B1966513
theorem B2212435 : Blo 1636017 2212435 := bstep (se 1 (by rfl) ⟨1659326, by rfl⟩ : syracuseStep 2212435 = 3318653) B3318653
theorem B5522093 : Blo 1636017 5522093 := bstep (se 3 (by rfl) ⟨1035392, by rfl⟩ : syracuseStep 5522093 = 2070785) B2070785
theorem B2761411 : Blo 1636017 2761411 := bstep (se 1 (by rfl) ⟨2071058, by rfl⟩ : syracuseStep 2761411 = 4142117) B4142117
theorem B4727501 : Blo 1636017 4727501 := bstep (se 3 (by rfl) ⟨886406, by rfl⟩ : syracuseStep 4727501 = 1772813) B1772813
theorem B5522147 : Blo 1636017 5522147 := bstep (se 1 (by rfl) ⟨4141610, by rfl⟩ : syracuseStep 5522147 = 8283221) B8283221
theorem B2761553 : Blo 1636017 2761553 := bstep (se 2 (by rfl) ⟨1035582, by rfl⟩ : syracuseStep 2761553 = 2071165) B2071165
theorem B9323363 : Blo 1636017 9323363 := bstep (se 1 (by rfl) ⟨6992522, by rfl⟩ : syracuseStep 9323363 = 13985045) B13985045
theorem B37823345 : Blo 1636017 37823345 := bstep (se 2 (by rfl) ⟨14183754, by rfl⟩ : syracuseStep 37823345 = 28367509) B28367509
theorem B4662161 : Blo 1636017 4662161 := bstep (se 2 (by rfl) ⟨1748310, by rfl⟩ : syracuseStep 4662161 = 3496621) B3496621
theorem B2761681 : Blo 1636017 2761681 := bstep (se 2 (by rfl) ⟨1035630, by rfl⟩ : syracuseStep 2761681 = 2071261) B2071261
theorem B2950115 : Blo 1636017 2950115 := bstep (se 1 (by rfl) ⟨2212586, by rfl⟩ : syracuseStep 2950115 = 4425173) B4425173
theorem B5522417 : Blo 1636017 5522417 := bstep (se 2 (by rfl) ⟨2070906, by rfl⟩ : syracuseStep 5522417 = 4141813) B4141813
theorem B2761715 : Blo 1636017 2761715 := bstep (se 1 (by rfl) ⟨2071286, by rfl⟩ : syracuseStep 2761715 = 4142573) B4142573
theorem B6218765 : Blo 1636017 6218765 := bstep (se 3 (by rfl) ⟨1166018, by rfl⟩ : syracuseStep 6218765 = 2332037) B2332037
theorem B2761843 : Blo 1636017 2761843 := bstep (se 1 (by rfl) ⟨2071382, by rfl⟩ : syracuseStep 2761843 = 4142765) B4142765
theorem B3106019 : Blo 1636017 3106019 := bstep (se 1 (by rfl) ⟨2329514, by rfl⟩ : syracuseStep 3106019 = 4659029) B4659029
theorem B15738097 : Blo 1636017 15738097 := bstep (se 2 (by rfl) ⟨5901786, by rfl⟩ : syracuseStep 15738097 = 11803573) B11803573
theorem B2761985 : Blo 1636017 2761985 := bstep (se 2 (by rfl) ⟨1035744, by rfl⟩ : syracuseStep 2761985 = 2071489) B2071489
theorem B2622755 : Blo 1636017 2622755 := bstep (se 1 (by rfl) ⟨1967066, by rfl⟩ : syracuseStep 2622755 = 3934133) B3934133
theorem B6989105 : Blo 1636017 6989105 := bstep (se 2 (by rfl) ⟨2620914, by rfl⟩ : syracuseStep 6989105 = 5241829) B5241829
theorem B2762113 : Blo 1636017 2762113 := bstep (se 2 (by rfl) ⟨1035792, by rfl⟩ : syracuseStep 2762113 = 2071585) B2071585
theorem B2762147 : Blo 1636017 2762147 := bstep (se 1 (by rfl) ⟨2071610, by rfl⟩ : syracuseStep 2762147 = 4143221) B4143221
theorem B2950577 : Blo 1636017 2950577 := bstep (se 2 (by rfl) ⟨1106466, by rfl⟩ : syracuseStep 2950577 = 2212933) B2212933
theorem B3458513 : Blo 1636017 3458513 := bstep (se 2 (by rfl) ⟨1296942, by rfl⟩ : syracuseStep 3458513 = 2593885) B2593885
theorem B5244419 : Blo 1636017 5244419 := bstep (se 1 (by rfl) ⟨3933314, by rfl⟩ : syracuseStep 5244419 = 7866629) B7866629
theorem B5522957 : Blo 1636017 5522957 := bstep (se 3 (by rfl) ⟨1035554, by rfl⟩ : syracuseStep 5522957 = 2071109) B2071109
theorem B2762275 : Blo 1636017 2762275 := bstep (se 1 (by rfl) ⟨2071706, by rfl⟩ : syracuseStep 2762275 = 4143413) B4143413
theorem B5523011 : Blo 1636017 5523011 := bstep (se 1 (by rfl) ⟨4142258, by rfl⟩ : syracuseStep 5523011 = 8284517) B8284517
theorem B8636003 : Blo 1636017 8636003 := bstep (se 1 (by rfl) ⟨6477002, by rfl⟩ : syracuseStep 8636003 = 12954005) B12954005
theorem B5244547 : Blo 1636017 5244547 := bstep (se 1 (by rfl) ⟨3933410, by rfl⟩ : syracuseStep 5244547 = 7866821) B7866821
theorem B4662947 : Blo 1636017 4662947 := bstep (se 1 (by rfl) ⟨3497210, by rfl⟩ : syracuseStep 4662947 = 6994421) B6994421
theorem B2762417 : Blo 1636017 2762417 := bstep (se 2 (by rfl) ⟨1035906, by rfl⟩ : syracuseStep 2762417 = 2071813) B2071813
theorem B5244689 : Blo 1636017 5244689 := bstep (se 2 (by rfl) ⟨1966758, by rfl⟩ : syracuseStep 5244689 = 3933517) B3933517
theorem B8292131 : Blo 1636017 8292131 := bstep (se 1 (by rfl) ⟨6219098, by rfl⟩ : syracuseStep 8292131 = 12438197) B12438197
theorem B2762545 : Blo 1636017 2762545 := bstep (se 2 (by rfl) ⟨1035954, by rfl⟩ : syracuseStep 2762545 = 2071909) B2071909
theorem B17704757 : Blo 1636017 17704757 := bstep (se 5 (by rfl) ⟨829910, by rfl⟩ : syracuseStep 17704757 = 1659821) B1659821
theorem B5523281 : Blo 1636017 5523281 := bstep (se 2 (by rfl) ⟨2071230, by rfl⟩ : syracuseStep 5523281 = 4142461) B4142461
theorem B2762579 : Blo 1636017 2762579 := bstep (se 1 (by rfl) ⟨2071934, by rfl⟩ : syracuseStep 2762579 = 4143869) B4143869
theorem B5244803 : Blo 1636017 5244803 := bstep (se 1 (by rfl) ⟨3933602, by rfl⟩ : syracuseStep 5244803 = 7867205) B7867205
theorem B6989773 : Blo 1636017 6989773 := bstep (se 3 (by rfl) ⟨1310582, by rfl⟩ : syracuseStep 6989773 = 2621165) B2621165
theorem B2762707 : Blo 1636017 2762707 := bstep (se 1 (by rfl) ⟨2072030, by rfl⟩ : syracuseStep 2762707 = 4144061) B4144061
theorem B12593123 : Blo 1636017 12593123 := bstep (se 1 (by rfl) ⟨9444842, by rfl⟩ : syracuseStep 12593123 = 18889685) B18889685
theorem B4663277 : Blo 1636017 4663277 := bstep (se 3 (by rfl) ⟨874364, by rfl⟩ : syracuseStep 4663277 = 1748729) B1748729
theorem B4663345 : Blo 1636017 4663345 := bstep (se 2 (by rfl) ⟨1748754, by rfl⟩ : syracuseStep 4663345 = 3497509) B3497509
theorem B3237937 : Blo 1636017 3237937 := bstep (se 2 (by rfl) ⟨1214226, by rfl⟩ : syracuseStep 3237937 = 2428453) B2428453
theorem B2762849 : Blo 1636017 2762849 := bstep (se 2 (by rfl) ⟨1036068, by rfl⟩ : syracuseStep 2762849 = 2072137) B2072137
theorem B2762977 : Blo 1636017 2762977 := bstep (se 2 (by rfl) ⟨1036116, by rfl⟩ : syracuseStep 2762977 = 2072233) B2072233
theorem B2763011 : Blo 1636017 2763011 := bstep (se 1 (by rfl) ⟨2072258, by rfl⟩ : syracuseStep 2763011 = 4144517) B4144517
theorem B2623747 : Blo 1636017 2623747 := bstep (se 1 (by rfl) ⟨1967810, by rfl⟩ : syracuseStep 2623747 = 3935621) B3935621
theorem B3107089 : Blo 1636017 3107089 := bstep (se 2 (by rfl) ⟨1165158, by rfl⟩ : syracuseStep 3107089 = 2330317) B2330317
theorem B4663619 : Blo 1636017 4663619 := bstep (se 1 (by rfl) ⟨3497714, by rfl⟩ : syracuseStep 4663619 = 6995429) B6995429
theorem B5523821 : Blo 1636017 5523821 := bstep (se 3 (by rfl) ⟨1035716, by rfl⟩ : syracuseStep 5523821 = 2071433) B2071433
theorem B2763139 : Blo 1636017 2763139 := bstep (se 1 (by rfl) ⟨2072354, by rfl⟩ : syracuseStep 2763139 = 4144709) B4144709
theorem B5523875 : Blo 1636017 5523875 := bstep (se 1 (by rfl) ⟨4142906, by rfl⟩ : syracuseStep 5523875 = 8285813) B8285813
theorem B1747379 : Blo 1636017 1747379 := bstep (se 1 (by rfl) ⟨1310534, by rfl⟩ : syracuseStep 1747379 = 2621069) B2621069
theorem B4426211 : Blo 1636017 4426211 := bstep (se 1 (by rfl) ⟨3319658, by rfl⟩ : syracuseStep 4426211 = 6639317) B6639317
theorem B2763281 : Blo 1636017 2763281 := bstep (se 2 (by rfl) ⟨1036230, by rfl⟩ : syracuseStep 2763281 = 2072461) B2072461
theorem B6990371 : Blo 1636017 6990371 := bstep (se 1 (by rfl) ⟨5242778, by rfl⟩ : syracuseStep 6990371 = 10485557) B10485557
theorem B6212173 : Blo 1636017 6212173 := bstep (se 3 (by rfl) ⟨1164782, by rfl⟩ : syracuseStep 6212173 = 2329565) B2329565
theorem B2763409 : Blo 1636017 2763409 := bstep (se 2 (by rfl) ⟨1036278, by rfl⟩ : syracuseStep 2763409 = 2072557) B2072557
theorem B5524145 : Blo 1636017 5524145 := bstep (se 2 (by rfl) ⟨2071554, by rfl⟩ : syracuseStep 5524145 = 4143109) B4143109
theorem B2763443 : Blo 1636017 2763443 := bstep (se 1 (by rfl) ⟨2072582, by rfl⟩ : syracuseStep 2763443 = 4145165) B4145165
theorem B2763571 : Blo 1636017 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B255085453 : Blo 1636017 255085453 := bstep (se 3 (by rfl) ⟨47828522, by rfl⟩ : syracuseStep 255085453 = 95657045) B95657045
theorem B2763713 : Blo 1636017 2763713 := bstep (se 2 (by rfl) ⟨1036392, by rfl⟩ : syracuseStep 2763713 = 2072785) B2072785
theorem B3681233 : Blo 1636017 3681233 := bstep (se 2 (by rfl) ⟨1380462, by rfl⟩ : syracuseStep 3681233 = 2760925) B2760925
theorem B3681251 : Blo 1636017 3681251 := bstep (se 1 (by rfl) ⟨2760938, by rfl⟩ : syracuseStep 3681251 = 5521877) B5521877
theorem B2329651 : Blo 1636017 2329651 := bstep (se 1 (by rfl) ⟨1747238, by rfl⟩ : syracuseStep 2329651 = 3494477) B3494477
theorem B2763841 : Blo 1636017 2763841 := bstep (se 2 (by rfl) ⟨1036440, by rfl⟩ : syracuseStep 2763841 = 2072881) B2072881
theorem B2763875 : Blo 1636017 2763875 := bstep (se 1 (by rfl) ⟨2072906, by rfl⟩ : syracuseStep 2763875 = 4145813) B4145813
theorem B4664461 : Blo 1636017 4664461 := bstep (se 3 (by rfl) ⟨874586, by rfl⟩ : syracuseStep 4664461 = 1749173) B1749173
theorem B5598353 : Blo 1636017 5598353 := bstep (se 2 (by rfl) ⟨2099382, by rfl⟩ : syracuseStep 5598353 = 4198765) B4198765
theorem B5524685 : Blo 1636017 5524685 := bstep (se 3 (by rfl) ⟨1035878, by rfl⟩ : syracuseStep 5524685 = 2071757) B2071757
theorem B2764003 : Blo 1636017 2764003 := bstep (se 1 (by rfl) ⟨2073002, by rfl⟩ : syracuseStep 2764003 = 4146005) B4146005
theorem B3681521 : Blo 1636017 3681521 := bstep (se 2 (by rfl) ⟨1380570, by rfl⟩ : syracuseStep 3681521 = 2761141) B2761141
theorem B3681539 : Blo 1636017 3681539 := bstep (se 1 (by rfl) ⟨2761154, by rfl⟩ : syracuseStep 3681539 = 5522309) B5522309
theorem B5524739 : Blo 1636017 5524739 := bstep (se 1 (by rfl) ⟨4143554, by rfl⟩ : syracuseStep 5524739 = 8287109) B8287109
theorem B8285489 : Blo 1636017 8285489 := bstep (se 2 (by rfl) ⟨3107058, by rfl⟩ : syracuseStep 8285489 = 6214117) B6214117
theorem B3108145 : Blo 1636017 3108145 := bstep (se 2 (by rfl) ⟨1165554, by rfl⟩ : syracuseStep 3108145 = 2331109) B2331109
theorem B6212963 : Blo 1636017 6212963 := bstep (se 1 (by rfl) ⟨4659722, by rfl⟩ : syracuseStep 6212963 = 9319445) B9319445
theorem B2764145 : Blo 1636017 2764145 := bstep (se 2 (by rfl) ⟨1036554, by rfl⟩ : syracuseStep 2764145 = 2073109) B2073109
theorem B2329987 : Blo 1636017 2329987 := bstep (se 1 (by rfl) ⟨1747490, by rfl⟩ : syracuseStep 2329987 = 3494981) B3494981
theorem B5615021 : Blo 1636017 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B3681809 : Blo 1636017 3681809 := bstep (se 2 (by rfl) ⟨1380678, by rfl⟩ : syracuseStep 3681809 = 2761357) B2761357
theorem B5525009 : Blo 1636017 5525009 := bstep (se 2 (by rfl) ⟨2071878, by rfl⟩ : syracuseStep 5525009 = 4143757) B4143757
theorem B3681827 : Blo 1636017 3681827 := bstep (se 1 (by rfl) ⟨2761370, by rfl⟩ : syracuseStep 3681827 = 5522741) B5522741
theorem B5246545 : Blo 1636017 5246545 := bstep (se 2 (by rfl) ⟨1967454, by rfl⟩ : syracuseStep 5246545 = 3934909) B3934909
theorem B9317987 : Blo 1636017 9317987 := bstep (se 1 (by rfl) ⟨6988490, by rfl⟩ : syracuseStep 9317987 = 13976981) B13976981
theorem B20967011 : Blo 1636017 20967011 := bstep (se 1 (by rfl) ⟨15725258, by rfl⟩ : syracuseStep 20967011 = 31450517) B31450517
theorem B3108547 : Blo 1636017 3108547 := bstep (se 1 (by rfl) ⟨2331410, by rfl⟩ : syracuseStep 3108547 = 4662821) B4662821
theorem B3108593 : Blo 1636017 3108593 := bstep (se 2 (by rfl) ⟨1165722, by rfl⟩ : syracuseStep 3108593 = 2331445) B2331445
theorem B3682097 : Blo 1636017 3682097 := bstep (se 2 (by rfl) ⟨1380786, by rfl⟩ : syracuseStep 3682097 = 2761573) B2761573
theorem B3682115 : Blo 1636017 3682115 := bstep (se 1 (by rfl) ⟨2761586, by rfl⟩ : syracuseStep 3682115 = 5523173) B5523173
theorem B4722605 : Blo 1636017 4722605 := bstep (se 3 (by rfl) ⟨885488, by rfl⟩ : syracuseStep 4722605 = 1770977) B1770977
theorem B2330545 : Blo 1636017 2330545 := bstep (se 2 (by rfl) ⟨873954, by rfl⟩ : syracuseStep 2330545 = 1747909) B1747909
theorem B2330579 : Blo 1636017 2330579 := bstep (se 1 (by rfl) ⟨1747934, by rfl⟩ : syracuseStep 2330579 = 3495869) B3495869
theorem B1748947 : Blo 1636017 1748947 := bstep (se 1 (by rfl) ⟨1311710, by rfl⟩ : syracuseStep 1748947 = 2623421) B2623421
theorem B2838497 : Blo 1636017 2838497 := bstep (se 2 (by rfl) ⟨1064436, by rfl⟩ : syracuseStep 2838497 = 2128873) B2128873
theorem B6213617 : Blo 1636017 6213617 := bstep (se 2 (by rfl) ⟨2330106, by rfl⟩ : syracuseStep 6213617 = 4660213) B4660213
theorem B3108881 : Blo 1636017 3108881 := bstep (se 2 (by rfl) ⟨1165830, by rfl⟩ : syracuseStep 3108881 = 2331661) B2331661
theorem B5525549 : Blo 1636017 5525549 := bstep (se 3 (by rfl) ⟨1036040, by rfl⟩ : syracuseStep 5525549 = 2072081) B2072081
theorem B4255811 : Blo 1636017 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B3682385 : Blo 1636017 3682385 := bstep (se 2 (by rfl) ⟨1380894, by rfl⟩ : syracuseStep 3682385 = 2761789) B2761789
theorem B3682403 : Blo 1636017 3682403 := bstep (se 1 (by rfl) ⟨2761802, by rfl⟩ : syracuseStep 3682403 = 5523605) B5523605
theorem B5525603 : Blo 1636017 5525603 := bstep (se 1 (by rfl) ⟨4144202, by rfl⟩ : syracuseStep 5525603 = 8288405) B8288405
theorem B1659043 : Blo 1636017 1659043 := bstep (se 1 (by rfl) ⟨1244282, by rfl⟩ : syracuseStep 1659043 = 2488565) B2488565
theorem B4788397 : Blo 1636017 4788397 := bstep (se 3 (by rfl) ⟨897824, by rfl⟩ : syracuseStep 4788397 = 1795649) B1795649
theorem B3592387 : Blo 1636017 3592387 := bstep (se 1 (by rfl) ⟨2694290, by rfl⟩ : syracuseStep 3592387 = 5388581) B5388581
theorem B102133973 : Blo 1636017 102133973 := bstep (se 7 (by rfl) ⟨1196882, by rfl⟩ : syracuseStep 102133973 = 2393765) B2393765
theorem B3682673 : Blo 1636017 3682673 := bstep (se 2 (by rfl) ⟨1381002, by rfl⟩ : syracuseStep 3682673 = 2762005) B2762005
theorem B5525873 : Blo 1636017 5525873 := bstep (se 2 (by rfl) ⟨2072202, by rfl⟩ : syracuseStep 5525873 = 4144405) B4144405
theorem B3682691 : Blo 1636017 3682691 := bstep (se 1 (by rfl) ⟨2762018, by rfl⟩ : syracuseStep 3682691 = 5524037) B5524037
theorem B4141489 : Blo 1636017 4141489 := bstep (se 2 (by rfl) ⟨1553058, by rfl⟩ : syracuseStep 4141489 = 3106117) B3106117
theorem B2331137 : Blo 1636017 2331137 := bstep (se 2 (by rfl) ⟨874176, by rfl⟩ : syracuseStep 2331137 = 1748353) B1748353
theorem B2454035 : Blo 1636017 2454035 := bstep (se 1 (by rfl) ⟨1840526, by rfl⟩ : syracuseStep 2454035 = 3681053) B3681053
theorem B2454065 : Blo 1636017 2454065 := bstep (se 2 (by rfl) ⟨920274, by rfl⟩ : syracuseStep 2454065 = 1840549) B1840549
theorem B2454083 : Blo 1636017 2454083 := bstep (se 1 (by rfl) ⟨1840562, by rfl⟩ : syracuseStep 2454083 = 3681125) B3681125
theorem B9318989 : Blo 1636017 9318989 := bstep (se 3 (by rfl) ⟨1747310, by rfl⟩ : syracuseStep 9318989 = 3494621) B3494621
theorem B2331217 : Blo 1636017 2331217 := bstep (se 2 (by rfl) ⟨874206, by rfl⟩ : syracuseStep 2331217 = 1748413) B1748413
theorem B2454113 : Blo 1636017 2454113 := bstep (se 2 (by rfl) ⟨920292, by rfl⟩ : syracuseStep 2454113 = 1840585) B1840585
theorem B2454131 : Blo 1636017 2454131 := bstep (se 1 (by rfl) ⟨1840598, by rfl⟩ : syracuseStep 2454131 = 3681197) B3681197
theorem B2454161 : Blo 1636017 2454161 := bstep (se 2 (by rfl) ⟨920310, by rfl⟩ : syracuseStep 2454161 = 1840621) B1840621
theorem B3682961 : Blo 1636017 3682961 := bstep (se 2 (by rfl) ⟨1381110, by rfl⟩ : syracuseStep 3682961 = 2762221) B2762221
theorem B2454179 : Blo 1636017 2454179 := bstep (se 1 (by rfl) ⟨1840634, by rfl⟩ : syracuseStep 2454179 = 3681269) B3681269
theorem B3682979 : Blo 1636017 3682979 := bstep (se 1 (by rfl) ⟨2762234, by rfl⟩ : syracuseStep 3682979 = 5524469) B5524469
theorem B2454209 : Blo 1636017 2454209 := bstep (se 2 (by rfl) ⟨920328, by rfl⟩ : syracuseStep 2454209 = 1840657) B1840657
theorem B4141763 : Blo 1636017 4141763 := bstep (se 1 (by rfl) ⟨3106322, by rfl⟩ : syracuseStep 4141763 = 6212645) B6212645
theorem B26546885 : Blo 1636017 26546885 := bstep (se 4 (by rfl) ⟨2488770, by rfl⟩ : syracuseStep 26546885 = 4977541) B4977541
theorem B8852165 : Blo 1636017 8852165 := bstep (se 4 (by rfl) ⟨829890, by rfl⟩ : syracuseStep 8852165 = 1659781) B1659781
theorem B2454227 : Blo 1636017 2454227 := bstep (se 1 (by rfl) ⟨1840670, by rfl⟩ : syracuseStep 2454227 = 3681341) B3681341
theorem B8286947 : Blo 1636017 8286947 := bstep (se 1 (by rfl) ⟨6215210, by rfl⟩ : syracuseStep 8286947 = 12430421) B12430421
theorem B3109603 : Blo 1636017 3109603 := bstep (se 1 (by rfl) ⟨2332202, by rfl⟩ : syracuseStep 3109603 = 4664405) B4664405
theorem B2454257 : Blo 1636017 2454257 := bstep (se 2 (by rfl) ⟨920346, by rfl⟩ : syracuseStep 2454257 = 1840693) B1840693
theorem B2454275 : Blo 1636017 2454275 := bstep (se 1 (by rfl) ⟨1840706, by rfl⟩ : syracuseStep 2454275 = 3681413) B3681413
theorem B10490629 : Blo 1636017 10490629 := bstep (se 4 (by rfl) ⟨983496, by rfl⟩ : syracuseStep 10490629 = 1966993) B1966993
theorem B2454305 : Blo 1636017 2454305 := bstep (se 2 (by rfl) ⟨920364, by rfl⟩ : syracuseStep 2454305 = 1840729) B1840729
theorem B2454323 : Blo 1636017 2454323 := bstep (se 1 (by rfl) ⟨1840742, by rfl⟩ : syracuseStep 2454323 = 3681485) B3681485
theorem B22410053 : Blo 1636017 22410053 := bstep (se 4 (by rfl) ⟨2100942, by rfl⟩ : syracuseStep 22410053 = 4201885) B4201885
theorem B2454353 : Blo 1636017 2454353 := bstep (se 2 (by rfl) ⟨920382, by rfl⟩ : syracuseStep 2454353 = 1840765) B1840765
theorem B2454371 : Blo 1636017 2454371 := bstep (se 1 (by rfl) ⟨1840778, by rfl⟩ : syracuseStep 2454371 = 3681557) B3681557
theorem B2454401 : Blo 1636017 2454401 := bstep (se 2 (by rfl) ⟨920400, by rfl⟩ : syracuseStep 2454401 = 1840801) B1840801
theorem B4141955 : Blo 1636017 4141955 := bstep (se 1 (by rfl) ⟨3106466, by rfl⟩ : syracuseStep 4141955 = 6212933) B6212933
theorem B5526413 : Blo 1636017 5526413 := bstep (se 3 (by rfl) ⟨1036202, by rfl⟩ : syracuseStep 5526413 = 2072405) B2072405
theorem B2454419 : Blo 1636017 2454419 := bstep (se 1 (by rfl) ⟨1840814, by rfl⟩ : syracuseStep 2454419 = 3681629) B3681629
theorem B3494819 : Blo 1636017 3494819 := bstep (se 1 (by rfl) ⟨2621114, by rfl⟩ : syracuseStep 3494819 = 5242229) B5242229
theorem B5600173 : Blo 1636017 5600173 := bstep (se 3 (by rfl) ⟨1050032, by rfl⟩ : syracuseStep 5600173 = 2100065) B2100065
theorem B2454449 : Blo 1636017 2454449 := bstep (se 2 (by rfl) ⟨920418, by rfl⟩ : syracuseStep 2454449 = 1840837) B1840837
theorem B3683249 : Blo 1636017 3683249 := bstep (se 2 (by rfl) ⟨1381218, by rfl⟩ : syracuseStep 3683249 = 2762437) B2762437
theorem B2454467 : Blo 1636017 2454467 := bstep (se 1 (by rfl) ⟨1840850, by rfl⟩ : syracuseStep 2454467 = 3681701) B3681701
theorem B3683267 : Blo 1636017 3683267 := bstep (se 1 (by rfl) ⟨2762450, by rfl⟩ : syracuseStep 3683267 = 5524901) B5524901
theorem B5526467 : Blo 1636017 5526467 := bstep (se 1 (by rfl) ⟨4144850, by rfl⟩ : syracuseStep 5526467 = 8289701) B8289701
theorem B2454497 : Blo 1636017 2454497 := bstep (se 2 (by rfl) ⟨920436, by rfl⟩ : syracuseStep 2454497 = 1840873) B1840873
theorem B2454515 : Blo 1636017 2454515 := bstep (se 1 (by rfl) ⟨1840886, by rfl⟩ : syracuseStep 2454515 = 3681773) B3681773
theorem B4723715 : Blo 1636017 4723715 := bstep (se 1 (by rfl) ⟨3542786, by rfl⟩ : syracuseStep 4723715 = 7085573) B7085573
theorem B2454545 : Blo 1636017 2454545 := bstep (se 2 (by rfl) ⟨920454, by rfl⟩ : syracuseStep 2454545 = 1840909) B1840909
theorem B3494929 : Blo 1636017 3494929 := bstep (se 2 (by rfl) ⟨1310598, by rfl⟩ : syracuseStep 3494929 = 2621197) B2621197
theorem B2454563 : Blo 1636017 2454563 := bstep (se 1 (by rfl) ⟨1840922, by rfl⟩ : syracuseStep 2454563 = 3681845) B3681845
theorem B2454593 : Blo 1636017 2454593 := bstep (se 2 (by rfl) ⟨920472, by rfl⟩ : syracuseStep 2454593 = 1840945) B1840945
theorem B2454611 : Blo 1636017 2454611 := bstep (se 1 (by rfl) ⟨1840958, by rfl⟩ : syracuseStep 2454611 = 3681917) B3681917
theorem B229774421 : Blo 1636017 229774421 := bstep (se 8 (by rfl) ⟨1346334, by rfl⟩ : syracuseStep 229774421 = 2692669) B2692669
theorem B2454641 : Blo 1636017 2454641 := bstep (se 2 (by rfl) ⟨920490, by rfl⟩ : syracuseStep 2454641 = 1840981) B1840981
theorem B2454659 : Blo 1636017 2454659 := bstep (se 1 (by rfl) ⟨1840994, by rfl⟩ : syracuseStep 2454659 = 3681989) B3681989
theorem B2454689 : Blo 1636017 2454689 := bstep (se 2 (by rfl) ⟨920508, by rfl⟩ : syracuseStep 2454689 = 1841017) B1841017
theorem B2454707 : Blo 1636017 2454707 := bstep (se 1 (by rfl) ⟨1841030, by rfl⟩ : syracuseStep 2454707 = 3682061) B3682061
theorem B2454737 : Blo 1636017 2454737 := bstep (se 2 (by rfl) ⟨920526, by rfl⟩ : syracuseStep 2454737 = 1841053) B1841053
theorem B3683537 : Blo 1636017 3683537 := bstep (se 2 (by rfl) ⟨1381326, by rfl⟩ : syracuseStep 3683537 = 2762653) B2762653
theorem B5526737 : Blo 1636017 5526737 := bstep (se 2 (by rfl) ⟨2072526, by rfl⟩ : syracuseStep 5526737 = 4145053) B4145053
theorem B2454755 : Blo 1636017 2454755 := bstep (se 1 (by rfl) ⟨1841066, by rfl⟩ : syracuseStep 2454755 = 3682133) B3682133
theorem B3683555 : Blo 1636017 3683555 := bstep (se 1 (by rfl) ⟨2762666, by rfl⟩ : syracuseStep 3683555 = 5525333) B5525333
theorem B2454785 : Blo 1636017 2454785 := bstep (se 2 (by rfl) ⟨920544, by rfl⟩ : syracuseStep 2454785 = 1841089) B1841089
theorem B2454803 : Blo 1636017 2454803 := bstep (se 1 (by rfl) ⟨1841102, by rfl⟩ : syracuseStep 2454803 = 3682205) B3682205
theorem B2454833 : Blo 1636017 2454833 := bstep (se 2 (by rfl) ⟨920562, by rfl⟩ : syracuseStep 2454833 = 1841125) B1841125
theorem B2454851 : Blo 1636017 2454851 := bstep (se 1 (by rfl) ⟨1841138, by rfl⟩ : syracuseStep 2454851 = 3682277) B3682277
theorem B2454881 : Blo 1636017 2454881 := bstep (se 2 (by rfl) ⟨920580, by rfl⟩ : syracuseStep 2454881 = 1841161) B1841161
theorem B2332003 : Blo 1636017 2332003 := bstep (se 1 (by rfl) ⟨1749002, by rfl⟩ : syracuseStep 2332003 = 3498005) B3498005
theorem B2454899 : Blo 1636017 2454899 := bstep (se 1 (by rfl) ⟨1841174, by rfl⟩ : syracuseStep 2454899 = 3682349) B3682349
theorem B12424589 : Blo 1636017 12424589 := bstep (se 3 (by rfl) ⟨2329610, by rfl⟩ : syracuseStep 12424589 = 4659221) B4659221
theorem B2454929 : Blo 1636017 2454929 := bstep (se 2 (by rfl) ⟨920598, by rfl⟩ : syracuseStep 2454929 = 1841197) B1841197
theorem B1840531 : Blo 1636017 1840531 := bstep (se 1 (by rfl) ⟨1380398, by rfl⟩ : syracuseStep 1840531 = 2760797) B2760797
theorem B2454947 : Blo 1636017 2454947 := bstep (se 1 (by rfl) ⟨1841210, by rfl⟩ : syracuseStep 2454947 = 3682421) B3682421
theorem B6215075 : Blo 1636017 6215075 := bstep (se 1 (by rfl) ⟨4661306, by rfl⟩ : syracuseStep 6215075 = 9322613) B9322613
theorem B6215089 : Blo 1636017 6215089 := bstep (se 2 (by rfl) ⟨2330658, by rfl⟩ : syracuseStep 6215089 = 4661317) B4661317
theorem B6387121 : Blo 1636017 6387121 := bstep (se 2 (by rfl) ⟨2395170, by rfl⟩ : syracuseStep 6387121 = 4790341) B4790341
theorem B2454977 : Blo 1636017 2454977 := bstep (se 2 (by rfl) ⟨920616, by rfl⟩ : syracuseStep 2454977 = 1841233) B1841233
theorem B2454995 : Blo 1636017 2454995 := bstep (se 1 (by rfl) ⟨1841246, by rfl⟩ : syracuseStep 2454995 = 3682493) B3682493
theorem B2455025 : Blo 1636017 2455025 := bstep (se 2 (by rfl) ⟨920634, by rfl⟩ : syracuseStep 2455025 = 1841269) B1841269
theorem B3683825 : Blo 1636017 3683825 := bstep (se 2 (by rfl) ⟨1381434, by rfl⟩ : syracuseStep 3683825 = 2762869) B2762869
theorem B2455043 : Blo 1636017 2455043 := bstep (se 1 (by rfl) ⟨1841282, by rfl⟩ : syracuseStep 2455043 = 3682565) B3682565
theorem B3683843 : Blo 1636017 3683843 := bstep (se 1 (by rfl) ⟨2762882, by rfl⟩ : syracuseStep 3683843 = 5525765) B5525765
theorem B8287757 : Blo 1636017 8287757 := bstep (se 3 (by rfl) ⟨1553954, by rfl⟩ : syracuseStep 8287757 = 3107909) B3107909
theorem B13276685 : Blo 1636017 13276685 := bstep (se 3 (by rfl) ⟨2489378, by rfl⟩ : syracuseStep 13276685 = 4978757) B4978757
theorem B2455073 : Blo 1636017 2455073 := bstep (se 2 (by rfl) ⟨920652, by rfl⟩ : syracuseStep 2455073 = 1841305) B1841305
theorem B1840675 : Blo 1636017 1840675 := bstep (se 1 (by rfl) ⟨1380506, by rfl⟩ : syracuseStep 1840675 = 2761013) B2761013
theorem B2455091 : Blo 1636017 2455091 := bstep (se 1 (by rfl) ⟨1841318, by rfl⟩ : syracuseStep 2455091 = 3682637) B3682637
theorem B2455121 : Blo 1636017 2455121 := bstep (se 2 (by rfl) ⟨920670, by rfl⟩ : syracuseStep 2455121 = 1841341) B1841341
theorem B2455139 : Blo 1636017 2455139 := bstep (se 1 (by rfl) ⟨1841354, by rfl⟩ : syracuseStep 2455139 = 3682709) B3682709
theorem B15734371 : Blo 1636017 15734371 := bstep (se 1 (by rfl) ⟨11800778, by rfl⟩ : syracuseStep 15734371 = 23601557) B23601557
theorem B14939747 : Blo 1636017 14939747 := bstep (se 1 (by rfl) ⟨11204810, by rfl⟩ : syracuseStep 14939747 = 22409621) B22409621
theorem B2455169 : Blo 1636017 2455169 := bstep (se 2 (by rfl) ⟨920688, by rfl⟩ : syracuseStep 2455169 = 1841377) B1841377
theorem B2455187 : Blo 1636017 2455187 := bstep (se 1 (by rfl) ⟨1841390, by rfl⟩ : syracuseStep 2455187 = 3682781) B3682781
theorem B2455217 : Blo 1636017 2455217 := bstep (se 2 (by rfl) ⟨920706, by rfl⟩ : syracuseStep 2455217 = 1841413) B1841413
theorem B1636019 : Blo 1636017 1636019 := bstep (se 1 (by rfl) ⟨1227014, by rfl⟩ : syracuseStep 1636019 = 2454029) B2454029
theorem B1840819 : Blo 1636017 1840819 := bstep (se 1 (by rfl) ⟨1380614, by rfl⟩ : syracuseStep 1840819 = 2761229) B2761229
theorem B1636035 : Blo 1636017 1636035 := bstep (se 1 (by rfl) ⟨1227026, by rfl⟩ : syracuseStep 1636035 = 2454053) B2454053
theorem B2455235 : Blo 1636017 2455235 := bstep (se 1 (by rfl) ⟨1841426, by rfl⟩ : syracuseStep 2455235 = 3682853) B3682853
theorem B1636051 : Blo 1636017 1636051 := bstep (se 1 (by rfl) ⟨1227038, by rfl⟩ : syracuseStep 1636051 = 2454077) B2454077
theorem B2455265 : Blo 1636017 2455265 := bstep (se 2 (by rfl) ⟨920724, by rfl⟩ : syracuseStep 2455265 = 1841449) B1841449
theorem B1636067 : Blo 1636017 1636067 := bstep (se 1 (by rfl) ⟨1227050, by rfl⟩ : syracuseStep 1636067 = 2454101) B2454101
theorem B5527277 : Blo 1636017 5527277 := bstep (se 3 (by rfl) ⟨1036364, by rfl⟩ : syracuseStep 5527277 = 2072729) B2072729
theorem B1636083 : Blo 1636017 1636083 := bstep (se 1 (by rfl) ⟨1227062, by rfl⟩ : syracuseStep 1636083 = 2454125) B2454125
theorem B2455283 : Blo 1636017 2455283 := bstep (se 1 (by rfl) ⟨1841462, by rfl⟩ : syracuseStep 2455283 = 3682925) B3682925
theorem B1636099 : Blo 1636017 1636099 := bstep (se 1 (by rfl) ⟨1227074, by rfl⟩ : syracuseStep 1636099 = 2454149) B2454149
theorem B2455313 : Blo 1636017 2455313 := bstep (se 2 (by rfl) ⟨920742, by rfl⟩ : syracuseStep 2455313 = 1841485) B1841485
theorem B3684113 : Blo 1636017 3684113 := bstep (se 2 (by rfl) ⟨1381542, by rfl⟩ : syracuseStep 3684113 = 2763085) B2763085
theorem B1636115 : Blo 1636017 1636115 := bstep (se 1 (by rfl) ⟨1227086, by rfl⟩ : syracuseStep 1636115 = 2454173) B2454173
theorem B1636131 : Blo 1636017 1636131 := bstep (se 1 (by rfl) ⟨1227098, by rfl⟩ : syracuseStep 1636131 = 2454197) B2454197
theorem B2455331 : Blo 1636017 2455331 := bstep (se 1 (by rfl) ⟨1841498, by rfl⟩ : syracuseStep 2455331 = 3682997) B3682997
theorem B3684131 : Blo 1636017 3684131 := bstep (se 1 (by rfl) ⟨2763098, by rfl⟩ : syracuseStep 3684131 = 5526197) B5526197
theorem B5527331 : Blo 1636017 5527331 := bstep (se 1 (by rfl) ⟨4145498, by rfl⟩ : syracuseStep 5527331 = 8290997) B8290997
theorem B4142897 : Blo 1636017 4142897 := bstep (se 2 (by rfl) ⟨1553586, by rfl⟩ : syracuseStep 4142897 = 3107173) B3107173
theorem B1636147 : Blo 1636017 1636147 := bstep (se 1 (by rfl) ⟨1227110, by rfl⟩ : syracuseStep 1636147 = 2454221) B2454221
theorem B2455361 : Blo 1636017 2455361 := bstep (se 2 (by rfl) ⟨920760, by rfl⟩ : syracuseStep 2455361 = 1841521) B1841521
theorem B1636163 : Blo 1636017 1636163 := bstep (se 1 (by rfl) ⟨1227122, by rfl⟩ : syracuseStep 1636163 = 2454245) B2454245
theorem B1840963 : Blo 1636017 1840963 := bstep (se 1 (by rfl) ⟨1380722, by rfl⟩ : syracuseStep 1840963 = 2761445) B2761445
theorem B1636179 : Blo 1636017 1636179 := bstep (se 1 (by rfl) ⟨1227134, by rfl⟩ : syracuseStep 1636179 = 2454269) B2454269
theorem B2455379 : Blo 1636017 2455379 := bstep (se 1 (by rfl) ⟨1841534, by rfl⟩ : syracuseStep 2455379 = 3683069) B3683069
theorem B1636195 : Blo 1636017 1636195 := bstep (se 1 (by rfl) ⟨1227146, by rfl⟩ : syracuseStep 1636195 = 2454293) B2454293
theorem B4142947 : Blo 1636017 4142947 := bstep (se 1 (by rfl) ⟨3107210, by rfl⟩ : syracuseStep 4142947 = 6214421) B6214421
theorem B2455409 : Blo 1636017 2455409 := bstep (se 2 (by rfl) ⟨920778, by rfl⟩ : syracuseStep 2455409 = 1841557) B1841557
theorem B1636211 : Blo 1636017 1636211 := bstep (se 1 (by rfl) ⟨1227158, by rfl⟩ : syracuseStep 1636211 = 2454317) B2454317
theorem B1636227 : Blo 1636017 1636227 := bstep (se 1 (by rfl) ⟨1227170, by rfl⟩ : syracuseStep 1636227 = 2454341) B2454341
theorem B2455427 : Blo 1636017 2455427 := bstep (se 1 (by rfl) ⟨1841570, by rfl⟩ : syracuseStep 2455427 = 3683141) B3683141
theorem B1636243 : Blo 1636017 1636243 := bstep (se 1 (by rfl) ⟨1227182, by rfl⟩ : syracuseStep 1636243 = 2454365) B2454365
theorem B2455457 : Blo 1636017 2455457 := bstep (se 2 (by rfl) ⟨920796, by rfl⟩ : syracuseStep 2455457 = 1841593) B1841593
theorem B1636259 : Blo 1636017 1636259 := bstep (se 1 (by rfl) ⟨1227194, by rfl⟩ : syracuseStep 1636259 = 2454389) B2454389
theorem B1636275 : Blo 1636017 1636275 := bstep (se 1 (by rfl) ⟨1227206, by rfl⟩ : syracuseStep 1636275 = 2454413) B2454413
theorem B2455475 : Blo 1636017 2455475 := bstep (se 1 (by rfl) ⟨1841606, by rfl⟩ : syracuseStep 2455475 = 3683213) B3683213
theorem B1636291 : Blo 1636017 1636291 := bstep (se 1 (by rfl) ⟨1227218, by rfl⟩ : syracuseStep 1636291 = 2454437) B2454437
theorem B2455505 : Blo 1636017 2455505 := bstep (se 2 (by rfl) ⟨920814, by rfl⟩ : syracuseStep 2455505 = 1841629) B1841629
theorem B1636307 : Blo 1636017 1636307 := bstep (se 1 (by rfl) ⟨1227230, by rfl⟩ : syracuseStep 1636307 = 2454461) B2454461
theorem B1841107 : Blo 1636017 1841107 := bstep (se 1 (by rfl) ⟨1380830, by rfl⟩ : syracuseStep 1841107 = 2761661) B2761661
theorem B1636323 : Blo 1636017 1636323 := bstep (se 1 (by rfl) ⟨1227242, by rfl⟩ : syracuseStep 1636323 = 2454485) B2454485
theorem B2455523 : Blo 1636017 2455523 := bstep (se 1 (by rfl) ⟨1841642, by rfl⟩ : syracuseStep 2455523 = 3683285) B3683285
theorem B4143089 : Blo 1636017 4143089 := bstep (se 2 (by rfl) ⟨1553658, by rfl⟩ : syracuseStep 4143089 = 3107317) B3107317
theorem B1636339 : Blo 1636017 1636339 := bstep (se 1 (by rfl) ⟨1227254, by rfl⟩ : syracuseStep 1636339 = 2454509) B2454509
theorem B2455553 : Blo 1636017 2455553 := bstep (se 2 (by rfl) ⟨920832, by rfl⟩ : syracuseStep 2455553 = 1841665) B1841665
theorem B1636355 : Blo 1636017 1636355 := bstep (se 1 (by rfl) ⟨1227266, by rfl⟩ : syracuseStep 1636355 = 2454533) B2454533
theorem B1636371 : Blo 1636017 1636371 := bstep (se 1 (by rfl) ⟨1227278, by rfl⟩ : syracuseStep 1636371 = 2454557) B2454557
theorem B2455571 : Blo 1636017 2455571 := bstep (se 1 (by rfl) ⟨1841678, by rfl⟩ : syracuseStep 2455571 = 3683357) B3683357
theorem B1636387 : Blo 1636017 1636387 := bstep (se 1 (by rfl) ⟨1227290, by rfl⟩ : syracuseStep 1636387 = 2454581) B2454581
theorem B4659245 : Blo 1636017 4659245 := bstep (se 3 (by rfl) ⟨873608, by rfl⟩ : syracuseStep 4659245 = 1747217) B1747217
theorem B2455601 : Blo 1636017 2455601 := bstep (se 2 (by rfl) ⟨920850, by rfl⟩ : syracuseStep 2455601 = 1841701) B1841701
theorem B3684401 : Blo 1636017 3684401 := bstep (se 2 (by rfl) ⟨1381650, by rfl⟩ : syracuseStep 3684401 = 2763301) B2763301
theorem B1636403 : Blo 1636017 1636403 := bstep (se 1 (by rfl) ⟨1227302, by rfl⟩ : syracuseStep 1636403 = 2454605) B2454605
theorem B5527601 : Blo 1636017 5527601 := bstep (se 2 (by rfl) ⟨2072850, by rfl⟩ : syracuseStep 5527601 = 4145701) B4145701
theorem B1636419 : Blo 1636017 1636419 := bstep (se 1 (by rfl) ⟨1227314, by rfl⟩ : syracuseStep 1636419 = 2454629) B2454629
theorem B2455619 : Blo 1636017 2455619 := bstep (se 1 (by rfl) ⟨1841714, by rfl⟩ : syracuseStep 2455619 = 3683429) B3683429
theorem B3684419 : Blo 1636017 3684419 := bstep (se 1 (by rfl) ⟨2763314, by rfl⟩ : syracuseStep 3684419 = 5526629) B5526629
theorem B1636435 : Blo 1636017 1636435 := bstep (se 1 (by rfl) ⟨1227326, by rfl⟩ : syracuseStep 1636435 = 2454653) B2454653
theorem B2455649 : Blo 1636017 2455649 := bstep (se 2 (by rfl) ⟨920868, by rfl⟩ : syracuseStep 2455649 = 1841737) B1841737
theorem B1636451 : Blo 1636017 1636451 := bstep (se 1 (by rfl) ⟨1227338, by rfl⟩ : syracuseStep 1636451 = 2454677) B2454677
theorem B1841251 : Blo 1636017 1841251 := bstep (se 1 (by rfl) ⟨1380938, by rfl⟩ : syracuseStep 1841251 = 2761877) B2761877
theorem B1636467 : Blo 1636017 1636467 := bstep (se 1 (by rfl) ⟨1227350, by rfl⟩ : syracuseStep 1636467 = 2454701) B2454701
theorem B2455667 : Blo 1636017 2455667 := bstep (se 1 (by rfl) ⟨1841750, by rfl⟩ : syracuseStep 2455667 = 3683501) B3683501
theorem B1636483 : Blo 1636017 1636483 := bstep (se 1 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 1636483 = 2454725) B2454725
theorem B2455697 : Blo 1636017 2455697 := bstep (se 2 (by rfl) ⟨920886, by rfl⟩ : syracuseStep 2455697 = 1841773) B1841773
theorem B1636499 : Blo 1636017 1636499 := bstep (se 1 (by rfl) ⟨1227374, by rfl⟩ : syracuseStep 1636499 = 2454749) B2454749
theorem B1636515 : Blo 1636017 1636515 := bstep (se 1 (by rfl) ⟨1227386, by rfl⟩ : syracuseStep 1636515 = 2454773) B2454773
theorem B2455715 : Blo 1636017 2455715 := bstep (se 1 (by rfl) ⟨1841786, by rfl⟩ : syracuseStep 2455715 = 3683573) B3683573
theorem B1636531 : Blo 1636017 1636531 := bstep (se 1 (by rfl) ⟨1227398, by rfl⟩ : syracuseStep 1636531 = 2454797) B2454797
theorem B2455745 : Blo 1636017 2455745 := bstep (se 2 (by rfl) ⟨920904, by rfl⟩ : syracuseStep 2455745 = 1841809) B1841809
theorem B1636547 : Blo 1636017 1636547 := bstep (se 1 (by rfl) ⟨1227410, by rfl⟩ : syracuseStep 1636547 = 2454821) B2454821
theorem B1636563 : Blo 1636017 1636563 := bstep (se 1 (by rfl) ⟨1227422, by rfl⟩ : syracuseStep 1636563 = 2454845) B2454845
theorem B2455763 : Blo 1636017 2455763 := bstep (se 1 (by rfl) ⟨1841822, by rfl⟩ : syracuseStep 2455763 = 3683645) B3683645
theorem B2799841 : Blo 1636017 2799841 := bstep (se 2 (by rfl) ⟨1049940, by rfl⟩ : syracuseStep 2799841 = 2099881) B2099881
theorem B1636579 : Blo 1636017 1636579 := bstep (se 1 (by rfl) ⟨1227434, by rfl⟩ : syracuseStep 1636579 = 2454869) B2454869
theorem B6994147 : Blo 1636017 6994147 := bstep (se 1 (by rfl) ⟨5245610, by rfl⟩ : syracuseStep 6994147 = 10491221) B10491221
theorem B2455793 : Blo 1636017 2455793 := bstep (se 2 (by rfl) ⟨920922, by rfl⟩ : syracuseStep 2455793 = 1841845) B1841845
theorem B1636595 : Blo 1636017 1636595 := bstep (se 1 (by rfl) ⟨1227446, by rfl⟩ : syracuseStep 1636595 = 2454893) B2454893
theorem B1841395 : Blo 1636017 1841395 := bstep (se 1 (by rfl) ⟨1381046, by rfl⟩ : syracuseStep 1841395 = 2762093) B2762093
theorem B1636611 : Blo 1636017 1636611 := bstep (se 1 (by rfl) ⟨1227458, by rfl⟩ : syracuseStep 1636611 = 2454917) B2454917
theorem B2455811 : Blo 1636017 2455811 := bstep (se 1 (by rfl) ⟨1841858, by rfl⟩ : syracuseStep 2455811 = 3683717) B3683717
theorem B5601539 : Blo 1636017 5601539 := bstep (se 1 (by rfl) ⟨4201154, by rfl⟩ : syracuseStep 5601539 = 8402309) B8402309
theorem B1636627 : Blo 1636017 1636627 := bstep (se 1 (by rfl) ⟨1227470, by rfl⟩ : syracuseStep 1636627 = 2454941) B2454941
theorem B2455841 : Blo 1636017 2455841 := bstep (se 2 (by rfl) ⟨920940, by rfl⟩ : syracuseStep 2455841 = 1841881) B1841881
theorem B1636643 : Blo 1636017 1636643 := bstep (se 1 (by rfl) ⟨1227482, by rfl⟩ : syracuseStep 1636643 = 2454965) B2454965
theorem B1636659 : Blo 1636017 1636659 := bstep (se 1 (by rfl) ⟨1227494, by rfl⟩ : syracuseStep 1636659 = 2454989) B2454989
theorem B2455859 : Blo 1636017 2455859 := bstep (se 1 (by rfl) ⟨1841894, by rfl⟩ : syracuseStep 2455859 = 3683789) B3683789
theorem B1636675 : Blo 1636017 1636675 := bstep (se 1 (by rfl) ⟨1227506, by rfl⟩ : syracuseStep 1636675 = 2455013) B2455013
theorem B2455889 : Blo 1636017 2455889 := bstep (se 2 (by rfl) ⟨920958, by rfl⟩ : syracuseStep 2455889 = 1841917) B1841917
theorem B3684689 : Blo 1636017 3684689 := bstep (se 2 (by rfl) ⟨1381758, by rfl⟩ : syracuseStep 3684689 = 2763517) B2763517
theorem B1636691 : Blo 1636017 1636691 := bstep (se 1 (by rfl) ⟨1227518, by rfl⟩ : syracuseStep 1636691 = 2455037) B2455037
theorem B1636707 : Blo 1636017 1636707 := bstep (se 1 (by rfl) ⟨1227530, by rfl⟩ : syracuseStep 1636707 = 2455061) B2455061
theorem B2455907 : Blo 1636017 2455907 := bstep (se 1 (by rfl) ⟨1841930, by rfl⟩ : syracuseStep 2455907 = 3683861) B3683861
theorem B3684707 : Blo 1636017 3684707 := bstep (se 1 (by rfl) ⟨2763530, by rfl⟩ : syracuseStep 3684707 = 5527061) B5527061
theorem B1636723 : Blo 1636017 1636723 := bstep (se 1 (by rfl) ⟨1227542, by rfl⟩ : syracuseStep 1636723 = 2455085) B2455085
theorem B12605809 : Blo 1636017 12605809 := bstep (se 2 (by rfl) ⟨4727178, by rfl⟩ : syracuseStep 12605809 = 9454357) B9454357
theorem B2455937 : Blo 1636017 2455937 := bstep (se 2 (by rfl) ⟨920976, by rfl⟩ : syracuseStep 2455937 = 1841953) B1841953
theorem B1636739 : Blo 1636017 1636739 := bstep (se 1 (by rfl) ⟨1227554, by rfl⟩ : syracuseStep 1636739 = 2455109) B2455109
theorem B1841539 : Blo 1636017 1841539 := bstep (se 1 (by rfl) ⟨1381154, by rfl⟩ : syracuseStep 1841539 = 2762309) B2762309
theorem B8853893 : Blo 1636017 8853893 := bstep (se 4 (by rfl) ⟨830052, by rfl⟩ : syracuseStep 8853893 = 1660105) B1660105
theorem B7862669 : Blo 1636017 7862669 := bstep (se 3 (by rfl) ⟨1474250, by rfl⟩ : syracuseStep 7862669 = 2948501) B2948501
theorem B1636755 : Blo 1636017 1636755 := bstep (se 1 (by rfl) ⟨1227566, by rfl⟩ : syracuseStep 1636755 = 2455133) B2455133
theorem B2455955 : Blo 1636017 2455955 := bstep (se 1 (by rfl) ⟨1841966, by rfl⟩ : syracuseStep 2455955 = 3683933) B3683933
theorem B2070947 : Blo 1636017 2070947 := bstep (se 1 (by rfl) ⟨1553210, by rfl⟩ : syracuseStep 2070947 = 3106421) B3106421
theorem B1636771 : Blo 1636017 1636771 := bstep (se 1 (by rfl) ⟨1227578, by rfl⟩ : syracuseStep 1636771 = 2455157) B2455157
theorem B2455985 : Blo 1636017 2455985 := bstep (se 2 (by rfl) ⟨920994, by rfl⟩ : syracuseStep 2455985 = 1841989) B1841989
theorem B7469489 : Blo 1636017 7469489 := bstep (se 2 (by rfl) ⟨2801058, by rfl⟩ : syracuseStep 7469489 = 5602117) B5602117
theorem B1636787 : Blo 1636017 1636787 := bstep (se 1 (by rfl) ⟨1227590, by rfl⟩ : syracuseStep 1636787 = 2455181) B2455181
theorem B1636803 : Blo 1636017 1636803 := bstep (se 1 (by rfl) ⟨1227602, by rfl⟩ : syracuseStep 1636803 = 2455205) B2455205
theorem B2456003 : Blo 1636017 2456003 := bstep (se 1 (by rfl) ⟨1842002, by rfl⟩ : syracuseStep 2456003 = 3684005) B3684005
theorem B1636819 : Blo 1636017 1636819 := bstep (se 1 (by rfl) ⟨1227614, by rfl⟩ : syracuseStep 1636819 = 2455229) B2455229
theorem B2456033 : Blo 1636017 2456033 := bstep (se 2 (by rfl) ⟨921012, by rfl⟩ : syracuseStep 2456033 = 1842025) B1842025
theorem B1636835 : Blo 1636017 1636835 := bstep (se 1 (by rfl) ⟨1227626, by rfl⟩ : syracuseStep 1636835 = 2455253) B2455253
theorem B1636851 : Blo 1636017 1636851 := bstep (se 1 (by rfl) ⟨1227638, by rfl⟩ : syracuseStep 1636851 = 2455277) B2455277
theorem B2456051 : Blo 1636017 2456051 := bstep (se 1 (by rfl) ⟨1842038, by rfl⟩ : syracuseStep 2456051 = 3684077) B3684077
theorem B1636867 : Blo 1636017 1636867 := bstep (se 1 (by rfl) ⟨1227650, by rfl⟩ : syracuseStep 1636867 = 2455301) B2455301
theorem B2456081 : Blo 1636017 2456081 := bstep (se 2 (by rfl) ⟨921030, by rfl⟩ : syracuseStep 2456081 = 1842061) B1842061
theorem B1636883 : Blo 1636017 1636883 := bstep (se 1 (by rfl) ⟨1227662, by rfl⟩ : syracuseStep 1636883 = 2455325) B2455325
theorem B1841683 : Blo 1636017 1841683 := bstep (se 1 (by rfl) ⟨1381262, by rfl⟩ : syracuseStep 1841683 = 2762525) B2762525
theorem B1636899 : Blo 1636017 1636899 := bstep (se 1 (by rfl) ⟨1227674, by rfl⟩ : syracuseStep 1636899 = 2455349) B2455349
theorem B2800163 : Blo 1636017 2800163 := bstep (se 1 (by rfl) ⟨2100122, by rfl⟩ : syracuseStep 2800163 = 4200245) B4200245
theorem B2456099 : Blo 1636017 2456099 := bstep (se 1 (by rfl) ⟨1842074, by rfl⟩ : syracuseStep 2456099 = 3684149) B3684149
theorem B4979245 : Blo 1636017 4979245 := bstep (se 3 (by rfl) ⟨933608, by rfl⟩ : syracuseStep 4979245 = 1867217) B1867217
theorem B1636915 : Blo 1636017 1636915 := bstep (se 1 (by rfl) ⟨1227686, by rfl⟩ : syracuseStep 1636915 = 2455373) B2455373
theorem B2456129 : Blo 1636017 2456129 := bstep (se 2 (by rfl) ⟨921048, by rfl⟩ : syracuseStep 2456129 = 1842097) B1842097
theorem B1636931 : Blo 1636017 1636931 := bstep (se 1 (by rfl) ⟨1227698, by rfl⟩ : syracuseStep 1636931 = 2455397) B2455397
theorem B5528141 : Blo 1636017 5528141 := bstep (se 3 (by rfl) ⟨1036526, by rfl⟩ : syracuseStep 5528141 = 2073053) B2073053
theorem B1636947 : Blo 1636017 1636947 := bstep (se 1 (by rfl) ⟨1227710, by rfl⟩ : syracuseStep 1636947 = 2455421) B2455421
theorem B2456147 : Blo 1636017 2456147 := bstep (se 1 (by rfl) ⟨1842110, by rfl⟩ : syracuseStep 2456147 = 3684221) B3684221
theorem B1636963 : Blo 1636017 1636963 := bstep (se 1 (by rfl) ⟨1227722, by rfl⟩ : syracuseStep 1636963 = 2455445) B2455445
theorem B2456177 : Blo 1636017 2456177 := bstep (se 2 (by rfl) ⟨921066, by rfl⟩ : syracuseStep 2456177 = 1842133) B1842133
theorem B3684977 : Blo 1636017 3684977 := bstep (se 2 (by rfl) ⟨1381866, by rfl⟩ : syracuseStep 3684977 = 2763733) B2763733
theorem B1636979 : Blo 1636017 1636979 := bstep (se 1 (by rfl) ⟨1227734, by rfl⟩ : syracuseStep 1636979 = 2455469) B2455469
theorem B1636995 : Blo 1636017 1636995 := bstep (se 1 (by rfl) ⟨1227746, by rfl⟩ : syracuseStep 1636995 = 2455493) B2455493
theorem B2456195 : Blo 1636017 2456195 := bstep (se 1 (by rfl) ⟨1842146, by rfl⟩ : syracuseStep 2456195 = 3684293) B3684293
theorem B3684995 : Blo 1636017 3684995 := bstep (se 1 (by rfl) ⟨2763746, by rfl⟩ : syracuseStep 3684995 = 5527493) B5527493
theorem B5528195 : Blo 1636017 5528195 := bstep (se 1 (by rfl) ⟨4146146, by rfl⟩ : syracuseStep 5528195 = 8292293) B8292293
theorem B1637011 : Blo 1636017 1637011 := bstep (se 1 (by rfl) ⟨1227758, by rfl⟩ : syracuseStep 1637011 = 2455517) B2455517
theorem B2456225 : Blo 1636017 2456225 := bstep (se 2 (by rfl) ⟨921084, by rfl⟩ : syracuseStep 2456225 = 1842169) B1842169
theorem B1637027 : Blo 1636017 1637027 := bstep (se 1 (by rfl) ⟨1227770, by rfl⟩ : syracuseStep 1637027 = 2455541) B2455541
theorem B1841827 : Blo 1636017 1841827 := bstep (se 1 (by rfl) ⟨1381370, by rfl⟩ : syracuseStep 1841827 = 2762741) B2762741
theorem B1637043 : Blo 1636017 1637043 := bstep (se 1 (by rfl) ⟨1227782, by rfl⟩ : syracuseStep 1637043 = 2455565) B2455565
theorem B2456243 : Blo 1636017 2456243 := bstep (se 1 (by rfl) ⟨1842182, by rfl⟩ : syracuseStep 2456243 = 3684365) B3684365
theorem B1637059 : Blo 1636017 1637059 := bstep (se 1 (by rfl) ⟨1227794, by rfl⟩ : syracuseStep 1637059 = 2455589) B2455589
theorem B2456273 : Blo 1636017 2456273 := bstep (se 2 (by rfl) ⟨921102, by rfl⟩ : syracuseStep 2456273 = 1842205) B1842205
theorem B1866451 : Blo 1636017 1866451 := bstep (se 1 (by rfl) ⟨1399838, by rfl⟩ : syracuseStep 1866451 = 2799677) B2799677
theorem B1637075 : Blo 1636017 1637075 := bstep (se 1 (by rfl) ⟨1227806, by rfl⟩ : syracuseStep 1637075 = 2455613) B2455613
theorem B1637091 : Blo 1636017 1637091 := bstep (se 1 (by rfl) ⟨1227818, by rfl⟩ : syracuseStep 1637091 = 2455637) B2455637
theorem B2456291 : Blo 1636017 2456291 := bstep (se 1 (by rfl) ⟨1842218, by rfl⟩ : syracuseStep 2456291 = 3684437) B3684437
theorem B1637107 : Blo 1636017 1637107 := bstep (se 1 (by rfl) ⟨1227830, by rfl⟩ : syracuseStep 1637107 = 2455661) B2455661
theorem B2456321 : Blo 1636017 2456321 := bstep (se 2 (by rfl) ⟨921120, by rfl⟩ : syracuseStep 2456321 = 1842241) B1842241
theorem B1637123 : Blo 1636017 1637123 := bstep (se 1 (by rfl) ⟨1227842, by rfl⟩ : syracuseStep 1637123 = 2455685) B2455685
theorem B1637139 : Blo 1636017 1637139 := bstep (se 1 (by rfl) ⟨1227854, by rfl⟩ : syracuseStep 1637139 = 2455709) B2455709
theorem B2456339 : Blo 1636017 2456339 := bstep (se 1 (by rfl) ⟨1842254, by rfl⟩ : syracuseStep 2456339 = 3684509) B3684509
theorem B1637155 : Blo 1636017 1637155 := bstep (se 1 (by rfl) ⟨1227866, by rfl⟩ : syracuseStep 1637155 = 2455733) B2455733
theorem B2456369 : Blo 1636017 2456369 := bstep (se 2 (by rfl) ⟨921138, by rfl⟩ : syracuseStep 2456369 = 1842277) B1842277
theorem B1637171 : Blo 1636017 1637171 := bstep (se 1 (by rfl) ⟨1227878, by rfl⟩ : syracuseStep 1637171 = 2455757) B2455757
theorem B1841971 : Blo 1636017 1841971 := bstep (se 1 (by rfl) ⟨1381478, by rfl⟩ : syracuseStep 1841971 = 2762957) B2762957
theorem B1637187 : Blo 1636017 1637187 := bstep (se 1 (by rfl) ⟨1227890, by rfl⟩ : syracuseStep 1637187 = 2455781) B2455781
theorem B2456387 : Blo 1636017 2456387 := bstep (se 1 (by rfl) ⟨1842290, by rfl⟩ : syracuseStep 2456387 = 3684581) B3684581
theorem B1637203 : Blo 1636017 1637203 := bstep (se 1 (by rfl) ⟨1227902, by rfl⟩ : syracuseStep 1637203 = 2455805) B2455805
theorem B2456417 : Blo 1636017 2456417 := bstep (se 2 (by rfl) ⟨921156, by rfl⟩ : syracuseStep 2456417 = 1842313) B1842313
theorem B1637219 : Blo 1636017 1637219 := bstep (se 1 (by rfl) ⟨1227914, by rfl⟩ : syracuseStep 1637219 = 2455829) B2455829
theorem B6216547 : Blo 1636017 6216547 := bstep (se 1 (by rfl) ⟨4662410, by rfl⟩ : syracuseStep 6216547 = 9324821) B9324821
theorem B1637235 : Blo 1636017 1637235 := bstep (se 1 (by rfl) ⟨1227926, by rfl⟩ : syracuseStep 1637235 = 2455853) B2455853
theorem B2456435 : Blo 1636017 2456435 := bstep (se 1 (by rfl) ⟨1842326, by rfl⟩ : syracuseStep 2456435 = 3684653) B3684653
theorem B1637251 : Blo 1636017 1637251 := bstep (se 1 (by rfl) ⟨1227938, by rfl⟩ : syracuseStep 1637251 = 2455877) B2455877
theorem B2456465 : Blo 1636017 2456465 := bstep (se 2 (by rfl) ⟨921174, by rfl⟩ : syracuseStep 2456465 = 1842349) B1842349
theorem B3685265 : Blo 1636017 3685265 := bstep (se 2 (by rfl) ⟨1381974, by rfl⟩ : syracuseStep 3685265 = 2763949) B2763949
theorem B1637267 : Blo 1636017 1637267 := bstep (se 1 (by rfl) ⟨1227950, by rfl⟩ : syracuseStep 1637267 = 2455901) B2455901
theorem B1637283 : Blo 1636017 1637283 := bstep (se 1 (by rfl) ⟨1227962, by rfl⟩ : syracuseStep 1637283 = 2455925) B2455925
theorem B2456483 : Blo 1636017 2456483 := bstep (se 1 (by rfl) ⟨1842362, by rfl⟩ : syracuseStep 2456483 = 3684725) B3684725
theorem B3685283 : Blo 1636017 3685283 := bstep (se 1 (by rfl) ⟨2763962, by rfl⟩ : syracuseStep 3685283 = 5527925) B5527925
theorem B1637299 : Blo 1636017 1637299 := bstep (se 1 (by rfl) ⟨1227974, by rfl⟩ : syracuseStep 1637299 = 2455949) B2455949
theorem B2456513 : Blo 1636017 2456513 := bstep (se 2 (by rfl) ⟨921192, by rfl⟩ : syracuseStep 2456513 = 1842385) B1842385
theorem B1637315 : Blo 1636017 1637315 := bstep (se 1 (by rfl) ⟨1227986, by rfl⟩ : syracuseStep 1637315 = 2455973) B2455973
theorem B1842115 : Blo 1636017 1842115 := bstep (se 1 (by rfl) ⟨1381586, by rfl⟩ : syracuseStep 1842115 = 2763173) B2763173
theorem B4144081 : Blo 1636017 4144081 := bstep (se 2 (by rfl) ⟨1554030, by rfl⟩ : syracuseStep 4144081 = 3108061) B3108061
theorem B1637331 : Blo 1636017 1637331 := bstep (se 1 (by rfl) ⟨1227998, by rfl⟩ : syracuseStep 1637331 = 2455997) B2455997
theorem B2456531 : Blo 1636017 2456531 := bstep (se 1 (by rfl) ⟨1842398, by rfl⟩ : syracuseStep 2456531 = 3684797) B3684797
theorem B1637347 : Blo 1636017 1637347 := bstep (se 1 (by rfl) ⟨1228010, by rfl⟩ : syracuseStep 1637347 = 2456021) B2456021
theorem B3496945 : Blo 1636017 3496945 := bstep (se 2 (by rfl) ⟨1311354, by rfl⟩ : syracuseStep 3496945 = 2622709) B2622709
theorem B2456561 : Blo 1636017 2456561 := bstep (se 2 (by rfl) ⟨921210, by rfl⟩ : syracuseStep 2456561 = 1842421) B1842421
theorem B1637363 : Blo 1636017 1637363 := bstep (se 1 (by rfl) ⟨1228022, by rfl⟩ : syracuseStep 1637363 = 2456045) B2456045
theorem B1637379 : Blo 1636017 1637379 := bstep (se 1 (by rfl) ⟨1228034, by rfl⟩ : syracuseStep 1637379 = 2456069) B2456069
theorem B2456579 : Blo 1636017 2456579 := bstep (se 1 (by rfl) ⟨1842434, by rfl⟩ : syracuseStep 2456579 = 3684869) B3684869
theorem B1637395 : Blo 1636017 1637395 := bstep (se 1 (by rfl) ⟨1228046, by rfl⟩ : syracuseStep 1637395 = 2456093) B2456093
theorem B1637411 : Blo 1636017 1637411 := bstep (se 1 (by rfl) ⟨1228058, by rfl⟩ : syracuseStep 1637411 = 2456117) B2456117
theorem B2456609 : Blo 1636017 2456609 := bstep (se 2 (by rfl) ⟨921228, by rfl⟩ : syracuseStep 2456609 = 1842457) B1842457
theorem B1637427 : Blo 1636017 1637427 := bstep (se 1 (by rfl) ⟨1228070, by rfl⟩ : syracuseStep 1637427 = 2456141) B2456141
theorem B2456627 : Blo 1636017 2456627 := bstep (se 1 (by rfl) ⟨1842470, by rfl⟩ : syracuseStep 2456627 = 3684941) B3684941
theorem B1637443 : Blo 1636017 1637443 := bstep (se 1 (by rfl) ⟨1228082, by rfl⟩ : syracuseStep 1637443 = 2456165) B2456165
theorem B2456657 : Blo 1636017 2456657 := bstep (se 2 (by rfl) ⟨921246, by rfl⟩ : syracuseStep 2456657 = 1842493) B1842493
theorem B1637459 : Blo 1636017 1637459 := bstep (se 1 (by rfl) ⟨1228094, by rfl⟩ : syracuseStep 1637459 = 2456189) B2456189
theorem B1842259 : Blo 1636017 1842259 := bstep (se 1 (by rfl) ⟨1381694, by rfl⟩ : syracuseStep 1842259 = 2763389) B2763389
theorem B2071651 : Blo 1636017 2071651 := bstep (se 1 (by rfl) ⟨1553738, by rfl⟩ : syracuseStep 2071651 = 3107477) B3107477
theorem B1637475 : Blo 1636017 1637475 := bstep (se 1 (by rfl) ⟨1228106, by rfl⟩ : syracuseStep 1637475 = 2456213) B2456213
theorem B2456675 : Blo 1636017 2456675 := bstep (se 1 (by rfl) ⟨1842506, by rfl⟩ : syracuseStep 2456675 = 3685013) B3685013
theorem B19922033 : Blo 1636017 19922033 := bstep (se 2 (by rfl) ⟨7470762, by rfl⟩ : syracuseStep 19922033 = 14941525) B14941525
theorem B1637491 : Blo 1636017 1637491 := bstep (se 1 (by rfl) ⟨1228118, by rfl⟩ : syracuseStep 1637491 = 2456237) B2456237
theorem B2456705 : Blo 1636017 2456705 := bstep (se 2 (by rfl) ⟨921264, by rfl⟩ : syracuseStep 2456705 = 1842529) B1842529
theorem B1637507 : Blo 1636017 1637507 := bstep (se 1 (by rfl) ⟨1228130, by rfl⟩ : syracuseStep 1637507 = 2456261) B2456261
theorem B1637523 : Blo 1636017 1637523 := bstep (se 1 (by rfl) ⟨1228142, by rfl⟩ : syracuseStep 1637523 = 2456285) B2456285
theorem B2456723 : Blo 1636017 2456723 := bstep (se 1 (by rfl) ⟨1842542, by rfl⟩ : syracuseStep 2456723 = 3685085) B3685085
theorem B1637539 : Blo 1636017 1637539 := bstep (se 1 (by rfl) ⟨1228154, by rfl⟩ : syracuseStep 1637539 = 2456309) B2456309
theorem B4201649 : Blo 1636017 4201649 := bstep (se 2 (by rfl) ⟨1575618, by rfl⟩ : syracuseStep 4201649 = 3151237) B3151237
theorem B2456753 : Blo 1636017 2456753 := bstep (se 2 (by rfl) ⟨921282, by rfl⟩ : syracuseStep 2456753 = 1842565) B1842565
theorem B1637555 : Blo 1636017 1637555 := bstep (se 1 (by rfl) ⟨1228166, by rfl⟩ : syracuseStep 1637555 = 2456333) B2456333
theorem B2071747 : Blo 1636017 2071747 := bstep (se 1 (by rfl) ⟨1553810, by rfl⟩ : syracuseStep 2071747 = 3107621) B3107621
theorem B1637571 : Blo 1636017 1637571 := bstep (se 1 (by rfl) ⟨1228178, by rfl⟩ : syracuseStep 1637571 = 2456357) B2456357
theorem B2456771 : Blo 1636017 2456771 := bstep (se 1 (by rfl) ⟨1842578, by rfl⟩ : syracuseStep 2456771 = 3685157) B3685157
theorem B4660429 : Blo 1636017 4660429 := bstep (se 3 (by rfl) ⟨873830, by rfl⟩ : syracuseStep 4660429 = 1747661) B1747661
theorem B1637587 : Blo 1636017 1637587 := bstep (se 1 (by rfl) ⟨1228190, by rfl⟩ : syracuseStep 1637587 = 2456381) B2456381
theorem B2456801 : Blo 1636017 2456801 := bstep (se 2 (by rfl) ⟨921300, by rfl⟩ : syracuseStep 2456801 = 1842601) B1842601
theorem B4144355 : Blo 1636017 4144355 := bstep (se 1 (by rfl) ⟨3108266, by rfl⟩ : syracuseStep 4144355 = 6216533) B6216533
theorem B1637603 : Blo 1636017 1637603 := bstep (se 1 (by rfl) ⟨1228202, by rfl⟩ : syracuseStep 1637603 = 2456405) B2456405
theorem B1842403 : Blo 1636017 1842403 := bstep (se 1 (by rfl) ⟨1381802, by rfl⟩ : syracuseStep 1842403 = 2763605) B2763605
theorem B2522353 : Blo 1636017 2522353 := bstep (se 2 (by rfl) ⟨945882, by rfl⟩ : syracuseStep 2522353 = 1891765) B1891765
theorem B1637619 : Blo 1636017 1637619 := bstep (se 1 (by rfl) ⟨1228214, by rfl⟩ : syracuseStep 1637619 = 2456429) B2456429
theorem B2456819 : Blo 1636017 2456819 := bstep (se 1 (by rfl) ⟨1842614, by rfl⟩ : syracuseStep 2456819 = 3685229) B3685229
theorem B1637635 : Blo 1636017 1637635 := bstep (se 1 (by rfl) ⟨1228226, by rfl⟩ : syracuseStep 1637635 = 2456453) B2456453
theorem B2456849 : Blo 1636017 2456849 := bstep (se 2 (by rfl) ⟨921318, by rfl⟩ : syracuseStep 2456849 = 1842637) B1842637
theorem B1637651 : Blo 1636017 1637651 := bstep (se 1 (by rfl) ⟨1228238, by rfl⟩ : syracuseStep 1637651 = 2456477) B2456477
theorem B1637667 : Blo 1636017 1637667 := bstep (se 1 (by rfl) ⟨1228250, by rfl⟩ : syracuseStep 1637667 = 2456501) B2456501
theorem B2456867 : Blo 1636017 2456867 := bstep (se 1 (by rfl) ⟨1842650, by rfl⟩ : syracuseStep 2456867 = 3685301) B3685301
theorem B1637683 : Blo 1636017 1637683 := bstep (se 1 (by rfl) ⟨1228262, by rfl⟩ : syracuseStep 1637683 = 2456525) B2456525
theorem B2456897 : Blo 1636017 2456897 := bstep (se 2 (by rfl) ⟨921336, by rfl⟩ : syracuseStep 2456897 = 1842673) B1842673
theorem B1637699 : Blo 1636017 1637699 := bstep (se 1 (by rfl) ⟨1228274, by rfl⟩ : syracuseStep 1637699 = 2456549) B2456549
theorem B1637715 : Blo 1636017 1637715 := bstep (se 1 (by rfl) ⟨1228286, by rfl⟩ : syracuseStep 1637715 = 2456573) B2456573
theorem B2456915 : Blo 1636017 2456915 := bstep (se 1 (by rfl) ⟨1842686, by rfl⟩ : syracuseStep 2456915 = 3685373) B3685373
theorem B5979491 : Blo 1636017 5979491 := bstep (se 1 (by rfl) ⟨4484618, by rfl⟩ : syracuseStep 5979491 = 8969237) B8969237
theorem B1637731 : Blo 1636017 1637731 := bstep (se 1 (by rfl) ⟨1228298, by rfl⟩ : syracuseStep 1637731 = 2456597) B2456597
theorem B2456945 : Blo 1636017 2456945 := bstep (se 2 (by rfl) ⟨921354, by rfl⟩ : syracuseStep 2456945 = 1842709) B1842709
theorem B1637747 : Blo 1636017 1637747 := bstep (se 1 (by rfl) ⟨1228310, by rfl⟩ : syracuseStep 1637747 = 2456621) B2456621
theorem B1842547 : Blo 1636017 1842547 := bstep (se 1 (by rfl) ⟨1381910, by rfl⟩ : syracuseStep 1842547 = 2763821) B2763821
theorem B3497347 : Blo 1636017 3497347 := bstep (se 1 (by rfl) ⟨2623010, by rfl⟩ : syracuseStep 3497347 = 5246021) B5246021
theorem B1637763 : Blo 1636017 1637763 := bstep (se 1 (by rfl) ⟨1228322, by rfl⟩ : syracuseStep 1637763 = 2456645) B2456645
theorem B2456963 : Blo 1636017 2456963 := bstep (se 1 (by rfl) ⟨1842722, by rfl⟩ : syracuseStep 2456963 = 3685445) B3685445
theorem B1637779 : Blo 1636017 1637779 := bstep (se 1 (by rfl) ⟨1228334, by rfl⟩ : syracuseStep 1637779 = 2456669) B2456669
theorem B2456993 : Blo 1636017 2456993 := bstep (se 2 (by rfl) ⟨921372, by rfl⟩ : syracuseStep 2456993 = 1842745) B1842745
theorem B1965475 : Blo 1636017 1965475 := bstep (se 1 (by rfl) ⟨1474106, by rfl⟩ : syracuseStep 1965475 = 2948213) B2948213
theorem B4144547 : Blo 1636017 4144547 := bstep (se 1 (by rfl) ⟨3108410, by rfl⟩ : syracuseStep 4144547 = 6216821) B6216821
theorem B10493347 : Blo 1636017 10493347 := bstep (se 1 (by rfl) ⟨7870010, by rfl⟩ : syracuseStep 10493347 = 15740021) B15740021
theorem B1637795 : Blo 1636017 1637795 := bstep (se 1 (by rfl) ⟨1228346, by rfl⟩ : syracuseStep 1637795 = 2456693) B2456693
theorem B9321905 : Blo 1636017 9321905 := bstep (se 2 (by rfl) ⟨3495714, by rfl⟩ : syracuseStep 9321905 = 6991429) B6991429
theorem B1637811 : Blo 1636017 1637811 := bstep (se 1 (by rfl) ⟨1228358, by rfl⟩ : syracuseStep 1637811 = 2456717) B2456717
theorem B2457011 : Blo 1636017 2457011 := bstep (se 1 (by rfl) ⟨1842758, by rfl⟩ : syracuseStep 2457011 = 3685517) B3685517
theorem B1637827 : Blo 1636017 1637827 := bstep (se 1 (by rfl) ⟨1228370, by rfl⟩ : syracuseStep 1637827 = 2456741) B2456741
theorem B10485197 : Blo 1636017 10485197 := bstep (se 3 (by rfl) ⟨1965974, by rfl⟩ : syracuseStep 10485197 = 3931949) B3931949
theorem B1637843 : Blo 1636017 1637843 := bstep (se 1 (by rfl) ⟨1228382, by rfl⟩ : syracuseStep 1637843 = 2456765) B2456765
theorem B5979619 : Blo 1636017 5979619 := bstep (se 1 (by rfl) ⟨4484714, by rfl⟩ : syracuseStep 5979619 = 8969429) B8969429
theorem B1637859 : Blo 1636017 1637859 := bstep (se 1 (by rfl) ⟨1228394, by rfl⟩ : syracuseStep 1637859 = 2456789) B2456789
theorem B1637875 : Blo 1636017 1637875 := bstep (se 1 (by rfl) ⟨1228406, by rfl⟩ : syracuseStep 1637875 = 2456813) B2456813
theorem B1637891 : Blo 1636017 1637891 := bstep (se 1 (by rfl) ⟨1228418, by rfl⟩ : syracuseStep 1637891 = 2456837) B2456837
theorem B1842691 : Blo 1636017 1842691 := bstep (se 1 (by rfl) ⟨1382018, by rfl⟩ : syracuseStep 1842691 = 2764037) B2764037
theorem B1637907 : Blo 1636017 1637907 := bstep (se 1 (by rfl) ⟨1228430, by rfl⟩ : syracuseStep 1637907 = 2456861) B2456861
theorem B1637923 : Blo 1636017 1637923 := bstep (se 1 (by rfl) ⟨1228442, by rfl⟩ : syracuseStep 1637923 = 2456885) B2456885
theorem B1637939 : Blo 1636017 1637939 := bstep (se 1 (by rfl) ⟨1228454, by rfl⟩ : syracuseStep 1637939 = 2456909) B2456909
theorem B1637955 : Blo 1636017 1637955 := bstep (se 1 (by rfl) ⟨1228466, by rfl⟩ : syracuseStep 1637955 = 2456933) B2456933
theorem B5242445 : Blo 1636017 5242445 := bstep (se 3 (by rfl) ⟨982958, by rfl⟩ : syracuseStep 5242445 = 1965917) B1965917
theorem B1637971 : Blo 1636017 1637971 := bstep (se 1 (by rfl) ⟨1228478, by rfl⟩ : syracuseStep 1637971 = 2456957) B2456957
theorem B1637987 : Blo 1636017 1637987 := bstep (se 1 (by rfl) ⟨1228490, by rfl⟩ : syracuseStep 1637987 = 2456981) B2456981
theorem B1638003 : Blo 1636017 1638003 := bstep (se 1 (by rfl) ⟨1228502, by rfl⟩ : syracuseStep 1638003 = 2457005) B2457005
theorem B3784369 : Blo 1636017 3784369 := bstep (se 2 (by rfl) ⟨1419138, by rfl⟩ : syracuseStep 3784369 = 2838277) B2838277
theorem B2072243 : Blo 1636017 2072243 := bstep (se 1 (by rfl) ⟨1554182, by rfl⟩ : syracuseStep 2072243 = 3108365) B3108365
theorem B1965763 : Blo 1636017 1965763 := bstep (se 1 (by rfl) ⟨1474322, by rfl⟩ : syracuseStep 1965763 = 2948645) B2948645
theorem B5242573 : Blo 1636017 5242573 := bstep (se 3 (by rfl) ⟨982982, by rfl⟩ : syracuseStep 5242573 = 1965965) B1965965
theorem B5390051 : Blo 1636017 5390051 := bstep (se 1 (by rfl) ⟨4042538, by rfl⟩ : syracuseStep 5390051 = 8085077) B8085077
theorem B2621171 : Blo 1636017 2621171 := bstep (se 1 (by rfl) ⟨1965878, by rfl⟩ : syracuseStep 2621171 = 3931757) B3931757
theorem B11198321 : Blo 1636017 11198321 := bstep (se 2 (by rfl) ⟨4199370, by rfl⟩ : syracuseStep 11198321 = 8398741) B8398741
theorem B5603185 : Blo 1636017 5603185 := bstep (se 2 (by rfl) ⟨2101194, by rfl⟩ : syracuseStep 5603185 = 4202389) B4202389
theorem B31449059 : Blo 1636017 31449059 := bstep (se 1 (by rfl) ⟨23586794, by rfl⟩ : syracuseStep 31449059 = 47173589) B47173589
theorem B8290349 : Blo 1636017 8290349 := bstep (se 3 (by rfl) ⟨1554440, by rfl⟩ : syracuseStep 8290349 = 3108881) B3108881
theorem B6217793 : Blo 1636017 6217793 := bstep (se 2 (by rfl) ⟨2331672, by rfl⟩ : syracuseStep 6217793 = 4663345) B4663345
theorem B5898329 : Blo 1636017 5898329 := bstep (se 2 (by rfl) ⟨2211873, by rfl⟩ : syracuseStep 5898329 = 4423747) B4423747
theorem B5243059 : Blo 1636017 5243059 := bstep (se 1 (by rfl) ⟨3932294, by rfl⟩ : syracuseStep 5243059 = 7864589) B7864589
theorem B3932363 : Blo 1636017 3932363 := bstep (se 1 (by rfl) ⟨2949272, by rfl⟩ : syracuseStep 3932363 = 5898545) B5898545
theorem B8847577 : Blo 1636017 8847577 := bstep (se 2 (by rfl) ⟨3317841, by rfl⟩ : syracuseStep 8847577 = 6635683) B6635683
theorem B2212057 : Blo 1636017 2212057 := bstep (se 2 (by rfl) ⟨829521, by rfl⟩ : syracuseStep 2212057 = 1659043) B1659043
theorem B17268997 : Blo 1636017 17268997 := bstep (se 4 (by rfl) ⟨1618968, by rfl⟩ : syracuseStep 17268997 = 3237937) B3237937
theorem B19923205 : Blo 1636017 19923205 := bstep (se 4 (by rfl) ⟨1867800, by rfl⟩ : syracuseStep 19923205 = 3735601) B3735601
theorem B5521715 : Blo 1636017 5521715 := bstep (se 1 (by rfl) ⟨4141286, by rfl⟩ : syracuseStep 5521715 = 8282573) B8282573
theorem B3498329 : Blo 1636017 3498329 := bstep (se 2 (by rfl) ⟨1311873, by rfl⟩ : syracuseStep 3498329 = 2623747) B2623747
theorem B2761175 : Blo 1636017 2761175 := bstep (se 1 (by rfl) ⟨2070881, by rfl⟩ : syracuseStep 2761175 = 4141763) B4141763
theorem B5521985 : Blo 1636017 5521985 := bstep (se 2 (by rfl) ⟨2070744, by rfl⟩ : syracuseStep 5521985 = 4141489) B4141489
theorem B7864897 : Blo 1636017 7864897 := bstep (se 2 (by rfl) ⟨2949336, by rfl⟩ : syracuseStep 7864897 = 5898673) B5898673
theorem B25215563 : Blo 1636017 25215563 := bstep (se 1 (by rfl) ⟨18911672, by rfl⟩ : syracuseStep 25215563 = 37823345) B37823345
theorem B2761303 : Blo 1636017 2761303 := bstep (se 1 (by rfl) ⟨2070977, by rfl⟩ : syracuseStep 2761303 = 4141955) B4141955
theorem B4145843 : Blo 1636017 4145843 := bstep (se 1 (by rfl) ⟨3109382, by rfl⟩ : syracuseStep 4145843 = 6218765) B6218765
theorem B8282897 : Blo 1636017 8282897 := bstep (se 2 (by rfl) ⟨3106086, by rfl⟩ : syracuseStep 8282897 = 6212173) B6212173
theorem B2949913 : Blo 1636017 2949913 := bstep (se 2 (by rfl) ⟨1106217, by rfl⟩ : syracuseStep 2949913 = 2212435) B2212435
theorem B18637613 : Blo 1636017 18637613 := bstep (se 3 (by rfl) ⟨3494552, by rfl⟩ : syracuseStep 18637613 = 6989105) B6989105
theorem B8283059 : Blo 1636017 8283059 := bstep (se 1 (by rfl) ⟨6212294, by rfl⟩ : syracuseStep 8283059 = 12424589) B12424589
theorem B1967051 : Blo 1636017 1967051 := bstep (se 1 (by rfl) ⟨1475288, by rfl⟩ : syracuseStep 1967051 = 2950577) B2950577
theorem B4146137 : Blo 1636017 4146137 := bstep (se 2 (by rfl) ⟨1554801, by rfl⟩ : syracuseStep 4146137 = 3109603) B3109603
theorem B5522525 : Blo 1636017 5522525 := bstep (se 3 (by rfl) ⟨1035473, by rfl⟩ : syracuseStep 5522525 = 2070947) B2070947
theorem B2761931 : Blo 1636017 2761931 := bstep (se 1 (by rfl) ⟨2071448, by rfl⟩ : syracuseStep 2761931 = 4142897) B4142897
theorem B4662593 : Blo 1636017 4662593 := bstep (se 2 (by rfl) ⟨1748472, by rfl⟩ : syracuseStep 4662593 = 3496945) B3496945
theorem B2762059 : Blo 1636017 2762059 := bstep (se 1 (by rfl) ⟨2071544, by rfl⟩ : syracuseStep 2762059 = 4143089) B4143089
theorem B3106163 : Blo 1636017 3106163 := bstep (se 1 (by rfl) ⟨2329622, by rfl⟩ : syracuseStep 3106163 = 4659245) B4659245
theorem B3106201 : Blo 1636017 3106201 := bstep (se 2 (by rfl) ⟨1164825, by rfl⟩ : syracuseStep 3106201 = 2329651) B2329651
theorem B2762201 : Blo 1636017 2762201 := bstep (se 2 (by rfl) ⟨1035825, by rfl⟩ : syracuseStep 2762201 = 2071651) B2071651
theorem B6219281 : Blo 1636017 6219281 := bstep (se 2 (by rfl) ⟨2332230, by rfl⟩ : syracuseStep 6219281 = 4664461) B4664461
theorem B2762329 : Blo 1636017 2762329 := bstep (se 2 (by rfl) ⟨1035873, by rfl⟩ : syracuseStep 2762329 = 2071747) B2071747
theorem B3106649 : Blo 1636017 3106649 := bstep (se 2 (by rfl) ⟨1164993, by rfl⟩ : syracuseStep 3106649 = 2329987) B2329987
theorem B4663129 : Blo 1636017 4663129 := bstep (se 2 (by rfl) ⟨1748673, by rfl⟩ : syracuseStep 4663129 = 3497347) B3497347
theorem B7972825 : Blo 1636017 7972825 := bstep (se 2 (by rfl) ⟨2989809, by rfl⟩ : syracuseStep 7972825 = 5979619) B5979619
theorem B6989789 : Blo 1636017 6989789 := bstep (se 3 (by rfl) ⟨1310585, by rfl⟩ : syracuseStep 6989789 = 2621171) B2621171
theorem B13281355 : Blo 1636017 13281355 := bstep (se 1 (by rfl) ⟨9961016, by rfl⟩ : syracuseStep 13281355 = 19922033) B19922033
theorem B2762903 : Blo 1636017 2762903 := bstep (se 1 (by rfl) ⟨2072177, by rfl⟩ : syracuseStep 2762903 = 4144355) B4144355
theorem B5523659 : Blo 1636017 5523659 := bstep (se 1 (by rfl) ⟨4142744, by rfl⟩ : syracuseStep 5523659 = 8285489) B8285489
theorem B6990097 : Blo 1636017 6990097 := bstep (se 2 (by rfl) ⟨2621286, by rfl⟩ : syracuseStep 6990097 = 5242573) B5242573
theorem B2763031 : Blo 1636017 2763031 := bstep (se 1 (by rfl) ⟨2072273, by rfl⟩ : syracuseStep 2763031 = 4144547) B4144547
theorem B6990131 : Blo 1636017 6990131 := bstep (se 1 (by rfl) ⟨5242598, by rfl⟩ : syracuseStep 6990131 = 10485197) B10485197
theorem B6211991 : Blo 1636017 6211991 := bstep (se 1 (by rfl) ⟨4658993, by rfl⟩ : syracuseStep 6211991 = 9317987) B9317987
theorem B13978007 : Blo 1636017 13978007 := bstep (se 1 (by rfl) ⟨10483505, by rfl⟩ : syracuseStep 13978007 = 20967011) B20967011
theorem B5523929 : Blo 1636017 5523929 := bstep (se 2 (by rfl) ⟨2071473, by rfl⟩ : syracuseStep 5523929 = 4142947) B4142947
theorem B3107393 : Blo 1636017 3107393 := bstep (se 2 (by rfl) ⟨1165272, by rfl⟩ : syracuseStep 3107393 = 2330545) B2330545
theorem B7465547 : Blo 1636017 7465547 := bstep (se 1 (by rfl) ⟨5599160, by rfl⟩ : syracuseStep 7465547 = 11198321) B11198321
theorem B7866973 : Blo 1636017 7866973 := bstep (se 3 (by rfl) ⟨1475057, by rfl⟩ : syracuseStep 7866973 = 2950115) B2950115
theorem B3148403 : Blo 1636017 3148403 := bstep (se 1 (by rfl) ⟨2361302, by rfl⟩ : syracuseStep 3148403 = 4722605) B4722605
theorem B20966039 : Blo 1636017 20966039 := bstep (se 1 (by rfl) ⟨15724529, by rfl⟩ : syracuseStep 20966039 = 31449059) B31449059
theorem B2837207 : Blo 1636017 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B3681089 : Blo 1636017 3681089 := bstep (se 2 (by rfl) ⟨1380408, by rfl⟩ : syracuseStep 3681089 = 2760817) B2760817
theorem B8285003 : Blo 1636017 8285003 := bstep (se 1 (by rfl) ⟨6213752, by rfl⟩ : syracuseStep 8285003 = 12427505) B12427505
theorem B3107659 : Blo 1636017 3107659 := bstep (se 1 (by rfl) ⟨2330744, by rfl⟩ : syracuseStep 3107659 = 4661489) B4661489
theorem B612731789 : Blo 1636017 612731789 := bstep (se 3 (by rfl) ⟨114887210, by rfl⟩ : syracuseStep 612731789 = 229774421) B229774421
theorem B2763659 : Blo 1636017 2763659 := bstep (se 1 (by rfl) ⟨2072744, by rfl⟩ : syracuseStep 2763659 = 4145489) B4145489
theorem B6384529 : Blo 1636017 6384529 := bstep (se 2 (by rfl) ⟨2394198, by rfl⟩ : syracuseStep 6384529 = 4788397) B4788397
theorem B6302657 : Blo 1636017 6302657 := bstep (se 2 (by rfl) ⟨2363496, by rfl⟩ : syracuseStep 6302657 = 4726993) B4726993
theorem B1993675 : Blo 1636017 1993675 := bstep (se 1 (by rfl) ⟨1495256, by rfl⟩ : syracuseStep 1993675 = 2990513) B2990513
theorem B9325529 : Blo 1636017 9325529 := bstep (se 2 (by rfl) ⟨3497073, by rfl⟩ : syracuseStep 9325529 = 6994147) B6994147
theorem B2763787 : Blo 1636017 2763787 := bstep (se 1 (by rfl) ⟨2072840, by rfl⟩ : syracuseStep 2763787 = 4145681) B4145681
theorem B3681305 : Blo 1636017 3681305 := bstep (se 2 (by rfl) ⟨1380489, by rfl⟩ : syracuseStep 3681305 = 2760979) B2760979
theorem B14928941 : Blo 1636017 14928941 := bstep (se 3 (by rfl) ⟨2799176, by rfl⟩ : syracuseStep 14928941 = 5598353) B5598353
theorem B6212659 : Blo 1636017 6212659 := bstep (se 1 (by rfl) ⟨4659494, by rfl⟩ : syracuseStep 6212659 = 9318989) B9318989
theorem B3681395 : Blo 1636017 3681395 := bstep (se 1 (by rfl) ⟨2761046, by rfl⟩ : syracuseStep 3681395 = 5522093) B5522093
theorem B17697923 : Blo 1636017 17697923 := bstep (se 1 (by rfl) ⟨13273442, by rfl⟩ : syracuseStep 17697923 = 26546885) B26546885
theorem B5901443 : Blo 1636017 5901443 := bstep (se 1 (by rfl) ⟨4426082, by rfl⟩ : syracuseStep 5901443 = 8852165) B8852165
theorem B3681431 : Blo 1636017 3681431 := bstep (se 1 (by rfl) ⟨2761073, by rfl⟩ : syracuseStep 3681431 = 5522147) B5522147
theorem B5524631 : Blo 1636017 5524631 := bstep (se 1 (by rfl) ⟨4143473, by rfl⟩ : syracuseStep 5524631 = 8286947) B8286947
theorem B2763929 : Blo 1636017 2763929 := bstep (se 2 (by rfl) ⟨1036473, by rfl⟩ : syracuseStep 2763929 = 2072947) B2072947
theorem B3108107 : Blo 1636017 3108107 := bstep (se 1 (by rfl) ⟨2331080, by rfl⟩ : syracuseStep 3108107 = 4662161) B4662161
theorem B2329879 : Blo 1636017 2329879 := bstep (se 1 (by rfl) ⟨1747409, by rfl⟩ : syracuseStep 2329879 = 3494819) B3494819
theorem B2764057 : Blo 1636017 2764057 := bstep (se 2 (by rfl) ⟨1036521, by rfl⟩ : syracuseStep 2764057 = 2073043) B2073043
theorem B3681611 : Blo 1636017 3681611 := bstep (se 1 (by rfl) ⟨2761208, by rfl⟩ : syracuseStep 3681611 = 5522417) B5522417
theorem B14937437 : Blo 1636017 14937437 := bstep (se 3 (by rfl) ⟨2800769, by rfl⟩ : syracuseStep 14937437 = 5601539) B5601539
theorem B3681665 : Blo 1636017 3681665 := bstep (se 2 (by rfl) ⟨1380624, by rfl⟩ : syracuseStep 3681665 = 2761249) B2761249
theorem B6638993 : Blo 1636017 6638993 := bstep (se 2 (by rfl) ⟨2489622, by rfl⟩ : syracuseStep 6638993 = 4979245) B4979245
theorem B3108289 : Blo 1636017 3108289 := bstep (se 2 (by rfl) ⟨1165608, by rfl⟩ : syracuseStep 3108289 = 2331217) B2331217
theorem B1748503 : Blo 1636017 1748503 := bstep (se 1 (by rfl) ⟨1311377, by rfl⟩ : syracuseStep 1748503 = 2622755) B2622755
theorem B3681881 : Blo 1636017 3681881 := bstep (se 2 (by rfl) ⟨1380705, by rfl⟩ : syracuseStep 3681881 = 2761411) B2761411
theorem B2305675 : Blo 1636017 2305675 := bstep (se 1 (by rfl) ⟨1729256, by rfl⟩ : syracuseStep 2305675 = 3458513) B3458513
theorem B13987505 : Blo 1636017 13987505 := bstep (se 2 (by rfl) ⟨5245314, by rfl⟩ : syracuseStep 13987505 = 10490629) B10490629
theorem B3681971 : Blo 1636017 3681971 := bstep (se 1 (by rfl) ⟨2761478, by rfl⟩ : syracuseStep 3681971 = 5522957) B5522957
theorem B5525171 : Blo 1636017 5525171 := bstep (se 1 (by rfl) ⟨4143878, by rfl⟩ : syracuseStep 5525171 = 8287757) B8287757
theorem B8851123 : Blo 1636017 8851123 := bstep (se 1 (by rfl) ⟨6638342, by rfl⟩ : syracuseStep 8851123 = 13276685) B13276685
theorem B3682007 : Blo 1636017 3682007 := bstep (se 1 (by rfl) ⟨2761505, by rfl⟩ : syracuseStep 3682007 = 5523011) B5523011
theorem B3108631 : Blo 1636017 3108631 := bstep (se 1 (by rfl) ⟨2331473, by rfl⟩ : syracuseStep 3108631 = 4662947) B4662947
theorem B3682187 : Blo 1636017 3682187 := bstep (se 1 (by rfl) ⟨2761640, by rfl⟩ : syracuseStep 3682187 = 5523281) B5523281
theorem B7466897 : Blo 1636017 7466897 := bstep (se 2 (by rfl) ⟨2800086, by rfl⟩ : syracuseStep 7466897 = 5600173) B5600173
theorem B3682241 : Blo 1636017 3682241 := bstep (se 2 (by rfl) ⟨1380840, by rfl⟩ : syracuseStep 3682241 = 2761681) B2761681
theorem B5525441 : Blo 1636017 5525441 := bstep (se 2 (by rfl) ⟨2072040, by rfl⟩ : syracuseStep 5525441 = 4144081) B4144081
theorem B3108851 : Blo 1636017 3108851 := bstep (se 1 (by rfl) ⟨2331638, by rfl⟩ : syracuseStep 3108851 = 4663277) B4663277
theorem B3682457 : Blo 1636017 3682457 := bstep (se 2 (by rfl) ⟨1380921, by rfl⟩ : syracuseStep 3682457 = 2761843) B2761843
theorem B6992045 : Blo 1636017 6992045 := bstep (se 3 (by rfl) ⟨1311008, by rfl⟩ : syracuseStep 6992045 = 2622017) B2622017
theorem B3109079 : Blo 1636017 3109079 := bstep (se 1 (by rfl) ⟨2331809, by rfl⟩ : syracuseStep 3109079 = 4663619) B4663619
theorem B3682547 : Blo 1636017 3682547 := bstep (se 1 (by rfl) ⟨2761910, by rfl⟩ : syracuseStep 3682547 = 5523821) B5523821
theorem B5902595 : Blo 1636017 5902595 := bstep (se 1 (by rfl) ⟨4426946, by rfl⟩ : syracuseStep 5902595 = 8853893) B8853893
theorem B6213905 : Blo 1636017 6213905 := bstep (se 2 (by rfl) ⟨2330214, by rfl⟩ : syracuseStep 6213905 = 4660429) B4660429
theorem B3682583 : Blo 1636017 3682583 := bstep (se 1 (by rfl) ⟨2761937, by rfl⟩ : syracuseStep 3682583 = 5523875) B5523875
theorem B3363137 : Blo 1636017 3363137 := bstep (se 2 (by rfl) ⟨1261176, by rfl⟩ : syracuseStep 3363137 = 2522353) B2522353
theorem B20984129 : Blo 1636017 20984129 := bstep (se 2 (by rfl) ⟨7869048, by rfl⟩ : syracuseStep 20984129 = 15738097) B15738097
theorem B3682763 : Blo 1636017 3682763 := bstep (se 1 (by rfl) ⟨2762072, by rfl⟩ : syracuseStep 3682763 = 5524145) B5524145
theorem B3109337 : Blo 1636017 3109337 := bstep (se 2 (by rfl) ⟨1166001, by rfl⟩ : syracuseStep 3109337 = 2332003) B2332003
theorem B5525981 : Blo 1636017 5525981 := bstep (se 3 (by rfl) ⟨1036121, by rfl⟩ : syracuseStep 5525981 = 2072243) B2072243
theorem B3682817 : Blo 1636017 3682817 := bstep (se 2 (by rfl) ⟨1381056, by rfl⟩ : syracuseStep 3682817 = 2762113) B2762113
theorem B2454041 : Blo 1636017 2454041 := bstep (se 2 (by rfl) ⟨920265, by rfl⟩ : syracuseStep 2454041 = 1840531) B1840531
theorem B8286785 : Blo 1636017 8286785 := bstep (se 2 (by rfl) ⟨3107544, by rfl⟩ : syracuseStep 8286785 = 6215089) B6215089
theorem B8516161 : Blo 1636017 8516161 := bstep (se 2 (by rfl) ⟨3193560, by rfl⟩ : syracuseStep 8516161 = 6387121) B6387121
theorem B14373469 : Blo 1636017 14373469 := bstep (se 3 (by rfl) ⟨2695025, by rfl⟩ : syracuseStep 14373469 = 5390051) B5390051
theorem B2454155 : Blo 1636017 2454155 := bstep (se 1 (by rfl) ⟨1840616, by rfl⟩ : syracuseStep 2454155 = 3681233) B3681233
theorem B2454167 : Blo 1636017 2454167 := bstep (se 1 (by rfl) ⟨1840625, by rfl⟩ : syracuseStep 2454167 = 3681251) B3681251
theorem B2454233 : Blo 1636017 2454233 := bstep (se 2 (by rfl) ⟨920337, by rfl⟩ : syracuseStep 2454233 = 1840675) B1840675
theorem B3683033 : Blo 1636017 3683033 := bstep (se 2 (by rfl) ⟨1381137, by rfl⟩ : syracuseStep 3683033 = 2762275) B2762275
theorem B3683123 : Blo 1636017 3683123 := bstep (se 1 (by rfl) ⟨2762342, by rfl⟩ : syracuseStep 3683123 = 5524685) B5524685
theorem B2454347 : Blo 1636017 2454347 := bstep (se 1 (by rfl) ⟨1840760, by rfl⟩ : syracuseStep 2454347 = 3681521) B3681521
theorem B2454359 : Blo 1636017 2454359 := bstep (se 1 (by rfl) ⟨1840769, by rfl⟩ : syracuseStep 2454359 = 3681539) B3681539
theorem B3683159 : Blo 1636017 3683159 := bstep (se 1 (by rfl) ⟨2762369, by rfl⟩ : syracuseStep 3683159 = 5524739) B5524739
theorem B6992729 : Blo 1636017 6992729 := bstep (se 2 (by rfl) ⟨2622273, by rfl⟩ : syracuseStep 6992729 = 5244547) B5244547
theorem B10482533 : Blo 1636017 10482533 := bstep (se 4 (by rfl) ⟨982737, by rfl⟩ : syracuseStep 10482533 = 1965475) B1965475
theorem B4141975 : Blo 1636017 4141975 := bstep (se 1 (by rfl) ⟨3106481, by rfl⟩ : syracuseStep 4141975 = 6212963) B6212963
theorem B3986327 : Blo 1636017 3986327 := bstep (se 1 (by rfl) ⟨2989745, by rfl⟩ : syracuseStep 3986327 = 5979491) B5979491
theorem B2454425 : Blo 1636017 2454425 := bstep (se 2 (by rfl) ⟨920409, by rfl⟩ : syracuseStep 2454425 = 1840819) B1840819
theorem B6214603 : Blo 1636017 6214603 := bstep (se 1 (by rfl) ⟨4660952, by rfl⟩ : syracuseStep 6214603 = 9321905) B9321905
theorem B2454539 : Blo 1636017 2454539 := bstep (se 1 (by rfl) ⟨1840904, by rfl⟩ : syracuseStep 2454539 = 3681809) B3681809
theorem B3683339 : Blo 1636017 3683339 := bstep (se 1 (by rfl) ⟨2762504, by rfl⟩ : syracuseStep 3683339 = 5525009) B5525009
theorem B2454551 : Blo 1636017 2454551 := bstep (se 1 (by rfl) ⟨1840913, by rfl⟩ : syracuseStep 2454551 = 3681827) B3681827
theorem B3494963 : Blo 1636017 3494963 := bstep (se 1 (by rfl) ⟨2621222, by rfl⟩ : syracuseStep 3494963 = 5242445) B5242445
theorem B3683393 : Blo 1636017 3683393 := bstep (se 2 (by rfl) ⟨1381272, by rfl⟩ : syracuseStep 3683393 = 2762545) B2762545
theorem B2454617 : Blo 1636017 2454617 := bstep (se 2 (by rfl) ⟨920481, by rfl⟩ : syracuseStep 2454617 = 1840963) B1840963
theorem B2454731 : Blo 1636017 2454731 := bstep (se 1 (by rfl) ⟨1841048, by rfl⟩ : syracuseStep 2454731 = 3682097) B3682097
theorem B2454743 : Blo 1636017 2454743 := bstep (se 1 (by rfl) ⟨1841057, by rfl⟩ : syracuseStep 2454743 = 3682115) B3682115
theorem B6214877 : Blo 1636017 6214877 := bstep (se 3 (by rfl) ⟨1165289, by rfl⟩ : syracuseStep 6214877 = 2330579) B2330579
theorem B9319697 : Blo 1636017 9319697 := bstep (se 2 (by rfl) ⟨3494886, by rfl⟩ : syracuseStep 9319697 = 6989773) B6989773
theorem B2454809 : Blo 1636017 2454809 := bstep (se 2 (by rfl) ⟨920553, by rfl⟩ : syracuseStep 2454809 = 1841107) B1841107
theorem B3683609 : Blo 1636017 3683609 := bstep (se 2 (by rfl) ⟨1381353, by rfl⟩ : syracuseStep 3683609 = 2762707) B2762707
theorem B2331929 : Blo 1636017 2331929 := bstep (se 2 (by rfl) ⟨874473, by rfl⟩ : syracuseStep 2331929 = 1748947) B1748947
theorem B4142411 : Blo 1636017 4142411 := bstep (se 1 (by rfl) ⟨3106808, by rfl⟩ : syracuseStep 4142411 = 6213617) B6213617
theorem B12596573 : Blo 1636017 12596573 := bstep (se 3 (by rfl) ⟨2361857, by rfl⟩ : syracuseStep 12596573 = 4723715) B4723715
theorem B3683699 : Blo 1636017 3683699 := bstep (se 1 (by rfl) ⟨2762774, by rfl⟩ : syracuseStep 3683699 = 5525549) B5525549
theorem B2454923 : Blo 1636017 2454923 := bstep (se 1 (by rfl) ⟨1841192, by rfl⟩ : syracuseStep 2454923 = 3682385) B3682385
theorem B2454935 : Blo 1636017 2454935 := bstep (se 1 (by rfl) ⟨1841201, by rfl⟩ : syracuseStep 2454935 = 3682403) B3682403
theorem B3683735 : Blo 1636017 3683735 := bstep (se 1 (by rfl) ⟨2762801, by rfl⟩ : syracuseStep 3683735 = 5525603) B5525603
theorem B1840567 : Blo 1636017 1840567 := bstep (se 1 (by rfl) ⟨1380425, by rfl⟩ : syracuseStep 1840567 = 2760851) B2760851
theorem B2455001 : Blo 1636017 2455001 := bstep (se 2 (by rfl) ⟨920625, by rfl⟩ : syracuseStep 2455001 = 1841251) B1841251
theorem B53827085 : Blo 1636017 53827085 := bstep (se 3 (by rfl) ⟨10092578, by rfl⟩ : syracuseStep 53827085 = 20185157) B20185157
theorem B9328193 : Blo 1636017 9328193 := bstep (se 2 (by rfl) ⟨3498072, by rfl⟩ : syracuseStep 9328193 = 6996145) B6996145
theorem B2455115 : Blo 1636017 2455115 := bstep (se 1 (by rfl) ⟨1841336, by rfl⟩ : syracuseStep 2455115 = 3682673) B3682673
theorem B3683915 : Blo 1636017 3683915 := bstep (se 1 (by rfl) ⟨2762936, by rfl⟩ : syracuseStep 3683915 = 5525873) B5525873
theorem B5527115 : Blo 1636017 5527115 := bstep (se 1 (by rfl) ⟨4145336, by rfl⟩ : syracuseStep 5527115 = 8290673) B8290673
theorem B2455127 : Blo 1636017 2455127 := bstep (se 1 (by rfl) ⟨1841345, by rfl⟩ : syracuseStep 2455127 = 3682691) B3682691
theorem B4789849 : Blo 1636017 4789849 := bstep (se 2 (by rfl) ⟨1796193, by rfl⟩ : syracuseStep 4789849 = 3592387) B3592387
theorem B1840747 : Blo 1636017 1840747 := bstep (se 1 (by rfl) ⟨1380560, by rfl⟩ : syracuseStep 1840747 = 2761121) B2761121
theorem B3733121 : Blo 1636017 3733121 := bstep (se 2 (by rfl) ⟨1399920, by rfl⟩ : syracuseStep 3733121 = 2799841) B2799841
theorem B16799363 : Blo 1636017 16799363 := bstep (se 1 (by rfl) ⟨12599522, by rfl⟩ : syracuseStep 16799363 = 25199045) B25199045
theorem B3683969 : Blo 1636017 3683969 := bstep (se 2 (by rfl) ⟨1381488, by rfl⟩ : syracuseStep 3683969 = 2762977) B2762977
theorem B2455193 : Blo 1636017 2455193 := bstep (se 2 (by rfl) ⟨920697, by rfl⟩ : syracuseStep 2455193 = 1841395) B1841395
theorem B1636023 : Blo 1636017 1636023 := bstep (se 1 (by rfl) ⟨1227017, by rfl⟩ : syracuseStep 1636023 = 2454035) B2454035
theorem B4142785 : Blo 1636017 4142785 := bstep (se 2 (by rfl) ⟨1553544, by rfl⟩ : syracuseStep 4142785 = 3107089) B3107089
theorem B1636043 : Blo 1636017 1636043 := bstep (se 1 (by rfl) ⟨1227032, by rfl⟩ : syracuseStep 1636043 = 2454065) B2454065
theorem B1636055 : Blo 1636017 1636055 := bstep (se 1 (by rfl) ⟨1227041, by rfl⟩ : syracuseStep 1636055 = 2454083) B2454083
theorem B1840855 : Blo 1636017 1840855 := bstep (se 1 (by rfl) ⟨1380641, by rfl⟩ : syracuseStep 1840855 = 2761283) B2761283
theorem B1636075 : Blo 1636017 1636075 := bstep (se 1 (by rfl) ⟨1227056, by rfl⟩ : syracuseStep 1636075 = 2454113) B2454113
theorem B1636087 : Blo 1636017 1636087 := bstep (se 1 (by rfl) ⟨1227065, by rfl⟩ : syracuseStep 1636087 = 2454131) B2454131
theorem B1636107 : Blo 1636017 1636107 := bstep (se 1 (by rfl) ⟨1227080, by rfl⟩ : syracuseStep 1636107 = 2454161) B2454161
theorem B2455307 : Blo 1636017 2455307 := bstep (se 1 (by rfl) ⟨1841480, by rfl⟩ : syracuseStep 2455307 = 3682961) B3682961
theorem B1636119 : Blo 1636017 1636119 := bstep (se 1 (by rfl) ⟨1227089, by rfl⟩ : syracuseStep 1636119 = 2454179) B2454179
theorem B2455319 : Blo 1636017 2455319 := bstep (se 1 (by rfl) ⟨1841489, by rfl⟩ : syracuseStep 2455319 = 3682979) B3682979
theorem B1636139 : Blo 1636017 1636139 := bstep (se 1 (by rfl) ⟨1227104, by rfl⟩ : syracuseStep 1636139 = 2454209) B2454209
theorem B3151667 : Blo 1636017 3151667 := bstep (se 1 (by rfl) ⟨2363750, by rfl⟩ : syracuseStep 3151667 = 4727501) B4727501
theorem B1636151 : Blo 1636017 1636151 := bstep (se 1 (by rfl) ⟨1227113, by rfl⟩ : syracuseStep 1636151 = 2454227) B2454227
theorem B16807745 : Blo 1636017 16807745 := bstep (se 2 (by rfl) ⟨6302904, by rfl⟩ : syracuseStep 16807745 = 12605809) B12605809
theorem B1636171 : Blo 1636017 1636171 := bstep (se 1 (by rfl) ⟨1227128, by rfl⟩ : syracuseStep 1636171 = 2454257) B2454257
theorem B1636183 : Blo 1636017 1636183 := bstep (se 1 (by rfl) ⟨1227137, by rfl⟩ : syracuseStep 1636183 = 2454275) B2454275
theorem B2455385 : Blo 1636017 2455385 := bstep (se 2 (by rfl) ⟨920769, by rfl⟩ : syracuseStep 2455385 = 1841539) B1841539
theorem B3684185 : Blo 1636017 3684185 := bstep (se 2 (by rfl) ⟨1381569, by rfl⟩ : syracuseStep 3684185 = 2763139) B2763139
theorem B5527385 : Blo 1636017 5527385 := bstep (se 2 (by rfl) ⟨2072769, by rfl⟩ : syracuseStep 5527385 = 4145539) B4145539
theorem B1636203 : Blo 1636017 1636203 := bstep (se 1 (by rfl) ⟨1227152, by rfl⟩ : syracuseStep 1636203 = 2454305) B2454305
theorem B1636215 : Blo 1636017 1636215 := bstep (se 1 (by rfl) ⟨1227161, by rfl⟩ : syracuseStep 1636215 = 2454323) B2454323
theorem B14940035 : Blo 1636017 14940035 := bstep (se 1 (by rfl) ⟨11205026, by rfl⟩ : syracuseStep 14940035 = 22410053) B22410053
theorem B1636235 : Blo 1636017 1636235 := bstep (se 1 (by rfl) ⟨1227176, by rfl⟩ : syracuseStep 1636235 = 2454353) B2454353
theorem B1841035 : Blo 1636017 1841035 := bstep (se 1 (by rfl) ⟨1380776, by rfl⟩ : syracuseStep 1841035 = 2761553) B2761553
theorem B272357261 : Blo 1636017 272357261 := bstep (se 3 (by rfl) ⟨51066986, by rfl⟩ : syracuseStep 272357261 = 102133973) B102133973
theorem B1636247 : Blo 1636017 1636247 := bstep (se 1 (by rfl) ⟨1227185, by rfl⟩ : syracuseStep 1636247 = 2454371) B2454371
theorem B6215575 : Blo 1636017 6215575 := bstep (se 1 (by rfl) ⟨4661681, by rfl⟩ : syracuseStep 6215575 = 9323363) B9323363
theorem B1636267 : Blo 1636017 1636267 := bstep (se 1 (by rfl) ⟨1227200, by rfl⟩ : syracuseStep 1636267 = 2454401) B2454401
theorem B3684275 : Blo 1636017 3684275 := bstep (se 1 (by rfl) ⟨2763206, by rfl⟩ : syracuseStep 3684275 = 5526413) B5526413
theorem B1636279 : Blo 1636017 1636279 := bstep (se 1 (by rfl) ⟨1227209, by rfl⟩ : syracuseStep 1636279 = 2454419) B2454419
theorem B1636299 : Blo 1636017 1636299 := bstep (se 1 (by rfl) ⟨1227224, by rfl⟩ : syracuseStep 1636299 = 2454449) B2454449
theorem B2455499 : Blo 1636017 2455499 := bstep (se 1 (by rfl) ⟨1841624, by rfl⟩ : syracuseStep 2455499 = 3683249) B3683249
theorem B1636311 : Blo 1636017 1636311 := bstep (se 1 (by rfl) ⟨1227233, by rfl⟩ : syracuseStep 1636311 = 2454467) B2454467
theorem B2455511 : Blo 1636017 2455511 := bstep (se 1 (by rfl) ⟨1841633, by rfl⟩ : syracuseStep 2455511 = 3683267) B3683267
theorem B3684311 : Blo 1636017 3684311 := bstep (se 1 (by rfl) ⟨2763233, by rfl⟩ : syracuseStep 3684311 = 5526467) B5526467
theorem B1636331 : Blo 1636017 1636331 := bstep (se 1 (by rfl) ⟨1227248, by rfl⟩ : syracuseStep 1636331 = 2454497) B2454497
theorem B1841143 : Blo 1636017 1841143 := bstep (se 1 (by rfl) ⟨1380857, by rfl⟩ : syracuseStep 1841143 = 2761715) B2761715
theorem B1636343 : Blo 1636017 1636343 := bstep (se 1 (by rfl) ⟨1227257, by rfl⟩ : syracuseStep 1636343 = 2454515) B2454515
theorem B1636363 : Blo 1636017 1636363 := bstep (se 1 (by rfl) ⟨1227272, by rfl⟩ : syracuseStep 1636363 = 2454545) B2454545
theorem B1636375 : Blo 1636017 1636375 := bstep (se 1 (by rfl) ⟨1227281, by rfl⟩ : syracuseStep 1636375 = 2454563) B2454563
theorem B2455577 : Blo 1636017 2455577 := bstep (se 2 (by rfl) ⟨920841, by rfl⟩ : syracuseStep 2455577 = 1841683) B1841683
theorem B1636395 : Blo 1636017 1636395 := bstep (se 1 (by rfl) ⟨1227296, by rfl⟩ : syracuseStep 1636395 = 2454593) B2454593
theorem B1636407 : Blo 1636017 1636407 := bstep (se 1 (by rfl) ⟨1227305, by rfl⟩ : syracuseStep 1636407 = 2454611) B2454611
theorem B1636427 : Blo 1636017 1636427 := bstep (se 1 (by rfl) ⟨1227320, by rfl⟩ : syracuseStep 1636427 = 2454641) B2454641
theorem B1636439 : Blo 1636017 1636439 := bstep (se 1 (by rfl) ⟨1227329, by rfl⟩ : syracuseStep 1636439 = 2454659) B2454659
theorem B1636459 : Blo 1636017 1636459 := bstep (se 1 (by rfl) ⟨1227344, by rfl⟩ : syracuseStep 1636459 = 2454689) B2454689
theorem B1636471 : Blo 1636017 1636471 := bstep (se 1 (by rfl) ⟨1227353, by rfl⟩ : syracuseStep 1636471 = 2454707) B2454707
theorem B1636491 : Blo 1636017 1636491 := bstep (se 1 (by rfl) ⟨1227368, by rfl⟩ : syracuseStep 1636491 = 2454737) B2454737
theorem B2455691 : Blo 1636017 2455691 := bstep (se 1 (by rfl) ⟨1841768, by rfl⟩ : syracuseStep 2455691 = 3683537) B3683537
theorem B3684491 : Blo 1636017 3684491 := bstep (se 1 (by rfl) ⟨2763368, by rfl⟩ : syracuseStep 3684491 = 5526737) B5526737
theorem B2070679 : Blo 1636017 2070679 := bstep (se 1 (by rfl) ⟨1553009, by rfl⟩ : syracuseStep 2070679 = 3106019) B3106019
theorem B1636503 : Blo 1636017 1636503 := bstep (se 1 (by rfl) ⟨1227377, by rfl⟩ : syracuseStep 1636503 = 2454755) B2454755
theorem B2455703 : Blo 1636017 2455703 := bstep (se 1 (by rfl) ⟨1841777, by rfl⟩ : syracuseStep 2455703 = 3683555) B3683555
theorem B1636523 : Blo 1636017 1636523 := bstep (se 1 (by rfl) ⟨1227392, by rfl⟩ : syracuseStep 1636523 = 2454785) B2454785
theorem B1841323 : Blo 1636017 1841323 := bstep (se 1 (by rfl) ⟨1380992, by rfl⟩ : syracuseStep 1841323 = 2761985) B2761985
theorem B1636535 : Blo 1636017 1636535 := bstep (se 1 (by rfl) ⟨1227401, by rfl⟩ : syracuseStep 1636535 = 2454803) B2454803
theorem B3684545 : Blo 1636017 3684545 := bstep (se 2 (by rfl) ⟨1381704, by rfl⟩ : syracuseStep 3684545 = 2763409) B2763409
theorem B1636555 : Blo 1636017 1636555 := bstep (se 1 (by rfl) ⟨1227416, by rfl⟩ : syracuseStep 1636555 = 2454833) B2454833
theorem B1636567 : Blo 1636017 1636567 := bstep (se 1 (by rfl) ⟨1227425, by rfl⟩ : syracuseStep 1636567 = 2454851) B2454851
theorem B2455769 : Blo 1636017 2455769 := bstep (se 2 (by rfl) ⟨920913, by rfl⟩ : syracuseStep 2455769 = 1841827) B1841827
theorem B1636587 : Blo 1636017 1636587 := bstep (se 1 (by rfl) ⟨1227440, by rfl⟩ : syracuseStep 1636587 = 2454881) B2454881
theorem B1636599 : Blo 1636017 1636599 := bstep (se 1 (by rfl) ⟨1227449, by rfl⟩ : syracuseStep 1636599 = 2454899) B2454899
theorem B1636619 : Blo 1636017 1636619 := bstep (se 1 (by rfl) ⟨1227464, by rfl⟩ : syracuseStep 1636619 = 2454929) B2454929
theorem B1636631 : Blo 1636017 1636631 := bstep (se 1 (by rfl) ⟨1227473, by rfl⟩ : syracuseStep 1636631 = 2454947) B2454947
theorem B1841431 : Blo 1636017 1841431 := bstep (se 1 (by rfl) ⟨1381073, by rfl⟩ : syracuseStep 1841431 = 2762147) B2762147
theorem B2488601 : Blo 1636017 2488601 := bstep (se 2 (by rfl) ⟨933225, by rfl⟩ : syracuseStep 2488601 = 1866451) B1866451
theorem B4143383 : Blo 1636017 4143383 := bstep (se 1 (by rfl) ⟨3107537, by rfl⟩ : syracuseStep 4143383 = 6215075) B6215075
theorem B1636651 : Blo 1636017 1636651 := bstep (se 1 (by rfl) ⟨1227488, by rfl⟩ : syracuseStep 1636651 = 2454977) B2454977
theorem B1636663 : Blo 1636017 1636663 := bstep (se 1 (by rfl) ⟨1227497, by rfl⟩ : syracuseStep 1636663 = 2454995) B2454995
theorem B1636683 : Blo 1636017 1636683 := bstep (se 1 (by rfl) ⟨1227512, by rfl⟩ : syracuseStep 1636683 = 2455025) B2455025
theorem B2455883 : Blo 1636017 2455883 := bstep (se 1 (by rfl) ⟨1841912, by rfl⟩ : syracuseStep 2455883 = 3683825) B3683825
theorem B1636695 : Blo 1636017 1636695 := bstep (se 1 (by rfl) ⟨1227521, by rfl⟩ : syracuseStep 1636695 = 2455043) B2455043
theorem B3496279 : Blo 1636017 3496279 := bstep (se 1 (by rfl) ⟨2622209, by rfl⟩ : syracuseStep 3496279 = 5244419) B5244419
theorem B2455895 : Blo 1636017 2455895 := bstep (se 1 (by rfl) ⟨1841921, by rfl⟩ : syracuseStep 2455895 = 3683843) B3683843
theorem B1636715 : Blo 1636017 1636715 := bstep (se 1 (by rfl) ⟨1227536, by rfl⟩ : syracuseStep 1636715 = 2455073) B2455073
theorem B1636727 : Blo 1636017 1636727 := bstep (se 1 (by rfl) ⟨1227545, by rfl⟩ : syracuseStep 1636727 = 2455091) B2455091
theorem B1636747 : Blo 1636017 1636747 := bstep (se 1 (by rfl) ⟨1227560, by rfl⟩ : syracuseStep 1636747 = 2455121) B2455121
theorem B1636759 : Blo 1636017 1636759 := bstep (se 1 (by rfl) ⟨1227569, by rfl⟩ : syracuseStep 1636759 = 2455139) B2455139
theorem B9959831 : Blo 1636017 9959831 := bstep (se 1 (by rfl) ⟨7469873, by rfl⟩ : syracuseStep 9959831 = 14939747) B14939747
theorem B2455961 : Blo 1636017 2455961 := bstep (se 2 (by rfl) ⟨920985, by rfl⟩ : syracuseStep 2455961 = 1841971) B1841971
theorem B3684761 : Blo 1636017 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B5757335 : Blo 1636017 5757335 := bstep (se 1 (by rfl) ⟨4318001, by rfl⟩ : syracuseStep 5757335 = 8636003) B8636003
theorem B1636779 : Blo 1636017 1636779 := bstep (se 1 (by rfl) ⟨1227584, by rfl⟩ : syracuseStep 1636779 = 2455169) B2455169
theorem B1636791 : Blo 1636017 1636791 := bstep (se 1 (by rfl) ⟨1227593, by rfl⟩ : syracuseStep 1636791 = 2455187) B2455187
theorem B1636811 : Blo 1636017 1636811 := bstep (se 1 (by rfl) ⟨1227608, by rfl⟩ : syracuseStep 1636811 = 2455217) B2455217
theorem B1841611 : Blo 1636017 1841611 := bstep (se 1 (by rfl) ⟨1381208, by rfl⟩ : syracuseStep 1841611 = 2762417) B2762417
theorem B1636823 : Blo 1636017 1636823 := bstep (se 1 (by rfl) ⟨1227617, by rfl⟩ : syracuseStep 1636823 = 2455235) B2455235
theorem B8288729 : Blo 1636017 8288729 := bstep (se 2 (by rfl) ⟨3108273, by rfl⟩ : syracuseStep 8288729 = 6216547) B6216547
theorem B4659677 : Blo 1636017 4659677 := bstep (se 3 (by rfl) ⟨873689, by rfl⟩ : syracuseStep 4659677 = 1747379) B1747379
theorem B1636843 : Blo 1636017 1636843 := bstep (se 1 (by rfl) ⟨1227632, by rfl⟩ : syracuseStep 1636843 = 2455265) B2455265
theorem B1636855 : Blo 1636017 1636855 := bstep (se 1 (by rfl) ⟨1227641, by rfl⟩ : syracuseStep 1636855 = 2455283) B2455283
theorem B3684851 : Blo 1636017 3684851 := bstep (se 1 (by rfl) ⟨2763638, by rfl⟩ : syracuseStep 3684851 = 5527277) B5527277
theorem B1636875 : Blo 1636017 1636875 := bstep (se 1 (by rfl) ⟨1227656, by rfl⟩ : syracuseStep 1636875 = 2455313) B2455313
theorem B3496459 : Blo 1636017 3496459 := bstep (se 1 (by rfl) ⟨2622344, by rfl⟩ : syracuseStep 3496459 = 5244689) B5244689
theorem B2456075 : Blo 1636017 2456075 := bstep (se 1 (by rfl) ⟨1842056, by rfl⟩ : syracuseStep 2456075 = 3684113) B3684113
theorem B340113937 : Blo 1636017 340113937 := bstep (se 2 (by rfl) ⟨127542726, by rfl⟩ : syracuseStep 340113937 = 255085453) B255085453
theorem B1636887 : Blo 1636017 1636887 := bstep (se 1 (by rfl) ⟨1227665, by rfl⟩ : syracuseStep 1636887 = 2455331) B2455331
theorem B2456087 : Blo 1636017 2456087 := bstep (se 1 (by rfl) ⟨1842065, by rfl⟩ : syracuseStep 2456087 = 3684131) B3684131
theorem B3684887 : Blo 1636017 3684887 := bstep (se 1 (by rfl) ⟨2763665, by rfl⟩ : syracuseStep 3684887 = 5527331) B5527331
theorem B5528087 : Blo 1636017 5528087 := bstep (se 1 (by rfl) ⟨4146065, by rfl⟩ : syracuseStep 5528087 = 8292131) B8292131
theorem B11803171 : Blo 1636017 11803171 := bstep (se 1 (by rfl) ⟨8852378, by rfl⟩ : syracuseStep 11803171 = 17704757) B17704757
theorem B1636907 : Blo 1636017 1636907 := bstep (se 1 (by rfl) ⟨1227680, by rfl⟩ : syracuseStep 1636907 = 2455361) B2455361
theorem B1636919 : Blo 1636017 1636919 := bstep (se 1 (by rfl) ⟨1227689, by rfl⟩ : syracuseStep 1636919 = 2455379) B2455379
theorem B1841719 : Blo 1636017 1841719 := bstep (se 1 (by rfl) ⟨1381289, by rfl⟩ : syracuseStep 1841719 = 2762579) B2762579
theorem B1636939 : Blo 1636017 1636939 := bstep (se 1 (by rfl) ⟨1227704, by rfl⟩ : syracuseStep 1636939 = 2455409) B2455409
theorem B1636951 : Blo 1636017 1636951 := bstep (se 1 (by rfl) ⟨1227713, by rfl⟩ : syracuseStep 1636951 = 2455427) B2455427
theorem B3496535 : Blo 1636017 3496535 := bstep (se 1 (by rfl) ⟨2622401, by rfl⟩ : syracuseStep 3496535 = 5244803) B5244803
theorem B2456153 : Blo 1636017 2456153 := bstep (se 2 (by rfl) ⟨921057, by rfl⟩ : syracuseStep 2456153 = 1842115) B1842115
theorem B11803229 : Blo 1636017 11803229 := bstep (se 3 (by rfl) ⟨2213105, by rfl⟩ : syracuseStep 11803229 = 4426211) B4426211
theorem B1636971 : Blo 1636017 1636971 := bstep (se 1 (by rfl) ⟨1227728, by rfl⟩ : syracuseStep 1636971 = 2455457) B2455457
theorem B1636983 : Blo 1636017 1636983 := bstep (se 1 (by rfl) ⟨1227737, by rfl⟩ : syracuseStep 1636983 = 2455475) B2455475
theorem B1637003 : Blo 1636017 1637003 := bstep (se 1 (by rfl) ⟨1227752, by rfl⟩ : syracuseStep 1637003 = 2455505) B2455505
theorem B8395415 : Blo 1636017 8395415 := bstep (se 1 (by rfl) ⟨6296561, by rfl⟩ : syracuseStep 8395415 = 12593123) B12593123
theorem B1637015 : Blo 1636017 1637015 := bstep (se 1 (by rfl) ⟨1227761, by rfl⟩ : syracuseStep 1637015 = 2455523) B2455523
theorem B1637035 : Blo 1636017 1637035 := bstep (se 1 (by rfl) ⟨1227776, by rfl⟩ : syracuseStep 1637035 = 2455553) B2455553
theorem B6216365 : Blo 1636017 6216365 := bstep (se 3 (by rfl) ⟨1165568, by rfl⟩ : syracuseStep 6216365 = 2331137) B2331137
theorem B1637047 : Blo 1636017 1637047 := bstep (se 1 (by rfl) ⟨1227785, by rfl⟩ : syracuseStep 1637047 = 2455571) B2455571
theorem B4659905 : Blo 1636017 4659905 := bstep (se 2 (by rfl) ⟨1747464, by rfl⟩ : syracuseStep 4659905 = 3494929) B3494929
theorem B1637067 : Blo 1636017 1637067 := bstep (se 1 (by rfl) ⟨1227800, by rfl⟩ : syracuseStep 1637067 = 2455601) B2455601
theorem B2456267 : Blo 1636017 2456267 := bstep (se 1 (by rfl) ⟨1842200, by rfl⟩ : syracuseStep 2456267 = 3684401) B3684401
theorem B3685067 : Blo 1636017 3685067 := bstep (se 1 (by rfl) ⟨2763800, by rfl⟩ : syracuseStep 3685067 = 5527601) B5527601
theorem B1637079 : Blo 1636017 1637079 := bstep (se 1 (by rfl) ⟨1227809, by rfl⟩ : syracuseStep 1637079 = 2455619) B2455619
theorem B2456279 : Blo 1636017 2456279 := bstep (se 1 (by rfl) ⟨1842209, by rfl⟩ : syracuseStep 2456279 = 3684419) B3684419
theorem B1637099 : Blo 1636017 1637099 := bstep (se 1 (by rfl) ⟨1227824, by rfl⟩ : syracuseStep 1637099 = 2455649) B2455649
theorem B1841899 : Blo 1636017 1841899 := bstep (se 1 (by rfl) ⟨1381424, by rfl⟩ : syracuseStep 1841899 = 2762849) B2762849
theorem B1637111 : Blo 1636017 1637111 := bstep (se 1 (by rfl) ⟨1227833, by rfl⟩ : syracuseStep 1637111 = 2455667) B2455667
theorem B3685121 : Blo 1636017 3685121 := bstep (se 2 (by rfl) ⟨1381920, by rfl⟩ : syracuseStep 3685121 = 2763841) B2763841
theorem B1637131 : Blo 1636017 1637131 := bstep (se 1 (by rfl) ⟨1227848, by rfl⟩ : syracuseStep 1637131 = 2455697) B2455697
theorem B1637143 : Blo 1636017 1637143 := bstep (se 1 (by rfl) ⟨1227857, by rfl⟩ : syracuseStep 1637143 = 2455715) B2455715
theorem B2456345 : Blo 1636017 2456345 := bstep (se 2 (by rfl) ⟨921129, by rfl⟩ : syracuseStep 2456345 = 1842259) B1842259
theorem B1637163 : Blo 1636017 1637163 := bstep (se 1 (by rfl) ⟨1227872, by rfl⟩ : syracuseStep 1637163 = 2455745) B2455745
theorem B1637175 : Blo 1636017 1637175 := bstep (se 1 (by rfl) ⟨1227881, by rfl⟩ : syracuseStep 1637175 = 2455763) B2455763
theorem B1637195 : Blo 1636017 1637195 := bstep (se 1 (by rfl) ⟨1227896, by rfl⟩ : syracuseStep 1637195 = 2455793) B2455793
theorem B1637207 : Blo 1636017 1637207 := bstep (se 1 (by rfl) ⟨1227905, by rfl⟩ : syracuseStep 1637207 = 2455811) B2455811
theorem B1842007 : Blo 1636017 1842007 := bstep (se 1 (by rfl) ⟨1381505, by rfl⟩ : syracuseStep 1842007 = 2763011) B2763011
theorem B1637227 : Blo 1636017 1637227 := bstep (se 1 (by rfl) ⟨1227920, by rfl⟩ : syracuseStep 1637227 = 2455841) B2455841
theorem B1637239 : Blo 1636017 1637239 := bstep (se 1 (by rfl) ⟨1227929, by rfl⟩ : syracuseStep 1637239 = 2455859) B2455859
theorem B1637259 : Blo 1636017 1637259 := bstep (se 1 (by rfl) ⟨1227944, by rfl⟩ : syracuseStep 1637259 = 2455889) B2455889
theorem B2456459 : Blo 1636017 2456459 := bstep (se 1 (by rfl) ⟨1842344, by rfl⟩ : syracuseStep 2456459 = 3684689) B3684689
theorem B1637271 : Blo 1636017 1637271 := bstep (se 1 (by rfl) ⟨1227953, by rfl⟩ : syracuseStep 1637271 = 2455907) B2455907
theorem B2456471 : Blo 1636017 2456471 := bstep (se 1 (by rfl) ⟨1842353, by rfl⟩ : syracuseStep 2456471 = 3684707) B3684707
theorem B1637291 : Blo 1636017 1637291 := bstep (se 1 (by rfl) ⟨1227968, by rfl⟩ : syracuseStep 1637291 = 2455937) B2455937
theorem B5241779 : Blo 1636017 5241779 := bstep (se 1 (by rfl) ⟨3931334, by rfl⟩ : syracuseStep 5241779 = 7862669) B7862669
theorem B1637303 : Blo 1636017 1637303 := bstep (se 1 (by rfl) ⟨1227977, by rfl⟩ : syracuseStep 1637303 = 2455955) B2455955
theorem B1637323 : Blo 1636017 1637323 := bstep (se 1 (by rfl) ⟨1227992, by rfl⟩ : syracuseStep 1637323 = 2455985) B2455985
theorem B4979659 : Blo 1636017 4979659 := bstep (se 1 (by rfl) ⟨3734744, by rfl⟩ : syracuseStep 4979659 = 7469489) B7469489
theorem B1637335 : Blo 1636017 1637335 := bstep (se 1 (by rfl) ⟨1228001, by rfl⟩ : syracuseStep 1637335 = 2456003) B2456003
theorem B2456537 : Blo 1636017 2456537 := bstep (se 2 (by rfl) ⟨921201, by rfl⟩ : syracuseStep 2456537 = 1842403) B1842403
theorem B3685337 : Blo 1636017 3685337 := bstep (se 2 (by rfl) ⟨1382001, by rfl⟩ : syracuseStep 3685337 = 2764003) B2764003
theorem B1637355 : Blo 1636017 1637355 := bstep (se 1 (by rfl) ⟨1228016, by rfl⟩ : syracuseStep 1637355 = 2456033) B2456033
theorem B1637367 : Blo 1636017 1637367 := bstep (se 1 (by rfl) ⟨1228025, by rfl⟩ : syracuseStep 1637367 = 2456051) B2456051
theorem B1637387 : Blo 1636017 1637387 := bstep (se 1 (by rfl) ⟨1228040, by rfl⟩ : syracuseStep 1637387 = 2456081) B2456081
theorem B1842187 : Blo 1636017 1842187 := bstep (se 1 (by rfl) ⟨1381640, by rfl⟩ : syracuseStep 1842187 = 2763281) B2763281
theorem B4660247 : Blo 1636017 4660247 := bstep (se 1 (by rfl) ⟨3495185, by rfl⟩ : syracuseStep 4660247 = 6990371) B6990371
theorem B1866775 : Blo 1636017 1866775 := bstep (se 1 (by rfl) ⟨1400081, by rfl⟩ : syracuseStep 1866775 = 2800163) B2800163
theorem B1637399 : Blo 1636017 1637399 := bstep (se 1 (by rfl) ⟨1228049, by rfl⟩ : syracuseStep 1637399 = 2456099) B2456099
theorem B1637419 : Blo 1636017 1637419 := bstep (se 1 (by rfl) ⟨1228064, by rfl⟩ : syracuseStep 1637419 = 2456129) B2456129
theorem B3685427 : Blo 1636017 3685427 := bstep (se 1 (by rfl) ⟨2764070, by rfl⟩ : syracuseStep 3685427 = 5528141) B5528141
theorem B1637431 : Blo 1636017 1637431 := bstep (se 1 (by rfl) ⟨1228073, by rfl⟩ : syracuseStep 1637431 = 2456147) B2456147
theorem B4144193 : Blo 1636017 4144193 := bstep (se 2 (by rfl) ⟨1554072, by rfl⟩ : syracuseStep 4144193 = 3108145) B3108145
theorem B1637451 : Blo 1636017 1637451 := bstep (se 1 (by rfl) ⟨1228088, by rfl⟩ : syracuseStep 1637451 = 2456177) B2456177
theorem B2456651 : Blo 1636017 2456651 := bstep (se 1 (by rfl) ⟨1842488, by rfl⟩ : syracuseStep 2456651 = 3684977) B3684977
theorem B1637463 : Blo 1636017 1637463 := bstep (se 1 (by rfl) ⟨1228097, by rfl⟩ : syracuseStep 1637463 = 2456195) B2456195
theorem B2456663 : Blo 1636017 2456663 := bstep (se 1 (by rfl) ⟨1842497, by rfl⟩ : syracuseStep 2456663 = 3684995) B3684995
theorem B3685463 : Blo 1636017 3685463 := bstep (se 1 (by rfl) ⟨2764097, by rfl⟩ : syracuseStep 3685463 = 5528195) B5528195
theorem B1637483 : Blo 1636017 1637483 := bstep (se 1 (by rfl) ⟨1228112, by rfl⟩ : syracuseStep 1637483 = 2456225) B2456225
theorem B1637495 : Blo 1636017 1637495 := bstep (se 1 (by rfl) ⟨1228121, by rfl⟩ : syracuseStep 1637495 = 2456243) B2456243
theorem B1842295 : Blo 1636017 1842295 := bstep (se 1 (by rfl) ⟨1381721, by rfl⟩ : syracuseStep 1842295 = 2763443) B2763443
theorem B1637515 : Blo 1636017 1637515 := bstep (se 1 (by rfl) ⟨1228136, by rfl⟩ : syracuseStep 1637515 = 2456273) B2456273
theorem B1637527 : Blo 1636017 1637527 := bstep (se 1 (by rfl) ⟨1228145, by rfl⟩ : syracuseStep 1637527 = 2456291) B2456291
theorem B2456729 : Blo 1636017 2456729 := bstep (se 2 (by rfl) ⟨921273, by rfl⟩ : syracuseStep 2456729 = 1842547) B1842547
theorem B1637547 : Blo 1636017 1637547 := bstep (se 1 (by rfl) ⟨1228160, by rfl⟩ : syracuseStep 1637547 = 2456321) B2456321
theorem B1637559 : Blo 1636017 1637559 := bstep (se 1 (by rfl) ⟨1228169, by rfl⟩ : syracuseStep 1637559 = 2456339) B2456339
theorem B1637579 : Blo 1636017 1637579 := bstep (se 1 (by rfl) ⟨1228184, by rfl⟩ : syracuseStep 1637579 = 2456369) B2456369
theorem B1637591 : Blo 1636017 1637591 := bstep (se 1 (by rfl) ⟨1228193, by rfl⟩ : syracuseStep 1637591 = 2456387) B2456387
theorem B13991129 : Blo 1636017 13991129 := bstep (se 2 (by rfl) ⟨5246673, by rfl⟩ : syracuseStep 13991129 = 10493347) B10493347
theorem B1637611 : Blo 1636017 1637611 := bstep (se 1 (by rfl) ⟨1228208, by rfl⟩ : syracuseStep 1637611 = 2456417) B2456417
theorem B1637623 : Blo 1636017 1637623 := bstep (se 1 (by rfl) ⟨1228217, by rfl⟩ : syracuseStep 1637623 = 2456435) B2456435
theorem B1637643 : Blo 1636017 1637643 := bstep (se 1 (by rfl) ⟨1228232, by rfl⟩ : syracuseStep 1637643 = 2456465) B2456465
theorem B2456843 : Blo 1636017 2456843 := bstep (se 1 (by rfl) ⟨1842632, by rfl⟩ : syracuseStep 2456843 = 3685265) B3685265
theorem B1637655 : Blo 1636017 1637655 := bstep (se 1 (by rfl) ⟨1228241, by rfl⟩ : syracuseStep 1637655 = 2456483) B2456483
theorem B2456855 : Blo 1636017 2456855 := bstep (se 1 (by rfl) ⟨1842641, by rfl⟩ : syracuseStep 2456855 = 3685283) B3685283
theorem B1637675 : Blo 1636017 1637675 := bstep (se 1 (by rfl) ⟨1228256, by rfl⟩ : syracuseStep 1637675 = 2456513) B2456513
theorem B1842475 : Blo 1636017 1842475 := bstep (se 1 (by rfl) ⟨1381856, by rfl⟩ : syracuseStep 1842475 = 2763713) B2763713
theorem B1637687 : Blo 1636017 1637687 := bstep (se 1 (by rfl) ⟨1228265, by rfl⟩ : syracuseStep 1637687 = 2456531) B2456531
theorem B1637707 : Blo 1636017 1637707 := bstep (se 1 (by rfl) ⟨1228280, by rfl⟩ : syracuseStep 1637707 = 2456561) B2456561
theorem B1637719 : Blo 1636017 1637719 := bstep (se 1 (by rfl) ⟨1228289, by rfl⟩ : syracuseStep 1637719 = 2456579) B2456579
theorem B2456921 : Blo 1636017 2456921 := bstep (se 2 (by rfl) ⟨921345, by rfl⟩ : syracuseStep 2456921 = 1842691) B1842691
theorem B1637739 : Blo 1636017 1637739 := bstep (se 1 (by rfl) ⟨1228304, by rfl⟩ : syracuseStep 1637739 = 2456609) B2456609
theorem B1637751 : Blo 1636017 1637751 := bstep (se 1 (by rfl) ⟨1228313, by rfl⟩ : syracuseStep 1637751 = 2456627) B2456627
theorem B1637771 : Blo 1636017 1637771 := bstep (se 1 (by rfl) ⟨1228328, by rfl⟩ : syracuseStep 1637771 = 2456657) B2456657
theorem B1637783 : Blo 1636017 1637783 := bstep (se 1 (by rfl) ⟨1228337, by rfl⟩ : syracuseStep 1637783 = 2456675) B2456675
theorem B1842583 : Blo 1636017 1842583 := bstep (se 1 (by rfl) ⟨1381937, by rfl⟩ : syracuseStep 1842583 = 2763875) B2763875
theorem B1637803 : Blo 1636017 1637803 := bstep (se 1 (by rfl) ⟨1228352, by rfl⟩ : syracuseStep 1637803 = 2456705) B2456705
theorem B1637815 : Blo 1636017 1637815 := bstep (se 1 (by rfl) ⟨1228361, by rfl⟩ : syracuseStep 1637815 = 2456723) B2456723
theorem B6995393 : Blo 1636017 6995393 := bstep (se 2 (by rfl) ⟨2623272, by rfl⟩ : syracuseStep 6995393 = 5246545) B5246545
theorem B2801099 : Blo 1636017 2801099 := bstep (se 1 (by rfl) ⟨2100824, by rfl⟩ : syracuseStep 2801099 = 4201649) B4201649
theorem B1637835 : Blo 1636017 1637835 := bstep (se 1 (by rfl) ⟨1228376, by rfl⟩ : syracuseStep 1637835 = 2456753) B2456753
theorem B1637847 : Blo 1636017 1637847 := bstep (se 1 (by rfl) ⟨1228385, by rfl⟩ : syracuseStep 1637847 = 2456771) B2456771
theorem B20979161 : Blo 1636017 20979161 := bstep (se 2 (by rfl) ⟨7867185, by rfl⟩ : syracuseStep 20979161 = 15734371) B15734371
theorem B1637867 : Blo 1636017 1637867 := bstep (se 1 (by rfl) ⟨1228400, by rfl⟩ : syracuseStep 1637867 = 2456801) B2456801
theorem B1637879 : Blo 1636017 1637879 := bstep (se 1 (by rfl) ⟨1228409, by rfl⟩ : syracuseStep 1637879 = 2456819) B2456819
theorem B1637899 : Blo 1636017 1637899 := bstep (se 1 (by rfl) ⟨1228424, by rfl⟩ : syracuseStep 1637899 = 2456849) B2456849
theorem B1637911 : Blo 1636017 1637911 := bstep (se 1 (by rfl) ⟨1228433, by rfl⟩ : syracuseStep 1637911 = 2456867) B2456867
theorem B1637931 : Blo 1636017 1637931 := bstep (se 1 (by rfl) ⟨1228448, by rfl⟩ : syracuseStep 1637931 = 2456897) B2456897
theorem B1637943 : Blo 1636017 1637943 := bstep (se 1 (by rfl) ⟨1228457, by rfl⟩ : syracuseStep 1637943 = 2456915) B2456915
theorem B5045825 : Blo 1636017 5045825 := bstep (se 2 (by rfl) ⟨1892184, by rfl⟩ : syracuseStep 5045825 = 3784369) B3784369
theorem B1637963 : Blo 1636017 1637963 := bstep (se 1 (by rfl) ⟨1228472, by rfl⟩ : syracuseStep 1637963 = 2456945) B2456945
theorem B1842763 : Blo 1636017 1842763 := bstep (se 1 (by rfl) ⟨1382072, by rfl⟩ : syracuseStep 1842763 = 2764145) B2764145
theorem B1637975 : Blo 1636017 1637975 := bstep (se 1 (by rfl) ⟨1228481, by rfl⟩ : syracuseStep 1637975 = 2456963) B2456963
theorem B2621017 : Blo 1636017 2621017 := bstep (se 2 (by rfl) ⟨982881, by rfl⟩ : syracuseStep 2621017 = 1965763) B1965763
theorem B4144729 : Blo 1636017 4144729 := bstep (se 2 (by rfl) ⟨1554273, by rfl⟩ : syracuseStep 4144729 = 3108547) B3108547
theorem B1637995 : Blo 1636017 1637995 := bstep (se 1 (by rfl) ⟨1228496, by rfl⟩ : syracuseStep 1637995 = 2456993) B2456993
theorem B3743347 : Blo 1636017 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B1638007 : Blo 1636017 1638007 := bstep (se 1 (by rfl) ⟨1228505, by rfl⟩ : syracuseStep 1638007 = 2457011) B2457011
theorem B7470913 : Blo 1636017 7470913 := bstep (se 2 (by rfl) ⟨2801592, by rfl⟩ : syracuseStep 7470913 = 5603185) B5603185
theorem B2072395 : Blo 1636017 2072395 := bstep (se 1 (by rfl) ⟨1554296, by rfl⟩ : syracuseStep 2072395 = 3108593) B3108593
theorem B7569325 : Blo 1636017 7569325 := bstep (se 3 (by rfl) ⟨1419248, by rfl⟩ : syracuseStep 7569325 = 2838497) B2838497
theorem B4145195 : Blo 1636017 4145195 := bstep (se 1 (by rfl) ⟨3108896, by rfl⟩ : syracuseStep 4145195 = 6217793) B6217793
theorem B3932219 : Blo 1636017 3932219 := bstep (se 1 (by rfl) ⟨2949164, by rfl⟩ : syracuseStep 3932219 = 5898329) B5898329
theorem B4661363 : Blo 1636017 4661363 := bstep (se 1 (by rfl) ⟨3496022, by rfl⟩ : syracuseStep 4661363 = 6992045) B6992045
theorem B2621575 : Blo 1636017 2621575 := bstep (se 1 (by rfl) ⟨1966181, by rfl⟩ : syracuseStep 2621575 = 3932363) B3932363
theorem B2072719 : Blo 1636017 2072719 := bstep (se 1 (by rfl) ⟨1554539, by rfl⟩ : syracuseStep 2072719 = 3109079) B3109079
theorem B2760905 : Blo 1636017 2760905 := bstep (se 2 (by rfl) ⟨1035339, by rfl⟩ : syracuseStep 2760905 = 2070679) B2070679
theorem B11796769 : Blo 1636017 11796769 := bstep (se 2 (by rfl) ⟨4423788, by rfl⟩ : syracuseStep 11796769 = 8847577) B8847577
theorem B2949409 : Blo 1636017 2949409 := bstep (se 2 (by rfl) ⟨1106028, by rfl⟩ : syracuseStep 2949409 = 2212057) B2212057
theorem B2072891 : Blo 1636017 2072891 := bstep (se 1 (by rfl) ⟨1554668, by rfl⟩ : syracuseStep 2072891 = 3109337) B3109337
theorem B16810375 : Blo 1636017 16810375 := bstep (se 1 (by rfl) ⟨12607781, by rfl⟩ : syracuseStep 16810375 = 25215563) B25215563
theorem B4661705 : Blo 1636017 4661705 := bstep (se 2 (by rfl) ⟨1748139, by rfl⟩ : syracuseStep 4661705 = 3496279) B3496279
theorem B5521931 : Blo 1636017 5521931 := bstep (se 1 (by rfl) ⟨4141448, by rfl⟩ : syracuseStep 5521931 = 8282897) B8282897
theorem B4661819 : Blo 1636017 4661819 := bstep (se 1 (by rfl) ⟨3496364, by rfl⟩ : syracuseStep 4661819 = 6992729) B6992729
theorem B6988355 : Blo 1636017 6988355 := bstep (se 1 (by rfl) ⟨5241266, by rfl⟩ : syracuseStep 6988355 = 10482533) B10482533
theorem B5522039 : Blo 1636017 5522039 := bstep (se 1 (by rfl) ⟨4141529, by rfl⟩ : syracuseStep 5522039 = 8283059) B8283059
theorem B4661945 : Blo 1636017 4661945 := bstep (se 2 (by rfl) ⟨1748229, by rfl⟩ : syracuseStep 4661945 = 3496459) B3496459
theorem B453485249 : Blo 1636017 453485249 := bstep (se 2 (by rfl) ⟨170056968, by rfl⟩ : syracuseStep 453485249 = 340113937) B340113937
theorem B15737561 : Blo 1636017 15737561 := bstep (se 2 (by rfl) ⟨5901585, by rfl⟩ : syracuseStep 15737561 = 11803171) B11803171
theorem B12296933 : Blo 1636017 12296933 := bstep (se 4 (by rfl) ⟨1152837, by rfl⟩ : syracuseStep 12296933 = 2305675) B2305675
theorem B6636269 : Blo 1636017 6636269 := bstep (se 3 (by rfl) ⟨1244300, by rfl⟩ : syracuseStep 6636269 = 2488601) B2488601
theorem B6218477 : Blo 1636017 6218477 := bstep (se 3 (by rfl) ⟨1165964, by rfl⟩ : syracuseStep 6218477 = 2331929) B2331929
theorem B10486529 : Blo 1636017 10486529 := bstep (se 2 (by rfl) ⟨3932448, by rfl⟩ : syracuseStep 10486529 = 7864897) B7864897
theorem B9960023 : Blo 1636017 9960023 := bstep (se 1 (by rfl) ⟨7470017, by rfl⟩ : syracuseStep 9960023 = 14940035) B14940035
theorem B2761607 : Blo 1636017 2761607 := bstep (se 1 (by rfl) ⟨2071205, by rfl⟩ : syracuseStep 2761607 = 4142411) B4142411
theorem B8397715 : Blo 1636017 8397715 := bstep (se 1 (by rfl) ⟨6298286, by rfl⟩ : syracuseStep 8397715 = 12596573) B12596573
theorem B4146187 : Blo 1636017 4146187 := bstep (se 1 (by rfl) ⟨3109640, by rfl⟩ : syracuseStep 4146187 = 6219281) B6219281
theorem B3933217 : Blo 1636017 3933217 := bstep (se 2 (by rfl) ⟨1474956, by rfl⟩ : syracuseStep 3933217 = 2949913) B2949913
theorem B6218795 : Blo 1636017 6218795 := bstep (se 1 (by rfl) ⟨4664096, by rfl⟩ : syracuseStep 6218795 = 9328193) B9328193
theorem B11199575 : Blo 1636017 11199575 := bstep (se 1 (by rfl) ⟨8399681, by rfl⟩ : syracuseStep 11199575 = 16799363) B16799363
theorem B8512705 : Blo 1636017 8512705 := bstep (se 2 (by rfl) ⟨3192264, by rfl⟩ : syracuseStep 8512705 = 6384529) B6384529
theorem B5522633 : Blo 1636017 5522633 := bstep (se 2 (by rfl) ⟨2070987, by rfl⟩ : syracuseStep 5522633 = 4141975) B4141975
theorem B8283545 : Blo 1636017 8283545 := bstep (se 2 (by rfl) ⟨3106329, by rfl⟩ : syracuseStep 8283545 = 6212659) B6212659
theorem B2762255 : Blo 1636017 2762255 := bstep (se 1 (by rfl) ⟨2071691, by rfl⟩ : syracuseStep 2762255 = 4143383) B4143383
theorem B19908125 : Blo 1636017 19908125 := bstep (se 3 (by rfl) ⟨3732773, by rfl⟩ : syracuseStep 19908125 = 7465547) B7465547
theorem B3106451 : Blo 1636017 3106451 := bstep (se 1 (by rfl) ⟨2329838, by rfl⟩ : syracuseStep 3106451 = 4659677) B4659677
theorem B3106505 : Blo 1636017 3106505 := bstep (se 2 (by rfl) ⟨1164939, by rfl⟩ : syracuseStep 3106505 = 2329879) B2329879
theorem B5596943 : Blo 1636017 5596943 := bstep (se 1 (by rfl) ⟨4197707, by rfl⟩ : syracuseStep 5596943 = 8395415) B8395415
theorem B13977359 : Blo 1636017 13977359 := bstep (se 1 (by rfl) ⟨10483019, by rfl⟩ : syracuseStep 13977359 = 20966039) B20966039
theorem B3106603 : Blo 1636017 3106603 := bstep (se 1 (by rfl) ⟨2329952, by rfl⟩ : syracuseStep 3106603 = 4659905) B4659905
theorem B5523335 : Blo 1636017 5523335 := bstep (se 1 (by rfl) ⟨4142501, by rfl⟩ : syracuseStep 5523335 = 8285003) B8285003
theorem B408487859 : Blo 1636017 408487859 := bstep (se 1 (by rfl) ⟨306365894, by rfl⟩ : syracuseStep 408487859 = 612731789) B612731789
theorem B3106831 : Blo 1636017 3106831 := bstep (se 1 (by rfl) ⟨2330123, by rfl⟩ : syracuseStep 3106831 = 4660247) B4660247
theorem B2762795 : Blo 1636017 2762795 := bstep (se 1 (by rfl) ⟨2072096, by rfl⟩ : syracuseStep 2762795 = 4144193) B4144193
theorem B11798615 : Blo 1636017 11798615 := bstep (se 1 (by rfl) ⟨8848961, by rfl⟩ : syracuseStep 11798615 = 17697923) B17697923
theorem B3934295 : Blo 1636017 3934295 := bstep (se 1 (by rfl) ⟨2950721, by rfl⟩ : syracuseStep 3934295 = 5901443) B5901443
theorem B4991129 : Blo 1636017 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B5523713 : Blo 1636017 5523713 := bstep (se 2 (by rfl) ⟨2071392, by rfl⟩ : syracuseStep 5523713 = 4142785) B4142785
theorem B4425995 : Blo 1636017 4425995 := bstep (se 1 (by rfl) ⟨3319496, by rfl⟩ : syracuseStep 4425995 = 6638993) B6638993
theorem B4663595 : Blo 1636017 4663595 := bstep (se 1 (by rfl) ⟨3497696, by rfl⟩ : syracuseStep 4663595 = 6995393) B6995393
theorem B13986107 : Blo 1636017 13986107 := bstep (se 1 (by rfl) ⟨10489580, by rfl⟩ : syracuseStep 13986107 = 20979161) B20979161
theorem B2763193 : Blo 1636017 2763193 := bstep (se 2 (by rfl) ⟨1036197, by rfl⟩ : syracuseStep 2763193 = 2072395) B2072395
theorem B9325003 : Blo 1636017 9325003 := bstep (se 1 (by rfl) ⟨6993752, by rfl⟩ : syracuseStep 9325003 = 13987505) B13987505
theorem B5245469 : Blo 1636017 5245469 := bstep (se 3 (by rfl) ⟨983525, by rfl⟩ : syracuseStep 5245469 = 1967051) B1967051
theorem B3935063 : Blo 1636017 3935063 := bstep (se 1 (by rfl) ⟨2951297, by rfl⟩ : syracuseStep 3935063 = 5902595) B5902595
theorem B3681143 : Blo 1636017 3681143 := bstep (se 1 (by rfl) ⟨2760857, by rfl⟩ : syracuseStep 3681143 = 5521715) B5521715
theorem B45419525 : Blo 1636017 45419525 := bstep (se 4 (by rfl) ⟨4258080, by rfl⟩ : syracuseStep 45419525 = 8516161) B8516161
theorem B3681323 : Blo 1636017 3681323 := bstep (se 1 (by rfl) ⟨2760992, by rfl⟩ : syracuseStep 3681323 = 5521985) B5521985
theorem B5524523 : Blo 1636017 5524523 := bstep (se 1 (by rfl) ⟨4143392, by rfl⟩ : syracuseStep 5524523 = 8286785) B8286785
theorem B2763895 : Blo 1636017 2763895 := bstep (se 1 (by rfl) ⟨2072921, by rfl⟩ : syracuseStep 2763895 = 4145843) B4145843
theorem B13978757 : Blo 1636017 13978757 := bstep (se 4 (by rfl) ⟨1310508, by rfl⟩ : syracuseStep 13978757 = 2621017) B2621017
theorem B2657551 : Blo 1636017 2657551 := bstep (se 1 (by rfl) ⟨1993163, by rfl⟩ : syracuseStep 2657551 = 3986327) B3986327
theorem B2764091 : Blo 1636017 2764091 := bstep (se 1 (by rfl) ⟨2073068, by rfl⟩ : syracuseStep 2764091 = 4146137) B4146137
theorem B2329975 : Blo 1636017 2329975 := bstep (se 1 (by rfl) ⟨1747481, by rfl⟩ : syracuseStep 2329975 = 3494963) B3494963
theorem B3681683 : Blo 1636017 3681683 := bstep (se 1 (by rfl) ⟨2761262, by rfl⟩ : syracuseStep 3681683 = 5522525) B5522525
theorem B3681737 : Blo 1636017 3681737 := bstep (se 2 (by rfl) ⟨1380651, by rfl⟩ : syracuseStep 3681737 = 2761303) B2761303
theorem B10489297 : Blo 1636017 10489297 := bstep (se 2 (by rfl) ⟨3933486, by rfl⟩ : syracuseStep 10489297 = 7866973) B7866973
theorem B19164625 : Blo 1636017 19164625 := bstep (se 2 (by rfl) ⟨7186734, by rfl⟩ : syracuseStep 19164625 = 14373469) B14373469
theorem B6213131 : Blo 1636017 6213131 := bstep (se 1 (by rfl) ⟨4659848, by rfl⟩ : syracuseStep 6213131 = 9319697) B9319697
theorem B3108395 : Blo 1636017 3108395 := bstep (se 1 (by rfl) ⟨2331296, by rfl⟩ : syracuseStep 3108395 = 4662593) B4662593
theorem B27962981 : Blo 1636017 27962981 := bstep (se 4 (by rfl) ⟨2621529, by rfl⟩ : syracuseStep 27962981 = 5243059) B5243059
theorem B181571507 : Blo 1636017 181571507 := bstep (se 1 (by rfl) ⟨136178630, by rfl⟩ : syracuseStep 181571507 = 272357261) B272357261
theorem B8286137 : Blo 1636017 8286137 := bstep (se 2 (by rfl) ⟨3107301, by rfl⟩ : syracuseStep 8286137 = 6214603) B6214603
theorem B2658233 : Blo 1636017 2658233 := bstep (se 2 (by rfl) ⟨996837, by rfl⟩ : syracuseStep 2658233 = 1993675) B1993675
theorem B6639545 : Blo 1636017 6639545 := bstep (se 2 (by rfl) ⟨2489829, by rfl⟩ : syracuseStep 6639545 = 4979659) B4979659
theorem B3682439 : Blo 1636017 3682439 := bstep (se 1 (by rfl) ⟨2761829, by rfl⟩ : syracuseStep 3682439 = 5523659) B5523659
theorem B13455533 : Blo 1636017 13455533 := bstep (se 3 (by rfl) ⟨2522912, by rfl⟩ : syracuseStep 13455533 = 5045825) B5045825
theorem B9318671 : Blo 1636017 9318671 := bstep (se 1 (by rfl) ⟨6989003, by rfl⟩ : syracuseStep 9318671 = 13978007) B13978007
theorem B4141327 : Blo 1636017 4141327 := bstep (se 1 (by rfl) ⟨3105995, by rfl⟩ : syracuseStep 4141327 = 6211991) B6211991
theorem B6639887 : Blo 1636017 6639887 := bstep (se 1 (by rfl) ⟨4979915, by rfl⟩ : syracuseStep 6639887 = 9959831) B9959831
theorem B3838223 : Blo 1636017 3838223 := bstep (se 1 (by rfl) ⟨2878667, by rfl⟩ : syracuseStep 3838223 = 5757335) B5757335
theorem B3682619 : Blo 1636017 3682619 := bstep (se 1 (by rfl) ⟨2761964, by rfl⟩ : syracuseStep 3682619 = 5523929) B5523929
theorem B5525819 : Blo 1636017 5525819 := bstep (se 1 (by rfl) ⟨4144364, by rfl⟩ : syracuseStep 5525819 = 8288729) B8288729
theorem B2331023 : Blo 1636017 2331023 := bstep (se 1 (by rfl) ⟨1748267, by rfl⟩ : syracuseStep 2331023 = 3496535) B3496535
theorem B7868819 : Blo 1636017 7868819 := bstep (se 1 (by rfl) ⟨5901614, by rfl⟩ : syracuseStep 7868819 = 11803229) B11803229
theorem B3682745 : Blo 1636017 3682745 := bstep (se 2 (by rfl) ⟨1381029, by rfl⟩ : syracuseStep 3682745 = 2762059) B2762059
theorem B4141601 : Blo 1636017 4141601 := bstep (se 2 (by rfl) ⟨1553100, by rfl⟩ : syracuseStep 4141601 = 3106201) B3106201
theorem B2454059 : Blo 1636017 2454059 := bstep (se 1 (by rfl) ⟨1840544, by rfl⟩ : syracuseStep 2454059 = 3681089) B3681089
theorem B7565885 : Blo 1636017 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B2454089 : Blo 1636017 2454089 := bstep (se 2 (by rfl) ⟨920283, by rfl⟩ : syracuseStep 2454089 = 1840567) B1840567
theorem B3494519 : Blo 1636017 3494519 := bstep (se 1 (by rfl) ⟨2620889, by rfl⟩ : syracuseStep 3494519 = 5241779) B5241779
theorem B2454203 : Blo 1636017 2454203 := bstep (se 1 (by rfl) ⟨1840652, by rfl⟩ : syracuseStep 2454203 = 3681305) B3681305
theorem B2331337 : Blo 1636017 2331337 := bstep (se 2 (by rfl) ⟨874251, by rfl⟩ : syracuseStep 2331337 = 1748503) B1748503
theorem B2454263 : Blo 1636017 2454263 := bstep (se 1 (by rfl) ⟨1840697, by rfl⟩ : syracuseStep 2454263 = 3681395) B3681395
theorem B2454287 : Blo 1636017 2454287 := bstep (se 1 (by rfl) ⟨1840715, by rfl⟩ : syracuseStep 2454287 = 3681431) B3681431
theorem B3683087 : Blo 1636017 3683087 := bstep (se 1 (by rfl) ⟨2762315, by rfl⟩ : syracuseStep 3683087 = 5524631) B5524631
theorem B3683105 : Blo 1636017 3683105 := bstep (se 2 (by rfl) ⟨1381164, by rfl⟩ : syracuseStep 3683105 = 2762329) B2762329
theorem B6386465 : Blo 1636017 6386465 := bstep (se 2 (by rfl) ⟨2394924, by rfl⟩ : syracuseStep 6386465 = 4789849) B4789849
theorem B5526305 : Blo 1636017 5526305 := bstep (se 2 (by rfl) ⟨2072364, by rfl⟩ : syracuseStep 5526305 = 4144729) B4144729
theorem B2454329 : Blo 1636017 2454329 := bstep (se 2 (by rfl) ⟨920373, by rfl⟩ : syracuseStep 2454329 = 1840747) B1840747
theorem B9327419 : Blo 1636017 9327419 := bstep (se 1 (by rfl) ⟨6995564, by rfl⟩ : syracuseStep 9327419 = 13991129) B13991129
theorem B2454407 : Blo 1636017 2454407 := bstep (se 1 (by rfl) ⟨1840805, by rfl⟩ : syracuseStep 2454407 = 3681611) B3681611
theorem B9958291 : Blo 1636017 9958291 := bstep (se 1 (by rfl) ⟨7468718, by rfl⟩ : syracuseStep 9958291 = 14937437) B14937437
theorem B11801497 : Blo 1636017 11801497 := bstep (se 2 (by rfl) ⟨4425561, by rfl⟩ : syracuseStep 11801497 = 8851123) B8851123
theorem B2454443 : Blo 1636017 2454443 := bstep (se 1 (by rfl) ⟨1840832, by rfl⟩ : syracuseStep 2454443 = 3681665) B3681665
theorem B2454473 : Blo 1636017 2454473 := bstep (se 2 (by rfl) ⟨920427, by rfl⟩ : syracuseStep 2454473 = 1840855) B1840855
theorem B2454587 : Blo 1636017 2454587 := bstep (se 1 (by rfl) ⟨1840940, by rfl⟩ : syracuseStep 2454587 = 3681881) B3681881
theorem B2454647 : Blo 1636017 2454647 := bstep (se 1 (by rfl) ⟨1840985, by rfl⟩ : syracuseStep 2454647 = 3681971) B3681971
theorem B3683447 : Blo 1636017 3683447 := bstep (se 1 (by rfl) ⟨2762585, by rfl⟩ : syracuseStep 3683447 = 5525171) B5525171
theorem B2454671 : Blo 1636017 2454671 := bstep (se 1 (by rfl) ⟨1841003, by rfl⟩ : syracuseStep 2454671 = 3682007) B3682007
theorem B16807085 : Blo 1636017 16807085 := bstep (se 3 (by rfl) ⟨3151328, by rfl⟩ : syracuseStep 16807085 = 6302657) B6302657
theorem B2454713 : Blo 1636017 2454713 := bstep (se 2 (by rfl) ⟨920517, by rfl⟩ : syracuseStep 2454713 = 1841035) B1841035
theorem B8287433 : Blo 1636017 8287433 := bstep (se 2 (by rfl) ⟨3107787, by rfl⟩ : syracuseStep 8287433 = 6215575) B6215575
theorem B2454791 : Blo 1636017 2454791 := bstep (se 1 (by rfl) ⟨1841093, by rfl⟩ : syracuseStep 2454791 = 3682187) B3682187
theorem B4977931 : Blo 1636017 4977931 := bstep (se 1 (by rfl) ⟨3733448, by rfl⟩ : syracuseStep 4977931 = 7466897) B7466897
theorem B10630433 : Blo 1636017 10630433 := bstep (se 2 (by rfl) ⟨3986412, by rfl⟩ : syracuseStep 10630433 = 7972825) B7972825
theorem B2454827 : Blo 1636017 2454827 := bstep (se 1 (by rfl) ⟨1841120, by rfl⟩ : syracuseStep 2454827 = 3682241) B3682241
theorem B3683627 : Blo 1636017 3683627 := bstep (se 1 (by rfl) ⟨2762720, by rfl⟩ : syracuseStep 3683627 = 5525441) B5525441
theorem B2454857 : Blo 1636017 2454857 := bstep (se 2 (by rfl) ⟨920571, by rfl⟩ : syracuseStep 2454857 = 1841143) B1841143
theorem B5526899 : Blo 1636017 5526899 := bstep (se 1 (by rfl) ⟨4145174, by rfl⟩ : syracuseStep 5526899 = 8290349) B8290349
theorem B17708473 : Blo 1636017 17708473 := bstep (se 2 (by rfl) ⟨6640677, by rfl⟩ : syracuseStep 17708473 = 13281355) B13281355
theorem B2454971 : Blo 1636017 2454971 := bstep (se 1 (by rfl) ⟨1841228, by rfl⟩ : syracuseStep 2454971 = 3682457) B3682457
theorem B2455031 : Blo 1636017 2455031 := bstep (se 1 (by rfl) ⟨1841273, by rfl⟩ : syracuseStep 2455031 = 3682547) B3682547
theorem B4142603 : Blo 1636017 4142603 := bstep (se 1 (by rfl) ⟨3106952, by rfl⟩ : syracuseStep 4142603 = 6213905) B6213905
theorem B2455055 : Blo 1636017 2455055 := bstep (se 1 (by rfl) ⟨1841291, by rfl⟩ : syracuseStep 2455055 = 3682583) B3682583
theorem B2242091 : Blo 1636017 2242091 := bstep (se 1 (by rfl) ⟨1681568, by rfl⟩ : syracuseStep 2242091 = 3363137) B3363137
theorem B13989419 : Blo 1636017 13989419 := bstep (se 1 (by rfl) ⟨10492064, by rfl⟩ : syracuseStep 13989419 = 20984129) B20984129
theorem B2455097 : Blo 1636017 2455097 := bstep (se 2 (by rfl) ⟨920661, by rfl⟩ : syracuseStep 2455097 = 1841323) B1841323
theorem B2455175 : Blo 1636017 2455175 := bstep (se 1 (by rfl) ⟨1841381, by rfl⟩ : syracuseStep 2455175 = 3682763) B3682763
theorem B1840783 : Blo 1636017 1840783 := bstep (se 1 (by rfl) ⟨1380587, by rfl⟩ : syracuseStep 1840783 = 2761175) B2761175
theorem B3683987 : Blo 1636017 3683987 := bstep (se 1 (by rfl) ⟨2762990, by rfl⟩ : syracuseStep 3683987 = 5525981) B5525981
theorem B2455211 : Blo 1636017 2455211 := bstep (se 1 (by rfl) ⟨1841408, by rfl⟩ : syracuseStep 2455211 = 3682817) B3682817
theorem B23025329 : Blo 1636017 23025329 := bstep (se 2 (by rfl) ⟨8634498, by rfl⟩ : syracuseStep 23025329 = 17268997) B17268997
theorem B26564273 : Blo 1636017 26564273 := bstep (se 2 (by rfl) ⟨9961602, by rfl⟩ : syracuseStep 26564273 = 19923205) B19923205
theorem B1636027 : Blo 1636017 1636027 := bstep (se 1 (by rfl) ⟨1227020, by rfl⟩ : syracuseStep 1636027 = 2454041) B2454041
theorem B9320129 : Blo 1636017 9320129 := bstep (se 2 (by rfl) ⟨3495048, by rfl⟩ : syracuseStep 9320129 = 6990097) B6990097
theorem B2455241 : Blo 1636017 2455241 := bstep (se 2 (by rfl) ⟨920715, by rfl⟩ : syracuseStep 2455241 = 1841431) B1841431
theorem B3684041 : Blo 1636017 3684041 := bstep (se 2 (by rfl) ⟨1381515, by rfl⟩ : syracuseStep 3684041 = 2763031) B2763031
theorem B1636103 : Blo 1636017 1636103 := bstep (se 1 (by rfl) ⟨1227077, by rfl⟩ : syracuseStep 1636103 = 2454155) B2454155
theorem B1636111 : Blo 1636017 1636111 := bstep (se 1 (by rfl) ⟨1227083, by rfl⟩ : syracuseStep 1636111 = 2454167) B2454167
theorem B1636155 : Blo 1636017 1636155 := bstep (se 1 (by rfl) ⟨1227116, by rfl⟩ : syracuseStep 1636155 = 2454233) B2454233
theorem B2455355 : Blo 1636017 2455355 := bstep (se 1 (by rfl) ⟨1841516, by rfl⟩ : syracuseStep 2455355 = 3683033) B3683033
theorem B12425075 : Blo 1636017 12425075 := bstep (se 1 (by rfl) ⟨9318806, by rfl⟩ : syracuseStep 12425075 = 18637613) B18637613
theorem B2455415 : Blo 1636017 2455415 := bstep (se 1 (by rfl) ⟨1841561, by rfl⟩ : syracuseStep 2455415 = 3683123) B3683123
theorem B1636231 : Blo 1636017 1636231 := bstep (se 1 (by rfl) ⟨1227173, by rfl⟩ : syracuseStep 1636231 = 2454347) B2454347
theorem B1636239 : Blo 1636017 1636239 := bstep (se 1 (by rfl) ⟨1227179, by rfl⟩ : syracuseStep 1636239 = 2454359) B2454359
theorem B2455439 : Blo 1636017 2455439 := bstep (se 1 (by rfl) ⟨1841579, by rfl⟩ : syracuseStep 2455439 = 3683159) B3683159
theorem B2455481 : Blo 1636017 2455481 := bstep (se 2 (by rfl) ⟨920805, by rfl⟩ : syracuseStep 2455481 = 1841611) B1841611
theorem B1636283 : Blo 1636017 1636283 := bstep (se 1 (by rfl) ⟨1227212, by rfl⟩ : syracuseStep 1636283 = 2454425) B2454425
theorem B1636359 : Blo 1636017 1636359 := bstep (se 1 (by rfl) ⟨1227269, by rfl⟩ : syracuseStep 1636359 = 2454539) B2454539
theorem B2455559 : Blo 1636017 2455559 := bstep (se 1 (by rfl) ⟨1841669, by rfl⟩ : syracuseStep 2455559 = 3683339) B3683339
theorem B1636367 : Blo 1636017 1636367 := bstep (se 1 (by rfl) ⟨1227275, by rfl⟩ : syracuseStep 1636367 = 2454551) B2454551
theorem B2455595 : Blo 1636017 2455595 := bstep (se 1 (by rfl) ⟨1841696, by rfl⟩ : syracuseStep 2455595 = 3683393) B3683393
theorem B1636411 : Blo 1636017 1636411 := bstep (se 1 (by rfl) ⟨1227308, by rfl⟩ : syracuseStep 1636411 = 2454617) B2454617
theorem B2455625 : Blo 1636017 2455625 := bstep (se 2 (by rfl) ⟨920859, by rfl⟩ : syracuseStep 2455625 = 1841719) B1841719
theorem B1636487 : Blo 1636017 1636487 := bstep (se 1 (by rfl) ⟨1227365, by rfl⟩ : syracuseStep 1636487 = 2454731) B2454731
theorem B1841287 : Blo 1636017 1841287 := bstep (se 1 (by rfl) ⟨1380965, by rfl⟩ : syracuseStep 1841287 = 2761931) B2761931
theorem B1636495 : Blo 1636017 1636495 := bstep (se 1 (by rfl) ⟨1227371, by rfl⟩ : syracuseStep 1636495 = 2454743) B2454743
theorem B4143251 : Blo 1636017 4143251 := bstep (se 1 (by rfl) ⟨3107438, by rfl⟩ : syracuseStep 4143251 = 6214877) B6214877
theorem B1636539 : Blo 1636017 1636539 := bstep (se 1 (by rfl) ⟨1227404, by rfl⟩ : syracuseStep 1636539 = 2454809) B2454809
theorem B2455739 : Blo 1636017 2455739 := bstep (se 1 (by rfl) ⟨1841804, by rfl⟩ : syracuseStep 2455739 = 3683609) B3683609
theorem B9328877 : Blo 1636017 9328877 := bstep (se 3 (by rfl) ⟨1749164, by rfl⟩ : syracuseStep 9328877 = 3498329) B3498329
theorem B2070775 : Blo 1636017 2070775 := bstep (se 1 (by rfl) ⟨1553081, by rfl⟩ : syracuseStep 2070775 = 3106163) B3106163
theorem B2455799 : Blo 1636017 2455799 := bstep (se 1 (by rfl) ⟨1841849, by rfl⟩ : syracuseStep 2455799 = 3683699) B3683699
theorem B1636615 : Blo 1636017 1636615 := bstep (se 1 (by rfl) ⟨1227461, by rfl⟩ : syracuseStep 1636615 = 2454923) B2454923
theorem B1636623 : Blo 1636017 1636623 := bstep (se 1 (by rfl) ⟨1227467, by rfl⟩ : syracuseStep 1636623 = 2454935) B2454935
theorem B2455823 : Blo 1636017 2455823 := bstep (se 1 (by rfl) ⟨1841867, by rfl⟩ : syracuseStep 2455823 = 3683735) B3683735
theorem B2455865 : Blo 1636017 2455865 := bstep (se 2 (by rfl) ⟨920949, by rfl⟩ : syracuseStep 2455865 = 1841899) B1841899
theorem B1636667 : Blo 1636017 1636667 := bstep (se 1 (by rfl) ⟨1227500, by rfl⟩ : syracuseStep 1636667 = 2455001) B2455001
theorem B1841467 : Blo 1636017 1841467 := bstep (se 1 (by rfl) ⟨1381100, by rfl⟩ : syracuseStep 1841467 = 2762201) B2762201
theorem B1636743 : Blo 1636017 1636743 := bstep (se 1 (by rfl) ⟨1227557, by rfl⟩ : syracuseStep 1636743 = 2455115) B2455115
theorem B2455943 : Blo 1636017 2455943 := bstep (se 1 (by rfl) ⟨1841957, by rfl⟩ : syracuseStep 2455943 = 3683915) B3683915
theorem B3684743 : Blo 1636017 3684743 := bstep (se 1 (by rfl) ⟨2763557, by rfl⟩ : syracuseStep 3684743 = 5527115) B5527115
theorem B1636751 : Blo 1636017 1636751 := bstep (se 1 (by rfl) ⟨1227563, by rfl⟩ : syracuseStep 1636751 = 2455127) B2455127
theorem B2488747 : Blo 1636017 2488747 := bstep (se 1 (by rfl) ⟨1866560, by rfl⟩ : syracuseStep 2488747 = 3733121) B3733121
theorem B2455979 : Blo 1636017 2455979 := bstep (se 1 (by rfl) ⟨1841984, by rfl⟩ : syracuseStep 2455979 = 3683969) B3683969
theorem B4143545 : Blo 1636017 4143545 := bstep (se 2 (by rfl) ⟨1553829, by rfl⟩ : syracuseStep 4143545 = 3107659) B3107659
theorem B1636795 : Blo 1636017 1636795 := bstep (se 1 (by rfl) ⟨1227596, by rfl⟩ : syracuseStep 1636795 = 2455193) B2455193
theorem B2456009 : Blo 1636017 2456009 := bstep (se 2 (by rfl) ⟨921003, by rfl⟩ : syracuseStep 2456009 = 1842007) B1842007
theorem B1636871 : Blo 1636017 1636871 := bstep (se 1 (by rfl) ⟨1227653, by rfl⟩ : syracuseStep 1636871 = 2455307) B2455307
theorem B1636879 : Blo 1636017 1636879 := bstep (se 1 (by rfl) ⟨1227659, by rfl⟩ : syracuseStep 1636879 = 2455319) B2455319
theorem B7469597 : Blo 1636017 7469597 := bstep (se 3 (by rfl) ⟨1400549, by rfl⟩ : syracuseStep 7469597 = 2801099) B2801099
theorem B11205163 : Blo 1636017 11205163 := bstep (se 1 (by rfl) ⟨8403872, by rfl⟩ : syracuseStep 11205163 = 16807745) B16807745
theorem B2071099 : Blo 1636017 2071099 := bstep (se 1 (by rfl) ⟨1553324, by rfl⟩ : syracuseStep 2071099 = 3106649) B3106649
theorem B1636923 : Blo 1636017 1636923 := bstep (se 1 (by rfl) ⟨1227692, by rfl⟩ : syracuseStep 1636923 = 2455385) B2455385
theorem B2456123 : Blo 1636017 2456123 := bstep (se 1 (by rfl) ⟨1842092, by rfl⟩ : syracuseStep 2456123 = 3684185) B3684185
theorem B3684923 : Blo 1636017 3684923 := bstep (se 1 (by rfl) ⟨2763692, by rfl⟩ : syracuseStep 3684923 = 5527385) B5527385
theorem B2456183 : Blo 1636017 2456183 := bstep (se 1 (by rfl) ⟨1842137, by rfl⟩ : syracuseStep 2456183 = 3684275) B3684275
theorem B1636999 : Blo 1636017 1636999 := bstep (se 1 (by rfl) ⟨1227749, by rfl⟩ : syracuseStep 1636999 = 2455499) B2455499
theorem B1637007 : Blo 1636017 1637007 := bstep (se 1 (by rfl) ⟨1227755, by rfl⟩ : syracuseStep 1637007 = 2455511) B2455511
theorem B2456207 : Blo 1636017 2456207 := bstep (se 1 (by rfl) ⟨1842155, by rfl⟩ : syracuseStep 2456207 = 3684311) B3684311
theorem B4659859 : Blo 1636017 4659859 := bstep (se 1 (by rfl) ⟨3494894, by rfl⟩ : syracuseStep 4659859 = 6989789) B6989789
theorem B2456249 : Blo 1636017 2456249 := bstep (se 2 (by rfl) ⟨921093, by rfl⟩ : syracuseStep 2456249 = 1842187) B1842187
theorem B3685049 : Blo 1636017 3685049 := bstep (se 2 (by rfl) ⟨1381893, by rfl⟩ : syracuseStep 3685049 = 2763787) B2763787
theorem B1637051 : Blo 1636017 1637051 := bstep (se 1 (by rfl) ⟨1227788, by rfl⟩ : syracuseStep 1637051 = 2455577) B2455577
theorem B2489033 : Blo 1636017 2489033 := bstep (se 2 (by rfl) ⟨933387, by rfl⟩ : syracuseStep 2489033 = 1866775) B1866775
theorem B143538893 : Blo 1636017 143538893 := bstep (se 3 (by rfl) ⟨26913542, by rfl⟩ : syracuseStep 143538893 = 53827085) B53827085
theorem B1637127 : Blo 1636017 1637127 := bstep (se 1 (by rfl) ⟨1227845, by rfl⟩ : syracuseStep 1637127 = 2455691) B2455691
theorem B2456327 : Blo 1636017 2456327 := bstep (se 1 (by rfl) ⟨1842245, by rfl⟩ : syracuseStep 2456327 = 3684491) B3684491
theorem B1637135 : Blo 1636017 1637135 := bstep (se 1 (by rfl) ⟨1227851, by rfl⟩ : syracuseStep 1637135 = 2455703) B2455703
theorem B1841935 : Blo 1636017 1841935 := bstep (se 1 (by rfl) ⟨1381451, by rfl⟩ : syracuseStep 1841935 = 2762903) B2762903
theorem B2456363 : Blo 1636017 2456363 := bstep (se 1 (by rfl) ⟨1842272, by rfl⟩ : syracuseStep 2456363 = 3684545) B3684545
theorem B1637179 : Blo 1636017 1637179 := bstep (se 1 (by rfl) ⟨1227884, by rfl⟩ : syracuseStep 1637179 = 2455769) B2455769
theorem B2456393 : Blo 1636017 2456393 := bstep (se 2 (by rfl) ⟨921147, by rfl⟩ : syracuseStep 2456393 = 1842295) B1842295
theorem B4660087 : Blo 1636017 4660087 := bstep (se 1 (by rfl) ⟨3495065, by rfl⟩ : syracuseStep 4660087 = 6990131) B6990131
theorem B1637255 : Blo 1636017 1637255 := bstep (se 1 (by rfl) ⟨1227941, by rfl⟩ : syracuseStep 1637255 = 2455883) B2455883
theorem B1637263 : Blo 1636017 1637263 := bstep (se 1 (by rfl) ⟨1227947, by rfl⟩ : syracuseStep 1637263 = 2455895) B2455895
theorem B1637307 : Blo 1636017 1637307 := bstep (se 1 (by rfl) ⟨1227980, by rfl⟩ : syracuseStep 1637307 = 2455961) B2455961
theorem B2456507 : Blo 1636017 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B8395741 : Blo 1636017 8395741 := bstep (se 3 (by rfl) ⟨1574201, by rfl⟩ : syracuseStep 8395741 = 3148403) B3148403
theorem B2456567 : Blo 1636017 2456567 := bstep (se 1 (by rfl) ⟨1842425, by rfl⟩ : syracuseStep 2456567 = 3684851) B3684851
theorem B1637383 : Blo 1636017 1637383 := bstep (se 1 (by rfl) ⟨1228037, by rfl⟩ : syracuseStep 1637383 = 2456075) B2456075
theorem B1637391 : Blo 1636017 1637391 := bstep (se 1 (by rfl) ⟨1228043, by rfl⟩ : syracuseStep 1637391 = 2456087) B2456087
theorem B2456591 : Blo 1636017 2456591 := bstep (se 1 (by rfl) ⟨1842443, by rfl⟩ : syracuseStep 2456591 = 3684887) B3684887
theorem B3685391 : Blo 1636017 3685391 := bstep (se 1 (by rfl) ⟨2764043, by rfl⟩ : syracuseStep 3685391 = 5528087) B5528087
theorem B3685409 : Blo 1636017 3685409 := bstep (se 2 (by rfl) ⟨1382028, by rfl⟩ : syracuseStep 3685409 = 2764057) B2764057
theorem B2071595 : Blo 1636017 2071595 := bstep (se 1 (by rfl) ⟨1553696, by rfl⟩ : syracuseStep 2071595 = 3107393) B3107393
theorem B2456633 : Blo 1636017 2456633 := bstep (se 2 (by rfl) ⟨921237, by rfl⟩ : syracuseStep 2456633 = 1842475) B1842475
theorem B1637435 : Blo 1636017 1637435 := bstep (se 1 (by rfl) ⟨1228076, by rfl⟩ : syracuseStep 1637435 = 2456153) B2456153
theorem B4144243 : Blo 1636017 4144243 := bstep (se 1 (by rfl) ⟨3108182, by rfl⟩ : syracuseStep 4144243 = 6216365) B6216365
theorem B1637511 : Blo 1636017 1637511 := bstep (se 1 (by rfl) ⟨1228133, by rfl⟩ : syracuseStep 1637511 = 2456267) B2456267
theorem B2456711 : Blo 1636017 2456711 := bstep (se 1 (by rfl) ⟨1842533, by rfl⟩ : syracuseStep 2456711 = 3685067) B3685067
theorem B1637519 : Blo 1636017 1637519 := bstep (se 1 (by rfl) ⟨1228139, by rfl⟩ : syracuseStep 1637519 = 2456279) B2456279
theorem B2456747 : Blo 1636017 2456747 := bstep (se 1 (by rfl) ⟨1842560, by rfl⟩ : syracuseStep 2456747 = 3685121) B3685121
theorem B1637563 : Blo 1636017 1637563 := bstep (se 1 (by rfl) ⟨1228172, by rfl⟩ : syracuseStep 1637563 = 2456345) B2456345
theorem B2456777 : Blo 1636017 2456777 := bstep (se 2 (by rfl) ⟨921291, by rfl⟩ : syracuseStep 2456777 = 1842583) B1842583
theorem B4144385 : Blo 1636017 4144385 := bstep (se 2 (by rfl) ⟨1554144, by rfl⟩ : syracuseStep 4144385 = 3108289) B3108289
theorem B1637639 : Blo 1636017 1637639 := bstep (se 1 (by rfl) ⟨1228229, by rfl⟩ : syracuseStep 1637639 = 2456459) B2456459
theorem B1842439 : Blo 1636017 1842439 := bstep (se 1 (by rfl) ⟨1381829, by rfl⟩ : syracuseStep 1842439 = 2763659) B2763659
theorem B1637647 : Blo 1636017 1637647 := bstep (se 1 (by rfl) ⟨1228235, by rfl⟩ : syracuseStep 1637647 = 2456471) B2456471
theorem B6217019 : Blo 1636017 6217019 := bstep (se 1 (by rfl) ⟨4662764, by rfl⟩ : syracuseStep 6217019 = 9325529) B9325529
theorem B1637691 : Blo 1636017 1637691 := bstep (se 1 (by rfl) ⟨1228268, by rfl⟩ : syracuseStep 1637691 = 2456537) B2456537
theorem B2456891 : Blo 1636017 2456891 := bstep (se 1 (by rfl) ⟨1842668, by rfl⟩ : syracuseStep 2456891 = 3685337) B3685337
theorem B9952627 : Blo 1636017 9952627 := bstep (se 1 (by rfl) ⟨7464470, by rfl⟩ : syracuseStep 9952627 = 14928941) B14928941
theorem B2456951 : Blo 1636017 2456951 := bstep (se 1 (by rfl) ⟨1842713, by rfl⟩ : syracuseStep 2456951 = 3685427) B3685427
theorem B1637767 : Blo 1636017 1637767 := bstep (se 1 (by rfl) ⟨1228325, by rfl⟩ : syracuseStep 1637767 = 2456651) B2456651
theorem B1637775 : Blo 1636017 1637775 := bstep (se 1 (by rfl) ⟨1228331, by rfl⟩ : syracuseStep 1637775 = 2456663) B2456663
theorem B2456975 : Blo 1636017 2456975 := bstep (se 1 (by rfl) ⟨1842731, by rfl⟩ : syracuseStep 2456975 = 3685463) B3685463
theorem B2457017 : Blo 1636017 2457017 := bstep (se 2 (by rfl) ⟨921381, by rfl⟩ : syracuseStep 2457017 = 1842763) B1842763
theorem B1637819 : Blo 1636017 1637819 := bstep (se 1 (by rfl) ⟨1228364, by rfl⟩ : syracuseStep 1637819 = 2456729) B2456729
theorem B1842619 : Blo 1636017 1842619 := bstep (se 1 (by rfl) ⟨1381964, by rfl⟩ : syracuseStep 1842619 = 2763929) B2763929
theorem B8404445 : Blo 1636017 8404445 := bstep (se 3 (by rfl) ⟨1575833, by rfl⟩ : syracuseStep 8404445 = 3151667) B3151667
theorem B2072071 : Blo 1636017 2072071 := bstep (se 1 (by rfl) ⟨1554053, by rfl⟩ : syracuseStep 2072071 = 3108107) B3108107
theorem B1637895 : Blo 1636017 1637895 := bstep (se 1 (by rfl) ⟨1228421, by rfl⟩ : syracuseStep 1637895 = 2456843) B2456843
theorem B1637903 : Blo 1636017 1637903 := bstep (se 1 (by rfl) ⟨1228427, by rfl⟩ : syracuseStep 1637903 = 2456855) B2456855
theorem B1637947 : Blo 1636017 1637947 := bstep (se 1 (by rfl) ⟨1228460, by rfl⟩ : syracuseStep 1637947 = 2456921) B2456921
theorem B4144841 : Blo 1636017 4144841 := bstep (se 2 (by rfl) ⟨1554315, by rfl⟩ : syracuseStep 4144841 = 3108631) B3108631
theorem B9961217 : Blo 1636017 9961217 := bstep (se 2 (by rfl) ⟨3735456, by rfl⟩ : syracuseStep 9961217 = 7470913) B7470913
theorem B6217505 : Blo 1636017 6217505 := bstep (se 2 (by rfl) ⟨2331564, by rfl⟩ : syracuseStep 6217505 = 4663129) B4663129
theorem B10092433 : Blo 1636017 10092433 := bstep (se 2 (by rfl) ⟨3784662, by rfl⟩ : syracuseStep 10092433 = 7569325) B7569325
theorem B2072567 : Blo 1636017 2072567 := bstep (se 1 (by rfl) ⟨1554425, by rfl⟩ : syracuseStep 2072567 = 3108851) B3108851
theorem B2621479 : Blo 1636017 2621479 := bstep (se 1 (by rfl) ⟨1966109, by rfl⟩ : syracuseStep 2621479 = 3932219) B3932219
theorem B8970355 : Blo 1636017 8970355 := bstep (se 1 (by rfl) ⟨6727766, by rfl⟩ : syracuseStep 8970355 = 13455533) B13455533
theorem B2761033 : Blo 1636017 2761033 := bstep (se 2 (by rfl) ⟨1035387, by rfl⟩ : syracuseStep 2761033 = 2070775) B2070775
theorem B5521769 : Blo 1636017 5521769 := bstep (se 2 (by rfl) ⟨2070663, by rfl⟩ : syracuseStep 5521769 = 4141327) B4141327
theorem B2761067 : Blo 1636017 2761067 := bstep (se 1 (by rfl) ⟨2070800, by rfl⟩ : syracuseStep 2761067 = 4141601) B4141601
theorem B15729025 : Blo 1636017 15729025 := bstep (se 2 (by rfl) ⟨5898384, by rfl⟩ : syracuseStep 15729025 = 11796769) B11796769
theorem B3932545 : Blo 1636017 3932545 := bstep (se 2 (by rfl) ⟨1474704, by rfl⟩ : syracuseStep 3932545 = 2949409) B2949409
theorem B4424179 : Blo 1636017 4424179 := bstep (se 1 (by rfl) ⟨3318134, by rfl⟩ : syracuseStep 4424179 = 6636269) B6636269
theorem B4145651 : Blo 1636017 4145651 := bstep (se 1 (by rfl) ⟨3109238, by rfl⟩ : syracuseStep 4145651 = 6218477) B6218477
theorem B22413833 : Blo 1636017 22413833 := bstep (se 2 (by rfl) ⟨8405187, by rfl⟩ : syracuseStep 22413833 = 16810375) B16810375
theorem B6218279 : Blo 1636017 6218279 := bstep (se 1 (by rfl) ⟨4663709, by rfl⟩ : syracuseStep 6218279 = 9327419) B9327419
theorem B3318329 : Blo 1636017 3318329 := bstep (se 2 (by rfl) ⟨1244373, by rfl⟩ : syracuseStep 3318329 = 2488747) B2488747
theorem B4145863 : Blo 1636017 4145863 := bstep (se 1 (by rfl) ⟨3109397, by rfl⟩ : syracuseStep 4145863 = 6218795) B6218795
theorem B2761465 : Blo 1636017 2761465 := bstep (se 2 (by rfl) ⟨1035549, by rfl⟩ : syracuseStep 2761465 = 2071099) B2071099
theorem B12436253 : Blo 1636017 12436253 := bstep (se 3 (by rfl) ⟨2331797, by rfl⟩ : syracuseStep 12436253 = 4663595) B4663595
theorem B7086955 : Blo 1636017 7086955 := bstep (se 1 (by rfl) ⟨5315216, by rfl⟩ : syracuseStep 7086955 = 10630433) B10630433
theorem B5522363 : Blo 1636017 5522363 := bstep (se 1 (by rfl) ⟨4141772, by rfl⟩ : syracuseStep 5522363 = 8283545) B8283545
theorem B2761735 : Blo 1636017 2761735 := bstep (se 1 (by rfl) ⟨2071301, by rfl⟩ : syracuseStep 2761735 = 4142603) B4142603
theorem B13272083 : Blo 1636017 13272083 := bstep (se 1 (by rfl) ⟨9954062, by rfl⟩ : syracuseStep 13272083 = 19908125) B19908125
theorem B8283383 : Blo 1636017 8283383 := bstep (se 1 (by rfl) ⟨6212537, by rfl⟩ : syracuseStep 8283383 = 12425075) B12425075
theorem B7865743 : Blo 1636017 7865743 := bstep (se 1 (by rfl) ⟨5899307, by rfl⟩ : syracuseStep 7865743 = 11798615) B11798615
theorem B2622863 : Blo 1636017 2622863 := bstep (se 1 (by rfl) ⟨1967147, by rfl⟩ : syracuseStep 2622863 = 3934295) B3934295
theorem B2762167 : Blo 1636017 2762167 := bstep (se 1 (by rfl) ⟨2071625, by rfl⟩ : syracuseStep 2762167 = 4143251) B4143251
theorem B3327419 : Blo 1636017 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B6219251 : Blo 1636017 6219251 := bstep (se 1 (by rfl) ⟨4664438, by rfl⟩ : syracuseStep 6219251 = 9328877) B9328877
theorem B2950663 : Blo 1636017 2950663 := bstep (se 1 (by rfl) ⟨2212997, by rfl⟩ : syracuseStep 2950663 = 4425995) B4425995
theorem B9324071 : Blo 1636017 9324071 := bstep (se 1 (by rfl) ⟨6993053, by rfl⟩ : syracuseStep 9324071 = 13986107) B13986107
theorem B2762363 : Blo 1636017 2762363 := bstep (se 1 (by rfl) ⟨2071772, by rfl⟩ : syracuseStep 2762363 = 4143545) B4143545
theorem B6637241 : Blo 1636017 6637241 := bstep (se 2 (by rfl) ⟨2488965, by rfl⟩ : syracuseStep 6637241 = 4977931) B4977931
theorem B8283869 : Blo 1636017 8283869 := bstep (se 3 (by rfl) ⟨1553225, by rfl⟩ : syracuseStep 8283869 = 3106451) B3106451
theorem B95692595 : Blo 1636017 95692595 := bstep (se 1 (by rfl) ⟨71769446, by rfl⟩ : syracuseStep 95692595 = 143538893) B143538893
theorem B2623375 : Blo 1636017 2623375 := bstep (se 1 (by rfl) ⟨1967531, by rfl⟩ : syracuseStep 2623375 = 3935063) B3935063
theorem B23611297 : Blo 1636017 23611297 := bstep (se 2 (by rfl) ⟨8854236, by rfl⟩ : syracuseStep 23611297 = 17708473) B17708473
theorem B13985729 : Blo 1636017 13985729 := bstep (se 2 (by rfl) ⟨5244648, by rfl⟩ : syracuseStep 13985729 = 10489297) B10489297
theorem B30279683 : Blo 1636017 30279683 := bstep (se 1 (by rfl) ⟨22709762, by rfl⟩ : syracuseStep 30279683 = 45419525) B45419525
theorem B2762761 : Blo 1636017 2762761 := bstep (se 2 (by rfl) ⟨1036035, by rfl⟩ : syracuseStep 2762761 = 2072071) B2072071
theorem B53110885 : Blo 1636017 53110885 := bstep (se 4 (by rfl) ⟨4979145, by rfl⟩ : syracuseStep 53110885 = 9958291) B9958291
theorem B2762923 : Blo 1636017 2762923 := bstep (se 1 (by rfl) ⟨2072192, by rfl⟩ : syracuseStep 2762923 = 4144385) B4144385
theorem B2763227 : Blo 1636017 2763227 := bstep (se 1 (by rfl) ⟨2072420, by rfl⟩ : syracuseStep 2763227 = 4144841) B4144841
theorem B121047671 : Blo 1636017 121047671 := bstep (se 1 (by rfl) ⟨90785753, by rfl⟩ : syracuseStep 121047671 = 181571507) B181571507
theorem B5524091 : Blo 1636017 5524091 := bstep (se 1 (by rfl) ⟨4143068, by rfl⟩ : syracuseStep 5524091 = 8286137) B8286137
theorem B1772155 : Blo 1636017 1772155 := bstep (se 1 (by rfl) ⟨1329116, by rfl⟩ : syracuseStep 1772155 = 2658233) B2658233
theorem B4426363 : Blo 1636017 4426363 := bstep (se 1 (by rfl) ⟨3319772, by rfl⟩ : syracuseStep 4426363 = 6639545) B6639545
theorem B2763463 : Blo 1636017 2763463 := bstep (se 1 (by rfl) ⟨2072597, by rfl⟩ : syracuseStep 2763463 = 4145195) B4145195
theorem B3107575 : Blo 1636017 3107575 := bstep (se 1 (by rfl) ⟨2330681, by rfl⟩ : syracuseStep 3107575 = 4661363) B4661363
theorem B5524253 : Blo 1636017 5524253 := bstep (se 3 (by rfl) ⟨1035797, by rfl⟩ : syracuseStep 5524253 = 2071595) B2071595
theorem B6212447 : Blo 1636017 6212447 := bstep (se 1 (by rfl) ⟨4659335, by rfl⟩ : syracuseStep 6212447 = 9318671) B9318671
theorem B4426591 : Blo 1636017 4426591 := bstep (se 1 (by rfl) ⟨3319943, by rfl⟩ : syracuseStep 4426591 = 6639887) B6639887
theorem B2763625 : Blo 1636017 2763625 := bstep (se 2 (by rfl) ⟨1036359, by rfl⟩ : syracuseStep 2763625 = 2072719) B2072719
theorem B5245879 : Blo 1636017 5245879 := bstep (se 1 (by rfl) ⟨3934409, by rfl⟩ : syracuseStep 5245879 = 7868819) B7868819
theorem B3107803 : Blo 1636017 3107803 := bstep (se 1 (by rfl) ⟨2330852, by rfl⟩ : syracuseStep 3107803 = 4661705) B4661705
theorem B3681287 : Blo 1636017 3681287 := bstep (se 1 (by rfl) ⟨2760965, by rfl⟩ : syracuseStep 3681287 = 5521931) B5521931
theorem B3107879 : Blo 1636017 3107879 := bstep (se 1 (by rfl) ⟨2330909, by rfl⟩ : syracuseStep 3107879 = 4661819) B4661819
theorem B3681359 : Blo 1636017 3681359 := bstep (se 1 (by rfl) ⟨2761019, by rfl⟩ : syracuseStep 3681359 = 5522039) B5522039
theorem B2329679 : Blo 1636017 2329679 := bstep (se 1 (by rfl) ⟨1747259, by rfl⟩ : syracuseStep 2329679 = 3494519) B3494519
theorem B3107963 : Blo 1636017 3107963 := bstep (se 1 (by rfl) ⟨2330972, by rfl⟩ : syracuseStep 3107963 = 4661945) B4661945
theorem B6991019 : Blo 1636017 6991019 := bstep (se 1 (by rfl) ⟨5243264, by rfl⟩ : syracuseStep 6991019 = 10486529) B10486529
theorem B10235261 : Blo 1636017 10235261 := bstep (se 3 (by rfl) ⟨1919111, by rfl⟩ : syracuseStep 10235261 = 3838223) B3838223
theorem B7466383 : Blo 1636017 7466383 := bstep (se 1 (by rfl) ⟨5599787, by rfl⟩ : syracuseStep 7466383 = 11199575) B11199575
theorem B3681755 : Blo 1636017 3681755 := bstep (se 1 (by rfl) ⟨2761316, by rfl⟩ : syracuseStep 3681755 = 5522633) B5522633
theorem B5524955 : Blo 1636017 5524955 := bstep (se 1 (by rfl) ⟨4143716, by rfl⟩ : syracuseStep 5524955 = 8287433) B8287433
theorem B6213145 : Blo 1636017 6213145 := bstep (se 2 (by rfl) ⟨2329929, by rfl⟩ : syracuseStep 6213145 = 4659859) B4659859
theorem B3108449 : Blo 1636017 3108449 := bstep (se 2 (by rfl) ⟨1165668, by rfl⟩ : syracuseStep 3108449 = 2331337) B2331337
theorem B9326279 : Blo 1636017 9326279 := bstep (se 1 (by rfl) ⟨6994709, by rfl⟩ : syracuseStep 9326279 = 13989419) B13989419
theorem B6213419 : Blo 1636017 6213419 := bstep (se 1 (by rfl) ⟨4660064, by rfl⟩ : syracuseStep 6213419 = 9320129) B9320129
theorem B6213449 : Blo 1636017 6213449 := bstep (se 2 (by rfl) ⟨2330043, by rfl⟩ : syracuseStep 6213449 = 4660087) B4660087
theorem B9318239 : Blo 1636017 9318239 := bstep (se 1 (by rfl) ⟨6988679, by rfl⟩ : syracuseStep 9318239 = 13977359) B13977359
theorem B3682223 : Blo 1636017 3682223 := bstep (se 1 (by rfl) ⟨2761667, by rfl⟩ : syracuseStep 3682223 = 5523335) B5523335
theorem B11194321 : Blo 1636017 11194321 := bstep (se 2 (by rfl) ⟨4197870, by rfl⟩ : syracuseStep 11194321 = 8395741) B8395741
theorem B5525657 : Blo 1636017 5525657 := bstep (se 2 (by rfl) ⟨2072121, by rfl⟩ : syracuseStep 5525657 = 4144243) B4144243
theorem B3682475 : Blo 1636017 3682475 := bstep (se 1 (by rfl) ⟨2761856, by rfl⟩ : syracuseStep 3682475 = 5523713) B5523713
theorem B11350273 : Blo 1636017 11350273 := bstep (se 2 (by rfl) ⟨4256352, by rfl⟩ : syracuseStep 11350273 = 8512705) B8512705
theorem B6640015 : Blo 1636017 6640015 := bstep (se 1 (by rfl) ⟨4980011, by rfl⟩ : syracuseStep 6640015 = 9960023) B9960023
theorem B1659355 : Blo 1636017 1659355 := bstep (se 1 (by rfl) ⟨1244516, by rfl⟩ : syracuseStep 1659355 = 2489033) B2489033
theorem B2454095 : Blo 1636017 2454095 := bstep (se 1 (by rfl) ⟨1840571, by rfl⟩ : syracuseStep 2454095 = 3681143) B3681143
theorem B2454215 : Blo 1636017 2454215 := bstep (se 1 (by rfl) ⟨1840661, by rfl⟩ : syracuseStep 2454215 = 3681323) B3681323
theorem B3683015 : Blo 1636017 3683015 := bstep (se 1 (by rfl) ⟨2762261, by rfl⟩ : syracuseStep 3683015 = 5524523) B5524523
theorem B9319171 : Blo 1636017 9319171 := bstep (se 1 (by rfl) ⟨6989378, by rfl⟩ : syracuseStep 9319171 = 13978757) B13978757
theorem B2454377 : Blo 1636017 2454377 := bstep (se 2 (by rfl) ⟨920391, by rfl⟩ : syracuseStep 2454377 = 1840783) B1840783
theorem B2454455 : Blo 1636017 2454455 := bstep (se 1 (by rfl) ⟨1840841, by rfl⟩ : syracuseStep 2454455 = 3681683) B3681683
theorem B2454491 : Blo 1636017 2454491 := bstep (se 1 (by rfl) ⟨1840868, by rfl⟩ : syracuseStep 2454491 = 3681737) B3681737
theorem B4142087 : Blo 1636017 4142087 := bstep (se 1 (by rfl) ⟨3106565, by rfl⟩ : syracuseStep 4142087 = 6213131) B6213131
theorem B4142137 : Blo 1636017 4142137 := bstep (se 2 (by rfl) ⟨1553301, by rfl⟩ : syracuseStep 4142137 = 3106603) B3106603
theorem B18641987 : Blo 1636017 18641987 := bstep (se 1 (by rfl) ⟨13981490, by rfl⟩ : syracuseStep 18641987 = 27962981) B27962981
theorem B6640811 : Blo 1636017 6640811 := bstep (se 1 (by rfl) ⟨4980608, by rfl⟩ : syracuseStep 6640811 = 9961217) B9961217
theorem B13456577 : Blo 1636017 13456577 := bstep (se 2 (by rfl) ⟨5046216, by rfl⟩ : syracuseStep 13456577 = 10092433) B10092433
theorem B5526845 : Blo 1636017 5526845 := bstep (se 3 (by rfl) ⟨1036283, by rfl⟩ : syracuseStep 5526845 = 2072567) B2072567
theorem B4142441 : Blo 1636017 4142441 := bstep (se 2 (by rfl) ⟨1553415, by rfl⟩ : syracuseStep 4142441 = 3106831) B3106831
theorem B2454959 : Blo 1636017 2454959 := bstep (se 1 (by rfl) ⟨1841219, by rfl⟩ : syracuseStep 2454959 = 3682439) B3682439
theorem B1840603 : Blo 1636017 1840603 := bstep (se 1 (by rfl) ⟨1380452, by rfl⟩ : syracuseStep 1840603 = 2760905) B2760905
theorem B20977157 : Blo 1636017 20977157 := bstep (se 4 (by rfl) ⟨1966608, by rfl⟩ : syracuseStep 20977157 = 3933217) B3933217
theorem B2455049 : Blo 1636017 2455049 := bstep (se 2 (by rfl) ⟨920643, by rfl⟩ : syracuseStep 2455049 = 1841287) B1841287
theorem B2455079 : Blo 1636017 2455079 := bstep (se 1 (by rfl) ⟨1841309, by rfl⟩ : syracuseStep 2455079 = 3682619) B3682619
theorem B3683879 : Blo 1636017 3683879 := bstep (se 1 (by rfl) ⟨2762909, by rfl⟩ : syracuseStep 3683879 = 5525819) B5525819
theorem B2455163 : Blo 1636017 2455163 := bstep (se 1 (by rfl) ⟨1841372, by rfl⟩ : syracuseStep 2455163 = 3682745) B3682745
theorem B56694421 : Blo 1636017 56694421 := bstep (se 6 (by rfl) ⟨1328775, by rfl⟩ : syracuseStep 56694421 = 2657551) B2657551
theorem B1636039 : Blo 1636017 1636039 := bstep (se 1 (by rfl) ⟨1227029, by rfl⟩ : syracuseStep 1636039 = 2454059) B2454059
theorem B5043923 : Blo 1636017 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B4658903 : Blo 1636017 4658903 := bstep (se 1 (by rfl) ⟨3494177, by rfl⟩ : syracuseStep 4658903 = 6988355) B6988355
theorem B1636059 : Blo 1636017 1636059 := bstep (se 1 (by rfl) ⟨1227044, by rfl⟩ : syracuseStep 1636059 = 2454089) B2454089
theorem B2455289 : Blo 1636017 2455289 := bstep (se 2 (by rfl) ⟨920733, by rfl⟩ : syracuseStep 2455289 = 1841467) B1841467
theorem B1636135 : Blo 1636017 1636135 := bstep (se 1 (by rfl) ⟨1227101, by rfl⟩ : syracuseStep 1636135 = 2454203) B2454203
theorem B302323499 : Blo 1636017 302323499 := bstep (se 1 (by rfl) ⟨226742624, by rfl⟩ : syracuseStep 302323499 = 453485249) B453485249
theorem B10491707 : Blo 1636017 10491707 := bstep (se 1 (by rfl) ⟨7868780, by rfl⟩ : syracuseStep 10491707 = 15737561) B15737561
theorem B8197955 : Blo 1636017 8197955 := bstep (se 1 (by rfl) ⟨6148466, by rfl⟩ : syracuseStep 8197955 = 12296933) B12296933
theorem B1636175 : Blo 1636017 1636175 := bstep (se 1 (by rfl) ⟨1227131, by rfl⟩ : syracuseStep 1636175 = 2454263) B2454263
theorem B1636191 : Blo 1636017 1636191 := bstep (se 1 (by rfl) ⟨1227143, by rfl⟩ : syracuseStep 1636191 = 2454287) B2454287
theorem B2455391 : Blo 1636017 2455391 := bstep (se 1 (by rfl) ⟨1841543, by rfl⟩ : syracuseStep 2455391 = 3683087) B3683087
theorem B2455403 : Blo 1636017 2455403 := bstep (se 1 (by rfl) ⟨1841552, by rfl⟩ : syracuseStep 2455403 = 3683105) B3683105
theorem B3684203 : Blo 1636017 3684203 := bstep (se 1 (by rfl) ⟨2763152, by rfl⟩ : syracuseStep 3684203 = 5526305) B5526305
theorem B1636219 : Blo 1636017 1636219 := bstep (se 1 (by rfl) ⟨1227164, by rfl⟩ : syracuseStep 1636219 = 2454329) B2454329
theorem B3684257 : Blo 1636017 3684257 := bstep (se 2 (by rfl) ⟨1381596, by rfl⟩ : syracuseStep 3684257 = 2763193) B2763193
theorem B1636271 : Blo 1636017 1636271 := bstep (se 1 (by rfl) ⟨1227203, by rfl⟩ : syracuseStep 1636271 = 2454407) B2454407
theorem B1841071 : Blo 1636017 1841071 := bstep (se 1 (by rfl) ⟨1380803, by rfl⟩ : syracuseStep 1841071 = 2761607) B2761607
theorem B12433337 : Blo 1636017 12433337 := bstep (se 2 (by rfl) ⟨4662501, by rfl⟩ : syracuseStep 12433337 = 9325003) B9325003
theorem B1636295 : Blo 1636017 1636295 := bstep (se 1 (by rfl) ⟨1227221, by rfl⟩ : syracuseStep 1636295 = 2454443) B2454443
theorem B1636315 : Blo 1636017 1636315 := bstep (se 1 (by rfl) ⟨1227236, by rfl⟩ : syracuseStep 1636315 = 2454473) B2454473
theorem B13981733 : Blo 1636017 13981733 := bstep (se 4 (by rfl) ⟨1310787, by rfl⟩ : syracuseStep 13981733 = 2621575) B2621575
theorem B1636391 : Blo 1636017 1636391 := bstep (se 1 (by rfl) ⟨1227293, by rfl⟩ : syracuseStep 1636391 = 2454587) B2454587
theorem B14940217 : Blo 1636017 14940217 := bstep (se 2 (by rfl) ⟨5602581, by rfl⟩ : syracuseStep 14940217 = 11205163) B11205163
theorem B1636431 : Blo 1636017 1636431 := bstep (se 1 (by rfl) ⟨1227323, by rfl⟩ : syracuseStep 1636431 = 2454647) B2454647
theorem B2455631 : Blo 1636017 2455631 := bstep (se 1 (by rfl) ⟨1841723, by rfl⟩ : syracuseStep 2455631 = 3683447) B3683447
theorem B1636447 : Blo 1636017 1636447 := bstep (se 1 (by rfl) ⟨1227335, by rfl⟩ : syracuseStep 1636447 = 2454671) B2454671
theorem B11204723 : Blo 1636017 11204723 := bstep (se 1 (by rfl) ⟨8403542, by rfl⟩ : syracuseStep 11204723 = 16807085) B16807085
theorem B1636475 : Blo 1636017 1636475 := bstep (se 1 (by rfl) ⟨1227356, by rfl⟩ : syracuseStep 1636475 = 2454713) B2454713
theorem B5527709 : Blo 1636017 5527709 := bstep (se 3 (by rfl) ⟨1036445, by rfl⟩ : syracuseStep 5527709 = 2072891) B2072891
theorem B1636527 : Blo 1636017 1636527 := bstep (se 1 (by rfl) ⟨1227395, by rfl⟩ : syracuseStep 1636527 = 2454791) B2454791
theorem B1636551 : Blo 1636017 1636551 := bstep (se 1 (by rfl) ⟨1227413, by rfl⟩ : syracuseStep 1636551 = 2454827) B2454827
theorem B2455751 : Blo 1636017 2455751 := bstep (se 1 (by rfl) ⟨1841813, by rfl⟩ : syracuseStep 2455751 = 3683627) B3683627
theorem B1636571 : Blo 1636017 1636571 := bstep (se 1 (by rfl) ⟨1227428, by rfl⟩ : syracuseStep 1636571 = 2454857) B2454857
theorem B3684599 : Blo 1636017 3684599 := bstep (se 1 (by rfl) ⟨2763449, by rfl⟩ : syracuseStep 3684599 = 5526899) B5526899
theorem B1636647 : Blo 1636017 1636647 := bstep (se 1 (by rfl) ⟨1227485, by rfl⟩ : syracuseStep 1636647 = 2454971) B2454971
theorem B1636687 : Blo 1636017 1636687 := bstep (se 1 (by rfl) ⟨1227515, by rfl⟩ : syracuseStep 1636687 = 2455031) B2455031
theorem B1636703 : Blo 1636017 1636703 := bstep (se 1 (by rfl) ⟨1227527, by rfl⟩ : syracuseStep 1636703 = 2455055) B2455055
theorem B1841503 : Blo 1636017 1841503 := bstep (se 1 (by rfl) ⟨1381127, by rfl⟩ : syracuseStep 1841503 = 2762255) B2762255
theorem B2455913 : Blo 1636017 2455913 := bstep (se 2 (by rfl) ⟨920967, by rfl⟩ : syracuseStep 2455913 = 1841935) B1841935
theorem B1636731 : Blo 1636017 1636731 := bstep (se 1 (by rfl) ⟨1227548, by rfl⟩ : syracuseStep 1636731 = 2455097) B2455097
theorem B6216061 : Blo 1636017 6216061 := bstep (se 3 (by rfl) ⟨1165511, by rfl⟩ : syracuseStep 6216061 = 2331023) B2331023
theorem B1636783 : Blo 1636017 1636783 := bstep (se 1 (by rfl) ⟨1227587, by rfl⟩ : syracuseStep 1636783 = 2455175) B2455175
theorem B2455991 : Blo 1636017 2455991 := bstep (se 1 (by rfl) ⟨1841993, by rfl⟩ : syracuseStep 2455991 = 3683987) B3683987
theorem B1636807 : Blo 1636017 1636807 := bstep (se 1 (by rfl) ⟨1227605, by rfl⟩ : syracuseStep 1636807 = 2455211) B2455211
theorem B15350219 : Blo 1636017 15350219 := bstep (se 1 (by rfl) ⟨11512664, by rfl⟩ : syracuseStep 15350219 = 23025329) B23025329
theorem B17709515 : Blo 1636017 17709515 := bstep (se 1 (by rfl) ⟨13282136, by rfl⟩ : syracuseStep 17709515 = 26564273) B26564273
theorem B2071003 : Blo 1636017 2071003 := bstep (se 1 (by rfl) ⟨1553252, by rfl⟩ : syracuseStep 2071003 = 3106505) B3106505
theorem B1636827 : Blo 1636017 1636827 := bstep (se 1 (by rfl) ⟨1227620, by rfl⟩ : syracuseStep 1636827 = 2455241) B2455241
theorem B2456027 : Blo 1636017 2456027 := bstep (se 1 (by rfl) ⟨1842020, by rfl⟩ : syracuseStep 2456027 = 3684041) B3684041
theorem B11196953 : Blo 1636017 11196953 := bstep (se 2 (by rfl) ⟨4198857, by rfl⟩ : syracuseStep 11196953 = 8397715) B8397715
theorem B15735329 : Blo 1636017 15735329 := bstep (se 2 (by rfl) ⟨5900748, by rfl⟩ : syracuseStep 15735329 = 11801497) B11801497
theorem B1636903 : Blo 1636017 1636903 := bstep (se 1 (by rfl) ⟨1227677, by rfl⟩ : syracuseStep 1636903 = 2455355) B2455355
theorem B1636943 : Blo 1636017 1636943 := bstep (se 1 (by rfl) ⟨1227707, by rfl⟩ : syracuseStep 1636943 = 2455415) B2455415
theorem B22411853 : Blo 1636017 22411853 := bstep (se 3 (by rfl) ⟨4202222, by rfl⟩ : syracuseStep 22411853 = 8404445) B8404445
theorem B1636959 : Blo 1636017 1636959 := bstep (se 1 (by rfl) ⟨1227719, by rfl⟩ : syracuseStep 1636959 = 2455439) B2455439
theorem B272325239 : Blo 1636017 272325239 := bstep (se 1 (by rfl) ⟨204243929, by rfl⟩ : syracuseStep 272325239 = 408487859) B408487859
theorem B1636987 : Blo 1636017 1636987 := bstep (se 1 (by rfl) ⟨1227740, by rfl⟩ : syracuseStep 1636987 = 2455481) B2455481
theorem B1637039 : Blo 1636017 1637039 := bstep (se 1 (by rfl) ⟨1227779, by rfl⟩ : syracuseStep 1637039 = 2455559) B2455559
theorem B5528249 : Blo 1636017 5528249 := bstep (se 2 (by rfl) ⟨2073093, by rfl⟩ : syracuseStep 5528249 = 4146187) B4146187
theorem B1637063 : Blo 1636017 1637063 := bstep (se 1 (by rfl) ⟨1227797, by rfl⟩ : syracuseStep 1637063 = 2455595) B2455595
theorem B1841863 : Blo 1636017 1841863 := bstep (se 1 (by rfl) ⟨1381397, by rfl⟩ : syracuseStep 1841863 = 2762795) B2762795
theorem B1637083 : Blo 1636017 1637083 := bstep (se 1 (by rfl) ⟨1227812, by rfl⟩ : syracuseStep 1637083 = 2455625) B2455625
theorem B5978909 : Blo 1636017 5978909 := bstep (se 3 (by rfl) ⟨1121045, by rfl⟩ : syracuseStep 5978909 = 2242091) B2242091
theorem B8289053 : Blo 1636017 8289053 := bstep (se 3 (by rfl) ⟨1554197, by rfl⟩ : syracuseStep 8289053 = 3108395) B3108395
theorem B1637159 : Blo 1636017 1637159 := bstep (se 1 (by rfl) ⟨1227869, by rfl⟩ : syracuseStep 1637159 = 2455739) B2455739
theorem B3685193 : Blo 1636017 3685193 := bstep (se 2 (by rfl) ⟨1381947, by rfl⟩ : syracuseStep 3685193 = 2763895) B2763895
theorem B1637199 : Blo 1636017 1637199 := bstep (se 1 (by rfl) ⟨1227899, by rfl⟩ : syracuseStep 1637199 = 2455799) B2455799
theorem B1637215 : Blo 1636017 1637215 := bstep (se 1 (by rfl) ⟨1227911, by rfl⟩ : syracuseStep 1637215 = 2455823) B2455823
theorem B1637243 : Blo 1636017 1637243 := bstep (se 1 (by rfl) ⟨1227932, by rfl⟩ : syracuseStep 1637243 = 2455865) B2455865
theorem B1637295 : Blo 1636017 1637295 := bstep (se 1 (by rfl) ⟨1227971, by rfl⟩ : syracuseStep 1637295 = 2455943) B2455943
theorem B2456495 : Blo 1636017 2456495 := bstep (se 1 (by rfl) ⟨1842371, by rfl⟩ : syracuseStep 2456495 = 3684743) B3684743
theorem B1637319 : Blo 1636017 1637319 := bstep (se 1 (by rfl) ⟨1227989, by rfl⟩ : syracuseStep 1637319 = 2455979) B2455979
theorem B1637339 : Blo 1636017 1637339 := bstep (se 1 (by rfl) ⟨1228004, by rfl⟩ : syracuseStep 1637339 = 2456009) B2456009
theorem B2456585 : Blo 1636017 2456585 := bstep (se 2 (by rfl) ⟨921219, by rfl⟩ : syracuseStep 2456585 = 1842439) B1842439
theorem B3496979 : Blo 1636017 3496979 := bstep (se 1 (by rfl) ⟨2622734, by rfl⟩ : syracuseStep 3496979 = 5245469) B5245469
theorem B408845333 : Blo 1636017 408845333 := bstep (se 6 (by rfl) ⟨9582312, by rfl⟩ : syracuseStep 408845333 = 19164625) B19164625
theorem B4979731 : Blo 1636017 4979731 := bstep (se 1 (by rfl) ⟨3734798, by rfl⟩ : syracuseStep 4979731 = 7469597) B7469597
theorem B1637415 : Blo 1636017 1637415 := bstep (se 1 (by rfl) ⟨1228061, by rfl⟩ : syracuseStep 1637415 = 2456123) B2456123
theorem B2456615 : Blo 1636017 2456615 := bstep (se 1 (by rfl) ⟨1842461, by rfl⟩ : syracuseStep 2456615 = 3684923) B3684923
theorem B1637455 : Blo 1636017 1637455 := bstep (se 1 (by rfl) ⟨1228091, by rfl⟩ : syracuseStep 1637455 = 2456183) B2456183
theorem B1637471 : Blo 1636017 1637471 := bstep (se 1 (by rfl) ⟨1228103, by rfl⟩ : syracuseStep 1637471 = 2456207) B2456207
theorem B1637499 : Blo 1636017 1637499 := bstep (se 1 (by rfl) ⟨1228124, by rfl⟩ : syracuseStep 1637499 = 2456249) B2456249
theorem B2456699 : Blo 1636017 2456699 := bstep (se 1 (by rfl) ⟨1842524, by rfl⟩ : syracuseStep 2456699 = 3685049) B3685049
theorem B13270169 : Blo 1636017 13270169 := bstep (se 2 (by rfl) ⟨4976313, by rfl⟩ : syracuseStep 13270169 = 9952627) B9952627
theorem B1637551 : Blo 1636017 1637551 := bstep (se 1 (by rfl) ⟨1228163, by rfl⟩ : syracuseStep 1637551 = 2456327) B2456327
theorem B1637575 : Blo 1636017 1637575 := bstep (se 1 (by rfl) ⟨1228181, by rfl⟩ : syracuseStep 1637575 = 2456363) B2456363
theorem B1637595 : Blo 1636017 1637595 := bstep (se 1 (by rfl) ⟨1228196, by rfl⟩ : syracuseStep 1637595 = 2456393) B2456393
theorem B2456825 : Blo 1636017 2456825 := bstep (se 2 (by rfl) ⟨921309, by rfl⟩ : syracuseStep 2456825 = 1842619) B1842619
theorem B12426533 : Blo 1636017 12426533 := bstep (se 4 (by rfl) ⟨1164987, by rfl⟩ : syracuseStep 12426533 = 2329975) B2329975
theorem B1637671 : Blo 1636017 1637671 := bstep (se 1 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 1637671 = 2456507) B2456507
theorem B1637711 : Blo 1636017 1637711 := bstep (se 1 (by rfl) ⟨1228283, by rfl⟩ : syracuseStep 1637711 = 2456567) B2456567
theorem B1637727 : Blo 1636017 1637727 := bstep (se 1 (by rfl) ⟨1228295, by rfl⟩ : syracuseStep 1637727 = 2456591) B2456591
theorem B2456927 : Blo 1636017 2456927 := bstep (se 1 (by rfl) ⟨1842695, by rfl⟩ : syracuseStep 2456927 = 3685391) B3685391
theorem B2456939 : Blo 1636017 2456939 := bstep (se 1 (by rfl) ⟨1842704, by rfl⟩ : syracuseStep 2456939 = 3685409) B3685409
theorem B14925181 : Blo 1636017 14925181 := bstep (se 3 (by rfl) ⟨2798471, by rfl⟩ : syracuseStep 14925181 = 5596943) B5596943
theorem B1637755 : Blo 1636017 1637755 := bstep (se 1 (by rfl) ⟨1228316, by rfl⟩ : syracuseStep 1637755 = 2456633) B2456633
theorem B17030573 : Blo 1636017 17030573 := bstep (se 3 (by rfl) ⟨3193232, by rfl⟩ : syracuseStep 17030573 = 6386465) B6386465
theorem B1637807 : Blo 1636017 1637807 := bstep (se 1 (by rfl) ⟨1228355, by rfl⟩ : syracuseStep 1637807 = 2456711) B2456711
theorem B1637831 : Blo 1636017 1637831 := bstep (se 1 (by rfl) ⟨1228373, by rfl⟩ : syracuseStep 1637831 = 2456747) B2456747
theorem B1637851 : Blo 1636017 1637851 := bstep (se 1 (by rfl) ⟨1228388, by rfl⟩ : syracuseStep 1637851 = 2456777) B2456777
theorem B4144679 : Blo 1636017 4144679 := bstep (se 1 (by rfl) ⟨3108509, by rfl⟩ : syracuseStep 4144679 = 6217019) B6217019
theorem B1637927 : Blo 1636017 1637927 := bstep (se 1 (by rfl) ⟨1228445, by rfl⟩ : syracuseStep 1637927 = 2456891) B2456891
theorem B1842727 : Blo 1636017 1842727 := bstep (se 1 (by rfl) ⟨1382045, by rfl⟩ : syracuseStep 1842727 = 2764091) B2764091
theorem B1637967 : Blo 1636017 1637967 := bstep (se 1 (by rfl) ⟨1228475, by rfl⟩ : syracuseStep 1637967 = 2456951) B2456951
theorem B1637983 : Blo 1636017 1637983 := bstep (se 1 (by rfl) ⟨1228487, by rfl⟩ : syracuseStep 1637983 = 2456975) B2456975
theorem B1638011 : Blo 1636017 1638011 := bstep (se 1 (by rfl) ⟨1228508, by rfl⟩ : syracuseStep 1638011 = 2457017) B2457017
theorem B4145003 : Blo 1636017 4145003 := bstep (se 1 (by rfl) ⟨3108752, by rfl⟩ : syracuseStep 4145003 = 6217505) B6217505
theorem B11960473 : Blo 1636017 11960473 := bstep (se 2 (by rfl) ⟨4485177, by rfl⟩ : syracuseStep 11960473 = 8970355) B8970355
theorem B14942555 : Blo 1636017 14942555 := bstep (se 1 (by rfl) ⟨11206916, by rfl⟩ : syracuseStep 14942555 = 22413833) B22413833
theorem B4145519 : Blo 1636017 4145519 := bstep (se 1 (by rfl) ⟨3109139, by rfl⟩ : syracuseStep 4145519 = 6218279) B6218279
theorem B2212219 : Blo 1636017 2212219 := bstep (se 1 (by rfl) ⟨1659164, by rfl⟩ : syracuseStep 2212219 = 3318329) B3318329
theorem B20972033 : Blo 1636017 20972033 := bstep (se 2 (by rfl) ⟨7864512, by rfl⟩ : syracuseStep 20972033 = 15729025) B15729025
theorem B5243393 : Blo 1636017 5243393 := bstep (se 2 (by rfl) ⟨1966272, by rfl⟩ : syracuseStep 5243393 = 3932545) B3932545
theorem B8290835 : Blo 1636017 8290835 := bstep (se 1 (by rfl) ⟨6218126, by rfl⟩ : syracuseStep 8290835 = 12436253) B12436253
theorem B2761337 : Blo 1636017 2761337 := bstep (se 2 (by rfl) ⟨1035501, by rfl⟩ : syracuseStep 2761337 = 2071003) B2071003
theorem B5898905 : Blo 1636017 5898905 := bstep (se 2 (by rfl) ⟨2212089, by rfl⟩ : syracuseStep 5898905 = 4424179) B4424179
theorem B2761391 : Blo 1636017 2761391 := bstep (se 1 (by rfl) ⟨2071043, by rfl⟩ : syracuseStep 2761391 = 4142087) B4142087
theorem B8848055 : Blo 1636017 8848055 := bstep (se 1 (by rfl) ⟨6636041, by rfl⟩ : syracuseStep 8848055 = 13272083) B13272083
theorem B12427991 : Blo 1636017 12427991 := bstep (se 1 (by rfl) ⟨9320993, by rfl⟩ : syracuseStep 12427991 = 18641987) B18641987
theorem B5522255 : Blo 1636017 5522255 := bstep (se 1 (by rfl) ⟨4141691, by rfl⟩ : syracuseStep 5522255 = 8283383) B8283383
theorem B2761627 : Blo 1636017 2761627 := bstep (se 1 (by rfl) ⟨2071220, by rfl⟩ : syracuseStep 2761627 = 4142441) B4142441
theorem B4146167 : Blo 1636017 4146167 := bstep (se 1 (by rfl) ⟨3109625, by rfl⟩ : syracuseStep 4146167 = 6219251) B6219251
theorem B13984771 : Blo 1636017 13984771 := bstep (se 1 (by rfl) ⟨10488578, by rfl⟩ : syracuseStep 13984771 = 20977157) B20977157
theorem B3105935 : Blo 1636017 3105935 := bstep (se 1 (by rfl) ⟨2329451, by rfl⟩ : syracuseStep 3105935 = 4658903) B4658903
theorem B5522579 : Blo 1636017 5522579 := bstep (se 1 (by rfl) ⟨4141934, by rfl⟩ : syracuseStep 5522579 = 8283869) B8283869
theorem B201548999 : Blo 1636017 201548999 := bstep (se 1 (by rfl) ⟨151161749, by rfl⟩ : syracuseStep 201548999 = 302323499) B302323499
theorem B5465303 : Blo 1636017 5465303 := bstep (se 1 (by rfl) ⟨4098977, by rfl⟩ : syracuseStep 5465303 = 8197955) B8197955
theorem B9323819 : Blo 1636017 9323819 := bstep (se 1 (by rfl) ⟨6992864, by rfl⟩ : syracuseStep 9323819 = 13985729) B13985729
theorem B20186455 : Blo 1636017 20186455 := bstep (se 1 (by rfl) ⟨15139841, by rfl⟩ : syracuseStep 20186455 = 30279683) B30279683
theorem B5522849 : Blo 1636017 5522849 := bstep (se 2 (by rfl) ⟨2071068, by rfl⟩ : syracuseStep 5522849 = 4142137) B4142137
theorem B10233479 : Blo 1636017 10233479 := bstep (se 1 (by rfl) ⟨7675109, by rfl⟩ : syracuseStep 10233479 = 15350219) B15350219
theorem B11806343 : Blo 1636017 11806343 := bstep (se 1 (by rfl) ⟨8854757, by rfl⟩ : syracuseStep 11806343 = 17709515) B17709515
theorem B7464635 : Blo 1636017 7464635 := bstep (se 1 (by rfl) ⟨5598476, by rfl⟩ : syracuseStep 7464635 = 11196953) B11196953
theorem B19900241 : Blo 1636017 19900241 := bstep (se 2 (by rfl) ⟨7462590, by rfl⟩ : syracuseStep 19900241 = 14925181) B14925181
theorem B10487657 : Blo 1636017 10487657 := bstep (se 2 (by rfl) ⟨3932871, by rfl⟩ : syracuseStep 10487657 = 7865743) B7865743
theorem B3934217 : Blo 1636017 3934217 := bstep (se 2 (by rfl) ⟨1475331, by rfl⟩ : syracuseStep 3934217 = 2950663) B2950663
theorem B8284193 : Blo 1636017 8284193 := bstep (se 2 (by rfl) ⟨3106572, by rfl⟩ : syracuseStep 8284193 = 6213145) B6213145
theorem B8284355 : Blo 1636017 8284355 := bstep (se 1 (by rfl) ⟨6213266, by rfl⟩ : syracuseStep 8284355 = 12426533) B12426533
theorem B2763119 : Blo 1636017 2763119 := bstep (se 1 (by rfl) ⟨2072339, by rfl⟩ : syracuseStep 2763119 = 4144679) B4144679
theorem B8849893 : Blo 1636017 8849893 := bstep (se 4 (by rfl) ⟨829677, by rfl⟩ : syracuseStep 8849893 = 1659355) B1659355
theorem B6212159 : Blo 1636017 6212159 := bstep (se 1 (by rfl) ⟨4659119, by rfl⟩ : syracuseStep 6212159 = 9318239) B9318239
theorem B2763335 : Blo 1636017 2763335 := bstep (se 1 (by rfl) ⟨2072501, by rfl⟩ : syracuseStep 2763335 = 4145003) B4145003
theorem B9325277 : Blo 1636017 9325277 := bstep (se 3 (by rfl) ⟨1748489, by rfl⟩ : syracuseStep 9325277 = 3496979) B3496979
theorem B70814513 : Blo 1636017 70814513 := bstep (se 2 (by rfl) ⟨26555442, by rfl⟩ : syracuseStep 70814513 = 53110885) B53110885
theorem B6212477 : Blo 1636017 6212477 := bstep (se 3 (by rfl) ⟨1164839, by rfl⟩ : syracuseStep 6212477 = 2329679) B2329679
theorem B3681179 : Blo 1636017 3681179 := bstep (se 1 (by rfl) ⟨2760884, by rfl⟩ : syracuseStep 3681179 = 5521769) B5521769
theorem B2763767 : Blo 1636017 2763767 := bstep (se 1 (by rfl) ⟨2072825, by rfl⟩ : syracuseStep 2763767 = 4145651) B4145651
theorem B15133697 : Blo 1636017 15133697 := bstep (se 2 (by rfl) ⟨5675136, by rfl⟩ : syracuseStep 15133697 = 11350273) B11350273
theorem B3681377 : Blo 1636017 3681377 := bstep (se 2 (by rfl) ⟨1380516, by rfl⟩ : syracuseStep 3681377 = 2761033) B2761033
theorem B35884205 : Blo 1636017 35884205 := bstep (se 3 (by rfl) ⟨6728288, by rfl⟩ : syracuseStep 35884205 = 13456577) B13456577
theorem B3681575 : Blo 1636017 3681575 := bstep (se 1 (by rfl) ⟨2761181, by rfl⟩ : syracuseStep 3681575 = 5522363) B5522363
theorem B4427207 : Blo 1636017 4427207 := bstep (se 1 (by rfl) ⟨3320405, by rfl⟩ : syracuseStep 4427207 = 6640811) B6640811
theorem B5901817 : Blo 1636017 5901817 := bstep (se 2 (by rfl) ⟨2213181, by rfl⟩ : syracuseStep 5901817 = 4426363) B4426363
theorem B1748575 : Blo 1636017 1748575 := bstep (se 1 (by rfl) ⟨1311431, by rfl⟩ : syracuseStep 1748575 = 2622863) B2622863
theorem B3681953 : Blo 1636017 3681953 := bstep (se 2 (by rfl) ⟨1380732, by rfl⟩ : syracuseStep 3681953 = 2761465) B2761465
theorem B5902121 : Blo 1636017 5902121 := bstep (se 2 (by rfl) ⟨2213295, by rfl⟩ : syracuseStep 5902121 = 4426591) B4426591
theorem B3362615 : Blo 1636017 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B9449273 : Blo 1636017 9449273 := bstep (se 2 (by rfl) ⟨3543477, by rfl⟩ : syracuseStep 9449273 = 7086955) B7086955
theorem B3682313 : Blo 1636017 3682313 := bstep (se 2 (by rfl) ⟨1380867, by rfl⟩ : syracuseStep 3682313 = 2761735) B2761735
theorem B6639641 : Blo 1636017 6639641 := bstep (se 2 (by rfl) ⟨2489865, by rfl⟩ : syracuseStep 6639641 = 4979731) B4979731
theorem B10490219 : Blo 1636017 10490219 := bstep (se 1 (by rfl) ⟨7867664, by rfl⟩ : syracuseStep 10490219 = 15735329) B15735329
theorem B3682727 : Blo 1636017 3682727 := bstep (se 1 (by rfl) ⟨2762045, by rfl⟩ : syracuseStep 3682727 = 5524091) B5524091
theorem B17699309 : Blo 1636017 17699309 := bstep (se 3 (by rfl) ⟨3318620, by rfl⟩ : syracuseStep 17699309 = 6637241) B6637241
theorem B3985939 : Blo 1636017 3985939 := bstep (se 1 (by rfl) ⟨2989454, by rfl⟩ : syracuseStep 3985939 = 5978909) B5978909
theorem B3682835 : Blo 1636017 3682835 := bstep (se 1 (by rfl) ⟨2762126, by rfl⟩ : syracuseStep 3682835 = 5524253) B5524253
theorem B5526035 : Blo 1636017 5526035 := bstep (se 1 (by rfl) ⟨4144526, by rfl⟩ : syracuseStep 5526035 = 8289053) B8289053
theorem B4141631 : Blo 1636017 4141631 := bstep (se 1 (by rfl) ⟨3106223, by rfl⟩ : syracuseStep 4141631 = 6212447) B6212447
theorem B3682889 : Blo 1636017 3682889 := bstep (se 2 (by rfl) ⟨1381083, by rfl⟩ : syracuseStep 3682889 = 2762167) B2762167
theorem B2454137 : Blo 1636017 2454137 := bstep (se 2 (by rfl) ⟨920301, by rfl⟩ : syracuseStep 2454137 = 1840603) B1840603
theorem B2454191 : Blo 1636017 2454191 := bstep (se 1 (by rfl) ⟨1840643, by rfl⟩ : syracuseStep 2454191 = 3681287) B3681287
theorem B2454239 : Blo 1636017 2454239 := bstep (se 1 (by rfl) ⟨1840679, by rfl⟩ : syracuseStep 2454239 = 3681359) B3681359
theorem B75592561 : Blo 1636017 75592561 := bstep (se 2 (by rfl) ⟨28347210, by rfl⟩ : syracuseStep 75592561 = 56694421) B56694421
theorem B2454503 : Blo 1636017 2454503 := bstep (se 1 (by rfl) ⟨1840877, by rfl⟩ : syracuseStep 2454503 = 3681755) B3681755
theorem B3683303 : Blo 1636017 3683303 := bstep (se 1 (by rfl) ⟨2762477, by rfl⟩ : syracuseStep 3683303 = 5524955) B5524955
theorem B4142279 : Blo 1636017 4142279 := bstep (se 1 (by rfl) ⟨3106709, by rfl⟩ : syracuseStep 4142279 = 6213419) B6213419
theorem B4142299 : Blo 1636017 4142299 := bstep (se 1 (by rfl) ⟨3106724, by rfl⟩ : syracuseStep 4142299 = 6213449) B6213449
theorem B2454761 : Blo 1636017 2454761 := bstep (se 2 (by rfl) ⟨920535, by rfl⟩ : syracuseStep 2454761 = 1841071) B1841071
theorem B2454815 : Blo 1636017 2454815 := bstep (se 1 (by rfl) ⟨1841111, by rfl⟩ : syracuseStep 2454815 = 3682223) B3682223
theorem B3683681 : Blo 1636017 3683681 := bstep (se 2 (by rfl) ⟨1381380, by rfl⟩ : syracuseStep 3683681 = 2762761) B2762761
theorem B3495305 : Blo 1636017 3495305 := bstep (se 2 (by rfl) ⟨1310739, by rfl⟩ : syracuseStep 3495305 = 2621479) B2621479
theorem B19920289 : Blo 1636017 19920289 := bstep (se 2 (by rfl) ⟨7470108, by rfl⟩ : syracuseStep 19920289 = 14940217) B14940217
theorem B3683771 : Blo 1636017 3683771 := bstep (se 1 (by rfl) ⟨2762828, by rfl⟩ : syracuseStep 3683771 = 5525657) B5525657
theorem B2454983 : Blo 1636017 2454983 := bstep (se 1 (by rfl) ⟨1841237, by rfl⟩ : syracuseStep 2454983 = 3682475) B3682475
theorem B3683897 : Blo 1636017 3683897 := bstep (se 2 (by rfl) ⟨1381461, by rfl⟩ : syracuseStep 3683897 = 2762923) B2762923
theorem B1840711 : Blo 1636017 1840711 := bstep (se 1 (by rfl) ⟨1380533, by rfl⟩ : syracuseStep 1840711 = 2761067) B2761067
theorem B1636063 : Blo 1636017 1636063 := bstep (se 1 (by rfl) ⟨1227047, by rfl⟩ : syracuseStep 1636063 = 2454095) B2454095
theorem B35387117 : Blo 1636017 35387117 := bstep (se 3 (by rfl) ⟨6635084, by rfl⟩ : syracuseStep 35387117 = 13270169) B13270169
theorem B2455337 : Blo 1636017 2455337 := bstep (se 2 (by rfl) ⟨920751, by rfl⟩ : syracuseStep 2455337 = 1841503) B1841503
theorem B1636143 : Blo 1636017 1636143 := bstep (se 1 (by rfl) ⟨1227107, by rfl⟩ : syracuseStep 1636143 = 2454215) B2454215
theorem B2455343 : Blo 1636017 2455343 := bstep (se 1 (by rfl) ⟨1841507, by rfl⟩ : syracuseStep 2455343 = 3683015) B3683015
theorem B8288081 : Blo 1636017 8288081 := bstep (se 2 (by rfl) ⟨3108030, by rfl⟩ : syracuseStep 8288081 = 6216061) B6216061
theorem B8853353 : Blo 1636017 8853353 := bstep (se 2 (by rfl) ⟨3320007, by rfl⟩ : syracuseStep 8853353 = 6640015) B6640015
theorem B1636251 : Blo 1636017 1636251 := bstep (se 1 (by rfl) ⟨1227188, by rfl⟩ : syracuseStep 1636251 = 2454377) B2454377
theorem B1636303 : Blo 1636017 1636303 := bstep (se 1 (by rfl) ⟨1227227, by rfl⟩ : syracuseStep 1636303 = 2454455) B2454455
theorem B9451493 : Blo 1636017 9451493 := bstep (se 4 (by rfl) ⟨886077, by rfl⟩ : syracuseStep 9451493 = 1772155) B1772155
theorem B1636327 : Blo 1636017 1636327 := bstep (se 1 (by rfl) ⟨1227245, by rfl⟩ : syracuseStep 1636327 = 2454491) B2454491
theorem B3684563 : Blo 1636017 3684563 := bstep (se 1 (by rfl) ⟨2763422, by rfl⟩ : syracuseStep 3684563 = 5526845) B5526845
theorem B2455817 : Blo 1636017 2455817 := bstep (se 2 (by rfl) ⟨920931, by rfl⟩ : syracuseStep 2455817 = 1841863) B1841863
theorem B3684617 : Blo 1636017 3684617 := bstep (se 2 (by rfl) ⟨1381731, by rfl⟩ : syracuseStep 3684617 = 2763463) B2763463
theorem B5527817 : Blo 1636017 5527817 := bstep (se 2 (by rfl) ⟨2072931, by rfl⟩ : syracuseStep 5527817 = 4145863) B4145863
theorem B1636639 : Blo 1636017 1636639 := bstep (se 1 (by rfl) ⟨1227479, by rfl⟩ : syracuseStep 1636639 = 2454959) B2454959
theorem B2218279 : Blo 1636017 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B4143433 : Blo 1636017 4143433 := bstep (se 2 (by rfl) ⟨1553787, by rfl⟩ : syracuseStep 4143433 = 3107575) B3107575
theorem B12425561 : Blo 1636017 12425561 := bstep (se 2 (by rfl) ⟨4659585, by rfl⟩ : syracuseStep 12425561 = 9319171) B9319171
theorem B1636699 : Blo 1636017 1636699 := bstep (se 1 (by rfl) ⟨1227524, by rfl⟩ : syracuseStep 1636699 = 2455049) B2455049
theorem B1636719 : Blo 1636017 1636719 := bstep (se 1 (by rfl) ⟨1227539, by rfl⟩ : syracuseStep 1636719 = 2455079) B2455079
theorem B6216047 : Blo 1636017 6216047 := bstep (se 1 (by rfl) ⟨4662035, by rfl⟩ : syracuseStep 6216047 = 9324071) B9324071
theorem B2455919 : Blo 1636017 2455919 := bstep (se 1 (by rfl) ⟨1841939, by rfl⟩ : syracuseStep 2455919 = 3683879) B3683879
theorem B1636775 : Blo 1636017 1636775 := bstep (se 1 (by rfl) ⟨1227581, by rfl⟩ : syracuseStep 1636775 = 2455163) B2455163
theorem B1841575 : Blo 1636017 1841575 := bstep (se 1 (by rfl) ⟨1381181, by rfl⟩ : syracuseStep 1841575 = 2762363) B2762363
theorem B3684833 : Blo 1636017 3684833 := bstep (se 2 (by rfl) ⟨1381812, by rfl⟩ : syracuseStep 3684833 = 2763625) B2763625
theorem B1636859 : Blo 1636017 1636859 := bstep (se 1 (by rfl) ⟨1227644, by rfl⟩ : syracuseStep 1636859 = 2455289) B2455289
theorem B6994471 : Blo 1636017 6994471 := bstep (se 1 (by rfl) ⟨5245853, by rfl⟩ : syracuseStep 6994471 = 10491707) B10491707
theorem B1636927 : Blo 1636017 1636927 := bstep (se 1 (by rfl) ⟨1227695, by rfl⟩ : syracuseStep 1636927 = 2455391) B2455391
theorem B1636935 : Blo 1636017 1636935 := bstep (se 1 (by rfl) ⟨1227701, by rfl⟩ : syracuseStep 1636935 = 2455403) B2455403
theorem B2456135 : Blo 1636017 2456135 := bstep (se 1 (by rfl) ⟨1842101, by rfl⟩ : syracuseStep 2456135 = 3684203) B3684203
theorem B6994505 : Blo 1636017 6994505 := bstep (se 2 (by rfl) ⟨2622939, by rfl⟩ : syracuseStep 6994505 = 5245879) B5245879
theorem B2456171 : Blo 1636017 2456171 := bstep (se 1 (by rfl) ⟨1842128, by rfl⟩ : syracuseStep 2456171 = 3684257) B3684257
theorem B4143737 : Blo 1636017 4143737 := bstep (se 2 (by rfl) ⟨1553901, by rfl⟩ : syracuseStep 4143737 = 3107803) B3107803
theorem B8288891 : Blo 1636017 8288891 := bstep (se 1 (by rfl) ⟨6216668, by rfl⟩ : syracuseStep 8288891 = 12433337) B12433337
theorem B9321155 : Blo 1636017 9321155 := bstep (se 1 (by rfl) ⟨6990866, by rfl⟩ : syracuseStep 9321155 = 13981733) B13981733
theorem B1637087 : Blo 1636017 1637087 := bstep (se 1 (by rfl) ⟨1227815, by rfl⟩ : syracuseStep 1637087 = 2455631) B2455631
theorem B7469815 : Blo 1636017 7469815 := bstep (se 1 (by rfl) ⟨5602361, by rfl⟩ : syracuseStep 7469815 = 11204723) B11204723
theorem B3685139 : Blo 1636017 3685139 := bstep (se 1 (by rfl) ⟨2763854, by rfl⟩ : syracuseStep 3685139 = 5527709) B5527709
theorem B1637167 : Blo 1636017 1637167 := bstep (se 1 (by rfl) ⟨1227875, by rfl⟩ : syracuseStep 1637167 = 2455751) B2455751
theorem B2456399 : Blo 1636017 2456399 := bstep (se 1 (by rfl) ⟨1842299, by rfl⟩ : syracuseStep 2456399 = 3684599) B3684599
theorem B1637275 : Blo 1636017 1637275 := bstep (se 1 (by rfl) ⟨1227956, by rfl⟩ : syracuseStep 1637275 = 2455913) B2455913
theorem B1637327 : Blo 1636017 1637327 := bstep (se 1 (by rfl) ⟨1227995, by rfl⟩ : syracuseStep 1637327 = 2455991) B2455991
theorem B1637351 : Blo 1636017 1637351 := bstep (se 1 (by rfl) ⟨1228013, by rfl⟩ : syracuseStep 1637351 = 2456027) B2456027
theorem B1842151 : Blo 1636017 1842151 := bstep (se 1 (by rfl) ⟨1381613, by rfl⟩ : syracuseStep 1842151 = 2763227) B2763227
theorem B14941235 : Blo 1636017 14941235 := bstep (se 1 (by rfl) ⟨11205926, by rfl⟩ : syracuseStep 14941235 = 22411853) B22411853
theorem B181550159 : Blo 1636017 181550159 := bstep (se 1 (by rfl) ⟨136162619, by rfl⟩ : syracuseStep 181550159 = 272325239) B272325239
theorem B80698447 : Blo 1636017 80698447 := bstep (se 1 (by rfl) ⟨60523835, by rfl⟩ : syracuseStep 80698447 = 121047671) B121047671
theorem B3685499 : Blo 1636017 3685499 := bstep (se 1 (by rfl) ⟨2764124, by rfl⟩ : syracuseStep 3685499 = 5528249) B5528249
theorem B2456795 : Blo 1636017 2456795 := bstep (se 1 (by rfl) ⟨1842596, by rfl⟩ : syracuseStep 2456795 = 3685193) B3685193
theorem B1637663 : Blo 1636017 1637663 := bstep (se 1 (by rfl) ⟨1228247, by rfl⟩ : syracuseStep 1637663 = 2456495) B2456495
theorem B1637723 : Blo 1636017 1637723 := bstep (se 1 (by rfl) ⟨1228292, by rfl⟩ : syracuseStep 1637723 = 2456585) B2456585
theorem B272563555 : Blo 1636017 272563555 := bstep (se 1 (by rfl) ⟨204422666, by rfl⟩ : syracuseStep 272563555 = 408845333) B408845333
theorem B2071919 : Blo 1636017 2071919 := bstep (se 1 (by rfl) ⟨1553939, by rfl⟩ : syracuseStep 2071919 = 3107879) B3107879
theorem B1637743 : Blo 1636017 1637743 := bstep (se 1 (by rfl) ⟨1228307, by rfl⟩ : syracuseStep 1637743 = 2456615) B2456615
theorem B2456969 : Blo 1636017 2456969 := bstep (se 2 (by rfl) ⟨921363, by rfl⟩ : syracuseStep 2456969 = 1842727) B1842727
theorem B39820709 : Blo 1636017 39820709 := bstep (se 4 (by rfl) ⟨3733191, by rfl⟩ : syracuseStep 39820709 = 7466383) B7466383
theorem B2071975 : Blo 1636017 2071975 := bstep (se 1 (by rfl) ⟨1553981, by rfl⟩ : syracuseStep 2071975 = 3107963) B3107963
theorem B1637799 : Blo 1636017 1637799 := bstep (se 1 (by rfl) ⟨1228349, by rfl⟩ : syracuseStep 1637799 = 2456699) B2456699
theorem B4660679 : Blo 1636017 4660679 := bstep (se 1 (by rfl) ⟨3495509, by rfl⟩ : syracuseStep 4660679 = 6991019) B6991019
theorem B255180253 : Blo 1636017 255180253 := bstep (se 3 (by rfl) ⟨47846297, by rfl⟩ : syracuseStep 255180253 = 95692595) B95692595
theorem B1637883 : Blo 1636017 1637883 := bstep (se 1 (by rfl) ⟨1228412, by rfl⟩ : syracuseStep 1637883 = 2456825) B2456825
theorem B1637951 : Blo 1636017 1637951 := bstep (se 1 (by rfl) ⟨1228463, by rfl⟩ : syracuseStep 1637951 = 2456927) B2456927
theorem B1637959 : Blo 1636017 1637959 := bstep (se 1 (by rfl) ⟨1228469, by rfl⟩ : syracuseStep 1637959 = 2456939) B2456939
theorem B6823507 : Blo 1636017 6823507 := bstep (se 1 (by rfl) ⟨5117630, by rfl⟩ : syracuseStep 6823507 = 10235261) B10235261
theorem B11353715 : Blo 1636017 11353715 := bstep (se 1 (by rfl) ⟨8515286, by rfl⟩ : syracuseStep 11353715 = 17030573) B17030573
theorem B2072299 : Blo 1636017 2072299 := bstep (se 1 (by rfl) ⟨1554224, by rfl⟩ : syracuseStep 2072299 = 3108449) B3108449
theorem B6217519 : Blo 1636017 6217519 := bstep (se 1 (by rfl) ⟨4663139, by rfl⟩ : syracuseStep 6217519 = 9326279) B9326279
theorem B3497833 : Blo 1636017 3497833 := bstep (se 2 (by rfl) ⟨1311687, by rfl⟩ : syracuseStep 3497833 = 2623375) B2623375
theorem B31481729 : Blo 1636017 31481729 := bstep (se 2 (by rfl) ⟨11805648, by rfl⟩ : syracuseStep 31481729 = 23611297) B23611297
theorem B14925761 : Blo 1636017 14925761 := bstep (se 2 (by rfl) ⟨5597160, by rfl⟩ : syracuseStep 14925761 = 11194321) B11194321
theorem B9961703 : Blo 1636017 9961703 := bstep (se 1 (by rfl) ⟨7471277, by rfl⟩ : syracuseStep 9961703 = 14942555) B14942555
theorem B2761087 : Blo 1636017 2761087 := bstep (se 1 (by rfl) ⟨2070815, by rfl⟩ : syracuseStep 2761087 = 4141631) B4141631
theorem B2957705 : Blo 1636017 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B3932603 : Blo 1636017 3932603 := bstep (se 1 (by rfl) ⟨2949452, by rfl⟩ : syracuseStep 3932603 = 5898905) B5898905
theorem B2949625 : Blo 1636017 2949625 := bstep (se 2 (by rfl) ⟨1106109, by rfl⟩ : syracuseStep 2949625 = 2212219) B2212219
theorem B2761519 : Blo 1636017 2761519 := bstep (se 1 (by rfl) ⟨2071139, by rfl⟩ : syracuseStep 2761519 = 4142279) B4142279
theorem B12428477 : Blo 1636017 12428477 := bstep (se 3 (by rfl) ⟨2330339, by rfl⟩ : syracuseStep 12428477 = 4660679) B4660679
theorem B6300995 : Blo 1636017 6300995 := bstep (se 1 (by rfl) ⟨4725746, by rfl⟩ : syracuseStep 6300995 = 9451493) B9451493
theorem B18646361 : Blo 1636017 18646361 := bstep (se 2 (by rfl) ⟨6992385, by rfl⟩ : syracuseStep 18646361 = 13984771) B13984771
theorem B5522795 : Blo 1636017 5522795 := bstep (se 1 (by rfl) ⟨4142096, by rfl⟩ : syracuseStep 5522795 = 8284193) B8284193
theorem B5522903 : Blo 1636017 5522903 := bstep (se 1 (by rfl) ⟨4142177, by rfl⟩ : syracuseStep 5522903 = 8284355) B8284355
theorem B8283707 : Blo 1636017 8283707 := bstep (se 1 (by rfl) ⟨6212780, by rfl⟩ : syracuseStep 8283707 = 12425561) B12425561
theorem B5523065 : Blo 1636017 5523065 := bstep (se 2 (by rfl) ⟨2071149, by rfl⟩ : syracuseStep 5523065 = 4142299) B4142299
theorem B4663003 : Blo 1636017 4663003 := bstep (se 1 (by rfl) ⟨3497252, by rfl⟩ : syracuseStep 4663003 = 6994505) B6994505
theorem B2762491 : Blo 1636017 2762491 := bstep (se 1 (by rfl) ⟨2071868, by rfl⟩ : syracuseStep 2762491 = 4143737) B4143737
theorem B23594813 : Blo 1636017 23594813 := bstep (se 3 (by rfl) ⟨4424027, by rfl⟩ : syracuseStep 23594813 = 8848055) B8848055
theorem B26560385 : Blo 1636017 26560385 := bstep (se 2 (by rfl) ⟨9960144, by rfl⟩ : syracuseStep 26560385 = 19920289) B19920289
theorem B18655109 : Blo 1636017 18655109 := bstep (se 4 (by rfl) ⟨1748916, by rfl⟩ : syracuseStep 18655109 = 3497833) B3497833
theorem B2762633 : Blo 1636017 2762633 := bstep (se 2 (by rfl) ⟨1035987, by rfl⟩ : syracuseStep 2762633 = 2071975) B2071975
theorem B340240337 : Blo 1636017 340240337 := bstep (se 2 (by rfl) ⟨127590126, by rfl⟩ : syracuseStep 340240337 = 255180253) B255180253
theorem B23922803 : Blo 1636017 23922803 := bstep (se 1 (by rfl) ⟨17942102, by rfl⟩ : syracuseStep 23922803 = 35884205) B35884205
theorem B2951471 : Blo 1636017 2951471 := bstep (se 1 (by rfl) ⟨2213603, by rfl⟩ : syracuseStep 2951471 = 4427207) B4427207
theorem B2763065 : Blo 1636017 2763065 := bstep (se 2 (by rfl) ⟨1036149, by rfl⟩ : syracuseStep 2763065 = 2072299) B2072299
theorem B3934747 : Blo 1636017 3934747 := bstep (se 1 (by rfl) ⟨2951060, by rfl⟩ : syracuseStep 3934747 = 5902121) B5902121
theorem B4426427 : Blo 1636017 4426427 := bstep (se 1 (by rfl) ⟨3319820, by rfl⟩ : syracuseStep 4426427 = 6639641) B6639641
theorem B2763679 : Blo 1636017 2763679 := bstep (se 1 (by rfl) ⟨2072759, by rfl⟩ : syracuseStep 2763679 = 4145519) B4145519
theorem B11799539 : Blo 1636017 11799539 := bstep (se 1 (by rfl) ⟨8849654, by rfl⟩ : syracuseStep 11799539 = 17699309) B17699309
theorem B5524577 : Blo 1636017 5524577 := bstep (se 2 (by rfl) ⟨2071716, by rfl⟩ : syracuseStep 5524577 = 4143433) B4143433
theorem B8285327 : Blo 1636017 8285327 := bstep (se 1 (by rfl) ⟨6213995, by rfl⟩ : syracuseStep 8285327 = 12427991) B12427991
theorem B537463997 : Blo 1636017 537463997 := bstep (se 3 (by rfl) ⟨100774499, by rfl⟩ : syracuseStep 537463997 = 201548999) B201548999
theorem B3681503 : Blo 1636017 3681503 := bstep (se 1 (by rfl) ⟨2761127, by rfl⟩ : syracuseStep 3681503 = 5522255) B5522255
theorem B11799857 : Blo 1636017 11799857 := bstep (se 2 (by rfl) ⟨4424946, by rfl⟩ : syracuseStep 11799857 = 8849893) B8849893
theorem B2764111 : Blo 1636017 2764111 := bstep (se 1 (by rfl) ⟨2073083, by rfl⟩ : syracuseStep 2764111 = 4146167) B4146167
theorem B9325961 : Blo 1636017 9325961 := bstep (se 2 (by rfl) ⟨3497235, by rfl⟩ : syracuseStep 9325961 = 6994471) B6994471
theorem B3681719 : Blo 1636017 3681719 := bstep (se 1 (by rfl) ⟨2761289, by rfl⟩ : syracuseStep 3681719 = 5522579) B5522579
theorem B2330203 : Blo 1636017 2330203 := bstep (se 1 (by rfl) ⟨1747652, by rfl⟩ : syracuseStep 2330203 = 3495305) B3495305
theorem B3681899 : Blo 1636017 3681899 := bstep (se 1 (by rfl) ⟨2761424, by rfl⟩ : syracuseStep 3681899 = 5522849) B5522849
theorem B5525117 : Blo 1636017 5525117 := bstep (se 3 (by rfl) ⟨1035959, by rfl⟩ : syracuseStep 5525117 = 2071919) B2071919
theorem B4976423 : Blo 1636017 4976423 := bstep (se 1 (by rfl) ⟨3732317, by rfl⟩ : syracuseStep 4976423 = 7464635) B7464635
theorem B100790081 : Blo 1636017 100790081 := bstep (se 2 (by rfl) ⟨37796280, by rfl⟩ : syracuseStep 100790081 = 75592561) B75592561
theorem B3682169 : Blo 1636017 3682169 := bstep (se 2 (by rfl) ⟨1380813, by rfl⟩ : syracuseStep 3682169 = 2761627) B2761627
theorem B13266827 : Blo 1636017 13266827 := bstep (se 1 (by rfl) ⟨9950120, by rfl⟩ : syracuseStep 13266827 = 19900241) B19900241
theorem B5525387 : Blo 1636017 5525387 := bstep (se 1 (by rfl) ⟨4144040, by rfl⟩ : syracuseStep 5525387 = 8288081) B8288081
theorem B6991771 : Blo 1636017 6991771 := bstep (se 1 (by rfl) ⟨5243828, by rfl⟩ : syracuseStep 6991771 = 10487657) B10487657
theorem B5902235 : Blo 1636017 5902235 := bstep (se 1 (by rfl) ⟨4426676, by rfl⟩ : syracuseStep 5902235 = 8853353) B8853353
theorem B107597929 : Blo 1636017 107597929 := bstep (se 2 (by rfl) ⟨40349223, by rfl⟩ : syracuseStep 107597929 = 80698447) B80698447
theorem B4141439 : Blo 1636017 4141439 := bstep (se 1 (by rfl) ⟨3106079, by rfl⟩ : syracuseStep 4141439 = 6212159) B6212159
theorem B5525927 : Blo 1636017 5525927 := bstep (se 1 (by rfl) ⟨4144445, by rfl⟩ : syracuseStep 5525927 = 8288891) B8288891
theorem B26915273 : Blo 1636017 26915273 := bstep (se 2 (by rfl) ⟨10093227, by rfl⟩ : syracuseStep 26915273 = 20186455) B20186455
theorem B6214103 : Blo 1636017 6214103 := bstep (se 1 (by rfl) ⟨4660577, by rfl⟩ : syracuseStep 6214103 = 9321155) B9321155
theorem B363418073 : Blo 1636017 363418073 := bstep (se 2 (by rfl) ⟨136281777, by rfl⟩ : syracuseStep 363418073 = 272563555) B272563555
theorem B4141651 : Blo 1636017 4141651 := bstep (se 1 (by rfl) ⟨3106238, by rfl⟩ : syracuseStep 4141651 = 6212477) B6212477
theorem B2454119 : Blo 1636017 2454119 := bstep (se 1 (by rfl) ⟨1840589, by rfl⟩ : syracuseStep 2454119 = 3681179) B3681179
theorem B7869089 : Blo 1636017 7869089 := bstep (se 2 (by rfl) ⟨2950908, by rfl⟩ : syracuseStep 7869089 = 5901817) B5901817
theorem B10089131 : Blo 1636017 10089131 := bstep (se 1 (by rfl) ⟨7566848, by rfl⟩ : syracuseStep 10089131 = 15133697) B15133697
theorem B121033439 : Blo 1636017 121033439 := bstep (se 1 (by rfl) ⟨90775079, by rfl⟩ : syracuseStep 121033439 = 181550159) B181550159
theorem B2454251 : Blo 1636017 2454251 := bstep (se 1 (by rfl) ⟨1840688, by rfl⟩ : syracuseStep 2454251 = 3681377) B3681377
theorem B2454281 : Blo 1636017 2454281 := bstep (se 2 (by rfl) ⟨920355, by rfl⟩ : syracuseStep 2454281 = 1840711) B1840711
theorem B9098009 : Blo 1636017 9098009 := bstep (se 2 (by rfl) ⟨3411753, by rfl⟩ : syracuseStep 9098009 = 6823507) B6823507
theorem B2331433 : Blo 1636017 2331433 := bstep (se 2 (by rfl) ⟨874287, by rfl⟩ : syracuseStep 2331433 = 1748575) B1748575
theorem B2454383 : Blo 1636017 2454383 := bstep (se 1 (by rfl) ⟨1840787, by rfl⟩ : syracuseStep 2454383 = 3681575) B3681575
theorem B26547139 : Blo 1636017 26547139 := bstep (se 1 (by rfl) ⟨19910354, by rfl⟩ : syracuseStep 26547139 = 39820709) B39820709
theorem B2454635 : Blo 1636017 2454635 := bstep (se 1 (by rfl) ⟨1840976, by rfl⟩ : syracuseStep 2454635 = 3681953) B3681953
theorem B2241743 : Blo 1636017 2241743 := bstep (se 1 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 2241743 = 3362615) B3362615
theorem B9950507 : Blo 1636017 9950507 := bstep (se 1 (by rfl) ⟨7462880, by rfl⟩ : syracuseStep 9950507 = 14925761) B14925761
theorem B2454875 : Blo 1636017 2454875 := bstep (se 1 (by rfl) ⟨1841156, by rfl⟩ : syracuseStep 2454875 = 3682313) B3682313
theorem B10491245 : Blo 1636017 10491245 := bstep (se 3 (by rfl) ⟨1967108, by rfl⟩ : syracuseStep 10491245 = 3934217) B3934217
theorem B15947297 : Blo 1636017 15947297 := bstep (se 2 (by rfl) ⟨5980236, by rfl⟩ : syracuseStep 15947297 = 11960473) B11960473
theorem B6993479 : Blo 1636017 6993479 := bstep (se 1 (by rfl) ⟨5245109, by rfl⟩ : syracuseStep 6993479 = 10490219) B10490219
theorem B2455151 : Blo 1636017 2455151 := bstep (se 1 (by rfl) ⟨1841363, by rfl⟩ : syracuseStep 2455151 = 3682727) B3682727
theorem B13981355 : Blo 1636017 13981355 := bstep (se 1 (by rfl) ⟨10486016, by rfl⟩ : syracuseStep 13981355 = 20972033) B20972033
theorem B2455223 : Blo 1636017 2455223 := bstep (se 1 (by rfl) ⟨1841417, by rfl⟩ : syracuseStep 2455223 = 3682835) B3682835
theorem B3684023 : Blo 1636017 3684023 := bstep (se 1 (by rfl) ⟨2763017, by rfl⟩ : syracuseStep 3684023 = 5526035) B5526035
theorem B5527223 : Blo 1636017 5527223 := bstep (se 1 (by rfl) ⟨4145417, by rfl⟩ : syracuseStep 5527223 = 8290835) B8290835
theorem B2455259 : Blo 1636017 2455259 := bstep (se 1 (by rfl) ⟨1841444, by rfl⟩ : syracuseStep 2455259 = 3682889) B3682889
theorem B1636091 : Blo 1636017 1636091 := bstep (se 1 (by rfl) ⟨1227068, by rfl⟩ : syracuseStep 1636091 = 2454137) B2454137
theorem B1840891 : Blo 1636017 1840891 := bstep (se 1 (by rfl) ⟨1380668, by rfl⟩ : syracuseStep 1840891 = 2761337) B2761337
theorem B1636127 : Blo 1636017 1636127 := bstep (se 1 (by rfl) ⟨1227095, by rfl⟩ : syracuseStep 1636127 = 2454191) B2454191
theorem B1840927 : Blo 1636017 1840927 := bstep (se 1 (by rfl) ⟨1380695, by rfl⟩ : syracuseStep 1840927 = 2761391) B2761391
theorem B1636159 : Blo 1636017 1636159 := bstep (se 1 (by rfl) ⟨1227119, by rfl⟩ : syracuseStep 1636159 = 2454239) B2454239
theorem B2455433 : Blo 1636017 2455433 := bstep (se 2 (by rfl) ⟨920787, by rfl⟩ : syracuseStep 2455433 = 1841575) B1841575
theorem B1636335 : Blo 1636017 1636335 := bstep (se 1 (by rfl) ⟨1227251, by rfl⟩ : syracuseStep 1636335 = 2454503) B2454503
theorem B2455535 : Blo 1636017 2455535 := bstep (se 1 (by rfl) ⟨1841651, by rfl⟩ : syracuseStep 2455535 = 3683303) B3683303
theorem B5314585 : Blo 1636017 5314585 := bstep (se 2 (by rfl) ⟨1992969, by rfl⟩ : syracuseStep 5314585 = 3985939) B3985939
theorem B2070623 : Blo 1636017 2070623 := bstep (se 1 (by rfl) ⟨1552967, by rfl⟩ : syracuseStep 2070623 = 3105935) B3105935
theorem B3643535 : Blo 1636017 3643535 := bstep (se 1 (by rfl) ⟨2732651, by rfl⟩ : syracuseStep 3643535 = 5465303) B5465303
theorem B1636507 : Blo 1636017 1636507 := bstep (se 1 (by rfl) ⟨1227380, by rfl⟩ : syracuseStep 1636507 = 2454761) B2454761
theorem B1636543 : Blo 1636017 1636543 := bstep (se 1 (by rfl) ⟨1227407, by rfl⟩ : syracuseStep 1636543 = 2454815) B2454815
theorem B6215879 : Blo 1636017 6215879 := bstep (se 1 (by rfl) ⟨4661909, by rfl⟩ : syracuseStep 6215879 = 9323819) B9323819
theorem B2455787 : Blo 1636017 2455787 := bstep (se 1 (by rfl) ⟨1841840, by rfl⟩ : syracuseStep 2455787 = 3683681) B3683681
theorem B2455847 : Blo 1636017 2455847 := bstep (se 1 (by rfl) ⟨1841885, by rfl⟩ : syracuseStep 2455847 = 3683771) B3683771
theorem B1636655 : Blo 1636017 1636655 := bstep (se 1 (by rfl) ⟨1227491, by rfl⟩ : syracuseStep 1636655 = 2454983) B2454983
theorem B9959753 : Blo 1636017 9959753 := bstep (se 2 (by rfl) ⟨3734907, by rfl⟩ : syracuseStep 9959753 = 7469815) B7469815
theorem B2455931 : Blo 1636017 2455931 := bstep (se 1 (by rfl) ⟨1841948, by rfl⟩ : syracuseStep 2455931 = 3683897) B3683897
theorem B6822319 : Blo 1636017 6822319 := bstep (se 1 (by rfl) ⟨5116739, by rfl⟩ : syracuseStep 6822319 = 10233479) B10233479
theorem B7870895 : Blo 1636017 7870895 := bstep (se 1 (by rfl) ⟨5903171, by rfl⟩ : syracuseStep 7870895 = 11806343) B11806343
theorem B23591411 : Blo 1636017 23591411 := bstep (se 1 (by rfl) ⟨17693558, by rfl⟩ : syracuseStep 23591411 = 35387117) B35387117
theorem B1636891 : Blo 1636017 1636891 := bstep (se 1 (by rfl) ⟨1227668, by rfl⟩ : syracuseStep 1636891 = 2455337) B2455337
theorem B1636895 : Blo 1636017 1636895 := bstep (se 1 (by rfl) ⟨1227671, by rfl⟩ : syracuseStep 1636895 = 2455343) B2455343
theorem B2456201 : Blo 1636017 2456201 := bstep (se 2 (by rfl) ⟨921075, by rfl⟩ : syracuseStep 2456201 = 1842151) B1842151
theorem B13982381 : Blo 1636017 13982381 := bstep (se 3 (by rfl) ⟨2621696, by rfl⟩ : syracuseStep 13982381 = 5243393) B5243393
theorem B2456375 : Blo 1636017 2456375 := bstep (se 1 (by rfl) ⟨1842281, by rfl⟩ : syracuseStep 2456375 = 3684563) B3684563
theorem B1637211 : Blo 1636017 1637211 := bstep (se 1 (by rfl) ⟨1227908, by rfl⟩ : syracuseStep 1637211 = 2455817) B2455817
theorem B2456411 : Blo 1636017 2456411 := bstep (se 1 (by rfl) ⟨1842308, by rfl⟩ : syracuseStep 2456411 = 3684617) B3684617
theorem B3685211 : Blo 1636017 3685211 := bstep (se 1 (by rfl) ⟨2763908, by rfl⟩ : syracuseStep 3685211 = 5527817) B5527817
theorem B4144031 : Blo 1636017 4144031 := bstep (se 1 (by rfl) ⟨3108023, by rfl⟩ : syracuseStep 4144031 = 6216047) B6216047
theorem B1637279 : Blo 1636017 1637279 := bstep (se 1 (by rfl) ⟨1227959, by rfl⟩ : syracuseStep 1637279 = 2455919) B2455919
theorem B1842079 : Blo 1636017 1842079 := bstep (se 1 (by rfl) ⟨1381559, by rfl⟩ : syracuseStep 1842079 = 2763119) B2763119
theorem B2456555 : Blo 1636017 2456555 := bstep (se 1 (by rfl) ⟨1842416, by rfl⟩ : syracuseStep 2456555 = 3684833) B3684833
theorem B1637423 : Blo 1636017 1637423 := bstep (se 1 (by rfl) ⟨1228067, by rfl⟩ : syracuseStep 1637423 = 2456135) B2456135
theorem B1842223 : Blo 1636017 1842223 := bstep (se 1 (by rfl) ⟨1381667, by rfl⟩ : syracuseStep 1842223 = 2763335) B2763335
theorem B1637447 : Blo 1636017 1637447 := bstep (se 1 (by rfl) ⟨1228085, by rfl⟩ : syracuseStep 1637447 = 2456171) B2456171
theorem B6216851 : Blo 1636017 6216851 := bstep (se 1 (by rfl) ⟨4662638, by rfl⟩ : syracuseStep 6216851 = 9325277) B9325277
theorem B2456759 : Blo 1636017 2456759 := bstep (se 1 (by rfl) ⟨1842569, by rfl⟩ : syracuseStep 2456759 = 3685139) B3685139
theorem B47209675 : Blo 1636017 47209675 := bstep (se 1 (by rfl) ⟨35407256, by rfl⟩ : syracuseStep 47209675 = 70814513) B70814513
theorem B1637599 : Blo 1636017 1637599 := bstep (se 1 (by rfl) ⟨1228199, by rfl⟩ : syracuseStep 1637599 = 2456399) B2456399
theorem B1842511 : Blo 1636017 1842511 := bstep (se 1 (by rfl) ⟨1381883, by rfl⟩ : syracuseStep 1842511 = 2763767) B2763767
theorem B9960823 : Blo 1636017 9960823 := bstep (se 1 (by rfl) ⟨7470617, by rfl⟩ : syracuseStep 9960823 = 14941235) B14941235
theorem B2456999 : Blo 1636017 2456999 := bstep (se 1 (by rfl) ⟨1842749, by rfl⟩ : syracuseStep 2456999 = 3685499) B3685499
theorem B1637863 : Blo 1636017 1637863 := bstep (se 1 (by rfl) ⟨1228397, by rfl⟩ : syracuseStep 1637863 = 2456795) B2456795
theorem B1637979 : Blo 1636017 1637979 := bstep (se 1 (by rfl) ⟨1228484, by rfl⟩ : syracuseStep 1637979 = 2456969) B2456969
theorem B8290025 : Blo 1636017 8290025 := bstep (se 2 (by rfl) ⟨3108759, by rfl⟩ : syracuseStep 8290025 = 6217519) B6217519
theorem B7569143 : Blo 1636017 7569143 := bstep (se 1 (by rfl) ⟨5676857, by rfl⟩ : syracuseStep 7569143 = 11353715) B11353715
theorem B6299515 : Blo 1636017 6299515 := bstep (se 1 (by rfl) ⟨4724636, by rfl⟩ : syracuseStep 6299515 = 9449273) B9449273
theorem B20987819 : Blo 1636017 20987819 := bstep (se 1 (by rfl) ⟨15740864, by rfl⟩ : syracuseStep 20987819 = 31481729) B31481729
theorem B7086113 : Blo 1636017 7086113 := bstep (se 2 (by rfl) ⟨2657292, by rfl⟩ : syracuseStep 7086113 = 5314585) B5314585
theorem B5521661 : Blo 1636017 5521661 := bstep (se 3 (by rfl) ⟨1035311, by rfl⟩ : syracuseStep 5521661 = 2070623) B2070623
theorem B2760959 : Blo 1636017 2760959 := bstep (se 1 (by rfl) ⟨2070719, by rfl⟩ : syracuseStep 2760959 = 4141439) B4141439
theorem B2621735 : Blo 1636017 2621735 := bstep (se 1 (by rfl) ⟨1966301, by rfl⟩ : syracuseStep 2621735 = 3932603) B3932603
theorem B242278715 : Blo 1636017 242278715 := bstep (se 1 (by rfl) ⟨181709036, by rfl⟩ : syracuseStep 242278715 = 363418073) B363418073
theorem B5522201 : Blo 1636017 5522201 := bstep (se 2 (by rfl) ⟨2070825, by rfl⟩ : syracuseStep 5522201 = 4141651) B4141651
theorem B16802653 : Blo 1636017 16802653 := bstep (se 3 (by rfl) ⟨3150497, by rfl⟩ : syracuseStep 16802653 = 6300995) B6300995
theorem B5522471 : Blo 1636017 5522471 := bstep (se 1 (by rfl) ⟨4141853, by rfl⟩ : syracuseStep 5522471 = 8283707) B8283707
theorem B15729875 : Blo 1636017 15729875 := bstep (se 1 (by rfl) ⟨11797406, by rfl⟩ : syracuseStep 15729875 = 23594813) B23594813
theorem B12436739 : Blo 1636017 12436739 := bstep (se 1 (by rfl) ⟨9327554, by rfl⟩ : syracuseStep 12436739 = 18655109) B18655109
theorem B1967647 : Blo 1636017 1967647 := bstep (se 1 (by rfl) ⟨1475735, by rfl⟩ : syracuseStep 1967647 = 2951471) B2951471
theorem B26904349 : Blo 1636017 26904349 := bstep (se 3 (by rfl) ⟨5044565, by rfl⟩ : syracuseStep 26904349 = 10089131) B10089131
theorem B13281097 : Blo 1636017 13281097 := bstep (se 2 (by rfl) ⟨4980411, by rfl⟩ : syracuseStep 13281097 = 9960823) B9960823
theorem B2762687 : Blo 1636017 2762687 := bstep (se 1 (by rfl) ⟨2072015, by rfl⟩ : syracuseStep 2762687 = 4144031) B4144031
theorem B33597413 : Blo 1636017 33597413 := bstep (se 4 (by rfl) ⟨3149757, by rfl⟩ : syracuseStep 33597413 = 6299515) B6299515
theorem B7866359 : Blo 1636017 7866359 := bstep (se 1 (by rfl) ⟨5899769, by rfl⟩ : syracuseStep 7866359 = 11799539) B11799539
theorem B5523551 : Blo 1636017 5523551 := bstep (se 1 (by rfl) ⟨4142663, by rfl⟩ : syracuseStep 5523551 = 8285327) B8285327
theorem B3106937 : Blo 1636017 3106937 := bstep (se 2 (by rfl) ⟨1165101, by rfl⟩ : syracuseStep 3106937 = 2330203) B2330203
theorem B7866571 : Blo 1636017 7866571 := bstep (se 1 (by rfl) ⟨5899928, by rfl⟩ : syracuseStep 7866571 = 11799857) B11799857
theorem B67193387 : Blo 1636017 67193387 := bstep (se 1 (by rfl) ⟨50395040, by rfl⟩ : syracuseStep 67193387 = 100790081) B100790081
theorem B3934823 : Blo 1636017 3934823 := bstep (se 1 (by rfl) ⟨2951117, by rfl⟩ : syracuseStep 3934823 = 5902235) B5902235
theorem B15731333 : Blo 1636017 15731333 := bstep (se 4 (by rfl) ⟨1474812, by rfl⟩ : syracuseStep 15731333 = 2949625) B2949625
theorem B17943515 : Blo 1636017 17943515 := bstep (se 1 (by rfl) ⟨13457636, by rfl⟩ : syracuseStep 17943515 = 26915273) B26915273
theorem B5246059 : Blo 1636017 5246059 := bstep (se 1 (by rfl) ⟨3934544, by rfl⟩ : syracuseStep 5246059 = 7869089) B7869089
theorem B3681449 : Blo 1636017 3681449 := bstep (se 2 (by rfl) ⟨1380543, by rfl⟩ : syracuseStep 3681449 = 2761087) B2761087
theorem B6065339 : Blo 1636017 6065339 := bstep (se 1 (by rfl) ⟨4549004, by rfl⟩ : syracuseStep 6065339 = 9098009) B9098009
theorem B9096425 : Blo 1636017 9096425 := bstep (se 2 (by rfl) ⟨3411159, by rfl⟩ : syracuseStep 9096425 = 6822319) B6822319
theorem B5246329 : Blo 1636017 5246329 := bstep (se 2 (by rfl) ⟨1967373, by rfl⟩ : syracuseStep 5246329 = 3934747) B3934747
theorem B8285651 : Blo 1636017 8285651 := bstep (se 1 (by rfl) ⟨6214238, by rfl⟩ : syracuseStep 8285651 = 12428477) B12428477
theorem B12430907 : Blo 1636017 12430907 := bstep (se 1 (by rfl) ⟨9323180, by rfl⟩ : syracuseStep 12430907 = 18646361) B18646361
theorem B3681863 : Blo 1636017 3681863 := bstep (se 1 (by rfl) ⟨2761397, by rfl⟩ : syracuseStep 3681863 = 5522795) B5522795
theorem B3681935 : Blo 1636017 3681935 := bstep (se 1 (by rfl) ⟨2761451, by rfl⟩ : syracuseStep 3681935 = 5522903) B5522903
theorem B3682025 : Blo 1636017 3682025 := bstep (se 2 (by rfl) ⟨1380759, by rfl⟩ : syracuseStep 3682025 = 2761519) B2761519
theorem B3682043 : Blo 1636017 3682043 := bstep (se 1 (by rfl) ⟨2761532, by rfl⟩ : syracuseStep 3682043 = 5523065) B5523065
theorem B17706923 : Blo 1636017 17706923 := bstep (se 1 (by rfl) ⟨13280192, by rfl⟩ : syracuseStep 17706923 = 26560385) B26560385
theorem B2429023 : Blo 1636017 2429023 := bstep (se 1 (by rfl) ⟨1821767, by rfl⟩ : syracuseStep 2429023 = 3643535) B3643535
theorem B18649277 : Blo 1636017 18649277 := bstep (se 3 (by rfl) ⟨3496739, by rfl⟩ : syracuseStep 18649277 = 6993479) B6993479
theorem B6639835 : Blo 1636017 6639835 := bstep (se 1 (by rfl) ⟨4979876, by rfl⟩ : syracuseStep 6639835 = 9959753) B9959753
theorem B5247263 : Blo 1636017 5247263 := bstep (se 1 (by rfl) ⟨3935447, by rfl⟩ : syracuseStep 5247263 = 7870895) B7870895
theorem B3683051 : Blo 1636017 3683051 := bstep (se 1 (by rfl) ⟨2762288, by rfl⟩ : syracuseStep 3683051 = 5524577) B5524577
theorem B2454335 : Blo 1636017 2454335 := bstep (se 1 (by rfl) ⟨1840751, by rfl⟩ : syracuseStep 2454335 = 3681503) B3681503
theorem B2454479 : Blo 1636017 2454479 := bstep (se 1 (by rfl) ⟨1840859, by rfl⟩ : syracuseStep 2454479 = 3681719) B3681719
theorem B2454521 : Blo 1636017 2454521 := bstep (se 2 (by rfl) ⟨920445, by rfl⟩ : syracuseStep 2454521 = 1840891) B1840891
theorem B3683321 : Blo 1636017 3683321 := bstep (se 2 (by rfl) ⟨1381245, by rfl⟩ : syracuseStep 3683321 = 2762491) B2762491
theorem B2454569 : Blo 1636017 2454569 := bstep (se 2 (by rfl) ⟨920463, by rfl⟩ : syracuseStep 2454569 = 1840927) B1840927
theorem B2454599 : Blo 1636017 2454599 := bstep (se 1 (by rfl) ⟨1840949, by rfl⟩ : syracuseStep 2454599 = 3681899) B3681899
theorem B3683411 : Blo 1636017 3683411 := bstep (se 1 (by rfl) ⟨2762558, by rfl⟩ : syracuseStep 3683411 = 5525117) B5525117
theorem B5526683 : Blo 1636017 5526683 := bstep (se 1 (by rfl) ⟨4145012, by rfl⟩ : syracuseStep 5526683 = 8290025) B8290025
theorem B2454779 : Blo 1636017 2454779 := bstep (se 1 (by rfl) ⟨1841084, by rfl⟩ : syracuseStep 2454779 = 3682169) B3682169
theorem B8844551 : Blo 1636017 8844551 := bstep (se 1 (by rfl) ⟨6633413, by rfl⟩ : syracuseStep 8844551 = 13266827) B13266827
theorem B3683591 : Blo 1636017 3683591 := bstep (se 1 (by rfl) ⟨2762693, by rfl⟩ : syracuseStep 3683591 = 5525387) B5525387
theorem B143463905 : Blo 1636017 143463905 := bstep (se 2 (by rfl) ⟨53798964, by rfl⟩ : syracuseStep 143463905 = 107597929) B107597929
theorem B6641135 : Blo 1636017 6641135 := bstep (se 1 (by rfl) ⟨4980851, by rfl⟩ : syracuseStep 6641135 = 9961703) B9961703
theorem B1971803 : Blo 1636017 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B3683951 : Blo 1636017 3683951 := bstep (se 1 (by rfl) ⟨2762963, by rfl⟩ : syracuseStep 3683951 = 5525927) B5525927
theorem B4142735 : Blo 1636017 4142735 := bstep (se 1 (by rfl) ⟨3107051, by rfl⟩ : syracuseStep 4142735 = 6214103) B6214103
theorem B1636079 : Blo 1636017 1636079 := bstep (se 1 (by rfl) ⟨1227059, by rfl⟩ : syracuseStep 1636079 = 2454119) B2454119
theorem B80688959 : Blo 1636017 80688959 := bstep (se 1 (by rfl) ⟨60516719, by rfl⟩ : syracuseStep 80688959 = 121033439) B121033439
theorem B1636167 : Blo 1636017 1636167 := bstep (se 1 (by rfl) ⟨1227125, by rfl⟩ : syracuseStep 1636167 = 2454251) B2454251
theorem B1636187 : Blo 1636017 1636187 := bstep (se 1 (by rfl) ⟨1227140, by rfl⟩ : syracuseStep 1636187 = 2454281) B2454281
theorem B5977981 : Blo 1636017 5977981 := bstep (se 3 (by rfl) ⟨1120871, by rfl⟩ : syracuseStep 5977981 = 2241743) B2241743
theorem B1636255 : Blo 1636017 1636255 := bstep (se 1 (by rfl) ⟨1227191, by rfl⟩ : syracuseStep 1636255 = 2454383) B2454383
theorem B1636423 : Blo 1636017 1636423 := bstep (se 1 (by rfl) ⟨1227317, by rfl⟩ : syracuseStep 1636423 = 2454635) B2454635
theorem B6633671 : Blo 1636017 6633671 := bstep (se 1 (by rfl) ⟨4975253, by rfl⟩ : syracuseStep 6633671 = 9950507) B9950507
theorem B1636583 : Blo 1636017 1636583 := bstep (se 1 (by rfl) ⟨1227437, by rfl⟩ : syracuseStep 1636583 = 2454875) B2454875
theorem B6994163 : Blo 1636017 6994163 := bstep (se 1 (by rfl) ⟨5245622, by rfl⟩ : syracuseStep 6994163 = 10491245) B10491245
theorem B10631531 : Blo 1636017 10631531 := bstep (se 1 (by rfl) ⟨7973648, by rfl⟩ : syracuseStep 10631531 = 15947297) B15947297
theorem B1636767 : Blo 1636017 1636767 := bstep (se 1 (by rfl) ⟨1227575, by rfl⟩ : syracuseStep 1636767 = 2455151) B2455151
theorem B9320903 : Blo 1636017 9320903 := bstep (se 1 (by rfl) ⟨6990677, by rfl⟩ : syracuseStep 9320903 = 13981355) B13981355
theorem B1636815 : Blo 1636017 1636815 := bstep (se 1 (by rfl) ⟨1227611, by rfl⟩ : syracuseStep 1636815 = 2455223) B2455223
theorem B2456015 : Blo 1636017 2456015 := bstep (se 1 (by rfl) ⟨1842011, by rfl⟩ : syracuseStep 2456015 = 3684023) B3684023
theorem B3684815 : Blo 1636017 3684815 := bstep (se 1 (by rfl) ⟨2763611, by rfl⟩ : syracuseStep 3684815 = 5527223) B5527223
theorem B1636839 : Blo 1636017 1636839 := bstep (se 1 (by rfl) ⟨1227629, by rfl⟩ : syracuseStep 1636839 = 2455259) B2455259
theorem B2456105 : Blo 1636017 2456105 := bstep (se 2 (by rfl) ⟨921039, by rfl⟩ : syracuseStep 2456105 = 1842079) B1842079
theorem B3684905 : Blo 1636017 3684905 := bstep (se 2 (by rfl) ⟨1381839, by rfl⟩ : syracuseStep 3684905 = 2763679) B2763679
theorem B35396185 : Blo 1636017 35396185 := bstep (se 2 (by rfl) ⟨13273569, by rfl⟩ : syracuseStep 35396185 = 26547139) B26547139
theorem B1636955 : Blo 1636017 1636955 := bstep (se 1 (by rfl) ⟨1227716, by rfl⟩ : syracuseStep 1636955 = 2455433) B2455433
theorem B1841755 : Blo 1636017 1841755 := bstep (se 1 (by rfl) ⟨1381316, by rfl⟩ : syracuseStep 1841755 = 2762633) B2762633
theorem B226826891 : Blo 1636017 226826891 := bstep (se 1 (by rfl) ⟨170120168, by rfl⟩ : syracuseStep 226826891 = 340240337) B340240337
theorem B1637023 : Blo 1636017 1637023 := bstep (se 1 (by rfl) ⟨1227767, by rfl⟩ : syracuseStep 1637023 = 2455535) B2455535
theorem B2456297 : Blo 1636017 2456297 := bstep (se 2 (by rfl) ⟨921111, by rfl⟩ : syracuseStep 2456297 = 1842223) B1842223
theorem B15948535 : Blo 1636017 15948535 := bstep (se 1 (by rfl) ⟨11961401, by rfl⟩ : syracuseStep 15948535 = 23922803) B23922803
theorem B4143919 : Blo 1636017 4143919 := bstep (se 1 (by rfl) ⟨3107939, by rfl⟩ : syracuseStep 4143919 = 6215879) B6215879
theorem B1637191 : Blo 1636017 1637191 := bstep (se 1 (by rfl) ⟨1227893, by rfl⟩ : syracuseStep 1637191 = 2455787) B2455787
theorem B1637231 : Blo 1636017 1637231 := bstep (se 1 (by rfl) ⟨1227923, by rfl⟩ : syracuseStep 1637231 = 2455847) B2455847
theorem B1842043 : Blo 1636017 1842043 := bstep (se 1 (by rfl) ⟨1381532, by rfl⟩ : syracuseStep 1842043 = 2763065) B2763065
theorem B12434309 : Blo 1636017 12434309 := bstep (se 4 (by rfl) ⟨1165716, by rfl⟩ : syracuseStep 12434309 = 2331433) B2331433
theorem B1637287 : Blo 1636017 1637287 := bstep (se 1 (by rfl) ⟨1227965, by rfl⟩ : syracuseStep 1637287 = 2455931) B2455931
theorem B62946233 : Blo 1636017 62946233 := bstep (se 2 (by rfl) ⟨23604837, by rfl⟩ : syracuseStep 62946233 = 47209675) B47209675
theorem B15727607 : Blo 1636017 15727607 := bstep (se 1 (by rfl) ⟨11795705, by rfl⟩ : syracuseStep 15727607 = 23591411) B23591411
theorem B1637467 : Blo 1636017 1637467 := bstep (se 1 (by rfl) ⟨1228100, by rfl⟩ : syracuseStep 1637467 = 2456201) B2456201
theorem B2456681 : Blo 1636017 2456681 := bstep (se 2 (by rfl) ⟨921255, by rfl⟩ : syracuseStep 2456681 = 1842511) B1842511
theorem B3685481 : Blo 1636017 3685481 := bstep (se 2 (by rfl) ⟨1382055, by rfl⟩ : syracuseStep 3685481 = 2764111) B2764111
theorem B9321587 : Blo 1636017 9321587 := bstep (se 1 (by rfl) ⟨6991190, by rfl⟩ : syracuseStep 9321587 = 13982381) B13982381
theorem B11803805 : Blo 1636017 11803805 := bstep (se 3 (by rfl) ⟨2213213, by rfl⟩ : syracuseStep 11803805 = 4426427) B4426427
theorem B1637583 : Blo 1636017 1637583 := bstep (se 1 (by rfl) ⟨1228187, by rfl⟩ : syracuseStep 1637583 = 2456375) B2456375
theorem B1637607 : Blo 1636017 1637607 := bstep (se 1 (by rfl) ⟨1228205, by rfl⟩ : syracuseStep 1637607 = 2456411) B2456411
theorem B2456807 : Blo 1636017 2456807 := bstep (se 1 (by rfl) ⟨1842605, by rfl⟩ : syracuseStep 2456807 = 3685211) B3685211
theorem B1637703 : Blo 1636017 1637703 := bstep (se 1 (by rfl) ⟨1228277, by rfl⟩ : syracuseStep 1637703 = 2456555) B2456555
theorem B4144567 : Blo 1636017 4144567 := bstep (se 1 (by rfl) ⟨3108425, by rfl⟩ : syracuseStep 4144567 = 6216851) B6216851
theorem B1637839 : Blo 1636017 1637839 := bstep (se 1 (by rfl) ⟨1228379, by rfl⟩ : syracuseStep 1637839 = 2456759) B2456759
theorem B358309331 : Blo 1636017 358309331 := bstep (se 1 (by rfl) ⟨268731998, by rfl⟩ : syracuseStep 358309331 = 537463997) B537463997
theorem B6217307 : Blo 1636017 6217307 := bstep (se 1 (by rfl) ⟨4662980, by rfl⟩ : syracuseStep 6217307 = 9325961) B9325961
theorem B1637999 : Blo 1636017 1637999 := bstep (se 1 (by rfl) ⟨1228499, by rfl⟩ : syracuseStep 1637999 = 2456999) B2456999
theorem B6217337 : Blo 1636017 6217337 := bstep (se 2 (by rfl) ⟨2331501, by rfl⟩ : syracuseStep 6217337 = 4663003) B4663003
theorem B5046095 : Blo 1636017 5046095 := bstep (se 1 (by rfl) ⟨3784571, by rfl⟩ : syracuseStep 5046095 = 7569143) B7569143
theorem B3317615 : Blo 1636017 3317615 := bstep (se 1 (by rfl) ⟨2488211, by rfl⟩ : syracuseStep 3317615 = 4976423) B4976423
theorem B9322361 : Blo 1636017 9322361 := bstep (se 2 (by rfl) ⟨3495885, by rfl⟩ : syracuseStep 9322361 = 6991771) B6991771
theorem B13991879 : Blo 1636017 13991879 := bstep (se 1 (by rfl) ⟨10493909, by rfl⟩ : syracuseStep 13991879 = 20987819) B20987819
theorem B3498175 : Blo 1636017 3498175 := bstep (se 1 (by rfl) ⟨2623631, by rfl⟩ : syracuseStep 3498175 = 5247263) B5247263
theorem B47194913 : Blo 1636017 47194913 := bstep (se 2 (by rfl) ⟨17698092, by rfl⟩ : syracuseStep 47194913 = 35396185) B35396185
theorem B10486583 : Blo 1636017 10486583 := bstep (se 1 (by rfl) ⟨7864937, by rfl⟩ : syracuseStep 10486583 = 15729875) B15729875
theorem B8291159 : Blo 1636017 8291159 := bstep (se 1 (by rfl) ⟨6218369, by rfl⟩ : syracuseStep 8291159 = 12436739) B12436739
theorem B95642603 : Blo 1636017 95642603 := bstep (se 1 (by rfl) ⟨71731952, by rfl⟩ : syracuseStep 95642603 = 143463905) B143463905
theorem B2761823 : Blo 1636017 2761823 := bstep (se 1 (by rfl) ⟨2071367, by rfl⟩ : syracuseStep 2761823 = 4142735) B4142735
theorem B22398275 : Blo 1636017 22398275 := bstep (se 1 (by rfl) ⟨16798706, by rfl⟩ : syracuseStep 22398275 = 33597413) B33597413
theorem B5244239 : Blo 1636017 5244239 := bstep (se 1 (by rfl) ⟨3933179, by rfl⟩ : syracuseStep 5244239 = 7866359) B7866359
theorem B4662775 : Blo 1636017 4662775 := bstep (se 1 (by rfl) ⟨3497081, by rfl⟩ : syracuseStep 4662775 = 6994163) B6994163
theorem B44795591 : Blo 1636017 44795591 := bstep (se 1 (by rfl) ⟨33596693, by rfl⟩ : syracuseStep 44795591 = 67193387) B67193387
theorem B10487555 : Blo 1636017 10487555 := bstep (se 1 (by rfl) ⟨7865666, by rfl⟩ : syracuseStep 10487555 = 15731333) B15731333
theorem B151217927 : Blo 1636017 151217927 := bstep (se 1 (by rfl) ⟨113413445, by rfl⟩ : syracuseStep 151217927 = 226826891) B226826891
theorem B11962343 : Blo 1636017 11962343 := bstep (se 1 (by rfl) ⟨8971757, by rfl⟩ : syracuseStep 11962343 = 17943515) B17943515
theorem B2623529 : Blo 1636017 2623529 := bstep (se 2 (by rfl) ⟨983823, by rfl⟩ : syracuseStep 2623529 = 1967647) B1967647
theorem B6064283 : Blo 1636017 6064283 := bstep (se 1 (by rfl) ⟨4548212, by rfl⟩ : syracuseStep 6064283 = 9096425) B9096425
theorem B238872887 : Blo 1636017 238872887 := bstep (se 1 (by rfl) ⟨179154665, by rfl⟩ : syracuseStep 238872887 = 358309331) B358309331
theorem B5523767 : Blo 1636017 5523767 := bstep (se 1 (by rfl) ⟨4142825, by rfl⟩ : syracuseStep 5523767 = 8285651) B8285651
theorem B3238697 : Blo 1636017 3238697 := bstep (se 2 (by rfl) ⟨1214511, by rfl⟩ : syracuseStep 3238697 = 2429023) B2429023
theorem B3681107 : Blo 1636017 3681107 := bstep (se 1 (by rfl) ⟨2760830, by rfl⟩ : syracuseStep 3681107 = 5521661) B5521661
theorem B1747823 : Blo 1636017 1747823 := bstep (se 1 (by rfl) ⟨1310867, by rfl⟩ : syracuseStep 1747823 = 2621735) B2621735
theorem B10488761 : Blo 1636017 10488761 := bstep (se 2 (by rfl) ⟨3933285, by rfl⟩ : syracuseStep 10488761 = 7866571) B7866571
theorem B8285165 : Blo 1636017 8285165 := bstep (se 3 (by rfl) ⟨1553468, by rfl⟩ : syracuseStep 8285165 = 3106937) B3106937
theorem B16174237 : Blo 1636017 16174237 := bstep (se 3 (by rfl) ⟨3032669, by rfl⟩ : syracuseStep 16174237 = 6065339) B6065339
theorem B3681467 : Blo 1636017 3681467 := bstep (se 1 (by rfl) ⟨2761100, by rfl⟩ : syracuseStep 3681467 = 5522201) B5522201
theorem B17689789 : Blo 1636017 17689789 := bstep (se 3 (by rfl) ⟨3316835, by rfl⟩ : syracuseStep 17689789 = 6633671) B6633671
theorem B3681647 : Blo 1636017 3681647 := bstep (se 1 (by rfl) ⟨2761235, by rfl⟩ : syracuseStep 3681647 = 5522471) B5522471
theorem B4427423 : Blo 1636017 4427423 := bstep (se 1 (by rfl) ⟨3320567, by rfl⟩ : syracuseStep 4427423 = 6641135) B6641135
theorem B5525225 : Blo 1636017 5525225 := bstep (se 2 (by rfl) ⟨2071959, by rfl⟩ : syracuseStep 5525225 = 4143919) B4143919
theorem B53792639 : Blo 1636017 53792639 := bstep (se 1 (by rfl) ⟨40344479, by rfl⟩ : syracuseStep 53792639 = 80688959) B80688959
theorem B3682367 : Blo 1636017 3682367 := bstep (se 1 (by rfl) ⟨2761775, by rfl⟩ : syracuseStep 3682367 = 5523551) B5523551
theorem B6213935 : Blo 1636017 6213935 := bstep (se 1 (by rfl) ⟨4660451, by rfl⟩ : syracuseStep 6213935 = 9320903) B9320903
theorem B5526089 : Blo 1636017 5526089 := bstep (se 2 (by rfl) ⟨2072283, by rfl⟩ : syracuseStep 5526089 = 4144567) B4144567
theorem B41964155 : Blo 1636017 41964155 := bstep (se 1 (by rfl) ⟨31473116, by rfl⟩ : syracuseStep 41964155 = 62946233) B62946233
theorem B6214391 : Blo 1636017 6214391 := bstep (se 1 (by rfl) ⟨4660793, by rfl⟩ : syracuseStep 6214391 = 9321587) B9321587
theorem B7869203 : Blo 1636017 7869203 := bstep (se 1 (by rfl) ⟨5901902, by rfl⟩ : syracuseStep 7869203 = 11803805) B11803805
theorem B2454299 : Blo 1636017 2454299 := bstep (se 1 (by rfl) ⟨1840724, by rfl⟩ : syracuseStep 2454299 = 3681449) B3681449
theorem B13456253 : Blo 1636017 13456253 := bstep (se 3 (by rfl) ⟨2523047, by rfl⟩ : syracuseStep 13456253 = 5046095) B5046095
theorem B8287271 : Blo 1636017 8287271 := bstep (se 1 (by rfl) ⟨6215453, by rfl⟩ : syracuseStep 8287271 = 12430907) B12430907
theorem B2454575 : Blo 1636017 2454575 := bstep (se 1 (by rfl) ⟨1840931, by rfl⟩ : syracuseStep 2454575 = 3681863) B3681863
theorem B2454623 : Blo 1636017 2454623 := bstep (se 1 (by rfl) ⟨1840967, by rfl⟩ : syracuseStep 2454623 = 3681935) B3681935
theorem B17708129 : Blo 1636017 17708129 := bstep (se 2 (by rfl) ⟨6640548, by rfl⟩ : syracuseStep 17708129 = 13281097) B13281097
theorem B2454683 : Blo 1636017 2454683 := bstep (se 1 (by rfl) ⟨1841012, by rfl⟩ : syracuseStep 2454683 = 3682025) B3682025
theorem B2454695 : Blo 1636017 2454695 := bstep (se 1 (by rfl) ⟨1841021, by rfl⟩ : syracuseStep 2454695 = 3682043) B3682043
theorem B6214907 : Blo 1636017 6214907 := bstep (se 1 (by rfl) ⟨4661180, by rfl⟩ : syracuseStep 6214907 = 9322361) B9322361
theorem B9327919 : Blo 1636017 9327919 := bstep (se 1 (by rfl) ⟨6995939, by rfl⟩ : syracuseStep 9327919 = 13991879) B13991879
theorem B4724075 : Blo 1636017 4724075 := bstep (se 1 (by rfl) ⟨3543056, by rfl⟩ : syracuseStep 4724075 = 7086113) B7086113
theorem B12432851 : Blo 1636017 12432851 := bstep (se 1 (by rfl) ⟨9324638, by rfl⟩ : syracuseStep 12432851 = 18649277) B18649277
theorem B1840639 : Blo 1636017 1840639 := bstep (se 1 (by rfl) ⟨1380479, by rfl⟩ : syracuseStep 1840639 = 2760959) B2760959
theorem B161519143 : Blo 1636017 161519143 := bstep (se 1 (by rfl) ⟨121139357, by rfl⟩ : syracuseStep 161519143 = 242278715) B242278715
theorem B8853113 : Blo 1636017 8853113 := bstep (se 2 (by rfl) ⟨3319917, by rfl⟩ : syracuseStep 8853113 = 6639835) B6639835
theorem B2455367 : Blo 1636017 2455367 := bstep (se 1 (by rfl) ⟨1841525, by rfl⟩ : syracuseStep 2455367 = 3683051) B3683051
theorem B1636223 : Blo 1636017 1636223 := bstep (se 1 (by rfl) ⟨1227167, by rfl⟩ : syracuseStep 1636223 = 2454335) B2454335
theorem B1636319 : Blo 1636017 1636319 := bstep (se 1 (by rfl) ⟨1227239, by rfl⟩ : syracuseStep 1636319 = 2454479) B2454479
theorem B1636347 : Blo 1636017 1636347 := bstep (se 1 (by rfl) ⟨1227260, by rfl⟩ : syracuseStep 1636347 = 2454521) B2454521
theorem B2455547 : Blo 1636017 2455547 := bstep (se 1 (by rfl) ⟨1841660, by rfl⟩ : syracuseStep 2455547 = 3683321) B3683321
theorem B1636379 : Blo 1636017 1636379 := bstep (se 1 (by rfl) ⟨1227284, by rfl⟩ : syracuseStep 1636379 = 2454569) B2454569
theorem B1636399 : Blo 1636017 1636399 := bstep (se 1 (by rfl) ⟨1227299, by rfl⟩ : syracuseStep 1636399 = 2454599) B2454599
theorem B2455607 : Blo 1636017 2455607 := bstep (se 1 (by rfl) ⟨1841705, by rfl⟩ : syracuseStep 2455607 = 3683411) B3683411
theorem B3684455 : Blo 1636017 3684455 := bstep (se 1 (by rfl) ⟨2763341, by rfl⟩ : syracuseStep 3684455 = 5526683) B5526683
theorem B2455673 : Blo 1636017 2455673 := bstep (se 2 (by rfl) ⟨920877, by rfl⟩ : syracuseStep 2455673 = 1841755) B1841755
theorem B1636519 : Blo 1636017 1636519 := bstep (se 1 (by rfl) ⟨1227389, by rfl⟩ : syracuseStep 1636519 = 2454779) B2454779
theorem B5896367 : Blo 1636017 5896367 := bstep (se 1 (by rfl) ⟨4422275, by rfl⟩ : syracuseStep 5896367 = 8844551) B8844551
theorem B2455727 : Blo 1636017 2455727 := bstep (se 1 (by rfl) ⟨1841795, by rfl⟩ : syracuseStep 2455727 = 3683591) B3683591
theorem B28350749 : Blo 1636017 28350749 := bstep (se 3 (by rfl) ⟨5315765, by rfl⟩ : syracuseStep 28350749 = 10631531) B10631531
theorem B21264713 : Blo 1636017 21264713 := bstep (se 2 (by rfl) ⟨7974267, by rfl⟩ : syracuseStep 21264713 = 15948535) B15948535
theorem B2455967 : Blo 1636017 2455967 := bstep (se 1 (by rfl) ⟨1841975, by rfl⟩ : syracuseStep 2455967 = 3683951) B3683951
theorem B22403537 : Blo 1636017 22403537 := bstep (se 2 (by rfl) ⟨8401326, by rfl⟩ : syracuseStep 22403537 = 16802653) B16802653
theorem B2456057 : Blo 1636017 2456057 := bstep (se 2 (by rfl) ⟨921021, by rfl⟩ : syracuseStep 2456057 = 1842043) B1842043
theorem B1841791 : Blo 1636017 1841791 := bstep (se 1 (by rfl) ⟨1381343, by rfl⟩ : syracuseStep 1841791 = 2762687) B2762687
theorem B6994745 : Blo 1636017 6994745 := bstep (se 2 (by rfl) ⟨2623029, by rfl⟩ : syracuseStep 6994745 = 5246059) B5246059
theorem B5258141 : Blo 1636017 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B10492861 : Blo 1636017 10492861 := bstep (se 3 (by rfl) ⟨1967411, by rfl⟩ : syracuseStep 10492861 = 3934823) B3934823
theorem B1637343 : Blo 1636017 1637343 := bstep (se 1 (by rfl) ⟨1228007, by rfl⟩ : syracuseStep 1637343 = 2456015) B2456015
theorem B2456543 : Blo 1636017 2456543 := bstep (se 1 (by rfl) ⟨1842407, by rfl⟩ : syracuseStep 2456543 = 3684815) B3684815
theorem B1637403 : Blo 1636017 1637403 := bstep (se 1 (by rfl) ⟨1228052, by rfl⟩ : syracuseStep 1637403 = 2456105) B2456105
theorem B2456603 : Blo 1636017 2456603 := bstep (se 1 (by rfl) ⟨1842452, by rfl⟩ : syracuseStep 2456603 = 3684905) B3684905
theorem B1637531 : Blo 1636017 1637531 := bstep (se 1 (by rfl) ⟨1228148, by rfl⟩ : syracuseStep 1637531 = 2456297) B2456297
theorem B6995105 : Blo 1636017 6995105 := bstep (se 2 (by rfl) ⟨2623164, by rfl⟩ : syracuseStep 6995105 = 5246329) B5246329
theorem B8289539 : Blo 1636017 8289539 := bstep (se 1 (by rfl) ⟨6217154, by rfl⟩ : syracuseStep 8289539 = 12434309) B12434309
theorem B31882565 : Blo 1636017 31882565 := bstep (se 4 (by rfl) ⟨2988990, by rfl⟩ : syracuseStep 31882565 = 5977981) B5977981
theorem B10485071 : Blo 1636017 10485071 := bstep (se 1 (by rfl) ⟨7863803, by rfl⟩ : syracuseStep 10485071 = 15727607) B15727607
theorem B1637787 : Blo 1636017 1637787 := bstep (se 1 (by rfl) ⟨1228340, by rfl⟩ : syracuseStep 1637787 = 2456681) B2456681
theorem B2456987 : Blo 1636017 2456987 := bstep (se 1 (by rfl) ⟨1842740, by rfl⟩ : syracuseStep 2456987 = 3685481) B3685481
theorem B1637871 : Blo 1636017 1637871 := bstep (se 1 (by rfl) ⟨1228403, by rfl⟩ : syracuseStep 1637871 = 2456807) B2456807
theorem B35872465 : Blo 1636017 35872465 := bstep (se 2 (by rfl) ⟨13452174, by rfl⟩ : syracuseStep 35872465 = 26904349) B26904349
theorem B4144871 : Blo 1636017 4144871 := bstep (se 1 (by rfl) ⟨3108653, by rfl⟩ : syracuseStep 4144871 = 6217307) B6217307
theorem B4144891 : Blo 1636017 4144891 := bstep (se 1 (by rfl) ⟨3108668, by rfl⟩ : syracuseStep 4144891 = 6217337) B6217337
theorem B2211743 : Blo 1636017 2211743 := bstep (se 1 (by rfl) ⟨1658807, by rfl⟩ : syracuseStep 2211743 = 3317615) B3317615
theorem B11804615 : Blo 1636017 11804615 := bstep (se 1 (by rfl) ⟨8853461, by rfl⟩ : syracuseStep 11804615 = 17706923) B17706923
theorem B6996077 : Blo 1636017 6996077 := bstep (se 3 (by rfl) ⟨1311764, by rfl⟩ : syracuseStep 6996077 = 2623529) B2623529
theorem B27976103 : Blo 1636017 27976103 := bstep (se 1 (by rfl) ⟨20982077, by rfl⟩ : syracuseStep 27976103 = 41964155) B41964155
theorem B8970835 : Blo 1636017 8970835 := bstep (se 1 (by rfl) ⟨6728126, by rfl⟩ : syracuseStep 8970835 = 13456253) B13456253
theorem B11805419 : Blo 1636017 11805419 := bstep (se 1 (by rfl) ⟨8854064, by rfl⟩ : syracuseStep 11805419 = 17708129) B17708129
theorem B100811951 : Blo 1636017 100811951 := bstep (se 1 (by rfl) ⟨75608963, by rfl⟩ : syracuseStep 100811951 = 151217927) B151217927
theorem B18900499 : Blo 1636017 18900499 := bstep (se 1 (by rfl) ⟨14175374, by rfl⟩ : syracuseStep 18900499 = 28350749) B28350749
theorem B23586385 : Blo 1636017 23586385 := bstep (se 2 (by rfl) ⟨8844894, by rfl⟩ : syracuseStep 23586385 = 17689789) B17689789
theorem B14935691 : Blo 1636017 14935691 := bstep (se 1 (by rfl) ⟨11201768, by rfl⟩ : syracuseStep 14935691 = 22403537) B22403537
theorem B12437225 : Blo 1636017 12437225 := bstep (se 2 (by rfl) ⟨4663959, by rfl⟩ : syracuseStep 12437225 = 9327919) B9327919
theorem B4663163 : Blo 1636017 4663163 := bstep (se 1 (by rfl) ⟨3497372, by rfl⟩ : syracuseStep 4663163 = 6994745) B6994745
theorem B5523443 : Blo 1636017 5523443 := bstep (se 1 (by rfl) ⟨4142582, by rfl⟩ : syracuseStep 5523443 = 8285165) B8285165
theorem B4663403 : Blo 1636017 4663403 := bstep (se 1 (by rfl) ⟨3497552, by rfl⟩ : syracuseStep 4663403 = 6995105) B6995105
theorem B6990047 : Blo 1636017 6990047 := bstep (se 1 (by rfl) ⟨5242535, by rfl⟩ : syracuseStep 6990047 = 10485071) B10485071
theorem B2951615 : Blo 1636017 2951615 := bstep (se 1 (by rfl) ⟨2213711, by rfl⟩ : syracuseStep 2951615 = 4427423) B4427423
theorem B2763247 : Blo 1636017 2763247 := bstep (se 1 (by rfl) ⟨2072435, by rfl⟩ : syracuseStep 2763247 = 4144871) B4144871
theorem B4664233 : Blo 1636017 4664233 := bstep (se 2 (by rfl) ⟨1749087, by rfl⟩ : syracuseStep 4664233 = 3498175) B3498175
theorem B5246135 : Blo 1636017 5246135 := bstep (se 1 (by rfl) ⟨3934601, by rfl⟩ : syracuseStep 5246135 = 7869203) B7869203
theorem B6991055 : Blo 1636017 6991055 := bstep (se 1 (by rfl) ⟨5243291, by rfl⟩ : syracuseStep 6991055 = 10486583) B10486583
theorem B63761735 : Blo 1636017 63761735 := bstep (se 1 (by rfl) ⟨47821301, by rfl⟩ : syracuseStep 63761735 = 95642603) B95642603
theorem B5524847 : Blo 1636017 5524847 := bstep (se 1 (by rfl) ⟨4143635, by rfl⟩ : syracuseStep 5524847 = 8287271) B8287271
theorem B3149383 : Blo 1636017 3149383 := bstep (se 1 (by rfl) ⟨2362037, by rfl⟩ : syracuseStep 3149383 = 4724075) B4724075
theorem B5902075 : Blo 1636017 5902075 := bstep (se 1 (by rfl) ⟨4426556, by rfl⟩ : syracuseStep 5902075 = 8853113) B8853113
theorem B29863727 : Blo 1636017 29863727 := bstep (se 1 (by rfl) ⟨22397795, by rfl⟩ : syracuseStep 29863727 = 44795591) B44795591
theorem B6991703 : Blo 1636017 6991703 := bstep (se 1 (by rfl) ⟨5243777, by rfl⟩ : syracuseStep 6991703 = 10487555) B10487555
theorem B4042855 : Blo 1636017 4042855 := bstep (se 1 (by rfl) ⟨3032141, by rfl⟩ : syracuseStep 4042855 = 6064283) B6064283
theorem B159248591 : Blo 1636017 159248591 := bstep (se 1 (by rfl) ⟨119436443, by rfl⟩ : syracuseStep 159248591 = 238872887) B238872887
theorem B3682511 : Blo 1636017 3682511 := bstep (se 1 (by rfl) ⟨2761883, by rfl⟩ : syracuseStep 3682511 = 5523767) B5523767
theorem B21565649 : Blo 1636017 21565649 := bstep (se 2 (by rfl) ⟨8087118, by rfl⟩ : syracuseStep 21565649 = 16174237) B16174237
theorem B14176475 : Blo 1636017 14176475 := bstep (se 1 (by rfl) ⟨10632356, by rfl⟩ : syracuseStep 14176475 = 21264713) B21264713
theorem B2159131 : Blo 1636017 2159131 := bstep (se 1 (by rfl) ⟨1619348, by rfl⟩ : syracuseStep 2159131 = 3238697) B3238697
theorem B2454071 : Blo 1636017 2454071 := bstep (se 1 (by rfl) ⟨1840553, by rfl⟩ : syracuseStep 2454071 = 3681107) B3681107
theorem B6992507 : Blo 1636017 6992507 := bstep (se 1 (by rfl) ⟨5244380, by rfl⟩ : syracuseStep 6992507 = 10488761) B10488761
theorem B2454185 : Blo 1636017 2454185 := bstep (se 2 (by rfl) ⟨920319, by rfl⟩ : syracuseStep 2454185 = 1840639) B1840639
theorem B2454311 : Blo 1636017 2454311 := bstep (se 1 (by rfl) ⟨1840733, by rfl⟩ : syracuseStep 2454311 = 3681467) B3681467
theorem B5526359 : Blo 1636017 5526359 := bstep (se 1 (by rfl) ⟨4144769, by rfl⟩ : syracuseStep 5526359 = 8289539) B8289539
theorem B21255043 : Blo 1636017 21255043 := bstep (se 1 (by rfl) ⟨15941282, by rfl⟩ : syracuseStep 21255043 = 31882565) B31882565
theorem B2454431 : Blo 1636017 2454431 := bstep (se 1 (by rfl) ⟨1840823, by rfl⟩ : syracuseStep 2454431 = 3681647) B3681647
theorem B47829953 : Blo 1636017 47829953 := bstep (se 2 (by rfl) ⟨17936232, by rfl⟩ : syracuseStep 47829953 = 35872465) B35872465
theorem B5526521 : Blo 1636017 5526521 := bstep (se 2 (by rfl) ⟨2072445, by rfl⟩ : syracuseStep 5526521 = 4144891) B4144891
theorem B3683483 : Blo 1636017 3683483 := bstep (se 1 (by rfl) ⟨2762612, by rfl⟩ : syracuseStep 3683483 = 5525225) B5525225
theorem B35861759 : Blo 1636017 35861759 := bstep (se 1 (by rfl) ⟨26896319, by rfl⟩ : syracuseStep 35861759 = 53792639) B53792639
theorem B7869743 : Blo 1636017 7869743 := bstep (se 1 (by rfl) ⟨5902307, by rfl⟩ : syracuseStep 7869743 = 11804615) B11804615
theorem B2454911 : Blo 1636017 2454911 := bstep (se 1 (by rfl) ⟨1841183, by rfl⟩ : syracuseStep 2454911 = 3682367) B3682367
theorem B4142623 : Blo 1636017 4142623 := bstep (se 1 (by rfl) ⟨3106967, by rfl⟩ : syracuseStep 4142623 = 6213935) B6213935
theorem B3684059 : Blo 1636017 3684059 := bstep (se 1 (by rfl) ⟨2763044, by rfl⟩ : syracuseStep 3684059 = 5526089) B5526089
theorem B4142927 : Blo 1636017 4142927 := bstep (se 1 (by rfl) ⟨3107195, by rfl⟩ : syracuseStep 4142927 = 6214391) B6214391
theorem B1636199 : Blo 1636017 1636199 := bstep (se 1 (by rfl) ⟨1227149, by rfl⟩ : syracuseStep 1636199 = 2454299) B2454299
theorem B31463275 : Blo 1636017 31463275 := bstep (se 1 (by rfl) ⟨23597456, by rfl⟩ : syracuseStep 31463275 = 47194913) B47194913
theorem B5527439 : Blo 1636017 5527439 := bstep (se 1 (by rfl) ⟨4145579, by rfl⟩ : syracuseStep 5527439 = 8291159) B8291159
theorem B1636383 : Blo 1636017 1636383 := bstep (se 1 (by rfl) ⟨1227287, by rfl⟩ : syracuseStep 1636383 = 2454575) B2454575
theorem B1636415 : Blo 1636017 1636415 := bstep (se 1 (by rfl) ⟨1227311, by rfl⟩ : syracuseStep 1636415 = 2454623) B2454623
theorem B1841215 : Blo 1636017 1841215 := bstep (se 1 (by rfl) ⟨1380911, by rfl⟩ : syracuseStep 1841215 = 2761823) B2761823
theorem B1636455 : Blo 1636017 1636455 := bstep (se 1 (by rfl) ⟨1227341, by rfl⟩ : syracuseStep 1636455 = 2454683) B2454683
theorem B1636463 : Blo 1636017 1636463 := bstep (se 1 (by rfl) ⟨1227347, by rfl⟩ : syracuseStep 1636463 = 2454695) B2454695
theorem B4143271 : Blo 1636017 4143271 := bstep (se 1 (by rfl) ⟨3107453, by rfl⟩ : syracuseStep 4143271 = 6214907) B6214907
theorem B2455721 : Blo 1636017 2455721 := bstep (se 2 (by rfl) ⟨920895, by rfl⟩ : syracuseStep 2455721 = 1841791) B1841791
theorem B14932183 : Blo 1636017 14932183 := bstep (se 1 (by rfl) ⟨11199137, by rfl⟩ : syracuseStep 14932183 = 22398275) B22398275
theorem B3496159 : Blo 1636017 3496159 := bstep (se 1 (by rfl) ⟨2622119, by rfl⟩ : syracuseStep 3496159 = 5244239) B5244239
theorem B8288567 : Blo 1636017 8288567 := bstep (se 1 (by rfl) ⟨6216425, by rfl⟩ : syracuseStep 8288567 = 12432851) B12432851
theorem B18643445 : Blo 1636017 18643445 := bstep (se 5 (by rfl) ⟨873911, by rfl⟩ : syracuseStep 18643445 = 1747823) B1747823
theorem B1636911 : Blo 1636017 1636911 := bstep (se 1 (by rfl) ⟨1227683, by rfl⟩ : syracuseStep 1636911 = 2455367) B2455367
theorem B13990481 : Blo 1636017 13990481 := bstep (se 2 (by rfl) ⟨5246430, by rfl⟩ : syracuseStep 13990481 = 10492861) B10492861
theorem B1637031 : Blo 1636017 1637031 := bstep (se 1 (by rfl) ⟨1227773, by rfl⟩ : syracuseStep 1637031 = 2455547) B2455547
theorem B1637071 : Blo 1636017 1637071 := bstep (se 1 (by rfl) ⟨1227803, by rfl⟩ : syracuseStep 1637071 = 2455607) B2455607
theorem B2456303 : Blo 1636017 2456303 := bstep (se 1 (by rfl) ⟨1842227, by rfl⟩ : syracuseStep 2456303 = 3684455) B3684455
theorem B1637115 : Blo 1636017 1637115 := bstep (se 1 (by rfl) ⟨1227836, by rfl⟩ : syracuseStep 1637115 = 2455673) B2455673
theorem B3930911 : Blo 1636017 3930911 := bstep (se 1 (by rfl) ⟨2948183, by rfl⟩ : syracuseStep 3930911 = 5896367) B5896367
theorem B1637151 : Blo 1636017 1637151 := bstep (se 1 (by rfl) ⟨1227863, by rfl⟩ : syracuseStep 1637151 = 2455727) B2455727
theorem B1637311 : Blo 1636017 1637311 := bstep (se 1 (by rfl) ⟨1227983, by rfl⟩ : syracuseStep 1637311 = 2455967) B2455967
theorem B1637371 : Blo 1636017 1637371 := bstep (se 1 (by rfl) ⟨1228028, by rfl⟩ : syracuseStep 1637371 = 2456057) B2456057
theorem B3505427 : Blo 1636017 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B1637695 : Blo 1636017 1637695 := bstep (se 1 (by rfl) ⟨1228271, by rfl⟩ : syracuseStep 1637695 = 2456543) B2456543
theorem B6217033 : Blo 1636017 6217033 := bstep (se 2 (by rfl) ⟨2331387, by rfl⟩ : syracuseStep 6217033 = 4662775) B4662775
theorem B1637735 : Blo 1636017 1637735 := bstep (se 1 (by rfl) ⟨1228301, by rfl⟩ : syracuseStep 1637735 = 2456603) B2456603
theorem B215358857 : Blo 1636017 215358857 := bstep (se 2 (by rfl) ⟨80759571, by rfl⟩ : syracuseStep 215358857 = 161519143) B161519143
theorem B1637991 : Blo 1636017 1637991 := bstep (se 1 (by rfl) ⟨1228493, by rfl⟩ : syracuseStep 1637991 = 2456987) B2456987
theorem B5897981 : Blo 1636017 5897981 := bstep (se 3 (by rfl) ⟨1105871, by rfl⟩ : syracuseStep 5897981 = 2211743) B2211743
theorem B31899581 : Blo 1636017 31899581 := bstep (se 3 (by rfl) ⟨5981171, by rfl⟩ : syracuseStep 31899581 = 11962343) B11962343
theorem B5390473 : Blo 1636017 5390473 := bstep (se 2 (by rfl) ⟨2021427, by rfl⟩ : syracuseStep 5390473 = 4042855) B4042855
theorem B14377099 : Blo 1636017 14377099 := bstep (se 1 (by rfl) ⟨10782824, by rfl⟩ : syracuseStep 14377099 = 21565649) B21565649
theorem B4661545 : Blo 1636017 4661545 := bstep (se 2 (by rfl) ⟨1748079, by rfl⟩ : syracuseStep 4661545 = 3496159) B3496159
theorem B4661671 : Blo 1636017 4661671 := bstep (se 1 (by rfl) ⟨3496253, by rfl⟩ : syracuseStep 4661671 = 6992507) B6992507
theorem B11961113 : Blo 1636017 11961113 := bstep (se 2 (by rfl) ⟨4485417, by rfl⟩ : syracuseStep 11961113 = 8970835) B8970835
theorem B67207967 : Blo 1636017 67207967 := bstep (se 1 (by rfl) ⟨50405975, by rfl⟩ : syracuseStep 67207967 = 100811951) B100811951
theorem B8291483 : Blo 1636017 8291483 := bstep (se 1 (by rfl) ⟨6218612, by rfl⟩ : syracuseStep 8291483 = 12437225) B12437225
theorem B2761951 : Blo 1636017 2761951 := bstep (se 1 (by rfl) ⟨2071463, by rfl⟩ : syracuseStep 2761951 = 4142927) B4142927
theorem B6218977 : Blo 1636017 6218977 := bstep (se 2 (by rfl) ⟨2332116, by rfl⟩ : syracuseStep 6218977 = 4664233) B4664233
theorem B1967743 : Blo 1636017 1967743 := bstep (se 1 (by rfl) ⟨1475807, by rfl⟩ : syracuseStep 1967743 = 2951615) B2951615
theorem B12428963 : Blo 1636017 12428963 := bstep (se 1 (by rfl) ⟨9321722, by rfl⟩ : syracuseStep 12428963 = 18643445) B18643445
theorem B25200665 : Blo 1636017 25200665 := bstep (se 2 (by rfl) ⟨9450249, by rfl⟩ : syracuseStep 25200665 = 18900499) B18900499
theorem B5523497 : Blo 1636017 5523497 := bstep (se 2 (by rfl) ⟨2071311, by rfl⟩ : syracuseStep 5523497 = 4142623) B4142623
theorem B2336951 : Blo 1636017 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B19909151 : Blo 1636017 19909151 := bstep (se 1 (by rfl) ⟨14931863, by rfl⟩ : syracuseStep 19909151 = 29863727) B29863727
theorem B4664051 : Blo 1636017 4664051 := bstep (se 1 (by rfl) ⟨3498038, by rfl⟩ : syracuseStep 4664051 = 6996077) B6996077
theorem B5524361 : Blo 1636017 5524361 := bstep (se 2 (by rfl) ⟨2071635, by rfl⟩ : syracuseStep 5524361 = 4143271) B4143271
theorem B19909577 : Blo 1636017 19909577 := bstep (se 2 (by rfl) ⟨7466091, by rfl⟩ : syracuseStep 19909577 = 14932183) B14932183
theorem B31886635 : Blo 1636017 31886635 := bstep (se 1 (by rfl) ⟨23914976, by rfl⟩ : syracuseStep 31886635 = 47829953) B47829953
theorem B2878841 : Blo 1636017 2878841 := bstep (se 2 (by rfl) ⟨1079565, by rfl⟩ : syracuseStep 2878841 = 2159131) B2159131
theorem B23907839 : Blo 1636017 23907839 := bstep (se 1 (by rfl) ⟨17930879, by rfl⟩ : syracuseStep 23907839 = 35861759) B35861759
theorem B5246495 : Blo 1636017 5246495 := bstep (se 1 (by rfl) ⟨3934871, by rfl⟩ : syracuseStep 5246495 = 7869743) B7869743
theorem B9957127 : Blo 1636017 9957127 := bstep (se 1 (by rfl) ⟨7467845, by rfl⟩ : syracuseStep 9957127 = 14935691) B14935691
theorem B28340057 : Blo 1636017 28340057 := bstep (se 2 (by rfl) ⟨10627521, by rfl⟩ : syracuseStep 28340057 = 21255043) B21255043
theorem B3108775 : Blo 1636017 3108775 := bstep (se 1 (by rfl) ⟨2331581, by rfl⟩ : syracuseStep 3108775 = 4663163) B4663163
theorem B31477733 : Blo 1636017 31477733 := bstep (se 4 (by rfl) ⟨2951037, by rfl⟩ : syracuseStep 31477733 = 5902075) B5902075
theorem B3682295 : Blo 1636017 3682295 := bstep (se 1 (by rfl) ⟨2761721, by rfl⟩ : syracuseStep 3682295 = 5523443) B5523443
theorem B3108935 : Blo 1636017 3108935 := bstep (se 1 (by rfl) ⟨2331701, by rfl⟩ : syracuseStep 3108935 = 4663403) B4663403
theorem B5525711 : Blo 1636017 5525711 := bstep (se 1 (by rfl) ⟨4144283, by rfl⟩ : syracuseStep 5525711 = 8288567) B8288567
theorem B9326987 : Blo 1636017 9326987 := bstep (se 1 (by rfl) ⟨6995240, by rfl⟩ : syracuseStep 9326987 = 13990481) B13990481
theorem B4199177 : Blo 1636017 4199177 := bstep (se 2 (by rfl) ⟨1574691, by rfl⟩ : syracuseStep 4199177 = 3149383) B3149383
theorem B3683231 : Blo 1636017 3683231 := bstep (se 1 (by rfl) ⟨2762423, by rfl⟩ : syracuseStep 3683231 = 5524847) B5524847
theorem B2454953 : Blo 1636017 2454953 := bstep (se 2 (by rfl) ⟨920607, by rfl⟩ : syracuseStep 2454953 = 1841215) B1841215
theorem B106165727 : Blo 1636017 106165727 := bstep (se 1 (by rfl) ⟨79624295, by rfl⟩ : syracuseStep 106165727 = 159248591) B159248591
theorem B2455007 : Blo 1636017 2455007 := bstep (se 1 (by rfl) ⟨1841255, by rfl⟩ : syracuseStep 2455007 = 3682511) B3682511
theorem B9450983 : Blo 1636017 9450983 := bstep (se 1 (by rfl) ⟨7088237, by rfl⟩ : syracuseStep 9450983 = 14176475) B14176475
theorem B18650735 : Blo 1636017 18650735 := bstep (se 1 (by rfl) ⟨13988051, by rfl⟩ : syracuseStep 18650735 = 27976103) B27976103
theorem B1636047 : Blo 1636017 1636047 := bstep (se 1 (by rfl) ⟨1227035, by rfl⟩ : syracuseStep 1636047 = 2454071) B2454071
theorem B1636123 : Blo 1636017 1636123 := bstep (se 1 (by rfl) ⟨1227092, by rfl⟩ : syracuseStep 1636123 = 2454185) B2454185
theorem B7870279 : Blo 1636017 7870279 := bstep (se 1 (by rfl) ⟨5902709, by rfl⟩ : syracuseStep 7870279 = 11805419) B11805419
theorem B1636207 : Blo 1636017 1636207 := bstep (se 1 (by rfl) ⟨1227155, by rfl⟩ : syracuseStep 1636207 = 2454311) B2454311
theorem B3684239 : Blo 1636017 3684239 := bstep (se 1 (by rfl) ⟨2763179, by rfl⟩ : syracuseStep 3684239 = 5526359) B5526359
theorem B1636287 : Blo 1636017 1636287 := bstep (se 1 (by rfl) ⟨1227215, by rfl⟩ : syracuseStep 1636287 = 2454431) B2454431
theorem B3684329 : Blo 1636017 3684329 := bstep (se 2 (by rfl) ⟨1381623, by rfl⟩ : syracuseStep 3684329 = 2763247) B2763247
theorem B3684347 : Blo 1636017 3684347 := bstep (se 1 (by rfl) ⟨2763260, by rfl⟩ : syracuseStep 3684347 = 5526521) B5526521
theorem B2455655 : Blo 1636017 2455655 := bstep (se 1 (by rfl) ⟨1841741, by rfl⟩ : syracuseStep 2455655 = 3683483) B3683483
theorem B1636607 : Blo 1636017 1636607 := bstep (se 1 (by rfl) ⟨1227455, by rfl⟩ : syracuseStep 1636607 = 2454911) B2454911
theorem B2456039 : Blo 1636017 2456039 := bstep (se 1 (by rfl) ⟨1842029, by rfl⟩ : syracuseStep 2456039 = 3684059) B3684059
theorem B3684959 : Blo 1636017 3684959 := bstep (se 1 (by rfl) ⟨2763719, by rfl⟩ : syracuseStep 3684959 = 5527439) B5527439
theorem B1637147 : Blo 1636017 1637147 := bstep (se 1 (by rfl) ⟨1227860, by rfl⟩ : syracuseStep 1637147 = 2455721) B2455721
theorem B4660031 : Blo 1636017 4660031 := bstep (se 1 (by rfl) ⟨3495023, by rfl⟩ : syracuseStep 4660031 = 6990047) B6990047
theorem B8289377 : Blo 1636017 8289377 := bstep (se 2 (by rfl) ⟨3108516, by rfl⟩ : syracuseStep 8289377 = 6217033) B6217033
theorem B1637535 : Blo 1636017 1637535 := bstep (se 1 (by rfl) ⟨1228151, by rfl⟩ : syracuseStep 1637535 = 2456303) B2456303
theorem B2620607 : Blo 1636017 2620607 := bstep (se 1 (by rfl) ⟨1965455, by rfl⟩ : syracuseStep 2620607 = 3930911) B3930911
theorem B31448513 : Blo 1636017 31448513 := bstep (se 2 (by rfl) ⟨11793192, by rfl⟩ : syracuseStep 31448513 = 23586385) B23586385
theorem B3497423 : Blo 1636017 3497423 := bstep (se 1 (by rfl) ⟨2623067, by rfl⟩ : syracuseStep 3497423 = 5246135) B5246135
theorem B4660703 : Blo 1636017 4660703 := bstep (se 1 (by rfl) ⟨3495527, by rfl⟩ : syracuseStep 4660703 = 6991055) B6991055
theorem B42507823 : Blo 1636017 42507823 := bstep (se 1 (by rfl) ⟨31880867, by rfl⟩ : syracuseStep 42507823 = 63761735) B63761735
theorem B143572571 : Blo 1636017 143572571 := bstep (se 1 (by rfl) ⟨107679428, by rfl⟩ : syracuseStep 143572571 = 215358857) B215358857
theorem B41951033 : Blo 1636017 41951033 := bstep (se 2 (by rfl) ⟨15731637, by rfl⟩ : syracuseStep 41951033 = 31463275) B31463275
theorem B3931987 : Blo 1636017 3931987 := bstep (se 1 (by rfl) ⟨2948990, by rfl⟩ : syracuseStep 3931987 = 5897981) B5897981
theorem B4661135 : Blo 1636017 4661135 := bstep (se 1 (by rfl) ⟨3495851, by rfl⟩ : syracuseStep 4661135 = 6991703) B6991703
theorem B21266387 : Blo 1636017 21266387 := bstep (se 1 (by rfl) ⟨15949790, by rfl⟩ : syracuseStep 21266387 = 31899581) B31899581
theorem B2072623 : Blo 1636017 2072623 := bstep (se 1 (by rfl) ⟨1554467, by rfl⟩ : syracuseStep 2072623 = 3108935) B3108935
theorem B19169465 : Blo 1636017 19169465 := bstep (se 2 (by rfl) ⟨7188549, by rfl⟩ : syracuseStep 19169465 = 14377099) B14377099
theorem B6217991 : Blo 1636017 6217991 := bstep (se 1 (by rfl) ⟨4663493, by rfl⟩ : syracuseStep 6217991 = 9326987) B9326987
theorem B6988285 : Blo 1636017 6988285 := bstep (se 3 (by rfl) ⟨1310303, by rfl⟩ : syracuseStep 6988285 = 2620607) B2620607
theorem B10494629 : Blo 1636017 10494629 := bstep (se 4 (by rfl) ⟨983871, by rfl⟩ : syracuseStep 10494629 = 1967743) B1967743
theorem B8291969 : Blo 1636017 8291969 := bstep (se 2 (by rfl) ⟨3109488, by rfl⟩ : syracuseStep 8291969 = 6218977) B6218977
theorem B13272767 : Blo 1636017 13272767 := bstep (se 1 (by rfl) ⟨9954575, by rfl⟩ : syracuseStep 13272767 = 19909151) B19909151
theorem B3106687 : Blo 1636017 3106687 := bstep (se 1 (by rfl) ⟨2330015, by rfl⟩ : syracuseStep 3106687 = 4660031) B4660031
theorem B75573485 : Blo 1636017 75573485 := bstep (se 3 (by rfl) ⟨14170028, by rfl⟩ : syracuseStep 75573485 = 28340057) B28340057
theorem B1919227 : Blo 1636017 1919227 := bstep (se 1 (by rfl) ⟨1439420, by rfl⟩ : syracuseStep 1919227 = 2878841) B2878841
theorem B20965675 : Blo 1636017 20965675 := bstep (se 1 (by rfl) ⟨15724256, by rfl⟩ : syracuseStep 20965675 = 31448513) B31448513
theorem B3107135 : Blo 1636017 3107135 := bstep (se 1 (by rfl) ⟨2330351, by rfl⟩ : syracuseStep 3107135 = 4660703) B4660703
theorem B3107423 : Blo 1636017 3107423 := bstep (se 1 (by rfl) ⟨2330567, by rfl⟩ : syracuseStep 3107423 = 4661135) B4661135
theorem B7187297 : Blo 1636017 7187297 := bstep (se 2 (by rfl) ⟨2695236, by rfl⟩ : syracuseStep 7187297 = 5390473) B5390473
theorem B44805311 : Blo 1636017 44805311 := bstep (se 1 (by rfl) ⟨33603983, by rfl⟩ : syracuseStep 44805311 = 67207967) B67207967
theorem B8285975 : Blo 1636017 8285975 := bstep (se 1 (by rfl) ⟨6214481, by rfl⟩ : syracuseStep 8285975 = 12428963) B12428963
theorem B9326461 : Blo 1636017 9326461 := bstep (se 3 (by rfl) ⟨1748711, by rfl⟩ : syracuseStep 9326461 = 3497423) B3497423
theorem B25202621 : Blo 1636017 25202621 := bstep (se 3 (by rfl) ⟨4725491, by rfl⟩ : syracuseStep 25202621 = 9450983) B9450983
theorem B63754237 : Blo 1636017 63754237 := bstep (se 3 (by rfl) ⟨11953919, by rfl⟩ : syracuseStep 63754237 = 23907839) B23907839
theorem B3682331 : Blo 1636017 3682331 := bstep (se 1 (by rfl) ⟨2761748, by rfl⟩ : syracuseStep 3682331 = 5523497) B5523497
theorem B3682601 : Blo 1636017 3682601 := bstep (se 2 (by rfl) ⟨1380975, by rfl⟩ : syracuseStep 3682601 = 2761951) B2761951
theorem B3109367 : Blo 1636017 3109367 := bstep (se 1 (by rfl) ⟨2332025, by rfl⟩ : syracuseStep 3109367 = 4664051) B4664051
theorem B3682907 : Blo 1636017 3682907 := bstep (se 1 (by rfl) ⟨2762180, by rfl⟩ : syracuseStep 3682907 = 5524361) B5524361
theorem B56677097 : Blo 1636017 56677097 := bstep (se 2 (by rfl) ⟨21253911, by rfl⟩ : syracuseStep 56677097 = 42507823) B42507823
theorem B31896301 : Blo 1636017 31896301 := bstep (se 3 (by rfl) ⟨5980556, by rfl⟩ : syracuseStep 31896301 = 11961113) B11961113
theorem B5526251 : Blo 1636017 5526251 := bstep (se 1 (by rfl) ⟨4144688, by rfl⟩ : syracuseStep 5526251 = 8289377) B8289377
theorem B13276169 : Blo 1636017 13276169 := bstep (se 2 (by rfl) ⟨4978563, by rfl⟩ : syracuseStep 13276169 = 9957127) B9957127
theorem B14177591 : Blo 1636017 14177591 := bstep (se 1 (by rfl) ⟨10633193, by rfl⟩ : syracuseStep 14177591 = 21266387) B21266387
theorem B20985155 : Blo 1636017 20985155 := bstep (se 1 (by rfl) ⟨15738866, by rfl⟩ : syracuseStep 20985155 = 31477733) B31477733
theorem B2454863 : Blo 1636017 2454863 := bstep (se 1 (by rfl) ⟨1841147, by rfl⟩ : syracuseStep 2454863 = 3682295) B3682295
theorem B3683807 : Blo 1636017 3683807 := bstep (se 1 (by rfl) ⟨2762855, by rfl⟩ : syracuseStep 3683807 = 5525711) B5525711
theorem B6215393 : Blo 1636017 6215393 := bstep (se 2 (by rfl) ⟨2330772, by rfl⟩ : syracuseStep 6215393 = 4661545) B4661545
theorem B6231869 : Blo 1636017 6231869 := bstep (se 3 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 6231869 = 2336951) B2336951
theorem B2799451 : Blo 1636017 2799451 := bstep (se 1 (by rfl) ⟨2099588, by rfl⟩ : syracuseStep 2799451 = 4199177) B4199177
theorem B6215561 : Blo 1636017 6215561 := bstep (se 2 (by rfl) ⟨2330835, by rfl⟩ : syracuseStep 6215561 = 4661671) B4661671
theorem B2455487 : Blo 1636017 2455487 := bstep (se 1 (by rfl) ⟨1841615, by rfl⟩ : syracuseStep 2455487 = 3683231) B3683231
theorem B5527655 : Blo 1636017 5527655 := bstep (se 1 (by rfl) ⟨4145741, by rfl⟩ : syracuseStep 5527655 = 8291483) B8291483
theorem B1636635 : Blo 1636017 1636635 := bstep (se 1 (by rfl) ⟨1227476, by rfl⟩ : syracuseStep 1636635 = 2454953) B2454953
theorem B70777151 : Blo 1636017 70777151 := bstep (se 1 (by rfl) ⟨53082863, by rfl⟩ : syracuseStep 70777151 = 106165727) B106165727
theorem B1636671 : Blo 1636017 1636671 := bstep (se 1 (by rfl) ⟨1227503, by rfl⟩ : syracuseStep 1636671 = 2455007) B2455007
theorem B12433823 : Blo 1636017 12433823 := bstep (se 1 (by rfl) ⟨9325367, by rfl⟩ : syracuseStep 12433823 = 18650735) B18650735
theorem B2456159 : Blo 1636017 2456159 := bstep (se 1 (by rfl) ⟨1842119, by rfl⟩ : syracuseStep 2456159 = 3684239) B3684239
theorem B2456219 : Blo 1636017 2456219 := bstep (se 1 (by rfl) ⟨1842164, by rfl⟩ : syracuseStep 2456219 = 3684329) B3684329
theorem B2456231 : Blo 1636017 2456231 := bstep (se 1 (by rfl) ⟨1842173, by rfl⟩ : syracuseStep 2456231 = 3684347) B3684347
theorem B16800443 : Blo 1636017 16800443 := bstep (se 1 (by rfl) ⟨12600332, by rfl⟩ : syracuseStep 16800443 = 25200665) B25200665
theorem B1637103 : Blo 1636017 1637103 := bstep (se 1 (by rfl) ⟨1227827, by rfl⟩ : syracuseStep 1637103 = 2455655) B2455655
theorem B1637359 : Blo 1636017 1637359 := bstep (se 1 (by rfl) ⟨1228019, by rfl⟩ : syracuseStep 1637359 = 2456039) B2456039
theorem B42515513 : Blo 1636017 42515513 := bstep (se 2 (by rfl) ⟨15943317, by rfl⟩ : syracuseStep 42515513 = 31886635) B31886635
theorem B2456639 : Blo 1636017 2456639 := bstep (se 1 (by rfl) ⟨1842479, by rfl⟩ : syracuseStep 2456639 = 3684959) B3684959
theorem B3497663 : Blo 1636017 3497663 := bstep (se 1 (by rfl) ⟨2623247, by rfl⟩ : syracuseStep 3497663 = 5246495) B5246495
theorem B95715047 : Blo 1636017 95715047 := bstep (se 1 (by rfl) ⟨71786285, by rfl⟩ : syracuseStep 95715047 = 143572571) B143572571
theorem B10493705 : Blo 1636017 10493705 := bstep (se 2 (by rfl) ⟨3935139, by rfl⟩ : syracuseStep 10493705 = 7870279) B7870279
theorem B5242649 : Blo 1636017 5242649 := bstep (se 2 (by rfl) ⟨1965993, by rfl⟩ : syracuseStep 5242649 = 3931987) B3931987
theorem B53092205 : Blo 1636017 53092205 := bstep (se 3 (by rfl) ⟨9954788, by rfl⟩ : syracuseStep 53092205 = 19909577) B19909577
theorem B27967355 : Blo 1636017 27967355 := bstep (se 1 (by rfl) ⟨20975516, by rfl⟩ : syracuseStep 27967355 = 41951033) B41951033
theorem B4145033 : Blo 1636017 4145033 := bstep (se 2 (by rfl) ⟨1554387, by rfl⟩ : syracuseStep 4145033 = 3108775) B3108775
theorem B4145327 : Blo 1636017 4145327 := bstep (se 1 (by rfl) ⟨3108995, by rfl⟩ : syracuseStep 4145327 = 6217991) B6217991
theorem B6996419 : Blo 1636017 6996419 := bstep (se 1 (by rfl) ⟨5247314, by rfl⟩ : syracuseStep 6996419 = 10494629) B10494629
theorem B51118573 : Blo 1636017 51118573 := bstep (se 3 (by rfl) ⟨9584732, by rfl⟩ : syracuseStep 51118573 = 19169465) B19169465
theorem B8848511 : Blo 1636017 8848511 := bstep (se 1 (by rfl) ⟨6636383, by rfl⟩ : syracuseStep 8848511 = 13272767) B13272767
theorem B4154579 : Blo 1636017 4154579 := bstep (se 1 (by rfl) ⟨3115934, by rfl⟩ : syracuseStep 4154579 = 6231869) B6231869
theorem B8291645 : Blo 1636017 8291645 := bstep (se 3 (by rfl) ⟨1554683, by rfl⟩ : syracuseStep 8291645 = 3109367) B3109367
theorem B50382323 : Blo 1636017 50382323 := bstep (se 1 (by rfl) ⟨37786742, by rfl⟩ : syracuseStep 50382323 = 75573485) B75573485
theorem B11200295 : Blo 1636017 11200295 := bstep (se 1 (by rfl) ⟨8400221, by rfl⟩ : syracuseStep 11200295 = 16800443) B16800443
theorem B29870207 : Blo 1636017 29870207 := bstep (se 1 (by rfl) ⟨22402655, by rfl⟩ : syracuseStep 29870207 = 44805311) B44805311
theorem B63810031 : Blo 1636017 63810031 := bstep (se 1 (by rfl) ⟨47857523, by rfl⟩ : syracuseStep 63810031 = 95715047) B95715047
theorem B5523983 : Blo 1636017 5523983 := bstep (se 1 (by rfl) ⟨4142987, by rfl⟩ : syracuseStep 5523983 = 8285975) B8285975
theorem B2763355 : Blo 1636017 2763355 := bstep (se 1 (by rfl) ⟨2072516, by rfl⟩ : syracuseStep 2763355 = 4145033) B4145033
theorem B2763497 : Blo 1636017 2763497 := bstep (se 2 (by rfl) ⟨1036311, by rfl⟩ : syracuseStep 2763497 = 2072623) B2072623
theorem B2558969 : Blo 1636017 2558969 := bstep (se 2 (by rfl) ⟨959613, by rfl⟩ : syracuseStep 2558969 = 1919227) B1919227
theorem B27954233 : Blo 1636017 27954233 := bstep (se 2 (by rfl) ⟨10482837, by rfl⟩ : syracuseStep 27954233 = 20965675) B20965675
theorem B37784731 : Blo 1636017 37784731 := bstep (se 1 (by rfl) ⟨28338548, by rfl⟩ : syracuseStep 37784731 = 56677097) B56677097
theorem B9317713 : Blo 1636017 9317713 := bstep (se 2 (by rfl) ⟨3494142, by rfl⟩ : syracuseStep 9317713 = 6988285) B6988285
theorem B8850779 : Blo 1636017 8850779 := bstep (se 1 (by rfl) ⟨6638084, by rfl⟩ : syracuseStep 8850779 = 13276169) B13276169
theorem B42528401 : Blo 1636017 42528401 := bstep (se 2 (by rfl) ⟨15948150, by rfl⟩ : syracuseStep 42528401 = 31896301) B31896301
theorem B76664501 : Blo 1636017 76664501 := bstep (se 5 (by rfl) ⟨3593648, by rfl⟩ : syracuseStep 76664501 = 7187297) B7187297
theorem B8286461 : Blo 1636017 8286461 := bstep (se 3 (by rfl) ⟨1553711, by rfl⟩ : syracuseStep 8286461 = 3107423) B3107423
theorem B14930405 : Blo 1636017 14930405 := bstep (se 4 (by rfl) ⟨1399725, by rfl⟩ : syracuseStep 14930405 = 2799451) B2799451
theorem B13980397 : Blo 1636017 13980397 := bstep (se 3 (by rfl) ⟨2621324, by rfl⟩ : syracuseStep 13980397 = 5242649) B5242649
theorem B2331775 : Blo 1636017 2331775 := bstep (se 1 (by rfl) ⟨1748831, by rfl⟩ : syracuseStep 2331775 = 3497663) B3497663
theorem B4142249 : Blo 1636017 4142249 := bstep (se 2 (by rfl) ⟨1553343, by rfl⟩ : syracuseStep 4142249 = 3106687) B3106687
theorem B35394803 : Blo 1636017 35394803 := bstep (se 1 (by rfl) ⟨26546102, by rfl⟩ : syracuseStep 35394803 = 53092205) B53092205
theorem B85005649 : Blo 1636017 85005649 := bstep (se 2 (by rfl) ⟨31877118, by rfl⟩ : syracuseStep 85005649 = 63754237) B63754237
theorem B2454887 : Blo 1636017 2454887 := bstep (se 1 (by rfl) ⟨1841165, by rfl⟩ : syracuseStep 2454887 = 3682331) B3682331
theorem B2455067 : Blo 1636017 2455067 := bstep (se 1 (by rfl) ⟨1841300, by rfl⟩ : syracuseStep 2455067 = 3682601) B3682601
theorem B2455271 : Blo 1636017 2455271 := bstep (se 1 (by rfl) ⟨1841453, by rfl⟩ : syracuseStep 2455271 = 3682907) B3682907
theorem B3684167 : Blo 1636017 3684167 := bstep (se 1 (by rfl) ⟨2763125, by rfl⟩ : syracuseStep 3684167 = 5526251) B5526251
theorem B9451727 : Blo 1636017 9451727 := bstep (se 1 (by rfl) ⟨7088795, by rfl⟩ : syracuseStep 9451727 = 14177591) B14177591
theorem B13990103 : Blo 1636017 13990103 := bstep (se 1 (by rfl) ⟨10492577, by rfl⟩ : syracuseStep 13990103 = 20985155) B20985155
theorem B1636575 : Blo 1636017 1636575 := bstep (se 1 (by rfl) ⟨1227431, by rfl⟩ : syracuseStep 1636575 = 2454863) B2454863
theorem B2455871 : Blo 1636017 2455871 := bstep (se 1 (by rfl) ⟨1841903, by rfl⟩ : syracuseStep 2455871 = 3683807) B3683807
theorem B5527979 : Blo 1636017 5527979 := bstep (se 1 (by rfl) ⟨4145984, by rfl⟩ : syracuseStep 5527979 = 8291969) B8291969
theorem B4143595 : Blo 1636017 4143595 := bstep (se 1 (by rfl) ⟨3107696, by rfl⟩ : syracuseStep 4143595 = 6215393) B6215393
theorem B4143707 : Blo 1636017 4143707 := bstep (se 1 (by rfl) ⟨3107780, by rfl⟩ : syracuseStep 4143707 = 6215561) B6215561
theorem B1636991 : Blo 1636017 1636991 := bstep (se 1 (by rfl) ⟨1227743, by rfl⟩ : syracuseStep 1636991 = 2455487) B2455487
theorem B3685103 : Blo 1636017 3685103 := bstep (se 1 (by rfl) ⟨2763827, by rfl⟩ : syracuseStep 3685103 = 5527655) B5527655
theorem B47184767 : Blo 1636017 47184767 := bstep (se 1 (by rfl) ⟨35388575, by rfl⟩ : syracuseStep 47184767 = 70777151) B70777151
theorem B2071423 : Blo 1636017 2071423 := bstep (se 1 (by rfl) ⟨1553567, by rfl⟩ : syracuseStep 2071423 = 3107135) B3107135
theorem B8289215 : Blo 1636017 8289215 := bstep (se 1 (by rfl) ⟨6216911, by rfl⟩ : syracuseStep 8289215 = 12433823) B12433823
theorem B1637439 : Blo 1636017 1637439 := bstep (se 1 (by rfl) ⟨1228079, by rfl⟩ : syracuseStep 1637439 = 2456159) B2456159
theorem B1637479 : Blo 1636017 1637479 := bstep (se 1 (by rfl) ⟨1228109, by rfl⟩ : syracuseStep 1637479 = 2456219) B2456219
theorem B1637487 : Blo 1636017 1637487 := bstep (se 1 (by rfl) ⟨1228115, by rfl⟩ : syracuseStep 1637487 = 2456231) B2456231
theorem B28343675 : Blo 1636017 28343675 := bstep (se 1 (by rfl) ⟨21257756, by rfl⟩ : syracuseStep 28343675 = 42515513) B42515513
theorem B1637759 : Blo 1636017 1637759 := bstep (se 1 (by rfl) ⟨1228319, by rfl⟩ : syracuseStep 1637759 = 2456639) B2456639
theorem B67206989 : Blo 1636017 67206989 := bstep (se 3 (by rfl) ⟨12601310, by rfl⟩ : syracuseStep 67206989 = 25202621) B25202621
theorem B12435281 : Blo 1636017 12435281 := bstep (se 2 (by rfl) ⟨4663230, by rfl⟩ : syracuseStep 12435281 = 9326461) B9326461
theorem B6995803 : Blo 1636017 6995803 := bstep (se 1 (by rfl) ⟨5246852, by rfl⟩ : syracuseStep 6995803 = 10493705) B10493705
theorem B18644903 : Blo 1636017 18644903 := bstep (se 1 (by rfl) ⟨13983677, by rfl⟩ : syracuseStep 18644903 = 27967355) B27967355
theorem B9953603 : Blo 1636017 9953603 := bstep (se 1 (by rfl) ⟨7465202, by rfl⟩ : syracuseStep 9953603 = 14930405) B14930405
theorem B68158097 : Blo 1636017 68158097 := bstep (se 2 (by rfl) ⟨25559286, by rfl⟩ : syracuseStep 68158097 = 51118573) B51118573
theorem B5899007 : Blo 1636017 5899007 := bstep (se 1 (by rfl) ⟨4424255, by rfl⟩ : syracuseStep 5899007 = 8848511) B8848511
theorem B2761499 : Blo 1636017 2761499 := bstep (se 1 (by rfl) ⟨2071124, by rfl⟩ : syracuseStep 2761499 = 4142249) B4142249
theorem B2769719 : Blo 1636017 2769719 := bstep (se 1 (by rfl) ⟨2077289, by rfl⟩ : syracuseStep 2769719 = 4154579) B4154579
theorem B33588215 : Blo 1636017 33588215 := bstep (se 1 (by rfl) ⟨25191161, by rfl⟩ : syracuseStep 33588215 = 50382323) B50382323
theorem B2761897 : Blo 1636017 2761897 := bstep (se 2 (by rfl) ⟨1035711, by rfl⟩ : syracuseStep 2761897 = 2071423) B2071423
theorem B6301151 : Blo 1636017 6301151 := bstep (se 1 (by rfl) ⟨4725863, by rfl⟩ : syracuseStep 6301151 = 9451727) B9451727
theorem B2762471 : Blo 1636017 2762471 := bstep (se 1 (by rfl) ⟨2071853, by rfl⟩ : syracuseStep 2762471 = 4143707) B4143707
theorem B1705979 : Blo 1636017 1705979 := bstep (se 1 (by rfl) ⟨1279484, by rfl⟩ : syracuseStep 1705979 = 2558969) B2558969
theorem B5900519 : Blo 1636017 5900519 := bstep (se 1 (by rfl) ⟨4425389, by rfl⟩ : syracuseStep 5900519 = 8850779) B8850779
theorem B44804659 : Blo 1636017 44804659 := bstep (se 1 (by rfl) ⟨33603494, by rfl⟩ : syracuseStep 44804659 = 67206989) B67206989
theorem B12429935 : Blo 1636017 12429935 := bstep (se 1 (by rfl) ⟨9322451, by rfl⟩ : syracuseStep 12429935 = 18644903) B18644903
theorem B2763551 : Blo 1636017 2763551 := bstep (se 1 (by rfl) ⟨2072663, by rfl⟩ : syracuseStep 2763551 = 4145327) B4145327
theorem B5524307 : Blo 1636017 5524307 := bstep (se 1 (by rfl) ⟨4143230, by rfl⟩ : syracuseStep 5524307 = 8286461) B8286461
theorem B4664279 : Blo 1636017 4664279 := bstep (se 1 (by rfl) ⟨3498209, by rfl⟩ : syracuseStep 4664279 = 6996419) B6996419
theorem B5524793 : Blo 1636017 5524793 := bstep (se 2 (by rfl) ⟨2071797, by rfl⟩ : syracuseStep 5524793 = 4143595) B4143595
theorem B23596535 : Blo 1636017 23596535 := bstep (se 1 (by rfl) ⟨17697401, by rfl⟩ : syracuseStep 23596535 = 35394803) B35394803
theorem B18640529 : Blo 1636017 18640529 := bstep (se 2 (by rfl) ⟨6990198, by rfl⟩ : syracuseStep 18640529 = 13980397) B13980397
theorem B7466863 : Blo 1636017 7466863 := bstep (se 1 (by rfl) ⟨5600147, by rfl⟩ : syracuseStep 7466863 = 11200295) B11200295
theorem B9326735 : Blo 1636017 9326735 := bstep (se 1 (by rfl) ⟨6995051, by rfl⟩ : syracuseStep 9326735 = 13990103) B13990103
theorem B3109033 : Blo 1636017 3109033 := bstep (se 2 (by rfl) ⟨1165887, by rfl⟩ : syracuseStep 3109033 = 2331775) B2331775
theorem B3682655 : Blo 1636017 3682655 := bstep (se 1 (by rfl) ⟨2761991, by rfl⟩ : syracuseStep 3682655 = 5523983) B5523983
theorem B12423617 : Blo 1636017 12423617 := bstep (se 2 (by rfl) ⟨4658856, by rfl⟩ : syracuseStep 12423617 = 9317713) B9317713
theorem B113340865 : Blo 1636017 113340865 := bstep (se 2 (by rfl) ⟨42502824, by rfl⟩ : syracuseStep 113340865 = 85005649) B85005649
theorem B5526143 : Blo 1636017 5526143 := bstep (se 1 (by rfl) ⟨4144607, by rfl⟩ : syracuseStep 5526143 = 8289215) B8289215
theorem B18895783 : Blo 1636017 18895783 := bstep (se 1 (by rfl) ⟨14171837, by rfl⟩ : syracuseStep 18895783 = 28343675) B28343675
theorem B9327737 : Blo 1636017 9327737 := bstep (se 2 (by rfl) ⟨3497901, by rfl⟩ : syracuseStep 9327737 = 6995803) B6995803
theorem B85080041 : Blo 1636017 85080041 := bstep (se 2 (by rfl) ⟨31905015, by rfl⟩ : syracuseStep 85080041 = 63810031) B63810031
theorem B3684473 : Blo 1636017 3684473 := bstep (se 2 (by rfl) ⟨1381677, by rfl⟩ : syracuseStep 3684473 = 2763355) B2763355
theorem B5527763 : Blo 1636017 5527763 := bstep (se 1 (by rfl) ⟨4145822, by rfl⟩ : syracuseStep 5527763 = 8291645) B8291645
theorem B1636591 : Blo 1636017 1636591 := bstep (se 1 (by rfl) ⟨1227443, by rfl⟩ : syracuseStep 1636591 = 2454887) B2454887
theorem B1636711 : Blo 1636017 1636711 := bstep (se 1 (by rfl) ⟨1227533, by rfl⟩ : syracuseStep 1636711 = 2455067) B2455067
theorem B1636847 : Blo 1636017 1636847 := bstep (se 1 (by rfl) ⟨1227635, by rfl⟩ : syracuseStep 1636847 = 2455271) B2455271
theorem B2456111 : Blo 1636017 2456111 := bstep (se 1 (by rfl) ⟨1842083, by rfl⟩ : syracuseStep 2456111 = 3684167) B3684167
theorem B19913471 : Blo 1636017 19913471 := bstep (se 1 (by rfl) ⟨14935103, by rfl⟩ : syracuseStep 19913471 = 29870207) B29870207
theorem B50379641 : Blo 1636017 50379641 := bstep (se 2 (by rfl) ⟨18892365, by rfl⟩ : syracuseStep 50379641 = 37784731) B37784731
theorem B1637247 : Blo 1636017 1637247 := bstep (se 1 (by rfl) ⟨1227935, by rfl⟩ : syracuseStep 1637247 = 2455871) B2455871
theorem B3685319 : Blo 1636017 3685319 := bstep (se 1 (by rfl) ⟨2763989, by rfl⟩ : syracuseStep 3685319 = 5527979) B5527979
theorem B1842331 : Blo 1636017 1842331 := bstep (se 1 (by rfl) ⟨1381748, by rfl⟩ : syracuseStep 1842331 = 2763497) B2763497
theorem B2456735 : Blo 1636017 2456735 := bstep (se 1 (by rfl) ⟨1842551, by rfl⟩ : syracuseStep 2456735 = 3685103) B3685103
theorem B31456511 : Blo 1636017 31456511 := bstep (se 1 (by rfl) ⟨23592383, by rfl⟩ : syracuseStep 31456511 = 47184767) B47184767
theorem B18636155 : Blo 1636017 18636155 := bstep (se 1 (by rfl) ⟨13977116, by rfl⟩ : syracuseStep 18636155 = 27954233) B27954233
theorem B28352267 : Blo 1636017 28352267 := bstep (se 1 (by rfl) ⟨21264200, by rfl⟩ : syracuseStep 28352267 = 42528401) B42528401
theorem B51109667 : Blo 1636017 51109667 := bstep (se 1 (by rfl) ⟨38332250, by rfl⟩ : syracuseStep 51109667 = 76664501) B76664501
theorem B8290187 : Blo 1636017 8290187 := bstep (se 1 (by rfl) ⟨6217640, by rfl⟩ : syracuseStep 8290187 = 12435281) B12435281
theorem B6217823 : Blo 1636017 6217823 := bstep (se 1 (by rfl) ⟨4663367, by rfl⟩ : syracuseStep 6217823 = 9326735) B9326735
theorem B6635735 : Blo 1636017 6635735 := bstep (se 1 (by rfl) ⟨4976801, by rfl⟩ : syracuseStep 6635735 = 9953603) B9953603
theorem B4145377 : Blo 1636017 4145377 := bstep (se 2 (by rfl) ⟨1554516, by rfl⟩ : syracuseStep 4145377 = 3109033) B3109033
theorem B8282411 : Blo 1636017 8282411 := bstep (se 1 (by rfl) ⟨6211808, by rfl⟩ : syracuseStep 8282411 = 12423617) B12423617
theorem B3932671 : Blo 1636017 3932671 := bstep (se 1 (by rfl) ⟨2949503, by rfl⟩ : syracuseStep 3932671 = 5899007) B5899007
theorem B6218491 : Blo 1636017 6218491 := bstep (se 1 (by rfl) ⟨4663868, by rfl⟩ : syracuseStep 6218491 = 9327737) B9327737
theorem B3933679 : Blo 1636017 3933679 := bstep (se 1 (by rfl) ⟨2950259, by rfl⟩ : syracuseStep 3933679 = 5900519) B5900519
theorem B15731023 : Blo 1636017 15731023 := bstep (se 1 (by rfl) ⟨11798267, by rfl⟩ : syracuseStep 15731023 = 23596535) B23596535
theorem B9955817 : Blo 1636017 9955817 := bstep (se 2 (by rfl) ⟨3733431, by rfl⟩ : syracuseStep 9955817 = 7466863) B7466863
theorem B18901511 : Blo 1636017 18901511 := bstep (se 1 (by rfl) ⟨14176133, by rfl⟩ : syracuseStep 18901511 = 28352267) B28352267
theorem B34073111 : Blo 1636017 34073111 := bstep (se 1 (by rfl) ⟨25554833, by rfl⟩ : syracuseStep 34073111 = 51109667) B51109667
theorem B4549277 : Blo 1636017 4549277 := bstep (se 3 (by rfl) ⟨852989, by rfl⟩ : syracuseStep 4549277 = 1705979) B1705979
theorem B151121153 : Blo 1636017 151121153 := bstep (se 2 (by rfl) ⟨56670432, by rfl⟩ : syracuseStep 151121153 = 113340865) B113340865
theorem B22392143 : Blo 1636017 22392143 := bstep (se 1 (by rfl) ⟨16794107, by rfl⟩ : syracuseStep 22392143 = 33588215) B33588215
theorem B59739545 : Blo 1636017 59739545 := bstep (se 2 (by rfl) ⟨22402329, by rfl⟩ : syracuseStep 59739545 = 44804659) B44804659
theorem B25194377 : Blo 1636017 25194377 := bstep (se 2 (by rfl) ⟨9447891, by rfl⟩ : syracuseStep 25194377 = 18895783) B18895783
theorem B3682529 : Blo 1636017 3682529 := bstep (se 2 (by rfl) ⟨1380948, by rfl⟩ : syracuseStep 3682529 = 2761897) B2761897
theorem B8286623 : Blo 1636017 8286623 := bstep (se 1 (by rfl) ⟨6214967, by rfl⟩ : syracuseStep 8286623 = 12429935) B12429935
theorem B13275647 : Blo 1636017 13275647 := bstep (se 1 (by rfl) ⟨9956735, by rfl⟩ : syracuseStep 13275647 = 19913471) B19913471
theorem B3682871 : Blo 1636017 3682871 := bstep (se 1 (by rfl) ⟨2762153, by rfl⟩ : syracuseStep 3682871 = 5524307) B5524307
theorem B3109519 : Blo 1636017 3109519 := bstep (se 1 (by rfl) ⟨2332139, by rfl⟩ : syracuseStep 3109519 = 4664279) B4664279
theorem B7385917 : Blo 1636017 7385917 := bstep (se 3 (by rfl) ⟨1384859, by rfl⟩ : syracuseStep 7385917 = 2769719) B2769719
theorem B3683195 : Blo 1636017 3683195 := bstep (se 1 (by rfl) ⟨2762396, by rfl⟩ : syracuseStep 3683195 = 5524793) B5524793
theorem B12424103 : Blo 1636017 12424103 := bstep (se 1 (by rfl) ⟨9318077, by rfl⟩ : syracuseStep 12424103 = 18636155) B18636155
theorem B5526791 : Blo 1636017 5526791 := bstep (se 1 (by rfl) ⟨4145093, by rfl⟩ : syracuseStep 5526791 = 8290187) B8290187
theorem B2455103 : Blo 1636017 2455103 := bstep (se 1 (by rfl) ⟨1841327, by rfl⟩ : syracuseStep 2455103 = 3682655) B3682655
theorem B3684095 : Blo 1636017 3684095 := bstep (se 1 (by rfl) ⟨2763071, by rfl⟩ : syracuseStep 3684095 = 5526143) B5526143
theorem B45438731 : Blo 1636017 45438731 := bstep (se 1 (by rfl) ⟨34079048, by rfl⟩ : syracuseStep 45438731 = 68158097) B68158097
theorem B1840999 : Blo 1636017 1840999 := bstep (se 1 (by rfl) ⟨1380749, by rfl⟩ : syracuseStep 1840999 = 2761499) B2761499
theorem B4200767 : Blo 1636017 4200767 := bstep (se 1 (by rfl) ⟨3150575, by rfl⟩ : syracuseStep 4200767 = 6301151) B6301151
theorem B1841647 : Blo 1636017 1841647 := bstep (se 1 (by rfl) ⟨1381235, by rfl⟩ : syracuseStep 1841647 = 2762471) B2762471
theorem B56720027 : Blo 1636017 56720027 := bstep (se 1 (by rfl) ⟨42540020, by rfl⟩ : syracuseStep 56720027 = 85080041) B85080041
theorem B2456315 : Blo 1636017 2456315 := bstep (se 1 (by rfl) ⟨1842236, by rfl⟩ : syracuseStep 2456315 = 3684473) B3684473
theorem B3685175 : Blo 1636017 3685175 := bstep (se 1 (by rfl) ⟨2763881, by rfl⟩ : syracuseStep 3685175 = 5527763) B5527763
theorem B2456441 : Blo 1636017 2456441 := bstep (se 2 (by rfl) ⟨921165, by rfl⟩ : syracuseStep 2456441 = 1842331) B1842331
theorem B1637407 : Blo 1636017 1637407 := bstep (se 1 (by rfl) ⟨1228055, by rfl⟩ : syracuseStep 1637407 = 2456111) B2456111
theorem B1842367 : Blo 1636017 1842367 := bstep (se 1 (by rfl) ⟨1381775, by rfl⟩ : syracuseStep 1842367 = 2763551) B2763551
theorem B33586427 : Blo 1636017 33586427 := bstep (se 1 (by rfl) ⟨25189820, by rfl⟩ : syracuseStep 33586427 = 50379641) B50379641
theorem B2456879 : Blo 1636017 2456879 := bstep (se 1 (by rfl) ⟨1842659, by rfl⟩ : syracuseStep 2456879 = 3685319) B3685319
theorem B1637823 : Blo 1636017 1637823 := bstep (se 1 (by rfl) ⟨1228367, by rfl⟩ : syracuseStep 1637823 = 2456735) B2456735
theorem B20971007 : Blo 1636017 20971007 := bstep (se 1 (by rfl) ⟨15728255, by rfl⟩ : syracuseStep 20971007 = 31456511) B31456511
theorem B12427019 : Blo 1636017 12427019 := bstep (se 1 (by rfl) ⟨9320264, by rfl⟩ : syracuseStep 12427019 = 18640529) B18640529
theorem B4145215 : Blo 1636017 4145215 := bstep (se 1 (by rfl) ⟨3108911, by rfl⟩ : syracuseStep 4145215 = 6217823) B6217823
theorem B4423823 : Blo 1636017 4423823 := bstep (se 1 (by rfl) ⟨3317867, by rfl⟩ : syracuseStep 4423823 = 6635735) B6635735
theorem B5521607 : Blo 1636017 5521607 := bstep (se 1 (by rfl) ⟨4141205, by rfl⟩ : syracuseStep 5521607 = 8282411) B8282411
theorem B8282735 : Blo 1636017 8282735 := bstep (se 1 (by rfl) ⟨6212051, by rfl⟩ : syracuseStep 8282735 = 12424103) B12424103
theorem B5243561 : Blo 1636017 5243561 := bstep (se 2 (by rfl) ⟨1966335, by rfl⟩ : syracuseStep 5243561 = 3932671) B3932671
theorem B4146025 : Blo 1636017 4146025 := bstep (se 2 (by rfl) ⟨1554759, by rfl⟩ : syracuseStep 4146025 = 3109519) B3109519
theorem B8291321 : Blo 1636017 8291321 := bstep (se 2 (by rfl) ⟨3109245, by rfl⟩ : syracuseStep 8291321 = 6218491) B6218491
theorem B9847889 : Blo 1636017 9847889 := bstep (se 2 (by rfl) ⟨3692958, by rfl⟩ : syracuseStep 9847889 = 7385917) B7385917
theorem B6637211 : Blo 1636017 6637211 := bstep (se 1 (by rfl) ⟨4977908, by rfl⟩ : syracuseStep 6637211 = 9955817) B9955817
theorem B12601007 : Blo 1636017 12601007 := bstep (se 1 (by rfl) ⟨9450755, by rfl⟩ : syracuseStep 12601007 = 18901511) B18901511
theorem B5244905 : Blo 1636017 5244905 := bstep (se 2 (by rfl) ⟨1966839, by rfl⟩ : syracuseStep 5244905 = 3933679) B3933679
theorem B22390951 : Blo 1636017 22390951 := bstep (se 1 (by rfl) ⟨16793213, by rfl⟩ : syracuseStep 22390951 = 33586427) B33586427
theorem B100747435 : Blo 1636017 100747435 := bstep (se 1 (by rfl) ⟨75560576, by rfl⟩ : syracuseStep 100747435 = 151121153) B151121153
theorem B14928095 : Blo 1636017 14928095 := bstep (se 1 (by rfl) ⟨11196071, by rfl⟩ : syracuseStep 14928095 = 22392143) B22392143
theorem B8284679 : Blo 1636017 8284679 := bstep (se 1 (by rfl) ⟨6213509, by rfl⟩ : syracuseStep 8284679 = 12427019) B12427019
theorem B16796251 : Blo 1636017 16796251 := bstep (se 1 (by rfl) ⟨12597188, by rfl⟩ : syracuseStep 16796251 = 25194377) B25194377
theorem B5524415 : Blo 1636017 5524415 := bstep (se 1 (by rfl) ⟨4143311, by rfl⟩ : syracuseStep 5524415 = 8286623) B8286623
theorem B8850431 : Blo 1636017 8850431 := bstep (se 1 (by rfl) ⟨6637823, by rfl⟩ : syracuseStep 8850431 = 13275647) B13275647
theorem B20974697 : Blo 1636017 20974697 := bstep (se 2 (by rfl) ⟨7865511, by rfl⟩ : syracuseStep 20974697 = 15731023) B15731023
theorem B39826363 : Blo 1636017 39826363 := bstep (se 1 (by rfl) ⟨29869772, by rfl⟩ : syracuseStep 39826363 = 59739545) B59739545
theorem B13980671 : Blo 1636017 13980671 := bstep (se 1 (by rfl) ⟨10485503, by rfl⟩ : syracuseStep 13980671 = 20971007) B20971007
theorem B2454665 : Blo 1636017 2454665 := bstep (se 2 (by rfl) ⟨920499, by rfl⟩ : syracuseStep 2454665 = 1840999) B1840999
theorem B2455019 : Blo 1636017 2455019 := bstep (se 1 (by rfl) ⟨1841264, by rfl⟩ : syracuseStep 2455019 = 3682529) B3682529
theorem B5527169 : Blo 1636017 5527169 := bstep (se 2 (by rfl) ⟨2072688, by rfl⟩ : syracuseStep 5527169 = 4145377) B4145377
theorem B2455247 : Blo 1636017 2455247 := bstep (se 1 (by rfl) ⟨1841435, by rfl⟩ : syracuseStep 2455247 = 3682871) B3682871
theorem B2455463 : Blo 1636017 2455463 := bstep (se 1 (by rfl) ⟨1841597, by rfl⟩ : syracuseStep 2455463 = 3683195) B3683195
theorem B2455529 : Blo 1636017 2455529 := bstep (se 2 (by rfl) ⟨920823, by rfl⟩ : syracuseStep 2455529 = 1841647) B1841647
theorem B3684527 : Blo 1636017 3684527 := bstep (se 1 (by rfl) ⟨2763395, by rfl⟩ : syracuseStep 3684527 = 5526791) B5526791
theorem B1636735 : Blo 1636017 1636735 := bstep (se 1 (by rfl) ⟨1227551, by rfl⟩ : syracuseStep 1636735 = 2455103) B2455103
theorem B2456063 : Blo 1636017 2456063 := bstep (se 1 (by rfl) ⟨1842047, by rfl⟩ : syracuseStep 2456063 = 3684095) B3684095
theorem B30292487 : Blo 1636017 30292487 := bstep (se 1 (by rfl) ⟨22719365, by rfl⟩ : syracuseStep 30292487 = 45438731) B45438731
theorem B2800511 : Blo 1636017 2800511 := bstep (se 1 (by rfl) ⟨2100383, by rfl⟩ : syracuseStep 2800511 = 4200767) B4200767
theorem B2456489 : Blo 1636017 2456489 := bstep (se 2 (by rfl) ⟨921183, by rfl⟩ : syracuseStep 2456489 = 1842367) B1842367
theorem B22715407 : Blo 1636017 22715407 := bstep (se 1 (by rfl) ⟨17036555, by rfl⟩ : syracuseStep 22715407 = 34073111) B34073111
theorem B12131405 : Blo 1636017 12131405 := bstep (se 3 (by rfl) ⟨2274638, by rfl⟩ : syracuseStep 12131405 = 4549277) B4549277
theorem B37813351 : Blo 1636017 37813351 := bstep (se 1 (by rfl) ⟨28360013, by rfl⟩ : syracuseStep 37813351 = 56720027) B56720027
theorem B1637543 : Blo 1636017 1637543 := bstep (se 1 (by rfl) ⟨1228157, by rfl⟩ : syracuseStep 1637543 = 2456315) B2456315
theorem B2456783 : Blo 1636017 2456783 := bstep (se 1 (by rfl) ⟨1842587, by rfl⟩ : syracuseStep 2456783 = 3685175) B3685175
theorem B1637627 : Blo 1636017 1637627 := bstep (se 1 (by rfl) ⟨1228220, by rfl⟩ : syracuseStep 1637627 = 2456441) B2456441
theorem B1637919 : Blo 1636017 1637919 := bstep (se 1 (by rfl) ⟨1228439, by rfl⟩ : syracuseStep 1637919 = 2456879) B2456879
theorem B2949215 : Blo 1636017 2949215 := bstep (se 1 (by rfl) ⟨2211911, by rfl⟩ : syracuseStep 2949215 = 4423823) B4423823
theorem B5521823 : Blo 1636017 5521823 := bstep (se 1 (by rfl) ⟨4141367, by rfl⟩ : syracuseStep 5521823 = 8282735) B8282735
theorem B4424807 : Blo 1636017 4424807 := bstep (se 1 (by rfl) ⟨3318605, by rfl⟩ : syracuseStep 4424807 = 6637211) B6637211
theorem B53101817 : Blo 1636017 53101817 := bstep (se 2 (by rfl) ⟨19913181, by rfl⟩ : syracuseStep 53101817 = 39826363) B39826363
theorem B30287209 : Blo 1636017 30287209 := bstep (se 2 (by rfl) ⟨11357703, by rfl⟩ : syracuseStep 30287209 = 22715407) B22715407
theorem B5523119 : Blo 1636017 5523119 := bstep (se 1 (by rfl) ⟨4142339, by rfl⟩ : syracuseStep 5523119 = 8284679) B8284679
theorem B20194991 : Blo 1636017 20194991 := bstep (se 1 (by rfl) ⟨15146243, by rfl⟩ : syracuseStep 20194991 = 30292487) B30292487
theorem B5900287 : Blo 1636017 5900287 := bstep (se 1 (by rfl) ⟨4425215, by rfl⟩ : syracuseStep 5900287 = 8850431) B8850431
theorem B8087603 : Blo 1636017 8087603 := bstep (se 1 (by rfl) ⟨6065702, by rfl⟩ : syracuseStep 8087603 = 12131405) B12131405
theorem B3681071 : Blo 1636017 3681071 := bstep (se 1 (by rfl) ⟨2760803, by rfl⟩ : syracuseStep 3681071 = 5521607) B5521607
theorem B29854601 : Blo 1636017 29854601 := bstep (se 2 (by rfl) ⟨11195475, by rfl⟩ : syracuseStep 29854601 = 22390951) B22390951
theorem B39808253 : Blo 1636017 39808253 := bstep (se 3 (by rfl) ⟨7464047, by rfl⟩ : syracuseStep 39808253 = 14928095) B14928095
theorem B6565259 : Blo 1636017 6565259 := bstep (se 1 (by rfl) ⟨4923944, by rfl⟩ : syracuseStep 6565259 = 9847889) B9847889
theorem B8400671 : Blo 1636017 8400671 := bstep (se 1 (by rfl) ⟨6300503, by rfl⟩ : syracuseStep 8400671 = 12601007) B12601007
theorem B50417801 : Blo 1636017 50417801 := bstep (se 2 (by rfl) ⟨18906675, by rfl⟩ : syracuseStep 50417801 = 37813351) B37813351
theorem B3682943 : Blo 1636017 3682943 := bstep (se 1 (by rfl) ⟨2762207, by rfl⟩ : syracuseStep 3682943 = 5524415) B5524415
theorem B5526953 : Blo 1636017 5526953 := bstep (se 2 (by rfl) ⟨2072607, by rfl⟩ : syracuseStep 5526953 = 4145215) B4145215
theorem B134329913 : Blo 1636017 134329913 := bstep (se 2 (by rfl) ⟨50373717, by rfl⟩ : syracuseStep 134329913 = 100747435) B100747435
theorem B3495707 : Blo 1636017 3495707 := bstep (se 1 (by rfl) ⟨2621780, by rfl⟩ : syracuseStep 3495707 = 5243561) B5243561
theorem B9320447 : Blo 1636017 9320447 := bstep (se 1 (by rfl) ⟨6990335, by rfl⟩ : syracuseStep 9320447 = 13980671) B13980671
theorem B5527547 : Blo 1636017 5527547 := bstep (se 1 (by rfl) ⟨4145660, by rfl⟩ : syracuseStep 5527547 = 8291321) B8291321
theorem B1636443 : Blo 1636017 1636443 := bstep (se 1 (by rfl) ⟨1227332, by rfl⟩ : syracuseStep 1636443 = 2454665) B2454665
theorem B22395001 : Blo 1636017 22395001 := bstep (se 2 (by rfl) ⟨8398125, by rfl⟩ : syracuseStep 22395001 = 16796251) B16796251
theorem B1636679 : Blo 1636017 1636679 := bstep (se 1 (by rfl) ⟨1227509, by rfl⟩ : syracuseStep 1636679 = 2455019) B2455019
theorem B3684779 : Blo 1636017 3684779 := bstep (se 1 (by rfl) ⟨2763584, by rfl⟩ : syracuseStep 3684779 = 5527169) B5527169
theorem B1636831 : Blo 1636017 1636831 := bstep (se 1 (by rfl) ⟨1227623, by rfl⟩ : syracuseStep 1636831 = 2455247) B2455247
theorem B5528033 : Blo 1636017 5528033 := bstep (se 2 (by rfl) ⟨2073012, by rfl⟩ : syracuseStep 5528033 = 4146025) B4146025
theorem B1636975 : Blo 1636017 1636975 := bstep (se 1 (by rfl) ⟨1227731, by rfl⟩ : syracuseStep 1636975 = 2455463) B2455463
theorem B1637019 : Blo 1636017 1637019 := bstep (se 1 (by rfl) ⟨1227764, by rfl⟩ : syracuseStep 1637019 = 2455529) B2455529
theorem B3496603 : Blo 1636017 3496603 := bstep (se 1 (by rfl) ⟨2622452, by rfl⟩ : syracuseStep 3496603 = 5244905) B5244905
theorem B2456351 : Blo 1636017 2456351 := bstep (se 1 (by rfl) ⟨1842263, by rfl⟩ : syracuseStep 2456351 = 3684527) B3684527
theorem B1637375 : Blo 1636017 1637375 := bstep (se 1 (by rfl) ⟨1228031, by rfl⟩ : syracuseStep 1637375 = 2456063) B2456063
theorem B1867007 : Blo 1636017 1867007 := bstep (se 1 (by rfl) ⟨1400255, by rfl⟩ : syracuseStep 1867007 = 2800511) B2800511
theorem B1637659 : Blo 1636017 1637659 := bstep (se 1 (by rfl) ⟨1228244, by rfl⟩ : syracuseStep 1637659 = 2456489) B2456489
theorem B13983131 : Blo 1636017 13983131 := bstep (se 1 (by rfl) ⟨10487348, by rfl⟩ : syracuseStep 13983131 = 20974697) B20974697
theorem B1637855 : Blo 1636017 1637855 := bstep (se 1 (by rfl) ⟨1228391, by rfl⟩ : syracuseStep 1637855 = 2456783) B2456783
theorem B33611867 : Blo 1636017 33611867 := bstep (se 1 (by rfl) ⟨25208900, by rfl⟩ : syracuseStep 33611867 = 50417801) B50417801
theorem B29860001 : Blo 1636017 29860001 := bstep (se 2 (by rfl) ⟨11197500, by rfl⟩ : syracuseStep 29860001 = 22395001) B22395001
theorem B7864573 : Blo 1636017 7864573 := bstep (se 3 (by rfl) ⟨1474607, by rfl⟩ : syracuseStep 7864573 = 2949215) B2949215
theorem B2949871 : Blo 1636017 2949871 := bstep (se 1 (by rfl) ⟨2212403, by rfl⟩ : syracuseStep 2949871 = 4424807) B4424807
theorem B4662137 : Blo 1636017 4662137 := bstep (se 2 (by rfl) ⟨1748301, by rfl⟩ : syracuseStep 4662137 = 3496603) B3496603
theorem B17507357 : Blo 1636017 17507357 := bstep (se 3 (by rfl) ⟨3282629, by rfl⟩ : syracuseStep 17507357 = 6565259) B6565259
theorem B7867049 : Blo 1636017 7867049 := bstep (se 2 (by rfl) ⟨2950143, by rfl⟩ : syracuseStep 7867049 = 5900287) B5900287
theorem B3681215 : Blo 1636017 3681215 := bstep (se 1 (by rfl) ⟨2760911, by rfl⟩ : syracuseStep 3681215 = 5521823) B5521823
theorem B35401211 : Blo 1636017 35401211 := bstep (se 1 (by rfl) ⟨26550908, by rfl⟩ : syracuseStep 35401211 = 53101817) B53101817
theorem B3682079 : Blo 1636017 3682079 := bstep (se 1 (by rfl) ⟨2761559, by rfl⟩ : syracuseStep 3682079 = 5523119) B5523119
theorem B13463327 : Blo 1636017 13463327 := bstep (se 1 (by rfl) ⟨10097495, by rfl⟩ : syracuseStep 13463327 = 20194991) B20194991
theorem B2330471 : Blo 1636017 2330471 := bstep (se 1 (by rfl) ⟨1747853, by rfl⟩ : syracuseStep 2330471 = 3495707) B3495707
theorem B6213631 : Blo 1636017 6213631 := bstep (se 1 (by rfl) ⟨4660223, by rfl⟩ : syracuseStep 6213631 = 9320447) B9320447
theorem B40382945 : Blo 1636017 40382945 := bstep (se 2 (by rfl) ⟨15143604, by rfl⟩ : syracuseStep 40382945 = 30287209) B30287209
theorem B2454047 : Blo 1636017 2454047 := bstep (se 1 (by rfl) ⟨1840535, by rfl⟩ : syracuseStep 2454047 = 3681071) B3681071
theorem B19903067 : Blo 1636017 19903067 := bstep (se 1 (by rfl) ⟨14927300, by rfl⟩ : syracuseStep 19903067 = 29854601) B29854601
theorem B26538835 : Blo 1636017 26538835 := bstep (se 1 (by rfl) ⟨19904126, by rfl⟩ : syracuseStep 26538835 = 39808253) B39808253
theorem B5600447 : Blo 1636017 5600447 := bstep (se 1 (by rfl) ⟨4200335, by rfl⟩ : syracuseStep 5600447 = 8400671) B8400671
theorem B21566941 : Blo 1636017 21566941 := bstep (se 3 (by rfl) ⟨4043801, by rfl⟩ : syracuseStep 21566941 = 8087603) B8087603
theorem B2455295 : Blo 1636017 2455295 := bstep (se 1 (by rfl) ⟨1841471, by rfl⟩ : syracuseStep 2455295 = 3682943) B3682943
theorem B4978685 : Blo 1636017 4978685 := bstep (se 3 (by rfl) ⟨933503, by rfl⟩ : syracuseStep 4978685 = 1867007) B1867007
theorem B3684635 : Blo 1636017 3684635 := bstep (se 1 (by rfl) ⟨2763476, by rfl⟩ : syracuseStep 3684635 = 5526953) B5526953
theorem B89553275 : Blo 1636017 89553275 := bstep (se 1 (by rfl) ⟨67164956, by rfl⟩ : syracuseStep 89553275 = 134329913) B134329913
theorem B3685031 : Blo 1636017 3685031 := bstep (se 1 (by rfl) ⟨2763773, by rfl⟩ : syracuseStep 3685031 = 5527547) B5527547
theorem B2456519 : Blo 1636017 2456519 := bstep (se 1 (by rfl) ⟨1842389, by rfl⟩ : syracuseStep 2456519 = 3684779) B3684779
theorem B3685355 : Blo 1636017 3685355 := bstep (se 1 (by rfl) ⟨2764016, by rfl⟩ : syracuseStep 3685355 = 5528033) B5528033
theorem B1637567 : Blo 1636017 1637567 := bstep (se 1 (by rfl) ⟨1228175, by rfl⟩ : syracuseStep 1637567 = 2456351) B2456351
theorem B9322087 : Blo 1636017 9322087 := bstep (se 1 (by rfl) ⟨6991565, by rfl⟩ : syracuseStep 9322087 = 13983131) B13983131
theorem B19906667 : Blo 1636017 19906667 := bstep (se 1 (by rfl) ⟨14930000, by rfl⟩ : syracuseStep 19906667 = 29860001) B29860001
theorem B10486097 : Blo 1636017 10486097 := bstep (se 2 (by rfl) ⟨3932286, by rfl⟩ : syracuseStep 10486097 = 7864573) B7864573
theorem B3933161 : Blo 1636017 3933161 := bstep (se 2 (by rfl) ⟨1474935, by rfl⟩ : syracuseStep 3933161 = 2949871) B2949871
theorem B12429449 : Blo 1636017 12429449 := bstep (se 2 (by rfl) ⟨4661043, by rfl⟩ : syracuseStep 12429449 = 9322087) B9322087
theorem B8284841 : Blo 1636017 8284841 := bstep (se 2 (by rfl) ⟨3106815, by rfl⟩ : syracuseStep 8284841 = 6213631) B6213631
theorem B22407911 : Blo 1636017 22407911 := bstep (se 1 (by rfl) ⟨16805933, by rfl⟩ : syracuseStep 22407911 = 33611867) B33611867
theorem B26921963 : Blo 1636017 26921963 := bstep (se 1 (by rfl) ⟨20191472, by rfl⟩ : syracuseStep 26921963 = 40382945) B40382945
theorem B35385113 : Blo 1636017 35385113 := bstep (se 2 (by rfl) ⟨13269417, by rfl⟩ : syracuseStep 35385113 = 26538835) B26538835
theorem B2454143 : Blo 1636017 2454143 := bstep (se 1 (by rfl) ⟨1840607, by rfl⟩ : syracuseStep 2454143 = 3681215) B3681215
theorem B6214589 : Blo 1636017 6214589 := bstep (se 3 (by rfl) ⟨1165235, by rfl⟩ : syracuseStep 6214589 = 2330471) B2330471
theorem B12432365 : Blo 1636017 12432365 := bstep (se 3 (by rfl) ⟨2331068, by rfl⟩ : syracuseStep 12432365 = 4662137) B4662137
theorem B2454719 : Blo 1636017 2454719 := bstep (se 1 (by rfl) ⟨1841039, by rfl⟩ : syracuseStep 2454719 = 3682079) B3682079
theorem B8975551 : Blo 1636017 8975551 := bstep (se 1 (by rfl) ⟨6731663, by rfl⟩ : syracuseStep 8975551 = 13463327) B13463327
theorem B13276493 : Blo 1636017 13276493 := bstep (se 3 (by rfl) ⟨2489342, by rfl⟩ : syracuseStep 13276493 = 4978685) B4978685
theorem B1636031 : Blo 1636017 1636031 := bstep (se 1 (by rfl) ⟨1227023, by rfl⟩ : syracuseStep 1636031 = 2454047) B2454047
theorem B13268711 : Blo 1636017 13268711 := bstep (se 1 (by rfl) ⟨9951533, by rfl⟩ : syracuseStep 13268711 = 19903067) B19903067
theorem B11671571 : Blo 1636017 11671571 := bstep (se 1 (by rfl) ⟨8753678, by rfl⟩ : syracuseStep 11671571 = 17507357) B17507357
theorem B3733631 : Blo 1636017 3733631 := bstep (se 1 (by rfl) ⟨2800223, by rfl⟩ : syracuseStep 3733631 = 5600447) B5600447
theorem B1636863 : Blo 1636017 1636863 := bstep (se 1 (by rfl) ⟨1227647, by rfl⟩ : syracuseStep 1636863 = 2455295) B2455295
theorem B2456423 : Blo 1636017 2456423 := bstep (se 1 (by rfl) ⟨1842317, by rfl⟩ : syracuseStep 2456423 = 3684635) B3684635
theorem B59702183 : Blo 1636017 59702183 := bstep (se 1 (by rfl) ⟨44776637, by rfl⟩ : syracuseStep 59702183 = 89553275) B89553275
theorem B20978797 : Blo 1636017 20978797 := bstep (se 3 (by rfl) ⟨3933524, by rfl⟩ : syracuseStep 20978797 = 7867049) B7867049
theorem B2456687 : Blo 1636017 2456687 := bstep (se 1 (by rfl) ⟨1842515, by rfl⟩ : syracuseStep 2456687 = 3685031) B3685031
theorem B460094741 : Blo 1636017 460094741 := bstep (se 6 (by rfl) ⟨10783470, by rfl⟩ : syracuseStep 460094741 = 21566941) B21566941
theorem B1637679 : Blo 1636017 1637679 := bstep (se 1 (by rfl) ⟨1228259, by rfl⟩ : syracuseStep 1637679 = 2456519) B2456519
theorem B2456903 : Blo 1636017 2456903 := bstep (se 1 (by rfl) ⟨1842677, by rfl⟩ : syracuseStep 2456903 = 3685355) B3685355
theorem B23600807 : Blo 1636017 23600807 := bstep (se 1 (by rfl) ⟨17700605, by rfl⟩ : syracuseStep 23600807 = 35401211) B35401211
theorem B13271111 : Blo 1636017 13271111 := bstep (se 1 (by rfl) ⟨9953333, by rfl⟩ : syracuseStep 13271111 = 19906667) B19906667
theorem B2622107 : Blo 1636017 2622107 := bstep (se 1 (by rfl) ⟨1966580, by rfl⟩ : syracuseStep 2622107 = 3933161) B3933161
theorem B5523227 : Blo 1636017 5523227 := bstep (se 1 (by rfl) ⟨4142420, by rfl⟩ : syracuseStep 5523227 = 8284841) B8284841
theorem B31124189 : Blo 1636017 31124189 := bstep (se 3 (by rfl) ⟨5835785, by rfl⟩ : syracuseStep 31124189 = 11671571) B11671571
theorem B6990731 : Blo 1636017 6990731 := bstep (se 1 (by rfl) ⟨5243048, by rfl⟩ : syracuseStep 6990731 = 10486097) B10486097
theorem B8850995 : Blo 1636017 8850995 := bstep (se 1 (by rfl) ⟨6638246, by rfl⟩ : syracuseStep 8850995 = 13276493) B13276493
theorem B8286299 : Blo 1636017 8286299 := bstep (se 1 (by rfl) ⟨6214724, by rfl⟩ : syracuseStep 8286299 = 12429449) B12429449
theorem B27971729 : Blo 1636017 27971729 := bstep (se 2 (by rfl) ⟨10489398, by rfl⟩ : syracuseStep 27971729 = 20978797) B20978797
theorem B14938607 : Blo 1636017 14938607 := bstep (se 1 (by rfl) ⟨11203955, by rfl⟩ : syracuseStep 14938607 = 22407911) B22407911
theorem B39801455 : Blo 1636017 39801455 := bstep (se 1 (by rfl) ⟨29851091, by rfl⟩ : syracuseStep 39801455 = 59702183) B59702183
theorem B94360301 : Blo 1636017 94360301 := bstep (se 3 (by rfl) ⟨17692556, by rfl⟩ : syracuseStep 94360301 = 35385113) B35385113
theorem B306729827 : Blo 1636017 306729827 := bstep (se 1 (by rfl) ⟨230047370, by rfl⟩ : syracuseStep 306729827 = 460094741) B460094741
theorem B15733871 : Blo 1636017 15733871 := bstep (se 1 (by rfl) ⟨11800403, by rfl⟩ : syracuseStep 15733871 = 23600807) B23600807
theorem B1636095 : Blo 1636017 1636095 := bstep (se 1 (by rfl) ⟨1227071, by rfl⟩ : syracuseStep 1636095 = 2454143) B2454143
theorem B4143059 : Blo 1636017 4143059 := bstep (se 1 (by rfl) ⟨3107294, by rfl⟩ : syracuseStep 4143059 = 6214589) B6214589
theorem B8288243 : Blo 1636017 8288243 := bstep (se 1 (by rfl) ⟨6216182, by rfl⟩ : syracuseStep 8288243 = 12432365) B12432365
theorem B1636479 : Blo 1636017 1636479 := bstep (se 1 (by rfl) ⟨1227359, by rfl⟩ : syracuseStep 1636479 = 2454719) B2454719
theorem B8845807 : Blo 1636017 8845807 := bstep (se 1 (by rfl) ⟨6634355, by rfl⟩ : syracuseStep 8845807 = 13268711) B13268711
theorem B2489087 : Blo 1636017 2489087 := bstep (se 1 (by rfl) ⟨1866815, by rfl⟩ : syracuseStep 2489087 = 3733631) B3733631
theorem B11967401 : Blo 1636017 11967401 := bstep (se 2 (by rfl) ⟨4487775, by rfl⟩ : syracuseStep 11967401 = 8975551) B8975551
theorem B1637615 : Blo 1636017 1637615 := bstep (se 1 (by rfl) ⟨1228211, by rfl⟩ : syracuseStep 1637615 = 2456423) B2456423
theorem B17947975 : Blo 1636017 17947975 := bstep (se 1 (by rfl) ⟨13460981, by rfl⟩ : syracuseStep 17947975 = 26921963) B26921963
theorem B1637791 : Blo 1636017 1637791 := bstep (se 1 (by rfl) ⟨1228343, by rfl⟩ : syracuseStep 1637791 = 2456687) B2456687
theorem B1637935 : Blo 1636017 1637935 := bstep (se 1 (by rfl) ⟨1228451, by rfl⟩ : syracuseStep 1637935 = 2456903) B2456903
theorem B8847407 : Blo 1636017 8847407 := bstep (se 1 (by rfl) ⟨6635555, by rfl⟩ : syracuseStep 8847407 = 13271111) B13271111
theorem B26534303 : Blo 1636017 26534303 := bstep (se 1 (by rfl) ⟨19900727, by rfl⟩ : syracuseStep 26534303 = 39801455) B39801455
theorem B62906867 : Blo 1636017 62906867 := bstep (se 1 (by rfl) ⟨47180150, by rfl⟩ : syracuseStep 62906867 = 94360301) B94360301
theorem B2762039 : Blo 1636017 2762039 := bstep (se 1 (by rfl) ⟨2071529, by rfl⟩ : syracuseStep 2762039 = 4143059) B4143059
theorem B23930633 : Blo 1636017 23930633 := bstep (se 2 (by rfl) ⟨8973987, by rfl⟩ : syracuseStep 23930633 = 17947975) B17947975
theorem B6637565 : Blo 1636017 6637565 := bstep (se 3 (by rfl) ⟨1244543, by rfl⟩ : syracuseStep 6637565 = 2489087) B2489087
theorem B5900663 : Blo 1636017 5900663 := bstep (se 1 (by rfl) ⟨4425497, by rfl⟩ : syracuseStep 5900663 = 8850995) B8850995
theorem B5524199 : Blo 1636017 5524199 := bstep (se 1 (by rfl) ⟨4143149, by rfl⟩ : syracuseStep 5524199 = 8286299) B8286299
theorem B18647819 : Blo 1636017 18647819 := bstep (se 1 (by rfl) ⟨13985864, by rfl⟩ : syracuseStep 18647819 = 27971729) B27971729
theorem B1748071 : Blo 1636017 1748071 := bstep (se 1 (by rfl) ⟨1311053, by rfl⟩ : syracuseStep 1748071 = 2622107) B2622107
theorem B10489247 : Blo 1636017 10489247 := bstep (se 1 (by rfl) ⟨7866935, by rfl⟩ : syracuseStep 10489247 = 15733871) B15733871
theorem B3682151 : Blo 1636017 3682151 := bstep (se 1 (by rfl) ⟨2761613, by rfl⟩ : syracuseStep 3682151 = 5523227) B5523227
theorem B5525495 : Blo 1636017 5525495 := bstep (se 1 (by rfl) ⟨4144121, by rfl⟩ : syracuseStep 5525495 = 8288243) B8288243
theorem B9959071 : Blo 1636017 9959071 := bstep (se 1 (by rfl) ⟨7469303, by rfl⟩ : syracuseStep 9959071 = 14938607) B14938607
theorem B204486551 : Blo 1636017 204486551 := bstep (se 1 (by rfl) ⟨153364913, by rfl⟩ : syracuseStep 204486551 = 306729827) B306729827
theorem B11794409 : Blo 1636017 11794409 := bstep (se 2 (by rfl) ⟨4422903, by rfl⟩ : syracuseStep 11794409 = 8845807) B8845807
theorem B20749459 : Blo 1636017 20749459 := bstep (se 1 (by rfl) ⟨15562094, by rfl⟩ : syracuseStep 20749459 = 31124189) B31124189
theorem B4660487 : Blo 1636017 4660487 := bstep (se 1 (by rfl) ⟨3495365, by rfl⟩ : syracuseStep 4660487 = 6990731) B6990731
theorem B7978267 : Blo 1636017 7978267 := bstep (se 1 (by rfl) ⟨5983700, by rfl⟩ : syracuseStep 7978267 = 11967401) B11967401
theorem B5898271 : Blo 1636017 5898271 := bstep (se 1 (by rfl) ⟨4423703, by rfl⟩ : syracuseStep 5898271 = 8847407) B8847407
theorem B9323045 : Blo 1636017 9323045 := bstep (se 4 (by rfl) ⟨874035, by rfl⟩ : syracuseStep 9323045 = 1748071) B1748071
theorem B136324367 : Blo 1636017 136324367 := bstep (se 1 (by rfl) ⟨102243275, by rfl⟩ : syracuseStep 136324367 = 204486551) B204486551
theorem B4425043 : Blo 1636017 4425043 := bstep (se 1 (by rfl) ⟨3318782, by rfl⟩ : syracuseStep 4425043 = 6637565) B6637565
theorem B27665945 : Blo 1636017 27665945 := bstep (se 2 (by rfl) ⟨10374729, by rfl⟩ : syracuseStep 27665945 = 20749459) B20749459
theorem B3933775 : Blo 1636017 3933775 := bstep (se 1 (by rfl) ⟨2950331, by rfl⟩ : syracuseStep 3933775 = 5900663) B5900663
theorem B3106991 : Blo 1636017 3106991 := bstep (se 1 (by rfl) ⟨2330243, by rfl⟩ : syracuseStep 3106991 = 4660487) B4660487
theorem B17689535 : Blo 1636017 17689535 := bstep (se 1 (by rfl) ⟨13267151, by rfl⟩ : syracuseStep 17689535 = 26534303) B26534303
theorem B41937911 : Blo 1636017 41937911 := bstep (se 1 (by rfl) ⟨31453433, by rfl⟩ : syracuseStep 41937911 = 62906867) B62906867
theorem B15953755 : Blo 1636017 15953755 := bstep (se 1 (by rfl) ⟨11965316, by rfl⟩ : syracuseStep 15953755 = 23930633) B23930633
theorem B10637689 : Blo 1636017 10637689 := bstep (se 2 (by rfl) ⟨3989133, by rfl⟩ : syracuseStep 10637689 = 7978267) B7978267
theorem B3682799 : Blo 1636017 3682799 := bstep (se 1 (by rfl) ⟨2762099, by rfl⟩ : syracuseStep 3682799 = 5524199) B5524199
theorem B12431879 : Blo 1636017 12431879 := bstep (se 1 (by rfl) ⟨9323909, by rfl⟩ : syracuseStep 12431879 = 18647819) B18647819
theorem B6992831 : Blo 1636017 6992831 := bstep (se 1 (by rfl) ⟨5244623, by rfl⟩ : syracuseStep 6992831 = 10489247) B10489247
theorem B2454767 : Blo 1636017 2454767 := bstep (se 1 (by rfl) ⟨1841075, by rfl⟩ : syracuseStep 2454767 = 3682151) B3682151
theorem B3683663 : Blo 1636017 3683663 := bstep (se 1 (by rfl) ⟨2762747, by rfl⟩ : syracuseStep 3683663 = 5525495) B5525495
theorem B1841359 : Blo 1636017 1841359 := bstep (se 1 (by rfl) ⟨1381019, by rfl⟩ : syracuseStep 1841359 = 2762039) B2762039
theorem B7862939 : Blo 1636017 7862939 := bstep (se 1 (by rfl) ⟨5897204, by rfl⟩ : syracuseStep 7862939 = 11794409) B11794409
theorem B13278761 : Blo 1636017 13278761 := bstep (se 2 (by rfl) ⟨4979535, by rfl⟩ : syracuseStep 13278761 = 9959071) B9959071
theorem B7864361 : Blo 1636017 7864361 := bstep (se 2 (by rfl) ⟨2949135, by rfl⟩ : syracuseStep 7864361 = 5898271) B5898271
theorem B20980133 : Blo 1636017 20980133 := bstep (se 4 (by rfl) ⟨1966887, by rfl⟩ : syracuseStep 20980133 = 3933775) B3933775
theorem B4661887 : Blo 1636017 4661887 := bstep (se 1 (by rfl) ⟨3496415, by rfl⟩ : syracuseStep 4661887 = 6992831) B6992831
theorem B90882911 : Blo 1636017 90882911 := bstep (se 1 (by rfl) ⟨68162183, by rfl⟩ : syracuseStep 90882911 = 136324367) B136324367
theorem B5900057 : Blo 1636017 5900057 := bstep (se 2 (by rfl) ⟨2212521, by rfl⟩ : syracuseStep 5900057 = 4425043) B4425043
theorem B14183585 : Blo 1636017 14183585 := bstep (se 2 (by rfl) ⟨5318844, by rfl⟩ : syracuseStep 14183585 = 10637689) B10637689
theorem B18443963 : Blo 1636017 18443963 := bstep (se 1 (by rfl) ⟨13832972, by rfl⟩ : syracuseStep 18443963 = 27665945) B27665945
theorem B11793023 : Blo 1636017 11793023 := bstep (se 1 (by rfl) ⟨8844767, by rfl⟩ : syracuseStep 11793023 = 17689535) B17689535
theorem B8852507 : Blo 1636017 8852507 := bstep (se 1 (by rfl) ⟨6639380, by rfl⟩ : syracuseStep 8852507 = 13278761) B13278761
theorem B21271673 : Blo 1636017 21271673 := bstep (se 2 (by rfl) ⟨7976877, by rfl⟩ : syracuseStep 21271673 = 15953755) B15953755
theorem B2455145 : Blo 1636017 2455145 := bstep (se 2 (by rfl) ⟨920679, by rfl⟩ : syracuseStep 2455145 = 1841359) B1841359
theorem B2455199 : Blo 1636017 2455199 := bstep (se 1 (by rfl) ⟨1841399, by rfl⟩ : syracuseStep 2455199 = 3682799) B3682799
theorem B8287919 : Blo 1636017 8287919 := bstep (se 1 (by rfl) ⟨6215939, by rfl⟩ : syracuseStep 8287919 = 12431879) B12431879
theorem B6215363 : Blo 1636017 6215363 := bstep (se 1 (by rfl) ⟨4661522, by rfl⟩ : syracuseStep 6215363 = 9323045) B9323045
theorem B1636511 : Blo 1636017 1636511 := bstep (se 1 (by rfl) ⟨1227383, by rfl⟩ : syracuseStep 1636511 = 2454767) B2454767
theorem B2455775 : Blo 1636017 2455775 := bstep (se 1 (by rfl) ⟨1841831, by rfl⟩ : syracuseStep 2455775 = 3683663) B3683663
theorem B2071327 : Blo 1636017 2071327 := bstep (se 1 (by rfl) ⟨1553495, by rfl⟩ : syracuseStep 2071327 = 3106991) B3106991
theorem B5241959 : Blo 1636017 5241959 := bstep (se 1 (by rfl) ⟨3931469, by rfl⟩ : syracuseStep 5241959 = 7862939) B7862939
theorem B27958607 : Blo 1636017 27958607 := bstep (se 1 (by rfl) ⟨20968955, by rfl⟩ : syracuseStep 27958607 = 41937911) B41937911
theorem B5242907 : Blo 1636017 5242907 := bstep (se 1 (by rfl) ⟨3932180, by rfl⟩ : syracuseStep 5242907 = 7864361) B7864361
theorem B60588607 : Blo 1636017 60588607 := bstep (se 1 (by rfl) ⟨45441455, by rfl⟩ : syracuseStep 60588607 = 90882911) B90882911
theorem B2761769 : Blo 1636017 2761769 := bstep (se 2 (by rfl) ⟨1035663, by rfl⟩ : syracuseStep 2761769 = 2071327) B2071327
theorem B3933371 : Blo 1636017 3933371 := bstep (se 1 (by rfl) ⟨2950028, by rfl⟩ : syracuseStep 3933371 = 5900057) B5900057
theorem B9455723 : Blo 1636017 9455723 := bstep (se 1 (by rfl) ⟨7091792, by rfl⟩ : syracuseStep 9455723 = 14183585) B14183585
theorem B18639071 : Blo 1636017 18639071 := bstep (se 1 (by rfl) ⟨13979303, by rfl⟩ : syracuseStep 18639071 = 27958607) B27958607
theorem B13986755 : Blo 1636017 13986755 := bstep (se 1 (by rfl) ⟨10490066, by rfl⟩ : syracuseStep 13986755 = 20980133) B20980133
theorem B56724461 : Blo 1636017 56724461 := bstep (se 3 (by rfl) ⟨10635836, by rfl⟩ : syracuseStep 56724461 = 21271673) B21271673
theorem B5901671 : Blo 1636017 5901671 := bstep (se 1 (by rfl) ⟨4426253, by rfl⟩ : syracuseStep 5901671 = 8852507) B8852507
theorem B5525279 : Blo 1636017 5525279 := bstep (se 1 (by rfl) ⟨4143959, by rfl⟩ : syracuseStep 5525279 = 8287919) B8287919
theorem B3494639 : Blo 1636017 3494639 := bstep (se 1 (by rfl) ⟨2620979, by rfl⟩ : syracuseStep 3494639 = 5241959) B5241959
theorem B7862015 : Blo 1636017 7862015 := bstep (se 1 (by rfl) ⟨5896511, by rfl⟩ : syracuseStep 7862015 = 11793023) B11793023
theorem B6215849 : Blo 1636017 6215849 := bstep (se 2 (by rfl) ⟨2330943, by rfl⟩ : syracuseStep 6215849 = 4661887) B4661887
theorem B1636763 : Blo 1636017 1636763 := bstep (se 1 (by rfl) ⟨1227572, by rfl⟩ : syracuseStep 1636763 = 2455145) B2455145
theorem B1636799 : Blo 1636017 1636799 := bstep (se 1 (by rfl) ⟨1227599, by rfl⟩ : syracuseStep 1636799 = 2455199) B2455199
theorem B4143575 : Blo 1636017 4143575 := bstep (se 1 (by rfl) ⟨3107681, by rfl⟩ : syracuseStep 4143575 = 6215363) B6215363
theorem B1637183 : Blo 1636017 1637183 := bstep (se 1 (by rfl) ⟨1227887, by rfl⟩ : syracuseStep 1637183 = 2455775) B2455775
theorem B12295975 : Blo 1636017 12295975 := bstep (se 1 (by rfl) ⟨9221981, by rfl⟩ : syracuseStep 12295975 = 18443963) B18443963
theorem B15737789 : Blo 1636017 15737789 := bstep (se 3 (by rfl) ⟨2950835, by rfl⟩ : syracuseStep 15737789 = 5901671) B5901671
theorem B2762383 : Blo 1636017 2762383 := bstep (se 1 (by rfl) ⟨2071787, by rfl⟩ : syracuseStep 2762383 = 4143575) B4143575
theorem B9324503 : Blo 1636017 9324503 := bstep (se 1 (by rfl) ⟨6993377, by rfl⟩ : syracuseStep 9324503 = 13986755) B13986755
theorem B37816307 : Blo 1636017 37816307 := bstep (se 1 (by rfl) ⟨28362230, by rfl⟩ : syracuseStep 37816307 = 56724461) B56724461
theorem B16394633 : Blo 1636017 16394633 := bstep (se 2 (by rfl) ⟨6147987, by rfl⟩ : syracuseStep 16394633 = 12295975) B12295975
theorem B10488989 : Blo 1636017 10488989 := bstep (se 3 (by rfl) ⟨1966685, by rfl⟩ : syracuseStep 10488989 = 3933371) B3933371
theorem B2329759 : Blo 1636017 2329759 := bstep (se 1 (by rfl) ⟨1747319, by rfl⟩ : syracuseStep 2329759 = 3494639) B3494639
theorem B80784809 : Blo 1636017 80784809 := bstep (se 2 (by rfl) ⟨30294303, by rfl⟩ : syracuseStep 80784809 = 60588607) B60588607
theorem B6303815 : Blo 1636017 6303815 := bstep (se 1 (by rfl) ⟨4727861, by rfl⟩ : syracuseStep 6303815 = 9455723) B9455723
theorem B3683519 : Blo 1636017 3683519 := bstep (se 1 (by rfl) ⟨2762639, by rfl⟩ : syracuseStep 3683519 = 5525279) B5525279
theorem B3495271 : Blo 1636017 3495271 := bstep (se 1 (by rfl) ⟨2621453, by rfl⟩ : syracuseStep 3495271 = 5242907) B5242907
theorem B1841179 : Blo 1636017 1841179 := bstep (se 1 (by rfl) ⟨1380884, by rfl⟩ : syracuseStep 1841179 = 2761769) B2761769
theorem B5241343 : Blo 1636017 5241343 := bstep (se 1 (by rfl) ⟨3931007, by rfl⟩ : syracuseStep 5241343 = 7862015) B7862015
theorem B4143899 : Blo 1636017 4143899 := bstep (se 1 (by rfl) ⟨3107924, by rfl⟩ : syracuseStep 4143899 = 6215849) B6215849
theorem B12426047 : Blo 1636017 12426047 := bstep (se 1 (by rfl) ⟨9319535, by rfl⟩ : syracuseStep 12426047 = 18639071) B18639071
theorem B4202543 : Blo 1636017 4202543 := bstep (se 1 (by rfl) ⟨3151907, by rfl⟩ : syracuseStep 4202543 = 6303815) B6303815
theorem B6988457 : Blo 1636017 6988457 := bstep (se 2 (by rfl) ⟨2620671, by rfl⟩ : syracuseStep 6988457 = 5241343) B5241343
theorem B3106345 : Blo 1636017 3106345 := bstep (se 2 (by rfl) ⟨1164879, by rfl⟩ : syracuseStep 3106345 = 2329759) B2329759
theorem B10929755 : Blo 1636017 10929755 := bstep (se 1 (by rfl) ⟨8197316, by rfl⟩ : syracuseStep 10929755 = 16394633) B16394633
theorem B2762599 : Blo 1636017 2762599 := bstep (se 1 (by rfl) ⟨2071949, by rfl⟩ : syracuseStep 2762599 = 4143899) B4143899
theorem B8284031 : Blo 1636017 8284031 := bstep (se 1 (by rfl) ⟨6213023, by rfl⟩ : syracuseStep 8284031 = 12426047) B12426047
theorem B53856539 : Blo 1636017 53856539 := bstep (se 1 (by rfl) ⟨40392404, by rfl⟩ : syracuseStep 53856539 = 80784809) B80784809
theorem B25210871 : Blo 1636017 25210871 := bstep (se 1 (by rfl) ⟨18908153, by rfl⟩ : syracuseStep 25210871 = 37816307) B37816307
theorem B6992659 : Blo 1636017 6992659 := bstep (se 1 (by rfl) ⟨5244494, by rfl⟩ : syracuseStep 6992659 = 10488989) B10488989
theorem B3683177 : Blo 1636017 3683177 := bstep (se 2 (by rfl) ⟨1381191, by rfl⟩ : syracuseStep 3683177 = 2762383) B2762383
theorem B2454905 : Blo 1636017 2454905 := bstep (se 2 (by rfl) ⟨920589, by rfl⟩ : syracuseStep 2454905 = 1841179) B1841179
theorem B10491859 : Blo 1636017 10491859 := bstep (se 1 (by rfl) ⟨7868894, by rfl⟩ : syracuseStep 10491859 = 15737789) B15737789
theorem B2455679 : Blo 1636017 2455679 := bstep (se 1 (by rfl) ⟨1841759, by rfl⟩ : syracuseStep 2455679 = 3683519) B3683519
theorem B6216335 : Blo 1636017 6216335 := bstep (se 1 (by rfl) ⟨4662251, by rfl⟩ : syracuseStep 6216335 = 9324503) B9324503
theorem B4660361 : Blo 1636017 4660361 := bstep (se 2 (by rfl) ⟨1747635, by rfl⟩ : syracuseStep 4660361 = 3495271) B3495271
theorem B11206781 : Blo 1636017 11206781 := bstep (se 3 (by rfl) ⟨2101271, by rfl⟩ : syracuseStep 11206781 = 4202543) B4202543
theorem B9323545 : Blo 1636017 9323545 := bstep (se 2 (by rfl) ⟨3496329, by rfl⟩ : syracuseStep 9323545 = 6992659) B6992659
theorem B5522687 : Blo 1636017 5522687 := bstep (se 1 (by rfl) ⟨4142015, by rfl⟩ : syracuseStep 5522687 = 8284031) B8284031
theorem B3106907 : Blo 1636017 3106907 := bstep (se 1 (by rfl) ⟨2330180, by rfl⟩ : syracuseStep 3106907 = 4660361) B4660361
theorem B4141793 : Blo 1636017 4141793 := bstep (se 2 (by rfl) ⟨1553172, by rfl⟩ : syracuseStep 4141793 = 3106345) B3106345
theorem B3683465 : Blo 1636017 3683465 := bstep (se 2 (by rfl) ⟨1381299, by rfl⟩ : syracuseStep 3683465 = 2762599) B2762599
theorem B13989145 : Blo 1636017 13989145 := bstep (se 2 (by rfl) ⟨5245929, by rfl⟩ : syracuseStep 13989145 = 10491859) B10491859
theorem B16807247 : Blo 1636017 16807247 := bstep (se 1 (by rfl) ⟨12605435, by rfl⟩ : syracuseStep 16807247 = 25210871) B25210871
theorem B4658971 : Blo 1636017 4658971 := bstep (se 1 (by rfl) ⟨3494228, by rfl⟩ : syracuseStep 4658971 = 6988457) B6988457
theorem B2455451 : Blo 1636017 2455451 := bstep (se 1 (by rfl) ⟨1841588, by rfl⟩ : syracuseStep 2455451 = 3683177) B3683177
theorem B1636603 : Blo 1636017 1636603 := bstep (se 1 (by rfl) ⟨1227452, by rfl⟩ : syracuseStep 1636603 = 2454905) B2454905
theorem B1637119 : Blo 1636017 1637119 := bstep (se 1 (by rfl) ⟨1227839, by rfl⟩ : syracuseStep 1637119 = 2455679) B2455679
theorem B35904359 : Blo 1636017 35904359 := bstep (se 1 (by rfl) ⟨26928269, by rfl⟩ : syracuseStep 35904359 = 53856539) B53856539
theorem B29146013 : Blo 1636017 29146013 := bstep (se 3 (by rfl) ⟨5464877, by rfl⟩ : syracuseStep 29146013 = 10929755) B10929755
theorem B4144223 : Blo 1636017 4144223 := bstep (se 1 (by rfl) ⟨3108167, by rfl⟩ : syracuseStep 4144223 = 6216335) B6216335
theorem B7471187 : Blo 1636017 7471187 := bstep (se 1 (by rfl) ⟨5603390, by rfl⟩ : syracuseStep 7471187 = 11206781) B11206781
theorem B2761195 : Blo 1636017 2761195 := bstep (se 1 (by rfl) ⟨2070896, by rfl⟩ : syracuseStep 2761195 = 4141793) B4141793
theorem B2762815 : Blo 1636017 2762815 := bstep (se 1 (by rfl) ⟨2072111, by rfl⟩ : syracuseStep 2762815 = 4144223) B4144223
theorem B6211961 : Blo 1636017 6211961 := bstep (se 2 (by rfl) ⟨2329485, by rfl⟩ : syracuseStep 6211961 = 4658971) B4658971
theorem B3681791 : Blo 1636017 3681791 := bstep (se 1 (by rfl) ⟨2761343, by rfl⟩ : syracuseStep 3681791 = 5522687) B5522687
theorem B12431393 : Blo 1636017 12431393 := bstep (se 2 (by rfl) ⟨4661772, by rfl⟩ : syracuseStep 12431393 = 9323545) B9323545
theorem B11204831 : Blo 1636017 11204831 := bstep (se 1 (by rfl) ⟨8403623, by rfl⟩ : syracuseStep 11204831 = 16807247) B16807247
theorem B2455643 : Blo 1636017 2455643 := bstep (se 1 (by rfl) ⟨1841732, by rfl⟩ : syracuseStep 2455643 = 3683465) B3683465
theorem B1636967 : Blo 1636017 1636967 := bstep (se 1 (by rfl) ⟨1227725, by rfl⟩ : syracuseStep 1636967 = 2455451) B2455451
theorem B2071271 : Blo 1636017 2071271 := bstep (se 1 (by rfl) ⟨1553453, by rfl⟩ : syracuseStep 2071271 = 3106907) B3106907
theorem B18652193 : Blo 1636017 18652193 := bstep (se 2 (by rfl) ⟨6994572, by rfl⟩ : syracuseStep 18652193 = 13989145) B13989145
theorem B23936239 : Blo 1636017 23936239 := bstep (se 1 (by rfl) ⟨17952179, by rfl⟩ : syracuseStep 23936239 = 35904359) B35904359
theorem B19430675 : Blo 1636017 19430675 := bstep (se 1 (by rfl) ⟨14573006, by rfl⟩ : syracuseStep 19430675 = 29146013) B29146013
theorem B4980791 : Blo 1636017 4980791 := bstep (se 1 (by rfl) ⟨3735593, by rfl⟩ : syracuseStep 4980791 = 7471187) B7471187
theorem B5523389 : Blo 1636017 5523389 := bstep (se 3 (by rfl) ⟨1035635, by rfl⟩ : syracuseStep 5523389 = 2071271) B2071271
theorem B12953783 : Blo 1636017 12953783 := bstep (se 1 (by rfl) ⟨9715337, by rfl⟩ : syracuseStep 12953783 = 19430675) B19430675
theorem B3681593 : Blo 1636017 3681593 := bstep (se 2 (by rfl) ⟨1380597, by rfl⟩ : syracuseStep 3681593 = 2761195) B2761195
theorem B127659941 : Blo 1636017 127659941 := bstep (se 4 (by rfl) ⟨11968119, by rfl⟩ : syracuseStep 127659941 = 23936239) B23936239
theorem B4141307 : Blo 1636017 4141307 := bstep (se 1 (by rfl) ⟨3105980, by rfl⟩ : syracuseStep 4141307 = 6211961) B6211961
theorem B2454527 : Blo 1636017 2454527 := bstep (se 1 (by rfl) ⟨1840895, by rfl⟩ : syracuseStep 2454527 = 3681791) B3681791
theorem B8287595 : Blo 1636017 8287595 := bstep (se 1 (by rfl) ⟨6215696, by rfl⟩ : syracuseStep 8287595 = 12431393) B12431393
theorem B3683753 : Blo 1636017 3683753 := bstep (se 2 (by rfl) ⟨1381407, by rfl⟩ : syracuseStep 3683753 = 2762815) B2762815
theorem B1637095 : Blo 1636017 1637095 := bstep (se 1 (by rfl) ⟨1227821, by rfl⟩ : syracuseStep 1637095 = 2455643) B2455643
theorem B7469887 : Blo 1636017 7469887 := bstep (se 1 (by rfl) ⟨5602415, by rfl⟩ : syracuseStep 7469887 = 11204831) B11204831
theorem B12434795 : Blo 1636017 12434795 := bstep (se 1 (by rfl) ⟨9326096, by rfl⟩ : syracuseStep 12434795 = 18652193) B18652193
theorem B2760871 : Blo 1636017 2760871 := bstep (se 1 (by rfl) ⟨2070653, by rfl⟩ : syracuseStep 2760871 = 4141307) B4141307
theorem B8635855 : Blo 1636017 8635855 := bstep (se 1 (by rfl) ⟨6476891, by rfl⟩ : syracuseStep 8635855 = 12953783) B12953783
theorem B3320527 : Blo 1636017 3320527 := bstep (se 1 (by rfl) ⟨2490395, by rfl⟩ : syracuseStep 3320527 = 4980791) B4980791
theorem B5525063 : Blo 1636017 5525063 := bstep (se 1 (by rfl) ⟨4143797, by rfl⟩ : syracuseStep 5525063 = 8287595) B8287595
theorem B3682259 : Blo 1636017 3682259 := bstep (se 1 (by rfl) ⟨2761694, by rfl⟩ : syracuseStep 3682259 = 5523389) B5523389
theorem B2454395 : Blo 1636017 2454395 := bstep (se 1 (by rfl) ⟨1840796, by rfl⟩ : syracuseStep 2454395 = 3681593) B3681593
theorem B1636351 : Blo 1636017 1636351 := bstep (se 1 (by rfl) ⟨1227263, by rfl⟩ : syracuseStep 1636351 = 2454527) B2454527
theorem B2455835 : Blo 1636017 2455835 := bstep (se 1 (by rfl) ⟨1841876, by rfl⟩ : syracuseStep 2455835 = 3683753) B3683753
theorem B9959849 : Blo 1636017 9959849 := bstep (se 2 (by rfl) ⟨3734943, by rfl⟩ : syracuseStep 9959849 = 7469887) B7469887
theorem B8289863 : Blo 1636017 8289863 := bstep (se 1 (by rfl) ⟨6217397, by rfl⟩ : syracuseStep 8289863 = 12434795) B12434795
theorem B85106627 : Blo 1636017 85106627 := bstep (se 1 (by rfl) ⟨63829970, by rfl⟩ : syracuseStep 85106627 = 127659941) B127659941
theorem B3681161 : Blo 1636017 3681161 := bstep (se 2 (by rfl) ⟨1380435, by rfl⟩ : syracuseStep 3681161 = 2760871) B2760871
theorem B4427369 : Blo 1636017 4427369 := bstep (se 2 (by rfl) ⟨1660263, by rfl⟩ : syracuseStep 4427369 = 3320527) B3320527
theorem B6639899 : Blo 1636017 6639899 := bstep (se 1 (by rfl) ⟨4979924, by rfl⟩ : syracuseStep 6639899 = 9959849) B9959849
theorem B11514473 : Blo 1636017 11514473 := bstep (se 2 (by rfl) ⟨4317927, by rfl⟩ : syracuseStep 11514473 = 8635855) B8635855
theorem B3683375 : Blo 1636017 3683375 := bstep (se 1 (by rfl) ⟨2762531, by rfl⟩ : syracuseStep 3683375 = 5525063) B5525063
theorem B5526575 : Blo 1636017 5526575 := bstep (se 1 (by rfl) ⟨4144931, by rfl⟩ : syracuseStep 5526575 = 8289863) B8289863
theorem B2454839 : Blo 1636017 2454839 := bstep (se 1 (by rfl) ⟨1841129, by rfl⟩ : syracuseStep 2454839 = 3682259) B3682259
theorem B1636263 : Blo 1636017 1636263 := bstep (se 1 (by rfl) ⟨1227197, by rfl⟩ : syracuseStep 1636263 = 2454395) B2454395
theorem B1637223 : Blo 1636017 1637223 := bstep (se 1 (by rfl) ⟨1227917, by rfl⟩ : syracuseStep 1637223 = 2455835) B2455835
theorem B56737751 : Blo 1636017 56737751 := bstep (se 1 (by rfl) ⟨42553313, by rfl⟩ : syracuseStep 56737751 = 85106627) B85106627
theorem B7676315 : Blo 1636017 7676315 := bstep (se 1 (by rfl) ⟨5757236, by rfl⟩ : syracuseStep 7676315 = 11514473) B11514473
theorem B2951579 : Blo 1636017 2951579 := bstep (se 1 (by rfl) ⟨2213684, by rfl⟩ : syracuseStep 2951579 = 4427369) B4427369
theorem B151300669 : Blo 1636017 151300669 := bstep (se 3 (by rfl) ⟨28368875, by rfl⟩ : syracuseStep 151300669 = 56737751) B56737751
theorem B17706397 : Blo 1636017 17706397 := bstep (se 3 (by rfl) ⟨3319949, by rfl⟩ : syracuseStep 17706397 = 6639899) B6639899
theorem B2454107 : Blo 1636017 2454107 := bstep (se 1 (by rfl) ⟨1840580, by rfl⟩ : syracuseStep 2454107 = 3681161) B3681161
theorem B2455583 : Blo 1636017 2455583 := bstep (se 1 (by rfl) ⟨1841687, by rfl⟩ : syracuseStep 2455583 = 3683375) B3683375
theorem B3684383 : Blo 1636017 3684383 := bstep (se 1 (by rfl) ⟨2763287, by rfl⟩ : syracuseStep 3684383 = 5526575) B5526575
theorem B1636559 : Blo 1636017 1636559 := bstep (se 1 (by rfl) ⟨1227419, by rfl⟩ : syracuseStep 1636559 = 2454839) B2454839
theorem B5117543 : Blo 1636017 5117543 := bstep (se 1 (by rfl) ⟨3838157, by rfl⟩ : syracuseStep 5117543 = 7676315) B7676315
theorem B1636071 : Blo 1636017 1636071 := bstep (se 1 (by rfl) ⟨1227053, by rfl⟩ : syracuseStep 1636071 = 2454107) B2454107
theorem B201734225 : Blo 1636017 201734225 := bstep (se 2 (by rfl) ⟨75650334, by rfl⟩ : syracuseStep 201734225 = 151300669) B151300669
theorem B7870877 : Blo 1636017 7870877 := bstep (se 3 (by rfl) ⟨1475789, by rfl⟩ : syracuseStep 7870877 = 2951579) B2951579
theorem B1637055 : Blo 1636017 1637055 := bstep (se 1 (by rfl) ⟨1227791, by rfl⟩ : syracuseStep 1637055 = 2455583) B2455583
theorem B2456255 : Blo 1636017 2456255 := bstep (se 1 (by rfl) ⟨1842191, by rfl⟩ : syracuseStep 2456255 = 3684383) B3684383
theorem B23608529 : Blo 1636017 23608529 := bstep (se 2 (by rfl) ⟨8853198, by rfl⟩ : syracuseStep 23608529 = 17706397) B17706397
theorem B134489483 : Blo 1636017 134489483 := bstep (se 1 (by rfl) ⟨100867112, by rfl⟩ : syracuseStep 134489483 = 201734225) B201734225
theorem B15739019 : Blo 1636017 15739019 := bstep (se 1 (by rfl) ⟨11804264, by rfl⟩ : syracuseStep 15739019 = 23608529) B23608529
theorem B3411695 : Blo 1636017 3411695 := bstep (se 1 (by rfl) ⟨2558771, by rfl⟩ : syracuseStep 3411695 = 5117543) B5117543
theorem B5247251 : Blo 1636017 5247251 := bstep (se 1 (by rfl) ⟨3935438, by rfl⟩ : syracuseStep 5247251 = 7870877) B7870877
theorem B1637503 : Blo 1636017 1637503 := bstep (se 1 (by rfl) ⟨1228127, by rfl⟩ : syracuseStep 1637503 = 2456255) B2456255
theorem B3498167 : Blo 1636017 3498167 := bstep (se 1 (by rfl) ⟨2623625, by rfl⟩ : syracuseStep 3498167 = 5247251) B5247251
theorem B2274463 : Blo 1636017 2274463 := bstep (se 1 (by rfl) ⟨1705847, by rfl⟩ : syracuseStep 2274463 = 3411695) B3411695
theorem B89659655 : Blo 1636017 89659655 := bstep (se 1 (by rfl) ⟨67244741, by rfl⟩ : syracuseStep 89659655 = 134489483) B134489483
theorem B10492679 : Blo 1636017 10492679 := bstep (se 1 (by rfl) ⟨7869509, by rfl⟩ : syracuseStep 10492679 = 15739019) B15739019
theorem B59773103 : Blo 1636017 59773103 := bstep (se 1 (by rfl) ⟨44829827, by rfl⟩ : syracuseStep 59773103 = 89659655) B89659655
theorem B27980477 : Blo 1636017 27980477 := bstep (se 3 (by rfl) ⟨5246339, by rfl⟩ : syracuseStep 27980477 = 10492679) B10492679
theorem B9328445 : Blo 1636017 9328445 := bstep (se 3 (by rfl) ⟨1749083, by rfl⟩ : syracuseStep 9328445 = 3498167) B3498167
theorem B12130469 : Blo 1636017 12130469 := bstep (se 4 (by rfl) ⟨1137231, by rfl⟩ : syracuseStep 12130469 = 2274463) B2274463
theorem B18653651 : Blo 1636017 18653651 := bstep (se 1 (by rfl) ⟨13990238, by rfl⟩ : syracuseStep 18653651 = 27980477) B27980477
theorem B6218963 : Blo 1636017 6218963 := bstep (se 1 (by rfl) ⟨4664222, by rfl⟩ : syracuseStep 6218963 = 9328445) B9328445
theorem B8086979 : Blo 1636017 8086979 := bstep (se 1 (by rfl) ⟨6065234, by rfl⟩ : syracuseStep 8086979 = 12130469) B12130469
theorem B39848735 : Blo 1636017 39848735 := bstep (se 1 (by rfl) ⟨29886551, by rfl⟩ : syracuseStep 39848735 = 59773103) B59773103
theorem B12435767 : Blo 1636017 12435767 := bstep (se 1 (by rfl) ⟨9326825, by rfl⟩ : syracuseStep 12435767 = 18653651) B18653651
theorem B4145975 : Blo 1636017 4145975 := bstep (se 1 (by rfl) ⟨3109481, by rfl⟩ : syracuseStep 4145975 = 6218963) B6218963
theorem B21565277 : Blo 1636017 21565277 := bstep (se 3 (by rfl) ⟨4043489, by rfl⟩ : syracuseStep 21565277 = 8086979) B8086979
theorem B26565823 : Blo 1636017 26565823 := bstep (se 1 (by rfl) ⟨19924367, by rfl⟩ : syracuseStep 26565823 = 39848735) B39848735
theorem B8290511 : Blo 1636017 8290511 := bstep (se 1 (by rfl) ⟨6217883, by rfl⟩ : syracuseStep 8290511 = 12435767) B12435767
theorem B2763983 : Blo 1636017 2763983 := bstep (se 1 (by rfl) ⟨2072987, by rfl⟩ : syracuseStep 2763983 = 4145975) B4145975
theorem B35421097 : Blo 1636017 35421097 := bstep (se 2 (by rfl) ⟨13282911, by rfl⟩ : syracuseStep 35421097 = 26565823) B26565823
theorem B14376851 : Blo 1636017 14376851 := bstep (se 1 (by rfl) ⟨10782638, by rfl⟩ : syracuseStep 14376851 = 21565277) B21565277
theorem B47228129 : Blo 1636017 47228129 := bstep (se 2 (by rfl) ⟨17710548, by rfl⟩ : syracuseStep 47228129 = 35421097) B35421097
theorem B5527007 : Blo 1636017 5527007 := bstep (se 1 (by rfl) ⟨4145255, by rfl⟩ : syracuseStep 5527007 = 8290511) B8290511
theorem B1842655 : Blo 1636017 1842655 := bstep (se 1 (by rfl) ⟨1381991, by rfl⟩ : syracuseStep 1842655 = 2763983) B2763983
theorem B9584567 : Blo 1636017 9584567 := bstep (se 1 (by rfl) ⟨7188425, by rfl⟩ : syracuseStep 9584567 = 14376851) B14376851
theorem B31485419 : Blo 1636017 31485419 := bstep (se 1 (by rfl) ⟨23614064, by rfl⟩ : syracuseStep 31485419 = 47228129) B47228129
theorem B3684671 : Blo 1636017 3684671 := bstep (se 1 (by rfl) ⟨2763503, by rfl⟩ : syracuseStep 3684671 = 5527007) B5527007
theorem B2456873 : Blo 1636017 2456873 := bstep (se 2 (by rfl) ⟨921327, by rfl⟩ : syracuseStep 2456873 = 1842655) B1842655
theorem B6389711 : Blo 1636017 6389711 := bstep (se 1 (by rfl) ⟨4792283, by rfl⟩ : syracuseStep 6389711 = 9584567) B9584567
theorem B20990279 : Blo 1636017 20990279 := bstep (se 1 (by rfl) ⟨15742709, by rfl⟩ : syracuseStep 20990279 = 31485419) B31485419
theorem B2456447 : Blo 1636017 2456447 := bstep (se 1 (by rfl) ⟨1842335, by rfl⟩ : syracuseStep 2456447 = 3684671) B3684671
theorem B1637915 : Blo 1636017 1637915 := bstep (se 1 (by rfl) ⟨1228436, by rfl⟩ : syracuseStep 1637915 = 2456873) B2456873
theorem B4259807 : Blo 1636017 4259807 := bstep (se 1 (by rfl) ⟨3194855, by rfl⟩ : syracuseStep 4259807 = 6389711) B6389711
theorem B13993519 : Blo 1636017 13993519 := bstep (se 1 (by rfl) ⟨10495139, by rfl⟩ : syracuseStep 13993519 = 20990279) B20990279
theorem B2839871 : Blo 1636017 2839871 := bstep (se 1 (by rfl) ⟨2129903, by rfl⟩ : syracuseStep 2839871 = 4259807) B4259807
theorem B1637631 : Blo 1636017 1637631 := bstep (se 1 (by rfl) ⟨1228223, by rfl⟩ : syracuseStep 1637631 = 2456447) B2456447
theorem B7572989 : Blo 1636017 7572989 := bstep (se 3 (by rfl) ⟨1419935, by rfl⟩ : syracuseStep 7572989 = 2839871) B2839871
theorem B18658025 : Blo 1636017 18658025 := bstep (se 2 (by rfl) ⟨6996759, by rfl⟩ : syracuseStep 18658025 = 13993519) B13993519
theorem B5048659 : Blo 1636017 5048659 := bstep (se 1 (by rfl) ⟨3786494, by rfl⟩ : syracuseStep 5048659 = 7572989) B7572989
theorem B12438683 : Blo 1636017 12438683 := bstep (se 1 (by rfl) ⟨9329012, by rfl⟩ : syracuseStep 12438683 = 18658025) B18658025
theorem B8292455 : Blo 1636017 8292455 := bstep (se 1 (by rfl) ⟨6219341, by rfl⟩ : syracuseStep 8292455 = 12438683) B12438683
theorem B6731545 : Blo 1636017 6731545 := bstep (se 2 (by rfl) ⟨2524329, by rfl⟩ : syracuseStep 6731545 = 5048659) B5048659
theorem B8975393 : Blo 1636017 8975393 := bstep (se 2 (by rfl) ⟨3365772, by rfl⟩ : syracuseStep 8975393 = 6731545) B6731545
theorem B5528303 : Blo 1636017 5528303 := bstep (se 1 (by rfl) ⟨4146227, by rfl⟩ : syracuseStep 5528303 = 8292455) B8292455
theorem B5983595 : Blo 1636017 5983595 := bstep (se 1 (by rfl) ⟨4487696, by rfl⟩ : syracuseStep 5983595 = 8975393) B8975393
theorem B3685535 : Blo 1636017 3685535 := bstep (se 1 (by rfl) ⟨2764151, by rfl⟩ : syracuseStep 3685535 = 5528303) B5528303
theorem B2457023 : Blo 1636017 2457023 := bstep (se 1 (by rfl) ⟨1842767, by rfl⟩ : syracuseStep 2457023 = 3685535) B3685535
theorem B3989063 : Blo 1636017 3989063 := bstep (se 1 (by rfl) ⟨2991797, by rfl⟩ : syracuseStep 3989063 = 5983595) B5983595
theorem B2659375 : Blo 1636017 2659375 := bstep (se 1 (by rfl) ⟨1994531, by rfl⟩ : syracuseStep 2659375 = 3989063) B3989063
theorem B1638015 : Blo 1636017 1638015 := bstep (se 1 (by rfl) ⟨1228511, by rfl⟩ : syracuseStep 1638015 = 2457023) B2457023
theorem B14183333 : Blo 1636017 14183333 := bstep (se 4 (by rfl) ⟨1329687, by rfl⟩ : syracuseStep 14183333 = 2659375) B2659375
theorem B9455555 : Blo 1636017 9455555 := bstep (se 1 (by rfl) ⟨7091666, by rfl⟩ : syracuseStep 9455555 = 14183333) B14183333
theorem B6303703 : Blo 1636017 6303703 := bstep (se 1 (by rfl) ⟨4727777, by rfl⟩ : syracuseStep 6303703 = 9455555) B9455555
theorem B8404937 : Blo 1636017 8404937 := bstep (se 2 (by rfl) ⟨3151851, by rfl⟩ : syracuseStep 8404937 = 6303703) B6303703
theorem B5603291 : Blo 1636017 5603291 := bstep (se 1 (by rfl) ⟨4202468, by rfl⟩ : syracuseStep 5603291 = 8404937) B8404937
theorem B3735527 : Blo 1636017 3735527 := bstep (se 1 (by rfl) ⟨2801645, by rfl⟩ : syracuseStep 3735527 = 5603291) B5603291
theorem B39845621 : Blo 1636017 39845621 := bstep (se 5 (by rfl) ⟨1867763, by rfl⟩ : syracuseStep 39845621 = 3735527) B3735527
theorem B26563747 : Blo 1636017 26563747 := bstep (se 1 (by rfl) ⟨19922810, by rfl⟩ : syracuseStep 26563747 = 39845621) B39845621
theorem B35418329 : Blo 1636017 35418329 := bstep (se 2 (by rfl) ⟨13281873, by rfl⟩ : syracuseStep 35418329 = 26563747) B26563747
theorem B23612219 : Blo 1636017 23612219 := bstep (se 1 (by rfl) ⟨17709164, by rfl⟩ : syracuseStep 23612219 = 35418329) B35418329
theorem B15741479 : Blo 1636017 15741479 := bstep (se 1 (by rfl) ⟨11806109, by rfl⟩ : syracuseStep 15741479 = 23612219) B23612219
theorem B41977277 : Blo 1636017 41977277 := bstep (se 3 (by rfl) ⟨7870739, by rfl⟩ : syracuseStep 41977277 = 15741479) B15741479
theorem B27984851 : Blo 1636017 27984851 := bstep (se 1 (by rfl) ⟨20988638, by rfl⟩ : syracuseStep 27984851 = 41977277) B41977277
theorem B18656567 : Blo 1636017 18656567 := bstep (se 1 (by rfl) ⟨13992425, by rfl⟩ : syracuseStep 18656567 = 27984851) B27984851
theorem B12437711 : Blo 1636017 12437711 := bstep (se 1 (by rfl) ⟨9328283, by rfl⟩ : syracuseStep 12437711 = 18656567) B18656567
theorem B8291807 : Blo 1636017 8291807 := bstep (se 1 (by rfl) ⟨6218855, by rfl⟩ : syracuseStep 8291807 = 12437711) B12437711
theorem B5527871 : Blo 1636017 5527871 := bstep (se 1 (by rfl) ⟨4145903, by rfl⟩ : syracuseStep 5527871 = 8291807) B8291807
theorem B3685247 : Blo 1636017 3685247 := bstep (se 1 (by rfl) ⟨2763935, by rfl⟩ : syracuseStep 3685247 = 5527871) B5527871
theorem B2456831 : Blo 1636017 2456831 := bstep (se 1 (by rfl) ⟨1842623, by rfl⟩ : syracuseStep 2456831 = 3685247) B3685247
theorem B1637887 : Blo 1636017 1637887 := bstep (se 1 (by rfl) ⟨1228415, by rfl⟩ : syracuseStep 1637887 = 2456831) B2456831

theorem C0 (j : ℕ) (h1 : 409004 ≤ j) (h2 : j ≤ 409503) : Blo 1636017 (4 * j + 3) := by
  interval_cases j
  · exact B1636019
  · exact B1636023
  · exact B1636027
  · exact B1636031
  · exact B1636035
  · exact B1636039
  · exact B1636043
  · exact B1636047
  · exact B1636051
  · exact B1636055
  · exact B1636059
  · exact B1636063
  · exact B1636067
  · exact B1636071
  · exact B1636075
  · exact B1636079
  · exact B1636083
  · exact B1636087
  · exact B1636091
  · exact B1636095
  · exact B1636099
  · exact B1636103
  · exact B1636107
  · exact B1636111
  · exact B1636115
  · exact B1636119
  · exact B1636123
  · exact B1636127
  · exact B1636131
  · exact B1636135
  · exact B1636139
  · exact B1636143
  · exact B1636147
  · exact B1636151
  · exact B1636155
  · exact B1636159
  · exact B1636163
  · exact B1636167
  · exact B1636171
  · exact B1636175
  · exact B1636179
  · exact B1636183
  · exact B1636187
  · exact B1636191
  · exact B1636195
  · exact B1636199
  · exact B1636203
  · exact B1636207
  · exact B1636211
  · exact B1636215
  · exact B1636219
  · exact B1636223
  · exact B1636227
  · exact B1636231
  · exact B1636235
  · exact B1636239
  · exact B1636243
  · exact B1636247
  · exact B1636251
  · exact B1636255
  · exact B1636259
  · exact B1636263
  · exact B1636267
  · exact B1636271
  · exact B1636275
  · exact B1636279
  · exact B1636283
  · exact B1636287
  · exact B1636291
  · exact B1636295
  · exact B1636299
  · exact B1636303
  · exact B1636307
  · exact B1636311
  · exact B1636315
  · exact B1636319
  · exact B1636323
  · exact B1636327
  · exact B1636331
  · exact B1636335
  · exact B1636339
  · exact B1636343
  · exact B1636347
  · exact B1636351
  · exact B1636355
  · exact B1636359
  · exact B1636363
  · exact B1636367
  · exact B1636371
  · exact B1636375
  · exact B1636379
  · exact B1636383
  · exact B1636387
  · exact B1636391
  · exact B1636395
  · exact B1636399
  · exact B1636403
  · exact B1636407
  · exact B1636411
  · exact B1636415
  · exact B1636419
  · exact B1636423
  · exact B1636427
  · exact B1636431
  · exact B1636435
  · exact B1636439
  · exact B1636443
  · exact B1636447
  · exact B1636451
  · exact B1636455
  · exact B1636459
  · exact B1636463
  · exact B1636467
  · exact B1636471
  · exact B1636475
  · exact B1636479
  · exact B1636483
  · exact B1636487
  · exact B1636491
  · exact B1636495
  · exact B1636499
  · exact B1636503
  · exact B1636507
  · exact B1636511
  · exact B1636515
  · exact B1636519
  · exact B1636523
  · exact B1636527
  · exact B1636531
  · exact B1636535
  · exact B1636539
  · exact B1636543
  · exact B1636547
  · exact B1636551
  · exact B1636555
  · exact B1636559
  · exact B1636563
  · exact B1636567
  · exact B1636571
  · exact B1636575
  · exact B1636579
  · exact B1636583
  · exact B1636587
  · exact B1636591
  · exact B1636595
  · exact B1636599
  · exact B1636603
  · exact B1636607
  · exact B1636611
  · exact B1636615
  · exact B1636619
  · exact B1636623
  · exact B1636627
  · exact B1636631
  · exact B1636635
  · exact B1636639
  · exact B1636643
  · exact B1636647
  · exact B1636651
  · exact B1636655
  · exact B1636659
  · exact B1636663
  · exact B1636667
  · exact B1636671
  · exact B1636675
  · exact B1636679
  · exact B1636683
  · exact B1636687
  · exact B1636691
  · exact B1636695
  · exact B1636699
  · exact B1636703
  · exact B1636707
  · exact B1636711
  · exact B1636715
  · exact B1636719
  · exact B1636723
  · exact B1636727
  · exact B1636731
  · exact B1636735
  · exact B1636739
  · exact B1636743
  · exact B1636747
  · exact B1636751
  · exact B1636755
  · exact B1636759
  · exact B1636763
  · exact B1636767
  · exact B1636771
  · exact B1636775
  · exact B1636779
  · exact B1636783
  · exact B1636787
  · exact B1636791
  · exact B1636795
  · exact B1636799
  · exact B1636803
  · exact B1636807
  · exact B1636811
  · exact B1636815
  · exact B1636819
  · exact B1636823
  · exact B1636827
  · exact B1636831
  · exact B1636835
  · exact B1636839
  · exact B1636843
  · exact B1636847
  · exact B1636851
  · exact B1636855
  · exact B1636859
  · exact B1636863
  · exact B1636867
  · exact B1636871
  · exact B1636875
  · exact B1636879
  · exact B1636883
  · exact B1636887
  · exact B1636891
  · exact B1636895
  · exact B1636899
  · exact B1636903
  · exact B1636907
  · exact B1636911
  · exact B1636915
  · exact B1636919
  · exact B1636923
  · exact B1636927
  · exact B1636931
  · exact B1636935
  · exact B1636939
  · exact B1636943
  · exact B1636947
  · exact B1636951
  · exact B1636955
  · exact B1636959
  · exact B1636963
  · exact B1636967
  · exact B1636971
  · exact B1636975
  · exact B1636979
  · exact B1636983
  · exact B1636987
  · exact B1636991
  · exact B1636995
  · exact B1636999
  · exact B1637003
  · exact B1637007
  · exact B1637011
  · exact B1637015
  · exact B1637019
  · exact B1637023
  · exact B1637027
  · exact B1637031
  · exact B1637035
  · exact B1637039
  · exact B1637043
  · exact B1637047
  · exact B1637051
  · exact B1637055
  · exact B1637059
  · exact B1637063
  · exact B1637067
  · exact B1637071
  · exact B1637075
  · exact B1637079
  · exact B1637083
  · exact B1637087
  · exact B1637091
  · exact B1637095
  · exact B1637099
  · exact B1637103
  · exact B1637107
  · exact B1637111
  · exact B1637115
  · exact B1637119
  · exact B1637123
  · exact B1637127
  · exact B1637131
  · exact B1637135
  · exact B1637139
  · exact B1637143
  · exact B1637147
  · exact B1637151
  · exact B1637155
  · exact B1637159
  · exact B1637163
  · exact B1637167
  · exact B1637171
  · exact B1637175
  · exact B1637179
  · exact B1637183
  · exact B1637187
  · exact B1637191
  · exact B1637195
  · exact B1637199
  · exact B1637203
  · exact B1637207
  · exact B1637211
  · exact B1637215
  · exact B1637219
  · exact B1637223
  · exact B1637227
  · exact B1637231
  · exact B1637235
  · exact B1637239
  · exact B1637243
  · exact B1637247
  · exact B1637251
  · exact B1637255
  · exact B1637259
  · exact B1637263
  · exact B1637267
  · exact B1637271
  · exact B1637275
  · exact B1637279
  · exact B1637283
  · exact B1637287
  · exact B1637291
  · exact B1637295
  · exact B1637299
  · exact B1637303
  · exact B1637307
  · exact B1637311
  · exact B1637315
  · exact B1637319
  · exact B1637323
  · exact B1637327
  · exact B1637331
  · exact B1637335
  · exact B1637339
  · exact B1637343
  · exact B1637347
  · exact B1637351
  · exact B1637355
  · exact B1637359
  · exact B1637363
  · exact B1637367
  · exact B1637371
  · exact B1637375
  · exact B1637379
  · exact B1637383
  · exact B1637387
  · exact B1637391
  · exact B1637395
  · exact B1637399
  · exact B1637403
  · exact B1637407
  · exact B1637411
  · exact B1637415
  · exact B1637419
  · exact B1637423
  · exact B1637427
  · exact B1637431
  · exact B1637435
  · exact B1637439
  · exact B1637443
  · exact B1637447
  · exact B1637451
  · exact B1637455
  · exact B1637459
  · exact B1637463
  · exact B1637467
  · exact B1637471
  · exact B1637475
  · exact B1637479
  · exact B1637483
  · exact B1637487
  · exact B1637491
  · exact B1637495
  · exact B1637499
  · exact B1637503
  · exact B1637507
  · exact B1637511
  · exact B1637515
  · exact B1637519
  · exact B1637523
  · exact B1637527
  · exact B1637531
  · exact B1637535
  · exact B1637539
  · exact B1637543
  · exact B1637547
  · exact B1637551
  · exact B1637555
  · exact B1637559
  · exact B1637563
  · exact B1637567
  · exact B1637571
  · exact B1637575
  · exact B1637579
  · exact B1637583
  · exact B1637587
  · exact B1637591
  · exact B1637595
  · exact B1637599
  · exact B1637603
  · exact B1637607
  · exact B1637611
  · exact B1637615
  · exact B1637619
  · exact B1637623
  · exact B1637627
  · exact B1637631
  · exact B1637635
  · exact B1637639
  · exact B1637643
  · exact B1637647
  · exact B1637651
  · exact B1637655
  · exact B1637659
  · exact B1637663
  · exact B1637667
  · exact B1637671
  · exact B1637675
  · exact B1637679
  · exact B1637683
  · exact B1637687
  · exact B1637691
  · exact B1637695
  · exact B1637699
  · exact B1637703
  · exact B1637707
  · exact B1637711
  · exact B1637715
  · exact B1637719
  · exact B1637723
  · exact B1637727
  · exact B1637731
  · exact B1637735
  · exact B1637739
  · exact B1637743
  · exact B1637747
  · exact B1637751
  · exact B1637755
  · exact B1637759
  · exact B1637763
  · exact B1637767
  · exact B1637771
  · exact B1637775
  · exact B1637779
  · exact B1637783
  · exact B1637787
  · exact B1637791
  · exact B1637795
  · exact B1637799
  · exact B1637803
  · exact B1637807
  · exact B1637811
  · exact B1637815
  · exact B1637819
  · exact B1637823
  · exact B1637827
  · exact B1637831
  · exact B1637835
  · exact B1637839
  · exact B1637843
  · exact B1637847
  · exact B1637851
  · exact B1637855
  · exact B1637859
  · exact B1637863
  · exact B1637867
  · exact B1637871
  · exact B1637875
  · exact B1637879
  · exact B1637883
  · exact B1637887
  · exact B1637891
  · exact B1637895
  · exact B1637899
  · exact B1637903
  · exact B1637907
  · exact B1637911
  · exact B1637915
  · exact B1637919
  · exact B1637923
  · exact B1637927
  · exact B1637931
  · exact B1637935
  · exact B1637939
  · exact B1637943
  · exact B1637947
  · exact B1637951
  · exact B1637955
  · exact B1637959
  · exact B1637963
  · exact B1637967
  · exact B1637971
  · exact B1637975
  · exact B1637979
  · exact B1637983
  · exact B1637987
  · exact B1637991
  · exact B1637995
  · exact B1637999
  · exact B1638003
  · exact B1638007
  · exact B1638011
  · exact B1638015

theorem solution (m : ℕ) (hlo : 1636017 ≤ m) (hhi : m ≤ 1638017) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 409004 ≤ j := by omega
    have hj2 : j ≤ 409503 := by omega
    have hb : Blo 1636017 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
