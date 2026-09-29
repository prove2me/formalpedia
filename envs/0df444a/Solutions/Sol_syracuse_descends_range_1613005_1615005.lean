-- Prove2me | solution 1 for syracuse_descends_range_1613005_1615005
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:12:17.614986+00:00
-- url     : https://prove2.me/submissions/af68d95e-040d-4ccc-a36f-0b2a24052b25

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


theorem B8175653 : Blo 1613005 8175653 := bbase (se 4 (by rfl) ⟨766467, by rfl⟩ : syracuseStep 8175653 = 1532935) (by norm_num)
theorem B11043029 : Blo 1613005 11043029 := bbase (se 7 (by rfl) ⟨129410, by rfl⟩ : syracuseStep 11043029 = 258821) (by norm_num)
theorem B3629285 : Blo 1613005 3629285 := bbase (se 4 (by rfl) ⟨340245, by rfl⟩ : syracuseStep 3629285 = 680491) (by norm_num)
theorem B3629357 : Blo 1613005 3629357 := bbase (se 3 (by rfl) ⟨680504, by rfl⟩ : syracuseStep 3629357 = 1361009) (by norm_num)
theorem B5448005 : Blo 1613005 5448005 := bbase (se 4 (by rfl) ⟨510750, by rfl⟩ : syracuseStep 5448005 = 1021501) (by norm_num)
theorem B3629429 : Blo 1613005 3629429 := bbase (se 5 (by rfl) ⟨170129, by rfl⟩ : syracuseStep 3629429 = 340259) (by norm_num)
theorem B3629501 : Blo 1613005 3629501 := bbase (se 3 (by rfl) ⟨680531, by rfl⟩ : syracuseStep 3629501 = 1361063) (by norm_num)
theorem B8167877 : Blo 1613005 8167877 := bbase (se 4 (by rfl) ⟨765738, by rfl⟩ : syracuseStep 8167877 = 1531477) (by norm_num)
theorem B5816789 : Blo 1613005 5816789 := bbase (se 7 (by rfl) ⟨68165, by rfl⟩ : syracuseStep 5816789 = 136331) (by norm_num)
theorem B2097649 : Blo 1613005 2097649 := bbase (se 2 (by rfl) ⟨786618, by rfl⟩ : syracuseStep 2097649 = 1573237) (by norm_num)
theorem B3629573 : Blo 1613005 3629573 := bbase (se 4 (by rfl) ⟨340272, by rfl⟩ : syracuseStep 3629573 = 680545) (by norm_num)
theorem B4596277 : Blo 1613005 4596277 := bbase (se 5 (by rfl) ⟨215450, by rfl⟩ : syracuseStep 4596277 = 430901) (by norm_num)
theorem B3629645 : Blo 1613005 3629645 := bbase (se 3 (by rfl) ⟨680558, by rfl⟩ : syracuseStep 3629645 = 1361117) (by norm_num)
theorem B3064405 : Blo 1613005 3064405 := bbase (se 8 (by rfl) ⟨17955, by rfl⟩ : syracuseStep 3064405 = 35911) (by norm_num)
theorem B6898277 : Blo 1613005 6898277 := bbase (se 4 (by rfl) ⟨646713, by rfl⟩ : syracuseStep 6898277 = 1293427) (by norm_num)
theorem B5898869 : Blo 1613005 5898869 := bbase (se 5 (by rfl) ⟨276509, by rfl⟩ : syracuseStep 5898869 = 553019) (by norm_num)
theorem B2908813 : Blo 1613005 2908813 := bbase (se 3 (by rfl) ⟨545402, by rfl⟩ : syracuseStep 2908813 = 1090805) (by norm_num)
theorem B3629717 : Blo 1613005 3629717 := bbase (se 6 (by rfl) ⟨85071, by rfl⟩ : syracuseStep 3629717 = 170143) (by norm_num)
theorem B3629789 : Blo 1613005 3629789 := bbase (se 3 (by rfl) ⟨680585, by rfl⟩ : syracuseStep 3629789 = 1361171) (by norm_num)
theorem B4907749 : Blo 1613005 4907749 := bbase (se 4 (by rfl) ⟨460101, by rfl⟩ : syracuseStep 4907749 = 920203) (by norm_num)
theorem B3064549 : Blo 1613005 3064549 := bbase (se 4 (by rfl) ⟨287301, by rfl⟩ : syracuseStep 3064549 = 574603) (by norm_num)
theorem B5448437 : Blo 1613005 5448437 := bbase (se 5 (by rfl) ⟨255395, by rfl⟩ : syracuseStep 5448437 = 510791) (by norm_num)
theorem B3629861 : Blo 1613005 3629861 := bbase (se 4 (by rfl) ⟨340299, by rfl⟩ : syracuseStep 3629861 = 680599) (by norm_num)
theorem B2909029 : Blo 1613005 2909029 := bbase (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) (by norm_num)
theorem B3629933 : Blo 1613005 3629933 := bbase (se 3 (by rfl) ⟨680612, by rfl⟩ : syracuseStep 3629933 = 1361225) (by norm_num)
theorem B3064709 : Blo 1613005 3064709 := bbase (se 4 (by rfl) ⟨287316, by rfl⟩ : syracuseStep 3064709 = 574633) (by norm_num)
theorem B9569173 : Blo 1613005 9569173 := bbase (se 6 (by rfl) ⟨224277, by rfl⟩ : syracuseStep 9569173 = 448555) (by norm_num)
theorem B3630005 : Blo 1613005 3630005 := bbase (se 5 (by rfl) ⟨170156, by rfl⟩ : syracuseStep 3630005 = 340313) (by norm_num)
theorem B6128581 : Blo 1613005 6128581 := bbase (se 4 (by rfl) ⟨574554, by rfl⟩ : syracuseStep 6128581 = 1149109) (by norm_num)
theorem B6890453 : Blo 1613005 6890453 := bbase (se 7 (by rfl) ⟨80747, by rfl⟩ : syracuseStep 6890453 = 161495) (by norm_num)
theorem B15516629 : Blo 1613005 15516629 := bbase (se 7 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 15516629 = 363671) (by norm_num)
theorem B3630077 : Blo 1613005 3630077 := bbase (se 3 (by rfl) ⟨680639, by rfl⟩ : syracuseStep 3630077 = 1361279) (by norm_num)
theorem B3679253 : Blo 1613005 3679253 := bbase (se 6 (by rfl) ⟨86232, by rfl⟩ : syracuseStep 3679253 = 172465) (by norm_num)
theorem B3064853 : Blo 1613005 3064853 := bbase (se 6 (by rfl) ⟨71832, by rfl⟩ : syracuseStep 3064853 = 143665) (by norm_num)
theorem B3630149 : Blo 1613005 3630149 := bbase (se 4 (by rfl) ⟨340326, by rfl⟩ : syracuseStep 3630149 = 680653) (by norm_num)
theorem B3630221 : Blo 1613005 3630221 := bbase (se 3 (by rfl) ⟨680666, by rfl⟩ : syracuseStep 3630221 = 1361333) (by norm_num)
theorem B5448869 : Blo 1613005 5448869 := bbase (se 4 (by rfl) ⟨510831, by rfl⟩ : syracuseStep 5448869 = 1021663) (by norm_num)
theorem B3630293 : Blo 1613005 3630293 := bbase (se 7 (by rfl) ⟨42542, by rfl⟩ : syracuseStep 3630293 = 85085) (by norm_num)
theorem B6128885 : Blo 1613005 6128885 := bbase (se 5 (by rfl) ⟨287291, by rfl⟩ : syracuseStep 6128885 = 574583) (by norm_num)
theorem B3630365 : Blo 1613005 3630365 := bbase (se 3 (by rfl) ⟨680693, by rfl⟩ : syracuseStep 3630365 = 1361387) (by norm_num)
theorem B3065141 : Blo 1613005 3065141 := bbase (se 5 (by rfl) ⟨143678, by rfl⟩ : syracuseStep 3065141 = 287357) (by norm_num)
theorem B3630437 : Blo 1613005 3630437 := bbase (se 4 (by rfl) ⟨340353, by rfl⟩ : syracuseStep 3630437 = 680707) (by norm_num)
theorem B1795429 : Blo 1613005 1795429 := bbase (se 4 (by rfl) ⟨168321, by rfl⟩ : syracuseStep 1795429 = 336643) (by norm_num)
theorem B3876245 : Blo 1613005 3876245 := bbase (se 6 (by rfl) ⟨90849, by rfl⟩ : syracuseStep 3876245 = 181699) (by norm_num)
theorem B3630509 : Blo 1613005 3630509 := bbase (se 3 (by rfl) ⟨680720, by rfl⟩ : syracuseStep 3630509 = 1361441) (by norm_num)
theorem B3065293 : Blo 1613005 3065293 := bbase (se 3 (by rfl) ⟨574742, by rfl⟩ : syracuseStep 3065293 = 1149485) (by norm_num)
theorem B3630581 : Blo 1613005 3630581 := bbase (se 5 (by rfl) ⟨170183, by rfl⟩ : syracuseStep 3630581 = 340367) (by norm_num)
theorem B3630653 : Blo 1613005 3630653 := bbase (se 3 (by rfl) ⟨680747, by rfl⟩ : syracuseStep 3630653 = 1361495) (by norm_num)
theorem B2098757 : Blo 1613005 2098757 := bbase (se 4 (by rfl) ⟨196758, by rfl⟩ : syracuseStep 2098757 = 393517) (by norm_num)
theorem B3876437 : Blo 1613005 3876437 := bbase (se 8 (by rfl) ⟨22713, by rfl⟩ : syracuseStep 3876437 = 45427) (by norm_num)
theorem B5449301 : Blo 1613005 5449301 := bbase (se 8 (by rfl) ⟨31929, by rfl⟩ : syracuseStep 5449301 = 63859) (by norm_num)
theorem B3630725 : Blo 1613005 3630725 := bbase (se 4 (by rfl) ⟨340380, by rfl⟩ : syracuseStep 3630725 = 680761) (by norm_num)
theorem B2909837 : Blo 1613005 2909837 := bbase (se 3 (by rfl) ⟨545594, by rfl⟩ : syracuseStep 2909837 = 1091189) (by norm_num)
theorem B2180773 : Blo 1613005 2180773 := bbase (se 4 (by rfl) ⟨204447, by rfl⟩ : syracuseStep 2180773 = 408895) (by norm_num)
theorem B3630797 : Blo 1613005 3630797 := bbase (se 3 (by rfl) ⟨680774, by rfl⟩ : syracuseStep 3630797 = 1361549) (by norm_num)
theorem B8169173 : Blo 1613005 8169173 := bbase (se 7 (by rfl) ⟨95732, by rfl⟩ : syracuseStep 8169173 = 191465) (by norm_num)
theorem B5523157 : Blo 1613005 5523157 := bbase (se 7 (by rfl) ⟨64724, by rfl⟩ : syracuseStep 5523157 = 129449) (by norm_num)
theorem B16574165 : Blo 1613005 16574165 := bbase (se 7 (by rfl) ⟨194228, by rfl⟩ : syracuseStep 16574165 = 388457) (by norm_num)
theorem B3065597 : Blo 1613005 3065597 := bbase (se 3 (by rfl) ⟨574799, by rfl⟩ : syracuseStep 3065597 = 1149599) (by norm_num)
theorem B3630869 : Blo 1613005 3630869 := bbase (se 6 (by rfl) ⟨85098, by rfl⟩ : syracuseStep 3630869 = 170197) (by norm_num)
theorem B2041625 : Blo 1613005 2041625 := bbase (se 2 (by rfl) ⟨765609, by rfl⟩ : syracuseStep 2041625 = 1531219) (by norm_num)
theorem B2909981 : Blo 1613005 2909981 := bbase (se 3 (by rfl) ⟨545621, by rfl⟩ : syracuseStep 2909981 = 1091243) (by norm_num)
theorem B2041681 : Blo 1613005 2041681 := bbase (se 2 (by rfl) ⟨765630, by rfl⟩ : syracuseStep 2041681 = 1531261) (by norm_num)
theorem B3630941 : Blo 1613005 3630941 := bbase (se 3 (by rfl) ⟨680801, by rfl⟩ : syracuseStep 3630941 = 1361603) (by norm_num)
theorem B2328421 : Blo 1613005 2328421 := bbase (se 4 (by rfl) ⟨218289, by rfl⟩ : syracuseStep 2328421 = 436579) (by norm_num)
theorem B3631013 : Blo 1613005 3631013 := bbase (se 4 (by rfl) ⟨340407, by rfl⟩ : syracuseStep 3631013 = 680815) (by norm_num)
theorem B2041777 : Blo 1613005 2041777 := bbase (se 2 (by rfl) ⟨765666, by rfl⟩ : syracuseStep 2041777 = 1531333) (by norm_num)
theorem B3631085 : Blo 1613005 3631085 := bbase (se 3 (by rfl) ⟨680828, by rfl⟩ : syracuseStep 3631085 = 1361657) (by norm_num)
theorem B2910197 : Blo 1613005 2910197 := bbase (se 5 (by rfl) ⟨136415, by rfl⟩ : syracuseStep 2910197 = 272831) (by norm_num)
theorem B5449733 : Blo 1613005 5449733 := bbase (se 4 (by rfl) ⟨510912, by rfl⟩ : syracuseStep 5449733 = 1021825) (by norm_num)
theorem B3631157 : Blo 1613005 3631157 := bbase (se 5 (by rfl) ⟨170210, by rfl⟩ : syracuseStep 3631157 = 340421) (by norm_num)
theorem B2041949 : Blo 1613005 2041949 := bbase (se 3 (by rfl) ⟨382865, by rfl⟩ : syracuseStep 2041949 = 765731) (by norm_num)
theorem B1722485 : Blo 1613005 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B3631229 : Blo 1613005 3631229 := bbase (se 3 (by rfl) ⟨680855, by rfl⟩ : syracuseStep 3631229 = 1361711) (by norm_num)
theorem B2042005 : Blo 1613005 2042005 := bbase (se 6 (by rfl) ⟨47859, by rfl⟩ : syracuseStep 2042005 = 95719) (by norm_num)
theorem B3631301 : Blo 1613005 3631301 := bbase (se 4 (by rfl) ⟨340434, by rfl⟩ : syracuseStep 3631301 = 680869) (by norm_num)
theorem B8726741 : Blo 1613005 8726741 := bbase (se 7 (by rfl) ⟨102266, by rfl⟩ : syracuseStep 8726741 = 204533) (by norm_num)
theorem B3885293 : Blo 1613005 3885293 := bbase (se 3 (by rfl) ⟨728492, by rfl⟩ : syracuseStep 3885293 = 1456985) (by norm_num)
theorem B2042101 : Blo 1613005 2042101 := bbase (se 5 (by rfl) ⟨95723, by rfl⟩ : syracuseStep 2042101 = 191447) (by norm_num)
theorem B2722045 : Blo 1613005 2722045 := bbase (se 3 (by rfl) ⟨510383, by rfl⟩ : syracuseStep 2722045 = 1020767) (by norm_num)
theorem B3631373 : Blo 1613005 3631373 := bbase (se 3 (by rfl) ⟨680882, by rfl⟩ : syracuseStep 3631373 = 1361765) (by norm_num)
theorem B4360517 : Blo 1613005 4360517 := bbase (se 4 (by rfl) ⟨408798, by rfl⟩ : syracuseStep 4360517 = 817597) (by norm_num)
theorem B2722133 : Blo 1613005 2722133 := bbase (se 10 (by rfl) ⟨3987, by rfl⟩ : syracuseStep 2722133 = 7975) (by norm_num)
theorem B3631445 : Blo 1613005 3631445 := bbase (se 10 (by rfl) ⟨5319, by rfl⟩ : syracuseStep 3631445 = 10639) (by norm_num)
theorem B1681817 : Blo 1613005 1681817 := bbase (se 2 (by rfl) ⟨630681, by rfl⟩ : syracuseStep 1681817 = 1261363) (by norm_num)
theorem B3631517 : Blo 1613005 3631517 := bbase (se 3 (by rfl) ⟨680909, by rfl⟩ : syracuseStep 3631517 = 1361819) (by norm_num)
theorem B2042273 : Blo 1613005 2042273 := bbase (se 2 (by rfl) ⟨765852, by rfl⟩ : syracuseStep 2042273 = 1531705) (by norm_num)
theorem B5450165 : Blo 1613005 5450165 := bbase (se 5 (by rfl) ⟨255476, by rfl⟩ : syracuseStep 5450165 = 510953) (by norm_num)
theorem B2722261 : Blo 1613005 2722261 := bbase (se 7 (by rfl) ⟨31901, by rfl⟩ : syracuseStep 2722261 = 63803) (by norm_num)
theorem B2042329 : Blo 1613005 2042329 := bbase (se 2 (by rfl) ⟨765873, by rfl⟩ : syracuseStep 2042329 = 1531747) (by norm_num)
theorem B3631589 : Blo 1613005 3631589 := bbase (se 4 (by rfl) ⟨340461, by rfl⟩ : syracuseStep 3631589 = 680923) (by norm_num)
theorem B7752181 : Blo 1613005 7752181 := bbase (se 5 (by rfl) ⟨363383, by rfl⟩ : syracuseStep 7752181 = 726767) (by norm_num)
theorem B2722349 : Blo 1613005 2722349 := bbase (se 3 (by rfl) ⟨510440, by rfl⟩ : syracuseStep 2722349 = 1020881) (by norm_num)
theorem B3631661 : Blo 1613005 3631661 := bbase (se 3 (by rfl) ⟨680936, by rfl⟩ : syracuseStep 3631661 = 1361873) (by norm_num)
theorem B1722929 : Blo 1613005 1722929 := bbase (se 2 (by rfl) ⟨646098, by rfl⟩ : syracuseStep 1722929 = 1292197) (by norm_num)
theorem B2042425 : Blo 1613005 2042425 := bbase (se 2 (by rfl) ⟨765909, by rfl⟩ : syracuseStep 2042425 = 1531819) (by norm_num)
theorem B1722989 : Blo 1613005 1722989 := bbase (se 3 (by rfl) ⟨323060, by rfl⟩ : syracuseStep 1722989 = 646121) (by norm_num)
theorem B3631733 : Blo 1613005 3631733 := bbase (se 5 (by rfl) ⟨170237, by rfl⟩ : syracuseStep 3631733 = 340475) (by norm_num)
theorem B1747597 : Blo 1613005 1747597 := bbase (se 3 (by rfl) ⟨327674, by rfl⟩ : syracuseStep 1747597 = 655349) (by norm_num)
theorem B2722477 : Blo 1613005 2722477 := bbase (se 3 (by rfl) ⟨510464, by rfl⟩ : syracuseStep 2722477 = 1020929) (by norm_num)
theorem B3631805 : Blo 1613005 3631805 := bbase (se 3 (by rfl) ⟨680963, by rfl⟩ : syracuseStep 3631805 = 1361927) (by norm_num)
theorem B6892229 : Blo 1613005 6892229 := bbase (se 4 (by rfl) ⟨646146, by rfl⟩ : syracuseStep 6892229 = 1292293) (by norm_num)
theorem B4139741 : Blo 1613005 4139741 := bbase (se 3 (by rfl) ⟨776201, by rfl⟩ : syracuseStep 4139741 = 1552403) (by norm_num)
theorem B2042597 : Blo 1613005 2042597 := bbase (se 4 (by rfl) ⟨191493, by rfl⟩ : syracuseStep 2042597 = 382987) (by norm_num)
theorem B1723117 : Blo 1613005 1723117 := bbase (se 3 (by rfl) ⟨323084, by rfl⟩ : syracuseStep 1723117 = 646169) (by norm_num)
theorem B4360949 : Blo 1613005 4360949 := bbase (se 5 (by rfl) ⟨204419, by rfl⟩ : syracuseStep 4360949 = 408839) (by norm_num)
theorem B2722565 : Blo 1613005 2722565 := bbase (se 4 (by rfl) ⟨255240, by rfl⟩ : syracuseStep 2722565 = 510481) (by norm_num)
theorem B3681029 : Blo 1613005 3681029 := bbase (se 4 (by rfl) ⟨345096, by rfl⟩ : syracuseStep 3681029 = 690193) (by norm_num)
theorem B3631877 : Blo 1613005 3631877 := bbase (se 4 (by rfl) ⟨340488, by rfl⟩ : syracuseStep 3631877 = 680977) (by norm_num)
theorem B2042653 : Blo 1613005 2042653 := bbase (se 3 (by rfl) ⟨382997, by rfl⟩ : syracuseStep 2042653 = 765995) (by norm_num)
theorem B5172005 : Blo 1613005 5172005 := bbase (se 4 (by rfl) ⟨484875, by rfl⟩ : syracuseStep 5172005 = 969751) (by norm_num)
theorem B2419517 : Blo 1613005 2419517 := bbase (se 3 (by rfl) ⟨453659, by rfl⟩ : syracuseStep 2419517 = 907319) (by norm_num)
theorem B3631949 : Blo 1613005 3631949 := bbase (se 3 (by rfl) ⟨680990, by rfl⟩ : syracuseStep 3631949 = 1361981) (by norm_num)
theorem B2419541 : Blo 1613005 2419541 := bbase (se 9 (by rfl) ⟨7088, by rfl⟩ : syracuseStep 2419541 = 14177) (by norm_num)
theorem B2296669 : Blo 1613005 2296669 := bbase (se 3 (by rfl) ⟨430625, by rfl⟩ : syracuseStep 2296669 = 861251) (by norm_num)
theorem B5450597 : Blo 1613005 5450597 := bbase (se 4 (by rfl) ⟨510993, by rfl⟩ : syracuseStep 5450597 = 1021987) (by norm_num)
theorem B2419565 : Blo 1613005 2419565 := bbase (se 3 (by rfl) ⟨453668, by rfl⟩ : syracuseStep 2419565 = 907337) (by norm_num)
theorem B2042749 : Blo 1613005 2042749 := bbase (se 3 (by rfl) ⟨383015, by rfl⟩ : syracuseStep 2042749 = 766031) (by norm_num)
theorem B2419589 : Blo 1613005 2419589 := bbase (se 4 (by rfl) ⟨226836, by rfl⟩ : syracuseStep 2419589 = 453673) (by norm_num)
theorem B2722693 : Blo 1613005 2722693 := bbase (se 4 (by rfl) ⟨255252, by rfl⟩ : syracuseStep 2722693 = 510505) (by norm_num)
theorem B3632021 : Blo 1613005 3632021 := bbase (se 6 (by rfl) ⟨85125, by rfl⟩ : syracuseStep 3632021 = 170251) (by norm_num)
theorem B2419613 : Blo 1613005 2419613 := bbase (se 3 (by rfl) ⟨453677, by rfl⟩ : syracuseStep 2419613 = 907355) (by norm_num)
theorem B2419637 : Blo 1613005 2419637 := bbase (se 5 (by rfl) ⟨113420, by rfl⟩ : syracuseStep 2419637 = 226841) (by norm_num)
theorem B3681221 : Blo 1613005 3681221 := bbase (se 4 (by rfl) ⟨345114, by rfl⟩ : syracuseStep 3681221 = 690229) (by norm_num)
theorem B2419661 : Blo 1613005 2419661 := bbase (se 3 (by rfl) ⟨453686, by rfl⟩ : syracuseStep 2419661 = 907373) (by norm_num)
theorem B19639253 : Blo 1613005 19639253 := bbase (se 7 (by rfl) ⟨230147, by rfl⟩ : syracuseStep 19639253 = 460295) (by norm_num)
theorem B2722781 : Blo 1613005 2722781 := bbase (se 3 (by rfl) ⟨510521, by rfl⟩ : syracuseStep 2722781 = 1021043) (by norm_num)
theorem B3632093 : Blo 1613005 3632093 := bbase (se 3 (by rfl) ⟨681017, by rfl⟩ : syracuseStep 3632093 = 1362035) (by norm_num)
theorem B2419685 : Blo 1613005 2419685 := bbase (se 4 (by rfl) ⟨226845, by rfl⟩ : syracuseStep 2419685 = 453691) (by norm_num)
theorem B8170469 : Blo 1613005 8170469 := bbase (se 4 (by rfl) ⟨765981, by rfl⟩ : syracuseStep 8170469 = 1531963) (by norm_num)
theorem B2419709 : Blo 1613005 2419709 := bbase (se 3 (by rfl) ⟨453695, by rfl⟩ : syracuseStep 2419709 = 907391) (by norm_num)
theorem B2419733 : Blo 1613005 2419733 := bbase (se 6 (by rfl) ⟨56712, by rfl⟩ : syracuseStep 2419733 = 113425) (by norm_num)
theorem B3632165 : Blo 1613005 3632165 := bbase (se 4 (by rfl) ⟨340515, by rfl⟩ : syracuseStep 3632165 = 681031) (by norm_num)
theorem B2042921 : Blo 1613005 2042921 := bbase (se 2 (by rfl) ⟨766095, by rfl⟩ : syracuseStep 2042921 = 1532191) (by norm_num)
theorem B2419757 : Blo 1613005 2419757 := bbase (se 3 (by rfl) ⟨453704, by rfl⟩ : syracuseStep 2419757 = 907409) (by norm_num)
theorem B2419781 : Blo 1613005 2419781 := bbase (se 4 (by rfl) ⟨226854, by rfl⟩ : syracuseStep 2419781 = 453709) (by norm_num)
theorem B4361285 : Blo 1613005 4361285 := bbase (se 4 (by rfl) ⟨408870, by rfl⟩ : syracuseStep 4361285 = 817741) (by norm_num)
theorem B2419805 : Blo 1613005 2419805 := bbase (se 3 (by rfl) ⟨453713, by rfl⟩ : syracuseStep 2419805 = 907427) (by norm_num)
theorem B2722909 : Blo 1613005 2722909 := bbase (se 3 (by rfl) ⟨510545, by rfl⟩ : syracuseStep 2722909 = 1021091) (by norm_num)
theorem B2042977 : Blo 1613005 2042977 := bbase (se 2 (by rfl) ⟨766116, by rfl⟩ : syracuseStep 2042977 = 1532233) (by norm_num)
theorem B3632237 : Blo 1613005 3632237 := bbase (se 3 (by rfl) ⟨681044, by rfl⟩ : syracuseStep 3632237 = 1362089) (by norm_num)
theorem B2419829 : Blo 1613005 2419829 := bbase (se 5 (by rfl) ⟨113429, by rfl⟩ : syracuseStep 2419829 = 226859) (by norm_num)
theorem B2419853 : Blo 1613005 2419853 := bbase (se 3 (by rfl) ⟨453722, by rfl⟩ : syracuseStep 2419853 = 907445) (by norm_num)
theorem B2419877 : Blo 1613005 2419877 := bbase (se 4 (by rfl) ⟨226863, by rfl⟩ : syracuseStep 2419877 = 453727) (by norm_num)
theorem B4361381 : Blo 1613005 4361381 := bbase (se 4 (by rfl) ⟨408879, by rfl⟩ : syracuseStep 4361381 = 817759) (by norm_num)
theorem B1723561 : Blo 1613005 1723561 := bbase (se 2 (by rfl) ⟨646335, by rfl⟩ : syracuseStep 1723561 = 1292671) (by norm_num)
theorem B2722997 : Blo 1613005 2722997 := bbase (se 5 (by rfl) ⟨127640, by rfl⟩ : syracuseStep 2722997 = 255281) (by norm_num)
theorem B3632309 : Blo 1613005 3632309 := bbase (se 5 (by rfl) ⟨170264, by rfl⟩ : syracuseStep 3632309 = 340529) (by norm_num)
theorem B2419901 : Blo 1613005 2419901 := bbase (se 3 (by rfl) ⟨453731, by rfl⟩ : syracuseStep 2419901 = 907463) (by norm_num)
theorem B2043073 : Blo 1613005 2043073 := bbase (se 2 (by rfl) ⟨766152, by rfl⟩ : syracuseStep 2043073 = 1532305) (by norm_num)
theorem B2419925 : Blo 1613005 2419925 := bbase (se 7 (by rfl) ⟨28358, by rfl⟩ : syracuseStep 2419925 = 56717) (by norm_num)
theorem B2297045 : Blo 1613005 2297045 := bbase (se 7 (by rfl) ⟨26918, by rfl⟩ : syracuseStep 2297045 = 53837) (by norm_num)
theorem B28331221 : Blo 1613005 28331221 := bbase (se 7 (by rfl) ⟨332006, by rfl⟩ : syracuseStep 28331221 = 664013) (by norm_num)
theorem B2419949 : Blo 1613005 2419949 := bbase (se 3 (by rfl) ⟨453740, by rfl⟩ : syracuseStep 2419949 = 907481) (by norm_num)
theorem B9194741 : Blo 1613005 9194741 := bbase (se 5 (by rfl) ⟨431003, by rfl⟩ : syracuseStep 9194741 = 862007) (by norm_num)
theorem B3632381 : Blo 1613005 3632381 := bbase (se 3 (by rfl) ⟨681071, by rfl⟩ : syracuseStep 3632381 = 1362143) (by norm_num)
theorem B2419973 : Blo 1613005 2419973 := bbase (se 4 (by rfl) ⟨226872, by rfl⟩ : syracuseStep 2419973 = 453745) (by norm_num)
theorem B4082957 : Blo 1613005 4082957 := bbase (se 3 (by rfl) ⟨765554, by rfl⟩ : syracuseStep 4082957 = 1531109) (by norm_num)
theorem B2419997 : Blo 1613005 2419997 := bbase (se 3 (by rfl) ⟨453749, by rfl⟩ : syracuseStep 2419997 = 907499) (by norm_num)
theorem B1723681 : Blo 1613005 1723681 := bbase (se 2 (by rfl) ⟨646380, by rfl⟩ : syracuseStep 1723681 = 1292761) (by norm_num)
theorem B2420021 : Blo 1613005 2420021 := bbase (se 5 (by rfl) ⟨113438, by rfl⟩ : syracuseStep 2420021 = 226877) (by norm_num)
theorem B2723125 : Blo 1613005 2723125 := bbase (se 5 (by rfl) ⟨127646, by rfl⟩ : syracuseStep 2723125 = 255293) (by norm_num)
theorem B6130997 : Blo 1613005 6130997 := bbase (se 5 (by rfl) ⟨287390, by rfl⟩ : syracuseStep 6130997 = 574781) (by norm_num)
theorem B3632453 : Blo 1613005 3632453 := bbase (se 4 (by rfl) ⟨340542, by rfl⟩ : syracuseStep 3632453 = 681085) (by norm_num)
theorem B2420045 : Blo 1613005 2420045 := bbase (se 3 (by rfl) ⟨453758, by rfl⟩ : syracuseStep 2420045 = 907517) (by norm_num)
theorem B2420069 : Blo 1613005 2420069 := bbase (se 4 (by rfl) ⟨226881, by rfl⟩ : syracuseStep 2420069 = 453763) (by norm_num)
theorem B2043245 : Blo 1613005 2043245 := bbase (se 3 (by rfl) ⟨383108, by rfl⟩ : syracuseStep 2043245 = 766217) (by norm_num)
theorem B2420093 : Blo 1613005 2420093 := bbase (se 3 (by rfl) ⟨453767, by rfl⟩ : syracuseStep 2420093 = 907535) (by norm_num)
theorem B6540677 : Blo 1613005 6540677 := bbase (se 4 (by rfl) ⟨613188, by rfl⟩ : syracuseStep 6540677 = 1226377) (by norm_num)
theorem B2723213 : Blo 1613005 2723213 := bbase (se 3 (by rfl) ⟨510602, by rfl⟩ : syracuseStep 2723213 = 1021205) (by norm_num)
theorem B3632525 : Blo 1613005 3632525 := bbase (se 3 (by rfl) ⟨681098, by rfl⟩ : syracuseStep 3632525 = 1362197) (by norm_num)
theorem B2420117 : Blo 1613005 2420117 := bbase (se 6 (by rfl) ⟨56721, by rfl⟩ : syracuseStep 2420117 = 113443) (by norm_num)
theorem B2043301 : Blo 1613005 2043301 := bbase (se 4 (by rfl) ⟨191559, by rfl⟩ : syracuseStep 2043301 = 383119) (by norm_num)
theorem B2420141 : Blo 1613005 2420141 := bbase (se 3 (by rfl) ⟨453776, by rfl⟩ : syracuseStep 2420141 = 907553) (by norm_num)
theorem B2420165 : Blo 1613005 2420165 := bbase (se 4 (by rfl) ⟨226890, by rfl⟩ : syracuseStep 2420165 = 453781) (by norm_num)
theorem B4083149 : Blo 1613005 4083149 := bbase (se 3 (by rfl) ⟨765590, by rfl⟩ : syracuseStep 4083149 = 1531181) (by norm_num)
theorem B3632597 : Blo 1613005 3632597 := bbase (se 7 (by rfl) ⟨42569, by rfl⟩ : syracuseStep 3632597 = 85139) (by norm_num)
theorem B2420189 : Blo 1613005 2420189 := bbase (se 3 (by rfl) ⟨453785, by rfl⟩ : syracuseStep 2420189 = 907571) (by norm_num)
theorem B2420213 : Blo 1613005 2420213 := bbase (se 5 (by rfl) ⟨113447, by rfl⟩ : syracuseStep 2420213 = 226895) (by norm_num)
theorem B8277509 : Blo 1613005 8277509 := bbase (se 4 (by rfl) ⟨776016, by rfl⟩ : syracuseStep 8277509 = 1552033) (by norm_num)
theorem B2043397 : Blo 1613005 2043397 := bbase (se 4 (by rfl) ⟨191568, by rfl⟩ : syracuseStep 2043397 = 383137) (by norm_num)
theorem B2420237 : Blo 1613005 2420237 := bbase (se 3 (by rfl) ⟨453794, by rfl⟩ : syracuseStep 2420237 = 907589) (by norm_num)
theorem B2723341 : Blo 1613005 2723341 := bbase (se 3 (by rfl) ⟨510626, by rfl⟩ : syracuseStep 2723341 = 1021253) (by norm_num)
theorem B1723933 : Blo 1613005 1723933 := bbase (se 3 (by rfl) ⟨323237, by rfl⟩ : syracuseStep 1723933 = 646475) (by norm_num)
theorem B3632669 : Blo 1613005 3632669 := bbase (se 3 (by rfl) ⟨681125, by rfl⟩ : syracuseStep 3632669 = 1362251) (by norm_num)
theorem B1723937 : Blo 1613005 1723937 := bbase (se 2 (by rfl) ⟨646476, by rfl⟩ : syracuseStep 1723937 = 1292953) (by norm_num)
theorem B2420261 : Blo 1613005 2420261 := bbase (se 4 (by rfl) ⟨226899, by rfl⟩ : syracuseStep 2420261 = 453799) (by norm_num)
theorem B2420285 : Blo 1613005 2420285 := bbase (se 3 (by rfl) ⟨453803, by rfl⟩ : syracuseStep 2420285 = 907607) (by norm_num)
theorem B2420309 : Blo 1613005 2420309 := bbase (se 8 (by rfl) ⟨14181, by rfl⟩ : syracuseStep 2420309 = 28363) (by norm_num)
theorem B6131285 : Blo 1613005 6131285 := bbase (se 8 (by rfl) ⟨35925, by rfl⟩ : syracuseStep 6131285 = 71851) (by norm_num)
theorem B2723429 : Blo 1613005 2723429 := bbase (se 4 (by rfl) ⟨255321, by rfl⟩ : syracuseStep 2723429 = 510643) (by norm_num)
theorem B3632741 : Blo 1613005 3632741 := bbase (se 4 (by rfl) ⟨340569, by rfl⟩ : syracuseStep 3632741 = 681139) (by norm_num)
theorem B2420333 : Blo 1613005 2420333 := bbase (se 3 (by rfl) ⟨453812, by rfl⟩ : syracuseStep 2420333 = 907625) (by norm_num)
theorem B2420357 : Blo 1613005 2420357 := bbase (se 4 (by rfl) ⟨226908, by rfl⟩ : syracuseStep 2420357 = 453817) (by norm_num)
theorem B3272333 : Blo 1613005 3272333 := bbase (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) (by norm_num)
theorem B2420381 : Blo 1613005 2420381 := bbase (se 3 (by rfl) ⟨453821, by rfl⟩ : syracuseStep 2420381 = 907643) (by norm_num)
theorem B3632813 : Blo 1613005 3632813 := bbase (se 3 (by rfl) ⟨681152, by rfl⟩ : syracuseStep 3632813 = 1362305) (by norm_num)
theorem B2043569 : Blo 1613005 2043569 := bbase (se 2 (by rfl) ⟨766338, by rfl⟩ : syracuseStep 2043569 = 1532677) (by norm_num)
theorem B2420405 : Blo 1613005 2420405 := bbase (se 5 (by rfl) ⟨113456, by rfl⟩ : syracuseStep 2420405 = 226913) (by norm_num)
theorem B2330309 : Blo 1613005 2330309 := bbase (se 4 (by rfl) ⟨218466, by rfl⟩ : syracuseStep 2330309 = 436933) (by norm_num)
theorem B2420429 : Blo 1613005 2420429 := bbase (se 3 (by rfl) ⟨453830, by rfl⟩ : syracuseStep 2420429 = 907661) (by norm_num)
theorem B27578069 : Blo 1613005 27578069 := bbase (se 7 (by rfl) ⟨323180, by rfl⟩ : syracuseStep 27578069 = 646361) (by norm_num)
theorem B2420453 : Blo 1613005 2420453 := bbase (se 4 (by rfl) ⟨226917, by rfl⟩ : syracuseStep 2420453 = 453835) (by norm_num)
theorem B2723557 : Blo 1613005 2723557 := bbase (se 4 (by rfl) ⟨255333, by rfl⟩ : syracuseStep 2723557 = 510667) (by norm_num)
theorem B2043625 : Blo 1613005 2043625 := bbase (se 2 (by rfl) ⟨766359, by rfl⟩ : syracuseStep 2043625 = 1532719) (by norm_num)
theorem B3632885 : Blo 1613005 3632885 := bbase (se 5 (by rfl) ⟨170291, by rfl⟩ : syracuseStep 3632885 = 340583) (by norm_num)
theorem B2420477 : Blo 1613005 2420477 := bbase (se 3 (by rfl) ⟨453839, by rfl⟩ : syracuseStep 2420477 = 907679) (by norm_num)
theorem B2420501 : Blo 1613005 2420501 := bbase (se 6 (by rfl) ⟨56730, by rfl⟩ : syracuseStep 2420501 = 113461) (by norm_num)
theorem B4083493 : Blo 1613005 4083493 := bbase (se 4 (by rfl) ⟨382827, by rfl⟩ : syracuseStep 4083493 = 765655) (by norm_num)
theorem B2420525 : Blo 1613005 2420525 := bbase (se 3 (by rfl) ⟨453848, by rfl⟩ : syracuseStep 2420525 = 907697) (by norm_num)
theorem B2584381 : Blo 1613005 2584381 := bbase (se 3 (by rfl) ⟨484571, by rfl⟩ : syracuseStep 2584381 = 969143) (by norm_num)
theorem B2723645 : Blo 1613005 2723645 := bbase (se 3 (by rfl) ⟨510683, by rfl⟩ : syracuseStep 2723645 = 1021367) (by norm_num)
theorem B3632957 : Blo 1613005 3632957 := bbase (se 3 (by rfl) ⟨681179, by rfl⟩ : syracuseStep 3632957 = 1362359) (by norm_num)
theorem B2420549 : Blo 1613005 2420549 := bbase (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) (by norm_num)
theorem B3878725 : Blo 1613005 3878725 := bbase (se 4 (by rfl) ⟨363630, by rfl⟩ : syracuseStep 3878725 = 727261) (by norm_num)
theorem B2043721 : Blo 1613005 2043721 := bbase (se 2 (by rfl) ⟨766395, by rfl⟩ : syracuseStep 2043721 = 1532791) (by norm_num)
theorem B2420573 : Blo 1613005 2420573 := bbase (se 3 (by rfl) ⟨453857, by rfl⟩ : syracuseStep 2420573 = 907715) (by norm_num)
theorem B2420597 : Blo 1613005 2420597 := bbase (se 5 (by rfl) ⟨113465, by rfl⟩ : syracuseStep 2420597 = 226931) (by norm_num)
theorem B3633029 : Blo 1613005 3633029 := bbase (se 4 (by rfl) ⟨340596, by rfl⟩ : syracuseStep 3633029 = 681193) (by norm_num)
theorem B2420621 : Blo 1613005 2420621 := bbase (se 3 (by rfl) ⟨453866, by rfl⟩ : syracuseStep 2420621 = 907733) (by norm_num)
theorem B4083605 : Blo 1613005 4083605 := bbase (se 6 (by rfl) ⟨95709, by rfl⟩ : syracuseStep 4083605 = 191419) (by norm_num)
theorem B18386837 : Blo 1613005 18386837 := bbase (se 6 (by rfl) ⟨430941, by rfl⟩ : syracuseStep 18386837 = 861883) (by norm_num)
theorem B2420645 : Blo 1613005 2420645 := bbase (se 4 (by rfl) ⟨226935, by rfl⟩ : syracuseStep 2420645 = 453871) (by norm_num)
theorem B2420669 : Blo 1613005 2420669 := bbase (se 3 (by rfl) ⟨453875, by rfl⟩ : syracuseStep 2420669 = 907751) (by norm_num)
theorem B2723773 : Blo 1613005 2723773 := bbase (se 3 (by rfl) ⟨510707, by rfl⟩ : syracuseStep 2723773 = 1021415) (by norm_num)
theorem B3633101 : Blo 1613005 3633101 := bbase (se 3 (by rfl) ⟨681206, by rfl⟩ : syracuseStep 3633101 = 1362413) (by norm_num)
theorem B2420693 : Blo 1613005 2420693 := bbase (se 7 (by rfl) ⟨28367, by rfl⟩ : syracuseStep 2420693 = 56735) (by norm_num)
theorem B11636693 : Blo 1613005 11636693 := bbase (se 7 (by rfl) ⟨136367, by rfl⟩ : syracuseStep 11636693 = 272735) (by norm_num)
theorem B2420717 : Blo 1613005 2420717 := bbase (se 3 (by rfl) ⟨453884, by rfl⟩ : syracuseStep 2420717 = 907769) (by norm_num)
theorem B2043893 : Blo 1613005 2043893 := bbase (se 5 (by rfl) ⟨95807, by rfl⟩ : syracuseStep 2043893 = 191615) (by norm_num)
theorem B2420741 : Blo 1613005 2420741 := bbase (se 4 (by rfl) ⟨226944, by rfl⟩ : syracuseStep 2420741 = 453889) (by norm_num)
theorem B2723861 : Blo 1613005 2723861 := bbase (se 6 (by rfl) ⟨63840, by rfl⟩ : syracuseStep 2723861 = 127681) (by norm_num)
theorem B12259349 : Blo 1613005 12259349 := bbase (se 6 (by rfl) ⟨287328, by rfl⟩ : syracuseStep 12259349 = 574657) (by norm_num)
theorem B3633173 : Blo 1613005 3633173 := bbase (se 6 (by rfl) ⟨85152, by rfl⟩ : syracuseStep 3633173 = 170305) (by norm_num)
theorem B2420765 : Blo 1613005 2420765 := bbase (se 3 (by rfl) ⟨453893, by rfl⟩ : syracuseStep 2420765 = 907787) (by norm_num)
theorem B2043949 : Blo 1613005 2043949 := bbase (se 3 (by rfl) ⟨383240, by rfl⟩ : syracuseStep 2043949 = 766481) (by norm_num)
theorem B2420789 : Blo 1613005 2420789 := bbase (se 5 (by rfl) ⟨113474, by rfl⟩ : syracuseStep 2420789 = 226949) (by norm_num)
theorem B2330677 : Blo 1613005 2330677 := bbase (se 5 (by rfl) ⟨109250, by rfl⟩ : syracuseStep 2330677 = 218501) (by norm_num)
theorem B2420813 : Blo 1613005 2420813 := bbase (se 3 (by rfl) ⟨453902, by rfl⟩ : syracuseStep 2420813 = 907805) (by norm_num)
theorem B4083797 : Blo 1613005 4083797 := bbase (se 8 (by rfl) ⟨23928, by rfl⟩ : syracuseStep 4083797 = 47857) (by norm_num)
theorem B1724501 : Blo 1613005 1724501 := bbase (se 8 (by rfl) ⟨10104, by rfl⟩ : syracuseStep 1724501 = 20209) (by norm_num)
theorem B3682397 : Blo 1613005 3682397 := bbase (se 3 (by rfl) ⟨690449, by rfl⟩ : syracuseStep 3682397 = 1380899) (by norm_num)
theorem B3633245 : Blo 1613005 3633245 := bbase (se 3 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 3633245 = 1362467) (by norm_num)
theorem B2420837 : Blo 1613005 2420837 := bbase (se 4 (by rfl) ⟨226953, by rfl⟩ : syracuseStep 2420837 = 453907) (by norm_num)
theorem B2420861 : Blo 1613005 2420861 := bbase (se 3 (by rfl) ⟨453911, by rfl⟩ : syracuseStep 2420861 = 907823) (by norm_num)
theorem B1814665 : Blo 1613005 1814665 := bbase (se 2 (by rfl) ⟨680499, by rfl⟩ : syracuseStep 1814665 = 1360999) (by norm_num)
theorem B2420885 : Blo 1613005 2420885 := bbase (se 6 (by rfl) ⟨56739, by rfl⟩ : syracuseStep 2420885 = 113479) (by norm_num)
theorem B2723989 : Blo 1613005 2723989 := bbase (se 6 (by rfl) ⟨63843, by rfl⟩ : syracuseStep 2723989 = 127687) (by norm_num)
theorem B3633317 : Blo 1613005 3633317 := bbase (se 4 (by rfl) ⟨340623, by rfl⟩ : syracuseStep 3633317 = 681247) (by norm_num)
theorem B1814701 : Blo 1613005 1814701 := bbase (se 3 (by rfl) ⟨340256, by rfl⟩ : syracuseStep 1814701 = 680513) (by norm_num)
theorem B2420909 : Blo 1613005 2420909 := bbase (se 3 (by rfl) ⟨453920, by rfl⟩ : syracuseStep 2420909 = 907841) (by norm_num)
theorem B2420933 : Blo 1613005 2420933 := bbase (se 4 (by rfl) ⟨226962, by rfl⟩ : syracuseStep 2420933 = 453925) (by norm_num)
theorem B2330821 : Blo 1613005 2330821 := bbase (se 4 (by rfl) ⟨218514, by rfl⟩ : syracuseStep 2330821 = 437029) (by norm_num)
theorem B1814737 : Blo 1613005 1814737 := bbase (se 2 (by rfl) ⟨680526, by rfl⟩ : syracuseStep 1814737 = 1361053) (by norm_num)
theorem B2420957 : Blo 1613005 2420957 := bbase (se 3 (by rfl) ⟨453929, by rfl⟩ : syracuseStep 2420957 = 907859) (by norm_num)
theorem B2724077 : Blo 1613005 2724077 := bbase (se 3 (by rfl) ⟨510764, by rfl⟩ : syracuseStep 2724077 = 1021529) (by norm_num)
theorem B3633389 : Blo 1613005 3633389 := bbase (se 3 (by rfl) ⟨681260, by rfl⟩ : syracuseStep 3633389 = 1362521) (by norm_num)
theorem B1814773 : Blo 1613005 1814773 := bbase (se 5 (by rfl) ⟨85067, by rfl⟩ : syracuseStep 1814773 = 170135) (by norm_num)
theorem B2420981 : Blo 1613005 2420981 := bbase (se 5 (by rfl) ⟨113483, by rfl⟩ : syracuseStep 2420981 = 226967) (by norm_num)
theorem B8171765 : Blo 1613005 8171765 := bbase (se 5 (by rfl) ⟨383051, by rfl⟩ : syracuseStep 8171765 = 766103) (by norm_num)
theorem B2584829 : Blo 1613005 2584829 := bbase (se 3 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 2584829 = 969311) (by norm_num)
theorem B2421005 : Blo 1613005 2421005 := bbase (se 3 (by rfl) ⟨453938, by rfl⟩ : syracuseStep 2421005 = 907877) (by norm_num)
theorem B1814809 : Blo 1613005 1814809 := bbase (se 2 (by rfl) ⟨680553, by rfl⟩ : syracuseStep 1814809 = 1361107) (by norm_num)
theorem B3445021 : Blo 1613005 3445021 := bbase (se 3 (by rfl) ⟨645941, by rfl⟩ : syracuseStep 3445021 = 1291883) (by norm_num)
theorem B2421029 : Blo 1613005 2421029 := bbase (se 4 (by rfl) ⟨226971, by rfl⟩ : syracuseStep 2421029 = 453943) (by norm_num)
theorem B3633461 : Blo 1613005 3633461 := bbase (se 5 (by rfl) ⟨170318, by rfl⟩ : syracuseStep 3633461 = 340637) (by norm_num)
theorem B1814845 : Blo 1613005 1814845 := bbase (se 3 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 1814845 = 680567) (by norm_num)
theorem B2421053 : Blo 1613005 2421053 := bbase (se 3 (by rfl) ⟨453947, by rfl⟩ : syracuseStep 2421053 = 907895) (by norm_num)
theorem B2421077 : Blo 1613005 2421077 := bbase (se 10 (by rfl) ⟨3546, by rfl⟩ : syracuseStep 2421077 = 7093) (by norm_num)
theorem B1814881 : Blo 1613005 1814881 := bbase (se 2 (by rfl) ⟨680580, by rfl⟩ : syracuseStep 1814881 = 1361161) (by norm_num)
theorem B2421101 : Blo 1613005 2421101 := bbase (se 3 (by rfl) ⟨453956, by rfl⟩ : syracuseStep 2421101 = 907913) (by norm_num)
theorem B2724205 : Blo 1613005 2724205 := bbase (se 3 (by rfl) ⟨510788, by rfl⟩ : syracuseStep 2724205 = 1021577) (by norm_num)
theorem B3633533 : Blo 1613005 3633533 := bbase (se 3 (by rfl) ⟨681287, by rfl⟩ : syracuseStep 3633533 = 1362575) (by norm_num)
theorem B1814917 : Blo 1613005 1814917 := bbase (se 4 (by rfl) ⟨170148, by rfl⟩ : syracuseStep 1814917 = 340297) (by norm_num)
theorem B2421125 : Blo 1613005 2421125 := bbase (se 4 (by rfl) ⟨226980, by rfl⟩ : syracuseStep 2421125 = 453961) (by norm_num)
theorem B2421149 : Blo 1613005 2421149 := bbase (se 3 (by rfl) ⟨453965, by rfl⟩ : syracuseStep 2421149 = 907931) (by norm_num)
theorem B1814953 : Blo 1613005 1814953 := bbase (se 2 (by rfl) ⟨680607, by rfl⟩ : syracuseStep 1814953 = 1361215) (by norm_num)
theorem B4084141 : Blo 1613005 4084141 := bbase (se 3 (by rfl) ⟨765776, by rfl⟩ : syracuseStep 4084141 = 1531553) (by norm_num)
theorem B12251573 : Blo 1613005 12251573 := bbase (se 5 (by rfl) ⟨574292, by rfl⟩ : syracuseStep 12251573 = 1148585) (by norm_num)
theorem B2421173 : Blo 1613005 2421173 := bbase (se 5 (by rfl) ⟨113492, by rfl⟩ : syracuseStep 2421173 = 226985) (by norm_num)
theorem B1937849 : Blo 1613005 1937849 := bbase (se 2 (by rfl) ⟨726693, by rfl⟩ : syracuseStep 1937849 = 1453387) (by norm_num)
theorem B2585029 : Blo 1613005 2585029 := bbase (se 4 (by rfl) ⟨242346, by rfl⟩ : syracuseStep 2585029 = 484693) (by norm_num)
theorem B2724293 : Blo 1613005 2724293 := bbase (se 4 (by rfl) ⟨255402, by rfl⟩ : syracuseStep 2724293 = 510805) (by norm_num)
theorem B3633605 : Blo 1613005 3633605 := bbase (se 4 (by rfl) ⟨340650, by rfl⟩ : syracuseStep 3633605 = 681301) (by norm_num)
theorem B1814989 : Blo 1613005 1814989 := bbase (se 3 (by rfl) ⟨340310, by rfl⟩ : syracuseStep 1814989 = 680621) (by norm_num)
theorem B2421197 : Blo 1613005 2421197 := bbase (se 3 (by rfl) ⟨453974, by rfl⟩ : syracuseStep 2421197 = 907949) (by norm_num)
theorem B3879389 : Blo 1613005 3879389 := bbase (se 3 (by rfl) ⟨727385, by rfl⟩ : syracuseStep 3879389 = 1454771) (by norm_num)
theorem B2421221 : Blo 1613005 2421221 := bbase (se 4 (by rfl) ⟨226989, by rfl⟩ : syracuseStep 2421221 = 453979) (by norm_num)
theorem B1815025 : Blo 1613005 1815025 := bbase (se 2 (by rfl) ⟨680634, by rfl⟩ : syracuseStep 1815025 = 1361269) (by norm_num)
theorem B2421245 : Blo 1613005 2421245 := bbase (se 3 (by rfl) ⟨453983, by rfl⟩ : syracuseStep 2421245 = 907967) (by norm_num)
theorem B3633677 : Blo 1613005 3633677 := bbase (se 3 (by rfl) ⟨681314, by rfl⟩ : syracuseStep 3633677 = 1362629) (by norm_num)
theorem B5444117 : Blo 1613005 5444117 := bbase (se 6 (by rfl) ⟨127596, by rfl⟩ : syracuseStep 5444117 = 255193) (by norm_num)
theorem B1815061 : Blo 1613005 1815061 := bbase (se 6 (by rfl) ⟨42540, by rfl⟩ : syracuseStep 1815061 = 85081) (by norm_num)
theorem B2421269 : Blo 1613005 2421269 := bbase (se 6 (by rfl) ⟨56748, by rfl⟩ : syracuseStep 2421269 = 113497) (by norm_num)
theorem B4084253 : Blo 1613005 4084253 := bbase (se 3 (by rfl) ⟨765797, by rfl⟩ : syracuseStep 4084253 = 1531595) (by norm_num)
theorem B2421293 : Blo 1613005 2421293 := bbase (se 3 (by rfl) ⟨453992, by rfl⟩ : syracuseStep 2421293 = 907985) (by norm_num)
theorem B1815097 : Blo 1613005 1815097 := bbase (se 2 (by rfl) ⟨680661, by rfl⟩ : syracuseStep 1815097 = 1361323) (by norm_num)
theorem B2421317 : Blo 1613005 2421317 := bbase (se 4 (by rfl) ⟨226998, by rfl⟩ : syracuseStep 2421317 = 453997) (by norm_num)
theorem B2724421 : Blo 1613005 2724421 := bbase (se 4 (by rfl) ⟨255414, by rfl⟩ : syracuseStep 2724421 = 510829) (by norm_num)
theorem B3633749 : Blo 1613005 3633749 := bbase (se 8 (by rfl) ⟨21291, by rfl⟩ : syracuseStep 3633749 = 42583) (by norm_num)
theorem B1815133 : Blo 1613005 1815133 := bbase (se 3 (by rfl) ⟨340337, by rfl⟩ : syracuseStep 1815133 = 680675) (by norm_num)
theorem B2421341 : Blo 1613005 2421341 := bbase (se 3 (by rfl) ⟨454001, by rfl⟩ : syracuseStep 2421341 = 908003) (by norm_num)
theorem B2298469 : Blo 1613005 2298469 := bbase (se 4 (by rfl) ⟨215481, by rfl⟩ : syracuseStep 2298469 = 430963) (by norm_num)
theorem B1839721 : Blo 1613005 1839721 := bbase (se 2 (by rfl) ⟨689895, by rfl⟩ : syracuseStep 1839721 = 1379791) (by norm_num)
theorem B2421365 : Blo 1613005 2421365 := bbase (se 5 (by rfl) ⟨113501, by rfl⟩ : syracuseStep 2421365 = 227003) (by norm_num)
theorem B1815169 : Blo 1613005 1815169 := bbase (se 2 (by rfl) ⟨680688, by rfl⟩ : syracuseStep 1815169 = 1361377) (by norm_num)
theorem B2421389 : Blo 1613005 2421389 := bbase (se 3 (by rfl) ⟨454010, by rfl⟩ : syracuseStep 2421389 = 908021) (by norm_num)
theorem B2724509 : Blo 1613005 2724509 := bbase (se 3 (by rfl) ⟨510845, by rfl⟩ : syracuseStep 2724509 = 1021691) (by norm_num)
theorem B1815205 : Blo 1613005 1815205 := bbase (se 4 (by rfl) ⟨170175, by rfl⟩ : syracuseStep 1815205 = 340351) (by norm_num)
theorem B2421413 : Blo 1613005 2421413 := bbase (se 4 (by rfl) ⟨227007, by rfl⟩ : syracuseStep 2421413 = 454015) (by norm_num)
theorem B3273389 : Blo 1613005 3273389 := bbase (se 3 (by rfl) ⟨613760, by rfl⟩ : syracuseStep 3273389 = 1227521) (by norm_num)
theorem B2421437 : Blo 1613005 2421437 := bbase (se 3 (by rfl) ⟨454019, by rfl⟩ : syracuseStep 2421437 = 908039) (by norm_num)
theorem B2585285 : Blo 1613005 2585285 := bbase (se 4 (by rfl) ⟨242370, by rfl⟩ : syracuseStep 2585285 = 484741) (by norm_num)
theorem B1815241 : Blo 1613005 1815241 := bbase (se 2 (by rfl) ⟨680715, by rfl⟩ : syracuseStep 1815241 = 1361431) (by norm_num)
theorem B2421461 : Blo 1613005 2421461 := bbase (se 7 (by rfl) ⟨28376, by rfl⟩ : syracuseStep 2421461 = 56753) (by norm_num)
theorem B4084445 : Blo 1613005 4084445 := bbase (se 3 (by rfl) ⟨765833, by rfl⟩ : syracuseStep 4084445 = 1531667) (by norm_num)
theorem B1815277 : Blo 1613005 1815277 := bbase (se 3 (by rfl) ⟨340364, by rfl⟩ : syracuseStep 1815277 = 680729) (by norm_num)
theorem B2421485 : Blo 1613005 2421485 := bbase (se 3 (by rfl) ⟨454028, by rfl⟩ : syracuseStep 2421485 = 908057) (by norm_num)
theorem B2421509 : Blo 1613005 2421509 := bbase (se 4 (by rfl) ⟨227016, by rfl⟩ : syracuseStep 2421509 = 454033) (by norm_num)
theorem B3445517 : Blo 1613005 3445517 := bbase (se 3 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 3445517 = 1292069) (by norm_num)
theorem B1815313 : Blo 1613005 1815313 := bbase (se 2 (by rfl) ⟨680742, by rfl⟩ : syracuseStep 1815313 = 1361485) (by norm_num)
theorem B2421533 : Blo 1613005 2421533 := bbase (se 3 (by rfl) ⟨454037, by rfl⟩ : syracuseStep 2421533 = 908075) (by norm_num)
theorem B2724637 : Blo 1613005 2724637 := bbase (se 3 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 2724637 = 1021739) (by norm_num)
theorem B1635113 : Blo 1613005 1635113 := bbase (se 2 (by rfl) ⟨613167, by rfl⟩ : syracuseStep 1635113 = 1226335) (by norm_num)
theorem B1815349 : Blo 1613005 1815349 := bbase (se 5 (by rfl) ⟨85094, by rfl⟩ : syracuseStep 1815349 = 170189) (by norm_num)
theorem B2421557 : Blo 1613005 2421557 := bbase (se 5 (by rfl) ⟨113510, by rfl⟩ : syracuseStep 2421557 = 227021) (by norm_num)
theorem B2421581 : Blo 1613005 2421581 := bbase (se 3 (by rfl) ⟨454046, by rfl⟩ : syracuseStep 2421581 = 908093) (by norm_num)
theorem B1815385 : Blo 1613005 1815385 := bbase (se 2 (by rfl) ⟨680769, by rfl⟩ : syracuseStep 1815385 = 1361539) (by norm_num)
theorem B2421605 : Blo 1613005 2421605 := bbase (se 4 (by rfl) ⟨227025, by rfl⟩ : syracuseStep 2421605 = 454051) (by norm_num)
theorem B2069357 : Blo 1613005 2069357 := bbase (se 3 (by rfl) ⟨388004, by rfl⟩ : syracuseStep 2069357 = 776009) (by norm_num)
theorem B2724725 : Blo 1613005 2724725 := bbase (se 5 (by rfl) ⟨127721, by rfl⟩ : syracuseStep 2724725 = 255443) (by norm_num)
theorem B1815421 : Blo 1613005 1815421 := bbase (se 3 (by rfl) ⟨340391, by rfl⟩ : syracuseStep 1815421 = 680783) (by norm_num)
theorem B2421629 : Blo 1613005 2421629 := bbase (se 3 (by rfl) ⟨454055, by rfl⟩ : syracuseStep 2421629 = 908111) (by norm_num)
theorem B2421653 : Blo 1613005 2421653 := bbase (se 6 (by rfl) ⟨56757, by rfl⟩ : syracuseStep 2421653 = 113515) (by norm_num)
theorem B1815457 : Blo 1613005 1815457 := bbase (se 2 (by rfl) ⟨680796, by rfl⟩ : syracuseStep 1815457 = 1361593) (by norm_num)
theorem B2421677 : Blo 1613005 2421677 := bbase (se 3 (by rfl) ⟨454064, by rfl⟩ : syracuseStep 2421677 = 908129) (by norm_num)
theorem B5444549 : Blo 1613005 5444549 := bbase (se 4 (by rfl) ⟨510426, by rfl⟩ : syracuseStep 5444549 = 1020853) (by norm_num)
theorem B1815493 : Blo 1613005 1815493 := bbase (se 4 (by rfl) ⟨170202, by rfl⟩ : syracuseStep 1815493 = 340405) (by norm_num)
theorem B2421701 : Blo 1613005 2421701 := bbase (se 4 (by rfl) ⟨227034, by rfl⟩ : syracuseStep 2421701 = 454069) (by norm_num)
theorem B2421725 : Blo 1613005 2421725 := bbase (se 3 (by rfl) ⟨454073, by rfl⟩ : syracuseStep 2421725 = 908147) (by norm_num)
theorem B1815529 : Blo 1613005 1815529 := bbase (se 2 (by rfl) ⟨680823, by rfl⟩ : syracuseStep 1815529 = 1361647) (by norm_num)
theorem B2421749 : Blo 1613005 2421749 := bbase (se 5 (by rfl) ⟨113519, by rfl⟩ : syracuseStep 2421749 = 227039) (by norm_num)
theorem B2724853 : Blo 1613005 2724853 := bbase (se 5 (by rfl) ⟨127727, by rfl⟩ : syracuseStep 2724853 = 255455) (by norm_num)
theorem B1815565 : Blo 1613005 1815565 := bbase (se 3 (by rfl) ⟨340418, by rfl⟩ : syracuseStep 1815565 = 680837) (by norm_num)
theorem B2421773 : Blo 1613005 2421773 := bbase (se 3 (by rfl) ⟨454082, by rfl⟩ : syracuseStep 2421773 = 908165) (by norm_num)
theorem B1938449 : Blo 1613005 1938449 := bbase (se 2 (by rfl) ⟨726918, by rfl⟩ : syracuseStep 1938449 = 1453837) (by norm_num)
theorem B2421797 : Blo 1613005 2421797 := bbase (se 4 (by rfl) ⟨227043, by rfl⟩ : syracuseStep 2421797 = 454087) (by norm_num)
theorem B1815601 : Blo 1613005 1815601 := bbase (se 2 (by rfl) ⟨680850, by rfl⟩ : syracuseStep 1815601 = 1361701) (by norm_num)
theorem B4084789 : Blo 1613005 4084789 := bbase (se 5 (by rfl) ⟨191474, by rfl⟩ : syracuseStep 4084789 = 382949) (by norm_num)
theorem B2421821 : Blo 1613005 2421821 := bbase (se 3 (by rfl) ⟨454091, by rfl⟩ : syracuseStep 2421821 = 908183) (by norm_num)
theorem B2724941 : Blo 1613005 2724941 := bbase (se 3 (by rfl) ⟨510926, by rfl⟩ : syracuseStep 2724941 = 1021853) (by norm_num)
theorem B1815637 : Blo 1613005 1815637 := bbase (se 8 (by rfl) ⟨10638, by rfl⟩ : syracuseStep 1815637 = 21277) (by norm_num)
theorem B2421845 : Blo 1613005 2421845 := bbase (se 8 (by rfl) ⟨14190, by rfl⟩ : syracuseStep 2421845 = 28381) (by norm_num)
theorem B2421869 : Blo 1613005 2421869 := bbase (se 3 (by rfl) ⟨454100, by rfl⟩ : syracuseStep 2421869 = 908201) (by norm_num)
theorem B1815673 : Blo 1613005 1815673 := bbase (se 2 (by rfl) ⟨680877, by rfl⟩ : syracuseStep 1815673 = 1361755) (by norm_num)
theorem B2421893 : Blo 1613005 2421893 := bbase (se 4 (by rfl) ⟨227052, by rfl⟩ : syracuseStep 2421893 = 454105) (by norm_num)
theorem B6124693 : Blo 1613005 6124693 := bbase (se 6 (by rfl) ⟨143547, by rfl⟩ : syracuseStep 6124693 = 287095) (by norm_num)
theorem B1815709 : Blo 1613005 1815709 := bbase (se 3 (by rfl) ⟨340445, by rfl⟩ : syracuseStep 1815709 = 680891) (by norm_num)
theorem B2421917 : Blo 1613005 2421917 := bbase (se 3 (by rfl) ⟨454109, by rfl⟩ : syracuseStep 2421917 = 908219) (by norm_num)
theorem B4084901 : Blo 1613005 4084901 := bbase (se 4 (by rfl) ⟨382959, by rfl⟩ : syracuseStep 4084901 = 765919) (by norm_num)
theorem B2421941 : Blo 1613005 2421941 := bbase (se 5 (by rfl) ⟨113528, by rfl⟩ : syracuseStep 2421941 = 227057) (by norm_num)
theorem B2299061 : Blo 1613005 2299061 := bbase (se 5 (by rfl) ⟨107768, by rfl⟩ : syracuseStep 2299061 = 215537) (by norm_num)
theorem B1815745 : Blo 1613005 1815745 := bbase (se 2 (by rfl) ⟨680904, by rfl⟩ : syracuseStep 1815745 = 1361809) (by norm_num)
theorem B2421965 : Blo 1613005 2421965 := bbase (se 3 (by rfl) ⟨454118, by rfl⟩ : syracuseStep 2421965 = 908237) (by norm_num)
theorem B2725069 : Blo 1613005 2725069 := bbase (se 3 (by rfl) ⟨510950, by rfl⟩ : syracuseStep 2725069 = 1021901) (by norm_num)
theorem B1815781 : Blo 1613005 1815781 := bbase (se 4 (by rfl) ⟨170229, by rfl⟩ : syracuseStep 1815781 = 340459) (by norm_num)
theorem B2421989 : Blo 1613005 2421989 := bbase (se 4 (by rfl) ⟨227061, by rfl⟩ : syracuseStep 2421989 = 454123) (by norm_num)
theorem B2422013 : Blo 1613005 2422013 := bbase (se 3 (by rfl) ⟨454127, by rfl⟩ : syracuseStep 2422013 = 908255) (by norm_num)
theorem B2299141 : Blo 1613005 2299141 := bbase (se 4 (by rfl) ⟨215544, by rfl⟩ : syracuseStep 2299141 = 431089) (by norm_num)
theorem B1815817 : Blo 1613005 1815817 := bbase (se 2 (by rfl) ⟨680931, by rfl⟩ : syracuseStep 1815817 = 1361863) (by norm_num)
theorem B2422037 : Blo 1613005 2422037 := bbase (se 6 (by rfl) ⟨56766, by rfl⟩ : syracuseStep 2422037 = 113533) (by norm_num)
theorem B2725157 : Blo 1613005 2725157 := bbase (se 4 (by rfl) ⟨255483, by rfl⟩ : syracuseStep 2725157 = 510967) (by norm_num)
theorem B1815853 : Blo 1613005 1815853 := bbase (se 3 (by rfl) ⟨340472, by rfl⟩ : syracuseStep 1815853 = 680945) (by norm_num)
theorem B2422061 : Blo 1613005 2422061 := bbase (se 3 (by rfl) ⟨454136, by rfl⟩ : syracuseStep 2422061 = 908273) (by norm_num)
theorem B1938757 : Blo 1613005 1938757 := bbase (se 4 (by rfl) ⟨181758, by rfl⟩ : syracuseStep 1938757 = 363517) (by norm_num)
theorem B2422085 : Blo 1613005 2422085 := bbase (se 4 (by rfl) ⟨227070, by rfl⟩ : syracuseStep 2422085 = 454141) (by norm_num)
theorem B1815889 : Blo 1613005 1815889 := bbase (se 2 (by rfl) ⟨680958, by rfl⟩ : syracuseStep 1815889 = 1361917) (by norm_num)
theorem B2692445 : Blo 1613005 2692445 := bbase (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) (by norm_num)
theorem B2422109 : Blo 1613005 2422109 := bbase (se 3 (by rfl) ⟨454145, by rfl⟩ : syracuseStep 2422109 = 908291) (by norm_num)
theorem B4085093 : Blo 1613005 4085093 := bbase (se 4 (by rfl) ⟨382977, by rfl⟩ : syracuseStep 4085093 = 765955) (by norm_num)
theorem B5444981 : Blo 1613005 5444981 := bbase (se 5 (by rfl) ⟨255233, by rfl⟩ : syracuseStep 5444981 = 510467) (by norm_num)
theorem B1815925 : Blo 1613005 1815925 := bbase (se 5 (by rfl) ⟨85121, by rfl⟩ : syracuseStep 1815925 = 170243) (by norm_num)
theorem B2422133 : Blo 1613005 2422133 := bbase (se 5 (by rfl) ⟨113537, by rfl⟩ : syracuseStep 2422133 = 227075) (by norm_num)
theorem B2299261 : Blo 1613005 2299261 := bbase (se 3 (by rfl) ⟨431111, by rfl⟩ : syracuseStep 2299261 = 862223) (by norm_num)
theorem B2422157 : Blo 1613005 2422157 := bbase (se 3 (by rfl) ⟨454154, by rfl⟩ : syracuseStep 2422157 = 908309) (by norm_num)
theorem B1815961 : Blo 1613005 1815961 := bbase (se 2 (by rfl) ⟨680985, by rfl⟩ : syracuseStep 1815961 = 1361971) (by norm_num)
theorem B1938853 : Blo 1613005 1938853 := bbase (se 4 (by rfl) ⟨181767, by rfl⟩ : syracuseStep 1938853 = 363535) (by norm_num)
theorem B2422181 : Blo 1613005 2422181 := bbase (se 4 (by rfl) ⟨227079, by rfl⟩ : syracuseStep 2422181 = 454159) (by norm_num)
theorem B2725285 : Blo 1613005 2725285 := bbase (se 4 (by rfl) ⟨255495, by rfl⟩ : syracuseStep 2725285 = 510991) (by norm_num)
theorem B11040181 : Blo 1613005 11040181 := bbase (se 5 (by rfl) ⟨517508, by rfl⟩ : syracuseStep 11040181 = 1035017) (by norm_num)
theorem B1815997 : Blo 1613005 1815997 := bbase (se 3 (by rfl) ⟨340499, by rfl⟩ : syracuseStep 1815997 = 680999) (by norm_num)
theorem B2422205 : Blo 1613005 2422205 := bbase (se 3 (by rfl) ⟨454163, by rfl⟩ : syracuseStep 2422205 = 908327) (by norm_num)
theorem B6124997 : Blo 1613005 6124997 := bbase (se 4 (by rfl) ⟨574218, by rfl⟩ : syracuseStep 6124997 = 1148437) (by norm_num)
theorem B8721877 : Blo 1613005 8721877 := bbase (se 7 (by rfl) ⟨102209, by rfl⟩ : syracuseStep 8721877 = 204419) (by norm_num)
theorem B1938901 : Blo 1613005 1938901 := bbase (se 7 (by rfl) ⟨22721, by rfl⟩ : syracuseStep 1938901 = 45443) (by norm_num)
theorem B2422229 : Blo 1613005 2422229 := bbase (se 7 (by rfl) ⟨28385, by rfl⟩ : syracuseStep 2422229 = 56771) (by norm_num)
theorem B2299357 : Blo 1613005 2299357 := bbase (se 3 (by rfl) ⟨431129, by rfl⟩ : syracuseStep 2299357 = 862259) (by norm_num)
theorem B1816033 : Blo 1613005 1816033 := bbase (se 2 (by rfl) ⟨681012, by rfl⟩ : syracuseStep 1816033 = 1362025) (by norm_num)
theorem B2422253 : Blo 1613005 2422253 := bbase (se 3 (by rfl) ⟨454172, by rfl⟩ : syracuseStep 2422253 = 908345) (by norm_num)
theorem B1816069 : Blo 1613005 1816069 := bbase (se 4 (by rfl) ⟨170256, by rfl⟩ : syracuseStep 1816069 = 340513) (by norm_num)
theorem B8173061 : Blo 1613005 8173061 := bbase (se 4 (by rfl) ⟨766224, by rfl⟩ : syracuseStep 8173061 = 1532449) (by norm_num)
theorem B2422277 : Blo 1613005 2422277 := bbase (se 4 (by rfl) ⟨227088, by rfl⟩ : syracuseStep 2422277 = 454177) (by norm_num)
theorem B2422301 : Blo 1613005 2422301 := bbase (se 3 (by rfl) ⟨454181, by rfl⟩ : syracuseStep 2422301 = 908363) (by norm_num)
theorem B1816105 : Blo 1613005 1816105 := bbase (se 2 (by rfl) ⟨681039, by rfl⟩ : syracuseStep 1816105 = 1362079) (by norm_num)
theorem B2422325 : Blo 1613005 2422325 := bbase (se 5 (by rfl) ⟨113546, by rfl⟩ : syracuseStep 2422325 = 227093) (by norm_num)
theorem B1816141 : Blo 1613005 1816141 := bbase (se 3 (by rfl) ⟨340526, by rfl⟩ : syracuseStep 1816141 = 681053) (by norm_num)
theorem B2422349 : Blo 1613005 2422349 := bbase (se 3 (by rfl) ⟨454190, by rfl⟩ : syracuseStep 2422349 = 908381) (by norm_num)
theorem B2422373 : Blo 1613005 2422373 := bbase (se 4 (by rfl) ⟨227097, by rfl⟩ : syracuseStep 2422373 = 454195) (by norm_num)
theorem B1816177 : Blo 1613005 1816177 := bbase (se 2 (by rfl) ⟨681066, by rfl⟩ : syracuseStep 1816177 = 1362133) (by norm_num)
theorem B3929717 : Blo 1613005 3929717 := bbase (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) (by norm_num)
theorem B2422397 : Blo 1613005 2422397 := bbase (se 3 (by rfl) ⟨454199, by rfl⟩ : syracuseStep 2422397 = 908399) (by norm_num)
theorem B3446405 : Blo 1613005 3446405 := bbase (se 4 (by rfl) ⟨323100, by rfl⟩ : syracuseStep 3446405 = 646201) (by norm_num)
theorem B6542981 : Blo 1613005 6542981 := bbase (se 4 (by rfl) ⟨613404, by rfl⟩ : syracuseStep 6542981 = 1226809) (by norm_num)
theorem B1816213 : Blo 1613005 1816213 := bbase (se 6 (by rfl) ⟨42567, by rfl⟩ : syracuseStep 1816213 = 85135) (by norm_num)
theorem B2422421 : Blo 1613005 2422421 := bbase (se 6 (by rfl) ⟨56775, by rfl⟩ : syracuseStep 2422421 = 113551) (by norm_num)
theorem B2422445 : Blo 1613005 2422445 := bbase (se 3 (by rfl) ⟨454208, by rfl⟩ : syracuseStep 2422445 = 908417) (by norm_num)
theorem B1816249 : Blo 1613005 1816249 := bbase (se 2 (by rfl) ⟨681093, by rfl⟩ : syracuseStep 1816249 = 1362187) (by norm_num)
theorem B4085437 : Blo 1613005 4085437 := bbase (se 3 (by rfl) ⟨766019, by rfl⟩ : syracuseStep 4085437 = 1532039) (by norm_num)
theorem B2422469 : Blo 1613005 2422469 := bbase (se 4 (by rfl) ⟨227106, by rfl⟩ : syracuseStep 2422469 = 454213) (by norm_num)
theorem B1816285 : Blo 1613005 1816285 := bbase (se 3 (by rfl) ⟨340553, by rfl⟩ : syracuseStep 1816285 = 681107) (by norm_num)
theorem B2422493 : Blo 1613005 2422493 := bbase (se 3 (by rfl) ⟨454217, by rfl⟩ : syracuseStep 2422493 = 908435) (by norm_num)
theorem B3446525 : Blo 1613005 3446525 := bbase (se 3 (by rfl) ⟨646223, by rfl⟩ : syracuseStep 3446525 = 1292447) (by norm_num)
theorem B1816321 : Blo 1613005 1816321 := bbase (se 2 (by rfl) ⟨681120, by rfl⟩ : syracuseStep 1816321 = 1362241) (by norm_num)
theorem B6543109 : Blo 1613005 6543109 := bbase (se 4 (by rfl) ⟨613416, by rfl⟩ : syracuseStep 6543109 = 1226833) (by norm_num)
theorem B5445413 : Blo 1613005 5445413 := bbase (se 4 (by rfl) ⟨510507, by rfl⟩ : syracuseStep 5445413 = 1021015) (by norm_num)
theorem B1816357 : Blo 1613005 1816357 := bbase (se 4 (by rfl) ⟨170283, by rfl⟩ : syracuseStep 1816357 = 340567) (by norm_num)
theorem B4085549 : Blo 1613005 4085549 := bbase (se 3 (by rfl) ⟨766040, by rfl⟩ : syracuseStep 4085549 = 1532081) (by norm_num)
theorem B2586413 : Blo 1613005 2586413 := bbase (se 3 (by rfl) ⟨484952, by rfl⟩ : syracuseStep 2586413 = 969905) (by norm_num)
theorem B1816393 : Blo 1613005 1816393 := bbase (se 2 (by rfl) ⟨681147, by rfl⟩ : syracuseStep 1816393 = 1362295) (by norm_num)
theorem B1816429 : Blo 1613005 1816429 := bbase (se 3 (by rfl) ⟨340580, by rfl⟩ : syracuseStep 1816429 = 681161) (by norm_num)
theorem B1816465 : Blo 1613005 1816465 := bbase (se 2 (by rfl) ⟨681174, by rfl⟩ : syracuseStep 1816465 = 1362349) (by norm_num)
theorem B2070425 : Blo 1613005 2070425 := bbase (se 2 (by rfl) ⟨776409, by rfl⟩ : syracuseStep 2070425 = 1552819) (by norm_num)
theorem B1816501 : Blo 1613005 1816501 := bbase (se 5 (by rfl) ⟨85148, by rfl⟩ : syracuseStep 1816501 = 170297) (by norm_num)
theorem B1816537 : Blo 1613005 1816537 := bbase (se 2 (by rfl) ⟨681201, by rfl⟩ : syracuseStep 1816537 = 1362403) (by norm_num)
theorem B4085741 : Blo 1613005 4085741 := bbase (se 3 (by rfl) ⟨766076, by rfl⟩ : syracuseStep 4085741 = 1532153) (by norm_num)
theorem B1636345 : Blo 1613005 1636345 := bbase (se 2 (by rfl) ⟨613629, by rfl⟩ : syracuseStep 1636345 = 1227259) (by norm_num)
theorem B1816573 : Blo 1613005 1816573 := bbase (se 3 (by rfl) ⟨340607, by rfl⟩ : syracuseStep 1816573 = 681215) (by norm_num)
theorem B5314565 : Blo 1613005 5314565 := bbase (se 4 (by rfl) ⟨498240, by rfl⟩ : syracuseStep 5314565 = 996481) (by norm_num)
theorem B1816609 : Blo 1613005 1816609 := bbase (se 2 (by rfl) ⟨681228, by rfl⟩ : syracuseStep 1816609 = 1362457) (by norm_num)
theorem B1816645 : Blo 1613005 1816645 := bbase (se 4 (by rfl) ⟨170310, by rfl⟩ : syracuseStep 1816645 = 340621) (by norm_num)
theorem B1816681 : Blo 1613005 1816681 := bbase (se 2 (by rfl) ⟨681255, by rfl⟩ : syracuseStep 1816681 = 1362511) (by norm_num)
theorem B1816717 : Blo 1613005 1816717 := bbase (se 3 (by rfl) ⟨340634, by rfl⟩ : syracuseStep 1816717 = 681269) (by norm_num)
theorem B1816753 : Blo 1613005 1816753 := bbase (se 2 (by rfl) ⟨681282, by rfl⟩ : syracuseStep 1816753 = 1362565) (by norm_num)
theorem B5445845 : Blo 1613005 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B1816789 : Blo 1613005 1816789 := bbase (se 7 (by rfl) ⟨21290, by rfl⟩ : syracuseStep 1816789 = 42581) (by norm_num)
theorem B1816825 : Blo 1613005 1816825 := bbase (se 2 (by rfl) ⟨681309, by rfl⟩ : syracuseStep 1816825 = 1362619) (by norm_num)
theorem B1841417 : Blo 1613005 1841417 := bbase (se 2 (by rfl) ⟨690531, by rfl⟩ : syracuseStep 1841417 = 1381063) (by norm_num)
theorem B1816861 : Blo 1613005 1816861 := bbase (se 3 (by rfl) ⟨340661, by rfl⟩ : syracuseStep 1816861 = 681323) (by norm_num)
theorem B2586925 : Blo 1613005 2586925 := bbase (se 3 (by rfl) ⟨485048, by rfl⟩ : syracuseStep 2586925 = 970097) (by norm_num)
theorem B4086085 : Blo 1613005 4086085 := bbase (se 4 (by rfl) ⟨383070, by rfl⟩ : syracuseStep 4086085 = 766141) (by norm_num)
theorem B2070893 : Blo 1613005 2070893 := bbase (se 3 (by rfl) ⟨388292, by rfl⟩ : syracuseStep 2070893 = 776585) (by norm_num)
theorem B3447157 : Blo 1613005 3447157 := bbase (se 5 (by rfl) ⟨161585, by rfl⟩ : syracuseStep 3447157 = 323171) (by norm_num)
theorem B5519765 : Blo 1613005 5519765 := bbase (se 6 (by rfl) ⟨129369, by rfl⟩ : syracuseStep 5519765 = 258739) (by norm_num)
theorem B7756181 : Blo 1613005 7756181 := bbase (se 6 (by rfl) ⟨181785, by rfl⟩ : syracuseStep 7756181 = 363571) (by norm_num)
theorem B4086197 : Blo 1613005 4086197 := bbase (se 5 (by rfl) ⟨191540, by rfl⟩ : syracuseStep 4086197 = 383081) (by norm_num)
theorem B20683349 : Blo 1613005 20683349 := bbase (se 8 (by rfl) ⟨121191, by rfl⟩ : syracuseStep 20683349 = 242383) (by norm_num)
theorem B4086389 : Blo 1613005 4086389 := bbase (se 5 (by rfl) ⟨191549, by rfl⟩ : syracuseStep 4086389 = 383099) (by norm_num)
theorem B5446277 : Blo 1613005 5446277 := bbase (se 4 (by rfl) ⟨510588, by rfl⟩ : syracuseStep 5446277 = 1021177) (by norm_num)
theorem B1940117 : Blo 1613005 1940117 := bbase (se 6 (by rfl) ⟨45471, by rfl⟩ : syracuseStep 1940117 = 90943) (by norm_num)
theorem B7756469 : Blo 1613005 7756469 := bbase (se 5 (by rfl) ⟨363584, by rfl⟩ : syracuseStep 7756469 = 727169) (by norm_num)
theorem B3062461 : Blo 1613005 3062461 := bbase (se 3 (by rfl) ⟨574211, by rfl⟩ : syracuseStep 3062461 = 1148423) (by norm_num)
theorem B5167813 : Blo 1613005 5167813 := bbase (se 4 (by rfl) ⟨484482, by rfl⟩ : syracuseStep 5167813 = 968965) (by norm_num)
theorem B4365013 : Blo 1613005 4365013 := bbase (se 7 (by rfl) ⟨51152, by rfl⟩ : syracuseStep 4365013 = 102305) (by norm_num)
theorem B4594421 : Blo 1613005 4594421 := bbase (se 5 (by rfl) ⟨215363, by rfl⟩ : syracuseStep 4594421 = 430727) (by norm_num)
theorem B7363333 : Blo 1613005 7363333 := bbase (se 4 (by rfl) ⟨690312, by rfl⟩ : syracuseStep 7363333 = 1380625) (by norm_num)
theorem B8174357 : Blo 1613005 8174357 := bbase (se 6 (by rfl) ⟨191586, by rfl⟩ : syracuseStep 8174357 = 383173) (by norm_num)
theorem B3062605 : Blo 1613005 3062605 := bbase (se 3 (by rfl) ⟨574238, by rfl⟩ : syracuseStep 3062605 = 1148477) (by norm_num)
theorem B6896501 : Blo 1613005 6896501 := bbase (se 5 (by rfl) ⟨323273, by rfl⟩ : syracuseStep 6896501 = 646547) (by norm_num)
theorem B23280533 : Blo 1613005 23280533 := bbase (se 6 (by rfl) ⟨545637, by rfl⟩ : syracuseStep 23280533 = 1091275) (by norm_num)
theorem B4086733 : Blo 1613005 4086733 := bbase (se 3 (by rfl) ⟨766262, by rfl⟩ : syracuseStep 4086733 = 1532525) (by norm_num)
theorem B3062765 : Blo 1613005 3062765 := bbase (se 3 (by rfl) ⟨574268, by rfl⟩ : syracuseStep 3062765 = 1148537) (by norm_num)
theorem B7461877 : Blo 1613005 7461877 := bbase (se 5 (by rfl) ⟨349775, by rfl⟩ : syracuseStep 7461877 = 699551) (by norm_num)
theorem B5446709 : Blo 1613005 5446709 := bbase (se 5 (by rfl) ⟨255314, by rfl⟩ : syracuseStep 5446709 = 510629) (by norm_num)
theorem B4086845 : Blo 1613005 4086845 := bbase (se 3 (by rfl) ⟨766283, by rfl⟩ : syracuseStep 4086845 = 1532567) (by norm_num)
theorem B3062909 : Blo 1613005 3062909 := bbase (se 3 (by rfl) ⟨574295, by rfl⟩ : syracuseStep 3062909 = 1148591) (by norm_num)
theorem B8166581 : Blo 1613005 8166581 := bbase (se 5 (by rfl) ⟨382808, by rfl⟩ : syracuseStep 8166581 = 765617) (by norm_num)
theorem B3448045 : Blo 1613005 3448045 := bbase (se 3 (by rfl) ⟨646508, by rfl⟩ : syracuseStep 3448045 = 1293017) (by norm_num)
theorem B4087037 : Blo 1613005 4087037 := bbase (se 3 (by rfl) ⟨766319, by rfl⟩ : syracuseStep 4087037 = 1532639) (by norm_num)
theorem B5815637 : Blo 1613005 5815637 := bbase (se 11 (by rfl) ⟨4259, by rfl⟩ : syracuseStep 5815637 = 8519) (by norm_num)
theorem B3448165 : Blo 1613005 3448165 := bbase (se 4 (by rfl) ⟨323265, by rfl⟩ : syracuseStep 3448165 = 646531) (by norm_num)
theorem B2522477 : Blo 1613005 2522477 := bbase (se 3 (by rfl) ⟨472964, by rfl⟩ : syracuseStep 2522477 = 945929) (by norm_num)
theorem B4595093 : Blo 1613005 4595093 := bbase (se 6 (by rfl) ⟨107697, by rfl⟩ : syracuseStep 4595093 = 215395) (by norm_num)
theorem B10624405 : Blo 1613005 10624405 := bbase (se 6 (by rfl) ⟨249009, by rfl⟩ : syracuseStep 10624405 = 498019) (by norm_num)
theorem B10345877 : Blo 1613005 10345877 := bbase (se 6 (by rfl) ⟨242481, by rfl⟩ : syracuseStep 10345877 = 484963) (by norm_num)
theorem B3063197 : Blo 1613005 3063197 := bbase (se 3 (by rfl) ⟨574349, by rfl⟩ : syracuseStep 3063197 = 1148699) (by norm_num)
theorem B2620837 : Blo 1613005 2620837 := bbase (se 4 (by rfl) ⟨245703, by rfl⟩ : syracuseStep 2620837 = 491407) (by norm_num)
theorem B5447141 : Blo 1613005 5447141 := bbase (se 4 (by rfl) ⟨510669, by rfl⟩ : syracuseStep 5447141 = 1021339) (by norm_num)
theorem B14720501 : Blo 1613005 14720501 := bbase (se 5 (by rfl) ⟨690023, by rfl⟩ : syracuseStep 14720501 = 1380047) (by norm_num)
theorem B6127109 : Blo 1613005 6127109 := bbase (se 4 (by rfl) ⟨574416, by rfl⟩ : syracuseStep 6127109 = 1148833) (by norm_num)
theorem B2760205 : Blo 1613005 2760205 := bbase (se 3 (by rfl) ⟨517538, by rfl⟩ : syracuseStep 2760205 = 1035077) (by norm_num)
theorem B3063349 : Blo 1613005 3063349 := bbase (se 5 (by rfl) ⟨143594, by rfl⟩ : syracuseStep 3063349 = 287189) (by norm_num)
theorem B4087381 : Blo 1613005 4087381 := bbase (se 8 (by rfl) ⟨23949, by rfl⟩ : syracuseStep 4087381 = 47899) (by norm_num)
theorem B3448421 : Blo 1613005 3448421 := bbase (se 4 (by rfl) ⟨323289, by rfl⟩ : syracuseStep 3448421 = 646579) (by norm_num)
theorem B4087493 : Blo 1613005 4087493 := bbase (se 4 (by rfl) ⟨383202, by rfl⟩ : syracuseStep 4087493 = 766405) (by norm_num)
theorem B6127397 : Blo 1613005 6127397 := bbase (se 4 (by rfl) ⟨574443, by rfl⟩ : syracuseStep 6127397 = 1148887) (by norm_num)
theorem B4595525 : Blo 1613005 4595525 := bbase (se 4 (by rfl) ⟨430830, by rfl⟩ : syracuseStep 4595525 = 861661) (by norm_num)
theorem B3063653 : Blo 1613005 3063653 := bbase (se 4 (by rfl) ⟨287217, by rfl⟩ : syracuseStep 3063653 = 574435) (by norm_num)
theorem B4087685 : Blo 1613005 4087685 := bbase (se 4 (by rfl) ⟨383220, by rfl⟩ : syracuseStep 4087685 = 766441) (by norm_num)
theorem B5447573 : Blo 1613005 5447573 := bbase (se 6 (by rfl) ⟨127677, by rfl⟩ : syracuseStep 5447573 = 255355) (by norm_num)
theorem B7364501 : Blo 1613005 7364501 := bbase (se 6 (by rfl) ⟨172605, by rfl⟩ : syracuseStep 7364501 = 345211) (by norm_num)
theorem B1613827 : Blo 1613005 1613827 := bstep (se 1 (by rfl) ⟨1210370, by rfl⟩ : syracuseStep 1613827 = 2420741) B2420741
theorem B1613843 : Blo 1613005 1613843 := bstep (se 1 (by rfl) ⟨1210382, by rfl⟩ : syracuseStep 1613843 = 2420765) B2420765
theorem B1613859 : Blo 1613005 1613859 := bstep (se 1 (by rfl) ⟨1210394, by rfl⟩ : syracuseStep 1613859 = 2420789) B2420789
theorem B5169197 : Blo 1613005 5169197 := bstep (se 3 (by rfl) ⟨969224, by rfl⟩ : syracuseStep 5169197 = 1938449) B1938449
theorem B1613875 : Blo 1613005 1613875 := bstep (se 1 (by rfl) ⟨1210406, by rfl⟩ : syracuseStep 1613875 = 2420813) B2420813
theorem B1613891 : Blo 1613005 1613891 := bstep (se 1 (by rfl) ⟨1210418, by rfl⟩ : syracuseStep 1613891 = 2420837) B2420837
theorem B1613907 : Blo 1613005 1613907 := bstep (se 1 (by rfl) ⟨1210430, by rfl⟩ : syracuseStep 1613907 = 2420861) B2420861
theorem B1613923 : Blo 1613005 1613923 := bstep (se 1 (by rfl) ⟨1210442, by rfl⟩ : syracuseStep 1613923 = 2420885) B2420885
theorem B5447789 : Blo 1613005 5447789 := bstep (se 3 (by rfl) ⟨1021460, by rfl⟩ : syracuseStep 5447789 = 2042921) B2042921
theorem B1613939 : Blo 1613005 1613939 := bstep (se 1 (by rfl) ⟨1210454, by rfl⟩ : syracuseStep 1613939 = 2420909) B2420909
theorem B1613955 : Blo 1613005 1613955 := bstep (se 1 (by rfl) ⟨1210466, by rfl⟩ : syracuseStep 1613955 = 2420933) B2420933
theorem B1613971 : Blo 1613005 1613971 := bstep (se 1 (by rfl) ⟨1210478, by rfl⟩ : syracuseStep 1613971 = 2420957) B2420957
theorem B1613987 : Blo 1613005 1613987 := bstep (se 1 (by rfl) ⟨1210490, by rfl⟩ : syracuseStep 1613987 = 2420981) B2420981
theorem B5447843 : Blo 1613005 5447843 := bstep (se 1 (by rfl) ⟨4085882, by rfl⟩ : syracuseStep 5447843 = 8171765) B8171765
theorem B1614003 : Blo 1613005 1614003 := bstep (se 1 (by rfl) ⟨1210502, by rfl⟩ : syracuseStep 1614003 = 2421005) B2421005
theorem B1614019 : Blo 1613005 1614019 := bstep (se 1 (by rfl) ⟨1210514, by rfl⟩ : syracuseStep 1614019 = 2421029) B2421029
theorem B1614035 : Blo 1613005 1614035 := bstep (se 1 (by rfl) ⟨1210526, by rfl⟩ : syracuseStep 1614035 = 2421053) B2421053
theorem B1614051 : Blo 1613005 1614051 := bstep (se 1 (by rfl) ⟨1210538, by rfl⟩ : syracuseStep 1614051 = 2421077) B2421077
theorem B1614067 : Blo 1613005 1614067 := bstep (se 1 (by rfl) ⟨1210550, by rfl⟩ : syracuseStep 1614067 = 2421101) B2421101
theorem B1614083 : Blo 1613005 1614083 := bstep (se 1 (by rfl) ⟨1210562, by rfl⟩ : syracuseStep 1614083 = 2421125) B2421125
theorem B1614099 : Blo 1613005 1614099 := bstep (se 1 (by rfl) ⟨1210574, by rfl⟩ : syracuseStep 1614099 = 2421149) B2421149
theorem B8167715 : Blo 1613005 8167715 := bstep (se 1 (by rfl) ⟨6125786, by rfl⟩ : syracuseStep 8167715 = 12251573) B12251573
theorem B1614115 : Blo 1613005 1614115 := bstep (se 1 (by rfl) ⟨1210586, by rfl⟩ : syracuseStep 1614115 = 2421173) B2421173
theorem B1614131 : Blo 1613005 1614131 := bstep (se 1 (by rfl) ⟨1210598, by rfl⟩ : syracuseStep 1614131 = 2421197) B2421197
theorem B1614147 : Blo 1613005 1614147 := bstep (se 1 (by rfl) ⟨1210610, by rfl⟩ : syracuseStep 1614147 = 2421221) B2421221
theorem B3629393 : Blo 1613005 3629393 := bstep (se 2 (by rfl) ⟨1361022, by rfl⟩ : syracuseStep 3629393 = 2722045) B2722045
theorem B1614163 : Blo 1613005 1614163 := bstep (se 1 (by rfl) ⟨1210622, by rfl⟩ : syracuseStep 1614163 = 2421245) B2421245
theorem B3629411 : Blo 1613005 3629411 := bstep (se 1 (by rfl) ⟨2722058, by rfl⟩ : syracuseStep 3629411 = 5444117) B5444117
theorem B1614179 : Blo 1613005 1614179 := bstep (se 1 (by rfl) ⟨1210634, by rfl⟩ : syracuseStep 1614179 = 2421269) B2421269
theorem B1614195 : Blo 1613005 1614195 := bstep (se 1 (by rfl) ⟨1210646, by rfl⟩ : syracuseStep 1614195 = 2421293) B2421293
theorem B1614211 : Blo 1613005 1614211 := bstep (se 1 (by rfl) ⟨1210658, by rfl⟩ : syracuseStep 1614211 = 2421317) B2421317
theorem B3449233 : Blo 1613005 3449233 := bstep (se 2 (by rfl) ⟨1293462, by rfl⟩ : syracuseStep 3449233 = 2586925) B2586925
theorem B1614227 : Blo 1613005 1614227 := bstep (se 1 (by rfl) ⟨1210670, by rfl⟩ : syracuseStep 1614227 = 2421341) B2421341
theorem B1614243 : Blo 1613005 1614243 := bstep (se 1 (by rfl) ⟨1210682, by rfl⟩ : syracuseStep 1614243 = 2421365) B2421365
theorem B3932579 : Blo 1613005 3932579 := bstep (se 1 (by rfl) ⟨2949434, by rfl⟩ : syracuseStep 3932579 = 5898869) B5898869
theorem B5448113 : Blo 1613005 5448113 := bstep (se 2 (by rfl) ⟨2043042, by rfl⟩ : syracuseStep 5448113 = 4086085) B4086085
theorem B1614259 : Blo 1613005 1614259 := bstep (se 1 (by rfl) ⟨1210694, by rfl⟩ : syracuseStep 1614259 = 2421389) B2421389
theorem B1614275 : Blo 1613005 1614275 := bstep (se 1 (by rfl) ⟨1210706, by rfl⟩ : syracuseStep 1614275 = 2421413) B2421413
theorem B1614291 : Blo 1613005 1614291 := bstep (se 1 (by rfl) ⟨1210718, by rfl⟩ : syracuseStep 1614291 = 2421437) B2421437
theorem B1614307 : Blo 1613005 1614307 := bstep (se 1 (by rfl) ⟨1210730, by rfl⟩ : syracuseStep 1614307 = 2421461) B2421461
theorem B4596209 : Blo 1613005 4596209 := bstep (se 2 (by rfl) ⟨1723578, by rfl⟩ : syracuseStep 4596209 = 3447157) B3447157
theorem B1614323 : Blo 1613005 1614323 := bstep (se 1 (by rfl) ⟨1210742, by rfl⟩ : syracuseStep 1614323 = 2421485) B2421485
theorem B1614339 : Blo 1613005 1614339 := bstep (se 1 (by rfl) ⟨1210754, by rfl⟩ : syracuseStep 1614339 = 2421509) B2421509
theorem B1614355 : Blo 1613005 1614355 := bstep (se 1 (by rfl) ⟨1210766, by rfl⟩ : syracuseStep 1614355 = 2421533) B2421533
theorem B1614371 : Blo 1613005 1614371 := bstep (se 1 (by rfl) ⟨1210778, by rfl⟩ : syracuseStep 1614371 = 2421557) B2421557
theorem B1614387 : Blo 1613005 1614387 := bstep (se 1 (by rfl) ⟨1210790, by rfl⟩ : syracuseStep 1614387 = 2421581) B2421581
theorem B1614403 : Blo 1613005 1614403 := bstep (se 1 (by rfl) ⟨1210802, by rfl⟩ : syracuseStep 1614403 = 2421605) B2421605
theorem B1614419 : Blo 1613005 1614419 := bstep (se 1 (by rfl) ⟨1210814, by rfl⟩ : syracuseStep 1614419 = 2421629) B2421629
theorem B1614435 : Blo 1613005 1614435 := bstep (se 1 (by rfl) ⟨1210826, by rfl⟩ : syracuseStep 1614435 = 2421653) B2421653
theorem B3629681 : Blo 1613005 3629681 := bstep (se 2 (by rfl) ⟨1361130, by rfl⟩ : syracuseStep 3629681 = 2722261) B2722261
theorem B1614451 : Blo 1613005 1614451 := bstep (se 1 (by rfl) ⟨1210838, by rfl⟩ : syracuseStep 1614451 = 2421677) B2421677
theorem B3629699 : Blo 1613005 3629699 := bstep (se 1 (by rfl) ⟨2722274, by rfl⟩ : syracuseStep 3629699 = 5444549) B5444549
theorem B1614467 : Blo 1613005 1614467 := bstep (se 1 (by rfl) ⟨1210850, by rfl⟩ : syracuseStep 1614467 = 2421701) B2421701
theorem B1614483 : Blo 1613005 1614483 := bstep (se 1 (by rfl) ⟨1210862, by rfl⟩ : syracuseStep 1614483 = 2421725) B2421725
theorem B1614499 : Blo 1613005 1614499 := bstep (se 1 (by rfl) ⟨1210874, by rfl⟩ : syracuseStep 1614499 = 2421749) B2421749
theorem B1614515 : Blo 1613005 1614515 := bstep (se 1 (by rfl) ⟨1210886, by rfl⟩ : syracuseStep 1614515 = 2421773) B2421773
theorem B1614531 : Blo 1613005 1614531 := bstep (se 1 (by rfl) ⟨1210898, by rfl⟩ : syracuseStep 1614531 = 2421797) B2421797
theorem B1614547 : Blo 1613005 1614547 := bstep (se 1 (by rfl) ⟨1210910, by rfl⟩ : syracuseStep 1614547 = 2421821) B2421821
theorem B1614563 : Blo 1613005 1614563 := bstep (se 1 (by rfl) ⟨1210922, by rfl⟩ : syracuseStep 1614563 = 2421845) B2421845
theorem B6128369 : Blo 1613005 6128369 := bstep (se 2 (by rfl) ⟨2298138, by rfl⟩ : syracuseStep 6128369 = 4596277) B4596277
theorem B1614579 : Blo 1613005 1614579 := bstep (se 1 (by rfl) ⟨1210934, by rfl⟩ : syracuseStep 1614579 = 2421869) B2421869
theorem B1614595 : Blo 1613005 1614595 := bstep (se 1 (by rfl) ⟨1210946, by rfl⟩ : syracuseStep 1614595 = 2421893) B2421893
theorem B1614611 : Blo 1613005 1614611 := bstep (se 1 (by rfl) ⟨1210958, by rfl⟩ : syracuseStep 1614611 = 2421917) B2421917
theorem B1614627 : Blo 1613005 1614627 := bstep (se 1 (by rfl) ⟨1210970, by rfl⟩ : syracuseStep 1614627 = 2421941) B2421941
theorem B3064625 : Blo 1613005 3064625 := bstep (se 2 (by rfl) ⟨1149234, by rfl⟩ : syracuseStep 3064625 = 2298469) B2298469
theorem B1614643 : Blo 1613005 1614643 := bstep (se 1 (by rfl) ⟨1210982, by rfl⟩ : syracuseStep 1614643 = 2421965) B2421965
theorem B1614659 : Blo 1613005 1614659 := bstep (se 1 (by rfl) ⟨1210994, by rfl⟩ : syracuseStep 1614659 = 2421989) B2421989
theorem B1614675 : Blo 1613005 1614675 := bstep (se 1 (by rfl) ⟨1211006, by rfl⟩ : syracuseStep 1614675 = 2422013) B2422013
theorem B1614691 : Blo 1613005 1614691 := bstep (se 1 (by rfl) ⟨1211018, by rfl⟩ : syracuseStep 1614691 = 2422037) B2422037
theorem B1614707 : Blo 1613005 1614707 := bstep (se 1 (by rfl) ⟨1211030, by rfl⟩ : syracuseStep 1614707 = 2422061) B2422061
theorem B1614723 : Blo 1613005 1614723 := bstep (se 1 (by rfl) ⟨1211042, by rfl⟩ : syracuseStep 1614723 = 2422085) B2422085
theorem B9192325 : Blo 1613005 9192325 := bstep (se 4 (by rfl) ⟨861780, by rfl⟩ : syracuseStep 9192325 = 1723561) B1723561
theorem B3629969 : Blo 1613005 3629969 := bstep (se 2 (by rfl) ⟨1361238, by rfl⟩ : syracuseStep 3629969 = 2722477) B2722477
theorem B1614739 : Blo 1613005 1614739 := bstep (se 1 (by rfl) ⟨1211054, by rfl⟩ : syracuseStep 1614739 = 2422109) B2422109
theorem B3629987 : Blo 1613005 3629987 := bstep (se 1 (by rfl) ⟨2722490, by rfl⟩ : syracuseStep 3629987 = 5444981) B5444981
theorem B1614755 : Blo 1613005 1614755 := bstep (se 1 (by rfl) ⟨1211066, by rfl⟩ : syracuseStep 1614755 = 2422133) B2422133
theorem B6890417 : Blo 1613005 6890417 := bstep (se 2 (by rfl) ⟨2583906, by rfl⟩ : syracuseStep 6890417 = 5167813) B5167813
theorem B1614771 : Blo 1613005 1614771 := bstep (se 1 (by rfl) ⟨1211078, by rfl⟩ : syracuseStep 1614771 = 2422157) B2422157
theorem B1614787 : Blo 1613005 1614787 := bstep (se 1 (by rfl) ⟨1211090, by rfl⟩ : syracuseStep 1614787 = 2422181) B2422181
theorem B5522381 : Blo 1613005 5522381 := bstep (se 3 (by rfl) ⟨1035446, by rfl⟩ : syracuseStep 5522381 = 2070893) B2070893
theorem B5448653 : Blo 1613005 5448653 := bstep (se 3 (by rfl) ⟨1021622, by rfl⟩ : syracuseStep 5448653 = 2043245) B2043245
theorem B1614803 : Blo 1613005 1614803 := bstep (se 1 (by rfl) ⟨1211102, by rfl⟩ : syracuseStep 1614803 = 2422205) B2422205
theorem B1614819 : Blo 1613005 1614819 := bstep (se 1 (by rfl) ⟨1211114, by rfl⟩ : syracuseStep 1614819 = 2422229) B2422229
theorem B1614835 : Blo 1613005 1614835 := bstep (se 1 (by rfl) ⟨1211126, by rfl⟩ : syracuseStep 1614835 = 2422253) B2422253
theorem B5448707 : Blo 1613005 5448707 := bstep (se 1 (by rfl) ⟨4086530, by rfl⟩ : syracuseStep 5448707 = 8173061) B8173061
theorem B1614851 : Blo 1613005 1614851 := bstep (se 1 (by rfl) ⟨1211138, by rfl⟩ : syracuseStep 1614851 = 2422277) B2422277
theorem B1614867 : Blo 1613005 1614867 := bstep (se 1 (by rfl) ⟨1211150, by rfl⟩ : syracuseStep 1614867 = 2422301) B2422301
theorem B1614883 : Blo 1613005 1614883 := bstep (se 1 (by rfl) ⟨1211162, by rfl⟩ : syracuseStep 1614883 = 2422325) B2422325
theorem B1614899 : Blo 1613005 1614899 := bstep (se 1 (by rfl) ⟨1211174, by rfl⟩ : syracuseStep 1614899 = 2422349) B2422349
theorem B1614915 : Blo 1613005 1614915 := bstep (se 1 (by rfl) ⟨1211186, by rfl⟩ : syracuseStep 1614915 = 2422373) B2422373
theorem B8168525 : Blo 1613005 8168525 := bstep (se 3 (by rfl) ⟨1531598, by rfl⟩ : syracuseStep 8168525 = 3063197) B3063197
theorem B1614931 : Blo 1613005 1614931 := bstep (se 1 (by rfl) ⟨1211198, by rfl⟩ : syracuseStep 1614931 = 2422397) B2422397
theorem B1614947 : Blo 1613005 1614947 := bstep (se 1 (by rfl) ⟨1211210, by rfl⟩ : syracuseStep 1614947 = 2422421) B2422421
theorem B1614963 : Blo 1613005 1614963 := bstep (se 1 (by rfl) ⟨1211222, by rfl⟩ : syracuseStep 1614963 = 2422445) B2422445
theorem B1614979 : Blo 1613005 1614979 := bstep (se 1 (by rfl) ⟨1211234, by rfl⟩ : syracuseStep 1614979 = 2422469) B2422469
theorem B1614995 : Blo 1613005 1614995 := bstep (se 1 (by rfl) ⟨1211246, by rfl⟩ : syracuseStep 1614995 = 2422493) B2422493
theorem B3630257 : Blo 1613005 3630257 := bstep (se 2 (by rfl) ⟨1361346, by rfl⟩ : syracuseStep 3630257 = 2722693) B2722693
theorem B3630275 : Blo 1613005 3630275 := bstep (se 1 (by rfl) ⟨2722706, by rfl⟩ : syracuseStep 3630275 = 5445413) B5445413
theorem B5448977 : Blo 1613005 5448977 := bstep (se 2 (by rfl) ⟨2043366, by rfl⟩ : syracuseStep 5448977 = 4086733) B4086733
theorem B4597165 : Blo 1613005 4597165 := bstep (se 3 (by rfl) ⟨861968, by rfl⟩ : syracuseStep 4597165 = 1723937) B1723937
theorem B3630545 : Blo 1613005 3630545 := bstep (se 2 (by rfl) ⟨1361454, by rfl⟩ : syracuseStep 3630545 = 2722909) B2722909
theorem B3630563 : Blo 1613005 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B5817827 : Blo 1613005 5817827 := bstep (se 1 (by rfl) ⟨4363370, by rfl⟩ : syracuseStep 5817827 = 8726741) B8726741
theorem B5596685 : Blo 1613005 5596685 := bstep (se 3 (by rfl) ⟨1049378, by rfl⟩ : syracuseStep 5596685 = 2098757) B2098757
theorem B3679843 : Blo 1613005 3679843 := bstep (se 1 (by rfl) ⟨2759882, by rfl⟩ : syracuseStep 3679843 = 5519765) B5519765
theorem B5170787 : Blo 1613005 5170787 := bstep (se 1 (by rfl) ⟨3878090, by rfl⟩ : syracuseStep 5170787 = 7756181) B7756181
theorem B37774961 : Blo 1613005 37774961 := bstep (se 2 (by rfl) ⟨14165610, by rfl⟩ : syracuseStep 37774961 = 28331221) B28331221
theorem B4597393 : Blo 1613005 4597393 := bstep (se 2 (by rfl) ⟨1724022, by rfl⟩ : syracuseStep 4597393 = 3448045) B3448045
theorem B3065521 : Blo 1613005 3065521 := bstep (se 2 (by rfl) ⟨1149570, by rfl⟩ : syracuseStep 3065521 = 2299141) B2299141
theorem B8726221 : Blo 1613005 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B13788899 : Blo 1613005 13788899 := bstep (se 1 (by rfl) ⟨10341674, by rfl⟩ : syracuseStep 13788899 = 20683349) B20683349
theorem B3630833 : Blo 1613005 3630833 := bstep (se 2 (by rfl) ⟨1361562, by rfl⟩ : syracuseStep 3630833 = 2723125) B2723125
theorem B3630851 : Blo 1613005 3630851 := bstep (se 1 (by rfl) ⟨2723138, by rfl⟩ : syracuseStep 3630851 = 5446277) B5446277
theorem B5170979 : Blo 1613005 5170979 := bstep (se 1 (by rfl) ⟨3878234, by rfl⟩ : syracuseStep 5170979 = 7756469) B7756469
theorem B5449517 : Blo 1613005 5449517 := bstep (se 3 (by rfl) ⟨1021784, by rfl⟩ : syracuseStep 5449517 = 2043569) B2043569
theorem B4597553 : Blo 1613005 4597553 := bstep (se 2 (by rfl) ⟨1724082, by rfl⟩ : syracuseStep 4597553 = 3448165) B3448165
theorem B3065681 : Blo 1613005 3065681 := bstep (se 2 (by rfl) ⟨1149630, by rfl⟩ : syracuseStep 3065681 = 2299261) B2299261
theorem B5449571 : Blo 1613005 5449571 := bstep (se 1 (by rfl) ⟨4087178, by rfl⟩ : syracuseStep 5449571 = 8174357) B8174357
theorem B14165873 : Blo 1613005 14165873 := bstep (se 2 (by rfl) ⟨5312202, by rfl⟩ : syracuseStep 14165873 = 10624405) B10624405
theorem B4597667 : Blo 1613005 4597667 := bstep (se 1 (by rfl) ⟨3448250, by rfl⟩ : syracuseStep 4597667 = 6896501) B6896501
theorem B13092835 : Blo 1613005 13092835 := bstep (se 1 (by rfl) ⟨9819626, by rfl⟩ : syracuseStep 13092835 = 19639253) B19639253
theorem B2041843 : Blo 1613005 2041843 := bstep (se 1 (by rfl) ⟨1531382, by rfl⟩ : syracuseStep 2041843 = 3062765) B3062765
theorem B3680273 : Blo 1613005 3680273 := bstep (se 2 (by rfl) ⟨1380102, by rfl⟩ : syracuseStep 3680273 = 2760205) B2760205
theorem B3631121 : Blo 1613005 3631121 := bstep (se 2 (by rfl) ⟨1361670, by rfl⟩ : syracuseStep 3631121 = 2723341) B2723341
theorem B3631139 : Blo 1613005 3631139 := bstep (se 1 (by rfl) ⟨2723354, by rfl⟩ : syracuseStep 3631139 = 5446709) B5446709
theorem B2041939 : Blo 1613005 2041939 := bstep (se 1 (by rfl) ⟨1531454, by rfl⟩ : syracuseStep 2041939 = 3062909) B3062909
theorem B4360301 : Blo 1613005 4360301 := bstep (se 3 (by rfl) ⟨817556, by rfl⟩ : syracuseStep 4360301 = 1635113) B1635113
theorem B5449841 : Blo 1613005 5449841 := bstep (se 2 (by rfl) ⟨2043690, by rfl⟩ : syracuseStep 5449841 = 4087381) B4087381
theorem B6129827 : Blo 1613005 6129827 := bstep (se 1 (by rfl) ⟨4597370, by rfl⟩ : syracuseStep 6129827 = 9194741) B9194741
theorem B2721971 : Blo 1613005 2721971 := bstep (se 1 (by rfl) ⟨2041478, by rfl⟩ : syracuseStep 2721971 = 4082957) B4082957
theorem B3877091 : Blo 1613005 3877091 := bstep (se 1 (by rfl) ⟨2907818, by rfl⟩ : syracuseStep 3877091 = 5815637) B5815637
theorem B1681651 : Blo 1613005 1681651 := bstep (se 1 (by rfl) ⟨1261238, by rfl⟩ : syracuseStep 1681651 = 2522477) B2522477
theorem B4360451 : Blo 1613005 4360451 := bstep (se 1 (by rfl) ⟨3270338, by rfl⟩ : syracuseStep 4360451 = 6540677) B6540677
theorem B3631409 : Blo 1613005 3631409 := bstep (se 2 (by rfl) ⟨1361778, by rfl⟩ : syracuseStep 3631409 = 2723557) B2723557
theorem B2722099 : Blo 1613005 2722099 := bstep (se 1 (by rfl) ⟨2041574, by rfl⟩ : syracuseStep 2722099 = 4083149) B4083149
theorem B3631427 : Blo 1613005 3631427 := bstep (se 1 (by rfl) ⟨2723570, by rfl⟩ : syracuseStep 3631427 = 5447141) B5447141
theorem B5171633 : Blo 1613005 5171633 := bstep (se 2 (by rfl) ⟨1939362, by rfl⟩ : syracuseStep 5171633 = 3878725) B3878725
theorem B2722241 : Blo 1613005 2722241 := bstep (se 2 (by rfl) ⟨1020840, by rfl⟩ : syracuseStep 2722241 = 2041681) B2041681
theorem B18385379 : Blo 1613005 18385379 := bstep (se 1 (by rfl) ⟨13789034, by rfl⟩ : syracuseStep 18385379 = 27578069) B27578069
theorem B9816589 : Blo 1613005 9816589 := bstep (se 3 (by rfl) ⟨1840610, by rfl⟩ : syracuseStep 9816589 = 3681221) B3681221
theorem B2722369 : Blo 1613005 2722369 := bstep (se 2 (by rfl) ⟨1020888, by rfl⟩ : syracuseStep 2722369 = 2041777) B2041777
theorem B2042435 : Blo 1613005 2042435 := bstep (se 1 (by rfl) ⟨1531826, by rfl⟩ : syracuseStep 2042435 = 3063653) B3063653
theorem B3631697 : Blo 1613005 3631697 := bstep (se 2 (by rfl) ⟨1361886, by rfl⟩ : syracuseStep 3631697 = 2723773) B2723773
theorem B2722403 : Blo 1613005 2722403 := bstep (se 1 (by rfl) ⟨2041802, by rfl⟩ : syracuseStep 2722403 = 4083605) B4083605
theorem B3631715 : Blo 1613005 3631715 := bstep (se 1 (by rfl) ⟨2723786, by rfl⟩ : syracuseStep 3631715 = 5447573) B5447573
theorem B12257891 : Blo 1613005 12257891 := bstep (se 1 (by rfl) ⟨9193418, by rfl⟩ : syracuseStep 12257891 = 18386837) B18386837
theorem B4909667 : Blo 1613005 4909667 := bstep (se 1 (by rfl) ⟨3682250, by rfl⟩ : syracuseStep 4909667 = 7364501) B7364501
theorem B8727173 : Blo 1613005 8727173 := bstep (se 4 (by rfl) ⟨818172, by rfl⟩ : syracuseStep 8727173 = 1636345) B1636345
theorem B5450381 : Blo 1613005 5450381 := bstep (se 3 (by rfl) ⟨1021946, by rfl⟩ : syracuseStep 5450381 = 2043893) B2043893
theorem B5450435 : Blo 1613005 5450435 := bstep (se 1 (by rfl) ⟨4087826, by rfl⟩ : syracuseStep 5450435 = 8175653) B8175653
theorem B2722531 : Blo 1613005 2722531 := bstep (se 1 (by rfl) ⟨2041898, by rfl⟩ : syracuseStep 2722531 = 4083797) B4083797
theorem B2419523 : Blo 1613005 2419523 := bstep (se 1 (by rfl) ⟨1814642, by rfl⟩ : syracuseStep 2419523 = 3629285) B3629285
theorem B9194309 : Blo 1613005 9194309 := bstep (se 4 (by rfl) ⟨861966, by rfl⟩ : syracuseStep 9194309 = 1723933) B1723933
theorem B2419553 : Blo 1613005 2419553 := bstep (se 2 (by rfl) ⟨907332, by rfl⟩ : syracuseStep 2419553 = 1814665) B1814665
theorem B2722673 : Blo 1613005 2722673 := bstep (se 2 (by rfl) ⟨1021002, by rfl⟩ : syracuseStep 2722673 = 2042005) B2042005
theorem B3631985 : Blo 1613005 3631985 := bstep (se 2 (by rfl) ⟨1361994, by rfl⟩ : syracuseStep 3631985 = 2723989) B2723989
theorem B2419571 : Blo 1613005 2419571 := bstep (se 1 (by rfl) ⟨1814678, by rfl⟩ : syracuseStep 2419571 = 3629357) B3629357
theorem B3632003 : Blo 1613005 3632003 := bstep (se 1 (by rfl) ⟨2724002, by rfl⟩ : syracuseStep 3632003 = 5448005) B5448005
theorem B4598669 : Blo 1613005 4598669 := bstep (se 3 (by rfl) ⟨862250, by rfl⟩ : syracuseStep 4598669 = 1724501) B1724501
theorem B2419601 : Blo 1613005 2419601 := bstep (se 2 (by rfl) ⟨907350, by rfl⟩ : syracuseStep 2419601 = 1814701) B1814701
theorem B2419619 : Blo 1613005 2419619 := bstep (se 1 (by rfl) ⟨1814714, by rfl⟩ : syracuseStep 2419619 = 3629429) B3629429
theorem B2419649 : Blo 1613005 2419649 := bstep (se 2 (by rfl) ⟨907368, by rfl⟩ : syracuseStep 2419649 = 1814737) B1814737
theorem B12430277 : Blo 1613005 12430277 := bstep (se 4 (by rfl) ⟨1165338, by rfl⟩ : syracuseStep 12430277 = 2330677) B2330677
theorem B2419667 : Blo 1613005 2419667 := bstep (se 1 (by rfl) ⟨1814750, by rfl⟩ : syracuseStep 2419667 = 3629501) B3629501
theorem B3877859 : Blo 1613005 3877859 := bstep (se 1 (by rfl) ⟨2908394, by rfl⟩ : syracuseStep 3877859 = 5816789) B5816789
theorem B2419697 : Blo 1613005 2419697 := bstep (se 2 (by rfl) ⟨907386, by rfl⟩ : syracuseStep 2419697 = 1814773) B1814773
theorem B2722801 : Blo 1613005 2722801 := bstep (se 2 (by rfl) ⟨1021050, by rfl⟩ : syracuseStep 2722801 = 2042101) B2042101
theorem B2419715 : Blo 1613005 2419715 := bstep (se 1 (by rfl) ⟨1814786, by rfl⟩ : syracuseStep 2419715 = 3629573) B3629573
theorem B2722835 : Blo 1613005 2722835 := bstep (se 1 (by rfl) ⟨2042126, by rfl⟩ : syracuseStep 2722835 = 4084253) B4084253
theorem B2419745 : Blo 1613005 2419745 := bstep (se 2 (by rfl) ⟨907404, by rfl⟩ : syracuseStep 2419745 = 1814809) B1814809
theorem B2419763 : Blo 1613005 2419763 := bstep (se 1 (by rfl) ⟨1814822, by rfl⟩ : syracuseStep 2419763 = 3629645) B3629645
theorem B4598851 : Blo 1613005 4598851 := bstep (se 1 (by rfl) ⟨3449138, by rfl⟩ : syracuseStep 4598851 = 6898277) B6898277
theorem B2419793 : Blo 1613005 2419793 := bstep (se 2 (by rfl) ⟨907422, by rfl⟩ : syracuseStep 2419793 = 1814845) B1814845
theorem B2419811 : Blo 1613005 2419811 := bstep (se 1 (by rfl) ⟨1814858, by rfl⟩ : syracuseStep 2419811 = 3629717) B3629717
theorem B2182259 : Blo 1613005 2182259 := bstep (se 1 (by rfl) ⟨1636694, by rfl⟩ : syracuseStep 2182259 = 3273389) B3273389
theorem B2419841 : Blo 1613005 2419841 := bstep (se 2 (by rfl) ⟨907440, by rfl⟩ : syracuseStep 2419841 = 1814881) B1814881
theorem B1723523 : Blo 1613005 1723523 := bstep (se 1 (by rfl) ⟨1292642, by rfl⟩ : syracuseStep 1723523 = 2585285) B2585285
theorem B6130829 : Blo 1613005 6130829 := bstep (se 3 (by rfl) ⟨1149530, by rfl⟩ : syracuseStep 6130829 = 2299061) B2299061
theorem B3632273 : Blo 1613005 3632273 := bstep (se 2 (by rfl) ⟨1362102, by rfl⟩ : syracuseStep 3632273 = 2724205) B2724205
theorem B2419859 : Blo 1613005 2419859 := bstep (se 1 (by rfl) ⟨1814894, by rfl⟩ : syracuseStep 2419859 = 3629789) B3629789
theorem B2722963 : Blo 1613005 2722963 := bstep (se 1 (by rfl) ⟨2042222, by rfl⟩ : syracuseStep 2722963 = 4084445) B4084445
theorem B3632291 : Blo 1613005 3632291 := bstep (se 1 (by rfl) ⟨2724218, by rfl⟩ : syracuseStep 3632291 = 5448437) B5448437
theorem B2419889 : Blo 1613005 2419889 := bstep (se 2 (by rfl) ⟨907458, by rfl⟩ : syracuseStep 2419889 = 1814917) B1814917
theorem B2297011 : Blo 1613005 2297011 := bstep (se 1 (by rfl) ⟨1722758, by rfl⟩ : syracuseStep 2297011 = 3445517) B3445517
theorem B2419907 : Blo 1613005 2419907 := bstep (se 1 (by rfl) ⟨1814930, by rfl⟩ : syracuseStep 2419907 = 3629861) B3629861
theorem B2419937 : Blo 1613005 2419937 := bstep (se 2 (by rfl) ⟨907476, by rfl⟩ : syracuseStep 2419937 = 1814953) B1814953
theorem B2419955 : Blo 1613005 2419955 := bstep (se 1 (by rfl) ⟨1814966, by rfl⟩ : syracuseStep 2419955 = 3629933) B3629933
theorem B2043139 : Blo 1613005 2043139 := bstep (se 1 (by rfl) ⟨1532354, by rfl⟩ : syracuseStep 2043139 = 3064709) B3064709
theorem B2419985 : Blo 1613005 2419985 := bstep (se 2 (by rfl) ⟨907494, by rfl⟩ : syracuseStep 2419985 = 1814989) B1814989
theorem B2723105 : Blo 1613005 2723105 := bstep (se 2 (by rfl) ⟨1021164, by rfl⟩ : syracuseStep 2723105 = 2042329) B2042329
theorem B2420003 : Blo 1613005 2420003 := bstep (se 1 (by rfl) ⟨1815002, by rfl⟩ : syracuseStep 2420003 = 3630005) B3630005
theorem B2796865 : Blo 1613005 2796865 := bstep (se 2 (by rfl) ⟨1048824, by rfl⟩ : syracuseStep 2796865 = 2097649) B2097649
theorem B2420033 : Blo 1613005 2420033 := bstep (se 2 (by rfl) ⟨907512, by rfl⟩ : syracuseStep 2420033 = 1815025) B1815025
theorem B6892877 : Blo 1613005 6892877 := bstep (se 3 (by rfl) ⟨1292414, by rfl⟩ : syracuseStep 6892877 = 2584829) B2584829
theorem B2420051 : Blo 1613005 2420051 := bstep (se 1 (by rfl) ⟨1815038, by rfl⟩ : syracuseStep 2420051 = 3630077) B3630077
theorem B2452835 : Blo 1613005 2452835 := bstep (se 1 (by rfl) ⟨1839626, by rfl⟩ : syracuseStep 2452835 = 3679253) B3679253
theorem B2043235 : Blo 1613005 2043235 := bstep (se 1 (by rfl) ⟨1532426, by rfl⟩ : syracuseStep 2043235 = 3064853) B3064853
theorem B2420081 : Blo 1613005 2420081 := bstep (se 2 (by rfl) ⟨907530, by rfl⟩ : syracuseStep 2420081 = 1815061) B1815061
theorem B2420099 : Blo 1613005 2420099 := bstep (se 1 (by rfl) ⟨1815074, by rfl⟩ : syracuseStep 2420099 = 3630149) B3630149
theorem B2420129 : Blo 1613005 2420129 := bstep (se 2 (by rfl) ⟨907548, by rfl⟩ : syracuseStep 2420129 = 1815097) B1815097
theorem B2723233 : Blo 1613005 2723233 := bstep (se 2 (by rfl) ⟨1021212, by rfl⟩ : syracuseStep 2723233 = 2042425) B2042425
theorem B3632561 : Blo 1613005 3632561 := bstep (se 2 (by rfl) ⟨1362210, by rfl⟩ : syracuseStep 3632561 = 2724421) B2724421
theorem B2420147 : Blo 1613005 2420147 := bstep (se 1 (by rfl) ⟨1815110, by rfl⟩ : syracuseStep 2420147 = 3630221) B3630221
theorem B2723267 : Blo 1613005 2723267 := bstep (se 1 (by rfl) ⟨2042450, by rfl⟩ : syracuseStep 2723267 = 4084901) B4084901
theorem B3632579 : Blo 1613005 3632579 := bstep (se 1 (by rfl) ⟨2724434, by rfl⟩ : syracuseStep 3632579 = 5448869) B5448869
theorem B2420177 : Blo 1613005 2420177 := bstep (se 2 (by rfl) ⟨907566, by rfl⟩ : syracuseStep 2420177 = 1815133) B1815133
theorem B2452961 : Blo 1613005 2452961 := bstep (se 2 (by rfl) ⟨919860, by rfl⟩ : syracuseStep 2452961 = 1839721) B1839721
theorem B2420195 : Blo 1613005 2420195 := bstep (se 1 (by rfl) ⟨1815146, by rfl⟩ : syracuseStep 2420195 = 3630293) B3630293
theorem B2420225 : Blo 1613005 2420225 := bstep (se 2 (by rfl) ⟨907584, by rfl⟩ : syracuseStep 2420225 = 1815169) B1815169
theorem B3878417 : Blo 1613005 3878417 := bstep (se 2 (by rfl) ⟨1454406, by rfl⟩ : syracuseStep 3878417 = 2908813) B2908813
theorem B2330129 : Blo 1613005 2330129 := bstep (se 2 (by rfl) ⟨873798, by rfl⟩ : syracuseStep 2330129 = 1747597) B1747597
theorem B2420243 : Blo 1613005 2420243 := bstep (se 1 (by rfl) ⟨1815182, by rfl⟩ : syracuseStep 2420243 = 3630365) B3630365
theorem B2420273 : Blo 1613005 2420273 := bstep (se 2 (by rfl) ⟨907602, by rfl⟩ : syracuseStep 2420273 = 1815205) B1815205
theorem B2420291 : Blo 1613005 2420291 := bstep (se 1 (by rfl) ⟨1815218, by rfl⟩ : syracuseStep 2420291 = 3630437) B3630437
theorem B2723395 : Blo 1613005 2723395 := bstep (se 1 (by rfl) ⟨2042546, by rfl⟩ : syracuseStep 2723395 = 4085093) B4085093
theorem B7179853 : Blo 1613005 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B4083281 : Blo 1613005 4083281 := bstep (se 2 (by rfl) ⟨1531230, by rfl⟩ : syracuseStep 4083281 = 3062461) B3062461
theorem B2420321 : Blo 1613005 2420321 := bstep (se 2 (by rfl) ⟨907620, by rfl⟩ : syracuseStep 2420321 = 1815241) B1815241
theorem B2584163 : Blo 1613005 2584163 := bstep (se 1 (by rfl) ⟨1938122, by rfl⟩ : syracuseStep 2584163 = 3876245) B3876245
theorem B5820017 : Blo 1613005 5820017 := bstep (se 2 (by rfl) ⟨2182506, by rfl⟩ : syracuseStep 5820017 = 4365013) B4365013
theorem B2420339 : Blo 1613005 2420339 := bstep (se 1 (by rfl) ⟨1815254, by rfl⟩ : syracuseStep 2420339 = 3630509) B3630509
theorem B4083331 : Blo 1613005 4083331 := bstep (se 1 (by rfl) ⟨3062498, by rfl⟩ : syracuseStep 4083331 = 6124997) B6124997
theorem B2420369 : Blo 1613005 2420369 := bstep (se 2 (by rfl) ⟨907638, by rfl⟩ : syracuseStep 2420369 = 1815277) B1815277
theorem B2297489 : Blo 1613005 2297489 := bstep (se 2 (by rfl) ⟨861558, by rfl⟩ : syracuseStep 2297489 = 1723117) B1723117
theorem B2420387 : Blo 1613005 2420387 := bstep (se 1 (by rfl) ⟨1815290, by rfl⟩ : syracuseStep 2420387 = 3630581) B3630581
theorem B9817777 : Blo 1613005 9817777 := bstep (se 2 (by rfl) ⟨3681666, by rfl⟩ : syracuseStep 9817777 = 7363333) B7363333
theorem B2420417 : Blo 1613005 2420417 := bstep (se 2 (by rfl) ⟨907656, by rfl⟩ : syracuseStep 2420417 = 1815313) B1815313
theorem B12431045 : Blo 1613005 12431045 := bstep (se 4 (by rfl) ⟨1165410, by rfl⟩ : syracuseStep 12431045 = 2330821) B2330821
theorem B2723537 : Blo 1613005 2723537 := bstep (se 2 (by rfl) ⟨1021326, by rfl⟩ : syracuseStep 2723537 = 2042653) B2042653
theorem B3632849 : Blo 1613005 3632849 := bstep (se 2 (by rfl) ⟨1362318, by rfl⟩ : syracuseStep 3632849 = 2724637) B2724637
theorem B2420435 : Blo 1613005 2420435 := bstep (se 1 (by rfl) ⟨1815326, by rfl⟩ : syracuseStep 2420435 = 3630653) B3630653
theorem B3632867 : Blo 1613005 3632867 := bstep (se 1 (by rfl) ⟨2724650, by rfl⟩ : syracuseStep 3632867 = 5449301) B5449301
theorem B4484845 : Blo 1613005 4484845 := bstep (se 3 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 4484845 = 1681817) B1681817
theorem B2420465 : Blo 1613005 2420465 := bstep (se 2 (by rfl) ⟨907674, by rfl⟩ : syracuseStep 2420465 = 1815349) B1815349
theorem B2420483 : Blo 1613005 2420483 := bstep (se 1 (by rfl) ⟨1815362, by rfl⟩ : syracuseStep 2420483 = 3630725) B3630725
theorem B2297603 : Blo 1613005 2297603 := bstep (se 1 (by rfl) ⟨1723202, by rfl⟩ : syracuseStep 2297603 = 3446405) B3446405
theorem B4361987 : Blo 1613005 4361987 := bstep (se 1 (by rfl) ⟨3271490, by rfl⟩ : syracuseStep 4361987 = 6542981) B6542981
theorem B4083473 : Blo 1613005 4083473 := bstep (se 2 (by rfl) ⟨1531302, by rfl⟩ : syracuseStep 4083473 = 3062605) B3062605
theorem B235523861 : Blo 1613005 235523861 := bstep (se 6 (by rfl) ⟨5520090, by rfl⟩ : syracuseStep 235523861 = 11040181) B11040181
theorem B2420513 : Blo 1613005 2420513 := bstep (se 2 (by rfl) ⟨907692, by rfl⟩ : syracuseStep 2420513 = 1815385) B1815385
theorem B3878705 : Blo 1613005 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B2420531 : Blo 1613005 2420531 := bstep (se 1 (by rfl) ⟨1815398, by rfl⟩ : syracuseStep 2420531 = 3630797) B3630797
theorem B22073141 : Blo 1613005 22073141 := bstep (se 5 (by rfl) ⟨1034678, by rfl⟩ : syracuseStep 22073141 = 2069357) B2069357
theorem B2420561 : Blo 1613005 2420561 := bstep (se 2 (by rfl) ⟨907710, by rfl⟩ : syracuseStep 2420561 = 1815421) B1815421
theorem B2723665 : Blo 1613005 2723665 := bstep (se 2 (by rfl) ⟨1021374, by rfl⟩ : syracuseStep 2723665 = 2042749) B2042749
theorem B2297683 : Blo 1613005 2297683 := bstep (se 1 (by rfl) ⟨1723262, by rfl⟩ : syracuseStep 2297683 = 3446525) B3446525
theorem B2043731 : Blo 1613005 2043731 := bstep (se 1 (by rfl) ⟨1532798, by rfl⟩ : syracuseStep 2043731 = 3065597) B3065597
theorem B2420579 : Blo 1613005 2420579 := bstep (se 1 (by rfl) ⟨1815434, by rfl⟩ : syracuseStep 2420579 = 3630869) B3630869
theorem B12758897 : Blo 1613005 12758897 := bstep (se 2 (by rfl) ⟨4784586, by rfl⟩ : syracuseStep 12758897 = 9569173) B9569173
theorem B2723699 : Blo 1613005 2723699 := bstep (se 1 (by rfl) ⟨2042774, by rfl⟩ : syracuseStep 2723699 = 4085549) B4085549
theorem B1724275 : Blo 1613005 1724275 := bstep (se 1 (by rfl) ⟨1293206, by rfl⟩ : syracuseStep 1724275 = 2586413) B2586413
theorem B2420609 : Blo 1613005 2420609 := bstep (se 2 (by rfl) ⟨907728, by rfl⟩ : syracuseStep 2420609 = 1815457) B1815457
theorem B2420627 : Blo 1613005 2420627 := bstep (se 1 (by rfl) ⟨1815470, by rfl⟩ : syracuseStep 2420627 = 3630941) B3630941
theorem B2420657 : Blo 1613005 2420657 := bstep (se 2 (by rfl) ⟨907746, by rfl⟩ : syracuseStep 2420657 = 1815493) B1815493
theorem B8171441 : Blo 1613005 8171441 := bstep (se 2 (by rfl) ⟨3064290, by rfl⟩ : syracuseStep 8171441 = 6128581) B6128581
theorem B2420675 : Blo 1613005 2420675 := bstep (se 1 (by rfl) ⟨1815506, by rfl⟩ : syracuseStep 2420675 = 3631013) B3631013
theorem B2420705 : Blo 1613005 2420705 := bstep (se 2 (by rfl) ⟨907764, by rfl⟩ : syracuseStep 2420705 = 1815529) B1815529
theorem B9949169 : Blo 1613005 9949169 := bstep (se 2 (by rfl) ⟨3730938, by rfl⟩ : syracuseStep 9949169 = 7461877) B7461877
theorem B3633137 : Blo 1613005 3633137 := bstep (se 2 (by rfl) ⟨1362426, by rfl⟩ : syracuseStep 3633137 = 2724853) B2724853
theorem B2420723 : Blo 1613005 2420723 := bstep (se 1 (by rfl) ⟨1815542, by rfl⟩ : syracuseStep 2420723 = 3631085) B3631085
theorem B2723827 : Blo 1613005 2723827 := bstep (se 1 (by rfl) ⟨2042870, by rfl⟩ : syracuseStep 2723827 = 4085741) B4085741
theorem B3543043 : Blo 1613005 3543043 := bstep (se 1 (by rfl) ⟨2657282, by rfl⟩ : syracuseStep 3543043 = 5314565) B5314565
theorem B3633155 : Blo 1613005 3633155 := bstep (se 1 (by rfl) ⟨2724866, by rfl⟩ : syracuseStep 3633155 = 5449733) B5449733
theorem B22073357 : Blo 1613005 22073357 := bstep (se 3 (by rfl) ⟨4138754, by rfl⟩ : syracuseStep 22073357 = 8277509) B8277509
theorem B2420753 : Blo 1613005 2420753 := bstep (se 2 (by rfl) ⟨907782, by rfl⟩ : syracuseStep 2420753 = 1815565) B1815565
theorem B2420771 : Blo 1613005 2420771 := bstep (se 1 (by rfl) ⟨1815578, by rfl⟩ : syracuseStep 2420771 = 3631157) B3631157
theorem B2420801 : Blo 1613005 2420801 := bstep (se 2 (by rfl) ⟨907800, by rfl⟩ : syracuseStep 2420801 = 1815601) B1815601
theorem B2420819 : Blo 1613005 2420819 := bstep (se 1 (by rfl) ⟨1815614, by rfl⟩ : syracuseStep 2420819 = 3631229) B3631229
theorem B2420849 : Blo 1613005 2420849 := bstep (se 2 (by rfl) ⟨907818, by rfl⟩ : syracuseStep 2420849 = 1815637) B1815637
theorem B2723969 : Blo 1613005 2723969 := bstep (se 2 (by rfl) ⟨1021488, by rfl⟩ : syracuseStep 2723969 = 2042977) B2042977
theorem B2420867 : Blo 1613005 2420867 := bstep (se 1 (by rfl) ⟨1815650, by rfl⟩ : syracuseStep 2420867 = 3631301) B3631301
theorem B2420897 : Blo 1613005 2420897 := bstep (se 2 (by rfl) ⟨907836, by rfl⟩ : syracuseStep 2420897 = 1815673) B1815673
theorem B2420915 : Blo 1613005 2420915 := bstep (se 1 (by rfl) ⟨1815686, by rfl⟩ : syracuseStep 2420915 = 3631373) B3631373
theorem B2420945 : Blo 1613005 2420945 := bstep (se 2 (by rfl) ⟨907854, by rfl⟩ : syracuseStep 2420945 = 1815709) B1815709
theorem B1814755 : Blo 1613005 1814755 := bstep (se 1 (by rfl) ⟨1361066, by rfl⟩ : syracuseStep 1814755 = 2722133) B2722133
theorem B2420963 : Blo 1613005 2420963 := bstep (se 1 (by rfl) ⟨1815722, by rfl⟩ : syracuseStep 2420963 = 3631445) B3631445
theorem B2420993 : Blo 1613005 2420993 := bstep (se 2 (by rfl) ⟨907872, by rfl⟩ : syracuseStep 2420993 = 1815745) B1815745
theorem B2724097 : Blo 1613005 2724097 := bstep (se 2 (by rfl) ⟨1021536, by rfl⟩ : syracuseStep 2724097 = 2043073) B2043073
theorem B3633425 : Blo 1613005 3633425 := bstep (se 2 (by rfl) ⟨1362534, by rfl⟩ : syracuseStep 3633425 = 2725069) B2725069
theorem B2421011 : Blo 1613005 2421011 := bstep (se 1 (by rfl) ⟨1815758, by rfl⟩ : syracuseStep 2421011 = 3631517) B3631517
theorem B2724131 : Blo 1613005 2724131 := bstep (se 1 (by rfl) ⟨2043098, by rfl⟩ : syracuseStep 2724131 = 4086197) B4086197
theorem B3633443 : Blo 1613005 3633443 := bstep (se 1 (by rfl) ⟨2725082, by rfl⟩ : syracuseStep 3633443 = 5450165) B5450165
theorem B2421041 : Blo 1613005 2421041 := bstep (se 2 (by rfl) ⟨907890, by rfl⟩ : syracuseStep 2421041 = 1815781) B1815781
theorem B2421059 : Blo 1613005 2421059 := bstep (se 1 (by rfl) ⟨1815794, by rfl⟩ : syracuseStep 2421059 = 3631589) B3631589
theorem B2421089 : Blo 1613005 2421089 := bstep (se 2 (by rfl) ⟨907908, by rfl⟩ : syracuseStep 2421089 = 1815817) B1815817
theorem B1814899 : Blo 1613005 1814899 := bstep (se 1 (by rfl) ⟨1361174, by rfl⟩ : syracuseStep 1814899 = 2722349) B2722349
theorem B2421107 : Blo 1613005 2421107 := bstep (se 1 (by rfl) ⟨1815830, by rfl⟩ : syracuseStep 2421107 = 3631661) B3631661
theorem B2298241 : Blo 1613005 2298241 := bstep (se 2 (by rfl) ⟨861840, by rfl⟩ : syracuseStep 2298241 = 1723681) B1723681
theorem B5173645 : Blo 1613005 5173645 := bstep (se 3 (by rfl) ⟨970058, by rfl⟩ : syracuseStep 5173645 = 1940117) B1940117
theorem B2421137 : Blo 1613005 2421137 := bstep (se 2 (by rfl) ⟨907926, by rfl⟩ : syracuseStep 2421137 = 1815853) B1815853
theorem B2421155 : Blo 1613005 2421155 := bstep (se 1 (by rfl) ⟨1815866, by rfl⟩ : syracuseStep 2421155 = 3631733) B3631733
theorem B2724259 : Blo 1613005 2724259 := bstep (se 1 (by rfl) ⟨2043194, by rfl⟩ : syracuseStep 2724259 = 4086389) B4086389
theorem B2585009 : Blo 1613005 2585009 := bstep (se 2 (by rfl) ⟨969378, by rfl⟩ : syracuseStep 2585009 = 1938757) B1938757
theorem B2421185 : Blo 1613005 2421185 := bstep (se 2 (by rfl) ⟨907944, by rfl⟩ : syracuseStep 2421185 = 1815889) B1815889
theorem B2421203 : Blo 1613005 2421203 := bstep (se 1 (by rfl) ⟨1815902, by rfl⟩ : syracuseStep 2421203 = 3631805) B3631805
theorem B2421233 : Blo 1613005 2421233 := bstep (se 2 (by rfl) ⟨907962, by rfl⟩ : syracuseStep 2421233 = 1815925) B1815925
theorem B1815043 : Blo 1613005 1815043 := bstep (se 1 (by rfl) ⟨1361282, by rfl⟩ : syracuseStep 1815043 = 2722565) B2722565
theorem B2454019 : Blo 1613005 2454019 := bstep (se 1 (by rfl) ⟨1840514, by rfl⟩ : syracuseStep 2454019 = 3681029) B3681029
theorem B2421251 : Blo 1613005 2421251 := bstep (se 1 (by rfl) ⟨1815938, by rfl⟩ : syracuseStep 2421251 = 3631877) B3631877
theorem B6214157 : Blo 1613005 6214157 := bstep (se 3 (by rfl) ⟨1165154, by rfl⟩ : syracuseStep 6214157 = 2330309) B2330309
theorem B2421281 : Blo 1613005 2421281 := bstep (se 2 (by rfl) ⟨907980, by rfl⟩ : syracuseStep 2421281 = 1815961) B1815961
theorem B2585137 : Blo 1613005 2585137 := bstep (se 2 (by rfl) ⟨969426, by rfl⟩ : syracuseStep 2585137 = 1938853) B1938853
theorem B3494449 : Blo 1613005 3494449 := bstep (se 2 (by rfl) ⟨1310418, by rfl⟩ : syracuseStep 3494449 = 2620837) B2620837
theorem B2421299 : Blo 1613005 2421299 := bstep (se 1 (by rfl) ⟨1815974, by rfl⟩ : syracuseStep 2421299 = 3631949) B3631949
theorem B2724401 : Blo 1613005 2724401 := bstep (se 2 (by rfl) ⟨1021650, by rfl⟩ : syracuseStep 2724401 = 2043301) B2043301
theorem B3633713 : Blo 1613005 3633713 := bstep (se 2 (by rfl) ⟨1362642, by rfl⟩ : syracuseStep 3633713 = 2725285) B2725285
theorem B3633731 : Blo 1613005 3633731 := bstep (se 1 (by rfl) ⟨2725298, by rfl⟩ : syracuseStep 3633731 = 5450597) B5450597
theorem B2421329 : Blo 1613005 2421329 := bstep (se 2 (by rfl) ⟨907998, by rfl⟩ : syracuseStep 2421329 = 1815997) B1815997
theorem B2421347 : Blo 1613005 2421347 := bstep (se 1 (by rfl) ⟨1816010, by rfl⟩ : syracuseStep 2421347 = 3632021) B3632021
theorem B15520355 : Blo 1613005 15520355 := bstep (se 1 (by rfl) ⟨11640266, by rfl⟩ : syracuseStep 15520355 = 23280533) B23280533
theorem B11629169 : Blo 1613005 11629169 := bstep (se 2 (by rfl) ⟨4360938, by rfl⟩ : syracuseStep 11629169 = 8721877) B8721877
theorem B2585201 : Blo 1613005 2585201 := bstep (se 2 (by rfl) ⟨969450, by rfl⟩ : syracuseStep 2585201 = 1938901) B1938901
theorem B2421377 : Blo 1613005 2421377 := bstep (se 2 (by rfl) ⟨908016, by rfl⟩ : syracuseStep 2421377 = 1816033) B1816033
theorem B1815187 : Blo 1613005 1815187 := bstep (se 1 (by rfl) ⟨1361390, by rfl⟩ : syracuseStep 1815187 = 2722781) B2722781
theorem B2421395 : Blo 1613005 2421395 := bstep (se 1 (by rfl) ⟨1816046, by rfl⟩ : syracuseStep 2421395 = 3632093) B3632093
theorem B2421425 : Blo 1613005 2421425 := bstep (se 2 (by rfl) ⟨908034, by rfl⟩ : syracuseStep 2421425 = 1816069) B1816069
theorem B2724529 : Blo 1613005 2724529 := bstep (se 2 (by rfl) ⟨1021698, by rfl⟩ : syracuseStep 2724529 = 2043397) B2043397
theorem B2421443 : Blo 1613005 2421443 := bstep (se 1 (by rfl) ⟨1816082, by rfl⟩ : syracuseStep 2421443 = 3632165) B3632165
theorem B2724563 : Blo 1613005 2724563 := bstep (se 1 (by rfl) ⟨2043422, by rfl⟩ : syracuseStep 2724563 = 4086845) B4086845
theorem B2421473 : Blo 1613005 2421473 := bstep (se 2 (by rfl) ⟨908052, by rfl⟩ : syracuseStep 2421473 = 1816105) B1816105
theorem B5444333 : Blo 1613005 5444333 := bstep (se 3 (by rfl) ⟨1020812, by rfl⟩ : syracuseStep 5444333 = 2041625) B2041625
theorem B4084465 : Blo 1613005 4084465 := bstep (se 2 (by rfl) ⟨1531674, by rfl⟩ : syracuseStep 4084465 = 3063349) B3063349
theorem B2421491 : Blo 1613005 2421491 := bstep (se 1 (by rfl) ⟨1816118, by rfl⟩ : syracuseStep 2421491 = 3632237) B3632237
theorem B2421521 : Blo 1613005 2421521 := bstep (se 2 (by rfl) ⟨908070, by rfl⟩ : syracuseStep 2421521 = 1816141) B1816141
theorem B5444387 : Blo 1613005 5444387 := bstep (se 1 (by rfl) ⟨4083290, by rfl⟩ : syracuseStep 5444387 = 8166581) B8166581
theorem B1815331 : Blo 1613005 1815331 := bstep (se 1 (by rfl) ⟨1361498, by rfl⟩ : syracuseStep 1815331 = 2722997) B2722997
theorem B2421539 : Blo 1613005 2421539 := bstep (se 1 (by rfl) ⟨1816154, by rfl⟩ : syracuseStep 2421539 = 3632309) B3632309
theorem B2421569 : Blo 1613005 2421569 := bstep (se 2 (by rfl) ⟨908088, by rfl⟩ : syracuseStep 2421569 = 1816177) B1816177
theorem B2421587 : Blo 1613005 2421587 := bstep (se 1 (by rfl) ⟨1816190, by rfl⟩ : syracuseStep 2421587 = 3632381) B3632381
theorem B2724691 : Blo 1613005 2724691 := bstep (se 1 (by rfl) ⟨2043518, by rfl⟩ : syracuseStep 2724691 = 4087037) B4087037
theorem B2421617 : Blo 1613005 2421617 := bstep (se 2 (by rfl) ⟨908106, by rfl⟩ : syracuseStep 2421617 = 1816213) B1816213
theorem B2421635 : Blo 1613005 2421635 := bstep (se 1 (by rfl) ⟨1816226, by rfl⟩ : syracuseStep 2421635 = 3632453) B3632453
theorem B2421665 : Blo 1613005 2421665 := bstep (se 2 (by rfl) ⟨908124, by rfl⟩ : syracuseStep 2421665 = 1816249) B1816249
theorem B1815475 : Blo 1613005 1815475 := bstep (se 1 (by rfl) ⟨1361606, by rfl⟩ : syracuseStep 1815475 = 2723213) B2723213
theorem B2421683 : Blo 1613005 2421683 := bstep (se 1 (by rfl) ⟨1816262, by rfl⟩ : syracuseStep 2421683 = 3632525) B3632525
theorem B2421713 : Blo 1613005 2421713 := bstep (se 2 (by rfl) ⟨908142, by rfl⟩ : syracuseStep 2421713 = 1816285) B1816285
theorem B2724833 : Blo 1613005 2724833 := bstep (se 2 (by rfl) ⟨1021812, by rfl⟩ : syracuseStep 2724833 = 2043625) B2043625
theorem B2421731 : Blo 1613005 2421731 := bstep (se 1 (by rfl) ⟨1816298, by rfl⟩ : syracuseStep 2421731 = 3632597) B3632597
theorem B2421761 : Blo 1613005 2421761 := bstep (se 2 (by rfl) ⟨908160, by rfl⟩ : syracuseStep 2421761 = 1816321) B1816321
theorem B4084739 : Blo 1613005 4084739 := bstep (se 1 (by rfl) ⟨3063554, by rfl⟩ : syracuseStep 4084739 = 6127109) B6127109
theorem B2421779 : Blo 1613005 2421779 := bstep (se 1 (by rfl) ⟨1816334, by rfl⟩ : syracuseStep 2421779 = 3632669) B3632669
theorem B5444657 : Blo 1613005 5444657 := bstep (se 2 (by rfl) ⟨2041746, by rfl⟩ : syracuseStep 5444657 = 4083493) B4083493
theorem B2421809 : Blo 1613005 2421809 := bstep (se 2 (by rfl) ⟨908178, by rfl⟩ : syracuseStep 2421809 = 1816357) B1816357
theorem B1815619 : Blo 1613005 1815619 := bstep (se 1 (by rfl) ⟨1361714, by rfl⟩ : syracuseStep 1815619 = 2723429) B2723429
theorem B2421827 : Blo 1613005 2421827 := bstep (se 1 (by rfl) ⟨1816370, by rfl⟩ : syracuseStep 2421827 = 3632741) B3632741
theorem B2298947 : Blo 1613005 2298947 := bstep (se 1 (by rfl) ⟨1724210, by rfl⟩ : syracuseStep 2298947 = 3448421) B3448421
theorem B3445841 : Blo 1613005 3445841 := bstep (se 2 (by rfl) ⟨1292190, by rfl⟩ : syracuseStep 3445841 = 2584381) B2584381
theorem B2421857 : Blo 1613005 2421857 := bstep (se 2 (by rfl) ⟨908196, by rfl⟩ : syracuseStep 2421857 = 1816393) B1816393
theorem B2724961 : Blo 1613005 2724961 := bstep (se 2 (by rfl) ⟨1021860, by rfl⟩ : syracuseStep 2724961 = 2043721) B2043721
theorem B2421875 : Blo 1613005 2421875 := bstep (se 1 (by rfl) ⟨1816406, by rfl⟩ : syracuseStep 2421875 = 3632813) B3632813
theorem B2724995 : Blo 1613005 2724995 := bstep (se 1 (by rfl) ⟨2043746, by rfl⟩ : syracuseStep 2724995 = 4087493) B4087493
theorem B2421905 : Blo 1613005 2421905 := bstep (se 2 (by rfl) ⟨908214, by rfl⟩ : syracuseStep 2421905 = 1816429) B1816429
theorem B2421923 : Blo 1613005 2421923 := bstep (se 1 (by rfl) ⟨1816442, by rfl⟩ : syracuseStep 2421923 = 3632885) B3632885
theorem B4084931 : Blo 1613005 4084931 := bstep (se 1 (by rfl) ⟨3063698, by rfl⟩ : syracuseStep 4084931 = 6127397) B6127397
theorem B2421953 : Blo 1613005 2421953 := bstep (se 2 (by rfl) ⟨908232, by rfl⟩ : syracuseStep 2421953 = 1816465) B1816465
theorem B1815763 : Blo 1613005 1815763 := bstep (se 1 (by rfl) ⟨1361822, by rfl⟩ : syracuseStep 1815763 = 2723645) B2723645
theorem B2421971 : Blo 1613005 2421971 := bstep (se 1 (by rfl) ⟨1816478, by rfl⟩ : syracuseStep 2421971 = 3632957) B3632957
theorem B2422001 : Blo 1613005 2422001 := bstep (se 2 (by rfl) ⟨908250, by rfl⟩ : syracuseStep 2422001 = 1816501) B1816501
theorem B2422019 : Blo 1613005 2422019 := bstep (se 1 (by rfl) ⟨1816514, by rfl⟩ : syracuseStep 2422019 = 3633029) B3633029
theorem B2725123 : Blo 1613005 2725123 := bstep (se 1 (by rfl) ⟨2043842, by rfl⟩ : syracuseStep 2725123 = 4087685) B4087685
theorem B2422049 : Blo 1613005 2422049 := bstep (se 2 (by rfl) ⟨908268, by rfl⟩ : syracuseStep 2422049 = 1816537) B1816537
theorem B2422067 : Blo 1613005 2422067 := bstep (se 1 (by rfl) ⟨1816550, by rfl⟩ : syracuseStep 2422067 = 3633101) B3633101
theorem B2422097 : Blo 1613005 2422097 := bstep (se 2 (by rfl) ⟨908286, by rfl⟩ : syracuseStep 2422097 = 1816573) B1816573
theorem B1815907 : Blo 1613005 1815907 := bstep (se 1 (by rfl) ⟨1361930, by rfl⟩ : syracuseStep 1815907 = 2723861) B2723861
theorem B8172899 : Blo 1613005 8172899 := bstep (se 1 (by rfl) ⟨6129674, by rfl⟩ : syracuseStep 8172899 = 12259349) B12259349
theorem B2422115 : Blo 1613005 2422115 := bstep (se 1 (by rfl) ⟨1816586, by rfl⟩ : syracuseStep 2422115 = 3633173) B3633173
theorem B2422145 : Blo 1613005 2422145 := bstep (se 2 (by rfl) ⟨908304, by rfl⟩ : syracuseStep 2422145 = 1816609) B1816609
theorem B2725265 : Blo 1613005 2725265 := bstep (se 2 (by rfl) ⟨1021974, by rfl⟩ : syracuseStep 2725265 = 2043949) B2043949
theorem B2454931 : Blo 1613005 2454931 := bstep (se 1 (by rfl) ⟨1841198, by rfl⟩ : syracuseStep 2454931 = 3682397) B3682397
theorem B2422163 : Blo 1613005 2422163 := bstep (se 1 (by rfl) ⟨1816622, by rfl⟩ : syracuseStep 2422163 = 3633245) B3633245
theorem B2422193 : Blo 1613005 2422193 := bstep (se 2 (by rfl) ⟨908322, by rfl⟩ : syracuseStep 2422193 = 1816645) B1816645
theorem B19641781 : Blo 1613005 19641781 := bstep (se 5 (by rfl) ⟨920708, by rfl⟩ : syracuseStep 19641781 = 1841417) B1841417
theorem B2422211 : Blo 1613005 2422211 := bstep (se 1 (by rfl) ⟨1816658, by rfl⟩ : syracuseStep 2422211 = 3633317) B3633317
theorem B7362019 : Blo 1613005 7362019 := bstep (se 1 (by rfl) ⟨5521514, by rfl⟩ : syracuseStep 7362019 = 11043029) B11043029
theorem B2422241 : Blo 1613005 2422241 := bstep (se 2 (by rfl) ⟨908340, by rfl⟩ : syracuseStep 2422241 = 1816681) B1816681
theorem B1816051 : Blo 1613005 1816051 := bstep (se 1 (by rfl) ⟨1362038, by rfl⟩ : syracuseStep 1816051 = 2724077) B2724077
theorem B2422259 : Blo 1613005 2422259 := bstep (se 1 (by rfl) ⟨1816694, by rfl⟩ : syracuseStep 2422259 = 3633389) B3633389
theorem B2422289 : Blo 1613005 2422289 := bstep (se 2 (by rfl) ⟨908358, by rfl⟩ : syracuseStep 2422289 = 1816717) B1816717
theorem B2422307 : Blo 1613005 2422307 := bstep (se 1 (by rfl) ⟨1816730, by rfl⟩ : syracuseStep 2422307 = 3633461) B3633461
theorem B2422337 : Blo 1613005 2422337 := bstep (se 2 (by rfl) ⟨908376, by rfl⟩ : syracuseStep 2422337 = 1816753) B1816753
theorem B5445197 : Blo 1613005 5445197 := bstep (se 3 (by rfl) ⟨1020974, by rfl⟩ : syracuseStep 5445197 = 2041949) B2041949
theorem B2422355 : Blo 1613005 2422355 := bstep (se 1 (by rfl) ⟨1816766, by rfl⟩ : syracuseStep 2422355 = 3633533) B3633533
theorem B2422385 : Blo 1613005 2422385 := bstep (se 2 (by rfl) ⟨908394, by rfl⟩ : syracuseStep 2422385 = 1816789) B1816789
theorem B5445251 : Blo 1613005 5445251 := bstep (se 1 (by rfl) ⟨4083938, by rfl⟩ : syracuseStep 5445251 = 8167877) B8167877
theorem B1816195 : Blo 1613005 1816195 := bstep (se 1 (by rfl) ⟨1362146, by rfl⟩ : syracuseStep 1816195 = 2724293) B2724293
theorem B2422403 : Blo 1613005 2422403 := bstep (se 1 (by rfl) ⟨1816802, by rfl⟩ : syracuseStep 2422403 = 3633605) B3633605
theorem B4593293 : Blo 1613005 4593293 := bstep (se 3 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 4593293 = 1722485) B1722485
theorem B2586259 : Blo 1613005 2586259 := bstep (se 1 (by rfl) ⟨1939694, by rfl⟩ : syracuseStep 2586259 = 3879389) B3879389
theorem B2422433 : Blo 1613005 2422433 := bstep (se 2 (by rfl) ⟨908412, by rfl⟩ : syracuseStep 2422433 = 1816825) B1816825
theorem B2422451 : Blo 1613005 2422451 := bstep (se 1 (by rfl) ⟨1816838, by rfl⟩ : syracuseStep 2422451 = 3633677) B3633677
theorem B4593361 : Blo 1613005 4593361 := bstep (se 2 (by rfl) ⟨1722510, by rfl⟩ : syracuseStep 4593361 = 3445021) B3445021
theorem B2422481 : Blo 1613005 2422481 := bstep (se 2 (by rfl) ⟨908430, by rfl⟩ : syracuseStep 2422481 = 1816861) B1816861
theorem B2422499 : Blo 1613005 2422499 := bstep (se 1 (by rfl) ⟨1816874, by rfl⟩ : syracuseStep 2422499 = 3633749) B3633749
theorem B1816339 : Blo 1613005 1816339 := bstep (se 1 (by rfl) ⟨1362254, by rfl⟩ : syracuseStep 1816339 = 2724509) B2724509
theorem B6125453 : Blo 1613005 6125453 := bstep (se 3 (by rfl) ⟨1148522, by rfl⟩ : syracuseStep 6125453 = 2297045) B2297045
theorem B5445521 : Blo 1613005 5445521 := bstep (se 2 (by rfl) ⟨2042070, by rfl⟩ : syracuseStep 5445521 = 4084141) B4084141
theorem B1816483 : Blo 1613005 1816483 := bstep (se 1 (by rfl) ⟨1362362, by rfl⟩ : syracuseStep 1816483 = 2724725) B2724725
theorem B3446705 : Blo 1613005 3446705 := bstep (se 2 (by rfl) ⟨1292514, by rfl⟩ : syracuseStep 3446705 = 2585029) B2585029
theorem B10360781 : Blo 1613005 10360781 := bstep (se 3 (by rfl) ⟨1942646, by rfl⟩ : syracuseStep 10360781 = 3885293) B3885293
theorem B4593635 : Blo 1613005 4593635 := bstep (se 1 (by rfl) ⟨3445226, by rfl⟩ : syracuseStep 4593635 = 6890453) B6890453
theorem B10344419 : Blo 1613005 10344419 := bstep (se 1 (by rfl) ⟨7758314, by rfl⟩ : syracuseStep 10344419 = 15516629) B15516629
theorem B10336241 : Blo 1613005 10336241 := bstep (se 2 (by rfl) ⟨3876090, by rfl⟩ : syracuseStep 10336241 = 7752181) B7752181
theorem B1816627 : Blo 1613005 1816627 := bstep (se 1 (by rfl) ⟨1362470, by rfl⟩ : syracuseStep 1816627 = 2724941) B2724941
theorem B4085873 : Blo 1613005 4085873 := bstep (se 2 (by rfl) ⟨1532202, by rfl⟩ : syracuseStep 4085873 = 3064405) B3064405
theorem B8173709 : Blo 1613005 8173709 := bstep (se 3 (by rfl) ⟨1532570, by rfl⟩ : syracuseStep 8173709 = 3065141) B3065141
theorem B4085923 : Blo 1613005 4085923 := bstep (se 1 (by rfl) ⟨3064442, by rfl⟩ : syracuseStep 4085923 = 6128885) B6128885
theorem B1816771 : Blo 1613005 1816771 := bstep (se 1 (by rfl) ⟨1362578, by rfl⟩ : syracuseStep 1816771 = 2725157) B2725157
theorem B6543665 : Blo 1613005 6543665 := bstep (se 2 (by rfl) ⟨2453874, by rfl⟩ : syracuseStep 6543665 = 4907749) B4907749
theorem B4086065 : Blo 1613005 4086065 := bstep (se 2 (by rfl) ⟨1532274, by rfl⟩ : syracuseStep 4086065 = 3064549) B3064549
theorem B2619811 : Blo 1613005 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B5446061 : Blo 1613005 5446061 := bstep (se 3 (by rfl) ⟨1021136, by rfl⟩ : syracuseStep 5446061 = 2042273) B2042273
theorem B1939891 : Blo 1613005 1939891 := bstep (se 1 (by rfl) ⟨1454918, by rfl⟩ : syracuseStep 1939891 = 2909837) B2909837
theorem B3062225 : Blo 1613005 3062225 := bstep (se 2 (by rfl) ⟨1148334, by rfl⟩ : syracuseStep 3062225 = 2296669) B2296669
theorem B5446115 : Blo 1613005 5446115 := bstep (se 1 (by rfl) ⟨4084586, by rfl⟩ : syracuseStep 5446115 = 8169173) B8169173
theorem B11049443 : Blo 1613005 11049443 := bstep (se 1 (by rfl) ⟨8287082, by rfl⟩ : syracuseStep 11049443 = 16574165) B16574165
theorem B5167597 : Blo 1613005 5167597 := bstep (se 3 (by rfl) ⟨968924, by rfl⟩ : syracuseStep 5167597 = 1937849) B1937849
theorem B1939987 : Blo 1613005 1939987 := bstep (se 1 (by rfl) ⟨1454990, by rfl⟩ : syracuseStep 1939987 = 2909981) B2909981
theorem B39254669 : Blo 1613005 39254669 := bstep (se 3 (by rfl) ⟨7360250, by rfl⟩ : syracuseStep 39254669 = 14720501) B14720501
theorem B1940131 : Blo 1613005 1940131 := bstep (se 1 (by rfl) ⟨1455098, by rfl⟩ : syracuseStep 1940131 = 2910197) B2910197
theorem B5446385 : Blo 1613005 5446385 := bstep (se 2 (by rfl) ⟨2042394, by rfl⟩ : syracuseStep 5446385 = 4084789) B4084789
theorem B4594477 : Blo 1613005 4594477 := bstep (se 3 (by rfl) ⟨861464, by rfl⟩ : syracuseStep 4594477 = 1722929) B1722929
theorem B8166257 : Blo 1613005 8166257 := bstep (se 2 (by rfl) ⟨3062346, by rfl⟩ : syracuseStep 8166257 = 6124693) B6124693
theorem B2907011 : Blo 1613005 2907011 := bstep (se 1 (by rfl) ⟨2180258, by rfl⟩ : syracuseStep 2907011 = 4360517) B4360517
theorem B10337165 : Blo 1613005 10337165 := bstep (se 3 (by rfl) ⟨1938218, by rfl⟩ : syracuseStep 10337165 = 3876437) B3876437
theorem B4594637 : Blo 1613005 4594637 := bstep (se 3 (by rfl) ⟨861494, by rfl⟩ : syracuseStep 4594637 = 1722989) B1722989
theorem B4594819 : Blo 1613005 4594819 := bstep (se 1 (by rfl) ⟨3446114, by rfl⟩ : syracuseStep 4594819 = 6892229) B6892229
theorem B2759827 : Blo 1613005 2759827 := bstep (se 1 (by rfl) ⟨2069870, by rfl⟩ : syracuseStep 2759827 = 4139741) B4139741
theorem B2907299 : Blo 1613005 2907299 := bstep (se 1 (by rfl) ⟨2180474, by rfl⟩ : syracuseStep 2907299 = 4360949) B4360949
theorem B3062947 : Blo 1613005 3062947 := bstep (se 1 (by rfl) ⟨2297210, by rfl⟩ : syracuseStep 3062947 = 4594421) B4594421
theorem B3448003 : Blo 1613005 3448003 := bstep (se 1 (by rfl) ⟨2586002, by rfl⟩ : syracuseStep 3448003 = 5172005) B5172005
theorem B9575621 : Blo 1613005 9575621 := bstep (se 4 (by rfl) ⟨897714, by rfl⟩ : syracuseStep 9575621 = 1795429) B1795429
theorem B1613011 : Blo 1613005 1613011 := bstep (se 1 (by rfl) ⟨1209758, by rfl⟩ : syracuseStep 1613011 = 2419517) B2419517
theorem B1613027 : Blo 1613005 1613027 := bstep (se 1 (by rfl) ⟨1209770, by rfl⟩ : syracuseStep 1613027 = 2419541) B2419541
theorem B1613043 : Blo 1613005 1613043 := bstep (se 1 (by rfl) ⟨1209782, by rfl⟩ : syracuseStep 1613043 = 2419565) B2419565
theorem B1613059 : Blo 1613005 1613059 := bstep (se 1 (by rfl) ⟨1209794, by rfl⟩ : syracuseStep 1613059 = 2419589) B2419589
theorem B5446925 : Blo 1613005 5446925 := bstep (se 3 (by rfl) ⟨1021298, by rfl⟩ : syracuseStep 5446925 = 2042597) B2042597
theorem B4087057 : Blo 1613005 4087057 := bstep (se 2 (by rfl) ⟨1532646, by rfl⟩ : syracuseStep 4087057 = 3065293) B3065293
theorem B1613075 : Blo 1613005 1613075 := bstep (se 1 (by rfl) ⟨1209806, by rfl⟩ : syracuseStep 1613075 = 2419613) B2419613
theorem B1613091 : Blo 1613005 1613091 := bstep (se 1 (by rfl) ⟨1209818, by rfl⟩ : syracuseStep 1613091 = 2419637) B2419637
theorem B1613107 : Blo 1613005 1613107 := bstep (se 1 (by rfl) ⟨1209830, by rfl⟩ : syracuseStep 1613107 = 2419661) B2419661
theorem B1613123 : Blo 1613005 1613123 := bstep (se 1 (by rfl) ⟨1209842, by rfl⟩ : syracuseStep 1613123 = 2419685) B2419685
theorem B5446979 : Blo 1613005 5446979 := bstep (se 1 (by rfl) ⟨4085234, by rfl⟩ : syracuseStep 5446979 = 8170469) B8170469
theorem B1613139 : Blo 1613005 1613139 := bstep (se 1 (by rfl) ⟨1209854, by rfl⟩ : syracuseStep 1613139 = 2419709) B2419709
theorem B1613155 : Blo 1613005 1613155 := bstep (se 1 (by rfl) ⟨1209866, by rfl⟩ : syracuseStep 1613155 = 2419733) B2419733
theorem B1613171 : Blo 1613005 1613171 := bstep (se 1 (by rfl) ⟨1209878, by rfl⟩ : syracuseStep 1613171 = 2419757) B2419757
theorem B1613187 : Blo 1613005 1613187 := bstep (se 1 (by rfl) ⟨1209890, by rfl⟩ : syracuseStep 1613187 = 2419781) B2419781
theorem B2907523 : Blo 1613005 2907523 := bstep (se 1 (by rfl) ⟨2180642, by rfl⟩ : syracuseStep 2907523 = 4361285) B4361285
theorem B1613203 : Blo 1613005 1613203 := bstep (se 1 (by rfl) ⟨1209902, by rfl⟩ : syracuseStep 1613203 = 2419805) B2419805
theorem B1613219 : Blo 1613005 1613219 := bstep (se 1 (by rfl) ⟨1209914, by rfl⟩ : syracuseStep 1613219 = 2419829) B2419829
theorem B1613235 : Blo 1613005 1613235 := bstep (se 1 (by rfl) ⟨1209926, by rfl⟩ : syracuseStep 1613235 = 2419853) B2419853
theorem B1613251 : Blo 1613005 1613251 := bstep (se 1 (by rfl) ⟨1209938, by rfl⟩ : syracuseStep 1613251 = 2419877) B2419877
theorem B2907587 : Blo 1613005 2907587 := bstep (se 1 (by rfl) ⟨2180690, by rfl⟩ : syracuseStep 2907587 = 4361381) B4361381
theorem B1613267 : Blo 1613005 1613267 := bstep (se 1 (by rfl) ⟨1209950, by rfl⟩ : syracuseStep 1613267 = 2419901) B2419901
theorem B1613283 : Blo 1613005 1613283 := bstep (se 1 (by rfl) ⟨1209962, by rfl⟩ : syracuseStep 1613283 = 2419925) B2419925
theorem B1613299 : Blo 1613005 1613299 := bstep (se 1 (by rfl) ⟨1209974, by rfl⟩ : syracuseStep 1613299 = 2419949) B2419949
theorem B1613315 : Blo 1613005 1613315 := bstep (se 1 (by rfl) ⟨1209986, by rfl⟩ : syracuseStep 1613315 = 2419973) B2419973
theorem B1613331 : Blo 1613005 1613331 := bstep (se 1 (by rfl) ⟨1209998, by rfl⟩ : syracuseStep 1613331 = 2419997) B2419997
theorem B1613347 : Blo 1613005 1613347 := bstep (se 1 (by rfl) ⟨1210010, by rfl⟩ : syracuseStep 1613347 = 2420021) B2420021
theorem B4087331 : Blo 1613005 4087331 := bstep (se 1 (by rfl) ⟨3065498, by rfl⟩ : syracuseStep 4087331 = 6130997) B6130997
theorem B2907697 : Blo 1613005 2907697 := bstep (se 2 (by rfl) ⟨1090386, by rfl⟩ : syracuseStep 2907697 = 2180773) B2180773
theorem B1613363 : Blo 1613005 1613363 := bstep (se 1 (by rfl) ⟨1210022, by rfl⟩ : syracuseStep 1613363 = 2420045) B2420045
theorem B1613379 : Blo 1613005 1613379 := bstep (se 1 (by rfl) ⟨1210034, by rfl⟩ : syracuseStep 1613379 = 2420069) B2420069
theorem B5447249 : Blo 1613005 5447249 := bstep (se 2 (by rfl) ⟨2042718, by rfl⟩ : syracuseStep 5447249 = 4085437) B4085437
theorem B1613395 : Blo 1613005 1613395 := bstep (se 1 (by rfl) ⟨1210046, by rfl⟩ : syracuseStep 1613395 = 2420093) B2420093
theorem B1613411 : Blo 1613005 1613411 := bstep (se 1 (by rfl) ⟨1210058, by rfl⟩ : syracuseStep 1613411 = 2420117) B2420117
theorem B3063395 : Blo 1613005 3063395 := bstep (se 1 (by rfl) ⟨2297546, by rfl⟩ : syracuseStep 3063395 = 4595093) B4595093
theorem B6897251 : Blo 1613005 6897251 := bstep (se 1 (by rfl) ⟨5172938, by rfl⟩ : syracuseStep 6897251 = 10345877) B10345877
theorem B7364209 : Blo 1613005 7364209 := bstep (se 2 (by rfl) ⟨2761578, by rfl⟩ : syracuseStep 7364209 = 5523157) B5523157
theorem B1613427 : Blo 1613005 1613427 := bstep (se 1 (by rfl) ⟨1210070, by rfl⟩ : syracuseStep 1613427 = 2420141) B2420141
theorem B1613443 : Blo 1613005 1613443 := bstep (se 1 (by rfl) ⟨1210082, by rfl⟩ : syracuseStep 1613443 = 2420165) B2420165
theorem B1613459 : Blo 1613005 1613459 := bstep (se 1 (by rfl) ⟨1210094, by rfl⟩ : syracuseStep 1613459 = 2420189) B2420189
theorem B1613475 : Blo 1613005 1613475 := bstep (se 1 (by rfl) ⟨1210106, by rfl⟩ : syracuseStep 1613475 = 2420213) B2420213
theorem B8724145 : Blo 1613005 8724145 := bstep (se 2 (by rfl) ⟨3271554, by rfl⟩ : syracuseStep 8724145 = 6543109) B6543109
theorem B1613491 : Blo 1613005 1613491 := bstep (se 1 (by rfl) ⟨1210118, by rfl⟩ : syracuseStep 1613491 = 2420237) B2420237
theorem B1613507 : Blo 1613005 1613507 := bstep (se 1 (by rfl) ⟨1210130, by rfl⟩ : syracuseStep 1613507 = 2420261) B2420261
theorem B1613523 : Blo 1613005 1613523 := bstep (se 1 (by rfl) ⟨1210142, by rfl⟩ : syracuseStep 1613523 = 2420285) B2420285
theorem B1613539 : Blo 1613005 1613539 := bstep (se 1 (by rfl) ⟨1210154, by rfl⟩ : syracuseStep 1613539 = 2420309) B2420309
theorem B4087523 : Blo 1613005 4087523 := bstep (se 1 (by rfl) ⟨3065642, by rfl⟩ : syracuseStep 4087523 = 6131285) B6131285
theorem B5521133 : Blo 1613005 5521133 := bstep (se 3 (by rfl) ⟨1035212, by rfl⟩ : syracuseStep 5521133 = 2070425) B2070425
theorem B1613555 : Blo 1613005 1613555 := bstep (se 1 (by rfl) ⟨1210166, by rfl⟩ : syracuseStep 1613555 = 2420333) B2420333
theorem B1613571 : Blo 1613005 1613571 := bstep (se 1 (by rfl) ⟨1210178, by rfl⟩ : syracuseStep 1613571 = 2420357) B2420357
theorem B1613587 : Blo 1613005 1613587 := bstep (se 1 (by rfl) ⟨1210190, by rfl⟩ : syracuseStep 1613587 = 2420381) B2420381
theorem B1613603 : Blo 1613005 1613603 := bstep (se 1 (by rfl) ⟨1210202, by rfl⟩ : syracuseStep 1613603 = 2420405) B2420405
theorem B3104561 : Blo 1613005 3104561 := bstep (se 2 (by rfl) ⟨1164210, by rfl⟩ : syracuseStep 3104561 = 2328421) B2328421
theorem B1613619 : Blo 1613005 1613619 := bstep (se 1 (by rfl) ⟨1210214, by rfl⟩ : syracuseStep 1613619 = 2420429) B2420429
theorem B1613635 : Blo 1613005 1613635 := bstep (se 1 (by rfl) ⟨1210226, by rfl⟩ : syracuseStep 1613635 = 2420453) B2420453
theorem B12263237 : Blo 1613005 12263237 := bstep (se 4 (by rfl) ⟨1149678, by rfl⟩ : syracuseStep 12263237 = 2299357) B2299357
theorem B1613651 : Blo 1613005 1613651 := bstep (se 1 (by rfl) ⟨1210238, by rfl⟩ : syracuseStep 1613651 = 2420477) B2420477
theorem B1613667 : Blo 1613005 1613667 := bstep (se 1 (by rfl) ⟨1210250, by rfl⟩ : syracuseStep 1613667 = 2420501) B2420501
theorem B1613683 : Blo 1613005 1613683 := bstep (se 1 (by rfl) ⟨1210262, by rfl⟩ : syracuseStep 1613683 = 2420525) B2420525
theorem B1613699 : Blo 1613005 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B3063683 : Blo 1613005 3063683 := bstep (se 1 (by rfl) ⟨2297762, by rfl⟩ : syracuseStep 3063683 = 4595525) B4595525
theorem B1613715 : Blo 1613005 1613715 := bstep (se 1 (by rfl) ⟨1210286, by rfl⟩ : syracuseStep 1613715 = 2420573) B2420573
theorem B1613731 : Blo 1613005 1613731 := bstep (se 1 (by rfl) ⟨1210298, by rfl⟩ : syracuseStep 1613731 = 2420597) B2420597
theorem B1613747 : Blo 1613005 1613747 := bstep (se 1 (by rfl) ⟨1210310, by rfl⟩ : syracuseStep 1613747 = 2420621) B2420621
theorem B1613763 : Blo 1613005 1613763 := bstep (se 1 (by rfl) ⟨1210322, by rfl⟩ : syracuseStep 1613763 = 2420645) B2420645
theorem B1613779 : Blo 1613005 1613779 := bstep (se 1 (by rfl) ⟨1210334, by rfl⟩ : syracuseStep 1613779 = 2420669) B2420669
theorem B1613795 : Blo 1613005 1613795 := bstep (se 1 (by rfl) ⟨1210346, by rfl⟩ : syracuseStep 1613795 = 2420693) B2420693
theorem B7757795 : Blo 1613005 7757795 := bstep (se 1 (by rfl) ⟨5818346, by rfl⟩ : syracuseStep 7757795 = 11636693) B11636693
theorem B1613811 : Blo 1613005 1613811 := bstep (se 1 (by rfl) ⟨1210358, by rfl⟩ : syracuseStep 1613811 = 2420717) B2420717
theorem B1613835 : Blo 1613005 1613835 := bstep (se 1 (by rfl) ⟨1210376, by rfl⟩ : syracuseStep 1613835 = 2420753) B2420753
theorem B1613847 : Blo 1613005 1613847 := bstep (se 1 (by rfl) ⟨1210385, by rfl⟩ : syracuseStep 1613847 = 2420771) B2420771
theorem B1613867 : Blo 1613005 1613867 := bstep (se 1 (by rfl) ⟨1210400, by rfl⟩ : syracuseStep 1613867 = 2420801) B2420801
theorem B9814061 : Blo 1613005 9814061 := bstep (se 3 (by rfl) ⟨1840136, by rfl⟩ : syracuseStep 9814061 = 3680273) B3680273
theorem B1613879 : Blo 1613005 1613879 := bstep (se 1 (by rfl) ⟨1210409, by rfl⟩ : syracuseStep 1613879 = 2420819) B2420819
theorem B1613899 : Blo 1613005 1613899 := bstep (se 1 (by rfl) ⟨1210424, by rfl⟩ : syracuseStep 1613899 = 2420849) B2420849
theorem B1613911 : Blo 1613005 1613911 := bstep (se 1 (by rfl) ⟨1210433, by rfl⟩ : syracuseStep 1613911 = 2420867) B2420867
theorem B1613931 : Blo 1613005 1613931 := bstep (se 1 (by rfl) ⟨1210448, by rfl⟩ : syracuseStep 1613931 = 2420897) B2420897
theorem B1613943 : Blo 1613005 1613943 := bstep (se 1 (by rfl) ⟨1210457, by rfl⟩ : syracuseStep 1613943 = 2420915) B2420915
theorem B1613963 : Blo 1613005 1613963 := bstep (se 1 (by rfl) ⟨1210472, by rfl⟩ : syracuseStep 1613963 = 2420945) B2420945
theorem B1613975 : Blo 1613005 1613975 := bstep (se 1 (by rfl) ⟨1210481, by rfl⟩ : syracuseStep 1613975 = 2420963) B2420963
theorem B1613995 : Blo 1613005 1613995 := bstep (se 1 (by rfl) ⟨1210496, by rfl⟩ : syracuseStep 1613995 = 2420993) B2420993
theorem B1614007 : Blo 1613005 1614007 := bstep (se 1 (by rfl) ⟨1210505, by rfl⟩ : syracuseStep 1614007 = 2421011) B2421011
theorem B1614027 : Blo 1613005 1614027 := bstep (se 1 (by rfl) ⟨1210520, by rfl⟩ : syracuseStep 1614027 = 2421041) B2421041
theorem B1614039 : Blo 1613005 1614039 := bstep (se 1 (by rfl) ⟨1210529, by rfl⟩ : syracuseStep 1614039 = 2421059) B2421059
theorem B5447897 : Blo 1613005 5447897 := bstep (se 2 (by rfl) ⟨2042961, by rfl⟩ : syracuseStep 5447897 = 4085923) B4085923
theorem B1614059 : Blo 1613005 1614059 := bstep (se 1 (by rfl) ⟨1210544, by rfl⟩ : syracuseStep 1614059 = 2421089) B2421089
theorem B1614071 : Blo 1613005 1614071 := bstep (se 1 (by rfl) ⟨1210553, by rfl⟩ : syracuseStep 1614071 = 2421107) B2421107
theorem B1614091 : Blo 1613005 1614091 := bstep (se 1 (by rfl) ⟨1210568, by rfl⟩ : syracuseStep 1614091 = 2421137) B2421137
theorem B1614103 : Blo 1613005 1614103 := bstep (se 1 (by rfl) ⟨1210577, by rfl⟩ : syracuseStep 1614103 = 2421155) B2421155
theorem B2621719 : Blo 1613005 2621719 := bstep (se 1 (by rfl) ⟨1966289, by rfl⟩ : syracuseStep 2621719 = 3932579) B3932579
theorem B1614123 : Blo 1613005 1614123 := bstep (se 1 (by rfl) ⟨1210592, by rfl⟩ : syracuseStep 1614123 = 2421185) B2421185
theorem B1614135 : Blo 1613005 1614135 := bstep (se 1 (by rfl) ⟨1210601, by rfl⟩ : syracuseStep 1614135 = 2421203) B2421203
theorem B3064139 : Blo 1613005 3064139 := bstep (se 1 (by rfl) ⟨2298104, by rfl⟩ : syracuseStep 3064139 = 4596209) B4596209
theorem B1614155 : Blo 1613005 1614155 := bstep (se 1 (by rfl) ⟨1210616, by rfl⟩ : syracuseStep 1614155 = 2421233) B2421233
theorem B1614167 : Blo 1613005 1614167 := bstep (se 1 (by rfl) ⟨1210625, by rfl⟩ : syracuseStep 1614167 = 2421251) B2421251
theorem B4596061 : Blo 1613005 4596061 := bstep (se 3 (by rfl) ⟨861761, by rfl⟩ : syracuseStep 4596061 = 1723523) B1723523
theorem B1614187 : Blo 1613005 1614187 := bstep (se 1 (by rfl) ⟨1210640, by rfl⟩ : syracuseStep 1614187 = 2421281) B2421281
theorem B1614199 : Blo 1613005 1614199 := bstep (se 1 (by rfl) ⟨1210649, by rfl⟩ : syracuseStep 1614199 = 2421299) B2421299
theorem B1614219 : Blo 1613005 1614219 := bstep (se 1 (by rfl) ⟨1210664, by rfl⟩ : syracuseStep 1614219 = 2421329) B2421329
theorem B1614231 : Blo 1613005 1614231 := bstep (se 1 (by rfl) ⟨1210673, by rfl⟩ : syracuseStep 1614231 = 2421347) B2421347
theorem B10346903 : Blo 1613005 10346903 := bstep (se 1 (by rfl) ⟨7760177, by rfl⟩ : syracuseStep 10346903 = 15520355) B15520355
theorem B3629465 : Blo 1613005 3629465 := bstep (se 2 (by rfl) ⟨1361049, by rfl⟩ : syracuseStep 3629465 = 2722099) B2722099
theorem B1614251 : Blo 1613005 1614251 := bstep (se 1 (by rfl) ⟨1210688, by rfl⟩ : syracuseStep 1614251 = 2421377) B2421377
theorem B1614263 : Blo 1613005 1614263 := bstep (se 1 (by rfl) ⟨1210697, by rfl⟩ : syracuseStep 1614263 = 2421395) B2421395
theorem B1614283 : Blo 1613005 1614283 := bstep (se 1 (by rfl) ⟨1210712, by rfl⟩ : syracuseStep 1614283 = 2421425) B2421425
theorem B1614295 : Blo 1613005 1614295 := bstep (se 1 (by rfl) ⟨1210721, by rfl⟩ : syracuseStep 1614295 = 2421443) B2421443
theorem B1614315 : Blo 1613005 1614315 := bstep (se 1 (by rfl) ⟨1210736, by rfl⟩ : syracuseStep 1614315 = 2421473) B2421473
theorem B3629555 : Blo 1613005 3629555 := bstep (se 1 (by rfl) ⟨2722166, by rfl⟩ : syracuseStep 3629555 = 5444333) B5444333
theorem B1614327 : Blo 1613005 1614327 := bstep (se 1 (by rfl) ⟨1210745, by rfl⟩ : syracuseStep 1614327 = 2421491) B2421491
theorem B3064321 : Blo 1613005 3064321 := bstep (se 2 (by rfl) ⟨1149120, by rfl⟩ : syracuseStep 3064321 = 2298241) B2298241
theorem B1614347 : Blo 1613005 1614347 := bstep (se 1 (by rfl) ⟨1210760, by rfl⟩ : syracuseStep 1614347 = 2421521) B2421521
theorem B6898193 : Blo 1613005 6898193 := bstep (se 2 (by rfl) ⟨2586822, by rfl⟩ : syracuseStep 6898193 = 5173645) B5173645
theorem B3629591 : Blo 1613005 3629591 := bstep (se 1 (by rfl) ⟨2722193, by rfl⟩ : syracuseStep 3629591 = 5444387) B5444387
theorem B1614359 : Blo 1613005 1614359 := bstep (se 1 (by rfl) ⟨1210769, by rfl⟩ : syracuseStep 1614359 = 2421539) B2421539
theorem B1614379 : Blo 1613005 1614379 := bstep (se 1 (by rfl) ⟨1210784, by rfl⟩ : syracuseStep 1614379 = 2421569) B2421569
theorem B1614391 : Blo 1613005 1614391 := bstep (se 1 (by rfl) ⟨1210793, by rfl⟩ : syracuseStep 1614391 = 2421587) B2421587
theorem B1614411 : Blo 1613005 1614411 := bstep (se 1 (by rfl) ⟨1210808, by rfl⟩ : syracuseStep 1614411 = 2421617) B2421617
theorem B1614423 : Blo 1613005 1614423 := bstep (se 1 (by rfl) ⟨1210817, by rfl⟩ : syracuseStep 1614423 = 2421635) B2421635
theorem B1614443 : Blo 1613005 1614443 := bstep (se 1 (by rfl) ⟨1210832, by rfl⟩ : syracuseStep 1614443 = 2421665) B2421665
theorem B1614455 : Blo 1613005 1614455 := bstep (se 1 (by rfl) ⟨1210841, by rfl⟩ : syracuseStep 1614455 = 2421683) B2421683
theorem B1614475 : Blo 1613005 1614475 := bstep (se 1 (by rfl) ⟨1210856, by rfl⟩ : syracuseStep 1614475 = 2421713) B2421713
theorem B6890129 : Blo 1613005 6890129 := bstep (se 2 (by rfl) ⟨2583798, by rfl⟩ : syracuseStep 6890129 = 5167597) B5167597
theorem B1614487 : Blo 1613005 1614487 := bstep (se 1 (by rfl) ⟨1210865, by rfl⟩ : syracuseStep 1614487 = 2421731) B2421731
theorem B1614507 : Blo 1613005 1614507 := bstep (se 1 (by rfl) ⟨1210880, by rfl⟩ : syracuseStep 1614507 = 2421761) B2421761
theorem B1614519 : Blo 1613005 1614519 := bstep (se 1 (by rfl) ⟨1210889, by rfl⟩ : syracuseStep 1614519 = 2421779) B2421779
theorem B3629771 : Blo 1613005 3629771 := bstep (se 1 (by rfl) ⟨2722328, by rfl⟩ : syracuseStep 3629771 = 5444657) B5444657
theorem B1614539 : Blo 1613005 1614539 := bstep (se 1 (by rfl) ⟨1210904, by rfl⟩ : syracuseStep 1614539 = 2421809) B2421809
theorem B1614551 : Blo 1613005 1614551 := bstep (se 1 (by rfl) ⟨1210913, by rfl⟩ : syracuseStep 1614551 = 2421827) B2421827
theorem B1614571 : Blo 1613005 1614571 := bstep (se 1 (by rfl) ⟨1210928, by rfl⟩ : syracuseStep 1614571 = 2421857) B2421857
theorem B1614583 : Blo 1613005 1614583 := bstep (se 1 (by rfl) ⟨1210937, by rfl⟩ : syracuseStep 1614583 = 2421875) B2421875
theorem B3629825 : Blo 1613005 3629825 := bstep (se 2 (by rfl) ⟨1361184, by rfl⟩ : syracuseStep 3629825 = 2722369) B2722369
theorem B1614603 : Blo 1613005 1614603 := bstep (se 1 (by rfl) ⟨1210952, by rfl⟩ : syracuseStep 1614603 = 2421905) B2421905
theorem B1614615 : Blo 1613005 1614615 := bstep (se 1 (by rfl) ⟨1210961, by rfl⟩ : syracuseStep 1614615 = 2421923) B2421923
theorem B1614635 : Blo 1613005 1614635 := bstep (se 1 (by rfl) ⟨1210976, by rfl⟩ : syracuseStep 1614635 = 2421953) B2421953
theorem B1614647 : Blo 1613005 1614647 := bstep (se 1 (by rfl) ⟨1210985, by rfl⟩ : syracuseStep 1614647 = 2421971) B2421971
theorem B1614667 : Blo 1613005 1614667 := bstep (se 1 (by rfl) ⟨1211000, by rfl⟩ : syracuseStep 1614667 = 2422001) B2422001
theorem B1614679 : Blo 1613005 1614679 := bstep (se 1 (by rfl) ⟨1211009, by rfl⟩ : syracuseStep 1614679 = 2422019) B2422019
theorem B10347365 : Blo 1613005 10347365 := bstep (se 4 (by rfl) ⟨970065, by rfl⟩ : syracuseStep 10347365 = 1940131) B1940131
theorem B1614699 : Blo 1613005 1614699 := bstep (se 1 (by rfl) ⟨1211024, by rfl⟩ : syracuseStep 1614699 = 2422049) B2422049
theorem B1614711 : Blo 1613005 1614711 := bstep (se 1 (by rfl) ⟨1211033, by rfl⟩ : syracuseStep 1614711 = 2422067) B2422067
theorem B1614731 : Blo 1613005 1614731 := bstep (se 1 (by rfl) ⟨1211048, by rfl⟩ : syracuseStep 1614731 = 2422097) B2422097
theorem B5448599 : Blo 1613005 5448599 := bstep (se 1 (by rfl) ⟨4086449, by rfl⟩ : syracuseStep 5448599 = 8172899) B8172899
theorem B1614743 : Blo 1613005 1614743 := bstep (se 1 (by rfl) ⟨1211057, by rfl⟩ : syracuseStep 1614743 = 2422115) B2422115
theorem B1614763 : Blo 1613005 1614763 := bstep (se 1 (by rfl) ⟨1211072, by rfl⟩ : syracuseStep 1614763 = 2422145) B2422145
theorem B1614775 : Blo 1613005 1614775 := bstep (se 1 (by rfl) ⟨1211081, by rfl⟩ : syracuseStep 1614775 = 2422163) B2422163
theorem B1614795 : Blo 1613005 1614795 := bstep (se 1 (by rfl) ⟨1211096, by rfl⟩ : syracuseStep 1614795 = 2422193) B2422193
theorem B1614807 : Blo 1613005 1614807 := bstep (se 1 (by rfl) ⟨1211105, by rfl⟩ : syracuseStep 1614807 = 2422211) B2422211
theorem B3630041 : Blo 1613005 3630041 := bstep (se 2 (by rfl) ⟨1361265, by rfl⟩ : syracuseStep 3630041 = 2722531) B2722531
theorem B1614827 : Blo 1613005 1614827 := bstep (se 1 (by rfl) ⟨1211120, by rfl⟩ : syracuseStep 1614827 = 2422241) B2422241
theorem B1614839 : Blo 1613005 1614839 := bstep (se 1 (by rfl) ⟨1211129, by rfl⟩ : syracuseStep 1614839 = 2422259) B2422259
theorem B1614859 : Blo 1613005 1614859 := bstep (se 1 (by rfl) ⟨1211144, by rfl⟩ : syracuseStep 1614859 = 2422289) B2422289
theorem B1614871 : Blo 1613005 1614871 := bstep (se 1 (by rfl) ⟨1211153, by rfl⟩ : syracuseStep 1614871 = 2422307) B2422307
theorem B1614891 : Blo 1613005 1614891 := bstep (se 1 (by rfl) ⟨1211168, by rfl⟩ : syracuseStep 1614891 = 2422337) B2422337
theorem B3630131 : Blo 1613005 3630131 := bstep (se 1 (by rfl) ⟨2722598, by rfl⟩ : syracuseStep 3630131 = 5445197) B5445197
theorem B1614903 : Blo 1613005 1614903 := bstep (se 1 (by rfl) ⟨1211177, by rfl⟩ : syracuseStep 1614903 = 2422355) B2422355
theorem B25183307 : Blo 1613005 25183307 := bstep (se 1 (by rfl) ⟨18887480, by rfl⟩ : syracuseStep 25183307 = 37774961) B37774961
theorem B1614923 : Blo 1613005 1614923 := bstep (se 1 (by rfl) ⟨1211192, by rfl⟩ : syracuseStep 1614923 = 2422385) B2422385
theorem B3630167 : Blo 1613005 3630167 := bstep (se 1 (by rfl) ⟨2722625, by rfl⟩ : syracuseStep 3630167 = 5445251) B5445251
theorem B1614935 : Blo 1613005 1614935 := bstep (se 1 (by rfl) ⟨1211201, by rfl⟩ : syracuseStep 1614935 = 2422403) B2422403
theorem B1614955 : Blo 1613005 1614955 := bstep (se 1 (by rfl) ⟨1211216, by rfl⟩ : syracuseStep 1614955 = 2422433) B2422433
theorem B1614967 : Blo 1613005 1614967 := bstep (se 1 (by rfl) ⟨1211225, by rfl⟩ : syracuseStep 1614967 = 2422451) B2422451
theorem B1614987 : Blo 1613005 1614987 := bstep (se 1 (by rfl) ⟨1211240, by rfl⟩ : syracuseStep 1614987 = 2422481) B2422481
theorem B9192599 : Blo 1613005 9192599 := bstep (se 1 (by rfl) ⟨6894449, by rfl⟩ : syracuseStep 9192599 = 13788899) B13788899
theorem B1614999 : Blo 1613005 1614999 := bstep (se 1 (by rfl) ⟨1211249, by rfl⟩ : syracuseStep 1614999 = 2422499) B2422499
theorem B12256433 : Blo 1613005 12256433 := bstep (se 2 (by rfl) ⟨4596162, by rfl⟩ : syracuseStep 12256433 = 9192325) B9192325
theorem B62080181 : Blo 1613005 62080181 := bstep (se 5 (by rfl) ⟨2910008, by rfl⟩ : syracuseStep 62080181 = 5820017) B5820017
theorem B3065035 : Blo 1613005 3065035 := bstep (se 1 (by rfl) ⟨2298776, by rfl⟩ : syracuseStep 3065035 = 4597553) B4597553
theorem B3630347 : Blo 1613005 3630347 := bstep (se 1 (by rfl) ⟨2722760, by rfl⟩ : syracuseStep 3630347 = 5445521) B5445521
theorem B3065111 : Blo 1613005 3065111 := bstep (se 1 (by rfl) ⟨2298833, by rfl⟩ : syracuseStep 3065111 = 4597667) B4597667
theorem B6907187 : Blo 1613005 6907187 := bstep (se 1 (by rfl) ⟨5180390, by rfl⟩ : syracuseStep 6907187 = 10360781) B10360781
theorem B3630401 : Blo 1613005 3630401 := bstep (se 2 (by rfl) ⟨1361400, by rfl⟩ : syracuseStep 3630401 = 2722801) B2722801
theorem B6890827 : Blo 1613005 6890827 := bstep (se 1 (by rfl) ⟨5168120, by rfl⟩ : syracuseStep 6890827 = 10336241) B10336241
theorem B5449139 : Blo 1613005 5449139 := bstep (se 1 (by rfl) ⟨4086854, by rfl⟩ : syracuseStep 5449139 = 8173709) B8173709
theorem B3679769 : Blo 1613005 3679769 := bstep (se 2 (by rfl) ⟨1379913, by rfl⟩ : syracuseStep 3679769 = 2759827) B2759827
theorem B3630617 : Blo 1613005 3630617 := bstep (se 2 (by rfl) ⟨1361481, by rfl⟩ : syracuseStep 3630617 = 2722963) B2722963
theorem B4597337 : Blo 1613005 4597337 := bstep (se 2 (by rfl) ⟨1724001, by rfl⟩ : syracuseStep 4597337 = 3448003) B3448003
theorem B6891101 : Blo 1613005 6891101 := bstep (se 3 (by rfl) ⟨1292081, by rfl⟩ : syracuseStep 6891101 = 2584163) B2584163
theorem B13092445 : Blo 1613005 13092445 := bstep (se 3 (by rfl) ⟨2454833, by rfl⟩ : syracuseStep 13092445 = 4909667) B4909667
theorem B18392669 : Blo 1613005 18392669 := bstep (se 3 (by rfl) ⟨3448625, by rfl⟩ : syracuseStep 18392669 = 6897251) B6897251
theorem B3630707 : Blo 1613005 3630707 := bstep (se 1 (by rfl) ⟨2723030, by rfl⟩ : syracuseStep 3630707 = 5446061) B5446061
theorem B3630743 : Blo 1613005 3630743 := bstep (se 1 (by rfl) ⟨2723057, by rfl⟩ : syracuseStep 3630743 = 5446115) B5446115
theorem B12256919 : Blo 1613005 12256919 := bstep (se 1 (by rfl) ⟨9192689, by rfl⟩ : syracuseStep 12256919 = 18385379) B18385379
theorem B7366295 : Blo 1613005 7366295 := bstep (se 1 (by rfl) ⟨5524721, by rfl⟩ : syracuseStep 7366295 = 11049443) B11049443
theorem B5449409 : Blo 1613005 5449409 := bstep (se 2 (by rfl) ⟨2043528, by rfl⟩ : syracuseStep 5449409 = 4087057) B4087057
theorem B5818115 : Blo 1613005 5818115 := bstep (se 1 (by rfl) ⟨4363586, by rfl⟩ : syracuseStep 5818115 = 8727173) B8727173
theorem B3630923 : Blo 1613005 3630923 := bstep (se 1 (by rfl) ⟨2723192, by rfl⟩ : syracuseStep 3630923 = 5446385) B5446385
theorem B3876697 : Blo 1613005 3876697 := bstep (se 2 (by rfl) ⟨1453761, by rfl⟩ : syracuseStep 3876697 = 2907523) B2907523
theorem B3630977 : Blo 1613005 3630977 := bstep (se 2 (by rfl) ⟨1361616, by rfl⟩ : syracuseStep 3630977 = 2723233) B2723233
theorem B6129539 : Blo 1613005 6129539 := bstep (se 1 (by rfl) ⟨4597154, by rfl⟩ : syracuseStep 6129539 = 9194309) B9194309
theorem B6129553 : Blo 1613005 6129553 := bstep (se 2 (by rfl) ⟨2298582, by rfl⟩ : syracuseStep 6129553 = 4597165) B4597165
theorem B6891443 : Blo 1613005 6891443 := bstep (se 1 (by rfl) ⟨5168582, by rfl⟩ : syracuseStep 6891443 = 10337165) B10337165
theorem B3065779 : Blo 1613005 3065779 := bstep (se 1 (by rfl) ⟨2299334, by rfl⟩ : syracuseStep 3065779 = 4598669) B4598669
theorem B14723021 : Blo 1613005 14723021 := bstep (se 3 (by rfl) ⟨2760566, by rfl⟩ : syracuseStep 14723021 = 5521133) B5521133
theorem B102139957 : Blo 1613005 102139957 := bstep (se 5 (by rfl) ⟨4787810, by rfl⟩ : syracuseStep 102139957 = 9575621) B9575621
theorem B3876929 : Blo 1613005 3876929 := bstep (se 2 (by rfl) ⟨1453848, by rfl⟩ : syracuseStep 3876929 = 2907697) B2907697
theorem B3631193 : Blo 1613005 3631193 := bstep (se 2 (by rfl) ⟨1361697, by rfl⟩ : syracuseStep 3631193 = 2723395) B2723395
theorem B13789277 : Blo 1613005 13789277 := bstep (se 3 (by rfl) ⟨2585489, by rfl⟩ : syracuseStep 13789277 = 5170979) B5170979
theorem B3631283 : Blo 1613005 3631283 := bstep (se 1 (by rfl) ⟨2723462, by rfl⟩ : syracuseStep 3631283 = 5446925) B5446925
theorem B6129857 : Blo 1613005 6129857 := bstep (se 2 (by rfl) ⟨2298696, by rfl⟩ : syracuseStep 6129857 = 4597393) B4597393
theorem B3631319 : Blo 1613005 3631319 := bstep (se 1 (by rfl) ⟨2723489, by rfl⟩ : syracuseStep 3631319 = 5446979) B5446979
theorem B5449949 : Blo 1613005 5449949 := bstep (se 3 (by rfl) ⟨1021865, by rfl⟩ : syracuseStep 5449949 = 2043731) B2043731
theorem B11634961 : Blo 1613005 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B8169821 : Blo 1613005 8169821 := bstep (se 3 (by rfl) ⟨1531841, by rfl⟩ : syracuseStep 8169821 = 3063683) B3063683
theorem B2722187 : Blo 1613005 2722187 := bstep (se 1 (by rfl) ⟨2041640, by rfl⟩ : syracuseStep 2722187 = 4083281) B4083281
theorem B3631499 : Blo 1613005 3631499 := bstep (se 1 (by rfl) ⟨2723624, by rfl⟩ : syracuseStep 3631499 = 5447249) B5447249
theorem B2042263 : Blo 1613005 2042263 := bstep (se 1 (by rfl) ⟨1531697, by rfl⟩ : syracuseStep 2042263 = 3063395) B3063395
theorem B3631553 : Blo 1613005 3631553 := bstep (se 2 (by rfl) ⟨1361832, by rfl⟩ : syracuseStep 3631553 = 2723665) B2723665
theorem B2722315 : Blo 1613005 2722315 := bstep (se 1 (by rfl) ⟨2041736, by rfl⟩ : syracuseStep 2722315 = 4083473) B4083473
theorem B14715427 : Blo 1613005 14715427 := bstep (se 1 (by rfl) ⟨11036570, by rfl⟩ : syracuseStep 14715427 = 22073141) B22073141
theorem B8505931 : Blo 1613005 8505931 := bstep (se 1 (by rfl) ⟨6379448, by rfl⟩ : syracuseStep 8505931 = 12758897) B12758897
theorem B5171863 : Blo 1613005 5171863 := bstep (se 1 (by rfl) ⟨3878897, by rfl⟩ : syracuseStep 5171863 = 7757795) B7757795
theorem B2722457 : Blo 1613005 2722457 := bstep (se 2 (by rfl) ⟨1020921, by rfl⟩ : syracuseStep 2722457 = 2041843) B2041843
theorem B3631769 : Blo 1613005 3631769 := bstep (se 2 (by rfl) ⟨1361913, by rfl⟩ : syracuseStep 3631769 = 2723827) B2723827
theorem B58862285 : Blo 1613005 58862285 := bstep (se 3 (by rfl) ⟨11036678, by rfl⟩ : syracuseStep 58862285 = 22073357) B22073357
theorem B3631859 : Blo 1613005 3631859 := bstep (se 1 (by rfl) ⟨2723894, by rfl⟩ : syracuseStep 3631859 = 5447789) B5447789
theorem B3631895 : Blo 1613005 3631895 := bstep (se 1 (by rfl) ⟨2723921, by rfl⟩ : syracuseStep 3631895 = 5447843) B5447843
theorem B2722585 : Blo 1613005 2722585 := bstep (se 2 (by rfl) ⟨1020969, by rfl⟩ : syracuseStep 2722585 = 2041939) B2041939
theorem B6130525 : Blo 1613005 6130525 := bstep (se 3 (by rfl) ⟨1149473, by rfl⟩ : syracuseStep 6130525 = 2298947) B2298947
theorem B2419595 : Blo 1613005 2419595 := bstep (se 1 (by rfl) ⟨1814696, by rfl⟩ : syracuseStep 2419595 = 3629393) B3629393
theorem B2419607 : Blo 1613005 2419607 := bstep (se 1 (by rfl) ⟨1814705, by rfl⟩ : syracuseStep 2419607 = 3629411) B3629411
theorem B1723339 : Blo 1613005 1723339 := bstep (se 1 (by rfl) ⟨1292504, by rfl⟩ : syracuseStep 1723339 = 2585009) B2585009
theorem B3632075 : Blo 1613005 3632075 := bstep (se 1 (by rfl) ⟨2724056, by rfl⟩ : syracuseStep 3632075 = 5448113) B5448113
theorem B2419673 : Blo 1613005 2419673 := bstep (se 2 (by rfl) ⟨907377, by rfl⟩ : syracuseStep 2419673 = 1814755) B1814755
theorem B5819357 : Blo 1613005 5819357 := bstep (se 3 (by rfl) ⟨1091129, by rfl⟩ : syracuseStep 5819357 = 2182259) B2182259
theorem B3632129 : Blo 1613005 3632129 := bstep (se 2 (by rfl) ⟨1362048, by rfl⟩ : syracuseStep 3632129 = 2724097) B2724097
theorem B2419787 : Blo 1613005 2419787 := bstep (se 1 (by rfl) ⟨1814840, by rfl⟩ : syracuseStep 2419787 = 3629681) B3629681
theorem B7752779 : Blo 1613005 7752779 := bstep (se 1 (by rfl) ⟨5814584, by rfl⟩ : syracuseStep 7752779 = 11629169) B11629169
theorem B2419799 : Blo 1613005 2419799 := bstep (se 1 (by rfl) ⟨1814849, by rfl⟩ : syracuseStep 2419799 = 3629699) B3629699
theorem B7752797 : Blo 1613005 7752797 := bstep (se 3 (by rfl) ⟨1453649, by rfl⟩ : syracuseStep 7752797 = 2907299) B2907299
theorem B2419865 : Blo 1613005 2419865 := bstep (se 2 (by rfl) ⟨907449, by rfl⟩ : syracuseStep 2419865 = 1814899) B1814899
theorem B4598977 : Blo 1613005 4598977 := bstep (se 2 (by rfl) ⟨1724616, by rfl⟩ : syracuseStep 4598977 = 3449233) B3449233
theorem B2043083 : Blo 1613005 2043083 := bstep (se 1 (by rfl) ⟨1532312, by rfl⟩ : syracuseStep 2043083 = 3064625) B3064625
theorem B3493081 : Blo 1613005 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B3632345 : Blo 1613005 3632345 := bstep (se 2 (by rfl) ⟨1362129, by rfl⟩ : syracuseStep 3632345 = 2724259) B2724259
theorem B2419979 : Blo 1613005 2419979 := bstep (se 1 (by rfl) ⟨1814984, by rfl⟩ : syracuseStep 2419979 = 3629969) B3629969
theorem B2419991 : Blo 1613005 2419991 := bstep (se 1 (by rfl) ⟨1814993, by rfl⟩ : syracuseStep 2419991 = 3629987) B3629987
theorem B3681587 : Blo 1613005 3681587 := bstep (se 1 (by rfl) ⟨2761190, by rfl⟩ : syracuseStep 3681587 = 5522381) B5522381
theorem B3632435 : Blo 1613005 3632435 := bstep (se 1 (by rfl) ⟨2724326, by rfl⟩ : syracuseStep 3632435 = 5448653) B5448653
theorem B2723159 : Blo 1613005 2723159 := bstep (se 1 (by rfl) ⟨2042369, by rfl⟩ : syracuseStep 2723159 = 4084739) B4084739
theorem B3632471 : Blo 1613005 3632471 := bstep (se 1 (by rfl) ⟨2724353, by rfl⟩ : syracuseStep 3632471 = 5448707) B5448707
theorem B2420057 : Blo 1613005 2420057 := bstep (se 2 (by rfl) ⟨907521, by rfl⟩ : syracuseStep 2420057 = 1815043) B1815043
theorem B11627869 : Blo 1613005 11627869 := bstep (se 3 (by rfl) ⟨2180225, by rfl⟩ : syracuseStep 11627869 = 4360451) B4360451
theorem B2420171 : Blo 1613005 2420171 := bstep (se 1 (by rfl) ⟨1815128, by rfl⟩ : syracuseStep 2420171 = 3630257) B3630257
theorem B2420183 : Blo 1613005 2420183 := bstep (se 1 (by rfl) ⟨1815137, by rfl⟩ : syracuseStep 2420183 = 3630275) B3630275
theorem B2723287 : Blo 1613005 2723287 := bstep (se 1 (by rfl) ⟨2042465, by rfl⟩ : syracuseStep 2723287 = 4084931) B4084931
theorem B3632651 : Blo 1613005 3632651 := bstep (se 1 (by rfl) ⟨2724488, by rfl⟩ : syracuseStep 3632651 = 5448977) B5448977
theorem B2420249 : Blo 1613005 2420249 := bstep (se 2 (by rfl) ⟨907593, by rfl⟩ : syracuseStep 2420249 = 1815187) B1815187
theorem B3632705 : Blo 1613005 3632705 := bstep (se 2 (by rfl) ⟨1362264, by rfl⟩ : syracuseStep 3632705 = 2724529) B2724529
theorem B2420363 : Blo 1613005 2420363 := bstep (se 1 (by rfl) ⟨1815272, by rfl⟩ : syracuseStep 2420363 = 3630545) B3630545
theorem B2420375 : Blo 1613005 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B3878551 : Blo 1613005 3878551 := bstep (se 1 (by rfl) ⟨2908913, by rfl⟩ : syracuseStep 3878551 = 5817827) B5817827
theorem B3731123 : Blo 1613005 3731123 := bstep (se 1 (by rfl) ⟨2798342, by rfl⟩ : syracuseStep 3731123 = 5596685) B5596685
theorem B2420441 : Blo 1613005 2420441 := bstep (se 2 (by rfl) ⟨907665, by rfl⟩ : syracuseStep 2420441 = 1815331) B1815331
theorem B3632921 : Blo 1613005 3632921 := bstep (se 2 (by rfl) ⟨1362345, by rfl⟩ : syracuseStep 3632921 = 2724691) B2724691
theorem B2420555 : Blo 1613005 2420555 := bstep (se 1 (by rfl) ⟨1815416, by rfl⟩ : syracuseStep 2420555 = 3630833) B3630833
theorem B2420567 : Blo 1613005 2420567 := bstep (se 1 (by rfl) ⟨1815425, by rfl⟩ : syracuseStep 2420567 = 3630851) B3630851
theorem B7753565 : Blo 1613005 7753565 := bstep (se 3 (by rfl) ⟨1453793, by rfl⟩ : syracuseStep 7753565 = 2907587) B2907587
theorem B3633011 : Blo 1613005 3633011 := bstep (se 1 (by rfl) ⟨2724758, by rfl⟩ : syracuseStep 3633011 = 5449517) B5449517
theorem B2043787 : Blo 1613005 2043787 := bstep (se 1 (by rfl) ⟨1532840, by rfl⟩ : syracuseStep 2043787 = 3065681) B3065681
theorem B3633047 : Blo 1613005 3633047 := bstep (se 1 (by rfl) ⟨2724785, by rfl⟩ : syracuseStep 3633047 = 5449571) B5449571
theorem B2420633 : Blo 1613005 2420633 := bstep (se 2 (by rfl) ⟨907737, by rfl⟩ : syracuseStep 2420633 = 1815475) B1815475
theorem B6541229 : Blo 1613005 6541229 := bstep (se 3 (by rfl) ⟨1226480, by rfl⟩ : syracuseStep 6541229 = 2452961) B2452961
theorem B4083635 : Blo 1613005 4083635 := bstep (se 1 (by rfl) ⟨3062726, by rfl⟩ : syracuseStep 4083635 = 6125453) B6125453
theorem B2297803 : Blo 1613005 2297803 := bstep (se 1 (by rfl) ⟨1723352, by rfl⟩ : syracuseStep 2297803 = 3446705) B3446705
theorem B2420747 : Blo 1613005 2420747 := bstep (se 1 (by rfl) ⟨1815560, by rfl⟩ : syracuseStep 2420747 = 3631121) B3631121
theorem B59666453 : Blo 1613005 59666453 := bstep (se 6 (by rfl) ⟨1398432, by rfl⟩ : syracuseStep 59666453 = 2796865) B2796865
theorem B2420759 : Blo 1613005 2420759 := bstep (se 1 (by rfl) ⟨1815569, by rfl⟩ : syracuseStep 2420759 = 3631139) B3631139
theorem B6213677 : Blo 1613005 6213677 := bstep (se 3 (by rfl) ⟨1165064, by rfl⟩ : syracuseStep 6213677 = 2330129) B2330129
theorem B2723915 : Blo 1613005 2723915 := bstep (se 1 (by rfl) ⟨2042936, by rfl⟩ : syracuseStep 2723915 = 4085873) B4085873
theorem B3633227 : Blo 1613005 3633227 := bstep (se 1 (by rfl) ⟨2724920, by rfl⟩ : syracuseStep 3633227 = 5449841) B5449841
theorem B2420825 : Blo 1613005 2420825 := bstep (se 2 (by rfl) ⟨907809, by rfl⟩ : syracuseStep 2420825 = 1815619) B1815619
theorem B6131801 : Blo 1613005 6131801 := bstep (se 2 (by rfl) ⟨2299425, by rfl⟩ : syracuseStep 6131801 = 4598851) B4598851
theorem B1814647 : Blo 1613005 1814647 := bstep (se 1 (by rfl) ⟨1360985, by rfl⟩ : syracuseStep 1814647 = 2721971) B2721971
theorem B3633281 : Blo 1613005 3633281 := bstep (se 2 (by rfl) ⟨1362480, by rfl⟩ : syracuseStep 3633281 = 2724961) B2724961
theorem B2584727 : Blo 1613005 2584727 := bstep (se 1 (by rfl) ⟨1938545, by rfl⟩ : syracuseStep 2584727 = 3877091) B3877091
theorem B4362443 : Blo 1613005 4362443 := bstep (se 1 (by rfl) ⟨3271832, by rfl⟩ : syracuseStep 4362443 = 6543665) B6543665
theorem B2420939 : Blo 1613005 2420939 := bstep (se 1 (by rfl) ⟨1815704, by rfl⟩ : syracuseStep 2420939 = 3631409) B3631409
theorem B2724043 : Blo 1613005 2724043 := bstep (se 1 (by rfl) ⟨2043032, by rfl⟩ : syracuseStep 2724043 = 4086065) B4086065
theorem B2420951 : Blo 1613005 2420951 := bstep (se 1 (by rfl) ⟨1815713, by rfl⟩ : syracuseStep 2420951 = 3631427) B3631427
theorem B4083929 : Blo 1613005 4083929 := bstep (se 2 (by rfl) ⟨1531473, by rfl⟩ : syracuseStep 4083929 = 3062947) B3062947
theorem B2421017 : Blo 1613005 2421017 := bstep (se 2 (by rfl) ⟨907881, by rfl⟩ : syracuseStep 2421017 = 1815763) B1815763
theorem B1814827 : Blo 1613005 1814827 := bstep (se 1 (by rfl) ⟨1361120, by rfl⟩ : syracuseStep 1814827 = 2722241) B2722241
theorem B6893869 : Blo 1613005 6893869 := bstep (se 3 (by rfl) ⟨1292600, by rfl⟩ : syracuseStep 6893869 = 2585201) B2585201
theorem B2724185 : Blo 1613005 2724185 := bstep (se 2 (by rfl) ⟨1021569, by rfl⟩ : syracuseStep 2724185 = 2043139) B2043139
theorem B3633497 : Blo 1613005 3633497 := bstep (se 2 (by rfl) ⟨1362561, by rfl⟩ : syracuseStep 3633497 = 2725123) B2725123
theorem B2421131 : Blo 1613005 2421131 := bstep (se 1 (by rfl) ⟨1815848, by rfl⟩ : syracuseStep 2421131 = 3631697) B3631697
theorem B1814935 : Blo 1613005 1814935 := bstep (se 1 (by rfl) ⟨1361201, by rfl⟩ : syracuseStep 1814935 = 2722403) B2722403
theorem B2421143 : Blo 1613005 2421143 := bstep (se 1 (by rfl) ⟨1815857, by rfl⟩ : syracuseStep 2421143 = 3631715) B3631715
theorem B8171927 : Blo 1613005 8171927 := bstep (se 1 (by rfl) ⟨6128945, by rfl⟩ : syracuseStep 8171927 = 12257891) B12257891
theorem B26169779 : Blo 1613005 26169779 := bstep (se 1 (by rfl) ⟨19627334, by rfl⟩ : syracuseStep 26169779 = 39254669) B39254669
theorem B3633587 : Blo 1613005 3633587 := bstep (se 1 (by rfl) ⟨2725190, by rfl⟩ : syracuseStep 3633587 = 5450381) B5450381
theorem B3633623 : Blo 1613005 3633623 := bstep (se 1 (by rfl) ⟨2725217, by rfl⟩ : syracuseStep 3633623 = 5450435) B5450435
theorem B2421209 : Blo 1613005 2421209 := bstep (se 2 (by rfl) ⟨907953, by rfl⟩ : syracuseStep 2421209 = 1815907) B1815907
theorem B2724313 : Blo 1613005 2724313 := bstep (se 2 (by rfl) ⟨1021617, by rfl⟩ : syracuseStep 2724313 = 2043235) B2043235
theorem B3273241 : Blo 1613005 3273241 := bstep (se 2 (by rfl) ⟨1227465, by rfl⟩ : syracuseStep 3273241 = 2454931) B2454931
theorem B5444171 : Blo 1613005 5444171 := bstep (se 1 (by rfl) ⟨4083128, by rfl⟩ : syracuseStep 5444171 = 8166257) B8166257
theorem B1815115 : Blo 1613005 1815115 := bstep (se 1 (by rfl) ⟨1361336, by rfl⟩ : syracuseStep 1815115 = 2722673) B2722673
theorem B2421323 : Blo 1613005 2421323 := bstep (se 1 (by rfl) ⟨1815992, by rfl⟩ : syracuseStep 2421323 = 3631985) B3631985
theorem B1938007 : Blo 1613005 1938007 := bstep (se 1 (by rfl) ⟨1453505, by rfl⟩ : syracuseStep 1938007 = 2907011) B2907011
theorem B2421335 : Blo 1613005 2421335 := bstep (se 1 (by rfl) ⟨1816001, by rfl⟩ : syracuseStep 2421335 = 3632003) B3632003
theorem B8286851 : Blo 1613005 8286851 := bstep (se 1 (by rfl) ⟨6215138, by rfl⟩ : syracuseStep 8286851 = 12430277) B12430277
theorem B2585239 : Blo 1613005 2585239 := bstep (se 1 (by rfl) ⟨1938929, by rfl⟩ : syracuseStep 2585239 = 3877859) B3877859
theorem B2421401 : Blo 1613005 2421401 := bstep (se 2 (by rfl) ⟨908025, by rfl⟩ : syracuseStep 2421401 = 1816051) B1816051
theorem B1815223 : Blo 1613005 1815223 := bstep (se 1 (by rfl) ⟨1361417, by rfl⟩ : syracuseStep 1815223 = 2722835) B2722835
theorem B2421515 : Blo 1613005 2421515 := bstep (se 1 (by rfl) ⟨1816136, by rfl⟩ : syracuseStep 2421515 = 3632273) B3632273
theorem B9573137 : Blo 1613005 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B2421527 : Blo 1613005 2421527 := bstep (se 1 (by rfl) ⟨1816145, by rfl⟩ : syracuseStep 2421527 = 3632291) B3632291
theorem B10343213 : Blo 1613005 10343213 := bstep (se 3 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 10343213 = 3878705) B3878705
theorem B9818945 : Blo 1613005 9818945 := bstep (se 2 (by rfl) ⟨3682104, by rfl⟩ : syracuseStep 9818945 = 7364209) B7364209
theorem B5444441 : Blo 1613005 5444441 := bstep (se 2 (by rfl) ⟨2041665, by rfl⟩ : syracuseStep 5444441 = 4083331) B4083331
theorem B2421593 : Blo 1613005 2421593 := bstep (se 2 (by rfl) ⟨908097, by rfl⟩ : syracuseStep 2421593 = 1816195) B1816195
theorem B1815403 : Blo 1613005 1815403 := bstep (se 1 (by rfl) ⟨1361552, by rfl⟩ : syracuseStep 1815403 = 2723105) B2723105
theorem B1635223 : Blo 1613005 1635223 := bstep (se 1 (by rfl) ⟨1226417, by rfl⟩ : syracuseStep 1635223 = 2452835) B2452835
theorem B6124481 : Blo 1613005 6124481 := bstep (se 2 (by rfl) ⟨2296680, by rfl⟩ : syracuseStep 6124481 = 4593361) B4593361
theorem B2421707 : Blo 1613005 2421707 := bstep (se 1 (by rfl) ⟨1816280, by rfl⟩ : syracuseStep 2421707 = 3632561) B3632561
theorem B1815511 : Blo 1613005 1815511 := bstep (se 1 (by rfl) ⟨1361633, by rfl⟩ : syracuseStep 1815511 = 2723267) B2723267
theorem B2421719 : Blo 1613005 2421719 := bstep (se 1 (by rfl) ⟨1816289, by rfl⟩ : syracuseStep 2421719 = 3632579) B3632579
theorem B2585611 : Blo 1613005 2585611 := bstep (se 1 (by rfl) ⟨1939208, by rfl⟩ : syracuseStep 2585611 = 3878417) B3878417
theorem B2724887 : Blo 1613005 2724887 := bstep (se 1 (by rfl) ⟨2043665, by rfl⟩ : syracuseStep 2724887 = 4087331) B4087331
theorem B2421785 : Blo 1613005 2421785 := bstep (se 2 (by rfl) ⟨908169, by rfl⟩ : syracuseStep 2421785 = 1816339) B1816339
theorem B8287363 : Blo 1613005 8287363 := bstep (se 1 (by rfl) ⟨6215522, by rfl⟩ : syracuseStep 8287363 = 12431045) B12431045
theorem B1815691 : Blo 1613005 1815691 := bstep (se 1 (by rfl) ⟨1361768, by rfl⟩ : syracuseStep 1815691 = 2723537) B2723537
theorem B2421899 : Blo 1613005 2421899 := bstep (se 1 (by rfl) ⟨1816424, by rfl⟩ : syracuseStep 2421899 = 3632849) B3632849
theorem B2421911 : Blo 1613005 2421911 := bstep (se 1 (by rfl) ⟨1816433, by rfl⟩ : syracuseStep 2421911 = 3632867) B3632867
theorem B2725015 : Blo 1613005 2725015 := bstep (se 1 (by rfl) ⟨2043761, by rfl⟩ : syracuseStep 2725015 = 4087523) B4087523
theorem B2299033 : Blo 1613005 2299033 := bstep (se 2 (by rfl) ⟨862137, by rfl⟩ : syracuseStep 2299033 = 1724275) B1724275
theorem B2069707 : Blo 1613005 2069707 := bstep (se 1 (by rfl) ⟨1552280, by rfl⟩ : syracuseStep 2069707 = 3104561) B3104561
theorem B2421977 : Blo 1613005 2421977 := bstep (se 2 (by rfl) ⟨908241, by rfl⟩ : syracuseStep 2421977 = 1816483) B1816483
theorem B1815799 : Blo 1613005 1815799 := bstep (se 1 (by rfl) ⟨1361849, by rfl⟩ : syracuseStep 1815799 = 2723699) B2723699
theorem B6632779 : Blo 1613005 6632779 := bstep (se 1 (by rfl) ⟨4974584, by rfl⟩ : syracuseStep 6632779 = 9949169) B9949169
theorem B2422091 : Blo 1613005 2422091 := bstep (se 1 (by rfl) ⟨1816568, by rfl⟩ : syracuseStep 2422091 = 3633137) B3633137
theorem B2422103 : Blo 1613005 2422103 := bstep (se 1 (by rfl) ⟨1816577, by rfl⟩ : syracuseStep 2422103 = 3633155) B3633155
theorem B4724057 : Blo 1613005 4724057 := bstep (se 2 (by rfl) ⟨1771521, by rfl⟩ : syracuseStep 4724057 = 3543043) B3543043
theorem B52352405 : Blo 1613005 52352405 := bstep (se 6 (by rfl) ⟨1227009, by rfl⟩ : syracuseStep 52352405 = 2454019) B2454019
theorem B2422169 : Blo 1613005 2422169 := bstep (se 2 (by rfl) ⟨908313, by rfl⟩ : syracuseStep 2422169 = 1816627) B1816627
theorem B1815979 : Blo 1613005 1815979 := bstep (se 1 (by rfl) ⟨1361984, by rfl⟩ : syracuseStep 1815979 = 2723969) B2723969
theorem B13784525 : Blo 1613005 13784525 := bstep (se 3 (by rfl) ⟨2584598, by rfl⟩ : syracuseStep 13784525 = 5169197) B5169197
theorem B2422283 : Blo 1613005 2422283 := bstep (se 1 (by rfl) ⟨1816712, by rfl⟩ : syracuseStep 2422283 = 3633425) B3633425
theorem B5445143 : Blo 1613005 5445143 := bstep (se 1 (by rfl) ⟨4083857, by rfl⟩ : syracuseStep 5445143 = 8167715) B8167715
theorem B1816087 : Blo 1613005 1816087 := bstep (se 1 (by rfl) ⟨1362065, by rfl⟩ : syracuseStep 1816087 = 2724131) B2724131
theorem B2422295 : Blo 1613005 2422295 := bstep (se 1 (by rfl) ⟨1816721, by rfl⟩ : syracuseStep 2422295 = 3633443) B3633443
theorem B9188909 : Blo 1613005 9188909 := bstep (se 3 (by rfl) ⟨1722920, by rfl⟩ : syracuseStep 9188909 = 3445841) B3445841
theorem B2422361 : Blo 1613005 2422361 := bstep (se 2 (by rfl) ⟨908385, by rfl⟩ : syracuseStep 2422361 = 1816771) B1816771
theorem B4142771 : Blo 1613005 4142771 := bstep (se 1 (by rfl) ⟨3107078, by rfl⟩ : syracuseStep 4142771 = 6214157) B6214157
theorem B1816267 : Blo 1613005 1816267 := bstep (se 1 (by rfl) ⟨1362200, by rfl⟩ : syracuseStep 1816267 = 2724401) B2724401
theorem B2422475 : Blo 1613005 2422475 := bstep (se 1 (by rfl) ⟨1816856, by rfl⟩ : syracuseStep 2422475 = 3633713) B3633713
theorem B2422487 : Blo 1613005 2422487 := bstep (se 1 (by rfl) ⟨1816865, by rfl⟩ : syracuseStep 2422487 = 3633731) B3633731
theorem B1816375 : Blo 1613005 1816375 := bstep (se 1 (by rfl) ⟨1362281, by rfl⟩ : syracuseStep 1816375 = 2724563) B2724563
theorem B4085579 : Blo 1613005 4085579 := bstep (se 1 (by rfl) ⟨3064184, by rfl⟩ : syracuseStep 4085579 = 6128369) B6128369
theorem B2586521 : Blo 1613005 2586521 := bstep (se 2 (by rfl) ⟨969945, by rfl⟩ : syracuseStep 2586521 = 1939891) B1939891
theorem B4593611 : Blo 1613005 4593611 := bstep (se 1 (by rfl) ⟨3445208, by rfl⟩ : syracuseStep 4593611 = 6890417) B6890417
theorem B1816555 : Blo 1613005 1816555 := bstep (se 1 (by rfl) ⟨1362416, by rfl⟩ : syracuseStep 1816555 = 2724833) B2724833
theorem B13088785 : Blo 1613005 13088785 := bstep (se 2 (by rfl) ⟨4908294, by rfl⟩ : syracuseStep 13088785 = 9816589) B9816589
theorem B2586649 : Blo 1613005 2586649 := bstep (se 2 (by rfl) ⟨969993, by rfl⟩ : syracuseStep 2586649 = 1939987) B1939987
theorem B5445683 : Blo 1613005 5445683 := bstep (se 1 (by rfl) ⟨4084262, by rfl⟩ : syracuseStep 5445683 = 8168525) B8168525
theorem B3446849 : Blo 1613005 3446849 := bstep (se 2 (by rfl) ⟨1292568, by rfl⟩ : syracuseStep 3446849 = 2585137) B2585137
theorem B4659265 : Blo 1613005 4659265 := bstep (se 2 (by rfl) ⟨1747224, by rfl⟩ : syracuseStep 4659265 = 3494449) B3494449
theorem B1816663 : Blo 1613005 1816663 := bstep (se 1 (by rfl) ⟨1362497, by rfl⟩ : syracuseStep 1816663 = 2724995) B2724995
theorem B18381005 : Blo 1613005 18381005 := bstep (se 3 (by rfl) ⟨3446438, by rfl⟩ : syracuseStep 18381005 = 6892877) B6892877
theorem B1816843 : Blo 1613005 1816843 := bstep (se 1 (by rfl) ⟨1362632, by rfl⟩ : syracuseStep 1816843 = 2725265) B2725265
theorem B5445953 : Blo 1613005 5445953 := bstep (se 2 (by rfl) ⟨2042232, by rfl⟩ : syracuseStep 5445953 = 4084465) B4084465
theorem B6125969 : Blo 1613005 6125969 := bstep (se 2 (by rfl) ⟨2297238, by rfl⟩ : syracuseStep 6125969 = 4594477) B4594477
theorem B3447191 : Blo 1613005 3447191 := bstep (se 1 (by rfl) ⟨2585393, by rfl⟩ : syracuseStep 3447191 = 5170787) B5170787
theorem B3062195 : Blo 1613005 3062195 := bstep (se 1 (by rfl) ⟨2296646, by rfl⟩ : syracuseStep 3062195 = 4593293) B4593293
theorem B8165933 : Blo 1613005 8165933 := bstep (se 3 (by rfl) ⟨1531112, by rfl⟩ : syracuseStep 8165933 = 3062225) B3062225
theorem B9443915 : Blo 1613005 9443915 := bstep (se 1 (by rfl) ⟨7082936, by rfl⟩ : syracuseStep 9443915 = 14165873) B14165873
theorem B8968805 : Blo 1613005 8968805 := bstep (se 4 (by rfl) ⟨840825, by rfl⟩ : syracuseStep 8968805 = 1681651) B1681651
theorem B3062423 : Blo 1613005 3062423 := bstep (se 1 (by rfl) ⟨2296817, by rfl⟩ : syracuseStep 3062423 = 4593635) B4593635
theorem B6896279 : Blo 1613005 6896279 := bstep (se 1 (by rfl) ⟨5172209, by rfl⟩ : syracuseStep 6896279 = 10344419) B10344419
theorem B2906867 : Blo 1613005 2906867 := bstep (se 1 (by rfl) ⟨2180150, by rfl⟩ : syracuseStep 2906867 = 4360301) B4360301
theorem B4086551 : Blo 1613005 4086551 := bstep (se 1 (by rfl) ⟨3064913, by rfl⟩ : syracuseStep 4086551 = 6129827) B6129827
theorem B6126425 : Blo 1613005 6126425 := bstep (se 2 (by rfl) ⟨2297409, by rfl⟩ : syracuseStep 6126425 = 4594819) B4594819
theorem B5446493 : Blo 1613005 5446493 := bstep (se 3 (by rfl) ⟨1021217, by rfl⟩ : syracuseStep 5446493 = 2042435) B2042435
theorem B3062681 : Blo 1613005 3062681 := bstep (se 2 (by rfl) ⟨1148505, by rfl⟩ : syracuseStep 3062681 = 2297011) B2297011
theorem B3447755 : Blo 1613005 3447755 := bstep (se 1 (by rfl) ⟨2585816, by rfl⟩ : syracuseStep 3447755 = 5171633) B5171633
theorem B6126637 : Blo 1613005 6126637 := bstep (se 3 (by rfl) ⟨1148744, by rfl⟩ : syracuseStep 6126637 = 2297489) B2297489
theorem B1613015 : Blo 1613005 1613015 := bstep (se 1 (by rfl) ⟨1209761, by rfl⟩ : syracuseStep 1613015 = 2419523) B2419523
theorem B1613035 : Blo 1613005 1613035 := bstep (se 1 (by rfl) ⟨1209776, by rfl⟩ : syracuseStep 1613035 = 2419553) B2419553
theorem B26189041 : Blo 1613005 26189041 := bstep (se 2 (by rfl) ⟨9820890, by rfl⟩ : syracuseStep 26189041 = 19641781) B19641781
theorem B1613047 : Blo 1613005 1613047 := bstep (se 1 (by rfl) ⟨1209785, by rfl⟩ : syracuseStep 1613047 = 2419571) B2419571
theorem B1613067 : Blo 1613005 1613067 := bstep (se 1 (by rfl) ⟨1209800, by rfl⟩ : syracuseStep 1613067 = 2419601) B2419601
theorem B1613079 : Blo 1613005 1613079 := bstep (se 1 (by rfl) ⟨1209809, by rfl⟩ : syracuseStep 1613079 = 2419619) B2419619
theorem B1613099 : Blo 1613005 1613099 := bstep (se 1 (by rfl) ⟨1209824, by rfl⟩ : syracuseStep 1613099 = 2419649) B2419649
theorem B3063091 : Blo 1613005 3063091 := bstep (se 1 (by rfl) ⟨2297318, by rfl⟩ : syracuseStep 3063091 = 4594637) B4594637
theorem B1613111 : Blo 1613005 1613111 := bstep (se 1 (by rfl) ⟨1209833, by rfl⟩ : syracuseStep 1613111 = 2419667) B2419667
theorem B1613131 : Blo 1613005 1613131 := bstep (se 1 (by rfl) ⟨1209848, by rfl⟩ : syracuseStep 1613131 = 2419697) B2419697
theorem B1613143 : Blo 1613005 1613143 := bstep (se 1 (by rfl) ⟨1209857, by rfl⟩ : syracuseStep 1613143 = 2419715) B2419715
theorem B6126941 : Blo 1613005 6126941 := bstep (se 3 (by rfl) ⟨1148801, by rfl⟩ : syracuseStep 6126941 = 2297603) B2297603
theorem B1613163 : Blo 1613005 1613163 := bstep (se 1 (by rfl) ⟨1209872, by rfl⟩ : syracuseStep 1613163 = 2419745) B2419745
theorem B1613175 : Blo 1613005 1613175 := bstep (se 1 (by rfl) ⟨1209881, by rfl⟩ : syracuseStep 1613175 = 2419763) B2419763
theorem B1613195 : Blo 1613005 1613195 := bstep (se 1 (by rfl) ⟨1209896, by rfl⟩ : syracuseStep 1613195 = 2419793) B2419793
theorem B1613207 : Blo 1613005 1613207 := bstep (se 1 (by rfl) ⟨1209905, by rfl⟩ : syracuseStep 1613207 = 2419811) B2419811
theorem B1613227 : Blo 1613005 1613227 := bstep (se 1 (by rfl) ⟨1209920, by rfl⟩ : syracuseStep 1613227 = 2419841) B2419841
theorem B4087219 : Blo 1613005 4087219 := bstep (se 1 (by rfl) ⟨3065414, by rfl⟩ : syracuseStep 4087219 = 6130829) B6130829
theorem B1613239 : Blo 1613005 1613239 := bstep (se 1 (by rfl) ⟨1209929, by rfl⟩ : syracuseStep 1613239 = 2419859) B2419859
theorem B1613259 : Blo 1613005 1613259 := bstep (se 1 (by rfl) ⟨1209944, by rfl⟩ : syracuseStep 1613259 = 2419889) B2419889
theorem B1613271 : Blo 1613005 1613271 := bstep (se 1 (by rfl) ⟨1209953, by rfl⟩ : syracuseStep 1613271 = 2419907) B2419907
theorem B4906457 : Blo 1613005 4906457 := bstep (se 2 (by rfl) ⟨1839921, by rfl⟩ : syracuseStep 4906457 = 3679843) B3679843
theorem B1613291 : Blo 1613005 1613291 := bstep (se 1 (by rfl) ⟨1209968, by rfl⟩ : syracuseStep 1613291 = 2419937) B2419937
theorem B1613303 : Blo 1613005 1613303 := bstep (se 1 (by rfl) ⟨1209977, by rfl⟩ : syracuseStep 1613303 = 2419955) B2419955
theorem B1613323 : Blo 1613005 1613323 := bstep (se 1 (by rfl) ⟨1209992, by rfl⟩ : syracuseStep 1613323 = 2419985) B2419985
theorem B1613335 : Blo 1613005 1613335 := bstep (se 1 (by rfl) ⟨1210001, by rfl⟩ : syracuseStep 1613335 = 2420003) B2420003
theorem B3448345 : Blo 1613005 3448345 := bstep (se 2 (by rfl) ⟨1293129, by rfl⟩ : syracuseStep 3448345 = 2586259) B2586259
theorem B1613355 : Blo 1613005 1613355 := bstep (se 1 (by rfl) ⟨1210016, by rfl⟩ : syracuseStep 1613355 = 2420033) B2420033
theorem B1613367 : Blo 1613005 1613367 := bstep (se 1 (by rfl) ⟨1210025, by rfl⟩ : syracuseStep 1613367 = 2420051) B2420051
theorem B11632193 : Blo 1613005 11632193 := bstep (se 2 (by rfl) ⟨4362072, by rfl⟩ : syracuseStep 11632193 = 8724145) B8724145
theorem B13090369 : Blo 1613005 13090369 := bstep (se 2 (by rfl) ⟨4908888, by rfl⟩ : syracuseStep 13090369 = 9817777) B9817777
theorem B4087361 : Blo 1613005 4087361 := bstep (se 2 (by rfl) ⟨1532760, by rfl⟩ : syracuseStep 4087361 = 3065521) B3065521
theorem B1613387 : Blo 1613005 1613387 := bstep (se 1 (by rfl) ⟨1210040, by rfl⟩ : syracuseStep 1613387 = 2420081) B2420081
theorem B1613399 : Blo 1613005 1613399 := bstep (se 1 (by rfl) ⟨1210049, by rfl⟩ : syracuseStep 1613399 = 2420099) B2420099
theorem B1613419 : Blo 1613005 1613419 := bstep (se 1 (by rfl) ⟨1210064, by rfl⟩ : syracuseStep 1613419 = 2420129) B2420129
theorem B1613431 : Blo 1613005 1613431 := bstep (se 1 (by rfl) ⟨1210073, by rfl⟩ : syracuseStep 1613431 = 2420147) B2420147
theorem B1613451 : Blo 1613005 1613451 := bstep (se 1 (by rfl) ⟨1210088, by rfl⟩ : syracuseStep 1613451 = 2420177) B2420177
theorem B5979793 : Blo 1613005 5979793 := bstep (se 2 (by rfl) ⟨2242422, by rfl⟩ : syracuseStep 5979793 = 4484845) B4484845
theorem B1613463 : Blo 1613005 1613463 := bstep (se 1 (by rfl) ⟨1210097, by rfl⟩ : syracuseStep 1613463 = 2420195) B2420195
theorem B1613483 : Blo 1613005 1613483 := bstep (se 1 (by rfl) ⟨1210112, by rfl⟩ : syracuseStep 1613483 = 2420225) B2420225
theorem B1613495 : Blo 1613005 1613495 := bstep (se 1 (by rfl) ⟨1210121, by rfl⟩ : syracuseStep 1613495 = 2420243) B2420243
theorem B1613515 : Blo 1613005 1613515 := bstep (se 1 (by rfl) ⟨1210136, by rfl⟩ : syracuseStep 1613515 = 2420273) B2420273
theorem B1613527 : Blo 1613005 1613527 := bstep (se 1 (by rfl) ⟨1210145, by rfl⟩ : syracuseStep 1613527 = 2420291) B2420291
theorem B1613547 : Blo 1613005 1613547 := bstep (se 1 (by rfl) ⟨1210160, by rfl⟩ : syracuseStep 1613547 = 2420321) B2420321
theorem B1613559 : Blo 1613005 1613559 := bstep (se 1 (by rfl) ⟨1210169, by rfl⟩ : syracuseStep 1613559 = 2420339) B2420339
theorem B1613579 : Blo 1613005 1613579 := bstep (se 1 (by rfl) ⟨1210184, by rfl⟩ : syracuseStep 1613579 = 2420369) B2420369
theorem B1613591 : Blo 1613005 1613591 := bstep (se 1 (by rfl) ⟨1210193, by rfl⟩ : syracuseStep 1613591 = 2420387) B2420387
theorem B3063577 : Blo 1613005 3063577 := bstep (se 2 (by rfl) ⟨1148841, by rfl⟩ : syracuseStep 3063577 = 2297683) B2297683
theorem B1613611 : Blo 1613005 1613611 := bstep (se 1 (by rfl) ⟨1210208, by rfl⟩ : syracuseStep 1613611 = 2420417) B2420417
theorem B1613623 : Blo 1613005 1613623 := bstep (se 1 (by rfl) ⟨1210217, by rfl⟩ : syracuseStep 1613623 = 2420435) B2420435
theorem B1613643 : Blo 1613005 1613643 := bstep (se 1 (by rfl) ⟨1210232, by rfl⟩ : syracuseStep 1613643 = 2420465) B2420465
theorem B1613655 : Blo 1613005 1613655 := bstep (se 1 (by rfl) ⟨1210241, by rfl⟩ : syracuseStep 1613655 = 2420483) B2420483
theorem B2907991 : Blo 1613005 2907991 := bstep (se 1 (by rfl) ⟨2180993, by rfl⟩ : syracuseStep 2907991 = 4361987) B4361987
theorem B157015907 : Blo 1613005 157015907 := bstep (se 1 (by rfl) ⟨117761930, by rfl⟩ : syracuseStep 157015907 = 235523861) B235523861
theorem B39264101 : Blo 1613005 39264101 := bstep (se 4 (by rfl) ⟨3681009, by rfl⟩ : syracuseStep 39264101 = 7362019) B7362019
theorem B1613675 : Blo 1613005 1613675 := bstep (se 1 (by rfl) ⟨1210256, by rfl⟩ : syracuseStep 1613675 = 2420513) B2420513
theorem B1613687 : Blo 1613005 1613687 := bstep (se 1 (by rfl) ⟨1210265, by rfl⟩ : syracuseStep 1613687 = 2420531) B2420531
theorem B8175491 : Blo 1613005 8175491 := bstep (se 1 (by rfl) ⟨6131618, by rfl⟩ : syracuseStep 8175491 = 12263237) B12263237
theorem B1613707 : Blo 1613005 1613707 := bstep (se 1 (by rfl) ⟨1210280, by rfl⟩ : syracuseStep 1613707 = 2420561) B2420561
theorem B1613719 : Blo 1613005 1613719 := bstep (se 1 (by rfl) ⟨1210289, by rfl⟩ : syracuseStep 1613719 = 2420579) B2420579
theorem B1613739 : Blo 1613005 1613739 := bstep (se 1 (by rfl) ⟨1210304, by rfl⟩ : syracuseStep 1613739 = 2420609) B2420609
theorem B1613751 : Blo 1613005 1613751 := bstep (se 1 (by rfl) ⟨1210313, by rfl⟩ : syracuseStep 1613751 = 2420627) B2420627
theorem B1613771 : Blo 1613005 1613771 := bstep (se 1 (by rfl) ⟨1210328, by rfl⟩ : syracuseStep 1613771 = 2420657) B2420657
theorem B5447627 : Blo 1613005 5447627 := bstep (se 1 (by rfl) ⟨4085720, by rfl⟩ : syracuseStep 5447627 = 8171441) B8171441
theorem B1613783 : Blo 1613005 1613783 := bstep (se 1 (by rfl) ⟨1210337, by rfl⟩ : syracuseStep 1613783 = 2420675) B2420675
theorem B17457113 : Blo 1613005 17457113 := bstep (se 2 (by rfl) ⟨6546417, by rfl⟩ : syracuseStep 17457113 = 13092835) B13092835
theorem B1613803 : Blo 1613005 1613803 := bstep (se 1 (by rfl) ⟨1210352, by rfl⟩ : syracuseStep 1613803 = 2420705) B2420705
theorem B1613815 : Blo 1613005 1613815 := bstep (se 1 (by rfl) ⟨1210361, by rfl⟩ : syracuseStep 1613815 = 2420723) B2420723
theorem B1613831 : Blo 1613005 1613831 := bstep (se 1 (by rfl) ⟨1210373, by rfl⟩ : syracuseStep 1613831 = 2420747) B2420747
theorem B1613839 : Blo 1613005 1613839 := bstep (se 1 (by rfl) ⟨1210379, by rfl⟩ : syracuseStep 1613839 = 2420759) B2420759
theorem B3448865 : Blo 1613005 3448865 := bstep (se 2 (by rfl) ⟨1293324, by rfl⟩ : syracuseStep 3448865 = 2586649) B2586649
theorem B1613883 : Blo 1613005 1613883 := bstep (se 1 (by rfl) ⟨1210412, by rfl⟩ : syracuseStep 1613883 = 2420825) B2420825
theorem B4087867 : Blo 1613005 4087867 := bstep (se 1 (by rfl) ⟨3065900, by rfl⟩ : syracuseStep 4087867 = 6131801) B6131801
theorem B2908295 : Blo 1613005 2908295 := bstep (se 1 (by rfl) ⟨2181221, by rfl⟩ : syracuseStep 2908295 = 4362443) B4362443
theorem B1613959 : Blo 1613005 1613959 := bstep (se 1 (by rfl) ⟨1210469, by rfl⟩ : syracuseStep 1613959 = 2420939) B2420939
theorem B1613967 : Blo 1613005 1613967 := bstep (se 1 (by rfl) ⟨1210475, by rfl⟩ : syracuseStep 1613967 = 2420951) B2420951
theorem B1614011 : Blo 1613005 1614011 := bstep (se 1 (by rfl) ⟨1210508, by rfl⟩ : syracuseStep 1614011 = 2421017) B2421017
theorem B1614087 : Blo 1613005 1614087 := bstep (se 1 (by rfl) ⟨1210565, by rfl⟩ : syracuseStep 1614087 = 2421131) B2421131
theorem B1614095 : Blo 1613005 1614095 := bstep (se 1 (by rfl) ⟨1210571, by rfl⟩ : syracuseStep 1614095 = 2421143) B2421143
theorem B5447951 : Blo 1613005 5447951 := bstep (se 1 (by rfl) ⟨4085963, by rfl⟩ : syracuseStep 5447951 = 8171927) B8171927
theorem B6897935 : Blo 1613005 6897935 := bstep (se 1 (by rfl) ⟨5173451, by rfl⟩ : syracuseStep 6897935 = 10346903) B10346903
theorem B1614139 : Blo 1613005 1614139 := bstep (se 1 (by rfl) ⟨1210604, by rfl⟩ : syracuseStep 1614139 = 2421209) B2421209
theorem B3629447 : Blo 1613005 3629447 := bstep (se 1 (by rfl) ⟨2722085, by rfl⟩ : syracuseStep 3629447 = 5444171) B5444171
theorem B1614215 : Blo 1613005 1614215 := bstep (se 1 (by rfl) ⟨1210661, by rfl⟩ : syracuseStep 1614215 = 2421323) B2421323
theorem B1614223 : Blo 1613005 1614223 := bstep (se 1 (by rfl) ⟨1210667, by rfl⟩ : syracuseStep 1614223 = 2421335) B2421335
theorem B9191825 : Blo 1613005 9191825 := bstep (se 2 (by rfl) ⟨3446934, by rfl⟩ : syracuseStep 9191825 = 6893869) B6893869
theorem B1614267 : Blo 1613005 1614267 := bstep (se 1 (by rfl) ⟨1210700, by rfl⟩ : syracuseStep 1614267 = 2421401) B2421401
theorem B6128081 : Blo 1613005 6128081 := bstep (se 2 (by rfl) ⟨2298030, by rfl⟩ : syracuseStep 6128081 = 4596061) B4596061
theorem B1614343 : Blo 1613005 1614343 := bstep (se 1 (by rfl) ⟨1210757, by rfl⟩ : syracuseStep 1614343 = 2421515) B2421515
theorem B6382091 : Blo 1613005 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B1614351 : Blo 1613005 1614351 := bstep (se 1 (by rfl) ⟨1210763, by rfl⟩ : syracuseStep 1614351 = 2421527) B2421527
theorem B5448221 : Blo 1613005 5448221 := bstep (se 3 (by rfl) ⟨1021541, by rfl⟩ : syracuseStep 5448221 = 2043083) B2043083
theorem B6545963 : Blo 1613005 6545963 := bstep (se 1 (by rfl) ⟨4909472, by rfl⟩ : syracuseStep 6545963 = 9818945) B9818945
theorem B3629627 : Blo 1613005 3629627 := bstep (se 1 (by rfl) ⟨2722220, by rfl⟩ : syracuseStep 3629627 = 5444441) B5444441
theorem B1614395 : Blo 1613005 1614395 := bstep (se 1 (by rfl) ⟨1210796, by rfl⟩ : syracuseStep 1614395 = 2421593) B2421593
theorem B6898243 : Blo 1613005 6898243 := bstep (se 1 (by rfl) ⟨5173682, by rfl⟩ : syracuseStep 6898243 = 10347365) B10347365
theorem B1614471 : Blo 1613005 1614471 := bstep (se 1 (by rfl) ⟨1210853, by rfl⟩ : syracuseStep 1614471 = 2421707) B2421707
theorem B1614479 : Blo 1613005 1614479 := bstep (se 1 (by rfl) ⟨1210859, by rfl⟩ : syracuseStep 1614479 = 2421719) B2421719
theorem B3629753 : Blo 1613005 3629753 := bstep (se 2 (by rfl) ⟨1361157, by rfl⟩ : syracuseStep 3629753 = 2722315) B2722315
theorem B1614523 : Blo 1613005 1614523 := bstep (se 1 (by rfl) ⟨1210892, by rfl⟩ : syracuseStep 1614523 = 2421785) B2421785
theorem B19620569 : Blo 1613005 19620569 := bstep (se 2 (by rfl) ⟨7357713, by rfl⟩ : syracuseStep 19620569 = 14715427) B14715427
theorem B1614599 : Blo 1613005 1614599 := bstep (se 1 (by rfl) ⟨1210949, by rfl⟩ : syracuseStep 1614599 = 2421899) B2421899
theorem B6128399 : Blo 1613005 6128399 := bstep (se 1 (by rfl) ⟨4596299, by rfl⟩ : syracuseStep 6128399 = 9192599) B9192599
theorem B1614607 : Blo 1613005 1614607 := bstep (se 1 (by rfl) ⟨1210955, by rfl⟩ : syracuseStep 1614607 = 2421911) B2421911
theorem B41386787 : Blo 1613005 41386787 := bstep (se 1 (by rfl) ⟨31040090, by rfl⟩ : syracuseStep 41386787 = 62080181) B62080181
theorem B13787941 : Blo 1613005 13787941 := bstep (se 4 (by rfl) ⟨1292619, by rfl⟩ : syracuseStep 13787941 = 2585239) B2585239
theorem B1614651 : Blo 1613005 1614651 := bstep (se 1 (by rfl) ⟨1210988, by rfl⟩ : syracuseStep 1614651 = 2421977) B2421977
theorem B1614727 : Blo 1613005 1614727 := bstep (se 1 (by rfl) ⟨1211045, by rfl⟩ : syracuseStep 1614727 = 2422091) B2422091
theorem B1614735 : Blo 1613005 1614735 := bstep (se 1 (by rfl) ⟨1211051, by rfl⟩ : syracuseStep 1614735 = 2422103) B2422103
theorem B1614779 : Blo 1613005 1614779 := bstep (se 1 (by rfl) ⟨1211084, by rfl⟩ : syracuseStep 1614779 = 2422169) B2422169
theorem B1614855 : Blo 1613005 1614855 := bstep (se 1 (by rfl) ⟨1211141, by rfl⟩ : syracuseStep 1614855 = 2422283) B2422283
theorem B3630095 : Blo 1613005 3630095 := bstep (se 1 (by rfl) ⟨2722571, by rfl⟩ : syracuseStep 3630095 = 5445143) B5445143
theorem B1614863 : Blo 1613005 1614863 := bstep (se 1 (by rfl) ⟨1211147, by rfl⟩ : syracuseStep 1614863 = 2422295) B2422295
theorem B3630113 : Blo 1613005 3630113 := bstep (se 2 (by rfl) ⟨1361292, by rfl⟩ : syracuseStep 3630113 = 2722585) B2722585
theorem B3064891 : Blo 1613005 3064891 := bstep (se 1 (by rfl) ⟨2298668, by rfl⟩ : syracuseStep 3064891 = 4597337) B4597337
theorem B1614907 : Blo 1613005 1614907 := bstep (se 1 (by rfl) ⟨1211180, by rfl⟩ : syracuseStep 1614907 = 2422361) B2422361
theorem B2761847 : Blo 1613005 2761847 := bstep (se 1 (by rfl) ⟨2071385, by rfl⟩ : syracuseStep 2761847 = 4142771) B4142771
theorem B1614983 : Blo 1613005 1614983 := bstep (se 1 (by rfl) ⟨1211237, by rfl⟩ : syracuseStep 1614983 = 2422475) B2422475
theorem B1614991 : Blo 1613005 1614991 := bstep (se 1 (by rfl) ⟨1211243, by rfl⟩ : syracuseStep 1614991 = 2422487) B2422487
theorem B2180297 : Blo 1613005 2180297 := bstep (se 2 (by rfl) ⟨817611, by rfl⟩ : syracuseStep 2180297 = 1635223) B1635223
theorem B9815347 : Blo 1613005 9815347 := bstep (se 1 (by rfl) ⟨7361510, by rfl⟩ : syracuseStep 9815347 = 14723021) B14723021
theorem B3630455 : Blo 1613005 3630455 := bstep (se 1 (by rfl) ⟨2722841, by rfl⟩ : syracuseStep 3630455 = 5445683) B5445683
theorem B8168849 : Blo 1613005 8168849 := bstep (se 2 (by rfl) ⟨3063318, by rfl⟩ : syracuseStep 8168849 = 6126637) B6126637
theorem B9192851 : Blo 1613005 9192851 := bstep (se 1 (by rfl) ⟨6894638, by rfl⟩ : syracuseStep 9192851 = 13789277) B13789277
theorem B3065377 : Blo 1613005 3065377 := bstep (se 2 (by rfl) ⟨1149516, by rfl⟩ : syracuseStep 3065377 = 2299033) B2299033
theorem B3630635 : Blo 1613005 3630635 := bstep (se 1 (by rfl) ⟨2722976, by rfl⟩ : syracuseStep 3630635 = 5445953) B5445953
theorem B2041463 : Blo 1613005 2041463 := bstep (se 1 (by rfl) ⟨1531097, by rfl⟩ : syracuseStep 2041463 = 3062195) B3062195
theorem B2041615 : Blo 1613005 2041615 := bstep (se 1 (by rfl) ⟨1531211, by rfl⟩ : syracuseStep 2041615 = 3062423) B3062423
theorem B4597519 : Blo 1613005 4597519 := bstep (se 1 (by rfl) ⟨3448139, by rfl⟩ : syracuseStep 4597519 = 6896279) B6896279
theorem B39241523 : Blo 1613005 39241523 := bstep (se 1 (by rfl) ⟨29431142, by rfl⟩ : syracuseStep 39241523 = 58862285) B58862285
theorem B3630995 : Blo 1613005 3630995 := bstep (se 1 (by rfl) ⟨2723246, by rfl⟩ : syracuseStep 3630995 = 5446493) B5446493
theorem B5449625 : Blo 1613005 5449625 := bstep (se 2 (by rfl) ⟨2043609, by rfl⟩ : syracuseStep 5449625 = 4087219) B4087219
theorem B2041787 : Blo 1613005 2041787 := bstep (se 1 (by rfl) ⟨1531340, by rfl⟩ : syracuseStep 2041787 = 3062681) B3062681
theorem B3631049 : Blo 1613005 3631049 := bstep (se 2 (by rfl) ⟨1361643, by rfl⟩ : syracuseStep 3631049 = 2723287) B2723287
theorem B7751645 : Blo 1613005 7751645 := bstep (se 3 (by rfl) ⟨1453433, by rfl⟩ : syracuseStep 7751645 = 2906867) B2906867
theorem B4597793 : Blo 1613005 4597793 := bstep (se 2 (by rfl) ⟨1724172, by rfl⟩ : syracuseStep 4597793 = 3448345) B3448345
theorem B7973057 : Blo 1613005 7973057 := bstep (se 2 (by rfl) ⟨2989896, by rfl⟩ : syracuseStep 7973057 = 5979793) B5979793
theorem B5171401 : Blo 1613005 5171401 := bstep (se 2 (by rfl) ⟨1939275, by rfl⟩ : syracuseStep 5171401 = 3878551) B3878551
theorem B3270971 : Blo 1613005 3270971 := bstep (se 1 (by rfl) ⟨2453228, by rfl⟩ : syracuseStep 3270971 = 4906457) B4906457
theorem B3877321 : Blo 1613005 3877321 := bstep (se 2 (by rfl) ⟨1453995, by rfl⟩ : syracuseStep 3877321 = 2907991) B2907991
theorem B12249629 : Blo 1613005 12249629 := bstep (se 3 (by rfl) ⟨2296805, by rfl⟩ : syracuseStep 12249629 = 4593611) B4593611
theorem B26176067 : Blo 1613005 26176067 := bstep (se 1 (by rfl) ⟨19632050, by rfl⟩ : syracuseStep 26176067 = 39264101) B39264101
theorem B5450327 : Blo 1613005 5450327 := bstep (se 1 (by rfl) ⟨4087745, by rfl⟩ : syracuseStep 5450327 = 8175491) B8175491
theorem B4360819 : Blo 1613005 4360819 := bstep (se 1 (by rfl) ⟨3270614, by rfl⟩ : syracuseStep 4360819 = 6541229) B6541229
theorem B2722423 : Blo 1613005 2722423 := bstep (se 1 (by rfl) ⟨2041817, by rfl⟩ : syracuseStep 2722423 = 4083635) B4083635
theorem B3631751 : Blo 1613005 3631751 := bstep (se 1 (by rfl) ⟨2723813, by rfl⟩ : syracuseStep 3631751 = 5447627) B5447627
theorem B17451713 : Blo 1613005 17451713 := bstep (se 2 (by rfl) ⟨6544392, by rfl⟩ : syracuseStep 17451713 = 13088785) B13088785
theorem B13789925 : Blo 1613005 13789925 := bstep (se 4 (by rfl) ⟨1292805, by rfl⟩ : syracuseStep 13789925 = 2585611) B2585611
theorem B136186609 : Blo 1613005 136186609 := bstep (se 2 (by rfl) ⟨51069978, by rfl⟩ : syracuseStep 136186609 = 102139957) B102139957
theorem B1723151 : Blo 1613005 1723151 := bstep (se 1 (by rfl) ⟨1292363, by rfl⟩ : syracuseStep 1723151 = 2584727) B2584727
theorem B2722619 : Blo 1613005 2722619 := bstep (se 1 (by rfl) ⟨2041964, by rfl⟩ : syracuseStep 2722619 = 4083929) B4083929
theorem B3631931 : Blo 1613005 3631931 := bstep (se 1 (by rfl) ⟨2723948, by rfl⟩ : syracuseStep 3631931 = 5447897) B5447897
theorem B2419529 : Blo 1613005 2419529 := bstep (se 2 (by rfl) ⟨907323, by rfl⟩ : syracuseStep 2419529 = 1814647) B1814647
theorem B2042759 : Blo 1613005 2042759 := bstep (se 1 (by rfl) ⟨1532069, by rfl⟩ : syracuseStep 2042759 = 3064139) B3064139
theorem B3632057 : Blo 1613005 3632057 := bstep (se 2 (by rfl) ⟨1362021, by rfl⟩ : syracuseStep 3632057 = 2724043) B2724043
theorem B2419643 : Blo 1613005 2419643 := bstep (se 1 (by rfl) ⟨1814732, by rfl⟩ : syracuseStep 2419643 = 3629465) B3629465
theorem B2419703 : Blo 1613005 2419703 := bstep (se 1 (by rfl) ⟨1814777, by rfl⟩ : syracuseStep 2419703 = 3629555) B3629555
theorem B24849413 : Blo 1613005 24849413 := bstep (se 4 (by rfl) ⟨2329632, by rfl⟩ : syracuseStep 24849413 = 4659265) B4659265
theorem B4598795 : Blo 1613005 4598795 := bstep (se 1 (by rfl) ⟨3449096, by rfl⟩ : syracuseStep 4598795 = 6898193) B6898193
theorem B2419727 : Blo 1613005 2419727 := bstep (se 1 (by rfl) ⟨1814795, by rfl⟩ : syracuseStep 2419727 = 3629591) B3629591
theorem B2419769 : Blo 1613005 2419769 := bstep (se 2 (by rfl) ⟨907413, by rfl⟩ : syracuseStep 2419769 = 1814827) B1814827
theorem B5524567 : Blo 1613005 5524567 := bstep (se 1 (by rfl) ⟨4143425, by rfl⟩ : syracuseStep 5524567 = 8286851) B8286851
theorem B2419847 : Blo 1613005 2419847 := bstep (se 1 (by rfl) ⟨1814885, by rfl⟩ : syracuseStep 2419847 = 3629771) B3629771
theorem B2419883 : Blo 1613005 2419883 := bstep (se 1 (by rfl) ⟨1814912, by rfl⟩ : syracuseStep 2419883 = 3629825) B3629825
theorem B2419913 : Blo 1613005 2419913 := bstep (se 2 (by rfl) ⟨907467, by rfl⟩ : syracuseStep 2419913 = 1814935) B1814935
theorem B2723017 : Blo 1613005 2723017 := bstep (se 2 (by rfl) ⟨1021131, by rfl⟩ : syracuseStep 2723017 = 2042263) B2042263
theorem B3632399 : Blo 1613005 3632399 := bstep (se 1 (by rfl) ⟨2724299, by rfl⟩ : syracuseStep 3632399 = 5448599) B5448599
theorem B3632417 : Blo 1613005 3632417 := bstep (se 2 (by rfl) ⟨1362156, by rfl⟩ : syracuseStep 3632417 = 2724313) B2724313
theorem B4082987 : Blo 1613005 4082987 := bstep (se 1 (by rfl) ⟨3062240, by rfl⟩ : syracuseStep 4082987 = 6124481) B6124481
theorem B2420027 : Blo 1613005 2420027 := bstep (se 1 (by rfl) ⟨1815020, by rfl⟩ : syracuseStep 2420027 = 3630041) B3630041
theorem B44199269 : Blo 1613005 44199269 := bstep (se 4 (by rfl) ⟨4143681, by rfl⟩ : syracuseStep 44199269 = 8287363) B8287363
theorem B2420087 : Blo 1613005 2420087 := bstep (se 1 (by rfl) ⟨1815065, by rfl⟩ : syracuseStep 2420087 = 3630131) B3630131
theorem B16788871 : Blo 1613005 16788871 := bstep (se 1 (by rfl) ⟨12591653, by rfl⟩ : syracuseStep 16788871 = 25183307) B25183307
theorem B2420111 : Blo 1613005 2420111 := bstep (se 1 (by rfl) ⟨1815083, by rfl⟩ : syracuseStep 2420111 = 3630167) B3630167
theorem B11341241 : Blo 1613005 11341241 := bstep (se 2 (by rfl) ⟨4252965, by rfl⟩ : syracuseStep 11341241 = 8505931) B8505931
theorem B2420153 : Blo 1613005 2420153 := bstep (se 2 (by rfl) ⟨907557, by rfl⟩ : syracuseStep 2420153 = 1815115) B1815115
theorem B2584009 : Blo 1613005 2584009 := bstep (se 2 (by rfl) ⟨969003, by rfl⟩ : syracuseStep 2584009 = 1938007) B1938007
theorem B8170955 : Blo 1613005 8170955 := bstep (se 1 (by rfl) ⟨6128216, by rfl⟩ : syracuseStep 8170955 = 12256433) B12256433
theorem B18419165 : Blo 1613005 18419165 := bstep (se 3 (by rfl) ⟨3453593, by rfl⟩ : syracuseStep 18419165 = 6907187) B6907187
theorem B2420231 : Blo 1613005 2420231 := bstep (se 1 (by rfl) ⟨1815173, by rfl⟩ : syracuseStep 2420231 = 3630347) B3630347
theorem B2043407 : Blo 1613005 2043407 := bstep (se 1 (by rfl) ⟨1532555, by rfl⟩ : syracuseStep 2043407 = 3065111) B3065111
theorem B2420267 : Blo 1613005 2420267 := bstep (se 1 (by rfl) ⟨1815200, by rfl⟩ : syracuseStep 2420267 = 3630401) B3630401
theorem B3149371 : Blo 1613005 3149371 := bstep (se 1 (by rfl) ⟨2362028, by rfl⟩ : syracuseStep 3149371 = 4724057) B4724057
theorem B2420297 : Blo 1613005 2420297 := bstep (se 2 (by rfl) ⟨907611, by rfl⟩ : syracuseStep 2420297 = 1815223) B1815223
theorem B34901603 : Blo 1613005 34901603 := bstep (se 1 (by rfl) ⟨26176202, by rfl⟩ : syracuseStep 34901603 = 52352405) B52352405
theorem B3632759 : Blo 1613005 3632759 := bstep (se 1 (by rfl) ⟨2724569, by rfl⟩ : syracuseStep 3632759 = 5449139) B5449139
theorem B2420411 : Blo 1613005 2420411 := bstep (se 1 (by rfl) ⟨1815308, by rfl⟩ : syracuseStep 2420411 = 3630617) B3630617
theorem B2420471 : Blo 1613005 2420471 := bstep (se 1 (by rfl) ⟨1815353, by rfl⟩ : syracuseStep 2420471 = 3630707) B3630707
theorem B2420495 : Blo 1613005 2420495 := bstep (se 1 (by rfl) ⟨1815371, by rfl⟩ : syracuseStep 2420495 = 3630743) B3630743
theorem B8171279 : Blo 1613005 8171279 := bstep (se 1 (by rfl) ⟨6128459, by rfl⟩ : syracuseStep 8171279 = 12256919) B12256919
theorem B4910863 : Blo 1613005 4910863 := bstep (se 1 (by rfl) ⟨3683147, by rfl⟩ : syracuseStep 4910863 = 7366295) B7366295
theorem B3632939 : Blo 1613005 3632939 := bstep (se 1 (by rfl) ⟨2724704, by rfl⟩ : syracuseStep 3632939 = 5449409) B5449409
theorem B2420537 : Blo 1613005 2420537 := bstep (se 2 (by rfl) ⟨907701, by rfl⟩ : syracuseStep 2420537 = 1815403) B1815403
theorem B2420615 : Blo 1613005 2420615 := bstep (se 1 (by rfl) ⟨1815461, by rfl⟩ : syracuseStep 2420615 = 3630923) B3630923
theorem B2723719 : Blo 1613005 2723719 := bstep (se 1 (by rfl) ⟨2042789, by rfl⟩ : syracuseStep 2723719 = 4085579) B4085579
theorem B2420651 : Blo 1613005 2420651 := bstep (se 1 (by rfl) ⟨1815488, by rfl⟩ : syracuseStep 2420651 = 3630977) B3630977
theorem B1724347 : Blo 1613005 1724347 := bstep (se 1 (by rfl) ⟨1293260, by rfl⟩ : syracuseStep 1724347 = 2586521) B2586521
theorem B2420681 : Blo 1613005 2420681 := bstep (se 2 (by rfl) ⟨907755, by rfl⟩ : syracuseStep 2420681 = 1815511) B1815511
theorem B2584619 : Blo 1613005 2584619 := bstep (se 1 (by rfl) ⟨1938464, by rfl⟩ : syracuseStep 2584619 = 3876929) B3876929
theorem B2297899 : Blo 1613005 2297899 := bstep (se 1 (by rfl) ⟨1723424, by rfl⟩ : syracuseStep 2297899 = 3446849) B3446849
theorem B2420795 : Blo 1613005 2420795 := bstep (se 1 (by rfl) ⟨1815596, by rfl⟩ : syracuseStep 2420795 = 3631193) B3631193
theorem B2420855 : Blo 1613005 2420855 := bstep (se 1 (by rfl) ⟨1815641, by rfl⟩ : syracuseStep 2420855 = 3631283) B3631283
theorem B2420879 : Blo 1613005 2420879 := bstep (se 1 (by rfl) ⟨1815659, by rfl⟩ : syracuseStep 2420879 = 3631319) B3631319
theorem B3633299 : Blo 1613005 3633299 := bstep (se 1 (by rfl) ⟨2724974, by rfl⟩ : syracuseStep 3633299 = 5449949) B5449949
theorem B2420921 : Blo 1613005 2420921 := bstep (se 2 (by rfl) ⟨907845, by rfl⟩ : syracuseStep 2420921 = 1815691) B1815691
theorem B3633353 : Blo 1613005 3633353 := bstep (se 2 (by rfl) ⟨1362507, by rfl⟩ : syracuseStep 3633353 = 2725015) B2725015
theorem B6131969 : Blo 1613005 6131969 := bstep (se 2 (by rfl) ⟨2299488, by rfl⟩ : syracuseStep 6131969 = 4598977) B4598977
theorem B1814791 : Blo 1613005 1814791 := bstep (se 1 (by rfl) ⟨1361093, by rfl⟩ : syracuseStep 1814791 = 2722187) B2722187
theorem B2420999 : Blo 1613005 2420999 := bstep (se 1 (by rfl) ⟨1815749, by rfl⟩ : syracuseStep 2420999 = 3631499) B3631499
theorem B4083979 : Blo 1613005 4083979 := bstep (se 1 (by rfl) ⟨3062984, by rfl⟩ : syracuseStep 4083979 = 6125969) B6125969
theorem B2298127 : Blo 1613005 2298127 := bstep (se 1 (by rfl) ⟨1723595, by rfl⟩ : syracuseStep 2298127 = 3447191) B3447191
theorem B4657441 : Blo 1613005 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B2421035 : Blo 1613005 2421035 := bstep (se 1 (by rfl) ⟨1815776, by rfl⟩ : syracuseStep 2421035 = 3631553) B3631553
theorem B34918721 : Blo 1613005 34918721 := bstep (se 2 (by rfl) ⟨13094520, by rfl⟩ : syracuseStep 34918721 = 26189041) B26189041
theorem B2421065 : Blo 1613005 2421065 := bstep (se 2 (by rfl) ⟨907899, by rfl⟩ : syracuseStep 2421065 = 1815799) B1815799
theorem B5443955 : Blo 1613005 5443955 := bstep (se 1 (by rfl) ⟨4082966, by rfl⟩ : syracuseStep 5443955 = 8165933) B8165933
theorem B6295943 : Blo 1613005 6295943 := bstep (se 1 (by rfl) ⟨4721957, by rfl⟩ : syracuseStep 6295943 = 9443915) B9443915
theorem B4084121 : Blo 1613005 4084121 := bstep (se 2 (by rfl) ⟨1531545, by rfl⟩ : syracuseStep 4084121 = 3063091) B3063091
theorem B9187769 : Blo 1613005 9187769 := bstep (se 2 (by rfl) ⟨3445413, by rfl⟩ : syracuseStep 9187769 = 6890827) B6890827
theorem B1814971 : Blo 1613005 1814971 := bstep (se 1 (by rfl) ⟨1361228, by rfl⟩ : syracuseStep 1814971 = 2722457) B2722457
theorem B8843705 : Blo 1613005 8843705 := bstep (se 2 (by rfl) ⟨3316389, by rfl⟩ : syracuseStep 8843705 = 6632779) B6632779
theorem B2421179 : Blo 1613005 2421179 := bstep (se 1 (by rfl) ⟨1815884, by rfl⟩ : syracuseStep 2421179 = 3631769) B3631769
theorem B15503825 : Blo 1613005 15503825 := bstep (se 2 (by rfl) ⟨5813934, by rfl⟩ : syracuseStep 15503825 = 11627869) B11627869
theorem B2421239 : Blo 1613005 2421239 := bstep (se 1 (by rfl) ⟨1815929, by rfl⟩ : syracuseStep 2421239 = 3631859) B3631859
theorem B2421263 : Blo 1613005 2421263 := bstep (se 1 (by rfl) ⟨1815947, by rfl⟩ : syracuseStep 2421263 = 3631895) B3631895
theorem B2724367 : Blo 1613005 2724367 := bstep (se 1 (by rfl) ⟨2043275, by rfl⟩ : syracuseStep 2724367 = 4086551) B4086551
theorem B2421305 : Blo 1613005 2421305 := bstep (se 2 (by rfl) ⟨907989, by rfl⟩ : syracuseStep 2421305 = 1815979) B1815979
theorem B4084283 : Blo 1613005 4084283 := bstep (se 1 (by rfl) ⟨3063212, by rfl⟩ : syracuseStep 4084283 = 6126425) B6126425
theorem B2421383 : Blo 1613005 2421383 := bstep (se 1 (by rfl) ⟨1816037, by rfl⟩ : syracuseStep 2421383 = 3632075) B3632075
theorem B2298503 : Blo 1613005 2298503 := bstep (se 1 (by rfl) ⟨1723877, by rfl⟩ : syracuseStep 2298503 = 3447755) B3447755
theorem B3879571 : Blo 1613005 3879571 := bstep (se 1 (by rfl) ⟨2909678, by rfl⟩ : syracuseStep 3879571 = 5819357) B5819357
theorem B2421419 : Blo 1613005 2421419 := bstep (se 1 (by rfl) ⟨1816064, by rfl⟩ : syracuseStep 2421419 = 3632129) B3632129
theorem B2421449 : Blo 1613005 2421449 := bstep (se 2 (by rfl) ⟨908043, by rfl⟩ : syracuseStep 2421449 = 1816087) B1816087
theorem B17453825 : Blo 1613005 17453825 := bstep (se 2 (by rfl) ⟨6545184, by rfl⟩ : syracuseStep 17453825 = 13090369) B13090369
theorem B2421563 : Blo 1613005 2421563 := bstep (se 1 (by rfl) ⟨1816172, by rfl⟩ : syracuseStep 2421563 = 3632345) B3632345
theorem B2454391 : Blo 1613005 2454391 := bstep (se 1 (by rfl) ⟨1840793, by rfl⟩ : syracuseStep 2454391 = 3681587) B3681587
theorem B2421623 : Blo 1613005 2421623 := bstep (se 1 (by rfl) ⟨1816217, by rfl⟩ : syracuseStep 2421623 = 3632435) B3632435
theorem B1815439 : Blo 1613005 1815439 := bstep (se 1 (by rfl) ⟨1361579, by rfl⟩ : syracuseStep 1815439 = 2723159) B2723159
theorem B2421647 : Blo 1613005 2421647 := bstep (se 1 (by rfl) ⟨1816235, by rfl⟩ : syracuseStep 2421647 = 3632471) B3632471
theorem B4084627 : Blo 1613005 4084627 := bstep (se 1 (by rfl) ⟨3063470, by rfl⟩ : syracuseStep 4084627 = 6126941) B6126941
theorem B2421689 : Blo 1613005 2421689 := bstep (se 2 (by rfl) ⟨908133, by rfl⟩ : syracuseStep 2421689 = 1816267) B1816267
theorem B2421767 : Blo 1613005 2421767 := bstep (se 1 (by rfl) ⟨1816325, by rfl⟩ : syracuseStep 2421767 = 3632651) B3632651
theorem B4084769 : Blo 1613005 4084769 := bstep (se 2 (by rfl) ⟨1531788, by rfl⟩ : syracuseStep 4084769 = 3063577) B3063577
theorem B7754795 : Blo 1613005 7754795 := bstep (se 1 (by rfl) ⟨5816096, by rfl⟩ : syracuseStep 7754795 = 11632193) B11632193
theorem B2421803 : Blo 1613005 2421803 := bstep (se 1 (by rfl) ⟨1816352, by rfl⟩ : syracuseStep 2421803 = 3632705) B3632705
theorem B2724907 : Blo 1613005 2724907 := bstep (se 1 (by rfl) ⟨2043680, by rfl⟩ : syracuseStep 2724907 = 4087361) B4087361
theorem B2421833 : Blo 1613005 2421833 := bstep (se 2 (by rfl) ⟨908187, by rfl⟩ : syracuseStep 2421833 = 1816375) B1816375
theorem B2487415 : Blo 1613005 2487415 := bstep (se 1 (by rfl) ⟨1865561, by rfl⟩ : syracuseStep 2487415 = 3731123) B3731123
theorem B2725049 : Blo 1613005 2725049 := bstep (se 2 (by rfl) ⟨1021893, by rfl⟩ : syracuseStep 2725049 = 2043787) B2043787
theorem B2421947 : Blo 1613005 2421947 := bstep (se 1 (by rfl) ⟨1816460, by rfl⟩ : syracuseStep 2421947 = 3632921) B3632921
theorem B8172737 : Blo 1613005 8172737 := bstep (se 2 (by rfl) ⟨3064776, by rfl⟩ : syracuseStep 8172737 = 6129553) B6129553
theorem B2422007 : Blo 1613005 2422007 := bstep (se 1 (by rfl) ⟨1816505, by rfl⟩ : syracuseStep 2422007 = 3633011) B3633011
theorem B2422031 : Blo 1613005 2422031 := bstep (se 1 (by rfl) ⟨1816523, by rfl⟩ : syracuseStep 2422031 = 3633047) B3633047
theorem B2422073 : Blo 1613005 2422073 := bstep (se 2 (by rfl) ⟨908277, by rfl⟩ : syracuseStep 2422073 = 1816555) B1816555
theorem B11638075 : Blo 1613005 11638075 := bstep (se 1 (by rfl) ⟨8728556, by rfl⟩ : syracuseStep 11638075 = 17457113) B17457113
theorem B39777635 : Blo 1613005 39777635 := bstep (se 1 (by rfl) ⟨29833226, by rfl⟩ : syracuseStep 39777635 = 59666453) B59666453
theorem B6542707 : Blo 1613005 6542707 := bstep (se 1 (by rfl) ⟨4907030, by rfl⟩ : syracuseStep 6542707 = 9814061) B9814061
theorem B1815943 : Blo 1613005 1815943 := bstep (se 1 (by rfl) ⟨1361957, by rfl⟩ : syracuseStep 1815943 = 2723915) B2723915
theorem B2422151 : Blo 1613005 2422151 := bstep (se 1 (by rfl) ⟨1816613, by rfl⟩ : syracuseStep 2422151 = 3633227) B3633227
theorem B2422187 : Blo 1613005 2422187 := bstep (se 1 (by rfl) ⟨1816640, by rfl⟩ : syracuseStep 2422187 = 3633281) B3633281
theorem B2422217 : Blo 1613005 2422217 := bstep (se 2 (by rfl) ⟨908331, by rfl⟩ : syracuseStep 2422217 = 1816663) B1816663
theorem B16569805 : Blo 1613005 16569805 := bstep (se 3 (by rfl) ⟨3106838, by rfl⟩ : syracuseStep 16569805 = 6213677) B6213677
theorem B1816123 : Blo 1613005 1816123 := bstep (se 1 (by rfl) ⟨1362092, by rfl⟩ : syracuseStep 1816123 = 2724185) B2724185
theorem B2422331 : Blo 1613005 2422331 := bstep (se 1 (by rfl) ⟨1816748, by rfl⟩ : syracuseStep 2422331 = 3633497) B3633497
theorem B17446519 : Blo 1613005 17446519 := bstep (se 1 (by rfl) ⟨13084889, by rfl⟩ : syracuseStep 17446519 = 26169779) B26169779
theorem B2422391 : Blo 1613005 2422391 := bstep (se 1 (by rfl) ⟨1816793, by rfl⟩ : syracuseStep 2422391 = 3633587) B3633587
theorem B2422415 : Blo 1613005 2422415 := bstep (se 1 (by rfl) ⟨1816811, by rfl⟩ : syracuseStep 2422415 = 3633623) B3633623
theorem B2422457 : Blo 1613005 2422457 := bstep (se 2 (by rfl) ⟨908421, by rfl⟩ : syracuseStep 2422457 = 1816843) B1816843
theorem B15513281 : Blo 1613005 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B4593419 : Blo 1613005 4593419 := bstep (se 1 (by rfl) ⟨3445064, by rfl⟩ : syracuseStep 4593419 = 6890129) B6890129
theorem B6895475 : Blo 1613005 6895475 := bstep (se 1 (by rfl) ⟨5171606, by rfl⟩ : syracuseStep 6895475 = 10343213) B10343213
theorem B4085761 : Blo 1613005 4085761 := bstep (se 2 (by rfl) ⟨1532160, by rfl⟩ : syracuseStep 4085761 = 3064321) B3064321
theorem B1816591 : Blo 1613005 1816591 := bstep (se 1 (by rfl) ⟨1362443, by rfl⟩ : syracuseStep 1816591 = 2724887) B2724887
theorem B4364321 : Blo 1613005 4364321 := bstep (se 2 (by rfl) ⟨1636620, by rfl⟩ : syracuseStep 4364321 = 3273241) B3273241
theorem B6895817 : Blo 1613005 6895817 := bstep (se 2 (by rfl) ⟨2585931, by rfl⟩ : syracuseStep 6895817 = 5171863) B5171863
theorem B9189683 : Blo 1613005 9189683 := bstep (se 1 (by rfl) ⟨6892262, by rfl⟩ : syracuseStep 9189683 = 13784525) B13784525
theorem B6125939 : Blo 1613005 6125939 := bstep (se 1 (by rfl) ⟨4594454, by rfl⟩ : syracuseStep 6125939 = 9188909) B9188909
theorem B4594067 : Blo 1613005 4594067 := bstep (se 1 (by rfl) ⟨3445550, by rfl⟩ : syracuseStep 4594067 = 6891101) B6891101
theorem B12261779 : Blo 1613005 12261779 := bstep (se 1 (by rfl) ⟨9196334, by rfl⟩ : syracuseStep 12261779 = 18392669) B18392669
theorem B8174033 : Blo 1613005 8174033 := bstep (se 2 (by rfl) ⟨3065262, by rfl⟩ : syracuseStep 8174033 = 6130525) B6130525
theorem B4086359 : Blo 1613005 4086359 := bstep (se 1 (by rfl) ⟨3064769, by rfl⟩ : syracuseStep 4086359 = 6129539) B6129539
theorem B4594295 : Blo 1613005 4594295 := bstep (se 1 (by rfl) ⟨3445721, by rfl⟩ : syracuseStep 4594295 = 6891443) B6891443
theorem B9812717 : Blo 1613005 9812717 := bstep (se 3 (by rfl) ⟨1839884, by rfl⟩ : syracuseStep 9812717 = 3679769) B3679769
theorem B13982501 : Blo 1613005 13982501 := bstep (se 4 (by rfl) ⟨1310859, by rfl⟩ : syracuseStep 13982501 = 2621719) B2621719
theorem B4086571 : Blo 1613005 4086571 := bstep (se 1 (by rfl) ⟨3064928, by rfl⟩ : syracuseStep 4086571 = 6129857) B6129857
theorem B12254003 : Blo 1613005 12254003 := bstep (se 1 (by rfl) ⟨9190502, by rfl⟩ : syracuseStep 12254003 = 18381005) B18381005
theorem B5446547 : Blo 1613005 5446547 := bstep (se 1 (by rfl) ⟨4084910, by rfl⟩ : syracuseStep 5446547 = 8169821) B8169821
theorem B2759609 : Blo 1613005 2759609 := bstep (se 2 (by rfl) ⟨1034853, by rfl⟩ : syracuseStep 2759609 = 2069707) B2069707
theorem B4086713 : Blo 1613005 4086713 := bstep (se 2 (by rfl) ⟨1532517, by rfl⟩ : syracuseStep 4086713 = 3065035) B3065035
theorem B5979203 : Blo 1613005 5979203 := bstep (se 1 (by rfl) ⟨4484402, by rfl⟩ : syracuseStep 5979203 = 8968805) B8968805
theorem B1613063 : Blo 1613005 1613063 := bstep (se 1 (by rfl) ⟨1209797, by rfl⟩ : syracuseStep 1613063 = 2419595) B2419595
theorem B1613071 : Blo 1613005 1613071 := bstep (se 1 (by rfl) ⟨1209803, by rfl⟩ : syracuseStep 1613071 = 2419607) B2419607
theorem B1613115 : Blo 1613005 1613115 := bstep (se 1 (by rfl) ⟨1209836, by rfl⟩ : syracuseStep 1613115 = 2419673) B2419673
theorem B15514973 : Blo 1613005 15514973 := bstep (se 3 (by rfl) ⟨2909057, by rfl⟩ : syracuseStep 15514973 = 5818115) B5818115
theorem B1613191 : Blo 1613005 1613191 := bstep (se 1 (by rfl) ⟨1209893, by rfl⟩ : syracuseStep 1613191 = 2419787) B2419787
theorem B5168519 : Blo 1613005 5168519 := bstep (se 1 (by rfl) ⟨3876389, by rfl⟩ : syracuseStep 5168519 = 7752779) B7752779
theorem B1613199 : Blo 1613005 1613199 := bstep (se 1 (by rfl) ⟨1209899, by rfl⟩ : syracuseStep 1613199 = 2419799) B2419799
theorem B5168531 : Blo 1613005 5168531 := bstep (se 1 (by rfl) ⟨3876398, by rfl⟩ : syracuseStep 5168531 = 7752797) B7752797
theorem B1613243 : Blo 1613005 1613243 := bstep (se 1 (by rfl) ⟨1209932, by rfl⟩ : syracuseStep 1613243 = 2419865) B2419865
theorem B17456593 : Blo 1613005 17456593 := bstep (se 2 (by rfl) ⟨6546222, by rfl⟩ : syracuseStep 17456593 = 13092445) B13092445
theorem B1613319 : Blo 1613005 1613319 := bstep (se 1 (by rfl) ⟨1209989, by rfl⟩ : syracuseStep 1613319 = 2419979) B2419979
theorem B1613327 : Blo 1613005 1613327 := bstep (se 1 (by rfl) ⟨1209995, by rfl⟩ : syracuseStep 1613327 = 2419991) B2419991
theorem B1613371 : Blo 1613005 1613371 := bstep (se 1 (by rfl) ⟨1210028, by rfl⟩ : syracuseStep 1613371 = 2420057) B2420057
theorem B1613447 : Blo 1613005 1613447 := bstep (se 1 (by rfl) ⟨1210085, by rfl⟩ : syracuseStep 1613447 = 2420171) B2420171
theorem B1613455 : Blo 1613005 1613455 := bstep (se 1 (by rfl) ⟨1210091, by rfl⟩ : syracuseStep 1613455 = 2420183) B2420183
theorem B1613499 : Blo 1613005 1613499 := bstep (se 1 (by rfl) ⟨1210124, by rfl⟩ : syracuseStep 1613499 = 2420249) B2420249
theorem B9191141 : Blo 1613005 9191141 := bstep (se 4 (by rfl) ⟨861669, by rfl⟩ : syracuseStep 9191141 = 1723339) B1723339
theorem B1613575 : Blo 1613005 1613575 := bstep (se 1 (by rfl) ⟨1210181, by rfl⟩ : syracuseStep 1613575 = 2420363) B2420363
theorem B1613583 : Blo 1613005 1613583 := bstep (se 1 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 1613583 = 2420375) B2420375
theorem B5168929 : Blo 1613005 5168929 := bstep (se 2 (by rfl) ⟨1938348, by rfl⟩ : syracuseStep 5168929 = 3876697) B3876697
theorem B1613627 : Blo 1613005 1613627 := bstep (se 1 (by rfl) ⟨1210220, by rfl⟩ : syracuseStep 1613627 = 2420441) B2420441
theorem B1613703 : Blo 1613005 1613703 := bstep (se 1 (by rfl) ⟨1210277, by rfl⟩ : syracuseStep 1613703 = 2420555) B2420555
theorem B1613711 : Blo 1613005 1613711 := bstep (se 1 (by rfl) ⟨1210283, by rfl⟩ : syracuseStep 1613711 = 2420567) B2420567
theorem B5169043 : Blo 1613005 5169043 := bstep (se 1 (by rfl) ⟨3876782, by rfl⟩ : syracuseStep 5169043 = 7753565) B7753565
theorem B104677271 : Blo 1613005 104677271 := bstep (se 1 (by rfl) ⟨78507953, by rfl⟩ : syracuseStep 104677271 = 157015907) B157015907
theorem B4087705 : Blo 1613005 4087705 := bstep (se 2 (by rfl) ⟨1532889, by rfl⟩ : syracuseStep 4087705 = 3065779) B3065779
theorem B3063737 : Blo 1613005 3063737 := bstep (se 2 (by rfl) ⟨1148901, by rfl⟩ : syracuseStep 3063737 = 2297803) B2297803
theorem B1613755 : Blo 1613005 1613755 := bstep (se 1 (by rfl) ⟨1210316, by rfl⟩ : syracuseStep 1613755 = 2420633) B2420633
theorem B5447681 : Blo 1613005 5447681 := bstep (se 2 (by rfl) ⟨2042880, by rfl⟩ : syracuseStep 5447681 = 4085761) B4085761
theorem B1613863 : Blo 1613005 1613863 := bstep (se 1 (by rfl) ⟨1210397, by rfl⟩ : syracuseStep 1613863 = 2420795) B2420795
theorem B1613903 : Blo 1613005 1613903 := bstep (se 1 (by rfl) ⟨1210427, by rfl⟩ : syracuseStep 1613903 = 2420855) B2420855
theorem B1613919 : Blo 1613005 1613919 := bstep (se 1 (by rfl) ⟨1210439, by rfl⟩ : syracuseStep 1613919 = 2420879) B2420879
theorem B1613947 : Blo 1613005 1613947 := bstep (se 1 (by rfl) ⟨1210460, by rfl⟩ : syracuseStep 1613947 = 2420921) B2420921
theorem B4087979 : Blo 1613005 4087979 := bstep (se 1 (by rfl) ⟨3065984, by rfl⟩ : syracuseStep 4087979 = 6131969) B6131969
theorem B1613999 : Blo 1613005 1613999 := bstep (se 1 (by rfl) ⟨1210499, by rfl⟩ : syracuseStep 1613999 = 2420999) B2420999
theorem B1614023 : Blo 1613005 1614023 := bstep (se 1 (by rfl) ⟨1210517, by rfl⟩ : syracuseStep 1614023 = 2421035) B2421035
theorem B1614043 : Blo 1613005 1614043 := bstep (se 1 (by rfl) ⟨1210532, by rfl⟩ : syracuseStep 1614043 = 2421065) B2421065
theorem B12255461 : Blo 1613005 12255461 := bstep (se 4 (by rfl) ⟨1148949, by rfl⟩ : syracuseStep 12255461 = 2297899) B2297899
theorem B3629303 : Blo 1613005 3629303 := bstep (se 1 (by rfl) ⟨2721977, by rfl⟩ : syracuseStep 3629303 = 5443955) B5443955
theorem B6127883 : Blo 1613005 6127883 := bstep (se 1 (by rfl) ⟨4595912, by rfl⟩ : syracuseStep 6127883 = 9191825) B9191825
theorem B1614119 : Blo 1613005 1614119 := bstep (se 1 (by rfl) ⟨1210589, by rfl⟩ : syracuseStep 1614119 = 2421179) B2421179
theorem B1614159 : Blo 1613005 1614159 := bstep (se 1 (by rfl) ⟨1210619, by rfl⟩ : syracuseStep 1614159 = 2421239) B2421239
theorem B1614175 : Blo 1613005 1614175 := bstep (se 1 (by rfl) ⟨1210631, by rfl⟩ : syracuseStep 1614175 = 2421263) B2421263
theorem B3064169 : Blo 1613005 3064169 := bstep (se 2 (by rfl) ⟨1149063, by rfl⟩ : syracuseStep 3064169 = 2298127) B2298127
theorem B1614203 : Blo 1613005 1614203 := bstep (se 1 (by rfl) ⟨1210652, by rfl⟩ : syracuseStep 1614203 = 2421305) B2421305
theorem B6209921 : Blo 1613005 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B1614255 : Blo 1613005 1614255 := bstep (se 1 (by rfl) ⟨1210691, by rfl⟩ : syracuseStep 1614255 = 2421383) B2421383
theorem B1614279 : Blo 1613005 1614279 := bstep (se 1 (by rfl) ⟨1210709, by rfl⟩ : syracuseStep 1614279 = 2421419) B2421419
theorem B1614299 : Blo 1613005 1614299 := bstep (se 1 (by rfl) ⟨1210724, by rfl⟩ : syracuseStep 1614299 = 2421449) B2421449
theorem B27591191 : Blo 1613005 27591191 := bstep (se 1 (by rfl) ⟨20693393, by rfl⟩ : syracuseStep 27591191 = 41386787) B41386787
theorem B1614375 : Blo 1613005 1614375 := bstep (se 1 (by rfl) ⟨1210781, by rfl⟩ : syracuseStep 1614375 = 2421563) B2421563
theorem B1614415 : Blo 1613005 1614415 := bstep (se 1 (by rfl) ⟨1210811, by rfl⟩ : syracuseStep 1614415 = 2421623) B2421623
theorem B1614431 : Blo 1613005 1614431 := bstep (se 1 (by rfl) ⟨1210823, by rfl⟩ : syracuseStep 1614431 = 2421647) B2421647
theorem B5169761 : Blo 1613005 5169761 := bstep (se 2 (by rfl) ⟨1938660, by rfl⟩ : syracuseStep 5169761 = 3877321) B3877321
theorem B1614459 : Blo 1613005 1614459 := bstep (se 1 (by rfl) ⟨1210844, by rfl⟩ : syracuseStep 1614459 = 2421689) B2421689
theorem B1614511 : Blo 1613005 1614511 := bstep (se 1 (by rfl) ⟨1210883, by rfl⟩ : syracuseStep 1614511 = 2421767) B2421767
theorem B5169863 : Blo 1613005 5169863 := bstep (se 1 (by rfl) ⟨3877397, by rfl⟩ : syracuseStep 5169863 = 7754795) B7754795
theorem B1614535 : Blo 1613005 1614535 := bstep (se 1 (by rfl) ⟨1210901, by rfl⟩ : syracuseStep 1614535 = 2421803) B2421803
theorem B1614555 : Blo 1613005 1614555 := bstep (se 1 (by rfl) ⟨1210916, by rfl⟩ : syracuseStep 1614555 = 2421833) B2421833
theorem B1614631 : Blo 1613005 1614631 := bstep (se 1 (by rfl) ⟨1210973, by rfl⟩ : syracuseStep 1614631 = 2421947) B2421947
theorem B5448491 : Blo 1613005 5448491 := bstep (se 1 (by rfl) ⟨4086368, by rfl⟩ : syracuseStep 5448491 = 8172737) B8172737
theorem B3629897 : Blo 1613005 3629897 := bstep (se 2 (by rfl) ⟨1361211, by rfl⟩ : syracuseStep 3629897 = 2722423) B2722423
theorem B1614671 : Blo 1613005 1614671 := bstep (se 1 (by rfl) ⟨1211003, by rfl⟩ : syracuseStep 1614671 = 2422007) B2422007
theorem B1614687 : Blo 1613005 1614687 := bstep (se 1 (by rfl) ⟨1211015, by rfl⟩ : syracuseStep 1614687 = 2422031) B2422031
theorem B1614715 : Blo 1613005 1614715 := bstep (se 1 (by rfl) ⟨1211036, by rfl⟩ : syracuseStep 1614715 = 2422073) B2422073
theorem B26518423 : Blo 1613005 26518423 := bstep (se 1 (by rfl) ⟨19888817, by rfl⟩ : syracuseStep 26518423 = 39777635) B39777635
theorem B1614767 : Blo 1613005 1614767 := bstep (se 1 (by rfl) ⟨1211075, by rfl⟩ : syracuseStep 1614767 = 2422151) B2422151
theorem B6128567 : Blo 1613005 6128567 := bstep (se 1 (by rfl) ⟨4596425, by rfl⟩ : syracuseStep 6128567 = 9192851) B9192851
theorem B1614791 : Blo 1613005 1614791 := bstep (se 1 (by rfl) ⟨1211093, by rfl⟩ : syracuseStep 1614791 = 2422187) B2422187
theorem B1614811 : Blo 1613005 1614811 := bstep (se 1 (by rfl) ⟨1211108, by rfl⟩ : syracuseStep 1614811 = 2422217) B2422217
theorem B1614887 : Blo 1613005 1614887 := bstep (se 1 (by rfl) ⟨1211165, by rfl⟩ : syracuseStep 1614887 = 2422331) B2422331
theorem B18383921 : Blo 1613005 18383921 := bstep (se 2 (by rfl) ⟨6893970, by rfl⟩ : syracuseStep 18383921 = 13787941) B13787941
theorem B5448761 : Blo 1613005 5448761 := bstep (se 2 (by rfl) ⟨2043285, by rfl⟩ : syracuseStep 5448761 = 4086571) B4086571
theorem B1614927 : Blo 1613005 1614927 := bstep (se 1 (by rfl) ⟨1211195, by rfl⟩ : syracuseStep 1614927 = 2422391) B2422391
theorem B1614943 : Blo 1613005 1614943 := bstep (se 1 (by rfl) ⟨1211207, by rfl⟩ : syracuseStep 1614943 = 2422415) B2422415
theorem B1614971 : Blo 1613005 1614971 := bstep (se 1 (by rfl) ⟨1211228, by rfl⟩ : syracuseStep 1614971 = 2422457) B2422457
theorem B4596983 : Blo 1613005 4596983 := bstep (se 1 (by rfl) ⟨3447737, by rfl⟩ : syracuseStep 4596983 = 6895475) B6895475
theorem B3065195 : Blo 1613005 3065195 := bstep (se 1 (by rfl) ⟨2298896, by rfl⟩ : syracuseStep 3065195 = 4597793) B4597793
theorem B5449085 : Blo 1613005 5449085 := bstep (se 3 (by rfl) ⟨1021703, by rfl⟩ : syracuseStep 5449085 = 2043407) B2043407
theorem B4597211 : Blo 1613005 4597211 := bstep (se 1 (by rfl) ⟨3447908, by rfl⟩ : syracuseStep 4597211 = 6895817) B6895817
theorem B2180647 : Blo 1613005 2180647 := bstep (se 1 (by rfl) ⟨1635485, by rfl⟩ : syracuseStep 2180647 = 3270971) B3270971
theorem B3630689 : Blo 1613005 3630689 := bstep (se 2 (by rfl) ⟨1361508, by rfl⟩ : syracuseStep 3630689 = 2723017) B2723017
theorem B5449355 : Blo 1613005 5449355 := bstep (se 1 (by rfl) ⟨4087016, by rfl⟩ : syracuseStep 5449355 = 8174033) B8174033
theorem B6129341 : Blo 1613005 6129341 := bstep (se 3 (by rfl) ⟨1149251, by rfl⟩ : syracuseStep 6129341 = 2298503) B2298503
theorem B17450711 : Blo 1613005 17450711 := bstep (se 1 (by rfl) ⟨13088033, by rfl⟩ : syracuseStep 17450711 = 26176067) B26176067
theorem B15517433 : Blo 1613005 15517433 := bstep (se 2 (by rfl) ⟨5819037, by rfl⟩ : syracuseStep 15517433 = 11638075) B11638075
theorem B11634475 : Blo 1613005 11634475 := bstep (se 1 (by rfl) ⟨8725856, by rfl⟩ : syracuseStep 11634475 = 17451713) B17451713
theorem B9193283 : Blo 1613005 9193283 := bstep (se 1 (by rfl) ⟨6894962, by rfl⟩ : syracuseStep 9193283 = 13789925) B13789925
theorem B8169335 : Blo 1613005 8169335 := bstep (se 1 (by rfl) ⟨6127001, by rfl⟩ : syracuseStep 8169335 = 12254003) B12254003
theorem B3631031 : Blo 1613005 3631031 := bstep (se 1 (by rfl) ⟨2723273, by rfl⟩ : syracuseStep 3631031 = 5446547) B5446547
theorem B23275457 : Blo 1613005 23275457 := bstep (se 2 (by rfl) ⟨8728296, by rfl⟩ : syracuseStep 23275457 = 17456593) B17456593
theorem B16566275 : Blo 1613005 16566275 := bstep (se 1 (by rfl) ⟨12424706, by rfl⟩ : syracuseStep 16566275 = 24849413) B24849413
theorem B3065863 : Blo 1613005 3065863 := bstep (se 1 (by rfl) ⟨2299397, by rfl⟩ : syracuseStep 3065863 = 4598795) B4598795
theorem B2721991 : Blo 1613005 2721991 := bstep (se 1 (by rfl) ⟨2041493, by rfl⟩ : syracuseStep 2721991 = 4082987) B4082987
theorem B2722153 : Blo 1613005 2722153 := bstep (se 2 (by rfl) ⟨1020807, by rfl⟩ : syracuseStep 2722153 = 2041615) B2041615
theorem B6130025 : Blo 1613005 6130025 := bstep (se 2 (by rfl) ⟨2298759, by rfl⟩ : syracuseStep 6130025 = 4597519) B4597519
theorem B6547817 : Blo 1613005 6547817 := bstep (se 2 (by rfl) ⟨2455431, by rfl⟩ : syracuseStep 6547817 = 4910863) B4910863
theorem B6891905 : Blo 1613005 6891905 := bstep (se 2 (by rfl) ⟨2584464, by rfl⟩ : syracuseStep 6891905 = 5168929) B5168929
theorem B23267735 : Blo 1613005 23267735 := bstep (se 1 (by rfl) ⟨17450801, by rfl⟩ : syracuseStep 23267735 = 34901603) B34901603
theorem B3631625 : Blo 1613005 3631625 := bstep (se 2 (by rfl) ⟨1361859, by rfl⟩ : syracuseStep 3631625 = 2723719) B2723719
theorem B6892057 : Blo 1613005 6892057 := bstep (se 2 (by rfl) ⟨2584521, by rfl⟩ : syracuseStep 6892057 = 5169043) B5169043
theorem B5450273 : Blo 1613005 5450273 := bstep (se 2 (by rfl) ⟨2043852, by rfl⟩ : syracuseStep 5450273 = 4087705) B4087705
theorem B2042491 : Blo 1613005 2042491 := bstep (se 1 (by rfl) ⟨1531868, by rfl⟩ : syracuseStep 2042491 = 3063737) B3063737
theorem B1723079 : Blo 1613005 1723079 := bstep (se 1 (by rfl) ⟨1292309, by rfl⟩ : syracuseStep 1723079 = 2584619) B2584619
theorem B5450489 : Blo 1613005 5450489 := bstep (se 2 (by rfl) ⟨2043933, by rfl⟩ : syracuseStep 5450489 = 4087867) B4087867
theorem B3631967 : Blo 1613005 3631967 := bstep (se 1 (by rfl) ⟨2723975, by rfl⟩ : syracuseStep 3631967 = 5447951) B5447951
theorem B4598623 : Blo 1613005 4598623 := bstep (se 1 (by rfl) ⟨3448967, by rfl⟩ : syracuseStep 4598623 = 6897935) B6897935
theorem B2419631 : Blo 1613005 2419631 := bstep (se 1 (by rfl) ⟨1814723, by rfl⟩ : syracuseStep 2419631 = 3629447) B3629447
theorem B4197295 : Blo 1613005 4197295 := bstep (se 1 (by rfl) ⟨3147971, by rfl⟩ : syracuseStep 4197295 = 6295943) B6295943
theorem B2722747 : Blo 1613005 2722747 := bstep (se 1 (by rfl) ⟨2042060, by rfl⟩ : syracuseStep 2722747 = 4084121) B4084121
theorem B2419721 : Blo 1613005 2419721 := bstep (se 2 (by rfl) ⟨907395, by rfl⟩ : syracuseStep 2419721 = 1814791) B1814791
theorem B3632147 : Blo 1613005 3632147 := bstep (se 1 (by rfl) ⟨2724110, by rfl⟩ : syracuseStep 3632147 = 5448221) B5448221
theorem B2419751 : Blo 1613005 2419751 := bstep (se 1 (by rfl) ⟨1814813, by rfl⟩ : syracuseStep 2419751 = 3629627) B3629627
theorem B2722855 : Blo 1613005 2722855 := bstep (se 1 (by rfl) ⟨2042141, by rfl⟩ : syracuseStep 2722855 = 4084283) B4084283
theorem B2419835 : Blo 1613005 2419835 := bstep (se 1 (by rfl) ⟨1814876, by rfl⟩ : syracuseStep 2419835 = 3629753) B3629753
theorem B11635883 : Blo 1613005 11635883 := bstep (se 1 (by rfl) ⟨8726912, by rfl⟩ : syracuseStep 11635883 = 17453825) B17453825
theorem B2419961 : Blo 1613005 2419961 := bstep (se 2 (by rfl) ⟨907485, by rfl⟩ : syracuseStep 2419961 = 1814971) B1814971
theorem B2420063 : Blo 1613005 2420063 := bstep (se 1 (by rfl) ⟨1815047, by rfl⟩ : syracuseStep 2420063 = 3630095) B3630095
theorem B3632489 : Blo 1613005 3632489 := bstep (se 2 (by rfl) ⟨1362183, by rfl⟩ : syracuseStep 3632489 = 2724367) B2724367
theorem B2420075 : Blo 1613005 2420075 := bstep (se 1 (by rfl) ⟨1815056, by rfl⟩ : syracuseStep 2420075 = 3630113) B3630113
theorem B2723179 : Blo 1613005 2723179 := bstep (se 1 (by rfl) ⟨2042384, by rfl⟩ : syracuseStep 2723179 = 4084769) B4084769
theorem B5172761 : Blo 1613005 5172761 := bstep (se 2 (by rfl) ⟨1939785, by rfl⟩ : syracuseStep 5172761 = 3879571) B3879571
theorem B2420303 : Blo 1613005 2420303 := bstep (se 1 (by rfl) ⟨1815227, by rfl⟩ : syracuseStep 2420303 = 3630455) B3630455
theorem B2420423 : Blo 1613005 2420423 := bstep (se 1 (by rfl) ⟨1815317, by rfl⟩ : syracuseStep 2420423 = 3630635) B3630635
theorem B10342187 : Blo 1613005 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B2420585 : Blo 1613005 2420585 := bstep (se 2 (by rfl) ⟨907719, by rfl⟩ : syracuseStep 2420585 = 1815439) B1815439
theorem B26161015 : Blo 1613005 26161015 := bstep (se 1 (by rfl) ⟨19620761, by rfl⟩ : syracuseStep 26161015 = 39241523) B39241523
theorem B2420663 : Blo 1613005 2420663 := bstep (se 1 (by rfl) ⟨1815497, by rfl⟩ : syracuseStep 2420663 = 3630995) B3630995
theorem B3633083 : Blo 1613005 3633083 := bstep (se 1 (by rfl) ⟨2724812, by rfl⟩ : syracuseStep 3633083 = 5449625) B5449625
theorem B2420699 : Blo 1613005 2420699 := bstep (se 1 (by rfl) ⟨1815524, by rfl⟩ : syracuseStep 2420699 = 3631049) B3631049
theorem B17018909 : Blo 1613005 17018909 := bstep (se 3 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 17018909 = 6382091) B6382091
theorem B3633209 : Blo 1613005 3633209 := bstep (se 2 (by rfl) ⟨1362453, by rfl⟩ : syracuseStep 3633209 = 2724907) B2724907
theorem B4083959 : Blo 1613005 4083959 := bstep (se 1 (by rfl) ⟨3062969, by rfl⟩ : syracuseStep 4083959 = 6125939) B6125939
theorem B5443901 : Blo 1613005 5443901 := bstep (se 3 (by rfl) ⟨1020731, by rfl⟩ : syracuseStep 5443901 = 2041463) B2041463
theorem B2724239 : Blo 1613005 2724239 := bstep (se 1 (by rfl) ⟨2043179, by rfl⟩ : syracuseStep 2724239 = 4086359) B4086359
theorem B3633551 : Blo 1613005 3633551 := bstep (se 1 (by rfl) ⟨2725163, by rfl⟩ : syracuseStep 3633551 = 5450327) B5450327
theorem B13087129 : Blo 1613005 13087129 := bstep (se 2 (by rfl) ⟨4907673, by rfl⟩ : syracuseStep 13087129 = 9815347) B9815347
theorem B2421167 : Blo 1613005 2421167 := bstep (se 1 (by rfl) ⟨1815875, by rfl⟩ : syracuseStep 2421167 = 3631751) B3631751
theorem B6541811 : Blo 1613005 6541811 := bstep (se 1 (by rfl) ⟨4906358, by rfl⟩ : syracuseStep 6541811 = 9812717) B9812717
theorem B22385161 : Blo 1613005 22385161 := bstep (se 2 (by rfl) ⟨8394435, by rfl⟩ : syracuseStep 22385161 = 16788871) B16788871
theorem B2421257 : Blo 1613005 2421257 := bstep (se 2 (by rfl) ⟨907971, by rfl⟩ : syracuseStep 2421257 = 1815943) B1815943
theorem B1815079 : Blo 1613005 1815079 := bstep (se 1 (by rfl) ⟨1361309, by rfl⟩ : syracuseStep 1815079 = 2722619) B2722619
theorem B2421287 : Blo 1613005 2421287 := bstep (se 1 (by rfl) ⟨1815965, by rfl⟩ : syracuseStep 2421287 = 3631931) B3631931
theorem B3445345 : Blo 1613005 3445345 := bstep (se 2 (by rfl) ⟨1292004, by rfl⟩ : syracuseStep 3445345 = 2584009) B2584009
theorem B1839739 : Blo 1613005 1839739 := bstep (se 1 (by rfl) ⟨1379804, by rfl⟩ : syracuseStep 1839739 = 2759609) B2759609
theorem B2421371 : Blo 1613005 2421371 := bstep (se 1 (by rfl) ⟨1816028, by rfl⟩ : syracuseStep 2421371 = 3632057) B3632057
theorem B2724475 : Blo 1613005 2724475 := bstep (se 1 (by rfl) ⟨2043356, by rfl⟩ : syracuseStep 2724475 = 4086713) B4086713
theorem B3986135 : Blo 1613005 3986135 := bstep (se 1 (by rfl) ⟨2989601, by rfl⟩ : syracuseStep 3986135 = 5979203) B5979203
theorem B2421497 : Blo 1613005 2421497 := bstep (se 2 (by rfl) ⟨908061, by rfl⟩ : syracuseStep 2421497 = 1816123) B1816123
theorem B4199161 : Blo 1613005 4199161 := bstep (se 2 (by rfl) ⟨1574685, by rfl⟩ : syracuseStep 4199161 = 3149371) B3149371
theorem B37286669 : Blo 1613005 37286669 := bstep (se 3 (by rfl) ⟨6991250, by rfl⟩ : syracuseStep 37286669 = 13982501) B13982501
theorem B23262025 : Blo 1613005 23262025 := bstep (se 2 (by rfl) ⟨8723259, by rfl⟩ : syracuseStep 23262025 = 17446519) B17446519
theorem B2421599 : Blo 1613005 2421599 := bstep (se 1 (by rfl) ⟨1816199, by rfl⟩ : syracuseStep 2421599 = 3632399) B3632399
theorem B2421611 : Blo 1613005 2421611 := bstep (se 1 (by rfl) ⟨1816208, by rfl⟩ : syracuseStep 2421611 = 3632417) B3632417
theorem B10343315 : Blo 1613005 10343315 := bstep (se 1 (by rfl) ⟨7757486, by rfl⟩ : syracuseStep 10343315 = 15514973) B15514973
theorem B3445679 : Blo 1613005 3445679 := bstep (se 1 (by rfl) ⟨2584259, by rfl⟩ : syracuseStep 3445679 = 5168519) B5168519
theorem B3445687 : Blo 1613005 3445687 := bstep (se 1 (by rfl) ⟨2584265, by rfl⟩ : syracuseStep 3445687 = 5168531) B5168531
theorem B9196517 : Blo 1613005 9196517 := bstep (se 4 (by rfl) ⟨862173, by rfl⟩ : syracuseStep 9196517 = 1724347) B1724347
theorem B2421839 : Blo 1613005 2421839 := bstep (se 1 (by rfl) ⟨1816379, by rfl⟩ : syracuseStep 2421839 = 3632759) B3632759
theorem B5444765 : Blo 1613005 5444765 := bstep (se 3 (by rfl) ⟨1020893, by rfl⟩ : syracuseStep 5444765 = 2041787) B2041787
theorem B2421959 : Blo 1613005 2421959 := bstep (se 1 (by rfl) ⟨1816469, by rfl⟩ : syracuseStep 2421959 = 3632939) B3632939
theorem B69784847 : Blo 1613005 69784847 := bstep (se 1 (by rfl) ⟨52338635, by rfl⟩ : syracuseStep 69784847 = 104677271) B104677271
theorem B2422121 : Blo 1613005 2422121 := bstep (se 2 (by rfl) ⟨908295, by rfl⟩ : syracuseStep 2422121 = 1816591) B1816591
theorem B11638189 : Blo 1613005 11638189 := bstep (se 3 (by rfl) ⟨2182160, by rfl⟩ : syracuseStep 11638189 = 4364321) B4364321
theorem B1938863 : Blo 1613005 1938863 := bstep (se 1 (by rfl) ⟨1454147, by rfl⟩ : syracuseStep 1938863 = 2908295) B2908295
theorem B9196973 : Blo 1613005 9196973 := bstep (se 3 (by rfl) ⟨1724432, by rfl⟩ : syracuseStep 9196973 = 3448865) B3448865
theorem B2422199 : Blo 1613005 2422199 := bstep (se 1 (by rfl) ⟨1816649, by rfl⟩ : syracuseStep 2422199 = 3633299) B3633299
theorem B2422235 : Blo 1613005 2422235 := bstep (se 1 (by rfl) ⟨1816676, by rfl⟩ : syracuseStep 2422235 = 3633353) B3633353
theorem B23279147 : Blo 1613005 23279147 := bstep (se 1 (by rfl) ⟨17459360, by rfl⟩ : syracuseStep 23279147 = 34918721) B34918721
theorem B6895201 : Blo 1613005 6895201 := bstep (se 2 (by rfl) ⟨2585700, by rfl⟩ : syracuseStep 6895201 = 5171401) B5171401
theorem B6125179 : Blo 1613005 6125179 := bstep (se 1 (by rfl) ⟨4593884, by rfl⟩ : syracuseStep 6125179 = 9187769) B9187769
theorem B5895803 : Blo 1613005 5895803 := bstep (se 1 (by rfl) ⟨4421852, by rfl⟩ : syracuseStep 5895803 = 8843705) B8843705
theorem B10335883 : Blo 1613005 10335883 := bstep (se 1 (by rfl) ⟨7751912, by rfl⟩ : syracuseStep 10335883 = 15503825) B15503825
theorem B4085387 : Blo 1613005 4085387 := bstep (se 1 (by rfl) ⟨3064040, by rfl⟩ : syracuseStep 4085387 = 6128081) B6128081
theorem B5445305 : Blo 1613005 5445305 := bstep (se 2 (by rfl) ⟨2041989, by rfl⟩ : syracuseStep 5445305 = 4083979) B4083979
theorem B4363975 : Blo 1613005 4363975 := bstep (se 1 (by rfl) ⟨3272981, by rfl⟩ : syracuseStep 4363975 = 6545963) B6545963
theorem B13080379 : Blo 1613005 13080379 := bstep (se 1 (by rfl) ⟨9810284, by rfl⟩ : syracuseStep 13080379 = 19620569) B19620569
theorem B4085599 : Blo 1613005 4085599 := bstep (se 1 (by rfl) ⟨3064199, by rfl⟩ : syracuseStep 4085599 = 6128399) B6128399
theorem B5814125 : Blo 1613005 5814125 := bstep (se 3 (by rfl) ⟨1090148, by rfl⟩ : syracuseStep 5814125 = 2180297) B2180297
theorem B1841231 : Blo 1613005 1841231 := bstep (se 1 (by rfl) ⟨1380923, by rfl⟩ : syracuseStep 1841231 = 2761847) B2761847
theorem B9197657 : Blo 1613005 9197657 := bstep (se 2 (by rfl) ⟨3449121, by rfl⟩ : syracuseStep 9197657 = 6898243) B6898243
theorem B1816699 : Blo 1613005 1816699 := bstep (se 1 (by rfl) ⟨1362524, by rfl⟩ : syracuseStep 1816699 = 2725049) B2725049
theorem B5814425 : Blo 1613005 5814425 := bstep (se 2 (by rfl) ⟨2180409, by rfl⟩ : syracuseStep 5814425 = 4360819) B4360819
theorem B5445899 : Blo 1613005 5445899 := bstep (se 1 (by rfl) ⟨4084424, by rfl⟩ : syracuseStep 5445899 = 8168849) B8168849
theorem B181582145 : Blo 1613005 181582145 := bstep (se 2 (by rfl) ⟨68093304, by rfl⟩ : syracuseStep 181582145 = 136186609) B136186609
theorem B3062279 : Blo 1613005 3062279 := bstep (se 1 (by rfl) ⟨2296709, by rfl⟩ : syracuseStep 3062279 = 4593419) B4593419
theorem B5446169 : Blo 1613005 5446169 := bstep (se 2 (by rfl) ⟨2042313, by rfl⟩ : syracuseStep 5446169 = 4084627) B4084627
theorem B5167763 : Blo 1613005 5167763 := bstep (se 1 (by rfl) ⟨3875822, by rfl⟩ : syracuseStep 5167763 = 7751645) B7751645
theorem B4086521 : Blo 1613005 4086521 := bstep (se 2 (by rfl) ⟨1532445, by rfl⟩ : syracuseStep 4086521 = 3064891) B3064891
theorem B5315371 : Blo 1613005 5315371 := bstep (se 1 (by rfl) ⟨3986528, by rfl⟩ : syracuseStep 5315371 = 7973057) B7973057
theorem B3316553 : Blo 1613005 3316553 := bstep (se 2 (by rfl) ⟨1243707, by rfl⟩ : syracuseStep 3316553 = 2487415) B2487415
theorem B6126455 : Blo 1613005 6126455 := bstep (se 1 (by rfl) ⟨4594841, by rfl⟩ : syracuseStep 6126455 = 9189683) B9189683
theorem B3062711 : Blo 1613005 3062711 := bstep (se 1 (by rfl) ⟨2297033, by rfl⟩ : syracuseStep 3062711 = 4594067) B4594067
theorem B8174519 : Blo 1613005 8174519 := bstep (se 1 (by rfl) ⟨6130889, by rfl⟩ : syracuseStep 8174519 = 12261779) B12261779
theorem B8166419 : Blo 1613005 8166419 := bstep (se 1 (by rfl) ⟨6124814, by rfl⟩ : syracuseStep 8166419 = 12249629) B12249629
theorem B3062863 : Blo 1613005 3062863 := bstep (se 1 (by rfl) ⟨2297147, by rfl⟩ : syracuseStep 3062863 = 4594295) B4594295
theorem B117857429 : Blo 1613005 117857429 := bstep (se 6 (by rfl) ⟨2762283, by rfl⟩ : syracuseStep 117857429 = 5524567) B5524567
theorem B8723609 : Blo 1613005 8723609 := bstep (se 2 (by rfl) ⟨3271353, by rfl⟩ : syracuseStep 8723609 = 6542707) B6542707
theorem B1613019 : Blo 1613005 1613019 := bstep (se 1 (by rfl) ⟨1209764, by rfl⟩ : syracuseStep 1613019 = 2419529) B2419529
theorem B22093073 : Blo 1613005 22093073 := bstep (se 2 (by rfl) ⟨8284902, by rfl⟩ : syracuseStep 22093073 = 16569805) B16569805
theorem B13090085 : Blo 1613005 13090085 := bstep (se 4 (by rfl) ⟨1227195, by rfl⟩ : syracuseStep 13090085 = 2454391) B2454391
theorem B1613095 : Blo 1613005 1613095 := bstep (se 1 (by rfl) ⟨1209821, by rfl⟩ : syracuseStep 1613095 = 2419643) B2419643
theorem B1613135 : Blo 1613005 1613135 := bstep (se 1 (by rfl) ⟨1209851, by rfl⟩ : syracuseStep 1613135 = 2419703) B2419703
theorem B1613151 : Blo 1613005 1613151 := bstep (se 1 (by rfl) ⟨1209863, by rfl⟩ : syracuseStep 1613151 = 2419727) B2419727
theorem B1613179 : Blo 1613005 1613179 := bstep (se 1 (by rfl) ⟨1209884, by rfl⟩ : syracuseStep 1613179 = 2419769) B2419769
theorem B4595069 : Blo 1613005 4595069 := bstep (se 3 (by rfl) ⟨861575, by rfl⟩ : syracuseStep 4595069 = 1723151) B1723151
theorem B4087169 : Blo 1613005 4087169 := bstep (se 2 (by rfl) ⟨1532688, by rfl⟩ : syracuseStep 4087169 = 3065377) B3065377
theorem B1613231 : Blo 1613005 1613231 := bstep (se 1 (by rfl) ⟨1209923, by rfl⟩ : syracuseStep 1613231 = 2419847) B2419847
theorem B1613255 : Blo 1613005 1613255 := bstep (se 1 (by rfl) ⟨1209941, by rfl⟩ : syracuseStep 1613255 = 2419883) B2419883
theorem B1613275 : Blo 1613005 1613275 := bstep (se 1 (by rfl) ⟨1209956, by rfl⟩ : syracuseStep 1613275 = 2419913) B2419913
theorem B1613351 : Blo 1613005 1613351 := bstep (se 1 (by rfl) ⟨1210013, by rfl⟩ : syracuseStep 1613351 = 2420027) B2420027
theorem B29466179 : Blo 1613005 29466179 := bstep (se 1 (by rfl) ⟨22099634, by rfl⟩ : syracuseStep 29466179 = 44199269) B44199269
theorem B1613391 : Blo 1613005 1613391 := bstep (se 1 (by rfl) ⟨1210043, by rfl⟩ : syracuseStep 1613391 = 2420087) B2420087
theorem B1613407 : Blo 1613005 1613407 := bstep (se 1 (by rfl) ⟨1210055, by rfl⟩ : syracuseStep 1613407 = 2420111) B2420111
theorem B7560827 : Blo 1613005 7560827 := bstep (se 1 (by rfl) ⟨5670620, by rfl⟩ : syracuseStep 7560827 = 11341241) B11341241
theorem B1613435 : Blo 1613005 1613435 := bstep (se 1 (by rfl) ⟨1210076, by rfl⟩ : syracuseStep 1613435 = 2420153) B2420153
theorem B5447303 : Blo 1613005 5447303 := bstep (se 1 (by rfl) ⟨4085477, by rfl⟩ : syracuseStep 5447303 = 8170955) B8170955
theorem B12279443 : Blo 1613005 12279443 := bstep (se 1 (by rfl) ⟨9209582, by rfl⟩ : syracuseStep 12279443 = 18419165) B18419165
theorem B1613487 : Blo 1613005 1613487 := bstep (se 1 (by rfl) ⟨1210115, by rfl⟩ : syracuseStep 1613487 = 2420231) B2420231
theorem B5447357 : Blo 1613005 5447357 := bstep (se 3 (by rfl) ⟨1021379, by rfl⟩ : syracuseStep 5447357 = 2042759) B2042759
theorem B1613511 : Blo 1613005 1613511 := bstep (se 1 (by rfl) ⟨1210133, by rfl⟩ : syracuseStep 1613511 = 2420267) B2420267
theorem B1613531 : Blo 1613005 1613531 := bstep (se 1 (by rfl) ⟨1210148, by rfl⟩ : syracuseStep 1613531 = 2420297) B2420297
theorem B1613607 : Blo 1613005 1613607 := bstep (se 1 (by rfl) ⟨1210205, by rfl⟩ : syracuseStep 1613607 = 2420411) B2420411
theorem B6127427 : Blo 1613005 6127427 := bstep (se 1 (by rfl) ⟨4595570, by rfl⟩ : syracuseStep 6127427 = 9191141) B9191141
theorem B1613647 : Blo 1613005 1613647 := bstep (se 1 (by rfl) ⟨1210235, by rfl⟩ : syracuseStep 1613647 = 2420471) B2420471
theorem B1613663 : Blo 1613005 1613663 := bstep (se 1 (by rfl) ⟨1210247, by rfl⟩ : syracuseStep 1613663 = 2420495) B2420495
theorem B5447519 : Blo 1613005 5447519 := bstep (se 1 (by rfl) ⟨4085639, by rfl⟩ : syracuseStep 5447519 = 8171279) B8171279
theorem B1613691 : Blo 1613005 1613691 := bstep (se 1 (by rfl) ⟨1210268, by rfl⟩ : syracuseStep 1613691 = 2420537) B2420537
theorem B1613743 : Blo 1613005 1613743 := bstep (se 1 (by rfl) ⟨1210307, by rfl⟩ : syracuseStep 1613743 = 2420615) B2420615
theorem B1613767 : Blo 1613005 1613767 := bstep (se 1 (by rfl) ⟨1210325, by rfl⟩ : syracuseStep 1613767 = 2420651) B2420651
theorem B1613787 : Blo 1613005 1613787 := bstep (se 1 (by rfl) ⟨1210340, by rfl⟩ : syracuseStep 1613787 = 2420681) B2420681
theorem B4087817 : Blo 1613005 4087817 := bstep (se 2 (by rfl) ⟨1532931, by rfl⟩ : syracuseStep 4087817 = 3065863) B3065863
theorem B11345939 : Blo 1613005 11345939 := bstep (se 1 (by rfl) ⟨8509454, by rfl⟩ : syracuseStep 11345939 = 17018909) B17018909
theorem B3629267 : Blo 1613005 3629267 := bstep (se 1 (by rfl) ⟨2721950, by rfl⟩ : syracuseStep 3629267 = 5443901) B5443901
theorem B3629321 : Blo 1613005 3629321 := bstep (se 2 (by rfl) ⟨1360995, by rfl⟩ : syracuseStep 3629321 = 2721991) B2721991
theorem B1614111 : Blo 1613005 1614111 := bstep (se 1 (by rfl) ⟨1210583, by rfl⟩ : syracuseStep 1614111 = 2421167) B2421167
theorem B1614171 : Blo 1613005 1614171 := bstep (se 1 (by rfl) ⟨1210628, by rfl⟩ : syracuseStep 1614171 = 2421257) B2421257
theorem B1614191 : Blo 1613005 1614191 := bstep (se 1 (by rfl) ⟨1210643, by rfl⟩ : syracuseStep 1614191 = 2421287) B2421287
theorem B1614247 : Blo 1613005 1614247 := bstep (se 1 (by rfl) ⟨1210685, by rfl⟩ : syracuseStep 1614247 = 2421371) B2421371
theorem B3629537 : Blo 1613005 3629537 := bstep (se 2 (by rfl) ⟨1361076, by rfl⟩ : syracuseStep 3629537 = 2722153) B2722153
theorem B1614331 : Blo 1613005 1614331 := bstep (se 1 (by rfl) ⟨1210748, by rfl⟩ : syracuseStep 1614331 = 2421497) B2421497
theorem B18375173 : Blo 1613005 18375173 := bstep (se 4 (by rfl) ⟨1722672, by rfl⟩ : syracuseStep 18375173 = 3445345) B3445345
theorem B17449505 : Blo 1613005 17449505 := bstep (se 2 (by rfl) ⟨6543564, by rfl⟩ : syracuseStep 17449505 = 13087129) B13087129
theorem B1614399 : Blo 1613005 1614399 := bstep (se 1 (by rfl) ⟨1210799, by rfl⟩ : syracuseStep 1614399 = 2421599) B2421599
theorem B1614407 : Blo 1613005 1614407 := bstep (se 1 (by rfl) ⟨1210805, by rfl⟩ : syracuseStep 1614407 = 2421611) B2421611
theorem B12255947 : Blo 1613005 12255947 := bstep (se 1 (by rfl) ⟨9191960, by rfl⟩ : syracuseStep 12255947 = 18383921) B18383921
theorem B1614559 : Blo 1613005 1614559 := bstep (se 1 (by rfl) ⟨1210919, by rfl⟩ : syracuseStep 1614559 = 2421839) B2421839
theorem B3629843 : Blo 1613005 3629843 := bstep (se 1 (by rfl) ⟨2722382, by rfl⟩ : syracuseStep 3629843 = 5444765) B5444765
theorem B1614639 : Blo 1613005 1614639 := bstep (se 1 (by rfl) ⟨1210979, by rfl⟩ : syracuseStep 1614639 = 2421959) B2421959
theorem B3064655 : Blo 1613005 3064655 := bstep (se 1 (by rfl) ⟨2298491, by rfl⟩ : syracuseStep 3064655 = 4596983) B4596983
theorem B46523231 : Blo 1613005 46523231 := bstep (se 1 (by rfl) ⟨34892423, by rfl⟩ : syracuseStep 46523231 = 69784847) B69784847
theorem B1614747 : Blo 1613005 1614747 := bstep (se 1 (by rfl) ⟨1211060, by rfl⟩ : syracuseStep 1614747 = 2422121) B2422121
theorem B1614799 : Blo 1613005 1614799 := bstep (se 1 (by rfl) ⟨1211099, by rfl⟩ : syracuseStep 1614799 = 2422199) B2422199
theorem B3064807 : Blo 1613005 3064807 := bstep (se 1 (by rfl) ⟨2298605, by rfl⟩ : syracuseStep 3064807 = 4597211) B4597211
theorem B1614823 : Blo 1613005 1614823 := bstep (se 1 (by rfl) ⟨1211117, by rfl⟩ : syracuseStep 1614823 = 2422235) B2422235
theorem B23274533 : Blo 1613005 23274533 := bstep (se 4 (by rfl) ⟨2181987, by rfl⟩ : syracuseStep 23274533 = 4363975) B4363975
theorem B31016033 : Blo 1613005 31016033 := bstep (se 2 (by rfl) ⟨11631012, by rfl⟩ : syracuseStep 31016033 = 23262025) B23262025
theorem B3630203 : Blo 1613005 3630203 := bstep (se 1 (by rfl) ⟨2722652, by rfl⟩ : syracuseStep 3630203 = 5445305) B5445305
theorem B5170301 : Blo 1613005 5170301 := bstep (se 3 (by rfl) ⟨969431, by rfl⟩ : syracuseStep 5170301 = 1938863) B1938863
theorem B11633807 : Blo 1613005 11633807 := bstep (se 1 (by rfl) ⟨8725355, by rfl⟩ : syracuseStep 11633807 = 17450711) B17450711
theorem B35357897 : Blo 1613005 35357897 := bstep (se 2 (by rfl) ⟨13259211, by rfl⟩ : syracuseStep 35357897 = 26518423) B26518423
theorem B6128855 : Blo 1613005 6128855 := bstep (se 1 (by rfl) ⟨4596641, by rfl⟩ : syracuseStep 6128855 = 9193283) B9193283
theorem B5596393 : Blo 1613005 5596393 := bstep (se 2 (by rfl) ⟨2098647, by rfl⟩ : syracuseStep 5596393 = 4197295) B4197295
theorem B3876083 : Blo 1613005 3876083 := bstep (se 1 (by rfl) ⟨2907062, by rfl⟩ : syracuseStep 3876083 = 5814125) B5814125
theorem B3630329 : Blo 1613005 3630329 := bstep (se 2 (by rfl) ⟨1361373, by rfl⟩ : syracuseStep 3630329 = 2722747) B2722747
theorem B15516971 : Blo 1613005 15516971 := bstep (se 1 (by rfl) ⟨11637728, by rfl⟩ : syracuseStep 15516971 = 23275457) B23275457
theorem B11044183 : Blo 1613005 11044183 := bstep (se 1 (by rfl) ⟨8283137, by rfl⟩ : syracuseStep 11044183 = 16566275) B16566275
theorem B3630473 : Blo 1613005 3630473 := bstep (se 2 (by rfl) ⟨1361427, by rfl⟩ : syracuseStep 3630473 = 2722855) B2722855
theorem B3876283 : Blo 1613005 3876283 := bstep (se 1 (by rfl) ⟨2907212, by rfl⟩ : syracuseStep 3876283 = 5814425) B5814425
theorem B3630599 : Blo 1613005 3630599 := bstep (se 1 (by rfl) ⟨2722949, by rfl⟩ : syracuseStep 3630599 = 5445899) B5445899
theorem B121054763 : Blo 1613005 121054763 := bstep (se 1 (by rfl) ⟨90791072, by rfl⟩ : syracuseStep 121054763 = 181582145) B181582145
theorem B2041519 : Blo 1613005 2041519 := bstep (se 1 (by rfl) ⟨1531139, by rfl⟩ : syracuseStep 2041519 = 3062279) B3062279
theorem B3630779 : Blo 1613005 3630779 := bstep (se 1 (by rfl) ⟨2723084, by rfl⟩ : syracuseStep 3630779 = 5446169) B5446169
theorem B32745181 : Blo 1613005 32745181 := bstep (se 3 (by rfl) ⟨6139721, by rfl⟩ : syracuseStep 32745181 = 12279443) B12279443
theorem B3630905 : Blo 1613005 3630905 := bstep (se 2 (by rfl) ⟨1361589, by rfl⟩ : syracuseStep 3630905 = 2723179) B2723179
theorem B15517585 : Blo 1613005 15517585 := bstep (se 2 (by rfl) ⟨5819094, by rfl⟩ : syracuseStep 15517585 = 11638189) B11638189
theorem B5449679 : Blo 1613005 5449679 := bstep (se 1 (by rfl) ⟨4087259, by rfl⟩ : syracuseStep 5449679 = 8174519) B8174519
theorem B78571619 : Blo 1613005 78571619 := bstep (se 1 (by rfl) ⟨58928714, by rfl⟩ : syracuseStep 78571619 = 117857429) B117857429
theorem B9193601 : Blo 1613005 9193601 := bstep (se 2 (by rfl) ⟨3447600, by rfl⟩ : syracuseStep 9193601 = 6895201) B6895201
theorem B13781177 : Blo 1613005 13781177 := bstep (se 2 (by rfl) ⟨5167941, by rfl⟩ : syracuseStep 13781177 = 10335883) B10335883
theorem B8726723 : Blo 1613005 8726723 := bstep (se 1 (by rfl) ⟨6545042, by rfl⟩ : syracuseStep 8726723 = 13090085) B13090085
theorem B5040551 : Blo 1613005 5040551 := bstep (se 1 (by rfl) ⟨3780413, by rfl⟩ : syracuseStep 5040551 = 7560827) B7560827
theorem B3631535 : Blo 1613005 3631535 := bstep (se 1 (by rfl) ⟨2723651, by rfl⟩ : syracuseStep 3631535 = 5447303) B5447303
theorem B3631571 : Blo 1613005 3631571 := bstep (se 1 (by rfl) ⟨2723678, by rfl⟩ : syracuseStep 3631571 = 5447357) B5447357
theorem B3631679 : Blo 1613005 3631679 := bstep (se 1 (by rfl) ⟨2723759, by rfl⟩ : syracuseStep 3631679 = 5447519) B5447519
theorem B3631787 : Blo 1613005 3631787 := bstep (se 1 (by rfl) ⟨2723840, by rfl⟩ : syracuseStep 3631787 = 5447681) B5447681
theorem B8170307 : Blo 1613005 8170307 := bstep (se 1 (by rfl) ⟨6127730, by rfl⟩ : syracuseStep 8170307 = 12255461) B12255461
theorem B2419535 : Blo 1613005 2419535 := bstep (se 1 (by rfl) ⟨1814651, by rfl⟩ : syracuseStep 2419535 = 3629303) B3629303
theorem B2722639 : Blo 1613005 2722639 := bstep (se 1 (by rfl) ⟨2041979, by rfl⟩ : syracuseStep 2722639 = 4083959) B4083959
theorem B4909949 : Blo 1613005 4909949 := bstep (se 3 (by rfl) ⟨920615, by rfl⟩ : syracuseStep 4909949 = 1841231) B1841231
theorem B4139947 : Blo 1613005 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B4361207 : Blo 1613005 4361207 := bstep (se 1 (by rfl) ⟨3270905, by rfl⟩ : syracuseStep 4361207 = 6541811) B6541811
theorem B18394127 : Blo 1613005 18394127 := bstep (se 1 (by rfl) ⟨13795595, by rfl⟩ : syracuseStep 18394127 = 27591191) B27591191
theorem B2657423 : Blo 1613005 2657423 := bstep (se 1 (by rfl) ⟨1993067, by rfl⟩ : syracuseStep 2657423 = 3986135) B3986135
theorem B24857779 : Blo 1613005 24857779 := bstep (se 1 (by rfl) ⟨18643334, by rfl⟩ : syracuseStep 24857779 = 37286669) B37286669
theorem B3632327 : Blo 1613005 3632327 := bstep (se 1 (by rfl) ⟨2724245, by rfl⟩ : syracuseStep 3632327 = 5448491) B5448491
theorem B2419931 : Blo 1613005 2419931 := bstep (se 1 (by rfl) ⟨1814948, by rfl⟩ : syracuseStep 2419931 = 3629897) B3629897
theorem B6131011 : Blo 1613005 6131011 := bstep (se 1 (by rfl) ⟨4598258, by rfl⟩ : syracuseStep 6131011 = 9196517) B9196517
theorem B3632507 : Blo 1613005 3632507 := bstep (se 1 (by rfl) ⟨2724380, by rfl⟩ : syracuseStep 3632507 = 5448761) B5448761
theorem B2420105 : Blo 1613005 2420105 := bstep (se 2 (by rfl) ⟨907539, by rfl⟩ : syracuseStep 2420105 = 1815079) B1815079
theorem B2452985 : Blo 1613005 2452985 := bstep (se 2 (by rfl) ⟨919869, by rfl⟩ : syracuseStep 2452985 = 1839739) B1839739
theorem B2723321 : Blo 1613005 2723321 := bstep (se 2 (by rfl) ⟨1021245, by rfl⟩ : syracuseStep 2723321 = 2042491) B2042491
theorem B3632633 : Blo 1613005 3632633 := bstep (se 2 (by rfl) ⟨1362237, by rfl⟩ : syracuseStep 3632633 = 2724475) B2724475
theorem B2043463 : Blo 1613005 2043463 := bstep (se 1 (by rfl) ⟨1532597, by rfl⟩ : syracuseStep 2043463 = 3065195) B3065195
theorem B3632723 : Blo 1613005 3632723 := bstep (se 1 (by rfl) ⟨2724542, by rfl⟩ : syracuseStep 3632723 = 5449085) B5449085
theorem B8171117 : Blo 1613005 8171117 := bstep (se 3 (by rfl) ⟨1532084, by rfl⟩ : syracuseStep 8171117 = 3064169) B3064169
theorem B6131315 : Blo 1613005 6131315 := bstep (se 1 (by rfl) ⟨4598486, by rfl⟩ : syracuseStep 6131315 = 9196973) B9196973
theorem B5598881 : Blo 1613005 5598881 := bstep (se 2 (by rfl) ⟨2099580, by rfl⟩ : syracuseStep 5598881 = 4199161) B4199161
theorem B15519431 : Blo 1613005 15519431 := bstep (se 1 (by rfl) ⟨11639573, by rfl⟩ : syracuseStep 15519431 = 23279147) B23279147
theorem B2420459 : Blo 1613005 2420459 := bstep (se 1 (by rfl) ⟨1815344, by rfl⟩ : syracuseStep 2420459 = 3630689) B3630689
theorem B2723591 : Blo 1613005 2723591 := bstep (se 1 (by rfl) ⟨2042693, by rfl⟩ : syracuseStep 2723591 = 4085387) B4085387
theorem B3632903 : Blo 1613005 3632903 := bstep (se 1 (by rfl) ⟨2724677, by rfl⟩ : syracuseStep 3632903 = 5449355) B5449355
theorem B6131497 : Blo 1613005 6131497 := bstep (se 2 (by rfl) ⟨2299311, by rfl⟩ : syracuseStep 6131497 = 4598623) B4598623
theorem B2420687 : Blo 1613005 2420687 := bstep (se 1 (by rfl) ⟨1815515, by rfl⟩ : syracuseStep 2420687 = 3631031) B3631031
theorem B6131771 : Blo 1613005 6131771 := bstep (se 1 (by rfl) ⟨4598828, by rfl⟩ : syracuseStep 6131771 = 9197657) B9197657
theorem B4083817 : Blo 1613005 4083817 := bstep (se 2 (by rfl) ⟨1531431, by rfl⟩ : syracuseStep 4083817 = 3062863) B3062863
theorem B28348645 : Blo 1613005 28348645 := bstep (se 4 (by rfl) ⟨2657685, by rfl⟩ : syracuseStep 28348645 = 5315371) B5315371
theorem B15511823 : Blo 1613005 15511823 := bstep (se 1 (by rfl) ⟨11633867, by rfl⟩ : syracuseStep 15511823 = 23267735) B23267735
theorem B2421083 : Blo 1613005 2421083 := bstep (se 1 (by rfl) ⟨1815812, by rfl⟩ : syracuseStep 2421083 = 3631625) B3631625
theorem B3633515 : Blo 1613005 3633515 := bstep (se 1 (by rfl) ⟨2725136, by rfl⟩ : syracuseStep 3633515 = 5450273) B5450273
theorem B3445175 : Blo 1613005 3445175 := bstep (se 1 (by rfl) ⟨2583881, by rfl⟩ : syracuseStep 3445175 = 5167763) B5167763
theorem B2724347 : Blo 1613005 2724347 := bstep (se 1 (by rfl) ⟨2043260, by rfl⟩ : syracuseStep 2724347 = 4086521) B4086521
theorem B3633659 : Blo 1613005 3633659 := bstep (se 1 (by rfl) ⟨2725244, by rfl⟩ : syracuseStep 3633659 = 5450489) B5450489
theorem B2421311 : Blo 1613005 2421311 := bstep (se 1 (by rfl) ⟨1815983, by rfl⟩ : syracuseStep 2421311 = 3631967) B3631967
theorem B4084303 : Blo 1613005 4084303 := bstep (se 1 (by rfl) ⟨3063227, by rfl⟩ : syracuseStep 4084303 = 6126455) B6126455
theorem B5444279 : Blo 1613005 5444279 := bstep (se 1 (by rfl) ⟨4083209, by rfl⟩ : syracuseStep 5444279 = 8166419) B8166419
theorem B2421431 : Blo 1613005 2421431 := bstep (se 1 (by rfl) ⟨1816073, by rfl⟩ : syracuseStep 2421431 = 3632147) B3632147
theorem B2421659 : Blo 1613005 2421659 := bstep (se 1 (by rfl) ⟨1816244, by rfl⟩ : syracuseStep 2421659 = 3632489) B3632489
theorem B2724779 : Blo 1613005 2724779 := bstep (se 1 (by rfl) ⟨2043584, by rfl⟩ : syracuseStep 2724779 = 4087169) B4087169
theorem B15512633 : Blo 1613005 15512633 := bstep (se 2 (by rfl) ⟨5817237, by rfl⟩ : syracuseStep 15512633 = 11634475) B11634475
theorem B9188477 : Blo 1613005 9188477 := bstep (se 3 (by rfl) ⟨1722839, by rfl⟩ : syracuseStep 9188477 = 3445679) B3445679
theorem B6894791 : Blo 1613005 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B4084951 : Blo 1613005 4084951 := bstep (se 1 (by rfl) ⟨3063713, by rfl⟩ : syracuseStep 4084951 = 6127427) B6127427
theorem B2422055 : Blo 1613005 2422055 := bstep (se 1 (by rfl) ⟨1816541, by rfl⟩ : syracuseStep 2422055 = 3633083) B3633083
theorem B2422139 : Blo 1613005 2422139 := bstep (se 1 (by rfl) ⟨1816604, by rfl⟩ : syracuseStep 2422139 = 3633209) B3633209
theorem B119387525 : Blo 1613005 119387525 := bstep (se 4 (by rfl) ⟨11192580, by rfl⟩ : syracuseStep 119387525 = 22385161) B22385161
theorem B2725319 : Blo 1613005 2725319 := bstep (se 1 (by rfl) ⟨2043989, by rfl⟩ : syracuseStep 2725319 = 4087979) B4087979
theorem B2422265 : Blo 1613005 2422265 := bstep (se 2 (by rfl) ⟨908349, by rfl⟩ : syracuseStep 2422265 = 1816699) B1816699
theorem B4085255 : Blo 1613005 4085255 := bstep (se 1 (by rfl) ⟨3063941, by rfl⟩ : syracuseStep 4085255 = 6127883) B6127883
theorem B11630117 : Blo 1613005 11630117 := bstep (se 4 (by rfl) ⟨1090323, by rfl⟩ : syracuseStep 11630117 = 2180647) B2180647
theorem B1816159 : Blo 1613005 1816159 := bstep (se 1 (by rfl) ⟨1362119, by rfl⟩ : syracuseStep 1816159 = 2724239) B2724239
theorem B2422367 : Blo 1613005 2422367 := bstep (se 1 (by rfl) ⟨1816775, by rfl⟩ : syracuseStep 2422367 = 3633551) B3633551
theorem B3446507 : Blo 1613005 3446507 := bstep (se 1 (by rfl) ⟨2584880, by rfl⟩ : syracuseStep 3446507 = 5169761) B5169761
theorem B6895543 : Blo 1613005 6895543 := bstep (se 1 (by rfl) ⟨5171657, by rfl⟩ : syracuseStep 6895543 = 10343315) B10343315
theorem B4085711 : Blo 1613005 4085711 := bstep (se 1 (by rfl) ⟨3064283, by rfl⟩ : syracuseStep 4085711 = 6128567) B6128567
theorem B9189409 : Blo 1613005 9189409 := bstep (se 2 (by rfl) ⟨3446028, by rfl⟩ : syracuseStep 9189409 = 6892057) B6892057
theorem B12253517 : Blo 1613005 12253517 := bstep (se 3 (by rfl) ⟨2297534, by rfl⟩ : syracuseStep 12253517 = 4595069) B4595069
theorem B3930535 : Blo 1613005 3930535 := bstep (se 1 (by rfl) ⟨2947901, by rfl⟩ : syracuseStep 3930535 = 5895803) B5895803
theorem B4086227 : Blo 1613005 4086227 := bstep (se 1 (by rfl) ⟨3064670, by rfl⟩ : syracuseStep 4086227 = 6129341) B6129341
theorem B10344955 : Blo 1613005 10344955 := bstep (se 1 (by rfl) ⟨7758716, by rfl⟩ : syracuseStep 10344955 = 15517433) B15517433
theorem B4594249 : Blo 1613005 4594249 := bstep (se 2 (by rfl) ⟨1722843, by rfl⟩ : syracuseStep 4594249 = 3445687) B3445687
theorem B5446223 : Blo 1613005 5446223 := bstep (se 1 (by rfl) ⟨4084667, by rfl⟩ : syracuseStep 5446223 = 8169335) B8169335
theorem B4086683 : Blo 1613005 4086683 := bstep (se 1 (by rfl) ⟨3065012, by rfl⟩ : syracuseStep 4086683 = 6130025) B6130025
theorem B4365211 : Blo 1613005 4365211 := bstep (se 1 (by rfl) ⟨3273908, by rfl⟩ : syracuseStep 4365211 = 6547817) B6547817
theorem B4594603 : Blo 1613005 4594603 := bstep (se 1 (by rfl) ⟨3445952, by rfl⟩ : syracuseStep 4594603 = 6891905) B6891905
theorem B4594877 : Blo 1613005 4594877 := bstep (se 3 (by rfl) ⟨861539, by rfl⟩ : syracuseStep 4594877 = 1723079) B1723079
theorem B13786301 : Blo 1613005 13786301 := bstep (se 3 (by rfl) ⟨2584931, by rfl⟩ : syracuseStep 13786301 = 5169863) B5169863
theorem B2211035 : Blo 1613005 2211035 := bstep (se 1 (by rfl) ⟨1658276, by rfl⟩ : syracuseStep 2211035 = 3316553) B3316553
theorem B1613087 : Blo 1613005 1613087 := bstep (se 1 (by rfl) ⟨1209815, by rfl⟩ : syracuseStep 1613087 = 2419631) B2419631
theorem B1613147 : Blo 1613005 1613147 := bstep (se 1 (by rfl) ⟨1209860, by rfl⟩ : syracuseStep 1613147 = 2419721) B2419721
theorem B1613167 : Blo 1613005 1613167 := bstep (se 1 (by rfl) ⟨1209875, by rfl⟩ : syracuseStep 1613167 = 2419751) B2419751
theorem B1613223 : Blo 1613005 1613223 := bstep (se 1 (by rfl) ⟨1209917, by rfl⟩ : syracuseStep 1613223 = 2419835) B2419835
theorem B5815739 : Blo 1613005 5815739 := bstep (se 1 (by rfl) ⟨4361804, by rfl⟩ : syracuseStep 5815739 = 8723609) B8723609
theorem B7757255 : Blo 1613005 7757255 := bstep (se 1 (by rfl) ⟨5817941, by rfl⟩ : syracuseStep 7757255 = 11635883) B11635883
theorem B8166905 : Blo 1613005 8166905 := bstep (se 2 (by rfl) ⟨3062589, by rfl⟩ : syracuseStep 8166905 = 6125179) B6125179
theorem B1613307 : Blo 1613005 1613307 := bstep (se 1 (by rfl) ⟨1209980, by rfl⟩ : syracuseStep 1613307 = 2419961) B2419961
theorem B14728715 : Blo 1613005 14728715 := bstep (se 1 (by rfl) ⟨11046536, by rfl⟩ : syracuseStep 14728715 = 22093073) B22093073
theorem B1613375 : Blo 1613005 1613375 := bstep (se 1 (by rfl) ⟨1210031, by rfl⟩ : syracuseStep 1613375 = 2420063) B2420063
theorem B1613383 : Blo 1613005 1613383 := bstep (se 1 (by rfl) ⟨1210037, by rfl⟩ : syracuseStep 1613383 = 2420075) B2420075
theorem B3448507 : Blo 1613005 3448507 := bstep (se 1 (by rfl) ⟨2586380, by rfl⟩ : syracuseStep 3448507 = 5172761) B5172761
theorem B19644119 : Blo 1613005 19644119 := bstep (se 1 (by rfl) ⟨14733089, by rfl⟩ : syracuseStep 19644119 = 29466179) B29466179
theorem B1613535 : Blo 1613005 1613535 := bstep (se 1 (by rfl) ⟨1210151, by rfl⟩ : syracuseStep 1613535 = 2420303) B2420303
theorem B17440505 : Blo 1613005 17440505 := bstep (se 2 (by rfl) ⟨6540189, by rfl⟩ : syracuseStep 17440505 = 13080379) B13080379
theorem B5447465 : Blo 1613005 5447465 := bstep (se 2 (by rfl) ⟨2042799, by rfl⟩ : syracuseStep 5447465 = 4085599) B4085599
theorem B1613615 : Blo 1613005 1613615 := bstep (se 1 (by rfl) ⟨1210211, by rfl⟩ : syracuseStep 1613615 = 2420423) B2420423
theorem B8167229 : Blo 1613005 8167229 := bstep (se 3 (by rfl) ⟨1531355, by rfl⟩ : syracuseStep 8167229 = 3062711) B3062711
theorem B34881353 : Blo 1613005 34881353 := bstep (se 2 (by rfl) ⟨13080507, by rfl⟩ : syracuseStep 34881353 = 26161015) B26161015
theorem B1613723 : Blo 1613005 1613723 := bstep (se 1 (by rfl) ⟨1210292, by rfl⟩ : syracuseStep 1613723 = 2420585) B2420585
theorem B1613775 : Blo 1613005 1613775 := bstep (se 1 (by rfl) ⟨1210331, by rfl⟩ : syracuseStep 1613775 = 2420663) B2420663
theorem B1613799 : Blo 1613005 1613799 := bstep (se 1 (by rfl) ⟨1210349, by rfl⟩ : syracuseStep 1613799 = 2420699) B2420699
theorem B4087847 : Blo 1613005 4087847 := bstep (se 1 (by rfl) ⟨3065885, by rfl⟩ : syracuseStep 4087847 = 6131771) B6131771
theorem B1614055 : Blo 1613005 1614055 := bstep (se 1 (by rfl) ⟨1210541, by rfl⟩ : syracuseStep 1614055 = 2421083) B2421083
theorem B11633003 : Blo 1613005 11633003 := bstep (se 1 (by rfl) ⟨8724752, by rfl⟩ : syracuseStep 11633003 = 17449505) B17449505
theorem B31023485 : Blo 1613005 31023485 := bstep (se 3 (by rfl) ⟨5816903, by rfl⟩ : syracuseStep 31023485 = 11633807) B11633807
theorem B7086461 : Blo 1613005 7086461 := bstep (se 3 (by rfl) ⟨1328711, by rfl⟩ : syracuseStep 7086461 = 2657423) B2657423
theorem B1614207 : Blo 1613005 1614207 := bstep (se 1 (by rfl) ⟨1210655, by rfl⟩ : syracuseStep 1614207 = 2421311) B2421311
theorem B3629519 : Blo 1613005 3629519 := bstep (se 1 (by rfl) ⟨2722139, by rfl⟩ : syracuseStep 3629519 = 5444279) B5444279
theorem B1614287 : Blo 1613005 1614287 := bstep (se 1 (by rfl) ⟨1210715, by rfl⟩ : syracuseStep 1614287 = 2421431) B2421431
theorem B31015487 : Blo 1613005 31015487 := bstep (se 1 (by rfl) ⟨23261615, by rfl⟩ : syracuseStep 31015487 = 46523231) B46523231
theorem B1614439 : Blo 1613005 1614439 := bstep (se 1 (by rfl) ⟨1210829, by rfl⟩ : syracuseStep 1614439 = 2421659) B2421659
theorem B15516355 : Blo 1613005 15516355 := bstep (se 1 (by rfl) ⟨11637266, by rfl⟩ : syracuseStep 15516355 = 23274533) B23274533
theorem B20677355 : Blo 1613005 20677355 := bstep (se 1 (by rfl) ⟨15508016, by rfl⟩ : syracuseStep 20677355 = 31016033) B31016033
theorem B4596527 : Blo 1613005 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B1614703 : Blo 1613005 1614703 := bstep (se 1 (by rfl) ⟨1211027, by rfl⟩ : syracuseStep 1614703 = 2422055) B2422055
theorem B1614759 : Blo 1613005 1614759 := bstep (se 1 (by rfl) ⟨1211069, by rfl⟩ : syracuseStep 1614759 = 2422139) B2422139
theorem B1614843 : Blo 1613005 1614843 := bstep (se 1 (by rfl) ⟨1211132, by rfl⟩ : syracuseStep 1614843 = 2422265) B2422265
theorem B1614911 : Blo 1613005 1614911 := bstep (se 1 (by rfl) ⟨1211183, by rfl⟩ : syracuseStep 1614911 = 2422367) B2422367
theorem B3630185 : Blo 1613005 3630185 := bstep (se 2 (by rfl) ⟨1361319, by rfl⟩ : syracuseStep 3630185 = 2722639) B2722639
theorem B20686013 : Blo 1613005 20686013 := bstep (se 3 (by rfl) ⟨3878627, by rfl⟩ : syracuseStep 20686013 = 7757255) B7757255
theorem B52381079 : Blo 1613005 52381079 := bstep (se 1 (by rfl) ⟨39285809, by rfl⟩ : syracuseStep 52381079 = 78571619) B78571619
theorem B6129067 : Blo 1613005 6129067 := bstep (se 1 (by rfl) ⟨4596800, by rfl⟩ : syracuseStep 6129067 = 9193601) B9193601
theorem B5817815 : Blo 1613005 5817815 := bstep (se 1 (by rfl) ⟨4363361, by rfl⟩ : syracuseStep 5817815 = 8726723) B8726723
theorem B8169011 : Blo 1613005 8169011 := bstep (se 1 (by rfl) ⟨6126758, by rfl⟩ : syracuseStep 8169011 = 12253517) B12253517
theorem B3630815 : Blo 1613005 3630815 := bstep (se 1 (by rfl) ⟨2723111, by rfl⟩ : syracuseStep 3630815 = 5446223) B5446223
theorem B2722025 : Blo 1613005 2722025 := bstep (se 2 (by rfl) ⟨1020759, by rfl⟩ : syracuseStep 2722025 = 2041519) B2041519
theorem B4598009 : Blo 1613005 4598009 := bstep (se 2 (by rfl) ⟨1724253, by rfl⟩ : syracuseStep 4598009 = 3448507) B3448507
theorem B3877159 : Blo 1613005 3877159 := bstep (se 1 (by rfl) ⟨2907869, by rfl⟩ : syracuseStep 3877159 = 5815739) B5815739
theorem B11627003 : Blo 1613005 11627003 := bstep (se 1 (by rfl) ⟨8720252, by rfl⟩ : syracuseStep 11627003 = 17440505) B17440505
theorem B3631643 : Blo 1613005 3631643 := bstep (se 1 (by rfl) ⟨2723732, by rfl⟩ : syracuseStep 3631643 = 5447465) B5447465
theorem B9194057 : Blo 1613005 9194057 := bstep (se 2 (by rfl) ⟨3447771, by rfl⟩ : syracuseStep 9194057 = 6895543) B6895543
theorem B7563959 : Blo 1613005 7563959 := bstep (se 1 (by rfl) ⟨5672969, by rfl⟩ : syracuseStep 7563959 = 11345939) B11345939
theorem B2419511 : Blo 1613005 2419511 := bstep (se 1 (by rfl) ⟨1814633, by rfl⟩ : syracuseStep 2419511 = 3629267) B3629267
theorem B2419547 : Blo 1613005 2419547 := bstep (se 1 (by rfl) ⟨1814660, by rfl⟩ : syracuseStep 2419547 = 3629321) B3629321
theorem B10341215 : Blo 1613005 10341215 := bstep (se 1 (by rfl) ⟨7755911, by rfl⟩ : syracuseStep 10341215 = 15511823) B15511823
theorem B2296783 : Blo 1613005 2296783 := bstep (se 1 (by rfl) ⟨1722587, by rfl⟩ : syracuseStep 2296783 = 3445175) B3445175
theorem B2419691 : Blo 1613005 2419691 := bstep (se 1 (by rfl) ⟨1814768, by rfl⟩ : syracuseStep 2419691 = 3629537) B3629537
theorem B12250115 : Blo 1613005 12250115 := bstep (se 1 (by rfl) ⟨9187586, by rfl⟩ : syracuseStep 12250115 = 18375173) B18375173
theorem B8170631 : Blo 1613005 8170631 := bstep (se 1 (by rfl) ⟨6127973, by rfl⟩ : syracuseStep 8170631 = 12255947) B12255947
theorem B2419895 : Blo 1613005 2419895 := bstep (se 1 (by rfl) ⟨1814921, by rfl⟩ : syracuseStep 2419895 = 3629843) B3629843
theorem B10341755 : Blo 1613005 10341755 := bstep (se 1 (by rfl) ⟨7756316, by rfl⟩ : syracuseStep 10341755 = 15512633) B15512633
theorem B2420135 : Blo 1613005 2420135 := bstep (se 1 (by rfl) ⟨1815101, by rfl⟩ : syracuseStep 2420135 = 3630203) B3630203
theorem B23571931 : Blo 1613005 23571931 := bstep (se 1 (by rfl) ⟨17678948, by rfl⟩ : syracuseStep 23571931 = 35357897) B35357897
theorem B2584055 : Blo 1613005 2584055 := bstep (se 1 (by rfl) ⟨1938041, by rfl⟩ : syracuseStep 2584055 = 3876083) B3876083
theorem B2420219 : Blo 1613005 2420219 := bstep (se 1 (by rfl) ⟨1815164, by rfl⟩ : syracuseStep 2420219 = 3630329) B3630329
theorem B2420315 : Blo 1613005 2420315 := bstep (se 1 (by rfl) ⟨1815236, by rfl⟩ : syracuseStep 2420315 = 3630473) B3630473
theorem B2420399 : Blo 1613005 2420399 := bstep (se 1 (by rfl) ⟨1815299, by rfl⟩ : syracuseStep 2420399 = 3630599) B3630599
theorem B2723503 : Blo 1613005 2723503 := bstep (se 1 (by rfl) ⟨2042627, by rfl⟩ : syracuseStep 2723503 = 4085255) B4085255
theorem B7753411 : Blo 1613005 7753411 := bstep (se 1 (by rfl) ⟨5815058, by rfl⟩ : syracuseStep 7753411 = 11630117) B11630117
theorem B80703175 : Blo 1613005 80703175 := bstep (se 1 (by rfl) ⟨60527381, by rfl⟩ : syracuseStep 80703175 = 121054763) B121054763
theorem B2420519 : Blo 1613005 2420519 := bstep (se 1 (by rfl) ⟨1815389, by rfl⟩ : syracuseStep 2420519 = 3630779) B3630779
theorem B5820281 : Blo 1613005 5820281 := bstep (se 2 (by rfl) ⟨2182605, by rfl⟩ : syracuseStep 5820281 = 4365211) B4365211
theorem B2420603 : Blo 1613005 2420603 := bstep (se 1 (by rfl) ⟨1815452, by rfl⟩ : syracuseStep 2420603 = 3630905) B3630905
theorem B2723807 : Blo 1613005 2723807 := bstep (se 1 (by rfl) ⟨2042855, by rfl⟩ : syracuseStep 2723807 = 4085711) B4085711
theorem B3633119 : Blo 1613005 3633119 := bstep (se 1 (by rfl) ⟨2724839, by rfl⟩ : syracuseStep 3633119 = 5449679) B5449679
theorem B1273466933 : Blo 1613005 1273466933 := bstep (se 5 (by rfl) ⟨59693762, by rfl⟩ : syracuseStep 1273466933 = 119387525) B119387525
theorem B9187451 : Blo 1613005 9187451 := bstep (se 1 (by rfl) ⟨6890588, by rfl⟩ : syracuseStep 9187451 = 13781177) B13781177
theorem B2421023 : Blo 1613005 2421023 := bstep (se 1 (by rfl) ⟨1815767, by rfl⟩ : syracuseStep 2421023 = 3631535) B3631535
theorem B2421047 : Blo 1613005 2421047 := bstep (se 1 (by rfl) ⟨1815785, by rfl⟩ : syracuseStep 2421047 = 3631571) B3631571
theorem B2724151 : Blo 1613005 2724151 := bstep (se 1 (by rfl) ⟨2043113, by rfl⟩ : syracuseStep 2724151 = 4086227) B4086227
theorem B2421119 : Blo 1613005 2421119 := bstep (se 1 (by rfl) ⟨1815839, by rfl⟩ : syracuseStep 2421119 = 3631679) B3631679
theorem B2421191 : Blo 1613005 2421191 := bstep (se 1 (by rfl) ⟨1815893, by rfl⟩ : syracuseStep 2421191 = 3631787) B3631787
theorem B14725577 : Blo 1613005 14725577 := bstep (se 2 (by rfl) ⟨5522091, by rfl⟩ : syracuseStep 14725577 = 11044183) B11044183
theorem B3273299 : Blo 1613005 3273299 := bstep (se 1 (by rfl) ⟨2454974, by rfl⟩ : syracuseStep 3273299 = 4909949) B4909949
theorem B2724455 : Blo 1613005 2724455 := bstep (se 1 (by rfl) ⟨2043341, by rfl⟩ : syracuseStep 2724455 = 4086683) B4086683
theorem B2724617 : Blo 1613005 2724617 := bstep (se 2 (by rfl) ⟨1021731, by rfl⟩ : syracuseStep 2724617 = 2043463) B2043463
theorem B604771093 : Blo 1613005 604771093 := bstep (se 6 (by rfl) ⟨14174322, by rfl⟩ : syracuseStep 604771093 = 28348645) B28348645
theorem B2421545 : Blo 1613005 2421545 := bstep (se 2 (by rfl) ⟨908079, by rfl⟩ : syracuseStep 2421545 = 1816159) B1816159
theorem B2421551 : Blo 1613005 2421551 := bstep (se 1 (by rfl) ⟨1816163, by rfl⟩ : syracuseStep 2421551 = 3632327) B3632327
theorem B8172413 : Blo 1613005 8172413 := bstep (se 3 (by rfl) ⟨1532327, by rfl⟩ : syracuseStep 8172413 = 3064655) B3064655
theorem B2421671 : Blo 1613005 2421671 := bstep (se 1 (by rfl) ⟨1816253, by rfl⟩ : syracuseStep 2421671 = 3632507) B3632507
theorem B43660241 : Blo 1613005 43660241 := bstep (se 2 (by rfl) ⟨16372590, by rfl⟩ : syracuseStep 43660241 = 32745181) B32745181
theorem B5444603 : Blo 1613005 5444603 := bstep (se 1 (by rfl) ⟨4083452, by rfl⟩ : syracuseStep 5444603 = 8166905) B8166905
theorem B1635323 : Blo 1613005 1635323 := bstep (se 1 (by rfl) ⟨1226492, by rfl⟩ : syracuseStep 1635323 = 2452985) B2452985
theorem B1815547 : Blo 1613005 1815547 := bstep (se 1 (by rfl) ⟨1361660, by rfl⟩ : syracuseStep 1815547 = 2723321) B2723321
theorem B2421755 : Blo 1613005 2421755 := bstep (se 1 (by rfl) ⟨1816316, by rfl⟩ : syracuseStep 2421755 = 3632633) B3632633
theorem B9819143 : Blo 1613005 9819143 := bstep (se 1 (by rfl) ⟨7364357, by rfl⟩ : syracuseStep 9819143 = 14728715) B14728715
theorem B2421815 : Blo 1613005 2421815 := bstep (se 1 (by rfl) ⟨1816361, by rfl⟩ : syracuseStep 2421815 = 3632723) B3632723
theorem B3732587 : Blo 1613005 3732587 := bstep (se 1 (by rfl) ⟨2799440, by rfl⟩ : syracuseStep 3732587 = 5598881) B5598881
theorem B13096079 : Blo 1613005 13096079 := bstep (se 1 (by rfl) ⟨9822059, by rfl⟩ : syracuseStep 13096079 = 19644119) B19644119
theorem B1815727 : Blo 1613005 1815727 := bstep (se 1 (by rfl) ⟨1361795, by rfl⟩ : syracuseStep 1815727 = 2723591) B2723591
theorem B2421935 : Blo 1613005 2421935 := bstep (se 1 (by rfl) ⟨1816451, by rfl⟩ : syracuseStep 2421935 = 3632903) B3632903
theorem B20690113 : Blo 1613005 20690113 := bstep (se 2 (by rfl) ⟨7758792, by rfl⟩ : syracuseStep 20690113 = 15517585) B15517585
theorem B5444819 : Blo 1613005 5444819 := bstep (se 1 (by rfl) ⟨4083614, by rfl⟩ : syracuseStep 5444819 = 8167229) B8167229
theorem B23254235 : Blo 1613005 23254235 := bstep (se 1 (by rfl) ⟨17440676, by rfl⟩ : syracuseStep 23254235 = 34881353) B34881353
theorem B46519541 : Blo 1613005 46519541 := bstep (se 5 (by rfl) ⟨2180603, by rfl⟩ : syracuseStep 46519541 = 4361207) B4361207
theorem B2725211 : Blo 1613005 2725211 := bstep (se 1 (by rfl) ⟨2043908, by rfl⟩ : syracuseStep 2725211 = 4087817) B4087817
theorem B12252545 : Blo 1613005 12252545 := bstep (se 2 (by rfl) ⟨4594704, by rfl⟩ : syracuseStep 12252545 = 9189409) B9189409
theorem B5445089 : Blo 1613005 5445089 := bstep (se 2 (by rfl) ⟨2041908, by rfl⟩ : syracuseStep 5445089 = 4083817) B4083817
theorem B2422343 : Blo 1613005 2422343 := bstep (se 1 (by rfl) ⟨1816757, by rfl⟩ : syracuseStep 2422343 = 3633515) B3633515
theorem B1816231 : Blo 1613005 1816231 := bstep (se 1 (by rfl) ⟨1362173, by rfl⟩ : syracuseStep 1816231 = 2724347) B2724347
theorem B2422439 : Blo 1613005 2422439 := bstep (se 1 (by rfl) ⟨1816829, by rfl⟩ : syracuseStep 2422439 = 3633659) B3633659
theorem B5240713 : Blo 1613005 5240713 := bstep (se 2 (by rfl) ⟨1965267, by rfl⟩ : syracuseStep 5240713 = 3930535) B3930535
theorem B5896093 : Blo 1613005 5896093 := bstep (se 3 (by rfl) ⟨1105517, by rfl⟩ : syracuseStep 5896093 = 2211035) B2211035
theorem B1816519 : Blo 1613005 1816519 := bstep (se 1 (by rfl) ⟨1362389, by rfl⟩ : syracuseStep 1816519 = 2724779) B2724779
theorem B13793273 : Blo 1613005 13793273 := bstep (se 2 (by rfl) ⟨5172477, by rfl⟩ : syracuseStep 13793273 = 10344955) B10344955
theorem B6125651 : Blo 1613005 6125651 := bstep (se 1 (by rfl) ⟨4594238, by rfl⟩ : syracuseStep 6125651 = 9188477) B9188477
theorem B3446867 : Blo 1613005 3446867 := bstep (se 1 (by rfl) ⟨2585150, by rfl⟩ : syracuseStep 3446867 = 5170301) B5170301
theorem B6125665 : Blo 1613005 6125665 := bstep (se 2 (by rfl) ⟨2297124, by rfl⟩ : syracuseStep 6125665 = 4594249) B4594249
theorem B5445737 : Blo 1613005 5445737 := bstep (se 2 (by rfl) ⟨2042151, by rfl⟩ : syracuseStep 5445737 = 4084303) B4084303
theorem B4085903 : Blo 1613005 4085903 := bstep (se 1 (by rfl) ⟨3064427, by rfl⟩ : syracuseStep 4085903 = 6128855) B6128855
theorem B10344647 : Blo 1613005 10344647 := bstep (se 1 (by rfl) ⟨7758485, by rfl⟩ : syracuseStep 10344647 = 15516971) B15516971
theorem B1816879 : Blo 1613005 1816879 := bstep (se 1 (by rfl) ⟨1362659, by rfl⟩ : syracuseStep 1816879 = 2725319) B2725319
theorem B13441469 : Blo 1613005 13441469 := bstep (se 3 (by rfl) ⟨2520275, by rfl⟩ : syracuseStep 13441469 = 5040551) B5040551
theorem B6126137 : Blo 1613005 6126137 := bstep (se 2 (by rfl) ⟨2297301, by rfl⟩ : syracuseStep 6126137 = 4594603) B4594603
theorem B5519929 : Blo 1613005 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B4086409 : Blo 1613005 4086409 := bstep (se 2 (by rfl) ⟨1532403, by rfl⟩ : syracuseStep 4086409 = 3064807) B3064807
theorem B33143705 : Blo 1613005 33143705 := bstep (se 2 (by rfl) ⟨12428889, by rfl⟩ : syracuseStep 33143705 = 24857779) B24857779
theorem B5446601 : Blo 1613005 5446601 := bstep (se 2 (by rfl) ⟨2042475, by rfl⟩ : syracuseStep 5446601 = 4084951) B4084951
theorem B7461857 : Blo 1613005 7461857 := bstep (se 2 (by rfl) ⟨2798196, by rfl⟩ : syracuseStep 7461857 = 5596393) B5596393
theorem B8174681 : Blo 1613005 8174681 := bstep (se 2 (by rfl) ⟨3065505, by rfl⟩ : syracuseStep 8174681 = 6131011) B6131011
theorem B5446871 : Blo 1613005 5446871 := bstep (se 1 (by rfl) ⟨4085153, by rfl⟩ : syracuseStep 5446871 = 8170307) B8170307
theorem B1613023 : Blo 1613005 1613023 := bstep (se 1 (by rfl) ⟨1209767, by rfl⟩ : syracuseStep 1613023 = 2419535) B2419535
theorem B5168377 : Blo 1613005 5168377 := bstep (se 2 (by rfl) ⟨1938141, by rfl⟩ : syracuseStep 5168377 = 3876283) B3876283
theorem B9190685 : Blo 1613005 9190685 := bstep (se 3 (by rfl) ⟨1723253, by rfl⟩ : syracuseStep 9190685 = 3446507) B3446507
theorem B12262751 : Blo 1613005 12262751 := bstep (se 1 (by rfl) ⟨9197063, by rfl⟩ : syracuseStep 12262751 = 18394127) B18394127
theorem B3063251 : Blo 1613005 3063251 := bstep (se 1 (by rfl) ⟨2297438, by rfl⟩ : syracuseStep 3063251 = 4594877) B4594877
theorem B9190867 : Blo 1613005 9190867 := bstep (se 1 (by rfl) ⟨6893150, by rfl⟩ : syracuseStep 9190867 = 13786301) B13786301
theorem B1613287 : Blo 1613005 1613287 := bstep (se 1 (by rfl) ⟨1209965, by rfl⟩ : syracuseStep 1613287 = 2419931) B2419931
theorem B1613403 : Blo 1613005 1613403 := bstep (se 1 (by rfl) ⟨1210052, by rfl⟩ : syracuseStep 1613403 = 2420105) B2420105
theorem B8175329 : Blo 1613005 8175329 := bstep (se 2 (by rfl) ⟨3065748, by rfl⟩ : syracuseStep 8175329 = 6131497) B6131497
theorem B5447411 : Blo 1613005 5447411 := bstep (se 1 (by rfl) ⟨4085558, by rfl⟩ : syracuseStep 5447411 = 8171117) B8171117
theorem B4087543 : Blo 1613005 4087543 := bstep (se 1 (by rfl) ⟨3065657, by rfl⟩ : syracuseStep 4087543 = 6131315) B6131315
theorem B10346287 : Blo 1613005 10346287 := bstep (se 1 (by rfl) ⟨7759715, by rfl⟩ : syracuseStep 10346287 = 15519431) B15519431
theorem B1613639 : Blo 1613005 1613639 := bstep (se 1 (by rfl) ⟨1210229, by rfl⟩ : syracuseStep 1613639 = 2420459) B2420459
theorem B1613791 : Blo 1613005 1613791 := bstep (se 1 (by rfl) ⟨1210343, by rfl⟩ : syracuseStep 1613791 = 2420687) B2420687
theorem B848977955 : Blo 1613005 848977955 := bstep (se 1 (by rfl) ⟨636733466, by rfl⟩ : syracuseStep 848977955 = 1273466933) B1273466933
theorem B8167553 : Blo 1613005 8167553 := bstep (se 2 (by rfl) ⟨3062832, by rfl⟩ : syracuseStep 8167553 = 6125665) B6125665
theorem B1614015 : Blo 1613005 1614015 := bstep (se 1 (by rfl) ⟨1210511, by rfl⟩ : syracuseStep 1614015 = 2421023) B2421023
theorem B1614031 : Blo 1613005 1614031 := bstep (se 1 (by rfl) ⟨1210523, by rfl⟩ : syracuseStep 1614031 = 2421047) B2421047
theorem B1614079 : Blo 1613005 1614079 := bstep (se 1 (by rfl) ⟨1210559, by rfl⟩ : syracuseStep 1614079 = 2421119) B2421119
theorem B1614127 : Blo 1613005 1614127 := bstep (se 1 (by rfl) ⟨1210595, by rfl⟩ : syracuseStep 1614127 = 2421191) B2421191
theorem B20676991 : Blo 1613005 20676991 := bstep (se 1 (by rfl) ⟨15507743, by rfl⟩ : syracuseStep 20676991 = 31015487) B31015487
theorem B5169545 : Blo 1613005 5169545 := bstep (se 2 (by rfl) ⟨1938579, by rfl⟩ : syracuseStep 5169545 = 3877159) B3877159
theorem B1614363 : Blo 1613005 1614363 := bstep (se 1 (by rfl) ⟨1210772, by rfl⟩ : syracuseStep 1614363 = 2421545) B2421545
theorem B1614367 : Blo 1613005 1614367 := bstep (se 1 (by rfl) ⟨1210775, by rfl⟩ : syracuseStep 1614367 = 2421551) B2421551
theorem B5448275 : Blo 1613005 5448275 := bstep (se 1 (by rfl) ⟨4086206, by rfl⟩ : syracuseStep 5448275 = 8172413) B8172413
theorem B1614447 : Blo 1613005 1614447 := bstep (se 1 (by rfl) ⟨1210835, by rfl⟩ : syracuseStep 1614447 = 2421671) B2421671
theorem B29106827 : Blo 1613005 29106827 := bstep (se 1 (by rfl) ⟨21830120, by rfl⟩ : syracuseStep 29106827 = 43660241) B43660241
theorem B3629735 : Blo 1613005 3629735 := bstep (se 1 (by rfl) ⟨2722301, by rfl⟩ : syracuseStep 3629735 = 5444603) B5444603
theorem B1614503 : Blo 1613005 1614503 := bstep (se 1 (by rfl) ⟨1210877, by rfl⟩ : syracuseStep 1614503 = 2421755) B2421755
theorem B6546095 : Blo 1613005 6546095 := bstep (se 1 (by rfl) ⟨4909571, by rfl⟩ : syracuseStep 6546095 = 9819143) B9819143
theorem B1614543 : Blo 1613005 1614543 := bstep (se 1 (by rfl) ⟨1210907, by rfl⟩ : syracuseStep 1614543 = 2421815) B2421815
theorem B1614623 : Blo 1613005 1614623 := bstep (se 1 (by rfl) ⟨1210967, by rfl⟩ : syracuseStep 1614623 = 2421935) B2421935
theorem B3629879 : Blo 1613005 3629879 := bstep (se 1 (by rfl) ⟨2722409, by rfl⟩ : syracuseStep 3629879 = 5444819) B5444819
theorem B5448545 : Blo 1613005 5448545 := bstep (se 2 (by rfl) ⟨2043204, by rfl⟩ : syracuseStep 5448545 = 4086409) B4086409
theorem B8168363 : Blo 1613005 8168363 := bstep (se 1 (by rfl) ⟨6126272, by rfl⟩ : syracuseStep 8168363 = 12252545) B12252545
theorem B3630059 : Blo 1613005 3630059 := bstep (se 1 (by rfl) ⟨2722544, by rfl⟩ : syracuseStep 3630059 = 5445089) B5445089
theorem B1614895 : Blo 1613005 1614895 := bstep (se 1 (by rfl) ⟨1211171, by rfl⟩ : syracuseStep 1614895 = 2422343) B2422343
theorem B1614959 : Blo 1613005 1614959 := bstep (se 1 (by rfl) ⟨1211219, by rfl⟩ : syracuseStep 1614959 = 2422439) B2422439
theorem B3630491 : Blo 1613005 3630491 := bstep (se 1 (by rfl) ⟨2722868, by rfl⟩ : syracuseStep 3630491 = 5445737) B5445737
theorem B3225445829 : Blo 1613005 3225445829 := bstep (se 4 (by rfl) ⟨302385546, by rfl⟩ : syracuseStep 3225445829 = 604771093) B604771093
theorem B3065339 : Blo 1613005 3065339 := bstep (se 1 (by rfl) ⟨2299004, by rfl⟩ : syracuseStep 3065339 = 4598009) B4598009
theorem B6891169 : Blo 1613005 6891169 := bstep (se 2 (by rfl) ⟨2584188, by rfl⟩ : syracuseStep 6891169 = 5168377) B5168377
theorem B6129371 : Blo 1613005 6129371 := bstep (se 1 (by rfl) ⟨4597028, by rfl⟩ : syracuseStep 6129371 = 9194057) B9194057
theorem B22095803 : Blo 1613005 22095803 := bstep (se 1 (by rfl) ⟨16571852, by rfl⟩ : syracuseStep 22095803 = 33143705) B33143705
theorem B3631067 : Blo 1613005 3631067 := bstep (se 1 (by rfl) ⟨2723300, by rfl⟩ : syracuseStep 3631067 = 5446601) B5446601
theorem B4974571 : Blo 1613005 4974571 := bstep (se 1 (by rfl) ⟨3730928, by rfl⟩ : syracuseStep 4974571 = 7461857) B7461857
theorem B5449787 : Blo 1613005 5449787 := bstep (se 1 (by rfl) ⟨4087340, by rfl⟩ : syracuseStep 5449787 = 8174681) B8174681
theorem B12257405 : Blo 1613005 12257405 := bstep (se 3 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 12257405 = 4596527) B4596527
theorem B3631247 : Blo 1613005 3631247 := bstep (se 1 (by rfl) ⟨2723435, by rfl⟩ : syracuseStep 3631247 = 5446871) B5446871
theorem B3631337 : Blo 1613005 3631337 := bstep (se 2 (by rfl) ⟨1361751, by rfl⟩ : syracuseStep 3631337 = 2723503) B2723503
theorem B107604233 : Blo 1613005 107604233 := bstep (se 2 (by rfl) ⟨40351587, by rfl⟩ : syracuseStep 107604233 = 80703175) B80703175
theorem B2042167 : Blo 1613005 2042167 := bstep (se 1 (by rfl) ⟨1531625, by rfl⟩ : syracuseStep 2042167 = 3063251) B3063251
theorem B5450057 : Blo 1613005 5450057 := bstep (se 2 (by rfl) ⟨2043771, by rfl⟩ : syracuseStep 5450057 = 4087543) B4087543
theorem B1722703 : Blo 1613005 1722703 := bstep (se 1 (by rfl) ⟨1292027, by rfl⟩ : syracuseStep 1722703 = 2584055) B2584055
theorem B5450219 : Blo 1613005 5450219 := bstep (se 1 (by rfl) ⟨4087664, by rfl⟩ : syracuseStep 5450219 = 8175329) B8175329
theorem B3631607 : Blo 1613005 3631607 := bstep (se 1 (by rfl) ⟨2723705, by rfl⟩ : syracuseStep 3631607 = 5447411) B5447411
theorem B4360861 : Blo 1613005 4360861 := bstep (se 3 (by rfl) ⟨817661, by rfl⟩ : syracuseStep 4360861 = 1635323) B1635323
theorem B9817051 : Blo 1613005 9817051 := bstep (se 1 (by rfl) ⟨7362788, by rfl⟩ : syracuseStep 9817051 = 14725577) B14725577
theorem B2419679 : Blo 1613005 2419679 := bstep (se 1 (by rfl) ⟨1814759, by rfl⟩ : syracuseStep 2419679 = 3629519) B3629519
theorem B2182199 : Blo 1613005 2182199 := bstep (se 1 (by rfl) ⟨1636649, by rfl⟩ : syracuseStep 2182199 = 3273299) B3273299
theorem B3632201 : Blo 1613005 3632201 := bstep (se 2 (by rfl) ⟨1362075, by rfl⟩ : syracuseStep 3632201 = 2724151) B2724151
theorem B2420123 : Blo 1613005 2420123 := bstep (se 1 (by rfl) ⟨1815092, by rfl⟩ : syracuseStep 2420123 = 3630185) B3630185
theorem B7359905 : Blo 1613005 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B13790675 : Blo 1613005 13790675 := bstep (se 1 (by rfl) ⟨10343006, by rfl⟩ : syracuseStep 13790675 = 20686013) B20686013
theorem B15502823 : Blo 1613005 15502823 := bstep (se 1 (by rfl) ⟨11627117, by rfl⟩ : syracuseStep 15502823 = 23254235) B23254235
theorem B20688473 : Blo 1613005 20688473 := bstep (se 2 (by rfl) ⟨7758177, by rfl⟩ : syracuseStep 20688473 = 15516355) B15516355
theorem B3878543 : Blo 1613005 3878543 := bstep (se 1 (by rfl) ⟨2908907, by rfl⟩ : syracuseStep 3878543 = 5817815) B5817815
theorem B2420543 : Blo 1613005 2420543 := bstep (se 1 (by rfl) ⟨1815407, by rfl⟩ : syracuseStep 2420543 = 3630815) B3630815
theorem B35843917 : Blo 1613005 35843917 := bstep (se 3 (by rfl) ⟨6720734, by rfl⟩ : syracuseStep 35843917 = 13441469) B13441469
theorem B2420729 : Blo 1613005 2420729 := bstep (se 2 (by rfl) ⟨907773, by rfl⟩ : syracuseStep 2420729 = 1815547) B1815547
theorem B9195515 : Blo 1613005 9195515 := bstep (se 1 (by rfl) ⟨6896636, by rfl⟩ : syracuseStep 9195515 = 13793273) B13793273
theorem B4083767 : Blo 1613005 4083767 := bstep (se 1 (by rfl) ⟨3062825, by rfl⟩ : syracuseStep 4083767 = 6125651) B6125651
theorem B2297911 : Blo 1613005 2297911 := bstep (se 1 (by rfl) ⟨1723433, by rfl⟩ : syracuseStep 2297911 = 3446867) B3446867
theorem B2723935 : Blo 1613005 2723935 := bstep (se 1 (by rfl) ⟨2042951, by rfl⟩ : syracuseStep 2723935 = 4085903) B4085903
theorem B1814683 : Blo 1613005 1814683 := bstep (se 1 (by rfl) ⟨1361012, by rfl⟩ : syracuseStep 1814683 = 2722025) B2722025
theorem B2420969 : Blo 1613005 2420969 := bstep (se 2 (by rfl) ⟨907863, by rfl⟩ : syracuseStep 2420969 = 1815727) B1815727
theorem B27586817 : Blo 1613005 27586817 := bstep (se 2 (by rfl) ⟨10345056, by rfl⟩ : syracuseStep 27586817 = 20690113) B20690113
theorem B2421095 : Blo 1613005 2421095 := bstep (se 1 (by rfl) ⟨1815821, by rfl⟩ : syracuseStep 2421095 = 3631643) B3631643
theorem B4084091 : Blo 1613005 4084091 := bstep (se 1 (by rfl) ⟨3063068, by rfl⟩ : syracuseStep 4084091 = 6126137) B6126137
theorem B5042639 : Blo 1613005 5042639 := bstep (se 1 (by rfl) ⟨3781979, by rfl⟩ : syracuseStep 5042639 = 7563959) B7563959
theorem B8172089 : Blo 1613005 8172089 := bstep (se 2 (by rfl) ⟨3064533, by rfl⟩ : syracuseStep 8172089 = 6129067) B6129067
theorem B6894143 : Blo 1613005 6894143 := bstep (se 1 (by rfl) ⟨5170607, by rfl⟩ : syracuseStep 6894143 = 10341215) B10341215
theorem B31429241 : Blo 1613005 31429241 := bstep (se 2 (by rfl) ⟨11785965, by rfl⟩ : syracuseStep 31429241 = 23571931) B23571931
theorem B2421641 : Blo 1613005 2421641 := bstep (se 2 (by rfl) ⟨908115, by rfl⟩ : syracuseStep 2421641 = 1816231) B1816231
theorem B6894503 : Blo 1613005 6894503 := bstep (se 1 (by rfl) ⟨5170877, by rfl⟩ : syracuseStep 6894503 = 10341755) B10341755
theorem B7861457 : Blo 1613005 7861457 := bstep (se 2 (by rfl) ⟨2948046, by rfl⟩ : syracuseStep 7861457 = 5896093) B5896093
theorem B3880187 : Blo 1613005 3880187 := bstep (se 1 (by rfl) ⟨2910140, by rfl⟩ : syracuseStep 3880187 = 5820281) B5820281
theorem B2422025 : Blo 1613005 2422025 := bstep (se 2 (by rfl) ⟨908259, by rfl⟩ : syracuseStep 2422025 = 1816519) B1816519
theorem B1815871 : Blo 1613005 1815871 := bstep (se 1 (by rfl) ⟨1361903, by rfl⟩ : syracuseStep 1815871 = 2723807) B2723807
theorem B2422079 : Blo 1613005 2422079 := bstep (se 1 (by rfl) ⟨1816559, by rfl⟩ : syracuseStep 2422079 = 3633119) B3633119
theorem B2725231 : Blo 1613005 2725231 := bstep (se 1 (by rfl) ⟨2043923, by rfl⟩ : syracuseStep 2725231 = 4087847) B4087847
theorem B6124967 : Blo 1613005 6124967 := bstep (se 1 (by rfl) ⟨4593725, by rfl⟩ : syracuseStep 6124967 = 9187451) B9187451
theorem B7755335 : Blo 1613005 7755335 := bstep (se 1 (by rfl) ⟨5816501, by rfl⟩ : syracuseStep 7755335 = 11633003) B11633003
theorem B20682323 : Blo 1613005 20682323 := bstep (se 1 (by rfl) ⟨15511742, by rfl⟩ : syracuseStep 20682323 = 31023485) B31023485
theorem B2422505 : Blo 1613005 2422505 := bstep (se 2 (by rfl) ⟨908439, by rfl⟩ : syracuseStep 2422505 = 1816879) B1816879
theorem B1816303 : Blo 1613005 1816303 := bstep (se 1 (by rfl) ⟨1362227, by rfl⟩ : syracuseStep 1816303 = 2724455) B2724455
theorem B13784903 : Blo 1613005 13784903 := bstep (se 1 (by rfl) ⟨10338677, by rfl⟩ : syracuseStep 13784903 = 20677355) B20677355
theorem B1816411 : Blo 1613005 1816411 := bstep (se 1 (by rfl) ⟨1362308, by rfl⟩ : syracuseStep 1816411 = 2724617) B2724617
theorem B2488391 : Blo 1613005 2488391 := bstep (se 1 (by rfl) ⟨1866293, by rfl⟩ : syracuseStep 2488391 = 3732587) B3732587
theorem B8730719 : Blo 1613005 8730719 := bstep (se 1 (by rfl) ⟨6548039, by rfl⟩ : syracuseStep 8730719 = 13096079) B13096079
theorem B31013027 : Blo 1613005 31013027 := bstep (se 1 (by rfl) ⟨23259770, by rfl⟩ : syracuseStep 31013027 = 46519541) B46519541
theorem B1816807 : Blo 1613005 1816807 := bstep (se 1 (by rfl) ⟨1362605, by rfl⟩ : syracuseStep 1816807 = 2725211) B2725211
theorem B34920719 : Blo 1613005 34920719 := bstep (se 1 (by rfl) ⟨26190539, by rfl⟩ : syracuseStep 34920719 = 52381079) B52381079
theorem B18897229 : Blo 1613005 18897229 := bstep (se 3 (by rfl) ⟨3543230, by rfl⟩ : syracuseStep 18897229 = 7086461) B7086461
theorem B5446007 : Blo 1613005 5446007 := bstep (se 1 (by rfl) ⟨4084505, by rfl⟩ : syracuseStep 5446007 = 8169011) B8169011
theorem B3062377 : Blo 1613005 3062377 := bstep (se 2 (by rfl) ⟨1148391, by rfl⟩ : syracuseStep 3062377 = 2296783) B2296783
theorem B31005341 : Blo 1613005 31005341 := bstep (se 3 (by rfl) ⟨5813501, by rfl⟩ : syracuseStep 31005341 = 11627003) B11627003
theorem B6896431 : Blo 1613005 6896431 := bstep (se 1 (by rfl) ⟨5172323, by rfl⟩ : syracuseStep 6896431 = 10344647) B10344647
theorem B1613007 : Blo 1613005 1613007 := bstep (se 1 (by rfl) ⟨1209755, by rfl⟩ : syracuseStep 1613007 = 2419511) B2419511
theorem B1613031 : Blo 1613005 1613031 := bstep (se 1 (by rfl) ⟨1209773, by rfl⟩ : syracuseStep 1613031 = 2419547) B2419547
theorem B12254489 : Blo 1613005 12254489 := bstep (se 2 (by rfl) ⟨4595433, by rfl⟩ : syracuseStep 12254489 = 9190867) B9190867
theorem B1613127 : Blo 1613005 1613127 := bstep (se 1 (by rfl) ⟨1209845, by rfl⟩ : syracuseStep 1613127 = 2419691) B2419691
theorem B8166743 : Blo 1613005 8166743 := bstep (se 1 (by rfl) ⟨6125057, by rfl⟩ : syracuseStep 8166743 = 12250115) B12250115
theorem B5447087 : Blo 1613005 5447087 := bstep (se 1 (by rfl) ⟨4085315, by rfl⟩ : syracuseStep 5447087 = 8170631) B8170631
theorem B1613263 : Blo 1613005 1613263 := bstep (se 1 (by rfl) ⟨1209947, by rfl⟩ : syracuseStep 1613263 = 2419895) B2419895
theorem B6127123 : Blo 1613005 6127123 := bstep (se 1 (by rfl) ⟨4595342, by rfl⟩ : syracuseStep 6127123 = 9190685) B9190685
theorem B8175167 : Blo 1613005 8175167 := bstep (se 1 (by rfl) ⟨6131375, by rfl⟩ : syracuseStep 8175167 = 12262751) B12262751
theorem B10337881 : Blo 1613005 10337881 := bstep (se 2 (by rfl) ⟨3876705, by rfl⟩ : syracuseStep 10337881 = 7753411) B7753411
theorem B1613423 : Blo 1613005 1613423 := bstep (se 1 (by rfl) ⟨1210067, by rfl⟩ : syracuseStep 1613423 = 2420135) B2420135
theorem B1613479 : Blo 1613005 1613479 := bstep (se 1 (by rfl) ⟨1210109, by rfl⟩ : syracuseStep 1613479 = 2420219) B2420219
theorem B1613543 : Blo 1613005 1613543 := bstep (se 1 (by rfl) ⟨1210157, by rfl⟩ : syracuseStep 1613543 = 2420315) B2420315
theorem B13795049 : Blo 1613005 13795049 := bstep (se 2 (by rfl) ⟨5173143, by rfl⟩ : syracuseStep 13795049 = 10346287) B10346287
theorem B1613599 : Blo 1613005 1613599 := bstep (se 1 (by rfl) ⟨1210199, by rfl⟩ : syracuseStep 1613599 = 2420399) B2420399
theorem B6987617 : Blo 1613005 6987617 := bstep (se 2 (by rfl) ⟨2620356, by rfl⟩ : syracuseStep 6987617 = 5240713) B5240713
theorem B1613679 : Blo 1613005 1613679 := bstep (se 1 (by rfl) ⟨1210259, by rfl⟩ : syracuseStep 1613679 = 2420519) B2420519
theorem B1613735 : Blo 1613005 1613735 := bstep (se 1 (by rfl) ⟨1210301, by rfl⟩ : syracuseStep 1613735 = 2420603) B2420603
theorem B565985303 : Blo 1613005 565985303 := bstep (se 1 (by rfl) ⟨424488977, by rfl⟩ : syracuseStep 565985303 = 848977955) B848977955
theorem B3063881 : Blo 1613005 3063881 := bstep (se 2 (by rfl) ⟨1148955, by rfl⟩ : syracuseStep 3063881 = 2297911) B2297911
theorem B1613979 : Blo 1613005 1613979 := bstep (se 1 (by rfl) ⟨1210484, by rfl⟩ : syracuseStep 1613979 = 2420969) B2420969
theorem B18391211 : Blo 1613005 18391211 := bstep (se 1 (by rfl) ⟨13793408, by rfl⟩ : syracuseStep 18391211 = 27586817) B27586817
theorem B1614063 : Blo 1613005 1614063 := bstep (se 1 (by rfl) ⟨1210547, by rfl⟩ : syracuseStep 1614063 = 2421095) B2421095
theorem B5448059 : Blo 1613005 5448059 := bstep (se 1 (by rfl) ⟨4086044, by rfl⟩ : syracuseStep 5448059 = 8172089) B8172089
theorem B4596095 : Blo 1613005 4596095 := bstep (se 1 (by rfl) ⟨3447071, by rfl⟩ : syracuseStep 4596095 = 6894143) B6894143
theorem B1614427 : Blo 1613005 1614427 := bstep (se 1 (by rfl) ⟨1210820, by rfl⟩ : syracuseStep 1614427 = 2421641) B2421641
theorem B4596335 : Blo 1613005 4596335 := bstep (se 1 (by rfl) ⟨3447251, by rfl⟩ : syracuseStep 4596335 = 6894503) B6894503
theorem B23257925 : Blo 1613005 23257925 := bstep (se 4 (by rfl) ⟨2180430, by rfl⟩ : syracuseStep 23257925 = 4360861) B4360861
theorem B1614683 : Blo 1613005 1614683 := bstep (se 1 (by rfl) ⟨1211012, by rfl⟩ : syracuseStep 1614683 = 2422025) B2422025
theorem B1614719 : Blo 1613005 1614719 := bstep (se 1 (by rfl) ⟨1211039, by rfl⟩ : syracuseStep 1614719 = 2422079) B2422079
theorem B5170223 : Blo 1613005 5170223 := bstep (se 1 (by rfl) ⟨3877667, by rfl⟩ : syracuseStep 5170223 = 7755335) B7755335
theorem B13788215 : Blo 1613005 13788215 := bstep (se 1 (by rfl) ⟨10341161, by rfl⟩ : syracuseStep 13788215 = 20682323) B20682323
theorem B1615003 : Blo 1613005 1615003 := bstep (se 1 (by rfl) ⟨1211252, by rfl⟩ : syracuseStep 1615003 = 2422505) B2422505
theorem B14730535 : Blo 1613005 14730535 := bstep (se 1 (by rfl) ⟨11047901, by rfl⟩ : syracuseStep 14730535 = 22095803) B22095803
theorem B3630671 : Blo 1613005 3630671 := bstep (se 1 (by rfl) ⟨2723003, by rfl⟩ : syracuseStep 3630671 = 5446007) B5446007
theorem B20670227 : Blo 1613005 20670227 := bstep (se 1 (by rfl) ⟨15502670, by rfl⟩ : syracuseStep 20670227 = 31005341) B31005341
theorem B8169497 : Blo 1613005 8169497 := bstep (se 2 (by rfl) ⟨3063561, by rfl⟩ : syracuseStep 8169497 = 6127123) B6127123
theorem B8169659 : Blo 1613005 8169659 := bstep (se 1 (by rfl) ⟨6127244, by rfl⟩ : syracuseStep 8169659 = 12254489) B12254489
theorem B3631391 : Blo 1613005 3631391 := bstep (se 1 (by rfl) ⟨2723543, by rfl⟩ : syracuseStep 3631391 = 5447087) B5447087
theorem B9193783 : Blo 1613005 9193783 := bstep (se 1 (by rfl) ⟨6895337, by rfl⟩ : syracuseStep 9193783 = 13790675) B13790675
theorem B5450111 : Blo 1613005 5450111 := bstep (se 1 (by rfl) ⟨4087583, by rfl⟩ : syracuseStep 5450111 = 8175167) B8175167
theorem B6130343 : Blo 1613005 6130343 := bstep (se 1 (by rfl) ⟨4597757, by rfl⟩ : syracuseStep 6130343 = 9195515) B9195515
theorem B2722511 : Blo 1613005 2722511 := bstep (se 1 (by rfl) ⟨2041883, by rfl⟩ : syracuseStep 2722511 = 4083767) B4083767
theorem B3631913 : Blo 1613005 3631913 := bstep (se 2 (by rfl) ⟨1361967, by rfl⟩ : syracuseStep 3631913 = 2723935) B2723935
theorem B5819197 : Blo 1613005 5819197 := bstep (se 3 (by rfl) ⟨1091099, by rfl⟩ : syracuseStep 5819197 = 2182199) B2182199
theorem B2419577 : Blo 1613005 2419577 := bstep (se 2 (by rfl) ⟨907341, by rfl⟩ : syracuseStep 2419577 = 1814683) B1814683
theorem B2722727 : Blo 1613005 2722727 := bstep (se 1 (by rfl) ⟨2042045, by rfl⟩ : syracuseStep 2722727 = 4084091) B4084091
theorem B3632183 : Blo 1613005 3632183 := bstep (se 1 (by rfl) ⟨2724137, by rfl⟩ : syracuseStep 3632183 = 5448275) B5448275
theorem B2722889 : Blo 1613005 2722889 := bstep (se 2 (by rfl) ⟨1021083, by rfl⟩ : syracuseStep 2722889 = 2042167) B2042167
theorem B2296937 : Blo 1613005 2296937 := bstep (se 2 (by rfl) ⟨861351, by rfl⟩ : syracuseStep 2296937 = 1722703) B1722703
theorem B2419823 : Blo 1613005 2419823 := bstep (se 1 (by rfl) ⟨1814867, by rfl⟩ : syracuseStep 2419823 = 3629735) B3629735
theorem B27569321 : Blo 1613005 27569321 := bstep (se 2 (by rfl) ⟨10338495, by rfl⟩ : syracuseStep 27569321 = 20676991) B20676991
theorem B2419919 : Blo 1613005 2419919 := bstep (se 1 (by rfl) ⟨1814939, by rfl⟩ : syracuseStep 2419919 = 3629879) B3629879
theorem B3632363 : Blo 1613005 3632363 := bstep (se 1 (by rfl) ⟨2724272, by rfl⟩ : syracuseStep 3632363 = 5448545) B5448545
theorem B2420039 : Blo 1613005 2420039 := bstep (se 1 (by rfl) ⟨1815029, by rfl⟩ : syracuseStep 2420039 = 3630059) B3630059
theorem B4083169 : Blo 1613005 4083169 := bstep (se 2 (by rfl) ⟨1531188, by rfl⟩ : syracuseStep 4083169 = 3062377) B3062377
theorem B2420327 : Blo 1613005 2420327 := bstep (se 1 (by rfl) ⟨1815245, by rfl⟩ : syracuseStep 2420327 = 3630491) B3630491
theorem B4083311 : Blo 1613005 4083311 := bstep (se 1 (by rfl) ⟨3062483, by rfl⟩ : syracuseStep 4083311 = 6124967) B6124967
theorem B2150297219 : Blo 1613005 2150297219 := bstep (se 1 (by rfl) ⟨1612722914, by rfl⟩ : syracuseStep 2150297219 = 3225445829) B3225445829
theorem B2043559 : Blo 1613005 2043559 := bstep (se 1 (by rfl) ⟨1532669, by rfl⟩ : syracuseStep 2043559 = 3065339) B3065339
theorem B9195241 : Blo 1613005 9195241 := bstep (se 2 (by rfl) ⟨3448215, by rfl⟩ : syracuseStep 9195241 = 6896431) B6896431
theorem B13447037 : Blo 1613005 13447037 := bstep (se 3 (by rfl) ⟨2521319, by rfl⟩ : syracuseStep 13447037 = 5042639) B5042639
theorem B2420711 : Blo 1613005 2420711 := bstep (se 1 (by rfl) ⟨1815533, by rfl⟩ : syracuseStep 2420711 = 3631067) B3631067
theorem B3633191 : Blo 1613005 3633191 := bstep (se 1 (by rfl) ⟨2724893, by rfl⟩ : syracuseStep 3633191 = 5449787) B5449787
theorem B1658927 : Blo 1613005 1658927 := bstep (se 1 (by rfl) ⟨1244195, by rfl⟩ : syracuseStep 1658927 = 2488391) B2488391
theorem B5820479 : Blo 1613005 5820479 := bstep (se 1 (by rfl) ⟨4365359, by rfl⟩ : syracuseStep 5820479 = 8730719) B8730719
theorem B8171603 : Blo 1613005 8171603 := bstep (se 1 (by rfl) ⟨6128702, by rfl⟩ : syracuseStep 8171603 = 12257405) B12257405
theorem B2420831 : Blo 1613005 2420831 := bstep (se 1 (by rfl) ⟨1815623, by rfl⟩ : syracuseStep 2420831 = 3631247) B3631247
theorem B2420891 : Blo 1613005 2420891 := bstep (se 1 (by rfl) ⟨1815668, by rfl⟩ : syracuseStep 2420891 = 3631337) B3631337
theorem B3633371 : Blo 1613005 3633371 := bstep (se 1 (by rfl) ⟨2725028, by rfl⟩ : syracuseStep 3633371 = 5450057) B5450057
theorem B3633479 : Blo 1613005 3633479 := bstep (se 1 (by rfl) ⟨2725109, by rfl⟩ : syracuseStep 3633479 = 5450219) B5450219
theorem B2421071 : Blo 1613005 2421071 := bstep (se 1 (by rfl) ⟨1815803, by rfl⟩ : syracuseStep 2421071 = 3631607) B3631607
theorem B2421161 : Blo 1613005 2421161 := bstep (se 2 (by rfl) ⟨907935, by rfl⟩ : syracuseStep 2421161 = 1815871) B1815871
theorem B3633641 : Blo 1613005 3633641 := bstep (se 2 (by rfl) ⟨1362615, by rfl⟩ : syracuseStep 3633641 = 2725231) B2725231
theorem B2421467 : Blo 1613005 2421467 := bstep (se 1 (by rfl) ⟨1816100, by rfl⟩ : syracuseStep 2421467 = 3632201) B3632201
theorem B13783841 : Blo 1613005 13783841 := bstep (se 2 (by rfl) ⟨5168940, by rfl⟩ : syracuseStep 13783841 = 10337881) B10337881
theorem B9188225 : Blo 1613005 9188225 := bstep (se 2 (by rfl) ⟨3445584, by rfl⟩ : syracuseStep 9188225 = 6891169) B6891169
theorem B5444495 : Blo 1613005 5444495 := bstep (se 1 (by rfl) ⟨4083371, by rfl⟩ : syracuseStep 5444495 = 8166743) B8166743
theorem B2421737 : Blo 1613005 2421737 := bstep (se 2 (by rfl) ⟨908151, by rfl⟩ : syracuseStep 2421737 = 1816303) B1816303
theorem B10335215 : Blo 1613005 10335215 := bstep (se 1 (by rfl) ⟨7751411, by rfl⟩ : syracuseStep 10335215 = 15502823) B15502823
theorem B13792315 : Blo 1613005 13792315 := bstep (se 1 (by rfl) ⟨10344236, by rfl⟩ : syracuseStep 13792315 = 20688473) B20688473
theorem B2585695 : Blo 1613005 2585695 := bstep (se 1 (by rfl) ⟨1939271, by rfl⟩ : syracuseStep 2585695 = 3878543) B3878543
theorem B2421881 : Blo 1613005 2421881 := bstep (se 2 (by rfl) ⟨908205, by rfl⟩ : syracuseStep 2421881 = 1816411) B1816411
theorem B9196699 : Blo 1613005 9196699 := bstep (se 1 (by rfl) ⟨6897524, by rfl⟩ : syracuseStep 9196699 = 13795049) B13795049
theorem B4658411 : Blo 1613005 4658411 := bstep (se 1 (by rfl) ⟨3493808, by rfl⟩ : syracuseStep 4658411 = 6987617) B6987617
theorem B6632761 : Blo 1613005 6632761 := bstep (se 2 (by rfl) ⟨2487285, by rfl⟩ : syracuseStep 6632761 = 4974571) B4974571
theorem B5445035 : Blo 1613005 5445035 := bstep (se 1 (by rfl) ⟨4083776, by rfl⟩ : syracuseStep 5445035 = 8167553) B8167553
theorem B3446363 : Blo 1613005 3446363 := bstep (se 1 (by rfl) ⟨2584772, by rfl⟩ : syracuseStep 3446363 = 5169545) B5169545
theorem B2422409 : Blo 1613005 2422409 := bstep (se 2 (by rfl) ⟨908403, by rfl⟩ : syracuseStep 2422409 = 1816807) B1816807
theorem B20952827 : Blo 1613005 20952827 := bstep (se 1 (by rfl) ⟨15714620, by rfl⟩ : syracuseStep 20952827 = 31429241) B31429241
theorem B19404551 : Blo 1613005 19404551 := bstep (se 1 (by rfl) ⟨14553413, by rfl⟩ : syracuseStep 19404551 = 29106827) B29106827
theorem B25196305 : Blo 1613005 25196305 := bstep (se 2 (by rfl) ⟨9448614, by rfl⟩ : syracuseStep 25196305 = 18897229) B18897229
theorem B4364063 : Blo 1613005 4364063 := bstep (se 1 (by rfl) ⟨3273047, by rfl⟩ : syracuseStep 4364063 = 6546095) B6546095
theorem B5445575 : Blo 1613005 5445575 := bstep (se 1 (by rfl) ⟨4084181, by rfl⟩ : syracuseStep 5445575 = 8168363) B8168363
theorem B5240971 : Blo 1613005 5240971 := bstep (se 1 (by rfl) ⟨3930728, by rfl⟩ : syracuseStep 5240971 = 7861457) B7861457
theorem B2586791 : Blo 1613005 2586791 := bstep (se 1 (by rfl) ⟨1940093, by rfl⟩ : syracuseStep 2586791 = 3880187) B3880187
theorem B4086247 : Blo 1613005 4086247 := bstep (se 1 (by rfl) ⟨3064685, by rfl⟩ : syracuseStep 4086247 = 6129371) B6129371
theorem B9189935 : Blo 1613005 9189935 := bstep (se 1 (by rfl) ⟨6892451, by rfl⟩ : syracuseStep 9189935 = 13784903) B13784903
theorem B13089401 : Blo 1613005 13089401 := bstep (se 2 (by rfl) ⟨4908525, by rfl⟩ : syracuseStep 13089401 = 9817051) B9817051
theorem B20675351 : Blo 1613005 20675351 := bstep (se 1 (by rfl) ⟨15506513, by rfl⟩ : syracuseStep 20675351 = 31013027) B31013027
theorem B71736155 : Blo 1613005 71736155 := bstep (se 1 (by rfl) ⟨53802116, by rfl⟩ : syracuseStep 71736155 = 107604233) B107604233
theorem B23280479 : Blo 1613005 23280479 := bstep (se 1 (by rfl) ⟨17460359, by rfl⟩ : syracuseStep 23280479 = 34920719) B34920719
theorem B1613119 : Blo 1613005 1613119 := bstep (se 1 (by rfl) ⟨1209839, by rfl⟩ : syracuseStep 1613119 = 2419679) B2419679
theorem B1613415 : Blo 1613005 1613415 := bstep (se 1 (by rfl) ⟨1210061, by rfl⟩ : syracuseStep 1613415 = 2420123) B2420123
theorem B4906603 : Blo 1613005 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B47791889 : Blo 1613005 47791889 := bstep (se 2 (by rfl) ⟨17921958, by rfl⟩ : syracuseStep 47791889 = 35843917) B35843917
theorem B1613695 : Blo 1613005 1613695 := bstep (se 1 (by rfl) ⟨1210271, by rfl⟩ : syracuseStep 1613695 = 2420543) B2420543
theorem B1613819 : Blo 1613005 1613819 := bstep (se 1 (by rfl) ⟨1210364, by rfl⟩ : syracuseStep 1613819 = 2420729) B2420729
theorem B377323535 : Blo 1613005 377323535 := bstep (se 1 (by rfl) ⟨282992651, by rfl⟩ : syracuseStep 377323535 = 565985303) B565985303
theorem B5447735 : Blo 1613005 5447735 := bstep (se 1 (by rfl) ⟨4085801, by rfl⟩ : syracuseStep 5447735 = 8171603) B8171603
theorem B1613887 : Blo 1613005 1613887 := bstep (se 1 (by rfl) ⟨1210415, by rfl⟩ : syracuseStep 1613887 = 2420831) B2420831
theorem B1613927 : Blo 1613005 1613927 := bstep (se 1 (by rfl) ⟨1210445, by rfl⟩ : syracuseStep 1613927 = 2420891) B2420891
theorem B4423805 : Blo 1613005 4423805 := bstep (se 3 (by rfl) ⟨829463, by rfl⟩ : syracuseStep 4423805 = 1658927) B1658927
theorem B6987961 : Blo 1613005 6987961 := bstep (se 2 (by rfl) ⟨2620485, by rfl⟩ : syracuseStep 6987961 = 5240971) B5240971
theorem B1614047 : Blo 1613005 1614047 := bstep (se 1 (by rfl) ⟨1210535, by rfl⟩ : syracuseStep 1614047 = 2421071) B2421071
theorem B3064063 : Blo 1613005 3064063 := bstep (se 1 (by rfl) ⟨2298047, by rfl⟩ : syracuseStep 3064063 = 4596095) B4596095
theorem B1614107 : Blo 1613005 1614107 := bstep (se 1 (by rfl) ⟨1210580, by rfl⟩ : syracuseStep 1614107 = 2421161) B2421161
theorem B3064223 : Blo 1613005 3064223 := bstep (se 1 (by rfl) ⟨2298167, by rfl⟩ : syracuseStep 3064223 = 4596335) B4596335
theorem B1614311 : Blo 1613005 1614311 := bstep (se 1 (by rfl) ⟨1210733, by rfl⟩ : syracuseStep 1614311 = 2421467) B2421467
theorem B3629663 : Blo 1613005 3629663 := bstep (se 1 (by rfl) ⟨2722247, by rfl⟩ : syracuseStep 3629663 = 5444495) B5444495
theorem B5448329 : Blo 1613005 5448329 := bstep (se 2 (by rfl) ⟨2043123, by rfl⟩ : syracuseStep 5448329 = 4086247) B4086247
theorem B1614491 : Blo 1613005 1614491 := bstep (se 1 (by rfl) ⟨1210868, by rfl⟩ : syracuseStep 1614491 = 2421737) B2421737
theorem B9192143 : Blo 1613005 9192143 := bstep (se 1 (by rfl) ⟨6894107, by rfl⟩ : syracuseStep 9192143 = 13788215) B13788215
theorem B1614587 : Blo 1613005 1614587 := bstep (se 1 (by rfl) ⟨1210940, by rfl⟩ : syracuseStep 1614587 = 2421881) B2421881
theorem B3105607 : Blo 1613005 3105607 := bstep (se 1 (by rfl) ⟨2329205, by rfl⟩ : syracuseStep 3105607 = 4658411) B4658411
theorem B3630023 : Blo 1613005 3630023 := bstep (se 1 (by rfl) ⟨2722517, by rfl⟩ : syracuseStep 3630023 = 5445035) B5445035
theorem B7758929 : Blo 1613005 7758929 := bstep (se 2 (by rfl) ⟨2909598, by rfl⟩ : syracuseStep 7758929 = 5819197) B5819197
theorem B1614939 : Blo 1613005 1614939 := bstep (se 1 (by rfl) ⟨1211204, by rfl⟩ : syracuseStep 1614939 = 2422409) B2422409
theorem B13968551 : Blo 1613005 13968551 := bstep (se 1 (by rfl) ⟨10476413, by rfl⟩ : syracuseStep 13968551 = 20952827) B20952827
theorem B12936367 : Blo 1613005 12936367 := bstep (se 1 (by rfl) ⟨9702275, by rfl⟩ : syracuseStep 12936367 = 19404551) B19404551
theorem B13780151 : Blo 1613005 13780151 := bstep (se 1 (by rfl) ⟨10335113, by rfl⟩ : syracuseStep 13780151 = 20670227) B20670227
theorem B2909375 : Blo 1613005 2909375 := bstep (se 1 (by rfl) ⟨2182031, by rfl⟩ : syracuseStep 2909375 = 4364063) B4364063
theorem B3630383 : Blo 1613005 3630383 := bstep (se 1 (by rfl) ⟨2722787, by rfl⟩ : syracuseStep 3630383 = 5445575) B5445575
theorem B8726267 : Blo 1613005 8726267 := bstep (se 1 (by rfl) ⟨6544700, by rfl⟩ : syracuseStep 8726267 = 13089401) B13089401
theorem B35858765 : Blo 1613005 35858765 := bstep (se 3 (by rfl) ⟨6723518, by rfl⟩ : syracuseStep 35858765 = 13447037) B13447037
theorem B2722207 : Blo 1613005 2722207 := bstep (se 1 (by rfl) ⟨2041655, by rfl⟩ : syracuseStep 2722207 = 4083311) B4083311
theorem B31861259 : Blo 1613005 31861259 := bstep (se 1 (by rfl) ⟨23895944, by rfl⟩ : syracuseStep 31861259 = 47791889) B47791889
theorem B27560573 : Blo 1613005 27560573 := bstep (se 3 (by rfl) ⟨5167607, by rfl⟩ : syracuseStep 27560573 = 10335215) B10335215
theorem B2042587 : Blo 1613005 2042587 := bstep (se 1 (by rfl) ⟨1531940, by rfl⟩ : syracuseStep 2042587 = 3063881) B3063881
theorem B3632039 : Blo 1613005 3632039 := bstep (se 1 (by rfl) ⟨2724029, by rfl⟩ : syracuseStep 3632039 = 5448059) B5448059
theorem B12258377 : Blo 1613005 12258377 := bstep (se 2 (by rfl) ⟨4596891, by rfl⟩ : syracuseStep 12258377 = 9193783) B9193783
theorem B2420447 : Blo 1613005 2420447 := bstep (se 1 (by rfl) ⟨1815335, by rfl⟩ : syracuseStep 2420447 = 3630671) B3630671
theorem B2297575 : Blo 1613005 2297575 := bstep (se 1 (by rfl) ⟨1723181, by rfl⟩ : syracuseStep 2297575 = 3446363) B3446363
theorem B1724527 : Blo 1613005 1724527 := bstep (se 1 (by rfl) ⟨1293395, by rfl⟩ : syracuseStep 1724527 = 2586791) B2586791
theorem B2420927 : Blo 1613005 2420927 := bstep (se 1 (by rfl) ⟨1815695, by rfl⟩ : syracuseStep 2420927 = 3631391) B3631391
theorem B3633407 : Blo 1613005 3633407 := bstep (se 1 (by rfl) ⟨2725055, by rfl⟩ : syracuseStep 3633407 = 5450111) B5450111
theorem B5734125917 : Blo 1613005 5734125917 := bstep (se 3 (by rfl) ⟨1075148609, by rfl⟩ : syracuseStep 5734125917 = 2150297219) B2150297219
theorem B19640713 : Blo 1613005 19640713 := bstep (se 2 (by rfl) ⟨7365267, by rfl⟩ : syracuseStep 19640713 = 14730535) B14730535
theorem B8843681 : Blo 1613005 8843681 := bstep (se 2 (by rfl) ⟨3316380, by rfl⟩ : syracuseStep 8843681 = 6632761) B6632761
theorem B1815007 : Blo 1613005 1815007 := bstep (se 1 (by rfl) ⟨1361255, by rfl⟩ : syracuseStep 1815007 = 2722511) B2722511
theorem B13783567 : Blo 1613005 13783567 := bstep (se 1 (by rfl) ⟨10337675, by rfl⟩ : syracuseStep 13783567 = 20675351) B20675351
theorem B2421275 : Blo 1613005 2421275 := bstep (se 1 (by rfl) ⟨1815956, by rfl⟩ : syracuseStep 2421275 = 3631913) B3631913
theorem B15520319 : Blo 1613005 15520319 := bstep (se 1 (by rfl) ⟨11640239, by rfl⟩ : syracuseStep 15520319 = 23280479) B23280479
theorem B1815151 : Blo 1613005 1815151 := bstep (se 1 (by rfl) ⟨1361363, by rfl⟩ : syracuseStep 1815151 = 2722727) B2722727
theorem B5444225 : Blo 1613005 5444225 := bstep (se 2 (by rfl) ⟨2041584, by rfl⟩ : syracuseStep 5444225 = 4083169) B4083169
theorem B2421455 : Blo 1613005 2421455 := bstep (se 1 (by rfl) ⟨1816091, by rfl⟩ : syracuseStep 2421455 = 3632183) B3632183
theorem B1815259 : Blo 1613005 1815259 := bstep (se 1 (by rfl) ⟨1361444, by rfl⟩ : syracuseStep 1815259 = 2722889) B2722889
theorem B18379547 : Blo 1613005 18379547 := bstep (se 1 (by rfl) ⟨13784660, by rfl⟩ : syracuseStep 18379547 = 27569321) B27569321
theorem B6542137 : Blo 1613005 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B2421575 : Blo 1613005 2421575 := bstep (se 1 (by rfl) ⟨1816181, by rfl⟩ : syracuseStep 2421575 = 3632363) B3632363
theorem B2724745 : Blo 1613005 2724745 := bstep (se 2 (by rfl) ⟨1021779, by rfl⟩ : syracuseStep 2724745 = 2043559) B2043559
theorem B12260321 : Blo 1613005 12260321 := bstep (se 2 (by rfl) ⟨4597620, by rfl⟩ : syracuseStep 12260321 = 9195241) B9195241
theorem B2422127 : Blo 1613005 2422127 := bstep (se 1 (by rfl) ⟨1816595, by rfl⟩ : syracuseStep 2422127 = 3633191) B3633191
theorem B3880319 : Blo 1613005 3880319 := bstep (se 1 (by rfl) ⟨2910239, by rfl⟩ : syracuseStep 3880319 = 5820479) B5820479
theorem B12260807 : Blo 1613005 12260807 := bstep (se 1 (by rfl) ⟨9195605, by rfl⟩ : syracuseStep 12260807 = 18391211) B18391211
theorem B2422247 : Blo 1613005 2422247 := bstep (se 1 (by rfl) ⟨1816685, by rfl⟩ : syracuseStep 2422247 = 3633371) B3633371
theorem B2422319 : Blo 1613005 2422319 := bstep (se 1 (by rfl) ⟨1816739, by rfl⟩ : syracuseStep 2422319 = 3633479) B3633479
theorem B6125165 : Blo 1613005 6125165 := bstep (se 3 (by rfl) ⟨1148468, by rfl⟩ : syracuseStep 6125165 = 2296937) B2296937
theorem B2422427 : Blo 1613005 2422427 := bstep (se 1 (by rfl) ⟨1816820, by rfl⟩ : syracuseStep 2422427 = 3633641) B3633641
theorem B9189227 : Blo 1613005 9189227 := bstep (se 1 (by rfl) ⟨6891920, by rfl⟩ : syracuseStep 9189227 = 13783841) B13783841
theorem B15505283 : Blo 1613005 15505283 := bstep (se 1 (by rfl) ⟨11628962, by rfl⟩ : syracuseStep 15505283 = 23257925) B23257925
theorem B6125483 : Blo 1613005 6125483 := bstep (se 1 (by rfl) ⟨4594112, by rfl⟩ : syracuseStep 6125483 = 9188225) B9188225
theorem B3446815 : Blo 1613005 3446815 := bstep (se 1 (by rfl) ⟨2585111, by rfl⟩ : syracuseStep 3446815 = 5170223) B5170223
theorem B5446331 : Blo 1613005 5446331 := bstep (se 1 (by rfl) ⟨4084748, by rfl⟩ : syracuseStep 5446331 = 8169497) B8169497
theorem B18389753 : Blo 1613005 18389753 := bstep (se 2 (by rfl) ⟨6896157, by rfl⟩ : syracuseStep 18389753 = 13792315) B13792315
theorem B5446439 : Blo 1613005 5446439 := bstep (se 1 (by rfl) ⟨4084829, by rfl⟩ : syracuseStep 5446439 = 8169659) B8169659
theorem B3447593 : Blo 1613005 3447593 := bstep (se 2 (by rfl) ⟨1292847, by rfl⟩ : syracuseStep 3447593 = 2585695) B2585695
theorem B12262265 : Blo 1613005 12262265 := bstep (se 2 (by rfl) ⟨4598349, by rfl⟩ : syracuseStep 12262265 = 9196699) B9196699
theorem B6126623 : Blo 1613005 6126623 := bstep (se 1 (by rfl) ⟨4594967, by rfl⟩ : syracuseStep 6126623 = 9189935) B9189935
theorem B4086895 : Blo 1613005 4086895 := bstep (se 1 (by rfl) ⟨3065171, by rfl⟩ : syracuseStep 4086895 = 6130343) B6130343
theorem B47824103 : Blo 1613005 47824103 := bstep (se 1 (by rfl) ⟨35868077, by rfl⟩ : syracuseStep 47824103 = 71736155) B71736155
theorem B1613051 : Blo 1613005 1613051 := bstep (se 1 (by rfl) ⟨1209788, by rfl⟩ : syracuseStep 1613051 = 2419577) B2419577
theorem B1613215 : Blo 1613005 1613215 := bstep (se 1 (by rfl) ⟨1209911, by rfl⟩ : syracuseStep 1613215 = 2419823) B2419823
theorem B1613279 : Blo 1613005 1613279 := bstep (se 1 (by rfl) ⟨1209959, by rfl⟩ : syracuseStep 1613279 = 2419919) B2419919
theorem B1613359 : Blo 1613005 1613359 := bstep (se 1 (by rfl) ⟨1210019, by rfl⟩ : syracuseStep 1613359 = 2420039) B2420039
theorem B33595073 : Blo 1613005 33595073 := bstep (se 2 (by rfl) ⟨12598152, by rfl⟩ : syracuseStep 33595073 = 25196305) B25196305
theorem B1613551 : Blo 1613005 1613551 := bstep (se 1 (by rfl) ⟨1210163, by rfl⟩ : syracuseStep 1613551 = 2420327) B2420327
theorem B1613807 : Blo 1613005 1613807 := bstep (se 1 (by rfl) ⟨1210355, by rfl⟩ : syracuseStep 1613807 = 2420711) B2420711
theorem B4595753 : Blo 1613005 4595753 := bstep (se 2 (by rfl) ⟨1723407, by rfl⟩ : syracuseStep 4595753 = 3446815) B3446815
theorem B2949203 : Blo 1613005 2949203 := bstep (se 1 (by rfl) ⟨2211902, by rfl⟩ : syracuseStep 2949203 = 4423805) B4423805
theorem B1613951 : Blo 1613005 1613951 := bstep (se 1 (by rfl) ⟨1210463, by rfl⟩ : syracuseStep 1613951 = 2420927) B2420927
theorem B1614183 : Blo 1613005 1614183 := bstep (se 1 (by rfl) ⟨1210637, by rfl⟩ : syracuseStep 1614183 = 2421275) B2421275
theorem B10346879 : Blo 1613005 10346879 := bstep (se 1 (by rfl) ⟨7760159, by rfl⟩ : syracuseStep 10346879 = 15520319) B15520319
theorem B3629483 : Blo 1613005 3629483 := bstep (se 1 (by rfl) ⟨2722112, by rfl⟩ : syracuseStep 3629483 = 5444225) B5444225
theorem B6128095 : Blo 1613005 6128095 := bstep (se 1 (by rfl) ⟨4596071, by rfl⟩ : syracuseStep 6128095 = 9192143) B9192143
theorem B1614303 : Blo 1613005 1614303 := bstep (se 1 (by rfl) ⟨1210727, by rfl⟩ : syracuseStep 1614303 = 2421455) B2421455
theorem B3629609 : Blo 1613005 3629609 := bstep (se 2 (by rfl) ⟨1361103, by rfl⟩ : syracuseStep 3629609 = 2722207) B2722207
theorem B1614383 : Blo 1613005 1614383 := bstep (se 1 (by rfl) ⟨1210787, by rfl⟩ : syracuseStep 1614383 = 2421575) B2421575
theorem B1614751 : Blo 1613005 1614751 := bstep (se 1 (by rfl) ⟨1211063, by rfl⟩ : syracuseStep 1614751 = 2422127) B2422127
theorem B68993957 : Blo 1613005 68993957 := bstep (se 4 (by rfl) ⟨6468183, by rfl⟩ : syracuseStep 68993957 = 12936367) B12936367
theorem B1614831 : Blo 1613005 1614831 := bstep (se 1 (by rfl) ⟨1211123, by rfl⟩ : syracuseStep 1614831 = 2422247) B2422247
theorem B10347517 : Blo 1613005 10347517 := bstep (se 3 (by rfl) ⟨1940159, by rfl⟩ : syracuseStep 10347517 = 3880319) B3880319
theorem B1614879 : Blo 1613005 1614879 := bstep (se 1 (by rfl) ⟨1211159, by rfl⟩ : syracuseStep 1614879 = 2422319) B2422319
theorem B1614951 : Blo 1613005 1614951 := bstep (se 1 (by rfl) ⟨1211213, by rfl⟩ : syracuseStep 1614951 = 2422427) B2422427
theorem B5817511 : Blo 1613005 5817511 := bstep (se 1 (by rfl) ⟨4363133, by rfl⟩ : syracuseStep 5817511 = 8726267) B8726267
theorem B5449193 : Blo 1613005 5449193 := bstep (se 2 (by rfl) ⟨2043447, by rfl⟩ : syracuseStep 5449193 = 4086895) B4086895
theorem B23905843 : Blo 1613005 23905843 := bstep (se 1 (by rfl) ⟨17929382, by rfl⟩ : syracuseStep 23905843 = 35858765) B35858765
theorem B34891397 : Blo 1613005 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B3630887 : Blo 1613005 3630887 := bstep (se 1 (by rfl) ⟨2723165, by rfl⟩ : syracuseStep 3630887 = 5446331) B5446331
theorem B3630959 : Blo 1613005 3630959 := bstep (se 1 (by rfl) ⟨2723219, by rfl⟩ : syracuseStep 3630959 = 5446439) B5446439
theorem B41347421 : Blo 1613005 41347421 := bstep (se 3 (by rfl) ⟨7752641, by rfl⟩ : syracuseStep 41347421 = 15505283) B15505283
theorem B3631823 : Blo 1613005 3631823 := bstep (se 1 (by rfl) ⟨2723867, by rfl⟩ : syracuseStep 3631823 = 5447735) B5447735
theorem B3822750611 : Blo 1613005 3822750611 := bstep (se 1 (by rfl) ⟨2867062958, by rfl⟩ : syracuseStep 3822750611 = 5734125917) B5734125917
theorem B9317281 : Blo 1613005 9317281 := bstep (se 2 (by rfl) ⟨3493980, by rfl⟩ : syracuseStep 9317281 = 6987961) B6987961
theorem B2042815 : Blo 1613005 2042815 := bstep (se 1 (by rfl) ⟨1532111, by rfl⟩ : syracuseStep 2042815 = 3064223) B3064223
theorem B2419775 : Blo 1613005 2419775 := bstep (se 1 (by rfl) ⟨1814831, by rfl⟩ : syracuseStep 2419775 = 3629663) B3629663
theorem B3632219 : Blo 1613005 3632219 := bstep (se 1 (by rfl) ⟨2724164, by rfl⟩ : syracuseStep 3632219 = 5448329) B5448329
theorem B2420009 : Blo 1613005 2420009 := bstep (se 2 (by rfl) ⟨907503, by rfl⟩ : syracuseStep 2420009 = 1815007) B1815007
theorem B2420015 : Blo 1613005 2420015 := bstep (se 1 (by rfl) ⟨1815011, by rfl⟩ : syracuseStep 2420015 = 3630023) B3630023
theorem B18378089 : Blo 1613005 18378089 := bstep (se 2 (by rfl) ⟨6891783, by rfl⟩ : syracuseStep 18378089 = 13783567) B13783567
theorem B9186767 : Blo 1613005 9186767 := bstep (se 1 (by rfl) ⟨6890075, by rfl⟩ : syracuseStep 9186767 = 13780151) B13780151
theorem B2420201 : Blo 1613005 2420201 := bstep (se 2 (by rfl) ⟨907575, by rfl⟩ : syracuseStep 2420201 = 1815151) B1815151
theorem B2420255 : Blo 1613005 2420255 := bstep (se 1 (by rfl) ⟨1815191, by rfl⟩ : syracuseStep 2420255 = 3630383) B3630383
theorem B2420345 : Blo 1613005 2420345 := bstep (se 2 (by rfl) ⟨907629, by rfl⟩ : syracuseStep 2420345 = 1815259) B1815259
theorem B2723449 : Blo 1613005 2723449 := bstep (se 2 (by rfl) ⟨1021293, by rfl⟩ : syracuseStep 2723449 = 2042587) B2042587
theorem B4083443 : Blo 1613005 4083443 := bstep (se 1 (by rfl) ⟨3062582, by rfl⟩ : syracuseStep 4083443 = 6125165) B6125165
theorem B4140809 : Blo 1613005 4140809 := bstep (se 2 (by rfl) ⟨1552803, by rfl⟩ : syracuseStep 4140809 = 3105607) B3105607
theorem B3632993 : Blo 1613005 3632993 := bstep (se 2 (by rfl) ⟨1362372, by rfl⟩ : syracuseStep 3632993 = 2724745) B2724745
theorem B4083655 : Blo 1613005 4083655 := bstep (se 1 (by rfl) ⟨3062741, by rfl⟩ : syracuseStep 4083655 = 6125483) B6125483
theorem B12259835 : Blo 1613005 12259835 := bstep (se 1 (by rfl) ⟨9194876, by rfl⟩ : syracuseStep 12259835 = 18389753) B18389753
theorem B2298395 : Blo 1613005 2298395 := bstep (se 1 (by rfl) ⟨1723796, by rfl⟩ : syracuseStep 2298395 = 3447593) B3447593
theorem B2421359 : Blo 1613005 2421359 := bstep (se 1 (by rfl) ⟨1816019, by rfl⟩ : syracuseStep 2421359 = 3632039) B3632039
theorem B4084415 : Blo 1613005 4084415 := bstep (se 1 (by rfl) ⟨3063311, by rfl⟩ : syracuseStep 4084415 = 6126623) B6126623
theorem B8172251 : Blo 1613005 8172251 := bstep (se 1 (by rfl) ⟨6129188, by rfl⟩ : syracuseStep 8172251 = 12258377) B12258377
theorem B251549023 : Blo 1613005 251549023 := bstep (se 1 (by rfl) ⟨188661767, by rfl⟩ : syracuseStep 251549023 = 377323535) B377323535
theorem B2299369 : Blo 1613005 2299369 := bstep (se 2 (by rfl) ⟨862263, by rfl⟩ : syracuseStep 2299369 = 1724527) B1724527
theorem B2422271 : Blo 1613005 2422271 := bstep (se 1 (by rfl) ⟨1816703, by rfl⟩ : syracuseStep 2422271 = 3633407) B3633407
theorem B20690477 : Blo 1613005 20690477 := bstep (se 3 (by rfl) ⟨3879464, by rfl⟩ : syracuseStep 20690477 = 7758929) B7758929
theorem B4085417 : Blo 1613005 4085417 := bstep (se 2 (by rfl) ⟨1532031, by rfl⟩ : syracuseStep 4085417 = 3064063) B3064063
theorem B26187617 : Blo 1613005 26187617 := bstep (se 2 (by rfl) ⟨9820356, by rfl⟩ : syracuseStep 26187617 = 19640713) B19640713
theorem B12253031 : Blo 1613005 12253031 := bstep (se 1 (by rfl) ⟨9189773, by rfl⟩ : syracuseStep 12253031 = 18379547) B18379547
theorem B127530941 : Blo 1613005 127530941 := bstep (se 3 (by rfl) ⟨23912051, by rfl⟩ : syracuseStep 127530941 = 47824103) B47824103
theorem B8173547 : Blo 1613005 8173547 := bstep (se 1 (by rfl) ⟨6130160, by rfl⟩ : syracuseStep 8173547 = 12260321) B12260321
theorem B9312367 : Blo 1613005 9312367 := bstep (se 1 (by rfl) ⟨6984275, by rfl⟩ : syracuseStep 9312367 = 13968551) B13968551
theorem B1939583 : Blo 1613005 1939583 := bstep (se 1 (by rfl) ⟨1454687, by rfl⟩ : syracuseStep 1939583 = 2909375) B2909375
theorem B8173871 : Blo 1613005 8173871 := bstep (se 1 (by rfl) ⟨6130403, by rfl⟩ : syracuseStep 8173871 = 12260807) B12260807
theorem B23583149 : Blo 1613005 23583149 := bstep (se 3 (by rfl) ⟨4421840, by rfl⟩ : syracuseStep 23583149 = 8843681) B8843681
theorem B6126151 : Blo 1613005 6126151 := bstep (se 1 (by rfl) ⟨4594613, by rfl⟩ : syracuseStep 6126151 = 9189227) B9189227
theorem B21240839 : Blo 1613005 21240839 := bstep (se 1 (by rfl) ⟨15930629, by rfl⟩ : syracuseStep 21240839 = 31861259) B31861259
theorem B18373715 : Blo 1613005 18373715 := bstep (se 1 (by rfl) ⟨13780286, by rfl⟩ : syracuseStep 18373715 = 27560573) B27560573
theorem B8174843 : Blo 1613005 8174843 := bstep (se 1 (by rfl) ⟨6131132, by rfl⟩ : syracuseStep 8174843 = 12262265) B12262265
theorem B3063433 : Blo 1613005 3063433 := bstep (se 2 (by rfl) ⟨1148787, by rfl⟩ : syracuseStep 3063433 = 2297575) B2297575
theorem B22396715 : Blo 1613005 22396715 := bstep (se 1 (by rfl) ⟨16797536, by rfl⟩ : syracuseStep 22396715 = 33595073) B33595073
theorem B1613631 : Blo 1613005 1613631 := bstep (se 1 (by rfl) ⟨1210223, by rfl⟩ : syracuseStep 1613631 = 2420447) B2420447
theorem B3063835 : Blo 1613005 3063835 := bstep (se 1 (by rfl) ⟨2297876, by rfl⟩ : syracuseStep 3063835 = 4595753) B4595753
theorem B1966135 : Blo 1613005 1966135 := bstep (se 1 (by rfl) ⟨1474601, by rfl⟩ : syracuseStep 1966135 = 2949203) B2949203
theorem B6897919 : Blo 1613005 6897919 := bstep (se 1 (by rfl) ⟨5173439, by rfl⟩ : syracuseStep 6897919 = 10346879) B10346879
theorem B1614239 : Blo 1613005 1614239 := bstep (se 1 (by rfl) ⟨1210679, by rfl⟩ : syracuseStep 1614239 = 2421359) B2421359
theorem B5448167 : Blo 1613005 5448167 := bstep (se 1 (by rfl) ⟨4086125, by rfl⟩ : syracuseStep 5448167 = 8172251) B8172251
theorem B8168201 : Blo 1613005 8168201 := bstep (se 2 (by rfl) ⟨3063075, by rfl⟩ : syracuseStep 8168201 = 6126151) B6126151
theorem B1614847 : Blo 1613005 1614847 := bstep (se 1 (by rfl) ⟨1211135, by rfl⟩ : syracuseStep 1614847 = 2422271) B2422271
theorem B17458411 : Blo 1613005 17458411 := bstep (se 1 (by rfl) ⟨13093808, by rfl⟩ : syracuseStep 17458411 = 26187617) B26187617
theorem B8168687 : Blo 1613005 8168687 := bstep (se 1 (by rfl) ⟨6126515, by rfl⟩ : syracuseStep 8168687 = 12253031) B12253031
theorem B5449031 : Blo 1613005 5449031 := bstep (se 1 (by rfl) ⟨4086773, by rfl⟩ : syracuseStep 5449031 = 8173547) B8173547
theorem B13796689 : Blo 1613005 13796689 := bstep (se 2 (by rfl) ⟨5173758, by rfl⟩ : syracuseStep 13796689 = 10347517) B10347517
theorem B6129053 : Blo 1613005 6129053 := bstep (se 3 (by rfl) ⟨1149197, by rfl⟩ : syracuseStep 6129053 = 2298395) B2298395
theorem B5449247 : Blo 1613005 5449247 := bstep (se 1 (by rfl) ⟨4086935, by rfl⟩ : syracuseStep 5449247 = 8173871) B8173871
theorem B15722099 : Blo 1613005 15722099 := bstep (se 1 (by rfl) ⟨11791574, by rfl⟩ : syracuseStep 15722099 = 23583149) B23583149
theorem B335398697 : Blo 1613005 335398697 := bstep (se 2 (by rfl) ⟨125774511, by rfl⟩ : syracuseStep 335398697 = 251549023) B251549023
theorem B2548500407 : Blo 1613005 2548500407 := bstep (se 1 (by rfl) ⟨1911375305, by rfl⟩ : syracuseStep 2548500407 = 3822750611) B3822750611
theorem B3065825 : Blo 1613005 3065825 := bstep (se 2 (by rfl) ⟨1149684, by rfl⟩ : syracuseStep 3065825 = 2299369) B2299369
theorem B12249143 : Blo 1613005 12249143 := bstep (se 1 (by rfl) ⟨9186857, by rfl⟩ : syracuseStep 12249143 = 18373715) B18373715
theorem B3631265 : Blo 1613005 3631265 := bstep (se 2 (by rfl) ⟨1361724, by rfl⟩ : syracuseStep 3631265 = 2723449) B2723449
theorem B5449895 : Blo 1613005 5449895 := bstep (se 1 (by rfl) ⟨4087421, by rfl⟩ : syracuseStep 5449895 = 8174843) B8174843
theorem B2722295 : Blo 1613005 2722295 := bstep (se 1 (by rfl) ⟨2041721, by rfl⟩ : syracuseStep 2722295 = 4083443) B4083443
theorem B56642237 : Blo 1613005 56642237 := bstep (se 3 (by rfl) ⟨10620419, by rfl⟩ : syracuseStep 56642237 = 21240839) B21240839
theorem B2419655 : Blo 1613005 2419655 := bstep (se 1 (by rfl) ⟨1814741, by rfl⟩ : syracuseStep 2419655 = 3629483) B3629483
theorem B5172221 : Blo 1613005 5172221 := bstep (se 3 (by rfl) ⟨969791, by rfl⟩ : syracuseStep 5172221 = 1939583) B1939583
theorem B2419739 : Blo 1613005 2419739 := bstep (se 1 (by rfl) ⟨1814804, by rfl⟩ : syracuseStep 2419739 = 3629609) B3629609
theorem B2722943 : Blo 1613005 2722943 := bstep (se 1 (by rfl) ⟨2042207, by rfl⟩ : syracuseStep 2722943 = 4084415) B4084415
theorem B8170793 : Blo 1613005 8170793 := bstep (se 2 (by rfl) ⟨3064047, by rfl⟩ : syracuseStep 8170793 = 6128095) B6128095
theorem B3632795 : Blo 1613005 3632795 := bstep (se 1 (by rfl) ⟨2724596, by rfl⟩ : syracuseStep 3632795 = 5449193) B5449193
theorem B23260931 : Blo 1613005 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B2723611 : Blo 1613005 2723611 := bstep (se 1 (by rfl) ⟨2042708, by rfl⟩ : syracuseStep 2723611 = 4085417) B4085417
theorem B2420591 : Blo 1613005 2420591 := bstep (se 1 (by rfl) ⟨1815443, by rfl⟩ : syracuseStep 2420591 = 3630887) B3630887
theorem B12423041 : Blo 1613005 12423041 := bstep (se 2 (by rfl) ⟨4658640, by rfl⟩ : syracuseStep 12423041 = 9317281) B9317281
theorem B2420639 : Blo 1613005 2420639 := bstep (se 1 (by rfl) ⟨1815479, by rfl⟩ : syracuseStep 2420639 = 3630959) B3630959
theorem B2723753 : Blo 1613005 2723753 := bstep (se 2 (by rfl) ⟨1021407, by rfl⟩ : syracuseStep 2723753 = 2042815) B2042815
theorem B2421215 : Blo 1613005 2421215 := bstep (se 1 (by rfl) ⟨1815911, by rfl⟩ : syracuseStep 2421215 = 3631823) B3631823
theorem B2421479 : Blo 1613005 2421479 := bstep (se 1 (by rfl) ⟨1816109, by rfl⟩ : syracuseStep 2421479 = 3632219) B3632219
theorem B4084577 : Blo 1613005 4084577 := bstep (se 2 (by rfl) ⟨1531716, by rfl⟩ : syracuseStep 4084577 = 3063433) B3063433
theorem B12252059 : Blo 1613005 12252059 := bstep (se 1 (by rfl) ⟨9189044, by rfl⟩ : syracuseStep 12252059 = 18378089) B18378089
theorem B6124511 : Blo 1613005 6124511 := bstep (se 1 (by rfl) ⟨4593383, by rfl⟩ : syracuseStep 6124511 = 9186767) B9186767
theorem B14931143 : Blo 1613005 14931143 := bstep (se 1 (by rfl) ⟨11198357, by rfl⟩ : syracuseStep 14931143 = 22396715) B22396715
theorem B2421995 : Blo 1613005 2421995 := bstep (se 1 (by rfl) ⟨1816496, by rfl⟩ : syracuseStep 2421995 = 3632993) B3632993
theorem B5444873 : Blo 1613005 5444873 := bstep (se 2 (by rfl) ⟨2041827, by rfl⟩ : syracuseStep 5444873 = 4083655) B4083655
theorem B12416489 : Blo 1613005 12416489 := bstep (se 2 (by rfl) ⟨4656183, by rfl⟩ : syracuseStep 12416489 = 9312367) B9312367
theorem B127497829 : Blo 1613005 127497829 := bstep (se 4 (by rfl) ⟨11952921, by rfl⟩ : syracuseStep 127497829 = 23905843) B23905843
theorem B8173223 : Blo 1613005 8173223 := bstep (se 1 (by rfl) ⟨6129917, by rfl⟩ : syracuseStep 8173223 = 12259835) B12259835
theorem B45995971 : Blo 1613005 45995971 := bstep (se 1 (by rfl) ⟨34496978, by rfl⟩ : syracuseStep 45995971 = 68993957) B68993957
theorem B13793651 : Blo 1613005 13793651 := bstep (se 1 (by rfl) ⟨10345238, by rfl⟩ : syracuseStep 13793651 = 20690477) B20690477
theorem B7756681 : Blo 1613005 7756681 := bstep (se 2 (by rfl) ⟨2908755, by rfl⟩ : syracuseStep 7756681 = 5817511) B5817511
theorem B27564947 : Blo 1613005 27564947 := bstep (se 1 (by rfl) ⟨20673710, by rfl⟩ : syracuseStep 27564947 = 41347421) B41347421
theorem B1613183 : Blo 1613005 1613183 := bstep (se 1 (by rfl) ⟨1209887, by rfl⟩ : syracuseStep 1613183 = 2419775) B2419775
theorem B1613339 : Blo 1613005 1613339 := bstep (se 1 (by rfl) ⟨1210004, by rfl⟩ : syracuseStep 1613339 = 2420009) B2420009
theorem B1613343 : Blo 1613005 1613343 := bstep (se 1 (by rfl) ⟨1210007, by rfl⟩ : syracuseStep 1613343 = 2420015) B2420015
theorem B1613467 : Blo 1613005 1613467 := bstep (se 1 (by rfl) ⟨1210100, by rfl⟩ : syracuseStep 1613467 = 2420201) B2420201
theorem B1613503 : Blo 1613005 1613503 := bstep (se 1 (by rfl) ⟨1210127, by rfl⟩ : syracuseStep 1613503 = 2420255) B2420255
theorem B1613563 : Blo 1613005 1613563 := bstep (se 1 (by rfl) ⟨1210172, by rfl⟩ : syracuseStep 1613563 = 2420345) B2420345
theorem B340082509 : Blo 1613005 340082509 := bstep (se 3 (by rfl) ⟨63765470, by rfl⟩ : syracuseStep 340082509 = 127530941) B127530941
theorem B2760539 : Blo 1613005 2760539 := bstep (se 1 (by rfl) ⟨2070404, by rfl⟩ : syracuseStep 2760539 = 4140809) B4140809
theorem B2621513 : Blo 1613005 2621513 := bstep (se 2 (by rfl) ⟨983067, by rfl⟩ : syracuseStep 2621513 = 1966135) B1966135
theorem B1614143 : Blo 1613005 1614143 := bstep (se 1 (by rfl) ⟨1210607, by rfl⟩ : syracuseStep 1614143 = 2421215) B2421215
theorem B1614319 : Blo 1613005 1614319 := bstep (se 1 (by rfl) ⟨1210739, by rfl⟩ : syracuseStep 1614319 = 2421479) B2421479
theorem B8168039 : Blo 1613005 8168039 := bstep (se 1 (by rfl) ⟨6126029, by rfl⟩ : syracuseStep 8168039 = 12252059) B12252059
theorem B9954095 : Blo 1613005 9954095 := bstep (se 1 (by rfl) ⟨7465571, by rfl⟩ : syracuseStep 9954095 = 14931143) B14931143
theorem B1614663 : Blo 1613005 1614663 := bstep (se 1 (by rfl) ⟨1210997, by rfl⟩ : syracuseStep 1614663 = 2421995) B2421995
theorem B3629915 : Blo 1613005 3629915 := bstep (se 1 (by rfl) ⟨2722436, by rfl⟩ : syracuseStep 3629915 = 5444873) B5444873
theorem B5448815 : Blo 1613005 5448815 := bstep (se 1 (by rfl) ⟨4086611, by rfl⟩ : syracuseStep 5448815 = 8173223) B8173223
theorem B18376631 : Blo 1613005 18376631 := bstep (se 1 (by rfl) ⟨13782473, by rfl⟩ : syracuseStep 18376631 = 27564947) B27564947
theorem B3631481 : Blo 1613005 3631481 := bstep (se 2 (by rfl) ⟨1361805, by rfl⟩ : syracuseStep 3631481 = 2723611) B2723611
theorem B61327961 : Blo 1613005 61327961 := bstep (se 2 (by rfl) ⟨22997985, by rfl⟩ : syracuseStep 61327961 = 45995971) B45995971
theorem B3632111 : Blo 1613005 3632111 := bstep (se 1 (by rfl) ⟨2724083, by rfl⟩ : syracuseStep 3632111 = 5448167) B5448167
theorem B2723051 : Blo 1613005 2723051 := bstep (se 1 (by rfl) ⟨2042288, by rfl⟩ : syracuseStep 2723051 = 4084577) B4084577
theorem B4083007 : Blo 1613005 4083007 := bstep (se 1 (by rfl) ⟨3062255, by rfl⟩ : syracuseStep 4083007 = 6124511) B6124511
theorem B3632687 : Blo 1613005 3632687 := bstep (se 1 (by rfl) ⟨2724515, by rfl⟩ : syracuseStep 3632687 = 5449031) B5449031
theorem B8277659 : Blo 1613005 8277659 := bstep (se 1 (by rfl) ⟨6208244, by rfl⟩ : syracuseStep 8277659 = 12416489) B12416489
theorem B3632831 : Blo 1613005 3632831 := bstep (se 1 (by rfl) ⟨2724623, by rfl⟩ : syracuseStep 3632831 = 5449247) B5449247
theorem B10481399 : Blo 1613005 10481399 := bstep (se 1 (by rfl) ⟨7861049, by rfl⟩ : syracuseStep 10481399 = 15722099) B15722099
theorem B10342241 : Blo 1613005 10342241 := bstep (se 2 (by rfl) ⟨3878340, by rfl⟩ : syracuseStep 10342241 = 7756681) B7756681
theorem B1699000271 : Blo 1613005 1699000271 := bstep (se 1 (by rfl) ⟨1274250203, by rfl⟩ : syracuseStep 1699000271 = 2548500407) B2548500407
theorem B2043883 : Blo 1613005 2043883 := bstep (se 1 (by rfl) ⟨1532912, by rfl⟩ : syracuseStep 2043883 = 3065825) B3065825
theorem B2420843 : Blo 1613005 2420843 := bstep (se 1 (by rfl) ⟨1815632, by rfl⟩ : syracuseStep 2420843 = 3631265) B3631265
theorem B3633263 : Blo 1613005 3633263 := bstep (se 1 (by rfl) ⟨2724947, by rfl⟩ : syracuseStep 3633263 = 5449895) B5449895
theorem B9195767 : Blo 1613005 9195767 := bstep (se 1 (by rfl) ⟨6896825, by rfl⟩ : syracuseStep 9195767 = 13793651) B13793651
theorem B23277881 : Blo 1613005 23277881 := bstep (se 2 (by rfl) ⟨8729205, by rfl⟩ : syracuseStep 23277881 = 17458411) B17458411
theorem B1814863 : Blo 1613005 1814863 := bstep (se 1 (by rfl) ⟨1361147, by rfl⟩ : syracuseStep 1814863 = 2722295) B2722295
theorem B18395585 : Blo 1613005 18395585 := bstep (se 2 (by rfl) ⟨6898344, by rfl⟩ : syracuseStep 18395585 = 13796689) B13796689
theorem B37761491 : Blo 1613005 37761491 := bstep (se 1 (by rfl) ⟨28321118, by rfl⟩ : syracuseStep 37761491 = 56642237) B56642237
theorem B1815295 : Blo 1613005 1815295 := bstep (se 1 (by rfl) ⟨1361471, by rfl⟩ : syracuseStep 1815295 = 2722943) B2722943
theorem B169997105 : Blo 1613005 169997105 := bstep (se 2 (by rfl) ⟨63748914, by rfl⟩ : syracuseStep 169997105 = 127497829) B127497829
theorem B7361437 : Blo 1613005 7361437 := bstep (se 3 (by rfl) ⟨1380269, by rfl⟩ : syracuseStep 7361437 = 2760539) B2760539
theorem B2421863 : Blo 1613005 2421863 := bstep (se 1 (by rfl) ⟨1816397, by rfl⟩ : syracuseStep 2421863 = 3632795) B3632795
theorem B1815835 : Blo 1613005 1815835 := bstep (se 1 (by rfl) ⟨1361876, by rfl⟩ : syracuseStep 1815835 = 2723753) B2723753
theorem B13792589 : Blo 1613005 13792589 := bstep (se 3 (by rfl) ⟨2586110, by rfl⟩ : syracuseStep 13792589 = 5172221) B5172221
theorem B4085113 : Blo 1613005 4085113 := bstep (se 2 (by rfl) ⟨1531917, by rfl⟩ : syracuseStep 4085113 = 3063835) B3063835
theorem B9197225 : Blo 1613005 9197225 := bstep (se 2 (by rfl) ⟨3448959, by rfl⟩ : syracuseStep 9197225 = 6897919) B6897919
theorem B5445467 : Blo 1613005 5445467 := bstep (se 1 (by rfl) ⟨4084100, by rfl⟩ : syracuseStep 5445467 = 8168201) B8168201
theorem B5445791 : Blo 1613005 5445791 := bstep (se 1 (by rfl) ⟨4084343, by rfl⟩ : syracuseStep 5445791 = 8168687) B8168687
theorem B4086035 : Blo 1613005 4086035 := bstep (se 1 (by rfl) ⟨3064526, by rfl⟩ : syracuseStep 4086035 = 6129053) B6129053
theorem B223599131 : Blo 1613005 223599131 := bstep (se 1 (by rfl) ⟨167699348, by rfl⟩ : syracuseStep 223599131 = 335398697) B335398697
theorem B8166095 : Blo 1613005 8166095 := bstep (se 1 (by rfl) ⟨6124571, by rfl⟩ : syracuseStep 8166095 = 12249143) B12249143
theorem B1613103 : Blo 1613005 1613103 := bstep (se 1 (by rfl) ⟨1209827, by rfl⟩ : syracuseStep 1613103 = 2419655) B2419655
theorem B1613159 : Blo 1613005 1613159 := bstep (se 1 (by rfl) ⟨1209869, by rfl⟩ : syracuseStep 1613159 = 2419739) B2419739
theorem B5447195 : Blo 1613005 5447195 := bstep (se 1 (by rfl) ⟨4085396, by rfl⟩ : syracuseStep 5447195 = 8170793) B8170793
theorem B453443345 : Blo 1613005 453443345 := bstep (se 2 (by rfl) ⟨170041254, by rfl⟩ : syracuseStep 453443345 = 340082509) B340082509
theorem B15507287 : Blo 1613005 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B1613727 : Blo 1613005 1613727 := bstep (se 1 (by rfl) ⟨1210295, by rfl⟩ : syracuseStep 1613727 = 2420591) B2420591
theorem B8282027 : Blo 1613005 8282027 := bstep (se 1 (by rfl) ⟨6211520, by rfl⟩ : syracuseStep 8282027 = 12423041) B12423041
theorem B1613759 : Blo 1613005 1613759 := bstep (se 1 (by rfl) ⟨1210319, by rfl⟩ : syracuseStep 1613759 = 2420639) B2420639
theorem B1613895 : Blo 1613005 1613895 := bstep (se 1 (by rfl) ⟨1210421, by rfl⟩ : syracuseStep 1613895 = 2420843) B2420843
theorem B12263723 : Blo 1613005 12263723 := bstep (se 1 (by rfl) ⟨9197792, by rfl⟩ : syracuseStep 12263723 = 18395585) B18395585
theorem B25174327 : Blo 1613005 25174327 := bstep (se 1 (by rfl) ⟨18880745, by rfl⟩ : syracuseStep 25174327 = 37761491) B37761491
theorem B106177013 : Blo 1613005 106177013 := bstep (se 5 (by rfl) ⟨4977047, by rfl⟩ : syracuseStep 106177013 = 9954095) B9954095
theorem B1614575 : Blo 1613005 1614575 := bstep (se 1 (by rfl) ⟨1210931, by rfl⟩ : syracuseStep 1614575 = 2421863) B2421863
theorem B9815249 : Blo 1613005 9815249 := bstep (se 2 (by rfl) ⟨3680718, by rfl⟩ : syracuseStep 9815249 = 7361437) B7361437
theorem B3630311 : Blo 1613005 3630311 := bstep (se 1 (by rfl) ⟨2722733, by rfl⟩ : syracuseStep 3630311 = 5445467) B5445467
theorem B3630527 : Blo 1613005 3630527 := bstep (se 1 (by rfl) ⟨2722895, by rfl⟩ : syracuseStep 3630527 = 5445791) B5445791
theorem B3631463 : Blo 1613005 3631463 := bstep (se 1 (by rfl) ⟨2723597, by rfl⟩ : syracuseStep 3631463 = 5447195) B5447195
theorem B302295563 : Blo 1613005 302295563 := bstep (se 1 (by rfl) ⟨226721672, by rfl⟩ : syracuseStep 302295563 = 453443345) B453443345
theorem B1747675 : Blo 1613005 1747675 := bstep (se 1 (by rfl) ⟨1310756, by rfl⟩ : syracuseStep 1747675 = 2621513) B2621513
theorem B6130511 : Blo 1613005 6130511 := bstep (se 1 (by rfl) ⟨4597883, by rfl⟩ : syracuseStep 6130511 = 9195767) B9195767
theorem B15518587 : Blo 1613005 15518587 := bstep (se 1 (by rfl) ⟨11638940, by rfl⟩ : syracuseStep 15518587 = 23277881) B23277881
theorem B2419817 : Blo 1613005 2419817 := bstep (se 2 (by rfl) ⟨907431, by rfl⟩ : syracuseStep 2419817 = 1814863) B1814863
theorem B113331403 : Blo 1613005 113331403 := bstep (se 1 (by rfl) ⟨84998552, by rfl⟩ : syracuseStep 113331403 = 169997105) B169997105
theorem B2419943 : Blo 1613005 2419943 := bstep (se 1 (by rfl) ⟨1814957, by rfl⟩ : syracuseStep 2419943 = 3629915) B3629915
theorem B3632543 : Blo 1613005 3632543 := bstep (se 1 (by rfl) ⟨2724407, by rfl⟩ : syracuseStep 3632543 = 5448815) B5448815
theorem B9195059 : Blo 1613005 9195059 := bstep (se 1 (by rfl) ⟨6896294, by rfl⟩ : syracuseStep 9195059 = 13792589) B13792589
theorem B2420393 : Blo 1613005 2420393 := bstep (se 2 (by rfl) ⟨907647, by rfl⟩ : syracuseStep 2420393 = 1815295) B1815295
theorem B6131483 : Blo 1613005 6131483 := bstep (se 1 (by rfl) ⟨4598612, by rfl⟩ : syracuseStep 6131483 = 9197225) B9197225
theorem B12251087 : Blo 1613005 12251087 := bstep (se 1 (by rfl) ⟨9188315, by rfl⟩ : syracuseStep 12251087 = 18376631) B18376631
theorem B2724023 : Blo 1613005 2724023 := bstep (se 1 (by rfl) ⟨2043017, by rfl⟩ : syracuseStep 2724023 = 4086035) B4086035
theorem B2420987 : Blo 1613005 2420987 := bstep (se 1 (by rfl) ⟨1815740, by rfl⟩ : syracuseStep 2420987 = 3631481) B3631481
theorem B149066087 : Blo 1613005 149066087 := bstep (se 1 (by rfl) ⟨111799565, by rfl⟩ : syracuseStep 149066087 = 223599131) B223599131
theorem B2421113 : Blo 1613005 2421113 := bstep (se 2 (by rfl) ⟨907917, by rfl⟩ : syracuseStep 2421113 = 1815835) B1815835
theorem B5444009 : Blo 1613005 5444009 := bstep (se 2 (by rfl) ⟨2041503, by rfl⟩ : syracuseStep 5444009 = 4083007) B4083007
theorem B5444063 : Blo 1613005 5444063 := bstep (se 1 (by rfl) ⟨4083047, by rfl⟩ : syracuseStep 5444063 = 8166095) B8166095
theorem B2421407 : Blo 1613005 2421407 := bstep (se 1 (by rfl) ⟨1816055, by rfl⟩ : syracuseStep 2421407 = 3632111) B3632111
theorem B1815367 : Blo 1613005 1815367 := bstep (se 1 (by rfl) ⟨1361525, by rfl⟩ : syracuseStep 1815367 = 2723051) B2723051
theorem B2421791 : Blo 1613005 2421791 := bstep (se 1 (by rfl) ⟨1816343, by rfl⟩ : syracuseStep 2421791 = 3632687) B3632687
theorem B5518439 : Blo 1613005 5518439 := bstep (se 1 (by rfl) ⟨4138829, by rfl⟩ : syracuseStep 5518439 = 8277659) B8277659
theorem B2421887 : Blo 1613005 2421887 := bstep (se 1 (by rfl) ⟨1816415, by rfl⟩ : syracuseStep 2421887 = 3632831) B3632831
theorem B6894827 : Blo 1613005 6894827 := bstep (se 1 (by rfl) ⟨5171120, by rfl⟩ : syracuseStep 6894827 = 10342241) B10342241
theorem B2725177 : Blo 1613005 2725177 := bstep (se 2 (by rfl) ⟨1021941, by rfl⟩ : syracuseStep 2725177 = 2043883) B2043883
theorem B2422175 : Blo 1613005 2422175 := bstep (se 1 (by rfl) ⟨1816631, by rfl⟩ : syracuseStep 2422175 = 3633263) B3633263
theorem B5445359 : Blo 1613005 5445359 := bstep (se 1 (by rfl) ⟨4084019, by rfl⟩ : syracuseStep 5445359 = 8168039) B8168039
theorem B40885307 : Blo 1613005 40885307 := bstep (se 1 (by rfl) ⟨30663980, by rfl⟩ : syracuseStep 40885307 = 61327961) B61327961
theorem B5446817 : Blo 1613005 5446817 := bstep (se 2 (by rfl) ⟨2042556, by rfl⟩ : syracuseStep 5446817 = 4085113) B4085113
theorem B22085405 : Blo 1613005 22085405 := bstep (se 3 (by rfl) ⟨4141013, by rfl⟩ : syracuseStep 22085405 = 8282027) B8282027
theorem B6987599 : Blo 1613005 6987599 := bstep (se 1 (by rfl) ⟨5240699, by rfl⟩ : syracuseStep 6987599 = 10481399) B10481399
theorem B10338191 : Blo 1613005 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B1132666847 : Blo 1613005 1132666847 := bstep (se 1 (by rfl) ⟨849500135, by rfl⟩ : syracuseStep 1132666847 = 1699000271) B1699000271
theorem B1613991 : Blo 1613005 1613991 := bstep (se 1 (by rfl) ⟨1210493, by rfl⟩ : syracuseStep 1613991 = 2420987) B2420987
theorem B8175815 : Blo 1613005 8175815 := bstep (se 1 (by rfl) ⟨6131861, by rfl⟩ : syracuseStep 8175815 = 12263723) B12263723
theorem B1614075 : Blo 1613005 1614075 := bstep (se 1 (by rfl) ⟨1210556, by rfl⟩ : syracuseStep 1614075 = 2421113) B2421113
theorem B3629339 : Blo 1613005 3629339 := bstep (se 1 (by rfl) ⟨2722004, by rfl⟩ : syracuseStep 3629339 = 5444009) B5444009
theorem B3629375 : Blo 1613005 3629375 := bstep (se 1 (by rfl) ⟨2722031, by rfl⟩ : syracuseStep 3629375 = 5444063) B5444063
theorem B1614271 : Blo 1613005 1614271 := bstep (se 1 (by rfl) ⟨1210703, by rfl⟩ : syracuseStep 1614271 = 2421407) B2421407
theorem B1614527 : Blo 1613005 1614527 := bstep (se 1 (by rfl) ⟨1210895, by rfl⟩ : syracuseStep 1614527 = 2421791) B2421791
theorem B3678959 : Blo 1613005 3678959 := bstep (se 1 (by rfl) ⟨2759219, by rfl⟩ : syracuseStep 3678959 = 5518439) B5518439
theorem B1614591 : Blo 1613005 1614591 := bstep (se 1 (by rfl) ⟨1210943, by rfl⟩ : syracuseStep 1614591 = 2421887) B2421887
theorem B4596551 : Blo 1613005 4596551 := bstep (se 1 (by rfl) ⟨3447413, by rfl⟩ : syracuseStep 4596551 = 6894827) B6894827
theorem B397509565 : Blo 1613005 397509565 := bstep (se 3 (by rfl) ⟨74533043, by rfl⟩ : syracuseStep 397509565 = 149066087) B149066087
theorem B1614783 : Blo 1613005 1614783 := bstep (se 1 (by rfl) ⟨1211087, by rfl⟩ : syracuseStep 1614783 = 2422175) B2422175
theorem B3630239 : Blo 1613005 3630239 := bstep (se 1 (by rfl) ⟨2722679, by rfl⟩ : syracuseStep 3630239 = 5445359) B5445359
theorem B27256871 : Blo 1613005 27256871 := bstep (se 1 (by rfl) ⟨20442653, by rfl⟩ : syracuseStep 27256871 = 40885307) B40885307
theorem B3631211 : Blo 1613005 3631211 := bstep (se 1 (by rfl) ⟨2723408, by rfl⟩ : syracuseStep 3631211 = 5446817) B5446817
theorem B6130039 : Blo 1613005 6130039 := bstep (se 1 (by rfl) ⟨4597529, by rfl⟩ : syracuseStep 6130039 = 9195059) B9195059
theorem B14723603 : Blo 1613005 14723603 := bstep (se 1 (by rfl) ⟨11042702, by rfl⟩ : syracuseStep 14723603 = 22085405) B22085405
theorem B6892127 : Blo 1613005 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B33565769 : Blo 1613005 33565769 := bstep (se 2 (by rfl) ⟨12587163, by rfl⟩ : syracuseStep 33565769 = 25174327) B25174327
theorem B2420207 : Blo 1613005 2420207 := bstep (se 1 (by rfl) ⟨1815155, by rfl⟩ : syracuseStep 2420207 = 3630311) B3630311
theorem B2420351 : Blo 1613005 2420351 := bstep (se 1 (by rfl) ⟨1815263, by rfl⟩ : syracuseStep 2420351 = 3630527) B3630527
theorem B2420489 : Blo 1613005 2420489 := bstep (se 2 (by rfl) ⟨907683, by rfl⟩ : syracuseStep 2420489 = 1815367) B1815367
theorem B2420975 : Blo 1613005 2420975 := bstep (se 1 (by rfl) ⟨1815731, by rfl⟩ : syracuseStep 2420975 = 3631463) B3631463
theorem B3633569 : Blo 1613005 3633569 := bstep (se 2 (by rfl) ⟨1362588, by rfl⟩ : syracuseStep 3633569 = 2725177) B2725177
theorem B2421695 : Blo 1613005 2421695 := bstep (se 1 (by rfl) ⟨1816271, by rfl⟩ : syracuseStep 2421695 = 3632543) B3632543
theorem B4658399 : Blo 1613005 4658399 := bstep (se 1 (by rfl) ⟨3493799, by rfl⟩ : syracuseStep 4658399 = 6987599) B6987599
theorem B755111231 : Blo 1613005 755111231 := bstep (se 1 (by rfl) ⟨566333423, by rfl⟩ : syracuseStep 755111231 = 1132666847) B1132666847
theorem B1816015 : Blo 1613005 1816015 := bstep (se 1 (by rfl) ⟨1362011, by rfl⟩ : syracuseStep 1816015 = 2724023) B2724023
theorem B70784675 : Blo 1613005 70784675 := bstep (se 1 (by rfl) ⟨53088506, by rfl⟩ : syracuseStep 70784675 = 106177013) B106177013
theorem B6543499 : Blo 1613005 6543499 := bstep (se 1 (by rfl) ⟨4907624, by rfl⟩ : syracuseStep 6543499 = 9815249) B9815249
theorem B9320933 : Blo 1613005 9320933 := bstep (se 4 (by rfl) ⟨873837, by rfl⟩ : syracuseStep 9320933 = 1747675) B1747675
theorem B20691449 : Blo 1613005 20691449 := bstep (se 2 (by rfl) ⟨7759293, by rfl⟩ : syracuseStep 20691449 = 15518587) B15518587
theorem B151108537 : Blo 1613005 151108537 := bstep (se 2 (by rfl) ⟨56665701, by rfl⟩ : syracuseStep 151108537 = 113331403) B113331403
theorem B201530375 : Blo 1613005 201530375 := bstep (se 1 (by rfl) ⟨151147781, by rfl⟩ : syracuseStep 201530375 = 302295563) B302295563
theorem B4087007 : Blo 1613005 4087007 := bstep (se 1 (by rfl) ⟨3065255, by rfl⟩ : syracuseStep 4087007 = 6130511) B6130511
theorem B1613211 : Blo 1613005 1613211 := bstep (se 1 (by rfl) ⟨1209908, by rfl⟩ : syracuseStep 1613211 = 2419817) B2419817
theorem B1613295 : Blo 1613005 1613295 := bstep (se 1 (by rfl) ⟨1209971, by rfl⟩ : syracuseStep 1613295 = 2419943) B2419943
theorem B1613595 : Blo 1613005 1613595 := bstep (se 1 (by rfl) ⟨1210196, by rfl⟩ : syracuseStep 1613595 = 2420393) B2420393
theorem B4087655 : Blo 1613005 4087655 := bstep (se 1 (by rfl) ⟨3065741, by rfl⟩ : syracuseStep 4087655 = 6131483) B6131483
theorem B8167391 : Blo 1613005 8167391 := bstep (se 1 (by rfl) ⟨6125543, by rfl⟩ : syracuseStep 8167391 = 12251087) B12251087
theorem B1613983 : Blo 1613005 1613983 := bstep (se 1 (by rfl) ⟨1210487, by rfl⟩ : syracuseStep 1613983 = 2420975) B2420975
theorem B8724665 : Blo 1613005 8724665 := bstep (se 2 (by rfl) ⟨3271749, by rfl⟩ : syracuseStep 8724665 = 6543499) B6543499
theorem B3064367 : Blo 1613005 3064367 := bstep (se 1 (by rfl) ⟨2298275, by rfl⟩ : syracuseStep 3064367 = 4596551) B4596551
theorem B1614463 : Blo 1613005 1614463 := bstep (se 1 (by rfl) ⟨1210847, by rfl⟩ : syracuseStep 1614463 = 2421695) B2421695
theorem B3105599 : Blo 1613005 3105599 := bstep (se 1 (by rfl) ⟨2329199, by rfl⟩ : syracuseStep 3105599 = 4658399) B4658399
theorem B503407487 : Blo 1613005 503407487 := bstep (se 1 (by rfl) ⟨377555615, by rfl⟩ : syracuseStep 503407487 = 755111231) B755111231
theorem B9815735 : Blo 1613005 9815735 := bstep (se 1 (by rfl) ⟨7361801, by rfl⟩ : syracuseStep 9815735 = 14723603) B14723603
theorem B5450543 : Blo 1613005 5450543 := bstep (se 1 (by rfl) ⟨4087907, by rfl⟩ : syracuseStep 5450543 = 8175815) B8175815
theorem B2419559 : Blo 1613005 2419559 := bstep (se 1 (by rfl) ⟨1814669, by rfl⟩ : syracuseStep 2419559 = 3629339) B3629339
theorem B2419583 : Blo 1613005 2419583 := bstep (se 1 (by rfl) ⟨1814687, by rfl⟩ : syracuseStep 2419583 = 3629375) B3629375
theorem B2420159 : Blo 1613005 2420159 := bstep (se 1 (by rfl) ⟨1815119, by rfl⟩ : syracuseStep 2420159 = 3630239) B3630239
theorem B47189783 : Blo 1613005 47189783 := bstep (se 1 (by rfl) ⟨35392337, by rfl⟩ : syracuseStep 47189783 = 70784675) B70784675
theorem B201478049 : Blo 1613005 201478049 := bstep (se 2 (by rfl) ⟨75554268, by rfl⟩ : syracuseStep 201478049 = 151108537) B151108537
theorem B2420807 : Blo 1613005 2420807 := bstep (se 1 (by rfl) ⟨1815605, by rfl⟩ : syracuseStep 2420807 = 3631211) B3631211
theorem B6213955 : Blo 1613005 6213955 := bstep (se 1 (by rfl) ⟨4660466, by rfl⟩ : syracuseStep 6213955 = 9320933) B9320933
theorem B2421353 : Blo 1613005 2421353 := bstep (se 2 (by rfl) ⟨908007, by rfl⟩ : syracuseStep 2421353 = 1816015) B1816015
theorem B9810557 : Blo 1613005 9810557 := bstep (se 3 (by rfl) ⟨1839479, by rfl⟩ : syracuseStep 9810557 = 3678959) B3678959
theorem B134353583 : Blo 1613005 134353583 := bstep (se 1 (by rfl) ⟨100765187, by rfl⟩ : syracuseStep 134353583 = 201530375) B201530375
theorem B22377179 : Blo 1613005 22377179 := bstep (se 1 (by rfl) ⟨16782884, by rfl⟩ : syracuseStep 22377179 = 33565769) B33565769
theorem B2724671 : Blo 1613005 2724671 := bstep (se 1 (by rfl) ⟨2043503, by rfl⟩ : syracuseStep 2724671 = 4087007) B4087007
theorem B2725103 : Blo 1613005 2725103 := bstep (se 1 (by rfl) ⟨2043827, by rfl⟩ : syracuseStep 2725103 = 4087655) B4087655
theorem B5444927 : Blo 1613005 5444927 := bstep (se 1 (by rfl) ⟨4083695, by rfl⟩ : syracuseStep 5444927 = 8167391) B8167391
theorem B72684989 : Blo 1613005 72684989 := bstep (se 3 (by rfl) ⟨13628435, by rfl⟩ : syracuseStep 72684989 = 27256871) B27256871
theorem B2422379 : Blo 1613005 2422379 := bstep (se 1 (by rfl) ⟨1816784, by rfl⟩ : syracuseStep 2422379 = 3633569) B3633569
theorem B8173385 : Blo 1613005 8173385 := bstep (se 2 (by rfl) ⟨3065019, by rfl⟩ : syracuseStep 8173385 = 6130039) B6130039
theorem B530012753 : Blo 1613005 530012753 := bstep (se 2 (by rfl) ⟨198754782, by rfl⟩ : syracuseStep 530012753 = 397509565) B397509565
theorem B13794299 : Blo 1613005 13794299 := bstep (se 1 (by rfl) ⟨10345724, by rfl⟩ : syracuseStep 13794299 = 20691449) B20691449
theorem B4594751 : Blo 1613005 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B1613471 : Blo 1613005 1613471 := bstep (se 1 (by rfl) ⟨1210103, by rfl⟩ : syracuseStep 1613471 = 2420207) B2420207
theorem B1613567 : Blo 1613005 1613567 := bstep (se 1 (by rfl) ⟨1210175, by rfl⟩ : syracuseStep 1613567 = 2420351) B2420351
theorem B1613659 : Blo 1613005 1613659 := bstep (se 1 (by rfl) ⟨1210244, by rfl⟩ : syracuseStep 1613659 = 2420489) B2420489
theorem B1613871 : Blo 1613005 1613871 := bstep (se 1 (by rfl) ⟨1210403, by rfl⟩ : syracuseStep 1613871 = 2420807) B2420807
theorem B5816443 : Blo 1613005 5816443 := bstep (se 1 (by rfl) ⟨4362332, by rfl⟩ : syracuseStep 5816443 = 8724665) B8724665
theorem B1614235 : Blo 1613005 1614235 := bstep (se 1 (by rfl) ⟨1210676, by rfl⟩ : syracuseStep 1614235 = 2421353) B2421353
theorem B3629951 : Blo 1613005 3629951 := bstep (se 1 (by rfl) ⟨2722463, by rfl⟩ : syracuseStep 3629951 = 5444927) B5444927
theorem B48456659 : Blo 1613005 48456659 := bstep (se 1 (by rfl) ⟨36342494, by rfl⟩ : syracuseStep 48456659 = 72684989) B72684989
theorem B1614919 : Blo 1613005 1614919 := bstep (se 1 (by rfl) ⟨1211189, by rfl⟩ : syracuseStep 1614919 = 2422379) B2422379
theorem B5448923 : Blo 1613005 5448923 := bstep (se 1 (by rfl) ⟨4086692, by rfl⟩ : syracuseStep 5448923 = 8173385) B8173385
theorem B59672477 : Blo 1613005 59672477 := bstep (se 3 (by rfl) ⟨11188589, by rfl⟩ : syracuseStep 59672477 = 22377179) B22377179
theorem B31459855 : Blo 1613005 31459855 := bstep (se 1 (by rfl) ⟨23594891, by rfl⟩ : syracuseStep 31459855 = 47189783) B47189783
theorem B134318699 : Blo 1613005 134318699 := bstep (se 1 (by rfl) ⟨100739024, by rfl⟩ : syracuseStep 134318699 = 201478049) B201478049
theorem B2042911 : Blo 1613005 2042911 := bstep (se 1 (by rfl) ⟨1532183, by rfl⟩ : syracuseStep 2042911 = 3064367) B3064367
theorem B6540371 : Blo 1613005 6540371 := bstep (se 1 (by rfl) ⟨4905278, by rfl⟩ : syracuseStep 6540371 = 9810557) B9810557
theorem B8285273 : Blo 1613005 8285273 := bstep (se 2 (by rfl) ⟨3106977, by rfl⟩ : syracuseStep 8285273 = 6213955) B6213955
theorem B335604991 : Blo 1613005 335604991 := bstep (se 1 (by rfl) ⟨251703743, by rfl⟩ : syracuseStep 335604991 = 503407487) B503407487
theorem B353341835 : Blo 1613005 353341835 := bstep (se 1 (by rfl) ⟨265006376, by rfl⟩ : syracuseStep 353341835 = 530012753) B530012753
theorem B3633695 : Blo 1613005 3633695 := bstep (se 1 (by rfl) ⟨2725271, by rfl⟩ : syracuseStep 3633695 = 5450543) B5450543
theorem B9196199 : Blo 1613005 9196199 := bstep (se 1 (by rfl) ⟨6897149, by rfl⟩ : syracuseStep 9196199 = 13794299) B13794299
theorem B89569055 : Blo 1613005 89569055 := bstep (se 1 (by rfl) ⟨67176791, by rfl⟩ : syracuseStep 89569055 = 134353583) B134353583
theorem B1816447 : Blo 1613005 1816447 := bstep (se 1 (by rfl) ⟨1362335, by rfl⟩ : syracuseStep 1816447 = 2724671) B2724671
theorem B1816735 : Blo 1613005 1816735 := bstep (se 1 (by rfl) ⟨1362551, by rfl⟩ : syracuseStep 1816735 = 2725103) B2725103
theorem B6543823 : Blo 1613005 6543823 := bstep (se 1 (by rfl) ⟨4907867, by rfl⟩ : syracuseStep 6543823 = 9815735) B9815735
theorem B1613039 : Blo 1613005 1613039 := bstep (se 1 (by rfl) ⟨1209779, by rfl⟩ : syracuseStep 1613039 = 2419559) B2419559
theorem B1613055 : Blo 1613005 1613055 := bstep (se 1 (by rfl) ⟨1209791, by rfl⟩ : syracuseStep 1613055 = 2419583) B2419583
theorem B3063167 : Blo 1613005 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B8281597 : Blo 1613005 8281597 := bstep (se 3 (by rfl) ⟨1552799, by rfl⟩ : syracuseStep 8281597 = 3105599) B3105599
theorem B1613439 : Blo 1613005 1613439 := bstep (se 1 (by rfl) ⟨1210079, by rfl⟩ : syracuseStep 1613439 = 2420159) B2420159
theorem B235561223 : Blo 1613005 235561223 := bstep (se 1 (by rfl) ⟨176670917, by rfl⟩ : syracuseStep 235561223 = 353341835) B353341835
theorem B8725097 : Blo 1613005 8725097 := bstep (se 2 (by rfl) ⟨3271911, by rfl⟩ : syracuseStep 8725097 = 6543823) B6543823
theorem B39781651 : Blo 1613005 39781651 := bstep (se 1 (by rfl) ⟨29836238, by rfl⟩ : syracuseStep 39781651 = 59672477) B59672477
theorem B447473321 : Blo 1613005 447473321 := bstep (se 2 (by rfl) ⟨167802495, by rfl⟩ : syracuseStep 447473321 = 335604991) B335604991
theorem B4360247 : Blo 1613005 4360247 := bstep (se 1 (by rfl) ⟨3270185, by rfl⟩ : syracuseStep 4360247 = 6540371) B6540371
theorem B5523515 : Blo 1613005 5523515 := bstep (se 1 (by rfl) ⟨4142636, by rfl⟩ : syracuseStep 5523515 = 8285273) B8285273
theorem B2042111 : Blo 1613005 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B6130799 : Blo 1613005 6130799 := bstep (se 1 (by rfl) ⟨4598099, by rfl⟩ : syracuseStep 6130799 = 9196199) B9196199
theorem B2419967 : Blo 1613005 2419967 := bstep (se 1 (by rfl) ⟨1814975, by rfl⟩ : syracuseStep 2419967 = 3629951) B3629951
theorem B32304439 : Blo 1613005 32304439 := bstep (se 1 (by rfl) ⟨24228329, by rfl⟩ : syracuseStep 32304439 = 48456659) B48456659
theorem B41946473 : Blo 1613005 41946473 := bstep (se 2 (by rfl) ⟨15729927, by rfl⟩ : syracuseStep 41946473 = 31459855) B31459855
theorem B3632615 : Blo 1613005 3632615 := bstep (se 1 (by rfl) ⟨2724461, by rfl⟩ : syracuseStep 3632615 = 5448923) B5448923
theorem B2723881 : Blo 1613005 2723881 := bstep (se 2 (by rfl) ⟨1021455, by rfl⟩ : syracuseStep 2723881 = 2042911) B2042911
theorem B238850813 : Blo 1613005 238850813 := bstep (se 3 (by rfl) ⟨44784527, by rfl⟩ : syracuseStep 238850813 = 89569055) B89569055
theorem B2421929 : Blo 1613005 2421929 := bstep (se 2 (by rfl) ⟨908223, by rfl⟩ : syracuseStep 2421929 = 1816447) B1816447
theorem B7755257 : Blo 1613005 7755257 := bstep (se 2 (by rfl) ⟨2908221, by rfl⟩ : syracuseStep 7755257 = 5816443) B5816443
theorem B2422313 : Blo 1613005 2422313 := bstep (se 2 (by rfl) ⟨908367, by rfl⟩ : syracuseStep 2422313 = 1816735) B1816735
theorem B2422463 : Blo 1613005 2422463 := bstep (se 1 (by rfl) ⟨1816847, by rfl⟩ : syracuseStep 2422463 = 3633695) B3633695
theorem B89545799 : Blo 1613005 89545799 := bstep (se 1 (by rfl) ⟨67159349, by rfl⟩ : syracuseStep 89545799 = 134318699) B134318699
theorem B11042129 : Blo 1613005 11042129 := bstep (se 2 (by rfl) ⟨4140798, by rfl⟩ : syracuseStep 11042129 = 8281597) B8281597
theorem B157040815 : Blo 1613005 157040815 := bstep (se 1 (by rfl) ⟨117780611, by rfl⟩ : syracuseStep 157040815 = 235561223) B235561223
theorem B1614619 : Blo 1613005 1614619 := bstep (se 1 (by rfl) ⟨1210964, by rfl⟩ : syracuseStep 1614619 = 2421929) B2421929
theorem B5170171 : Blo 1613005 5170171 := bstep (se 1 (by rfl) ⟨3877628, by rfl⟩ : syracuseStep 5170171 = 7755257) B7755257
theorem B1614875 : Blo 1613005 1614875 := bstep (se 1 (by rfl) ⟨1211156, by rfl⟩ : syracuseStep 1614875 = 2422313) B2422313
theorem B1614975 : Blo 1613005 1614975 := bstep (se 1 (by rfl) ⟨1211231, by rfl⟩ : syracuseStep 1614975 = 2422463) B2422463
theorem B23266925 : Blo 1613005 23266925 := bstep (se 3 (by rfl) ⟨4362548, by rfl⟩ : syracuseStep 23266925 = 8725097) B8725097
theorem B59697199 : Blo 1613005 59697199 := bstep (se 1 (by rfl) ⟨44772899, by rfl⟩ : syracuseStep 59697199 = 89545799) B89545799
theorem B3631841 : Blo 1613005 3631841 := bstep (se 2 (by rfl) ⟨1361940, by rfl⟩ : syracuseStep 3631841 = 2723881) B2723881
theorem B29445677 : Blo 1613005 29445677 := bstep (se 3 (by rfl) ⟨5521064, by rfl⟩ : syracuseStep 29445677 = 11042129) B11042129
theorem B298315547 : Blo 1613005 298315547 := bstep (se 1 (by rfl) ⟨223736660, by rfl⟩ : syracuseStep 298315547 = 447473321) B447473321
theorem B3682343 : Blo 1613005 3682343 := bstep (se 1 (by rfl) ⟨2761757, by rfl⟩ : syracuseStep 3682343 = 5523515) B5523515
theorem B172290341 : Blo 1613005 172290341 := bstep (se 4 (by rfl) ⟨16152219, by rfl⟩ : syracuseStep 172290341 = 32304439) B32304439
theorem B27964315 : Blo 1613005 27964315 := bstep (se 1 (by rfl) ⟨20973236, by rfl⟩ : syracuseStep 27964315 = 41946473) B41946473
theorem B2421743 : Blo 1613005 2421743 := bstep (se 1 (by rfl) ⟨1816307, by rfl⟩ : syracuseStep 2421743 = 3632615) B3632615
theorem B5445629 : Blo 1613005 5445629 := bstep (se 3 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 5445629 = 2042111) B2042111
theorem B2906831 : Blo 1613005 2906831 := bstep (se 1 (by rfl) ⟨2180123, by rfl⟩ : syracuseStep 2906831 = 4360247) B4360247
theorem B53042201 : Blo 1613005 53042201 := bstep (se 2 (by rfl) ⟨19890825, by rfl⟩ : syracuseStep 53042201 = 39781651) B39781651
theorem B636935501 : Blo 1613005 636935501 := bstep (se 3 (by rfl) ⟨119425406, by rfl⟩ : syracuseStep 636935501 = 238850813) B238850813
theorem B4087199 : Blo 1613005 4087199 := bstep (se 1 (by rfl) ⟨3065399, by rfl⟩ : syracuseStep 4087199 = 6130799) B6130799
theorem B1613311 : Blo 1613005 1613311 := bstep (se 1 (by rfl) ⟨1209983, by rfl⟩ : syracuseStep 1613311 = 2419967) B2419967
theorem B114860227 : Blo 1613005 114860227 := bstep (se 1 (by rfl) ⟨86145170, by rfl⟩ : syracuseStep 114860227 = 172290341) B172290341
theorem B209387753 : Blo 1613005 209387753 := bstep (se 2 (by rfl) ⟨78520407, by rfl⟩ : syracuseStep 209387753 = 157040815) B157040815
theorem B1614495 : Blo 1613005 1614495 := bstep (se 1 (by rfl) ⟨1210871, by rfl⟩ : syracuseStep 1614495 = 2421743) B2421743
theorem B3630419 : Blo 1613005 3630419 := bstep (se 1 (by rfl) ⟨2722814, by rfl⟩ : syracuseStep 3630419 = 5445629) B5445629
theorem B19630451 : Blo 1613005 19630451 := bstep (se 1 (by rfl) ⟨14722838, by rfl⟩ : syracuseStep 19630451 = 29445677) B29445677
theorem B79596265 : Blo 1613005 79596265 := bstep (se 2 (by rfl) ⟨29848599, by rfl⟩ : syracuseStep 79596265 = 59697199) B59697199
theorem B15511283 : Blo 1613005 15511283 := bstep (se 1 (by rfl) ⟨11633462, by rfl⟩ : syracuseStep 15511283 = 23266925) B23266925
theorem B37285753 : Blo 1613005 37285753 := bstep (se 2 (by rfl) ⟨13982157, by rfl⟩ : syracuseStep 37285753 = 27964315) B27964315
theorem B6893561 : Blo 1613005 6893561 := bstep (se 2 (by rfl) ⟨2585085, by rfl⟩ : syracuseStep 6893561 = 5170171) B5170171
theorem B1937887 : Blo 1613005 1937887 := bstep (se 1 (by rfl) ⟨1453415, by rfl⟩ : syracuseStep 1937887 = 2906831) B2906831
theorem B2421227 : Blo 1613005 2421227 := bstep (se 1 (by rfl) ⟨1815920, by rfl⟩ : syracuseStep 2421227 = 3631841) B3631841
theorem B35361467 : Blo 1613005 35361467 := bstep (se 1 (by rfl) ⟨26521100, by rfl⟩ : syracuseStep 35361467 = 53042201) B53042201
theorem B2724799 : Blo 1613005 2724799 := bstep (se 1 (by rfl) ⟨2043599, by rfl⟩ : syracuseStep 2724799 = 4087199) B4087199
theorem B2454895 : Blo 1613005 2454895 := bstep (se 1 (by rfl) ⟨1841171, by rfl⟩ : syracuseStep 2454895 = 3682343) B3682343
theorem B424623667 : Blo 1613005 424623667 := bstep (se 1 (by rfl) ⟨318467750, by rfl⟩ : syracuseStep 424623667 = 636935501) B636935501
theorem B198877031 : Blo 1613005 198877031 := bstep (se 1 (by rfl) ⟨149157773, by rfl⟩ : syracuseStep 198877031 = 298315547) B298315547
theorem B139591835 : Blo 1613005 139591835 := bstep (se 1 (by rfl) ⟨104693876, by rfl⟩ : syracuseStep 139591835 = 209387753) B209387753
theorem B1614151 : Blo 1613005 1614151 := bstep (se 1 (by rfl) ⟨1210613, by rfl⟩ : syracuseStep 1614151 = 2421227) B2421227
theorem B106128353 : Blo 1613005 106128353 := bstep (se 2 (by rfl) ⟨39798132, by rfl⟩ : syracuseStep 106128353 = 79596265) B79596265
theorem B10340855 : Blo 1613005 10340855 := bstep (se 1 (by rfl) ⟨7755641, by rfl⟩ : syracuseStep 10340855 = 15511283) B15511283
theorem B2420279 : Blo 1613005 2420279 := bstep (se 1 (by rfl) ⟨1815209, by rfl⟩ : syracuseStep 2420279 = 3630419) B3630419
theorem B3633065 : Blo 1613005 3633065 := bstep (se 2 (by rfl) ⟨1362399, by rfl⟩ : syracuseStep 3633065 = 2724799) B2724799
theorem B4595707 : Blo 1613005 4595707 := bstep (se 1 (by rfl) ⟨3446780, by rfl⟩ : syracuseStep 4595707 = 6893561) B6893561
theorem B13086967 : Blo 1613005 13086967 := bstep (se 1 (by rfl) ⟨9815225, by rfl⟩ : syracuseStep 13086967 = 19630451) B19630451
theorem B3273193 : Blo 1613005 3273193 := bstep (se 2 (by rfl) ⟨1227447, by rfl⟩ : syracuseStep 3273193 = 2454895) B2454895
theorem B49714337 : Blo 1613005 49714337 := bstep (se 2 (by rfl) ⟨18642876, by rfl⟩ : syracuseStep 49714337 = 37285753) B37285753
theorem B10335397 : Blo 1613005 10335397 := bstep (se 4 (by rfl) ⟨968943, by rfl⟩ : syracuseStep 10335397 = 1937887) B1937887
theorem B132584687 : Blo 1613005 132584687 := bstep (se 1 (by rfl) ⟨99438515, by rfl⟩ : syracuseStep 132584687 = 198877031) B198877031
theorem B153146969 : Blo 1613005 153146969 := bstep (se 2 (by rfl) ⟨57430113, by rfl⟩ : syracuseStep 153146969 = 114860227) B114860227
theorem B23574311 : Blo 1613005 23574311 := bstep (se 1 (by rfl) ⟨17680733, by rfl⟩ : syracuseStep 23574311 = 35361467) B35361467
theorem B566164889 : Blo 1613005 566164889 := bstep (se 2 (by rfl) ⟨212311833, by rfl⟩ : syracuseStep 566164889 = 424623667) B424623667
theorem B93061223 : Blo 1613005 93061223 := bstep (se 1 (by rfl) ⟨69795917, by rfl⟩ : syracuseStep 93061223 = 139591835) B139591835
theorem B17449289 : Blo 1613005 17449289 := bstep (se 2 (by rfl) ⟨6543483, by rfl⟩ : syracuseStep 17449289 = 13086967) B13086967
theorem B102097979 : Blo 1613005 102097979 := bstep (se 1 (by rfl) ⟨76573484, by rfl⟩ : syracuseStep 102097979 = 153146969) B153146969
theorem B13780529 : Blo 1613005 13780529 := bstep (se 2 (by rfl) ⟨5167698, by rfl⟩ : syracuseStep 13780529 = 10335397) B10335397
theorem B15716207 : Blo 1613005 15716207 := bstep (se 1 (by rfl) ⟨11787155, by rfl⟩ : syracuseStep 15716207 = 23574311) B23574311
theorem B6893903 : Blo 1613005 6893903 := bstep (se 1 (by rfl) ⟨5170427, by rfl⟩ : syracuseStep 6893903 = 10340855) B10340855
theorem B377443259 : Blo 1613005 377443259 := bstep (se 1 (by rfl) ⟨283082444, by rfl⟩ : syracuseStep 377443259 = 566164889) B566164889
theorem B2422043 : Blo 1613005 2422043 := bstep (se 1 (by rfl) ⟨1816532, by rfl⟩ : syracuseStep 2422043 = 3633065) B3633065
theorem B33142891 : Blo 1613005 33142891 := bstep (se 1 (by rfl) ⟨24857168, by rfl⟩ : syracuseStep 33142891 = 49714337) B49714337
theorem B88389791 : Blo 1613005 88389791 := bstep (se 1 (by rfl) ⟨66292343, by rfl⟩ : syracuseStep 88389791 = 132584687) B132584687
theorem B1613519 : Blo 1613005 1613519 := bstep (se 1 (by rfl) ⟨1210139, by rfl⟩ : syracuseStep 1613519 = 2420279) B2420279
theorem B17457029 : Blo 1613005 17457029 := bstep (se 4 (by rfl) ⟨1636596, by rfl⟩ : syracuseStep 17457029 = 3273193) B3273193
theorem B283008941 : Blo 1613005 283008941 := bstep (se 3 (by rfl) ⟨53064176, by rfl⟩ : syracuseStep 283008941 = 106128353) B106128353
theorem B6127609 : Blo 1613005 6127609 := bstep (se 2 (by rfl) ⟨2297853, by rfl⟩ : syracuseStep 6127609 = 4595707) B4595707
theorem B11632859 : Blo 1613005 11632859 := bstep (se 1 (by rfl) ⟨8724644, by rfl⟩ : syracuseStep 11632859 = 17449289) B17449289
theorem B4595935 : Blo 1613005 4595935 := bstep (se 1 (by rfl) ⟨3446951, by rfl⟩ : syracuseStep 4595935 = 6893903) B6893903
theorem B1614695 : Blo 1613005 1614695 := bstep (se 1 (by rfl) ⟨1211021, by rfl⟩ : syracuseStep 1614695 = 2422043) B2422043
theorem B58926527 : Blo 1613005 58926527 := bstep (se 1 (by rfl) ⟨44194895, by rfl⟩ : syracuseStep 58926527 = 88389791) B88389791
theorem B188672627 : Blo 1613005 188672627 := bstep (se 1 (by rfl) ⟨141504470, by rfl⟩ : syracuseStep 188672627 = 283008941) B283008941
theorem B8170145 : Blo 1613005 8170145 := bstep (se 2 (by rfl) ⟨3063804, by rfl⟩ : syracuseStep 8170145 = 6127609) B6127609
theorem B62040815 : Blo 1613005 62040815 := bstep (se 1 (by rfl) ⟨46530611, by rfl⟩ : syracuseStep 62040815 = 93061223) B93061223
theorem B44190521 : Blo 1613005 44190521 := bstep (se 2 (by rfl) ⟨16571445, by rfl⟩ : syracuseStep 44190521 = 33142891) B33142891
theorem B251628839 : Blo 1613005 251628839 := bstep (se 1 (by rfl) ⟨188721629, by rfl⟩ : syracuseStep 251628839 = 377443259) B377443259
theorem B9187019 : Blo 1613005 9187019 := bstep (se 1 (by rfl) ⟨6890264, by rfl⟩ : syracuseStep 9187019 = 13780529) B13780529
theorem B11638019 : Blo 1613005 11638019 := bstep (se 1 (by rfl) ⟨8728514, by rfl⟩ : syracuseStep 11638019 = 17457029) B17457029
theorem B68065319 : Blo 1613005 68065319 := bstep (se 1 (by rfl) ⟨51048989, by rfl⟩ : syracuseStep 68065319 = 102097979) B102097979
theorem B10477471 : Blo 1613005 10477471 := bstep (se 1 (by rfl) ⟨7858103, by rfl⟩ : syracuseStep 10477471 = 15716207) B15716207
theorem B6127913 : Blo 1613005 6127913 := bstep (se 2 (by rfl) ⟨2297967, by rfl⟩ : syracuseStep 6127913 = 4595935) B4595935
theorem B7758679 : Blo 1613005 7758679 := bstep (se 1 (by rfl) ⟨5819009, by rfl⟩ : syracuseStep 7758679 = 11638019) B11638019
theorem B125781751 : Blo 1613005 125781751 := bstep (se 1 (by rfl) ⟨94336313, by rfl⟩ : syracuseStep 125781751 = 188672627) B188672627
theorem B29460347 : Blo 1613005 29460347 := bstep (se 1 (by rfl) ⟨22095260, by rfl⟩ : syracuseStep 29460347 = 44190521) B44190521
theorem B13969961 : Blo 1613005 13969961 := bstep (se 2 (by rfl) ⟨5238735, by rfl⟩ : syracuseStep 13969961 = 10477471) B10477471
theorem B39284351 : Blo 1613005 39284351 := bstep (se 1 (by rfl) ⟨29463263, by rfl⟩ : syracuseStep 39284351 = 58926527) B58926527
theorem B167752559 : Blo 1613005 167752559 := bstep (se 1 (by rfl) ⟨125814419, by rfl⟩ : syracuseStep 167752559 = 251628839) B251628839
theorem B6124679 : Blo 1613005 6124679 := bstep (se 1 (by rfl) ⟨4593509, by rfl⟩ : syracuseStep 6124679 = 9187019) B9187019
theorem B181507517 : Blo 1613005 181507517 := bstep (se 3 (by rfl) ⟨34032659, by rfl⟩ : syracuseStep 181507517 = 68065319) B68065319
theorem B7755239 : Blo 1613005 7755239 := bstep (se 1 (by rfl) ⟨5816429, by rfl⟩ : syracuseStep 7755239 = 11632859) B11632859
theorem B5446763 : Blo 1613005 5446763 := bstep (se 1 (by rfl) ⟨4085072, by rfl⟩ : syracuseStep 5446763 = 8170145) B8170145
theorem B41360543 : Blo 1613005 41360543 := bstep (se 1 (by rfl) ⟨31020407, by rfl⟩ : syracuseStep 41360543 = 62040815) B62040815
theorem B121005011 : Blo 1613005 121005011 := bstep (se 1 (by rfl) ⟨90753758, by rfl⟩ : syracuseStep 121005011 = 181507517) B181507517
theorem B5170159 : Blo 1613005 5170159 := bstep (se 1 (by rfl) ⟨3877619, by rfl⟩ : syracuseStep 5170159 = 7755239) B7755239
theorem B3631175 : Blo 1613005 3631175 := bstep (se 1 (by rfl) ⟨2723381, by rfl⟩ : syracuseStep 3631175 = 5446763) B5446763
theorem B167709001 : Blo 1613005 167709001 := bstep (se 2 (by rfl) ⟨62890875, by rfl⟩ : syracuseStep 167709001 = 125781751) B125781751
theorem B4083119 : Blo 1613005 4083119 := bstep (se 1 (by rfl) ⟨3062339, by rfl⟩ : syracuseStep 4083119 = 6124679) B6124679
theorem B19640231 : Blo 1613005 19640231 := bstep (se 1 (by rfl) ⟨14730173, by rfl⟩ : syracuseStep 19640231 = 29460347) B29460347
theorem B4085275 : Blo 1613005 4085275 := bstep (se 1 (by rfl) ⟨3063956, by rfl⟩ : syracuseStep 4085275 = 6127913) B6127913
theorem B10344905 : Blo 1613005 10344905 := bstep (se 2 (by rfl) ⟨3879339, by rfl⟩ : syracuseStep 10344905 = 7758679) B7758679
theorem B9313307 : Blo 1613005 9313307 := bstep (se 1 (by rfl) ⟨6984980, by rfl⟩ : syracuseStep 9313307 = 13969961) B13969961
theorem B27573695 : Blo 1613005 27573695 := bstep (se 1 (by rfl) ⟨20680271, by rfl⟩ : syracuseStep 27573695 = 41360543) B41360543
theorem B447340157 : Blo 1613005 447340157 := bstep (se 3 (by rfl) ⟨83876279, by rfl⟩ : syracuseStep 447340157 = 167752559) B167752559
theorem B26189567 : Blo 1613005 26189567 := bstep (se 1 (by rfl) ⟨19642175, by rfl⟩ : syracuseStep 26189567 = 39284351) B39284351
theorem B2722079 : Blo 1613005 2722079 := bstep (se 1 (by rfl) ⟨2041559, by rfl⟩ : syracuseStep 2722079 = 4083119) B4083119
theorem B17459711 : Blo 1613005 17459711 := bstep (se 1 (by rfl) ⟨13094783, by rfl⟩ : syracuseStep 17459711 = 26189567) B26189567
theorem B13093487 : Blo 1613005 13093487 := bstep (se 1 (by rfl) ⟨9820115, by rfl⟩ : syracuseStep 13093487 = 19640231) B19640231
theorem B223612001 : Blo 1613005 223612001 := bstep (se 2 (by rfl) ⟨83854500, by rfl⟩ : syracuseStep 223612001 = 167709001) B167709001
theorem B80670007 : Blo 1613005 80670007 := bstep (se 1 (by rfl) ⟨60502505, by rfl⟩ : syracuseStep 80670007 = 121005011) B121005011
theorem B6893545 : Blo 1613005 6893545 := bstep (se 2 (by rfl) ⟨2585079, by rfl⟩ : syracuseStep 6893545 = 5170159) B5170159
theorem B2420783 : Blo 1613005 2420783 := bstep (se 1 (by rfl) ⟨1815587, by rfl⟩ : syracuseStep 2420783 = 3631175) B3631175
theorem B298226771 : Blo 1613005 298226771 := bstep (se 1 (by rfl) ⟨223670078, by rfl⟩ : syracuseStep 298226771 = 447340157) B447340157
theorem B6896603 : Blo 1613005 6896603 := bstep (se 1 (by rfl) ⟨5172452, by rfl⟩ : syracuseStep 6896603 = 10344905) B10344905
theorem B6208871 : Blo 1613005 6208871 := bstep (se 1 (by rfl) ⟨4656653, by rfl⟩ : syracuseStep 6208871 = 9313307) B9313307
theorem B5447033 : Blo 1613005 5447033 := bstep (se 2 (by rfl) ⟨2042637, by rfl⟩ : syracuseStep 5447033 = 4085275) B4085275
theorem B18382463 : Blo 1613005 18382463 := bstep (se 1 (by rfl) ⟨13786847, by rfl⟩ : syracuseStep 18382463 = 27573695) B27573695
theorem B1613855 : Blo 1613005 1613855 := bstep (se 1 (by rfl) ⟨1210391, by rfl⟩ : syracuseStep 1613855 = 2420783) B2420783
theorem B16556989 : Blo 1613005 16556989 := bstep (se 3 (by rfl) ⟨3104435, by rfl⟩ : syracuseStep 16556989 = 6208871) B6208871
theorem B4597735 : Blo 1613005 4597735 := bstep (se 1 (by rfl) ⟨3448301, by rfl⟩ : syracuseStep 4597735 = 6896603) B6896603
theorem B3631355 : Blo 1613005 3631355 := bstep (se 1 (by rfl) ⟨2723516, by rfl⟩ : syracuseStep 3631355 = 5447033) B5447033
theorem B1814719 : Blo 1613005 1814719 := bstep (se 1 (by rfl) ⟨1361039, by rfl⟩ : syracuseStep 1814719 = 2722079) B2722079
theorem B8728991 : Blo 1613005 8728991 := bstep (se 1 (by rfl) ⟨6546743, by rfl⟩ : syracuseStep 8728991 = 13093487) B13093487
theorem B149074667 : Blo 1613005 149074667 := bstep (se 1 (by rfl) ⟨111806000, by rfl⟩ : syracuseStep 149074667 = 223612001) B223612001
theorem B198817847 : Blo 1613005 198817847 := bstep (se 1 (by rfl) ⟨149113385, by rfl⟩ : syracuseStep 198817847 = 298226771) B298226771
theorem B11639807 : Blo 1613005 11639807 := bstep (se 1 (by rfl) ⟨8729855, by rfl⟩ : syracuseStep 11639807 = 17459711) B17459711
theorem B107560009 : Blo 1613005 107560009 := bstep (se 2 (by rfl) ⟨40335003, by rfl⟩ : syracuseStep 107560009 = 80670007) B80670007
theorem B12254975 : Blo 1613005 12254975 := bstep (se 1 (by rfl) ⟨9191231, by rfl⟩ : syracuseStep 12254975 = 18382463) B18382463
theorem B9191393 : Blo 1613005 9191393 := bstep (se 2 (by rfl) ⟨3446772, by rfl⟩ : syracuseStep 9191393 = 6893545) B6893545
theorem B7759871 : Blo 1613005 7759871 := bstep (se 1 (by rfl) ⟨5819903, by rfl⟩ : syracuseStep 7759871 = 11639807) B11639807
theorem B8169983 : Blo 1613005 8169983 := bstep (se 1 (by rfl) ⟨6127487, by rfl⟩ : syracuseStep 8169983 = 12254975) B12254975
theorem B6130313 : Blo 1613005 6130313 := bstep (se 2 (by rfl) ⟨2298867, by rfl⟩ : syracuseStep 6130313 = 4597735) B4597735
theorem B2419625 : Blo 1613005 2419625 := bstep (se 2 (by rfl) ⟨907359, by rfl⟩ : syracuseStep 2419625 = 1814719) B1814719
theorem B5819327 : Blo 1613005 5819327 := bstep (se 1 (by rfl) ⟨4364495, by rfl⟩ : syracuseStep 5819327 = 8728991) B8728991
theorem B143413345 : Blo 1613005 143413345 := bstep (se 2 (by rfl) ⟨53780004, by rfl⟩ : syracuseStep 143413345 = 107560009) B107560009
theorem B2420903 : Blo 1613005 2420903 := bstep (se 1 (by rfl) ⟨1815677, by rfl⟩ : syracuseStep 2420903 = 3631355) B3631355
theorem B99383111 : Blo 1613005 99383111 := bstep (se 1 (by rfl) ⟨74537333, by rfl⟩ : syracuseStep 99383111 = 149074667) B149074667
theorem B22075985 : Blo 1613005 22075985 := bstep (se 2 (by rfl) ⟨8278494, by rfl⟩ : syracuseStep 22075985 = 16556989) B16556989
theorem B132545231 : Blo 1613005 132545231 := bstep (se 1 (by rfl) ⟨99408923, by rfl⟩ : syracuseStep 132545231 = 198817847) B198817847
theorem B6127595 : Blo 1613005 6127595 := bstep (se 1 (by rfl) ⟨4595696, by rfl⟩ : syracuseStep 6127595 = 9191393) B9191393
theorem B1613935 : Blo 1613005 1613935 := bstep (se 1 (by rfl) ⟨1210451, by rfl⟩ : syracuseStep 1613935 = 2420903) B2420903
theorem B191217793 : Blo 1613005 191217793 := bstep (se 2 (by rfl) ⟨71706672, by rfl⟩ : syracuseStep 191217793 = 143413345) B143413345
theorem B5173247 : Blo 1613005 5173247 := bstep (se 1 (by rfl) ⟨3879935, by rfl⟩ : syracuseStep 5173247 = 7759871) B7759871
theorem B14717323 : Blo 1613005 14717323 := bstep (se 1 (by rfl) ⟨11037992, by rfl⟩ : syracuseStep 14717323 = 22075985) B22075985
theorem B88363487 : Blo 1613005 88363487 := bstep (se 1 (by rfl) ⟨66272615, by rfl⟩ : syracuseStep 88363487 = 132545231) B132545231
theorem B3879551 : Blo 1613005 3879551 := bstep (se 1 (by rfl) ⟨2909663, by rfl⟩ : syracuseStep 3879551 = 5819327) B5819327
theorem B4085063 : Blo 1613005 4085063 := bstep (se 1 (by rfl) ⟨3063797, by rfl⟩ : syracuseStep 4085063 = 6127595) B6127595
theorem B66255407 : Blo 1613005 66255407 := bstep (se 1 (by rfl) ⟨49691555, by rfl⟩ : syracuseStep 66255407 = 99383111) B99383111
theorem B5446655 : Blo 1613005 5446655 := bstep (se 1 (by rfl) ⟨4084991, by rfl⟩ : syracuseStep 5446655 = 8169983) B8169983
theorem B4086875 : Blo 1613005 4086875 := bstep (se 1 (by rfl) ⟨3065156, by rfl⟩ : syracuseStep 4086875 = 6130313) B6130313
theorem B1613083 : Blo 1613005 1613083 := bstep (se 1 (by rfl) ⟨1209812, by rfl⟩ : syracuseStep 1613083 = 2419625) B2419625
theorem B58908991 : Blo 1613005 58908991 := bstep (se 1 (by rfl) ⟨44181743, by rfl⟩ : syracuseStep 58908991 = 88363487) B88363487
theorem B3448831 : Blo 1613005 3448831 := bstep (se 1 (by rfl) ⟨2586623, by rfl⟩ : syracuseStep 3448831 = 5173247) B5173247
theorem B3631103 : Blo 1613005 3631103 := bstep (se 1 (by rfl) ⟨2723327, by rfl⟩ : syracuseStep 3631103 = 5446655) B5446655
theorem B19623097 : Blo 1613005 19623097 := bstep (se 2 (by rfl) ⟨7358661, by rfl⟩ : syracuseStep 19623097 = 14717323) B14717323
theorem B2723375 : Blo 1613005 2723375 := bstep (se 1 (by rfl) ⟨2042531, by rfl⟩ : syracuseStep 2723375 = 4085063) B4085063
theorem B2724583 : Blo 1613005 2724583 := bstep (se 1 (by rfl) ⟨2043437, by rfl⟩ : syracuseStep 2724583 = 4086875) B4086875
theorem B254957057 : Blo 1613005 254957057 := bstep (se 2 (by rfl) ⟨95608896, by rfl⟩ : syracuseStep 254957057 = 191217793) B191217793
theorem B2586367 : Blo 1613005 2586367 := bstep (se 1 (by rfl) ⟨1939775, by rfl⟩ : syracuseStep 2586367 = 3879551) B3879551
theorem B44170271 : Blo 1613005 44170271 := bstep (se 1 (by rfl) ⟨33127703, by rfl⟩ : syracuseStep 44170271 = 66255407) B66255407
theorem B78545321 : Blo 1613005 78545321 := bstep (se 2 (by rfl) ⟨29454495, by rfl⟩ : syracuseStep 78545321 = 58908991) B58908991
theorem B4598441 : Blo 1613005 4598441 := bstep (se 2 (by rfl) ⟨1724415, by rfl⟩ : syracuseStep 4598441 = 3448831) B3448831
theorem B3632777 : Blo 1613005 3632777 := bstep (se 2 (by rfl) ⟨1362291, by rfl⟩ : syracuseStep 3632777 = 2724583) B2724583
theorem B169971371 : Blo 1613005 169971371 := bstep (se 1 (by rfl) ⟨127478528, by rfl⟩ : syracuseStep 169971371 = 254957057) B254957057
theorem B2420735 : Blo 1613005 2420735 := bstep (se 1 (by rfl) ⟨1815551, by rfl⟩ : syracuseStep 2420735 = 3631103) B3631103
theorem B29446847 : Blo 1613005 29446847 := bstep (se 1 (by rfl) ⟨22085135, by rfl⟩ : syracuseStep 29446847 = 44170271) B44170271
theorem B1815583 : Blo 1613005 1815583 := bstep (se 1 (by rfl) ⟨1361687, by rfl⟩ : syracuseStep 1815583 = 2723375) B2723375
theorem B26164129 : Blo 1613005 26164129 := bstep (se 2 (by rfl) ⟨9811548, by rfl⟩ : syracuseStep 26164129 = 19623097) B19623097
theorem B3448489 : Blo 1613005 3448489 := bstep (se 2 (by rfl) ⟨1293183, by rfl⟩ : syracuseStep 3448489 = 2586367) B2586367
theorem B52363547 : Blo 1613005 52363547 := bstep (se 1 (by rfl) ⟨39272660, by rfl⟩ : syracuseStep 52363547 = 78545321) B78545321
theorem B3065627 : Blo 1613005 3065627 := bstep (se 1 (by rfl) ⟨2299220, by rfl⟩ : syracuseStep 3065627 = 4598441) B4598441
theorem B4597985 : Blo 1613005 4597985 := bstep (se 2 (by rfl) ⟨1724244, by rfl⟩ : syracuseStep 4597985 = 3448489) B3448489
theorem B113314247 : Blo 1613005 113314247 := bstep (se 1 (by rfl) ⟨84985685, by rfl⟩ : syracuseStep 113314247 = 169971371) B169971371
theorem B19631231 : Blo 1613005 19631231 := bstep (se 1 (by rfl) ⟨14723423, by rfl⟩ : syracuseStep 19631231 = 29446847) B29446847
theorem B34885505 : Blo 1613005 34885505 := bstep (se 2 (by rfl) ⟨13082064, by rfl⟩ : syracuseStep 34885505 = 26164129) B26164129
theorem B2420777 : Blo 1613005 2420777 := bstep (se 2 (by rfl) ⟨907791, by rfl⟩ : syracuseStep 2420777 = 1815583) B1815583
theorem B2421851 : Blo 1613005 2421851 := bstep (se 1 (by rfl) ⟨1816388, by rfl⟩ : syracuseStep 2421851 = 3632777) B3632777
theorem B1613823 : Blo 1613005 1613823 := bstep (se 1 (by rfl) ⟨1210367, by rfl⟩ : syracuseStep 1613823 = 2420735) B2420735
theorem B1613851 : Blo 1613005 1613851 := bstep (se 1 (by rfl) ⟨1210388, by rfl⟩ : syracuseStep 1613851 = 2420777) B2420777
theorem B1614567 : Blo 1613005 1614567 := bstep (se 1 (by rfl) ⟨1210925, by rfl⟩ : syracuseStep 1614567 = 2421851) B2421851
theorem B34909031 : Blo 1613005 34909031 := bstep (se 1 (by rfl) ⟨26181773, by rfl⟩ : syracuseStep 34909031 = 52363547) B52363547
theorem B75542831 : Blo 1613005 75542831 := bstep (se 1 (by rfl) ⟨56657123, by rfl⟩ : syracuseStep 75542831 = 113314247) B113314247
theorem B13087487 : Blo 1613005 13087487 := bstep (se 1 (by rfl) ⟨9815615, by rfl⟩ : syracuseStep 13087487 = 19631231) B19631231
theorem B12261293 : Blo 1613005 12261293 := bstep (se 3 (by rfl) ⟨2298992, by rfl⟩ : syracuseStep 12261293 = 4597985) B4597985
theorem B8175005 : Blo 1613005 8175005 := bstep (se 3 (by rfl) ⟨1532813, by rfl⟩ : syracuseStep 8175005 = 3065627) B3065627
theorem B23257003 : Blo 1613005 23257003 := bstep (se 1 (by rfl) ⟨17442752, by rfl⟩ : syracuseStep 23257003 = 34885505) B34885505
theorem B8724991 : Blo 1613005 8724991 := bstep (se 1 (by rfl) ⟨6543743, by rfl⟩ : syracuseStep 8724991 = 13087487) B13087487
theorem B5450003 : Blo 1613005 5450003 := bstep (se 1 (by rfl) ⟨4087502, by rfl⟩ : syracuseStep 5450003 = 8175005) B8175005
theorem B31009337 : Blo 1613005 31009337 := bstep (se 2 (by rfl) ⟨11628501, by rfl⟩ : syracuseStep 31009337 = 23257003) B23257003
theorem B50361887 : Blo 1613005 50361887 := bstep (se 1 (by rfl) ⟨37771415, by rfl⟩ : syracuseStep 50361887 = 75542831) B75542831
theorem B8174195 : Blo 1613005 8174195 := bstep (se 1 (by rfl) ⟨6130646, by rfl⟩ : syracuseStep 8174195 = 12261293) B12261293
theorem B23272687 : Blo 1613005 23272687 := bstep (se 1 (by rfl) ⟨17454515, by rfl⟩ : syracuseStep 23272687 = 34909031) B34909031
theorem B11633321 : Blo 1613005 11633321 := bstep (se 2 (by rfl) ⟨4362495, by rfl⟩ : syracuseStep 11633321 = 8724991) B8724991
theorem B5449463 : Blo 1613005 5449463 := bstep (se 1 (by rfl) ⟨4087097, by rfl⟩ : syracuseStep 5449463 = 8174195) B8174195
theorem B33574591 : Blo 1613005 33574591 := bstep (se 1 (by rfl) ⟨25180943, by rfl⟩ : syracuseStep 33574591 = 50361887) B50361887
theorem B3633335 : Blo 1613005 3633335 := bstep (se 1 (by rfl) ⟨2725001, by rfl⟩ : syracuseStep 3633335 = 5450003) B5450003
theorem B20672891 : Blo 1613005 20672891 := bstep (se 1 (by rfl) ⟨15504668, by rfl⟩ : syracuseStep 20672891 = 31009337) B31009337
theorem B31030249 : Blo 1613005 31030249 := bstep (se 2 (by rfl) ⟨11636343, by rfl⟩ : syracuseStep 31030249 = 23272687) B23272687
theorem B13781927 : Blo 1613005 13781927 := bstep (se 1 (by rfl) ⟨10336445, by rfl⟩ : syracuseStep 13781927 = 20672891) B20672891
theorem B3632975 : Blo 1613005 3632975 := bstep (se 1 (by rfl) ⟨2724731, by rfl⟩ : syracuseStep 3632975 = 5449463) B5449463
theorem B41373665 : Blo 1613005 41373665 := bstep (se 2 (by rfl) ⟨15515124, by rfl⟩ : syracuseStep 41373665 = 31030249) B31030249
theorem B44766121 : Blo 1613005 44766121 := bstep (se 2 (by rfl) ⟨16787295, by rfl⟩ : syracuseStep 44766121 = 33574591) B33574591
theorem B2422223 : Blo 1613005 2422223 := bstep (se 1 (by rfl) ⟨1816667, by rfl⟩ : syracuseStep 2422223 = 3633335) B3633335
theorem B7755547 : Blo 1613005 7755547 := bstep (se 1 (by rfl) ⟨5816660, by rfl⟩ : syracuseStep 7755547 = 11633321) B11633321
theorem B1614815 : Blo 1613005 1614815 := bstep (se 1 (by rfl) ⟨1211111, by rfl⟩ : syracuseStep 1614815 = 2422223) B2422223
theorem B59688161 : Blo 1613005 59688161 := bstep (se 2 (by rfl) ⟨22383060, by rfl⟩ : syracuseStep 59688161 = 44766121) B44766121
theorem B10340729 : Blo 1613005 10340729 := bstep (se 2 (by rfl) ⟨3877773, by rfl⟩ : syracuseStep 10340729 = 7755547) B7755547
theorem B9187951 : Blo 1613005 9187951 := bstep (se 1 (by rfl) ⟨6890963, by rfl⟩ : syracuseStep 9187951 = 13781927) B13781927
theorem B2421983 : Blo 1613005 2421983 := bstep (se 1 (by rfl) ⟨1816487, by rfl⟩ : syracuseStep 2421983 = 3632975) B3632975
theorem B27582443 : Blo 1613005 27582443 := bstep (se 1 (by rfl) ⟨20686832, by rfl⟩ : syracuseStep 27582443 = 41373665) B41373665
theorem B1614655 : Blo 1613005 1614655 := bstep (se 1 (by rfl) ⟨1210991, by rfl⟩ : syracuseStep 1614655 = 2421983) B2421983
theorem B12250601 : Blo 1613005 12250601 := bstep (se 2 (by rfl) ⟨4593975, by rfl⟩ : syracuseStep 12250601 = 9187951) B9187951
theorem B39792107 : Blo 1613005 39792107 := bstep (se 1 (by rfl) ⟨29844080, by rfl⟩ : syracuseStep 39792107 = 59688161) B59688161
theorem B6893819 : Blo 1613005 6893819 := bstep (se 1 (by rfl) ⟨5170364, by rfl⟩ : syracuseStep 6893819 = 10340729) B10340729
theorem B18388295 : Blo 1613005 18388295 := bstep (se 1 (by rfl) ⟨13791221, by rfl⟩ : syracuseStep 18388295 = 27582443) B27582443
theorem B4595879 : Blo 1613005 4595879 := bstep (se 1 (by rfl) ⟨3446909, by rfl⟩ : syracuseStep 4595879 = 6893819) B6893819
theorem B26528071 : Blo 1613005 26528071 := bstep (se 1 (by rfl) ⟨19896053, by rfl⟩ : syracuseStep 26528071 = 39792107) B39792107
theorem B12258863 : Blo 1613005 12258863 := bstep (se 1 (by rfl) ⟨9194147, by rfl⟩ : syracuseStep 12258863 = 18388295) B18388295
theorem B8167067 : Blo 1613005 8167067 := bstep (se 1 (by rfl) ⟨6125300, by rfl⟩ : syracuseStep 8167067 = 12250601) B12250601
theorem B3063919 : Blo 1613005 3063919 := bstep (se 1 (by rfl) ⟨2297939, by rfl⟩ : syracuseStep 3063919 = 4595879) B4595879
theorem B8172575 : Blo 1613005 8172575 := bstep (se 1 (by rfl) ⟨6129431, by rfl⟩ : syracuseStep 8172575 = 12258863) B12258863
theorem B5444711 : Blo 1613005 5444711 := bstep (se 1 (by rfl) ⟨4083533, by rfl⟩ : syracuseStep 5444711 = 8167067) B8167067
theorem B35370761 : Blo 1613005 35370761 := bstep (se 2 (by rfl) ⟨13264035, by rfl⟩ : syracuseStep 35370761 = 26528071) B26528071
theorem B5448383 : Blo 1613005 5448383 := bstep (se 1 (by rfl) ⟨4086287, by rfl⟩ : syracuseStep 5448383 = 8172575) B8172575
theorem B3629807 : Blo 1613005 3629807 := bstep (se 1 (by rfl) ⟨2722355, by rfl⟩ : syracuseStep 3629807 = 5444711) B5444711
theorem B4085225 : Blo 1613005 4085225 := bstep (se 2 (by rfl) ⟨1531959, by rfl⟩ : syracuseStep 4085225 = 3063919) B3063919
theorem B94322029 : Blo 1613005 94322029 := bstep (se 3 (by rfl) ⟨17685380, by rfl⟩ : syracuseStep 94322029 = 35370761) B35370761
theorem B3632255 : Blo 1613005 3632255 := bstep (se 1 (by rfl) ⟨2724191, by rfl⟩ : syracuseStep 3632255 = 5448383) B5448383
theorem B2419871 : Blo 1613005 2419871 := bstep (se 1 (by rfl) ⟨1814903, by rfl⟩ : syracuseStep 2419871 = 3629807) B3629807
theorem B2723483 : Blo 1613005 2723483 := bstep (se 1 (by rfl) ⟨2042612, by rfl⟩ : syracuseStep 2723483 = 4085225) B4085225
theorem B125762705 : Blo 1613005 125762705 := bstep (se 2 (by rfl) ⟨47161014, by rfl⟩ : syracuseStep 125762705 = 94322029) B94322029
theorem B2421503 : Blo 1613005 2421503 := bstep (se 1 (by rfl) ⟨1816127, by rfl⟩ : syracuseStep 2421503 = 3632255) B3632255
theorem B83841803 : Blo 1613005 83841803 := bstep (se 1 (by rfl) ⟨62881352, by rfl⟩ : syracuseStep 83841803 = 125762705) B125762705
theorem B1815655 : Blo 1613005 1815655 := bstep (se 1 (by rfl) ⟨1361741, by rfl⟩ : syracuseStep 1815655 = 2723483) B2723483
theorem B1613247 : Blo 1613005 1613247 := bstep (se 1 (by rfl) ⟨1209935, by rfl⟩ : syracuseStep 1613247 = 2419871) B2419871
theorem B1614335 : Blo 1613005 1614335 := bstep (se 1 (by rfl) ⟨1210751, by rfl⟩ : syracuseStep 1614335 = 2421503) B2421503
theorem B55894535 : Blo 1613005 55894535 := bstep (se 1 (by rfl) ⟨41920901, by rfl⟩ : syracuseStep 55894535 = 83841803) B83841803
theorem B2420873 : Blo 1613005 2420873 := bstep (se 2 (by rfl) ⟨907827, by rfl⟩ : syracuseStep 2420873 = 1815655) B1815655
theorem B1613915 : Blo 1613005 1613915 := bstep (se 1 (by rfl) ⟨1210436, by rfl⟩ : syracuseStep 1613915 = 2420873) B2420873
theorem B37263023 : Blo 1613005 37263023 := bstep (se 1 (by rfl) ⟨27947267, by rfl⟩ : syracuseStep 37263023 = 55894535) B55894535
theorem B24842015 : Blo 1613005 24842015 := bstep (se 1 (by rfl) ⟨18631511, by rfl⟩ : syracuseStep 24842015 = 37263023) B37263023
theorem B16561343 : Blo 1613005 16561343 := bstep (se 1 (by rfl) ⟨12421007, by rfl⟩ : syracuseStep 16561343 = 24842015) B24842015
theorem B11040895 : Blo 1613005 11040895 := bstep (se 1 (by rfl) ⟨8280671, by rfl⟩ : syracuseStep 11040895 = 16561343) B16561343
theorem B14721193 : Blo 1613005 14721193 := bstep (se 2 (by rfl) ⟨5520447, by rfl⟩ : syracuseStep 14721193 = 11040895) B11040895
theorem B19628257 : Blo 1613005 19628257 := bstep (se 2 (by rfl) ⟨7360596, by rfl⟩ : syracuseStep 19628257 = 14721193) B14721193
theorem B26171009 : Blo 1613005 26171009 := bstep (se 2 (by rfl) ⟨9814128, by rfl⟩ : syracuseStep 26171009 = 19628257) B19628257
theorem B17447339 : Blo 1613005 17447339 := bstep (se 1 (by rfl) ⟨13085504, by rfl⟩ : syracuseStep 17447339 = 26171009) B26171009
theorem B46526237 : Blo 1613005 46526237 := bstep (se 3 (by rfl) ⟨8723669, by rfl⟩ : syracuseStep 46526237 = 17447339) B17447339
theorem B31017491 : Blo 1613005 31017491 := bstep (se 1 (by rfl) ⟨23263118, by rfl⟩ : syracuseStep 31017491 = 46526237) B46526237
theorem B20678327 : Blo 1613005 20678327 := bstep (se 1 (by rfl) ⟨15508745, by rfl⟩ : syracuseStep 20678327 = 31017491) B31017491
theorem B13785551 : Blo 1613005 13785551 := bstep (se 1 (by rfl) ⟨10339163, by rfl⟩ : syracuseStep 13785551 = 20678327) B20678327
theorem B9190367 : Blo 1613005 9190367 := bstep (se 1 (by rfl) ⟨6892775, by rfl⟩ : syracuseStep 9190367 = 13785551) B13785551
theorem B6126911 : Blo 1613005 6126911 := bstep (se 1 (by rfl) ⟨4595183, by rfl⟩ : syracuseStep 6126911 = 9190367) B9190367
theorem B4084607 : Blo 1613005 4084607 := bstep (se 1 (by rfl) ⟨3063455, by rfl⟩ : syracuseStep 4084607 = 6126911) B6126911
theorem B2723071 : Blo 1613005 2723071 := bstep (se 1 (by rfl) ⟨2042303, by rfl⟩ : syracuseStep 2723071 = 4084607) B4084607
theorem B3630761 : Blo 1613005 3630761 := bstep (se 2 (by rfl) ⟨1361535, by rfl⟩ : syracuseStep 3630761 = 2723071) B2723071
theorem B2420507 : Blo 1613005 2420507 := bstep (se 1 (by rfl) ⟨1815380, by rfl⟩ : syracuseStep 2420507 = 3630761) B3630761
theorem B1613671 : Blo 1613005 1613671 := bstep (se 1 (by rfl) ⟨1210253, by rfl⟩ : syracuseStep 1613671 = 2420507) B2420507

theorem C0 (j : ℕ) (h1 : 403251 ≤ j) (h2 : j ≤ 403750) : Blo 1613005 (4 * j + 3) := by
  interval_cases j
  · exact B1613007
  · exact B1613011
  · exact B1613015
  · exact B1613019
  · exact B1613023
  · exact B1613027
  · exact B1613031
  · exact B1613035
  · exact B1613039
  · exact B1613043
  · exact B1613047
  · exact B1613051
  · exact B1613055
  · exact B1613059
  · exact B1613063
  · exact B1613067
  · exact B1613071
  · exact B1613075
  · exact B1613079
  · exact B1613083
  · exact B1613087
  · exact B1613091
  · exact B1613095
  · exact B1613099
  · exact B1613103
  · exact B1613107
  · exact B1613111
  · exact B1613115
  · exact B1613119
  · exact B1613123
  · exact B1613127
  · exact B1613131
  · exact B1613135
  · exact B1613139
  · exact B1613143
  · exact B1613147
  · exact B1613151
  · exact B1613155
  · exact B1613159
  · exact B1613163
  · exact B1613167
  · exact B1613171
  · exact B1613175
  · exact B1613179
  · exact B1613183
  · exact B1613187
  · exact B1613191
  · exact B1613195
  · exact B1613199
  · exact B1613203
  · exact B1613207
  · exact B1613211
  · exact B1613215
  · exact B1613219
  · exact B1613223
  · exact B1613227
  · exact B1613231
  · exact B1613235
  · exact B1613239
  · exact B1613243
  · exact B1613247
  · exact B1613251
  · exact B1613255
  · exact B1613259
  · exact B1613263
  · exact B1613267
  · exact B1613271
  · exact B1613275
  · exact B1613279
  · exact B1613283
  · exact B1613287
  · exact B1613291
  · exact B1613295
  · exact B1613299
  · exact B1613303
  · exact B1613307
  · exact B1613311
  · exact B1613315
  · exact B1613319
  · exact B1613323
  · exact B1613327
  · exact B1613331
  · exact B1613335
  · exact B1613339
  · exact B1613343
  · exact B1613347
  · exact B1613351
  · exact B1613355
  · exact B1613359
  · exact B1613363
  · exact B1613367
  · exact B1613371
  · exact B1613375
  · exact B1613379
  · exact B1613383
  · exact B1613387
  · exact B1613391
  · exact B1613395
  · exact B1613399
  · exact B1613403
  · exact B1613407
  · exact B1613411
  · exact B1613415
  · exact B1613419
  · exact B1613423
  · exact B1613427
  · exact B1613431
  · exact B1613435
  · exact B1613439
  · exact B1613443
  · exact B1613447
  · exact B1613451
  · exact B1613455
  · exact B1613459
  · exact B1613463
  · exact B1613467
  · exact B1613471
  · exact B1613475
  · exact B1613479
  · exact B1613483
  · exact B1613487
  · exact B1613491
  · exact B1613495
  · exact B1613499
  · exact B1613503
  · exact B1613507
  · exact B1613511
  · exact B1613515
  · exact B1613519
  · exact B1613523
  · exact B1613527
  · exact B1613531
  · exact B1613535
  · exact B1613539
  · exact B1613543
  · exact B1613547
  · exact B1613551
  · exact B1613555
  · exact B1613559
  · exact B1613563
  · exact B1613567
  · exact B1613571
  · exact B1613575
  · exact B1613579
  · exact B1613583
  · exact B1613587
  · exact B1613591
  · exact B1613595
  · exact B1613599
  · exact B1613603
  · exact B1613607
  · exact B1613611
  · exact B1613615
  · exact B1613619
  · exact B1613623
  · exact B1613627
  · exact B1613631
  · exact B1613635
  · exact B1613639
  · exact B1613643
  · exact B1613647
  · exact B1613651
  · exact B1613655
  · exact B1613659
  · exact B1613663
  · exact B1613667
  · exact B1613671
  · exact B1613675
  · exact B1613679
  · exact B1613683
  · exact B1613687
  · exact B1613691
  · exact B1613695
  · exact B1613699
  · exact B1613703
  · exact B1613707
  · exact B1613711
  · exact B1613715
  · exact B1613719
  · exact B1613723
  · exact B1613727
  · exact B1613731
  · exact B1613735
  · exact B1613739
  · exact B1613743
  · exact B1613747
  · exact B1613751
  · exact B1613755
  · exact B1613759
  · exact B1613763
  · exact B1613767
  · exact B1613771
  · exact B1613775
  · exact B1613779
  · exact B1613783
  · exact B1613787
  · exact B1613791
  · exact B1613795
  · exact B1613799
  · exact B1613803
  · exact B1613807
  · exact B1613811
  · exact B1613815
  · exact B1613819
  · exact B1613823
  · exact B1613827
  · exact B1613831
  · exact B1613835
  · exact B1613839
  · exact B1613843
  · exact B1613847
  · exact B1613851
  · exact B1613855
  · exact B1613859
  · exact B1613863
  · exact B1613867
  · exact B1613871
  · exact B1613875
  · exact B1613879
  · exact B1613883
  · exact B1613887
  · exact B1613891
  · exact B1613895
  · exact B1613899
  · exact B1613903
  · exact B1613907
  · exact B1613911
  · exact B1613915
  · exact B1613919
  · exact B1613923
  · exact B1613927
  · exact B1613931
  · exact B1613935
  · exact B1613939
  · exact B1613943
  · exact B1613947
  · exact B1613951
  · exact B1613955
  · exact B1613959
  · exact B1613963
  · exact B1613967
  · exact B1613971
  · exact B1613975
  · exact B1613979
  · exact B1613983
  · exact B1613987
  · exact B1613991
  · exact B1613995
  · exact B1613999
  · exact B1614003
  · exact B1614007
  · exact B1614011
  · exact B1614015
  · exact B1614019
  · exact B1614023
  · exact B1614027
  · exact B1614031
  · exact B1614035
  · exact B1614039
  · exact B1614043
  · exact B1614047
  · exact B1614051
  · exact B1614055
  · exact B1614059
  · exact B1614063
  · exact B1614067
  · exact B1614071
  · exact B1614075
  · exact B1614079
  · exact B1614083
  · exact B1614087
  · exact B1614091
  · exact B1614095
  · exact B1614099
  · exact B1614103
  · exact B1614107
  · exact B1614111
  · exact B1614115
  · exact B1614119
  · exact B1614123
  · exact B1614127
  · exact B1614131
  · exact B1614135
  · exact B1614139
  · exact B1614143
  · exact B1614147
  · exact B1614151
  · exact B1614155
  · exact B1614159
  · exact B1614163
  · exact B1614167
  · exact B1614171
  · exact B1614175
  · exact B1614179
  · exact B1614183
  · exact B1614187
  · exact B1614191
  · exact B1614195
  · exact B1614199
  · exact B1614203
  · exact B1614207
  · exact B1614211
  · exact B1614215
  · exact B1614219
  · exact B1614223
  · exact B1614227
  · exact B1614231
  · exact B1614235
  · exact B1614239
  · exact B1614243
  · exact B1614247
  · exact B1614251
  · exact B1614255
  · exact B1614259
  · exact B1614263
  · exact B1614267
  · exact B1614271
  · exact B1614275
  · exact B1614279
  · exact B1614283
  · exact B1614287
  · exact B1614291
  · exact B1614295
  · exact B1614299
  · exact B1614303
  · exact B1614307
  · exact B1614311
  · exact B1614315
  · exact B1614319
  · exact B1614323
  · exact B1614327
  · exact B1614331
  · exact B1614335
  · exact B1614339
  · exact B1614343
  · exact B1614347
  · exact B1614351
  · exact B1614355
  · exact B1614359
  · exact B1614363
  · exact B1614367
  · exact B1614371
  · exact B1614375
  · exact B1614379
  · exact B1614383
  · exact B1614387
  · exact B1614391
  · exact B1614395
  · exact B1614399
  · exact B1614403
  · exact B1614407
  · exact B1614411
  · exact B1614415
  · exact B1614419
  · exact B1614423
  · exact B1614427
  · exact B1614431
  · exact B1614435
  · exact B1614439
  · exact B1614443
  · exact B1614447
  · exact B1614451
  · exact B1614455
  · exact B1614459
  · exact B1614463
  · exact B1614467
  · exact B1614471
  · exact B1614475
  · exact B1614479
  · exact B1614483
  · exact B1614487
  · exact B1614491
  · exact B1614495
  · exact B1614499
  · exact B1614503
  · exact B1614507
  · exact B1614511
  · exact B1614515
  · exact B1614519
  · exact B1614523
  · exact B1614527
  · exact B1614531
  · exact B1614535
  · exact B1614539
  · exact B1614543
  · exact B1614547
  · exact B1614551
  · exact B1614555
  · exact B1614559
  · exact B1614563
  · exact B1614567
  · exact B1614571
  · exact B1614575
  · exact B1614579
  · exact B1614583
  · exact B1614587
  · exact B1614591
  · exact B1614595
  · exact B1614599
  · exact B1614603
  · exact B1614607
  · exact B1614611
  · exact B1614615
  · exact B1614619
  · exact B1614623
  · exact B1614627
  · exact B1614631
  · exact B1614635
  · exact B1614639
  · exact B1614643
  · exact B1614647
  · exact B1614651
  · exact B1614655
  · exact B1614659
  · exact B1614663
  · exact B1614667
  · exact B1614671
  · exact B1614675
  · exact B1614679
  · exact B1614683
  · exact B1614687
  · exact B1614691
  · exact B1614695
  · exact B1614699
  · exact B1614703
  · exact B1614707
  · exact B1614711
  · exact B1614715
  · exact B1614719
  · exact B1614723
  · exact B1614727
  · exact B1614731
  · exact B1614735
  · exact B1614739
  · exact B1614743
  · exact B1614747
  · exact B1614751
  · exact B1614755
  · exact B1614759
  · exact B1614763
  · exact B1614767
  · exact B1614771
  · exact B1614775
  · exact B1614779
  · exact B1614783
  · exact B1614787
  · exact B1614791
  · exact B1614795
  · exact B1614799
  · exact B1614803
  · exact B1614807
  · exact B1614811
  · exact B1614815
  · exact B1614819
  · exact B1614823
  · exact B1614827
  · exact B1614831
  · exact B1614835
  · exact B1614839
  · exact B1614843
  · exact B1614847
  · exact B1614851
  · exact B1614855
  · exact B1614859
  · exact B1614863
  · exact B1614867
  · exact B1614871
  · exact B1614875
  · exact B1614879
  · exact B1614883
  · exact B1614887
  · exact B1614891
  · exact B1614895
  · exact B1614899
  · exact B1614903
  · exact B1614907
  · exact B1614911
  · exact B1614915
  · exact B1614919
  · exact B1614923
  · exact B1614927
  · exact B1614931
  · exact B1614935
  · exact B1614939
  · exact B1614943
  · exact B1614947
  · exact B1614951
  · exact B1614955
  · exact B1614959
  · exact B1614963
  · exact B1614967
  · exact B1614971
  · exact B1614975
  · exact B1614979
  · exact B1614983
  · exact B1614987
  · exact B1614991
  · exact B1614995
  · exact B1614999
  · exact B1615003

theorem solution (m : ℕ) (hlo : 1613005 ≤ m) (hhi : m ≤ 1615005) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 403251 ≤ j := by omega
    have hj2 : j ≤ 403750 := by omega
    have hb : Blo 1613005 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
