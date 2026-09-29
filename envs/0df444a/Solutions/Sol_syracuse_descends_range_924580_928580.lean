-- Prove2me | solution 1 for syracuse_descends_range_924580_928580
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:54.21604+00:00
-- url     : https://prove2.me/submissions/0f5297e5-706b-433e-b5c1-5ec4bb4df2d6

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


theorem B6029525 : Blo 924580 6029525 := bbase (se 7 (by rfl) ⟨70658, by rfl⟩ : syracuseStep 6029525 = 141317) (by norm_num)
theorem B4456741 : Blo 924580 4456741 := bbase (se 4 (by rfl) ⟨417819, by rfl⟩ : syracuseStep 4456741 = 835639) (by norm_num)
theorem B3965237 : Blo 924580 3965237 := bbase (se 5 (by rfl) ⟨185870, by rfl⟩ : syracuseStep 3965237 = 371741) (by norm_num)
theorem B1114445 : Blo 924580 1114445 := bbase (se 3 (by rfl) ⟨208958, by rfl⟩ : syracuseStep 1114445 = 417917) (by norm_num)
theorem B1671653 : Blo 924580 1671653 := bbase (se 4 (by rfl) ⟨156717, by rfl⟩ : syracuseStep 1671653 = 313435) (by norm_num)
theorem B3572437 : Blo 924580 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B1671941 : Blo 924580 1671941 := bbase (se 4 (by rfl) ⟨156744, by rfl⟩ : syracuseStep 1671941 = 313489) (by norm_num)
theorem B1672013 : Blo 924580 1672013 := bbase (se 3 (by rfl) ⟨313502, by rfl⟩ : syracuseStep 1672013 = 627005) (by norm_num)
theorem B3343189 : Blo 924580 3343189 := bbase (se 9 (by rfl) ⟨9794, by rfl⟩ : syracuseStep 3343189 = 19589) (by norm_num)
theorem B1606541 : Blo 924580 1606541 := bbase (se 3 (by rfl) ⟨301226, by rfl⟩ : syracuseStep 1606541 = 602453) (by norm_num)
theorem B4686821 : Blo 924580 4686821 := bbase (se 4 (by rfl) ⟨439389, by rfl⟩ : syracuseStep 4686821 = 878779) (by norm_num)
theorem B1115137 : Blo 924580 1115137 := bbase (se 2 (by rfl) ⟨418176, by rfl⟩ : syracuseStep 1115137 = 836353) (by norm_num)
theorem B1115353 : Blo 924580 1115353 := bbase (se 2 (by rfl) ⟨418257, by rfl⟩ : syracuseStep 1115353 = 836515) (by norm_num)
theorem B4752901 : Blo 924580 4752901 := bbase (se 4 (by rfl) ⟨445584, by rfl⟩ : syracuseStep 4752901 = 891169) (by norm_num)
theorem B2229869 : Blo 924580 2229869 := bbase (se 3 (by rfl) ⟨418100, by rfl⟩ : syracuseStep 2229869 = 836201) (by norm_num)
theorem B4688117 : Blo 924580 4688117 := bbase (se 5 (by rfl) ⟨219755, by rfl⟩ : syracuseStep 4688117 = 439511) (by norm_num)
theorem B1608317 : Blo 924580 1608317 := bbase (se 3 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 1608317 = 603119) (by norm_num)
theorem B11865365 : Blo 924580 11865365 := bbase (se 6 (by rfl) ⟨278094, by rfl⟩ : syracuseStep 11865365 = 556189) (by norm_num)
theorem B1445333 : Blo 924580 1445333 := bbase (se 7 (by rfl) ⟨16937, by rfl⟩ : syracuseStep 1445333 = 33875) (by norm_num)
theorem B1609205 : Blo 924580 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B4689413 : Blo 924580 4689413 := bbase (se 4 (by rfl) ⟨439632, by rfl⟩ : syracuseStep 4689413 = 879265) (by norm_num)
theorem B987337 : Blo 924580 987337 := bbase (se 2 (by rfl) ⟨370251, by rfl⟩ : syracuseStep 987337 = 740503) (by norm_num)
theorem B7049429 : Blo 924580 7049429 := bbase (se 7 (by rfl) ⟨82610, by rfl⟩ : syracuseStep 7049429 = 165221) (by norm_num)
theorem B3051893 : Blo 924580 3051893 := bbase (se 5 (by rfl) ⟨143057, by rfl⟩ : syracuseStep 3051893 = 286115) (by norm_num)
theorem B3510773 : Blo 924580 3510773 := bbase (se 5 (by rfl) ⟨164567, by rfl⟩ : syracuseStep 3510773 = 329135) (by norm_num)
theorem B987653 : Blo 924580 987653 := bbase (se 4 (by rfl) ⟨92592, by rfl⟩ : syracuseStep 987653 = 185185) (by norm_num)
theorem B5345909 : Blo 924580 5345909 := bbase (se 5 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 5345909 = 501179) (by norm_num)
theorem B19075733 : Blo 924580 19075733 := bbase (se 6 (by rfl) ⟨447087, by rfl⟩ : syracuseStep 19075733 = 894175) (by norm_num)
theorem B5640853 : Blo 924580 5640853 := bbase (se 6 (by rfl) ⟨132207, by rfl⟩ : syracuseStep 5640853 = 264415) (by norm_num)
theorem B4690709 : Blo 924580 4690709 := bbase (se 6 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 4690709 = 219877) (by norm_num)
theorem B988097 : Blo 924580 988097 := bbase (se 2 (by rfl) ⟨370536, by rfl⟩ : syracuseStep 988097 = 741073) (by norm_num)
theorem B988157 : Blo 924580 988157 := bbase (se 3 (by rfl) ⟨185279, by rfl⟩ : syracuseStep 988157 = 370559) (by norm_num)
theorem B5706773 : Blo 924580 5706773 := bbase (se 6 (by rfl) ⟨133752, by rfl⟩ : syracuseStep 5706773 = 267505) (by norm_num)
theorem B988285 : Blo 924580 988285 := bbase (se 3 (by rfl) ⟨185303, by rfl⟩ : syracuseStep 988285 = 370607) (by norm_num)
theorem B2823493 : Blo 924580 2823493 := bbase (se 4 (by rfl) ⟨264702, by rfl⟩ : syracuseStep 2823493 = 529405) (by norm_num)
theorem B988729 : Blo 924580 988729 := bbase (se 2 (by rfl) ⟨370773, by rfl⟩ : syracuseStep 988729 = 741547) (by norm_num)
theorem B3511957 : Blo 924580 3511957 := bbase (se 6 (by rfl) ⟨82311, by rfl⟩ : syracuseStep 3511957 = 164623) (by norm_num)
theorem B988849 : Blo 924580 988849 := bbase (se 2 (by rfl) ⟨370818, by rfl⟩ : syracuseStep 988849 = 741637) (by norm_num)
theorem B5936885 : Blo 924580 5936885 := bbase (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) (by norm_num)
theorem B1316677 : Blo 924580 1316677 := bbase (se 4 (by rfl) ⟨123438, by rfl⟩ : syracuseStep 1316677 = 246877) (by norm_num)
theorem B1054577 : Blo 924580 1054577 := bbase (se 2 (by rfl) ⟨395466, by rfl⟩ : syracuseStep 1054577 = 790933) (by norm_num)
theorem B989101 : Blo 924580 989101 := bbase (se 3 (by rfl) ⟨185456, by rfl⟩ : syracuseStep 989101 = 370913) (by norm_num)
theorem B989105 : Blo 924580 989105 := bbase (se 2 (by rfl) ⟨370914, by rfl⟩ : syracuseStep 989105 = 741829) (by norm_num)
theorem B3512261 : Blo 924580 3512261 := bbase (se 4 (by rfl) ⟨329274, by rfl⟩ : syracuseStep 3512261 = 658549) (by norm_num)
theorem B1316893 : Blo 924580 1316893 := bbase (se 3 (by rfl) ⟨246917, by rfl⟩ : syracuseStep 1316893 = 493835) (by norm_num)
theorem B4692005 : Blo 924580 4692005 := bbase (se 4 (by rfl) ⟨439875, by rfl⟩ : syracuseStep 4692005 = 879751) (by norm_num)
theorem B1317269 : Blo 924580 1317269 := bbase (se 6 (by rfl) ⟨30873, by rfl⟩ : syracuseStep 1317269 = 61747) (by norm_num)
theorem B1481141 : Blo 924580 1481141 := bbase (se 5 (by rfl) ⟨69428, by rfl⟩ : syracuseStep 1481141 = 138857) (by norm_num)
theorem B989669 : Blo 924580 989669 := bbase (se 4 (by rfl) ⟨92781, by rfl⟩ : syracuseStep 989669 = 185563) (by norm_num)
theorem B989857 : Blo 924580 989857 := bbase (se 2 (by rfl) ⟨371196, by rfl⟩ : syracuseStep 989857 = 742393) (by norm_num)
theorem B1874917 : Blo 924580 1874917 := bbase (se 4 (by rfl) ⟨175773, by rfl⟩ : syracuseStep 1874917 = 351547) (by norm_num)
theorem B1055873 : Blo 924580 1055873 := bbase (se 2 (by rfl) ⟨395952, by rfl⟩ : syracuseStep 1055873 = 791905) (by norm_num)
theorem B4693301 : Blo 924580 4693301 := bbase (se 5 (by rfl) ⟨219998, by rfl⟩ : syracuseStep 4693301 = 439997) (by norm_num)
theorem B1482133 : Blo 924580 1482133 := bbase (se 6 (by rfl) ⟨34737, by rfl⟩ : syracuseStep 1482133 = 69475) (by norm_num)
theorem B1875413 : Blo 924580 1875413 := bbase (se 7 (by rfl) ⟨21977, by rfl⟩ : syracuseStep 1875413 = 43955) (by norm_num)
theorem B990677 : Blo 924580 990677 := bbase (se 7 (by rfl) ⟨11609, by rfl⟩ : syracuseStep 990677 = 23219) (by norm_num)
theorem B14294677 : Blo 924580 14294677 := bbase (se 6 (by rfl) ⟨335031, by rfl⟩ : syracuseStep 14294677 = 670063) (by norm_num)
theorem B3120821 : Blo 924580 3120821 := bbase (se 5 (by rfl) ⟨146288, by rfl⟩ : syracuseStep 3120821 = 292577) (by norm_num)
theorem B1318693 : Blo 924580 1318693 := bbase (se 4 (by rfl) ⟨123627, by rfl⟩ : syracuseStep 1318693 = 247255) (by norm_num)
theorem B1482581 : Blo 924580 1482581 := bbase (se 9 (by rfl) ⟨4343, by rfl⟩ : syracuseStep 1482581 = 8687) (by norm_num)
theorem B5283701 : Blo 924580 5283701 := bbase (se 5 (by rfl) ⟨247673, by rfl⟩ : syracuseStep 5283701 = 495347) (by norm_num)
theorem B1187713 : Blo 924580 1187713 := bbase (se 2 (by rfl) ⟨445392, by rfl⟩ : syracuseStep 1187713 = 890785) (by norm_num)
theorem B991121 : Blo 924580 991121 := bbase (se 2 (by rfl) ⟨371670, by rfl⟩ : syracuseStep 991121 = 743341) (by norm_num)
theorem B3514373 : Blo 924580 3514373 := bbase (se 4 (by rfl) ⟨329472, by rfl⟩ : syracuseStep 3514373 = 658945) (by norm_num)
theorem B1253389 : Blo 924580 1253389 := bbase (se 3 (by rfl) ⟨235010, by rfl⟩ : syracuseStep 1253389 = 470021) (by norm_num)
theorem B1482781 : Blo 924580 1482781 := bbase (se 3 (by rfl) ⟨278021, by rfl⟩ : syracuseStep 1482781 = 556043) (by norm_num)
theorem B1187893 : Blo 924580 1187893 := bbase (se 5 (by rfl) ⟨55682, by rfl⟩ : syracuseStep 1187893 = 111365) (by norm_num)
theorem B1056821 : Blo 924580 1056821 := bbase (se 5 (by rfl) ⟨49538, by rfl⟩ : syracuseStep 1056821 = 99077) (by norm_num)
theorem B3121253 : Blo 924580 3121253 := bbase (se 4 (by rfl) ⟨292617, by rfl⟩ : syracuseStep 3121253 = 585235) (by norm_num)
theorem B991369 : Blo 924580 991369 := bbase (se 2 (by rfl) ⟨371763, by rfl⟩ : syracuseStep 991369 = 743527) (by norm_num)
theorem B10035413 : Blo 924580 10035413 := bbase (se 7 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 10035413 = 235205) (by norm_num)
theorem B1483037 : Blo 924580 1483037 := bbase (se 3 (by rfl) ⟨278069, by rfl⟩ : syracuseStep 1483037 = 556139) (by norm_num)
theorem B3514661 : Blo 924580 3514661 := bbase (se 4 (by rfl) ⟨329499, by rfl⟩ : syracuseStep 3514661 = 658999) (by norm_num)
theorem B1319285 : Blo 924580 1319285 := bbase (se 5 (by rfl) ⟨61841, by rfl⟩ : syracuseStep 1319285 = 123683) (by norm_num)
theorem B1319365 : Blo 924580 1319365 := bbase (se 4 (by rfl) ⟨123690, by rfl⟩ : syracuseStep 1319365 = 247381) (by norm_num)
theorem B3121685 : Blo 924580 3121685 := bbase (se 6 (by rfl) ⟨73164, by rfl⟩ : syracuseStep 3121685 = 146329) (by norm_num)
theorem B1319485 : Blo 924580 1319485 := bbase (se 3 (by rfl) ⟨247403, by rfl⟩ : syracuseStep 1319485 = 494807) (by norm_num)
theorem B4694597 : Blo 924580 4694597 := bbase (se 4 (by rfl) ⟨440118, by rfl⟩ : syracuseStep 4694597 = 880237) (by norm_num)
theorem B1876621 : Blo 924580 1876621 := bbase (se 3 (by rfl) ⟨351866, by rfl⟩ : syracuseStep 1876621 = 703733) (by norm_num)
theorem B1319581 : Blo 924580 1319581 := bbase (se 3 (by rfl) ⟨247421, by rfl⟩ : syracuseStep 1319581 = 494843) (by norm_num)
theorem B1254085 : Blo 924580 1254085 := bbase (se 4 (by rfl) ⟨117570, by rfl⟩ : syracuseStep 1254085 = 235141) (by norm_num)
theorem B1876717 : Blo 924580 1876717 := bbase (se 3 (by rfl) ⟨351884, by rfl⟩ : syracuseStep 1876717 = 703769) (by norm_num)
theorem B2499349 : Blo 924580 2499349 := bbase (se 6 (by rfl) ⟨58578, by rfl⟩ : syracuseStep 2499349 = 117157) (by norm_num)
theorem B3122117 : Blo 924580 3122117 := bbase (se 4 (by rfl) ⟨292698, by rfl⟩ : syracuseStep 3122117 = 585397) (by norm_num)
theorem B1057789 : Blo 924580 1057789 := bbase (se 3 (by rfl) ⟨198335, by rfl⟩ : syracuseStep 1057789 = 396671) (by norm_num)
theorem B5284885 : Blo 924580 5284885 := bbase (se 6 (by rfl) ⟨123864, by rfl⟩ : syracuseStep 5284885 = 247729) (by norm_num)
theorem B1975357 : Blo 924580 1975357 := bbase (se 3 (by rfl) ⟨370379, by rfl⟩ : syracuseStep 1975357 = 740759) (by norm_num)
theorem B1320077 : Blo 924580 1320077 := bbase (se 3 (by rfl) ⟨247514, by rfl⟩ : syracuseStep 1320077 = 495029) (by norm_num)
theorem B3122549 : Blo 924580 3122549 := bbase (se 5 (by rfl) ⟨146369, by rfl⟩ : syracuseStep 3122549 = 292739) (by norm_num)
theorem B1484165 : Blo 924580 1484165 := bbase (se 4 (by rfl) ⟨139140, by rfl⟩ : syracuseStep 1484165 = 278281) (by norm_num)
theorem B3515845 : Blo 924580 3515845 := bbase (se 4 (by rfl) ⟨329610, by rfl⟩ : syracuseStep 3515845 = 659221) (by norm_num)
theorem B1189417 : Blo 924580 1189417 := bbase (se 2 (by rfl) ⟨446031, by rfl⟩ : syracuseStep 1189417 = 892063) (by norm_num)
theorem B1975853 : Blo 924580 1975853 := bbase (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) (by norm_num)
theorem B2008733 : Blo 924580 2008733 := bbase (se 3 (by rfl) ⟨376637, by rfl⟩ : syracuseStep 2008733 = 753275) (by norm_num)
theorem B1320629 : Blo 924580 1320629 := bbase (se 5 (by rfl) ⟨61904, by rfl⟩ : syracuseStep 1320629 = 123809) (by norm_num)
theorem B24094421 : Blo 924580 24094421 := bbase (se 7 (by rfl) ⟨282356, by rfl⟩ : syracuseStep 24094421 = 564713) (by norm_num)
theorem B1189601 : Blo 924580 1189601 := bbase (se 2 (by rfl) ⟨446100, by rfl⟩ : syracuseStep 1189601 = 892201) (by norm_num)
theorem B3516149 : Blo 924580 3516149 := bbase (se 5 (by rfl) ⟨164819, by rfl⟩ : syracuseStep 3516149 = 329639) (by norm_num)
theorem B3122981 : Blo 924580 3122981 := bbase (se 4 (by rfl) ⟨292779, by rfl⟩ : syracuseStep 3122981 = 585559) (by norm_num)
theorem B4695893 : Blo 924580 4695893 := bbase (se 9 (by rfl) ⟨13757, by rfl⟩ : syracuseStep 4695893 = 27515) (by norm_num)
theorem B1484677 : Blo 924580 1484677 := bbase (se 4 (by rfl) ⟨139188, by rfl⟩ : syracuseStep 1484677 = 278377) (by norm_num)
theorem B4532117 : Blo 924580 4532117 := bbase (se 6 (by rfl) ⟨106221, by rfl⟩ : syracuseStep 4532117 = 212443) (by norm_num)
theorem B3123413 : Blo 924580 3123413 := bbase (se 7 (by rfl) ⟨36602, by rfl⟩ : syracuseStep 3123413 = 73205) (by norm_num)
theorem B3385637 : Blo 924580 3385637 := bbase (se 4 (by rfl) ⟨317403, by rfl⟩ : syracuseStep 3385637 = 634807) (by norm_num)
theorem B2500949 : Blo 924580 2500949 := bbase (se 10 (by rfl) ⟨3663, by rfl⟩ : syracuseStep 2500949 = 7327) (by norm_num)
theorem B1386893 : Blo 924580 1386893 := bbase (se 3 (by rfl) ⟨260042, by rfl⟩ : syracuseStep 1386893 = 520085) (by norm_num)
theorem B1386917 : Blo 924580 1386917 := bbase (se 4 (by rfl) ⟨130023, by rfl⟩ : syracuseStep 1386917 = 260047) (by norm_num)
theorem B1976741 : Blo 924580 1976741 := bbase (se 4 (by rfl) ⟨185319, by rfl⟩ : syracuseStep 1976741 = 370639) (by norm_num)
theorem B1485221 : Blo 924580 1485221 := bbase (se 4 (by rfl) ⟨139239, by rfl⟩ : syracuseStep 1485221 = 278479) (by norm_num)
theorem B1321381 : Blo 924580 1321381 := bbase (se 4 (by rfl) ⟨123879, by rfl⟩ : syracuseStep 1321381 = 247759) (by norm_num)
theorem B1386941 : Blo 924580 1386941 := bbase (se 3 (by rfl) ⟨260051, by rfl⟩ : syracuseStep 1386941 = 520103) (by norm_num)
theorem B1386965 : Blo 924580 1386965 := bbase (se 7 (by rfl) ⟨16253, by rfl⟩ : syracuseStep 1386965 = 32507) (by norm_num)
theorem B1386989 : Blo 924580 1386989 := bbase (se 3 (by rfl) ⟨260060, by rfl⟩ : syracuseStep 1386989 = 520121) (by norm_num)
theorem B1387013 : Blo 924580 1387013 := bbase (se 4 (by rfl) ⟨130032, by rfl⟩ : syracuseStep 1387013 = 260065) (by norm_num)
theorem B1190413 : Blo 924580 1190413 := bbase (se 3 (by rfl) ⟨223202, by rfl⟩ : syracuseStep 1190413 = 446405) (by norm_num)
theorem B1387037 : Blo 924580 1387037 := bbase (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) (by norm_num)
theorem B1976861 : Blo 924580 1976861 := bbase (se 3 (by rfl) ⟨370661, by rfl⟩ : syracuseStep 1976861 = 741323) (by norm_num)
theorem B1387061 : Blo 924580 1387061 := bbase (se 5 (by rfl) ⟨65018, by rfl⟩ : syracuseStep 1387061 = 130037) (by norm_num)
theorem B1387085 : Blo 924580 1387085 := bbase (se 3 (by rfl) ⟨260078, by rfl⟩ : syracuseStep 1387085 = 520157) (by norm_num)
theorem B1780309 : Blo 924580 1780309 := bbase (se 8 (by rfl) ⟨10431, by rfl⟩ : syracuseStep 1780309 = 20863) (by norm_num)
theorem B1387109 : Blo 924580 1387109 := bbase (se 4 (by rfl) ⟨130041, by rfl⟩ : syracuseStep 1387109 = 260083) (by norm_num)
theorem B1387133 : Blo 924580 1387133 := bbase (se 3 (by rfl) ⟨260087, by rfl⟩ : syracuseStep 1387133 = 520175) (by norm_num)
theorem B3123845 : Blo 924580 3123845 := bbase (se 4 (by rfl) ⟨292860, by rfl⟩ : syracuseStep 3123845 = 585721) (by norm_num)
theorem B1387157 : Blo 924580 1387157 := bbase (se 6 (by rfl) ⟨32511, by rfl⟩ : syracuseStep 1387157 = 65023) (by norm_num)
theorem B1387181 : Blo 924580 1387181 := bbase (se 3 (by rfl) ⟨260096, by rfl⟩ : syracuseStep 1387181 = 520193) (by norm_num)
theorem B1387205 : Blo 924580 1387205 := bbase (se 4 (by rfl) ⟨130050, by rfl⟩ : syracuseStep 1387205 = 260101) (by norm_num)
theorem B1387229 : Blo 924580 1387229 := bbase (se 3 (by rfl) ⟨260105, by rfl⟩ : syracuseStep 1387229 = 520211) (by norm_num)
theorem B1387253 : Blo 924580 1387253 := bbase (se 5 (by rfl) ⟨65027, by rfl⟩ : syracuseStep 1387253 = 130055) (by norm_num)
theorem B1387277 : Blo 924580 1387277 := bbase (se 3 (by rfl) ⟨260114, by rfl⟩ : syracuseStep 1387277 = 520229) (by norm_num)
theorem B1387301 : Blo 924580 1387301 := bbase (se 4 (by rfl) ⟨130059, by rfl⟩ : syracuseStep 1387301 = 260119) (by norm_num)
theorem B1387325 : Blo 924580 1387325 := bbase (se 3 (by rfl) ⟨260123, by rfl⟩ : syracuseStep 1387325 = 520247) (by norm_num)
theorem B1387349 : Blo 924580 1387349 := bbase (se 9 (by rfl) ⟨4064, by rfl⟩ : syracuseStep 1387349 = 8129) (by norm_num)
theorem B1387373 : Blo 924580 1387373 := bbase (se 3 (by rfl) ⟨260132, by rfl⟩ : syracuseStep 1387373 = 520265) (by norm_num)
theorem B1387397 : Blo 924580 1387397 := bbase (se 4 (by rfl) ⟨130068, by rfl⟩ : syracuseStep 1387397 = 260137) (by norm_num)
theorem B8924053 : Blo 924580 8924053 := bbase (se 6 (by rfl) ⟨209157, by rfl⟩ : syracuseStep 8924053 = 418315) (by norm_num)
theorem B1387421 : Blo 924580 1387421 := bbase (se 3 (by rfl) ⟨260141, by rfl⟩ : syracuseStep 1387421 = 520283) (by norm_num)
theorem B1387445 : Blo 924580 1387445 := bbase (se 5 (by rfl) ⟨65036, by rfl⟩ : syracuseStep 1387445 = 130073) (by norm_num)
theorem B1387469 : Blo 924580 1387469 := bbase (se 3 (by rfl) ⟨260150, by rfl⟩ : syracuseStep 1387469 = 520301) (by norm_num)
theorem B1485773 : Blo 924580 1485773 := bbase (se 3 (by rfl) ⟨278582, by rfl⟩ : syracuseStep 1485773 = 557165) (by norm_num)
theorem B5286869 : Blo 924580 5286869 := bbase (se 7 (by rfl) ⟨61955, by rfl⟩ : syracuseStep 5286869 = 123911) (by norm_num)
theorem B1387493 : Blo 924580 1387493 := bbase (se 4 (by rfl) ⟨130077, by rfl⟩ : syracuseStep 1387493 = 260155) (by norm_num)
theorem B1485805 : Blo 924580 1485805 := bbase (se 3 (by rfl) ⟨278588, by rfl⟩ : syracuseStep 1485805 = 557177) (by norm_num)
theorem B1387517 : Blo 924580 1387517 := bbase (se 3 (by rfl) ⟨260159, by rfl⟩ : syracuseStep 1387517 = 520319) (by norm_num)
theorem B1387541 : Blo 924580 1387541 := bbase (se 6 (by rfl) ⟨32520, by rfl⟩ : syracuseStep 1387541 = 65041) (by norm_num)
theorem B1387565 : Blo 924580 1387565 := bbase (se 3 (by rfl) ⟨260168, by rfl⟩ : syracuseStep 1387565 = 520337) (by norm_num)
theorem B3124277 : Blo 924580 3124277 := bbase (se 5 (by rfl) ⟨146450, by rfl⟩ : syracuseStep 3124277 = 292901) (by norm_num)
theorem B1387589 : Blo 924580 1387589 := bbase (se 4 (by rfl) ⟨130086, by rfl⟩ : syracuseStep 1387589 = 260173) (by norm_num)
theorem B1387613 : Blo 924580 1387613 := bbase (se 3 (by rfl) ⟨260177, by rfl⟩ : syracuseStep 1387613 = 520355) (by norm_num)
theorem B4697189 : Blo 924580 4697189 := bbase (se 4 (by rfl) ⟨440361, by rfl⟩ : syracuseStep 4697189 = 880723) (by norm_num)
theorem B1387637 : Blo 924580 1387637 := bbase (se 5 (by rfl) ⟨65045, by rfl⟩ : syracuseStep 1387637 = 130091) (by norm_num)
theorem B1387661 : Blo 924580 1387661 := bbase (se 3 (by rfl) ⟨260186, by rfl⟩ : syracuseStep 1387661 = 520373) (by norm_num)
theorem B1977493 : Blo 924580 1977493 := bbase (se 6 (by rfl) ⟨46347, by rfl⟩ : syracuseStep 1977493 = 92695) (by norm_num)
theorem B1387685 : Blo 924580 1387685 := bbase (se 4 (by rfl) ⟨130095, by rfl⟩ : syracuseStep 1387685 = 260191) (by norm_num)
theorem B1387709 : Blo 924580 1387709 := bbase (se 3 (by rfl) ⟨260195, by rfl⟩ : syracuseStep 1387709 = 520391) (by norm_num)
theorem B1387733 : Blo 924580 1387733 := bbase (se 7 (by rfl) ⟨16262, by rfl⟩ : syracuseStep 1387733 = 32525) (by norm_num)
theorem B1387757 : Blo 924580 1387757 := bbase (se 3 (by rfl) ⟨260204, by rfl⟩ : syracuseStep 1387757 = 520409) (by norm_num)
theorem B1387781 : Blo 924580 1387781 := bbase (se 4 (by rfl) ⟨130104, by rfl⟩ : syracuseStep 1387781 = 260209) (by norm_num)
theorem B1387805 : Blo 924580 1387805 := bbase (se 3 (by rfl) ⟨260213, by rfl⟩ : syracuseStep 1387805 = 520427) (by norm_num)
theorem B1387829 : Blo 924580 1387829 := bbase (se 5 (by rfl) ⟨65054, by rfl⟩ : syracuseStep 1387829 = 130109) (by norm_num)
theorem B1387853 : Blo 924580 1387853 := bbase (se 3 (by rfl) ⟨260222, by rfl⟩ : syracuseStep 1387853 = 520445) (by norm_num)
theorem B1387877 : Blo 924580 1387877 := bbase (se 4 (by rfl) ⟨130113, by rfl⟩ : syracuseStep 1387877 = 260227) (by norm_num)
theorem B1387901 : Blo 924580 1387901 := bbase (se 3 (by rfl) ⟨260231, by rfl⟩ : syracuseStep 1387901 = 520463) (by norm_num)
theorem B1387925 : Blo 924580 1387925 := bbase (se 6 (by rfl) ⟨32529, by rfl⟩ : syracuseStep 1387925 = 65059) (by norm_num)
theorem B1387949 : Blo 924580 1387949 := bbase (se 3 (by rfl) ⟨260240, by rfl⟩ : syracuseStep 1387949 = 520481) (by norm_num)
theorem B1387973 : Blo 924580 1387973 := bbase (se 4 (by rfl) ⟨130122, by rfl⟩ : syracuseStep 1387973 = 260245) (by norm_num)
theorem B1387997 : Blo 924580 1387997 := bbase (se 3 (by rfl) ⟨260249, by rfl⟩ : syracuseStep 1387997 = 520499) (by norm_num)
theorem B3124709 : Blo 924580 3124709 := bbase (se 4 (by rfl) ⟨292941, by rfl⟩ : syracuseStep 3124709 = 585883) (by norm_num)
theorem B1388021 : Blo 924580 1388021 := bbase (se 5 (by rfl) ⟨65063, by rfl⟩ : syracuseStep 1388021 = 130127) (by norm_num)
theorem B1388045 : Blo 924580 1388045 := bbase (se 3 (by rfl) ⟨260258, by rfl⟩ : syracuseStep 1388045 = 520517) (by norm_num)
theorem B1388069 : Blo 924580 1388069 := bbase (se 4 (by rfl) ⟨130131, by rfl⟩ : syracuseStep 1388069 = 260263) (by norm_num)
theorem B1388093 : Blo 924580 1388093 := bbase (se 3 (by rfl) ⟨260267, by rfl⟩ : syracuseStep 1388093 = 520535) (by norm_num)
theorem B2633285 : Blo 924580 2633285 := bbase (se 4 (by rfl) ⟨246870, by rfl⟩ : syracuseStep 2633285 = 493741) (by norm_num)
theorem B1388117 : Blo 924580 1388117 := bbase (se 8 (by rfl) ⟨8133, by rfl⟩ : syracuseStep 1388117 = 16267) (by norm_num)
theorem B1388141 : Blo 924580 1388141 := bbase (se 3 (by rfl) ⟨260276, by rfl⟩ : syracuseStep 1388141 = 520553) (by norm_num)
theorem B1388165 : Blo 924580 1388165 := bbase (se 4 (by rfl) ⟨130140, by rfl⟩ : syracuseStep 1388165 = 260281) (by norm_num)
theorem B1388189 : Blo 924580 1388189 := bbase (se 3 (by rfl) ⟨260285, by rfl⟩ : syracuseStep 1388189 = 520571) (by norm_num)
theorem B1388213 : Blo 924580 1388213 := bbase (se 5 (by rfl) ⟨65072, by rfl⟩ : syracuseStep 1388213 = 130145) (by norm_num)
theorem B1388237 : Blo 924580 1388237 := bbase (se 3 (by rfl) ⟨260294, by rfl⟩ : syracuseStep 1388237 = 520589) (by norm_num)
theorem B1388261 : Blo 924580 1388261 := bbase (se 4 (by rfl) ⟨130149, by rfl⟩ : syracuseStep 1388261 = 260299) (by norm_num)
theorem B1388285 : Blo 924580 1388285 := bbase (se 3 (by rfl) ⟨260303, by rfl⟩ : syracuseStep 1388285 = 520607) (by norm_num)
theorem B1388309 : Blo 924580 1388309 := bbase (se 6 (by rfl) ⟨32538, by rfl⟩ : syracuseStep 1388309 = 65077) (by norm_num)
theorem B1388333 : Blo 924580 1388333 := bbase (se 3 (by rfl) ⟨260312, by rfl⟩ : syracuseStep 1388333 = 520625) (by norm_num)
theorem B3518261 : Blo 924580 3518261 := bbase (se 5 (by rfl) ⟨164918, by rfl⟩ : syracuseStep 3518261 = 329837) (by norm_num)
theorem B1388357 : Blo 924580 1388357 := bbase (se 4 (by rfl) ⟨130158, by rfl⟩ : syracuseStep 1388357 = 260317) (by norm_num)
theorem B2502485 : Blo 924580 2502485 := bbase (se 9 (by rfl) ⟨7331, by rfl⟩ : syracuseStep 2502485 = 14663) (by norm_num)
theorem B1388381 : Blo 924580 1388381 := bbase (se 3 (by rfl) ⟨260321, by rfl⟩ : syracuseStep 1388381 = 520643) (by norm_num)
theorem B1388405 : Blo 924580 1388405 := bbase (se 5 (by rfl) ⟨65081, by rfl⟩ : syracuseStep 1388405 = 130163) (by norm_num)
theorem B1388429 : Blo 924580 1388429 := bbase (se 3 (by rfl) ⟨260330, by rfl⟩ : syracuseStep 1388429 = 520661) (by norm_num)
theorem B1486733 : Blo 924580 1486733 := bbase (se 3 (by rfl) ⟨278762, by rfl⟩ : syracuseStep 1486733 = 557525) (by norm_num)
theorem B3125141 : Blo 924580 3125141 := bbase (se 6 (by rfl) ⟨73245, by rfl⟩ : syracuseStep 3125141 = 146491) (by norm_num)
theorem B1388453 : Blo 924580 1388453 := bbase (se 4 (by rfl) ⟨130167, by rfl⟩ : syracuseStep 1388453 = 260335) (by norm_num)
theorem B1781677 : Blo 924580 1781677 := bbase (se 3 (by rfl) ⟨334064, by rfl⟩ : syracuseStep 1781677 = 668129) (by norm_num)
theorem B1388477 : Blo 924580 1388477 := bbase (se 3 (by rfl) ⟨260339, by rfl⟩ : syracuseStep 1388477 = 520679) (by norm_num)
theorem B1388501 : Blo 924580 1388501 := bbase (se 7 (by rfl) ⟨16271, by rfl⟩ : syracuseStep 1388501 = 32543) (by norm_num)
theorem B1388525 : Blo 924580 1388525 := bbase (se 3 (by rfl) ⟨260348, by rfl⟩ : syracuseStep 1388525 = 520697) (by norm_num)
theorem B2109445 : Blo 924580 2109445 := bbase (se 4 (by rfl) ⟨197760, by rfl⟩ : syracuseStep 2109445 = 395521) (by norm_num)
theorem B1388549 : Blo 924580 1388549 := bbase (se 4 (by rfl) ⟨130176, by rfl⟩ : syracuseStep 1388549 = 260353) (by norm_num)
theorem B1978381 : Blo 924580 1978381 := bbase (se 3 (by rfl) ⟨370946, by rfl⟩ : syracuseStep 1978381 = 741893) (by norm_num)
theorem B1388573 : Blo 924580 1388573 := bbase (se 3 (by rfl) ⟨260357, by rfl⟩ : syracuseStep 1388573 = 520715) (by norm_num)
theorem B1388597 : Blo 924580 1388597 := bbase (se 5 (by rfl) ⟨65090, by rfl⟩ : syracuseStep 1388597 = 130181) (by norm_num)
theorem B1388621 : Blo 924580 1388621 := bbase (se 3 (by rfl) ⟨260366, by rfl⟩ : syracuseStep 1388621 = 520733) (by norm_num)
theorem B2535509 : Blo 924580 2535509 := bbase (se 8 (by rfl) ⟨14856, by rfl⟩ : syracuseStep 2535509 = 29713) (by norm_num)
theorem B3518549 : Blo 924580 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B1388645 : Blo 924580 1388645 := bbase (se 4 (by rfl) ⟨130185, by rfl⟩ : syracuseStep 1388645 = 260371) (by norm_num)
theorem B1388669 : Blo 924580 1388669 := bbase (se 3 (by rfl) ⟨260375, by rfl⟩ : syracuseStep 1388669 = 520751) (by norm_num)
theorem B1978501 : Blo 924580 1978501 := bbase (se 4 (by rfl) ⟨185484, by rfl⟩ : syracuseStep 1978501 = 370969) (by norm_num)
theorem B1388693 : Blo 924580 1388693 := bbase (se 6 (by rfl) ⟨32547, by rfl⟩ : syracuseStep 1388693 = 65095) (by norm_num)
theorem B1388717 : Blo 924580 1388717 := bbase (se 3 (by rfl) ⟨260384, by rfl⟩ : syracuseStep 1388717 = 520769) (by norm_num)
theorem B1388741 : Blo 924580 1388741 := bbase (se 4 (by rfl) ⟨130194, by rfl⟩ : syracuseStep 1388741 = 260389) (by norm_num)
theorem B1388765 : Blo 924580 1388765 := bbase (se 3 (by rfl) ⟨260393, by rfl⟩ : syracuseStep 1388765 = 520787) (by norm_num)
theorem B1388789 : Blo 924580 1388789 := bbase (se 5 (by rfl) ⟨65099, by rfl⟩ : syracuseStep 1388789 = 130199) (by norm_num)
theorem B1388813 : Blo 924580 1388813 := bbase (se 3 (by rfl) ⟨260402, by rfl⟩ : syracuseStep 1388813 = 520805) (by norm_num)
theorem B1388837 : Blo 924580 1388837 := bbase (se 4 (by rfl) ⟨130203, by rfl⟩ : syracuseStep 1388837 = 260407) (by norm_num)
theorem B1388861 : Blo 924580 1388861 := bbase (se 3 (by rfl) ⟨260411, by rfl⟩ : syracuseStep 1388861 = 520823) (by norm_num)
theorem B3125573 : Blo 924580 3125573 := bbase (se 4 (by rfl) ⟨293022, by rfl⟩ : syracuseStep 3125573 = 586045) (by norm_num)
theorem B1388885 : Blo 924580 1388885 := bbase (se 10 (by rfl) ⟨2034, by rfl⟩ : syracuseStep 1388885 = 4069) (by norm_num)
theorem B1388909 : Blo 924580 1388909 := bbase (se 3 (by rfl) ⟨260420, by rfl⟩ : syracuseStep 1388909 = 520841) (by norm_num)
theorem B4698485 : Blo 924580 4698485 := bbase (se 5 (by rfl) ⟨220241, by rfl⟩ : syracuseStep 4698485 = 440483) (by norm_num)
theorem B1388933 : Blo 924580 1388933 := bbase (se 4 (by rfl) ⟨130212, by rfl⟩ : syracuseStep 1388933 = 260425) (by norm_num)
theorem B1978757 : Blo 924580 1978757 := bbase (se 4 (by rfl) ⟨185508, by rfl⟩ : syracuseStep 1978757 = 371017) (by norm_num)
theorem B1388957 : Blo 924580 1388957 := bbase (se 3 (by rfl) ⟨260429, by rfl⟩ : syracuseStep 1388957 = 520859) (by norm_num)
theorem B1388981 : Blo 924580 1388981 := bbase (se 5 (by rfl) ⟨65108, by rfl⟩ : syracuseStep 1388981 = 130217) (by norm_num)
theorem B1389005 : Blo 924580 1389005 := bbase (se 3 (by rfl) ⟨260438, by rfl⟩ : syracuseStep 1389005 = 520877) (by norm_num)
theorem B1389029 : Blo 924580 1389029 := bbase (se 4 (by rfl) ⟨130221, by rfl⟩ : syracuseStep 1389029 = 260443) (by norm_num)
theorem B2535925 : Blo 924580 2535925 := bbase (se 5 (by rfl) ⟨118871, by rfl⟩ : syracuseStep 2535925 = 237743) (by norm_num)
theorem B1389053 : Blo 924580 1389053 := bbase (se 3 (by rfl) ⟨260447, by rfl⟩ : syracuseStep 1389053 = 520895) (by norm_num)
theorem B1389077 : Blo 924580 1389077 := bbase (se 6 (by rfl) ⟨32556, by rfl⟩ : syracuseStep 1389077 = 65113) (by norm_num)
theorem B1389101 : Blo 924580 1389101 := bbase (se 3 (by rfl) ⟨260456, by rfl⟩ : syracuseStep 1389101 = 520913) (by norm_num)
theorem B1389125 : Blo 924580 1389125 := bbase (se 4 (by rfl) ⟨130230, by rfl⟩ : syracuseStep 1389125 = 260461) (by norm_num)
theorem B1389149 : Blo 924580 1389149 := bbase (se 3 (by rfl) ⟨260465, by rfl⟩ : syracuseStep 1389149 = 520931) (by norm_num)
theorem B1389173 : Blo 924580 1389173 := bbase (se 5 (by rfl) ⟨65117, by rfl⟩ : syracuseStep 1389173 = 130235) (by norm_num)
theorem B1389197 : Blo 924580 1389197 := bbase (se 3 (by rfl) ⟨260474, by rfl⟩ : syracuseStep 1389197 = 520949) (by norm_num)
theorem B1389221 : Blo 924580 1389221 := bbase (se 4 (by rfl) ⟨130239, by rfl⟩ : syracuseStep 1389221 = 260479) (by norm_num)
theorem B1389245 : Blo 924580 1389245 := bbase (se 3 (by rfl) ⟨260483, by rfl⟩ : syracuseStep 1389245 = 520967) (by norm_num)
theorem B1389269 : Blo 924580 1389269 := bbase (se 7 (by rfl) ⟨16280, by rfl⟩ : syracuseStep 1389269 = 32561) (by norm_num)
theorem B1389293 : Blo 924580 1389293 := bbase (se 3 (by rfl) ⟨260492, by rfl⟩ : syracuseStep 1389293 = 520985) (by norm_num)
theorem B3126005 : Blo 924580 3126005 := bbase (se 5 (by rfl) ⟨146531, by rfl⟩ : syracuseStep 3126005 = 293063) (by norm_num)
theorem B1389317 : Blo 924580 1389317 := bbase (se 4 (by rfl) ⟨130248, by rfl⟩ : syracuseStep 1389317 = 260497) (by norm_num)
theorem B1389341 : Blo 924580 1389341 := bbase (se 3 (by rfl) ⟨260501, by rfl⟩ : syracuseStep 1389341 = 521003) (by norm_num)
theorem B1389365 : Blo 924580 1389365 := bbase (se 5 (by rfl) ⟨65126, by rfl⟩ : syracuseStep 1389365 = 130253) (by norm_num)
theorem B1389389 : Blo 924580 1389389 := bbase (se 3 (by rfl) ⟨260510, by rfl⟩ : syracuseStep 1389389 = 521021) (by norm_num)
theorem B10695509 : Blo 924580 10695509 := bbase (se 9 (by rfl) ⟨31334, by rfl⟩ : syracuseStep 10695509 = 62669) (by norm_num)
theorem B1389413 : Blo 924580 1389413 := bbase (se 4 (by rfl) ⟨130257, by rfl⟩ : syracuseStep 1389413 = 260515) (by norm_num)
theorem B1389437 : Blo 924580 1389437 := bbase (se 3 (by rfl) ⟨260519, by rfl⟩ : syracuseStep 1389437 = 521039) (by norm_num)
theorem B2110357 : Blo 924580 2110357 := bbase (se 6 (by rfl) ⟨49461, by rfl⟩ : syracuseStep 2110357 = 98923) (by norm_num)
theorem B1389461 : Blo 924580 1389461 := bbase (se 6 (by rfl) ⟨32565, by rfl⟩ : syracuseStep 1389461 = 65131) (by norm_num)
theorem B1389485 : Blo 924580 1389485 := bbase (se 3 (by rfl) ⟨260528, by rfl⟩ : syracuseStep 1389485 = 521057) (by norm_num)
theorem B1389509 : Blo 924580 1389509 := bbase (se 4 (by rfl) ⟨130266, by rfl⟩ : syracuseStep 1389509 = 260533) (by norm_num)
theorem B12530645 : Blo 924580 12530645 := bbase (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) (by norm_num)
theorem B1389533 : Blo 924580 1389533 := bbase (se 3 (by rfl) ⟨260537, by rfl⟩ : syracuseStep 1389533 = 521075) (by norm_num)
theorem B1389557 : Blo 924580 1389557 := bbase (se 5 (by rfl) ⟨65135, by rfl⟩ : syracuseStep 1389557 = 130271) (by norm_num)
theorem B1389581 : Blo 924580 1389581 := bbase (se 3 (by rfl) ⟨260546, by rfl⟩ : syracuseStep 1389581 = 521093) (by norm_num)
theorem B1389605 : Blo 924580 1389605 := bbase (se 4 (by rfl) ⟨130275, by rfl⟩ : syracuseStep 1389605 = 260551) (by norm_num)
theorem B1389629 : Blo 924580 1389629 := bbase (se 3 (by rfl) ⟨260555, by rfl⟩ : syracuseStep 1389629 = 521111) (by norm_num)
theorem B1389653 : Blo 924580 1389653 := bbase (se 8 (by rfl) ⟨8142, by rfl⟩ : syracuseStep 1389653 = 16285) (by norm_num)
theorem B1389677 : Blo 924580 1389677 := bbase (se 3 (by rfl) ⟨260564, by rfl⟩ : syracuseStep 1389677 = 521129) (by norm_num)
theorem B2634869 : Blo 924580 2634869 := bbase (se 5 (by rfl) ⟨123509, by rfl⟩ : syracuseStep 2634869 = 247019) (by norm_num)
theorem B1389701 : Blo 924580 1389701 := bbase (se 4 (by rfl) ⟨130284, by rfl⟩ : syracuseStep 1389701 = 260569) (by norm_num)
theorem B1389725 : Blo 924580 1389725 := bbase (se 3 (by rfl) ⟨260573, by rfl⟩ : syracuseStep 1389725 = 521147) (by norm_num)
theorem B3126437 : Blo 924580 3126437 := bbase (se 4 (by rfl) ⟨293103, by rfl⟩ : syracuseStep 3126437 = 586207) (by norm_num)
theorem B1389749 : Blo 924580 1389749 := bbase (se 5 (by rfl) ⟨65144, by rfl⟩ : syracuseStep 1389749 = 130289) (by norm_num)
theorem B1389773 : Blo 924580 1389773 := bbase (se 3 (by rfl) ⟨260582, by rfl⟩ : syracuseStep 1389773 = 521165) (by norm_num)
theorem B1389797 : Blo 924580 1389797 := bbase (se 4 (by rfl) ⟨130293, by rfl⟩ : syracuseStep 1389797 = 260587) (by norm_num)
theorem B3519733 : Blo 924580 3519733 := bbase (se 5 (by rfl) ⟨164987, by rfl⟩ : syracuseStep 3519733 = 329975) (by norm_num)
theorem B1389821 : Blo 924580 1389821 := bbase (se 3 (by rfl) ⟨260591, by rfl⟩ : syracuseStep 1389821 = 521183) (by norm_num)
theorem B1979645 : Blo 924580 1979645 := bbase (se 3 (by rfl) ⟨371183, by rfl⟩ : syracuseStep 1979645 = 742367) (by norm_num)
theorem B1389845 : Blo 924580 1389845 := bbase (se 6 (by rfl) ⟨32574, by rfl⟩ : syracuseStep 1389845 = 65149) (by norm_num)
theorem B1389869 : Blo 924580 1389869 := bbase (se 3 (by rfl) ⟨260600, by rfl⟩ : syracuseStep 1389869 = 521201) (by norm_num)
theorem B1389893 : Blo 924580 1389893 := bbase (se 4 (by rfl) ⟨130302, by rfl⟩ : syracuseStep 1389893 = 260605) (by norm_num)
theorem B1389917 : Blo 924580 1389917 := bbase (se 3 (by rfl) ⟨260609, by rfl⟩ : syracuseStep 1389917 = 521219) (by norm_num)
theorem B1389941 : Blo 924580 1389941 := bbase (se 5 (by rfl) ⟨65153, by rfl⟩ : syracuseStep 1389941 = 130307) (by norm_num)
theorem B1389965 : Blo 924580 1389965 := bbase (se 3 (by rfl) ⟨260618, by rfl⟩ : syracuseStep 1389965 = 521237) (by norm_num)
theorem B1389989 : Blo 924580 1389989 := bbase (se 4 (by rfl) ⟨130311, by rfl⟩ : syracuseStep 1389989 = 260623) (by norm_num)
theorem B7026101 : Blo 924580 7026101 := bbase (se 5 (by rfl) ⟨329348, by rfl⟩ : syracuseStep 7026101 = 658697) (by norm_num)
theorem B1390013 : Blo 924580 1390013 := bbase (se 3 (by rfl) ⟨260627, by rfl⟩ : syracuseStep 1390013 = 521255) (by norm_num)
theorem B1390037 : Blo 924580 1390037 := bbase (se 7 (by rfl) ⟨16289, by rfl⟩ : syracuseStep 1390037 = 32579) (by norm_num)
theorem B1390061 : Blo 924580 1390061 := bbase (se 3 (by rfl) ⟨260636, by rfl⟩ : syracuseStep 1390061 = 521273) (by norm_num)
theorem B1979885 : Blo 924580 1979885 := bbase (se 3 (by rfl) ⟨371228, by rfl⟩ : syracuseStep 1979885 = 742457) (by norm_num)
theorem B1390085 : Blo 924580 1390085 := bbase (se 4 (by rfl) ⟨130320, by rfl⟩ : syracuseStep 1390085 = 260641) (by norm_num)
theorem B2340373 : Blo 924580 2340373 := bbase (se 6 (by rfl) ⟨54852, by rfl⟩ : syracuseStep 2340373 = 109705) (by norm_num)
theorem B1390109 : Blo 924580 1390109 := bbase (se 3 (by rfl) ⟨260645, by rfl⟩ : syracuseStep 1390109 = 521291) (by norm_num)
theorem B3520037 : Blo 924580 3520037 := bbase (se 4 (by rfl) ⟨330003, by rfl⟩ : syracuseStep 3520037 = 660007) (by norm_num)
theorem B1390133 : Blo 924580 1390133 := bbase (se 5 (by rfl) ⟨65162, by rfl⟩ : syracuseStep 1390133 = 130325) (by norm_num)
theorem B1390157 : Blo 924580 1390157 := bbase (se 3 (by rfl) ⟨260654, by rfl⟩ : syracuseStep 1390157 = 521309) (by norm_num)
theorem B3126869 : Blo 924580 3126869 := bbase (se 8 (by rfl) ⟨18321, by rfl⟩ : syracuseStep 3126869 = 36643) (by norm_num)
theorem B1390181 : Blo 924580 1390181 := bbase (se 4 (by rfl) ⟨130329, by rfl⟩ : syracuseStep 1390181 = 260659) (by norm_num)
theorem B1390205 : Blo 924580 1390205 := bbase (se 3 (by rfl) ⟨260663, by rfl⟩ : syracuseStep 1390205 = 521327) (by norm_num)
theorem B2340485 : Blo 924580 2340485 := bbase (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) (by norm_num)
theorem B4699781 : Blo 924580 4699781 := bbase (se 4 (by rfl) ⟨440604, by rfl⟩ : syracuseStep 4699781 = 881209) (by norm_num)
theorem B1390229 : Blo 924580 1390229 := bbase (se 6 (by rfl) ⟨32583, by rfl⟩ : syracuseStep 1390229 = 65167) (by norm_num)
theorem B1390253 : Blo 924580 1390253 := bbase (se 3 (by rfl) ⟨260672, by rfl⟩ : syracuseStep 1390253 = 521345) (by norm_num)
theorem B1390277 : Blo 924580 1390277 := bbase (se 4 (by rfl) ⟨130338, by rfl⟩ : syracuseStep 1390277 = 260677) (by norm_num)
theorem B1390301 : Blo 924580 1390301 := bbase (se 3 (by rfl) ⟨260681, by rfl⟩ : syracuseStep 1390301 = 521363) (by norm_num)
theorem B1390325 : Blo 924580 1390325 := bbase (se 5 (by rfl) ⟨65171, by rfl⟩ : syracuseStep 1390325 = 130343) (by norm_num)
theorem B1390349 : Blo 924580 1390349 := bbase (se 3 (by rfl) ⟨260690, by rfl⟩ : syracuseStep 1390349 = 521381) (by norm_num)
theorem B2635541 : Blo 924580 2635541 := bbase (se 6 (by rfl) ⟨61770, by rfl⟩ : syracuseStep 2635541 = 123541) (by norm_num)
theorem B1390373 : Blo 924580 1390373 := bbase (se 4 (by rfl) ⟨130347, by rfl⟩ : syracuseStep 1390373 = 260695) (by norm_num)
theorem B1390397 : Blo 924580 1390397 := bbase (se 3 (by rfl) ⟨260699, by rfl⟩ : syracuseStep 1390397 = 521399) (by norm_num)
theorem B2340677 : Blo 924580 2340677 := bbase (se 4 (by rfl) ⟨219438, by rfl⟩ : syracuseStep 2340677 = 438877) (by norm_num)
theorem B1390421 : Blo 924580 1390421 := bbase (se 9 (by rfl) ⟨4073, by rfl⟩ : syracuseStep 1390421 = 8147) (by norm_num)
theorem B1390445 : Blo 924580 1390445 := bbase (se 3 (by rfl) ⟨260708, by rfl⟩ : syracuseStep 1390445 = 521417) (by norm_num)
theorem B2963317 : Blo 924580 2963317 := bbase (se 5 (by rfl) ⟨138905, by rfl⟩ : syracuseStep 2963317 = 277811) (by norm_num)
theorem B1390469 : Blo 924580 1390469 := bbase (se 4 (by rfl) ⟨130356, by rfl⟩ : syracuseStep 1390469 = 260713) (by norm_num)
theorem B1390493 : Blo 924580 1390493 := bbase (se 3 (by rfl) ⟨260717, by rfl⟩ : syracuseStep 1390493 = 521435) (by norm_num)
theorem B1390517 : Blo 924580 1390517 := bbase (se 5 (by rfl) ⟨65180, by rfl⟩ : syracuseStep 1390517 = 130361) (by norm_num)
theorem B1390541 : Blo 924580 1390541 := bbase (se 3 (by rfl) ⟨260726, by rfl⟩ : syracuseStep 1390541 = 521453) (by norm_num)
theorem B1390565 : Blo 924580 1390565 := bbase (se 4 (by rfl) ⟨130365, by rfl⟩ : syracuseStep 1390565 = 260731) (by norm_num)
theorem B1980389 : Blo 924580 1980389 := bbase (se 4 (by rfl) ⟨185661, by rfl⟩ : syracuseStep 1980389 = 371323) (by norm_num)
theorem B1980397 : Blo 924580 1980397 := bbase (se 3 (by rfl) ⟨371324, by rfl⟩ : syracuseStep 1980397 = 742649) (by norm_num)
theorem B1128433 : Blo 924580 1128433 := bbase (se 2 (by rfl) ⟨423162, by rfl⟩ : syracuseStep 1128433 = 846325) (by norm_num)
theorem B1390589 : Blo 924580 1390589 := bbase (se 3 (by rfl) ⟨260735, by rfl⟩ : syracuseStep 1390589 = 521471) (by norm_num)
theorem B3127301 : Blo 924580 3127301 := bbase (se 4 (by rfl) ⟨293184, by rfl⟩ : syracuseStep 3127301 = 586369) (by norm_num)
theorem B1390613 : Blo 924580 1390613 := bbase (se 6 (by rfl) ⟨32592, by rfl⟩ : syracuseStep 1390613 = 65185) (by norm_num)
theorem B1390637 : Blo 924580 1390637 := bbase (se 3 (by rfl) ⟨260744, by rfl⟩ : syracuseStep 1390637 = 521489) (by norm_num)
theorem B1390661 : Blo 924580 1390661 := bbase (se 4 (by rfl) ⟨130374, by rfl⟩ : syracuseStep 1390661 = 260749) (by norm_num)
theorem B1390685 : Blo 924580 1390685 := bbase (se 3 (by rfl) ⟨260753, by rfl⟩ : syracuseStep 1390685 = 521507) (by norm_num)
theorem B1390709 : Blo 924580 1390709 := bbase (se 5 (by rfl) ⟨65189, by rfl⟩ : syracuseStep 1390709 = 130379) (by norm_num)
theorem B1390733 : Blo 924580 1390733 := bbase (se 3 (by rfl) ⟨260762, by rfl⟩ : syracuseStep 1390733 = 521525) (by norm_num)
theorem B2341021 : Blo 924580 2341021 := bbase (se 3 (by rfl) ⟨438941, by rfl⟩ : syracuseStep 2341021 = 877883) (by norm_num)
theorem B1390757 : Blo 924580 1390757 := bbase (se 4 (by rfl) ⟨130383, by rfl⟩ : syracuseStep 1390757 = 260767) (by norm_num)
theorem B1390781 : Blo 924580 1390781 := bbase (se 3 (by rfl) ⟨260771, by rfl⟩ : syracuseStep 1390781 = 521543) (by norm_num)
theorem B2635973 : Blo 924580 2635973 := bbase (se 4 (by rfl) ⟨247122, by rfl⟩ : syracuseStep 2635973 = 494245) (by norm_num)
theorem B1390805 : Blo 924580 1390805 := bbase (se 7 (by rfl) ⟨16298, by rfl⟩ : syracuseStep 1390805 = 32597) (by norm_num)
theorem B1390829 : Blo 924580 1390829 := bbase (se 3 (by rfl) ⟨260780, by rfl⟩ : syracuseStep 1390829 = 521561) (by norm_num)
theorem B1390853 : Blo 924580 1390853 := bbase (se 4 (by rfl) ⟨130392, by rfl⟩ : syracuseStep 1390853 = 260785) (by norm_num)
theorem B2341133 : Blo 924580 2341133 := bbase (se 3 (by rfl) ⟨438962, by rfl⟩ : syracuseStep 2341133 = 877925) (by norm_num)
theorem B1390877 : Blo 924580 1390877 := bbase (se 3 (by rfl) ⟨260789, by rfl⟩ : syracuseStep 1390877 = 521579) (by norm_num)
theorem B1390901 : Blo 924580 1390901 := bbase (se 5 (by rfl) ⟨65198, by rfl⟩ : syracuseStep 1390901 = 130397) (by norm_num)
theorem B1390925 : Blo 924580 1390925 := bbase (se 3 (by rfl) ⟨260798, by rfl⟩ : syracuseStep 1390925 = 521597) (by norm_num)
theorem B1390949 : Blo 924580 1390949 := bbase (se 4 (by rfl) ⟨130401, by rfl⟩ : syracuseStep 1390949 = 260803) (by norm_num)
theorem B1390973 : Blo 924580 1390973 := bbase (se 3 (by rfl) ⟨260807, by rfl⟩ : syracuseStep 1390973 = 521615) (by norm_num)
theorem B1390997 : Blo 924580 1390997 := bbase (se 6 (by rfl) ⟨32601, by rfl⟩ : syracuseStep 1390997 = 65203) (by norm_num)
theorem B1391021 : Blo 924580 1391021 := bbase (se 3 (by rfl) ⟨260816, by rfl⟩ : syracuseStep 1391021 = 521633) (by norm_num)
theorem B3127733 : Blo 924580 3127733 := bbase (se 5 (by rfl) ⟨146612, by rfl⟩ : syracuseStep 3127733 = 293225) (by norm_num)
theorem B1391045 : Blo 924580 1391045 := bbase (se 4 (by rfl) ⟨130410, by rfl⟩ : syracuseStep 1391045 = 260821) (by norm_num)
theorem B2341325 : Blo 924580 2341325 := bbase (se 3 (by rfl) ⟨438998, by rfl⟩ : syracuseStep 2341325 = 877997) (by norm_num)
theorem B1391069 : Blo 924580 1391069 := bbase (se 3 (by rfl) ⟨260825, by rfl⟩ : syracuseStep 1391069 = 521651) (by norm_num)
theorem B1391093 : Blo 924580 1391093 := bbase (se 5 (by rfl) ⟨65207, by rfl⟩ : syracuseStep 1391093 = 130415) (by norm_num)
theorem B2505221 : Blo 924580 2505221 := bbase (se 4 (by rfl) ⟨234864, by rfl⟩ : syracuseStep 2505221 = 469729) (by norm_num)
theorem B1391117 : Blo 924580 1391117 := bbase (se 3 (by rfl) ⟨260834, by rfl⟩ : syracuseStep 1391117 = 521669) (by norm_num)
theorem B1391141 : Blo 924580 1391141 := bbase (se 4 (by rfl) ⟨130419, by rfl⟩ : syracuseStep 1391141 = 260839) (by norm_num)
theorem B1391165 : Blo 924580 1391165 := bbase (se 3 (by rfl) ⟨260843, by rfl⟩ : syracuseStep 1391165 = 521687) (by norm_num)
theorem B1391189 : Blo 924580 1391189 := bbase (se 8 (by rfl) ⟨8151, by rfl⟩ : syracuseStep 1391189 = 16303) (by norm_num)
theorem B1391213 : Blo 924580 1391213 := bbase (se 3 (by rfl) ⟨260852, by rfl⟩ : syracuseStep 1391213 = 521705) (by norm_num)
theorem B1391237 : Blo 924580 1391237 := bbase (se 4 (by rfl) ⟨130428, by rfl⟩ : syracuseStep 1391237 = 260857) (by norm_num)
theorem B1391261 : Blo 924580 1391261 := bbase (se 3 (by rfl) ⟨260861, by rfl⟩ : syracuseStep 1391261 = 521723) (by norm_num)
theorem B1391285 : Blo 924580 1391285 := bbase (se 5 (by rfl) ⟨65216, by rfl⟩ : syracuseStep 1391285 = 130433) (by norm_num)
theorem B1391309 : Blo 924580 1391309 := bbase (se 3 (by rfl) ⟨260870, by rfl⟩ : syracuseStep 1391309 = 521741) (by norm_num)
theorem B1391333 : Blo 924580 1391333 := bbase (se 4 (by rfl) ⟨130437, by rfl⟩ : syracuseStep 1391333 = 260875) (by norm_num)
theorem B1391357 : Blo 924580 1391357 := bbase (se 3 (by rfl) ⟨260879, by rfl⟩ : syracuseStep 1391357 = 521759) (by norm_num)
theorem B1391381 : Blo 924580 1391381 := bbase (se 6 (by rfl) ⟨32610, by rfl⟩ : syracuseStep 1391381 = 65221) (by norm_num)
theorem B2341669 : Blo 924580 2341669 := bbase (se 4 (by rfl) ⟨219531, by rfl⟩ : syracuseStep 2341669 = 439063) (by norm_num)
theorem B1391405 : Blo 924580 1391405 := bbase (se 3 (by rfl) ⟨260888, by rfl⟩ : syracuseStep 1391405 = 521777) (by norm_num)
theorem B1391429 : Blo 924580 1391429 := bbase (se 4 (by rfl) ⟨130446, by rfl⟩ : syracuseStep 1391429 = 260893) (by norm_num)
theorem B7519061 : Blo 924580 7519061 := bbase (se 9 (by rfl) ⟨22028, by rfl⟩ : syracuseStep 7519061 = 44057) (by norm_num)
theorem B1391453 : Blo 924580 1391453 := bbase (se 3 (by rfl) ⟨260897, by rfl⟩ : syracuseStep 1391453 = 521795) (by norm_num)
theorem B3128165 : Blo 924580 3128165 := bbase (se 4 (by rfl) ⟨293265, by rfl⟩ : syracuseStep 3128165 = 586531) (by norm_num)
theorem B2112365 : Blo 924580 2112365 := bbase (se 3 (by rfl) ⟨396068, by rfl⟩ : syracuseStep 2112365 = 792137) (by norm_num)
theorem B1391477 : Blo 924580 1391477 := bbase (se 5 (by rfl) ⟨65225, by rfl⟩ : syracuseStep 1391477 = 130451) (by norm_num)
theorem B1391501 : Blo 924580 1391501 := bbase (se 3 (by rfl) ⟨260906, by rfl⟩ : syracuseStep 1391501 = 521813) (by norm_num)
theorem B2341781 : Blo 924580 2341781 := bbase (se 6 (by rfl) ⟨54885, by rfl⟩ : syracuseStep 2341781 = 109771) (by norm_num)
theorem B1391525 : Blo 924580 1391525 := bbase (se 4 (by rfl) ⟨130455, by rfl⟩ : syracuseStep 1391525 = 260911) (by norm_num)
theorem B1588133 : Blo 924580 1588133 := bbase (se 4 (by rfl) ⟨148887, by rfl⟩ : syracuseStep 1588133 = 297775) (by norm_num)
theorem B2636725 : Blo 924580 2636725 := bbase (se 5 (by rfl) ⟨123596, by rfl⟩ : syracuseStep 2636725 = 247193) (by norm_num)
theorem B1391549 : Blo 924580 1391549 := bbase (se 3 (by rfl) ⟨260915, by rfl⟩ : syracuseStep 1391549 = 521831) (by norm_num)
theorem B1391573 : Blo 924580 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B1391597 : Blo 924580 1391597 := bbase (se 3 (by rfl) ⟨260924, by rfl⟩ : syracuseStep 1391597 = 521849) (by norm_num)
theorem B1391621 : Blo 924580 1391621 := bbase (se 4 (by rfl) ⟨130464, by rfl⟩ : syracuseStep 1391621 = 260929) (by norm_num)
theorem B1391645 : Blo 924580 1391645 := bbase (se 3 (by rfl) ⟨260933, by rfl⟩ : syracuseStep 1391645 = 521867) (by norm_num)
theorem B1391669 : Blo 924580 1391669 := bbase (se 5 (by rfl) ⟨65234, by rfl⟩ : syracuseStep 1391669 = 130469) (by norm_num)
theorem B1391693 : Blo 924580 1391693 := bbase (se 3 (by rfl) ⟨260942, by rfl⟩ : syracuseStep 1391693 = 521885) (by norm_num)
theorem B2341973 : Blo 924580 2341973 := bbase (se 8 (by rfl) ⟨13722, by rfl⟩ : syracuseStep 2341973 = 27445) (by norm_num)
theorem B11877461 : Blo 924580 11877461 := bbase (se 8 (by rfl) ⟨69594, by rfl⟩ : syracuseStep 11877461 = 139189) (by norm_num)
theorem B1981525 : Blo 924580 1981525 := bbase (se 8 (by rfl) ⟨11610, by rfl⟩ : syracuseStep 1981525 = 23221) (by norm_num)
theorem B1391717 : Blo 924580 1391717 := bbase (se 4 (by rfl) ⟨130473, by rfl⟩ : syracuseStep 1391717 = 260947) (by norm_num)
theorem B1391741 : Blo 924580 1391741 := bbase (se 3 (by rfl) ⟨260951, by rfl⟩ : syracuseStep 1391741 = 521903) (by norm_num)
theorem B1391765 : Blo 924580 1391765 := bbase (se 6 (by rfl) ⟨32619, by rfl⟩ : syracuseStep 1391765 = 65239) (by norm_num)
theorem B1391789 : Blo 924580 1391789 := bbase (se 3 (by rfl) ⟨260960, by rfl⟩ : syracuseStep 1391789 = 521921) (by norm_num)
theorem B1391813 : Blo 924580 1391813 := bbase (se 4 (by rfl) ⟨130482, by rfl⟩ : syracuseStep 1391813 = 260965) (by norm_num)
theorem B1391837 : Blo 924580 1391837 := bbase (se 3 (by rfl) ⟨260969, by rfl⟩ : syracuseStep 1391837 = 521939) (by norm_num)
theorem B1391861 : Blo 924580 1391861 := bbase (se 5 (by rfl) ⟨65243, by rfl⟩ : syracuseStep 1391861 = 130487) (by norm_num)
theorem B1391885 : Blo 924580 1391885 := bbase (se 3 (by rfl) ⟨260978, by rfl⟩ : syracuseStep 1391885 = 521957) (by norm_num)
theorem B3128597 : Blo 924580 3128597 := bbase (se 6 (by rfl) ⟨73326, by rfl⟩ : syracuseStep 3128597 = 146653) (by norm_num)
theorem B1391909 : Blo 924580 1391909 := bbase (se 4 (by rfl) ⟨130491, by rfl⟩ : syracuseStep 1391909 = 260983) (by norm_num)
theorem B1391933 : Blo 924580 1391933 := bbase (se 3 (by rfl) ⟨260987, by rfl⟩ : syracuseStep 1391933 = 521975) (by norm_num)
theorem B1391957 : Blo 924580 1391957 := bbase (se 11 (by rfl) ⟨1019, by rfl⟩ : syracuseStep 1391957 = 2039) (by norm_num)
theorem B1391981 : Blo 924580 1391981 := bbase (se 3 (by rfl) ⟨260996, by rfl⟩ : syracuseStep 1391981 = 521993) (by norm_num)
theorem B1392005 : Blo 924580 1392005 := bbase (se 4 (by rfl) ⟨130500, by rfl⟩ : syracuseStep 1392005 = 261001) (by norm_num)
theorem B1392029 : Blo 924580 1392029 := bbase (se 3 (by rfl) ⟨261005, by rfl⟩ : syracuseStep 1392029 = 522011) (by norm_num)
theorem B2342317 : Blo 924580 2342317 := bbase (se 3 (by rfl) ⟨439184, by rfl⟩ : syracuseStep 2342317 = 878369) (by norm_num)
theorem B1392053 : Blo 924580 1392053 := bbase (se 5 (by rfl) ⟨65252, by rfl⟩ : syracuseStep 1392053 = 130505) (by norm_num)
theorem B1981901 : Blo 924580 1981901 := bbase (se 3 (by rfl) ⟨371606, by rfl⟩ : syracuseStep 1981901 = 743213) (by norm_num)
theorem B1392077 : Blo 924580 1392077 := bbase (se 3 (by rfl) ⟨261014, by rfl⟩ : syracuseStep 1392077 = 522029) (by norm_num)
theorem B1392101 : Blo 924580 1392101 := bbase (se 4 (by rfl) ⟨130509, by rfl⟩ : syracuseStep 1392101 = 261019) (by norm_num)
theorem B1392125 : Blo 924580 1392125 := bbase (se 3 (by rfl) ⟨261023, by rfl⟩ : syracuseStep 1392125 = 522047) (by norm_num)
theorem B1392149 : Blo 924580 1392149 := bbase (se 6 (by rfl) ⟨32628, by rfl⟩ : syracuseStep 1392149 = 65257) (by norm_num)
theorem B2342429 : Blo 924580 2342429 := bbase (se 3 (by rfl) ⟨439205, by rfl⟩ : syracuseStep 2342429 = 878411) (by norm_num)
theorem B1392173 : Blo 924580 1392173 := bbase (se 3 (by rfl) ⟨261032, by rfl⟩ : syracuseStep 1392173 = 522065) (by norm_num)
theorem B1130041 : Blo 924580 1130041 := bbase (se 2 (by rfl) ⟨423765, by rfl⟩ : syracuseStep 1130041 = 847531) (by norm_num)
theorem B1392197 : Blo 924580 1392197 := bbase (se 4 (by rfl) ⟨130518, by rfl⟩ : syracuseStep 1392197 = 261037) (by norm_num)
theorem B2080349 : Blo 924580 2080349 := bbase (se 3 (by rfl) ⟨390065, by rfl⟩ : syracuseStep 2080349 = 780131) (by norm_num)
theorem B1392221 : Blo 924580 1392221 := bbase (se 3 (by rfl) ⟨261041, by rfl⟩ : syracuseStep 1392221 = 522083) (by norm_num)
theorem B3522149 : Blo 924580 3522149 := bbase (se 4 (by rfl) ⟨330201, by rfl⟩ : syracuseStep 3522149 = 660403) (by norm_num)
theorem B1392245 : Blo 924580 1392245 := bbase (se 5 (by rfl) ⟨65261, by rfl⟩ : syracuseStep 1392245 = 130523) (by norm_num)
theorem B1392269 : Blo 924580 1392269 := bbase (se 3 (by rfl) ⟨261050, by rfl⟩ : syracuseStep 1392269 = 522101) (by norm_num)
theorem B2080421 : Blo 924580 2080421 := bbase (se 4 (by rfl) ⟨195039, by rfl⟩ : syracuseStep 2080421 = 390079) (by norm_num)
theorem B1392293 : Blo 924580 1392293 := bbase (se 4 (by rfl) ⟨130527, by rfl⟩ : syracuseStep 1392293 = 261055) (by norm_num)
theorem B3391141 : Blo 924580 3391141 := bbase (se 4 (by rfl) ⟨317919, by rfl⟩ : syracuseStep 3391141 = 635839) (by norm_num)
theorem B1392317 : Blo 924580 1392317 := bbase (se 3 (by rfl) ⟨261059, by rfl⟩ : syracuseStep 1392317 = 522119) (by norm_num)
theorem B3129029 : Blo 924580 3129029 := bbase (se 4 (by rfl) ⟨293346, by rfl⟩ : syracuseStep 3129029 = 586693) (by norm_num)
theorem B1392341 : Blo 924580 1392341 := bbase (se 7 (by rfl) ⟨16316, by rfl⟩ : syracuseStep 1392341 = 32633) (by norm_num)
theorem B2342621 : Blo 924580 2342621 := bbase (se 3 (by rfl) ⟨439241, by rfl⟩ : syracuseStep 2342621 = 878483) (by norm_num)
theorem B2080493 : Blo 924580 2080493 := bbase (se 3 (by rfl) ⟨390092, by rfl⟩ : syracuseStep 2080493 = 780185) (by norm_num)
theorem B1392365 : Blo 924580 1392365 := bbase (se 3 (by rfl) ⟨261068, by rfl⟩ : syracuseStep 1392365 = 522137) (by norm_num)
theorem B1392389 : Blo 924580 1392389 := bbase (se 4 (by rfl) ⟨130536, by rfl⟩ : syracuseStep 1392389 = 261073) (by norm_num)
theorem B1392413 : Blo 924580 1392413 := bbase (se 3 (by rfl) ⟨261077, by rfl⟩ : syracuseStep 1392413 = 522155) (by norm_num)
theorem B2080565 : Blo 924580 2080565 := bbase (se 5 (by rfl) ⟨97526, by rfl⟩ : syracuseStep 2080565 = 195053) (by norm_num)
theorem B1392437 : Blo 924580 1392437 := bbase (se 5 (by rfl) ⟨65270, by rfl⟩ : syracuseStep 1392437 = 130541) (by norm_num)
theorem B1392461 : Blo 924580 1392461 := bbase (se 3 (by rfl) ⟨261086, by rfl⟩ : syracuseStep 1392461 = 522173) (by norm_num)
theorem B1392485 : Blo 924580 1392485 := bbase (se 4 (by rfl) ⟨130545, by rfl⟩ : syracuseStep 1392485 = 261091) (by norm_num)
theorem B2080637 : Blo 924580 2080637 := bbase (se 3 (by rfl) ⟨390119, by rfl⟩ : syracuseStep 2080637 = 780239) (by norm_num)
theorem B1392509 : Blo 924580 1392509 := bbase (se 3 (by rfl) ⟨261095, by rfl⟩ : syracuseStep 1392509 = 522191) (by norm_num)
theorem B3522437 : Blo 924580 3522437 := bbase (se 4 (by rfl) ⟨330228, by rfl⟩ : syracuseStep 3522437 = 660457) (by norm_num)
theorem B1392533 : Blo 924580 1392533 := bbase (se 6 (by rfl) ⟨32637, by rfl⟩ : syracuseStep 1392533 = 65275) (by norm_num)
theorem B1392557 : Blo 924580 1392557 := bbase (se 3 (by rfl) ⟨261104, by rfl⟩ : syracuseStep 1392557 = 522209) (by norm_num)
theorem B2080709 : Blo 924580 2080709 := bbase (se 4 (by rfl) ⟨195066, by rfl⟩ : syracuseStep 2080709 = 390133) (by norm_num)
theorem B1392581 : Blo 924580 1392581 := bbase (se 4 (by rfl) ⟨130554, by rfl⟩ : syracuseStep 1392581 = 261109) (by norm_num)
theorem B1392605 : Blo 924580 1392605 := bbase (se 3 (by rfl) ⟨261113, by rfl⟩ : syracuseStep 1392605 = 522227) (by norm_num)
theorem B1392629 : Blo 924580 1392629 := bbase (se 5 (by rfl) ⟨65279, by rfl⟩ : syracuseStep 1392629 = 130559) (by norm_num)
theorem B2080781 : Blo 924580 2080781 := bbase (se 3 (by rfl) ⟨390146, by rfl⟩ : syracuseStep 2080781 = 780293) (by norm_num)
theorem B1392653 : Blo 924580 1392653 := bbase (se 3 (by rfl) ⟨261122, by rfl⟩ : syracuseStep 1392653 = 522245) (by norm_num)
theorem B1392677 : Blo 924580 1392677 := bbase (se 4 (by rfl) ⟨130563, by rfl⟩ : syracuseStep 1392677 = 261127) (by norm_num)
theorem B2342965 : Blo 924580 2342965 := bbase (se 5 (by rfl) ⟨109826, by rfl⟩ : syracuseStep 2342965 = 219653) (by norm_num)
theorem B5947445 : Blo 924580 5947445 := bbase (se 5 (by rfl) ⟨278786, by rfl⟩ : syracuseStep 5947445 = 557573) (by norm_num)
theorem B1392701 : Blo 924580 1392701 := bbase (se 3 (by rfl) ⟨261131, by rfl⟩ : syracuseStep 1392701 = 522263) (by norm_num)
theorem B2080853 : Blo 924580 2080853 := bbase (se 8 (by rfl) ⟨12192, by rfl⟩ : syracuseStep 2080853 = 24385) (by norm_num)
theorem B1392725 : Blo 924580 1392725 := bbase (se 8 (by rfl) ⟨8160, by rfl⟩ : syracuseStep 1392725 = 16321) (by norm_num)
theorem B1392749 : Blo 924580 1392749 := bbase (se 3 (by rfl) ⟨261140, by rfl⟩ : syracuseStep 1392749 = 522281) (by norm_num)
theorem B3129461 : Blo 924580 3129461 := bbase (se 5 (by rfl) ⟨146693, by rfl⟩ : syracuseStep 3129461 = 293387) (by norm_num)
theorem B1392773 : Blo 924580 1392773 := bbase (se 4 (by rfl) ⟨130572, by rfl⟩ : syracuseStep 1392773 = 261145) (by norm_num)
theorem B2080925 : Blo 924580 2080925 := bbase (se 3 (by rfl) ⟨390173, by rfl⟩ : syracuseStep 2080925 = 780347) (by norm_num)
theorem B1392797 : Blo 924580 1392797 := bbase (se 3 (by rfl) ⟨261149, by rfl⟩ : syracuseStep 1392797 = 522299) (by norm_num)
theorem B2343077 : Blo 924580 2343077 := bbase (se 4 (by rfl) ⟨219663, by rfl⟩ : syracuseStep 2343077 = 439327) (by norm_num)
theorem B1392821 : Blo 924580 1392821 := bbase (se 5 (by rfl) ⟨65288, by rfl⟩ : syracuseStep 1392821 = 130577) (by norm_num)
theorem B1392845 : Blo 924580 1392845 := bbase (se 3 (by rfl) ⟨261158, by rfl⟩ : syracuseStep 1392845 = 522317) (by norm_num)
theorem B2080997 : Blo 924580 2080997 := bbase (se 4 (by rfl) ⟨195093, by rfl⟩ : syracuseStep 2080997 = 390187) (by norm_num)
theorem B1392869 : Blo 924580 1392869 := bbase (se 4 (by rfl) ⟨130581, by rfl⟩ : syracuseStep 1392869 = 261163) (by norm_num)
theorem B2081069 : Blo 924580 2081069 := bbase (se 3 (by rfl) ⟨390200, by rfl⟩ : syracuseStep 2081069 = 780401) (by norm_num)
theorem B2343269 : Blo 924580 2343269 := bbase (se 4 (by rfl) ⟨219681, by rfl⟩ : syracuseStep 2343269 = 439363) (by norm_num)
theorem B2081141 : Blo 924580 2081141 := bbase (se 5 (by rfl) ⟨97553, by rfl⟩ : syracuseStep 2081141 = 195107) (by norm_num)
theorem B2081213 : Blo 924580 2081213 := bbase (se 3 (by rfl) ⟨390227, by rfl⟩ : syracuseStep 2081213 = 780455) (by norm_num)
theorem B2081285 : Blo 924580 2081285 := bbase (se 4 (by rfl) ⟨195120, by rfl⟩ : syracuseStep 2081285 = 390241) (by norm_num)
theorem B7225877 : Blo 924580 7225877 := bbase (se 6 (by rfl) ⟨169356, by rfl⟩ : syracuseStep 7225877 = 338713) (by norm_num)
theorem B3129893 : Blo 924580 3129893 := bbase (se 4 (by rfl) ⟨293427, by rfl⟩ : syracuseStep 3129893 = 586855) (by norm_num)
theorem B2114117 : Blo 924580 2114117 := bbase (se 4 (by rfl) ⟨198198, by rfl⟩ : syracuseStep 2114117 = 396397) (by norm_num)
theorem B2081357 : Blo 924580 2081357 := bbase (se 3 (by rfl) ⟨390254, by rfl⟩ : syracuseStep 2081357 = 780509) (by norm_num)
theorem B2081429 : Blo 924580 2081429 := bbase (se 6 (by rfl) ⟨48783, by rfl⟩ : syracuseStep 2081429 = 97567) (by norm_num)
theorem B2343613 : Blo 924580 2343613 := bbase (se 3 (by rfl) ⟨439427, by rfl⟩ : syracuseStep 2343613 = 878855) (by norm_num)
theorem B2081501 : Blo 924580 2081501 := bbase (se 3 (by rfl) ⟨390281, by rfl⟩ : syracuseStep 2081501 = 780563) (by norm_num)
theorem B2081573 : Blo 924580 2081573 := bbase (se 4 (by rfl) ⟨195147, by rfl⟩ : syracuseStep 2081573 = 390295) (by norm_num)
theorem B2343725 : Blo 924580 2343725 := bbase (se 3 (by rfl) ⟨439448, by rfl⟩ : syracuseStep 2343725 = 878897) (by norm_num)
theorem B2900821 : Blo 924580 2900821 := bbase (se 9 (by rfl) ⟨8498, by rfl⟩ : syracuseStep 2900821 = 16997) (by norm_num)
theorem B2081645 : Blo 924580 2081645 := bbase (se 3 (by rfl) ⟨390308, by rfl⟩ : syracuseStep 2081645 = 780617) (by norm_num)
theorem B2081717 : Blo 924580 2081717 := bbase (se 5 (by rfl) ⟨97580, by rfl⟩ : syracuseStep 2081717 = 195161) (by norm_num)
theorem B3130325 : Blo 924580 3130325 := bbase (se 7 (by rfl) ⟨36683, by rfl⟩ : syracuseStep 3130325 = 73367) (by norm_num)
theorem B2343917 : Blo 924580 2343917 := bbase (se 3 (by rfl) ⟨439484, by rfl⟩ : syracuseStep 2343917 = 878969) (by norm_num)
theorem B2081789 : Blo 924580 2081789 := bbase (se 3 (by rfl) ⟨390335, by rfl⟩ : syracuseStep 2081789 = 780671) (by norm_num)
theorem B3523621 : Blo 924580 3523621 := bbase (se 4 (by rfl) ⟨330339, by rfl⟩ : syracuseStep 3523621 = 660679) (by norm_num)
theorem B2081861 : Blo 924580 2081861 := bbase (se 4 (by rfl) ⟨195174, by rfl⟩ : syracuseStep 2081861 = 390349) (by norm_num)
theorem B2081933 : Blo 924580 2081933 := bbase (se 3 (by rfl) ⟨390362, by rfl⟩ : syracuseStep 2081933 = 780725) (by norm_num)
theorem B2082005 : Blo 924580 2082005 := bbase (se 7 (by rfl) ⟨24398, by rfl⟩ : syracuseStep 2082005 = 48797) (by norm_num)
theorem B2082077 : Blo 924580 2082077 := bbase (se 3 (by rfl) ⟨390389, by rfl⟩ : syracuseStep 2082077 = 780779) (by norm_num)
theorem B3163445 : Blo 924580 3163445 := bbase (se 5 (by rfl) ⟨148286, by rfl⟩ : syracuseStep 3163445 = 296573) (by norm_num)
theorem B2344261 : Blo 924580 2344261 := bbase (se 4 (by rfl) ⟨219774, by rfl⟩ : syracuseStep 2344261 = 439549) (by norm_num)
theorem B3523925 : Blo 924580 3523925 := bbase (se 12 (by rfl) ⟨1290, by rfl⟩ : syracuseStep 3523925 = 2581) (by norm_num)
theorem B2082149 : Blo 924580 2082149 := bbase (se 4 (by rfl) ⟨195201, by rfl⟩ : syracuseStep 2082149 = 390403) (by norm_num)
theorem B3130757 : Blo 924580 3130757 := bbase (se 4 (by rfl) ⟨293508, by rfl⟩ : syracuseStep 3130757 = 587017) (by norm_num)
theorem B2082221 : Blo 924580 2082221 := bbase (se 3 (by rfl) ⟨390416, by rfl⟩ : syracuseStep 2082221 = 780833) (by norm_num)
theorem B2344373 : Blo 924580 2344373 := bbase (se 5 (by rfl) ⟨109892, by rfl⟩ : syracuseStep 2344373 = 219785) (by norm_num)
theorem B2082293 : Blo 924580 2082293 := bbase (se 5 (by rfl) ⟨97607, by rfl⟩ : syracuseStep 2082293 = 195215) (by norm_num)
theorem B3950117 : Blo 924580 3950117 := bbase (se 4 (by rfl) ⟨370323, by rfl⟩ : syracuseStep 3950117 = 740647) (by norm_num)
theorem B2082365 : Blo 924580 2082365 := bbase (se 3 (by rfl) ⟨390443, by rfl⟩ : syracuseStep 2082365 = 780887) (by norm_num)
theorem B2344565 : Blo 924580 2344565 := bbase (se 5 (by rfl) ⟨109901, by rfl⟩ : syracuseStep 2344565 = 219803) (by norm_num)
theorem B2082437 : Blo 924580 2082437 := bbase (se 4 (by rfl) ⟨195228, by rfl⟩ : syracuseStep 2082437 = 390457) (by norm_num)
theorem B2508421 : Blo 924580 2508421 := bbase (se 4 (by rfl) ⟨235164, by rfl⟩ : syracuseStep 2508421 = 470329) (by norm_num)
theorem B2082509 : Blo 924580 2082509 := bbase (se 3 (by rfl) ⟨390470, by rfl⟩ : syracuseStep 2082509 = 780941) (by norm_num)
theorem B2639573 : Blo 924580 2639573 := bbase (se 7 (by rfl) ⟨30932, by rfl⟩ : syracuseStep 2639573 = 61865) (by norm_num)
theorem B2082581 : Blo 924580 2082581 := bbase (se 6 (by rfl) ⟨48810, by rfl⟩ : syracuseStep 2082581 = 97621) (by norm_num)
theorem B3131189 : Blo 924580 3131189 := bbase (se 5 (by rfl) ⟨146774, by rfl⟩ : syracuseStep 3131189 = 293549) (by norm_num)
theorem B2082653 : Blo 924580 2082653 := bbase (se 3 (by rfl) ⟨390497, by rfl⟩ : syracuseStep 2082653 = 780995) (by norm_num)
theorem B2082725 : Blo 924580 2082725 := bbase (se 4 (by rfl) ⟨195255, by rfl⟩ : syracuseStep 2082725 = 390511) (by norm_num)
theorem B2344909 : Blo 924580 2344909 := bbase (se 3 (by rfl) ⟨439670, by rfl⟩ : syracuseStep 2344909 = 879341) (by norm_num)
theorem B2967509 : Blo 924580 2967509 := bbase (se 7 (by rfl) ⟨34775, by rfl⟩ : syracuseStep 2967509 = 69551) (by norm_num)
theorem B2082797 : Blo 924580 2082797 := bbase (se 3 (by rfl) ⟨390524, by rfl⟩ : syracuseStep 2082797 = 781049) (by norm_num)
theorem B2377765 : Blo 924580 2377765 := bbase (se 4 (by rfl) ⟨222915, by rfl⟩ : syracuseStep 2377765 = 445831) (by norm_num)
theorem B2082869 : Blo 924580 2082869 := bbase (se 5 (by rfl) ⟨97634, by rfl⟩ : syracuseStep 2082869 = 195269) (by norm_num)
theorem B2345021 : Blo 924580 2345021 := bbase (se 3 (by rfl) ⟨439691, by rfl⟩ : syracuseStep 2345021 = 879383) (by norm_num)
theorem B2082941 : Blo 924580 2082941 := bbase (se 3 (by rfl) ⟨390551, by rfl⟩ : syracuseStep 2082941 = 781103) (by norm_num)
theorem B2083013 : Blo 924580 2083013 := bbase (se 4 (by rfl) ⟨195282, by rfl⟩ : syracuseStep 2083013 = 390565) (by norm_num)
theorem B1755341 : Blo 924580 1755341 := bbase (se 3 (by rfl) ⟨329126, by rfl⟩ : syracuseStep 1755341 = 658253) (by norm_num)
theorem B3131621 : Blo 924580 3131621 := bbase (se 4 (by rfl) ⟨293589, by rfl⟩ : syracuseStep 3131621 = 587179) (by norm_num)
theorem B2345213 : Blo 924580 2345213 := bbase (se 3 (by rfl) ⟨439727, by rfl⟩ : syracuseStep 2345213 = 879455) (by norm_num)
theorem B2083085 : Blo 924580 2083085 := bbase (se 3 (by rfl) ⟨390578, by rfl⟩ : syracuseStep 2083085 = 781157) (by norm_num)
theorem B1001765 : Blo 924580 1001765 := bbase (se 4 (by rfl) ⟨93915, by rfl⟩ : syracuseStep 1001765 = 187831) (by norm_num)
theorem B2083157 : Blo 924580 2083157 := bbase (se 10 (by rfl) ⟨3051, by rfl⟩ : syracuseStep 2083157 = 6103) (by norm_num)
theorem B2083229 : Blo 924580 2083229 := bbase (se 3 (by rfl) ⟨390605, by rfl⟩ : syracuseStep 2083229 = 781211) (by norm_num)
theorem B2083301 : Blo 924580 2083301 := bbase (se 4 (by rfl) ⟨195309, by rfl⟩ : syracuseStep 2083301 = 390619) (by norm_num)
theorem B3951125 : Blo 924580 3951125 := bbase (se 6 (by rfl) ⟨92604, by rfl⟩ : syracuseStep 3951125 = 185209) (by norm_num)
theorem B2083373 : Blo 924580 2083373 := bbase (se 3 (by rfl) ⟨390632, by rfl⟩ : syracuseStep 2083373 = 781265) (by norm_num)
theorem B4999733 : Blo 924580 4999733 := bbase (se 5 (by rfl) ⟨234362, by rfl⟩ : syracuseStep 4999733 = 468725) (by norm_num)
theorem B2345557 : Blo 924580 2345557 := bbase (se 8 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 2345557 = 27487) (by norm_num)
theorem B2083445 : Blo 924580 2083445 := bbase (se 5 (by rfl) ⟨97661, by rfl⟩ : syracuseStep 2083445 = 195323) (by norm_num)
theorem B3132053 : Blo 924580 3132053 := bbase (se 6 (by rfl) ⟨73407, by rfl⟩ : syracuseStep 3132053 = 146815) (by norm_num)
theorem B2083517 : Blo 924580 2083517 := bbase (se 3 (by rfl) ⟨390659, by rfl⟩ : syracuseStep 2083517 = 781319) (by norm_num)
theorem B2345669 : Blo 924580 2345669 := bbase (se 4 (by rfl) ⟨219906, by rfl⟩ : syracuseStep 2345669 = 439813) (by norm_num)
theorem B2083589 : Blo 924580 2083589 := bbase (se 4 (by rfl) ⟨195336, by rfl⟩ : syracuseStep 2083589 = 390673) (by norm_num)
theorem B2116381 : Blo 924580 2116381 := bbase (se 3 (by rfl) ⟨396821, by rfl⟩ : syracuseStep 2116381 = 793643) (by norm_num)
theorem B2083661 : Blo 924580 2083661 := bbase (se 3 (by rfl) ⟨390686, by rfl⟩ : syracuseStep 2083661 = 781373) (by norm_num)
theorem B2640757 : Blo 924580 2640757 := bbase (se 5 (by rfl) ⟨123785, by rfl⟩ : syracuseStep 2640757 = 247571) (by norm_num)
theorem B7523189 : Blo 924580 7523189 := bbase (se 5 (by rfl) ⟨352649, by rfl⟩ : syracuseStep 7523189 = 705299) (by norm_num)
theorem B2345861 : Blo 924580 2345861 := bbase (se 4 (by rfl) ⟨219924, by rfl⟩ : syracuseStep 2345861 = 439849) (by norm_num)
theorem B2083733 : Blo 924580 2083733 := bbase (se 6 (by rfl) ⟨48837, by rfl⟩ : syracuseStep 2083733 = 97675) (by norm_num)
theorem B1756093 : Blo 924580 1756093 := bbase (se 3 (by rfl) ⟨329267, by rfl⟩ : syracuseStep 1756093 = 658535) (by norm_num)
theorem B2083805 : Blo 924580 2083805 := bbase (se 3 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 2083805 = 781427) (by norm_num)
theorem B2640917 : Blo 924580 2640917 := bbase (se 6 (by rfl) ⟨61896, by rfl⟩ : syracuseStep 2640917 = 123793) (by norm_num)
theorem B2083877 : Blo 924580 2083877 := bbase (se 4 (by rfl) ⟨195363, by rfl⟩ : syracuseStep 2083877 = 390727) (by norm_num)
theorem B3132485 : Blo 924580 3132485 := bbase (se 4 (by rfl) ⟨293670, by rfl⟩ : syracuseStep 3132485 = 587341) (by norm_num)
theorem B1756237 : Blo 924580 1756237 := bbase (se 3 (by rfl) ⟨329294, by rfl⟩ : syracuseStep 1756237 = 658589) (by norm_num)
theorem B2083949 : Blo 924580 2083949 := bbase (se 3 (by rfl) ⟨390740, by rfl⟩ : syracuseStep 2083949 = 781481) (by norm_num)
theorem B1428629 : Blo 924580 1428629 := bbase (se 6 (by rfl) ⟨33483, by rfl⟩ : syracuseStep 1428629 = 66967) (by norm_num)
theorem B2084021 : Blo 924580 2084021 := bbase (se 5 (by rfl) ⟨97688, by rfl⟩ : syracuseStep 2084021 = 195377) (by norm_num)
theorem B2346205 : Blo 924580 2346205 := bbase (se 3 (by rfl) ⟨439913, by rfl⟩ : syracuseStep 2346205 = 879827) (by norm_num)
theorem B1756397 : Blo 924580 1756397 := bbase (se 3 (by rfl) ⟨329324, by rfl⟩ : syracuseStep 1756397 = 658649) (by norm_num)
theorem B2084093 : Blo 924580 2084093 := bbase (se 3 (by rfl) ⟨390767, by rfl⟩ : syracuseStep 2084093 = 781535) (by norm_num)
theorem B2641157 : Blo 924580 2641157 := bbase (se 4 (by rfl) ⟨247608, by rfl⟩ : syracuseStep 2641157 = 495217) (by norm_num)
theorem B3755285 : Blo 924580 3755285 := bbase (se 6 (by rfl) ⟨88014, by rfl⟩ : syracuseStep 3755285 = 176029) (by norm_num)
theorem B2084165 : Blo 924580 2084165 := bbase (se 4 (by rfl) ⟨195390, by rfl⟩ : syracuseStep 2084165 = 390781) (by norm_num)
theorem B2346317 : Blo 924580 2346317 := bbase (se 3 (by rfl) ⟨439934, by rfl⟩ : syracuseStep 2346317 = 879869) (by norm_num)
theorem B9522517 : Blo 924580 9522517 := bbase (se 11 (by rfl) ⟨6974, by rfl⟩ : syracuseStep 9522517 = 13949) (by norm_num)
theorem B1756541 : Blo 924580 1756541 := bbase (se 3 (by rfl) ⟨329351, by rfl⟩ : syracuseStep 1756541 = 658703) (by norm_num)
theorem B2084237 : Blo 924580 2084237 := bbase (se 3 (by rfl) ⟨390794, by rfl⟩ : syracuseStep 2084237 = 781589) (by norm_num)
theorem B2641349 : Blo 924580 2641349 := bbase (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) (by norm_num)
theorem B2084309 : Blo 924580 2084309 := bbase (se 7 (by rfl) ⟨24425, by rfl⟩ : syracuseStep 2084309 = 48851) (by norm_num)
theorem B3132917 : Blo 924580 3132917 := bbase (se 5 (by rfl) ⟨146855, by rfl⟩ : syracuseStep 3132917 = 293711) (by norm_num)
theorem B2346509 : Blo 924580 2346509 := bbase (se 3 (by rfl) ⟨439970, by rfl⟩ : syracuseStep 2346509 = 879941) (by norm_num)
theorem B2084381 : Blo 924580 2084381 := bbase (se 3 (by rfl) ⟨390821, by rfl⟩ : syracuseStep 2084381 = 781643) (by norm_num)
theorem B2084453 : Blo 924580 2084453 := bbase (se 4 (by rfl) ⟨195417, by rfl⟩ : syracuseStep 2084453 = 390835) (by norm_num)
theorem B1756829 : Blo 924580 1756829 := bbase (se 3 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 1756829 = 658811) (by norm_num)
theorem B2117285 : Blo 924580 2117285 := bbase (se 4 (by rfl) ⟨198495, by rfl⟩ : syracuseStep 2117285 = 396991) (by norm_num)
theorem B2084525 : Blo 924580 2084525 := bbase (se 3 (by rfl) ⟨390848, by rfl⟩ : syracuseStep 2084525 = 781697) (by norm_num)
theorem B1560269 : Blo 924580 1560269 := bbase (se 3 (by rfl) ⟨292550, by rfl⟩ : syracuseStep 1560269 = 585101) (by norm_num)
theorem B2084597 : Blo 924580 2084597 := bbase (se 5 (by rfl) ⟨97715, by rfl⟩ : syracuseStep 2084597 = 195431) (by norm_num)
theorem B3165973 : Blo 924580 3165973 := bbase (se 6 (by rfl) ⟨74202, by rfl⟩ : syracuseStep 3165973 = 148405) (by norm_num)
theorem B1756981 : Blo 924580 1756981 := bbase (se 5 (by rfl) ⟨82358, by rfl⟩ : syracuseStep 1756981 = 164717) (by norm_num)
theorem B2084669 : Blo 924580 2084669 := bbase (se 3 (by rfl) ⟨390875, by rfl⟩ : syracuseStep 2084669 = 781751) (by norm_num)
theorem B1560397 : Blo 924580 1560397 := bbase (se 3 (by rfl) ⟨292574, by rfl⟩ : syracuseStep 1560397 = 585149) (by norm_num)
theorem B2346853 : Blo 924580 2346853 := bbase (se 4 (by rfl) ⟨220017, by rfl⟩ : syracuseStep 2346853 = 440035) (by norm_num)
theorem B2084741 : Blo 924580 2084741 := bbase (se 4 (by rfl) ⟨195444, by rfl⟩ : syracuseStep 2084741 = 390889) (by norm_num)
theorem B1560485 : Blo 924580 1560485 := bbase (se 4 (by rfl) ⟨146295, by rfl⟩ : syracuseStep 1560485 = 292591) (by norm_num)
theorem B3133349 : Blo 924580 3133349 := bbase (se 4 (by rfl) ⟨293751, by rfl⟩ : syracuseStep 3133349 = 587503) (by norm_num)
theorem B2084813 : Blo 924580 2084813 := bbase (se 3 (by rfl) ⟨390902, by rfl⟩ : syracuseStep 2084813 = 781805) (by norm_num)
theorem B2346965 : Blo 924580 2346965 := bbase (se 7 (by rfl) ⟨27503, by rfl⟩ : syracuseStep 2346965 = 55007) (by norm_num)
theorem B937969 : Blo 924580 937969 := bbase (se 2 (by rfl) ⟨351738, by rfl⟩ : syracuseStep 937969 = 703477) (by norm_num)
theorem B2084885 : Blo 924580 2084885 := bbase (se 6 (by rfl) ⟨48864, by rfl⟩ : syracuseStep 2084885 = 97729) (by norm_num)
theorem B1560613 : Blo 924580 1560613 := bbase (se 4 (by rfl) ⟨146307, by rfl⟩ : syracuseStep 1560613 = 292615) (by norm_num)
theorem B2084957 : Blo 924580 2084957 := bbase (se 3 (by rfl) ⟨390929, by rfl⟩ : syracuseStep 2084957 = 781859) (by norm_num)
theorem B1757285 : Blo 924580 1757285 := bbase (se 4 (by rfl) ⟨164745, by rfl⟩ : syracuseStep 1757285 = 329491) (by norm_num)
theorem B1560701 : Blo 924580 1560701 := bbase (se 3 (by rfl) ⟨292631, by rfl⟩ : syracuseStep 1560701 = 585263) (by norm_num)
theorem B4509829 : Blo 924580 4509829 := bbase (se 4 (by rfl) ⟨422796, by rfl⟩ : syracuseStep 4509829 = 845593) (by norm_num)
theorem B2347157 : Blo 924580 2347157 := bbase (se 6 (by rfl) ⟨55011, by rfl⟩ : syracuseStep 2347157 = 110023) (by norm_num)
theorem B2085029 : Blo 924580 2085029 := bbase (se 4 (by rfl) ⟨195471, by rfl⟩ : syracuseStep 2085029 = 390943) (by norm_num)
theorem B2085101 : Blo 924580 2085101 := bbase (se 3 (by rfl) ⟨390956, by rfl⟩ : syracuseStep 2085101 = 781913) (by norm_num)
theorem B1560829 : Blo 924580 1560829 := bbase (se 3 (by rfl) ⟨292655, by rfl⟩ : syracuseStep 1560829 = 585311) (by norm_num)
theorem B3952901 : Blo 924580 3952901 := bbase (se 4 (by rfl) ⟨370584, by rfl⟩ : syracuseStep 3952901 = 741169) (by norm_num)
theorem B938261 : Blo 924580 938261 := bbase (se 6 (by rfl) ⟨21990, by rfl⟩ : syracuseStep 938261 = 43981) (by norm_num)
theorem B2085173 : Blo 924580 2085173 := bbase (se 5 (by rfl) ⟨97742, by rfl⟩ : syracuseStep 2085173 = 195485) (by norm_num)
theorem B1560917 : Blo 924580 1560917 := bbase (se 10 (by rfl) ⟨2286, by rfl⟩ : syracuseStep 1560917 = 4573) (by norm_num)
theorem B3133781 : Blo 924580 3133781 := bbase (se 10 (by rfl) ⟨4590, by rfl⟩ : syracuseStep 3133781 = 9181) (by norm_num)
theorem B2085245 : Blo 924580 2085245 := bbase (se 3 (by rfl) ⟨390983, by rfl⟩ : syracuseStep 2085245 = 781967) (by norm_num)
theorem B2642341 : Blo 924580 2642341 := bbase (se 4 (by rfl) ⟨247719, by rfl⟩ : syracuseStep 2642341 = 495439) (by norm_num)
theorem B2085317 : Blo 924580 2085317 := bbase (se 4 (by rfl) ⟨195498, by rfl⟩ : syracuseStep 2085317 = 390997) (by norm_num)
theorem B1561045 : Blo 924580 1561045 := bbase (se 7 (by rfl) ⟨18293, by rfl⟩ : syracuseStep 1561045 = 36587) (by norm_num)
theorem B2347501 : Blo 924580 2347501 := bbase (se 3 (by rfl) ⟨440156, by rfl⟩ : syracuseStep 2347501 = 880313) (by norm_num)
theorem B2413061 : Blo 924580 2413061 := bbase (se 4 (by rfl) ⟨226224, by rfl⟩ : syracuseStep 2413061 = 452449) (by norm_num)
theorem B2085389 : Blo 924580 2085389 := bbase (se 3 (by rfl) ⟨391010, by rfl⟩ : syracuseStep 2085389 = 782021) (by norm_num)
theorem B1692181 : Blo 924580 1692181 := bbase (se 6 (by rfl) ⟨39660, by rfl⟩ : syracuseStep 1692181 = 79321) (by norm_num)
theorem B1561133 : Blo 924580 1561133 := bbase (se 3 (by rfl) ⟨292712, by rfl⟩ : syracuseStep 1561133 = 585425) (by norm_num)
theorem B2085461 : Blo 924580 2085461 := bbase (se 8 (by rfl) ⟨12219, by rfl⟩ : syracuseStep 2085461 = 24439) (by norm_num)
theorem B2347613 : Blo 924580 2347613 := bbase (se 3 (by rfl) ⟨440177, by rfl⟩ : syracuseStep 2347613 = 880355) (by norm_num)
theorem B1692269 : Blo 924580 1692269 := bbase (se 3 (by rfl) ⟨317300, by rfl⟩ : syracuseStep 1692269 = 634601) (by norm_num)
theorem B2413165 : Blo 924580 2413165 := bbase (se 3 (by rfl) ⟨452468, by rfl⟩ : syracuseStep 2413165 = 904937) (by norm_num)
theorem B2085533 : Blo 924580 2085533 := bbase (se 3 (by rfl) ⟨391037, by rfl⟩ : syracuseStep 2085533 = 782075) (by norm_num)
theorem B1561261 : Blo 924580 1561261 := bbase (se 3 (by rfl) ⟨292736, by rfl⟩ : syracuseStep 1561261 = 585473) (by norm_num)
theorem B4444901 : Blo 924580 4444901 := bbase (se 4 (by rfl) ⟨416709, by rfl⟩ : syracuseStep 4444901 = 833419) (by norm_num)
theorem B2085605 : Blo 924580 2085605 := bbase (se 4 (by rfl) ⟨195525, by rfl⟩ : syracuseStep 2085605 = 391051) (by norm_num)
theorem B2970341 : Blo 924580 2970341 := bbase (se 4 (by rfl) ⟨278469, by rfl⟩ : syracuseStep 2970341 = 556939) (by norm_num)
theorem B1430245 : Blo 924580 1430245 := bbase (se 4 (by rfl) ⟨134085, by rfl⟩ : syracuseStep 1430245 = 268171) (by norm_num)
theorem B4575989 : Blo 924580 4575989 := bbase (se 5 (by rfl) ⟨214499, by rfl⟩ : syracuseStep 4575989 = 428999) (by norm_num)
theorem B1561349 : Blo 924580 1561349 := bbase (se 4 (by rfl) ⟨146376, by rfl⟩ : syracuseStep 1561349 = 292753) (by norm_num)
theorem B2347805 : Blo 924580 2347805 := bbase (se 3 (by rfl) ⟨440213, by rfl⟩ : syracuseStep 2347805 = 880427) (by norm_num)
theorem B2085677 : Blo 924580 2085677 := bbase (se 3 (by rfl) ⟨391064, by rfl⟩ : syracuseStep 2085677 = 782129) (by norm_num)
theorem B6673205 : Blo 924580 6673205 := bbase (se 5 (by rfl) ⟨312806, by rfl⟩ : syracuseStep 6673205 = 625613) (by norm_num)
theorem B1758037 : Blo 924580 1758037 := bbase (se 9 (by rfl) ⟨5150, by rfl⟩ : syracuseStep 1758037 = 10301) (by norm_num)
theorem B2085749 : Blo 924580 2085749 := bbase (se 5 (by rfl) ⟨97769, by rfl⟩ : syracuseStep 2085749 = 195539) (by norm_num)
theorem B1561477 : Blo 924580 1561477 := bbase (se 4 (by rfl) ⟨146388, by rfl⟩ : syracuseStep 1561477 = 292777) (by norm_num)
theorem B2085821 : Blo 924580 2085821 := bbase (se 3 (by rfl) ⟨391091, by rfl⟩ : syracuseStep 2085821 = 782183) (by norm_num)
theorem B1561565 : Blo 924580 1561565 := bbase (se 3 (by rfl) ⟨292793, by rfl⟩ : syracuseStep 1561565 = 585587) (by norm_num)
theorem B1758181 : Blo 924580 1758181 := bbase (se 4 (by rfl) ⟨164829, by rfl⟩ : syracuseStep 1758181 = 329659) (by norm_num)
theorem B2118637 : Blo 924580 2118637 := bbase (se 3 (by rfl) ⟨397244, by rfl⟩ : syracuseStep 2118637 = 794489) (by norm_num)
theorem B2675717 : Blo 924580 2675717 := bbase (se 4 (by rfl) ⟨250848, by rfl⟩ : syracuseStep 2675717 = 501697) (by norm_num)
theorem B2085893 : Blo 924580 2085893 := bbase (se 4 (by rfl) ⟨195552, by rfl⟩ : syracuseStep 2085893 = 391105) (by norm_num)
theorem B7033877 : Blo 924580 7033877 := bbase (se 6 (by rfl) ⟨164856, by rfl⟩ : syracuseStep 7033877 = 329713) (by norm_num)
theorem B2085965 : Blo 924580 2085965 := bbase (se 3 (by rfl) ⟨391118, by rfl⟩ : syracuseStep 2085965 = 782237) (by norm_num)
theorem B1561693 : Blo 924580 1561693 := bbase (se 3 (by rfl) ⟨292817, by rfl⟩ : syracuseStep 1561693 = 585635) (by norm_num)
theorem B2348149 : Blo 924580 2348149 := bbase (se 5 (by rfl) ⟨110069, by rfl⟩ : syracuseStep 2348149 = 220139) (by norm_num)
theorem B939133 : Blo 924580 939133 := bbase (se 3 (by rfl) ⟨176087, by rfl⟩ : syracuseStep 939133 = 352175) (by norm_num)
theorem B1758341 : Blo 924580 1758341 := bbase (se 4 (by rfl) ⟨164844, by rfl⟩ : syracuseStep 1758341 = 329689) (by norm_num)
theorem B2086037 : Blo 924580 2086037 := bbase (se 6 (by rfl) ⟨48891, by rfl⟩ : syracuseStep 2086037 = 97783) (by norm_num)
theorem B1004713 : Blo 924580 1004713 := bbase (se 2 (by rfl) ⟨376767, by rfl⟩ : syracuseStep 1004713 = 753535) (by norm_num)
theorem B1561781 : Blo 924580 1561781 := bbase (se 5 (by rfl) ⟨73208, by rfl⟩ : syracuseStep 1561781 = 146417) (by norm_num)
theorem B2086109 : Blo 924580 2086109 := bbase (se 3 (by rfl) ⟨391145, by rfl⟩ : syracuseStep 2086109 = 782291) (by norm_num)
theorem B2348261 : Blo 924580 2348261 := bbase (se 4 (by rfl) ⟨220149, by rfl⟩ : syracuseStep 2348261 = 440299) (by norm_num)
theorem B1758485 : Blo 924580 1758485 := bbase (se 6 (by rfl) ⟨41214, by rfl⟩ : syracuseStep 1758485 = 82429) (by norm_num)
theorem B2086181 : Blo 924580 2086181 := bbase (se 4 (by rfl) ⟨195579, by rfl⟩ : syracuseStep 2086181 = 391159) (by norm_num)
theorem B1561909 : Blo 924580 1561909 := bbase (se 5 (by rfl) ⟨73214, by rfl⟩ : syracuseStep 1561909 = 146429) (by norm_num)
theorem B2086253 : Blo 924580 2086253 := bbase (se 3 (by rfl) ⟨391172, by rfl⟩ : syracuseStep 2086253 = 782345) (by norm_num)
theorem B1561997 : Blo 924580 1561997 := bbase (se 3 (by rfl) ⟨292874, by rfl⟩ : syracuseStep 1561997 = 585749) (by norm_num)
theorem B2348453 : Blo 924580 2348453 := bbase (se 4 (by rfl) ⟨220167, by rfl⟩ : syracuseStep 2348453 = 440335) (by norm_num)
theorem B2086325 : Blo 924580 2086325 := bbase (se 5 (by rfl) ⟨97796, by rfl⟩ : syracuseStep 2086325 = 195593) (by norm_num)
theorem B1070537 : Blo 924580 1070537 := bbase (se 2 (by rfl) ⟨401451, by rfl⟩ : syracuseStep 1070537 = 802903) (by norm_num)
theorem B2643445 : Blo 924580 2643445 := bbase (se 5 (by rfl) ⟨123911, by rfl⟩ : syracuseStep 2643445 = 247823) (by norm_num)
theorem B2086397 : Blo 924580 2086397 := bbase (se 3 (by rfl) ⟨391199, by rfl⟩ : syracuseStep 2086397 = 782399) (by norm_num)
theorem B1562125 : Blo 924580 1562125 := bbase (se 3 (by rfl) ⟨292898, by rfl⟩ : syracuseStep 1562125 = 585797) (by norm_num)
theorem B1758773 : Blo 924580 1758773 := bbase (se 5 (by rfl) ⟨82442, by rfl⟩ : syracuseStep 1758773 = 164885) (by norm_num)
theorem B2086469 : Blo 924580 2086469 := bbase (se 4 (by rfl) ⟨195606, by rfl⟩ : syracuseStep 2086469 = 391213) (by norm_num)
theorem B1562213 : Blo 924580 1562213 := bbase (se 4 (by rfl) ⟨146457, by rfl⟩ : syracuseStep 1562213 = 292915) (by norm_num)
theorem B2971237 : Blo 924580 2971237 := bbase (se 4 (by rfl) ⟨278553, by rfl⟩ : syracuseStep 2971237 = 557107) (by norm_num)
theorem B2086541 : Blo 924580 2086541 := bbase (se 3 (by rfl) ⟨391226, by rfl⟩ : syracuseStep 2086541 = 782453) (by norm_num)
theorem B4019861 : Blo 924580 4019861 := bbase (se 6 (by rfl) ⟨94215, by rfl⟩ : syracuseStep 4019861 = 188431) (by norm_num)
theorem B1758925 : Blo 924580 1758925 := bbase (se 3 (by rfl) ⟨329798, by rfl⟩ : syracuseStep 1758925 = 659597) (by norm_num)
theorem B2086613 : Blo 924580 2086613 := bbase (se 7 (by rfl) ⟨24452, by rfl⟩ : syracuseStep 2086613 = 48905) (by norm_num)
theorem B1562341 : Blo 924580 1562341 := bbase (se 4 (by rfl) ⟨146469, by rfl⟩ : syracuseStep 1562341 = 292939) (by norm_num)
theorem B2348797 : Blo 924580 2348797 := bbase (se 3 (by rfl) ⟨440399, by rfl⟩ : syracuseStep 2348797 = 880799) (by norm_num)
theorem B2086685 : Blo 924580 2086685 := bbase (se 3 (by rfl) ⟨391253, by rfl⟩ : syracuseStep 2086685 = 782507) (by norm_num)
theorem B1562429 : Blo 924580 1562429 := bbase (se 3 (by rfl) ⟨292955, by rfl⟩ : syracuseStep 1562429 = 585911) (by norm_num)
theorem B4446053 : Blo 924580 4446053 := bbase (se 4 (by rfl) ⟨416817, by rfl⟩ : syracuseStep 4446053 = 833635) (by norm_num)
theorem B2086757 : Blo 924580 2086757 := bbase (se 4 (by rfl) ⟨195633, by rfl⟩ : syracuseStep 2086757 = 391267) (by norm_num)
theorem B2348909 : Blo 924580 2348909 := bbase (se 3 (by rfl) ⟨440420, by rfl⟩ : syracuseStep 2348909 = 880841) (by norm_num)
theorem B2086829 : Blo 924580 2086829 := bbase (se 3 (by rfl) ⟨391280, by rfl⟩ : syracuseStep 2086829 = 782561) (by norm_num)
theorem B1562557 : Blo 924580 1562557 := bbase (se 3 (by rfl) ⟨292979, by rfl⟩ : syracuseStep 1562557 = 585959) (by norm_num)
theorem B2086901 : Blo 924580 2086901 := bbase (se 5 (by rfl) ⟨97823, by rfl⟩ : syracuseStep 2086901 = 195647) (by norm_num)
theorem B1759229 : Blo 924580 1759229 := bbase (se 3 (by rfl) ⟨329855, by rfl⟩ : syracuseStep 1759229 = 659711) (by norm_num)
theorem B1562645 : Blo 924580 1562645 := bbase (se 6 (by rfl) ⟨36624, by rfl⟩ : syracuseStep 1562645 = 73249) (by norm_num)
theorem B2349101 : Blo 924580 2349101 := bbase (se 3 (by rfl) ⟨440456, by rfl⟩ : syracuseStep 2349101 = 880913) (by norm_num)
theorem B2086973 : Blo 924580 2086973 := bbase (se 3 (by rfl) ⟨391307, by rfl⟩ : syracuseStep 2086973 = 782615) (by norm_num)
theorem B2087045 : Blo 924580 2087045 := bbase (se 4 (by rfl) ⟨195660, by rfl⟩ : syracuseStep 2087045 = 391321) (by norm_num)
theorem B1562773 : Blo 924580 1562773 := bbase (se 6 (by rfl) ⟨36627, by rfl⟩ : syracuseStep 1562773 = 73255) (by norm_num)
theorem B2087117 : Blo 924580 2087117 := bbase (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) (by norm_num)
theorem B1562861 : Blo 924580 1562861 := bbase (se 3 (by rfl) ⟨293036, by rfl⟩ : syracuseStep 1562861 = 586073) (by norm_num)
theorem B2087189 : Blo 924580 2087189 := bbase (se 6 (by rfl) ⟨48918, by rfl⟩ : syracuseStep 2087189 = 97837) (by norm_num)
theorem B2087261 : Blo 924580 2087261 := bbase (se 3 (by rfl) ⟨391361, by rfl⟩ : syracuseStep 2087261 = 782723) (by norm_num)
theorem B1562989 : Blo 924580 1562989 := bbase (se 3 (by rfl) ⟨293060, by rfl⟩ : syracuseStep 1562989 = 586121) (by norm_num)
theorem B2349445 : Blo 924580 2349445 := bbase (se 4 (by rfl) ⟨220260, by rfl⟩ : syracuseStep 2349445 = 440521) (by norm_num)
theorem B2087333 : Blo 924580 2087333 := bbase (se 4 (by rfl) ⟨195687, by rfl⟩ : syracuseStep 2087333 = 391375) (by norm_num)
theorem B1563077 : Blo 924580 1563077 := bbase (se 4 (by rfl) ⟨146538, by rfl⟩ : syracuseStep 1563077 = 293077) (by norm_num)
theorem B2087405 : Blo 924580 2087405 := bbase (se 3 (by rfl) ⟨391388, by rfl⟩ : syracuseStep 2087405 = 782777) (by norm_num)
theorem B2349557 : Blo 924580 2349557 := bbase (se 5 (by rfl) ⟨110135, by rfl⟩ : syracuseStep 2349557 = 220271) (by norm_num)
theorem B2382365 : Blo 924580 2382365 := bbase (se 3 (by rfl) ⟨446693, by rfl⟩ : syracuseStep 2382365 = 893387) (by norm_num)
theorem B2087477 : Blo 924580 2087477 := bbase (se 5 (by rfl) ⟨97850, by rfl⟩ : syracuseStep 2087477 = 195701) (by norm_num)
theorem B1563205 : Blo 924580 1563205 := bbase (se 4 (by rfl) ⟨146550, by rfl⟩ : syracuseStep 1563205 = 293101) (by norm_num)
theorem B4446821 : Blo 924580 4446821 := bbase (se 4 (by rfl) ⟨416889, by rfl⟩ : syracuseStep 4446821 = 833779) (by norm_num)
theorem B940645 : Blo 924580 940645 := bbase (se 4 (by rfl) ⟨88185, by rfl⟩ : syracuseStep 940645 = 176371) (by norm_num)
theorem B2087549 : Blo 924580 2087549 := bbase (se 3 (by rfl) ⟨391415, by rfl⟩ : syracuseStep 2087549 = 782831) (by norm_num)
theorem B1563293 : Blo 924580 1563293 := bbase (se 3 (by rfl) ⟨293117, by rfl⟩ : syracuseStep 1563293 = 586235) (by norm_num)
theorem B2349749 : Blo 924580 2349749 := bbase (se 5 (by rfl) ⟨110144, by rfl⟩ : syracuseStep 2349749 = 220289) (by norm_num)
theorem B2087621 : Blo 924580 2087621 := bbase (se 4 (by rfl) ⟨195714, by rfl⟩ : syracuseStep 2087621 = 391429) (by norm_num)
theorem B1759981 : Blo 924580 1759981 := bbase (se 3 (by rfl) ⟨329996, by rfl⟩ : syracuseStep 1759981 = 659993) (by norm_num)
theorem B2087693 : Blo 924580 2087693 := bbase (se 3 (by rfl) ⟨391442, by rfl⟩ : syracuseStep 2087693 = 782885) (by norm_num)
theorem B1563421 : Blo 924580 1563421 := bbase (se 3 (by rfl) ⟨293141, by rfl⟩ : syracuseStep 1563421 = 586283) (by norm_num)
theorem B1170217 : Blo 924580 1170217 := bbase (se 2 (by rfl) ⟨438831, by rfl⟩ : syracuseStep 1170217 = 877663) (by norm_num)
theorem B2087765 : Blo 924580 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B1563509 : Blo 924580 1563509 := bbase (se 5 (by rfl) ⟨73289, by rfl⟩ : syracuseStep 1563509 = 146579) (by norm_num)
theorem B1760125 : Blo 924580 1760125 := bbase (se 3 (by rfl) ⟨330023, by rfl⟩ : syracuseStep 1760125 = 660047) (by norm_num)
theorem B2087837 : Blo 924580 2087837 := bbase (se 3 (by rfl) ⟨391469, by rfl⟩ : syracuseStep 2087837 = 782939) (by norm_num)
theorem B1170389 : Blo 924580 1170389 := bbase (se 7 (by rfl) ⟨13715, by rfl⟩ : syracuseStep 1170389 = 27431) (by norm_num)
theorem B2087909 : Blo 924580 2087909 := bbase (se 4 (by rfl) ⟨195741, by rfl⟩ : syracuseStep 2087909 = 391483) (by norm_num)
theorem B1563637 : Blo 924580 1563637 := bbase (se 5 (by rfl) ⟨73295, by rfl⟩ : syracuseStep 1563637 = 146591) (by norm_num)
theorem B1170445 : Blo 924580 1170445 := bbase (se 3 (by rfl) ⟨219458, by rfl⟩ : syracuseStep 1170445 = 438917) (by norm_num)
theorem B2350093 : Blo 924580 2350093 := bbase (se 3 (by rfl) ⟨440642, by rfl⟩ : syracuseStep 2350093 = 881285) (by norm_num)
theorem B1760285 : Blo 924580 1760285 := bbase (se 3 (by rfl) ⟨330053, by rfl⟩ : syracuseStep 1760285 = 660107) (by norm_num)
theorem B2087981 : Blo 924580 2087981 := bbase (se 3 (by rfl) ⟨391496, by rfl⟩ : syracuseStep 2087981 = 782993) (by norm_num)
theorem B1563725 : Blo 924580 1563725 := bbase (se 3 (by rfl) ⟨293198, by rfl⟩ : syracuseStep 1563725 = 586397) (by norm_num)
theorem B1170541 : Blo 924580 1170541 := bbase (se 3 (by rfl) ⟨219476, by rfl⟩ : syracuseStep 1170541 = 438953) (by norm_num)
theorem B2088053 : Blo 924580 2088053 := bbase (se 5 (by rfl) ⟨97877, by rfl⟩ : syracuseStep 2088053 = 195755) (by norm_num)
theorem B941177 : Blo 924580 941177 := bbase (se 2 (by rfl) ⟨352941, by rfl⟩ : syracuseStep 941177 = 705883) (by norm_num)
theorem B2350205 : Blo 924580 2350205 := bbase (se 3 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 2350205 = 881327) (by norm_num)
theorem B1760429 : Blo 924580 1760429 := bbase (se 3 (by rfl) ⟨330080, by rfl⟩ : syracuseStep 1760429 = 660161) (by norm_num)
theorem B2088125 : Blo 924580 2088125 := bbase (se 3 (by rfl) ⟨391523, by rfl⟩ : syracuseStep 2088125 = 783047) (by norm_num)
theorem B3169477 : Blo 924580 3169477 := bbase (se 4 (by rfl) ⟨297138, by rfl⟩ : syracuseStep 3169477 = 594277) (by norm_num)
theorem B1563853 : Blo 924580 1563853 := bbase (se 3 (by rfl) ⟨293222, by rfl⟩ : syracuseStep 1563853 = 586445) (by norm_num)
theorem B2088197 : Blo 924580 2088197 := bbase (se 4 (by rfl) ⟨195768, by rfl⟩ : syracuseStep 2088197 = 391537) (by norm_num)
theorem B1170713 : Blo 924580 1170713 := bbase (se 2 (by rfl) ⟨439017, by rfl⟩ : syracuseStep 1170713 = 878035) (by norm_num)
theorem B1563941 : Blo 924580 1563941 := bbase (se 4 (by rfl) ⟨146619, by rfl⟩ : syracuseStep 1563941 = 293239) (by norm_num)
theorem B2350397 : Blo 924580 2350397 := bbase (se 3 (by rfl) ⟨440699, by rfl⟩ : syracuseStep 2350397 = 881399) (by norm_num)
theorem B2088269 : Blo 924580 2088269 := bbase (se 3 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 2088269 = 783101) (by norm_num)
theorem B1170769 : Blo 924580 1170769 := bbase (se 2 (by rfl) ⟨439038, by rfl⟩ : syracuseStep 1170769 = 878077) (by norm_num)
theorem B57105749 : Blo 924580 57105749 := bbase (se 11 (by rfl) ⟨41825, by rfl⟩ : syracuseStep 57105749 = 83651) (by norm_num)
theorem B13557077 : Blo 924580 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B2088341 : Blo 924580 2088341 := bbase (se 6 (by rfl) ⟨48945, by rfl⟩ : syracuseStep 2088341 = 97891) (by norm_num)
theorem B1564069 : Blo 924580 1564069 := bbase (se 4 (by rfl) ⟨146631, by rfl⟩ : syracuseStep 1564069 = 293263) (by norm_num)
theorem B1170865 : Blo 924580 1170865 := bbase (se 2 (by rfl) ⟨439074, by rfl⟩ : syracuseStep 1170865 = 878149) (by norm_num)
theorem B1760717 : Blo 924580 1760717 := bbase (se 3 (by rfl) ⟨330134, by rfl⟩ : syracuseStep 1760717 = 660269) (by norm_num)
theorem B2088413 : Blo 924580 2088413 := bbase (se 3 (by rfl) ⟨391577, by rfl⟩ : syracuseStep 2088413 = 783155) (by norm_num)
theorem B1564157 : Blo 924580 1564157 := bbase (se 3 (by rfl) ⟨293279, by rfl⟩ : syracuseStep 1564157 = 586559) (by norm_num)
theorem B2088485 : Blo 924580 2088485 := bbase (se 4 (by rfl) ⟨195795, by rfl⟩ : syracuseStep 2088485 = 391591) (by norm_num)
theorem B1171037 : Blo 924580 1171037 := bbase (se 3 (by rfl) ⟨219569, by rfl⟩ : syracuseStep 1171037 = 439139) (by norm_num)
theorem B1760869 : Blo 924580 1760869 := bbase (se 4 (by rfl) ⟨165081, by rfl⟩ : syracuseStep 1760869 = 330163) (by norm_num)
theorem B2088557 : Blo 924580 2088557 := bbase (se 3 (by rfl) ⟨391604, by rfl⟩ : syracuseStep 2088557 = 783209) (by norm_num)
theorem B1564285 : Blo 924580 1564285 := bbase (se 3 (by rfl) ⟨293303, by rfl⟩ : syracuseStep 1564285 = 586607) (by norm_num)
theorem B1171093 : Blo 924580 1171093 := bbase (se 6 (by rfl) ⟨27447, by rfl⟩ : syracuseStep 1171093 = 54895) (by norm_num)
theorem B2088629 : Blo 924580 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B1564373 : Blo 924580 1564373 := bbase (se 7 (by rfl) ⟨18332, by rfl⟩ : syracuseStep 1564373 = 36665) (by norm_num)
theorem B1171189 : Blo 924580 1171189 := bbase (se 5 (by rfl) ⟨54899, by rfl⟩ : syracuseStep 1171189 = 109799) (by norm_num)
theorem B2088701 : Blo 924580 2088701 := bbase (se 3 (by rfl) ⟨391631, by rfl⟩ : syracuseStep 2088701 = 783263) (by norm_num)
theorem B1040161 : Blo 924580 1040161 := bbase (se 2 (by rfl) ⟨390060, by rfl⟩ : syracuseStep 1040161 = 780121) (by norm_num)
theorem B1040197 : Blo 924580 1040197 := bbase (se 4 (by rfl) ⟨97518, by rfl⟩ : syracuseStep 1040197 = 195037) (by norm_num)
theorem B2088773 : Blo 924580 2088773 := bbase (se 4 (by rfl) ⟨195822, by rfl⟩ : syracuseStep 2088773 = 391645) (by norm_num)
theorem B1564501 : Blo 924580 1564501 := bbase (se 9 (by rfl) ⟨4583, by rfl⟩ : syracuseStep 1564501 = 9167) (by norm_num)
theorem B1040233 : Blo 924580 1040233 := bbase (se 2 (by rfl) ⟨390087, by rfl⟩ : syracuseStep 1040233 = 780175) (by norm_num)
theorem B1040269 : Blo 924580 1040269 := bbase (se 3 (by rfl) ⟨195050, by rfl⟩ : syracuseStep 1040269 = 390101) (by norm_num)
theorem B2088845 : Blo 924580 2088845 := bbase (se 3 (by rfl) ⟨391658, by rfl⟩ : syracuseStep 2088845 = 783317) (by norm_num)
theorem B1761173 : Blo 924580 1761173 := bbase (se 6 (by rfl) ⟨41277, by rfl⟩ : syracuseStep 1761173 = 82555) (by norm_num)
theorem B1171361 : Blo 924580 1171361 := bbase (se 2 (by rfl) ⟨439260, by rfl⟩ : syracuseStep 1171361 = 878521) (by norm_num)
theorem B1564589 : Blo 924580 1564589 := bbase (se 3 (by rfl) ⟨293360, by rfl⟩ : syracuseStep 1564589 = 586721) (by norm_num)
theorem B1040305 : Blo 924580 1040305 := bbase (se 2 (by rfl) ⟨390114, by rfl⟩ : syracuseStep 1040305 = 780229) (by norm_num)
theorem B3170245 : Blo 924580 3170245 := bbase (se 4 (by rfl) ⟨297210, by rfl⟩ : syracuseStep 3170245 = 594421) (by norm_num)
theorem B1040341 : Blo 924580 1040341 := bbase (se 7 (by rfl) ⟨12191, by rfl⟩ : syracuseStep 1040341 = 24383) (by norm_num)
theorem B2088917 : Blo 924580 2088917 := bbase (se 7 (by rfl) ⟨24479, by rfl⟩ : syracuseStep 2088917 = 48959) (by norm_num)
theorem B1171417 : Blo 924580 1171417 := bbase (se 2 (by rfl) ⟨439281, by rfl⟩ : syracuseStep 1171417 = 878563) (by norm_num)
theorem B1040377 : Blo 924580 1040377 := bbase (se 2 (by rfl) ⟨390141, by rfl⟩ : syracuseStep 1040377 = 780283) (by norm_num)
theorem B1040413 : Blo 924580 1040413 := bbase (se 3 (by rfl) ⟨195077, by rfl⟩ : syracuseStep 1040413 = 390155) (by norm_num)
theorem B2088989 : Blo 924580 2088989 := bbase (se 3 (by rfl) ⟨391685, by rfl⟩ : syracuseStep 2088989 = 783371) (by norm_num)
theorem B1564717 : Blo 924580 1564717 := bbase (se 3 (by rfl) ⟨293384, by rfl⟩ : syracuseStep 1564717 = 586769) (by norm_num)
theorem B1171513 : Blo 924580 1171513 := bbase (se 2 (by rfl) ⟨439317, by rfl⟩ : syracuseStep 1171513 = 878635) (by norm_num)
theorem B1040449 : Blo 924580 1040449 := bbase (se 2 (by rfl) ⟨390168, by rfl⟩ : syracuseStep 1040449 = 780337) (by norm_num)
theorem B1040485 : Blo 924580 1040485 := bbase (se 4 (by rfl) ⟨97545, by rfl⟩ : syracuseStep 1040485 = 195091) (by norm_num)
theorem B2089061 : Blo 924580 2089061 := bbase (se 4 (by rfl) ⟨195849, by rfl⟩ : syracuseStep 2089061 = 391699) (by norm_num)
theorem B2252909 : Blo 924580 2252909 := bbase (se 3 (by rfl) ⟨422420, by rfl⟩ : syracuseStep 2252909 = 844841) (by norm_num)
theorem B1564805 : Blo 924580 1564805 := bbase (se 4 (by rfl) ⟨146700, by rfl⟩ : syracuseStep 1564805 = 293401) (by norm_num)
theorem B1040521 : Blo 924580 1040521 := bbase (se 2 (by rfl) ⟨390195, by rfl⟩ : syracuseStep 1040521 = 780391) (by norm_num)
theorem B1040557 : Blo 924580 1040557 := bbase (se 3 (by rfl) ⟨195104, by rfl⟩ : syracuseStep 1040557 = 390209) (by norm_num)
theorem B2089133 : Blo 924580 2089133 := bbase (se 3 (by rfl) ⟨391712, by rfl⟩ : syracuseStep 2089133 = 783425) (by norm_num)
theorem B1040593 : Blo 924580 1040593 := bbase (se 2 (by rfl) ⟨390222, by rfl⟩ : syracuseStep 1040593 = 780445) (by norm_num)
theorem B1171685 : Blo 924580 1171685 := bbase (se 4 (by rfl) ⟨109845, by rfl⟩ : syracuseStep 1171685 = 219691) (by norm_num)
theorem B1040629 : Blo 924580 1040629 := bbase (se 5 (by rfl) ⟨48779, by rfl⟩ : syracuseStep 1040629 = 97559) (by norm_num)
theorem B2089205 : Blo 924580 2089205 := bbase (se 5 (by rfl) ⟨97931, by rfl⟩ : syracuseStep 2089205 = 195863) (by norm_num)
theorem B1564933 : Blo 924580 1564933 := bbase (se 4 (by rfl) ⟨146712, by rfl⟩ : syracuseStep 1564933 = 293425) (by norm_num)
theorem B1040665 : Blo 924580 1040665 := bbase (se 2 (by rfl) ⟨390249, by rfl⟩ : syracuseStep 1040665 = 780499) (by norm_num)
theorem B1171741 : Blo 924580 1171741 := bbase (se 3 (by rfl) ⟨219701, by rfl⟩ : syracuseStep 1171741 = 439403) (by norm_num)
theorem B1040701 : Blo 924580 1040701 := bbase (se 3 (by rfl) ⟨195131, by rfl⟩ : syracuseStep 1040701 = 390263) (by norm_num)
theorem B2089277 : Blo 924580 2089277 := bbase (se 3 (by rfl) ⟨391739, by rfl⟩ : syracuseStep 2089277 = 783479) (by norm_num)
theorem B1565021 : Blo 924580 1565021 := bbase (se 3 (by rfl) ⟨293441, by rfl⟩ : syracuseStep 1565021 = 586883) (by norm_num)
theorem B1040737 : Blo 924580 1040737 := bbase (se 2 (by rfl) ⟨390276, by rfl⟩ : syracuseStep 1040737 = 780553) (by norm_num)
theorem B1171837 : Blo 924580 1171837 := bbase (se 3 (by rfl) ⟨219719, by rfl⟩ : syracuseStep 1171837 = 439439) (by norm_num)
theorem B1040773 : Blo 924580 1040773 := bbase (se 4 (by rfl) ⟨97572, by rfl⟩ : syracuseStep 1040773 = 195145) (by norm_num)
theorem B1040809 : Blo 924580 1040809 := bbase (se 2 (by rfl) ⟨390303, by rfl⟩ : syracuseStep 1040809 = 780607) (by norm_num)
theorem B3957173 : Blo 924580 3957173 := bbase (se 5 (by rfl) ⟨185492, by rfl⟩ : syracuseStep 3957173 = 370985) (by norm_num)
theorem B2974133 : Blo 924580 2974133 := bbase (se 5 (by rfl) ⟨139412, by rfl⟩ : syracuseStep 2974133 = 278825) (by norm_num)
theorem B1040845 : Blo 924580 1040845 := bbase (se 3 (by rfl) ⟨195158, by rfl⟩ : syracuseStep 1040845 = 390317) (by norm_num)
theorem B1565149 : Blo 924580 1565149 := bbase (se 3 (by rfl) ⟨293465, by rfl⟩ : syracuseStep 1565149 = 586931) (by norm_num)
theorem B1335781 : Blo 924580 1335781 := bbase (se 4 (by rfl) ⟨125229, by rfl⟩ : syracuseStep 1335781 = 250459) (by norm_num)
theorem B1040881 : Blo 924580 1040881 := bbase (se 2 (by rfl) ⟨390330, by rfl⟩ : syracuseStep 1040881 = 780661) (by norm_num)
theorem B1040917 : Blo 924580 1040917 := bbase (se 6 (by rfl) ⟨24396, by rfl⟩ : syracuseStep 1040917 = 48793) (by norm_num)
theorem B2253349 : Blo 924580 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B1172009 : Blo 924580 1172009 := bbase (se 2 (by rfl) ⟨439503, by rfl⟩ : syracuseStep 1172009 = 879007) (by norm_num)
theorem B1565237 : Blo 924580 1565237 := bbase (se 5 (by rfl) ⟨73370, by rfl⟩ : syracuseStep 1565237 = 146741) (by norm_num)
theorem B1040953 : Blo 924580 1040953 := bbase (se 2 (by rfl) ⟨390357, by rfl⟩ : syracuseStep 1040953 = 780715) (by norm_num)
theorem B1040989 : Blo 924580 1040989 := bbase (se 3 (by rfl) ⟨195185, by rfl⟩ : syracuseStep 1040989 = 390371) (by norm_num)
theorem B1172065 : Blo 924580 1172065 := bbase (se 2 (by rfl) ⟨439524, by rfl⟩ : syracuseStep 1172065 = 879049) (by norm_num)
theorem B1041025 : Blo 924580 1041025 := bbase (se 2 (by rfl) ⟨390384, by rfl⟩ : syracuseStep 1041025 = 780769) (by norm_num)
theorem B1761925 : Blo 924580 1761925 := bbase (se 4 (by rfl) ⟨165180, by rfl⟩ : syracuseStep 1761925 = 330361) (by norm_num)
theorem B1041061 : Blo 924580 1041061 := bbase (se 4 (by rfl) ⟨97599, by rfl⟩ : syracuseStep 1041061 = 195199) (by norm_num)
theorem B1565365 : Blo 924580 1565365 := bbase (se 5 (by rfl) ⟨73376, by rfl⟩ : syracuseStep 1565365 = 146753) (by norm_num)
theorem B1172161 : Blo 924580 1172161 := bbase (se 2 (by rfl) ⟨439560, by rfl⟩ : syracuseStep 1172161 = 879121) (by norm_num)
theorem B1041097 : Blo 924580 1041097 := bbase (se 2 (by rfl) ⟨390411, by rfl⟩ : syracuseStep 1041097 = 780823) (by norm_num)
theorem B1041133 : Blo 924580 1041133 := bbase (se 3 (by rfl) ⟨195212, by rfl⟩ : syracuseStep 1041133 = 390425) (by norm_num)
theorem B1565453 : Blo 924580 1565453 := bbase (se 3 (by rfl) ⟨293522, by rfl⟩ : syracuseStep 1565453 = 587045) (by norm_num)
theorem B1041169 : Blo 924580 1041169 := bbase (se 2 (by rfl) ⟨390438, by rfl⟩ : syracuseStep 1041169 = 780877) (by norm_num)
theorem B1762069 : Blo 924580 1762069 := bbase (se 6 (by rfl) ⟨41298, by rfl⟩ : syracuseStep 1762069 = 82597) (by norm_num)
theorem B1336109 : Blo 924580 1336109 := bbase (se 3 (by rfl) ⟨250520, by rfl⟩ : syracuseStep 1336109 = 501041) (by norm_num)
theorem B1041205 : Blo 924580 1041205 := bbase (se 5 (by rfl) ⟨48806, by rfl⟩ : syracuseStep 1041205 = 97613) (by norm_num)
theorem B1041241 : Blo 924580 1041241 := bbase (se 2 (by rfl) ⟨390465, by rfl⟩ : syracuseStep 1041241 = 780931) (by norm_num)
theorem B1172333 : Blo 924580 1172333 := bbase (se 3 (by rfl) ⟨219812, by rfl⟩ : syracuseStep 1172333 = 439625) (by norm_num)
theorem B1041277 : Blo 924580 1041277 := bbase (se 3 (by rfl) ⟨195239, by rfl⟩ : syracuseStep 1041277 = 390479) (by norm_num)
theorem B1565581 : Blo 924580 1565581 := bbase (se 3 (by rfl) ⟨293546, by rfl⟩ : syracuseStep 1565581 = 587093) (by norm_num)
theorem B1041313 : Blo 924580 1041313 := bbase (se 2 (by rfl) ⟨390492, by rfl⟩ : syracuseStep 1041313 = 780985) (by norm_num)
theorem B1172389 : Blo 924580 1172389 := bbase (se 4 (by rfl) ⟨109911, by rfl⟩ : syracuseStep 1172389 = 219823) (by norm_num)
theorem B1762229 : Blo 924580 1762229 := bbase (se 5 (by rfl) ⟨82604, by rfl⟩ : syracuseStep 1762229 = 165209) (by norm_num)
theorem B1041349 : Blo 924580 1041349 := bbase (se 4 (by rfl) ⟨97626, by rfl⟩ : syracuseStep 1041349 = 195253) (by norm_num)
theorem B1565669 : Blo 924580 1565669 := bbase (se 4 (by rfl) ⟨146781, by rfl⟩ : syracuseStep 1565669 = 293563) (by norm_num)
theorem B1041385 : Blo 924580 1041385 := bbase (se 2 (by rfl) ⟨390519, by rfl⟩ : syracuseStep 1041385 = 781039) (by norm_num)
theorem B1172485 : Blo 924580 1172485 := bbase (se 4 (by rfl) ⟨109920, by rfl⟩ : syracuseStep 1172485 = 219841) (by norm_num)
theorem B1041421 : Blo 924580 1041421 := bbase (se 3 (by rfl) ⟨195266, by rfl⟩ : syracuseStep 1041421 = 390533) (by norm_num)
theorem B1041457 : Blo 924580 1041457 := bbase (se 2 (by rfl) ⟨390546, by rfl⟩ : syracuseStep 1041457 = 781093) (by norm_num)
theorem B1762373 : Blo 924580 1762373 := bbase (se 4 (by rfl) ⟨165222, by rfl⟩ : syracuseStep 1762373 = 330445) (by norm_num)
theorem B1041493 : Blo 924580 1041493 := bbase (se 8 (by rfl) ⟨6102, by rfl⟩ : syracuseStep 1041493 = 12205) (by norm_num)
theorem B1565797 : Blo 924580 1565797 := bbase (se 4 (by rfl) ⟨146793, by rfl⟩ : syracuseStep 1565797 = 293587) (by norm_num)
theorem B1041529 : Blo 924580 1041529 := bbase (se 2 (by rfl) ⟨390573, by rfl⟩ : syracuseStep 1041529 = 781147) (by norm_num)
theorem B1041565 : Blo 924580 1041565 := bbase (se 3 (by rfl) ⟨195293, by rfl⟩ : syracuseStep 1041565 = 390587) (by norm_num)
theorem B1172657 : Blo 924580 1172657 := bbase (se 2 (by rfl) ⟨439746, by rfl⟩ : syracuseStep 1172657 = 879493) (by norm_num)
theorem B1565885 : Blo 924580 1565885 := bbase (se 3 (by rfl) ⟨293603, by rfl⟩ : syracuseStep 1565885 = 587207) (by norm_num)
theorem B1041601 : Blo 924580 1041601 := bbase (se 2 (by rfl) ⟨390600, by rfl⟩ : syracuseStep 1041601 = 781201) (by norm_num)
theorem B1041637 : Blo 924580 1041637 := bbase (se 4 (by rfl) ⟨97653, by rfl⟩ : syracuseStep 1041637 = 195307) (by norm_num)
theorem B1172713 : Blo 924580 1172713 := bbase (se 2 (by rfl) ⟨439767, by rfl⟩ : syracuseStep 1172713 = 879535) (by norm_num)
theorem B2254061 : Blo 924580 2254061 := bbase (se 3 (by rfl) ⟨422636, by rfl⟩ : syracuseStep 2254061 = 845273) (by norm_num)
theorem B1041673 : Blo 924580 1041673 := bbase (se 2 (by rfl) ⟨390627, by rfl⟩ : syracuseStep 1041673 = 781255) (by norm_num)
theorem B1041709 : Blo 924580 1041709 := bbase (se 3 (by rfl) ⟨195320, by rfl⟩ : syracuseStep 1041709 = 390641) (by norm_num)
theorem B1566013 : Blo 924580 1566013 := bbase (se 3 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 1566013 = 587255) (by norm_num)
theorem B1172809 : Blo 924580 1172809 := bbase (se 2 (by rfl) ⟨439803, by rfl⟩ : syracuseStep 1172809 = 879607) (by norm_num)
theorem B1041745 : Blo 924580 1041745 := bbase (se 2 (by rfl) ⟨390654, by rfl⟩ : syracuseStep 1041745 = 781309) (by norm_num)
theorem B1762661 : Blo 924580 1762661 := bbase (se 4 (by rfl) ⟨165249, by rfl⟩ : syracuseStep 1762661 = 330499) (by norm_num)
theorem B1041781 : Blo 924580 1041781 := bbase (se 5 (by rfl) ⟨48833, by rfl⟩ : syracuseStep 1041781 = 97667) (by norm_num)
theorem B1566101 : Blo 924580 1566101 := bbase (se 6 (by rfl) ⟨36705, by rfl⟩ : syracuseStep 1566101 = 73411) (by norm_num)
theorem B1041817 : Blo 924580 1041817 := bbase (se 2 (by rfl) ⟨390681, by rfl⟩ : syracuseStep 1041817 = 781363) (by norm_num)
theorem B1041853 : Blo 924580 1041853 := bbase (se 3 (by rfl) ⟨195347, by rfl⟩ : syracuseStep 1041853 = 390695) (by norm_num)
theorem B1041889 : Blo 924580 1041889 := bbase (se 2 (by rfl) ⟨390708, by rfl⟩ : syracuseStep 1041889 = 781417) (by norm_num)
theorem B1172981 : Blo 924580 1172981 := bbase (se 5 (by rfl) ⟨54983, by rfl⟩ : syracuseStep 1172981 = 109967) (by norm_num)
theorem B2221565 : Blo 924580 2221565 := bbase (se 3 (by rfl) ⟨416543, by rfl⟩ : syracuseStep 2221565 = 833087) (by norm_num)
theorem B1762813 : Blo 924580 1762813 := bbase (se 3 (by rfl) ⟨330527, by rfl⟩ : syracuseStep 1762813 = 661055) (by norm_num)
theorem B1041925 : Blo 924580 1041925 := bbase (se 4 (by rfl) ⟨97680, by rfl⟩ : syracuseStep 1041925 = 195361) (by norm_num)
theorem B1566229 : Blo 924580 1566229 := bbase (se 6 (by rfl) ⟨36708, by rfl⟩ : syracuseStep 1566229 = 73417) (by norm_num)
theorem B1041961 : Blo 924580 1041961 := bbase (se 2 (by rfl) ⟨390735, by rfl⟩ : syracuseStep 1041961 = 781471) (by norm_num)
theorem B1173037 : Blo 924580 1173037 := bbase (se 3 (by rfl) ⟨219944, by rfl⟩ : syracuseStep 1173037 = 439889) (by norm_num)
theorem B1041997 : Blo 924580 1041997 := bbase (se 3 (by rfl) ⟨195374, by rfl⟩ : syracuseStep 1041997 = 390749) (by norm_num)
theorem B1566317 : Blo 924580 1566317 := bbase (se 3 (by rfl) ⟨293684, by rfl⟩ : syracuseStep 1566317 = 587369) (by norm_num)
theorem B1042033 : Blo 924580 1042033 := bbase (se 2 (by rfl) ⟨390762, by rfl⟩ : syracuseStep 1042033 = 781525) (by norm_num)
theorem B1173133 : Blo 924580 1173133 := bbase (se 3 (by rfl) ⟨219962, by rfl⟩ : syracuseStep 1173133 = 439925) (by norm_num)
theorem B1042069 : Blo 924580 1042069 := bbase (se 6 (by rfl) ⟨24423, by rfl⟩ : syracuseStep 1042069 = 48847) (by norm_num)
theorem B1336981 : Blo 924580 1336981 := bbase (se 6 (by rfl) ⟨31335, by rfl⟩ : syracuseStep 1336981 = 62671) (by norm_num)
theorem B1042105 : Blo 924580 1042105 := bbase (se 2 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 1042105 = 781579) (by norm_num)
theorem B1042141 : Blo 924580 1042141 := bbase (se 3 (by rfl) ⟨195401, by rfl⟩ : syracuseStep 1042141 = 390803) (by norm_num)
theorem B1566445 : Blo 924580 1566445 := bbase (se 3 (by rfl) ⟨293708, by rfl⟩ : syracuseStep 1566445 = 587417) (by norm_num)
theorem B1042177 : Blo 924580 1042177 := bbase (se 2 (by rfl) ⟨390816, by rfl⟩ : syracuseStep 1042177 = 781633) (by norm_num)
theorem B1042213 : Blo 924580 1042213 := bbase (se 4 (by rfl) ⟨97707, by rfl⟩ : syracuseStep 1042213 = 195415) (by norm_num)
theorem B1173305 : Blo 924580 1173305 := bbase (se 2 (by rfl) ⟨439989, by rfl⟩ : syracuseStep 1173305 = 879979) (by norm_num)
theorem B1566533 : Blo 924580 1566533 := bbase (se 4 (by rfl) ⟨146862, by rfl⟩ : syracuseStep 1566533 = 293725) (by norm_num)
theorem B1042249 : Blo 924580 1042249 := bbase (se 2 (by rfl) ⟨390843, by rfl⟩ : syracuseStep 1042249 = 781687) (by norm_num)
theorem B1042285 : Blo 924580 1042285 := bbase (se 3 (by rfl) ⟨195428, by rfl⟩ : syracuseStep 1042285 = 390857) (by norm_num)
theorem B1173361 : Blo 924580 1173361 := bbase (se 2 (by rfl) ⟨440010, by rfl⟩ : syracuseStep 1173361 = 880021) (by norm_num)
theorem B1042321 : Blo 924580 1042321 := bbase (se 2 (by rfl) ⟨390870, by rfl⟩ : syracuseStep 1042321 = 781741) (by norm_num)
theorem B5924789 : Blo 924580 5924789 := bbase (se 5 (by rfl) ⟨277724, by rfl⟩ : syracuseStep 5924789 = 555449) (by norm_num)
theorem B1042357 : Blo 924580 1042357 := bbase (se 5 (by rfl) ⟨48860, by rfl⟩ : syracuseStep 1042357 = 97721) (by norm_num)
theorem B1566661 : Blo 924580 1566661 := bbase (se 4 (by rfl) ⟨146874, by rfl⟩ : syracuseStep 1566661 = 293749) (by norm_num)
theorem B1173457 : Blo 924580 1173457 := bbase (se 2 (by rfl) ⟨440046, by rfl⟩ : syracuseStep 1173457 = 880093) (by norm_num)
theorem B15820757 : Blo 924580 15820757 := bbase (se 7 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 15820757 = 370799) (by norm_num)
theorem B1042393 : Blo 924580 1042393 := bbase (se 2 (by rfl) ⟨390897, by rfl⟩ : syracuseStep 1042393 = 781795) (by norm_num)
theorem B1042429 : Blo 924580 1042429 := bbase (se 3 (by rfl) ⟨195455, by rfl⟩ : syracuseStep 1042429 = 390911) (by norm_num)
theorem B1566749 : Blo 924580 1566749 := bbase (se 3 (by rfl) ⟨293765, by rfl⟩ : syracuseStep 1566749 = 587531) (by norm_num)
theorem B1042465 : Blo 924580 1042465 := bbase (se 2 (by rfl) ⟨390924, by rfl⟩ : syracuseStep 1042465 = 781849) (by norm_num)
theorem B1042501 : Blo 924580 1042501 := bbase (se 4 (by rfl) ⟨97734, by rfl⟩ : syracuseStep 1042501 = 195469) (by norm_num)
theorem B1042537 : Blo 924580 1042537 := bbase (se 2 (by rfl) ⟨390951, by rfl⟩ : syracuseStep 1042537 = 781903) (by norm_num)
theorem B1173629 : Blo 924580 1173629 := bbase (se 3 (by rfl) ⟨220055, by rfl⟩ : syracuseStep 1173629 = 440111) (by norm_num)
theorem B1042573 : Blo 924580 1042573 := bbase (se 3 (by rfl) ⟨195482, by rfl⟩ : syracuseStep 1042573 = 390965) (by norm_num)
theorem B1271965 : Blo 924580 1271965 := bbase (se 3 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 1271965 = 476987) (by norm_num)
theorem B1566877 : Blo 924580 1566877 := bbase (se 3 (by rfl) ⟨293789, by rfl⟩ : syracuseStep 1566877 = 587579) (by norm_num)
theorem B3958949 : Blo 924580 3958949 := bbase (se 4 (by rfl) ⟨371151, by rfl⟩ : syracuseStep 3958949 = 742303) (by norm_num)
theorem B1042609 : Blo 924580 1042609 := bbase (se 2 (by rfl) ⟨390978, by rfl⟩ : syracuseStep 1042609 = 781957) (by norm_num)
theorem B1173685 : Blo 924580 1173685 := bbase (se 5 (by rfl) ⟨55016, by rfl⟩ : syracuseStep 1173685 = 110033) (by norm_num)
theorem B1042645 : Blo 924580 1042645 := bbase (se 7 (by rfl) ⟨12218, by rfl⟩ : syracuseStep 1042645 = 24437) (by norm_num)
theorem B1566965 : Blo 924580 1566965 := bbase (se 5 (by rfl) ⟨73451, by rfl⟩ : syracuseStep 1566965 = 146903) (by norm_num)
theorem B1042681 : Blo 924580 1042681 := bbase (se 2 (by rfl) ⟨391005, by rfl⟩ : syracuseStep 1042681 = 782011) (by norm_num)
theorem B1173781 : Blo 924580 1173781 := bbase (se 6 (by rfl) ⟨27510, by rfl⟩ : syracuseStep 1173781 = 55021) (by norm_num)
theorem B1042717 : Blo 924580 1042717 := bbase (se 3 (by rfl) ⟨195509, by rfl⟩ : syracuseStep 1042717 = 391019) (by norm_num)
theorem B1042753 : Blo 924580 1042753 := bbase (se 2 (by rfl) ⟨391032, by rfl⟩ : syracuseStep 1042753 = 782065) (by norm_num)
theorem B4811093 : Blo 924580 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B1042789 : Blo 924580 1042789 := bbase (se 4 (by rfl) ⟨97761, by rfl⟩ : syracuseStep 1042789 = 195523) (by norm_num)
theorem B1042825 : Blo 924580 1042825 := bbase (se 2 (by rfl) ⟨391059, by rfl⟩ : syracuseStep 1042825 = 782119) (by norm_num)
theorem B3959189 : Blo 924580 3959189 := bbase (se 6 (by rfl) ⟨92793, by rfl⟩ : syracuseStep 3959189 = 185587) (by norm_num)
theorem B1042861 : Blo 924580 1042861 := bbase (se 3 (by rfl) ⟨195536, by rfl⟩ : syracuseStep 1042861 = 391073) (by norm_num)
theorem B1173953 : Blo 924580 1173953 := bbase (se 2 (by rfl) ⟨440232, by rfl⟩ : syracuseStep 1173953 = 880465) (by norm_num)
theorem B1042897 : Blo 924580 1042897 := bbase (se 2 (by rfl) ⟨391086, by rfl⟩ : syracuseStep 1042897 = 782173) (by norm_num)
theorem B1042933 : Blo 924580 1042933 := bbase (se 5 (by rfl) ⟨48887, by rfl⟩ : syracuseStep 1042933 = 97775) (by norm_num)
theorem B1174009 : Blo 924580 1174009 := bbase (se 2 (by rfl) ⟨440253, by rfl⟩ : syracuseStep 1174009 = 880507) (by norm_num)
theorem B1042969 : Blo 924580 1042969 := bbase (se 2 (by rfl) ⟨391113, by rfl⟩ : syracuseStep 1042969 = 782227) (by norm_num)
theorem B1043005 : Blo 924580 1043005 := bbase (se 3 (by rfl) ⟨195563, by rfl⟩ : syracuseStep 1043005 = 391127) (by norm_num)
theorem B1174105 : Blo 924580 1174105 := bbase (se 2 (by rfl) ⟨440289, by rfl⟩ : syracuseStep 1174105 = 880579) (by norm_num)
theorem B1043041 : Blo 924580 1043041 := bbase (se 2 (by rfl) ⟨391140, by rfl⟩ : syracuseStep 1043041 = 782281) (by norm_num)
theorem B1043077 : Blo 924580 1043077 := bbase (se 4 (by rfl) ⟨97788, by rfl⟩ : syracuseStep 1043077 = 195577) (by norm_num)
theorem B1043113 : Blo 924580 1043113 := bbase (se 2 (by rfl) ⟨391167, by rfl⟩ : syracuseStep 1043113 = 782335) (by norm_num)
theorem B1043149 : Blo 924580 1043149 := bbase (se 3 (by rfl) ⟨195590, by rfl⟩ : syracuseStep 1043149 = 391181) (by norm_num)
theorem B1043185 : Blo 924580 1043185 := bbase (se 2 (by rfl) ⟨391194, by rfl⟩ : syracuseStep 1043185 = 782389) (by norm_num)
theorem B1174277 : Blo 924580 1174277 := bbase (se 4 (by rfl) ⟨110088, by rfl⟩ : syracuseStep 1174277 = 220177) (by norm_num)
theorem B1043221 : Blo 924580 1043221 := bbase (se 6 (by rfl) ⟨24450, by rfl⟩ : syracuseStep 1043221 = 48901) (by norm_num)
theorem B1043257 : Blo 924580 1043257 := bbase (se 2 (by rfl) ⟨391221, by rfl⟩ : syracuseStep 1043257 = 782443) (by norm_num)
theorem B1174333 : Blo 924580 1174333 := bbase (se 3 (by rfl) ⟨220187, by rfl⟩ : syracuseStep 1174333 = 440375) (by norm_num)
theorem B1043293 : Blo 924580 1043293 := bbase (se 3 (by rfl) ⟨195617, by rfl⟩ : syracuseStep 1043293 = 391235) (by norm_num)
theorem B1043329 : Blo 924580 1043329 := bbase (se 2 (by rfl) ⟨391248, by rfl⟩ : syracuseStep 1043329 = 782497) (by norm_num)
theorem B1174429 : Blo 924580 1174429 := bbase (se 3 (by rfl) ⟨220205, by rfl⟩ : syracuseStep 1174429 = 440411) (by norm_num)
theorem B1043365 : Blo 924580 1043365 := bbase (se 4 (by rfl) ⟨97815, by rfl⟩ : syracuseStep 1043365 = 195631) (by norm_num)
theorem B1043401 : Blo 924580 1043401 := bbase (se 2 (by rfl) ⟨391275, by rfl⟩ : syracuseStep 1043401 = 782551) (by norm_num)
theorem B1043437 : Blo 924580 1043437 := bbase (se 3 (by rfl) ⟨195644, by rfl⟩ : syracuseStep 1043437 = 391289) (by norm_num)
theorem B1043473 : Blo 924580 1043473 := bbase (se 2 (by rfl) ⟨391302, by rfl⟩ : syracuseStep 1043473 = 782605) (by norm_num)
theorem B1043509 : Blo 924580 1043509 := bbase (se 5 (by rfl) ⟨48914, by rfl⟩ : syracuseStep 1043509 = 97829) (by norm_num)
theorem B1174601 : Blo 924580 1174601 := bbase (se 2 (by rfl) ⟨440475, by rfl⟩ : syracuseStep 1174601 = 880951) (by norm_num)
theorem B1043545 : Blo 924580 1043545 := bbase (se 2 (by rfl) ⟨391329, by rfl⟩ : syracuseStep 1043545 = 782659) (by norm_num)
theorem B1043581 : Blo 924580 1043581 := bbase (se 3 (by rfl) ⟨195671, by rfl⟩ : syracuseStep 1043581 = 391343) (by norm_num)
theorem B1174657 : Blo 924580 1174657 := bbase (se 2 (by rfl) ⟨440496, by rfl⟩ : syracuseStep 1174657 = 880993) (by norm_num)
theorem B1043617 : Blo 924580 1043617 := bbase (se 2 (by rfl) ⟨391356, by rfl⟩ : syracuseStep 1043617 = 782713) (by norm_num)
theorem B1141933 : Blo 924580 1141933 := bbase (se 3 (by rfl) ⟨214112, by rfl⟩ : syracuseStep 1141933 = 428225) (by norm_num)
theorem B1043653 : Blo 924580 1043653 := bbase (se 4 (by rfl) ⟨97842, by rfl⟩ : syracuseStep 1043653 = 195685) (by norm_num)
theorem B1666261 : Blo 924580 1666261 := bbase (se 7 (by rfl) ⟨19526, by rfl⟩ : syracuseStep 1666261 = 39053) (by norm_num)
theorem B2223325 : Blo 924580 2223325 := bbase (se 3 (by rfl) ⟨416873, by rfl⟩ : syracuseStep 2223325 = 833747) (by norm_num)
theorem B1174753 : Blo 924580 1174753 := bbase (se 2 (by rfl) ⟨440532, by rfl⟩ : syracuseStep 1174753 = 881065) (by norm_num)
theorem B1043689 : Blo 924580 1043689 := bbase (se 2 (by rfl) ⟨391383, by rfl⟩ : syracuseStep 1043689 = 782767) (by norm_num)
theorem B1043725 : Blo 924580 1043725 := bbase (se 3 (by rfl) ⟨195698, by rfl⟩ : syracuseStep 1043725 = 391397) (by norm_num)
theorem B3763493 : Blo 924580 3763493 := bbase (se 4 (by rfl) ⟨352827, by rfl⟩ : syracuseStep 3763493 = 705655) (by norm_num)
theorem B1043761 : Blo 924580 1043761 := bbase (se 2 (by rfl) ⟨391410, by rfl⟩ : syracuseStep 1043761 = 782821) (by norm_num)
theorem B1043797 : Blo 924580 1043797 := bbase (se 11 (by rfl) ⟨764, by rfl⟩ : syracuseStep 1043797 = 1529) (by norm_num)
theorem B1043833 : Blo 924580 1043833 := bbase (se 2 (by rfl) ⟨391437, by rfl⟩ : syracuseStep 1043833 = 782875) (by norm_num)
theorem B1174925 : Blo 924580 1174925 := bbase (se 3 (by rfl) ⟨220298, by rfl⟩ : syracuseStep 1174925 = 440597) (by norm_num)
theorem B7925141 : Blo 924580 7925141 := bbase (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) (by norm_num)
theorem B1043869 : Blo 924580 1043869 := bbase (se 3 (by rfl) ⟨195725, by rfl⟩ : syracuseStep 1043869 = 391451) (by norm_num)
theorem B1666477 : Blo 924580 1666477 := bbase (se 3 (by rfl) ⟨312464, by rfl⟩ : syracuseStep 1666477 = 624929) (by norm_num)
theorem B1043905 : Blo 924580 1043905 := bbase (se 2 (by rfl) ⟨391464, by rfl⟩ : syracuseStep 1043905 = 782929) (by norm_num)
theorem B2223557 : Blo 924580 2223557 := bbase (se 4 (by rfl) ⟨208458, by rfl⟩ : syracuseStep 2223557 = 416917) (by norm_num)
theorem B1174981 : Blo 924580 1174981 := bbase (se 4 (by rfl) ⟨110154, by rfl⟩ : syracuseStep 1174981 = 220309) (by norm_num)
theorem B1043941 : Blo 924580 1043941 := bbase (se 4 (by rfl) ⟨97869, by rfl⟩ : syracuseStep 1043941 = 195739) (by norm_num)
theorem B1043977 : Blo 924580 1043977 := bbase (se 2 (by rfl) ⟨391491, by rfl⟩ : syracuseStep 1043977 = 782983) (by norm_num)
theorem B1175077 : Blo 924580 1175077 := bbase (se 4 (by rfl) ⟨110163, by rfl⟩ : syracuseStep 1175077 = 220327) (by norm_num)
theorem B1044013 : Blo 924580 1044013 := bbase (se 3 (by rfl) ⟨195752, by rfl⟩ : syracuseStep 1044013 = 391505) (by norm_num)
theorem B5008949 : Blo 924580 5008949 := bbase (se 5 (by rfl) ⟨234794, by rfl⟩ : syracuseStep 5008949 = 469589) (by norm_num)
theorem B1044049 : Blo 924580 1044049 := bbase (se 2 (by rfl) ⟨391518, by rfl⟩ : syracuseStep 1044049 = 783037) (by norm_num)
theorem B1044085 : Blo 924580 1044085 := bbase (se 5 (by rfl) ⟨48941, by rfl⟩ : syracuseStep 1044085 = 97883) (by norm_num)
theorem B1044121 : Blo 924580 1044121 := bbase (se 2 (by rfl) ⟨391545, by rfl⟩ : syracuseStep 1044121 = 783091) (by norm_num)
theorem B1044157 : Blo 924580 1044157 := bbase (se 3 (by rfl) ⟨195779, by rfl⟩ : syracuseStep 1044157 = 391559) (by norm_num)
theorem B1044193 : Blo 924580 1044193 := bbase (se 2 (by rfl) ⟨391572, by rfl⟩ : syracuseStep 1044193 = 783145) (by norm_num)
theorem B1044229 : Blo 924580 1044229 := bbase (se 4 (by rfl) ⟨97896, by rfl⟩ : syracuseStep 1044229 = 195793) (by norm_num)
theorem B1044265 : Blo 924580 1044265 := bbase (se 2 (by rfl) ⟨391599, by rfl⟩ : syracuseStep 1044265 = 783199) (by norm_num)
theorem B7499573 : Blo 924580 7499573 := bbase (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) (by norm_num)
theorem B2223949 : Blo 924580 2223949 := bbase (se 3 (by rfl) ⟨416990, by rfl⟩ : syracuseStep 2223949 = 833981) (by norm_num)
theorem B1044301 : Blo 924580 1044301 := bbase (se 3 (by rfl) ⟨195806, by rfl⟩ : syracuseStep 1044301 = 391613) (by norm_num)
theorem B1044337 : Blo 924580 1044337 := bbase (se 2 (by rfl) ⟨391626, by rfl⟩ : syracuseStep 1044337 = 783253) (by norm_num)
theorem B4747157 : Blo 924580 4747157 := bbase (se 6 (by rfl) ⟨111261, by rfl⟩ : syracuseStep 4747157 = 222523) (by norm_num)
theorem B1044373 : Blo 924580 1044373 := bbase (se 6 (by rfl) ⟨24477, by rfl⟩ : syracuseStep 1044373 = 48955) (by norm_num)
theorem B4681637 : Blo 924580 4681637 := bbase (se 4 (by rfl) ⟨438903, by rfl⟩ : syracuseStep 4681637 = 877807) (by norm_num)
theorem B1044409 : Blo 924580 1044409 := bbase (se 2 (by rfl) ⟨391653, by rfl⟩ : syracuseStep 1044409 = 783307) (by norm_num)
theorem B1044445 : Blo 924580 1044445 := bbase (se 3 (by rfl) ⟨195833, by rfl⟩ : syracuseStep 1044445 = 391667) (by norm_num)
theorem B1044481 : Blo 924580 1044481 := bbase (se 2 (by rfl) ⟨391680, by rfl⟩ : syracuseStep 1044481 = 783361) (by norm_num)
theorem B1044517 : Blo 924580 1044517 := bbase (se 4 (by rfl) ⟨97923, by rfl⟩ : syracuseStep 1044517 = 195847) (by norm_num)
theorem B1044553 : Blo 924580 1044553 := bbase (se 2 (by rfl) ⟨391707, by rfl⟩ : syracuseStep 1044553 = 783415) (by norm_num)
theorem B33747029 : Blo 924580 33747029 := bbase (se 8 (by rfl) ⟨197736, by rfl⟩ : syracuseStep 33747029 = 395473) (by norm_num)
theorem B7499861 : Blo 924580 7499861 := bbase (se 8 (by rfl) ⟨43944, by rfl⟩ : syracuseStep 7499861 = 87889) (by norm_num)
theorem B1044589 : Blo 924580 1044589 := bbase (se 3 (by rfl) ⟨195860, by rfl⟩ : syracuseStep 1044589 = 391721) (by norm_num)
theorem B1044625 : Blo 924580 1044625 := bbase (se 2 (by rfl) ⟨391734, by rfl⟩ : syracuseStep 1044625 = 783469) (by norm_num)
theorem B1667645 : Blo 924580 1667645 := bbase (se 3 (by rfl) ⟨312683, by rfl⟩ : syracuseStep 1667645 = 625367) (by norm_num)
theorem B7041653 : Blo 924580 7041653 := bbase (se 5 (by rfl) ⟨330077, by rfl⟩ : syracuseStep 7041653 = 660155) (by norm_num)
theorem B3961477 : Blo 924580 3961477 := bbase (se 4 (by rfl) ⟨371388, by rfl⟩ : syracuseStep 3961477 = 742777) (by norm_num)
theorem B2257645 : Blo 924580 2257645 := bbase (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) (by norm_num)
theorem B3764981 : Blo 924580 3764981 := bbase (se 5 (by rfl) ⟨176483, by rfl⟩ : syracuseStep 3764981 = 352967) (by norm_num)
theorem B4223765 : Blo 924580 4223765 := bbase (se 6 (by rfl) ⟨98994, by rfl⟩ : syracuseStep 4223765 = 197989) (by norm_num)
theorem B2225045 : Blo 924580 2225045 := bbase (se 6 (by rfl) ⟨52149, by rfl⟩ : syracuseStep 2225045 = 104299) (by norm_num)
theorem B1110937 : Blo 924580 1110937 := bbase (se 2 (by rfl) ⟨416601, by rfl⟩ : syracuseStep 1110937 = 833203) (by norm_num)
theorem B9630677 : Blo 924580 9630677 := bbase (se 7 (by rfl) ⟨112859, by rfl⟩ : syracuseStep 9630677 = 225719) (by norm_num)
theorem B1504261 : Blo 924580 1504261 := bbase (se 4 (by rfl) ⟨141024, by rfl⟩ : syracuseStep 1504261 = 282049) (by norm_num)
theorem B3339269 : Blo 924580 3339269 := bbase (se 4 (by rfl) ⟨313056, by rfl⟩ : syracuseStep 3339269 = 626113) (by norm_num)
theorem B1111201 : Blo 924580 1111201 := bbase (se 2 (by rfl) ⟨416700, by rfl⟩ : syracuseStep 1111201 = 833401) (by norm_num)
theorem B4682933 : Blo 924580 4682933 := bbase (se 5 (by rfl) ⟨219512, by rfl⟩ : syracuseStep 4682933 = 439025) (by norm_num)
theorem B2225333 : Blo 924580 2225333 := bbase (se 5 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 2225333 = 208625) (by norm_num)
theorem B1111321 : Blo 924580 1111321 := bbase (se 2 (by rfl) ⟨416745, by rfl⟩ : syracuseStep 1111321 = 833491) (by norm_num)
theorem B1406317 : Blo 924580 1406317 := bbase (se 3 (by rfl) ⟨263684, by rfl⟩ : syracuseStep 1406317 = 527369) (by norm_num)
theorem B10548629 : Blo 924580 10548629 := bbase (se 6 (by rfl) ⟨247233, by rfl⟩ : syracuseStep 10548629 = 494467) (by norm_num)
theorem B3962965 : Blo 924580 3962965 := bbase (se 8 (by rfl) ⟨23220, by rfl⟩ : syracuseStep 3962965 = 46441) (by norm_num)
theorem B3962981 : Blo 924580 3962981 := bbase (se 4 (by rfl) ⟨371529, by rfl⟩ : syracuseStep 3962981 = 743059) (by norm_num)
theorem B1112177 : Blo 924580 1112177 := bbase (se 2 (by rfl) ⟨417066, by rfl⟩ : syracuseStep 1112177 = 834133) (by norm_num)
theorem B3340421 : Blo 924580 3340421 := bbase (se 4 (by rfl) ⟨313164, by rfl⟩ : syracuseStep 3340421 = 626329) (by norm_num)
theorem B6027509 : Blo 924580 6027509 := bbase (se 5 (by rfl) ⟨282539, by rfl⟩ : syracuseStep 6027509 = 565079) (by norm_num)
theorem B7928117 : Blo 924580 7928117 := bbase (se 5 (by rfl) ⟨371630, by rfl⟩ : syracuseStep 7928117 = 743261) (by norm_num)
theorem B19003733 : Blo 924580 19003733 := bbase (se 10 (by rfl) ⟨27837, by rfl⟩ : syracuseStep 19003733 = 55675) (by norm_num)
theorem B4684229 : Blo 924580 4684229 := bbase (se 4 (by rfl) ⟨439146, by rfl⟩ : syracuseStep 4684229 = 878293) (by norm_num)
theorem B7502453 : Blo 924580 7502453 := bbase (se 5 (by rfl) ⟨351677, by rfl⟩ : syracuseStep 7502453 = 703355) (by norm_num)
theorem B4455125 : Blo 924580 4455125 := bbase (se 7 (by rfl) ⟨52208, by rfl⟩ : syracuseStep 4455125 = 104417) (by norm_num)
theorem B1932005 : Blo 924580 1932005 := bbase (se 4 (by rfl) ⟨181125, by rfl⟩ : syracuseStep 1932005 = 362251) (by norm_num)
theorem B6683381 : Blo 924580 6683381 := bbase (se 5 (by rfl) ⟨313283, by rfl⟩ : syracuseStep 6683381 = 626567) (by norm_num)
theorem B1112897 : Blo 924580 1112897 := bbase (se 2 (by rfl) ⟨417336, by rfl⟩ : syracuseStep 1112897 = 834673) (by norm_num)
theorem B4225861 : Blo 924580 4225861 := bbase (se 4 (by rfl) ⟨396174, by rfl⟩ : syracuseStep 4225861 = 792349) (by norm_num)
theorem B1407989 : Blo 924580 1407989 := bbase (se 5 (by rfl) ⟨65999, by rfl⟩ : syracuseStep 1407989 = 131999) (by norm_num)
theorem B1408117 : Blo 924580 1408117 := bbase (se 5 (by rfl) ⟨66005, by rfl⟩ : syracuseStep 1408117 = 132011) (by norm_num)
theorem B1113205 : Blo 924580 1113205 := bbase (se 5 (by rfl) ⟨52181, by rfl⟩ : syracuseStep 1113205 = 104363) (by norm_num)
theorem B1113301 : Blo 924580 1113301 := bbase (se 7 (by rfl) ⟨13046, by rfl⟩ : syracuseStep 1113301 = 26093) (by norm_num)
theorem B2227429 : Blo 924580 2227429 := bbase (se 4 (by rfl) ⟨208821, by rfl⟩ : syracuseStep 2227429 = 417643) (by norm_num)
theorem B1113445 : Blo 924580 1113445 := bbase (se 4 (by rfl) ⟨104385, by rfl⟩ : syracuseStep 1113445 = 208771) (by norm_num)
theorem B1670557 : Blo 924580 1670557 := bbase (se 3 (by rfl) ⟨313229, by rfl⟩ : syracuseStep 1670557 = 626459) (by norm_num)
theorem B1670629 : Blo 924580 1670629 := bbase (se 4 (by rfl) ⟨156621, by rfl⟩ : syracuseStep 1670629 = 313243) (by norm_num)
theorem B1670861 : Blo 924580 1670861 := bbase (se 3 (by rfl) ⟨313286, by rfl⟩ : syracuseStep 1670861 = 626573) (by norm_num)
theorem B4685525 : Blo 924580 4685525 := bbase (se 7 (by rfl) ⟨54908, by rfl⟩ : syracuseStep 4685525 = 109817) (by norm_num)
theorem B3047141 : Blo 924580 3047141 := bbase (se 4 (by rfl) ⟨285669, by rfl⟩ : syracuseStep 3047141 = 571339) (by norm_num)
theorem B950077 : Blo 924580 950077 := bbase (se 3 (by rfl) ⟨178139, by rfl⟩ : syracuseStep 950077 = 356279) (by norm_num)
theorem B3342181 : Blo 924580 3342181 := bbase (se 4 (by rfl) ⟨313329, by rfl⟩ : syracuseStep 3342181 = 626659) (by norm_num)
theorem B2228093 : Blo 924580 2228093 := bbase (se 3 (by rfl) ⟨417767, by rfl⟩ : syracuseStep 2228093 = 835535) (by norm_num)
theorem B5275637 : Blo 924580 5275637 := bbase (se 5 (by rfl) ⟨247295, by rfl⟩ : syracuseStep 5275637 = 494591) (by norm_num)
theorem B1671185 : Blo 924580 1671185 := bstep (se 2 (by rfl) ⟨626694, by rfl⟩ : syracuseStep 1671185 = 1253389) B1253389
theorem B3964963 : Blo 924580 3964963 := bstep (se 1 (by rfl) ⟨2973722, by rfl⟩ : syracuseStep 3964963 = 5947445) B5947445
theorem B2818189 : Blo 924580 2818189 := bstep (se 3 (by rfl) ⟨528410, by rfl⟩ : syracuseStep 2818189 = 1056821) B1056821
theorem B1114435 : Blo 924580 1114435 := bstep (se 1 (by rfl) ⟨835826, by rfl⟩ : syracuseStep 1114435 = 1671653) B1671653
theorem B4817251 : Blo 924580 4817251 := bstep (se 1 (by rfl) ⟨3612938, by rfl⟩ : syracuseStep 4817251 = 7225877) B7225877
theorem B1409411 : Blo 924580 1409411 := bstep (se 1 (by rfl) ⟨1057058, by rfl⟩ : syracuseStep 1409411 = 2114117) B2114117
theorem B24052421 : Blo 924580 24052421 := bstep (se 4 (by rfl) ⟨2254914, by rfl⟩ : syracuseStep 24052421 = 4509829) B4509829
theorem B4457585 : Blo 924580 4457585 := bstep (se 2 (by rfl) ⟨1671594, by rfl⟩ : syracuseStep 4457585 = 3343189) B3343189
theorem B3867761 : Blo 924580 3867761 := bstep (se 2 (by rfl) ⟨1450410, by rfl⟩ : syracuseStep 3867761 = 2900821) B2900821
theorem B1410385 : Blo 924580 1410385 := bstep (se 2 (by rfl) ⟨528894, by rfl⟩ : syracuseStep 1410385 = 1057789) B1057789
theorem B7046513 : Blo 924580 7046513 := bstep (se 2 (by rfl) ⟨2642442, by rfl⟩ : syracuseStep 7046513 = 5284885) B5284885
theorem B15238709 : Blo 924580 15238709 := bstep (se 5 (by rfl) ⟨714314, by rfl⟩ : syracuseStep 15238709 = 1428629) B1428629
theorem B5015459 : Blo 924580 5015459 := bstep (se 1 (by rfl) ⟨3761594, by rfl⟩ : syracuseStep 5015459 = 7523189) B7523189
theorem B4687793 : Blo 924580 4687793 := bstep (se 2 (by rfl) ⟨1757922, by rfl⟩ : syracuseStep 4687793 = 3515845) B3515845
theorem B4458509 : Blo 924580 4458509 := bstep (se 3 (by rfl) ⟨835970, by rfl⟩ : syracuseStep 4458509 = 1671941) B1671941
theorem B3344561 : Blo 924580 3344561 := bstep (se 2 (by rfl) ⟨1254210, by rfl⟩ : syracuseStep 3344561 = 2508421) B2508421
theorem B4458701 : Blo 924580 4458701 := bstep (se 3 (by rfl) ⟨836006, by rfl⟩ : syracuseStep 4458701 = 1672013) B1672013
theorem B1411523 : Blo 924580 1411523 := bstep (se 1 (by rfl) ⟨1058642, by rfl⟩ : syracuseStep 1411523 = 2117285) B2117285
theorem B2034595 : Blo 924580 2034595 := bstep (se 1 (by rfl) ⟨1525946, by rfl⟩ : syracuseStep 2034595 = 3051893) B3051893
theorem B1608707 : Blo 924580 1608707 := bstep (se 1 (by rfl) ⟨1206530, by rfl⟩ : syracuseStep 1608707 = 2413061) B2413061
theorem B12717155 : Blo 924580 12717155 := bstep (se 1 (by rfl) ⟨9537866, by rfl⟩ : syracuseStep 12717155 = 19075733) B19075733
theorem B5934221 : Blo 924580 5934221 := bstep (se 3 (by rfl) ⟨1112666, by rfl⟩ : syracuseStep 5934221 = 2225333) B2225333
theorem B3050659 : Blo 924580 3050659 := bstep (se 1 (by rfl) ⟨2287994, by rfl⟩ : syracuseStep 3050659 = 4575989) B4575989
theorem B5016773 : Blo 924580 5016773 := bstep (se 4 (by rfl) ⟨470322, by rfl⟩ : syracuseStep 5016773 = 940645) B940645
theorem B5279053 : Blo 924580 5279053 := bstep (se 3 (by rfl) ⟨989822, by rfl⟩ : syracuseStep 5279053 = 1979645) B1979645
theorem B3804515 : Blo 924580 3804515 := bstep (se 1 (by rfl) ⟨2853386, by rfl⟩ : syracuseStep 3804515 = 5706773) B5706773
theorem B4689251 : Blo 924580 4689251 := bstep (se 1 (by rfl) ⟨3516938, by rfl⟩ : syracuseStep 4689251 = 7033877) B7033877
theorem B2821841 : Blo 924580 2821841 := bstep (se 2 (by rfl) ⟨1058190, by rfl⟩ : syracuseStep 2821841 = 2116381) B2116381
theorem B2854765 : Blo 924580 2854765 := bstep (se 3 (by rfl) ⟨535268, by rfl⟩ : syracuseStep 2854765 = 1070537) B1070537
theorem B11898737 : Blo 924580 11898737 := bstep (se 2 (by rfl) ⟨4462026, by rfl⟩ : syracuseStep 11898737 = 8924053) B8924053
theorem B4690061 : Blo 924580 4690061 := bstep (se 3 (by rfl) ⟨879386, by rfl⟩ : syracuseStep 4690061 = 1758773) B1758773
theorem B987427 : Blo 924580 987427 := bstep (se 1 (by rfl) ⟨740570, by rfl⟩ : syracuseStep 987427 = 1481141) B1481141
theorem B9999557 : Blo 924580 9999557 := bstep (se 4 (by rfl) ⟨937458, by rfl⟩ : syracuseStep 9999557 = 1874917) B1874917
theorem B5281037 : Blo 924580 5281037 := bstep (se 3 (by rfl) ⟨990194, by rfl⟩ : syracuseStep 5281037 = 1980389) B1980389
theorem B6690275 : Blo 924580 6690275 := bstep (se 1 (by rfl) ⟨5017706, by rfl⟩ : syracuseStep 6690275 = 10035413) B10035413
theorem B988691 : Blo 924580 988691 := bstep (se 1 (by rfl) ⟨741518, by rfl⟩ : syracuseStep 988691 = 1483037) B1483037
theorem B1316449 : Blo 924580 1316449 := bstep (se 2 (by rfl) ⟨493668, by rfl⟩ : syracuseStep 1316449 = 987337) B987337
theorem B3381233 : Blo 924580 3381233 := bstep (se 2 (by rfl) ⟨1267962, by rfl⟩ : syracuseStep 3381233 = 2535925) B2535925
theorem B3217553 : Blo 924580 3217553 := bstep (se 2 (by rfl) ⟨1206582, by rfl⟩ : syracuseStep 3217553 = 2413165) B2413165
theorem B5281969 : Blo 924580 5281969 := bstep (se 2 (by rfl) ⟨1980738, by rfl⟩ : syracuseStep 5281969 = 3961477) B3961477
theorem B989443 : Blo 924580 989443 := bstep (se 1 (by rfl) ⟨742082, by rfl⟩ : syracuseStep 989443 = 1484165) B1484165
theorem B1906993 : Blo 924580 1906993 := bstep (se 2 (by rfl) ⟨715122, by rfl⟩ : syracuseStep 1906993 = 1430245) B1430245
theorem B1317235 : Blo 924580 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B3512717 : Blo 924580 3512717 := bstep (se 3 (by rfl) ⟨658634, by rfl⟩ : syracuseStep 3512717 = 1317269) B1317269
theorem B16062947 : Blo 924580 16062947 := bstep (se 1 (by rfl) ⟨12047210, by rfl⟩ : syracuseStep 16062947 = 24094421) B24094421
theorem B1481249 : Blo 924580 1481249 := bstep (se 2 (by rfl) ⟨555468, by rfl⟩ : syracuseStep 1481249 = 1110937) B1110937
theorem B2824849 : Blo 924580 2824849 := bstep (se 2 (by rfl) ⟨1059318, by rfl⟩ : syracuseStep 2824849 = 2118637) B2118637
theorem B2005681 : Blo 924580 2005681 := bstep (se 2 (by rfl) ⟨752130, by rfl⟩ : syracuseStep 2005681 = 1504261) B1504261
theorem B1317713 : Blo 924580 1317713 := bstep (se 2 (by rfl) ⟨494142, by rfl⟩ : syracuseStep 1317713 = 988285) B988285
theorem B924595 : Blo 924580 924595 := bstep (se 1 (by rfl) ⟨693446, by rfl⟩ : syracuseStep 924595 = 1386893) B1386893
theorem B924611 : Blo 924580 924611 := bstep (se 1 (by rfl) ⟨693458, by rfl⟩ : syracuseStep 924611 = 1386917) B1386917
theorem B1317827 : Blo 924580 1317827 := bstep (se 1 (by rfl) ⟨988370, by rfl⟩ : syracuseStep 1317827 = 1976741) B1976741
theorem B924627 : Blo 924580 924627 := bstep (se 1 (by rfl) ⟨693470, by rfl⟩ : syracuseStep 924627 = 1386941) B1386941
theorem B924643 : Blo 924580 924643 := bstep (se 1 (by rfl) ⟨693482, by rfl⟩ : syracuseStep 924643 = 1386965) B1386965
theorem B4692977 : Blo 924580 4692977 := bstep (se 2 (by rfl) ⟨1759866, by rfl⟩ : syracuseStep 4692977 = 3519733) B3519733
theorem B924659 : Blo 924580 924659 := bstep (se 1 (by rfl) ⟨693494, by rfl⟩ : syracuseStep 924659 = 1386989) B1386989
theorem B924675 : Blo 924580 924675 := bstep (se 1 (by rfl) ⟨693506, by rfl⟩ : syracuseStep 924675 = 1387013) B1387013
theorem B924691 : Blo 924580 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B1317907 : Blo 924580 1317907 := bstep (se 1 (by rfl) ⟨988430, by rfl⟩ : syracuseStep 1317907 = 1976861) B1976861
theorem B1481761 : Blo 924580 1481761 := bstep (se 2 (by rfl) ⟨555660, by rfl⟩ : syracuseStep 1481761 = 1111321) B1111321
theorem B924707 : Blo 924580 924707 := bstep (se 1 (by rfl) ⟨693530, by rfl⟩ : syracuseStep 924707 = 1387061) B1387061
theorem B924723 : Blo 924580 924723 := bstep (se 1 (by rfl) ⟨693542, by rfl⟩ : syracuseStep 924723 = 1387085) B1387085
theorem B924739 : Blo 924580 924739 := bstep (se 1 (by rfl) ⟨693554, by rfl⟩ : syracuseStep 924739 = 1387109) B1387109
theorem B924755 : Blo 924580 924755 := bstep (se 1 (by rfl) ⟨693566, by rfl⟩ : syracuseStep 924755 = 1387133) B1387133
theorem B924771 : Blo 924580 924771 := bstep (se 1 (by rfl) ⟨693578, by rfl⟩ : syracuseStep 924771 = 1387157) B1387157
theorem B924787 : Blo 924580 924787 := bstep (se 1 (by rfl) ⟨693590, by rfl⟩ : syracuseStep 924787 = 1387181) B1387181
theorem B924803 : Blo 924580 924803 := bstep (se 1 (by rfl) ⟨693602, by rfl⟩ : syracuseStep 924803 = 1387205) B1387205
theorem B1875089 : Blo 924580 1875089 := bstep (se 2 (by rfl) ⟨703158, by rfl⟩ : syracuseStep 1875089 = 1406317) B1406317
theorem B924819 : Blo 924580 924819 := bstep (se 1 (by rfl) ⟨693614, by rfl⟩ : syracuseStep 924819 = 1387229) B1387229
theorem B924835 : Blo 924580 924835 := bstep (se 1 (by rfl) ⟨693626, by rfl⟩ : syracuseStep 924835 = 1387253) B1387253
theorem B924851 : Blo 924580 924851 := bstep (se 1 (by rfl) ⟨693638, by rfl⟩ : syracuseStep 924851 = 1387277) B1387277
theorem B924867 : Blo 924580 924867 := bstep (se 1 (by rfl) ⟨693650, by rfl⟩ : syracuseStep 924867 = 1387301) B1387301
theorem B5938373 : Blo 924580 5938373 := bstep (se 4 (by rfl) ⟨556722, by rfl⟩ : syracuseStep 5938373 = 1113445) B1113445
theorem B924883 : Blo 924580 924883 := bstep (se 1 (by rfl) ⟨693662, by rfl⟩ : syracuseStep 924883 = 1387325) B1387325
theorem B924899 : Blo 924580 924899 := bstep (se 1 (by rfl) ⟨693674, by rfl⟩ : syracuseStep 924899 = 1387349) B1387349
theorem B924915 : Blo 924580 924915 := bstep (se 1 (by rfl) ⟨693686, by rfl⟩ : syracuseStep 924915 = 1387373) B1387373
theorem B924931 : Blo 924580 924931 := bstep (se 1 (by rfl) ⟨693698, by rfl⟩ : syracuseStep 924931 = 1387397) B1387397
theorem B924947 : Blo 924580 924947 := bstep (se 1 (by rfl) ⟨693710, by rfl⟩ : syracuseStep 924947 = 1387421) B1387421
theorem B924963 : Blo 924580 924963 := bstep (se 1 (by rfl) ⟨693722, by rfl⟩ : syracuseStep 924963 = 1387445) B1387445
theorem B924979 : Blo 924580 924979 := bstep (se 1 (by rfl) ⟨693734, by rfl⟩ : syracuseStep 924979 = 1387469) B1387469
theorem B990515 : Blo 924580 990515 := bstep (se 1 (by rfl) ⟨742886, by rfl⟩ : syracuseStep 990515 = 1485773) B1485773
theorem B924995 : Blo 924580 924995 := bstep (se 1 (by rfl) ⟨693746, by rfl⟩ : syracuseStep 924995 = 1387493) B1387493
theorem B925011 : Blo 924580 925011 := bstep (se 1 (by rfl) ⟨693758, by rfl⟩ : syracuseStep 925011 = 1387517) B1387517
theorem B925027 : Blo 924580 925027 := bstep (se 1 (by rfl) ⟨693770, by rfl⟩ : syracuseStep 925027 = 1387541) B1387541
theorem B3120497 : Blo 924580 3120497 := bstep (se 2 (by rfl) ⟨1170186, by rfl⟩ : syracuseStep 3120497 = 2340373) B2340373
theorem B925043 : Blo 924580 925043 := bstep (se 1 (by rfl) ⟨693782, by rfl⟩ : syracuseStep 925043 = 1387565) B1387565
theorem B925059 : Blo 924580 925059 := bstep (se 1 (by rfl) ⟨693794, by rfl⟩ : syracuseStep 925059 = 1387589) B1387589
theorem B925075 : Blo 924580 925075 := bstep (se 1 (by rfl) ⟨693806, by rfl⟩ : syracuseStep 925075 = 1387613) B1387613
theorem B925091 : Blo 924580 925091 := bstep (se 1 (by rfl) ⟨693818, by rfl⟩ : syracuseStep 925091 = 1387637) B1387637
theorem B925107 : Blo 924580 925107 := bstep (se 1 (by rfl) ⟨693830, by rfl⟩ : syracuseStep 925107 = 1387661) B1387661
theorem B925123 : Blo 924580 925123 := bstep (se 1 (by rfl) ⟨693842, by rfl⟩ : syracuseStep 925123 = 1387685) B1387685
theorem B925139 : Blo 924580 925139 := bstep (se 1 (by rfl) ⟨693854, by rfl⟩ : syracuseStep 925139 = 1387709) B1387709
theorem B925155 : Blo 924580 925155 := bstep (se 1 (by rfl) ⟨693866, by rfl⟩ : syracuseStep 925155 = 1387733) B1387733
theorem B925171 : Blo 924580 925171 := bstep (se 1 (by rfl) ⟨693878, by rfl⟩ : syracuseStep 925171 = 1387757) B1387757
theorem B925187 : Blo 924580 925187 := bstep (se 1 (by rfl) ⟨693890, by rfl⟩ : syracuseStep 925187 = 1387781) B1387781
theorem B925203 : Blo 924580 925203 := bstep (se 1 (by rfl) ⟨693902, by rfl⟩ : syracuseStep 925203 = 1387805) B1387805
theorem B925219 : Blo 924580 925219 := bstep (se 1 (by rfl) ⟨693914, by rfl⟩ : syracuseStep 925219 = 1387829) B1387829
theorem B925235 : Blo 924580 925235 := bstep (se 1 (by rfl) ⟨693926, by rfl⟩ : syracuseStep 925235 = 1387853) B1387853
theorem B1318465 : Blo 924580 1318465 := bstep (se 2 (by rfl) ⟨494424, by rfl⟩ : syracuseStep 1318465 = 988849) B988849
theorem B925251 : Blo 924580 925251 := bstep (se 1 (by rfl) ⟨693938, by rfl⟩ : syracuseStep 925251 = 1387877) B1387877
theorem B8887877 : Blo 924580 8887877 := bstep (se 4 (by rfl) ⟨833238, by rfl⟩ : syracuseStep 8887877 = 1666477) B1666477
theorem B925267 : Blo 924580 925267 := bstep (se 1 (by rfl) ⟨693950, by rfl⟩ : syracuseStep 925267 = 1387901) B1387901
theorem B925283 : Blo 924580 925283 := bstep (se 1 (by rfl) ⟨693962, by rfl⟩ : syracuseStep 925283 = 1387925) B1387925
theorem B5283427 : Blo 924580 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B925299 : Blo 924580 925299 := bstep (se 1 (by rfl) ⟨693974, by rfl⟩ : syracuseStep 925299 = 1387949) B1387949
theorem B1482371 : Blo 924580 1482371 := bstep (se 1 (by rfl) ⟨1111778, by rfl⟩ : syracuseStep 1482371 = 2223557) B2223557
theorem B925315 : Blo 924580 925315 := bstep (se 1 (by rfl) ⟨693986, by rfl⟩ : syracuseStep 925315 = 1387973) B1387973
theorem B925331 : Blo 924580 925331 := bstep (se 1 (by rfl) ⟨693998, by rfl⟩ : syracuseStep 925331 = 1387997) B1387997
theorem B925347 : Blo 924580 925347 := bstep (se 1 (by rfl) ⟨694010, by rfl⟩ : syracuseStep 925347 = 1388021) B1388021
theorem B925363 : Blo 924580 925363 := bstep (se 1 (by rfl) ⟨694022, by rfl⟩ : syracuseStep 925363 = 1388045) B1388045
theorem B12689077 : Blo 924580 12689077 := bstep (se 5 (by rfl) ⟨594800, by rfl⟩ : syracuseStep 12689077 = 1189601) B1189601
theorem B925379 : Blo 924580 925379 := bstep (se 1 (by rfl) ⟨694034, by rfl⟩ : syracuseStep 925379 = 1388069) B1388069
theorem B925395 : Blo 924580 925395 := bstep (se 1 (by rfl) ⟨694046, by rfl⟩ : syracuseStep 925395 = 1388093) B1388093
theorem B925411 : Blo 924580 925411 := bstep (se 1 (by rfl) ⟨694058, by rfl⟩ : syracuseStep 925411 = 1388117) B1388117
theorem B925427 : Blo 924580 925427 := bstep (se 1 (by rfl) ⟨694070, by rfl⟩ : syracuseStep 925427 = 1388141) B1388141
theorem B925443 : Blo 924580 925443 := bstep (se 1 (by rfl) ⟨694082, by rfl⟩ : syracuseStep 925443 = 1388165) B1388165
theorem B925459 : Blo 924580 925459 := bstep (se 1 (by rfl) ⟨694094, by rfl⟩ : syracuseStep 925459 = 1388189) B1388189
theorem B925475 : Blo 924580 925475 := bstep (se 1 (by rfl) ⟨694106, by rfl⟩ : syracuseStep 925475 = 1388213) B1388213
theorem B925491 : Blo 924580 925491 := bstep (se 1 (by rfl) ⟨694118, by rfl⟩ : syracuseStep 925491 = 1388237) B1388237
theorem B925507 : Blo 924580 925507 := bstep (se 1 (by rfl) ⟨694130, by rfl⟩ : syracuseStep 925507 = 1388261) B1388261
theorem B925523 : Blo 924580 925523 := bstep (se 1 (by rfl) ⟨694142, by rfl⟩ : syracuseStep 925523 = 1388285) B1388285
theorem B925539 : Blo 924580 925539 := bstep (se 1 (by rfl) ⟨694154, by rfl⟩ : syracuseStep 925539 = 1388309) B1388309
theorem B925555 : Blo 924580 925555 := bstep (se 1 (by rfl) ⟨694166, by rfl⟩ : syracuseStep 925555 = 1388333) B1388333
theorem B925571 : Blo 924580 925571 := bstep (se 1 (by rfl) ⟨694178, by rfl⟩ : syracuseStep 925571 = 1388357) B1388357
theorem B3121037 : Blo 924580 3121037 := bstep (se 3 (by rfl) ⟨585194, by rfl⟩ : syracuseStep 3121037 = 1170389) B1170389
theorem B925587 : Blo 924580 925587 := bstep (se 1 (by rfl) ⟨694190, by rfl⟩ : syracuseStep 925587 = 1388381) B1388381
theorem B925603 : Blo 924580 925603 := bstep (se 1 (by rfl) ⟨694202, by rfl⟩ : syracuseStep 925603 = 1388405) B1388405
theorem B925619 : Blo 924580 925619 := bstep (se 1 (by rfl) ⟨694214, by rfl⟩ : syracuseStep 925619 = 1388429) B1388429
theorem B3121091 : Blo 924580 3121091 := bstep (se 1 (by rfl) ⟨2340818, by rfl⟩ : syracuseStep 3121091 = 4681637) B4681637
theorem B925635 : Blo 924580 925635 := bstep (se 1 (by rfl) ⟨694226, by rfl⟩ : syracuseStep 925635 = 1388453) B1388453
theorem B925651 : Blo 924580 925651 := bstep (se 1 (by rfl) ⟨694238, by rfl⟩ : syracuseStep 925651 = 1388477) B1388477
theorem B925667 : Blo 924580 925667 := bstep (se 1 (by rfl) ⟨694250, by rfl⟩ : syracuseStep 925667 = 1388501) B1388501
theorem B925683 : Blo 924580 925683 := bstep (se 1 (by rfl) ⟨694262, by rfl⟩ : syracuseStep 925683 = 1388525) B1388525
theorem B925699 : Blo 924580 925699 := bstep (se 1 (by rfl) ⟨694274, by rfl⟩ : syracuseStep 925699 = 1388549) B1388549
theorem B925715 : Blo 924580 925715 := bstep (se 1 (by rfl) ⟨694286, by rfl⟩ : syracuseStep 925715 = 1388573) B1388573
theorem B925731 : Blo 924580 925731 := bstep (se 1 (by rfl) ⟨694298, by rfl⟩ : syracuseStep 925731 = 1388597) B1388597
theorem B925747 : Blo 924580 925747 := bstep (se 1 (by rfl) ⟨694310, by rfl⟩ : syracuseStep 925747 = 1388621) B1388621
theorem B925763 : Blo 924580 925763 := bstep (se 1 (by rfl) ⟨694322, by rfl⟩ : syracuseStep 925763 = 1388645) B1388645
theorem B925779 : Blo 924580 925779 := bstep (se 1 (by rfl) ⟨694334, by rfl⟩ : syracuseStep 925779 = 1388669) B1388669
theorem B925795 : Blo 924580 925795 := bstep (se 1 (by rfl) ⟨694346, by rfl⟩ : syracuseStep 925795 = 1388693) B1388693
theorem B5283953 : Blo 924580 5283953 := bstep (se 2 (by rfl) ⟨1981482, by rfl⟩ : syracuseStep 5283953 = 3962965) B3962965
theorem B925811 : Blo 924580 925811 := bstep (se 1 (by rfl) ⟨694358, by rfl⟩ : syracuseStep 925811 = 1388717) B1388717
theorem B925827 : Blo 924580 925827 := bstep (se 1 (by rfl) ⟨694370, by rfl⟩ : syracuseStep 925827 = 1388741) B1388741
theorem B925843 : Blo 924580 925843 := bstep (se 1 (by rfl) ⟨694382, by rfl⟩ : syracuseStep 925843 = 1388765) B1388765
theorem B925859 : Blo 924580 925859 := bstep (se 1 (by rfl) ⟨694394, by rfl⟩ : syracuseStep 925859 = 1388789) B1388789
theorem B925875 : Blo 924580 925875 := bstep (se 1 (by rfl) ⟨694406, by rfl⟩ : syracuseStep 925875 = 1388813) B1388813
theorem B925891 : Blo 924580 925891 := bstep (se 1 (by rfl) ⟨694418, by rfl⟩ : syracuseStep 925891 = 1388837) B1388837
theorem B3121361 : Blo 924580 3121361 := bstep (se 2 (by rfl) ⟨1170510, by rfl⟩ : syracuseStep 3121361 = 2341021) B2341021
theorem B925907 : Blo 924580 925907 := bstep (se 1 (by rfl) ⟨694430, by rfl⟩ : syracuseStep 925907 = 1388861) B1388861
theorem B925923 : Blo 924580 925923 := bstep (se 1 (by rfl) ⟨694442, by rfl⟩ : syracuseStep 925923 = 1388885) B1388885
theorem B925939 : Blo 924580 925939 := bstep (se 1 (by rfl) ⟨694454, by rfl⟩ : syracuseStep 925939 = 1388909) B1388909
theorem B925955 : Blo 924580 925955 := bstep (se 1 (by rfl) ⟨694466, by rfl⟩ : syracuseStep 925955 = 1388933) B1388933
theorem B1319171 : Blo 924580 1319171 := bstep (se 1 (by rfl) ⟨989378, by rfl⟩ : syracuseStep 1319171 = 1978757) B1978757
theorem B925971 : Blo 924580 925971 := bstep (se 1 (by rfl) ⟨694478, by rfl⟩ : syracuseStep 925971 = 1388957) B1388957
theorem B925987 : Blo 924580 925987 := bstep (se 1 (by rfl) ⟨694490, by rfl⟩ : syracuseStep 925987 = 1388981) B1388981
theorem B926003 : Blo 924580 926003 := bstep (se 1 (by rfl) ⟨694502, by rfl⟩ : syracuseStep 926003 = 1389005) B1389005
theorem B926019 : Blo 924580 926019 := bstep (se 1 (by rfl) ⟨694514, by rfl⟩ : syracuseStep 926019 = 1389029) B1389029
theorem B926035 : Blo 924580 926035 := bstep (se 1 (by rfl) ⟨694526, by rfl⟩ : syracuseStep 926035 = 1389053) B1389053
theorem B926051 : Blo 924580 926051 := bstep (se 1 (by rfl) ⟨694538, by rfl⟩ : syracuseStep 926051 = 1389077) B1389077
theorem B926067 : Blo 924580 926067 := bstep (se 1 (by rfl) ⟨694550, by rfl⟩ : syracuseStep 926067 = 1389101) B1389101
theorem B926083 : Blo 924580 926083 := bstep (se 1 (by rfl) ⟨694562, by rfl⟩ : syracuseStep 926083 = 1389125) B1389125
theorem B926099 : Blo 924580 926099 := bstep (se 1 (by rfl) ⟨694574, by rfl⟩ : syracuseStep 926099 = 1389149) B1389149
theorem B926115 : Blo 924580 926115 := bstep (se 1 (by rfl) ⟨694586, by rfl⟩ : syracuseStep 926115 = 1389173) B1389173
theorem B4694435 : Blo 924580 4694435 := bstep (se 1 (by rfl) ⟨3520826, by rfl⟩ : syracuseStep 4694435 = 7041653) B7041653
theorem B926131 : Blo 924580 926131 := bstep (se 1 (by rfl) ⟨694598, by rfl⟩ : syracuseStep 926131 = 1389197) B1389197
theorem B926147 : Blo 924580 926147 := bstep (se 1 (by rfl) ⟨694610, by rfl⟩ : syracuseStep 926147 = 1389221) B1389221
theorem B926163 : Blo 924580 926163 := bstep (se 1 (by rfl) ⟨694622, by rfl⟩ : syracuseStep 926163 = 1389245) B1389245
theorem B926179 : Blo 924580 926179 := bstep (se 1 (by rfl) ⟨694634, by rfl⟩ : syracuseStep 926179 = 1389269) B1389269
theorem B926195 : Blo 924580 926195 := bstep (se 1 (by rfl) ⟨694646, by rfl⟩ : syracuseStep 926195 = 1389293) B1389293
theorem B926211 : Blo 924580 926211 := bstep (se 1 (by rfl) ⟨694658, by rfl⟩ : syracuseStep 926211 = 1389317) B1389317
theorem B926227 : Blo 924580 926227 := bstep (se 1 (by rfl) ⟨694670, by rfl⟩ : syracuseStep 926227 = 1389341) B1389341
theorem B926243 : Blo 924580 926243 := bstep (se 1 (by rfl) ⟨694682, by rfl⟩ : syracuseStep 926243 = 1389365) B1389365
theorem B926259 : Blo 924580 926259 := bstep (se 1 (by rfl) ⟨694694, by rfl⟩ : syracuseStep 926259 = 1389389) B1389389
theorem B926275 : Blo 924580 926275 := bstep (se 1 (by rfl) ⟨694706, by rfl⟩ : syracuseStep 926275 = 1389413) B1389413
theorem B926291 : Blo 924580 926291 := bstep (se 1 (by rfl) ⟨694718, by rfl⟩ : syracuseStep 926291 = 1389437) B1389437
theorem B1483363 : Blo 924580 1483363 := bstep (se 1 (by rfl) ⟨1112522, by rfl⟩ : syracuseStep 1483363 = 2225045) B2225045
theorem B926307 : Blo 924580 926307 := bstep (se 1 (by rfl) ⟨694730, by rfl⟩ : syracuseStep 926307 = 1389461) B1389461
theorem B926323 : Blo 924580 926323 := bstep (se 1 (by rfl) ⟨694742, by rfl⟩ : syracuseStep 926323 = 1389485) B1389485
theorem B926339 : Blo 924580 926339 := bstep (se 1 (by rfl) ⟨694754, by rfl⟩ : syracuseStep 926339 = 1389509) B1389509
theorem B926355 : Blo 924580 926355 := bstep (se 1 (by rfl) ⟨694766, by rfl⟩ : syracuseStep 926355 = 1389533) B1389533
theorem B926371 : Blo 924580 926371 := bstep (se 1 (by rfl) ⟨694778, by rfl⟩ : syracuseStep 926371 = 1389557) B1389557
theorem B926387 : Blo 924580 926387 := bstep (se 1 (by rfl) ⟨694790, by rfl⟩ : syracuseStep 926387 = 1389581) B1389581
theorem B926403 : Blo 924580 926403 := bstep (se 1 (by rfl) ⟨694802, by rfl⟩ : syracuseStep 926403 = 1389605) B1389605
theorem B926419 : Blo 924580 926419 := bstep (se 1 (by rfl) ⟨694814, by rfl⟩ : syracuseStep 926419 = 1389629) B1389629
theorem B926435 : Blo 924580 926435 := bstep (se 1 (by rfl) ⟨694826, by rfl⟩ : syracuseStep 926435 = 1389653) B1389653
theorem B3121901 : Blo 924580 3121901 := bstep (se 3 (by rfl) ⟨585356, by rfl⟩ : syracuseStep 3121901 = 1170713) B1170713
theorem B926451 : Blo 924580 926451 := bstep (se 1 (by rfl) ⟨694838, by rfl⟩ : syracuseStep 926451 = 1389677) B1389677
theorem B926467 : Blo 924580 926467 := bstep (se 1 (by rfl) ⟨694850, by rfl⟩ : syracuseStep 926467 = 1389701) B1389701
theorem B926483 : Blo 924580 926483 := bstep (se 1 (by rfl) ⟨694862, by rfl⟩ : syracuseStep 926483 = 1389725) B1389725
theorem B3121955 : Blo 924580 3121955 := bstep (se 1 (by rfl) ⟨2341466, by rfl⟩ : syracuseStep 3121955 = 4682933) B4682933
theorem B926499 : Blo 924580 926499 := bstep (se 1 (by rfl) ⟨694874, by rfl⟩ : syracuseStep 926499 = 1389749) B1389749
theorem B926515 : Blo 924580 926515 := bstep (se 1 (by rfl) ⟨694886, by rfl⟩ : syracuseStep 926515 = 1389773) B1389773
theorem B926531 : Blo 924580 926531 := bstep (se 1 (by rfl) ⟨694898, by rfl⟩ : syracuseStep 926531 = 1389797) B1389797
theorem B926547 : Blo 924580 926547 := bstep (se 1 (by rfl) ⟨694910, by rfl⟩ : syracuseStep 926547 = 1389821) B1389821
theorem B926563 : Blo 924580 926563 := bstep (se 1 (by rfl) ⟨694922, by rfl⟩ : syracuseStep 926563 = 1389845) B1389845
theorem B926579 : Blo 924580 926579 := bstep (se 1 (by rfl) ⟨694934, by rfl⟩ : syracuseStep 926579 = 1389869) B1389869
theorem B1319809 : Blo 924580 1319809 := bstep (se 2 (by rfl) ⟨494928, by rfl⟩ : syracuseStep 1319809 = 989857) B989857
theorem B926595 : Blo 924580 926595 := bstep (se 1 (by rfl) ⟨694946, by rfl⟩ : syracuseStep 926595 = 1389893) B1389893
theorem B926611 : Blo 924580 926611 := bstep (se 1 (by rfl) ⟨694958, by rfl⟩ : syracuseStep 926611 = 1389917) B1389917
theorem B926627 : Blo 924580 926627 := bstep (se 1 (by rfl) ⟨694970, by rfl⟩ : syracuseStep 926627 = 1389941) B1389941
theorem B926643 : Blo 924580 926643 := bstep (se 1 (by rfl) ⟨694982, by rfl⟩ : syracuseStep 926643 = 1389965) B1389965
theorem B926659 : Blo 924580 926659 := bstep (se 1 (by rfl) ⟨694994, by rfl⟩ : syracuseStep 926659 = 1389989) B1389989
theorem B926675 : Blo 924580 926675 := bstep (se 1 (by rfl) ⟨695006, by rfl⟩ : syracuseStep 926675 = 1390013) B1390013
theorem B926691 : Blo 924580 926691 := bstep (se 1 (by rfl) ⟨695018, by rfl⟩ : syracuseStep 926691 = 1390037) B1390037
theorem B926707 : Blo 924580 926707 := bstep (se 1 (by rfl) ⟨695030, by rfl⟩ : syracuseStep 926707 = 1390061) B1390061
theorem B1319923 : Blo 924580 1319923 := bstep (se 1 (by rfl) ⟨989942, by rfl⟩ : syracuseStep 1319923 = 1979885) B1979885
theorem B926723 : Blo 924580 926723 := bstep (se 1 (by rfl) ⟨695042, by rfl⟩ : syracuseStep 926723 = 1390085) B1390085
theorem B926739 : Blo 924580 926739 := bstep (se 1 (by rfl) ⟨695054, by rfl⟩ : syracuseStep 926739 = 1390109) B1390109
theorem B926755 : Blo 924580 926755 := bstep (se 1 (by rfl) ⟨695066, by rfl⟩ : syracuseStep 926755 = 1390133) B1390133
theorem B3122225 : Blo 924580 3122225 := bstep (se 2 (by rfl) ⟨1170834, by rfl⟩ : syracuseStep 3122225 = 2341669) B2341669
theorem B926771 : Blo 924580 926771 := bstep (se 1 (by rfl) ⟨695078, by rfl⟩ : syracuseStep 926771 = 1390157) B1390157
theorem B926787 : Blo 924580 926787 := bstep (se 1 (by rfl) ⟨695090, by rfl⟩ : syracuseStep 926787 = 1390181) B1390181
theorem B926803 : Blo 924580 926803 := bstep (se 1 (by rfl) ⟨695102, by rfl⟩ : syracuseStep 926803 = 1390205) B1390205
theorem B926819 : Blo 924580 926819 := bstep (se 1 (by rfl) ⟨695114, by rfl⟩ : syracuseStep 926819 = 1390229) B1390229
theorem B926835 : Blo 924580 926835 := bstep (se 1 (by rfl) ⟨695126, by rfl⟩ : syracuseStep 926835 = 1390253) B1390253
theorem B926851 : Blo 924580 926851 := bstep (se 1 (by rfl) ⟨695138, by rfl⟩ : syracuseStep 926851 = 1390277) B1390277
theorem B926867 : Blo 924580 926867 := bstep (se 1 (by rfl) ⟨695150, by rfl⟩ : syracuseStep 926867 = 1390301) B1390301
theorem B926883 : Blo 924580 926883 := bstep (se 1 (by rfl) ⟨695162, by rfl⟩ : syracuseStep 926883 = 1390325) B1390325
theorem B926899 : Blo 924580 926899 := bstep (se 1 (by rfl) ⟨695174, by rfl⟩ : syracuseStep 926899 = 1390349) B1390349
theorem B926915 : Blo 924580 926915 := bstep (se 1 (by rfl) ⟨695186, by rfl⟩ : syracuseStep 926915 = 1390373) B1390373
theorem B4695245 : Blo 924580 4695245 := bstep (se 3 (by rfl) ⟨880358, by rfl⟩ : syracuseStep 4695245 = 1760717) B1760717
theorem B926931 : Blo 924580 926931 := bstep (se 1 (by rfl) ⟨695198, by rfl⟩ : syracuseStep 926931 = 1390397) B1390397
theorem B926947 : Blo 924580 926947 := bstep (se 1 (by rfl) ⟨695210, by rfl⟩ : syracuseStep 926947 = 1390421) B1390421
theorem B3515633 : Blo 924580 3515633 := bstep (se 2 (by rfl) ⟨1318362, by rfl⟩ : syracuseStep 3515633 = 2636725) B2636725
theorem B926963 : Blo 924580 926963 := bstep (se 1 (by rfl) ⟨695222, by rfl⟩ : syracuseStep 926963 = 1390445) B1390445
theorem B926979 : Blo 924580 926979 := bstep (se 1 (by rfl) ⟨695234, by rfl⟩ : syracuseStep 926979 = 1390469) B1390469
theorem B926995 : Blo 924580 926995 := bstep (se 1 (by rfl) ⟨695246, by rfl⟩ : syracuseStep 926995 = 1390493) B1390493
theorem B927011 : Blo 924580 927011 := bstep (se 1 (by rfl) ⟨695258, by rfl⟩ : syracuseStep 927011 = 1390517) B1390517
theorem B927027 : Blo 924580 927027 := bstep (se 1 (by rfl) ⟨695270, by rfl⟩ : syracuseStep 927027 = 1390541) B1390541
theorem B927043 : Blo 924580 927043 := bstep (se 1 (by rfl) ⟨695282, by rfl⟩ : syracuseStep 927043 = 1390565) B1390565
theorem B927059 : Blo 924580 927059 := bstep (se 1 (by rfl) ⟨695294, by rfl⟩ : syracuseStep 927059 = 1390589) B1390589
theorem B927075 : Blo 924580 927075 := bstep (se 1 (by rfl) ⟨695306, by rfl⟩ : syracuseStep 927075 = 1390613) B1390613
theorem B927091 : Blo 924580 927091 := bstep (se 1 (by rfl) ⟨695318, by rfl⟩ : syracuseStep 927091 = 1390637) B1390637
theorem B927107 : Blo 924580 927107 := bstep (se 1 (by rfl) ⟨695330, by rfl⟩ : syracuseStep 927107 = 1390661) B1390661
theorem B927123 : Blo 924580 927123 := bstep (se 1 (by rfl) ⟨695342, by rfl⟩ : syracuseStep 927123 = 1390685) B1390685
theorem B927139 : Blo 924580 927139 := bstep (se 1 (by rfl) ⟨695354, by rfl⟩ : syracuseStep 927139 = 1390709) B1390709
theorem B927155 : Blo 924580 927155 := bstep (se 1 (by rfl) ⟨695366, by rfl⟩ : syracuseStep 927155 = 1390733) B1390733
theorem B927171 : Blo 924580 927171 := bstep (se 1 (by rfl) ⟨695378, by rfl⟩ : syracuseStep 927171 = 1390757) B1390757
theorem B16885189 : Blo 924580 16885189 := bstep (se 4 (by rfl) ⟨1582986, by rfl⟩ : syracuseStep 16885189 = 3165973) B3165973
theorem B927187 : Blo 924580 927187 := bstep (se 1 (by rfl) ⟨695390, by rfl⟩ : syracuseStep 927187 = 1390781) B1390781
theorem B927203 : Blo 924580 927203 := bstep (se 1 (by rfl) ⟨695402, by rfl⟩ : syracuseStep 927203 = 1390805) B1390805
theorem B1877489 : Blo 924580 1877489 := bstep (se 2 (by rfl) ⟨704058, by rfl⟩ : syracuseStep 1877489 = 1408117) B1408117
theorem B1484273 : Blo 924580 1484273 := bstep (se 2 (by rfl) ⟨556602, by rfl⟩ : syracuseStep 1484273 = 1113205) B1113205
theorem B927219 : Blo 924580 927219 := bstep (se 1 (by rfl) ⟨695414, by rfl⟩ : syracuseStep 927219 = 1390829) B1390829
theorem B927235 : Blo 924580 927235 := bstep (se 1 (by rfl) ⟨695426, by rfl⟩ : syracuseStep 927235 = 1390853) B1390853
theorem B927251 : Blo 924580 927251 := bstep (se 1 (by rfl) ⟨695438, by rfl⟩ : syracuseStep 927251 = 1390877) B1390877
theorem B927267 : Blo 924580 927267 := bstep (se 1 (by rfl) ⟨695450, by rfl⟩ : syracuseStep 927267 = 1390901) B1390901
theorem B5285411 : Blo 924580 5285411 := bstep (se 1 (by rfl) ⟨3964058, by rfl⟩ : syracuseStep 5285411 = 7928117) B7928117
theorem B927283 : Blo 924580 927283 := bstep (se 1 (by rfl) ⟨695462, by rfl⟩ : syracuseStep 927283 = 1390925) B1390925
theorem B48342581 : Blo 924580 48342581 := bstep (se 5 (by rfl) ⟨2266058, by rfl⟩ : syracuseStep 48342581 = 4532117) B4532117
theorem B927299 : Blo 924580 927299 := bstep (se 1 (by rfl) ⟨695474, by rfl⟩ : syracuseStep 927299 = 1390949) B1390949
theorem B3122765 : Blo 924580 3122765 := bstep (se 3 (by rfl) ⟨585518, by rfl⟩ : syracuseStep 3122765 = 1171037) B1171037
theorem B927315 : Blo 924580 927315 := bstep (se 1 (by rfl) ⟨695486, by rfl⟩ : syracuseStep 927315 = 1390973) B1390973
theorem B927331 : Blo 924580 927331 := bstep (se 1 (by rfl) ⟨695498, by rfl⟩ : syracuseStep 927331 = 1390997) B1390997
theorem B1484401 : Blo 924580 1484401 := bstep (se 2 (by rfl) ⟨556650, by rfl⟩ : syracuseStep 1484401 = 1113301) B1113301
theorem B927347 : Blo 924580 927347 := bstep (se 1 (by rfl) ⟨695510, by rfl⟩ : syracuseStep 927347 = 1391021) B1391021
theorem B3122819 : Blo 924580 3122819 := bstep (se 1 (by rfl) ⟨2342114, by rfl⟩ : syracuseStep 3122819 = 4684229) B4684229
theorem B927363 : Blo 924580 927363 := bstep (se 1 (by rfl) ⟨695522, by rfl⟩ : syracuseStep 927363 = 1391045) B1391045
theorem B927379 : Blo 924580 927379 := bstep (se 1 (by rfl) ⟨695534, by rfl⟩ : syracuseStep 927379 = 1391069) B1391069
theorem B927395 : Blo 924580 927395 := bstep (se 1 (by rfl) ⟨695546, by rfl⟩ : syracuseStep 927395 = 1391093) B1391093
theorem B927411 : Blo 924580 927411 := bstep (se 1 (by rfl) ⟨695558, by rfl⟩ : syracuseStep 927411 = 1391117) B1391117
theorem B927427 : Blo 924580 927427 := bstep (se 1 (by rfl) ⟨695570, by rfl⟩ : syracuseStep 927427 = 1391141) B1391141
theorem B927443 : Blo 924580 927443 := bstep (se 1 (by rfl) ⟨695582, by rfl⟩ : syracuseStep 927443 = 1391165) B1391165
theorem B927459 : Blo 924580 927459 := bstep (se 1 (by rfl) ⟨695594, by rfl⟩ : syracuseStep 927459 = 1391189) B1391189
theorem B927475 : Blo 924580 927475 := bstep (se 1 (by rfl) ⟨695606, by rfl⟩ : syracuseStep 927475 = 1391213) B1391213
theorem B927491 : Blo 924580 927491 := bstep (se 1 (by rfl) ⟨695618, by rfl⟩ : syracuseStep 927491 = 1391237) B1391237
theorem B927507 : Blo 924580 927507 := bstep (se 1 (by rfl) ⟨695630, by rfl⟩ : syracuseStep 927507 = 1391261) B1391261
theorem B927523 : Blo 924580 927523 := bstep (se 1 (by rfl) ⟨695642, by rfl⟩ : syracuseStep 927523 = 1391285) B1391285
theorem B927539 : Blo 924580 927539 := bstep (se 1 (by rfl) ⟨695654, by rfl⟩ : syracuseStep 927539 = 1391309) B1391309
theorem B1288003 : Blo 924580 1288003 := bstep (se 1 (by rfl) ⟨966002, by rfl⟩ : syracuseStep 1288003 = 1932005) B1932005
theorem B927555 : Blo 924580 927555 := bstep (se 1 (by rfl) ⟨695666, by rfl⟩ : syracuseStep 927555 = 1391333) B1391333
theorem B927571 : Blo 924580 927571 := bstep (se 1 (by rfl) ⟨695678, by rfl⟩ : syracuseStep 927571 = 1391357) B1391357
theorem B927587 : Blo 924580 927587 := bstep (se 1 (by rfl) ⟨695690, by rfl⟩ : syracuseStep 927587 = 1391381) B1391381
theorem B1976177 : Blo 924580 1976177 := bstep (se 2 (by rfl) ⟨741066, by rfl⟩ : syracuseStep 1976177 = 1482133) B1482133
theorem B927603 : Blo 924580 927603 := bstep (se 1 (by rfl) ⟨695702, by rfl⟩ : syracuseStep 927603 = 1391405) B1391405
theorem B927619 : Blo 924580 927619 := bstep (se 1 (by rfl) ⟨695714, by rfl⟩ : syracuseStep 927619 = 1391429) B1391429
theorem B3123089 : Blo 924580 3123089 := bstep (se 2 (by rfl) ⟨1171158, by rfl⟩ : syracuseStep 3123089 = 2342317) B2342317
theorem B927635 : Blo 924580 927635 := bstep (se 1 (by rfl) ⟨695726, by rfl⟩ : syracuseStep 927635 = 1391453) B1391453
theorem B927651 : Blo 924580 927651 := bstep (se 1 (by rfl) ⟨695738, by rfl⟩ : syracuseStep 927651 = 1391477) B1391477
theorem B927667 : Blo 924580 927667 := bstep (se 1 (by rfl) ⟨695750, by rfl⟩ : syracuseStep 927667 = 1391501) B1391501
theorem B927683 : Blo 924580 927683 := bstep (se 1 (by rfl) ⟨695762, by rfl⟩ : syracuseStep 927683 = 1391525) B1391525
theorem B1058755 : Blo 924580 1058755 := bstep (se 1 (by rfl) ⟨794066, by rfl⟩ : syracuseStep 1058755 = 1588133) B1588133
theorem B927699 : Blo 924580 927699 := bstep (se 1 (by rfl) ⟨695774, by rfl⟩ : syracuseStep 927699 = 1391549) B1391549
theorem B927715 : Blo 924580 927715 := bstep (se 1 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 927715 = 1391573) B1391573
theorem B927731 : Blo 924580 927731 := bstep (se 1 (by rfl) ⟨695798, by rfl⟩ : syracuseStep 927731 = 1391597) B1391597
theorem B927747 : Blo 924580 927747 := bstep (se 1 (by rfl) ⟨695810, by rfl⟩ : syracuseStep 927747 = 1391621) B1391621
theorem B6334469 : Blo 924580 6334469 := bstep (se 4 (by rfl) ⟨593856, by rfl⟩ : syracuseStep 6334469 = 1187713) B1187713
theorem B927763 : Blo 924580 927763 := bstep (se 1 (by rfl) ⟨695822, by rfl⟩ : syracuseStep 927763 = 1391645) B1391645
theorem B927779 : Blo 924580 927779 := bstep (se 1 (by rfl) ⟨695834, by rfl⟩ : syracuseStep 927779 = 1391669) B1391669
theorem B927795 : Blo 924580 927795 := bstep (se 1 (by rfl) ⟨695846, by rfl⟩ : syracuseStep 927795 = 1391693) B1391693
theorem B927811 : Blo 924580 927811 := bstep (se 1 (by rfl) ⟨695858, by rfl⟩ : syracuseStep 927811 = 1391717) B1391717
theorem B927827 : Blo 924580 927827 := bstep (se 1 (by rfl) ⟨695870, by rfl⟩ : syracuseStep 927827 = 1391741) B1391741
theorem B927843 : Blo 924580 927843 := bstep (se 1 (by rfl) ⟨695882, by rfl⟩ : syracuseStep 927843 = 1391765) B1391765
theorem B927859 : Blo 924580 927859 := bstep (se 1 (by rfl) ⟨695894, by rfl⟩ : syracuseStep 927859 = 1391789) B1391789
theorem B927875 : Blo 924580 927875 := bstep (se 1 (by rfl) ⟨695906, by rfl⟩ : syracuseStep 927875 = 1391813) B1391813
theorem B927891 : Blo 924580 927891 := bstep (se 1 (by rfl) ⟨695918, by rfl⟩ : syracuseStep 927891 = 1391837) B1391837
theorem B927907 : Blo 924580 927907 := bstep (se 1 (by rfl) ⟨695930, by rfl⟩ : syracuseStep 927907 = 1391861) B1391861
theorem B927923 : Blo 924580 927923 := bstep (se 1 (by rfl) ⟨695942, by rfl⟩ : syracuseStep 927923 = 1391885) B1391885
theorem B927939 : Blo 924580 927939 := bstep (se 1 (by rfl) ⟨695954, by rfl⟩ : syracuseStep 927939 = 1391909) B1391909
theorem B927955 : Blo 924580 927955 := bstep (se 1 (by rfl) ⟨695966, by rfl⟩ : syracuseStep 927955 = 1391933) B1391933
theorem B927971 : Blo 924580 927971 := bstep (se 1 (by rfl) ⟨695978, by rfl⟩ : syracuseStep 927971 = 1391957) B1391957
theorem B927987 : Blo 924580 927987 := bstep (se 1 (by rfl) ⟨695990, by rfl⟩ : syracuseStep 927987 = 1391981) B1391981
theorem B928003 : Blo 924580 928003 := bstep (se 1 (by rfl) ⟨696002, by rfl⟩ : syracuseStep 928003 = 1392005) B1392005
theorem B928019 : Blo 924580 928019 := bstep (se 1 (by rfl) ⟨696014, by rfl⟩ : syracuseStep 928019 = 1392029) B1392029
theorem B928035 : Blo 924580 928035 := bstep (se 1 (by rfl) ⟨696026, by rfl⟩ : syracuseStep 928035 = 1392053) B1392053
theorem B1321267 : Blo 924580 1321267 := bstep (se 1 (by rfl) ⟨990950, by rfl⟩ : syracuseStep 1321267 = 1981901) B1981901
theorem B928051 : Blo 924580 928051 := bstep (se 1 (by rfl) ⟨696038, by rfl⟩ : syracuseStep 928051 = 1392077) B1392077
theorem B928067 : Blo 924580 928067 := bstep (se 1 (by rfl) ⟨696050, by rfl⟩ : syracuseStep 928067 = 1392101) B1392101
theorem B928083 : Blo 924580 928083 := bstep (se 1 (by rfl) ⟨696062, by rfl⟩ : syracuseStep 928083 = 1392125) B1392125
theorem B928099 : Blo 924580 928099 := bstep (se 1 (by rfl) ⟨696074, by rfl⟩ : syracuseStep 928099 = 1392149) B1392149
theorem B928115 : Blo 924580 928115 := bstep (se 1 (by rfl) ⟨696086, by rfl⟩ : syracuseStep 928115 = 1392173) B1392173
theorem B1386881 : Blo 924580 1386881 := bstep (se 2 (by rfl) ⟨520080, by rfl⟩ : syracuseStep 1386881 = 1040161) B1040161
theorem B928131 : Blo 924580 928131 := bstep (se 1 (by rfl) ⟨696098, by rfl⟩ : syracuseStep 928131 = 1392197) B1392197
theorem B1386899 : Blo 924580 1386899 := bstep (se 1 (by rfl) ⟨1040174, by rfl⟩ : syracuseStep 1386899 = 2080349) B2080349
theorem B928147 : Blo 924580 928147 := bstep (se 1 (by rfl) ⟨696110, by rfl⟩ : syracuseStep 928147 = 1392221) B1392221
theorem B928163 : Blo 924580 928163 := bstep (se 1 (by rfl) ⟨696122, by rfl⟩ : syracuseStep 928163 = 1392245) B1392245
theorem B3123629 : Blo 924580 3123629 := bstep (se 3 (by rfl) ⟨585680, by rfl⟩ : syracuseStep 3123629 = 1171361) B1171361
theorem B1386929 : Blo 924580 1386929 := bstep (se 2 (by rfl) ⟨520098, by rfl⟩ : syracuseStep 1386929 = 1040197) B1040197
theorem B928179 : Blo 924580 928179 := bstep (se 1 (by rfl) ⟨696134, by rfl⟩ : syracuseStep 928179 = 1392269) B1392269
theorem B1386947 : Blo 924580 1386947 := bstep (se 1 (by rfl) ⟨1040210, by rfl⟩ : syracuseStep 1386947 = 2080421) B2080421
theorem B928195 : Blo 924580 928195 := bstep (se 1 (by rfl) ⟨696146, by rfl⟩ : syracuseStep 928195 = 1392293) B1392293
theorem B928211 : Blo 924580 928211 := bstep (se 1 (by rfl) ⟨696158, by rfl⟩ : syracuseStep 928211 = 1392317) B1392317
theorem B1386977 : Blo 924580 1386977 := bstep (se 2 (by rfl) ⟨520116, by rfl⟩ : syracuseStep 1386977 = 1040233) B1040233
theorem B3123683 : Blo 924580 3123683 := bstep (se 1 (by rfl) ⟨2342762, by rfl⟩ : syracuseStep 3123683 = 4685525) B4685525
theorem B928227 : Blo 924580 928227 := bstep (se 1 (by rfl) ⟨696170, by rfl⟩ : syracuseStep 928227 = 1392341) B1392341
theorem B1386995 : Blo 924580 1386995 := bstep (se 1 (by rfl) ⟨1040246, by rfl⟩ : syracuseStep 1386995 = 2080493) B2080493
theorem B928243 : Blo 924580 928243 := bstep (se 1 (by rfl) ⟨696182, by rfl⟩ : syracuseStep 928243 = 1392365) B1392365
theorem B928259 : Blo 924580 928259 := bstep (se 1 (by rfl) ⟨696194, by rfl⟩ : syracuseStep 928259 = 1392389) B1392389
theorem B1387025 : Blo 924580 1387025 := bstep (se 2 (by rfl) ⟨520134, by rfl⟩ : syracuseStep 1387025 = 1040269) B1040269
theorem B928275 : Blo 924580 928275 := bstep (se 1 (by rfl) ⟨696206, by rfl⟩ : syracuseStep 928275 = 1392413) B1392413
theorem B1387043 : Blo 924580 1387043 := bstep (se 1 (by rfl) ⟨1040282, by rfl⟩ : syracuseStep 1387043 = 2080565) B2080565
theorem B928291 : Blo 924580 928291 := bstep (se 1 (by rfl) ⟨696218, by rfl⟩ : syracuseStep 928291 = 1392437) B1392437
theorem B928307 : Blo 924580 928307 := bstep (se 1 (by rfl) ⟨696230, by rfl⟩ : syracuseStep 928307 = 1392461) B1392461
theorem B1387073 : Blo 924580 1387073 := bstep (se 2 (by rfl) ⟨520152, by rfl⟩ : syracuseStep 1387073 = 1040305) B1040305
theorem B928323 : Blo 924580 928323 := bstep (se 1 (by rfl) ⟨696242, by rfl⟩ : syracuseStep 928323 = 1392485) B1392485
theorem B1387091 : Blo 924580 1387091 := bstep (se 1 (by rfl) ⟨1040318, by rfl⟩ : syracuseStep 1387091 = 2080637) B2080637
theorem B1485395 : Blo 924580 1485395 := bstep (se 1 (by rfl) ⟨1114046, by rfl⟩ : syracuseStep 1485395 = 2228093) B2228093
theorem B928339 : Blo 924580 928339 := bstep (se 1 (by rfl) ⟨696254, by rfl⟩ : syracuseStep 928339 = 1392509) B1392509
theorem B928355 : Blo 924580 928355 := bstep (se 1 (by rfl) ⟨696266, by rfl⟩ : syracuseStep 928355 = 1392533) B1392533
theorem B1387121 : Blo 924580 1387121 := bstep (se 2 (by rfl) ⟨520170, by rfl⟩ : syracuseStep 1387121 = 1040341) B1040341
theorem B928371 : Blo 924580 928371 := bstep (se 1 (by rfl) ⟨696278, by rfl⟩ : syracuseStep 928371 = 1392557) B1392557
theorem B1387139 : Blo 924580 1387139 := bstep (se 1 (by rfl) ⟨1040354, by rfl⟩ : syracuseStep 1387139 = 2080709) B2080709
theorem B928387 : Blo 924580 928387 := bstep (se 1 (by rfl) ⟨696290, by rfl⟩ : syracuseStep 928387 = 1392581) B1392581
theorem B928403 : Blo 924580 928403 := bstep (se 1 (by rfl) ⟨696302, by rfl⟩ : syracuseStep 928403 = 1392605) B1392605
theorem B1387169 : Blo 924580 1387169 := bstep (se 2 (by rfl) ⟨520188, by rfl⟩ : syracuseStep 1387169 = 1040377) B1040377
theorem B3517091 : Blo 924580 3517091 := bstep (se 1 (by rfl) ⟨2637818, by rfl⟩ : syracuseStep 3517091 = 5275637) B5275637
theorem B928419 : Blo 924580 928419 := bstep (se 1 (by rfl) ⟨696314, by rfl⟩ : syracuseStep 928419 = 1392629) B1392629
theorem B1387187 : Blo 924580 1387187 := bstep (se 1 (by rfl) ⟨1040390, by rfl⟩ : syracuseStep 1387187 = 2080781) B2080781
theorem B928435 : Blo 924580 928435 := bstep (se 1 (by rfl) ⟨696326, by rfl⟩ : syracuseStep 928435 = 1392653) B1392653
theorem B928451 : Blo 924580 928451 := bstep (se 1 (by rfl) ⟨696338, by rfl⟩ : syracuseStep 928451 = 1392677) B1392677
theorem B11250373 : Blo 924580 11250373 := bstep (se 4 (by rfl) ⟨1054722, by rfl⟩ : syracuseStep 11250373 = 2109445) B2109445
theorem B1387217 : Blo 924580 1387217 := bstep (se 2 (by rfl) ⟨520206, by rfl⟩ : syracuseStep 1387217 = 1040413) B1040413
theorem B1977041 : Blo 924580 1977041 := bstep (se 2 (by rfl) ⟨741390, by rfl⟩ : syracuseStep 1977041 = 1482781) B1482781
theorem B928467 : Blo 924580 928467 := bstep (se 1 (by rfl) ⟨696350, by rfl⟩ : syracuseStep 928467 = 1392701) B1392701
theorem B1387235 : Blo 924580 1387235 := bstep (se 1 (by rfl) ⟨1040426, by rfl⟩ : syracuseStep 1387235 = 2080853) B2080853
theorem B928483 : Blo 924580 928483 := bstep (se 1 (by rfl) ⟨696362, by rfl⟩ : syracuseStep 928483 = 1392725) B1392725
theorem B3123953 : Blo 924580 3123953 := bstep (se 2 (by rfl) ⟨1171482, by rfl⟩ : syracuseStep 3123953 = 2342965) B2342965
theorem B1583857 : Blo 924580 1583857 := bstep (se 2 (by rfl) ⟨593946, by rfl⟩ : syracuseStep 1583857 = 1187893) B1187893
theorem B928499 : Blo 924580 928499 := bstep (se 1 (by rfl) ⟨696374, by rfl⟩ : syracuseStep 928499 = 1392749) B1392749
theorem B1387265 : Blo 924580 1387265 := bstep (se 2 (by rfl) ⟨520224, by rfl⟩ : syracuseStep 1387265 = 1040449) B1040449
theorem B928515 : Blo 924580 928515 := bstep (se 1 (by rfl) ⟨696386, by rfl⟩ : syracuseStep 928515 = 1392773) B1392773
theorem B1387283 : Blo 924580 1387283 := bstep (se 1 (by rfl) ⟨1040462, by rfl⟩ : syracuseStep 1387283 = 2080925) B2080925
theorem B928531 : Blo 924580 928531 := bstep (se 1 (by rfl) ⟨696398, by rfl⟩ : syracuseStep 928531 = 1392797) B1392797
theorem B928547 : Blo 924580 928547 := bstep (se 1 (by rfl) ⟨696410, by rfl⟩ : syracuseStep 928547 = 1392821) B1392821
theorem B1387313 : Blo 924580 1387313 := bstep (se 2 (by rfl) ⟨520242, by rfl⟩ : syracuseStep 1387313 = 1040485) B1040485
theorem B928563 : Blo 924580 928563 := bstep (se 1 (by rfl) ⟨696422, by rfl⟩ : syracuseStep 928563 = 1392845) B1392845
theorem B1387331 : Blo 924580 1387331 := bstep (se 1 (by rfl) ⟨1040498, by rfl⟩ : syracuseStep 1387331 = 2080997) B2080997
theorem B928579 : Blo 924580 928579 := bstep (se 1 (by rfl) ⟨696434, by rfl⟩ : syracuseStep 928579 = 1392869) B1392869
theorem B1387361 : Blo 924580 1387361 := bstep (se 2 (by rfl) ⟨520260, by rfl⟩ : syracuseStep 1387361 = 1040521) B1040521
theorem B1387379 : Blo 924580 1387379 := bstep (se 1 (by rfl) ⟨1040534, by rfl⟩ : syracuseStep 1387379 = 2081069) B2081069
theorem B6761357 : Blo 924580 6761357 := bstep (se 3 (by rfl) ⟨1267754, by rfl⟩ : syracuseStep 6761357 = 2535509) B2535509
theorem B1387409 : Blo 924580 1387409 := bstep (se 2 (by rfl) ⟨520278, by rfl⟩ : syracuseStep 1387409 = 1040557) B1040557
theorem B1387427 : Blo 924580 1387427 := bstep (se 1 (by rfl) ⟨1040570, by rfl⟩ : syracuseStep 1387427 = 2081141) B2081141
theorem B1387457 : Blo 924580 1387457 := bstep (se 2 (by rfl) ⟨520296, by rfl⟩ : syracuseStep 1387457 = 1040593) B1040593
theorem B1387475 : Blo 924580 1387475 := bstep (se 1 (by rfl) ⟨1040606, by rfl⟩ : syracuseStep 1387475 = 2081213) B2081213
theorem B1387505 : Blo 924580 1387505 := bstep (se 2 (by rfl) ⟨520314, by rfl⟩ : syracuseStep 1387505 = 1040629) B1040629
theorem B1387523 : Blo 924580 1387523 := bstep (se 1 (by rfl) ⟨1040642, by rfl⟩ : syracuseStep 1387523 = 2081285) B2081285
theorem B1387553 : Blo 924580 1387553 := bstep (se 2 (by rfl) ⟨520332, by rfl⟩ : syracuseStep 1387553 = 1040665) B1040665
theorem B5942321 : Blo 924580 5942321 := bstep (se 2 (by rfl) ⟨2228370, by rfl⟩ : syracuseStep 5942321 = 4456741) B4456741
theorem B1387571 : Blo 924580 1387571 := bstep (se 1 (by rfl) ⟨1040678, by rfl⟩ : syracuseStep 1387571 = 2081357) B2081357
theorem B1387601 : Blo 924580 1387601 := bstep (se 2 (by rfl) ⟨520350, by rfl⟩ : syracuseStep 1387601 = 1040701) B1040701
theorem B1387619 : Blo 924580 1387619 := bstep (se 1 (by rfl) ⟨1040714, by rfl⟩ : syracuseStep 1387619 = 2081429) B2081429
theorem B1387649 : Blo 924580 1387649 := bstep (se 2 (by rfl) ⟨520368, by rfl⟩ : syracuseStep 1387649 = 1040737) B1040737
theorem B1387667 : Blo 924580 1387667 := bstep (se 1 (by rfl) ⟨1040750, by rfl⟩ : syracuseStep 1387667 = 2081501) B2081501
theorem B1387697 : Blo 924580 1387697 := bstep (se 2 (by rfl) ⟨520386, by rfl⟩ : syracuseStep 1387697 = 1040773) B1040773
theorem B1387715 : Blo 924580 1387715 := bstep (se 1 (by rfl) ⟨1040786, by rfl⟩ : syracuseStep 1387715 = 2081573) B2081573
theorem B1387745 : Blo 924580 1387745 := bstep (se 2 (by rfl) ⟨520404, by rfl⟩ : syracuseStep 1387745 = 1040809) B1040809
theorem B1387763 : Blo 924580 1387763 := bstep (se 1 (by rfl) ⟨1040822, by rfl⟩ : syracuseStep 1387763 = 2081645) B2081645
theorem B3124493 : Blo 924580 3124493 := bstep (se 3 (by rfl) ⟨585842, by rfl⟩ : syracuseStep 3124493 = 1171685) B1171685
theorem B1387793 : Blo 924580 1387793 := bstep (se 2 (by rfl) ⟨520422, by rfl⟩ : syracuseStep 1387793 = 1040845) B1040845
theorem B1387811 : Blo 924580 1387811 := bstep (se 1 (by rfl) ⟨1040858, by rfl⟩ : syracuseStep 1387811 = 2081717) B2081717
theorem B1781041 : Blo 924580 1781041 := bstep (se 2 (by rfl) ⟨667890, by rfl⟩ : syracuseStep 1781041 = 1335781) B1335781
theorem B1387841 : Blo 924580 1387841 := bstep (se 2 (by rfl) ⟨520440, by rfl⟩ : syracuseStep 1387841 = 1040881) B1040881
theorem B3124547 : Blo 924580 3124547 := bstep (se 1 (by rfl) ⟨2343410, by rfl⟩ : syracuseStep 3124547 = 4686821) B4686821
theorem B1387859 : Blo 924580 1387859 := bstep (se 1 (by rfl) ⟨1040894, by rfl⟩ : syracuseStep 1387859 = 2081789) B2081789
theorem B1387889 : Blo 924580 1387889 := bstep (se 2 (by rfl) ⟨520458, by rfl⟩ : syracuseStep 1387889 = 1040917) B1040917
theorem B1387907 : Blo 924580 1387907 := bstep (se 1 (by rfl) ⟨1040930, by rfl⟩ : syracuseStep 1387907 = 2081861) B2081861
theorem B5287301 : Blo 924580 5287301 := bstep (se 4 (by rfl) ⟨495684, by rfl⟩ : syracuseStep 5287301 = 991369) B991369
theorem B2502029 : Blo 924580 2502029 := bstep (se 3 (by rfl) ⟨469130, by rfl⟩ : syracuseStep 2502029 = 938261) B938261
theorem B1387937 : Blo 924580 1387937 := bstep (se 2 (by rfl) ⟨520476, by rfl⟩ : syracuseStep 1387937 = 1040953) B1040953
theorem B1387955 : Blo 924580 1387955 := bstep (se 1 (by rfl) ⟨1040966, by rfl⟩ : syracuseStep 1387955 = 2081933) B2081933
theorem B1387985 : Blo 924580 1387985 := bstep (se 2 (by rfl) ⟨520494, by rfl⟩ : syracuseStep 1387985 = 1040989) B1040989
theorem B1388003 : Blo 924580 1388003 := bstep (se 1 (by rfl) ⟨1041002, by rfl⟩ : syracuseStep 1388003 = 2082005) B2082005
theorem B1388033 : Blo 924580 1388033 := bstep (se 2 (by rfl) ⟨520512, by rfl⟩ : syracuseStep 1388033 = 1041025) B1041025
theorem B2502161 : Blo 924580 2502161 := bstep (se 2 (by rfl) ⟨938310, by rfl⟩ : syracuseStep 2502161 = 1876621) B1876621
theorem B1388051 : Blo 924580 1388051 := bstep (se 1 (by rfl) ⟨1041038, by rfl⟩ : syracuseStep 1388051 = 2082077) B2082077
theorem B2108963 : Blo 924580 2108963 := bstep (se 1 (by rfl) ⟨1581722, by rfl⟩ : syracuseStep 2108963 = 3163445) B3163445
theorem B1388081 : Blo 924580 1388081 := bstep (se 2 (by rfl) ⟨520530, by rfl⟩ : syracuseStep 1388081 = 1041061) B1041061
theorem B1388099 : Blo 924580 1388099 := bstep (se 1 (by rfl) ⟨1041074, by rfl⟩ : syracuseStep 1388099 = 2082149) B2082149
theorem B3124817 : Blo 924580 3124817 := bstep (se 2 (by rfl) ⟨1171806, by rfl⟩ : syracuseStep 3124817 = 2343613) B2343613
theorem B1388129 : Blo 924580 1388129 := bstep (se 2 (by rfl) ⟨520548, by rfl⟩ : syracuseStep 1388129 = 1041097) B1041097
theorem B4763249 : Blo 924580 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B1388147 : Blo 924580 1388147 := bstep (se 1 (by rfl) ⟨1041110, by rfl⟩ : syracuseStep 1388147 = 2082221) B2082221
theorem B3518093 : Blo 924580 3518093 := bstep (se 3 (by rfl) ⟨659642, by rfl⟩ : syracuseStep 3518093 = 1319285) B1319285
theorem B1388177 : Blo 924580 1388177 := bstep (se 2 (by rfl) ⟨520566, by rfl⟩ : syracuseStep 1388177 = 1041133) B1041133
theorem B2502289 : Blo 924580 2502289 := bstep (se 2 (by rfl) ⟨938358, by rfl⟩ : syracuseStep 2502289 = 1876717) B1876717
theorem B1388195 : Blo 924580 1388195 := bstep (se 1 (by rfl) ⟨1041146, by rfl⟩ : syracuseStep 1388195 = 2082293) B2082293
theorem B1388225 : Blo 924580 1388225 := bstep (se 2 (by rfl) ⟨520584, by rfl⟩ : syracuseStep 1388225 = 1041169) B1041169
theorem B2633411 : Blo 924580 2633411 := bstep (se 1 (by rfl) ⟨1975058, by rfl⟩ : syracuseStep 2633411 = 3950117) B3950117
theorem B1388243 : Blo 924580 1388243 := bstep (se 1 (by rfl) ⟨1041182, by rfl⟩ : syracuseStep 1388243 = 2082365) B2082365
theorem B1388273 : Blo 924580 1388273 := bstep (se 2 (by rfl) ⟨520602, by rfl⟩ : syracuseStep 1388273 = 1041205) B1041205
theorem B1388291 : Blo 924580 1388291 := bstep (se 1 (by rfl) ⟨1041218, by rfl⟩ : syracuseStep 1388291 = 2082437) B2082437
theorem B1388321 : Blo 924580 1388321 := bstep (se 2 (by rfl) ⟨520620, by rfl⟩ : syracuseStep 1388321 = 1041241) B1041241
theorem B1388339 : Blo 924580 1388339 := bstep (se 1 (by rfl) ⟨1041254, by rfl⟩ : syracuseStep 1388339 = 2082509) B2082509
theorem B1388369 : Blo 924580 1388369 := bstep (se 2 (by rfl) ⟨520638, by rfl⟩ : syracuseStep 1388369 = 1041277) B1041277
theorem B1388387 : Blo 924580 1388387 := bstep (se 1 (by rfl) ⟨1041290, by rfl⟩ : syracuseStep 1388387 = 2082581) B2082581
theorem B1388417 : Blo 924580 1388417 := bstep (se 2 (by rfl) ⟨520656, by rfl⟩ : syracuseStep 1388417 = 1041313) B1041313
theorem B1388435 : Blo 924580 1388435 := bstep (se 1 (by rfl) ⟨1041326, by rfl⟩ : syracuseStep 1388435 = 2082653) B2082653
theorem B1388465 : Blo 924580 1388465 := bstep (se 2 (by rfl) ⟨520674, by rfl⟩ : syracuseStep 1388465 = 1041349) B1041349
theorem B1388483 : Blo 924580 1388483 := bstep (se 1 (by rfl) ⟨1041362, by rfl⟩ : syracuseStep 1388483 = 2082725) B2082725
theorem B1388513 : Blo 924580 1388513 := bstep (se 2 (by rfl) ⟨520692, by rfl⟩ : syracuseStep 1388513 = 1041385) B1041385
theorem B1978339 : Blo 924580 1978339 := bstep (se 1 (by rfl) ⟨1483754, by rfl⟩ : syracuseStep 1978339 = 2967509) B2967509
theorem B1388531 : Blo 924580 1388531 := bstep (se 1 (by rfl) ⟨1041398, by rfl⟩ : syracuseStep 1388531 = 2082797) B2082797
theorem B1486849 : Blo 924580 1486849 := bstep (se 2 (by rfl) ⟨557568, by rfl⟩ : syracuseStep 1486849 = 1115137) B1115137
theorem B2633741 : Blo 924580 2633741 := bstep (se 3 (by rfl) ⟨493826, by rfl⟩ : syracuseStep 2633741 = 987653) B987653
theorem B1388561 : Blo 924580 1388561 := bstep (se 2 (by rfl) ⟨520710, by rfl⟩ : syracuseStep 1388561 = 1041421) B1041421
theorem B1388579 : Blo 924580 1388579 := bstep (se 1 (by rfl) ⟨1041434, by rfl⟩ : syracuseStep 1388579 = 2082869) B2082869
theorem B4698161 : Blo 924580 4698161 := bstep (se 2 (by rfl) ⟨1761810, by rfl⟩ : syracuseStep 4698161 = 3523621) B3523621
theorem B1388609 : Blo 924580 1388609 := bstep (se 2 (by rfl) ⟨520728, by rfl⟩ : syracuseStep 1388609 = 1041457) B1041457
theorem B2633809 : Blo 924580 2633809 := bstep (se 2 (by rfl) ⟨987678, by rfl⟩ : syracuseStep 2633809 = 1975357) B1975357
theorem B1388627 : Blo 924580 1388627 := bstep (se 1 (by rfl) ⟨1041470, by rfl⟩ : syracuseStep 1388627 = 2082941) B2082941
theorem B3125357 : Blo 924580 3125357 := bstep (se 3 (by rfl) ⟨586004, by rfl⟩ : syracuseStep 3125357 = 1172009) B1172009
theorem B1388657 : Blo 924580 1388657 := bstep (se 2 (by rfl) ⟨520746, by rfl⟩ : syracuseStep 1388657 = 1041493) B1041493
theorem B1388675 : Blo 924580 1388675 := bstep (se 1 (by rfl) ⟨1041506, by rfl⟩ : syracuseStep 1388675 = 2083013) B2083013
theorem B1388705 : Blo 924580 1388705 := bstep (se 2 (by rfl) ⟨520764, by rfl⟩ : syracuseStep 1388705 = 1041529) B1041529
theorem B3125411 : Blo 924580 3125411 := bstep (se 1 (by rfl) ⟨2344058, by rfl⟩ : syracuseStep 3125411 = 4688117) B4688117
theorem B1388723 : Blo 924580 1388723 := bstep (se 1 (by rfl) ⟨1041542, by rfl⟩ : syracuseStep 1388723 = 2083085) B2083085
theorem B1388753 : Blo 924580 1388753 := bstep (se 2 (by rfl) ⟨520782, by rfl⟩ : syracuseStep 1388753 = 1041565) B1041565
theorem B1388771 : Blo 924580 1388771 := bstep (se 1 (by rfl) ⟨1041578, by rfl⟩ : syracuseStep 1388771 = 2083157) B2083157
theorem B1388801 : Blo 924580 1388801 := bstep (se 2 (by rfl) ⟨520800, by rfl⟩ : syracuseStep 1388801 = 1041601) B1041601
theorem B1388819 : Blo 924580 1388819 := bstep (se 1 (by rfl) ⟨1041614, by rfl⟩ : syracuseStep 1388819 = 2083229) B2083229
theorem B1388849 : Blo 924580 1388849 := bstep (se 2 (by rfl) ⟨520818, by rfl⟩ : syracuseStep 1388849 = 1041637) B1041637
theorem B1388867 : Blo 924580 1388867 := bstep (se 1 (by rfl) ⟨1041650, by rfl⟩ : syracuseStep 1388867 = 2083301) B2083301
theorem B1388897 : Blo 924580 1388897 := bstep (se 2 (by rfl) ⟨520836, by rfl⟩ : syracuseStep 1388897 = 1041673) B1041673
theorem B2634083 : Blo 924580 2634083 := bstep (se 1 (by rfl) ⟨1975562, by rfl⟩ : syracuseStep 2634083 = 3951125) B3951125
theorem B1388915 : Blo 924580 1388915 := bstep (se 1 (by rfl) ⟨1041686, by rfl⟩ : syracuseStep 1388915 = 2083373) B2083373
theorem B1388945 : Blo 924580 1388945 := bstep (se 2 (by rfl) ⟨520854, by rfl⟩ : syracuseStep 1388945 = 1041709) B1041709
theorem B1388963 : Blo 924580 1388963 := bstep (se 1 (by rfl) ⟨1041722, by rfl⟩ : syracuseStep 1388963 = 2083445) B2083445
theorem B3125681 : Blo 924580 3125681 := bstep (se 2 (by rfl) ⟨1172130, by rfl⟩ : syracuseStep 3125681 = 2344261) B2344261
theorem B1388993 : Blo 924580 1388993 := bstep (se 2 (by rfl) ⟨520872, by rfl⟩ : syracuseStep 1388993 = 1041745) B1041745
theorem B1389011 : Blo 924580 1389011 := bstep (se 1 (by rfl) ⟨1041758, by rfl⟩ : syracuseStep 1389011 = 2083517) B2083517
theorem B1389041 : Blo 924580 1389041 := bstep (se 2 (by rfl) ⟨520890, by rfl⟩ : syracuseStep 1389041 = 1041781) B1041781
theorem B1389059 : Blo 924580 1389059 := bstep (se 1 (by rfl) ⟨1041794, by rfl⟩ : syracuseStep 1389059 = 2083589) B2083589
theorem B1389089 : Blo 924580 1389089 := bstep (se 2 (by rfl) ⟨520908, by rfl⟩ : syracuseStep 1389089 = 1041817) B1041817
theorem B1389107 : Blo 924580 1389107 := bstep (se 1 (by rfl) ⟨1041830, by rfl⟩ : syracuseStep 1389107 = 2083661) B2083661
theorem B1389137 : Blo 924580 1389137 := bstep (se 2 (by rfl) ⟨520926, by rfl⟩ : syracuseStep 1389137 = 1041853) B1041853
theorem B1389155 : Blo 924580 1389155 := bstep (se 1 (by rfl) ⟨1041866, by rfl⟩ : syracuseStep 1389155 = 2083733) B2083733
theorem B1389185 : Blo 924580 1389185 := bstep (se 2 (by rfl) ⟨520944, by rfl⟩ : syracuseStep 1389185 = 1041889) B1041889
theorem B10039949 : Blo 924580 10039949 := bstep (se 3 (by rfl) ⟨1882490, by rfl⟩ : syracuseStep 10039949 = 3764981) B3764981
theorem B1389203 : Blo 924580 1389203 := bstep (se 1 (by rfl) ⟨1041902, by rfl⟩ : syracuseStep 1389203 = 2083805) B2083805
theorem B1389233 : Blo 924580 1389233 := bstep (se 2 (by rfl) ⟨520962, by rfl⟩ : syracuseStep 1389233 = 1041925) B1041925
theorem B6337201 : Blo 924580 6337201 := bstep (se 2 (by rfl) ⟨2376450, by rfl⟩ : syracuseStep 6337201 = 4752901) B4752901
theorem B1389251 : Blo 924580 1389251 := bstep (se 1 (by rfl) ⟨1041938, by rfl⟩ : syracuseStep 1389251 = 2083877) B2083877
theorem B1389281 : Blo 924580 1389281 := bstep (se 2 (by rfl) ⟨520980, by rfl⟩ : syracuseStep 1389281 = 1041961) B1041961
theorem B1585889 : Blo 924580 1585889 := bstep (se 2 (by rfl) ⟨594708, by rfl⟩ : syracuseStep 1585889 = 1189417) B1189417
theorem B1389299 : Blo 924580 1389299 := bstep (se 1 (by rfl) ⟨1041974, by rfl⟩ : syracuseStep 1389299 = 2083949) B2083949
theorem B1389329 : Blo 924580 1389329 := bstep (se 2 (by rfl) ⟨520998, by rfl⟩ : syracuseStep 1389329 = 1041997) B1041997
theorem B1389347 : Blo 924580 1389347 := bstep (se 1 (by rfl) ⟨1042010, by rfl⟩ : syracuseStep 1389347 = 2084021) B2084021
theorem B1389377 : Blo 924580 1389377 := bstep (se 2 (by rfl) ⟨521016, by rfl⟩ : syracuseStep 1389377 = 1042033) B1042033
theorem B1389395 : Blo 924580 1389395 := bstep (se 1 (by rfl) ⟨1042046, by rfl⟩ : syracuseStep 1389395 = 2084093) B2084093
theorem B7910243 : Blo 924580 7910243 := bstep (se 1 (by rfl) ⟨5932682, by rfl⟩ : syracuseStep 7910243 = 11865365) B11865365
theorem B2503523 : Blo 924580 2503523 := bstep (se 1 (by rfl) ⟨1877642, by rfl⟩ : syracuseStep 2503523 = 3755285) B3755285
theorem B1389425 : Blo 924580 1389425 := bstep (se 2 (by rfl) ⟨521034, by rfl⟩ : syracuseStep 1389425 = 1042069) B1042069
theorem B1782641 : Blo 924580 1782641 := bstep (se 2 (by rfl) ⟨668490, by rfl⟩ : syracuseStep 1782641 = 1336981) B1336981
theorem B1389443 : Blo 924580 1389443 := bstep (se 1 (by rfl) ⟨1042082, by rfl⟩ : syracuseStep 1389443 = 2084165) B2084165
theorem B1389473 : Blo 924580 1389473 := bstep (se 2 (by rfl) ⟨521052, by rfl⟩ : syracuseStep 1389473 = 1042105) B1042105
theorem B1389491 : Blo 924580 1389491 := bstep (se 1 (by rfl) ⟨1042118, by rfl⟩ : syracuseStep 1389491 = 2084237) B2084237
theorem B3126221 : Blo 924580 3126221 := bstep (se 3 (by rfl) ⟨586166, by rfl⟩ : syracuseStep 3126221 = 1172333) B1172333
theorem B1389521 : Blo 924580 1389521 := bstep (se 2 (by rfl) ⟨521070, by rfl⟩ : syracuseStep 1389521 = 1042141) B1042141
theorem B1389539 : Blo 924580 1389539 := bstep (se 1 (by rfl) ⟨1042154, by rfl⟩ : syracuseStep 1389539 = 2084309) B2084309
theorem B1389569 : Blo 924580 1389569 := bstep (se 2 (by rfl) ⟨521088, by rfl⟩ : syracuseStep 1389569 = 1042177) B1042177
theorem B3126275 : Blo 924580 3126275 := bstep (se 1 (by rfl) ⟨2344706, by rfl⟩ : syracuseStep 3126275 = 4689413) B4689413
theorem B1389587 : Blo 924580 1389587 := bstep (se 1 (by rfl) ⟨1042190, by rfl⟩ : syracuseStep 1389587 = 2084381) B2084381
theorem B1389617 : Blo 924580 1389617 := bstep (se 2 (by rfl) ⟨521106, by rfl⟩ : syracuseStep 1389617 = 1042213) B1042213
theorem B1389635 : Blo 924580 1389635 := bstep (se 1 (by rfl) ⟨1042226, by rfl⟩ : syracuseStep 1389635 = 2084453) B2084453
theorem B1389665 : Blo 924580 1389665 := bstep (se 2 (by rfl) ⟨521124, by rfl⟩ : syracuseStep 1389665 = 1042249) B1042249
theorem B1389683 : Blo 924580 1389683 := bstep (se 1 (by rfl) ⟨1042262, by rfl⟩ : syracuseStep 1389683 = 2084525) B2084525
theorem B1389713 : Blo 924580 1389713 := bstep (se 2 (by rfl) ⟨521142, by rfl⟩ : syracuseStep 1389713 = 1042285) B1042285
theorem B1389731 : Blo 924580 1389731 := bstep (se 1 (by rfl) ⟨1042298, by rfl⟩ : syracuseStep 1389731 = 2084597) B2084597
theorem B2634925 : Blo 924580 2634925 := bstep (se 3 (by rfl) ⟨494048, by rfl⟩ : syracuseStep 2634925 = 988097) B988097
theorem B1979569 : Blo 924580 1979569 := bstep (se 2 (by rfl) ⟨742338, by rfl⟩ : syracuseStep 1979569 = 1484677) B1484677
theorem B1389761 : Blo 924580 1389761 := bstep (se 2 (by rfl) ⟨521160, by rfl⟩ : syracuseStep 1389761 = 1042321) B1042321
theorem B1389779 : Blo 924580 1389779 := bstep (se 1 (by rfl) ⟨1042334, by rfl⟩ : syracuseStep 1389779 = 2084669) B2084669
theorem B1389809 : Blo 924580 1389809 := bstep (se 2 (by rfl) ⟨521178, by rfl⟩ : syracuseStep 1389809 = 1042357) B1042357
theorem B1389827 : Blo 924580 1389827 := bstep (se 1 (by rfl) ⟨1042370, by rfl⟩ : syracuseStep 1389827 = 2084741) B2084741
theorem B3126545 : Blo 924580 3126545 := bstep (se 2 (by rfl) ⟨1172454, by rfl⟩ : syracuseStep 3126545 = 2344909) B2344909
theorem B1389857 : Blo 924580 1389857 := bstep (se 2 (by rfl) ⟨521196, by rfl⟩ : syracuseStep 1389857 = 1042393) B1042393
theorem B1389875 : Blo 924580 1389875 := bstep (se 1 (by rfl) ⟨1042406, by rfl⟩ : syracuseStep 1389875 = 2084813) B2084813
theorem B2635085 : Blo 924580 2635085 := bstep (se 3 (by rfl) ⟨494078, by rfl⟩ : syracuseStep 2635085 = 988157) B988157
theorem B1389905 : Blo 924580 1389905 := bstep (se 2 (by rfl) ⟨521214, by rfl⟩ : syracuseStep 1389905 = 1042429) B1042429
theorem B1389923 : Blo 924580 1389923 := bstep (se 1 (by rfl) ⟨1042442, by rfl⟩ : syracuseStep 1389923 = 2084885) B2084885
theorem B1389953 : Blo 924580 1389953 := bstep (se 2 (by rfl) ⟨521232, by rfl⟩ : syracuseStep 1389953 = 1042465) B1042465
theorem B1389971 : Blo 924580 1389971 := bstep (se 1 (by rfl) ⟨1042478, by rfl⟩ : syracuseStep 1389971 = 2084957) B2084957
theorem B1390001 : Blo 924580 1390001 := bstep (se 2 (by rfl) ⟨521250, by rfl⟩ : syracuseStep 1390001 = 1042501) B1042501
theorem B1390019 : Blo 924580 1390019 := bstep (se 1 (by rfl) ⟨1042514, by rfl⟩ : syracuseStep 1390019 = 2085029) B2085029
theorem B9024965 : Blo 924580 9024965 := bstep (se 4 (by rfl) ⟨846090, by rfl⟩ : syracuseStep 9024965 = 1692181) B1692181
theorem B1390049 : Blo 924580 1390049 := bstep (se 2 (by rfl) ⟨521268, by rfl⟩ : syracuseStep 1390049 = 1042537) B1042537
theorem B4699619 : Blo 924580 4699619 := bstep (se 1 (by rfl) ⟨3524714, by rfl⟩ : syracuseStep 4699619 = 7049429) B7049429
theorem B1390067 : Blo 924580 1390067 := bstep (se 1 (by rfl) ⟨1042550, by rfl⟩ : syracuseStep 1390067 = 2085101) B2085101
theorem B2635267 : Blo 924580 2635267 := bstep (se 1 (by rfl) ⟨1976450, by rfl⟩ : syracuseStep 2635267 = 3952901) B3952901
theorem B1390097 : Blo 924580 1390097 := bstep (se 2 (by rfl) ⟨521286, by rfl⟩ : syracuseStep 1390097 = 1042573) B1042573
theorem B1390115 : Blo 924580 1390115 := bstep (se 1 (by rfl) ⟨1042586, by rfl⟩ : syracuseStep 1390115 = 2085173) B2085173
theorem B1390145 : Blo 924580 1390145 := bstep (se 2 (by rfl) ⟨521304, by rfl⟩ : syracuseStep 1390145 = 1042609) B1042609
theorem B1390163 : Blo 924580 1390163 := bstep (se 1 (by rfl) ⟨1042622, by rfl⟩ : syracuseStep 1390163 = 2085245) B2085245
theorem B1390193 : Blo 924580 1390193 := bstep (se 2 (by rfl) ⟨521322, by rfl⟩ : syracuseStep 1390193 = 1042645) B1042645
theorem B1390211 : Blo 924580 1390211 := bstep (se 1 (by rfl) ⟨1042658, by rfl⟩ : syracuseStep 1390211 = 2085317) B2085317
theorem B1390241 : Blo 924580 1390241 := bstep (se 2 (by rfl) ⟨521340, by rfl⟩ : syracuseStep 1390241 = 1042681) B1042681
theorem B2340515 : Blo 924580 2340515 := bstep (se 1 (by rfl) ⟨1755386, by rfl⟩ : syracuseStep 2340515 = 3510773) B3510773
theorem B1390259 : Blo 924580 1390259 := bstep (se 1 (by rfl) ⟨1042694, by rfl⟩ : syracuseStep 1390259 = 2085389) B2085389
theorem B3520205 : Blo 924580 3520205 := bstep (se 3 (by rfl) ⟨660038, by rfl⟩ : syracuseStep 3520205 = 1320077) B1320077
theorem B1390289 : Blo 924580 1390289 := bstep (se 2 (by rfl) ⟨521358, by rfl⟩ : syracuseStep 1390289 = 1042717) B1042717
theorem B1390307 : Blo 924580 1390307 := bstep (se 1 (by rfl) ⟨1042730, by rfl⟩ : syracuseStep 1390307 = 2085461) B2085461
theorem B1128179 : Blo 924580 1128179 := bstep (se 1 (by rfl) ⟨846134, by rfl⟩ : syracuseStep 1128179 = 1692269) B1692269
theorem B1390337 : Blo 924580 1390337 := bstep (se 2 (by rfl) ⟨521376, by rfl⟩ : syracuseStep 1390337 = 1042753) B1042753
theorem B1390355 : Blo 924580 1390355 := bstep (se 1 (by rfl) ⟨1042766, by rfl⟩ : syracuseStep 1390355 = 2085533) B2085533
theorem B3127085 : Blo 924580 3127085 := bstep (se 3 (by rfl) ⟨586328, by rfl⟩ : syracuseStep 3127085 = 1172657) B1172657
theorem B1390385 : Blo 924580 1390385 := bstep (se 2 (by rfl) ⟨521394, by rfl⟩ : syracuseStep 1390385 = 1042789) B1042789
theorem B2963267 : Blo 924580 2963267 := bstep (se 1 (by rfl) ⟨2222450, by rfl⟩ : syracuseStep 2963267 = 4444901) B4444901
theorem B1390403 : Blo 924580 1390403 := bstep (se 1 (by rfl) ⟨1042802, by rfl⟩ : syracuseStep 1390403 = 2085605) B2085605
theorem B1980227 : Blo 924580 1980227 := bstep (se 1 (by rfl) ⟨1485170, by rfl⟩ : syracuseStep 1980227 = 2970341) B2970341
theorem B1390433 : Blo 924580 1390433 := bstep (se 2 (by rfl) ⟨521412, by rfl⟩ : syracuseStep 1390433 = 1042825) B1042825
theorem B3127139 : Blo 924580 3127139 := bstep (se 1 (by rfl) ⟨2345354, by rfl⟩ : syracuseStep 3127139 = 4690709) B4690709
theorem B1390451 : Blo 924580 1390451 := bstep (se 1 (by rfl) ⟨1042838, by rfl⟩ : syracuseStep 1390451 = 2085677) B2085677
theorem B1390481 : Blo 924580 1390481 := bstep (se 2 (by rfl) ⟨521430, by rfl⟩ : syracuseStep 1390481 = 1042861) B1042861
theorem B1390499 : Blo 924580 1390499 := bstep (se 1 (by rfl) ⟨1042874, by rfl⟩ : syracuseStep 1390499 = 2085749) B2085749
theorem B1390529 : Blo 924580 1390529 := bstep (se 2 (by rfl) ⟨521448, by rfl⟩ : syracuseStep 1390529 = 1042897) B1042897
theorem B1390547 : Blo 924580 1390547 := bstep (se 1 (by rfl) ⟨1042910, by rfl⟩ : syracuseStep 1390547 = 2085821) B2085821
theorem B1390577 : Blo 924580 1390577 := bstep (se 2 (by rfl) ⟨521466, by rfl⟩ : syracuseStep 1390577 = 1042933) B1042933
theorem B1783811 : Blo 924580 1783811 := bstep (se 1 (by rfl) ⟨1337858, by rfl⟩ : syracuseStep 1783811 = 2675717) B2675717
theorem B1390595 : Blo 924580 1390595 := bstep (se 1 (by rfl) ⟨1042946, by rfl⟩ : syracuseStep 1390595 = 2085893) B2085893
theorem B1587217 : Blo 924580 1587217 := bstep (se 2 (by rfl) ⟨595206, by rfl⟩ : syracuseStep 1587217 = 1190413) B1190413
theorem B1390625 : Blo 924580 1390625 := bstep (se 2 (by rfl) ⟨521484, by rfl⟩ : syracuseStep 1390625 = 1042969) B1042969
theorem B1390643 : Blo 924580 1390643 := bstep (se 1 (by rfl) ⟨1042982, by rfl⟩ : syracuseStep 1390643 = 2085965) B2085965
theorem B1390673 : Blo 924580 1390673 := bstep (se 2 (by rfl) ⟨521502, by rfl⟩ : syracuseStep 1390673 = 1043005) B1043005
theorem B1390691 : Blo 924580 1390691 := bstep (se 1 (by rfl) ⟨1043018, by rfl⟩ : syracuseStep 1390691 = 2086037) B2086037
theorem B2373745 : Blo 924580 2373745 := bstep (se 2 (by rfl) ⟨890154, by rfl⟩ : syracuseStep 2373745 = 1780309) B1780309
theorem B3127409 : Blo 924580 3127409 := bstep (se 2 (by rfl) ⟨1172778, by rfl⟩ : syracuseStep 3127409 = 2345557) B2345557
theorem B1390721 : Blo 924580 1390721 := bstep (se 2 (by rfl) ⟨521520, by rfl⟩ : syracuseStep 1390721 = 1043041) B1043041
theorem B1390739 : Blo 924580 1390739 := bstep (se 1 (by rfl) ⟨1043054, by rfl⟩ : syracuseStep 1390739 = 2086109) B2086109
theorem B1390769 : Blo 924580 1390769 := bstep (se 2 (by rfl) ⟨521538, by rfl⟩ : syracuseStep 1390769 = 1043077) B1043077
theorem B1390787 : Blo 924580 1390787 := bstep (se 1 (by rfl) ⟨1043090, by rfl⟩ : syracuseStep 1390787 = 2086181) B2086181
theorem B1390817 : Blo 924580 1390817 := bstep (se 2 (by rfl) ⟨521556, by rfl⟩ : syracuseStep 1390817 = 1043113) B1043113
theorem B1390835 : Blo 924580 1390835 := bstep (se 1 (by rfl) ⟨1043126, by rfl⟩ : syracuseStep 1390835 = 2086253) B2086253
theorem B4700429 : Blo 924580 4700429 := bstep (se 3 (by rfl) ⟨881330, by rfl⟩ : syracuseStep 4700429 = 1762661) B1762661
theorem B1390865 : Blo 924580 1390865 := bstep (se 2 (by rfl) ⟨521574, by rfl⟩ : syracuseStep 1390865 = 1043149) B1043149
theorem B1390883 : Blo 924580 1390883 := bstep (se 1 (by rfl) ⟨1043162, by rfl⟩ : syracuseStep 1390883 = 2086325) B2086325
theorem B1390913 : Blo 924580 1390913 := bstep (se 2 (by rfl) ⟨521592, by rfl⟩ : syracuseStep 1390913 = 1043185) B1043185
theorem B1390931 : Blo 924580 1390931 := bstep (se 1 (by rfl) ⟨1043198, by rfl⟩ : syracuseStep 1390931 = 2086397) B2086397
theorem B1390961 : Blo 924580 1390961 := bstep (se 2 (by rfl) ⟨521610, by rfl⟩ : syracuseStep 1390961 = 1043221) B1043221
theorem B1390979 : Blo 924580 1390979 := bstep (se 1 (by rfl) ⟨1043234, by rfl⟩ : syracuseStep 1390979 = 2086469) B2086469
theorem B1391009 : Blo 924580 1391009 := bstep (se 2 (by rfl) ⟨521628, by rfl⟩ : syracuseStep 1391009 = 1043257) B1043257
theorem B1391027 : Blo 924580 1391027 := bstep (se 1 (by rfl) ⟨1043270, by rfl⟩ : syracuseStep 1391027 = 2086541) B2086541
theorem B1391057 : Blo 924580 1391057 := bstep (se 2 (by rfl) ⟨521646, by rfl⟩ : syracuseStep 1391057 = 1043293) B1043293
theorem B1391075 : Blo 924580 1391075 := bstep (se 1 (by rfl) ⟨1043306, by rfl⟩ : syracuseStep 1391075 = 2086613) B2086613
theorem B3521009 : Blo 924580 3521009 := bstep (se 2 (by rfl) ⟨1320378, by rfl⟩ : syracuseStep 3521009 = 2640757) B2640757
theorem B1391105 : Blo 924580 1391105 := bstep (se 2 (by rfl) ⟨521664, by rfl⟩ : syracuseStep 1391105 = 1043329) B1043329
theorem B1391123 : Blo 924580 1391123 := bstep (se 1 (by rfl) ⟨1043342, by rfl⟩ : syracuseStep 1391123 = 2086685) B2086685
theorem B1391153 : Blo 924580 1391153 := bstep (se 2 (by rfl) ⟨521682, by rfl⟩ : syracuseStep 1391153 = 1043365) B1043365
theorem B2964035 : Blo 924580 2964035 := bstep (se 1 (by rfl) ⟨2223026, by rfl⟩ : syracuseStep 2964035 = 4446053) B4446053
theorem B1391171 : Blo 924580 1391171 := bstep (se 1 (by rfl) ⟨1043378, by rfl⟩ : syracuseStep 1391171 = 2086757) B2086757
theorem B2341457 : Blo 924580 2341457 := bstep (se 2 (by rfl) ⟨878046, by rfl⟩ : syracuseStep 2341457 = 1756093) B1756093
theorem B1391201 : Blo 924580 1391201 := bstep (se 2 (by rfl) ⟨521700, by rfl⟩ : syracuseStep 1391201 = 1043401) B1043401
theorem B1391219 : Blo 924580 1391219 := bstep (se 1 (by rfl) ⟨1043414, by rfl⟩ : syracuseStep 1391219 = 2086829) B2086829
theorem B2341507 : Blo 924580 2341507 := bstep (se 1 (by rfl) ⟨1756130, by rfl⟩ : syracuseStep 2341507 = 3512261) B3512261
theorem B3127949 : Blo 924580 3127949 := bstep (se 3 (by rfl) ⟨586490, by rfl⟩ : syracuseStep 3127949 = 1172981) B1172981
theorem B1391249 : Blo 924580 1391249 := bstep (se 2 (by rfl) ⟨521718, by rfl⟩ : syracuseStep 1391249 = 1043437) B1043437
theorem B1981073 : Blo 924580 1981073 := bstep (se 2 (by rfl) ⟨742902, by rfl⟩ : syracuseStep 1981073 = 1485805) B1485805
theorem B1391267 : Blo 924580 1391267 := bstep (se 1 (by rfl) ⟨1043450, by rfl⟩ : syracuseStep 1391267 = 2086901) B2086901
theorem B1391297 : Blo 924580 1391297 := bstep (se 2 (by rfl) ⟨521736, by rfl⟩ : syracuseStep 1391297 = 1043473) B1043473
theorem B3128003 : Blo 924580 3128003 := bstep (se 1 (by rfl) ⟨2346002, by rfl⟩ : syracuseStep 3128003 = 4692005) B4692005
theorem B1391315 : Blo 924580 1391315 := bstep (se 1 (by rfl) ⟨1043486, by rfl⟩ : syracuseStep 1391315 = 2086973) B2086973
theorem B1391345 : Blo 924580 1391345 := bstep (se 2 (by rfl) ⟨521754, by rfl⟩ : syracuseStep 1391345 = 1043509) B1043509
theorem B1391363 : Blo 924580 1391363 := bstep (se 1 (by rfl) ⟨1043522, by rfl⟩ : syracuseStep 1391363 = 2087045) B2087045
theorem B2341649 : Blo 924580 2341649 := bstep (se 2 (by rfl) ⟨878118, by rfl⟩ : syracuseStep 2341649 = 1756237) B1756237
theorem B26753813 : Blo 924580 26753813 := bstep (se 6 (by rfl) ⟨627042, by rfl⟩ : syracuseStep 26753813 = 1254085) B1254085
theorem B1391393 : Blo 924580 1391393 := bstep (se 2 (by rfl) ⟨521772, by rfl⟩ : syracuseStep 1391393 = 1043545) B1043545
theorem B1391411 : Blo 924580 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B1391441 : Blo 924580 1391441 := bstep (se 2 (by rfl) ⟨521790, by rfl⟩ : syracuseStep 1391441 = 1043581) B1043581
theorem B1391459 : Blo 924580 1391459 := bstep (se 1 (by rfl) ⟨1043594, by rfl⟩ : syracuseStep 1391459 = 2087189) B2087189
theorem B2636657 : Blo 924580 2636657 := bstep (se 2 (by rfl) ⟨988746, by rfl⟩ : syracuseStep 2636657 = 1977493) B1977493
theorem B1391489 : Blo 924580 1391489 := bstep (se 2 (by rfl) ⟨521808, by rfl⟩ : syracuseStep 1391489 = 1043617) B1043617
theorem B1522577 : Blo 924580 1522577 := bstep (se 2 (by rfl) ⟨570966, by rfl⟩ : syracuseStep 1522577 = 1141933) B1141933
theorem B1391507 : Blo 924580 1391507 := bstep (se 1 (by rfl) ⟨1043630, by rfl⟩ : syracuseStep 1391507 = 2087261) B2087261
theorem B1391537 : Blo 924580 1391537 := bstep (se 2 (by rfl) ⟨521826, by rfl⟩ : syracuseStep 1391537 = 1043653) B1043653
theorem B1391555 : Blo 924580 1391555 := bstep (se 1 (by rfl) ⟨1043666, by rfl⟩ : syracuseStep 1391555 = 2087333) B2087333
theorem B5946317 : Blo 924580 5946317 := bstep (se 3 (by rfl) ⟨1114934, by rfl⟩ : syracuseStep 5946317 = 2229869) B2229869
theorem B2964433 : Blo 924580 2964433 := bstep (se 2 (by rfl) ⟨1111662, by rfl⟩ : syracuseStep 2964433 = 2223325) B2223325
theorem B3128273 : Blo 924580 3128273 := bstep (se 2 (by rfl) ⟨1173102, by rfl⟩ : syracuseStep 3128273 = 2346205) B2346205
theorem B1391585 : Blo 924580 1391585 := bstep (se 2 (by rfl) ⟨521844, by rfl⟩ : syracuseStep 1391585 = 1043689) B1043689
theorem B1391603 : Blo 924580 1391603 := bstep (se 1 (by rfl) ⟨1043702, by rfl⟩ : syracuseStep 1391603 = 2087405) B2087405
theorem B1391633 : Blo 924580 1391633 := bstep (se 2 (by rfl) ⟨521862, by rfl⟩ : syracuseStep 1391633 = 1043725) B1043725
theorem B1588243 : Blo 924580 1588243 := bstep (se 1 (by rfl) ⟨1191182, by rfl⟩ : syracuseStep 1588243 = 2382365) B2382365
theorem B1391651 : Blo 924580 1391651 := bstep (se 1 (by rfl) ⟨1043738, by rfl⟩ : syracuseStep 1391651 = 2087477) B2087477
theorem B1391681 : Blo 924580 1391681 := bstep (se 2 (by rfl) ⟨521880, by rfl⟩ : syracuseStep 1391681 = 1043761) B1043761
theorem B2964547 : Blo 924580 2964547 := bstep (se 1 (by rfl) ⟨2223410, by rfl⟩ : syracuseStep 2964547 = 4446821) B4446821
theorem B5356621 : Blo 924580 5356621 := bstep (se 3 (by rfl) ⟨1004366, by rfl⟩ : syracuseStep 5356621 = 2008733) B2008733
theorem B1391699 : Blo 924580 1391699 := bstep (se 1 (by rfl) ⟨1043774, by rfl⟩ : syracuseStep 1391699 = 2087549) B2087549
theorem B1391729 : Blo 924580 1391729 := bstep (se 2 (by rfl) ⟨521898, by rfl⟩ : syracuseStep 1391729 = 1043797) B1043797
theorem B12696689 : Blo 924580 12696689 := bstep (se 2 (by rfl) ⟨4761258, by rfl⟩ : syracuseStep 12696689 = 9522517) B9522517
theorem B1391747 : Blo 924580 1391747 := bstep (se 1 (by rfl) ⟨1043810, by rfl⟩ : syracuseStep 1391747 = 2087621) B2087621
theorem B3521677 : Blo 924580 3521677 := bstep (se 3 (by rfl) ⟨660314, by rfl⟩ : syracuseStep 3521677 = 1320629) B1320629
theorem B1391777 : Blo 924580 1391777 := bstep (se 2 (by rfl) ⟨521916, by rfl⟩ : syracuseStep 1391777 = 1043833) B1043833
theorem B1391795 : Blo 924580 1391795 := bstep (se 1 (by rfl) ⟨1043846, by rfl⟩ : syracuseStep 1391795 = 2087693) B2087693
theorem B1391825 : Blo 924580 1391825 := bstep (se 2 (by rfl) ⟨521934, by rfl⟩ : syracuseStep 1391825 = 1043869) B1043869
theorem B1391843 : Blo 924580 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B1391873 : Blo 924580 1391873 := bstep (se 2 (by rfl) ⟨521952, by rfl⟩ : syracuseStep 1391873 = 1043905) B1043905
theorem B1391891 : Blo 924580 1391891 := bstep (se 1 (by rfl) ⟨1043918, by rfl⟩ : syracuseStep 1391891 = 2087837) B2087837
theorem B1391921 : Blo 924580 1391921 := bstep (se 2 (by rfl) ⟨521970, by rfl⟩ : syracuseStep 1391921 = 1043941) B1043941
theorem B1391939 : Blo 924580 1391939 := bstep (se 1 (by rfl) ⟨1043954, by rfl⟩ : syracuseStep 1391939 = 2087909) B2087909
theorem B1391969 : Blo 924580 1391969 := bstep (se 2 (by rfl) ⟨521988, by rfl⟩ : syracuseStep 1391969 = 1043977) B1043977
theorem B1391987 : Blo 924580 1391987 := bstep (se 1 (by rfl) ⟨1043990, by rfl⟩ : syracuseStep 1391987 = 2087981) B2087981
theorem B1392017 : Blo 924580 1392017 := bstep (se 2 (by rfl) ⟨522006, by rfl⟩ : syracuseStep 1392017 = 1044013) B1044013
theorem B1392035 : Blo 924580 1392035 := bstep (se 1 (by rfl) ⟨1044026, by rfl⟩ : syracuseStep 1392035 = 2088053) B2088053
theorem B1392065 : Blo 924580 1392065 := bstep (se 2 (by rfl) ⟨522024, by rfl⟩ : syracuseStep 1392065 = 1044049) B1044049
theorem B11255237 : Blo 924580 11255237 := bstep (se 4 (by rfl) ⟨1055178, by rfl⟩ : syracuseStep 11255237 = 2110357) B2110357
theorem B1392083 : Blo 924580 1392083 := bstep (se 1 (by rfl) ⟨1044062, by rfl⟩ : syracuseStep 1392083 = 2088125) B2088125
theorem B3128813 : Blo 924580 3128813 := bstep (se 3 (by rfl) ⟨586652, by rfl⟩ : syracuseStep 3128813 = 1173305) B1173305
theorem B1392113 : Blo 924580 1392113 := bstep (se 2 (by rfl) ⟨522042, by rfl⟩ : syracuseStep 1392113 = 1044085) B1044085
theorem B1392131 : Blo 924580 1392131 := bstep (se 1 (by rfl) ⟨1044098, by rfl⟩ : syracuseStep 1392131 = 2088197) B2088197
theorem B1392161 : Blo 924580 1392161 := bstep (se 2 (by rfl) ⟨522060, by rfl⟩ : syracuseStep 1392161 = 1044121) B1044121
theorem B3128867 : Blo 924580 3128867 := bstep (se 1 (by rfl) ⟨2346650, by rfl⟩ : syracuseStep 3128867 = 4693301) B4693301
theorem B1392179 : Blo 924580 1392179 := bstep (se 1 (by rfl) ⟨1044134, by rfl⟩ : syracuseStep 1392179 = 2088269) B2088269
theorem B15416885 : Blo 924580 15416885 := bstep (se 5 (by rfl) ⟨722666, by rfl⟩ : syracuseStep 15416885 = 1445333) B1445333
theorem B1392209 : Blo 924580 1392209 := bstep (se 2 (by rfl) ⟨522078, by rfl⟩ : syracuseStep 1392209 = 1044157) B1044157
theorem B1392227 : Blo 924580 1392227 := bstep (se 1 (by rfl) ⟨1044170, by rfl⟩ : syracuseStep 1392227 = 2088341) B2088341
theorem B1392257 : Blo 924580 1392257 := bstep (se 2 (by rfl) ⟨522096, by rfl⟩ : syracuseStep 1392257 = 1044193) B1044193
theorem B1392275 : Blo 924580 1392275 := bstep (se 1 (by rfl) ⟨1044206, by rfl⟩ : syracuseStep 1392275 = 2088413) B2088413
theorem B1392305 : Blo 924580 1392305 := bstep (se 2 (by rfl) ⟨522114, by rfl⟩ : syracuseStep 1392305 = 1044229) B1044229
theorem B1392323 : Blo 924580 1392323 := bstep (se 1 (by rfl) ⟨1044242, by rfl⟩ : syracuseStep 1392323 = 2088485) B2088485
theorem B1392353 : Blo 924580 1392353 := bstep (se 2 (by rfl) ⟨522132, by rfl⟩ : syracuseStep 1392353 = 1044265) B1044265
theorem B2342641 : Blo 924580 2342641 := bstep (se 2 (by rfl) ⟨878490, by rfl⟩ : syracuseStep 2342641 = 1756981) B1756981
theorem B1392371 : Blo 924580 1392371 := bstep (se 1 (by rfl) ⟨1044278, by rfl⟩ : syracuseStep 1392371 = 2088557) B2088557
theorem B2080529 : Blo 924580 2080529 := bstep (se 2 (by rfl) ⟨780198, by rfl⟩ : syracuseStep 2080529 = 1560397) B1560397
theorem B2965265 : Blo 924580 2965265 := bstep (se 2 (by rfl) ⟨1111974, by rfl⟩ : syracuseStep 2965265 = 2223949) B2223949
theorem B1392401 : Blo 924580 1392401 := bstep (se 2 (by rfl) ⟨522150, by rfl⟩ : syracuseStep 1392401 = 1044301) B1044301
theorem B2080547 : Blo 924580 2080547 := bstep (se 1 (by rfl) ⟨1560410, by rfl⟩ : syracuseStep 2080547 = 3120821) B3120821
theorem B1392419 : Blo 924580 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B2637613 : Blo 924580 2637613 := bstep (se 3 (by rfl) ⟨494552, by rfl⟩ : syracuseStep 2637613 = 989105) B989105
theorem B3129137 : Blo 924580 3129137 := bstep (se 2 (by rfl) ⟨1173426, by rfl⟩ : syracuseStep 3129137 = 2346853) B2346853
theorem B1392449 : Blo 924580 1392449 := bstep (se 2 (by rfl) ⟨522168, by rfl⟩ : syracuseStep 1392449 = 1044337) B1044337
theorem B1392467 : Blo 924580 1392467 := bstep (se 1 (by rfl) ⟨1044350, by rfl⟩ : syracuseStep 1392467 = 2088701) B2088701
theorem B1392497 : Blo 924580 1392497 := bstep (se 2 (by rfl) ⟨522186, by rfl⟩ : syracuseStep 1392497 = 1044373) B1044373
theorem B1392515 : Blo 924580 1392515 := bstep (se 1 (by rfl) ⟨1044386, by rfl⟩ : syracuseStep 1392515 = 2088773) B2088773
theorem B2375569 : Blo 924580 2375569 := bstep (se 2 (by rfl) ⟨890838, by rfl⟩ : syracuseStep 2375569 = 1781677) B1781677
theorem B1392545 : Blo 924580 1392545 := bstep (se 2 (by rfl) ⟨522204, by rfl⟩ : syracuseStep 1392545 = 1044409) B1044409
theorem B3522467 : Blo 924580 3522467 := bstep (se 1 (by rfl) ⟨2641850, by rfl⟩ : syracuseStep 3522467 = 5283701) B5283701
theorem B1392563 : Blo 924580 1392563 := bstep (se 1 (by rfl) ⟨1044422, by rfl⟩ : syracuseStep 1392563 = 2088845) B2088845
theorem B1392593 : Blo 924580 1392593 := bstep (se 2 (by rfl) ⟨522222, by rfl⟩ : syracuseStep 1392593 = 1044445) B1044445
theorem B1392611 : Blo 924580 1392611 := bstep (se 1 (by rfl) ⟨1044458, by rfl⟩ : syracuseStep 1392611 = 2088917) B2088917
theorem B2342915 : Blo 924580 2342915 := bstep (se 1 (by rfl) ⟨1757186, by rfl⟩ : syracuseStep 2342915 = 3514373) B3514373
theorem B1392641 : Blo 924580 1392641 := bstep (se 2 (by rfl) ⟨522240, by rfl⟩ : syracuseStep 1392641 = 1044481) B1044481
theorem B2637841 : Blo 924580 2637841 := bstep (se 2 (by rfl) ⟨989190, by rfl⟩ : syracuseStep 2637841 = 1978381) B1978381
theorem B1392659 : Blo 924580 1392659 := bstep (se 1 (by rfl) ⟨1044494, by rfl⟩ : syracuseStep 1392659 = 2088989) B2088989
theorem B2080817 : Blo 924580 2080817 := bstep (se 2 (by rfl) ⟨780306, by rfl⟩ : syracuseStep 2080817 = 1560613) B1560613
theorem B1392689 : Blo 924580 1392689 := bstep (se 2 (by rfl) ⟨522258, by rfl⟩ : syracuseStep 1392689 = 1044517) B1044517
theorem B2080835 : Blo 924580 2080835 := bstep (se 1 (by rfl) ⟨1560626, by rfl⟩ : syracuseStep 2080835 = 3121253) B3121253
theorem B1392707 : Blo 924580 1392707 := bstep (se 1 (by rfl) ⟨1044530, by rfl⟩ : syracuseStep 1392707 = 2089061) B2089061
theorem B1392737 : Blo 924580 1392737 := bstep (se 2 (by rfl) ⟨522276, by rfl⟩ : syracuseStep 1392737 = 1044553) B1044553
theorem B1392755 : Blo 924580 1392755 := bstep (se 1 (by rfl) ⟨1044566, by rfl⟩ : syracuseStep 1392755 = 2089133) B2089133
theorem B1392785 : Blo 924580 1392785 := bstep (se 2 (by rfl) ⟨522294, by rfl⟩ : syracuseStep 1392785 = 1044589) B1044589
theorem B1392803 : Blo 924580 1392803 := bstep (se 1 (by rfl) ⟨1044602, by rfl⟩ : syracuseStep 1392803 = 2089205) B2089205
theorem B2638001 : Blo 924580 2638001 := bstep (se 2 (by rfl) ⟨989250, by rfl⟩ : syracuseStep 2638001 = 1978501) B1978501
theorem B1392833 : Blo 924580 1392833 := bstep (se 2 (by rfl) ⟨522312, by rfl⟩ : syracuseStep 1392833 = 1044625) B1044625
theorem B2343107 : Blo 924580 2343107 := bstep (se 1 (by rfl) ⟨1757330, by rfl⟩ : syracuseStep 2343107 = 3514661) B3514661
theorem B1392851 : Blo 924580 1392851 := bstep (se 1 (by rfl) ⟨1044638, by rfl⟩ : syracuseStep 1392851 = 2089277) B2089277
theorem B2638115 : Blo 924580 2638115 := bstep (se 1 (by rfl) ⟨1978586, by rfl⟩ : syracuseStep 2638115 = 3957173) B3957173
theorem B1982755 : Blo 924580 1982755 := bstep (se 1 (by rfl) ⟨1487066, by rfl⟩ : syracuseStep 1982755 = 2974133) B2974133
theorem B2965805 : Blo 924580 2965805 := bstep (se 3 (by rfl) ⟨556088, by rfl⟩ : syracuseStep 2965805 = 1112177) B1112177
theorem B3129677 : Blo 924580 3129677 := bstep (se 3 (by rfl) ⟨586814, by rfl⟩ : syracuseStep 3129677 = 1173629) B1173629
theorem B2081105 : Blo 924580 2081105 := bstep (se 2 (by rfl) ⟨780414, by rfl⟩ : syracuseStep 2081105 = 1560829) B1560829
theorem B2081123 : Blo 924580 2081123 := bstep (se 1 (by rfl) ⟨1560842, by rfl⟩ : syracuseStep 2081123 = 3121685) B3121685
theorem B3129731 : Blo 924580 3129731 := bstep (se 1 (by rfl) ⟨2347298, by rfl⟩ : syracuseStep 3129731 = 4694597) B4694597
theorem B3523121 : Blo 924580 3523121 := bstep (se 2 (by rfl) ⟨1321170, by rfl⟩ : syracuseStep 3523121 = 2642341) B2642341
theorem B2081393 : Blo 924580 2081393 := bstep (se 2 (by rfl) ⟨780522, by rfl⟩ : syracuseStep 2081393 = 1561045) B1561045
theorem B2081411 : Blo 924580 2081411 := bstep (se 1 (by rfl) ⟨1561058, by rfl⟩ : syracuseStep 2081411 = 3122117) B3122117
theorem B3130001 : Blo 924580 3130001 := bstep (se 2 (by rfl) ⟨1173750, by rfl⟩ : syracuseStep 3130001 = 2347501) B2347501
theorem B2671373 : Blo 924580 2671373 := bstep (se 3 (by rfl) ⟨500882, by rfl⟩ : syracuseStep 2671373 = 1001765) B1001765
theorem B7521137 : Blo 924580 7521137 := bstep (se 2 (by rfl) ⟨2820426, by rfl⟩ : syracuseStep 7521137 = 5640853) B5640853
theorem B5358469 : Blo 924580 5358469 := bstep (se 4 (by rfl) ⟨502356, by rfl⟩ : syracuseStep 5358469 = 1004713) B1004713
theorem B2081681 : Blo 924580 2081681 := bstep (se 2 (by rfl) ⟨780630, by rfl⟩ : syracuseStep 2081681 = 1561261) B1561261
theorem B2081699 : Blo 924580 2081699 := bstep (se 1 (by rfl) ⟨1561274, by rfl⟩ : syracuseStep 2081699 = 3122549) B3122549
theorem B2344049 : Blo 924580 2344049 := bstep (se 2 (by rfl) ⟨879018, by rfl⟩ : syracuseStep 2344049 = 1758037) B1758037
theorem B5948549 : Blo 924580 5948549 := bstep (se 4 (by rfl) ⟨557676, by rfl⟩ : syracuseStep 5948549 = 1115353) B1115353
theorem B2344099 : Blo 924580 2344099 := bstep (se 1 (by rfl) ⟨1758074, by rfl⟩ : syracuseStep 2344099 = 3516149) B3516149
theorem B3130541 : Blo 924580 3130541 := bstep (se 3 (by rfl) ⟨586976, by rfl⟩ : syracuseStep 3130541 = 1173953) B1173953
theorem B2081969 : Blo 924580 2081969 := bstep (se 2 (by rfl) ⟨780738, by rfl⟩ : syracuseStep 2081969 = 1561477) B1561477
theorem B2081987 : Blo 924580 2081987 := bstep (se 1 (by rfl) ⟨1561490, by rfl⟩ : syracuseStep 2081987 = 3122981) B3122981
theorem B3130595 : Blo 924580 3130595 := bstep (se 1 (by rfl) ⟨2347946, by rfl⟩ : syracuseStep 3130595 = 4695893) B4695893
theorem B2639117 : Blo 924580 2639117 := bstep (se 3 (by rfl) ⟨494834, by rfl⟩ : syracuseStep 2639117 = 989669) B989669
theorem B3949859 : Blo 924580 3949859 := bstep (se 1 (by rfl) ⟨2962394, by rfl⟩ : syracuseStep 3949859 = 5924789) B5924789
theorem B2344241 : Blo 924580 2344241 := bstep (se 2 (by rfl) ⟨879090, by rfl⟩ : syracuseStep 2344241 = 1758181) B1758181
theorem B2639299 : Blo 924580 2639299 := bstep (se 1 (by rfl) ⟨1979474, by rfl⟩ : syracuseStep 2639299 = 3958949) B3958949
theorem B2082257 : Blo 924580 2082257 := bstep (se 2 (by rfl) ⟨780846, by rfl⟩ : syracuseStep 2082257 = 1561693) B1561693
theorem B2082275 : Blo 924580 2082275 := bstep (se 1 (by rfl) ⟨1561706, by rfl⟩ : syracuseStep 2082275 = 3123413) B3123413
theorem B3130865 : Blo 924580 3130865 := bstep (se 2 (by rfl) ⟨1174074, by rfl⟩ : syracuseStep 3130865 = 2348149) B2348149
theorem B2639459 : Blo 924580 2639459 := bstep (se 1 (by rfl) ⟨1979594, by rfl⟩ : syracuseStep 2639459 = 3959189) B3959189
theorem B2082545 : Blo 924580 2082545 := bstep (se 2 (by rfl) ⟨780954, by rfl⟩ : syracuseStep 2082545 = 1561909) B1561909
theorem B2082563 : Blo 924580 2082563 := bstep (se 1 (by rfl) ⟨1561922, by rfl⟩ : syracuseStep 2082563 = 3123845) B3123845
theorem B3524579 : Blo 924580 3524579 := bstep (se 1 (by rfl) ⟨2643434, by rfl⟩ : syracuseStep 3524579 = 5286869) B5286869
theorem B3524593 : Blo 924580 3524593 := bstep (se 2 (by rfl) ⟨1321722, by rfl⟩ : syracuseStep 3524593 = 2643445) B2643445
theorem B3131405 : Blo 924580 3131405 := bstep (se 3 (by rfl) ⟨587138, by rfl⟩ : syracuseStep 3131405 = 1174277) B1174277
theorem B2082833 : Blo 924580 2082833 := bstep (se 2 (by rfl) ⟨781062, by rfl⟩ : syracuseStep 2082833 = 1562125) B1562125
theorem B2082851 : Blo 924580 2082851 := bstep (se 1 (by rfl) ⟨1562138, by rfl⟩ : syracuseStep 2082851 = 3124277) B3124277
theorem B3131459 : Blo 924580 3131459 := bstep (se 1 (by rfl) ⟨2348594, by rfl⟩ : syracuseStep 3131459 = 4697189) B4697189
theorem B2967725 : Blo 924580 2967725 := bstep (se 3 (by rfl) ⟨556448, by rfl⟩ : syracuseStep 2967725 = 1112897) B1112897
theorem B2508995 : Blo 924580 2508995 := bstep (se 1 (by rfl) ⟨1881746, by rfl⟩ : syracuseStep 2508995 = 3763493) B3763493
theorem B2345233 : Blo 924580 2345233 := bstep (se 2 (by rfl) ⟨879462, by rfl⟩ : syracuseStep 2345233 = 1758925) B1758925
theorem B2083121 : Blo 924580 2083121 := bstep (se 2 (by rfl) ⟨781170, by rfl⟩ : syracuseStep 2083121 = 1562341) B1562341
theorem B2083139 : Blo 924580 2083139 := bstep (se 1 (by rfl) ⟨1562354, by rfl⟩ : syracuseStep 2083139 = 3124709) B3124709
theorem B3131729 : Blo 924580 3131729 := bstep (se 2 (by rfl) ⟨1174398, by rfl⟩ : syracuseStep 3131729 = 2348797) B2348797
theorem B1755523 : Blo 924580 1755523 := bstep (se 1 (by rfl) ⟨1316642, by rfl⟩ : syracuseStep 1755523 = 2633285) B2633285
theorem B1755569 : Blo 924580 1755569 := bstep (se 2 (by rfl) ⟨658338, by rfl⟩ : syracuseStep 1755569 = 1316677) B1316677
theorem B3951089 : Blo 924580 3951089 := bstep (se 2 (by rfl) ⟨1481658, by rfl⟩ : syracuseStep 3951089 = 2963317) B2963317
theorem B4999715 : Blo 924580 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B2345507 : Blo 924580 2345507 := bstep (se 1 (by rfl) ⟨1759130, by rfl⟩ : syracuseStep 2345507 = 3518261) B3518261
theorem B2083409 : Blo 924580 2083409 := bstep (se 2 (by rfl) ⟨781278, by rfl⟩ : syracuseStep 2083409 = 1562557) B1562557
theorem B3164771 : Blo 924580 3164771 := bstep (se 1 (by rfl) ⟨2373578, by rfl⟩ : syracuseStep 3164771 = 4747157) B4747157
theorem B2083427 : Blo 924580 2083427 := bstep (se 1 (by rfl) ⟨1562570, by rfl⟩ : syracuseStep 2083427 = 3125141) B3125141
theorem B2640529 : Blo 924580 2640529 := bstep (se 2 (by rfl) ⟨990198, by rfl⟩ : syracuseStep 2640529 = 1980397) B1980397
theorem B1755857 : Blo 924580 1755857 := bstep (se 2 (by rfl) ⟨658446, by rfl⟩ : syracuseStep 1755857 = 1316893) B1316893
theorem B22498019 : Blo 924580 22498019 := bstep (se 1 (by rfl) ⟨16873514, by rfl⟩ : syracuseStep 22498019 = 33747029) B33747029
theorem B4999907 : Blo 924580 4999907 := bstep (se 1 (by rfl) ⟨3749930, by rfl⟩ : syracuseStep 4999907 = 7499861) B7499861
theorem B2345699 : Blo 924580 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B3132269 : Blo 924580 3132269 := bstep (se 3 (by rfl) ⟨587300, by rfl⟩ : syracuseStep 3132269 = 1174601) B1174601
theorem B2083697 : Blo 924580 2083697 := bstep (se 2 (by rfl) ⟨781386, by rfl⟩ : syracuseStep 2083697 = 1562773) B1562773
theorem B2083715 : Blo 924580 2083715 := bstep (se 1 (by rfl) ⟨1562786, by rfl⟩ : syracuseStep 2083715 = 3125573) B3125573
theorem B3132323 : Blo 924580 3132323 := bstep (se 1 (by rfl) ⟨2349242, by rfl⟩ : syracuseStep 3132323 = 4698485) B4698485
theorem B2509805 : Blo 924580 2509805 := bstep (se 3 (by rfl) ⟨470588, by rfl⟩ : syracuseStep 2509805 = 941177) B941177
theorem B2083985 : Blo 924580 2083985 := bstep (se 2 (by rfl) ⟨781494, by rfl⟩ : syracuseStep 2083985 = 1562989) B1562989
theorem B2084003 : Blo 924580 2084003 := bstep (se 1 (by rfl) ⟨1563002, by rfl⟩ : syracuseStep 2084003 = 3126005) B3126005
theorem B3132593 : Blo 924580 3132593 := bstep (se 2 (by rfl) ⟨1174722, by rfl⟩ : syracuseStep 3132593 = 2349445) B2349445
theorem B7130339 : Blo 924580 7130339 := bstep (se 1 (by rfl) ⟨5347754, by rfl⟩ : syracuseStep 7130339 = 10695509) B10695509
theorem B1756579 : Blo 924580 1756579 := bstep (se 1 (by rfl) ⟨1317434, by rfl⟩ : syracuseStep 1756579 = 2634869) B2634869
theorem B2084273 : Blo 924580 2084273 := bstep (se 2 (by rfl) ⟨781602, by rfl⟩ : syracuseStep 2084273 = 1563205) B1563205
theorem B2084291 : Blo 924580 2084291 := bstep (se 1 (by rfl) ⟨1563218, by rfl⟩ : syracuseStep 2084291 = 3126437) B3126437
theorem B7032419 : Blo 924580 7032419 := bstep (se 1 (by rfl) ⟨5274314, by rfl⟩ : syracuseStep 7032419 = 10548629) B10548629
theorem B2346641 : Blo 924580 2346641 := bstep (se 2 (by rfl) ⟨879990, by rfl⟩ : syracuseStep 2346641 = 1759981) B1759981
theorem B2346691 : Blo 924580 2346691 := bstep (se 1 (by rfl) ⟨1760018, by rfl⟩ : syracuseStep 2346691 = 3520037) B3520037
theorem B3133133 : Blo 924580 3133133 := bstep (se 3 (by rfl) ⟨587462, by rfl⟩ : syracuseStep 3133133 = 1174925) B1174925
theorem B2084561 : Blo 924580 2084561 := bstep (se 2 (by rfl) ⟨781710, by rfl⟩ : syracuseStep 2084561 = 1563421) B1563421
theorem B1560289 : Blo 924580 1560289 := bstep (se 2 (by rfl) ⟨585108, by rfl⟩ : syracuseStep 1560289 = 1170217) B1170217
theorem B2084579 : Blo 924580 2084579 := bstep (se 1 (by rfl) ⟨1563434, by rfl⟩ : syracuseStep 2084579 = 3126869) B3126869
theorem B1560323 : Blo 924580 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B3133187 : Blo 924580 3133187 := bstep (se 1 (by rfl) ⟨2349890, by rfl⟩ : syracuseStep 3133187 = 4699781) B4699781
theorem B2346833 : Blo 924580 2346833 := bstep (se 2 (by rfl) ⟨880062, by rfl⟩ : syracuseStep 2346833 = 1760125) B1760125
theorem B1757027 : Blo 924580 1757027 := bstep (se 1 (by rfl) ⟨1317770, by rfl⟩ : syracuseStep 1757027 = 2635541) B2635541
theorem B1560451 : Blo 924580 1560451 := bstep (se 1 (by rfl) ⟨1170338, by rfl⟩ : syracuseStep 1560451 = 2340677) B2340677
theorem B5001101 : Blo 924580 5001101 := bstep (se 3 (by rfl) ⟨937706, by rfl⟩ : syracuseStep 5001101 = 1875413) B1875413
theorem B2641805 : Blo 924580 2641805 := bstep (se 3 (by rfl) ⟨495338, by rfl⟩ : syracuseStep 2641805 = 990677) B990677
theorem B2084849 : Blo 924580 2084849 := bstep (se 2 (by rfl) ⟨781818, by rfl⟩ : syracuseStep 2084849 = 1563637) B1563637
theorem B2084867 : Blo 924580 2084867 := bstep (se 1 (by rfl) ⟨1563650, by rfl⟩ : syracuseStep 2084867 = 3127301) B3127301
theorem B1560593 : Blo 924580 1560593 := bstep (se 2 (by rfl) ⟨585222, by rfl⟩ : syracuseStep 1560593 = 1170445) B1170445
theorem B3133457 : Blo 924580 3133457 := bstep (se 2 (by rfl) ⟨1175046, by rfl⟩ : syracuseStep 3133457 = 2350093) B2350093
theorem B2641987 : Blo 924580 2641987 := bstep (se 1 (by rfl) ⟨1981490, by rfl⟩ : syracuseStep 2641987 = 3962981) B3962981
theorem B2642033 : Blo 924580 2642033 := bstep (se 2 (by rfl) ⟨990762, by rfl⟩ : syracuseStep 2642033 = 1981525) B1981525
theorem B1757315 : Blo 924580 1757315 := bstep (se 1 (by rfl) ⟨1317986, by rfl⟩ : syracuseStep 1757315 = 2635973) B2635973
theorem B1560721 : Blo 924580 1560721 := bstep (se 2 (by rfl) ⟨585270, by rfl⟩ : syracuseStep 1560721 = 1170541) B1170541
theorem B4018339 : Blo 924580 4018339 := bstep (se 1 (by rfl) ⟨3013754, by rfl⟩ : syracuseStep 4018339 = 6027509) B6027509
theorem B1560755 : Blo 924580 1560755 := bstep (se 1 (by rfl) ⟨1170566, by rfl⟩ : syracuseStep 1560755 = 2341133) B2341133
theorem B10571957 : Blo 924580 10571957 := bstep (se 5 (by rfl) ⟨495560, by rfl⟩ : syracuseStep 10571957 = 991121) B991121
theorem B12669155 : Blo 924580 12669155 := bstep (se 1 (by rfl) ⟨9501866, by rfl⟩ : syracuseStep 12669155 = 19003733) B19003733
theorem B2085137 : Blo 924580 2085137 := bstep (se 2 (by rfl) ⟨781926, by rfl⟩ : syracuseStep 2085137 = 1563853) B1563853
theorem B2085155 : Blo 924580 2085155 := bstep (se 1 (by rfl) ⟨1563866, by rfl⟩ : syracuseStep 2085155 = 3127733) B3127733
theorem B2969905 : Blo 924580 2969905 := bstep (se 2 (by rfl) ⟨1113714, by rfl⟩ : syracuseStep 2969905 = 2227429) B2227429
theorem B1560883 : Blo 924580 1560883 := bstep (se 1 (by rfl) ⟨1170662, by rfl⟩ : syracuseStep 1560883 = 2341325) B2341325
theorem B5001635 : Blo 924580 5001635 := bstep (se 1 (by rfl) ⟨3751226, by rfl⟩ : syracuseStep 5001635 = 7502453) B7502453
theorem B1561025 : Blo 924580 1561025 := bstep (se 2 (by rfl) ⟨585384, by rfl⟩ : syracuseStep 1561025 = 1170769) B1170769
theorem B2970083 : Blo 924580 2970083 := bstep (se 1 (by rfl) ⟨2227562, by rfl⟩ : syracuseStep 2970083 = 4455125) B4455125
theorem B2085425 : Blo 924580 2085425 := bstep (se 2 (by rfl) ⟨782034, by rfl⟩ : syracuseStep 2085425 = 1564069) B1564069
theorem B1561153 : Blo 924580 1561153 := bstep (se 2 (by rfl) ⟨585432, by rfl⟩ : syracuseStep 1561153 = 1170865) B1170865
theorem B2085443 : Blo 924580 2085443 := bstep (se 1 (by rfl) ⟨1564082, by rfl⟩ : syracuseStep 2085443 = 3128165) B3128165
theorem B1561187 : Blo 924580 1561187 := bstep (se 1 (by rfl) ⟨1170890, by rfl⟩ : syracuseStep 1561187 = 2341781) B2341781
theorem B938659 : Blo 924580 938659 := bstep (se 1 (by rfl) ⟨703994, by rfl⟩ : syracuseStep 938659 = 1407989) B1407989
theorem B1561315 : Blo 924580 1561315 := bstep (se 1 (by rfl) ⟨1170986, by rfl⟩ : syracuseStep 1561315 = 2341973) B2341973
theorem B7918307 : Blo 924580 7918307 := bstep (se 1 (by rfl) ⟨5938730, by rfl⟩ : syracuseStep 7918307 = 11877461) B11877461
theorem B2347825 : Blo 924580 2347825 := bstep (se 2 (by rfl) ⟨880434, by rfl⟩ : syracuseStep 2347825 = 1760869) B1760869
theorem B2085713 : Blo 924580 2085713 := bstep (se 2 (by rfl) ⟨782142, by rfl⟩ : syracuseStep 2085713 = 1564285) B1564285
theorem B2085731 : Blo 924580 2085731 := bstep (se 1 (by rfl) ⟨1564298, by rfl⟩ : syracuseStep 2085731 = 3128597) B3128597
theorem B1561457 : Blo 924580 1561457 := bstep (se 2 (by rfl) ⟨585546, by rfl⟩ : syracuseStep 1561457 = 1171093) B1171093
theorem B19059569 : Blo 924580 19059569 := bstep (se 2 (by rfl) ⟨7147338, by rfl⟩ : syracuseStep 19059569 = 14294677) B14294677
theorem B3953549 : Blo 924580 3953549 := bstep (se 3 (by rfl) ⟨741290, by rfl⟩ : syracuseStep 3953549 = 1482581) B1482581
theorem B1561585 : Blo 924580 1561585 := bstep (se 2 (by rfl) ⟨585594, by rfl⟩ : syracuseStep 1561585 = 1171189) B1171189
theorem B1561619 : Blo 924580 1561619 := bstep (se 1 (by rfl) ⟨1171214, by rfl⟩ : syracuseStep 1561619 = 2342429) B2342429
theorem B1758257 : Blo 924580 1758257 := bstep (se 2 (by rfl) ⟨659346, by rfl⟩ : syracuseStep 1758257 = 1318693) B1318693
theorem B2348099 : Blo 924580 2348099 := bstep (se 1 (by rfl) ⟨1761074, by rfl⟩ : syracuseStep 2348099 = 3522149) B3522149
theorem B1266769 : Blo 924580 1266769 := bstep (se 2 (by rfl) ⟨475038, by rfl⟩ : syracuseStep 1266769 = 950077) B950077
theorem B2086001 : Blo 924580 2086001 := bstep (se 2 (by rfl) ⟨782250, by rfl⟩ : syracuseStep 2086001 = 1564501) B1564501
theorem B2086019 : Blo 924580 2086019 := bstep (se 1 (by rfl) ⟨1564514, by rfl⟩ : syracuseStep 2086019 = 3129029) B3129029
theorem B1561747 : Blo 924580 1561747 := bstep (se 1 (by rfl) ⟨1171310, by rfl⟩ : syracuseStep 1561747 = 2342621) B2342621
theorem B2348291 : Blo 924580 2348291 := bstep (se 1 (by rfl) ⟨1761218, by rfl⟩ : syracuseStep 2348291 = 3522437) B3522437
theorem B5002501 : Blo 924580 5002501 := bstep (se 4 (by rfl) ⟨468984, by rfl⟩ : syracuseStep 5002501 = 937969) B937969
theorem B1561889 : Blo 924580 1561889 := bstep (se 2 (by rfl) ⟨585708, by rfl⟩ : syracuseStep 1561889 = 1171417) B1171417
theorem B2086289 : Blo 924580 2086289 := bstep (se 2 (by rfl) ⟨782358, by rfl⟩ : syracuseStep 2086289 = 1564717) B1564717
theorem B1562017 : Blo 924580 1562017 := bstep (se 2 (by rfl) ⟨585756, by rfl⟩ : syracuseStep 1562017 = 1171513) B1171513
theorem B2086307 : Blo 924580 2086307 := bstep (se 1 (by rfl) ⟨1564730, by rfl⟩ : syracuseStep 2086307 = 3129461) B3129461
theorem B1562051 : Blo 924580 1562051 := bstep (se 1 (by rfl) ⟨1171538, by rfl⟩ : syracuseStep 1562051 = 2343077) B2343077
theorem B2643491 : Blo 924580 2643491 := bstep (se 1 (by rfl) ⟨1982618, by rfl⟩ : syracuseStep 2643491 = 3965237) B3965237
theorem B1562179 : Blo 924580 1562179 := bstep (se 1 (by rfl) ⟨1171634, by rfl⟩ : syracuseStep 1562179 = 2343269) B2343269
theorem B2086577 : Blo 924580 2086577 := bstep (se 2 (by rfl) ⟨782466, by rfl⟩ : syracuseStep 2086577 = 1564933) B1564933
theorem B2086595 : Blo 924580 2086595 := bstep (se 1 (by rfl) ⟨1564946, by rfl⟩ : syracuseStep 2086595 = 3129893) B3129893
theorem B1562321 : Blo 924580 1562321 := bstep (se 2 (by rfl) ⟨585870, by rfl⟩ : syracuseStep 1562321 = 1171741) B1171741
theorem B1562449 : Blo 924580 1562449 := bstep (se 2 (by rfl) ⟨585918, by rfl⟩ : syracuseStep 1562449 = 1171837) B1171837
theorem B1562483 : Blo 924580 1562483 := bstep (se 1 (by rfl) ⟨1171862, by rfl⟩ : syracuseStep 1562483 = 2343725) B2343725
theorem B16078733 : Blo 924580 16078733 := bstep (se 3 (by rfl) ⟨3014762, by rfl⟩ : syracuseStep 16078733 = 6029525) B6029525
theorem B1759153 : Blo 924580 1759153 := bstep (se 2 (by rfl) ⟨659682, by rfl⟩ : syracuseStep 1759153 = 1319365) B1319365
theorem B2086865 : Blo 924580 2086865 := bstep (se 2 (by rfl) ⟨782574, by rfl⟩ : syracuseStep 2086865 = 1565149) B1565149
theorem B2086883 : Blo 924580 2086883 := bstep (se 1 (by rfl) ⟨1565162, by rfl⟩ : syracuseStep 2086883 = 3130325) B3130325
theorem B1562611 : Blo 924580 1562611 := bstep (se 1 (by rfl) ⟨1171958, by rfl⟩ : syracuseStep 1562611 = 2343917) B2343917
theorem B3004465 : Blo 924580 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B1759313 : Blo 924580 1759313 := bstep (se 2 (by rfl) ⟨659742, by rfl⟩ : syracuseStep 1759313 = 1319485) B1319485
theorem B1562753 : Blo 924580 1562753 := bstep (se 2 (by rfl) ⟨586032, by rfl⟩ : syracuseStep 1562753 = 1172065) B1172065
theorem B2349233 : Blo 924580 2349233 := bstep (se 2 (by rfl) ⟨880962, by rfl⟩ : syracuseStep 2349233 = 1761925) B1761925
theorem B2971853 : Blo 924580 2971853 := bstep (se 3 (by rfl) ⟨557222, by rfl⟩ : syracuseStep 2971853 = 1114445) B1114445
theorem B2349283 : Blo 924580 2349283 := bstep (se 1 (by rfl) ⟨1761962, by rfl⟩ : syracuseStep 2349283 = 3523925) B3523925
theorem B2087153 : Blo 924580 2087153 := bstep (se 2 (by rfl) ⟨782682, by rfl⟩ : syracuseStep 2087153 = 1565365) B1565365
theorem B1562881 : Blo 924580 1562881 := bstep (se 2 (by rfl) ⟨586080, by rfl⟩ : syracuseStep 1562881 = 1172161) B1172161
theorem B2087171 : Blo 924580 2087171 := bstep (se 1 (by rfl) ⟨1565378, by rfl⟩ : syracuseStep 2087171 = 3130757) B3130757
theorem B1562915 : Blo 924580 1562915 := bstep (se 1 (by rfl) ⟨1172186, by rfl⟩ : syracuseStep 1562915 = 2344373) B2344373
theorem B3332465 : Blo 924580 3332465 := bstep (se 2 (by rfl) ⟨1249674, by rfl⟩ : syracuseStep 3332465 = 2499349) B2499349
theorem B2349425 : Blo 924580 2349425 := bstep (se 2 (by rfl) ⟨881034, by rfl⟩ : syracuseStep 2349425 = 1762069) B1762069
theorem B1563043 : Blo 924580 1563043 := bstep (se 1 (by rfl) ⟨1172282, by rfl⟩ : syracuseStep 1563043 = 2344565) B2344565
theorem B1759715 : Blo 924580 1759715 := bstep (se 1 (by rfl) ⟨1319786, by rfl⟩ : syracuseStep 1759715 = 2639573) B2639573
theorem B2087441 : Blo 924580 2087441 := bstep (se 2 (by rfl) ⟨782790, by rfl⟩ : syracuseStep 2087441 = 1565581) B1565581
theorem B2087459 : Blo 924580 2087459 := bstep (se 1 (by rfl) ⟨1565594, by rfl⟩ : syracuseStep 2087459 = 3131189) B3131189
theorem B1563185 : Blo 924580 1563185 := bstep (se 2 (by rfl) ⟨586194, by rfl⟩ : syracuseStep 1563185 = 1172389) B1172389
theorem B1563313 : Blo 924580 1563313 := bstep (se 2 (by rfl) ⟨586242, by rfl⟩ : syracuseStep 1563313 = 1172485) B1172485
theorem B1563347 : Blo 924580 1563347 := bstep (se 1 (by rfl) ⟨1172510, by rfl⟩ : syracuseStep 1563347 = 2345021) B2345021
theorem B2087729 : Blo 924580 2087729 := bstep (se 2 (by rfl) ⟨782898, by rfl⟩ : syracuseStep 2087729 = 1565797) B1565797
theorem B1170227 : Blo 924580 1170227 := bstep (se 1 (by rfl) ⟨877670, by rfl⟩ : syracuseStep 1170227 = 1755341) B1755341
theorem B2087747 : Blo 924580 2087747 := bstep (se 1 (by rfl) ⟨1565810, by rfl⟩ : syracuseStep 2087747 = 3131621) B3131621
theorem B1563475 : Blo 924580 1563475 := bstep (se 1 (by rfl) ⟨1172606, by rfl⟩ : syracuseStep 1563475 = 2345213) B2345213
theorem B1563617 : Blo 924580 1563617 := bstep (se 2 (by rfl) ⟨586356, by rfl⟩ : syracuseStep 1563617 = 1172713) B1172713
theorem B3333155 : Blo 924580 3333155 := bstep (se 1 (by rfl) ⟨2499866, by rfl⟩ : syracuseStep 3333155 = 4999733) B4999733
theorem B2088017 : Blo 924580 2088017 := bstep (se 2 (by rfl) ⟨783006, by rfl⟩ : syracuseStep 2088017 = 1566013) B1566013
theorem B1072211 : Blo 924580 1072211 := bstep (se 1 (by rfl) ⟨804158, by rfl⟩ : syracuseStep 1072211 = 1608317) B1608317
theorem B1563745 : Blo 924580 1563745 := bstep (se 2 (by rfl) ⟨586404, by rfl⟩ : syracuseStep 1563745 = 1172809) B1172809
theorem B2088035 : Blo 924580 2088035 := bstep (se 1 (by rfl) ⟨1566026, by rfl⟩ : syracuseStep 2088035 = 3132053) B3132053
theorem B1563779 : Blo 924580 1563779 := bstep (se 1 (by rfl) ⟨1172834, by rfl⟩ : syracuseStep 1563779 = 2345669) B2345669
theorem B1563907 : Blo 924580 1563907 := bstep (se 1 (by rfl) ⟨1172930, by rfl⟩ : syracuseStep 1563907 = 2345861) B2345861
theorem B2350417 : Blo 924580 2350417 := bstep (se 2 (by rfl) ⟨881406, by rfl⟩ : syracuseStep 2350417 = 1762813) B1762813
theorem B1760611 : Blo 924580 1760611 := bstep (se 1 (by rfl) ⟨1320458, by rfl⟩ : syracuseStep 1760611 = 2640917) B2640917
theorem B2088305 : Blo 924580 2088305 := bstep (se 2 (by rfl) ⟨783114, by rfl⟩ : syracuseStep 2088305 = 1566229) B1566229
theorem B2088323 : Blo 924580 2088323 := bstep (se 1 (by rfl) ⟨1566242, by rfl⟩ : syracuseStep 2088323 = 3132485) B3132485
theorem B1564049 : Blo 924580 1564049 := bstep (se 2 (by rfl) ⟨586518, by rfl⟩ : syracuseStep 1564049 = 1173037) B1173037
theorem B3562957 : Blo 924580 3562957 := bstep (se 3 (by rfl) ⟨668054, by rfl⟩ : syracuseStep 3562957 = 1336109) B1336109
theorem B1170931 : Blo 924580 1170931 := bstep (se 1 (by rfl) ⟨878198, by rfl⟩ : syracuseStep 1170931 = 1756397) B1756397
theorem B1760771 : Blo 924580 1760771 := bstep (se 1 (by rfl) ⟨1320578, by rfl⟩ : syracuseStep 1760771 = 2641157) B2641157
theorem B1564177 : Blo 924580 1564177 := bstep (se 2 (by rfl) ⟨586566, by rfl⟩ : syracuseStep 1564177 = 1173133) B1173133
theorem B1564211 : Blo 924580 1564211 := bstep (se 1 (by rfl) ⟨1173158, by rfl⟩ : syracuseStep 1564211 = 2346317) B2346317
theorem B1171027 : Blo 924580 1171027 := bstep (se 1 (by rfl) ⟨878270, by rfl⟩ : syracuseStep 1171027 = 1756541) B1756541
theorem B2088593 : Blo 924580 2088593 := bstep (se 2 (by rfl) ⟨783222, by rfl⟩ : syracuseStep 2088593 = 1566445) B1566445
theorem B2088611 : Blo 924580 2088611 := bstep (se 1 (by rfl) ⟨1566458, by rfl⟩ : syracuseStep 2088611 = 3132917) B3132917
theorem B1564339 : Blo 924580 1564339 := bstep (se 1 (by rfl) ⟨1173254, by rfl⟩ : syracuseStep 1564339 = 2346509) B2346509
theorem B4284109 : Blo 924580 4284109 := bstep (se 3 (by rfl) ⟨803270, by rfl⟩ : syracuseStep 4284109 = 1606541) B1606541
theorem B1040179 : Blo 924580 1040179 := bstep (se 1 (by rfl) ⟨780134, by rfl⟩ : syracuseStep 1040179 = 1560269) B1560269
theorem B1564481 : Blo 924580 1564481 := bstep (se 2 (by rfl) ⟨586680, by rfl⟩ : syracuseStep 1564481 = 1173361) B1173361
theorem B25681805 : Blo 924580 25681805 := bstep (se 3 (by rfl) ⟨4815338, by rfl⟩ : syracuseStep 25681805 = 9630677) B9630677
theorem B2088881 : Blo 924580 2088881 := bstep (se 2 (by rfl) ⟨783330, by rfl⟩ : syracuseStep 2088881 = 1566661) B1566661
theorem B1564609 : Blo 924580 1564609 := bstep (se 2 (by rfl) ⟨586728, by rfl⟩ : syracuseStep 1564609 = 1173457) B1173457
theorem B1040323 : Blo 924580 1040323 := bstep (se 1 (by rfl) ⟨780242, by rfl⟩ : syracuseStep 1040323 = 1560485) B1560485
theorem B2088899 : Blo 924580 2088899 := bstep (se 1 (by rfl) ⟨1566674, by rfl⟩ : syracuseStep 2088899 = 3133349) B3133349
theorem B1564643 : Blo 924580 1564643 := bstep (se 1 (by rfl) ⟨1173482, by rfl⟩ : syracuseStep 1564643 = 2346965) B2346965
theorem B3170353 : Blo 924580 3170353 := bstep (se 2 (by rfl) ⟨1188882, by rfl⟩ : syracuseStep 3170353 = 2377765) B2377765
theorem B1171523 : Blo 924580 1171523 := bstep (se 1 (by rfl) ⟨878642, by rfl⟩ : syracuseStep 1171523 = 1757285) B1757285
theorem B1040467 : Blo 924580 1040467 := bstep (se 1 (by rfl) ⟨780350, by rfl⟩ : syracuseStep 1040467 = 1560701) B1560701
theorem B1564771 : Blo 924580 1564771 := bstep (se 1 (by rfl) ⟨1173578, by rfl⟩ : syracuseStep 1564771 = 2347157) B2347157
theorem B1695953 : Blo 924580 1695953 := bstep (se 2 (by rfl) ⟨635982, by rfl⟩ : syracuseStep 1695953 = 1271965) B1271965
theorem B2089169 : Blo 924580 2089169 := bstep (se 2 (by rfl) ⟨783438, by rfl⟩ : syracuseStep 2089169 = 1566877) B1566877
theorem B1040611 : Blo 924580 1040611 := bstep (se 1 (by rfl) ⟨780458, by rfl⟩ : syracuseStep 1040611 = 1560917) B1560917
theorem B2089187 : Blo 924580 2089187 := bstep (se 1 (by rfl) ⟨1566890, by rfl⟩ : syracuseStep 2089187 = 3133781) B3133781
theorem B1564913 : Blo 924580 1564913 := bstep (se 2 (by rfl) ⟨586842, by rfl⟩ : syracuseStep 1564913 = 1173685) B1173685
theorem B1565041 : Blo 924580 1565041 := bstep (se 2 (by rfl) ⟨586890, by rfl⟩ : syracuseStep 1565041 = 1173781) B1173781
theorem B1040755 : Blo 924580 1040755 := bstep (se 1 (by rfl) ⟨780566, by rfl⟩ : syracuseStep 1040755 = 1561133) B1561133
theorem B1565075 : Blo 924580 1565075 := bstep (se 1 (by rfl) ⟨1173806, by rfl⟩ : syracuseStep 1565075 = 2347613) B2347613
theorem B3563939 : Blo 924580 3563939 := bstep (se 1 (by rfl) ⟨2672954, by rfl⟩ : syracuseStep 3563939 = 5345909) B5345909
theorem B1040899 : Blo 924580 1040899 := bstep (se 1 (by rfl) ⟨780674, by rfl⟩ : syracuseStep 1040899 = 1561349) B1561349
theorem B1565203 : Blo 924580 1565203 := bstep (se 1 (by rfl) ⟨1173902, by rfl⟩ : syracuseStep 1565203 = 2347805) B2347805
theorem B4448803 : Blo 924580 4448803 := bstep (se 1 (by rfl) ⟨3336602, by rfl⟩ : syracuseStep 4448803 = 6673205) B6673205
theorem B1761841 : Blo 924580 1761841 := bstep (se 2 (by rfl) ⟨660690, by rfl⟩ : syracuseStep 1761841 = 1321381) B1321381
theorem B1041043 : Blo 924580 1041043 := bstep (se 1 (by rfl) ⟨780782, by rfl⟩ : syracuseStep 1041043 = 1561565) B1561565
theorem B1565345 : Blo 924580 1565345 := bstep (se 2 (by rfl) ⟨587004, by rfl⟩ : syracuseStep 1565345 = 1174009) B1174009
theorem B1172227 : Blo 924580 1172227 := bstep (se 1 (by rfl) ⟨879170, by rfl⟩ : syracuseStep 1172227 = 1758341) B1758341
theorem B1565473 : Blo 924580 1565473 := bstep (se 2 (by rfl) ⟨587052, by rfl⟩ : syracuseStep 1565473 = 1174105) B1174105
theorem B1041187 : Blo 924580 1041187 := bstep (se 1 (by rfl) ⟨780890, by rfl⟩ : syracuseStep 1041187 = 1561781) B1561781
theorem B1565507 : Blo 924580 1565507 := bstep (se 1 (by rfl) ⟨1174130, by rfl⟩ : syracuseStep 1565507 = 2348261) B2348261
theorem B7037765 : Blo 924580 7037765 := bstep (se 4 (by rfl) ⟨659790, by rfl⟩ : syracuseStep 7037765 = 1319581) B1319581
theorem B1172323 : Blo 924580 1172323 := bstep (se 1 (by rfl) ⟨879242, by rfl⟩ : syracuseStep 1172323 = 1758485) B1758485
theorem B1041331 : Blo 924580 1041331 := bstep (se 1 (by rfl) ⟨780998, by rfl⟩ : syracuseStep 1041331 = 1561997) B1561997
theorem B1565635 : Blo 924580 1565635 := bstep (se 1 (by rfl) ⟨1174226, by rfl⟩ : syracuseStep 1565635 = 2348453) B2348453
theorem B1041475 : Blo 924580 1041475 := bstep (se 1 (by rfl) ⟨781106, by rfl⟩ : syracuseStep 1041475 = 1562213) B1562213
theorem B1565777 : Blo 924580 1565777 := bstep (se 2 (by rfl) ⟨587166, by rfl⟩ : syracuseStep 1565777 = 1174333) B1174333
theorem B2679907 : Blo 924580 2679907 := bstep (se 1 (by rfl) ⟨2009930, by rfl⟩ : syracuseStep 2679907 = 4019861) B4019861
theorem B3957923 : Blo 924580 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B1565905 : Blo 924580 1565905 := bstep (se 2 (by rfl) ⟨587214, by rfl⟩ : syracuseStep 1565905 = 1174429) B1174429
theorem B1041619 : Blo 924580 1041619 := bstep (se 1 (by rfl) ⟨781214, by rfl⟩ : syracuseStep 1041619 = 1562429) B1562429
theorem B1565939 : Blo 924580 1565939 := bstep (se 1 (by rfl) ⟨1174454, by rfl⟩ : syracuseStep 1565939 = 2348909) B2348909
theorem B5924173 : Blo 924580 5924173 := bstep (se 3 (by rfl) ⟨1110782, by rfl⟩ : syracuseStep 5924173 = 2221565) B2221565
theorem B1172819 : Blo 924580 1172819 := bstep (se 1 (by rfl) ⟨879614, by rfl⟩ : syracuseStep 1172819 = 1759229) B1759229
theorem B1041763 : Blo 924580 1041763 := bstep (se 1 (by rfl) ⟨781322, by rfl⟩ : syracuseStep 1041763 = 1562645) B1562645
theorem B1566067 : Blo 924580 1566067 := bstep (se 1 (by rfl) ⟨1174550, by rfl⟩ : syracuseStep 1566067 = 2349101) B2349101
theorem B1041907 : Blo 924580 1041907 := bstep (se 1 (by rfl) ⟨781430, by rfl⟩ : syracuseStep 1041907 = 1562861) B1562861
theorem B1566209 : Blo 924580 1566209 := bstep (se 2 (by rfl) ⟨587328, by rfl⟩ : syracuseStep 1566209 = 1174657) B1174657
theorem B2221681 : Blo 924580 2221681 := bstep (se 2 (by rfl) ⟨833130, by rfl⟩ : syracuseStep 2221681 = 1666261) B1666261
theorem B1566337 : Blo 924580 1566337 := bstep (se 2 (by rfl) ⟨587376, by rfl⟩ : syracuseStep 1566337 = 1174753) B1174753
theorem B1042051 : Blo 924580 1042051 := bstep (se 1 (by rfl) ⟨781538, by rfl⟩ : syracuseStep 1042051 = 1563077) B1563077
theorem B1566371 : Blo 924580 1566371 := bstep (se 1 (by rfl) ⟨1174778, by rfl⟩ : syracuseStep 1566371 = 2349557) B2349557
theorem B22537925 : Blo 924580 22537925 := bstep (se 4 (by rfl) ⟨2112930, by rfl⟩ : syracuseStep 22537925 = 4225861) B4225861
theorem B1042195 : Blo 924580 1042195 := bstep (se 1 (by rfl) ⟨781646, by rfl⟩ : syracuseStep 1042195 = 1563293) B1563293
theorem B1566499 : Blo 924580 1566499 := bstep (se 1 (by rfl) ⟨1174874, by rfl⟩ : syracuseStep 1566499 = 2349749) B2349749
theorem B1042339 : Blo 924580 1042339 := bstep (se 1 (by rfl) ⟨781754, by rfl⟩ : syracuseStep 1042339 = 1563509) B1563509
theorem B1566641 : Blo 924580 1566641 := bstep (se 2 (by rfl) ⟨587490, by rfl⟩ : syracuseStep 1566641 = 1174981) B1174981
theorem B1173523 : Blo 924580 1173523 := bstep (se 1 (by rfl) ⟨880142, by rfl⟩ : syracuseStep 1173523 = 1760285) B1760285
theorem B1566769 : Blo 924580 1566769 := bstep (se 2 (by rfl) ⟨587538, by rfl⟩ : syracuseStep 1566769 = 1175077) B1175077
theorem B1042483 : Blo 924580 1042483 := bstep (se 1 (by rfl) ⟨781862, by rfl⟩ : syracuseStep 1042483 = 1563725) B1563725
theorem B1566803 : Blo 924580 1566803 := bstep (se 1 (by rfl) ⟨1175102, by rfl⟩ : syracuseStep 1566803 = 2350205) B2350205
theorem B1173619 : Blo 924580 1173619 := bstep (se 1 (by rfl) ⟨880214, by rfl⟩ : syracuseStep 1173619 = 1760429) B1760429
theorem B1042627 : Blo 924580 1042627 := bstep (se 1 (by rfl) ⟨781970, by rfl⟩ : syracuseStep 1042627 = 1563941) B1563941
theorem B1566931 : Blo 924580 1566931 := bstep (se 1 (by rfl) ⟨1175198, by rfl⟩ : syracuseStep 1566931 = 2350397) B2350397
theorem B38070499 : Blo 924580 38070499 := bstep (se 1 (by rfl) ⟨28552874, by rfl⟩ : syracuseStep 38070499 = 57105749) B57105749
theorem B9038051 : Blo 924580 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B2812205 : Blo 924580 2812205 := bstep (se 3 (by rfl) ⟨527288, by rfl⟩ : syracuseStep 2812205 = 1054577) B1054577
theorem B1042771 : Blo 924580 1042771 := bstep (se 1 (by rfl) ⟨782078, by rfl⟩ : syracuseStep 1042771 = 1564157) B1564157
theorem B1042915 : Blo 924580 1042915 := bstep (se 1 (by rfl) ⟨782186, by rfl⟩ : syracuseStep 1042915 = 1564373) B1564373
theorem B1174115 : Blo 924580 1174115 := bstep (se 1 (by rfl) ⟨880586, by rfl⟩ : syracuseStep 1174115 = 1761173) B1761173
theorem B1043059 : Blo 924580 1043059 := bstep (se 1 (by rfl) ⟨782294, by rfl⟩ : syracuseStep 1043059 = 1564589) B1564589
theorem B1501939 : Blo 924580 1501939 := bstep (se 1 (by rfl) ⟨1126454, by rfl⟩ : syracuseStep 1501939 = 2252909) B2252909
theorem B1043203 : Blo 924580 1043203 := bstep (se 1 (by rfl) ⟨782402, by rfl⟩ : syracuseStep 1043203 = 1564805) B1564805
theorem B1043347 : Blo 924580 1043347 := bstep (se 1 (by rfl) ⟨782510, by rfl⟩ : syracuseStep 1043347 = 1565021) B1565021
theorem B1043491 : Blo 924580 1043491 := bstep (se 1 (by rfl) ⟨782618, by rfl⟩ : syracuseStep 1043491 = 1565237) B1565237
theorem B1043635 : Blo 924580 1043635 := bstep (se 1 (by rfl) ⟨782726, by rfl⟩ : syracuseStep 1043635 = 1565453) B1565453
theorem B1174819 : Blo 924580 1174819 := bstep (se 1 (by rfl) ⟨881114, by rfl⟩ : syracuseStep 1174819 = 1762229) B1762229
theorem B1043779 : Blo 924580 1043779 := bstep (se 1 (by rfl) ⟨782834, by rfl⟩ : syracuseStep 1043779 = 1565669) B1565669
theorem B5008709 : Blo 924580 5008709 := bstep (se 4 (by rfl) ⟨469566, by rfl⟩ : syracuseStep 5008709 = 939133) B939133
theorem B1174915 : Blo 924580 1174915 := bstep (se 1 (by rfl) ⟨881186, by rfl⟩ : syracuseStep 1174915 = 1762373) B1762373
theorem B1043923 : Blo 924580 1043923 := bstep (se 1 (by rfl) ⟨782942, by rfl⟩ : syracuseStep 1043923 = 1565885) B1565885
theorem B1502707 : Blo 924580 1502707 := bstep (se 1 (by rfl) ⟨1127030, by rfl⟩ : syracuseStep 1502707 = 2254061) B2254061
theorem B5926405 : Blo 924580 5926405 := bstep (se 4 (by rfl) ⟨555600, by rfl⟩ : syracuseStep 5926405 = 1111201) B1111201
theorem B1044067 : Blo 924580 1044067 := bstep (se 1 (by rfl) ⟨783050, by rfl⟩ : syracuseStep 1044067 = 1566101) B1566101
theorem B3010193 : Blo 924580 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B1044211 : Blo 924580 1044211 := bstep (se 1 (by rfl) ⟨783158, by rfl⟩ : syracuseStep 1044211 = 1566317) B1566317
theorem B3960589 : Blo 924580 3960589 := bstep (se 3 (by rfl) ⟨742610, by rfl⟩ : syracuseStep 3960589 = 1485221) B1485221
theorem B1044355 : Blo 924580 1044355 := bstep (se 1 (by rfl) ⟨783266, by rfl⟩ : syracuseStep 1044355 = 1566533) B1566533
theorem B10547171 : Blo 924580 10547171 := bstep (se 1 (by rfl) ⟨7910378, by rfl⟩ : syracuseStep 10547171 = 15820757) B15820757
theorem B1044499 : Blo 924580 1044499 := bstep (se 1 (by rfl) ⟨783374, by rfl⟩ : syracuseStep 1044499 = 1566749) B1566749
theorem B1044643 : Blo 924580 1044643 := bstep (se 1 (by rfl) ⟨783482, by rfl⟩ : syracuseStep 1044643 = 1566965) B1566965
theorem B2257091 : Blo 924580 2257091 := bstep (se 1 (by rfl) ⟨1692818, by rfl⟩ : syracuseStep 2257091 = 3385637) B3385637
theorem B3207395 : Blo 924580 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B1667299 : Blo 924580 1667299 := bstep (se 1 (by rfl) ⟨1250474, by rfl⟩ : syracuseStep 1667299 = 2500949) B2500949
theorem B3764657 : Blo 924580 3764657 := bstep (se 2 (by rfl) ⟨1411746, by rfl⟩ : syracuseStep 3764657 = 2823493) B2823493
theorem B3961649 : Blo 924580 3961649 := bstep (se 2 (by rfl) ⟨1485618, by rfl⟩ : syracuseStep 3961649 = 2971237) B2971237
theorem B4682609 : Blo 924580 4682609 := bstep (se 2 (by rfl) ⟨1755978, by rfl⟩ : syracuseStep 4682609 = 3511957) B3511957
theorem B5632973 : Blo 924580 5632973 := bstep (se 3 (by rfl) ⟨1056182, by rfl⟩ : syracuseStep 5632973 = 2112365) B2112365
theorem B3339299 : Blo 924580 3339299 := bstep (se 1 (by rfl) ⟨2504474, by rfl⟩ : syracuseStep 3339299 = 5008949) B5008949
theorem B1668323 : Blo 924580 1668323 := bstep (se 1 (by rfl) ⟨1251242, by rfl⟩ : syracuseStep 1668323 = 2502485) B2502485
theorem B1504577 : Blo 924580 1504577 := bstep (se 2 (by rfl) ⟨564216, by rfl⟩ : syracuseStep 1504577 = 1128433) B1128433
theorem B5273221 : Blo 924580 5273221 := bstep (se 4 (by rfl) ⟨494364, by rfl⟩ : syracuseStep 5273221 = 988729) B988729
theorem B6026885 : Blo 924580 6026885 := bstep (se 4 (by rfl) ⟨565020, by rfl⟩ : syracuseStep 6026885 = 1130041) B1130041
theorem B2815661 : Blo 924580 2815661 := bstep (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) B1055873
theorem B1111763 : Blo 924580 1111763 := bstep (se 1 (by rfl) ⟨833822, by rfl⟩ : syracuseStep 1111763 = 1667645) B1667645
theorem B2815843 : Blo 924580 2815843 := bstep (se 1 (by rfl) ⟨2111882, by rfl⟩ : syracuseStep 2815843 = 4223765) B4223765
theorem B8353763 : Blo 924580 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B2226179 : Blo 924580 2226179 := bstep (se 1 (by rfl) ⟨1669634, by rfl⟩ : syracuseStep 2226179 = 3339269) B3339269
theorem B4684067 : Blo 924580 4684067 := bstep (se 1 (by rfl) ⟨3513050, by rfl⟩ : syracuseStep 4684067 = 7026101) B7026101
theorem B7043597 : Blo 924580 7043597 := bstep (se 3 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 7043597 = 2641349) B2641349
theorem B4291213 : Blo 924580 4291213 := bstep (se 3 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 4291213 = 1609205) B1609205
theorem B2226947 : Blo 924580 2226947 := bstep (se 1 (by rfl) ⟨1670210, by rfl⟩ : syracuseStep 2226947 = 3340421) B3340421
theorem B4225969 : Blo 924580 4225969 := bstep (se 2 (by rfl) ⟨1584738, by rfl⟩ : syracuseStep 4225969 = 3169477) B3169477
theorem B1670147 : Blo 924580 1670147 := bstep (se 1 (by rfl) ⟨1252610, by rfl⟩ : syracuseStep 1670147 = 2505221) B2505221
theorem B4684877 : Blo 924580 4684877 := bstep (se 3 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 4684877 = 1756829) B1756829
theorem B4455587 : Blo 924580 4455587 := bstep (se 1 (by rfl) ⟨3341690, by rfl⟩ : syracuseStep 4455587 = 6683381) B6683381
theorem B2227409 : Blo 924580 2227409 := bstep (se 2 (by rfl) ⟨835278, by rfl⟩ : syracuseStep 2227409 = 1670557) B1670557
theorem B5012707 : Blo 924580 5012707 := bstep (se 1 (by rfl) ⟨3759530, by rfl⟩ : syracuseStep 5012707 = 7519061) B7519061
theorem B2227505 : Blo 924580 2227505 := bstep (se 2 (by rfl) ⟨835314, by rfl⟩ : syracuseStep 2227505 = 1670629) B1670629
theorem B4521521 : Blo 924580 4521521 := bstep (se 2 (by rfl) ⟨1695570, by rfl⟩ : syracuseStep 4521521 = 3391141) B3391141
theorem B5275205 : Blo 924580 5275205 := bstep (se 4 (by rfl) ⟨494550, by rfl⟩ : syracuseStep 5275205 = 989101) B989101
theorem B3964621 : Blo 924580 3964621 := bstep (se 3 (by rfl) ⟨743366, by rfl⟩ : syracuseStep 3964621 = 1486733) B1486733
theorem B4456241 : Blo 924580 4456241 := bstep (se 2 (by rfl) ⟨1671090, by rfl⟩ : syracuseStep 4456241 = 3342181) B3342181
theorem B1113907 : Blo 924580 1113907 := bstep (se 1 (by rfl) ⟨835430, by rfl⟩ : syracuseStep 1113907 = 1670861) B1670861
theorem B2031427 : Blo 924580 2031427 := bstep (se 1 (by rfl) ⟨1523570, by rfl⟩ : syracuseStep 2031427 = 3047141) B3047141
theorem B4226993 : Blo 924580 4226993 := bstep (se 2 (by rfl) ⟨1585122, by rfl⟩ : syracuseStep 4226993 = 3170245) B3170245
theorem B1114123 : Blo 924580 1114123 := bstep (se 1 (by rfl) ⟨835592, by rfl⟩ : syracuseStep 1114123 = 1671185) B1671185
theorem B4227137 : Blo 924580 4227137 := bstep (se 2 (by rfl) ⟨1585176, by rfl⟩ : syracuseStep 4227137 = 3170353) B3170353
theorem B4686173 : Blo 924580 4686173 := bstep (se 3 (by rfl) ⟨878657, by rfl⟩ : syracuseStep 4686173 = 1757315) B1757315
theorem B5014091 : Blo 924580 5014091 := bstep (se 1 (by rfl) ⟨3760568, by rfl⟩ : syracuseStep 5014091 = 7521137) B7521137
theorem B8553053 : Blo 924580 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B5931737 : Blo 924580 5931737 := bstep (se 2 (by rfl) ⟨2224401, by rfl⟩ : syracuseStep 5931737 = 4448803) B4448803
theorem B3965699 : Blo 924580 3965699 := bstep (se 1 (by rfl) ⟨2974274, by rfl⟩ : syracuseStep 3965699 = 5948549) B5948549
theorem B10159139 : Blo 924580 10159139 := bstep (se 1 (by rfl) ⟨7619354, by rfl⟩ : syracuseStep 10159139 = 15238709) B15238709
theorem B13337693 : Blo 924580 13337693 := bstep (se 3 (by rfl) ⟨2500817, by rfl⟩ : syracuseStep 13337693 = 5001635) B5001635
theorem B9503837 : Blo 924580 9503837 := bstep (se 3 (by rfl) ⟨1781969, by rfl⟩ : syracuseStep 9503837 = 3563939) B3563939
theorem B7144625 : Blo 924580 7144625 := bstep (se 2 (by rfl) ⟨2679234, by rfl⟩ : syracuseStep 7144625 = 5358469) B5358469
theorem B3343639 : Blo 924580 3343639 := bstep (se 1 (by rfl) ⟨2507729, by rfl⟩ : syracuseStep 3343639 = 5015459) B5015459
theorem B2229707 : Blo 924580 2229707 := bstep (se 1 (by rfl) ⟨1672280, by rfl⟩ : syracuseStep 2229707 = 3344561) B3344561
theorem B1672663 : Blo 924580 1672663 := bstep (se 1 (by rfl) ⟨1254497, by rfl⟩ : syracuseStep 1672663 = 2508995) B2508995
theorem B3573209 : Blo 924580 3573209 := bstep (se 2 (by rfl) ⟨1339953, by rfl⟩ : syracuseStep 3573209 = 2679907) B2679907
theorem B7898897 : Blo 924580 7898897 := bstep (se 2 (by rfl) ⟨2962086, by rfl⟩ : syracuseStep 7898897 = 5924173) B5924173
theorem B25692005 : Blo 924580 25692005 := bstep (se 4 (by rfl) ⟨2408625, by rfl⟩ : syracuseStep 25692005 = 4817251) B4817251
theorem B4753559 : Blo 924580 4753559 := bstep (se 1 (by rfl) ⟨3565169, by rfl⟩ : syracuseStep 4753559 = 7130339) B7130339
theorem B4688279 : Blo 924580 4688279 := bstep (se 1 (by rfl) ⟨3516209, by rfl⟩ : syracuseStep 4688279 = 7032419) B7032419
theorem B7932491 : Blo 924580 7932491 := bstep (se 1 (by rfl) ⟨5949368, by rfl⟩ : syracuseStep 7932491 = 11898737) B11898737
theorem B1411673 : Blo 924580 1411673 := bstep (se 2 (by rfl) ⟨529377, by rfl⟩ : syracuseStep 1411673 = 1058755) B1058755
theorem B7047971 : Blo 924580 7047971 := bstep (se 1 (by rfl) ⟨5285978, by rfl⟩ : syracuseStep 7047971 = 10571957) B10571957
theorem B50760665 : Blo 924580 50760665 := bstep (se 2 (by rfl) ⟨19035249, by rfl⟩ : syracuseStep 50760665 = 38070499) B38070499
theorem B10554461 : Blo 924580 10554461 := bstep (se 3 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 10554461 = 3957923) B3957923
theorem B5278871 : Blo 924580 5278871 := bstep (se 1 (by rfl) ⟨3959153, by rfl⟩ : syracuseStep 5278871 = 7918307) B7918307
theorem B4460183 : Blo 924580 4460183 := bstep (se 1 (by rfl) ⟨3345137, by rfl⟩ : syracuseStep 4460183 = 6690275) B6690275
theorem B10719155 : Blo 924580 10719155 := bstep (se 1 (by rfl) ⟨8039366, by rfl⟩ : syracuseStep 10719155 = 16078733) B16078733
theorem B4067545 : Blo 924580 4067545 := bstep (se 2 (by rfl) ⟨1525329, by rfl⟩ : syracuseStep 4067545 = 3050659) B3050659
theorem B987499 : Blo 924580 987499 := bstep (se 1 (by rfl) ⟨740624, by rfl⟩ : syracuseStep 987499 = 1481249) B1481249
theorem B2003609 : Blo 924580 2003609 := bstep (se 2 (by rfl) ⟨751353, by rfl⟩ : syracuseStep 2003609 = 1502707) B1502707
theorem B7901873 : Blo 924580 7901873 := bstep (se 2 (by rfl) ⟨2963202, by rfl⟩ : syracuseStep 7901873 = 5926405) B5926405
theorem B1250059 : Blo 924580 1250059 := bstep (se 1 (by rfl) ⟨937544, by rfl⟩ : syracuseStep 1250059 = 1875089) B1875089
theorem B5280785 : Blo 924580 5280785 := bstep (se 2 (by rfl) ⟨1980294, by rfl⟩ : syracuseStep 5280785 = 3960589) B3960589
theorem B988247 : Blo 924580 988247 := bstep (se 1 (by rfl) ⟨741185, by rfl⟩ : syracuseStep 988247 = 1482371) B1482371
theorem B3806353 : Blo 924580 3806353 := bstep (se 2 (by rfl) ⟨1427382, by rfl⟩ : syracuseStep 3806353 = 2854765) B2854765
theorem B3511745 : Blo 924580 3511745 := bstep (se 2 (by rfl) ⟨1316904, by rfl⟩ : syracuseStep 3511745 = 2633809) B2633809
theorem B1316569 : Blo 924580 1316569 := bstep (se 2 (by rfl) ⟨493713, by rfl⟩ : syracuseStep 1316569 = 987427) B987427
theorem B4691843 : Blo 924580 4691843 := bstep (se 1 (by rfl) ⟨3518882, by rfl⟩ : syracuseStep 4691843 = 7037765) B7037765
theorem B1251545 : Blo 924580 1251545 := bstep (se 2 (by rfl) ⟨469329, by rfl⟩ : syracuseStep 1251545 = 938659) B938659
theorem B1251659 : Blo 924580 1251659 := bstep (se 1 (by rfl) ⟨938744, by rfl⟩ : syracuseStep 1251659 = 1877489) B1877489
theorem B989515 : Blo 924580 989515 := bstep (se 1 (by rfl) ⟨742136, by rfl⟩ : syracuseStep 989515 = 1484273) B1484273
theorem B3513233 : Blo 924580 3513233 := bstep (se 2 (by rfl) ⟨1317462, by rfl⟩ : syracuseStep 3513233 = 2634925) B2634925
theorem B924587 : Blo 924580 924587 := bstep (se 1 (by rfl) ⟨693440, by rfl⟩ : syracuseStep 924587 = 1386881) B1386881
theorem B924599 : Blo 924580 924599 := bstep (se 1 (by rfl) ⟨693449, by rfl⟩ : syracuseStep 924599 = 1386899) B1386899
theorem B924619 : Blo 924580 924619 := bstep (se 1 (by rfl) ⟨693464, by rfl⟩ : syracuseStep 924619 = 1386929) B1386929
theorem B924631 : Blo 924580 924631 := bstep (se 1 (by rfl) ⟨693473, by rfl⟩ : syracuseStep 924631 = 1386947) B1386947
theorem B924651 : Blo 924580 924651 := bstep (se 1 (by rfl) ⟨693488, by rfl⟩ : syracuseStep 924651 = 1386977) B1386977
theorem B924663 : Blo 924580 924663 := bstep (se 1 (by rfl) ⟨693497, by rfl⟩ : syracuseStep 924663 = 1386995) B1386995
theorem B924683 : Blo 924580 924683 := bstep (se 1 (by rfl) ⟨693512, by rfl⟩ : syracuseStep 924683 = 1387025) B1387025
theorem B924695 : Blo 924580 924695 := bstep (se 1 (by rfl) ⟨693521, by rfl⟩ : syracuseStep 924695 = 1387043) B1387043
theorem B924715 : Blo 924580 924715 := bstep (se 1 (by rfl) ⟨693536, by rfl⟩ : syracuseStep 924715 = 1387073) B1387073
theorem B924727 : Blo 924580 924727 := bstep (se 1 (by rfl) ⟨693545, by rfl⟩ : syracuseStep 924727 = 1387091) B1387091
theorem B990263 : Blo 924580 990263 := bstep (se 1 (by rfl) ⟨742697, by rfl⟩ : syracuseStep 990263 = 1485395) B1485395
theorem B924747 : Blo 924580 924747 := bstep (se 1 (by rfl) ⟨693560, by rfl⟩ : syracuseStep 924747 = 1387121) B1387121
theorem B924759 : Blo 924580 924759 := bstep (se 1 (by rfl) ⟨693569, by rfl⟩ : syracuseStep 924759 = 1387139) B1387139
theorem B924779 : Blo 924580 924779 := bstep (se 1 (by rfl) ⟨693584, by rfl⟩ : syracuseStep 924779 = 1387169) B1387169
theorem B924791 : Blo 924580 924791 := bstep (se 1 (by rfl) ⟨693593, by rfl⟩ : syracuseStep 924791 = 1387187) B1387187
theorem B924811 : Blo 924580 924811 := bstep (se 1 (by rfl) ⟨693608, by rfl⟩ : syracuseStep 924811 = 1387217) B1387217
theorem B1318027 : Blo 924580 1318027 := bstep (se 1 (by rfl) ⟨988520, by rfl⟩ : syracuseStep 1318027 = 1977041) B1977041
theorem B924823 : Blo 924580 924823 := bstep (se 1 (by rfl) ⟨693617, by rfl⟩ : syracuseStep 924823 = 1387235) B1387235
theorem B924843 : Blo 924580 924843 := bstep (se 1 (by rfl) ⟨693632, by rfl⟩ : syracuseStep 924843 = 1387265) B1387265
theorem B924855 : Blo 924580 924855 := bstep (se 1 (by rfl) ⟨693641, by rfl⟩ : syracuseStep 924855 = 1387283) B1387283
theorem B924875 : Blo 924580 924875 := bstep (se 1 (by rfl) ⟨693656, by rfl⟩ : syracuseStep 924875 = 1387313) B1387313
theorem B924887 : Blo 924580 924887 := bstep (se 1 (by rfl) ⟨693665, by rfl⟩ : syracuseStep 924887 = 1387331) B1387331
theorem B924907 : Blo 924580 924907 := bstep (se 1 (by rfl) ⟨693680, by rfl⟩ : syracuseStep 924907 = 1387361) B1387361
theorem B924919 : Blo 924580 924919 := bstep (se 1 (by rfl) ⟨693689, by rfl⟩ : syracuseStep 924919 = 1387379) B1387379
theorem B924939 : Blo 924580 924939 := bstep (se 1 (by rfl) ⟨693704, by rfl⟩ : syracuseStep 924939 = 1387409) B1387409
theorem B924951 : Blo 924580 924951 := bstep (se 1 (by rfl) ⟨693713, by rfl⟩ : syracuseStep 924951 = 1387427) B1387427
theorem B924971 : Blo 924580 924971 := bstep (se 1 (by rfl) ⟨693728, by rfl⟩ : syracuseStep 924971 = 1387457) B1387457
theorem B924983 : Blo 924580 924983 := bstep (se 1 (by rfl) ⟨693737, by rfl⟩ : syracuseStep 924983 = 1387475) B1387475
theorem B925003 : Blo 924580 925003 := bstep (se 1 (by rfl) ⟨693752, by rfl⟩ : syracuseStep 925003 = 1387505) B1387505
theorem B925015 : Blo 924580 925015 := bstep (se 1 (by rfl) ⟨693761, by rfl⟩ : syracuseStep 925015 = 1387523) B1387523
theorem B3513689 : Blo 924580 3513689 := bstep (se 2 (by rfl) ⟨1317633, by rfl⟩ : syracuseStep 3513689 = 2635267) B2635267
theorem B5938525 : Blo 924580 5938525 := bstep (se 3 (by rfl) ⟨1113473, by rfl⟩ : syracuseStep 5938525 = 2226947) B2226947
theorem B925035 : Blo 924580 925035 := bstep (se 1 (by rfl) ⟨693776, by rfl⟩ : syracuseStep 925035 = 1387553) B1387553
theorem B925047 : Blo 924580 925047 := bstep (se 1 (by rfl) ⟨693785, by rfl⟩ : syracuseStep 925047 = 1387571) B1387571
theorem B925067 : Blo 924580 925067 := bstep (se 1 (by rfl) ⟨693800, by rfl⟩ : syracuseStep 925067 = 1387601) B1387601
theorem B925079 : Blo 924580 925079 := bstep (se 1 (by rfl) ⟨693809, by rfl⟩ : syracuseStep 925079 = 1387619) B1387619
theorem B925099 : Blo 924580 925099 := bstep (se 1 (by rfl) ⟨693824, by rfl⟩ : syracuseStep 925099 = 1387649) B1387649
theorem B925111 : Blo 924580 925111 := bstep (se 1 (by rfl) ⟨693833, by rfl⟩ : syracuseStep 925111 = 1387667) B1387667
theorem B925131 : Blo 924580 925131 := bstep (se 1 (by rfl) ⟨693848, by rfl⟩ : syracuseStep 925131 = 1387697) B1387697
theorem B925143 : Blo 924580 925143 := bstep (se 1 (by rfl) ⟨693857, by rfl⟩ : syracuseStep 925143 = 1387715) B1387715
theorem B3120605 : Blo 924580 3120605 := bstep (se 3 (by rfl) ⟨585113, by rfl⟩ : syracuseStep 3120605 = 1170227) B1170227
theorem B925163 : Blo 924580 925163 := bstep (se 1 (by rfl) ⟨693872, by rfl⟩ : syracuseStep 925163 = 1387745) B1387745
theorem B925175 : Blo 924580 925175 := bstep (se 1 (by rfl) ⟨693881, by rfl⟩ : syracuseStep 925175 = 1387763) B1387763
theorem B925195 : Blo 924580 925195 := bstep (se 1 (by rfl) ⟨693896, by rfl⟩ : syracuseStep 925195 = 1387793) B1387793
theorem B925207 : Blo 924580 925207 := bstep (se 1 (by rfl) ⟨693905, by rfl⟩ : syracuseStep 925207 = 1387811) B1387811
theorem B925227 : Blo 924580 925227 := bstep (se 1 (by rfl) ⟨693920, by rfl⟩ : syracuseStep 925227 = 1387841) B1387841
theorem B3513901 : Blo 924580 3513901 := bstep (se 3 (by rfl) ⟨658856, by rfl⟩ : syracuseStep 3513901 = 1317713) B1317713
theorem B925239 : Blo 924580 925239 := bstep (se 1 (by rfl) ⟨693929, by rfl⟩ : syracuseStep 925239 = 1387859) B1387859
theorem B925259 : Blo 924580 925259 := bstep (se 1 (by rfl) ⟨693944, by rfl⟩ : syracuseStep 925259 = 1387889) B1387889
theorem B925271 : Blo 924580 925271 := bstep (se 1 (by rfl) ⟨693953, by rfl⟩ : syracuseStep 925271 = 1387907) B1387907
theorem B925291 : Blo 924580 925291 := bstep (se 1 (by rfl) ⟨693968, by rfl⟩ : syracuseStep 925291 = 1387937) B1387937
theorem B925303 : Blo 924580 925303 := bstep (se 1 (by rfl) ⟨693977, by rfl⟩ : syracuseStep 925303 = 1387955) B1387955
theorem B925323 : Blo 924580 925323 := bstep (se 1 (by rfl) ⟨693992, by rfl⟩ : syracuseStep 925323 = 1387985) B1387985
theorem B925335 : Blo 924580 925335 := bstep (se 1 (by rfl) ⟨694001, by rfl⟩ : syracuseStep 925335 = 1388003) B1388003
theorem B925355 : Blo 924580 925355 := bstep (se 1 (by rfl) ⟨694016, by rfl⟩ : syracuseStep 925355 = 1388033) B1388033
theorem B925367 : Blo 924580 925367 := bstep (se 1 (by rfl) ⟨694025, by rfl⟩ : syracuseStep 925367 = 1388051) B1388051
theorem B90054341 : Blo 924580 90054341 := bstep (se 4 (by rfl) ⟨8442594, by rfl⟩ : syracuseStep 90054341 = 16885189) B16885189
theorem B925387 : Blo 924580 925387 := bstep (se 1 (by rfl) ⟨694040, by rfl⟩ : syracuseStep 925387 = 1388081) B1388081
theorem B925399 : Blo 924580 925399 := bstep (se 1 (by rfl) ⟨694049, by rfl⟩ : syracuseStep 925399 = 1388099) B1388099
theorem B925419 : Blo 924580 925419 := bstep (se 1 (by rfl) ⟨694064, by rfl⟩ : syracuseStep 925419 = 1388129) B1388129
theorem B925431 : Blo 924580 925431 := bstep (se 1 (by rfl) ⟨694073, by rfl⟩ : syracuseStep 925431 = 1388147) B1388147
theorem B925451 : Blo 924580 925451 := bstep (se 1 (by rfl) ⟨694088, by rfl⟩ : syracuseStep 925451 = 1388177) B1388177
theorem B2006795 : Blo 924580 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B925463 : Blo 924580 925463 := bstep (se 1 (by rfl) ⟨694097, by rfl⟩ : syracuseStep 925463 = 1388195) B1388195
theorem B925483 : Blo 924580 925483 := bstep (se 1 (by rfl) ⟨694112, by rfl⟩ : syracuseStep 925483 = 1388225) B1388225
theorem B925495 : Blo 924580 925495 := bstep (se 1 (by rfl) ⟨694121, by rfl⟩ : syracuseStep 925495 = 1388243) B1388243
theorem B925515 : Blo 924580 925515 := bstep (se 1 (by rfl) ⟨694136, by rfl⟩ : syracuseStep 925515 = 1388273) B1388273
theorem B925527 : Blo 924580 925527 := bstep (se 1 (by rfl) ⟨694145, by rfl⟩ : syracuseStep 925527 = 1388291) B1388291
theorem B3514205 : Blo 924580 3514205 := bstep (se 3 (by rfl) ⟨658913, by rfl⟩ : syracuseStep 3514205 = 1317827) B1317827
theorem B925547 : Blo 924580 925547 := bstep (se 1 (by rfl) ⟨694160, by rfl⟩ : syracuseStep 925547 = 1388321) B1388321
theorem B925559 : Blo 924580 925559 := bstep (se 1 (by rfl) ⟨694169, by rfl⟩ : syracuseStep 925559 = 1388339) B1388339
theorem B925579 : Blo 924580 925579 := bstep (se 1 (by rfl) ⟨694184, by rfl⟩ : syracuseStep 925579 = 1388369) B1388369
theorem B925591 : Blo 924580 925591 := bstep (se 1 (by rfl) ⟨694193, by rfl⟩ : syracuseStep 925591 = 1388387) B1388387
theorem B925611 : Blo 924580 925611 := bstep (se 1 (by rfl) ⟨694208, by rfl⟩ : syracuseStep 925611 = 1388417) B1388417
theorem B925623 : Blo 924580 925623 := bstep (se 1 (by rfl) ⟨694217, by rfl⟩ : syracuseStep 925623 = 1388435) B1388435
theorem B925643 : Blo 924580 925643 := bstep (se 1 (by rfl) ⟨694232, by rfl⟩ : syracuseStep 925643 = 1388465) B1388465
theorem B6692813 : Blo 924580 6692813 := bstep (se 3 (by rfl) ⟨1254902, by rfl⟩ : syracuseStep 6692813 = 2509805) B2509805
theorem B925655 : Blo 924580 925655 := bstep (se 1 (by rfl) ⟨694241, by rfl⟩ : syracuseStep 925655 = 1388483) B1388483
theorem B925675 : Blo 924580 925675 := bstep (se 1 (by rfl) ⟨694256, by rfl⟩ : syracuseStep 925675 = 1388513) B1388513
theorem B925687 : Blo 924580 925687 := bstep (se 1 (by rfl) ⟨694265, by rfl⟩ : syracuseStep 925687 = 1388531) B1388531
theorem B925707 : Blo 924580 925707 := bstep (se 1 (by rfl) ⟨694280, by rfl⟩ : syracuseStep 925707 = 1388561) B1388561
theorem B925719 : Blo 924580 925719 := bstep (se 1 (by rfl) ⟨694289, by rfl⟩ : syracuseStep 925719 = 1388579) B1388579
theorem B925739 : Blo 924580 925739 := bstep (se 1 (by rfl) ⟨694304, by rfl⟩ : syracuseStep 925739 = 1388609) B1388609
theorem B925751 : Blo 924580 925751 := bstep (se 1 (by rfl) ⟨694313, by rfl⟩ : syracuseStep 925751 = 1388627) B1388627
theorem B4005953 : Blo 924580 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B925771 : Blo 924580 925771 := bstep (se 1 (by rfl) ⟨694328, by rfl⟩ : syracuseStep 925771 = 1388657) B1388657
theorem B925783 : Blo 924580 925783 := bstep (se 1 (by rfl) ⟨694337, by rfl⟩ : syracuseStep 925783 = 1388675) B1388675
theorem B8888413 : Blo 924580 8888413 := bstep (se 3 (by rfl) ⟨1666577, by rfl⟩ : syracuseStep 8888413 = 3333155) B3333155
theorem B925803 : Blo 924580 925803 := bstep (se 1 (by rfl) ⟨694352, by rfl⟩ : syracuseStep 925803 = 1388705) B1388705
theorem B925815 : Blo 924580 925815 := bstep (se 1 (by rfl) ⟨694361, by rfl⟩ : syracuseStep 925815 = 1388723) B1388723
theorem B925835 : Blo 924580 925835 := bstep (se 1 (by rfl) ⟨694376, by rfl⟩ : syracuseStep 925835 = 1388753) B1388753
theorem B925847 : Blo 924580 925847 := bstep (se 1 (by rfl) ⟨694385, by rfl⟩ : syracuseStep 925847 = 1388771) B1388771
theorem B925867 : Blo 924580 925867 := bstep (se 1 (by rfl) ⟨694400, by rfl⟩ : syracuseStep 925867 = 1388801) B1388801
theorem B925879 : Blo 924580 925879 := bstep (se 1 (by rfl) ⟨694409, by rfl⟩ : syracuseStep 925879 = 1388819) B1388819
theorem B925899 : Blo 924580 925899 := bstep (se 1 (by rfl) ⟨694424, by rfl⟩ : syracuseStep 925899 = 1388849) B1388849
theorem B925911 : Blo 924580 925911 := bstep (se 1 (by rfl) ⟨694433, by rfl⟩ : syracuseStep 925911 = 1388867) B1388867
theorem B2859229 : Blo 924580 2859229 := bstep (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) B1072211
theorem B925931 : Blo 924580 925931 := bstep (se 1 (by rfl) ⟨694448, by rfl⟩ : syracuseStep 925931 = 1388897) B1388897
theorem B925943 : Blo 924580 925943 := bstep (se 1 (by rfl) ⟨694457, by rfl⟩ : syracuseStep 925943 = 1388915) B1388915
theorem B925963 : Blo 924580 925963 := bstep (se 1 (by rfl) ⟨694472, by rfl⟩ : syracuseStep 925963 = 1388945) B1388945
theorem B925975 : Blo 924580 925975 := bstep (se 1 (by rfl) ⟨694481, by rfl⟩ : syracuseStep 925975 = 1388963) B1388963
theorem B925995 : Blo 924580 925995 := bstep (se 1 (by rfl) ⟨694496, by rfl⟩ : syracuseStep 925995 = 1388993) B1388993
theorem B33857837 : Blo 924580 33857837 := bstep (se 3 (by rfl) ⟨6348344, by rfl⟩ : syracuseStep 33857837 = 12696689) B12696689
theorem B926007 : Blo 924580 926007 := bstep (se 1 (by rfl) ⟨694505, by rfl⟩ : syracuseStep 926007 = 1389011) B1389011
theorem B926027 : Blo 924580 926027 := bstep (se 1 (by rfl) ⟨694520, by rfl⟩ : syracuseStep 926027 = 1389041) B1389041
theorem B926039 : Blo 924580 926039 := bstep (se 1 (by rfl) ⟨694529, by rfl⟩ : syracuseStep 926039 = 1389059) B1389059
theorem B1319257 : Blo 924580 1319257 := bstep (se 2 (by rfl) ⟨494721, by rfl⟩ : syracuseStep 1319257 = 989443) B989443
theorem B926059 : Blo 924580 926059 := bstep (se 1 (by rfl) ⟨694544, by rfl⟩ : syracuseStep 926059 = 1389089) B1389089
theorem B926071 : Blo 924580 926071 := bstep (se 1 (by rfl) ⟨694553, by rfl⟩ : syracuseStep 926071 = 1389107) B1389107
theorem B926091 : Blo 924580 926091 := bstep (se 1 (by rfl) ⟨694568, by rfl⟩ : syracuseStep 926091 = 1389137) B1389137
theorem B926103 : Blo 924580 926103 := bstep (se 1 (by rfl) ⟨694577, by rfl⟩ : syracuseStep 926103 = 1389155) B1389155
theorem B926123 : Blo 924580 926123 := bstep (se 1 (by rfl) ⟨694592, by rfl⟩ : syracuseStep 926123 = 1389185) B1389185
theorem B6693299 : Blo 924580 6693299 := bstep (se 1 (by rfl) ⟨5019974, by rfl⟩ : syracuseStep 6693299 = 10039949) B10039949
theorem B926135 : Blo 924580 926135 := bstep (se 1 (by rfl) ⟨694601, by rfl⟩ : syracuseStep 926135 = 1389203) B1389203
theorem B926155 : Blo 924580 926155 := bstep (se 1 (by rfl) ⟨694616, by rfl⟩ : syracuseStep 926155 = 1389233) B1389233
theorem B926167 : Blo 924580 926167 := bstep (se 1 (by rfl) ⟨694625, by rfl⟩ : syracuseStep 926167 = 1389251) B1389251
theorem B926187 : Blo 924580 926187 := bstep (se 1 (by rfl) ⟨694640, by rfl⟩ : syracuseStep 926187 = 1389281) B1389281
theorem B1057259 : Blo 924580 1057259 := bstep (se 1 (by rfl) ⟨792944, by rfl⟩ : syracuseStep 1057259 = 1585889) B1585889
theorem B926199 : Blo 924580 926199 := bstep (se 1 (by rfl) ⟨694649, by rfl⟩ : syracuseStep 926199 = 1389299) B1389299
theorem B926219 : Blo 924580 926219 := bstep (se 1 (by rfl) ⟨694664, by rfl⟩ : syracuseStep 926219 = 1389329) B1389329
theorem B13378061 : Blo 924580 13378061 := bstep (se 3 (by rfl) ⟨2508386, by rfl⟩ : syracuseStep 13378061 = 5016773) B5016773
theorem B926231 : Blo 924580 926231 := bstep (se 1 (by rfl) ⟨694673, by rfl⟩ : syracuseStep 926231 = 1389347) B1389347
theorem B926251 : Blo 924580 926251 := bstep (se 1 (by rfl) ⟨694688, by rfl⟩ : syracuseStep 926251 = 1389377) B1389377
theorem B926263 : Blo 924580 926263 := bstep (se 1 (by rfl) ⟨694697, by rfl⟩ : syracuseStep 926263 = 1389395) B1389395
theorem B3121739 : Blo 924580 3121739 := bstep (se 1 (by rfl) ⟨2341304, by rfl⟩ : syracuseStep 3121739 = 4682609) B4682609
theorem B926283 : Blo 924580 926283 := bstep (se 1 (by rfl) ⟨694712, by rfl⟩ : syracuseStep 926283 = 1389425) B1389425
theorem B1188427 : Blo 924580 1188427 := bstep (se 1 (by rfl) ⟨891320, by rfl⟩ : syracuseStep 1188427 = 1782641) B1782641
theorem B926295 : Blo 924580 926295 := bstep (se 1 (by rfl) ⟨694721, by rfl⟩ : syracuseStep 926295 = 1389443) B1389443
theorem B926315 : Blo 924580 926315 := bstep (se 1 (by rfl) ⟨694736, by rfl⟩ : syracuseStep 926315 = 1389473) B1389473
theorem B926327 : Blo 924580 926327 := bstep (se 1 (by rfl) ⟨694745, by rfl⟩ : syracuseStep 926327 = 1389491) B1389491
theorem B926347 : Blo 924580 926347 := bstep (se 1 (by rfl) ⟨694760, by rfl⟩ : syracuseStep 926347 = 1389521) B1389521
theorem B926359 : Blo 924580 926359 := bstep (se 1 (by rfl) ⟨694769, by rfl⟩ : syracuseStep 926359 = 1389539) B1389539
theorem B926379 : Blo 924580 926379 := bstep (se 1 (by rfl) ⟨694784, by rfl⟩ : syracuseStep 926379 = 1389569) B1389569
theorem B926391 : Blo 924580 926391 := bstep (se 1 (by rfl) ⟨694793, by rfl⟩ : syracuseStep 926391 = 1389587) B1389587
theorem B926411 : Blo 924580 926411 := bstep (se 1 (by rfl) ⟨694808, by rfl⟩ : syracuseStep 926411 = 1389617) B1389617
theorem B926423 : Blo 924580 926423 := bstep (se 1 (by rfl) ⟨694817, by rfl⟩ : syracuseStep 926423 = 1389635) B1389635
theorem B926443 : Blo 924580 926443 := bstep (se 1 (by rfl) ⟨694832, by rfl⟩ : syracuseStep 926443 = 1389665) B1389665
theorem B926455 : Blo 924580 926455 := bstep (se 1 (by rfl) ⟨694841, by rfl⟩ : syracuseStep 926455 = 1389683) B1389683
theorem B926475 : Blo 924580 926475 := bstep (se 1 (by rfl) ⟨694856, by rfl⟩ : syracuseStep 926475 = 1389713) B1389713
theorem B926487 : Blo 924580 926487 := bstep (se 1 (by rfl) ⟨694865, by rfl⟩ : syracuseStep 926487 = 1389731) B1389731
theorem B926507 : Blo 924580 926507 := bstep (se 1 (by rfl) ⟨694880, by rfl⟩ : syracuseStep 926507 = 1389761) B1389761
theorem B5940013 : Blo 924580 5940013 := bstep (se 3 (by rfl) ⟨1113752, by rfl⟩ : syracuseStep 5940013 = 2227505) B2227505
theorem B926519 : Blo 924580 926519 := bstep (se 1 (by rfl) ⟨694889, by rfl⟩ : syracuseStep 926519 = 1389779) B1389779
theorem B926539 : Blo 924580 926539 := bstep (se 1 (by rfl) ⟨694904, by rfl⟩ : syracuseStep 926539 = 1389809) B1389809
theorem B926551 : Blo 924580 926551 := bstep (se 1 (by rfl) ⟨694913, by rfl⟩ : syracuseStep 926551 = 1389827) B1389827
theorem B3122009 : Blo 924580 3122009 := bstep (se 2 (by rfl) ⟨1170753, by rfl⟩ : syracuseStep 3122009 = 2341507) B2341507
theorem B926571 : Blo 924580 926571 := bstep (se 1 (by rfl) ⟨694928, by rfl⟩ : syracuseStep 926571 = 1389857) B1389857
theorem B926583 : Blo 924580 926583 := bstep (se 1 (by rfl) ⟨694937, by rfl⟩ : syracuseStep 926583 = 1389875) B1389875
theorem B926603 : Blo 924580 926603 := bstep (se 1 (by rfl) ⟨694952, by rfl⟩ : syracuseStep 926603 = 1389905) B1389905
theorem B926615 : Blo 924580 926615 := bstep (se 1 (by rfl) ⟨694961, by rfl⟩ : syracuseStep 926615 = 1389923) B1389923
theorem B926635 : Blo 924580 926635 := bstep (se 1 (by rfl) ⟨694976, by rfl⟩ : syracuseStep 926635 = 1389953) B1389953
theorem B926647 : Blo 924580 926647 := bstep (se 1 (by rfl) ⟨694985, by rfl⟩ : syracuseStep 926647 = 1389971) B1389971
theorem B926667 : Blo 924580 926667 := bstep (se 1 (by rfl) ⟨695000, by rfl⟩ : syracuseStep 926667 = 1390001) B1390001
theorem B926679 : Blo 924580 926679 := bstep (se 1 (by rfl) ⟨695009, by rfl⟩ : syracuseStep 926679 = 1390019) B1390019
theorem B926699 : Blo 924580 926699 := bstep (se 1 (by rfl) ⟨695024, by rfl⟩ : syracuseStep 926699 = 1390049) B1390049
theorem B926711 : Blo 924580 926711 := bstep (se 1 (by rfl) ⟨695033, by rfl⟩ : syracuseStep 926711 = 1390067) B1390067
theorem B926731 : Blo 924580 926731 := bstep (se 1 (by rfl) ⟨695048, by rfl⟩ : syracuseStep 926731 = 1390097) B1390097
theorem B926743 : Blo 924580 926743 := bstep (se 1 (by rfl) ⟨695057, by rfl⟩ : syracuseStep 926743 = 1390115) B1390115
theorem B926763 : Blo 924580 926763 := bstep (se 1 (by rfl) ⟨695072, by rfl⟩ : syracuseStep 926763 = 1390145) B1390145
theorem B926775 : Blo 924580 926775 := bstep (se 1 (by rfl) ⟨695081, by rfl⟩ : syracuseStep 926775 = 1390163) B1390163
theorem B22848581 : Blo 924580 22848581 := bstep (se 4 (by rfl) ⟨2142054, by rfl⟩ : syracuseStep 22848581 = 4284109) B4284109
theorem B926795 : Blo 924580 926795 := bstep (se 1 (by rfl) ⟨695096, by rfl⟩ : syracuseStep 926795 = 1390193) B1390193
theorem B926807 : Blo 924580 926807 := bstep (se 1 (by rfl) ⟨695105, by rfl⟩ : syracuseStep 926807 = 1390211) B1390211
theorem B926827 : Blo 924580 926827 := bstep (se 1 (by rfl) ⟨695120, by rfl⟩ : syracuseStep 926827 = 1390241) B1390241
theorem B1877107 : Blo 924580 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B926839 : Blo 924580 926839 := bstep (se 1 (by rfl) ⟨695129, by rfl⟩ : syracuseStep 926839 = 1390259) B1390259
theorem B926859 : Blo 924580 926859 := bstep (se 1 (by rfl) ⟨695144, by rfl⟩ : syracuseStep 926859 = 1390289) B1390289
theorem B926871 : Blo 924580 926871 := bstep (se 1 (by rfl) ⟨695153, by rfl⟩ : syracuseStep 926871 = 1390307) B1390307
theorem B926891 : Blo 924580 926891 := bstep (se 1 (by rfl) ⟨695168, by rfl⟩ : syracuseStep 926891 = 1390337) B1390337
theorem B926903 : Blo 924580 926903 := bstep (se 1 (by rfl) ⟨695177, by rfl⟩ : syracuseStep 926903 = 1390355) B1390355
theorem B926923 : Blo 924580 926923 := bstep (se 1 (by rfl) ⟨695192, by rfl⟩ : syracuseStep 926923 = 1390385) B1390385
theorem B1975511 : Blo 924580 1975511 := bstep (se 1 (by rfl) ⟨1481633, by rfl⟩ : syracuseStep 1975511 = 2963267) B2963267
theorem B926935 : Blo 924580 926935 := bstep (se 1 (by rfl) ⟨695201, by rfl⟩ : syracuseStep 926935 = 1390403) B1390403
theorem B1320151 : Blo 924580 1320151 := bstep (se 1 (by rfl) ⟨990113, by rfl⟩ : syracuseStep 1320151 = 1980227) B1980227
theorem B926955 : Blo 924580 926955 := bstep (se 1 (by rfl) ⟨695216, by rfl⟩ : syracuseStep 926955 = 1390433) B1390433
theorem B926967 : Blo 924580 926967 := bstep (se 1 (by rfl) ⟨695225, by rfl⟩ : syracuseStep 926967 = 1390451) B1390451
theorem B926987 : Blo 924580 926987 := bstep (se 1 (by rfl) ⟨695240, by rfl⟩ : syracuseStep 926987 = 1390481) B1390481
theorem B926999 : Blo 924580 926999 := bstep (se 1 (by rfl) ⟨695249, by rfl⟩ : syracuseStep 926999 = 1390499) B1390499
theorem B927019 : Blo 924580 927019 := bstep (se 1 (by rfl) ⟨695264, by rfl⟩ : syracuseStep 927019 = 1390529) B1390529
theorem B927031 : Blo 924580 927031 := bstep (se 1 (by rfl) ⟨695273, by rfl⟩ : syracuseStep 927031 = 1390547) B1390547
theorem B927051 : Blo 924580 927051 := bstep (se 1 (by rfl) ⟨695288, by rfl⟩ : syracuseStep 927051 = 1390577) B1390577
theorem B1484119 : Blo 924580 1484119 := bstep (se 1 (by rfl) ⟨1113089, by rfl⟩ : syracuseStep 1484119 = 2226179) B2226179
theorem B1189207 : Blo 924580 1189207 := bstep (se 1 (by rfl) ⟨891905, by rfl⟩ : syracuseStep 1189207 = 1783811) B1783811
theorem B927063 : Blo 924580 927063 := bstep (se 1 (by rfl) ⟨695297, by rfl⟩ : syracuseStep 927063 = 1390595) B1390595
theorem B927083 : Blo 924580 927083 := bstep (se 1 (by rfl) ⟨695312, by rfl⟩ : syracuseStep 927083 = 1390625) B1390625
theorem B927095 : Blo 924580 927095 := bstep (se 1 (by rfl) ⟨695321, by rfl⟩ : syracuseStep 927095 = 1390643) B1390643
theorem B1975681 : Blo 924580 1975681 := bstep (se 2 (by rfl) ⟨740880, by rfl⟩ : syracuseStep 1975681 = 1481761) B1481761
theorem B927115 : Blo 924580 927115 := bstep (se 1 (by rfl) ⟨695336, by rfl⟩ : syracuseStep 927115 = 1390673) B1390673
theorem B927127 : Blo 924580 927127 := bstep (se 1 (by rfl) ⟨695345, by rfl⟩ : syracuseStep 927127 = 1390691) B1390691
theorem B927147 : Blo 924580 927147 := bstep (se 1 (by rfl) ⟨695360, by rfl⟩ : syracuseStep 927147 = 1390721) B1390721
theorem B927159 : Blo 924580 927159 := bstep (se 1 (by rfl) ⟨695369, by rfl⟩ : syracuseStep 927159 = 1390739) B1390739
theorem B927179 : Blo 924580 927179 := bstep (se 1 (by rfl) ⟨695384, by rfl⟩ : syracuseStep 927179 = 1390769) B1390769
theorem B927191 : Blo 924580 927191 := bstep (se 1 (by rfl) ⟨695393, by rfl⟩ : syracuseStep 927191 = 1390787) B1390787
theorem B927211 : Blo 924580 927211 := bstep (se 1 (by rfl) ⟨695408, by rfl⟩ : syracuseStep 927211 = 1390817) B1390817
theorem B927223 : Blo 924580 927223 := bstep (se 1 (by rfl) ⟨695417, by rfl⟩ : syracuseStep 927223 = 1390835) B1390835
theorem B927243 : Blo 924580 927243 := bstep (se 1 (by rfl) ⟨695432, by rfl⟩ : syracuseStep 927243 = 1390865) B1390865
theorem B4695569 : Blo 924580 4695569 := bstep (se 2 (by rfl) ⟨1760838, by rfl⟩ : syracuseStep 4695569 = 3521677) B3521677
theorem B3122711 : Blo 924580 3122711 := bstep (se 1 (by rfl) ⟨2342033, by rfl⟩ : syracuseStep 3122711 = 4684067) B4684067
theorem B927255 : Blo 924580 927255 := bstep (se 1 (by rfl) ⟨695441, by rfl⟩ : syracuseStep 927255 = 1390883) B1390883
theorem B927275 : Blo 924580 927275 := bstep (se 1 (by rfl) ⟨695456, by rfl⟩ : syracuseStep 927275 = 1390913) B1390913
theorem B927287 : Blo 924580 927287 := bstep (se 1 (by rfl) ⟨695465, by rfl⟩ : syracuseStep 927287 = 1390931) B1390931
theorem B927307 : Blo 924580 927307 := bstep (se 1 (by rfl) ⟨695480, by rfl⟩ : syracuseStep 927307 = 1390961) B1390961
theorem B927319 : Blo 924580 927319 := bstep (se 1 (by rfl) ⟨695489, by rfl⟩ : syracuseStep 927319 = 1390979) B1390979
theorem B927339 : Blo 924580 927339 := bstep (se 1 (by rfl) ⟨695504, by rfl⟩ : syracuseStep 927339 = 1391009) B1391009
theorem B927351 : Blo 924580 927351 := bstep (se 1 (by rfl) ⟨695513, by rfl⟩ : syracuseStep 927351 = 1391027) B1391027
theorem B927371 : Blo 924580 927371 := bstep (se 1 (by rfl) ⟨695528, by rfl⟩ : syracuseStep 927371 = 1391057) B1391057
theorem B927383 : Blo 924580 927383 := bstep (se 1 (by rfl) ⟨695537, by rfl⟩ : syracuseStep 927383 = 1391075) B1391075
theorem B927403 : Blo 924580 927403 := bstep (se 1 (by rfl) ⟨695552, by rfl⟩ : syracuseStep 927403 = 1391105) B1391105
theorem B4695731 : Blo 924580 4695731 := bstep (se 1 (by rfl) ⟨3521798, by rfl⟩ : syracuseStep 4695731 = 7043597) B7043597
theorem B927415 : Blo 924580 927415 := bstep (se 1 (by rfl) ⟨695561, by rfl⟩ : syracuseStep 927415 = 1391123) B1391123
theorem B927435 : Blo 924580 927435 := bstep (se 1 (by rfl) ⟨695576, by rfl⟩ : syracuseStep 927435 = 1391153) B1391153
theorem B1976023 : Blo 924580 1976023 := bstep (se 1 (by rfl) ⟨1482017, by rfl⟩ : syracuseStep 1976023 = 2964035) B2964035
theorem B927447 : Blo 924580 927447 := bstep (se 1 (by rfl) ⟨695585, by rfl⟩ : syracuseStep 927447 = 1391171) B1391171
theorem B927467 : Blo 924580 927467 := bstep (se 1 (by rfl) ⟨695600, by rfl⟩ : syracuseStep 927467 = 1391201) B1391201
theorem B927479 : Blo 924580 927479 := bstep (se 1 (by rfl) ⟨695609, by rfl⟩ : syracuseStep 927479 = 1391219) B1391219
theorem B927499 : Blo 924580 927499 := bstep (se 1 (by rfl) ⟨695624, by rfl⟩ : syracuseStep 927499 = 1391249) B1391249
theorem B1320715 : Blo 924580 1320715 := bstep (se 1 (by rfl) ⟨990536, by rfl⟩ : syracuseStep 1320715 = 1981073) B1981073
theorem B927511 : Blo 924580 927511 := bstep (se 1 (by rfl) ⟨695633, by rfl⟩ : syracuseStep 927511 = 1391267) B1391267
theorem B927531 : Blo 924580 927531 := bstep (se 1 (by rfl) ⟨695648, by rfl⟩ : syracuseStep 927531 = 1391297) B1391297
theorem B927543 : Blo 924580 927543 := bstep (se 1 (by rfl) ⟨695657, by rfl⟩ : syracuseStep 927543 = 1391315) B1391315
theorem B927563 : Blo 924580 927563 := bstep (se 1 (by rfl) ⟨695672, by rfl⟩ : syracuseStep 927563 = 1391345) B1391345
theorem B927575 : Blo 924580 927575 := bstep (se 1 (by rfl) ⟨695681, by rfl⟩ : syracuseStep 927575 = 1391363) B1391363
theorem B17835875 : Blo 924580 17835875 := bstep (se 1 (by rfl) ⟨13376906, by rfl⟩ : syracuseStep 17835875 = 26753813) B26753813
theorem B927595 : Blo 924580 927595 := bstep (se 1 (by rfl) ⟨695696, by rfl⟩ : syracuseStep 927595 = 1391393) B1391393
theorem B927607 : Blo 924580 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B927627 : Blo 924580 927627 := bstep (se 1 (by rfl) ⟨695720, by rfl⟩ : syracuseStep 927627 = 1391441) B1391441
theorem B927639 : Blo 924580 927639 := bstep (se 1 (by rfl) ⟨695729, by rfl⟩ : syracuseStep 927639 = 1391459) B1391459
theorem B927659 : Blo 924580 927659 := bstep (se 1 (by rfl) ⟨695744, by rfl⟩ : syracuseStep 927659 = 1391489) B1391489
theorem B927671 : Blo 924580 927671 := bstep (se 1 (by rfl) ⟨695753, by rfl⟩ : syracuseStep 927671 = 1391507) B1391507
theorem B927691 : Blo 924580 927691 := bstep (se 1 (by rfl) ⟨695768, by rfl⟩ : syracuseStep 927691 = 1391537) B1391537
theorem B927703 : Blo 924580 927703 := bstep (se 1 (by rfl) ⟨695777, by rfl⟩ : syracuseStep 927703 = 1391555) B1391555
theorem B927723 : Blo 924580 927723 := bstep (se 1 (by rfl) ⟨695792, by rfl⟩ : syracuseStep 927723 = 1391585) B1391585
theorem B927735 : Blo 924580 927735 := bstep (se 1 (by rfl) ⟨695801, by rfl⟩ : syracuseStep 927735 = 1391603) B1391603
theorem B927755 : Blo 924580 927755 := bstep (se 1 (by rfl) ⟨695816, by rfl⟩ : syracuseStep 927755 = 1391633) B1391633
theorem B927767 : Blo 924580 927767 := bstep (se 1 (by rfl) ⟨695825, by rfl⟩ : syracuseStep 927767 = 1391651) B1391651
theorem B927787 : Blo 924580 927787 := bstep (se 1 (by rfl) ⟨695840, by rfl⟩ : syracuseStep 927787 = 1391681) B1391681
theorem B3123251 : Blo 924580 3123251 := bstep (se 1 (by rfl) ⟨2342438, by rfl⟩ : syracuseStep 3123251 = 4684877) B4684877
theorem B927799 : Blo 924580 927799 := bstep (se 1 (by rfl) ⟨695849, by rfl⟩ : syracuseStep 927799 = 1391699) B1391699
theorem B927819 : Blo 924580 927819 := bstep (se 1 (by rfl) ⟨695864, by rfl⟩ : syracuseStep 927819 = 1391729) B1391729
theorem B927831 : Blo 924580 927831 := bstep (se 1 (by rfl) ⟨695873, by rfl⟩ : syracuseStep 927831 = 1391747) B1391747
theorem B927851 : Blo 924580 927851 := bstep (se 1 (by rfl) ⟨695888, by rfl⟩ : syracuseStep 927851 = 1391777) B1391777
theorem B927863 : Blo 924580 927863 := bstep (se 1 (by rfl) ⟨695897, by rfl⟩ : syracuseStep 927863 = 1391795) B1391795
theorem B1484939 : Blo 924580 1484939 := bstep (se 1 (by rfl) ⟨1113704, by rfl⟩ : syracuseStep 1484939 = 2227409) B2227409
theorem B927883 : Blo 924580 927883 := bstep (se 1 (by rfl) ⟨695912, by rfl⟩ : syracuseStep 927883 = 1391825) B1391825
theorem B927895 : Blo 924580 927895 := bstep (se 1 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 927895 = 1391843) B1391843
theorem B927915 : Blo 924580 927915 := bstep (se 1 (by rfl) ⟨695936, by rfl⟩ : syracuseStep 927915 = 1391873) B1391873
theorem B927927 : Blo 924580 927927 := bstep (se 1 (by rfl) ⟨695945, by rfl⟩ : syracuseStep 927927 = 1391891) B1391891
theorem B927947 : Blo 924580 927947 := bstep (se 1 (by rfl) ⟨695960, by rfl⟩ : syracuseStep 927947 = 1391921) B1391921
theorem B927959 : Blo 924580 927959 := bstep (se 1 (by rfl) ⟨695969, by rfl⟩ : syracuseStep 927959 = 1391939) B1391939
theorem B927979 : Blo 924580 927979 := bstep (se 1 (by rfl) ⟨695984, by rfl⟩ : syracuseStep 927979 = 1391969) B1391969
theorem B16918769 : Blo 924580 16918769 := bstep (se 2 (by rfl) ⟨6344538, by rfl⟩ : syracuseStep 16918769 = 12689077) B12689077
theorem B927991 : Blo 924580 927991 := bstep (se 1 (by rfl) ⟨695993, by rfl⟩ : syracuseStep 927991 = 1391987) B1391987
theorem B928011 : Blo 924580 928011 := bstep (se 1 (by rfl) ⟨696008, by rfl⟩ : syracuseStep 928011 = 1392017) B1392017
theorem B5286161 : Blo 924580 5286161 := bstep (se 2 (by rfl) ⟨1982310, by rfl⟩ : syracuseStep 5286161 = 3964621) B3964621
theorem B928023 : Blo 924580 928023 := bstep (se 1 (by rfl) ⟨696017, by rfl⟩ : syracuseStep 928023 = 1392035) B1392035
theorem B928043 : Blo 924580 928043 := bstep (se 1 (by rfl) ⟨696032, by rfl⟩ : syracuseStep 928043 = 1392065) B1392065
theorem B928055 : Blo 924580 928055 := bstep (se 1 (by rfl) ⟨696041, by rfl⟩ : syracuseStep 928055 = 1392083) B1392083
theorem B3123521 : Blo 924580 3123521 := bstep (se 2 (by rfl) ⟨1171320, by rfl⟩ : syracuseStep 3123521 = 2342641) B2342641
theorem B928075 : Blo 924580 928075 := bstep (se 1 (by rfl) ⟨696056, by rfl⟩ : syracuseStep 928075 = 1392113) B1392113
theorem B928087 : Blo 924580 928087 := bstep (se 1 (by rfl) ⟨696065, by rfl⟩ : syracuseStep 928087 = 1392131) B1392131
theorem B928107 : Blo 924580 928107 := bstep (se 1 (by rfl) ⟨696080, by rfl⟩ : syracuseStep 928107 = 1392161) B1392161
theorem B928119 : Blo 924580 928119 := bstep (se 1 (by rfl) ⟨696089, by rfl⟩ : syracuseStep 928119 = 1392179) B1392179
theorem B3516803 : Blo 924580 3516803 := bstep (se 1 (by rfl) ⟨2637602, by rfl⟩ : syracuseStep 3516803 = 5275205) B5275205
theorem B928139 : Blo 924580 928139 := bstep (se 1 (by rfl) ⟨696104, by rfl⟩ : syracuseStep 928139 = 1392209) B1392209
theorem B3516817 : Blo 924580 3516817 := bstep (se 2 (by rfl) ⟨1318806, by rfl⟩ : syracuseStep 3516817 = 2637613) B2637613
theorem B928151 : Blo 924580 928151 := bstep (se 1 (by rfl) ⟨696113, by rfl⟩ : syracuseStep 928151 = 1392227) B1392227
theorem B1386905 : Blo 924580 1386905 := bstep (se 2 (by rfl) ⟨520089, by rfl⟩ : syracuseStep 1386905 = 1040179) B1040179
theorem B1485209 : Blo 924580 1485209 := bstep (se 2 (by rfl) ⟨556953, by rfl⟩ : syracuseStep 1485209 = 1113907) B1113907
theorem B928171 : Blo 924580 928171 := bstep (se 1 (by rfl) ⟨696128, by rfl⟩ : syracuseStep 928171 = 1392257) B1392257
theorem B928183 : Blo 924580 928183 := bstep (se 1 (by rfl) ⟨696137, by rfl⟩ : syracuseStep 928183 = 1392275) B1392275
theorem B928203 : Blo 924580 928203 := bstep (se 1 (by rfl) ⟨696152, by rfl⟩ : syracuseStep 928203 = 1392305) B1392305
theorem B928215 : Blo 924580 928215 := bstep (se 1 (by rfl) ⟨696161, by rfl⟩ : syracuseStep 928215 = 1392323) B1392323
theorem B928235 : Blo 924580 928235 := bstep (se 1 (by rfl) ⟨696176, by rfl⟩ : syracuseStep 928235 = 1392353) B1392353
theorem B928247 : Blo 924580 928247 := bstep (se 1 (by rfl) ⟨696185, by rfl⟩ : syracuseStep 928247 = 1392371) B1392371
theorem B1387019 : Blo 924580 1387019 := bstep (se 1 (by rfl) ⟨1040264, by rfl⟩ : syracuseStep 1387019 = 2080529) B2080529
theorem B1976843 : Blo 924580 1976843 := bstep (se 1 (by rfl) ⟨1482632, by rfl⟩ : syracuseStep 1976843 = 2965265) B2965265
theorem B928267 : Blo 924580 928267 := bstep (se 1 (by rfl) ⟨696200, by rfl⟩ : syracuseStep 928267 = 1392401) B1392401
theorem B1387031 : Blo 924580 1387031 := bstep (se 1 (by rfl) ⟨1040273, by rfl⟩ : syracuseStep 1387031 = 2080547) B2080547
theorem B928279 : Blo 924580 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B928299 : Blo 924580 928299 := bstep (se 1 (by rfl) ⟨696224, by rfl⟩ : syracuseStep 928299 = 1392449) B1392449
theorem B928311 : Blo 924580 928311 := bstep (se 1 (by rfl) ⟨696233, by rfl⟩ : syracuseStep 928311 = 1392467) B1392467
theorem B928331 : Blo 924580 928331 := bstep (se 1 (by rfl) ⟨696248, by rfl⟩ : syracuseStep 928331 = 1392497) B1392497
theorem B928343 : Blo 924580 928343 := bstep (se 1 (by rfl) ⟨696257, by rfl⟩ : syracuseStep 928343 = 1392515) B1392515
theorem B1387097 : Blo 924580 1387097 := bstep (se 2 (by rfl) ⟨520161, by rfl⟩ : syracuseStep 1387097 = 1040323) B1040323
theorem B928363 : Blo 924580 928363 := bstep (se 1 (by rfl) ⟨696272, by rfl⟩ : syracuseStep 928363 = 1392545) B1392545
theorem B928375 : Blo 924580 928375 := bstep (se 1 (by rfl) ⟨696281, by rfl⟩ : syracuseStep 928375 = 1392563) B1392563
theorem B928395 : Blo 924580 928395 := bstep (se 1 (by rfl) ⟨696296, by rfl⟩ : syracuseStep 928395 = 1392593) B1392593
theorem B928407 : Blo 924580 928407 := bstep (se 1 (by rfl) ⟨696305, by rfl⟩ : syracuseStep 928407 = 1392611) B1392611
theorem B928427 : Blo 924580 928427 := bstep (se 1 (by rfl) ⟨696320, by rfl⟩ : syracuseStep 928427 = 1392641) B1392641
theorem B928439 : Blo 924580 928439 := bstep (se 1 (by rfl) ⟨696329, by rfl⟩ : syracuseStep 928439 = 1392659) B1392659
theorem B3517121 : Blo 924580 3517121 := bstep (se 2 (by rfl) ⟨1318920, by rfl⟩ : syracuseStep 3517121 = 2637841) B2637841
theorem B1387211 : Blo 924580 1387211 := bstep (se 1 (by rfl) ⟨1040408, by rfl⟩ : syracuseStep 1387211 = 2080817) B2080817
theorem B928459 : Blo 924580 928459 := bstep (se 1 (by rfl) ⟨696344, by rfl⟩ : syracuseStep 928459 = 1392689) B1392689
theorem B1387223 : Blo 924580 1387223 := bstep (se 1 (by rfl) ⟨1040417, by rfl⟩ : syracuseStep 1387223 = 2080835) B2080835
theorem B928471 : Blo 924580 928471 := bstep (se 1 (by rfl) ⟨696353, by rfl⟩ : syracuseStep 928471 = 1392707) B1392707
theorem B5286617 : Blo 924580 5286617 := bstep (se 2 (by rfl) ⟨1982481, by rfl⟩ : syracuseStep 5286617 = 3964963) B3964963
theorem B928491 : Blo 924580 928491 := bstep (se 1 (by rfl) ⟨696368, by rfl⟩ : syracuseStep 928491 = 1392737) B1392737
theorem B928503 : Blo 924580 928503 := bstep (se 1 (by rfl) ⟨696377, by rfl⟩ : syracuseStep 928503 = 1392755) B1392755
theorem B928523 : Blo 924580 928523 := bstep (se 1 (by rfl) ⟨696392, by rfl⟩ : syracuseStep 928523 = 1392785) B1392785
theorem B928535 : Blo 924580 928535 := bstep (se 1 (by rfl) ⟨696401, by rfl⟩ : syracuseStep 928535 = 1392803) B1392803
theorem B1387289 : Blo 924580 1387289 := bstep (se 2 (by rfl) ⟨520233, by rfl⟩ : syracuseStep 1387289 = 1040467) B1040467
theorem B928555 : Blo 924580 928555 := bstep (se 1 (by rfl) ⟨696416, by rfl⟩ : syracuseStep 928555 = 1392833) B1392833
theorem B928567 : Blo 924580 928567 := bstep (se 1 (by rfl) ⟨696425, by rfl⟩ : syracuseStep 928567 = 1392851) B1392851
theorem B3124061 : Blo 924580 3124061 := bstep (se 3 (by rfl) ⟨585761, by rfl⟩ : syracuseStep 3124061 = 1171523) B1171523
theorem B1977203 : Blo 924580 1977203 := bstep (se 1 (by rfl) ⟨1482902, by rfl⟩ : syracuseStep 1977203 = 2965805) B2965805
theorem B1387403 : Blo 924580 1387403 := bstep (se 1 (by rfl) ⟨1040552, by rfl⟩ : syracuseStep 1387403 = 2081105) B2081105
theorem B1387415 : Blo 924580 1387415 := bstep (se 1 (by rfl) ⟨1040561, by rfl⟩ : syracuseStep 1387415 = 2081123) B2081123
theorem B1387481 : Blo 924580 1387481 := bstep (se 2 (by rfl) ⟨520305, by rfl⟩ : syracuseStep 1387481 = 1040611) B1040611
theorem B1387595 : Blo 924580 1387595 := bstep (se 1 (by rfl) ⟨1040696, by rfl⟩ : syracuseStep 1387595 = 2081393) B2081393
theorem B1387607 : Blo 924580 1387607 := bstep (se 1 (by rfl) ⟨1040705, by rfl⟩ : syracuseStep 1387607 = 2081411) B2081411
theorem B1485913 : Blo 924580 1485913 := bstep (se 2 (by rfl) ⟨557217, by rfl⟩ : syracuseStep 1485913 = 1114435) B1114435
theorem B1387673 : Blo 924580 1387673 := bstep (se 2 (by rfl) ⟨520377, by rfl⟩ : syracuseStep 1387673 = 1040755) B1040755
theorem B1780915 : Blo 924580 1780915 := bstep (se 1 (by rfl) ⟨1335686, by rfl⟩ : syracuseStep 1780915 = 2671373) B2671373
theorem B1387787 : Blo 924580 1387787 := bstep (se 1 (by rfl) ⟨1040840, by rfl⟩ : syracuseStep 1387787 = 2081681) B2081681
theorem B1387799 : Blo 924580 1387799 := bstep (se 1 (by rfl) ⟨1040849, by rfl⟩ : syracuseStep 1387799 = 2081699) B2081699
theorem B1387865 : Blo 924580 1387865 := bstep (se 2 (by rfl) ⟨520449, by rfl⟩ : syracuseStep 1387865 = 1040899) B1040899
theorem B3517789 : Blo 924580 3517789 := bstep (se 3 (by rfl) ⟨659585, by rfl⟩ : syracuseStep 3517789 = 1319171) B1319171
theorem B1387979 : Blo 924580 1387979 := bstep (se 1 (by rfl) ⟨1040984, by rfl⟩ : syracuseStep 1387979 = 2081969) B2081969
theorem B1387991 : Blo 924580 1387991 := bstep (se 1 (by rfl) ⟨1040993, by rfl⟩ : syracuseStep 1387991 = 2081987) B2081987
theorem B2633239 : Blo 924580 2633239 := bstep (se 1 (by rfl) ⟨1974929, by rfl⟩ : syracuseStep 2633239 = 3949859) B3949859
theorem B1388057 : Blo 924580 1388057 := bstep (se 2 (by rfl) ⟨520521, by rfl⟩ : syracuseStep 1388057 = 1041043) B1041043
theorem B4697675 : Blo 924580 4697675 := bstep (se 1 (by rfl) ⟨3523256, by rfl⟩ : syracuseStep 4697675 = 7046513) B7046513
theorem B1388171 : Blo 924580 1388171 := bstep (se 1 (by rfl) ⟨1041128, by rfl⟩ : syracuseStep 1388171 = 2082257) B2082257
theorem B1388183 : Blo 924580 1388183 := bstep (se 1 (by rfl) ⟨1041137, by rfl⟩ : syracuseStep 1388183 = 2082275) B2082275
theorem B1388249 : Blo 924580 1388249 := bstep (se 2 (by rfl) ⟨520593, by rfl⟩ : syracuseStep 1388249 = 1041187) B1041187
theorem B1388363 : Blo 924580 1388363 := bstep (se 1 (by rfl) ⟨1041272, by rfl⟩ : syracuseStep 1388363 = 2082545) B2082545
theorem B1388375 : Blo 924580 1388375 := bstep (se 1 (by rfl) ⟨1041281, by rfl⟩ : syracuseStep 1388375 = 2082563) B2082563
theorem B1388441 : Blo 924580 1388441 := bstep (se 2 (by rfl) ⟨520665, by rfl⟩ : syracuseStep 1388441 = 1041331) B1041331
theorem B3125195 : Blo 924580 3125195 := bstep (se 1 (by rfl) ⟨2343896, by rfl⟩ : syracuseStep 3125195 = 4687793) B4687793
theorem B1388555 : Blo 924580 1388555 := bstep (se 1 (by rfl) ⟨1041416, by rfl⟩ : syracuseStep 1388555 = 2082833) B2082833
theorem B1388567 : Blo 924580 1388567 := bstep (se 1 (by rfl) ⟨1041425, by rfl⟩ : syracuseStep 1388567 = 2082851) B2082851
theorem B1388633 : Blo 924580 1388633 := bstep (se 2 (by rfl) ⟨520737, by rfl⟩ : syracuseStep 1388633 = 1041475) B1041475
theorem B1388747 : Blo 924580 1388747 := bstep (se 1 (by rfl) ⟨1041560, by rfl⟩ : syracuseStep 1388747 = 2083121) B2083121
theorem B1388759 : Blo 924580 1388759 := bstep (se 1 (by rfl) ⟨1041569, by rfl⟩ : syracuseStep 1388759 = 2083139) B2083139
theorem B3125465 : Blo 924580 3125465 := bstep (se 2 (by rfl) ⟨1172049, by rfl⟩ : syracuseStep 3125465 = 2344099) B2344099
theorem B10170629 : Blo 924580 10170629 := bstep (se 4 (by rfl) ⟨953496, by rfl⟩ : syracuseStep 10170629 = 1906993) B1906993
theorem B1388825 : Blo 924580 1388825 := bstep (se 2 (by rfl) ⟨520809, by rfl⟩ : syracuseStep 1388825 = 1041619) B1041619
theorem B2634059 : Blo 924580 2634059 := bstep (se 1 (by rfl) ⟨1975544, by rfl⟩ : syracuseStep 2634059 = 3951089) B3951089
theorem B1388939 : Blo 924580 1388939 := bstep (se 1 (by rfl) ⟨1041704, by rfl⟩ : syracuseStep 1388939 = 2083409) B2083409
theorem B1388951 : Blo 924580 1388951 := bstep (se 1 (by rfl) ⟨1041713, by rfl⟩ : syracuseStep 1388951 = 2083427) B2083427
theorem B1880513 : Blo 924580 1880513 := bstep (se 2 (by rfl) ⟨705192, by rfl⟩ : syracuseStep 1880513 = 1410385) B1410385
theorem B1389017 : Blo 924580 1389017 := bstep (se 2 (by rfl) ⟨520881, by rfl⟩ : syracuseStep 1389017 = 1041763) B1041763
theorem B64139789 : Blo 924580 64139789 := bstep (se 3 (by rfl) ⟨12026210, by rfl⟩ : syracuseStep 64139789 = 24052421) B24052421
theorem B1389131 : Blo 924580 1389131 := bstep (se 1 (by rfl) ⟨1041848, by rfl⟩ : syracuseStep 1389131 = 2083697) B2083697
theorem B1389143 : Blo 924580 1389143 := bstep (se 1 (by rfl) ⟨1041857, by rfl⟩ : syracuseStep 1389143 = 2083715) B2083715
theorem B3519065 : Blo 924580 3519065 := bstep (se 2 (by rfl) ⟨1319649, by rfl⟩ : syracuseStep 3519065 = 2639299) B2639299
theorem B1389209 : Blo 924580 1389209 := bstep (se 2 (by rfl) ⟨520953, by rfl⟩ : syracuseStep 1389209 = 1041907) B1041907
theorem B1389323 : Blo 924580 1389323 := bstep (se 1 (by rfl) ⟨1041992, by rfl⟩ : syracuseStep 1389323 = 2083985) B2083985
theorem B1389335 : Blo 924580 1389335 := bstep (se 1 (by rfl) ⟨1042001, by rfl⟩ : syracuseStep 1389335 = 2084003) B2084003
theorem B2962241 : Blo 924580 2962241 := bstep (se 2 (by rfl) ⟨1110840, by rfl⟩ : syracuseStep 2962241 = 2221681) B2221681
theorem B1979201 : Blo 924580 1979201 := bstep (se 2 (by rfl) ⟨742200, by rfl⟩ : syracuseStep 1979201 = 1484401) B1484401
theorem B1389401 : Blo 924580 1389401 := bstep (se 2 (by rfl) ⟨521025, by rfl⟩ : syracuseStep 1389401 = 1042051) B1042051
theorem B2536343 : Blo 924580 2536343 := bstep (se 1 (by rfl) ⟨1902257, by rfl⟩ : syracuseStep 2536343 = 3804515) B3804515
theorem B3126167 : Blo 924580 3126167 := bstep (se 1 (by rfl) ⟨2344625, by rfl⟩ : syracuseStep 3126167 = 4689251) B4689251
theorem B1389515 : Blo 924580 1389515 := bstep (se 1 (by rfl) ⟨1042136, by rfl⟩ : syracuseStep 1389515 = 2084273) B2084273
theorem B1389527 : Blo 924580 1389527 := bstep (se 1 (by rfl) ⟨1042145, by rfl⟩ : syracuseStep 1389527 = 2084291) B2084291
theorem B1389593 : Blo 924580 1389593 := bstep (se 2 (by rfl) ⟨521097, by rfl⟩ : syracuseStep 1389593 = 1042195) B1042195
theorem B1717337 : Blo 924580 1717337 := bstep (se 2 (by rfl) ⟨644001, by rfl⟩ : syracuseStep 1717337 = 1288003) B1288003
theorem B1389707 : Blo 924580 1389707 := bstep (se 1 (by rfl) ⟨1042280, by rfl⟩ : syracuseStep 1389707 = 2084561) B2084561
theorem B1881227 : Blo 924580 1881227 := bstep (se 1 (by rfl) ⟨1410920, by rfl⟩ : syracuseStep 1881227 = 2821841) B2821841
theorem B1389719 : Blo 924580 1389719 := bstep (se 1 (by rfl) ⟨1042289, by rfl⟩ : syracuseStep 1389719 = 2084579) B2084579
theorem B1389785 : Blo 924580 1389785 := bstep (se 2 (by rfl) ⟨521169, by rfl⟩ : syracuseStep 1389785 = 1042339) B1042339
theorem B4699457 : Blo 924580 4699457 := bstep (se 2 (by rfl) ⟨1762296, by rfl⟩ : syracuseStep 4699457 = 3524593) B3524593
theorem B1389899 : Blo 924580 1389899 := bstep (se 1 (by rfl) ⟨1042424, by rfl⟩ : syracuseStep 1389899 = 2084849) B2084849
theorem B1389911 : Blo 924580 1389911 := bstep (se 1 (by rfl) ⟨1042433, by rfl⟩ : syracuseStep 1389911 = 2084867) B2084867
theorem B1389977 : Blo 924580 1389977 := bstep (se 2 (by rfl) ⟨521241, by rfl⟩ : syracuseStep 1389977 = 1042483) B1042483
theorem B3126707 : Blo 924580 3126707 := bstep (se 1 (by rfl) ⟨2345030, by rfl⟩ : syracuseStep 3126707 = 4690061) B4690061
theorem B1390091 : Blo 924580 1390091 := bstep (se 1 (by rfl) ⟨1042568, by rfl⟩ : syracuseStep 1390091 = 2085137) B2085137
theorem B1390103 : Blo 924580 1390103 := bstep (se 1 (by rfl) ⟨1042577, by rfl⟩ : syracuseStep 1390103 = 2085155) B2085155
theorem B1390169 : Blo 924580 1390169 := bstep (se 2 (by rfl) ⟨521313, by rfl⟩ : syracuseStep 1390169 = 1042627) B1042627
theorem B1980055 : Blo 924580 1980055 := bstep (se 1 (by rfl) ⟨1485041, by rfl⟩ : syracuseStep 1980055 = 2970083) B2970083
theorem B3126977 : Blo 924580 3126977 := bstep (se 2 (by rfl) ⟨1172616, by rfl⟩ : syracuseStep 3126977 = 2345233) B2345233
theorem B1390283 : Blo 924580 1390283 := bstep (se 1 (by rfl) ⟨1042712, by rfl⟩ : syracuseStep 1390283 = 2085425) B2085425
theorem B1390295 : Blo 924580 1390295 := bstep (se 1 (by rfl) ⟨1042721, by rfl⟩ : syracuseStep 1390295 = 2085443) B2085443
theorem B1390361 : Blo 924580 1390361 := bstep (se 2 (by rfl) ⟨521385, by rfl⟩ : syracuseStep 1390361 = 1042771) B1042771
theorem B2340697 : Blo 924580 2340697 := bstep (se 2 (by rfl) ⟨877761, by rfl⟩ : syracuseStep 2340697 = 1755523) B1755523
theorem B7911269 : Blo 924580 7911269 := bstep (se 4 (by rfl) ⟨741681, by rfl⟩ : syracuseStep 7911269 = 1483363) B1483363
theorem B1390475 : Blo 924580 1390475 := bstep (se 1 (by rfl) ⟨1042856, by rfl⟩ : syracuseStep 1390475 = 2085713) B2085713
theorem B1390487 : Blo 924580 1390487 := bstep (se 1 (by rfl) ⟨1042865, by rfl⟩ : syracuseStep 1390487 = 2085731) B2085731
theorem B1390553 : Blo 924580 1390553 := bstep (se 2 (by rfl) ⟨521457, by rfl⟩ : syracuseStep 1390553 = 1042915) B1042915
theorem B1390667 : Blo 924580 1390667 := bstep (se 1 (by rfl) ⟨1043000, by rfl⟩ : syracuseStep 1390667 = 2086001) B2086001
theorem B1390679 : Blo 924580 1390679 := bstep (se 1 (by rfl) ⟨1043009, by rfl⟩ : syracuseStep 1390679 = 2086019) B2086019
theorem B6666371 : Blo 924580 6666371 := bstep (se 1 (by rfl) ⟨4999778, by rfl⟩ : syracuseStep 6666371 = 9999557) B9999557
theorem B1390745 : Blo 924580 1390745 := bstep (se 2 (by rfl) ⟨521529, by rfl⟩ : syracuseStep 1390745 = 1043059) B1043059
theorem B3520691 : Blo 924580 3520691 := bstep (se 1 (by rfl) ⟨2640518, by rfl⟩ : syracuseStep 3520691 = 5281037) B5281037
theorem B3520705 : Blo 924580 3520705 := bstep (se 2 (by rfl) ⟨1320264, by rfl⟩ : syracuseStep 3520705 = 2640529) B2640529
theorem B3127517 : Blo 924580 3127517 := bstep (se 3 (by rfl) ⟨586409, by rfl⟩ : syracuseStep 3127517 = 1172819) B1172819
theorem B1390859 : Blo 924580 1390859 := bstep (se 1 (by rfl) ⟨1043144, by rfl⟩ : syracuseStep 1390859 = 2086289) B2086289
theorem B1390871 : Blo 924580 1390871 := bstep (se 1 (by rfl) ⟨1043153, by rfl⟩ : syracuseStep 1390871 = 2086307) B2086307
theorem B1390937 : Blo 924580 1390937 := bstep (se 2 (by rfl) ⟨521601, by rfl⟩ : syracuseStep 1390937 = 1043203) B1043203
theorem B1391051 : Blo 924580 1391051 := bstep (se 1 (by rfl) ⟨1043288, by rfl⟩ : syracuseStep 1391051 = 2086577) B2086577
theorem B1391063 : Blo 924580 1391063 := bstep (se 1 (by rfl) ⟨1043297, by rfl⟩ : syracuseStep 1391063 = 2086595) B2086595
theorem B1391129 : Blo 924580 1391129 := bstep (se 2 (by rfl) ⟨521673, by rfl⟩ : syracuseStep 1391129 = 1043347) B1043347
theorem B8010341 : Blo 924580 8010341 := bstep (se 4 (by rfl) ⟨750969, by rfl⟩ : syracuseStep 8010341 = 1501939) B1501939
theorem B1391243 : Blo 924580 1391243 := bstep (se 1 (by rfl) ⟨1043432, by rfl⟩ : syracuseStep 1391243 = 2086865) B2086865
theorem B1391255 : Blo 924580 1391255 := bstep (se 1 (by rfl) ⟨1043441, by rfl⟩ : syracuseStep 1391255 = 2086883) B2086883
theorem B1391321 : Blo 924580 1391321 := bstep (se 2 (by rfl) ⟨521745, by rfl⟩ : syracuseStep 1391321 = 1043491) B1043491
theorem B2636509 : Blo 924580 2636509 := bstep (se 3 (by rfl) ⟨494345, by rfl⟩ : syracuseStep 2636509 = 988691) B988691
theorem B2145035 : Blo 924580 2145035 := bstep (se 1 (by rfl) ⟨1608776, by rfl⟩ : syracuseStep 2145035 = 3217553) B3217553
theorem B1981235 : Blo 924580 1981235 := bstep (se 1 (by rfl) ⟨1485926, by rfl⟩ : syracuseStep 1981235 = 2971853) B2971853
theorem B1391435 : Blo 924580 1391435 := bstep (se 1 (by rfl) ⟨1043576, by rfl⟩ : syracuseStep 1391435 = 2087153) B2087153
theorem B1391447 : Blo 924580 1391447 := bstep (se 1 (by rfl) ⟨1043585, by rfl⟩ : syracuseStep 1391447 = 2087171) B2087171
theorem B1391513 : Blo 924580 1391513 := bstep (se 2 (by rfl) ⟨521817, by rfl⟩ : syracuseStep 1391513 = 1043635) B1043635
theorem B2341811 : Blo 924580 2341811 := bstep (se 1 (by rfl) ⟨1756358, by rfl⟩ : syracuseStep 2341811 = 3512717) B3512717
theorem B1391627 : Blo 924580 1391627 := bstep (se 1 (by rfl) ⟨1043720, by rfl⟩ : syracuseStep 1391627 = 2087441) B2087441
theorem B1391639 : Blo 924580 1391639 := bstep (se 1 (by rfl) ⟨1043729, by rfl⟩ : syracuseStep 1391639 = 2087459) B2087459
theorem B2374721 : Blo 924580 2374721 := bstep (se 2 (by rfl) ⟨890520, by rfl⟩ : syracuseStep 2374721 = 1781041) B1781041
theorem B1391705 : Blo 924580 1391705 := bstep (se 2 (by rfl) ⟨521889, by rfl⟩ : syracuseStep 1391705 = 1043779) B1043779
theorem B1391819 : Blo 924580 1391819 := bstep (se 1 (by rfl) ⟨1043864, by rfl⟩ : syracuseStep 1391819 = 2087729) B2087729
theorem B1391831 : Blo 924580 1391831 := bstep (se 1 (by rfl) ⟨1043873, by rfl⟩ : syracuseStep 1391831 = 2087747) B2087747
theorem B2342105 : Blo 924580 2342105 := bstep (se 2 (by rfl) ⟨878289, by rfl⟩ : syracuseStep 2342105 = 1756579) B1756579
theorem B2964701 : Blo 924580 2964701 := bstep (se 3 (by rfl) ⟨555881, by rfl⟩ : syracuseStep 2964701 = 1111763) B1111763
theorem B1391897 : Blo 924580 1391897 := bstep (se 2 (by rfl) ⟨521961, by rfl⟩ : syracuseStep 1391897 = 1043923) B1043923
theorem B3128651 : Blo 924580 3128651 := bstep (se 1 (by rfl) ⟨2346488, by rfl⟩ : syracuseStep 3128651 = 4692977) B4692977
theorem B1392011 : Blo 924580 1392011 := bstep (se 1 (by rfl) ⟨1044008, by rfl⟩ : syracuseStep 1392011 = 2088017) B2088017
theorem B1392023 : Blo 924580 1392023 := bstep (se 1 (by rfl) ⟨1044017, by rfl⟩ : syracuseStep 1392023 = 2088035) B2088035
theorem B1392089 : Blo 924580 1392089 := bstep (se 2 (by rfl) ⟨522033, by rfl⟩ : syracuseStep 1392089 = 1044067) B1044067
theorem B2080331 : Blo 924580 2080331 := bstep (se 1 (by rfl) ⟨1560248, by rfl⟩ : syracuseStep 2080331 = 3120497) B3120497
theorem B1392203 : Blo 924580 1392203 := bstep (se 1 (by rfl) ⟨1044152, by rfl⟩ : syracuseStep 1392203 = 2088305) B2088305
theorem B1392215 : Blo 924580 1392215 := bstep (se 1 (by rfl) ⟨1044161, by rfl⟩ : syracuseStep 1392215 = 2088323) B2088323
theorem B3128921 : Blo 924580 3128921 := bstep (se 2 (by rfl) ⟨1173345, by rfl⟩ : syracuseStep 3128921 = 2346691) B2346691
theorem B2080385 : Blo 924580 2080385 := bstep (se 2 (by rfl) ⟨780144, by rfl⟩ : syracuseStep 2080385 = 1560289) B1560289
theorem B1392281 : Blo 924580 1392281 := bstep (se 2 (by rfl) ⟨522105, by rfl⟩ : syracuseStep 1392281 = 1044211) B1044211
theorem B1392395 : Blo 924580 1392395 := bstep (se 1 (by rfl) ⟨1044296, by rfl⟩ : syracuseStep 1392395 = 2088593) B2088593
theorem B1392407 : Blo 924580 1392407 := bstep (se 1 (by rfl) ⟨1044305, by rfl⟩ : syracuseStep 1392407 = 2088611) B2088611
theorem B2080601 : Blo 924580 2080601 := bstep (se 2 (by rfl) ⟨780225, by rfl⟩ : syracuseStep 2080601 = 1560451) B1560451
theorem B1392473 : Blo 924580 1392473 := bstep (se 2 (by rfl) ⟨522177, by rfl⟩ : syracuseStep 1392473 = 1044355) B1044355
theorem B2080691 : Blo 924580 2080691 := bstep (se 1 (by rfl) ⟨1560518, by rfl⟩ : syracuseStep 2080691 = 3121037) B3121037
theorem B17121203 : Blo 924580 17121203 := bstep (se 1 (by rfl) ⟨12840902, by rfl⟩ : syracuseStep 17121203 = 25681805) B25681805
theorem B1392587 : Blo 924580 1392587 := bstep (se 1 (by rfl) ⟨1044440, by rfl⟩ : syracuseStep 1392587 = 2088881) B2088881
theorem B2080727 : Blo 924580 2080727 := bstep (se 1 (by rfl) ⟨1560545, by rfl⟩ : syracuseStep 2080727 = 3121091) B3121091
theorem B1392599 : Blo 924580 1392599 := bstep (se 1 (by rfl) ⟨1044449, by rfl⟩ : syracuseStep 1392599 = 2088899) B2088899
theorem B2637785 : Blo 924580 2637785 := bstep (se 2 (by rfl) ⟨989169, by rfl⟩ : syracuseStep 2637785 = 1978339) B1978339
theorem B1982465 : Blo 924580 1982465 := bstep (se 2 (by rfl) ⟨743424, by rfl⟩ : syracuseStep 1982465 = 1486849) B1486849
theorem B1392665 : Blo 924580 1392665 := bstep (se 2 (by rfl) ⟨522249, by rfl⟩ : syracuseStep 1392665 = 1044499) B1044499
theorem B3522635 : Blo 924580 3522635 := bstep (se 1 (by rfl) ⟨2641976, by rfl⟩ : syracuseStep 3522635 = 5283953) B5283953
theorem B3522649 : Blo 924580 3522649 := bstep (se 2 (by rfl) ⟨1320993, by rfl⟩ : syracuseStep 3522649 = 2641987) B2641987
theorem B2080907 : Blo 924580 2080907 := bstep (se 1 (by rfl) ⟨1560680, by rfl⟩ : syracuseStep 2080907 = 3121361) B3121361
theorem B1130635 : Blo 924580 1130635 := bstep (se 1 (by rfl) ⟨847976, by rfl⟩ : syracuseStep 1130635 = 1695953) B1695953
theorem B1392779 : Blo 924580 1392779 := bstep (se 1 (by rfl) ⟨1044584, by rfl⟩ : syracuseStep 1392779 = 2089169) B2089169
theorem B1392791 : Blo 924580 1392791 := bstep (se 1 (by rfl) ⟨1044593, by rfl⟩ : syracuseStep 1392791 = 2089187) B2089187
theorem B2080961 : Blo 924580 2080961 := bstep (se 2 (by rfl) ⟨780360, by rfl⟩ : syracuseStep 2080961 = 1560721) B1560721
theorem B5357785 : Blo 924580 5357785 := bstep (se 2 (by rfl) ⟨2009169, by rfl⟩ : syracuseStep 5357785 = 4018339) B4018339
theorem B1392857 : Blo 924580 1392857 := bstep (se 2 (by rfl) ⟨522321, by rfl⟩ : syracuseStep 1392857 = 1044643) B1044643
theorem B3129623 : Blo 924580 3129623 := bstep (se 1 (by rfl) ⟨2347217, by rfl⟩ : syracuseStep 3129623 = 4694435) B4694435
theorem B2081177 : Blo 924580 2081177 := bstep (se 2 (by rfl) ⟨780441, by rfl⟩ : syracuseStep 2081177 = 1560883) B1560883
theorem B7913933 : Blo 924580 7913933 := bstep (se 3 (by rfl) ⟨1483862, by rfl⟩ : syracuseStep 7913933 = 2967725) B2967725
theorem B2081267 : Blo 924580 2081267 := bstep (se 1 (by rfl) ⟨1560950, by rfl⟩ : syracuseStep 2081267 = 3121901) B3121901
theorem B2081303 : Blo 924580 2081303 := bstep (se 1 (by rfl) ⟨1560977, by rfl⟩ : syracuseStep 2081303 = 3121955) B3121955
theorem B2081483 : Blo 924580 2081483 := bstep (se 1 (by rfl) ⟨1561112, by rfl⟩ : syracuseStep 2081483 = 3122225) B3122225
theorem B2081537 : Blo 924580 2081537 := bstep (se 2 (by rfl) ⟨780576, by rfl⟩ : syracuseStep 2081537 = 1561153) B1561153
theorem B3130163 : Blo 924580 3130163 := bstep (se 1 (by rfl) ⟨2347622, by rfl⟩ : syracuseStep 3130163 = 4695245) B4695245
theorem B2343755 : Blo 924580 2343755 := bstep (se 1 (by rfl) ⟨1757816, by rfl⟩ : syracuseStep 2343755 = 3515633) B3515633
theorem B2081753 : Blo 924580 2081753 := bstep (se 2 (by rfl) ⟨780657, by rfl⟩ : syracuseStep 2081753 = 1561315) B1561315
theorem B3523607 : Blo 924580 3523607 := bstep (se 1 (by rfl) ⟨2642705, by rfl⟩ : syracuseStep 3523607 = 5285411) B5285411
theorem B32228387 : Blo 924580 32228387 := bstep (se 1 (by rfl) ⟨24171290, by rfl⟩ : syracuseStep 32228387 = 48342581) B48342581
theorem B2081843 : Blo 924580 2081843 := bstep (se 1 (by rfl) ⟨1561382, by rfl⟩ : syracuseStep 2081843 = 3122765) B3122765
theorem B3130433 : Blo 924580 3130433 := bstep (se 2 (by rfl) ⟨1173912, by rfl⟩ : syracuseStep 3130433 = 2347825) B2347825
theorem B2081879 : Blo 924580 2081879 := bstep (se 1 (by rfl) ⟨1561409, by rfl⟩ : syracuseStep 2081879 = 3122819) B3122819
theorem B15025283 : Blo 924580 15025283 := bstep (se 1 (by rfl) ⟨11268962, by rfl⟩ : syracuseStep 15025283 = 22537925) B22537925
theorem B2082059 : Blo 924580 2082059 := bstep (se 1 (by rfl) ⟨1561544, by rfl⟩ : syracuseStep 2082059 = 3123089) B3123089
theorem B2082113 : Blo 924580 2082113 := bstep (se 2 (by rfl) ⟨780792, by rfl⟩ : syracuseStep 2082113 = 1561585) B1561585
theorem B1689025 : Blo 924580 1689025 := bstep (se 2 (by rfl) ⟨633384, by rfl⟩ : syracuseStep 1689025 = 1266769) B1266769
theorem B2082329 : Blo 924580 2082329 := bstep (se 2 (by rfl) ⟨780873, by rfl⟩ : syracuseStep 2082329 = 1561747) B1561747
theorem B2639425 : Blo 924580 2639425 := bstep (se 2 (by rfl) ⟨989784, by rfl⟩ : syracuseStep 2639425 = 1979569) B1979569
theorem B8439389 : Blo 924580 8439389 := bstep (se 3 (by rfl) ⟨1582385, by rfl⟩ : syracuseStep 8439389 = 3164771) B3164771
theorem B3130973 : Blo 924580 3130973 := bstep (se 3 (by rfl) ⟨587057, by rfl⟩ : syracuseStep 3130973 = 1174115) B1174115
theorem B2082419 : Blo 924580 2082419 := bstep (se 1 (by rfl) ⟨1561814, by rfl⟩ : syracuseStep 2082419 = 3123629) B3123629
theorem B2082455 : Blo 924580 2082455 := bstep (se 1 (by rfl) ⟨1561841, by rfl⟩ : syracuseStep 2082455 = 3123683) B3123683
theorem B6670001 : Blo 924580 6670001 := bstep (se 2 (by rfl) ⟨2501250, by rfl⟩ : syracuseStep 6670001 = 5002501) B5002501
theorem B2344727 : Blo 924580 2344727 := bstep (se 1 (by rfl) ⟨1758545, by rfl⟩ : syracuseStep 2344727 = 3517091) B3517091
theorem B2082635 : Blo 924580 2082635 := bstep (se 1 (by rfl) ⟨1561976, by rfl⟩ : syracuseStep 2082635 = 3123953) B3123953
theorem B2082689 : Blo 924580 2082689 := bstep (se 2 (by rfl) ⟨781008, by rfl⟩ : syracuseStep 2082689 = 1562017) B1562017
theorem B4507571 : Blo 924580 4507571 := bstep (se 1 (by rfl) ⟨3380678, by rfl⟩ : syracuseStep 4507571 = 6761357) B6761357
theorem B2082905 : Blo 924580 2082905 := bstep (se 2 (by rfl) ⟨781089, by rfl⟩ : syracuseStep 2082905 = 1562179) B1562179
theorem B1755265 : Blo 924580 1755265 := bstep (se 2 (by rfl) ⟨658224, by rfl⟩ : syracuseStep 1755265 = 1316449) B1316449
theorem B7030961 : Blo 924580 7030961 := bstep (se 2 (by rfl) ⟨2636610, by rfl⟩ : syracuseStep 7030961 = 5273221) B5273221
theorem B2082995 : Blo 924580 2082995 := bstep (se 1 (by rfl) ⟨1562246, by rfl⟩ : syracuseStep 2082995 = 3124493) B3124493
theorem B2083031 : Blo 924580 2083031 := bstep (se 1 (by rfl) ⟨1562273, by rfl⟩ : syracuseStep 2083031 = 3124547) B3124547
theorem B3524867 : Blo 924580 3524867 := bstep (se 1 (by rfl) ⟨2643650, by rfl⟩ : syracuseStep 3524867 = 5287301) B5287301
theorem B2083211 : Blo 924580 2083211 := bstep (se 1 (by rfl) ⟨1562408, by rfl⟩ : syracuseStep 2083211 = 3124817) B3124817
theorem B2345395 : Blo 924580 2345395 := bstep (se 1 (by rfl) ⟨1759046, by rfl⟩ : syracuseStep 2345395 = 3518093) B3518093
theorem B2083265 : Blo 924580 2083265 := bstep (se 2 (by rfl) ⟨781224, by rfl⟩ : syracuseStep 2083265 = 1562449) B1562449
theorem B1755607 : Blo 924580 1755607 := bstep (se 1 (by rfl) ⟨1316705, by rfl⟩ : syracuseStep 1755607 = 2633411) B2633411
theorem B3754457 : Blo 924580 3754457 := bstep (se 2 (by rfl) ⟨1407921, by rfl⟩ : syracuseStep 3754457 = 2815843) B2815843
theorem B2345537 : Blo 924580 2345537 := bstep (se 2 (by rfl) ⟨879576, by rfl⟩ : syracuseStep 2345537 = 1759153) B1759153
theorem B7031447 : Blo 924580 7031447 := bstep (se 1 (by rfl) ⟨5273585, by rfl⟩ : syracuseStep 7031447 = 10547171) B10547171
theorem B2083481 : Blo 924580 2083481 := bstep (se 2 (by rfl) ⟨781305, by rfl⟩ : syracuseStep 2083481 = 1562611) B1562611
theorem B1755827 : Blo 924580 1755827 := bstep (se 1 (by rfl) ⟨1316870, by rfl⟩ : syracuseStep 1755827 = 2633741) B2633741
theorem B2116289 : Blo 924580 2116289 := bstep (se 2 (by rfl) ⟨793608, by rfl⟩ : syracuseStep 2116289 = 1587217) B1587217
theorem B3132107 : Blo 924580 3132107 := bstep (se 1 (by rfl) ⟨2349080, by rfl⟩ : syracuseStep 3132107 = 4698161) B4698161
theorem B2083571 : Blo 924580 2083571 := bstep (se 1 (by rfl) ⟨1562678, by rfl⟩ : syracuseStep 2083571 = 3125357) B3125357
theorem B2083607 : Blo 924580 2083607 := bstep (se 1 (by rfl) ⟨1562705, by rfl⟩ : syracuseStep 2083607 = 3125411) B3125411
theorem B3164993 : Blo 924580 3164993 := bstep (se 2 (by rfl) ⟨1186872, by rfl⟩ : syracuseStep 3164993 = 2373745) B2373745
theorem B1756055 : Blo 924580 1756055 := bstep (se 1 (by rfl) ⟨1317041, by rfl⟩ : syracuseStep 1756055 = 2634083) B2634083
theorem B2083787 : Blo 924580 2083787 := bstep (se 1 (by rfl) ⟨1562840, by rfl⟩ : syracuseStep 2083787 = 3125681) B3125681
theorem B2509771 : Blo 924580 2509771 := bstep (se 1 (by rfl) ⟨1882328, by rfl⟩ : syracuseStep 2509771 = 3764657) B3764657
theorem B3132377 : Blo 924580 3132377 := bstep (se 2 (by rfl) ⟨1174641, by rfl⟩ : syracuseStep 3132377 = 2349283) B2349283
theorem B2083841 : Blo 924580 2083841 := bstep (se 2 (by rfl) ⟨781440, by rfl⟩ : syracuseStep 2083841 = 1562881) B1562881
theorem B1756313 : Blo 924580 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B2641099 : Blo 924580 2641099 := bstep (se 1 (by rfl) ⟨1980824, by rfl⟩ : syracuseStep 2641099 = 3961649) B3961649
theorem B2084057 : Blo 924580 2084057 := bstep (se 2 (by rfl) ⟨781521, by rfl⟩ : syracuseStep 2084057 = 1563043) B1563043
theorem B3755315 : Blo 924580 3755315 := bstep (se 1 (by rfl) ⟨2816486, by rfl⟩ : syracuseStep 3755315 = 5632973) B5632973
theorem B2084147 : Blo 924580 2084147 := bstep (se 1 (by rfl) ⟨1563110, by rfl⟩ : syracuseStep 2084147 = 3126221) B3126221
theorem B2084183 : Blo 924580 2084183 := bstep (se 1 (by rfl) ⟨1563137, by rfl⟩ : syracuseStep 2084183 = 3126275) B3126275
theorem B2641373 : Blo 924580 2641373 := bstep (se 3 (by rfl) ⟨495257, by rfl⟩ : syracuseStep 2641373 = 990515) B990515
theorem B2084363 : Blo 924580 2084363 := bstep (se 1 (by rfl) ⟨1563272, by rfl⟩ : syracuseStep 2084363 = 3126545) B3126545
theorem B5721617 : Blo 924580 5721617 := bstep (se 2 (by rfl) ⟨2145606, by rfl⟩ : syracuseStep 5721617 = 4291213) B4291213
theorem B1003051 : Blo 924580 1003051 := bstep (se 1 (by rfl) ⟨752288, by rfl⟩ : syracuseStep 1003051 = 1504577) B1504577
theorem B1756723 : Blo 924580 1756723 := bstep (se 1 (by rfl) ⟨1317542, by rfl⟩ : syracuseStep 1756723 = 2635085) B2635085
theorem B2084417 : Blo 924580 2084417 := bstep (se 2 (by rfl) ⟨781656, by rfl⟩ : syracuseStep 2084417 = 1563313) B1563313
theorem B2674241 : Blo 924580 2674241 := bstep (se 2 (by rfl) ⟨1002840, by rfl⟩ : syracuseStep 2674241 = 2005681) B2005681
theorem B6016643 : Blo 924580 6016643 := bstep (se 1 (by rfl) ⟨4512482, by rfl⟩ : syracuseStep 6016643 = 9024965) B9024965
theorem B3133079 : Blo 924580 3133079 := bstep (se 1 (by rfl) ⟨2349809, by rfl⟩ : syracuseStep 3133079 = 4699619) B4699619
theorem B6672077 : Blo 924580 6672077 := bstep (se 3 (by rfl) ⟨1251014, by rfl⟩ : syracuseStep 6672077 = 2502029) B2502029
theorem B4017923 : Blo 924580 4017923 := bstep (se 1 (by rfl) ⟨3013442, by rfl⟩ : syracuseStep 4017923 = 6026885) B6026885
theorem B1560343 : Blo 924580 1560343 := bstep (se 1 (by rfl) ⟨1170257, by rfl⟩ : syracuseStep 1560343 = 2340515) B2340515
theorem B2084633 : Blo 924580 2084633 := bstep (se 2 (by rfl) ⟨781737, by rfl⟩ : syracuseStep 2084633 = 1563475) B1563475
theorem B2346803 : Blo 924580 2346803 := bstep (se 1 (by rfl) ⟨1760102, by rfl⟩ : syracuseStep 2346803 = 3520205) B3520205
theorem B2084723 : Blo 924580 2084723 := bstep (se 1 (by rfl) ⟨1563542, by rfl⟩ : syracuseStep 2084723 = 3127085) B3127085
theorem B2084759 : Blo 924580 2084759 := bstep (se 1 (by rfl) ⟨1563569, by rfl⟩ : syracuseStep 2084759 = 3127139) B3127139
theorem B3952577 : Blo 924580 3952577 := bstep (se 2 (by rfl) ⟨1482216, by rfl⟩ : syracuseStep 3952577 = 2964433) B2964433
theorem B1757209 : Blo 924580 1757209 := bstep (se 2 (by rfl) ⟨658953, by rfl⟩ : syracuseStep 1757209 = 1317907) B1317907
theorem B2117657 : Blo 924580 2117657 := bstep (se 2 (by rfl) ⟨794121, by rfl⟩ : syracuseStep 2117657 = 1588243) B1588243
theorem B2084939 : Blo 924580 2084939 := bstep (se 1 (by rfl) ⟨1563704, by rfl⟩ : syracuseStep 2084939 = 3127409) B3127409
theorem B3952729 : Blo 924580 3952729 := bstep (se 2 (by rfl) ⟨1482273, by rfl⟩ : syracuseStep 3952729 = 2964547) B2964547
theorem B5623901 : Blo 924580 5623901 := bstep (se 3 (by rfl) ⟨1054481, by rfl⟩ : syracuseStep 5623901 = 2108963) B2108963
theorem B2084993 : Blo 924580 2084993 := bstep (se 2 (by rfl) ⟨781872, by rfl⟩ : syracuseStep 2084993 = 1563745) B1563745
theorem B3133619 : Blo 924580 3133619 := bstep (se 1 (by rfl) ⟨2350214, by rfl⟩ : syracuseStep 3133619 = 4700429) B4700429
theorem B2347339 : Blo 924580 2347339 := bstep (se 1 (by rfl) ⟨1760504, by rfl⟩ : syracuseStep 2347339 = 3521009) B3521009
theorem B2085209 : Blo 924580 2085209 := bstep (se 2 (by rfl) ⟨781953, by rfl⟩ : syracuseStep 2085209 = 1563907) B1563907
theorem B1560971 : Blo 924580 1560971 := bstep (se 1 (by rfl) ⟨1170728, by rfl⟩ : syracuseStep 1560971 = 2341457) B2341457
theorem B2085299 : Blo 924580 2085299 := bstep (se 1 (by rfl) ⟨1563974, by rfl⟩ : syracuseStep 2085299 = 3127949) B3127949
theorem B3133889 : Blo 924580 3133889 := bstep (se 2 (by rfl) ⟨1175208, by rfl⟩ : syracuseStep 3133889 = 2350417) B2350417
theorem B2085335 : Blo 924580 2085335 := bstep (se 1 (by rfl) ⟨1564001, by rfl⟩ : syracuseStep 2085335 = 3128003) B3128003
theorem B2347481 : Blo 924580 2347481 := bstep (se 2 (by rfl) ⟨880305, by rfl⟩ : syracuseStep 2347481 = 1760611) B1760611
theorem B1561099 : Blo 924580 1561099 := bstep (se 1 (by rfl) ⟨1170824, by rfl⟩ : syracuseStep 1561099 = 2341649) B2341649
theorem B1757771 : Blo 924580 1757771 := bstep (se 1 (by rfl) ⟨1318328, by rfl⟩ : syracuseStep 1757771 = 2636657) B2636657
theorem B2085515 : Blo 924580 2085515 := bstep (se 1 (by rfl) ⟨1564136, by rfl⟩ : syracuseStep 2085515 = 3128273) B3128273
theorem B1561241 : Blo 924580 1561241 := bstep (se 2 (by rfl) ⟨585465, by rfl⟩ : syracuseStep 1561241 = 1170931) B1170931
theorem B2085569 : Blo 924580 2085569 := bstep (se 2 (by rfl) ⟨782088, by rfl⟩ : syracuseStep 2085569 = 1564177) B1564177
theorem B1757953 : Blo 924580 1757953 := bstep (se 2 (by rfl) ⟨659232, by rfl⟩ : syracuseStep 1757953 = 1318465) B1318465
theorem B12669701 : Blo 924580 12669701 := bstep (se 4 (by rfl) ⟨1187784, by rfl⟩ : syracuseStep 12669701 = 2375569) B2375569
theorem B2970391 : Blo 924580 2970391 := bstep (se 1 (by rfl) ⟨2227793, by rfl⟩ : syracuseStep 2970391 = 4455587) B4455587
theorem B1561369 : Blo 924580 1561369 := bstep (se 2 (by rfl) ⟨585513, by rfl⟩ : syracuseStep 1561369 = 1171027) B1171027
theorem B2085785 : Blo 924580 2085785 := bstep (se 2 (by rfl) ⟨782169, by rfl⟩ : syracuseStep 2085785 = 1564339) B1564339
theorem B2085875 : Blo 924580 2085875 := bstep (se 1 (by rfl) ⟨1564406, by rfl⟩ : syracuseStep 2085875 = 3128813) B3128813
theorem B2085911 : Blo 924580 2085911 := bstep (se 1 (by rfl) ⟨1564433, by rfl⟩ : syracuseStep 2085911 = 3128867) B3128867
theorem B10277923 : Blo 924580 10277923 := bstep (se 1 (by rfl) ⟨7708442, by rfl⟩ : syracuseStep 10277923 = 15416885) B15416885
theorem B2708569 : Blo 924580 2708569 := bstep (se 2 (by rfl) ⟨1015713, by rfl⟩ : syracuseStep 2708569 = 2031427) B2031427
theorem B36066485 : Blo 924580 36066485 := bstep (se 5 (by rfl) ⟨1690616, by rfl⟩ : syracuseStep 36066485 = 3381233) B3381233
theorem B2086091 : Blo 924580 2086091 := bstep (se 1 (by rfl) ⟨1564568, by rfl⟩ : syracuseStep 2086091 = 3129137) B3129137
theorem B2970827 : Blo 924580 2970827 := bstep (se 1 (by rfl) ⟨2228120, by rfl⟩ : syracuseStep 2970827 = 4456241) B4456241
theorem B2086145 : Blo 924580 2086145 := bstep (se 2 (by rfl) ⟨782304, by rfl⟩ : syracuseStep 2086145 = 1564609) B1564609
theorem B2348311 : Blo 924580 2348311 := bstep (se 1 (by rfl) ⟨1761233, by rfl⟩ : syracuseStep 2348311 = 3522467) B3522467
theorem B1561943 : Blo 924580 1561943 := bstep (se 1 (by rfl) ⟨1171457, by rfl⟩ : syracuseStep 1561943 = 2342915) B2342915
theorem B1758667 : Blo 924580 1758667 := bstep (se 1 (by rfl) ⟨1319000, by rfl⟩ : syracuseStep 1758667 = 2638001) B2638001
theorem B1562071 : Blo 924580 1562071 := bstep (se 1 (by rfl) ⟨1171553, by rfl⟩ : syracuseStep 1562071 = 2343107) B2343107
theorem B2086361 : Blo 924580 2086361 := bstep (se 2 (by rfl) ⟨782385, by rfl⟩ : syracuseStep 2086361 = 1564771) B1564771
theorem B3757585 : Blo 924580 3757585 := bstep (se 2 (by rfl) ⟨1409094, by rfl⟩ : syracuseStep 3757585 = 2818189) B2818189
theorem B1758743 : Blo 924580 1758743 := bstep (se 1 (by rfl) ⟨1319057, by rfl⟩ : syracuseStep 1758743 = 2638115) B2638115
theorem B2086451 : Blo 924580 2086451 := bstep (se 1 (by rfl) ⟨1564838, by rfl⟩ : syracuseStep 2086451 = 3129677) B3129677
theorem B939607 : Blo 924580 939607 := bstep (se 1 (by rfl) ⟨704705, by rfl⟩ : syracuseStep 939607 = 1409411) B1409411
theorem B2086487 : Blo 924580 2086487 := bstep (se 1 (by rfl) ⟨1564865, by rfl⟩ : syracuseStep 2086487 = 3129731) B3129731
theorem B2348747 : Blo 924580 2348747 := bstep (se 1 (by rfl) ⟨1761560, by rfl⟩ : syracuseStep 2348747 = 3523121) B3523121
theorem B2643673 : Blo 924580 2643673 := bstep (se 2 (by rfl) ⟨991377, by rfl⟩ : syracuseStep 2643673 = 1982755) B1982755
theorem B2086667 : Blo 924580 2086667 := bstep (se 1 (by rfl) ⟨1565000, by rfl⟩ : syracuseStep 2086667 = 3130001) B3130001
theorem B2086721 : Blo 924580 2086721 := bstep (se 2 (by rfl) ⟨782520, by rfl⟩ : syracuseStep 2086721 = 1565041) B1565041
theorem B2086937 : Blo 924580 2086937 := bstep (se 2 (by rfl) ⟨782601, by rfl⟩ : syracuseStep 2086937 = 1565203) B1565203
theorem B2349121 : Blo 924580 2349121 := bstep (se 2 (by rfl) ⟨880920, by rfl⟩ : syracuseStep 2349121 = 1761841) B1761841
theorem B1562699 : Blo 924580 1562699 := bstep (se 1 (by rfl) ⟨1172024, by rfl⟩ : syracuseStep 1562699 = 2344049) B2344049
theorem B2971723 : Blo 924580 2971723 := bstep (se 1 (by rfl) ⟨2228792, by rfl⟩ : syracuseStep 2971723 = 4457585) B4457585
theorem B2087027 : Blo 924580 2087027 := bstep (se 1 (by rfl) ⟨1565270, by rfl⟩ : syracuseStep 2087027 = 3130541) B3130541
theorem B2087063 : Blo 924580 2087063 := bstep (se 1 (by rfl) ⟨1565297, by rfl⟩ : syracuseStep 2087063 = 3130595) B3130595
theorem B1759411 : Blo 924580 1759411 := bstep (se 1 (by rfl) ⟨1319558, by rfl⟩ : syracuseStep 1759411 = 2639117) B2639117
theorem B1562827 : Blo 924580 1562827 := bstep (se 1 (by rfl) ⟨1172120, by rfl⟩ : syracuseStep 1562827 = 2344241) B2344241
theorem B2087243 : Blo 924580 2087243 := bstep (se 1 (by rfl) ⟨1565432, by rfl⟩ : syracuseStep 2087243 = 3130865) B3130865
theorem B1562969 : Blo 924580 1562969 := bstep (se 2 (by rfl) ⟨586113, by rfl⟩ : syracuseStep 1562969 = 1172227) B1172227
theorem B2087297 : Blo 924580 2087297 := bstep (se 2 (by rfl) ⟨782736, by rfl⟩ : syracuseStep 2087297 = 1565473) B1565473
theorem B1759639 : Blo 924580 1759639 := bstep (se 1 (by rfl) ⟨1319729, by rfl⟩ : syracuseStep 1759639 = 2639459) B2639459
theorem B1563097 : Blo 924580 1563097 := bstep (se 2 (by rfl) ⟨586161, by rfl⟩ : syracuseStep 1563097 = 1172323) B1172323
theorem B1759745 : Blo 924580 1759745 := bstep (se 2 (by rfl) ⟨659904, by rfl⟩ : syracuseStep 1759745 = 1319809) B1319809
theorem B2087513 : Blo 924580 2087513 := bstep (se 2 (by rfl) ⟨782817, by rfl⟩ : syracuseStep 2087513 = 1565635) B1565635
theorem B2349719 : Blo 924580 2349719 := bstep (se 1 (by rfl) ⟨1762289, by rfl⟩ : syracuseStep 2349719 = 3524579) B3524579
theorem B1759897 : Blo 924580 1759897 := bstep (se 2 (by rfl) ⟨659961, by rfl⟩ : syracuseStep 1759897 = 1319923) B1319923
theorem B2972339 : Blo 924580 2972339 := bstep (se 1 (by rfl) ⟨2229254, by rfl⟩ : syracuseStep 2972339 = 4458509) B4458509
theorem B2087603 : Blo 924580 2087603 := bstep (se 1 (by rfl) ⟨1565702, by rfl⟩ : syracuseStep 2087603 = 3131405) B3131405
theorem B2087639 : Blo 924580 2087639 := bstep (se 1 (by rfl) ⟨1565729, by rfl⟩ : syracuseStep 2087639 = 3131459) B3131459
theorem B2972467 : Blo 924580 2972467 := bstep (se 1 (by rfl) ⟨2229350, by rfl⟩ : syracuseStep 2972467 = 4458701) B4458701
theorem B2087819 : Blo 924580 2087819 := bstep (se 1 (by rfl) ⟨1565864, by rfl⟩ : syracuseStep 2087819 = 3131729) B3131729
theorem B2087873 : Blo 924580 2087873 := bstep (se 2 (by rfl) ⟨782952, by rfl⟩ : syracuseStep 2087873 = 1565905) B1565905
theorem B1170379 : Blo 924580 1170379 := bstep (se 1 (by rfl) ⟨877784, by rfl⟩ : syracuseStep 1170379 = 1755569) B1755569
theorem B941015 : Blo 924580 941015 := bstep (se 1 (by rfl) ⟨705761, by rfl⟩ : syracuseStep 941015 = 1411523) B1411523
theorem B3333143 : Blo 924580 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B1563671 : Blo 924580 1563671 := bstep (se 1 (by rfl) ⟨1172753, by rfl⟩ : syracuseStep 1563671 = 2345507) B2345507
theorem B14998679 : Blo 924580 14998679 := bstep (se 1 (by rfl) ⟨11249009, by rfl⟩ : syracuseStep 14998679 = 22498019) B22498019
theorem B3333271 : Blo 924580 3333271 := bstep (se 1 (by rfl) ⟨2499953, by rfl⟩ : syracuseStep 3333271 = 4999907) B4999907
theorem B1563799 : Blo 924580 1563799 := bstep (se 1 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 1563799 = 2345699) B2345699
theorem B2088089 : Blo 924580 2088089 := bstep (se 2 (by rfl) ⟨783033, by rfl⟩ : syracuseStep 2088089 = 1566067) B1566067
theorem B2088179 : Blo 924580 2088179 := bstep (se 1 (by rfl) ⟨1566134, by rfl⟩ : syracuseStep 2088179 = 3132269) B3132269
theorem B2088215 : Blo 924580 2088215 := bstep (se 1 (by rfl) ⟨1566161, by rfl⟩ : syracuseStep 2088215 = 3132323) B3132323
theorem B8478103 : Blo 924580 8478103 := bstep (se 1 (by rfl) ⟨6358577, by rfl⟩ : syracuseStep 8478103 = 12717155) B12717155
theorem B3956147 : Blo 924580 3956147 := bstep (se 1 (by rfl) ⟨2967110, by rfl⟩ : syracuseStep 3956147 = 5934221) B5934221
theorem B2088395 : Blo 924580 2088395 := bstep (se 1 (by rfl) ⟨1566296, by rfl⟩ : syracuseStep 2088395 = 3132593) B3132593
theorem B2088449 : Blo 924580 2088449 := bstep (se 2 (by rfl) ⟨783168, by rfl⟩ : syracuseStep 2088449 = 1566337) B1566337
theorem B10542797 : Blo 924580 10542797 := bstep (se 3 (by rfl) ⟨1976774, by rfl⟩ : syracuseStep 10542797 = 3953549) B3953549
theorem B2088665 : Blo 924580 2088665 := bstep (se 2 (by rfl) ⟨783249, by rfl⟩ : syracuseStep 2088665 = 1566499) B1566499
theorem B1564427 : Blo 924580 1564427 := bstep (se 1 (by rfl) ⟨1173320, by rfl⟩ : syracuseStep 1564427 = 2346641) B2346641
theorem B2088755 : Blo 924580 2088755 := bstep (se 1 (by rfl) ⟨1566566, by rfl⟩ : syracuseStep 2088755 = 3133133) B3133133
theorem B1040215 : Blo 924580 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B2088791 : Blo 924580 2088791 := bstep (se 1 (by rfl) ⟨1566593, by rfl⟩ : syracuseStep 2088791 = 3133187) B3133187
theorem B1564555 : Blo 924580 1564555 := bstep (se 1 (by rfl) ⟨1173416, by rfl⟩ : syracuseStep 1564555 = 2346833) B2346833
theorem B1171351 : Blo 924580 1171351 := bstep (se 1 (by rfl) ⟨878513, by rfl⟩ : syracuseStep 1171351 = 1757027) B1757027
theorem B3334067 : Blo 924580 3334067 := bstep (se 1 (by rfl) ⟨2500550, by rfl⟩ : syracuseStep 3334067 = 5001101) B5001101
theorem B1761203 : Blo 924580 1761203 := bstep (se 1 (by rfl) ⟨1320902, by rfl⟩ : syracuseStep 1761203 = 2641805) B2641805
theorem B1040395 : Blo 924580 1040395 := bstep (se 1 (by rfl) ⟨780296, by rfl⟩ : syracuseStep 1040395 = 1560593) B1560593
theorem B2088971 : Blo 924580 2088971 := bstep (se 1 (by rfl) ⟨1566728, by rfl⟩ : syracuseStep 2088971 = 3133457) B3133457
theorem B1564697 : Blo 924580 1564697 := bstep (se 2 (by rfl) ⟨586761, by rfl⟩ : syracuseStep 1564697 = 1173523) B1173523
theorem B2089025 : Blo 924580 2089025 := bstep (se 2 (by rfl) ⟨783384, by rfl⟩ : syracuseStep 2089025 = 1566769) B1566769
theorem B1761355 : Blo 924580 1761355 := bstep (se 1 (by rfl) ⟨1321016, by rfl⟩ : syracuseStep 1761355 = 2642033) B2642033
theorem B1040503 : Blo 924580 1040503 := bstep (se 1 (by rfl) ⟨780377, by rfl⟩ : syracuseStep 1040503 = 1560755) B1560755
theorem B8446103 : Blo 924580 8446103 := bstep (se 1 (by rfl) ⟨6334577, by rfl⟩ : syracuseStep 8446103 = 12669155) B12669155
theorem B1564825 : Blo 924580 1564825 := bstep (se 2 (by rfl) ⟨586809, by rfl⟩ : syracuseStep 1564825 = 1173619) B1173619
theorem B2089241 : Blo 924580 2089241 := bstep (se 2 (by rfl) ⟨783465, by rfl⟩ : syracuseStep 2089241 = 1566931) B1566931
theorem B1040683 : Blo 924580 1040683 := bstep (se 1 (by rfl) ⟨780512, by rfl⟩ : syracuseStep 1040683 = 1561025) B1561025
theorem B10314029 : Blo 924580 10314029 := bstep (se 3 (by rfl) ⟨1933880, by rfl⟩ : syracuseStep 10314029 = 3867761) B3867761
theorem B1040791 : Blo 924580 1040791 := bstep (se 1 (by rfl) ⟨780593, by rfl⟩ : syracuseStep 1040791 = 1561187) B1561187
theorem B1761689 : Blo 924580 1761689 := bstep (se 2 (by rfl) ⟨660633, by rfl⟩ : syracuseStep 1761689 = 1321267) B1321267
theorem B1040971 : Blo 924580 1040971 := bstep (se 1 (by rfl) ⟨780728, by rfl⟩ : syracuseStep 1040971 = 1561457) B1561457
theorem B12706379 : Blo 924580 12706379 := bstep (se 1 (by rfl) ⟨9529784, by rfl⟩ : syracuseStep 12706379 = 19059569) B19059569
theorem B1041079 : Blo 924580 1041079 := bstep (se 1 (by rfl) ⟨780809, by rfl⟩ : syracuseStep 1041079 = 1561619) B1561619
theorem B1172171 : Blo 924580 1172171 := bstep (se 1 (by rfl) ⟨879128, by rfl⟩ : syracuseStep 1172171 = 1758257) B1758257
theorem B1565399 : Blo 924580 1565399 := bstep (se 1 (by rfl) ⟨1174049, by rfl⟩ : syracuseStep 1565399 = 2348099) B2348099
theorem B15065861 : Blo 924580 15065861 := bstep (se 4 (by rfl) ⟨1412424, by rfl⟩ : syracuseStep 15065861 = 2824849) B2824849
theorem B1565527 : Blo 924580 1565527 := bstep (se 1 (by rfl) ⟨1174145, by rfl⟩ : syracuseStep 1565527 = 2348291) B2348291
theorem B1041259 : Blo 924580 1041259 := bstep (se 1 (by rfl) ⟨780944, by rfl⟩ : syracuseStep 1041259 = 1561889) B1561889
theorem B15000497 : Blo 924580 15000497 := bstep (se 2 (by rfl) ⟨5625186, by rfl⟩ : syracuseStep 15000497 = 11250373) B11250373
theorem B1041367 : Blo 924580 1041367 := bstep (se 1 (by rfl) ⟨781025, by rfl⟩ : syracuseStep 1041367 = 1562051) B1562051
theorem B1762327 : Blo 924580 1762327 := bstep (se 1 (by rfl) ⟨1321745, by rfl⟩ : syracuseStep 1762327 = 2643491) B2643491
theorem B1041547 : Blo 924580 1041547 := bstep (se 1 (by rfl) ⟨781160, by rfl⟩ : syracuseStep 1041547 = 1562321) B1562321
theorem B2712793 : Blo 924580 2712793 := bstep (se 2 (by rfl) ⟨1017297, by rfl⟩ : syracuseStep 2712793 = 2034595) B2034595
theorem B1041655 : Blo 924580 1041655 := bstep (se 1 (by rfl) ⟨781241, by rfl⟩ : syracuseStep 1041655 = 1562483) B1562483
theorem B8447237 : Blo 924580 8447237 := bstep (se 4 (by rfl) ⟨791928, by rfl⟩ : syracuseStep 8447237 = 1583857) B1583857
theorem B1172875 : Blo 924580 1172875 := bstep (se 1 (by rfl) ⟨879656, by rfl⟩ : syracuseStep 1172875 = 1759313) B1759313
theorem B1041835 : Blo 924580 1041835 := bstep (se 1 (by rfl) ⟨781376, by rfl⟩ : syracuseStep 1041835 = 1562753) B1562753
theorem B1566155 : Blo 924580 1566155 := bstep (se 1 (by rfl) ⟨1174616, by rfl⟩ : syracuseStep 1566155 = 2349233) B2349233
theorem B1041943 : Blo 924580 1041943 := bstep (se 1 (by rfl) ⟨781457, by rfl⟩ : syracuseStep 1041943 = 1562915) B1562915
theorem B2221643 : Blo 924580 2221643 := bstep (se 1 (by rfl) ⟨1666232, by rfl⟩ : syracuseStep 2221643 = 3332465) B3332465
theorem B1566283 : Blo 924580 1566283 := bstep (se 1 (by rfl) ⟨1174712, by rfl⟩ : syracuseStep 1566283 = 2349425) B2349425
theorem B1173143 : Blo 924580 1173143 := bstep (se 1 (by rfl) ⟨879857, by rfl⟩ : syracuseStep 1173143 = 1759715) B1759715
theorem B10708631 : Blo 924580 10708631 := bstep (se 1 (by rfl) ⟨8031473, by rfl⟩ : syracuseStep 10708631 = 16062947) B16062947
theorem B1042123 : Blo 924580 1042123 := bstep (se 1 (by rfl) ⟨781592, by rfl⟩ : syracuseStep 1042123 = 1563185) B1563185
theorem B1566425 : Blo 924580 1566425 := bstep (se 2 (by rfl) ⟨587409, by rfl⟩ : syracuseStep 1566425 = 1174819) B1174819
theorem B7038737 : Blo 924580 7038737 := bstep (se 2 (by rfl) ⟨2639526, by rfl⟩ : syracuseStep 7038737 = 5279053) B5279053
theorem B1042231 : Blo 924580 1042231 := bstep (se 1 (by rfl) ⟨781673, by rfl⟩ : syracuseStep 1042231 = 1563347) B1563347
theorem B1566553 : Blo 924580 1566553 := bstep (se 2 (by rfl) ⟨587457, by rfl⟩ : syracuseStep 1566553 = 1174915) B1174915
theorem B3008477 : Blo 924580 3008477 := bstep (se 3 (by rfl) ⟨564089, by rfl⟩ : syracuseStep 3008477 = 1128179) B1128179
theorem B1042411 : Blo 924580 1042411 := bstep (se 1 (by rfl) ⟨781808, by rfl⟩ : syracuseStep 1042411 = 1563617) B1563617
theorem B1042519 : Blo 924580 1042519 := bstep (se 1 (by rfl) ⟨781889, by rfl⟩ : syracuseStep 1042519 = 1563779) B1563779
theorem B3958915 : Blo 924580 3958915 := bstep (se 1 (by rfl) ⟨2969186, by rfl⟩ : syracuseStep 3958915 = 5938373) B5938373
theorem B3336385 : Blo 924580 3336385 := bstep (se 2 (by rfl) ⟨1251144, by rfl⟩ : syracuseStep 3336385 = 2502289) B2502289
theorem B1042699 : Blo 924580 1042699 := bstep (se 1 (by rfl) ⟨782024, by rfl⟩ : syracuseStep 1042699 = 1564049) B1564049
theorem B5269805 : Blo 924580 5269805 := bstep (se 3 (by rfl) ⟨988088, by rfl⟩ : syracuseStep 5269805 = 1976177) B1976177
theorem B1173847 : Blo 924580 1173847 := bstep (se 1 (by rfl) ⟨880385, by rfl⟩ : syracuseStep 1173847 = 1760771) B1760771
theorem B1042807 : Blo 924580 1042807 := bstep (se 1 (by rfl) ⟨782105, by rfl⟩ : syracuseStep 1042807 = 1564211) B1564211
theorem B5925251 : Blo 924580 5925251 := bstep (se 1 (by rfl) ⟨4443938, by rfl⟩ : syracuseStep 5925251 = 8887877) B8887877
theorem B1042987 : Blo 924580 1042987 := bstep (se 1 (by rfl) ⟨782240, by rfl⟩ : syracuseStep 1042987 = 1564481) B1564481
theorem B1043095 : Blo 924580 1043095 := bstep (se 1 (by rfl) ⟨782321, by rfl⟩ : syracuseStep 1043095 = 1564643) B1564643
theorem B1043275 : Blo 924580 1043275 := bstep (se 1 (by rfl) ⟨782456, by rfl⟩ : syracuseStep 1043275 = 1564913) B1564913
theorem B1043383 : Blo 924580 1043383 := bstep (se 1 (by rfl) ⟨782537, by rfl⟩ : syracuseStep 1043383 = 1565075) B1565075
theorem B2223065 : Blo 924580 2223065 := bstep (se 2 (by rfl) ⟨833649, by rfl⟩ : syracuseStep 2223065 = 1667299) B1667299
theorem B3959873 : Blo 924580 3959873 := bstep (se 2 (by rfl) ⟨1484952, by rfl⟩ : syracuseStep 3959873 = 2969905) B2969905
theorem B28568645 : Blo 924580 28568645 := bstep (se 4 (by rfl) ⟨2678310, by rfl⟩ : syracuseStep 28568645 = 5356621) B5356621
theorem B1043563 : Blo 924580 1043563 := bstep (se 1 (by rfl) ⟨782672, by rfl⟩ : syracuseStep 1043563 = 1565345) B1565345
theorem B1043671 : Blo 924580 1043671 := bstep (se 1 (by rfl) ⟨782753, by rfl⟩ : syracuseStep 1043671 = 1565507) B1565507
theorem B1043851 : Blo 924580 1043851 := bstep (se 1 (by rfl) ⟨782888, by rfl⟩ : syracuseStep 1043851 = 1565777) B1565777
theorem B7499213 : Blo 924580 7499213 := bstep (se 3 (by rfl) ⟨1406102, by rfl⟩ : syracuseStep 7499213 = 2812205) B2812205
theorem B1043959 : Blo 924580 1043959 := bstep (se 1 (by rfl) ⟨782969, by rfl⟩ : syracuseStep 1043959 = 1565939) B1565939
theorem B8449601 : Blo 924580 8449601 := bstep (se 2 (by rfl) ⟨3168600, by rfl⟩ : syracuseStep 8449601 = 6337201) B6337201
theorem B1044139 : Blo 924580 1044139 := bstep (se 1 (by rfl) ⟨783104, by rfl⟩ : syracuseStep 1044139 = 1566209) B1566209
theorem B1044247 : Blo 924580 1044247 := bstep (se 1 (by rfl) ⟨783185, by rfl⟩ : syracuseStep 1044247 = 1566371) B1566371
theorem B1044427 : Blo 924580 1044427 := bstep (se 1 (by rfl) ⟨783320, by rfl⟩ : syracuseStep 1044427 = 1566641) B1566641
theorem B4222979 : Blo 924580 4222979 := bstep (se 1 (by rfl) ⟨3167234, by rfl⟩ : syracuseStep 4222979 = 6334469) B6334469
theorem B1044535 : Blo 924580 1044535 := bstep (se 1 (by rfl) ⟨783401, by rfl⟩ : syracuseStep 1044535 = 1566803) B1566803
theorem B6025367 : Blo 924580 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B4682285 : Blo 924580 4682285 := bstep (se 3 (by rfl) ⟨877928, by rfl⟩ : syracuseStep 4682285 = 1755857) B1755857
theorem B3961547 : Blo 924580 3961547 := bstep (se 1 (by rfl) ⟨2971160, by rfl⟩ : syracuseStep 3961547 = 5942321) B5942321
theorem B3339139 : Blo 924580 3339139 := bstep (se 1 (by rfl) ⟨2504354, by rfl⟩ : syracuseStep 3339139 = 5008709) B5008709
theorem B1668107 : Blo 924580 1668107 := bstep (se 1 (by rfl) ⟨1251080, by rfl⟩ : syracuseStep 1668107 = 2502161) B2502161
theorem B4060205 : Blo 924580 4060205 := bstep (se 3 (by rfl) ⟨761288, by rfl⟩ : syracuseStep 4060205 = 1522577) B1522577
theorem B3175499 : Blo 924580 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B4289885 : Blo 924580 4289885 := bstep (se 3 (by rfl) ⟨804353, by rfl⟩ : syracuseStep 4289885 = 1608707) B1608707
theorem B1504727 : Blo 924580 1504727 := bstep (se 1 (by rfl) ⟨1128545, by rfl⟩ : syracuseStep 1504727 = 2257091) B2257091
theorem B7042625 : Blo 924580 7042625 := bstep (se 2 (by rfl) ⟨2640984, by rfl⟩ : syracuseStep 7042625 = 5281969) B5281969
theorem B5273495 : Blo 924580 5273495 := bstep (se 1 (by rfl) ⟨3955121, by rfl⟩ : syracuseStep 5273495 = 7910243) B7910243
theorem B1669015 : Blo 924580 1669015 := bstep (se 1 (by rfl) ⟨1251761, by rfl⟩ : syracuseStep 1669015 = 2503523) B2503523
theorem B2226199 : Blo 924580 2226199 := bstep (se 1 (by rfl) ⟨1669649, by rfl⟩ : syracuseStep 2226199 = 3339299) B3339299
theorem B1112215 : Blo 924580 1112215 := bstep (se 1 (by rfl) ⟨834161, by rfl⟩ : syracuseStep 1112215 = 1668323) B1668323
theorem B5634625 : Blo 924580 5634625 := bstep (se 2 (by rfl) ⟨2112984, by rfl⟩ : syracuseStep 5634625 = 4225969) B4225969
theorem B5569175 : Blo 924580 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B6683609 : Blo 924580 6683609 := bstep (se 2 (by rfl) ⟨2506353, by rfl⟩ : syracuseStep 6683609 = 5012707) B5012707
theorem B4750609 : Blo 924580 4750609 := bstep (se 2 (by rfl) ⟨1781478, by rfl⟩ : syracuseStep 4750609 = 3562957) B3562957
theorem B3964211 : Blo 924580 3964211 := bstep (se 1 (by rfl) ⟨2973158, by rfl⟩ : syracuseStep 3964211 = 5946317) B5946317
theorem B1113431 : Blo 924580 1113431 := bstep (se 1 (by rfl) ⟨835073, by rfl⟩ : syracuseStep 1113431 = 1670147) B1670147
theorem B7044569 : Blo 924580 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B7503491 : Blo 924580 7503491 := bstep (se 1 (by rfl) ⟨5627618, by rfl⟩ : syracuseStep 7503491 = 11255237) B11255237
theorem B3014347 : Blo 924580 3014347 := bstep (se 1 (by rfl) ⟨2260760, by rfl⟩ : syracuseStep 3014347 = 4521521) B4521521
theorem B2817995 : Blo 924580 2817995 := bstep (se 1 (by rfl) ⟨2113496, by rfl⟩ : syracuseStep 2817995 = 4226993) B4226993
theorem B2818091 : Blo 924580 2818091 := bstep (se 1 (by rfl) ⟨2113568, by rfl⟩ : syracuseStep 2818091 = 4227137) B4227137
theorem B1507513 : Blo 924580 1507513 := bstep (se 2 (by rfl) ⟨565317, by rfl⟩ : syracuseStep 1507513 = 1130635) B1130635
theorem B7143713 : Blo 924580 7143713 := bstep (se 2 (by rfl) ⟨2678892, by rfl⟩ : syracuseStep 7143713 = 5357785) B5357785
theorem B5275955 : Blo 924580 5275955 := bstep (se 1 (by rfl) ⟨3956966, by rfl⟩ : syracuseStep 5275955 = 7913933) B7913933
theorem B3342727 : Blo 924580 3342727 := bstep (se 1 (by rfl) ⟨2507045, by rfl⟩ : syracuseStep 3342727 = 5014091) B5014091
theorem B2819357 : Blo 924580 2819357 := bstep (se 3 (by rfl) ⟨528629, by rfl⟩ : syracuseStep 2819357 = 1057259) B1057259
theorem B4687307 : Blo 924580 4687307 := bstep (se 1 (by rfl) ⟨3515480, by rfl⟩ : syracuseStep 4687307 = 7030961) B7030961
theorem B22808141 : Blo 924580 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B4458185 : Blo 924580 4458185 := bstep (se 2 (by rfl) ⟨1671819, by rfl⟩ : syracuseStep 4458185 = 3343639) B3343639
theorem B5277413 : Blo 924580 5277413 := bstep (se 4 (by rfl) ⟨494757, by rfl⟩ : syracuseStep 5277413 = 989515) B989515
theorem B4687631 : Blo 924580 4687631 := bstep (se 1 (by rfl) ⟨3515723, by rfl⟩ : syracuseStep 4687631 = 7031447) B7031447
theorem B1410859 : Blo 924580 1410859 := bstep (se 1 (by rfl) ⟨1058144, by rfl⟩ : syracuseStep 1410859 = 2116289) B2116289
theorem B2230217 : Blo 924580 2230217 := bstep (se 2 (by rfl) ⟨836331, by rfl⟩ : syracuseStep 2230217 = 1672663) B1672663
theorem B33785869 : Blo 924580 33785869 := bstep (se 3 (by rfl) ⟨6334850, by rfl⟩ : syracuseStep 33785869 = 12669701) B12669701
theorem B5277869 : Blo 924580 5277869 := bstep (se 3 (by rfl) ⟨989600, by rfl⟩ : syracuseStep 5277869 = 1979201) B1979201
theorem B7146103 : Blo 924580 7146103 := bstep (se 1 (by rfl) ⟨5359577, by rfl⟩ : syracuseStep 7146103 = 10719155) B10719155
theorem B1411771 : Blo 924580 1411771 := bstep (se 1 (by rfl) ⟨1058828, by rfl⟩ : syracuseStep 1411771 = 2117657) B2117657
theorem B5278553 : Blo 924580 5278553 := bstep (se 2 (by rfl) ⟨1979457, by rfl⟩ : syracuseStep 5278553 = 3958915) B3958915
theorem B4689089 : Blo 924580 4689089 := bstep (se 2 (by rfl) ⟨1758408, by rfl⟩ : syracuseStep 4689089 = 3516817) B3516817
theorem B3346361 : Blo 924580 3346361 := bstep (se 2 (by rfl) ⟨1254885, by rfl⟩ : syracuseStep 3346361 = 2509771) B2509771
theorem B4690385 : Blo 924580 4690385 := bstep (se 2 (by rfl) ⟨1758894, by rfl⟩ : syracuseStep 4690385 = 3517789) B3517789
theorem B3510985 : Blo 924580 3510985 := bstep (se 2 (by rfl) ⟨1316619, by rfl⟩ : syracuseStep 3510985 = 2633239) B2633239
theorem B9999119 : Blo 924580 9999119 := bstep (se 1 (by rfl) ⟨7499339, by rfl⟩ : syracuseStep 9999119 = 14998679) B14998679
theorem B60036227 : Blo 924580 60036227 := bstep (se 1 (by rfl) ⟨45027170, by rfl⟩ : syracuseStep 60036227 = 90054341) B90054341
theorem B4461875 : Blo 924580 4461875 := bstep (se 1 (by rfl) ⟨3346406, by rfl⟩ : syracuseStep 4461875 = 6692813) B6692813
theorem B4462199 : Blo 924580 4462199 := bstep (se 1 (by rfl) ⟨3346649, by rfl⟩ : syracuseStep 4462199 = 6693299) B6693299
theorem B8918707 : Blo 924580 8918707 := bstep (se 1 (by rfl) ⟨6689030, by rfl⟩ : syracuseStep 8918707 = 13378061) B13378061
theorem B1316665 : Blo 924580 1316665 := bstep (se 2 (by rfl) ⟨493749, by rfl⟩ : syracuseStep 1316665 = 987499) B987499
theorem B10000331 : Blo 924580 10000331 := bstep (se 1 (by rfl) ⟨7500248, by rfl⟩ : syracuseStep 10000331 = 15000497) B15000497
theorem B1317007 : Blo 924580 1317007 := bstep (se 1 (by rfl) ⟨987755, by rfl⟩ : syracuseStep 1317007 = 1975511) B1975511
theorem B1481095 : Blo 924580 1481095 := bstep (se 1 (by rfl) ⟨1110821, by rfl⟩ : syracuseStep 1481095 = 2221643) B2221643
theorem B4692491 : Blo 924580 4692491 := bstep (se 1 (by rfl) ⟨3519368, by rfl⟩ : syracuseStep 4692491 = 7038737) B7038737
theorem B2005651 : Blo 924580 2005651 := bstep (se 1 (by rfl) ⟨1504238, by rfl⟩ : syracuseStep 2005651 = 3008477) B3008477
theorem B4692653 : Blo 924580 4692653 := bstep (se 3 (by rfl) ⟨879872, by rfl⟩ : syracuseStep 4692653 = 1759745) B1759745
theorem B13703897 : Blo 924580 13703897 := bstep (se 2 (by rfl) ⟨5138961, by rfl⟩ : syracuseStep 13703897 = 10277923) B10277923
theorem B11279179 : Blo 924580 11279179 := bstep (se 1 (by rfl) ⟨8459384, by rfl⟩ : syracuseStep 11279179 = 16918769) B16918769
theorem B3513203 : Blo 924580 3513203 := bstep (se 1 (by rfl) ⟨2634902, by rfl⟩ : syracuseStep 3513203 = 5269805) B5269805
theorem B924603 : Blo 924580 924603 := bstep (se 1 (by rfl) ⟨693452, by rfl⟩ : syracuseStep 924603 = 1386905) B1386905
theorem B990139 : Blo 924580 990139 := bstep (se 1 (by rfl) ⟨742604, by rfl⟩ : syracuseStep 990139 = 1485209) B1485209
theorem B924679 : Blo 924580 924679 := bstep (se 1 (by rfl) ⟨693509, by rfl⟩ : syracuseStep 924679 = 1387019) B1387019
theorem B924687 : Blo 924580 924687 := bstep (se 1 (by rfl) ⟨693515, by rfl⟩ : syracuseStep 924687 = 1387031) B1387031
theorem B924731 : Blo 924580 924731 := bstep (se 1 (by rfl) ⟨693548, by rfl⟩ : syracuseStep 924731 = 1387097) B1387097
theorem B14851133 : Blo 924580 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B924807 : Blo 924580 924807 := bstep (se 1 (by rfl) ⟨693605, by rfl⟩ : syracuseStep 924807 = 1387211) B1387211
theorem B924815 : Blo 924580 924815 := bstep (se 1 (by rfl) ⟨693611, by rfl⟩ : syracuseStep 924815 = 1387223) B1387223
theorem B924859 : Blo 924580 924859 := bstep (se 1 (by rfl) ⟨693644, by rfl⟩ : syracuseStep 924859 = 1387289) B1387289
theorem B1318135 : Blo 924580 1318135 := bstep (se 1 (by rfl) ⟨988601, by rfl⟩ : syracuseStep 1318135 = 1977203) B1977203
theorem B924935 : Blo 924580 924935 := bstep (se 1 (by rfl) ⟨693701, by rfl⟩ : syracuseStep 924935 = 1387403) B1387403
theorem B924943 : Blo 924580 924943 := bstep (se 1 (by rfl) ⟨693707, by rfl⟩ : syracuseStep 924943 = 1387415) B1387415
theorem B924987 : Blo 924580 924987 := bstep (se 1 (by rfl) ⟨693740, by rfl⟩ : syracuseStep 924987 = 1387481) B1387481
theorem B19045763 : Blo 924580 19045763 := bstep (se 1 (by rfl) ⟨14284322, by rfl⟩ : syracuseStep 19045763 = 28568645) B28568645
theorem B925063 : Blo 924580 925063 := bstep (se 1 (by rfl) ⟨693797, by rfl⟩ : syracuseStep 925063 = 1387595) B1387595
theorem B925071 : Blo 924580 925071 := bstep (se 1 (by rfl) ⟨693803, by rfl⟩ : syracuseStep 925071 = 1387607) B1387607
theorem B925115 : Blo 924580 925115 := bstep (se 1 (by rfl) ⟨693836, by rfl⟩ : syracuseStep 925115 = 1387673) B1387673
theorem B925191 : Blo 924580 925191 := bstep (se 1 (by rfl) ⟨693893, by rfl⟩ : syracuseStep 925191 = 1387787) B1387787
theorem B925199 : Blo 924580 925199 := bstep (se 1 (by rfl) ⟨693899, by rfl⟩ : syracuseStep 925199 = 1387799) B1387799
theorem B925243 : Blo 924580 925243 := bstep (se 1 (by rfl) ⟨693932, by rfl⟩ : syracuseStep 925243 = 1387865) B1387865
theorem B925319 : Blo 924580 925319 := bstep (se 1 (by rfl) ⟨693989, by rfl⟩ : syracuseStep 925319 = 1387979) B1387979
theorem B925327 : Blo 924580 925327 := bstep (se 1 (by rfl) ⟨693995, by rfl⟩ : syracuseStep 925327 = 1387991) B1387991
theorem B925371 : Blo 924580 925371 := bstep (se 1 (by rfl) ⟨694028, by rfl⟩ : syracuseStep 925371 = 1388057) B1388057
theorem B925447 : Blo 924580 925447 := bstep (se 1 (by rfl) ⟨694085, by rfl⟩ : syracuseStep 925447 = 1388171) B1388171
theorem B925455 : Blo 924580 925455 := bstep (se 1 (by rfl) ⟨694091, by rfl⟩ : syracuseStep 925455 = 1388183) B1388183
theorem B3120929 : Blo 924580 3120929 := bstep (se 2 (by rfl) ⟨1170348, by rfl⟩ : syracuseStep 3120929 = 2340697) B2340697
theorem B925499 : Blo 924580 925499 := bstep (se 1 (by rfl) ⟨694124, by rfl⟩ : syracuseStep 925499 = 1388249) B1388249
theorem B925575 : Blo 924580 925575 := bstep (se 1 (by rfl) ⟨694181, by rfl⟩ : syracuseStep 925575 = 1388363) B1388363
theorem B925583 : Blo 924580 925583 := bstep (se 1 (by rfl) ⟨694187, by rfl⟩ : syracuseStep 925583 = 1388375) B1388375
theorem B925627 : Blo 924580 925627 := bstep (se 1 (by rfl) ⟨694220, by rfl⟩ : syracuseStep 925627 = 1388441) B1388441
theorem B925703 : Blo 924580 925703 := bstep (se 1 (by rfl) ⟨694277, by rfl⟩ : syracuseStep 925703 = 1388555) B1388555
theorem B925711 : Blo 924580 925711 := bstep (se 1 (by rfl) ⟨694283, by rfl⟩ : syracuseStep 925711 = 1388567) B1388567
theorem B160702517 : Blo 924580 160702517 := bstep (se 5 (by rfl) ⟨7532930, by rfl⟩ : syracuseStep 160702517 = 15065861) B15065861
theorem B925755 : Blo 924580 925755 := bstep (se 1 (by rfl) ⟨694316, by rfl⟩ : syracuseStep 925755 = 1388633) B1388633
theorem B925831 : Blo 924580 925831 := bstep (se 1 (by rfl) ⟨694373, by rfl⟩ : syracuseStep 925831 = 1388747) B1388747
theorem B925839 : Blo 924580 925839 := bstep (se 1 (by rfl) ⟨694379, by rfl⟩ : syracuseStep 925839 = 1388759) B1388759
theorem B925883 : Blo 924580 925883 := bstep (se 1 (by rfl) ⟨694412, by rfl⟩ : syracuseStep 925883 = 1388825) B1388825
theorem B1482953 : Blo 924580 1482953 := bstep (se 2 (by rfl) ⟨556107, by rfl⟩ : syracuseStep 1482953 = 1112215) B1112215
theorem B4694273 : Blo 924580 4694273 := bstep (se 2 (by rfl) ⟨1760352, by rfl⟩ : syracuseStep 4694273 = 3520705) B3520705
theorem B925959 : Blo 924580 925959 := bstep (se 1 (by rfl) ⟨694469, by rfl⟩ : syracuseStep 925959 = 1388939) B1388939
theorem B925967 : Blo 924580 925967 := bstep (se 1 (by rfl) ⟨694475, by rfl⟩ : syracuseStep 925967 = 1388951) B1388951
theorem B1253675 : Blo 924580 1253675 := bstep (se 1 (by rfl) ⟨940256, by rfl⟩ : syracuseStep 1253675 = 1880513) B1880513
theorem B926011 : Blo 924580 926011 := bstep (se 1 (by rfl) ⟨694508, by rfl⟩ : syracuseStep 926011 = 1389017) B1389017
theorem B3121523 : Blo 924580 3121523 := bstep (se 1 (by rfl) ⟨2341142, by rfl⟩ : syracuseStep 3121523 = 4682285) B4682285
theorem B926087 : Blo 924580 926087 := bstep (se 1 (by rfl) ⟨694565, by rfl⟩ : syracuseStep 926087 = 1389131) B1389131
theorem B926095 : Blo 924580 926095 := bstep (se 1 (by rfl) ⟨694571, by rfl⟩ : syracuseStep 926095 = 1389143) B1389143
theorem B926139 : Blo 924580 926139 := bstep (se 1 (by rfl) ⟨694604, by rfl⟩ : syracuseStep 926139 = 1389209) B1389209
theorem B926215 : Blo 924580 926215 := bstep (se 1 (by rfl) ⟨694661, by rfl⟩ : syracuseStep 926215 = 1389323) B1389323
theorem B926223 : Blo 924580 926223 := bstep (se 1 (by rfl) ⟨694667, by rfl⟩ : syracuseStep 926223 = 1389335) B1389335
theorem B1974827 : Blo 924580 1974827 := bstep (se 1 (by rfl) ⟨1481120, by rfl⟩ : syracuseStep 1974827 = 2962241) B2962241
theorem B926267 : Blo 924580 926267 := bstep (se 1 (by rfl) ⟨694700, by rfl⟩ : syracuseStep 926267 = 1389401) B1389401
theorem B7905869 : Blo 924580 7905869 := bstep (se 3 (by rfl) ⟨1482350, by rfl⟩ : syracuseStep 7905869 = 2964701) B2964701
theorem B926343 : Blo 924580 926343 := bstep (se 1 (by rfl) ⟨694757, by rfl⟩ : syracuseStep 926343 = 1389515) B1389515
theorem B926351 : Blo 924580 926351 := bstep (se 1 (by rfl) ⟨694763, by rfl⟩ : syracuseStep 926351 = 1389527) B1389527
theorem B926395 : Blo 924580 926395 := bstep (se 1 (by rfl) ⟨694796, by rfl⟩ : syracuseStep 926395 = 1389593) B1389593
theorem B7512833 : Blo 924580 7512833 := bstep (se 2 (by rfl) ⟨2817312, by rfl⟩ : syracuseStep 7512833 = 5634625) B5634625
theorem B926471 : Blo 924580 926471 := bstep (se 1 (by rfl) ⟨694853, by rfl⟩ : syracuseStep 926471 = 1389707) B1389707
theorem B1254151 : Blo 924580 1254151 := bstep (se 1 (by rfl) ⟨940613, by rfl⟩ : syracuseStep 1254151 = 1881227) B1881227
theorem B926479 : Blo 924580 926479 := bstep (se 1 (by rfl) ⟨694859, by rfl⟩ : syracuseStep 926479 = 1389719) B1389719
theorem B10560293 : Blo 924580 10560293 := bstep (se 4 (by rfl) ⟨990027, by rfl⟩ : syracuseStep 10560293 = 1980055) B1980055
theorem B926523 : Blo 924580 926523 := bstep (se 1 (by rfl) ⟨694892, by rfl⟩ : syracuseStep 926523 = 1389785) B1389785
theorem B926599 : Blo 924580 926599 := bstep (se 1 (by rfl) ⟨694949, by rfl⟩ : syracuseStep 926599 = 1389899) B1389899
theorem B926607 : Blo 924580 926607 := bstep (se 1 (by rfl) ⟨694955, by rfl⟩ : syracuseStep 926607 = 1389911) B1389911
theorem B2859923 : Blo 924580 2859923 := bstep (se 1 (by rfl) ⟨2144942, by rfl⟩ : syracuseStep 2859923 = 4289885) B4289885
theorem B926651 : Blo 924580 926651 := bstep (se 1 (by rfl) ⟨694988, by rfl⟩ : syracuseStep 926651 = 1389977) B1389977
theorem B3515345 : Blo 924580 3515345 := bstep (se 2 (by rfl) ⟨1318254, by rfl⟩ : syracuseStep 3515345 = 2636509) B2636509
theorem B926727 : Blo 924580 926727 := bstep (se 1 (by rfl) ⟨695045, by rfl⟩ : syracuseStep 926727 = 1390091) B1390091
theorem B926735 : Blo 924580 926735 := bstep (se 1 (by rfl) ⟨695051, by rfl⟩ : syracuseStep 926735 = 1390103) B1390103
theorem B4695083 : Blo 924580 4695083 := bstep (se 1 (by rfl) ⟨3521312, by rfl⟩ : syracuseStep 4695083 = 7042625) B7042625
theorem B926779 : Blo 924580 926779 := bstep (se 1 (by rfl) ⟨695084, by rfl⟩ : syracuseStep 926779 = 1390169) B1390169
theorem B926855 : Blo 924580 926855 := bstep (se 1 (by rfl) ⟨695141, by rfl⟩ : syracuseStep 926855 = 1390283) B1390283
theorem B926863 : Blo 924580 926863 := bstep (se 1 (by rfl) ⟨695147, by rfl⟩ : syracuseStep 926863 = 1390295) B1390295
theorem B926907 : Blo 924580 926907 := bstep (se 1 (by rfl) ⟨695180, by rfl⟩ : syracuseStep 926907 = 1390361) B1390361
theorem B926983 : Blo 924580 926983 := bstep (se 1 (by rfl) ⟨695237, by rfl⟩ : syracuseStep 926983 = 1390475) B1390475
theorem B3515663 : Blo 924580 3515663 := bstep (se 1 (by rfl) ⟨2636747, by rfl⟩ : syracuseStep 3515663 = 5273495) B5273495
theorem B926991 : Blo 924580 926991 := bstep (se 1 (by rfl) ⟨695243, by rfl⟩ : syracuseStep 926991 = 1390487) B1390487
theorem B927035 : Blo 924580 927035 := bstep (se 1 (by rfl) ⟨695276, by rfl⟩ : syracuseStep 927035 = 1390553) B1390553
theorem B927111 : Blo 924580 927111 := bstep (se 1 (by rfl) ⟨695333, by rfl⟩ : syracuseStep 927111 = 1390667) B1390667
theorem B927119 : Blo 924580 927119 := bstep (se 1 (by rfl) ⟨695339, by rfl⟩ : syracuseStep 927119 = 1390679) B1390679
theorem B927163 : Blo 924580 927163 := bstep (se 1 (by rfl) ⟨695372, by rfl⟩ : syracuseStep 927163 = 1390745) B1390745
theorem B927239 : Blo 924580 927239 := bstep (se 1 (by rfl) ⟨695429, by rfl⟩ : syracuseStep 927239 = 1390859) B1390859
theorem B927247 : Blo 924580 927247 := bstep (se 1 (by rfl) ⟨695435, by rfl⟩ : syracuseStep 927247 = 1390871) B1390871
theorem B927291 : Blo 924580 927291 := bstep (se 1 (by rfl) ⟨695468, by rfl⟩ : syracuseStep 927291 = 1390937) B1390937
theorem B927367 : Blo 924580 927367 := bstep (se 1 (by rfl) ⟨695525, by rfl⟩ : syracuseStep 927367 = 1391051) B1391051
theorem B927375 : Blo 924580 927375 := bstep (se 1 (by rfl) ⟨695531, by rfl⟩ : syracuseStep 927375 = 1391063) B1391063
theorem B927419 : Blo 924580 927419 := bstep (se 1 (by rfl) ⟨695564, by rfl⟩ : syracuseStep 927419 = 1391129) B1391129
theorem B6334145 : Blo 924580 6334145 := bstep (se 2 (by rfl) ⟨2375304, by rfl⟩ : syracuseStep 6334145 = 4750609) B4750609
theorem B927495 : Blo 924580 927495 := bstep (se 1 (by rfl) ⟨695621, by rfl⟩ : syracuseStep 927495 = 1391243) B1391243
theorem B927503 : Blo 924580 927503 := bstep (se 1 (by rfl) ⟨695627, by rfl⟩ : syracuseStep 927503 = 1391255) B1391255
theorem B927547 : Blo 924580 927547 := bstep (se 1 (by rfl) ⟨695660, by rfl⟩ : syracuseStep 927547 = 1391321) B1391321
theorem B1320823 : Blo 924580 1320823 := bstep (se 1 (by rfl) ⟨990617, by rfl⟩ : syracuseStep 1320823 = 1981235) B1981235
theorem B927623 : Blo 924580 927623 := bstep (se 1 (by rfl) ⟨695717, by rfl⟩ : syracuseStep 927623 = 1391435) B1391435
theorem B927631 : Blo 924580 927631 := bstep (se 1 (by rfl) ⟨695723, by rfl⟩ : syracuseStep 927631 = 1391447) B1391447
theorem B927675 : Blo 924580 927675 := bstep (se 1 (by rfl) ⟨695756, by rfl⟩ : syracuseStep 927675 = 1391513) B1391513
theorem B927751 : Blo 924580 927751 := bstep (se 1 (by rfl) ⟨695813, by rfl⟩ : syracuseStep 927751 = 1391627) B1391627
theorem B927759 : Blo 924580 927759 := bstep (se 1 (by rfl) ⟨695819, by rfl⟩ : syracuseStep 927759 = 1391639) B1391639
theorem B5351453 : Blo 924580 5351453 := bstep (se 3 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 5351453 = 2006795) B2006795
theorem B1583147 : Blo 924580 1583147 := bstep (se 1 (by rfl) ⟨1187360, by rfl⟩ : syracuseStep 1583147 = 2374721) B2374721
theorem B927803 : Blo 924580 927803 := bstep (se 1 (by rfl) ⟨695852, by rfl⟩ : syracuseStep 927803 = 1391705) B1391705
theorem B927879 : Blo 924580 927879 := bstep (se 1 (by rfl) ⟨695909, by rfl⟩ : syracuseStep 927879 = 1391819) B1391819
theorem B927887 : Blo 924580 927887 := bstep (se 1 (by rfl) ⟨695915, by rfl⟩ : syracuseStep 927887 = 1391831) B1391831
theorem B927931 : Blo 924580 927931 := bstep (se 1 (by rfl) ⟨695948, by rfl⟩ : syracuseStep 927931 = 1391897) B1391897
theorem B928007 : Blo 924580 928007 := bstep (se 1 (by rfl) ⟨696005, by rfl⟩ : syracuseStep 928007 = 1392011) B1392011
theorem B928015 : Blo 924580 928015 := bstep (se 1 (by rfl) ⟨696011, by rfl⟩ : syracuseStep 928015 = 1392023) B1392023
theorem B4696379 : Blo 924580 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B928059 : Blo 924580 928059 := bstep (se 1 (by rfl) ⟨696044, by rfl⟩ : syracuseStep 928059 = 1392089) B1392089
theorem B1386887 : Blo 924580 1386887 := bstep (se 1 (by rfl) ⟨1040165, by rfl⟩ : syracuseStep 1386887 = 2080331) B2080331
theorem B928135 : Blo 924580 928135 := bstep (se 1 (by rfl) ⟨696101, by rfl⟩ : syracuseStep 928135 = 1392203) B1392203
theorem B928143 : Blo 924580 928143 := bstep (se 1 (by rfl) ⟨696107, by rfl⟩ : syracuseStep 928143 = 1392215) B1392215
theorem B1386923 : Blo 924580 1386923 := bstep (se 1 (by rfl) ⟨1040192, by rfl⟩ : syracuseStep 1386923 = 2080385) B2080385
theorem B928187 : Blo 924580 928187 := bstep (se 1 (by rfl) ⟨696140, by rfl⟩ : syracuseStep 928187 = 1392281) B1392281
theorem B1386953 : Blo 924580 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B4696541 : Blo 924580 4696541 := bstep (se 3 (by rfl) ⟨880601, by rfl⟩ : syracuseStep 4696541 = 1761203) B1761203
theorem B928263 : Blo 924580 928263 := bstep (se 1 (by rfl) ⟨696197, by rfl⟩ : syracuseStep 928263 = 1392395) B1392395
theorem B928271 : Blo 924580 928271 := bstep (se 1 (by rfl) ⟨696203, by rfl⟩ : syracuseStep 928271 = 1392407) B1392407
theorem B7514653 : Blo 924580 7514653 := bstep (se 3 (by rfl) ⟨1408997, by rfl⟩ : syracuseStep 7514653 = 2817995) B2817995
theorem B1387067 : Blo 924580 1387067 := bstep (se 1 (by rfl) ⟨1040300, by rfl⟩ : syracuseStep 1387067 = 2080601) B2080601
theorem B928315 : Blo 924580 928315 := bstep (se 1 (by rfl) ⟨696236, by rfl⟩ : syracuseStep 928315 = 1392473) B1392473
theorem B1387127 : Blo 924580 1387127 := bstep (se 1 (by rfl) ⟨1040345, by rfl⟩ : syracuseStep 1387127 = 2080691) B2080691
theorem B11414135 : Blo 924580 11414135 := bstep (se 1 (by rfl) ⟨8560601, by rfl⟩ : syracuseStep 11414135 = 17121203) B17121203
theorem B928391 : Blo 924580 928391 := bstep (se 1 (by rfl) ⟨696293, by rfl⟩ : syracuseStep 928391 = 1392587) B1392587
theorem B1387151 : Blo 924580 1387151 := bstep (se 1 (by rfl) ⟨1040363, by rfl⟩ : syracuseStep 1387151 = 2080727) B2080727
theorem B928399 : Blo 924580 928399 := bstep (se 1 (by rfl) ⟨696299, by rfl⟩ : syracuseStep 928399 = 1392599) B1392599
theorem B1321643 : Blo 924580 1321643 := bstep (se 1 (by rfl) ⟨991232, by rfl⟩ : syracuseStep 1321643 = 1982465) B1982465
theorem B1387193 : Blo 924580 1387193 := bstep (se 2 (by rfl) ⟨520197, by rfl⟩ : syracuseStep 1387193 = 1040395) B1040395
theorem B1485497 : Blo 924580 1485497 := bstep (se 2 (by rfl) ⟨557061, by rfl⟩ : syracuseStep 1485497 = 1114123) B1114123
theorem B928443 : Blo 924580 928443 := bstep (se 1 (by rfl) ⟨696332, by rfl⟩ : syracuseStep 928443 = 1392665) B1392665
theorem B1387271 : Blo 924580 1387271 := bstep (se 1 (by rfl) ⟨1040453, by rfl⟩ : syracuseStep 1387271 = 2080907) B2080907
theorem B928519 : Blo 924580 928519 := bstep (se 1 (by rfl) ⟨696389, by rfl⟩ : syracuseStep 928519 = 1392779) B1392779
theorem B928527 : Blo 924580 928527 := bstep (se 1 (by rfl) ⟨696395, by rfl⟩ : syracuseStep 928527 = 1392791) B1392791
theorem B4696865 : Blo 924580 4696865 := bstep (se 2 (by rfl) ⟨1761324, by rfl⟩ : syracuseStep 4696865 = 3522649) B3522649
theorem B1387307 : Blo 924580 1387307 := bstep (se 1 (by rfl) ⟨1040480, by rfl⟩ : syracuseStep 1387307 = 2080961) B2080961
theorem B928571 : Blo 924580 928571 := bstep (se 1 (by rfl) ⟨696428, by rfl⟩ : syracuseStep 928571 = 1392857) B1392857
theorem B1387337 : Blo 924580 1387337 := bstep (se 2 (by rfl) ⟨520251, by rfl⟩ : syracuseStep 1387337 = 1040503) B1040503
theorem B3124115 : Blo 924580 3124115 := bstep (se 1 (by rfl) ⟨2343086, by rfl⟩ : syracuseStep 3124115 = 4686173) B4686173
theorem B1387451 : Blo 924580 1387451 := bstep (se 1 (by rfl) ⟨1040588, by rfl⟩ : syracuseStep 1387451 = 2081177) B2081177
theorem B1387511 : Blo 924580 1387511 := bstep (se 1 (by rfl) ⟨1040633, by rfl⟩ : syracuseStep 1387511 = 2081267) B2081267
theorem B1387535 : Blo 924580 1387535 := bstep (se 1 (by rfl) ⟨1040651, by rfl⟩ : syracuseStep 1387535 = 2081303) B2081303
theorem B1387577 : Blo 924580 1387577 := bstep (se 2 (by rfl) ⟨520341, by rfl⟩ : syracuseStep 1387577 = 1040683) B1040683
theorem B16067645 : Blo 924580 16067645 := bstep (se 3 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 16067645 = 6025367) B6025367
theorem B1387655 : Blo 924580 1387655 := bstep (se 1 (by rfl) ⟨1040741, by rfl⟩ : syracuseStep 1387655 = 2081483) B2081483
theorem B1387691 : Blo 924580 1387691 := bstep (se 1 (by rfl) ⟨1040768, by rfl⟩ : syracuseStep 1387691 = 2081537) B2081537
theorem B1387721 : Blo 924580 1387721 := bstep (se 2 (by rfl) ⟨520395, by rfl⟩ : syracuseStep 1387721 = 1040791) B1040791
theorem B1387835 : Blo 924580 1387835 := bstep (se 1 (by rfl) ⟨1040876, by rfl⟩ : syracuseStep 1387835 = 2081753) B2081753
theorem B1387895 : Blo 924580 1387895 := bstep (se 1 (by rfl) ⟨1040921, by rfl⟩ : syracuseStep 1387895 = 2081843) B2081843
theorem B1387919 : Blo 924580 1387919 := bstep (se 1 (by rfl) ⟨1040939, by rfl⟩ : syracuseStep 1387919 = 2081879) B2081879
theorem B8891795 : Blo 924580 8891795 := bstep (se 1 (by rfl) ⟨6668846, by rfl⟩ : syracuseStep 8891795 = 13337693) B13337693
theorem B6335891 : Blo 924580 6335891 := bstep (se 1 (by rfl) ⟨4751918, by rfl⟩ : syracuseStep 6335891 = 9503837) B9503837
theorem B1387961 : Blo 924580 1387961 := bstep (se 2 (by rfl) ⟨520485, by rfl⟩ : syracuseStep 1387961 = 1040971) B1040971
theorem B1584569 : Blo 924580 1584569 := bstep (se 2 (by rfl) ⟨594213, by rfl⟩ : syracuseStep 1584569 = 1188427) B1188427
theorem B1388039 : Blo 924580 1388039 := bstep (se 1 (by rfl) ⟨1041029, by rfl⟩ : syracuseStep 1388039 = 2082059) B2082059
theorem B7024157 : Blo 924580 7024157 := bstep (se 3 (by rfl) ⟨1317029, by rfl⟩ : syracuseStep 7024157 = 2634059) B2634059
theorem B1388075 : Blo 924580 1388075 := bstep (se 1 (by rfl) ⟨1041056, by rfl⟩ : syracuseStep 1388075 = 2082113) B2082113
theorem B1388105 : Blo 924580 1388105 := bstep (se 2 (by rfl) ⟨520539, by rfl⟩ : syracuseStep 1388105 = 1041079) B1041079
theorem B1388219 : Blo 924580 1388219 := bstep (se 1 (by rfl) ⟨1041164, by rfl⟩ : syracuseStep 1388219 = 2082329) B2082329
theorem B4697837 : Blo 924580 4697837 := bstep (se 3 (by rfl) ⟨880844, by rfl⟩ : syracuseStep 4697837 = 1761689) B1761689
theorem B1388279 : Blo 924580 1388279 := bstep (se 1 (by rfl) ⟨1041209, by rfl⟩ : syracuseStep 1388279 = 2082419) B2082419
theorem B1388303 : Blo 924580 1388303 := bstep (se 1 (by rfl) ⟨1041227, by rfl⟩ : syracuseStep 1388303 = 2082455) B2082455
theorem B1388345 : Blo 924580 1388345 := bstep (se 2 (by rfl) ⟨520629, by rfl⟩ : syracuseStep 1388345 = 1041259) B1041259
theorem B15249221 : Blo 924580 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B1388423 : Blo 924580 1388423 := bstep (se 1 (by rfl) ⟨1041317, by rfl⟩ : syracuseStep 1388423 = 2082635) B2082635
theorem B1388459 : Blo 924580 1388459 := bstep (se 1 (by rfl) ⟨1041344, by rfl⟩ : syracuseStep 1388459 = 2082689) B2082689
theorem B1388489 : Blo 924580 1388489 := bstep (se 2 (by rfl) ⟨520683, by rfl⟩ : syracuseStep 1388489 = 1041367) B1041367
theorem B1388603 : Blo 924580 1388603 := bstep (se 1 (by rfl) ⟨1041452, by rfl⟩ : syracuseStep 1388603 = 2082905) B2082905
theorem B1388663 : Blo 924580 1388663 := bstep (se 1 (by rfl) ⟨1041497, by rfl⟩ : syracuseStep 1388663 = 2082995) B2082995
theorem B1388687 : Blo 924580 1388687 := bstep (se 1 (by rfl) ⟨1041515, by rfl⟩ : syracuseStep 1388687 = 2083031) B2083031
theorem B2502809 : Blo 924580 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B1388729 : Blo 924580 1388729 := bstep (se 2 (by rfl) ⟨520773, by rfl⟩ : syracuseStep 1388729 = 1041547) B1041547
theorem B1388807 : Blo 924580 1388807 := bstep (se 1 (by rfl) ⟨1041605, by rfl⟩ : syracuseStep 1388807 = 2083211) B2083211
theorem B3125519 : Blo 924580 3125519 := bstep (se 1 (by rfl) ⟨2344139, by rfl⟩ : syracuseStep 3125519 = 4688279) B4688279
theorem B3617057 : Blo 924580 3617057 := bstep (se 2 (by rfl) ⟨1356396, by rfl⟩ : syracuseStep 3617057 = 2712793) B2712793
theorem B1388843 : Blo 924580 1388843 := bstep (se 1 (by rfl) ⟨1041632, by rfl⟩ : syracuseStep 1388843 = 2083265) B2083265
theorem B2502971 : Blo 924580 2502971 := bstep (se 1 (by rfl) ⟨1877228, by rfl⟩ : syracuseStep 2502971 = 3754457) B3754457
theorem B1388873 : Blo 924580 1388873 := bstep (se 2 (by rfl) ⟨520827, by rfl⟩ : syracuseStep 1388873 = 1041655) B1041655
theorem B5288327 : Blo 924580 5288327 := bstep (se 1 (by rfl) ⟨3966245, by rfl⟩ : syracuseStep 5288327 = 7932491) B7932491
theorem B1388987 : Blo 924580 1388987 := bstep (se 1 (by rfl) ⟨1041740, by rfl⟩ : syracuseStep 1388987 = 2083481) B2083481
theorem B1978825 : Blo 924580 1978825 := bstep (se 2 (by rfl) ⟨742059, by rfl⟩ : syracuseStep 1978825 = 1484119) B1484119
theorem B1389047 : Blo 924580 1389047 := bstep (se 1 (by rfl) ⟨1041785, by rfl⟩ : syracuseStep 1389047 = 2083571) B2083571
theorem B1389071 : Blo 924580 1389071 := bstep (se 1 (by rfl) ⟨1041803, by rfl⟩ : syracuseStep 1389071 = 2083607) B2083607
theorem B4698647 : Blo 924580 4698647 := bstep (se 1 (by rfl) ⟨3523985, by rfl⟩ : syracuseStep 4698647 = 7047971) B7047971
theorem B3125789 : Blo 924580 3125789 := bstep (se 3 (by rfl) ⟨586085, by rfl⟩ : syracuseStep 3125789 = 1172171) B1172171
theorem B2109995 : Blo 924580 2109995 := bstep (se 1 (by rfl) ⟨1582496, by rfl⟩ : syracuseStep 2109995 = 3164993) B3164993
theorem B1389113 : Blo 924580 1389113 := bstep (se 2 (by rfl) ⟨520917, by rfl⟩ : syracuseStep 1389113 = 1041835) B1041835
theorem B1389191 : Blo 924580 1389191 := bstep (se 1 (by rfl) ⟨1041893, by rfl⟩ : syracuseStep 1389191 = 2083787) B2083787
theorem B1389227 : Blo 924580 1389227 := bstep (se 1 (by rfl) ⟨1041920, by rfl⟩ : syracuseStep 1389227 = 2083841) B2083841
theorem B1389257 : Blo 924580 1389257 := bstep (se 2 (by rfl) ⟨520971, by rfl⟩ : syracuseStep 1389257 = 1041943) B1041943
theorem B3519233 : Blo 924580 3519233 := bstep (se 2 (by rfl) ⟨1319712, by rfl⟩ : syracuseStep 3519233 = 2639425) B2639425
theorem B3519247 : Blo 924580 3519247 := bstep (se 1 (by rfl) ⟨2639435, by rfl⟩ : syracuseStep 3519247 = 5278871) B5278871
theorem B1389371 : Blo 924580 1389371 := bstep (se 1 (by rfl) ⟨1042028, by rfl⟩ : syracuseStep 1389371 = 2084057) B2084057
theorem B2503543 : Blo 924580 2503543 := bstep (se 1 (by rfl) ⟨1877657, by rfl⟩ : syracuseStep 2503543 = 3755315) B3755315
theorem B1389431 : Blo 924580 1389431 := bstep (se 1 (by rfl) ⟨1042073, by rfl⟩ : syracuseStep 1389431 = 2084147) B2084147
theorem B1389455 : Blo 924580 1389455 := bstep (se 1 (by rfl) ⟨1042091, by rfl⟩ : syracuseStep 1389455 = 2084183) B2084183
theorem B1389497 : Blo 924580 1389497 := bstep (se 2 (by rfl) ⟨521061, by rfl⟩ : syracuseStep 1389497 = 1042123) B1042123
theorem B2634697 : Blo 924580 2634697 := bstep (se 2 (by rfl) ⟨988011, by rfl⟩ : syracuseStep 2634697 = 1976023) B1976023
theorem B1389575 : Blo 924580 1389575 := bstep (se 1 (by rfl) ⟨1042181, by rfl⟩ : syracuseStep 1389575 = 2084363) B2084363
theorem B3814411 : Blo 924580 3814411 := bstep (se 1 (by rfl) ⟨2860808, by rfl⟩ : syracuseStep 3814411 = 5721617) B5721617
theorem B1389611 : Blo 924580 1389611 := bstep (se 1 (by rfl) ⟨1042208, by rfl⟩ : syracuseStep 1389611 = 2084417) B2084417
theorem B1782827 : Blo 924580 1782827 := bstep (se 1 (by rfl) ⟨1337120, by rfl⟩ : syracuseStep 1782827 = 2674241) B2674241
theorem B1389641 : Blo 924580 1389641 := bstep (se 2 (by rfl) ⟨521115, by rfl⟩ : syracuseStep 1389641 = 1042231) B1042231
theorem B4011095 : Blo 924580 4011095 := bstep (se 1 (by rfl) ⟨3008321, by rfl⟩ : syracuseStep 4011095 = 6016643) B6016643
theorem B1389755 : Blo 924580 1389755 := bstep (se 1 (by rfl) ⟨1042316, by rfl⟩ : syracuseStep 1389755 = 2084633) B2084633
theorem B1389815 : Blo 924580 1389815 := bstep (se 1 (by rfl) ⟨1042361, by rfl⟩ : syracuseStep 1389815 = 2084723) B2084723
theorem B1389839 : Blo 924580 1389839 := bstep (se 1 (by rfl) ⟨1042379, by rfl⟩ : syracuseStep 1389839 = 2084759) B2084759
theorem B2635051 : Blo 924580 2635051 := bstep (se 1 (by rfl) ⟨1976288, by rfl⟩ : syracuseStep 2635051 = 3952577) B3952577
theorem B1389881 : Blo 924580 1389881 := bstep (se 2 (by rfl) ⟨521205, by rfl⟩ : syracuseStep 1389881 = 1042411) B1042411
theorem B1389959 : Blo 924580 1389959 := bstep (se 1 (by rfl) ⟨1042469, by rfl⟩ : syracuseStep 1389959 = 2084939) B2084939
theorem B3749267 : Blo 924580 3749267 := bstep (se 1 (by rfl) ⟨2811950, by rfl⟩ : syracuseStep 3749267 = 5623901) B5623901
theorem B1389995 : Blo 924580 1389995 := bstep (se 1 (by rfl) ⟨1042496, by rfl⟩ : syracuseStep 1389995 = 2084993) B2084993
theorem B1390025 : Blo 924580 1390025 := bstep (se 2 (by rfl) ⟨521259, by rfl⟩ : syracuseStep 1390025 = 1042519) B1042519
theorem B2340353 : Blo 924580 2340353 := bstep (se 2 (by rfl) ⟨877632, by rfl⟩ : syracuseStep 2340353 = 1755265) B1755265
theorem B1390139 : Blo 924580 1390139 := bstep (se 1 (by rfl) ⟨1042604, by rfl⟩ : syracuseStep 1390139 = 2085209) B2085209
theorem B2635325 : Blo 924580 2635325 := bstep (se 3 (by rfl) ⟨494123, by rfl⟩ : syracuseStep 2635325 = 988247) B988247
theorem B1390199 : Blo 924580 1390199 := bstep (se 1 (by rfl) ⟨1042649, by rfl⟩ : syracuseStep 1390199 = 2085299) B2085299
theorem B1390223 : Blo 924580 1390223 := bstep (se 1 (by rfl) ⟨1042667, by rfl⟩ : syracuseStep 1390223 = 2085335) B2085335
theorem B1390265 : Blo 924580 1390265 := bstep (se 2 (by rfl) ⟨521349, by rfl⟩ : syracuseStep 1390265 = 1042699) B1042699
theorem B1390343 : Blo 924580 1390343 := bstep (se 1 (by rfl) ⟨1042757, by rfl⟩ : syracuseStep 1390343 = 2085515) B2085515
theorem B1390379 : Blo 924580 1390379 := bstep (se 1 (by rfl) ⟨1042784, by rfl⟩ : syracuseStep 1390379 = 2085569) B2085569
theorem B19052333 : Blo 924580 19052333 := bstep (se 3 (by rfl) ⟨3572312, by rfl⟩ : syracuseStep 19052333 = 7144625) B7144625
theorem B1390409 : Blo 924580 1390409 := bstep (se 2 (by rfl) ⟨521403, by rfl⟩ : syracuseStep 1390409 = 1042807) B1042807
theorem B3127193 : Blo 924580 3127193 := bstep (se 2 (by rfl) ⟨1172697, by rfl⟩ : syracuseStep 3127193 = 2345395) B2345395
theorem B1390523 : Blo 924580 1390523 := bstep (se 1 (by rfl) ⟨1042892, by rfl⟩ : syracuseStep 1390523 = 2085785) B2085785
theorem B2340809 : Blo 924580 2340809 := bstep (se 2 (by rfl) ⟨877803, by rfl⟩ : syracuseStep 2340809 = 1755607) B1755607
theorem B1390583 : Blo 924580 1390583 := bstep (se 1 (by rfl) ⟨1042937, by rfl⟩ : syracuseStep 1390583 = 2085875) B2085875
theorem B3520523 : Blo 924580 3520523 := bstep (se 1 (by rfl) ⟨2640392, by rfl⟩ : syracuseStep 3520523 = 5280785) B5280785
theorem B1390607 : Blo 924580 1390607 := bstep (se 1 (by rfl) ⟨1042955, by rfl⟩ : syracuseStep 1390607 = 2085911) B2085911
theorem B1390649 : Blo 924580 1390649 := bstep (se 2 (by rfl) ⟨521493, by rfl⟩ : syracuseStep 1390649 = 1042987) B1042987
theorem B1390727 : Blo 924580 1390727 := bstep (se 1 (by rfl) ⟨1043045, by rfl⟩ : syracuseStep 1390727 = 2086091) B2086091
theorem B1980551 : Blo 924580 1980551 := bstep (se 1 (by rfl) ⟨1485413, by rfl⟩ : syracuseStep 1980551 = 2970827) B2970827
theorem B1390763 : Blo 924580 1390763 := bstep (se 1 (by rfl) ⟨1043072, by rfl⟩ : syracuseStep 1390763 = 2086145) B2086145
theorem B1390793 : Blo 924580 1390793 := bstep (se 2 (by rfl) ⟨521547, by rfl⟩ : syracuseStep 1390793 = 1043095) B1043095
theorem B2341163 : Blo 924580 2341163 := bstep (se 1 (by rfl) ⟨1755872, by rfl⟩ : syracuseStep 2341163 = 3511745) B3511745
theorem B1390907 : Blo 924580 1390907 := bstep (se 1 (by rfl) ⟨1043180, by rfl⟩ : syracuseStep 1390907 = 2086361) B2086361
theorem B1390967 : Blo 924580 1390967 := bstep (se 1 (by rfl) ⟨1043225, by rfl⟩ : syracuseStep 1390967 = 2086451) B2086451
theorem B1390991 : Blo 924580 1390991 := bstep (se 1 (by rfl) ⟨1043243, by rfl⟩ : syracuseStep 1390991 = 2086487) B2086487
theorem B1391033 : Blo 924580 1391033 := bstep (se 2 (by rfl) ⟨521637, by rfl⟩ : syracuseStep 1391033 = 1043275) B1043275
theorem B1391111 : Blo 924580 1391111 := bstep (se 1 (by rfl) ⟨1043333, by rfl⟩ : syracuseStep 1391111 = 2086667) B2086667
theorem B5945885 : Blo 924580 5945885 := bstep (se 3 (by rfl) ⟨1114853, by rfl⟩ : syracuseStep 5945885 = 2229707) B2229707
theorem B1391147 : Blo 924580 1391147 := bstep (se 1 (by rfl) ⟨1043360, by rfl⟩ : syracuseStep 1391147 = 2086721) B2086721
theorem B1391177 : Blo 924580 1391177 := bstep (se 2 (by rfl) ⟨521691, by rfl⟩ : syracuseStep 1391177 = 1043383) B1043383
theorem B3127895 : Blo 924580 3127895 := bstep (se 1 (by rfl) ⟨2345921, by rfl⟩ : syracuseStep 3127895 = 4691843) B4691843
theorem B1391291 : Blo 924580 1391291 := bstep (se 1 (by rfl) ⟨1043468, by rfl⟩ : syracuseStep 1391291 = 2086937) B2086937
theorem B1391351 : Blo 924580 1391351 := bstep (se 1 (by rfl) ⟨1043513, by rfl⟩ : syracuseStep 1391351 = 2087027) B2087027
theorem B1391375 : Blo 924580 1391375 := bstep (se 1 (by rfl) ⟨1043531, by rfl⟩ : syracuseStep 1391375 = 2087063) B2087063
theorem B1981217 : Blo 924580 1981217 := bstep (se 2 (by rfl) ⟨742956, by rfl⟩ : syracuseStep 1981217 = 1485913) B1485913
theorem B1391417 : Blo 924580 1391417 := bstep (se 2 (by rfl) ⟨521781, by rfl⟩ : syracuseStep 1391417 = 1043563) B1043563
theorem B1391495 : Blo 924580 1391495 := bstep (se 1 (by rfl) ⟨1043621, by rfl⟩ : syracuseStep 1391495 = 2087243) B2087243
theorem B2374553 : Blo 924580 2374553 := bstep (se 2 (by rfl) ⟨890457, by rfl⟩ : syracuseStep 2374553 = 1780915) B1780915
theorem B1391531 : Blo 924580 1391531 := bstep (se 1 (by rfl) ⟨1043648, by rfl⟩ : syracuseStep 1391531 = 2087297) B2087297
theorem B3521465 : Blo 924580 3521465 := bstep (se 2 (by rfl) ⟨1320549, by rfl⟩ : syracuseStep 3521465 = 2641099) B2641099
theorem B1391561 : Blo 924580 1391561 := bstep (se 2 (by rfl) ⟨521835, by rfl⟩ : syracuseStep 1391561 = 1043671) B1043671
theorem B1391675 : Blo 924580 1391675 := bstep (se 1 (by rfl) ⟨1043756, by rfl⟩ : syracuseStep 1391675 = 2087513) B2087513
theorem B3128381 : Blo 924580 3128381 := bstep (se 3 (by rfl) ⟨586571, by rfl⟩ : syracuseStep 3128381 = 1173143) B1173143
theorem B1981559 : Blo 924580 1981559 := bstep (se 1 (by rfl) ⟨1486169, by rfl⟩ : syracuseStep 1981559 = 2972339) B2972339
theorem B1391735 : Blo 924580 1391735 := bstep (se 1 (by rfl) ⟨1043801, by rfl⟩ : syracuseStep 1391735 = 2087603) B2087603
theorem B1391759 : Blo 924580 1391759 := bstep (se 1 (by rfl) ⟨1043819, by rfl⟩ : syracuseStep 1391759 = 2087639) B2087639
theorem B1391801 : Blo 924580 1391801 := bstep (se 2 (by rfl) ⟨521925, by rfl⟩ : syracuseStep 1391801 = 1043851) B1043851
theorem B1391879 : Blo 924580 1391879 := bstep (se 1 (by rfl) ⟨1043909, by rfl⟩ : syracuseStep 1391879 = 2087819) B2087819
theorem B2342155 : Blo 924580 2342155 := bstep (se 1 (by rfl) ⟨1756616, by rfl⟩ : syracuseStep 2342155 = 3513233) B3513233
theorem B1391915 : Blo 924580 1391915 := bstep (se 1 (by rfl) ⟨1043936, by rfl⟩ : syracuseStep 1391915 = 2087873) B2087873
theorem B1391945 : Blo 924580 1391945 := bstep (se 2 (by rfl) ⟨521979, by rfl⟩ : syracuseStep 1391945 = 1043959) B1043959
theorem B2342297 : Blo 924580 2342297 := bstep (se 2 (by rfl) ⟨878361, by rfl⟩ : syracuseStep 2342297 = 1756723) B1756723
theorem B1392059 : Blo 924580 1392059 := bstep (se 1 (by rfl) ⟨1044044, by rfl⟩ : syracuseStep 1392059 = 2088089) B2088089
theorem B1392119 : Blo 924580 1392119 := bstep (se 1 (by rfl) ⟨1044089, by rfl⟩ : syracuseStep 1392119 = 2088179) B2088179
theorem B1392143 : Blo 924580 1392143 := bstep (se 1 (by rfl) ⟨1044107, by rfl⟩ : syracuseStep 1392143 = 2088215) B2088215
theorem B2342459 : Blo 924580 2342459 := bstep (se 1 (by rfl) ⟨1756844, by rfl⟩ : syracuseStep 2342459 = 3513689) B3513689
theorem B1392185 : Blo 924580 1392185 := bstep (se 2 (by rfl) ⟨522069, by rfl⟩ : syracuseStep 1392185 = 1044139) B1044139
theorem B2637431 : Blo 924580 2637431 := bstep (se 1 (by rfl) ⟨1978073, by rfl⟩ : syracuseStep 2637431 = 3956147) B3956147
theorem B1392263 : Blo 924580 1392263 := bstep (se 1 (by rfl) ⟨1044197, by rfl⟩ : syracuseStep 1392263 = 2088395) B2088395
theorem B2080403 : Blo 924580 2080403 := bstep (se 1 (by rfl) ⟨1560302, by rfl⟩ : syracuseStep 2080403 = 3120605) B3120605
theorem B1392299 : Blo 924580 1392299 := bstep (se 1 (by rfl) ⟨1044224, by rfl⟩ : syracuseStep 1392299 = 2088449) B2088449
theorem B2080457 : Blo 924580 2080457 := bstep (se 2 (by rfl) ⟨780171, by rfl⟩ : syracuseStep 2080457 = 1560343) B1560343
theorem B1392329 : Blo 924580 1392329 := bstep (se 2 (by rfl) ⟨522123, by rfl⟩ : syracuseStep 1392329 = 1044247) B1044247
theorem B7028531 : Blo 924580 7028531 := bstep (se 1 (by rfl) ⟨5271398, by rfl⟩ : syracuseStep 7028531 = 10542797) B10542797
theorem B1392443 : Blo 924580 1392443 := bstep (se 1 (by rfl) ⟨1044332, by rfl⟩ : syracuseStep 1392443 = 2088665) B2088665
theorem B1392503 : Blo 924580 1392503 := bstep (se 1 (by rfl) ⟨1044377, by rfl⟩ : syracuseStep 1392503 = 2088755) B2088755
theorem B1392527 : Blo 924580 1392527 := bstep (se 1 (by rfl) ⟨1044395, by rfl⟩ : syracuseStep 1392527 = 2088791) B2088791
theorem B2342803 : Blo 924580 2342803 := bstep (se 1 (by rfl) ⟨1757102, by rfl⟩ : syracuseStep 2342803 = 3514205) B3514205
theorem B1392569 : Blo 924580 1392569 := bstep (se 2 (by rfl) ⟨522213, by rfl⟩ : syracuseStep 1392569 = 1044427) B1044427
theorem B1392647 : Blo 924580 1392647 := bstep (se 1 (by rfl) ⟨1044485, by rfl⟩ : syracuseStep 1392647 = 2088971) B2088971
theorem B2342945 : Blo 924580 2342945 := bstep (se 2 (by rfl) ⟨878604, by rfl⟩ : syracuseStep 2342945 = 1757209) B1757209
theorem B2670635 : Blo 924580 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B1392683 : Blo 924580 1392683 := bstep (se 1 (by rfl) ⟨1044512, by rfl⟩ : syracuseStep 1392683 = 2089025) B2089025
theorem B1392713 : Blo 924580 1392713 := bstep (se 2 (by rfl) ⟨522267, by rfl⟩ : syracuseStep 1392713 = 1044535) B1044535
theorem B1392827 : Blo 924580 1392827 := bstep (se 1 (by rfl) ⟨1044620, by rfl⟩ : syracuseStep 1392827 = 2089241) B2089241
theorem B5423393 : Blo 924580 5423393 := bstep (se 2 (by rfl) ⟨2033772, by rfl⟩ : syracuseStep 5423393 = 4067545) B4067545
theorem B2081159 : Blo 924580 2081159 := bstep (se 1 (by rfl) ⟨1560869, by rfl⟩ : syracuseStep 2081159 = 3121739) B3121739
theorem B8470919 : Blo 924580 8470919 := bstep (se 1 (by rfl) ⟨6353189, by rfl⟩ : syracuseStep 8470919 = 12706379) B12706379
theorem B3129785 : Blo 924580 3129785 := bstep (se 2 (by rfl) ⟨1173669, by rfl⟩ : syracuseStep 3129785 = 2347339) B2347339
theorem B2081339 : Blo 924580 2081339 := bstep (se 1 (by rfl) ⟨1561004, by rfl⟩ : syracuseStep 2081339 = 3122009) B3122009
theorem B2081465 : Blo 924580 2081465 := bstep (se 2 (by rfl) ⟨780549, by rfl⟩ : syracuseStep 2081465 = 1561099) B1561099
theorem B15057845 : Blo 924580 15057845 := bstep (se 5 (by rfl) ⟨705836, by rfl⟩ : syracuseStep 15057845 = 1411673) B1411673
theorem B2343937 : Blo 924580 2343937 := bstep (se 2 (by rfl) ⟨878976, by rfl⟩ : syracuseStep 2343937 = 1757953) B1757953
theorem B3130379 : Blo 924580 3130379 := bstep (se 1 (by rfl) ⟨2347784, by rfl⟩ : syracuseStep 3130379 = 4695569) B4695569
theorem B2081807 : Blo 924580 2081807 := bstep (se 1 (by rfl) ⟨1561355, by rfl⟩ : syracuseStep 2081807 = 3122711) B3122711
theorem B2081825 : Blo 924580 2081825 := bstep (se 2 (by rfl) ⟨780684, by rfl⟩ : syracuseStep 2081825 = 1561369) B1561369
theorem B3130487 : Blo 924580 3130487 := bstep (se 1 (by rfl) ⟨2347865, by rfl⟩ : syracuseStep 3130487 = 4695731) B4695731
theorem B2082167 : Blo 924580 2082167 := bstep (se 1 (by rfl) ⟨1561625, by rfl⟩ : syracuseStep 2082167 = 3123251) B3123251
theorem B3524107 : Blo 924580 3524107 := bstep (se 1 (by rfl) ⟨2643080, by rfl⟩ : syracuseStep 3524107 = 5286161) B5286161
theorem B2082347 : Blo 924580 2082347 := bstep (se 1 (by rfl) ⟨1561760, by rfl⟩ : syracuseStep 2082347 = 3123521) B3123521
theorem B3950167 : Blo 924580 3950167 := bstep (se 1 (by rfl) ⟨2962625, by rfl⟩ : syracuseStep 3950167 = 5925251) B5925251
theorem B2344535 : Blo 924580 2344535 := bstep (se 1 (by rfl) ⟨1758401, by rfl⟩ : syracuseStep 2344535 = 3516803) B3516803
theorem B3131081 : Blo 924580 3131081 := bstep (se 2 (by rfl) ⟨1174155, by rfl⟩ : syracuseStep 3131081 = 2348311) B2348311
theorem B6342437 : Blo 924580 6342437 := bstep (se 4 (by rfl) ⟨594603, by rfl⟩ : syracuseStep 6342437 = 1189207) B1189207
theorem B2344747 : Blo 924580 2344747 := bstep (se 1 (by rfl) ⟨1758560, by rfl⟩ : syracuseStep 2344747 = 3517121) B3517121
theorem B3524411 : Blo 924580 3524411 := bstep (se 1 (by rfl) ⟨2643308, by rfl⟩ : syracuseStep 3524411 = 5286617) B5286617
theorem B2082707 : Blo 924580 2082707 := bstep (se 1 (by rfl) ⟨1562030, by rfl⟩ : syracuseStep 2082707 = 3124061) B3124061
theorem B2344889 : Blo 924580 2344889 := bstep (se 2 (by rfl) ⟨879333, by rfl⟩ : syracuseStep 2344889 = 1758667) B1758667
theorem B2082761 : Blo 924580 2082761 := bstep (se 2 (by rfl) ⟨781035, by rfl⟩ : syracuseStep 2082761 = 1562071) B1562071
theorem B10536965 : Blo 924580 10536965 := bstep (se 4 (by rfl) ⟨987840, by rfl⟩ : syracuseStep 10536965 = 1975681) B1975681
theorem B2639915 : Blo 924580 2639915 := bstep (se 1 (by rfl) ⟨1979936, by rfl⟩ : syracuseStep 2639915 = 3959873) B3959873
theorem B1755425 : Blo 924580 1755425 := bstep (se 2 (by rfl) ⟨658284, by rfl⟩ : syracuseStep 1755425 = 1316569) B1316569
theorem B3524897 : Blo 924580 3524897 := bstep (se 2 (by rfl) ⟨1321836, by rfl⟩ : syracuseStep 3524897 = 2643673) B2643673
theorem B4999475 : Blo 924580 4999475 := bstep (se 1 (by rfl) ⟨3749606, by rfl⟩ : syracuseStep 4999475 = 7499213) B7499213
theorem B3131783 : Blo 924580 3131783 := bstep (se 1 (by rfl) ⟨2348837, by rfl⟩ : syracuseStep 3131783 = 4697675) B4697675
theorem B2509373 : Blo 924580 2509373 := bstep (se 3 (by rfl) ⟨470507, by rfl⟩ : syracuseStep 2509373 = 941015) B941015
theorem B2083463 : Blo 924580 2083463 := bstep (se 1 (by rfl) ⟨1562597, by rfl⟩ : syracuseStep 2083463 = 3125195) B3125195
theorem B2968265 : Blo 924580 2968265 := bstep (se 2 (by rfl) ⟨1113099, by rfl⟩ : syracuseStep 2968265 = 2226199) B2226199
theorem B3132161 : Blo 924580 3132161 := bstep (se 2 (by rfl) ⟨1174560, by rfl⟩ : syracuseStep 3132161 = 2349121) B2349121
theorem B2083643 : Blo 924580 2083643 := bstep (se 1 (by rfl) ⟨1562732, by rfl⟩ : syracuseStep 2083643 = 3125465) B3125465
theorem B2640701 : Blo 924580 2640701 := bstep (se 3 (by rfl) ⟨495131, by rfl⟩ : syracuseStep 2640701 = 990263) B990263
theorem B2345881 : Blo 924580 2345881 := bstep (se 2 (by rfl) ⟨879705, by rfl⟩ : syracuseStep 2345881 = 1759411) B1759411
theorem B2083769 : Blo 924580 2083769 := bstep (se 2 (by rfl) ⟨781413, by rfl⟩ : syracuseStep 2083769 = 1562827) B1562827
theorem B2346043 : Blo 924580 2346043 := bstep (se 1 (by rfl) ⟨1759532, by rfl⟩ : syracuseStep 2346043 = 3519065) B3519065
theorem B2641031 : Blo 924580 2641031 := bstep (se 1 (by rfl) ⟨1980773, by rfl⟩ : syracuseStep 2641031 = 3961547) B3961547
theorem B2346185 : Blo 924580 2346185 := bstep (se 2 (by rfl) ⟨879819, by rfl⟩ : syracuseStep 2346185 = 1759639) B1759639
theorem B1690895 : Blo 924580 1690895 := bstep (se 1 (by rfl) ⟨1268171, by rfl⟩ : syracuseStep 1690895 = 2536343) B2536343
theorem B2084111 : Blo 924580 2084111 := bstep (se 1 (by rfl) ⟨1563083, by rfl⟩ : syracuseStep 2084111 = 3126167) B3126167
theorem B2084129 : Blo 924580 2084129 := bstep (se 2 (by rfl) ⟨781548, by rfl⟩ : syracuseStep 2084129 = 1563097) B1563097
theorem B2706803 : Blo 924580 2706803 := bstep (se 1 (by rfl) ⟨2030102, by rfl⟩ : syracuseStep 2706803 = 4060205) B4060205
theorem B2116999 : Blo 924580 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B2346529 : Blo 924580 2346529 := bstep (se 2 (by rfl) ⟨879948, by rfl⟩ : syracuseStep 2346529 = 1759897) B1759897
theorem B3132971 : Blo 924580 3132971 := bstep (se 1 (by rfl) ⟨2349728, by rfl⟩ : syracuseStep 3132971 = 4699457) B4699457
theorem B2969149 : Blo 924580 2969149 := bstep (se 3 (by rfl) ⟨556715, by rfl⟩ : syracuseStep 2969149 = 1113431) B1113431
theorem B2084471 : Blo 924580 2084471 := bstep (se 1 (by rfl) ⟨1563353, by rfl⟩ : syracuseStep 2084471 = 3126707) B3126707
theorem B1003151 : Blo 924580 1003151 := bstep (se 1 (by rfl) ⟨752363, by rfl⟩ : syracuseStep 1003151 = 1504727) B1504727
theorem B2084651 : Blo 924580 2084651 := bstep (se 1 (by rfl) ⟨1563488, by rfl⟩ : syracuseStep 2084651 = 3126977) B3126977
theorem B1560505 : Blo 924580 1560505 := bstep (se 2 (by rfl) ⟨585189, by rfl⟩ : syracuseStep 1560505 = 1170379) B1170379
theorem B4444247 : Blo 924580 4444247 := bstep (se 1 (by rfl) ⟨3333185, by rfl⟩ : syracuseStep 4444247 = 6666371) B6666371
theorem B2347127 : Blo 924580 2347127 := bstep (se 1 (by rfl) ⟨1760345, by rfl⟩ : syracuseStep 2347127 = 3520691) B3520691
theorem B2085011 : Blo 924580 2085011 := bstep (se 1 (by rfl) ⟨1563758, by rfl⟩ : syracuseStep 2085011 = 3127517) B3127517
theorem B22532269 : Blo 924580 22532269 := bstep (se 3 (by rfl) ⟨4224800, by rfl⟩ : syracuseStep 22532269 = 8449601) B8449601
theorem B1757369 : Blo 924580 1757369 := bstep (se 2 (by rfl) ⟨659013, by rfl⟩ : syracuseStep 1757369 = 1318027) B1318027
theorem B4444361 : Blo 924580 4444361 := bstep (se 2 (by rfl) ⟨1666635, by rfl⟩ : syracuseStep 4444361 = 3333271) B3333271
theorem B2085065 : Blo 924580 2085065 := bstep (se 2 (by rfl) ⟨781899, by rfl⟩ : syracuseStep 2085065 = 1563799) B1563799
theorem B7918033 : Blo 924580 7918033 := bstep (se 2 (by rfl) ⟨2969262, by rfl⟩ : syracuseStep 7918033 = 5938525) B5938525
theorem B1430023 : Blo 924580 1430023 := bstep (se 1 (by rfl) ⟨1072517, by rfl⟩ : syracuseStep 1430023 = 2145035) B2145035
theorem B1561207 : Blo 924580 1561207 := bstep (se 1 (by rfl) ⟨1170905, by rfl⟩ : syracuseStep 1561207 = 2341811) B2341811
theorem B1561403 : Blo 924580 1561403 := bstep (se 1 (by rfl) ⟨1171052, by rfl⟩ : syracuseStep 1561403 = 2342105) B2342105
theorem B2642807 : Blo 924580 2642807 := bstep (se 1 (by rfl) ⟨1982105, by rfl⟩ : syracuseStep 2642807 = 3964211) B3964211
theorem B2085767 : Blo 924580 2085767 := bstep (se 1 (by rfl) ⟨1564325, by rfl⟩ : syracuseStep 2085767 = 3128651) B3128651
theorem B4019129 : Blo 924580 4019129 := bstep (se 2 (by rfl) ⟨1507173, by rfl⟩ : syracuseStep 4019129 = 3014347) B3014347
theorem B2085947 : Blo 924580 2085947 := bstep (se 1 (by rfl) ⟨1564460, by rfl⟩ : syracuseStep 2085947 = 3128921) B3128921
theorem B5002327 : Blo 924580 5002327 := bstep (se 1 (by rfl) ⟨3751745, by rfl⟩ : syracuseStep 5002327 = 7503491) B7503491
theorem B2086073 : Blo 924580 2086073 := bstep (se 2 (by rfl) ⟨782277, by rfl⟩ : syracuseStep 2086073 = 1564555) B1564555
theorem B1561801 : Blo 924580 1561801 := bstep (se 2 (by rfl) ⟨585675, by rfl⟩ : syracuseStep 1561801 = 1171351) B1171351
theorem B1758523 : Blo 924580 1758523 := bstep (se 1 (by rfl) ⟨1318892, by rfl⟩ : syracuseStep 1758523 = 2637785) B2637785
theorem B2348423 : Blo 924580 2348423 := bstep (se 1 (by rfl) ⟨1761317, by rfl⟩ : syracuseStep 2348423 = 3522635) B3522635
theorem B2348473 : Blo 924580 2348473 := bstep (se 2 (by rfl) ⟨880677, by rfl⟩ : syracuseStep 2348473 = 1761355) B1761355
theorem B11851217 : Blo 924580 11851217 := bstep (se 2 (by rfl) ⟨4444206, by rfl⟩ : syracuseStep 11851217 = 8888413) B8888413
theorem B2086415 : Blo 924580 2086415 := bstep (se 1 (by rfl) ⟨1564811, by rfl⟩ : syracuseStep 2086415 = 3129623) B3129623
theorem B2086433 : Blo 924580 2086433 := bstep (se 2 (by rfl) ⟨782412, by rfl⟩ : syracuseStep 2086433 = 1564825) B1564825
theorem B1759009 : Blo 924580 1759009 := bstep (se 2 (by rfl) ⟨659628, by rfl⟩ : syracuseStep 1759009 = 1319257) B1319257
theorem B3954491 : Blo 924580 3954491 := bstep (se 1 (by rfl) ⟨2965868, by rfl⟩ : syracuseStep 3954491 = 5931737) B5931737
theorem B2643799 : Blo 924580 2643799 := bstep (se 1 (by rfl) ⟨1982849, by rfl⟩ : syracuseStep 2643799 = 3965699) B3965699
theorem B2086775 : Blo 924580 2086775 := bstep (se 1 (by rfl) ⟨1565081, by rfl⟩ : syracuseStep 2086775 = 3130163) B3130163
theorem B1562503 : Blo 924580 1562503 := bstep (se 1 (by rfl) ⟨1171877, by rfl⟩ : syracuseStep 1562503 = 2343755) B2343755
theorem B2349071 : Blo 924580 2349071 := bstep (se 1 (by rfl) ⟨1761803, by rfl⟩ : syracuseStep 2349071 = 3523607) B3523607
theorem B21485591 : Blo 924580 21485591 := bstep (se 1 (by rfl) ⟨16114193, by rfl⟩ : syracuseStep 21485591 = 32228387) B32228387
theorem B2086955 : Blo 924580 2086955 := bstep (se 1 (by rfl) ⟨1565216, by rfl⟩ : syracuseStep 2086955 = 3130433) B3130433
theorem B10016855 : Blo 924580 10016855 := bstep (se 1 (by rfl) ⟨7512641, by rfl⟩ : syracuseStep 10016855 = 15025283) B15025283
theorem B2382139 : Blo 924580 2382139 := bstep (se 1 (by rfl) ⟨1786604, by rfl⟩ : syracuseStep 2382139 = 3573209) B3573209
theorem B7920017 : Blo 924580 7920017 := bstep (se 2 (by rfl) ⟨2970006, by rfl⟩ : syracuseStep 7920017 = 5940013) B5940013
theorem B5626259 : Blo 924580 5626259 := bstep (se 1 (by rfl) ⟨4219694, by rfl⟩ : syracuseStep 5626259 = 8439389) B8439389
theorem B2087315 : Blo 924580 2087315 := bstep (se 1 (by rfl) ⟨1565486, by rfl⟩ : syracuseStep 2087315 = 3130973) B3130973
theorem B2087369 : Blo 924580 2087369 := bstep (se 2 (by rfl) ⟨782763, by rfl⟩ : syracuseStep 2087369 = 1565527) B1565527
theorem B4446667 : Blo 924580 4446667 := bstep (se 1 (by rfl) ⟨3335000, by rfl⟩ : syracuseStep 4446667 = 6670001) B6670001
theorem B5265931 : Blo 924580 5265931 := bstep (se 1 (by rfl) ⟨3949448, by rfl⟩ : syracuseStep 5265931 = 7898897) B7898897
theorem B1563151 : Blo 924580 1563151 := bstep (se 1 (by rfl) ⟨1172363, by rfl⟩ : syracuseStep 1563151 = 2344727) B2344727
theorem B3005047 : Blo 924580 3005047 := bstep (se 1 (by rfl) ⟨2253785, by rfl⟩ : syracuseStep 3005047 = 4507571) B4507571
theorem B2349769 : Blo 924580 2349769 := bstep (se 2 (by rfl) ⟨881163, by rfl⟩ : syracuseStep 2349769 = 1762327) B1762327
theorem B3169039 : Blo 924580 3169039 := bstep (se 1 (by rfl) ⟨2376779, by rfl⟩ : syracuseStep 3169039 = 4753559) B4753559
theorem B2349911 : Blo 924580 2349911 := bstep (se 1 (by rfl) ⟨1762433, by rfl⟩ : syracuseStep 2349911 = 3524867) B3524867
theorem B1760201 : Blo 924580 1760201 := bstep (se 2 (by rfl) ⟨660075, by rfl⟩ : syracuseStep 1760201 = 1320151) B1320151
theorem B1563691 : Blo 924580 1563691 := bstep (se 1 (by rfl) ⟨1172768, by rfl⟩ : syracuseStep 1563691 = 2345537) B2345537
theorem B1170551 : Blo 924580 1170551 := bstep (se 1 (by rfl) ⟨877913, by rfl⟩ : syracuseStep 1170551 = 1755827) B1755827
theorem B2088071 : Blo 924580 2088071 := bstep (se 1 (by rfl) ⟨1566053, by rfl⟩ : syracuseStep 2088071 = 3132107) B3132107
theorem B1563833 : Blo 924580 1563833 := bstep (se 2 (by rfl) ⟨586437, by rfl⟩ : syracuseStep 1563833 = 1172875) B1172875
theorem B2252033 : Blo 924580 2252033 := bstep (se 2 (by rfl) ⟨844512, by rfl⟩ : syracuseStep 2252033 = 1689025) B1689025
theorem B1170703 : Blo 924580 1170703 := bstep (se 1 (by rfl) ⟨878027, by rfl⟩ : syracuseStep 1170703 = 1756055) B1756055
theorem B33840443 : Blo 924580 33840443 := bstep (se 1 (by rfl) ⟨25380332, by rfl⟩ : syracuseStep 33840443 = 50760665) B50760665
theorem B2088251 : Blo 924580 2088251 := bstep (se 1 (by rfl) ⟨1566188, by rfl⟩ : syracuseStep 2088251 = 3132377) B3132377
theorem B7036307 : Blo 924580 7036307 := bstep (se 1 (by rfl) ⟨5277230, by rfl⟩ : syracuseStep 7036307 = 10554461) B10554461
theorem B2088377 : Blo 924580 2088377 := bstep (se 2 (by rfl) ⟨783141, by rfl⟩ : syracuseStep 2088377 = 1566283) B1566283
theorem B1170875 : Blo 924580 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B1760915 : Blo 924580 1760915 := bstep (se 1 (by rfl) ⟨1320686, by rfl⟩ : syracuseStep 1760915 = 2641373) B2641373
theorem B1760953 : Blo 924580 1760953 := bstep (se 2 (by rfl) ⟨660357, by rfl⟩ : syracuseStep 1760953 = 1320715) B1320715
theorem B2973455 : Blo 924580 2973455 := bstep (se 1 (by rfl) ⟨2230091, by rfl⟩ : syracuseStep 2973455 = 4460183) B4460183
theorem B2088719 : Blo 924580 2088719 := bstep (se 1 (by rfl) ⟨1566539, by rfl⟩ : syracuseStep 2088719 = 3133079) B3133079
theorem B2088737 : Blo 924580 2088737 := bstep (se 2 (by rfl) ⟨783276, by rfl⟩ : syracuseStep 2088737 = 1566553) B1566553
theorem B4448051 : Blo 924580 4448051 := bstep (se 1 (by rfl) ⟨3336038, by rfl⟩ : syracuseStep 4448051 = 6672077) B6672077
theorem B2678615 : Blo 924580 2678615 := bstep (se 1 (by rfl) ⟨2008961, by rfl⟩ : syracuseStep 2678615 = 4017923) B4017923
theorem B1564535 : Blo 924580 1564535 := bstep (se 1 (by rfl) ⟨1173401, by rfl⟩ : syracuseStep 1564535 = 2346803) B2346803
theorem B27091037 : Blo 924580 27091037 := bstep (se 3 (by rfl) ⟨5079569, by rfl⟩ : syracuseStep 27091037 = 10159139) B10159139
theorem B2089079 : Blo 924580 2089079 := bstep (se 1 (by rfl) ⟨1566809, by rfl⟩ : syracuseStep 2089079 = 3133619) B3133619
theorem B4448513 : Blo 924580 4448513 := bstep (se 2 (by rfl) ⟨1668192, by rfl⟩ : syracuseStep 4448513 = 3336385) B3336385
theorem B1040647 : Blo 924580 1040647 := bstep (se 1 (by rfl) ⟨780485, by rfl⟩ : syracuseStep 1040647 = 1560971) B1560971
theorem B2089259 : Blo 924580 2089259 := bstep (se 1 (by rfl) ⟨1566944, by rfl⟩ : syracuseStep 2089259 = 3133889) B3133889
theorem B1564987 : Blo 924580 1564987 := bstep (se 1 (by rfl) ⟨1173740, by rfl⟩ : syracuseStep 1564987 = 2347481) B2347481
theorem B1171847 : Blo 924580 1171847 := bstep (se 1 (by rfl) ⟨878885, by rfl⟩ : syracuseStep 1171847 = 1757771) B1757771
theorem B1040827 : Blo 924580 1040827 := bstep (se 1 (by rfl) ⟨780620, by rfl⟩ : syracuseStep 1040827 = 1561241) B1561241
theorem B1335739 : Blo 924580 1335739 := bstep (se 1 (by rfl) ⟨1001804, by rfl⟩ : syracuseStep 1335739 = 2003609) B2003609
theorem B1565129 : Blo 924580 1565129 := bstep (se 2 (by rfl) ⟨586923, by rfl⟩ : syracuseStep 1565129 = 1173847) B1173847
theorem B5267915 : Blo 924580 5267915 := bstep (se 1 (by rfl) ⟨3950936, by rfl⟩ : syracuseStep 5267915 = 7901873) B7901873
theorem B24044323 : Blo 924580 24044323 := bstep (se 1 (by rfl) ⟨18033242, by rfl⟩ : syracuseStep 24044323 = 36066485) B36066485
theorem B1041295 : Blo 924580 1041295 := bstep (se 1 (by rfl) ⟨780971, by rfl⟩ : syracuseStep 1041295 = 1561943) B1561943
theorem B1172495 : Blo 924580 1172495 := bstep (se 1 (by rfl) ⟨879371, by rfl⟩ : syracuseStep 1172495 = 1758743) B1758743
theorem B1565831 : Blo 924580 1565831 := bstep (se 1 (by rfl) ⟨1174373, by rfl⟩ : syracuseStep 1565831 = 2348747) B2348747
theorem B1041799 : Blo 924580 1041799 := bstep (se 1 (by rfl) ⟨781349, by rfl⟩ : syracuseStep 1041799 = 1562699) B1562699
theorem B1041979 : Blo 924580 1041979 := bstep (se 1 (by rfl) ⟨781484, by rfl⟩ : syracuseStep 1041979 = 1562969) B1562969
theorem B1566479 : Blo 924580 1566479 := bstep (se 1 (by rfl) ⟨1174859, by rfl⟩ : syracuseStep 1566479 = 2349719) B2349719
theorem B2222095 : Blo 924580 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B1042447 : Blo 924580 1042447 := bstep (se 1 (by rfl) ⟨781835, by rfl⟩ : syracuseStep 1042447 = 1563671) B1563671
theorem B1337401 : Blo 924580 1337401 := bstep (se 2 (by rfl) ⟨501525, by rfl⟩ : syracuseStep 1337401 = 1003051) B1003051
theorem B68512013 : Blo 924580 68512013 := bstep (se 3 (by rfl) ⟨12846002, by rfl⟩ : syracuseStep 68512013 = 25692005) B25692005
theorem B1042951 : Blo 924580 1042951 := bstep (se 1 (by rfl) ⟨782213, by rfl⟩ : syracuseStep 1042951 = 1564427) B1564427
theorem B2222711 : Blo 924580 2222711 := bstep (se 1 (by rfl) ⟨1667033, by rfl⟩ : syracuseStep 2222711 = 3334067) B3334067
theorem B1043131 : Blo 924580 1043131 := bstep (se 1 (by rfl) ⟨782348, by rfl⟩ : syracuseStep 1043131 = 1564697) B1564697
theorem B5630735 : Blo 924580 5630735 := bstep (se 1 (by rfl) ⟨4223051, by rfl⟩ : syracuseStep 5630735 = 8446103) B8446103
theorem B5270305 : Blo 924580 5270305 := bstep (se 2 (by rfl) ⟨1976364, by rfl⟩ : syracuseStep 5270305 = 3952729) B3952729
theorem B22571891 : Blo 924580 22571891 := bstep (se 1 (by rfl) ⟨16928918, by rfl⟩ : syracuseStep 22571891 = 33857837) B33857837
theorem B6876019 : Blo 924580 6876019 := bstep (se 1 (by rfl) ⟨5157014, by rfl⟩ : syracuseStep 6876019 = 10314029) B10314029
theorem B3959837 : Blo 924580 3959837 := bstep (se 3 (by rfl) ⟨742469, by rfl⟩ : syracuseStep 3959837 = 1484939) B1484939
theorem B14445701 : Blo 924580 14445701 := bstep (se 4 (by rfl) ⟨1354284, by rfl⟩ : syracuseStep 14445701 = 2708569) B2708569
theorem B1043599 : Blo 924580 1043599 := bstep (se 1 (by rfl) ⟨782699, by rfl⟩ : syracuseStep 1043599 = 1565399) B1565399
theorem B3337453 : Blo 924580 3337453 := bstep (se 3 (by rfl) ⟨625772, by rfl⟩ : syracuseStep 3337453 = 1251545) B1251545
theorem B15232387 : Blo 924580 15232387 := bstep (se 1 (by rfl) ⟨11424290, by rfl⟩ : syracuseStep 15232387 = 22848581) B22848581
theorem B5631491 : Blo 924580 5631491 := bstep (se 1 (by rfl) ⟨4223618, by rfl⟩ : syracuseStep 5631491 = 8447237) B8447237
theorem B3337757 : Blo 924580 3337757 := bstep (se 3 (by rfl) ⟨625829, by rfl⟩ : syracuseStep 3337757 = 1251659) B1251659
theorem B1044103 : Blo 924580 1044103 := bstep (se 1 (by rfl) ⟨783077, by rfl⟩ : syracuseStep 1044103 = 1566155) B1566155
theorem B1666745 : Blo 924580 1666745 := bstep (se 2 (by rfl) ⟨625029, by rfl⟩ : syracuseStep 1666745 = 1250059) B1250059
theorem B3960521 : Blo 924580 3960521 := bstep (se 2 (by rfl) ⟨1485195, by rfl⟩ : syracuseStep 3960521 = 2970391) B2970391
theorem B7139087 : Blo 924580 7139087 := bstep (se 1 (by rfl) ⟨5354315, by rfl⟩ : syracuseStep 7139087 = 10708631) B10708631
theorem B1044283 : Blo 924580 1044283 := bstep (se 1 (by rfl) ⟨783212, by rfl⟩ : syracuseStep 1044283 = 1566425) B1566425
theorem B4452185 : Blo 924580 4452185 := bstep (se 2 (by rfl) ⟨1669569, by rfl⟩ : syracuseStep 4452185 = 3339139) B3339139
theorem B11890583 : Blo 924580 11890583 := bstep (se 1 (by rfl) ⟨8917937, by rfl⟩ : syracuseStep 11890583 = 17835875) B17835875
theorem B5271581 : Blo 924580 5271581 := bstep (se 3 (by rfl) ⟨988421, by rfl⟩ : syracuseStep 5271581 = 1976843) B1976843
theorem B5075137 : Blo 924580 5075137 := bstep (se 2 (by rfl) ⟨1903176, by rfl⟩ : syracuseStep 5075137 = 3806353) B3806353
theorem B5010113 : Blo 924580 5010113 := bstep (se 2 (by rfl) ⟨1878792, by rfl⟩ : syracuseStep 5010113 = 3757585) B3757585
theorem B2225353 : Blo 924580 2225353 := bstep (se 2 (by rfl) ⟨834507, by rfl⟩ : syracuseStep 2225353 = 1669015) B1669015
theorem B5928173 : Blo 924580 5928173 := bstep (se 3 (by rfl) ⟨1111532, by rfl⟩ : syracuseStep 5928173 = 2223065) B2223065
theorem B2815319 : Blo 924580 2815319 := bstep (se 1 (by rfl) ⟨2111489, by rfl⟩ : syracuseStep 2815319 = 4222979) B4222979
theorem B3962297 : Blo 924580 3962297 := bstep (se 2 (by rfl) ⟨1485861, by rfl⟩ : syracuseStep 3962297 = 2971723) B2971723
theorem B6780419 : Blo 924580 6780419 := bstep (se 1 (by rfl) ⟨5085314, by rfl⟩ : syracuseStep 6780419 = 10170629) B10170629
theorem B42759859 : Blo 924580 42759859 := bstep (se 1 (by rfl) ⟨32069894, by rfl⟩ : syracuseStep 42759859 = 64139789) B64139789
theorem B5011237 : Blo 924580 5011237 := bstep (se 4 (by rfl) ⟨469803, by rfl⟩ : syracuseStep 5011237 = 939607) B939607
theorem B1112071 : Blo 924580 1112071 := bstep (se 1 (by rfl) ⟨834053, by rfl⟩ : syracuseStep 1112071 = 1668107) B1668107
theorem B1144891 : Blo 924580 1144891 := bstep (se 1 (by rfl) ⟨858668, by rfl⟩ : syracuseStep 1144891 = 1717337) B1717337
theorem B3963289 : Blo 924580 3963289 := bstep (se 2 (by rfl) ⟨1486233, by rfl⟩ : syracuseStep 3963289 = 2972467) B2972467
theorem B5274179 : Blo 924580 5274179 := bstep (se 1 (by rfl) ⟨3955634, by rfl⟩ : syracuseStep 5274179 = 7911269) B7911269
theorem B5340227 : Blo 924580 5340227 := bstep (se 1 (by rfl) ⟨4005170, by rfl⟩ : syracuseStep 5340227 = 8010341) B8010341
theorem B11304137 : Blo 924580 11304137 := bstep (se 2 (by rfl) ⟨4239051, by rfl⟩ : syracuseStep 11304137 = 8478103) B8478103
theorem B4455739 : Blo 924580 4455739 := bstep (se 1 (by rfl) ⟨3341804, by rfl⟩ : syracuseStep 4455739 = 6683609) B6683609
theorem B4685201 : Blo 924580 4685201 := bstep (se 2 (by rfl) ⟨1756950, by rfl⟩ : syracuseStep 4685201 = 3513901) B3513901
theorem B3343133 : Blo 924580 3343133 := bstep (se 3 (by rfl) ⟨626837, by rfl⟩ : syracuseStep 3343133 = 1253675) B1253675
theorem B1672201 : Blo 924580 1672201 := bstep (se 2 (by rfl) ⟨627075, by rfl⟩ : syracuseStep 1672201 = 1254151) B1254151
theorem B15205427 : Blo 924580 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B4228291 : Blo 924580 4228291 := bstep (se 1 (by rfl) ⟨3171218, by rfl⟩ : syracuseStep 4228291 = 6342437) B6342437
theorem B1672915 : Blo 924580 1672915 := bstep (se 1 (by rfl) ⟨1254686, by rfl⟩ : syracuseStep 1672915 = 2509373) B2509373
theorem B17827877 : Blo 924580 17827877 := bstep (se 4 (by rfl) ⟨1671363, by rfl⟩ : syracuseStep 17827877 = 3342727) B3342727
theorem B1804535 : Blo 924580 1804535 := bstep (se 1 (by rfl) ⟨1353401, by rfl⟩ : syracuseStep 1804535 = 2706803) B2706803
theorem B7047485 : Blo 924580 7047485 := bstep (se 3 (by rfl) ⟨1321403, by rfl⟩ : syracuseStep 7047485 = 2642807) B2642807
theorem B2230907 : Blo 924580 2230907 := bstep (se 1 (by rfl) ⟨1673180, by rfl⟩ : syracuseStep 2230907 = 3346361) B3346361
theorem B16026917 : Blo 924580 16026917 := bstep (se 4 (by rfl) ⟨1502523, by rfl⟩ : syracuseStep 16026917 = 3005047) B3005047
theorem B7900811 : Blo 924580 7900811 := bstep (se 1 (by rfl) ⟨5925608, by rfl⟩ : syracuseStep 7900811 = 11851217) B11851217
theorem B14323727 : Blo 924580 14323727 := bstep (se 1 (by rfl) ⟨10742795, by rfl⟩ : syracuseStep 14323727 = 21485591) B21485591
theorem B5280011 : Blo 924580 5280011 := bstep (se 1 (by rfl) ⟨3960008, by rfl⟩ : syracuseStep 5280011 = 7920017) B7920017
theorem B9900755 : Blo 924580 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B4690871 : Blo 924580 4690871 := bstep (se 1 (by rfl) ⟨3518153, by rfl⟩ : syracuseStep 4690871 = 7036307) B7036307
theorem B18060691 : Blo 924580 18060691 := bstep (se 1 (by rfl) ⟨13545518, by rfl⟩ : syracuseStep 18060691 = 27091037) B27091037
theorem B3511943 : Blo 924580 3511943 := bstep (se 1 (by rfl) ⟨2633957, by rfl⟩ : syracuseStep 3511943 = 5267915) B5267915
theorem B5281469 : Blo 924580 5281469 := bstep (se 3 (by rfl) ⟨990275, by rfl⟩ : syracuseStep 5281469 = 1980551) B1980551
theorem B26679077 : Blo 924580 26679077 := bstep (se 4 (by rfl) ⟨2501163, by rfl⟩ : syracuseStep 26679077 = 5002327) B5002327
theorem B1906615 : Blo 924580 1906615 := bstep (se 1 (by rfl) ⟨1429961, by rfl⟩ : syracuseStep 1906615 = 2859923) B2859923
theorem B10557377 : Blo 924580 10557377 := bstep (se 2 (by rfl) ⟨3959016, by rfl⟩ : syracuseStep 10557377 = 7918033) B7918033
theorem B1906697 : Blo 924580 1906697 := bstep (se 2 (by rfl) ⟨715011, by rfl⟩ : syracuseStep 1906697 = 1430023) B1430023
theorem B4692329 : Blo 924580 4692329 := bstep (se 2 (by rfl) ⟨1759623, by rfl⟩ : syracuseStep 4692329 = 3519247) B3519247
theorem B3512929 : Blo 924580 3512929 := bstep (se 2 (by rfl) ⟨1317348, by rfl⟩ : syracuseStep 3512929 = 2634697) B2634697
theorem B5085881 : Blo 924580 5085881 := bstep (se 2 (by rfl) ⟨1907205, by rfl⟩ : syracuseStep 5085881 = 3814411) B3814411
theorem B1055431 : Blo 924580 1055431 := bstep (se 1 (by rfl) ⟨791573, by rfl⟩ : syracuseStep 1055431 = 1583147) B1583147
theorem B924591 : Blo 924580 924591 := bstep (se 1 (by rfl) ⟨693443, by rfl⟩ : syracuseStep 924591 = 1386887) B1386887
theorem B924615 : Blo 924580 924615 := bstep (se 1 (by rfl) ⟨693461, by rfl⟩ : syracuseStep 924615 = 1386923) B1386923
theorem B924635 : Blo 924580 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B23763941 : Blo 924580 23763941 := bstep (se 4 (by rfl) ⟨2227869, by rfl⟩ : syracuseStep 23763941 = 4455739) B4455739
theorem B924711 : Blo 924580 924711 := bstep (se 1 (by rfl) ⟨693533, by rfl⟩ : syracuseStep 924711 = 1387067) B1387067
theorem B3513401 : Blo 924580 3513401 := bstep (se 2 (by rfl) ⟨1317525, by rfl⟩ : syracuseStep 3513401 = 2635051) B2635051
theorem B924751 : Blo 924580 924751 := bstep (se 1 (by rfl) ⟨693563, by rfl⟩ : syracuseStep 924751 = 1387127) B1387127
theorem B1481807 : Blo 924580 1481807 := bstep (se 1 (by rfl) ⟨1111355, by rfl⟩ : syracuseStep 1481807 = 2222711) B2222711
theorem B7609423 : Blo 924580 7609423 := bstep (se 1 (by rfl) ⟨5707067, by rfl⟩ : syracuseStep 7609423 = 11414135) B11414135
theorem B924767 : Blo 924580 924767 := bstep (se 1 (by rfl) ⟨693575, by rfl⟩ : syracuseStep 924767 = 1387151) B1387151
theorem B924795 : Blo 924580 924795 := bstep (se 1 (by rfl) ⟨693596, by rfl⟩ : syracuseStep 924795 = 1387193) B1387193
theorem B924847 : Blo 924580 924847 := bstep (se 1 (by rfl) ⟨693635, by rfl⟩ : syracuseStep 924847 = 1387271) B1387271
theorem B924871 : Blo 924580 924871 := bstep (se 1 (by rfl) ⟨693653, by rfl⟩ : syracuseStep 924871 = 1387307) B1387307
theorem B924891 : Blo 924580 924891 := bstep (se 1 (by rfl) ⟨693668, by rfl⟩ : syracuseStep 924891 = 1387337) B1387337
theorem B15047927 : Blo 924580 15047927 := bstep (se 1 (by rfl) ⟨11285945, by rfl⟩ : syracuseStep 15047927 = 22571891) B22571891
theorem B924967 : Blo 924580 924967 := bstep (se 1 (by rfl) ⟨693725, by rfl⟩ : syracuseStep 924967 = 1387451) B1387451
theorem B925007 : Blo 924580 925007 := bstep (se 1 (by rfl) ⟨693755, by rfl⟩ : syracuseStep 925007 = 1387511) B1387511
theorem B925023 : Blo 924580 925023 := bstep (se 1 (by rfl) ⟨693767, by rfl⟩ : syracuseStep 925023 = 1387535) B1387535
theorem B925051 : Blo 924580 925051 := bstep (se 1 (by rfl) ⟨693788, by rfl⟩ : syracuseStep 925051 = 1387577) B1387577
theorem B5283245 : Blo 924580 5283245 := bstep (se 3 (by rfl) ⟨990608, by rfl⟩ : syracuseStep 5283245 = 1981217) B1981217
theorem B925103 : Blo 924580 925103 := bstep (se 1 (by rfl) ⟨693827, by rfl⟩ : syracuseStep 925103 = 1387655) B1387655
theorem B925127 : Blo 924580 925127 := bstep (se 1 (by rfl) ⟨693845, by rfl⟩ : syracuseStep 925127 = 1387691) B1387691
theorem B925147 : Blo 924580 925147 := bstep (se 1 (by rfl) ⟨693860, by rfl⟩ : syracuseStep 925147 = 1387721) B1387721
theorem B925223 : Blo 924580 925223 := bstep (se 1 (by rfl) ⟨693917, by rfl⟩ : syracuseStep 925223 = 1387835) B1387835
theorem B925263 : Blo 924580 925263 := bstep (se 1 (by rfl) ⟨693947, by rfl⟩ : syracuseStep 925263 = 1387895) B1387895
theorem B925279 : Blo 924580 925279 := bstep (se 1 (by rfl) ⟨693959, by rfl⟩ : syracuseStep 925279 = 1387919) B1387919
theorem B925307 : Blo 924580 925307 := bstep (se 1 (by rfl) ⟨693980, by rfl⟩ : syracuseStep 925307 = 1387961) B1387961
theorem B925359 : Blo 924580 925359 := bstep (se 1 (by rfl) ⟨694019, by rfl⟩ : syracuseStep 925359 = 1388039) B1388039
theorem B925383 : Blo 924580 925383 := bstep (se 1 (by rfl) ⟨694037, by rfl⟩ : syracuseStep 925383 = 1388075) B1388075
theorem B925403 : Blo 924580 925403 := bstep (se 1 (by rfl) ⟨694052, by rfl⟩ : syracuseStep 925403 = 1388105) B1388105
theorem B6332141 : Blo 924580 6332141 := bstep (se 3 (by rfl) ⟨1187276, by rfl⟩ : syracuseStep 6332141 = 2374553) B2374553
theorem B925479 : Blo 924580 925479 := bstep (se 1 (by rfl) ⟨694109, by rfl⟩ : syracuseStep 925479 = 1388219) B1388219
theorem B925519 : Blo 924580 925519 := bstep (se 1 (by rfl) ⟨694139, by rfl⟩ : syracuseStep 925519 = 1388279) B1388279
theorem B925535 : Blo 924580 925535 := bstep (se 1 (by rfl) ⟨694151, by rfl⟩ : syracuseStep 925535 = 1388303) B1388303
theorem B4759391 : Blo 924580 4759391 := bstep (se 1 (by rfl) ⟨3569543, by rfl⟩ : syracuseStep 4759391 = 7139087) B7139087
theorem B925563 : Blo 924580 925563 := bstep (se 1 (by rfl) ⟨694172, by rfl⟩ : syracuseStep 925563 = 1388345) B1388345
theorem B10166147 : Blo 924580 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B925615 : Blo 924580 925615 := bstep (se 1 (by rfl) ⟨694211, by rfl⟩ : syracuseStep 925615 = 1388423) B1388423
theorem B925639 : Blo 924580 925639 := bstep (se 1 (by rfl) ⟨694229, by rfl⟩ : syracuseStep 925639 = 1388459) B1388459
theorem B925659 : Blo 924580 925659 := bstep (se 1 (by rfl) ⟨694244, by rfl⟩ : syracuseStep 925659 = 1388489) B1388489
theorem B1482761 : Blo 924580 1482761 := bstep (se 2 (by rfl) ⟨556035, by rfl⟩ : syracuseStep 1482761 = 1112071) B1112071
theorem B3514387 : Blo 924580 3514387 := bstep (se 1 (by rfl) ⟨2635790, by rfl⟩ : syracuseStep 3514387 = 5271581) B5271581
theorem B925735 : Blo 924580 925735 := bstep (se 1 (by rfl) ⟨694301, by rfl⟩ : syracuseStep 925735 = 1388603) B1388603
theorem B925775 : Blo 924580 925775 := bstep (se 1 (by rfl) ⟨694331, by rfl⟩ : syracuseStep 925775 = 1388663) B1388663
theorem B925791 : Blo 924580 925791 := bstep (se 1 (by rfl) ⟨694343, by rfl⟩ : syracuseStep 925791 = 1388687) B1388687
theorem B925819 : Blo 924580 925819 := bstep (se 1 (by rfl) ⟨694364, by rfl⟩ : syracuseStep 925819 = 1388729) B1388729
theorem B925871 : Blo 924580 925871 := bstep (se 1 (by rfl) ⟨694403, by rfl⟩ : syracuseStep 925871 = 1388807) B1388807
theorem B925895 : Blo 924580 925895 := bstep (se 1 (by rfl) ⟨694421, by rfl⟩ : syracuseStep 925895 = 1388843) B1388843
theorem B925915 : Blo 924580 925915 := bstep (se 1 (by rfl) ⟨694436, by rfl⟩ : syracuseStep 925915 = 1388873) B1388873
theorem B925991 : Blo 924580 925991 := bstep (se 1 (by rfl) ⟨694493, by rfl⟩ : syracuseStep 925991 = 1388987) B1388987
theorem B3121469 : Blo 924580 3121469 := bstep (se 3 (by rfl) ⟨585275, by rfl⟩ : syracuseStep 3121469 = 1170551) B1170551
theorem B926031 : Blo 924580 926031 := bstep (se 1 (by rfl) ⟨694523, by rfl⟩ : syracuseStep 926031 = 1389047) B1389047
theorem B926047 : Blo 924580 926047 := bstep (se 1 (by rfl) ⟨694535, by rfl⟩ : syracuseStep 926047 = 1389071) B1389071
theorem B926075 : Blo 924580 926075 := bstep (se 1 (by rfl) ⟨694556, by rfl⟩ : syracuseStep 926075 = 1389113) B1389113
theorem B926127 : Blo 924580 926127 := bstep (se 1 (by rfl) ⟨694595, by rfl⟩ : syracuseStep 926127 = 1389191) B1389191
theorem B926151 : Blo 924580 926151 := bstep (se 1 (by rfl) ⟨694613, by rfl⟩ : syracuseStep 926151 = 1389227) B1389227
theorem B926171 : Blo 924580 926171 := bstep (se 1 (by rfl) ⟨694628, by rfl⟩ : syracuseStep 926171 = 1389257) B1389257
theorem B1974793 : Blo 924580 1974793 := bstep (se 2 (by rfl) ⟨740547, by rfl⟩ : syracuseStep 1974793 = 1481095) B1481095
theorem B5284385 : Blo 924580 5284385 := bstep (se 2 (by rfl) ⟨1981644, by rfl⟩ : syracuseStep 5284385 = 3963289) B3963289
theorem B926247 : Blo 924580 926247 := bstep (se 1 (by rfl) ⟨694685, by rfl⟩ : syracuseStep 926247 = 1389371) B1389371
theorem B926287 : Blo 924580 926287 := bstep (se 1 (by rfl) ⟨694715, by rfl⟩ : syracuseStep 926287 = 1389431) B1389431
theorem B926303 : Blo 924580 926303 := bstep (se 1 (by rfl) ⟨694727, by rfl⟩ : syracuseStep 926303 = 1389455) B1389455
theorem B926331 : Blo 924580 926331 := bstep (se 1 (by rfl) ⟨694748, by rfl⟩ : syracuseStep 926331 = 1389497) B1389497
theorem B926383 : Blo 924580 926383 := bstep (se 1 (by rfl) ⟨694787, by rfl⟩ : syracuseStep 926383 = 1389575) B1389575
theorem B7021241 : Blo 924580 7021241 := bstep (se 2 (by rfl) ⟨2632965, by rfl⟩ : syracuseStep 7021241 = 5265931) B5265931
theorem B926407 : Blo 924580 926407 := bstep (se 1 (by rfl) ⟨694805, by rfl⟩ : syracuseStep 926407 = 1389611) B1389611
theorem B1188551 : Blo 924580 1188551 := bstep (se 1 (by rfl) ⟨891413, by rfl⟩ : syracuseStep 1188551 = 1782827) B1782827
theorem B926427 : Blo 924580 926427 := bstep (se 1 (by rfl) ⟨694820, by rfl⟩ : syracuseStep 926427 = 1389641) B1389641
theorem B926503 : Blo 924580 926503 := bstep (se 1 (by rfl) ⟨694877, by rfl⟩ : syracuseStep 926503 = 1389755) B1389755
theorem B926543 : Blo 924580 926543 := bstep (se 1 (by rfl) ⟨694907, by rfl⟩ : syracuseStep 926543 = 1389815) B1389815
theorem B926559 : Blo 924580 926559 := bstep (se 1 (by rfl) ⟨694919, by rfl⟩ : syracuseStep 926559 = 1389839) B1389839
theorem B926587 : Blo 924580 926587 := bstep (se 1 (by rfl) ⟨694940, by rfl⟩ : syracuseStep 926587 = 1389881) B1389881
theorem B1876879 : Blo 924580 1876879 := bstep (se 1 (by rfl) ⟨1407659, by rfl⟩ : syracuseStep 1876879 = 2815319) B2815319
theorem B926639 : Blo 924580 926639 := bstep (se 1 (by rfl) ⟨694979, by rfl⟩ : syracuseStep 926639 = 1389959) B1389959
theorem B2499511 : Blo 924580 2499511 := bstep (se 1 (by rfl) ⟨1874633, by rfl⟩ : syracuseStep 2499511 = 3749267) B3749267
theorem B926663 : Blo 924580 926663 := bstep (se 1 (by rfl) ⟨694997, by rfl⟩ : syracuseStep 926663 = 1389995) B1389995
theorem B926683 : Blo 924580 926683 := bstep (se 1 (by rfl) ⟨695012, by rfl⟩ : syracuseStep 926683 = 1390025) B1390025
theorem B926759 : Blo 924580 926759 := bstep (se 1 (by rfl) ⟨695069, by rfl⟩ : syracuseStep 926759 = 1390139) B1390139
theorem B926799 : Blo 924580 926799 := bstep (se 1 (by rfl) ⟨695099, by rfl⟩ : syracuseStep 926799 = 1390199) B1390199
theorem B926815 : Blo 924580 926815 := bstep (se 1 (by rfl) ⟨695111, by rfl⟩ : syracuseStep 926815 = 1390223) B1390223
theorem B926843 : Blo 924580 926843 := bstep (se 1 (by rfl) ⟨695132, by rfl⟩ : syracuseStep 926843 = 1390265) B1390265
theorem B3122333 : Blo 924580 3122333 := bstep (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) B1170875
theorem B926895 : Blo 924580 926895 := bstep (se 1 (by rfl) ⟨695171, by rfl⟩ : syracuseStep 926895 = 1390343) B1390343
theorem B926919 : Blo 924580 926919 := bstep (se 1 (by rfl) ⟨695189, by rfl⟩ : syracuseStep 926919 = 1390379) B1390379
theorem B926939 : Blo 924580 926939 := bstep (se 1 (by rfl) ⟨695204, by rfl⟩ : syracuseStep 926939 = 1390409) B1390409
theorem B1320185 : Blo 924580 1320185 := bstep (se 2 (by rfl) ⟨495069, by rfl⟩ : syracuseStep 1320185 = 990139) B990139
theorem B927015 : Blo 924580 927015 := bstep (se 1 (by rfl) ⟨695261, by rfl⟩ : syracuseStep 927015 = 1390523) B1390523
theorem B927055 : Blo 924580 927055 := bstep (se 1 (by rfl) ⟨695291, by rfl⟩ : syracuseStep 927055 = 1390583) B1390583
theorem B15017309 : Blo 924580 15017309 := bstep (se 3 (by rfl) ⟨2815745, by rfl⟩ : syracuseStep 15017309 = 5631491) B5631491
theorem B927071 : Blo 924580 927071 := bstep (se 1 (by rfl) ⟨695303, by rfl⟩ : syracuseStep 927071 = 1390607) B1390607
theorem B927099 : Blo 924580 927099 := bstep (se 1 (by rfl) ⟨695324, by rfl⟩ : syracuseStep 927099 = 1390649) B1390649
theorem B927151 : Blo 924580 927151 := bstep (se 1 (by rfl) ⟨695363, by rfl⟩ : syracuseStep 927151 = 1390727) B1390727
theorem B927175 : Blo 924580 927175 := bstep (se 1 (by rfl) ⟨695381, by rfl⟩ : syracuseStep 927175 = 1390763) B1390763
theorem B927195 : Blo 924580 927195 := bstep (se 1 (by rfl) ⟨695396, by rfl⟩ : syracuseStep 927195 = 1390793) B1390793
theorem B927271 : Blo 924580 927271 := bstep (se 1 (by rfl) ⟨695453, by rfl⟩ : syracuseStep 927271 = 1390907) B1390907
theorem B927311 : Blo 924580 927311 := bstep (se 1 (by rfl) ⟨695483, by rfl⟩ : syracuseStep 927311 = 1390967) B1390967
theorem B927327 : Blo 924580 927327 := bstep (se 1 (by rfl) ⟨695495, by rfl⟩ : syracuseStep 927327 = 1390991) B1390991
theorem B927355 : Blo 924580 927355 := bstep (se 1 (by rfl) ⟨695516, by rfl⟩ : syracuseStep 927355 = 1391033) B1391033
theorem B7022213 : Blo 924580 7022213 := bstep (se 4 (by rfl) ⟨658332, by rfl⟩ : syracuseStep 7022213 = 1316665) B1316665
theorem B927407 : Blo 924580 927407 := bstep (se 1 (by rfl) ⟨695555, by rfl⟩ : syracuseStep 927407 = 1391111) B1391111
theorem B3122873 : Blo 924580 3122873 := bstep (se 2 (by rfl) ⟨1171077, by rfl⟩ : syracuseStep 3122873 = 2342155) B2342155
theorem B927431 : Blo 924580 927431 := bstep (se 1 (by rfl) ⟨695573, by rfl⟩ : syracuseStep 927431 = 1391147) B1391147
theorem B3516119 : Blo 924580 3516119 := bstep (se 1 (by rfl) ⟨2637089, by rfl⟩ : syracuseStep 3516119 = 5274179) B5274179
theorem B927451 : Blo 924580 927451 := bstep (se 1 (by rfl) ⟨695588, by rfl⟩ : syracuseStep 927451 = 1391177) B1391177
theorem B927527 : Blo 924580 927527 := bstep (se 1 (by rfl) ⟨695645, by rfl⟩ : syracuseStep 927527 = 1391291) B1391291
theorem B927567 : Blo 924580 927567 := bstep (se 1 (by rfl) ⟨695675, by rfl⟩ : syracuseStep 927567 = 1391351) B1391351
theorem B927583 : Blo 924580 927583 := bstep (se 1 (by rfl) ⟨695687, by rfl⟩ : syracuseStep 927583 = 1391375) B1391375
theorem B927611 : Blo 924580 927611 := bstep (se 1 (by rfl) ⟨695708, by rfl⟩ : syracuseStep 927611 = 1391417) B1391417
theorem B927663 : Blo 924580 927663 := bstep (se 1 (by rfl) ⟨695747, by rfl⟩ : syracuseStep 927663 = 1391495) B1391495
theorem B927687 : Blo 924580 927687 := bstep (se 1 (by rfl) ⟨695765, by rfl⟩ : syracuseStep 927687 = 1391531) B1391531
theorem B927707 : Blo 924580 927707 := bstep (se 1 (by rfl) ⟨695780, by rfl⟩ : syracuseStep 927707 = 1391561) B1391561
theorem B927783 : Blo 924580 927783 := bstep (se 1 (by rfl) ⟨695837, by rfl⟩ : syracuseStep 927783 = 1391675) B1391675
theorem B1321039 : Blo 924580 1321039 := bstep (se 1 (by rfl) ⟨990779, by rfl⟩ : syracuseStep 1321039 = 1981559) B1981559
theorem B927823 : Blo 924580 927823 := bstep (se 1 (by rfl) ⟨695867, by rfl⟩ : syracuseStep 927823 = 1391735) B1391735
theorem B927839 : Blo 924580 927839 := bstep (se 1 (by rfl) ⟨695879, by rfl⟩ : syracuseStep 927839 = 1391759) B1391759
theorem B927867 : Blo 924580 927867 := bstep (se 1 (by rfl) ⟨695900, by rfl⟩ : syracuseStep 927867 = 1391801) B1391801
theorem B927919 : Blo 924580 927919 := bstep (se 1 (by rfl) ⟨695939, by rfl⟩ : syracuseStep 927919 = 1391879) B1391879
theorem B927943 : Blo 924580 927943 := bstep (se 1 (by rfl) ⟨695957, by rfl⟩ : syracuseStep 927943 = 1391915) B1391915
theorem B927963 : Blo 924580 927963 := bstep (se 1 (by rfl) ⟨695972, by rfl⟩ : syracuseStep 927963 = 1391945) B1391945
theorem B11872493 : Blo 924580 11872493 := bstep (se 3 (by rfl) ⟨2226092, by rfl⟩ : syracuseStep 11872493 = 4452185) B4452185
theorem B3123467 : Blo 924580 3123467 := bstep (se 1 (by rfl) ⟨2342600, by rfl⟩ : syracuseStep 3123467 = 4685201) B4685201
theorem B928039 : Blo 924580 928039 := bstep (se 1 (by rfl) ⟨696029, by rfl⟩ : syracuseStep 928039 = 1392059) B1392059
theorem B928079 : Blo 924580 928079 := bstep (se 1 (by rfl) ⟨696059, by rfl⟩ : syracuseStep 928079 = 1392119) B1392119
theorem B928095 : Blo 924580 928095 := bstep (se 1 (by rfl) ⟨696071, by rfl⟩ : syracuseStep 928095 = 1392143) B1392143
theorem B928123 : Blo 924580 928123 := bstep (se 1 (by rfl) ⟨696092, by rfl⟩ : syracuseStep 928123 = 1392185) B1392185
theorem B928175 : Blo 924580 928175 := bstep (se 1 (by rfl) ⟨696131, by rfl⟩ : syracuseStep 928175 = 1392263) B1392263
theorem B1386935 : Blo 924580 1386935 := bstep (se 1 (by rfl) ⟨1040201, by rfl⟩ : syracuseStep 1386935 = 2080403) B2080403
theorem B928199 : Blo 924580 928199 := bstep (se 1 (by rfl) ⟨696149, by rfl⟩ : syracuseStep 928199 = 1392299) B1392299
theorem B1386971 : Blo 924580 1386971 := bstep (se 1 (by rfl) ⟨1040228, by rfl⟩ : syracuseStep 1386971 = 2080457) B2080457
theorem B928219 : Blo 924580 928219 := bstep (se 1 (by rfl) ⟨696164, by rfl⟩ : syracuseStep 928219 = 1392329) B1392329
theorem B3123737 : Blo 924580 3123737 := bstep (se 2 (by rfl) ⟨1171401, by rfl⟩ : syracuseStep 3123737 = 2342803) B2342803
theorem B928295 : Blo 924580 928295 := bstep (se 1 (by rfl) ⟨696221, by rfl⟩ : syracuseStep 928295 = 1392443) B1392443
theorem B928335 : Blo 924580 928335 := bstep (se 1 (by rfl) ⟨696251, by rfl⟩ : syracuseStep 928335 = 1392503) B1392503
theorem B928351 : Blo 924580 928351 := bstep (se 1 (by rfl) ⟨696263, by rfl⟩ : syracuseStep 928351 = 1392527) B1392527
theorem B928379 : Blo 924580 928379 := bstep (se 1 (by rfl) ⟨696284, by rfl⟩ : syracuseStep 928379 = 1392569) B1392569
theorem B928431 : Blo 924580 928431 := bstep (se 1 (by rfl) ⟨696323, by rfl⟩ : syracuseStep 928431 = 1392647) B1392647
theorem B1780423 : Blo 924580 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B928455 : Blo 924580 928455 := bstep (se 1 (by rfl) ⟨696341, by rfl⟩ : syracuseStep 928455 = 1392683) B1392683
theorem B928475 : Blo 924580 928475 := bstep (se 1 (by rfl) ⟨696356, by rfl⟩ : syracuseStep 928475 = 1392713) B1392713
theorem B7514909 : Blo 924580 7514909 := bstep (se 3 (by rfl) ⟨1409045, by rfl⟩ : syracuseStep 7514909 = 2818091) B2818091
theorem B928551 : Blo 924580 928551 := bstep (se 1 (by rfl) ⟨696413, by rfl⟩ : syracuseStep 928551 = 1392827) B1392827
theorem B4762475 : Blo 924580 4762475 := bstep (se 1 (by rfl) ⟨3571856, by rfl⟩ : syracuseStep 4762475 = 7143713) B7143713
theorem B3517303 : Blo 924580 3517303 := bstep (se 1 (by rfl) ⟨2637977, by rfl⟩ : syracuseStep 3517303 = 5275955) B5275955
theorem B2010017 : Blo 924580 2010017 := bstep (se 2 (by rfl) ⟨753756, by rfl⟩ : syracuseStep 2010017 = 1507513) B1507513
theorem B1387439 : Blo 924580 1387439 := bstep (se 1 (by rfl) ⟨1040579, by rfl⟩ : syracuseStep 1387439 = 2081159) B2081159
theorem B5647279 : Blo 924580 5647279 := bstep (se 1 (by rfl) ⟨4235459, by rfl⟩ : syracuseStep 5647279 = 8470919) B8470919
theorem B1387529 : Blo 924580 1387529 := bstep (se 2 (by rfl) ⟨520323, by rfl⟩ : syracuseStep 1387529 = 1040647) B1040647
theorem B1387559 : Blo 924580 1387559 := bstep (se 1 (by rfl) ⟨1040669, by rfl⟩ : syracuseStep 1387559 = 2081339) B2081339
theorem B1387643 : Blo 924580 1387643 := bstep (se 1 (by rfl) ⟨1040732, by rfl⟩ : syracuseStep 1387643 = 2081465) B2081465
theorem B1387769 : Blo 924580 1387769 := bstep (se 2 (by rfl) ⟨520413, by rfl⟩ : syracuseStep 1387769 = 1040827) B1040827
theorem B1780985 : Blo 924580 1780985 := bstep (se 2 (by rfl) ⟨667869, by rfl⟩ : syracuseStep 1780985 = 1335739) B1335739
theorem B10038563 : Blo 924580 10038563 := bstep (se 1 (by rfl) ⟨7528922, by rfl⟩ : syracuseStep 10038563 = 15057845) B15057845
theorem B1387871 : Blo 924580 1387871 := bstep (se 1 (by rfl) ⟨1040903, by rfl⟩ : syracuseStep 1387871 = 2081807) B2081807
theorem B1387883 : Blo 924580 1387883 := bstep (se 1 (by rfl) ⟨1040912, by rfl⟩ : syracuseStep 1387883 = 2081825) B2081825
theorem B14462381 : Blo 924580 14462381 := bstep (se 3 (by rfl) ⟨2711696, by rfl⟩ : syracuseStep 14462381 = 5423393) B5423393
theorem B1879571 : Blo 924580 1879571 := bstep (se 1 (by rfl) ⟨1409678, by rfl⟩ : syracuseStep 1879571 = 2819357) B2819357
theorem B1388111 : Blo 924580 1388111 := bstep (se 1 (by rfl) ⟨1041083, by rfl⟩ : syracuseStep 1388111 = 2082167) B2082167
theorem B3124871 : Blo 924580 3124871 := bstep (se 1 (by rfl) ⟨2343653, by rfl⟩ : syracuseStep 3124871 = 4687307) B4687307
theorem B3124925 : Blo 924580 3124925 := bstep (se 3 (by rfl) ⟨585923, by rfl⟩ : syracuseStep 3124925 = 1171847) B1171847
theorem B1388231 : Blo 924580 1388231 := bstep (se 1 (by rfl) ⟨1041173, by rfl⟩ : syracuseStep 1388231 = 2082347) B2082347
theorem B32059097 : Blo 924580 32059097 := bstep (se 2 (by rfl) ⟨12022161, by rfl⟩ : syracuseStep 32059097 = 24044323) B24044323
theorem B3518275 : Blo 924580 3518275 := bstep (se 1 (by rfl) ⟨2638706, by rfl⟩ : syracuseStep 3518275 = 5277413) B5277413
theorem B3125087 : Blo 924580 3125087 := bstep (se 1 (by rfl) ⟨2343815, by rfl⟩ : syracuseStep 3125087 = 4687631) B4687631
theorem B1388393 : Blo 924580 1388393 := bstep (se 2 (by rfl) ⟨520647, by rfl⟩ : syracuseStep 1388393 = 1041295) B1041295
theorem B1388471 : Blo 924580 1388471 := bstep (se 1 (by rfl) ⟨1041353, by rfl⟩ : syracuseStep 1388471 = 2082707) B2082707
theorem B1388507 : Blo 924580 1388507 := bstep (se 1 (by rfl) ⟨1041380, by rfl⟩ : syracuseStep 1388507 = 2082761) B2082761
theorem B1486811 : Blo 924580 1486811 := bstep (se 1 (by rfl) ⟨1115108, by rfl⟩ : syracuseStep 1486811 = 2230217) B2230217
theorem B3125249 : Blo 924580 3125249 := bstep (se 2 (by rfl) ⟨1171968, by rfl⟩ : syracuseStep 3125249 = 2343937) B2343937
theorem B7024643 : Blo 924580 7024643 := bstep (se 1 (by rfl) ⟨5268482, by rfl⟩ : syracuseStep 7024643 = 10536965) B10536965
theorem B3518579 : Blo 924580 3518579 := bstep (se 1 (by rfl) ⟨2638934, by rfl⟩ : syracuseStep 3518579 = 5277869) B5277869
theorem B1388975 : Blo 924580 1388975 := bstep (se 1 (by rfl) ⟨1041731, by rfl⟩ : syracuseStep 1388975 = 2083463) B2083463
theorem B1978843 : Blo 924580 1978843 := bstep (se 1 (by rfl) ⟨1484132, by rfl⟩ : syracuseStep 1978843 = 2968265) B2968265
theorem B1389065 : Blo 924580 1389065 := bstep (se 2 (by rfl) ⟨520899, by rfl⟩ : syracuseStep 1389065 = 1041799) B1041799
theorem B1389095 : Blo 924580 1389095 := bstep (se 1 (by rfl) ⟨1041821, by rfl⟩ : syracuseStep 1389095 = 2083643) B2083643
theorem B3519035 : Blo 924580 3519035 := bstep (se 1 (by rfl) ⟨2639276, by rfl⟩ : syracuseStep 3519035 = 5278553) B5278553
theorem B1389179 : Blo 924580 1389179 := bstep (se 1 (by rfl) ⟨1041884, by rfl⟩ : syracuseStep 1389179 = 2083769) B2083769
theorem B4698809 : Blo 924580 4698809 := bstep (se 2 (by rfl) ⟨1762053, by rfl⟩ : syracuseStep 4698809 = 3524107) B3524107
theorem B1389305 : Blo 924580 1389305 := bstep (se 2 (by rfl) ⟨520989, by rfl⟩ : syracuseStep 1389305 = 1041979) B1041979
theorem B3126059 : Blo 924580 3126059 := bstep (se 1 (by rfl) ⟨2344544, by rfl⟩ : syracuseStep 3126059 = 4689089) B4689089
theorem B1127263 : Blo 924580 1127263 := bstep (se 1 (by rfl) ⟨845447, by rfl⟩ : syracuseStep 1127263 = 1690895) B1690895
theorem B1389407 : Blo 924580 1389407 := bstep (se 1 (by rfl) ⟨1042055, by rfl⟩ : syracuseStep 1389407 = 2084111) B2084111
theorem B1389419 : Blo 924580 1389419 := bstep (se 1 (by rfl) ⟨1042064, by rfl⟩ : syracuseStep 1389419 = 2084129) B2084129
theorem B3126329 : Blo 924580 3126329 := bstep (se 2 (by rfl) ⟨1172373, by rfl⟩ : syracuseStep 3126329 = 2344747) B2344747
theorem B1881145 : Blo 924580 1881145 := bstep (se 2 (by rfl) ⟨705429, by rfl⟩ : syracuseStep 1881145 = 1410859) B1410859
theorem B1389647 : Blo 924580 1389647 := bstep (se 1 (by rfl) ⟨1042235, by rfl⟩ : syracuseStep 1389647 = 2084471) B2084471
theorem B1389767 : Blo 924580 1389767 := bstep (se 1 (by rfl) ⟨1042325, by rfl⟩ : syracuseStep 1389767 = 2084651) B2084651
theorem B2962793 : Blo 924580 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B1389929 : Blo 924580 1389929 := bstep (se 2 (by rfl) ⟨521223, by rfl⟩ : syracuseStep 1389929 = 1042447) B1042447
theorem B3126653 : Blo 924580 3126653 := bstep (se 3 (by rfl) ⟨586247, by rfl⟩ : syracuseStep 3126653 = 1172495) B1172495
theorem B2962831 : Blo 924580 2962831 := bstep (se 1 (by rfl) ⟨2222123, by rfl⟩ : syracuseStep 2962831 = 4444247) B4444247
theorem B1783201 : Blo 924580 1783201 := bstep (se 2 (by rfl) ⟨668700, by rfl⟩ : syracuseStep 1783201 = 1337401) B1337401
theorem B1390007 : Blo 924580 1390007 := bstep (se 1 (by rfl) ⟨1042505, by rfl⟩ : syracuseStep 1390007 = 2085011) B2085011
theorem B2962907 : Blo 924580 2962907 := bstep (se 1 (by rfl) ⟨2222180, by rfl⟩ : syracuseStep 2962907 = 4444361) B4444361
theorem B1390043 : Blo 924580 1390043 := bstep (se 1 (by rfl) ⟨1042532, by rfl⟩ : syracuseStep 1390043 = 2085065) B2085065
theorem B3126923 : Blo 924580 3126923 := bstep (se 1 (by rfl) ⟨2345192, by rfl⟩ : syracuseStep 3126923 = 4690385) B4690385
theorem B6666079 : Blo 924580 6666079 := bstep (se 1 (by rfl) ⟨4999559, by rfl⟩ : syracuseStep 6666079 = 9999119) B9999119
theorem B1390511 : Blo 924580 1390511 := bstep (se 1 (by rfl) ⟨1042883, by rfl⟩ : syracuseStep 1390511 = 2085767) B2085767
theorem B1390601 : Blo 924580 1390601 := bstep (se 2 (by rfl) ⟨521475, by rfl⟩ : syracuseStep 1390601 = 1042951) B1042951
theorem B1390631 : Blo 924580 1390631 := bstep (se 1 (by rfl) ⟨1042973, by rfl⟩ : syracuseStep 1390631 = 2085947) B2085947
theorem B40024151 : Blo 924580 40024151 := bstep (se 1 (by rfl) ⟨30018113, by rfl⟩ : syracuseStep 40024151 = 60036227) B60036227
theorem B1390715 : Blo 924580 1390715 := bstep (se 1 (by rfl) ⟨1043036, by rfl⟩ : syracuseStep 1390715 = 2086073) B2086073
theorem B1390841 : Blo 924580 1390841 := bstep (se 2 (by rfl) ⟨521565, by rfl⟩ : syracuseStep 1390841 = 1043131) B1043131
theorem B1882361 : Blo 924580 1882361 := bstep (se 2 (by rfl) ⟨705885, by rfl⟩ : syracuseStep 1882361 = 1411771) B1411771
theorem B1390943 : Blo 924580 1390943 := bstep (se 1 (by rfl) ⟨1043207, by rfl⟩ : syracuseStep 1390943 = 2086415) B2086415
theorem B1390955 : Blo 924580 1390955 := bstep (se 1 (by rfl) ⟨1043216, by rfl⟩ : syracuseStep 1390955 = 2086433) B2086433
theorem B7027073 : Blo 924580 7027073 := bstep (se 2 (by rfl) ⟨2635152, by rfl⟩ : syracuseStep 7027073 = 5270305) B5270305
theorem B10566125 : Blo 924580 10566125 := bstep (se 3 (by rfl) ⟨1981148, by rfl⟩ : syracuseStep 10566125 = 3962297) B3962297
theorem B3127841 : Blo 924580 3127841 := bstep (se 2 (by rfl) ⟨1172940, by rfl⟩ : syracuseStep 3127841 = 2345881) B2345881
theorem B2636327 : Blo 924580 2636327 := bstep (se 1 (by rfl) ⟨1977245, by rfl⟩ : syracuseStep 2636327 = 3954491) B3954491
theorem B1391183 : Blo 924580 1391183 := bstep (se 1 (by rfl) ⟨1043387, by rfl⟩ : syracuseStep 1391183 = 2086775) B2086775
theorem B6666887 : Blo 924580 6666887 := bstep (se 1 (by rfl) ⟨5000165, by rfl⟩ : syracuseStep 6666887 = 10000331) B10000331
theorem B1391303 : Blo 924580 1391303 := bstep (se 1 (by rfl) ⟨1043477, by rfl⟩ : syracuseStep 1391303 = 2086955) B2086955
theorem B3128057 : Blo 924580 3128057 := bstep (se 2 (by rfl) ⟨1173021, by rfl⟩ : syracuseStep 3128057 = 2346043) B2346043
theorem B1391465 : Blo 924580 1391465 := bstep (se 2 (by rfl) ⟨521799, by rfl⟩ : syracuseStep 1391465 = 1043599) B1043599
theorem B3750839 : Blo 924580 3750839 := bstep (se 1 (by rfl) ⟨2813129, by rfl⟩ : syracuseStep 3750839 = 5626259) B5626259
theorem B1391543 : Blo 924580 1391543 := bstep (se 1 (by rfl) ⟨1043657, by rfl⟩ : syracuseStep 1391543 = 2087315) B2087315
theorem B1391579 : Blo 924580 1391579 := bstep (se 1 (by rfl) ⟨1043684, by rfl⟩ : syracuseStep 1391579 = 2087369) B2087369
theorem B3128327 : Blo 924580 3128327 := bstep (se 1 (by rfl) ⟨2346245, by rfl⟩ : syracuseStep 3128327 = 4692491) B4692491
theorem B3128435 : Blo 924580 3128435 := bstep (se 1 (by rfl) ⟨2346326, by rfl⟩ : syracuseStep 3128435 = 4692653) B4692653
theorem B2342135 : Blo 924580 2342135 := bstep (se 1 (by rfl) ⟨1756601, by rfl⟩ : syracuseStep 2342135 = 3513203) B3513203
theorem B3128705 : Blo 924580 3128705 := bstep (se 2 (by rfl) ⟨1173264, by rfl⟩ : syracuseStep 3128705 = 2346529) B2346529
theorem B1392047 : Blo 924580 1392047 := bstep (se 1 (by rfl) ⟨1044035, by rfl⟩ : syracuseStep 1392047 = 2088071) B2088071
theorem B1392137 : Blo 924580 1392137 := bstep (se 2 (by rfl) ⟨522051, by rfl⟩ : syracuseStep 1392137 = 1044103) B1044103
theorem B22560295 : Blo 924580 22560295 := bstep (se 1 (by rfl) ⟨16920221, by rfl⟩ : syracuseStep 22560295 = 33840443) B33840443
theorem B1392167 : Blo 924580 1392167 := bstep (se 1 (by rfl) ⟨1044125, by rfl⟩ : syracuseStep 1392167 = 2088251) B2088251
theorem B12697175 : Blo 924580 12697175 := bstep (se 1 (by rfl) ⟨9522881, by rfl⟩ : syracuseStep 12697175 = 19045763) B19045763
theorem B1392251 : Blo 924580 1392251 := bstep (se 1 (by rfl) ⟨1044188, by rfl⟩ : syracuseStep 1392251 = 2088377) B2088377
theorem B1392377 : Blo 924580 1392377 := bstep (se 2 (by rfl) ⟨522141, by rfl⟩ : syracuseStep 1392377 = 1044283) B1044283
theorem B1982303 : Blo 924580 1982303 := bstep (se 1 (by rfl) ⟨1486727, by rfl⟩ : syracuseStep 1982303 = 2973455) B2973455
theorem B1392479 : Blo 924580 1392479 := bstep (se 1 (by rfl) ⟨1044359, by rfl⟩ : syracuseStep 1392479 = 2088719) B2088719
theorem B2080619 : Blo 924580 2080619 := bstep (se 1 (by rfl) ⟨1560464, by rfl⟩ : syracuseStep 2080619 = 3120929) B3120929
theorem B1392491 : Blo 924580 1392491 := bstep (se 1 (by rfl) ⟨1044368, by rfl⟩ : syracuseStep 1392491 = 2088737) B2088737
theorem B2965367 : Blo 924580 2965367 := bstep (se 1 (by rfl) ⟨2224025, by rfl⟩ : syracuseStep 2965367 = 4448051) B4448051
theorem B1785743 : Blo 924580 1785743 := bstep (se 1 (by rfl) ⟨1339307, by rfl⟩ : syracuseStep 1785743 = 2678615) B2678615
theorem B2080673 : Blo 924580 2080673 := bstep (se 2 (by rfl) ⟨780252, by rfl⟩ : syracuseStep 2080673 = 1560505) B1560505
theorem B107135011 : Blo 924580 107135011 := bstep (se 1 (by rfl) ⟨80351258, by rfl⟩ : syracuseStep 107135011 = 160702517) B160702517
theorem B1392719 : Blo 924580 1392719 := bstep (se 1 (by rfl) ⟨1044539, by rfl⟩ : syracuseStep 1392719 = 2089079) B2089079
theorem B2965675 : Blo 924580 2965675 := bstep (se 1 (by rfl) ⟨2224256, by rfl⟩ : syracuseStep 2965675 = 4448513) B4448513
theorem B3129515 : Blo 924580 3129515 := bstep (se 1 (by rfl) ⟨2347136, by rfl⟩ : syracuseStep 3129515 = 4694273) B4694273
theorem B1392839 : Blo 924580 1392839 := bstep (se 1 (by rfl) ⟨1044629, by rfl⟩ : syracuseStep 1392839 = 2089259) B2089259
theorem B2081015 : Blo 924580 2081015 := bstep (se 1 (by rfl) ⟨1560761, by rfl⟩ : syracuseStep 2081015 = 3121523) B3121523
theorem B6766849 : Blo 924580 6766849 := bstep (se 2 (by rfl) ⟨2537568, by rfl⟩ : syracuseStep 6766849 = 5075137) B5075137
theorem B2638433 : Blo 924580 2638433 := bstep (se 2 (by rfl) ⟨989412, by rfl⟩ : syracuseStep 2638433 = 1978825) B1978825
theorem B2343563 : Blo 924580 2343563 := bstep (se 1 (by rfl) ⟨1757672, by rfl⟩ : syracuseStep 2343563 = 3515345) B3515345
theorem B3130055 : Blo 924580 3130055 := bstep (se 1 (by rfl) ⟨2347541, by rfl⟩ : syracuseStep 3130055 = 4695083) B4695083
theorem B2081609 : Blo 924580 2081609 := bstep (se 2 (by rfl) ⟨780603, by rfl⟩ : syracuseStep 2081609 = 1561207) B1561207
theorem B2343775 : Blo 924580 2343775 := bstep (se 1 (by rfl) ⟨1757831, by rfl⟩ : syracuseStep 2343775 = 3515663) B3515663
theorem B3130919 : Blo 924580 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B2082401 : Blo 924580 2082401 := bstep (se 2 (by rfl) ⟨780900, by rfl⟩ : syracuseStep 2082401 = 1561801) B1561801
theorem B2967137 : Blo 924580 2967137 := bstep (se 2 (by rfl) ⟨1112676, by rfl⟩ : syracuseStep 2967137 = 2225353) B2225353
theorem B3131027 : Blo 924580 3131027 := bstep (se 1 (by rfl) ⟨2348270, by rfl⟩ : syracuseStep 3131027 = 4696541) B4696541
theorem B2344697 : Blo 924580 2344697 := bstep (se 2 (by rfl) ⟨879261, by rfl⟩ : syracuseStep 2344697 = 1758523) B1758523
theorem B3524381 : Blo 924580 3524381 := bstep (se 3 (by rfl) ⟨660821, by rfl⟩ : syracuseStep 3524381 = 1321643) B1321643
theorem B3753823 : Blo 924580 3753823 := bstep (se 1 (by rfl) ⟨2815367, by rfl⟩ : syracuseStep 3753823 = 5630735) B5630735
theorem B3131243 : Blo 924580 3131243 := bstep (se 1 (by rfl) ⟨2348432, by rfl⟩ : syracuseStep 3131243 = 4696865) B4696865
theorem B3131297 : Blo 924580 3131297 := bstep (se 2 (by rfl) ⟨1174236, by rfl⟩ : syracuseStep 3131297 = 2348473) B2348473
theorem B2082743 : Blo 924580 2082743 := bstep (se 1 (by rfl) ⟨1562057, by rfl⟩ : syracuseStep 2082743 = 3124115) B3124115
theorem B2639891 : Blo 924580 2639891 := bstep (se 1 (by rfl) ⟨1979918, by rfl⟩ : syracuseStep 2639891 = 3959837) B3959837
theorem B11290661 : Blo 924580 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B2345345 : Blo 924580 2345345 := bstep (se 2 (by rfl) ⟨879504, by rfl⟩ : syracuseStep 2345345 = 1759009) B1759009
theorem B3525065 : Blo 924580 3525065 := bstep (se 2 (by rfl) ⟨1321899, by rfl⟩ : syracuseStep 3525065 = 2643799) B2643799
theorem B2640347 : Blo 924580 2640347 := bstep (se 1 (by rfl) ⟨1980260, by rfl⟩ : syracuseStep 2640347 = 3960521) B3960521
theorem B3131891 : Blo 924580 3131891 := bstep (se 1 (by rfl) ⟨2348918, by rfl⟩ : syracuseStep 3131891 = 4697837) B4697837
theorem B2083337 : Blo 924580 2083337 := bstep (se 2 (by rfl) ⟨781251, by rfl⟩ : syracuseStep 2083337 = 1562503) B1562503
theorem B1526521 : Blo 924580 1526521 := bstep (se 2 (by rfl) ⟨572445, by rfl⟩ : syracuseStep 1526521 = 1144891) B1144891
theorem B14240605 : Blo 924580 14240605 := bstep (se 3 (by rfl) ⟨2670113, by rfl⟩ : syracuseStep 14240605 = 5340227) B5340227
theorem B2083679 : Blo 924580 2083679 := bstep (se 1 (by rfl) ⟨1562759, by rfl⟩ : syracuseStep 2083679 = 3125519) B3125519
theorem B1756009 : Blo 924580 1756009 := bstep (se 2 (by rfl) ⟨658503, by rfl⟩ : syracuseStep 1756009 = 1317007) B1317007
theorem B2411371 : Blo 924580 2411371 := bstep (se 1 (by rfl) ⟨1808528, by rfl⟩ : syracuseStep 2411371 = 3617057) B3617057
theorem B3525551 : Blo 924580 3525551 := bstep (se 1 (by rfl) ⟨2644163, by rfl⟩ : syracuseStep 3525551 = 5288327) B5288327
theorem B3132431 : Blo 924580 3132431 := bstep (se 1 (by rfl) ⟨2349323, by rfl⟩ : syracuseStep 3132431 = 4698647) B4698647
theorem B2083859 : Blo 924580 2083859 := bstep (se 1 (by rfl) ⟨1562894, by rfl⟩ : syracuseStep 2083859 = 3125789) B3125789
theorem B2346155 : Blo 924580 2346155 := bstep (se 1 (by rfl) ⟨1759616, by rfl⟩ : syracuseStep 2346155 = 3519233) B3519233
theorem B2084201 : Blo 924580 2084201 := bstep (se 2 (by rfl) ⟨781575, by rfl⟩ : syracuseStep 2084201 = 1563151) B1563151
theorem B2674063 : Blo 924580 2674063 := bstep (se 1 (by rfl) ⟨2005547, by rfl⟩ : syracuseStep 2674063 = 4011095) B4011095
theorem B3952115 : Blo 924580 3952115 := bstep (se 1 (by rfl) ⟨2964086, by rfl⟩ : syracuseStep 3952115 = 5928173) B5928173
theorem B2674201 : Blo 924580 2674201 := bstep (se 2 (by rfl) ⟨1002825, by rfl⟩ : syracuseStep 2674201 = 2005651) B2005651
theorem B3133025 : Blo 924580 3133025 := bstep (se 2 (by rfl) ⟨1174884, by rfl⟩ : syracuseStep 3133025 = 2349769) B2349769
theorem B1560235 : Blo 924580 1560235 := bstep (se 1 (by rfl) ⟨1170176, by rfl⟩ : syracuseStep 1560235 = 2340353) B2340353
theorem B1756883 : Blo 924580 1756883 := bstep (se 1 (by rfl) ⟨1317662, by rfl⟩ : syracuseStep 1756883 = 2635325) B2635325
theorem B23711453 : Blo 924580 23711453 := bstep (se 3 (by rfl) ⟨4445897, by rfl⟩ : syracuseStep 23711453 = 8891795) B8891795
theorem B12701555 : Blo 924580 12701555 := bstep (se 1 (by rfl) ⟨9526166, by rfl⟩ : syracuseStep 12701555 = 19052333) B19052333
theorem B2084795 : Blo 924580 2084795 := bstep (se 1 (by rfl) ⟨1563596, by rfl⟩ : syracuseStep 2084795 = 3127193) B3127193
theorem B1560539 : Blo 924580 1560539 := bstep (se 1 (by rfl) ⟨1170404, by rfl⟩ : syracuseStep 1560539 = 2340809) B2340809
theorem B2347015 : Blo 924580 2347015 := bstep (se 1 (by rfl) ⟨1760261, by rfl⟩ : syracuseStep 2347015 = 3520523) B3520523
theorem B2084921 : Blo 924580 2084921 := bstep (se 2 (by rfl) ⟨781845, by rfl⟩ : syracuseStep 2084921 = 1563691) B1563691
theorem B26726597 : Blo 924580 26726597 := bstep (se 4 (by rfl) ⟨2505618, by rfl⟩ : syracuseStep 26726597 = 5011237) B5011237
theorem B1560775 : Blo 924580 1560775 := bstep (se 1 (by rfl) ⟨1170581, by rfl⟩ : syracuseStep 1560775 = 2341163) B2341163
theorem B1757513 : Blo 924580 1757513 := bstep (se 2 (by rfl) ⟨659067, by rfl⟩ : syracuseStep 1757513 = 1318135) B1318135
theorem B1560937 : Blo 924580 1560937 := bstep (se 2 (by rfl) ⟨585351, by rfl⟩ : syracuseStep 1560937 = 1170703) B1170703
theorem B2675069 : Blo 924580 2675069 := bstep (se 3 (by rfl) ⟨501575, by rfl⟩ : syracuseStep 2675069 = 1003151) B1003151
theorem B2085263 : Blo 924580 2085263 := bstep (se 1 (by rfl) ⟨1563947, by rfl⟩ : syracuseStep 2085263 = 3127895) B3127895
theorem B2347643 : Blo 924580 2347643 := bstep (se 1 (by rfl) ⟨1760732, by rfl⟩ : syracuseStep 2347643 = 3521465) B3521465
theorem B2085587 : Blo 924580 2085587 := bstep (se 1 (by rfl) ⟨1564190, by rfl⟩ : syracuseStep 2085587 = 3128381) B3128381
theorem B2347937 : Blo 924580 2347937 := bstep (se 2 (by rfl) ⟨880476, by rfl⟩ : syracuseStep 2347937 = 1760953) B1760953
theorem B1561531 : Blo 924580 1561531 := bstep (se 1 (by rfl) ⟨1171148, by rfl⟩ : syracuseStep 1561531 = 2342297) B2342297
theorem B1561639 : Blo 924580 1561639 := bstep (se 1 (by rfl) ⟨1171229, by rfl⟩ : syracuseStep 1561639 = 2342459) B2342459
theorem B1758287 : Blo 924580 1758287 := bstep (se 1 (by rfl) ⟨1318715, by rfl⟩ : syracuseStep 1758287 = 2637431) B2637431
theorem B1561963 : Blo 924580 1561963 := bstep (se 1 (by rfl) ⟨1171472, by rfl⟩ : syracuseStep 1561963 = 2342945) B2342945
theorem B2086523 : Blo 924580 2086523 := bstep (se 1 (by rfl) ⟨1564892, by rfl⟩ : syracuseStep 2086523 = 3129785) B3129785
theorem B2086649 : Blo 924580 2086649 := bstep (se 2 (by rfl) ⟨782493, by rfl⟩ : syracuseStep 2086649 = 1564987) B1564987
theorem B3954541 : Blo 924580 3954541 := bstep (se 3 (by rfl) ⟨741476, by rfl⟩ : syracuseStep 3954541 = 1482953) B1482953
theorem B2086919 : Blo 924580 2086919 := bstep (se 1 (by rfl) ⟨1565189, by rfl⟩ : syracuseStep 2086919 = 3130379) B3130379
theorem B2086991 : Blo 924580 2086991 := bstep (se 1 (by rfl) ⟨1565243, by rfl⟩ : syracuseStep 2086991 = 3130487) B3130487
theorem B1563023 : Blo 924580 1563023 := bstep (se 1 (by rfl) ⟨1172267, by rfl⟩ : syracuseStep 1563023 = 2344535) B2344535
theorem B2087387 : Blo 924580 2087387 := bstep (se 1 (by rfl) ⟨1565540, by rfl⟩ : syracuseStep 2087387 = 3131081) B3131081
theorem B2972123 : Blo 924580 2972123 := bstep (se 1 (by rfl) ⟨2229092, by rfl⟩ : syracuseStep 2972123 = 4458185) B4458185
theorem B2349607 : Blo 924580 2349607 := bstep (se 1 (by rfl) ⟨1762205, by rfl⟩ : syracuseStep 2349607 = 3524411) B3524411
theorem B1563259 : Blo 924580 1563259 := bstep (se 1 (by rfl) ⟨1172444, by rfl⟩ : syracuseStep 1563259 = 2344889) B2344889
theorem B1759943 : Blo 924580 1759943 := bstep (se 1 (by rfl) ⟨1319957, by rfl⟩ : syracuseStep 1759943 = 2639915) B2639915
theorem B5266205 : Blo 924580 5266205 := bstep (se 3 (by rfl) ⟨987413, by rfl⟩ : syracuseStep 5266205 = 1974827) B1974827
theorem B1170283 : Blo 924580 1170283 := bstep (se 1 (by rfl) ⟨877712, by rfl⟩ : syracuseStep 1170283 = 1755425) B1755425
theorem B2349931 : Blo 924580 2349931 := bstep (se 1 (by rfl) ⟨1762448, by rfl⟩ : syracuseStep 2349931 = 3524897) B3524897
theorem B3332983 : Blo 924580 3332983 := bstep (se 1 (by rfl) ⟨2499737, by rfl⟩ : syracuseStep 3332983 = 4999475) B4999475
theorem B2087855 : Blo 924580 2087855 := bstep (se 1 (by rfl) ⟨1565891, by rfl⟩ : syracuseStep 2087855 = 3131783) B3131783
theorem B2088107 : Blo 924580 2088107 := bstep (se 1 (by rfl) ⟨1566080, by rfl⟩ : syracuseStep 2088107 = 3132161) B3132161
theorem B13360301 : Blo 924580 13360301 := bstep (se 3 (by rfl) ⟨2505056, by rfl⟩ : syracuseStep 13360301 = 5010113) B5010113
theorem B1760467 : Blo 924580 1760467 := bstep (se 1 (by rfl) ⟨1320350, by rfl⟩ : syracuseStep 1760467 = 2640701) B2640701
theorem B1760687 : Blo 924580 1760687 := bstep (se 1 (by rfl) ⟨1320515, by rfl⟩ : syracuseStep 1760687 = 2641031) B2641031
theorem B5266889 : Blo 924580 5266889 := bstep (se 2 (by rfl) ⟨1975083, by rfl⟩ : syracuseStep 5266889 = 3950167) B3950167
theorem B1564123 : Blo 924580 1564123 := bstep (se 1 (by rfl) ⟨1173092, by rfl⟩ : syracuseStep 1564123 = 2346185) B2346185
theorem B2088647 : Blo 924580 2088647 := bstep (se 1 (by rfl) ⟨1566485, by rfl⟩ : syracuseStep 2088647 = 3132971) B3132971
theorem B1761097 : Blo 924580 1761097 := bstep (se 2 (by rfl) ⟨660411, by rfl⟩ : syracuseStep 1761097 = 1320823) B1320823
theorem B45047825 : Blo 924580 45047825 := bstep (se 2 (by rfl) ⟨16892934, by rfl⟩ : syracuseStep 45047825 = 33785869) B33785869
theorem B1564751 : Blo 924580 1564751 := bstep (se 1 (by rfl) ⟨1173563, by rfl⟩ : syracuseStep 1564751 = 2347127) B2347127
theorem B1171579 : Blo 924580 1171579 := bstep (se 1 (by rfl) ⟨878684, by rfl⟩ : syracuseStep 1171579 = 1757369) B1757369
theorem B1040935 : Blo 924580 1040935 := bstep (se 1 (by rfl) ⟨780701, by rfl⟩ : syracuseStep 1040935 = 1561403) B1561403
theorem B2679419 : Blo 924580 2679419 := bstep (se 1 (by rfl) ⟨2009564, by rfl⟩ : syracuseStep 2679419 = 4019129) B4019129
theorem B10019537 : Blo 924580 10019537 := bstep (se 2 (by rfl) ⟨3757326, by rfl⟩ : syracuseStep 10019537 = 7514653) B7514653
theorem B9528137 : Blo 924580 9528137 := bstep (se 2 (by rfl) ⟨3573051, by rfl⟩ : syracuseStep 9528137 = 7146103) B7146103
theorem B2974583 : Blo 924580 2974583 := bstep (se 1 (by rfl) ⟨2230937, by rfl⟩ : syracuseStep 2974583 = 4461875) B4461875
theorem B1565615 : Blo 924580 1565615 := bstep (se 1 (by rfl) ⟨1174211, by rfl⟩ : syracuseStep 1565615 = 2348423) B2348423
theorem B2974799 : Blo 924580 2974799 := bstep (se 1 (by rfl) ⟨2231099, by rfl⟩ : syracuseStep 2974799 = 4462199) B4462199
theorem B9168025 : Blo 924580 9168025 := bstep (se 2 (by rfl) ⟨3438009, by rfl⟩ : syracuseStep 9168025 = 6876019) B6876019
theorem B1566047 : Blo 924580 1566047 := bstep (se 1 (by rfl) ⟨1174535, by rfl⟩ : syracuseStep 1566047 = 2349071) B2349071
theorem B6677903 : Blo 924580 6677903 := bstep (se 1 (by rfl) ⟨5008427, by rfl⟩ : syracuseStep 6677903 = 10016855) B10016855
theorem B4449937 : Blo 924580 4449937 := bstep (se 2 (by rfl) ⟨1668726, by rfl⟩ : syracuseStep 4449937 = 3337453) B3337453
theorem B9135931 : Blo 924580 9135931 := bstep (se 1 (by rfl) ⟨6851948, by rfl⟩ : syracuseStep 9135931 = 13703897) B13703897
theorem B20309849 : Blo 924580 20309849 := bstep (se 2 (by rfl) ⟨7616193, by rfl⟩ : syracuseStep 20309849 = 15232387) B15232387
theorem B1566607 : Blo 924580 1566607 := bstep (se 1 (by rfl) ⟨1174955, by rfl⟩ : syracuseStep 1566607 = 2349911) B2349911
theorem B1173467 : Blo 924580 1173467 := bstep (se 1 (by rfl) ⟨880100, by rfl⟩ : syracuseStep 1173467 = 1760201) B1760201
theorem B3958865 : Blo 924580 3958865 := bstep (se 2 (by rfl) ⟨1484574, by rfl⟩ : syracuseStep 3958865 = 2969149) B2969149
theorem B1042555 : Blo 924580 1042555 := bstep (se 1 (by rfl) ⟨781916, by rfl⟩ : syracuseStep 1042555 = 1563833) B1563833
theorem B1501355 : Blo 924580 1501355 := bstep (se 1 (by rfl) ⟨1126016, by rfl⟩ : syracuseStep 1501355 = 2252033) B2252033
theorem B1173943 : Blo 924580 1173943 := bstep (se 1 (by rfl) ⟨880457, by rfl⟩ : syracuseStep 1173943 = 1760915) B1760915
theorem B1043023 : Blo 924580 1043023 := bstep (se 1 (by rfl) ⟨782267, by rfl⟩ : syracuseStep 1043023 = 1564535) B1564535
theorem B30043025 : Blo 924580 30043025 := bstep (se 2 (by rfl) ⟨11266134, by rfl⟩ : syracuseStep 30043025 = 22532269) B22532269
theorem B1043419 : Blo 924580 1043419 := bstep (se 1 (by rfl) ⟨782564, by rfl⟩ : syracuseStep 1043419 = 1565129) B1565129
theorem B5270579 : Blo 924580 5270579 := bstep (se 1 (by rfl) ⟨3952934, by rfl⟩ : syracuseStep 5270579 = 7905869) B7905869
theorem B5008555 : Blo 924580 5008555 := bstep (se 1 (by rfl) ⟨3756416, by rfl⟩ : syracuseStep 5008555 = 7512833) B7512833
theorem B7040195 : Blo 924580 7040195 := bstep (se 1 (by rfl) ⟨5280146, by rfl⟩ : syracuseStep 7040195 = 10560293) B10560293
theorem B1043887 : Blo 924580 1043887 := bstep (se 1 (by rfl) ⟨782915, by rfl⟩ : syracuseStep 1043887 = 1565831) B1565831
theorem B4681313 : Blo 924580 4681313 := bstep (se 2 (by rfl) ⟨1755492, by rfl⟩ : syracuseStep 4681313 = 3510985) B3510985
theorem B4222763 : Blo 924580 4222763 := bstep (se 1 (by rfl) ⟨3167072, by rfl⟩ : syracuseStep 4222763 = 6334145) B6334145
theorem B3338057 : Blo 924580 3338057 := bstep (se 2 (by rfl) ⟨1251771, by rfl⟩ : syracuseStep 3338057 = 2503543) B2503543
theorem B1044319 : Blo 924580 1044319 := bstep (se 1 (by rfl) ⟨783239, by rfl⟩ : syracuseStep 1044319 = 1566479) B1566479
theorem B3567635 : Blo 924580 3567635 := bstep (se 1 (by rfl) ⟨2675726, by rfl⟩ : syracuseStep 3567635 = 5351453) B5351453
theorem B45674675 : Blo 924580 45674675 := bstep (se 1 (by rfl) ⟨34256006, by rfl⟩ : syracuseStep 45674675 = 68512013) B68512013
theorem B3961325 : Blo 924580 3961325 := bstep (se 3 (by rfl) ⟨742748, by rfl⟩ : syracuseStep 3961325 = 1485497) B1485497
theorem B10711763 : Blo 924580 10711763 := bstep (se 1 (by rfl) ⟨8033822, by rfl⟩ : syracuseStep 10711763 = 16067645) B16067645
theorem B9630467 : Blo 924580 9630467 := bstep (se 1 (by rfl) ⟨7222850, by rfl⟩ : syracuseStep 9630467 = 14445701) B14445701
theorem B57013145 : Blo 924580 57013145 := bstep (se 2 (by rfl) ⟨21379929, by rfl⟩ : syracuseStep 57013145 = 42759859) B42759859
theorem B11891609 : Blo 924580 11891609 := bstep (se 2 (by rfl) ⟨4459353, by rfl⟩ : syracuseStep 11891609 = 8918707) B8918707
theorem B4223927 : Blo 924580 4223927 := bstep (se 1 (by rfl) ⟨3167945, by rfl⟩ : syracuseStep 4223927 = 6335891) B6335891
theorem B4682771 : Blo 924580 4682771 := bstep (se 1 (by rfl) ⟨3512078, by rfl⟩ : syracuseStep 4682771 = 7024157) B7024157
theorem B2225171 : Blo 924580 2225171 := bstep (se 1 (by rfl) ⟨1668878, by rfl⟩ : syracuseStep 2225171 = 3337757) B3337757
theorem B1111163 : Blo 924580 1111163 := bstep (se 1 (by rfl) ⟨833372, by rfl⟩ : syracuseStep 1111163 = 1666745) B1666745
theorem B7927055 : Blo 924580 7927055 := bstep (se 1 (by rfl) ⟨5945291, by rfl⟩ : syracuseStep 7927055 = 11890583) B11890583
theorem B1668539 : Blo 924580 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B1668647 : Blo 924580 1668647 := bstep (se 1 (by rfl) ⟨1251485, by rfl⟩ : syracuseStep 1668647 = 2502971) B2502971
theorem B1406663 : Blo 924580 1406663 := bstep (se 1 (by rfl) ⟨1054997, by rfl⟩ : syracuseStep 1406663 = 2109995) B2109995
theorem B3176185 : Blo 924580 3176185 := bstep (se 2 (by rfl) ⟨1191069, by rfl⟩ : syracuseStep 3176185 = 2382139) B2382139
theorem B5928889 : Blo 924580 5928889 := bstep (se 2 (by rfl) ⟨2223333, by rfl⟩ : syracuseStep 5928889 = 4446667) B4446667
theorem B4520279 : Blo 924580 4520279 := bstep (se 1 (by rfl) ⟨3390209, by rfl⟩ : syracuseStep 4520279 = 6780419) B6780419
theorem B4225385 : Blo 924580 4225385 := bstep (se 2 (by rfl) ⟨1584519, by rfl⟩ : syracuseStep 4225385 = 3169039) B3169039
theorem B15038905 : Blo 924580 15038905 := bstep (se 2 (by rfl) ⟨5639589, by rfl⟩ : syracuseStep 15038905 = 11279179) B11279179
theorem B4225517 : Blo 924580 4225517 := bstep (se 3 (by rfl) ⟨792284, by rfl⟩ : syracuseStep 4225517 = 1584569) B1584569
theorem B3963923 : Blo 924580 3963923 := bstep (se 1 (by rfl) ⟨2972942, by rfl⟩ : syracuseStep 3963923 = 5945885) B5945885
theorem B7536091 : Blo 924580 7536091 := bstep (se 1 (by rfl) ⟨5652068, by rfl⟩ : syracuseStep 7536091 = 11304137) B11304137
theorem B4685687 : Blo 924580 4685687 := bstep (se 1 (by rfl) ⟨3514265, by rfl⟩ : syracuseStep 4685687 = 7028531) B7028531
theorem B4685849 : Blo 924580 4685849 := bstep (se 2 (by rfl) ⟨1757193, by rfl⟩ : syracuseStep 4685849 = 3514387) B3514387
theorem B7045541 : Blo 924580 7045541 := bstep (se 4 (by rfl) ⟨660519, by rfl⟩ : syracuseStep 7045541 = 1321039) B1321039
theorem B2228755 : Blo 924580 2228755 := bstep (se 1 (by rfl) ⟨1671566, by rfl⟩ : syracuseStep 2228755 = 3343133) B3343133
theorem B2229601 : Blo 924580 2229601 := bstep (se 2 (by rfl) ⟨836100, by rfl⟩ : syracuseStep 2229601 = 1672201) B1672201
theorem B12224033 : Blo 924580 12224033 := bstep (se 2 (by rfl) ⟨4584012, by rfl⟩ : syracuseStep 12224033 = 9168025) B9168025
theorem B5637721 : Blo 924580 5637721 := bstep (se 2 (by rfl) ⟨2114145, by rfl⟩ : syracuseStep 5637721 = 4228291) B4228291
theorem B5933249 : Blo 924580 5933249 := bstep (se 2 (by rfl) ⟨2224968, by rfl⟩ : syracuseStep 5933249 = 4449937) B4449937
theorem B2230553 : Blo 924580 2230553 := bstep (se 2 (by rfl) ⟨836457, by rfl⟩ : syracuseStep 2230553 = 1672915) B1672915
theorem B4688765 : Blo 924580 4688765 := bstep (se 3 (by rfl) ⟨879143, by rfl⟩ : syracuseStep 4688765 = 1758287) B1758287
theorem B2035361 : Blo 924580 2035361 := bstep (se 2 (by rfl) ⟨763260, by rfl⟩ : syracuseStep 2035361 = 1526521) B1526521
theorem B3215161 : Blo 924580 3215161 := bstep (se 2 (by rfl) ⟨1205685, by rfl⟩ : syracuseStep 3215161 = 2411371) B2411371
theorem B4689737 : Blo 924580 4689737 := bstep (se 2 (by rfl) ⟨1758651, by rfl⟩ : syracuseStep 4689737 = 3517303) B3517303
theorem B3510803 : Blo 924580 3510803 := bstep (se 1 (by rfl) ⟨2633102, by rfl⟩ : syracuseStep 3510803 = 5266205) B5266205
theorem B987871 : Blo 924580 987871 := bstep (se 1 (by rfl) ⟨740903, by rfl⟩ : syracuseStep 987871 = 1481807) B1481807
theorem B10031951 : Blo 924580 10031951 := bstep (se 1 (by rfl) ⟨7523963, by rfl⟩ : syracuseStep 10031951 = 15047927) B15047927
theorem B3511259 : Blo 924580 3511259 := bstep (se 1 (by rfl) ⟨2633444, by rfl⟩ : syracuseStep 3511259 = 5266889) B5266889
theorem B4691033 : Blo 924580 4691033 := bstep (se 2 (by rfl) ⟨1759137, by rfl⟩ : syracuseStep 4691033 = 3518275) B3518275
theorem B988507 : Blo 924580 988507 := bstep (se 1 (by rfl) ⟨741380, by rfl⟩ : syracuseStep 988507 = 1482761) B1482761
theorem B5084525 : Blo 924580 5084525 := bstep (se 3 (by rfl) ⟨953348, by rfl⟩ : syracuseStep 5084525 = 1906697) B1906697
theorem B4003613 : Blo 924580 4003613 := bstep (se 3 (by rfl) ⟨750677, by rfl⟩ : syracuseStep 4003613 = 1501355) B1501355
theorem B13539899 : Blo 924580 13539899 := bstep (se 1 (by rfl) ⟨10154924, by rfl⟩ : syracuseStep 13539899 = 20309849) B20309849
theorem B924623 : Blo 924580 924623 := bstep (se 1 (by rfl) ⟨693467, by rfl⟩ : syracuseStep 924623 = 1386935) B1386935
theorem B924647 : Blo 924580 924647 := bstep (se 1 (by rfl) ⟨693485, by rfl⟩ : syracuseStep 924647 = 1386971) B1386971
theorem B20028683 : Blo 924580 20028683 := bstep (se 1 (by rfl) ⟨15021512, by rfl⟩ : syracuseStep 20028683 = 30043025) B30043025
theorem B924959 : Blo 924580 924959 := bstep (se 1 (by rfl) ⟨693719, by rfl⟩ : syracuseStep 924959 = 1387439) B1387439
theorem B925019 : Blo 924580 925019 := bstep (se 1 (by rfl) ⟨693764, by rfl⟩ : syracuseStep 925019 = 1387529) B1387529
theorem B925039 : Blo 924580 925039 := bstep (se 1 (by rfl) ⟨693779, by rfl⟩ : syracuseStep 925039 = 1387559) B1387559
theorem B3513719 : Blo 924580 3513719 := bstep (se 1 (by rfl) ⟨2635289, by rfl⟩ : syracuseStep 3513719 = 5270579) B5270579
theorem B925095 : Blo 924580 925095 := bstep (se 1 (by rfl) ⟨693821, by rfl⟩ : syracuseStep 925095 = 1387643) B1387643
theorem B4693463 : Blo 924580 4693463 := bstep (se 1 (by rfl) ⟨3520097, by rfl⟩ : syracuseStep 4693463 = 7040195) B7040195
theorem B925179 : Blo 924580 925179 := bstep (se 1 (by rfl) ⟨693884, by rfl⟩ : syracuseStep 925179 = 1387769) B1387769
theorem B6692375 : Blo 924580 6692375 := bstep (se 1 (by rfl) ⟨5019281, by rfl⟩ : syracuseStep 6692375 = 10038563) B10038563
theorem B925247 : Blo 924580 925247 := bstep (se 1 (by rfl) ⟨693935, by rfl⟩ : syracuseStep 925247 = 1387871) B1387871
theorem B925255 : Blo 924580 925255 := bstep (se 1 (by rfl) ⟨693941, by rfl⟩ : syracuseStep 925255 = 1387883) B1387883
theorem B9641587 : Blo 924580 9641587 := bstep (se 1 (by rfl) ⟨7231190, by rfl⟩ : syracuseStep 9641587 = 14462381) B14462381
theorem B4234913 : Blo 924580 4234913 := bstep (se 2 (by rfl) ⟨1588092, by rfl⟩ : syracuseStep 4234913 = 3176185) B3176185
theorem B925407 : Blo 924580 925407 := bstep (se 1 (by rfl) ⟨694055, by rfl⟩ : syracuseStep 925407 = 1388111) B1388111
theorem B3120875 : Blo 924580 3120875 := bstep (se 1 (by rfl) ⟨2340656, by rfl⟩ : syracuseStep 3120875 = 4681313) B4681313
theorem B8888105 : Blo 924580 8888105 := bstep (se 2 (by rfl) ⟨3333039, by rfl⟩ : syracuseStep 8888105 = 6666079) B6666079
theorem B925487 : Blo 924580 925487 := bstep (se 1 (by rfl) ⟨694115, by rfl⟩ : syracuseStep 925487 = 1388231) B1388231
theorem B21372731 : Blo 924580 21372731 := bstep (se 1 (by rfl) ⟨16029548, by rfl⟩ : syracuseStep 21372731 = 32059097) B32059097
theorem B925595 : Blo 924580 925595 := bstep (se 1 (by rfl) ⟨694196, by rfl⟩ : syracuseStep 925595 = 1388393) B1388393
theorem B7905185 : Blo 924580 7905185 := bstep (se 2 (by rfl) ⟨2964444, by rfl⟩ : syracuseStep 7905185 = 5928889) B5928889
theorem B925647 : Blo 924580 925647 := bstep (se 1 (by rfl) ⟨694235, by rfl⟩ : syracuseStep 925647 = 1388471) B1388471
theorem B925671 : Blo 924580 925671 := bstep (se 1 (by rfl) ⟨694253, by rfl⟩ : syracuseStep 925671 = 1388507) B1388507
theorem B991207 : Blo 924580 991207 := bstep (se 1 (by rfl) ⟨743405, by rfl⟩ : syracuseStep 991207 = 1486811) B1486811
theorem B30449783 : Blo 924580 30449783 := bstep (se 1 (by rfl) ⟨22837337, by rfl⟩ : syracuseStep 30449783 = 45674675) B45674675
theorem B925983 : Blo 924580 925983 := bstep (se 1 (by rfl) ⟨694487, by rfl⟩ : syracuseStep 925983 = 1388975) B1388975
theorem B926043 : Blo 924580 926043 := bstep (se 1 (by rfl) ⟨694532, by rfl⟩ : syracuseStep 926043 = 1389065) B1389065
theorem B926063 : Blo 924580 926063 := bstep (se 1 (by rfl) ⟨694547, by rfl⟩ : syracuseStep 926063 = 1389095) B1389095
theorem B926119 : Blo 924580 926119 := bstep (se 1 (by rfl) ⟨694589, by rfl⟩ : syracuseStep 926119 = 1389179) B1389179
theorem B926203 : Blo 924580 926203 := bstep (se 1 (by rfl) ⟨694652, by rfl⟩ : syracuseStep 926203 = 1389305) B1389305
theorem B926271 : Blo 924580 926271 := bstep (se 1 (by rfl) ⟨694703, by rfl⟩ : syracuseStep 926271 = 1389407) B1389407
theorem B926279 : Blo 924580 926279 := bstep (se 1 (by rfl) ⟨694709, by rfl⟩ : syracuseStep 926279 = 1389419) B1389419
theorem B3121847 : Blo 924580 3121847 := bstep (se 1 (by rfl) ⟨2341385, by rfl⟩ : syracuseStep 3121847 = 4682771) B4682771
theorem B1483447 : Blo 924580 1483447 := bstep (se 1 (by rfl) ⟨1112585, by rfl⟩ : syracuseStep 1483447 = 2225171) B2225171
theorem B926431 : Blo 924580 926431 := bstep (se 1 (by rfl) ⟨694823, by rfl⟩ : syracuseStep 926431 = 1389647) B1389647
theorem B42738445 : Blo 924580 42738445 := bstep (se 3 (by rfl) ⟨8013458, by rfl⟩ : syracuseStep 42738445 = 16026917) B16026917
theorem B926511 : Blo 924580 926511 := bstep (se 1 (by rfl) ⟨694883, by rfl⟩ : syracuseStep 926511 = 1389767) B1389767
theorem B5284703 : Blo 924580 5284703 := bstep (se 1 (by rfl) ⟨3963527, by rfl⟩ : syracuseStep 5284703 = 7927055) B7927055
theorem B1975195 : Blo 924580 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B926619 : Blo 924580 926619 := bstep (se 1 (by rfl) ⟨694964, by rfl⟩ : syracuseStep 926619 = 1389929) B1389929
theorem B926671 : Blo 924580 926671 := bstep (se 1 (by rfl) ⟨695003, by rfl⟩ : syracuseStep 926671 = 1390007) B1390007
theorem B1975271 : Blo 924580 1975271 := bstep (se 1 (by rfl) ⟨1481453, by rfl⟩ : syracuseStep 1975271 = 2962907) B2962907
theorem B926695 : Blo 924580 926695 := bstep (se 1 (by rfl) ⟨695021, by rfl⟩ : syracuseStep 926695 = 1390043) B1390043
theorem B927007 : Blo 924580 927007 := bstep (se 1 (by rfl) ⟨695255, by rfl⟩ : syracuseStep 927007 = 1390511) B1390511
theorem B927067 : Blo 924580 927067 := bstep (se 1 (by rfl) ⟨695300, by rfl⟩ : syracuseStep 927067 = 1390601) B1390601
theorem B927087 : Blo 924580 927087 := bstep (se 1 (by rfl) ⟨695315, by rfl⟩ : syracuseStep 927087 = 1390631) B1390631
theorem B26682767 : Blo 924580 26682767 := bstep (se 1 (by rfl) ⟨20012075, by rfl⟩ : syracuseStep 26682767 = 40024151) B40024151
theorem B927143 : Blo 924580 927143 := bstep (se 1 (by rfl) ⟨695357, by rfl⟩ : syracuseStep 927143 = 1390715) B1390715
theorem B927227 : Blo 924580 927227 := bstep (se 1 (by rfl) ⟨695420, by rfl⟩ : syracuseStep 927227 = 1390841) B1390841
theorem B1254907 : Blo 924580 1254907 := bstep (se 1 (by rfl) ⟨941180, by rfl⟩ : syracuseStep 1254907 = 1882361) B1882361
theorem B33859133 : Blo 924580 33859133 := bstep (se 3 (by rfl) ⟨6348587, by rfl⟩ : syracuseStep 33859133 = 12697175) B12697175
theorem B927295 : Blo 924580 927295 := bstep (se 1 (by rfl) ⟨695471, by rfl⟩ : syracuseStep 927295 = 1390943) B1390943
theorem B927303 : Blo 924580 927303 := bstep (se 1 (by rfl) ⟨695477, by rfl⟩ : syracuseStep 927303 = 1390955) B1390955
theorem B927455 : Blo 924580 927455 := bstep (se 1 (by rfl) ⟨695591, by rfl⟩ : syracuseStep 927455 = 1391183) B1391183
theorem B927535 : Blo 924580 927535 := bstep (se 1 (by rfl) ⟨695651, by rfl⟩ : syracuseStep 927535 = 1391303) B1391303
theorem B927643 : Blo 924580 927643 := bstep (se 1 (by rfl) ⟨695732, by rfl⟩ : syracuseStep 927643 = 1391465) B1391465
theorem B16885709 : Blo 924580 16885709 := bstep (se 3 (by rfl) ⟨3166070, by rfl⟩ : syracuseStep 16885709 = 6332141) B6332141
theorem B2500559 : Blo 924580 2500559 := bstep (se 1 (by rfl) ⟨1875419, by rfl⟩ : syracuseStep 2500559 = 3750839) B3750839
theorem B927695 : Blo 924580 927695 := bstep (se 1 (by rfl) ⟨695771, by rfl⟩ : syracuseStep 927695 = 1391543) B1391543
theorem B927719 : Blo 924580 927719 := bstep (se 1 (by rfl) ⟨695789, by rfl⟩ : syracuseStep 927719 = 1391579) B1391579
theorem B928031 : Blo 924580 928031 := bstep (se 1 (by rfl) ⟨696023, by rfl⟩ : syracuseStep 928031 = 1392047) B1392047
theorem B7907645 : Blo 924580 7907645 := bstep (se 3 (by rfl) ⟨1482683, by rfl⟩ : syracuseStep 7907645 = 2965367) B2965367
theorem B928091 : Blo 924580 928091 := bstep (se 1 (by rfl) ⟨696068, by rfl⟩ : syracuseStep 928091 = 1392137) B1392137
theorem B928111 : Blo 924580 928111 := bstep (se 1 (by rfl) ⟨696083, by rfl⟩ : syracuseStep 928111 = 1392167) B1392167
theorem B928167 : Blo 924580 928167 := bstep (se 1 (by rfl) ⟨696125, by rfl⟩ : syracuseStep 928167 = 1392251) B1392251
theorem B928251 : Blo 924580 928251 := bstep (se 1 (by rfl) ⟨696188, by rfl⟩ : syracuseStep 928251 = 1392377) B1392377
theorem B1321535 : Blo 924580 1321535 := bstep (se 1 (by rfl) ⟨991151, by rfl⟩ : syracuseStep 1321535 = 1982303) B1982303
theorem B928319 : Blo 924580 928319 := bstep (se 1 (by rfl) ⟨696239, by rfl⟩ : syracuseStep 928319 = 1392479) B1392479
theorem B1387079 : Blo 924580 1387079 := bstep (se 1 (by rfl) ⟨1040309, by rfl⟩ : syracuseStep 1387079 = 2080619) B2080619
theorem B928327 : Blo 924580 928327 := bstep (se 1 (by rfl) ⟨696245, by rfl⟩ : syracuseStep 928327 = 1392491) B1392491
theorem B3123791 : Blo 924580 3123791 := bstep (se 1 (by rfl) ⟨2342843, by rfl⟩ : syracuseStep 3123791 = 4685687) B4685687
theorem B1190495 : Blo 924580 1190495 := bstep (se 1 (by rfl) ⟨892871, by rfl⟩ : syracuseStep 1190495 = 1785743) B1785743
theorem B1387115 : Blo 924580 1387115 := bstep (se 1 (by rfl) ⟨1040336, by rfl⟩ : syracuseStep 1387115 = 2080673) B2080673
theorem B142846681 : Blo 924580 142846681 := bstep (se 2 (by rfl) ⟨53567505, by rfl⟩ : syracuseStep 142846681 = 107135011) B107135011
theorem B928479 : Blo 924580 928479 := bstep (se 1 (by rfl) ⟨696359, by rfl⟩ : syracuseStep 928479 = 1392719) B1392719
theorem B928559 : Blo 924580 928559 := bstep (se 1 (by rfl) ⟨696419, by rfl⟩ : syracuseStep 928559 = 1392839) B1392839
theorem B1387343 : Blo 924580 1387343 := bstep (se 1 (by rfl) ⟨1040507, by rfl⟩ : syracuseStep 1387343 = 2081015) B2081015
theorem B9022465 : Blo 924580 9022465 := bstep (se 2 (by rfl) ⟨3383424, by rfl⟩ : syracuseStep 9022465 = 6766849) B6766849
theorem B1387739 : Blo 924580 1387739 := bstep (se 1 (by rfl) ⟨1040804, by rfl⟩ : syracuseStep 1387739 = 2081609) B2081609
theorem B2633057 : Blo 924580 2633057 := bstep (se 2 (by rfl) ⟨987396, by rfl⟩ : syracuseStep 2633057 = 1974793) B1974793
theorem B10136951 : Blo 924580 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B1387913 : Blo 924580 1387913 := bstep (se 2 (by rfl) ⟨520467, by rfl⟩ : syracuseStep 1387913 = 1040935) B1040935
theorem B1388267 : Blo 924580 1388267 := bstep (se 1 (by rfl) ⟨1041200, by rfl⟩ : syracuseStep 1388267 = 2082401) B2082401
theorem B1978091 : Blo 924580 1978091 := bstep (se 1 (by rfl) ⟨1483568, by rfl⟩ : syracuseStep 1978091 = 2967137) B2967137
theorem B3125033 : Blo 924580 3125033 := bstep (se 2 (by rfl) ⟨1171887, by rfl⟩ : syracuseStep 3125033 = 2343775) B2343775
theorem B2502505 : Blo 924580 2502505 := bstep (se 2 (by rfl) ⟨938439, by rfl⟩ : syracuseStep 2502505 = 1876879) B1876879
theorem B1388495 : Blo 924580 1388495 := bstep (se 1 (by rfl) ⟨1041371, by rfl⟩ : syracuseStep 1388495 = 2082743) B2082743
theorem B4698323 : Blo 924580 4698323 := bstep (se 1 (by rfl) ⟨3523742, by rfl⟩ : syracuseStep 4698323 = 7047485) B7047485
theorem B1388891 : Blo 924580 1388891 := bstep (se 1 (by rfl) ⟨1041668, by rfl⟩ : syracuseStep 1388891 = 2083337) B2083337
theorem B1389119 : Blo 924580 1389119 := bstep (se 1 (by rfl) ⟨1041839, by rfl⟩ : syracuseStep 1389119 = 2083679) B2083679
theorem B1389239 : Blo 924580 1389239 := bstep (se 1 (by rfl) ⟨1041929, by rfl⟩ : syracuseStep 1389239 = 2083859) B2083859
theorem B1389467 : Blo 924580 1389467 := bstep (se 1 (by rfl) ⟨1042100, by rfl⟩ : syracuseStep 1389467 = 2084201) B2084201
theorem B2634743 : Blo 924580 2634743 := bstep (se 1 (by rfl) ⟨1976057, by rfl⟩ : syracuseStep 2634743 = 3952115) B3952115
theorem B15807635 : Blo 924580 15807635 := bstep (se 1 (by rfl) ⟨11855726, by rfl⟩ : syracuseStep 15807635 = 23711453) B23711453
theorem B8467703 : Blo 924580 8467703 := bstep (se 1 (by rfl) ⟨6350777, by rfl⟩ : syracuseStep 8467703 = 12701555) B12701555
theorem B1389863 : Blo 924580 1389863 := bstep (se 1 (by rfl) ⟨1042397, by rfl⟩ : syracuseStep 1389863 = 2084795) B2084795
theorem B1389947 : Blo 924580 1389947 := bstep (se 1 (by rfl) ⟨1042460, by rfl⟩ : syracuseStep 1389947 = 2084921) B2084921
theorem B1390073 : Blo 924580 1390073 := bstep (se 2 (by rfl) ⟨521277, by rfl⟩ : syracuseStep 1390073 = 1042555) B1042555
theorem B3520007 : Blo 924580 3520007 := bstep (se 1 (by rfl) ⟨2640005, by rfl⟩ : syracuseStep 3520007 = 5280011) B5280011
theorem B1783379 : Blo 924580 1783379 := bstep (se 1 (by rfl) ⟨1337534, by rfl⟩ : syracuseStep 1783379 = 2675069) B2675069
theorem B1390175 : Blo 924580 1390175 := bstep (se 1 (by rfl) ⟨1042631, by rfl⟩ : syracuseStep 1390175 = 2085263) B2085263
theorem B2963101 : Blo 924580 2963101 := bstep (se 3 (by rfl) ⟨555581, by rfl⟩ : syracuseStep 2963101 = 1111163) B1111163
theorem B6600503 : Blo 924580 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B1390391 : Blo 924580 1390391 := bstep (se 1 (by rfl) ⟨1042793, by rfl⟩ : syracuseStep 1390391 = 2085587) B2085587
theorem B3127247 : Blo 924580 3127247 := bstep (se 1 (by rfl) ⟨2345435, by rfl⟩ : syracuseStep 3127247 = 4690871) B4690871
theorem B3520493 : Blo 924580 3520493 := bstep (se 3 (by rfl) ⟨660092, by rfl⟩ : syracuseStep 3520493 = 1320185) B1320185
theorem B1390697 : Blo 924580 1390697 := bstep (se 2 (by rfl) ⟨521511, by rfl⟩ : syracuseStep 1390697 = 1043023) B1043023
theorem B1391015 : Blo 924580 1391015 := bstep (se 1 (by rfl) ⟨1043261, by rfl⟩ : syracuseStep 1391015 = 2086523) B2086523
theorem B2341295 : Blo 924580 2341295 := bstep (se 1 (by rfl) ⟨1755971, by rfl⟩ : syracuseStep 2341295 = 3511943) B3511943
theorem B18987473 : Blo 924580 18987473 := bstep (se 2 (by rfl) ⟨7120302, by rfl⟩ : syracuseStep 18987473 = 14240605) B14240605
theorem B3520979 : Blo 924580 3520979 := bstep (se 1 (by rfl) ⟨2640734, by rfl⟩ : syracuseStep 3520979 = 5281469) B5281469
theorem B2341345 : Blo 924580 2341345 := bstep (se 2 (by rfl) ⟨878004, by rfl⟩ : syracuseStep 2341345 = 1756009) B1756009
theorem B1391099 : Blo 924580 1391099 := bstep (se 1 (by rfl) ⟨1043324, by rfl⟩ : syracuseStep 1391099 = 2086649) B2086649
theorem B1391225 : Blo 924580 1391225 := bstep (se 2 (by rfl) ⟨521709, by rfl⟩ : syracuseStep 1391225 = 1043419) B1043419
theorem B1391279 : Blo 924580 1391279 := bstep (se 1 (by rfl) ⟨1043459, by rfl⟩ : syracuseStep 1391279 = 2086919) B2086919
theorem B1391327 : Blo 924580 1391327 := bstep (se 1 (by rfl) ⟨1043495, by rfl⟩ : syracuseStep 1391327 = 2086991) B2086991
theorem B3128219 : Blo 924580 3128219 := bstep (se 1 (by rfl) ⟨2346164, by rfl⟩ : syracuseStep 3128219 = 4692329) B4692329
theorem B1391591 : Blo 924580 1391591 := bstep (se 1 (by rfl) ⟨1043693, by rfl⟩ : syracuseStep 1391591 = 2087387) B2087387
theorem B1981415 : Blo 924580 1981415 := bstep (se 1 (by rfl) ⟨1486061, by rfl⟩ : syracuseStep 1981415 = 2972123) B2972123
theorem B3390587 : Blo 924580 3390587 := bstep (se 1 (by rfl) ⟨2542940, by rfl⟩ : syracuseStep 3390587 = 5085881) B5085881
theorem B1391849 : Blo 924580 1391849 := bstep (se 2 (by rfl) ⟨521943, by rfl⟩ : syracuseStep 1391849 = 1043887) B1043887
theorem B1391903 : Blo 924580 1391903 := bstep (se 1 (by rfl) ⟨1043927, by rfl⟩ : syracuseStep 1391903 = 2087855) B2087855
theorem B15842627 : Blo 924580 15842627 := bstep (se 1 (by rfl) ⟨11881970, by rfl⟩ : syracuseStep 15842627 = 23763941) B23763941
theorem B2342267 : Blo 924580 2342267 := bstep (se 1 (by rfl) ⟨1756700, by rfl⟩ : syracuseStep 2342267 = 3513401) B3513401
theorem B1392071 : Blo 924580 1392071 := bstep (se 1 (by rfl) ⟨1044053, by rfl⟩ : syracuseStep 1392071 = 2088107) B2088107
theorem B2080313 : Blo 924580 2080313 := bstep (se 2 (by rfl) ⟨780117, by rfl⟩ : syracuseStep 2080313 = 1560235) B1560235
theorem B3522163 : Blo 924580 3522163 := bstep (se 1 (by rfl) ⟨2641622, by rfl⟩ : syracuseStep 3522163 = 5283245) B5283245
theorem B1392425 : Blo 924580 1392425 := bstep (se 2 (by rfl) ⟨522159, by rfl⟩ : syracuseStep 1392425 = 1044319) B1044319
theorem B1392431 : Blo 924580 1392431 := bstep (se 1 (by rfl) ⟨1044323, by rfl⟩ : syracuseStep 1392431 = 2088647) B2088647
theorem B3129245 : Blo 924580 3129245 := bstep (se 3 (by rfl) ⟨586733, by rfl⟩ : syracuseStep 3129245 = 1173467) B1173467
theorem B3129353 : Blo 924580 3129353 := bstep (se 2 (by rfl) ⟨1173507, by rfl⟩ : syracuseStep 3129353 = 2347015) B2347015
theorem B30031883 : Blo 924580 30031883 := bstep (se 1 (by rfl) ⟨22523912, by rfl⟩ : syracuseStep 30031883 = 45047825) B45047825
theorem B2080979 : Blo 924580 2080979 := bstep (se 1 (by rfl) ⟨1560734, by rfl⟩ : syracuseStep 2080979 = 3121469) B3121469
theorem B2081033 : Blo 924580 2081033 := bstep (se 2 (by rfl) ⟨780387, by rfl⟩ : syracuseStep 2081033 = 1560775) B1560775
theorem B3522923 : Blo 924580 3522923 := bstep (se 1 (by rfl) ⟨2642192, by rfl⟩ : syracuseStep 3522923 = 5284385) B5284385
theorem B1786279 : Blo 924580 1786279 := bstep (se 1 (by rfl) ⟨1339709, by rfl⟩ : syracuseStep 1786279 = 2679419) B2679419
theorem B2081249 : Blo 924580 2081249 := bstep (se 2 (by rfl) ⟨780468, by rfl⟩ : syracuseStep 2081249 = 1560937) B1560937
theorem B1983055 : Blo 924580 1983055 := bstep (se 1 (by rfl) ⟨1487291, by rfl⟩ : syracuseStep 1983055 = 2974583) B2974583
theorem B2638457 : Blo 924580 2638457 := bstep (se 2 (by rfl) ⟨989421, by rfl⟩ : syracuseStep 2638457 = 1978843) B1978843
theorem B1983199 : Blo 924580 1983199 := bstep (se 1 (by rfl) ⟨1487399, by rfl⟩ : syracuseStep 1983199 = 2974799) B2974799
theorem B2081555 : Blo 924580 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B10011539 : Blo 924580 10011539 := bstep (se 1 (by rfl) ⟨7508654, by rfl⟩ : syracuseStep 10011539 = 15017309) B15017309
theorem B2081915 : Blo 924580 2081915 := bstep (se 1 (by rfl) ⟨1561436, by rfl⟩ : syracuseStep 2081915 = 3122873) B3122873
theorem B2344079 : Blo 924580 2344079 := bstep (se 1 (by rfl) ⟨1758059, by rfl⟩ : syracuseStep 2344079 = 3516119) B3516119
theorem B2082041 : Blo 924580 2082041 := bstep (se 2 (by rfl) ⟨780765, by rfl⟩ : syracuseStep 2082041 = 1561531) B1561531
theorem B2082185 : Blo 924580 2082185 := bstep (se 2 (by rfl) ⟨780819, by rfl⟩ : syracuseStep 2082185 = 1561639) B1561639
theorem B2639243 : Blo 924580 2639243 := bstep (se 1 (by rfl) ⟨1979432, by rfl⟩ : syracuseStep 2639243 = 3958865) B3958865
theorem B2508193 : Blo 924580 2508193 := bstep (se 2 (by rfl) ⟨940572, by rfl⟩ : syracuseStep 2508193 = 1881145) B1881145
theorem B7914995 : Blo 924580 7914995 := bstep (se 1 (by rfl) ⟨5936246, by rfl⟩ : syracuseStep 7914995 = 11872493) B11872493
theorem B2082311 : Blo 924580 2082311 := bstep (se 1 (by rfl) ⟨1561733, by rfl⟩ : syracuseStep 2082311 = 3123467) B3123467
theorem B5949085 : Blo 924580 5949085 := bstep (se 3 (by rfl) ⟨1115453, by rfl⟩ : syracuseStep 5949085 = 2230907) B2230907
theorem B2082491 : Blo 924580 2082491 := bstep (se 1 (by rfl) ⟨1561868, by rfl⟩ : syracuseStep 2082491 = 3123737) B3123737
theorem B17778365 : Blo 924580 17778365 := bstep (se 3 (by rfl) ⟨3333443, by rfl⟩ : syracuseStep 17778365 = 6666887) B6666887
theorem B2082617 : Blo 924580 2082617 := bstep (se 2 (by rfl) ⟨780981, by rfl⟩ : syracuseStep 2082617 = 1561963) B1561963
theorem B3950441 : Blo 924580 3950441 := bstep (se 2 (by rfl) ⟨1481415, by rfl⟩ : syracuseStep 3950441 = 2962831) B2962831
theorem B2377601 : Blo 924580 2377601 := bstep (se 2 (by rfl) ⟨891600, by rfl⟩ : syracuseStep 2377601 = 1783201) B1783201
theorem B2083247 : Blo 924580 2083247 := bstep (se 1 (by rfl) ⟨1562435, by rfl⟩ : syracuseStep 2083247 = 3124871) B3124871
theorem B2083283 : Blo 924580 2083283 := bstep (se 1 (by rfl) ⟨1562462, by rfl⟩ : syracuseStep 2083283 = 3124925) B3124925
theorem B2083391 : Blo 924580 2083391 := bstep (se 1 (by rfl) ⟨1562543, by rfl⟩ : syracuseStep 2083391 = 3125087) B3125087
theorem B2542153 : Blo 924580 2542153 := bstep (se 2 (by rfl) ⟨953307, by rfl⟩ : syracuseStep 2542153 = 1906615) B1906615
theorem B2083499 : Blo 924580 2083499 := bstep (se 1 (by rfl) ⟨1562624, by rfl⟩ : syracuseStep 2083499 = 3125249) B3125249
theorem B2378423 : Blo 924580 2378423 := bstep (se 1 (by rfl) ⟨1783817, by rfl⟩ : syracuseStep 2378423 = 3567635) B3567635
theorem B2345719 : Blo 924580 2345719 := bstep (se 1 (by rfl) ⟨1759289, by rfl⟩ : syracuseStep 2345719 = 3518579) B3518579
theorem B2640883 : Blo 924580 2640883 := bstep (se 1 (by rfl) ⟨1980662, by rfl⟩ : syracuseStep 2640883 = 3961325) B3961325
theorem B2346023 : Blo 924580 2346023 := bstep (se 1 (by rfl) ⟨1759517, by rfl⟩ : syracuseStep 2346023 = 3519035) B3519035
theorem B3132539 : Blo 924580 3132539 := bstep (se 1 (by rfl) ⟨2349404, by rfl⟩ : syracuseStep 3132539 = 4698809) B4698809
theorem B2084039 : Blo 924580 2084039 := bstep (se 1 (by rfl) ⟨1563029, by rfl⟩ : syracuseStep 2084039 = 3126059) B3126059
theorem B2084219 : Blo 924580 2084219 := bstep (se 1 (by rfl) ⟨1563164, by rfl⟩ : syracuseStep 2084219 = 3126329) B3126329
theorem B3132809 : Blo 924580 3132809 := bstep (se 2 (by rfl) ⟨1174803, by rfl⟩ : syracuseStep 3132809 = 2349607) B2349607
theorem B2084345 : Blo 924580 2084345 := bstep (se 2 (by rfl) ⟨781629, by rfl⟩ : syracuseStep 2084345 = 1563259) B1563259
theorem B2084435 : Blo 924580 2084435 := bstep (se 1 (by rfl) ⟨1563326, by rfl⟩ : syracuseStep 2084435 = 3126653) B3126653
theorem B2084615 : Blo 924580 2084615 := bstep (se 1 (by rfl) ⟨1563461, by rfl⟩ : syracuseStep 2084615 = 3126923) B3126923
theorem B937775 : Blo 924580 937775 := bstep (se 1 (by rfl) ⟨703331, by rfl⟩ : syracuseStep 937775 = 1406663) B1406663
theorem B1560377 : Blo 924580 1560377 := bstep (se 2 (by rfl) ⟨585141, by rfl⟩ : syracuseStep 1560377 = 1170283) B1170283
theorem B3133241 : Blo 924580 3133241 := bstep (se 2 (by rfl) ⟨1174965, by rfl⟩ : syracuseStep 3133241 = 2349931) B2349931
theorem B4443977 : Blo 924580 4443977 := bstep (se 2 (by rfl) ⟨1666491, by rfl⟩ : syracuseStep 4443977 = 3332983) B3332983
theorem B10145897 : Blo 924580 10145897 := bstep (se 2 (by rfl) ⟨3804711, by rfl⟩ : syracuseStep 10145897 = 7609423) B7609423
theorem B2347289 : Blo 924580 2347289 := bstep (se 2 (by rfl) ⟨880233, by rfl⟩ : syracuseStep 2347289 = 1760467) B1760467
theorem B2085227 : Blo 924580 2085227 := bstep (se 1 (by rfl) ⟨1563920, by rfl⟩ : syracuseStep 2085227 = 3127841) B3127841
theorem B1757551 : Blo 924580 1757551 := bstep (se 1 (by rfl) ⟨1318163, by rfl⟩ : syracuseStep 1757551 = 2636327) B2636327
theorem B2085371 : Blo 924580 2085371 := bstep (se 1 (by rfl) ⟨1564028, by rfl⟩ : syracuseStep 2085371 = 3128057) B3128057
theorem B2085497 : Blo 924580 2085497 := bstep (se 2 (by rfl) ⟨782061, by rfl⟩ : syracuseStep 2085497 = 1564123) B1564123
theorem B10048121 : Blo 924580 10048121 := bstep (se 2 (by rfl) ⟨3768045, by rfl⟩ : syracuseStep 10048121 = 7536091) B7536091
theorem B2085551 : Blo 924580 2085551 := bstep (se 1 (by rfl) ⟨1564163, by rfl⟩ : syracuseStep 2085551 = 3128327) B3128327
theorem B2642615 : Blo 924580 2642615 := bstep (se 1 (by rfl) ⟨1981961, by rfl⟩ : syracuseStep 2642615 = 3963923) B3963923
theorem B2085623 : Blo 924580 2085623 := bstep (se 1 (by rfl) ⟨1564217, by rfl⟩ : syracuseStep 2085623 = 3128435) B3128435
theorem B1561423 : Blo 924580 1561423 := bstep (se 1 (by rfl) ⟨1171067, by rfl⟩ : syracuseStep 1561423 = 2342135) B2342135
theorem B8901485 : Blo 924580 8901485 := bstep (se 3 (by rfl) ⟨1669028, by rfl⟩ : syracuseStep 8901485 = 3338057) B3338057
theorem B2085803 : Blo 924580 2085803 := bstep (se 1 (by rfl) ⟨1564352, by rfl⟩ : syracuseStep 2085803 = 3128705) B3128705
theorem B2348129 : Blo 924580 2348129 := bstep (se 2 (by rfl) ⟨880548, by rfl⟩ : syracuseStep 2348129 = 1761097) B1761097
theorem B38196605 : Blo 924580 38196605 := bstep (se 3 (by rfl) ⟨7161863, by rfl⟩ : syracuseStep 38196605 = 14323727) B14323727
theorem B2086343 : Blo 924580 2086343 := bstep (se 1 (by rfl) ⟨1564757, by rfl⟩ : syracuseStep 2086343 = 3129515) B3129515
theorem B1562105 : Blo 924580 1562105 := bstep (se 2 (by rfl) ⟨585789, by rfl⟩ : syracuseStep 1562105 = 1171579) B1171579
theorem B3954233 : Blo 924580 3954233 := bstep (se 2 (by rfl) ⟨1482837, by rfl⟩ : syracuseStep 3954233 = 2965675) B2965675
theorem B1562375 : Blo 924580 1562375 := bstep (se 1 (by rfl) ⟨1171781, by rfl⟩ : syracuseStep 1562375 = 2343563) B2343563
theorem B2086703 : Blo 924580 2086703 := bstep (se 1 (by rfl) ⟨1565027, by rfl⟩ : syracuseStep 2086703 = 3130055) B3130055
theorem B2087279 : Blo 924580 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B2087351 : Blo 924580 2087351 := bstep (se 1 (by rfl) ⟨1565513, by rfl⟩ : syracuseStep 2087351 = 3131027) B3131027
theorem B1563131 : Blo 924580 1563131 := bstep (se 1 (by rfl) ⟨1172348, by rfl⟩ : syracuseStep 1563131 = 2344697) B2344697
theorem B2349587 : Blo 924580 2349587 := bstep (se 1 (by rfl) ⟨1762190, by rfl⟩ : syracuseStep 2349587 = 3524381) B3524381
theorem B2087495 : Blo 924580 2087495 := bstep (se 1 (by rfl) ⟨1565621, by rfl⟩ : syracuseStep 2087495 = 3131243) B3131243
theorem B3332681 : Blo 924580 3332681 := bstep (se 2 (by rfl) ⟨1249755, by rfl⟩ : syracuseStep 3332681 = 2499511) B2499511
theorem B2087531 : Blo 924580 2087531 := bstep (se 1 (by rfl) ⟨1565648, by rfl⟩ : syracuseStep 2087531 = 3131297) B3131297
theorem B11885251 : Blo 924580 11885251 := bstep (se 1 (by rfl) ⟨8913938, by rfl⟩ : syracuseStep 11885251 = 17827877) B17827877
theorem B7527107 : Blo 924580 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B1203023 : Blo 924580 1203023 := bstep (se 1 (by rfl) ⟨902267, by rfl⟩ : syracuseStep 1203023 = 1804535) B1804535
theorem B1563563 : Blo 924580 1563563 := bstep (se 1 (by rfl) ⟨1172672, by rfl⟩ : syracuseStep 1563563 = 2345345) B2345345
theorem B7035821 : Blo 924580 7035821 := bstep (se 3 (by rfl) ⟨1319216, by rfl⟩ : syracuseStep 7035821 = 2638433) B2638433
theorem B2350043 : Blo 924580 2350043 := bstep (se 1 (by rfl) ⟨1762532, by rfl⟩ : syracuseStep 2350043 = 3525065) B3525065
theorem B1760231 : Blo 924580 1760231 := bstep (se 1 (by rfl) ⟨1320173, by rfl⟩ : syracuseStep 1760231 = 2640347) B2640347
theorem B2087927 : Blo 924580 2087927 := bstep (se 1 (by rfl) ⟨1565945, by rfl⟩ : syracuseStep 2087927 = 3131891) B3131891
theorem B3169469 : Blo 924580 3169469 := bstep (se 3 (by rfl) ⟨594275, by rfl⟩ : syracuseStep 3169469 = 1188551) B1188551
theorem B2350367 : Blo 924580 2350367 := bstep (se 1 (by rfl) ⟨1762775, by rfl⟩ : syracuseStep 2350367 = 3525551) B3525551
theorem B2088287 : Blo 924580 2088287 := bstep (se 1 (by rfl) ⟨1566215, by rfl⟩ : syracuseStep 2088287 = 3132431) B3132431
theorem B1564103 : Blo 924580 1564103 := bstep (se 1 (by rfl) ⟨1173077, by rfl⟩ : syracuseStep 1564103 = 2346155) B2346155
theorem B2088683 : Blo 924580 2088683 := bstep (se 1 (by rfl) ⟨1566512, by rfl⟩ : syracuseStep 2088683 = 3133025) B3133025
theorem B12181241 : Blo 924580 12181241 := bstep (se 2 (by rfl) ⟨4567965, by rfl⟩ : syracuseStep 12181241 = 9135931) B9135931
theorem B5267207 : Blo 924580 5267207 := bstep (se 1 (by rfl) ⟨3950405, by rfl⟩ : syracuseStep 5267207 = 7900811) B7900811
theorem B5005097 : Blo 924580 5005097 := bstep (se 2 (by rfl) ⟨1876911, by rfl⟩ : syracuseStep 5005097 = 3753823) B3753823
theorem B1171255 : Blo 924580 1171255 := bstep (se 1 (by rfl) ⟨878441, by rfl⟩ : syracuseStep 1171255 = 1756883) B1756883
theorem B2088809 : Blo 924580 2088809 := bstep (se 2 (by rfl) ⟨783303, by rfl⟩ : syracuseStep 2088809 = 1566607) B1566607
theorem B1040359 : Blo 924580 1040359 := bstep (se 1 (by rfl) ⟨780269, by rfl⟩ : syracuseStep 1040359 = 1560539) B1560539
theorem B17817731 : Blo 924580 17817731 := bstep (se 1 (by rfl) ⟨13363298, by rfl⟩ : syracuseStep 17817731 = 26726597) B26726597
theorem B1171675 : Blo 924580 1171675 := bstep (se 1 (by rfl) ⟨878756, by rfl⟩ : syracuseStep 1171675 = 1757513) B1757513
theorem B1565095 : Blo 924580 1565095 := bstep (se 1 (by rfl) ⟨1173821, by rfl⟩ : syracuseStep 1565095 = 2347643) B2347643
theorem B1565257 : Blo 924580 1565257 := bstep (se 2 (by rfl) ⟨586971, by rfl⟩ : syracuseStep 1565257 = 1173943) B1173943
theorem B1565291 : Blo 924580 1565291 := bstep (se 1 (by rfl) ⟨1173968, by rfl⟩ : syracuseStep 1565291 = 2347937) B2347937
theorem B9495589 : Blo 924580 9495589 := bstep (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) B1780423
theorem B4449437 : Blo 924580 4449437 := bstep (se 3 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 4449437 = 1668539) B1668539
theorem B17786051 : Blo 924580 17786051 := bstep (se 1 (by rfl) ⟨13339538, by rfl⟩ : syracuseStep 17786051 = 26679077) B26679077
theorem B7529705 : Blo 924580 7529705 := bstep (se 2 (by rfl) ⟨2823639, by rfl⟩ : syracuseStep 7529705 = 5647279) B5647279
theorem B7038251 : Blo 924580 7038251 := bstep (se 1 (by rfl) ⟨5278688, by rfl⟩ : syracuseStep 7038251 = 10557377) B10557377
theorem B4449725 : Blo 924580 4449725 := bstep (se 3 (by rfl) ⟨834323, by rfl⟩ : syracuseStep 4449725 = 1668647) B1668647
theorem B6678073 : Blo 924580 6678073 := bstep (se 2 (by rfl) ⟨2504277, by rfl⟩ : syracuseStep 6678073 = 5008555) B5008555
theorem B1042015 : Blo 924580 1042015 := bstep (se 1 (by rfl) ⟨781511, by rfl⟩ : syracuseStep 1042015 = 1563023) B1563023
theorem B1173295 : Blo 924580 1173295 := bstep (se 1 (by rfl) ⟨879971, by rfl⟩ : syracuseStep 1173295 = 1759943) B1759943
theorem B3565417 : Blo 924580 3565417 := bstep (se 2 (by rfl) ⟨1337031, by rfl⟩ : syracuseStep 3565417 = 2674063) B2674063
theorem B3565601 : Blo 924580 3565601 := bstep (se 2 (by rfl) ⟨1337100, by rfl⟩ : syracuseStep 3565601 = 2674201) B2674201
theorem B8906867 : Blo 924580 8906867 := bstep (se 1 (by rfl) ⟨6680150, by rfl⟩ : syracuseStep 8906867 = 13360301) B13360301
theorem B1173791 : Blo 924580 1173791 := bstep (se 1 (by rfl) ⟨880343, by rfl⟩ : syracuseStep 1173791 = 1760687) B1760687
theorem B3172927 : Blo 924580 3172927 := bstep (se 1 (by rfl) ⟨2379695, by rfl⟩ : syracuseStep 3172927 = 4759391) B4759391
theorem B6777431 : Blo 924580 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B7039709 : Blo 924580 7039709 := bstep (se 3 (by rfl) ⟨1319945, by rfl⟩ : syracuseStep 7039709 = 2639891) B2639891
theorem B1043167 : Blo 924580 1043167 := bstep (se 1 (by rfl) ⟨782375, by rfl⟩ : syracuseStep 1043167 = 1564751) B1564751
theorem B4680827 : Blo 924580 4680827 := bstep (se 1 (by rfl) ⟨3510620, by rfl⟩ : syracuseStep 4680827 = 7021241) B7021241
theorem B6679691 : Blo 924580 6679691 := bstep (se 1 (by rfl) ⟨5009768, by rfl⟩ : syracuseStep 6679691 = 10019537) B10019537
theorem B6352091 : Blo 924580 6352091 := bstep (se 1 (by rfl) ⟨4764068, by rfl⟩ : syracuseStep 6352091 = 9528137) B9528137
theorem B1043743 : Blo 924580 1043743 := bstep (se 1 (by rfl) ⟨782807, by rfl⟩ : syracuseStep 1043743 = 1565615) B1565615
theorem B1044031 : Blo 924580 1044031 := bstep (se 1 (by rfl) ⟨783023, by rfl⟩ : syracuseStep 1044031 = 1566047) B1566047
theorem B4451935 : Blo 924580 4451935 := bstep (se 1 (by rfl) ⟨3338951, by rfl⟩ : syracuseStep 4451935 = 6677903) B6677903
theorem B11267693 : Blo 924580 11267693 := bstep (se 3 (by rfl) ⟨2112692, by rfl⟩ : syracuseStep 11267693 = 4225385) B4225385
theorem B4681475 : Blo 924580 4681475 := bstep (se 1 (by rfl) ⟨3511106, by rfl⟩ : syracuseStep 4681475 = 7022213) B7022213
theorem B1503017 : Blo 924580 1503017 := bstep (se 2 (by rfl) ⟨563631, by rfl⟩ : syracuseStep 1503017 = 1127263) B1127263
theorem B5009939 : Blo 924580 5009939 := bstep (se 1 (by rfl) ⟨3757454, by rfl⟩ : syracuseStep 5009939 = 7514909) B7514909
theorem B24080921 : Blo 924580 24080921 := bstep (se 2 (by rfl) ⟨9030345, by rfl⟩ : syracuseStep 24080921 = 18060691) B18060691
theorem B3174983 : Blo 924580 3174983 := bstep (se 1 (by rfl) ⟨2381237, by rfl⟩ : syracuseStep 3174983 = 4762475) B4762475
theorem B1340011 : Blo 924580 1340011 := bstep (se 1 (by rfl) ⟨1005008, by rfl⟩ : syracuseStep 1340011 = 2010017) B2010017
theorem B5272721 : Blo 924580 5272721 := bstep (se 2 (by rfl) ⟨1977270, by rfl⟩ : syracuseStep 5272721 = 3954541) B3954541
theorem B2815175 : Blo 924580 2815175 := bstep (se 1 (by rfl) ⟨2111381, by rfl⟩ : syracuseStep 2815175 = 4222763) B4222763
theorem B4683095 : Blo 924580 4683095 := bstep (se 1 (by rfl) ⟨3512321, by rfl⟩ : syracuseStep 4683095 = 7024643) B7024643
theorem B7141175 : Blo 924580 7141175 := bstep (se 1 (by rfl) ⟨5355881, by rfl⟩ : syracuseStep 7141175 = 10711763) B10711763
theorem B6420311 : Blo 924580 6420311 := bstep (se 1 (by rfl) ⟨4815233, by rfl⟩ : syracuseStep 6420311 = 9630467) B9630467
theorem B20051873 : Blo 924580 20051873 := bstep (se 2 (by rfl) ⟨7519452, by rfl⟩ : syracuseStep 20051873 = 15038905) B15038905
theorem B38008763 : Blo 924580 38008763 := bstep (se 1 (by rfl) ⟨28506572, by rfl⟩ : syracuseStep 38008763 = 57013145) B57013145
theorem B7927739 : Blo 924580 7927739 := bstep (se 1 (by rfl) ⟨5945804, by rfl⟩ : syracuseStep 7927739 = 11891609) B11891609
theorem B2815951 : Blo 924580 2815951 := bstep (se 1 (by rfl) ⟨2111963, by rfl⟩ : syracuseStep 2815951 = 4223927) B4223927
theorem B4749293 : Blo 924580 4749293 := bstep (se 3 (by rfl) ⟨890492, by rfl⟩ : syracuseStep 4749293 = 1780985) B1780985
theorem B4683905 : Blo 924580 4683905 := bstep (se 2 (by rfl) ⟨1756464, by rfl⟩ : syracuseStep 4683905 = 3512929) B3512929
theorem B1407241 : Blo 924580 1407241 := bstep (se 2 (by rfl) ⟨527715, by rfl⟩ : syracuseStep 1407241 = 1055431) B1055431
theorem B5012189 : Blo 924580 5012189 := bstep (se 3 (by rfl) ⟨939785, by rfl⟩ : syracuseStep 5012189 = 1879571) B1879571
theorem B3013519 : Blo 924580 3013519 := bstep (se 1 (by rfl) ⟨2260139, by rfl⟩ : syracuseStep 3013519 = 4520279) B4520279
theorem B4684715 : Blo 924580 4684715 := bstep (se 1 (by rfl) ⟨3513536, by rfl⟩ : syracuseStep 4684715 = 7027073) B7027073
theorem B2817011 : Blo 924580 2817011 := bstep (se 1 (by rfl) ⟨2112758, by rfl⟩ : syracuseStep 2817011 = 4225517) B4225517
theorem B7044083 : Blo 924580 7044083 := bstep (se 1 (by rfl) ⟨5283062, by rfl⟩ : syracuseStep 7044083 = 10566125) B10566125
theorem B30080393 : Blo 924580 30080393 := bstep (se 2 (by rfl) ⟨11280147, by rfl⟩ : syracuseStep 30080393 = 22560295) B22560295
theorem B20021255 : Blo 924580 20021255 := bstep (se 1 (by rfl) ⟨15015941, by rfl⟩ : syracuseStep 20021255 = 30031883) B30031883
theorem B5276663 : Blo 924580 5276663 := bstep (se 1 (by rfl) ⟨3957497, by rfl⟩ : syracuseStep 5276663 = 7914995) B7914995
theorem B56984593 : Blo 924580 56984593 := bstep (se 2 (by rfl) ⟨21369222, by rfl⟩ : syracuseStep 56984593 = 42738445) B42738445
theorem B3344257 : Blo 924580 3344257 := bstep (se 2 (by rfl) ⟨1254096, by rfl⟩ : syracuseStep 3344257 = 2508193) B2508193
theorem B1673209 : Blo 924580 1673209 := bstep (se 2 (by rfl) ⟨627453, by rfl⟩ : syracuseStep 1673209 = 1254907) B1254907
theorem B7932113 : Blo 924580 7932113 := bstep (se 2 (by rfl) ⟨2974542, by rfl⟩ : syracuseStep 7932113 = 5949085) B5949085
theorem B4753889 : Blo 924580 4753889 := bstep (se 2 (by rfl) ⟨1782708, by rfl⟩ : syracuseStep 4753889 = 3565417) B3565417
theorem B6687967 : Blo 924580 6687967 := bstep (se 1 (by rfl) ⟨5015975, by rfl⟩ : syracuseStep 6687967 = 10031951) B10031951
theorem B5934323 : Blo 924580 5934323 := bstep (se 1 (by rfl) ⟨4450742, by rfl⟩ : syracuseStep 5934323 = 8901485) B8901485
theorem B4230569 : Blo 924580 4230569 := bstep (se 2 (by rfl) ⟨1586463, by rfl⟩ : syracuseStep 4230569 = 3172927) B3172927
theorem B25464403 : Blo 924580 25464403 := bstep (se 1 (by rfl) ⟨19098302, by rfl⟩ : syracuseStep 25464403 = 38196605) B38196605
theorem B12029953 : Blo 924580 12029953 := bstep (se 2 (by rfl) ⟨4511232, by rfl⟩ : syracuseStep 12029953 = 9022465) B9022465
theorem B4690547 : Blo 924580 4690547 := bstep (se 1 (by rfl) ⟨3517910, by rfl⟩ : syracuseStep 4690547 = 7035821) B7035821
theorem B5935913 : Blo 924580 5935913 := bstep (se 2 (by rfl) ⟨2225967, by rfl⟩ : syracuseStep 5935913 = 4451935) B4451935
theorem B4461583 : Blo 924580 4461583 := bstep (se 1 (by rfl) ⟨3346187, by rfl⟩ : syracuseStep 4461583 = 6692375) B6692375
theorem B2823275 : Blo 924580 2823275 := bstep (se 1 (by rfl) ⟨2117456, by rfl⟩ : syracuseStep 2823275 = 4234913) B4234913
theorem B3511471 : Blo 924580 3511471 := bstep (se 1 (by rfl) ⟨2633603, by rfl⟩ : syracuseStep 3511471 = 5267207) B5267207
theorem B5019803 : Blo 924580 5019803 := bstep (se 1 (by rfl) ⟨3764852, by rfl⟩ : syracuseStep 5019803 = 7529705) B7529705
theorem B4692167 : Blo 924580 4692167 := bstep (se 1 (by rfl) ⟨3519125, by rfl⟩ : syracuseStep 4692167 = 7038251) B7038251
theorem B1317161 : Blo 924580 1317161 := bstep (se 2 (by rfl) ⟨493935, by rfl⟩ : syracuseStep 1317161 = 987871) B987871
theorem B5937911 : Blo 924580 5937911 := bstep (se 1 (by rfl) ⟨4453433, by rfl⟩ : syracuseStep 5937911 = 8906867) B8906867
theorem B924719 : Blo 924580 924719 := bstep (se 1 (by rfl) ⟨693539, by rfl⟩ : syracuseStep 924719 = 1387079) B1387079
theorem B924743 : Blo 924580 924743 := bstep (se 1 (by rfl) ⟨693557, by rfl⟩ : syracuseStep 924743 = 1387115) B1387115
theorem B4693139 : Blo 924580 4693139 := bstep (se 1 (by rfl) ⟨3519854, by rfl⟩ : syracuseStep 4693139 = 7039709) B7039709
theorem B924895 : Blo 924580 924895 := bstep (se 1 (by rfl) ⟨693671, by rfl⟩ : syracuseStep 924895 = 1387343) B1387343
theorem B3120551 : Blo 924580 3120551 := bstep (se 1 (by rfl) ⟨2340413, by rfl⟩ : syracuseStep 3120551 = 4680827) B4680827
theorem B925159 : Blo 924580 925159 := bstep (se 1 (by rfl) ⟨693869, by rfl⟩ : syracuseStep 925159 = 1387739) B1387739
theorem B4234727 : Blo 924580 4234727 := bstep (se 1 (by rfl) ⟨3176045, by rfl⟩ : syracuseStep 4234727 = 6352091) B6352091
theorem B6757967 : Blo 924580 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B925275 : Blo 924580 925275 := bstep (se 1 (by rfl) ⟨693956, by rfl⟩ : syracuseStep 925275 = 1387913) B1387913
theorem B7511795 : Blo 924580 7511795 := bstep (se 1 (by rfl) ⟨5633846, by rfl⟩ : syracuseStep 7511795 = 11267693) B11267693
theorem B925511 : Blo 924580 925511 := bstep (se 1 (by rfl) ⟨694133, by rfl⟩ : syracuseStep 925511 = 1388267) B1388267
theorem B1318727 : Blo 924580 1318727 := bstep (se 1 (by rfl) ⟨989045, by rfl⟩ : syracuseStep 1318727 = 1978091) B1978091
theorem B3120983 : Blo 924580 3120983 := bstep (se 1 (by rfl) ⟨2340737, by rfl⟩ : syracuseStep 3120983 = 4681475) B4681475
theorem B4693949 : Blo 924580 4693949 := bstep (se 3 (by rfl) ⟨880115, by rfl⟩ : syracuseStep 4693949 = 1760231) B1760231
theorem B925663 : Blo 924580 925663 := bstep (se 1 (by rfl) ⟨694247, by rfl⟩ : syracuseStep 925663 = 1388495) B1388495
theorem B925927 : Blo 924580 925927 := bstep (se 1 (by rfl) ⟨694445, by rfl⟩ : syracuseStep 925927 = 1388891) B1388891
theorem B1876321 : Blo 924580 1876321 := bstep (se 2 (by rfl) ⟨703620, by rfl⟩ : syracuseStep 1876321 = 1407241) B1407241
theorem B926079 : Blo 924580 926079 := bstep (se 1 (by rfl) ⟨694559, by rfl⟩ : syracuseStep 926079 = 1389119) B1389119
theorem B926159 : Blo 924580 926159 := bstep (se 1 (by rfl) ⟨694619, by rfl⟩ : syracuseStep 926159 = 1389239) B1389239
theorem B926311 : Blo 924580 926311 := bstep (se 1 (by rfl) ⟨694733, by rfl⟩ : syracuseStep 926311 = 1389467) B1389467
theorem B3121793 : Blo 924580 3121793 := bstep (se 2 (by rfl) ⟨1170672, by rfl⟩ : syracuseStep 3121793 = 2341345) B2341345
theorem B3515147 : Blo 924580 3515147 := bstep (se 1 (by rfl) ⟨2636360, by rfl⟩ : syracuseStep 3515147 = 5272721) B5272721
theorem B1876783 : Blo 924580 1876783 := bstep (se 1 (by rfl) ⟨1407587, by rfl⟩ : syracuseStep 1876783 = 2815175) B2815175
theorem B5645135 : Blo 924580 5645135 := bstep (se 1 (by rfl) ⟨4233851, by rfl⟩ : syracuseStep 5645135 = 8467703) B8467703
theorem B926575 : Blo 924580 926575 := bstep (se 1 (by rfl) ⟨694931, by rfl⟩ : syracuseStep 926575 = 1389863) B1389863
theorem B3122063 : Blo 924580 3122063 := bstep (se 1 (by rfl) ⟨2341547, by rfl⟩ : syracuseStep 3122063 = 4683095) B4683095
theorem B926631 : Blo 924580 926631 := bstep (se 1 (by rfl) ⟨694973, by rfl⟩ : syracuseStep 926631 = 1389947) B1389947
theorem B926715 : Blo 924580 926715 := bstep (se 1 (by rfl) ⟨695036, by rfl⟩ : syracuseStep 926715 = 1390073) B1390073
theorem B1188919 : Blo 924580 1188919 := bstep (se 1 (by rfl) ⟨891689, by rfl⟩ : syracuseStep 1188919 = 1783379) B1783379
theorem B926783 : Blo 924580 926783 := bstep (se 1 (by rfl) ⟨695087, by rfl⟩ : syracuseStep 926783 = 1390175) B1390175
theorem B4400335 : Blo 924580 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B926927 : Blo 924580 926927 := bstep (se 1 (by rfl) ⟨695195, by rfl⟩ : syracuseStep 926927 = 1390391) B1390391
theorem B4760783 : Blo 924580 4760783 := bstep (se 1 (by rfl) ⟨3570587, by rfl⟩ : syracuseStep 4760783 = 7141175) B7141175
theorem B25339175 : Blo 924580 25339175 := bstep (se 1 (by rfl) ⟨19004381, by rfl⟩ : syracuseStep 25339175 = 38008763) B38008763
theorem B5285159 : Blo 924580 5285159 := bstep (se 1 (by rfl) ⟨3963869, by rfl⟩ : syracuseStep 5285159 = 7927739) B7927739
theorem B927131 : Blo 924580 927131 := bstep (se 1 (by rfl) ⟨695348, by rfl⟩ : syracuseStep 927131 = 1390697) B1390697
theorem B3122603 : Blo 924580 3122603 := bstep (se 1 (by rfl) ⟨2341952, by rfl⟩ : syracuseStep 3122603 = 4683905) B4683905
theorem B927343 : Blo 924580 927343 := bstep (se 1 (by rfl) ⟨695507, by rfl⟩ : syracuseStep 927343 = 1391015) B1391015
theorem B12658315 : Blo 924580 12658315 := bstep (se 1 (by rfl) ⟨9493736, by rfl⟩ : syracuseStep 12658315 = 18987473) B18987473
theorem B927399 : Blo 924580 927399 := bstep (se 1 (by rfl) ⟨695549, by rfl⟩ : syracuseStep 927399 = 1391099) B1391099
theorem B927483 : Blo 924580 927483 := bstep (se 1 (by rfl) ⟨695612, by rfl⟩ : syracuseStep 927483 = 1391225) B1391225
theorem B927519 : Blo 924580 927519 := bstep (se 1 (by rfl) ⟨695639, by rfl⟩ : syracuseStep 927519 = 1391279) B1391279
theorem B927551 : Blo 924580 927551 := bstep (se 1 (by rfl) ⟨695663, by rfl⟩ : syracuseStep 927551 = 1391327) B1391327
theorem B13346693 : Blo 924580 13346693 := bstep (se 4 (by rfl) ⟨1251252, by rfl⟩ : syracuseStep 13346693 = 2502505) B2502505
theorem B3123143 : Blo 924580 3123143 := bstep (se 1 (by rfl) ⟨2342357, by rfl⟩ : syracuseStep 3123143 = 4684715) B4684715
theorem B927727 : Blo 924580 927727 := bstep (se 1 (by rfl) ⟨695795, by rfl⟩ : syracuseStep 927727 = 1391591) B1391591
theorem B1320943 : Blo 924580 1320943 := bstep (se 1 (by rfl) ⟨990707, by rfl⟩ : syracuseStep 1320943 = 1981415) B1981415
theorem B1878007 : Blo 924580 1878007 := bstep (se 1 (by rfl) ⟨1408505, by rfl⟩ : syracuseStep 1878007 = 2817011) B2817011
theorem B4696055 : Blo 924580 4696055 := bstep (se 1 (by rfl) ⟨3522041, by rfl⟩ : syracuseStep 4696055 = 7044083) B7044083
theorem B2500733 : Blo 924580 2500733 := bstep (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) B937775
theorem B12855449 : Blo 924580 12855449 := bstep (se 2 (by rfl) ⟨4820793, by rfl⟩ : syracuseStep 12855449 = 9641587) B9641587
theorem B4696217 : Blo 924580 4696217 := bstep (se 2 (by rfl) ⟨1761081, by rfl⟩ : syracuseStep 4696217 = 3522163) B3522163
theorem B927899 : Blo 924580 927899 := bstep (se 1 (by rfl) ⟨695924, by rfl⟩ : syracuseStep 927899 = 1391849) B1391849
theorem B927935 : Blo 924580 927935 := bstep (se 1 (by rfl) ⟨695951, by rfl⟩ : syracuseStep 927935 = 1391903) B1391903
theorem B10561751 : Blo 924580 10561751 := bstep (se 1 (by rfl) ⟨7921313, by rfl⟩ : syracuseStep 10561751 = 15842627) B15842627
theorem B928047 : Blo 924580 928047 := bstep (se 1 (by rfl) ⟨696035, by rfl⟩ : syracuseStep 928047 = 1392071) B1392071
theorem B1386875 : Blo 924580 1386875 := bstep (se 1 (by rfl) ⟨1040156, by rfl⟩ : syracuseStep 1386875 = 2080313) B2080313
theorem B928283 : Blo 924580 928283 := bstep (se 1 (by rfl) ⟨696212, by rfl⟩ : syracuseStep 928283 = 1392425) B1392425
theorem B928287 : Blo 924580 928287 := bstep (se 1 (by rfl) ⟨696215, by rfl⟩ : syracuseStep 928287 = 1392431) B1392431
theorem B1387145 : Blo 924580 1387145 := bstep (se 2 (by rfl) ⟨520179, by rfl⟩ : syracuseStep 1387145 = 1040359) B1040359
theorem B1321609 : Blo 924580 1321609 := bstep (se 2 (by rfl) ⟨495603, by rfl⟩ : syracuseStep 1321609 = 991207) B991207
theorem B3123899 : Blo 924580 3123899 := bstep (se 1 (by rfl) ⟨2342924, by rfl⟩ : syracuseStep 3123899 = 4685849) B4685849
theorem B1387319 : Blo 924580 1387319 := bstep (se 1 (by rfl) ⟨1040489, by rfl⟩ : syracuseStep 1387319 = 2080979) B2080979
theorem B1387355 : Blo 924580 1387355 := bstep (se 1 (by rfl) ⟨1040516, by rfl⟩ : syracuseStep 1387355 = 2081033) B2081033
theorem B4697027 : Blo 924580 4697027 := bstep (se 1 (by rfl) ⟨3522770, by rfl⟩ : syracuseStep 4697027 = 7045541) B7045541
theorem B1387499 : Blo 924580 1387499 := bstep (se 1 (by rfl) ⟨1040624, by rfl⟩ : syracuseStep 1387499 = 2081249) B2081249
theorem B1387703 : Blo 924580 1387703 := bstep (se 1 (by rfl) ⟨1040777, by rfl⟩ : syracuseStep 1387703 = 2081555) B2081555
theorem B1387943 : Blo 924580 1387943 := bstep (se 1 (by rfl) ⟨1040957, by rfl⟩ : syracuseStep 1387943 = 2081915) B2081915
theorem B1388027 : Blo 924580 1388027 := bstep (se 1 (by rfl) ⟨1041020, by rfl⟩ : syracuseStep 1388027 = 2082041) B2082041
theorem B1977929 : Blo 924580 1977929 := bstep (se 2 (by rfl) ⟨741723, by rfl⟩ : syracuseStep 1977929 = 1483447) B1483447
theorem B1388123 : Blo 924580 1388123 := bstep (se 1 (by rfl) ⟨1041092, by rfl⟩ : syracuseStep 1388123 = 2082185) B2082185
theorem B1388207 : Blo 924580 1388207 := bstep (se 1 (by rfl) ⟨1041155, by rfl⟩ : syracuseStep 1388207 = 2082311) B2082311
theorem B1388327 : Blo 924580 1388327 := bstep (se 1 (by rfl) ⟨1041245, by rfl⟩ : syracuseStep 1388327 = 2082491) B2082491
theorem B2633593 : Blo 924580 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B1388411 : Blo 924580 1388411 := bstep (se 1 (by rfl) ⟨1041308, by rfl⟩ : syracuseStep 1388411 = 2082617) B2082617
theorem B2633627 : Blo 924580 2633627 := bstep (se 1 (by rfl) ⟨1975220, by rfl⟩ : syracuseStep 2633627 = 3950441) B3950441
theorem B1585067 : Blo 924580 1585067 := bstep (se 1 (by rfl) ⟨1188800, by rfl⟩ : syracuseStep 1585067 = 2377601) B2377601
theorem B12660785 : Blo 924580 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B1487035 : Blo 924580 1487035 := bstep (se 1 (by rfl) ⟨1115276, by rfl⟩ : syracuseStep 1487035 = 2230553) B2230553
theorem B1388831 : Blo 924580 1388831 := bstep (se 1 (by rfl) ⟨1041623, by rfl⟩ : syracuseStep 1388831 = 2083247) B2083247
theorem B1388855 : Blo 924580 1388855 := bstep (se 1 (by rfl) ⟨1041641, by rfl⟩ : syracuseStep 1388855 = 2083283) B2083283
theorem B1388927 : Blo 924580 1388927 := bstep (se 1 (by rfl) ⟨1041695, by rfl⟩ : syracuseStep 1388927 = 2083391) B2083391
theorem B1388999 : Blo 924580 1388999 := bstep (se 1 (by rfl) ⟨1041749, by rfl⟩ : syracuseStep 1388999 = 2083499) B2083499
theorem B3125843 : Blo 924580 3125843 := bstep (se 1 (by rfl) ⟨2344382, by rfl⟩ : syracuseStep 3125843 = 4688765) B4688765
theorem B7516961 : Blo 924580 7516961 := bstep (se 2 (by rfl) ⟨2818860, by rfl⟩ : syracuseStep 7516961 = 5637721) B5637721
theorem B1389353 : Blo 924580 1389353 := bstep (se 2 (by rfl) ⟨521007, by rfl⟩ : syracuseStep 1389353 = 1042015) B1042015
theorem B1389359 : Blo 924580 1389359 := bstep (se 1 (by rfl) ⟨1042019, by rfl⟩ : syracuseStep 1389359 = 2084039) B2084039
theorem B1389479 : Blo 924580 1389479 := bstep (se 1 (by rfl) ⟨1042109, by rfl⟩ : syracuseStep 1389479 = 2084219) B2084219
theorem B1389563 : Blo 924580 1389563 := bstep (se 1 (by rfl) ⟨1042172, by rfl⟩ : syracuseStep 1389563 = 2084345) B2084345
theorem B1389623 : Blo 924580 1389623 := bstep (se 1 (by rfl) ⟨1042217, by rfl⟩ : syracuseStep 1389623 = 2084435) B2084435
theorem B1356907 : Blo 924580 1356907 := bstep (se 1 (by rfl) ⟨1017680, by rfl⟩ : syracuseStep 1356907 = 2035361) B2035361
theorem B1389743 : Blo 924580 1389743 := bstep (se 1 (by rfl) ⟨1042307, by rfl⟩ : syracuseStep 1389743 = 2084615) B2084615
theorem B2962651 : Blo 924580 2962651 := bstep (se 1 (by rfl) ⟨2221988, by rfl⟩ : syracuseStep 2962651 = 4443977) B4443977
theorem B3126491 : Blo 924580 3126491 := bstep (se 1 (by rfl) ⟨2344868, by rfl⟩ : syracuseStep 3126491 = 4689737) B4689737
theorem B6763931 : Blo 924580 6763931 := bstep (se 1 (by rfl) ⟨5072948, by rfl⟩ : syracuseStep 6763931 = 10145897) B10145897
theorem B1390151 : Blo 924580 1390151 := bstep (se 1 (by rfl) ⟨1042613, by rfl⟩ : syracuseStep 1390151 = 2085227) B2085227
theorem B1390247 : Blo 924580 1390247 := bstep (se 1 (by rfl) ⟨1042685, by rfl⟩ : syracuseStep 1390247 = 2085371) B2085371
theorem B2340535 : Blo 924580 2340535 := bstep (se 1 (by rfl) ⟨1755401, by rfl⟩ : syracuseStep 2340535 = 3510803) B3510803
theorem B1390331 : Blo 924580 1390331 := bstep (se 1 (by rfl) ⟨1042748, by rfl⟩ : syracuseStep 1390331 = 2085497) B2085497
theorem B6698747 : Blo 924580 6698747 := bstep (se 1 (by rfl) ⟨5024060, by rfl⟩ : syracuseStep 6698747 = 10048121) B10048121
theorem B1390367 : Blo 924580 1390367 := bstep (se 1 (by rfl) ⟨1042775, by rfl⟩ : syracuseStep 1390367 = 2085551) B2085551
theorem B1390415 : Blo 924580 1390415 := bstep (se 1 (by rfl) ⟨1042811, by rfl⟩ : syracuseStep 1390415 = 2085623) B2085623
theorem B1390535 : Blo 924580 1390535 := bstep (se 1 (by rfl) ⟨1042901, by rfl⟩ : syracuseStep 1390535 = 2085803) B2085803
theorem B2340839 : Blo 924580 2340839 := bstep (se 1 (by rfl) ⟨1755629, by rfl⟩ : syracuseStep 2340839 = 3511259) B3511259
theorem B3127355 : Blo 924580 3127355 := bstep (se 1 (by rfl) ⟨2345516, by rfl⟩ : syracuseStep 3127355 = 4691033) B4691033
theorem B3389537 : Blo 924580 3389537 := bstep (se 2 (by rfl) ⟨1271076, by rfl⟩ : syracuseStep 3389537 = 2542153) B2542153
theorem B3389683 : Blo 924580 3389683 := bstep (se 1 (by rfl) ⟨2542262, by rfl⟩ : syracuseStep 3389683 = 5084525) B5084525
theorem B190462241 : Blo 924580 190462241 := bstep (se 2 (by rfl) ⟨71423340, by rfl⟩ : syracuseStep 190462241 = 142846681) B142846681
theorem B1390889 : Blo 924580 1390889 := bstep (se 2 (by rfl) ⟨521583, by rfl⟩ : syracuseStep 1390889 = 1043167) B1043167
theorem B1390895 : Blo 924580 1390895 := bstep (se 1 (by rfl) ⟨1043171, by rfl⟩ : syracuseStep 1390895 = 2086343) B2086343
theorem B3127625 : Blo 924580 3127625 := bstep (se 2 (by rfl) ⟨1172859, by rfl⟩ : syracuseStep 3127625 = 2345719) B2345719
theorem B2636155 : Blo 924580 2636155 := bstep (se 1 (by rfl) ⟨1977116, by rfl⟩ : syracuseStep 2636155 = 3954233) B3954233
theorem B2669075 : Blo 924580 2669075 := bstep (se 1 (by rfl) ⟨2001806, by rfl⟩ : syracuseStep 2669075 = 4003613) B4003613
theorem B1391135 : Blo 924580 1391135 := bstep (se 1 (by rfl) ⟨1043351, by rfl⟩ : syracuseStep 1391135 = 2086703) B2086703
theorem B3521177 : Blo 924580 3521177 := bstep (se 2 (by rfl) ⟨1320441, by rfl⟩ : syracuseStep 3521177 = 2640883) B2640883
theorem B1391519 : Blo 924580 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B1391567 : Blo 924580 1391567 := bstep (se 1 (by rfl) ⟨1043675, by rfl⟩ : syracuseStep 1391567 = 2087351) B2087351
theorem B9026599 : Blo 924580 9026599 := bstep (se 1 (by rfl) ⟨6769949, by rfl⟩ : syracuseStep 9026599 = 13539899) B13539899
theorem B1391657 : Blo 924580 1391657 := bstep (se 2 (by rfl) ⟨521871, by rfl⟩ : syracuseStep 1391657 = 1043743) B1043743
theorem B1391663 : Blo 924580 1391663 := bstep (se 1 (by rfl) ⟨1043747, by rfl⟩ : syracuseStep 1391663 = 2087495) B2087495
theorem B1391687 : Blo 924580 1391687 := bstep (se 1 (by rfl) ⟨1043765, by rfl⟩ : syracuseStep 1391687 = 2087531) B2087531
theorem B1391951 : Blo 924580 1391951 := bstep (se 1 (by rfl) ⟨1043963, by rfl⟩ : syracuseStep 1391951 = 2087927) B2087927
theorem B1392041 : Blo 924580 1392041 := bstep (se 2 (by rfl) ⟨522015, by rfl⟩ : syracuseStep 1392041 = 1044031) B1044031
theorem B2112979 : Blo 924580 2112979 := bstep (se 1 (by rfl) ⟨1584734, by rfl⟩ : syracuseStep 2112979 = 3169469) B3169469
theorem B13352455 : Blo 924580 13352455 := bstep (se 1 (by rfl) ⟨10014341, by rfl⟩ : syracuseStep 13352455 = 20028683) B20028683
theorem B1392191 : Blo 924580 1392191 := bstep (se 1 (by rfl) ⟨1044143, by rfl⟩ : syracuseStep 1392191 = 2088287) B2088287
theorem B2342479 : Blo 924580 2342479 := bstep (se 1 (by rfl) ⟨1756859, by rfl⟩ : syracuseStep 2342479 = 3513719) B3513719
theorem B3128975 : Blo 924580 3128975 := bstep (se 1 (by rfl) ⟨2346731, by rfl⟩ : syracuseStep 3128975 = 4693463) B4693463
theorem B2080583 : Blo 924580 2080583 := bstep (se 1 (by rfl) ⟨1560437, by rfl⟩ : syracuseStep 2080583 = 3120875) B3120875
theorem B1392455 : Blo 924580 1392455 := bstep (se 1 (by rfl) ⟨1044341, by rfl⟩ : syracuseStep 1392455 = 2088683) B2088683
theorem B1392539 : Blo 924580 1392539 := bstep (se 1 (by rfl) ⟨1044404, by rfl⟩ : syracuseStep 1392539 = 2088809) B2088809
theorem B12664781 : Blo 924580 12664781 := bstep (se 3 (by rfl) ⟨2374646, by rfl⟩ : syracuseStep 12664781 = 4749293) B4749293
theorem B20299855 : Blo 924580 20299855 := bstep (se 1 (by rfl) ⟨15224891, by rfl⟩ : syracuseStep 20299855 = 30449783) B30449783
theorem B11878487 : Blo 924580 11878487 := bstep (se 1 (by rfl) ⟨8908865, by rfl⟩ : syracuseStep 11878487 = 17817731) B17817731
theorem B2081231 : Blo 924580 2081231 := bstep (se 1 (by rfl) ⟨1560923, by rfl⟩ : syracuseStep 2081231 = 3121847) B3121847
theorem B2343401 : Blo 924580 2343401 := bstep (se 2 (by rfl) ⟨878775, by rfl⟩ : syracuseStep 2343401 = 1757551) B1757551
theorem B3523135 : Blo 924580 3523135 := bstep (se 1 (by rfl) ⟨2642351, by rfl⟩ : syracuseStep 3523135 = 5284703) B5284703
theorem B3130109 : Blo 924580 3130109 := bstep (se 3 (by rfl) ⟨586895, by rfl⟩ : syracuseStep 3130109 = 1173791) B1173791
theorem B2966291 : Blo 924580 2966291 := bstep (se 1 (by rfl) ⟨2224718, by rfl⟩ : syracuseStep 2966291 = 4449437) B4449437
theorem B1786681 : Blo 924580 1786681 := bstep (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) B1340011
theorem B2966483 : Blo 924580 2966483 := bstep (se 1 (by rfl) ⟨2224862, by rfl⟩ : syracuseStep 2966483 = 4449725) B4449725
theorem B2081897 : Blo 924580 2081897 := bstep (se 2 (by rfl) ⟨780711, by rfl⟩ : syracuseStep 2081897 = 1561423) B1561423
theorem B11257139 : Blo 924580 11257139 := bstep (se 1 (by rfl) ⟨8442854, by rfl⟩ : syracuseStep 11257139 = 16885709) B16885709
theorem B2377067 : Blo 924580 2377067 := bstep (se 1 (by rfl) ⟨1782800, by rfl⟩ : syracuseStep 2377067 = 3565601) B3565601
theorem B3524093 : Blo 924580 3524093 := bstep (se 3 (by rfl) ⟨660767, by rfl⟩ : syracuseStep 3524093 = 1321535) B1321535
theorem B2082527 : Blo 924580 2082527 := bstep (se 1 (by rfl) ⟨1561895, by rfl⟩ : syracuseStep 2082527 = 3123791) B3123791
theorem B6342461 : Blo 924580 6342461 := bstep (se 3 (by rfl) ⟨1189211, by rfl⟩ : syracuseStep 6342461 = 2378423) B2378423
theorem B20072285 : Blo 924580 20072285 := bstep (se 3 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 20072285 = 7527107) B7527107
theorem B3950801 : Blo 924580 3950801 := bstep (se 2 (by rfl) ⟨1481550, by rfl⟩ : syracuseStep 3950801 = 2963101) B2963101
theorem B1755371 : Blo 924580 1755371 := bstep (se 1 (by rfl) ⟨1316528, by rfl⟩ : syracuseStep 1755371 = 2633057) B2633057
theorem B1002011 : Blo 924580 1002011 := bstep (se 1 (by rfl) ⟨751508, by rfl⟩ : syracuseStep 1002011 = 1503017) B1503017
theorem B2083355 : Blo 924580 2083355 := bstep (se 1 (by rfl) ⟨1562516, by rfl⟩ : syracuseStep 2083355 = 3125033) B3125033
theorem B3754601 : Blo 924580 3754601 := bstep (se 2 (by rfl) ⟨1407975, by rfl⟩ : syracuseStep 3754601 = 2815951) B2815951
theorem B3132215 : Blo 924580 3132215 := bstep (se 1 (by rfl) ⟨2349161, by rfl⟩ : syracuseStep 3132215 = 4698323) B4698323
theorem B2116655 : Blo 924580 2116655 := bstep (se 1 (by rfl) ⟨1587491, by rfl⟩ : syracuseStep 2116655 = 3174983) B3174983
theorem B1756495 : Blo 924580 1756495 := bstep (se 1 (by rfl) ⟨1317371, by rfl⟩ : syracuseStep 1756495 = 2634743) B2634743
theorem B10538423 : Blo 924580 10538423 := bstep (se 1 (by rfl) ⟨7903817, by rfl⟩ : syracuseStep 10538423 = 15807635) B15807635
theorem B15847001 : Blo 924580 15847001 := bstep (se 2 (by rfl) ⟨5942625, by rfl⟩ : syracuseStep 15847001 = 11885251) B11885251
theorem B2346671 : Blo 924580 2346671 := bstep (se 1 (by rfl) ⟨1760003, by rfl⟩ : syracuseStep 2346671 = 3520007) B3520007
theorem B4018025 : Blo 924580 4018025 := bstep (se 2 (by rfl) ⟨1506759, by rfl⟩ : syracuseStep 4018025 = 3013519) B3013519
theorem B4280207 : Blo 924580 4280207 := bstep (se 1 (by rfl) ⟨3210155, by rfl⟩ : syracuseStep 4280207 = 6420311) B6420311
theorem B2084831 : Blo 924580 2084831 := bstep (se 1 (by rfl) ⟨1563623, by rfl⟩ : syracuseStep 2084831 = 3127247) B3127247
theorem B2346995 : Blo 924580 2346995 := bstep (se 1 (by rfl) ⟨1760246, by rfl⟩ : syracuseStep 2346995 = 3520493) B3520493
theorem B1560863 : Blo 924580 1560863 := bstep (se 1 (by rfl) ⟨1170647, by rfl⟩ : syracuseStep 1560863 = 2341295) B2341295
theorem B2347319 : Blo 924580 2347319 := bstep (se 1 (by rfl) ⟨1760489, by rfl⟩ : syracuseStep 2347319 = 3520979) B3520979
theorem B2085479 : Blo 924580 2085479 := bstep (se 1 (by rfl) ⟨1564109, by rfl⟩ : syracuseStep 2085479 = 3128219) B3128219
theorem B1561511 : Blo 924580 1561511 := bstep (se 1 (by rfl) ⟨1171133, by rfl⟩ : syracuseStep 1561511 = 2342267) B2342267
theorem B1561673 : Blo 924580 1561673 := bstep (se 2 (by rfl) ⟨585627, by rfl⟩ : syracuseStep 1561673 = 1171255) B1171255
theorem B2086163 : Blo 924580 2086163 := bstep (se 1 (by rfl) ⟨1564622, by rfl⟩ : syracuseStep 2086163 = 3129245) B3129245
theorem B2086235 : Blo 924580 2086235 := bstep (se 1 (by rfl) ⟨1564676, by rfl⟩ : syracuseStep 2086235 = 3129353) B3129353
theorem B2348615 : Blo 924580 2348615 := bstep (se 1 (by rfl) ⟨1761461, by rfl⟩ : syracuseStep 2348615 = 3522923) B3522923
theorem B1562233 : Blo 924580 1562233 := bstep (se 2 (by rfl) ⟨585837, by rfl⟩ : syracuseStep 1562233 = 1171675) B1171675
theorem B1758971 : Blo 924580 1758971 := bstep (se 1 (by rfl) ⟨1319228, by rfl⟩ : syracuseStep 1758971 = 2638457) B2638457
theorem B2086793 : Blo 924580 2086793 := bstep (se 2 (by rfl) ⟨782547, by rfl⟩ : syracuseStep 2086793 = 1565095) B1565095
theorem B2381705 : Blo 924580 2381705 := bstep (se 2 (by rfl) ⟨893139, by rfl⟩ : syracuseStep 2381705 = 1786279) B1786279
theorem B6674359 : Blo 924580 6674359 := bstep (se 1 (by rfl) ⟨5005769, by rfl⟩ : syracuseStep 6674359 = 10011539) B10011539
theorem B2971673 : Blo 924580 2971673 := bstep (se 2 (by rfl) ⟨1114377, by rfl⟩ : syracuseStep 2971673 = 2228755) B2228755
theorem B1562719 : Blo 924580 1562719 := bstep (se 1 (by rfl) ⟨1172039, by rfl⟩ : syracuseStep 1562719 = 2344079) B2344079
theorem B2087009 : Blo 924580 2087009 := bstep (se 2 (by rfl) ⟨782628, by rfl⟩ : syracuseStep 2087009 = 1565257) B1565257
theorem B2644073 : Blo 924580 2644073 := bstep (se 2 (by rfl) ⟨991527, by rfl⟩ : syracuseStep 2644073 = 1983055) B1983055
theorem B1759495 : Blo 924580 1759495 := bstep (se 1 (by rfl) ⟨1319621, by rfl⟩ : syracuseStep 1759495 = 2639243) B2639243
theorem B2644265 : Blo 924580 2644265 := bstep (se 2 (by rfl) ⟨991599, by rfl⟩ : syracuseStep 2644265 = 1983199) B1983199
theorem B8149355 : Blo 924580 8149355 := bstep (se 1 (by rfl) ⟨6112016, by rfl⟩ : syracuseStep 8149355 = 12224033) B12224033
theorem B11852243 : Blo 924580 11852243 := bstep (se 1 (by rfl) ⟨8889182, by rfl⟩ : syracuseStep 11852243 = 17778365) B17778365
theorem B3955499 : Blo 924580 3955499 := bstep (se 1 (by rfl) ⟨2966624, by rfl⟩ : syracuseStep 3955499 = 5933249) B5933249
theorem B2972801 : Blo 924580 2972801 := bstep (se 2 (by rfl) ⟨1114800, by rfl⟩ : syracuseStep 2972801 = 2229601) B2229601
theorem B1564015 : Blo 924580 1564015 := bstep (se 1 (by rfl) ⟨1173011, by rfl⟩ : syracuseStep 1564015 = 2346023) B2346023
theorem B8904097 : Blo 924580 8904097 := bstep (se 2 (by rfl) ⟨3339036, by rfl⟩ : syracuseStep 8904097 = 6678073) B6678073
theorem B2088359 : Blo 924580 2088359 := bstep (se 1 (by rfl) ⟨1566269, by rfl⟩ : syracuseStep 2088359 = 3132539) B3132539
theorem B2088539 : Blo 924580 2088539 := bstep (se 1 (by rfl) ⟨1566404, by rfl⟩ : syracuseStep 2088539 = 3132809) B3132809
theorem B1564393 : Blo 924580 1564393 := bstep (se 2 (by rfl) ⟨586647, by rfl⟩ : syracuseStep 1564393 = 1173295) B1173295
theorem B1040251 : Blo 924580 1040251 := bstep (se 1 (by rfl) ⟨780188, by rfl⟩ : syracuseStep 1040251 = 1560377) B1560377
theorem B2088827 : Blo 924580 2088827 := bstep (se 1 (by rfl) ⟨1566620, by rfl⟩ : syracuseStep 2088827 = 3133241) B3133241
theorem B5267389 : Blo 924580 5267389 := bstep (se 3 (by rfl) ⟨987635, by rfl⟩ : syracuseStep 5267389 = 1975271) B1975271
theorem B1564859 : Blo 924580 1564859 := bstep (se 1 (by rfl) ⟨1173644, by rfl⟩ : syracuseStep 1564859 = 2347289) B2347289
theorem B1761743 : Blo 924580 1761743 := bstep (se 1 (by rfl) ⟨1321307, by rfl⟩ : syracuseStep 1761743 = 2642615) B2642615
theorem B1565419 : Blo 924580 1565419 := bstep (se 1 (by rfl) ⟨1174064, by rfl⟩ : syracuseStep 1565419 = 2348129) B2348129
theorem B1041403 : Blo 924580 1041403 := bstep (se 1 (by rfl) ⟨781052, by rfl⟩ : syracuseStep 1041403 = 1562105) B1562105
theorem B1041583 : Blo 924580 1041583 := bstep (se 1 (by rfl) ⟨781187, by rfl⟩ : syracuseStep 1041583 = 1562375) B1562375
theorem B1042087 : Blo 924580 1042087 := bstep (se 1 (by rfl) ⟨781565, by rfl⟩ : syracuseStep 1042087 = 1563131) B1563131
theorem B1566391 : Blo 924580 1566391 := bstep (se 1 (by rfl) ⟨1174793, by rfl⟩ : syracuseStep 1566391 = 2349587) B2349587
theorem B2221787 : Blo 924580 2221787 := bstep (se 1 (by rfl) ⟨1666340, by rfl⟩ : syracuseStep 2221787 = 3332681) B3332681
theorem B1042375 : Blo 924580 1042375 := bstep (se 1 (by rfl) ⟨781781, by rfl⟩ : syracuseStep 1042375 = 1563563) B1563563
theorem B1566695 : Blo 924580 1566695 := bstep (se 1 (by rfl) ⟨1175021, by rfl⟩ : syracuseStep 1566695 = 2350043) B2350043
theorem B1566911 : Blo 924580 1566911 := bstep (se 1 (by rfl) ⟨1175183, by rfl⟩ : syracuseStep 1566911 = 2350367) B2350367
theorem B1042735 : Blo 924580 1042735 := bstep (se 1 (by rfl) ⟨782051, by rfl⟩ : syracuseStep 1042735 = 1564103) B1564103
theorem B4286881 : Blo 924580 4286881 := bstep (se 2 (by rfl) ⟨1607580, by rfl⟩ : syracuseStep 4286881 = 3215161) B3215161
theorem B8120827 : Blo 924580 8120827 := bstep (se 1 (by rfl) ⟨6090620, by rfl⟩ : syracuseStep 8120827 = 12181241) B12181241
theorem B5925403 : Blo 924580 5925403 := bstep (se 1 (by rfl) ⟨4444052, by rfl⟩ : syracuseStep 5925403 = 8888105) B8888105
theorem B3336731 : Blo 924580 3336731 := bstep (se 1 (by rfl) ⟨2502548, by rfl⟩ : syracuseStep 3336731 = 5005097) B5005097
theorem B14248487 : Blo 924580 14248487 := bstep (se 1 (by rfl) ⟨10686365, by rfl⟩ : syracuseStep 14248487 = 21372731) B21372731
theorem B5270123 : Blo 924580 5270123 := bstep (se 1 (by rfl) ⟨3952592, by rfl⟩ : syracuseStep 5270123 = 7905185) B7905185
theorem B1043527 : Blo 924580 1043527 := bstep (se 1 (by rfl) ⟨782645, by rfl⟩ : syracuseStep 1043527 = 1565291) B1565291
theorem B11857367 : Blo 924580 11857367 := bstep (se 1 (by rfl) ⟨8893025, by rfl⟩ : syracuseStep 11857367 = 17786051) B17786051
theorem B17788511 : Blo 924580 17788511 := bstep (se 1 (by rfl) ⟨13341383, by rfl⟩ : syracuseStep 17788511 = 26682767) B26682767
theorem B22572755 : Blo 924580 22572755 := bstep (se 1 (by rfl) ⟨16929566, by rfl⟩ : syracuseStep 22572755 = 33859133) B33859133
theorem B1667039 : Blo 924580 1667039 := bstep (se 1 (by rfl) ⟨1250279, by rfl⟩ : syracuseStep 1667039 = 2500559) B2500559
theorem B5271763 : Blo 924580 5271763 := bstep (se 1 (by rfl) ⟨3953822, by rfl⟩ : syracuseStep 5271763 = 7907645) B7907645
theorem B3174653 : Blo 924580 3174653 := bstep (se 3 (by rfl) ⟨595247, by rfl⟩ : syracuseStep 3174653 = 1190495) B1190495
theorem B4518287 : Blo 924580 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B5272037 : Blo 924580 5272037 := bstep (se 4 (by rfl) ⟨494253, by rfl⟩ : syracuseStep 5272037 = 988507) B988507
theorem B4453127 : Blo 924580 4453127 := bstep (se 1 (by rfl) ⟨3339845, by rfl⟩ : syracuseStep 4453127 = 6679691) B6679691
theorem B3208061 : Blo 924580 3208061 := bstep (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) B1203023
theorem B3339959 : Blo 924580 3339959 := bstep (se 1 (by rfl) ⟨2504969, by rfl⟩ : syracuseStep 3339959 = 5009939) B5009939
theorem B16053947 : Blo 924580 16053947 := bstep (se 1 (by rfl) ⟨12040460, by rfl⟩ : syracuseStep 16053947 = 24080921) B24080921
theorem B13367915 : Blo 924580 13367915 := bstep (se 1 (by rfl) ⟨10025936, by rfl⟩ : syracuseStep 13367915 = 20051873) B20051873
theorem B3341459 : Blo 924580 3341459 := bstep (se 1 (by rfl) ⟨2506094, by rfl⟩ : syracuseStep 3341459 = 5012189) B5012189
theorem B2260391 : Blo 924580 2260391 := bstep (se 1 (by rfl) ⟨1695293, by rfl⟩ : syracuseStep 2260391 = 3390587) B3390587
theorem B20053595 : Blo 924580 20053595 := bstep (se 1 (by rfl) ⟨15040196, by rfl⟩ : syracuseStep 20053595 = 30080393) B30080393
theorem B27066473 : Blo 924580 27066473 := bstep (se 2 (by rfl) ⟨10149927, by rfl⟩ : syracuseStep 27066473 = 20299855) B20299855
theorem B7504759 : Blo 924580 7504759 := bstep (se 1 (by rfl) ⟨5628569, by rfl⟩ : syracuseStep 7504759 = 11257139) B11257139
theorem B4228307 : Blo 924580 4228307 := bstep (se 1 (by rfl) ⟨3171230, by rfl⟩ : syracuseStep 4228307 = 6342461) B6342461
theorem B5867113 : Blo 924580 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B1411103 : Blo 924580 1411103 := bstep (se 1 (by rfl) ⟨1058327, by rfl⟩ : syracuseStep 1411103 = 2116655) B2116655
theorem B16877753 : Blo 924580 16877753 := bstep (se 2 (by rfl) ⟨6329157, by rfl⟩ : syracuseStep 16877753 = 12658315) B12658315
theorem B4459009 : Blo 924580 4459009 := bstep (se 2 (by rfl) ⟨1672128, by rfl⟩ : syracuseStep 4459009 = 3344257) B3344257
theorem B2230945 : Blo 924580 2230945 := bstep (se 2 (by rfl) ⟨836604, by rfl⟩ : syracuseStep 2230945 = 1673209) B1673209
theorem B7900537 : Blo 924580 7900537 := bstep (se 2 (by rfl) ⟨2962701, by rfl⟩ : syracuseStep 7900537 = 5925403) B5925403
theorem B3346535 : Blo 924580 3346535 := bstep (se 1 (by rfl) ⟨2509901, by rfl⟩ : syracuseStep 3346535 = 5019803) B5019803
theorem B8917289 : Blo 924580 8917289 := bstep (se 2 (by rfl) ⟨3343983, by rfl⟩ : syracuseStep 8917289 = 6687967) B6687967
theorem B7901495 : Blo 924580 7901495 := bstep (se 1 (by rfl) ⟨5926121, by rfl⟩ : syracuseStep 7901495 = 11852243) B11852243
theorem B17863325 : Blo 924580 17863325 := bstep (se 3 (by rfl) ⟨3349373, by rfl⟩ : syracuseStep 17863325 = 6698747) B6698747
theorem B33952537 : Blo 924580 33952537 := bstep (se 2 (by rfl) ⟨12732201, by rfl⟩ : syracuseStep 33952537 = 25464403) B25464403
theorem B3511457 : Blo 924580 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B3512429 : Blo 924580 3512429 := bstep (se 3 (by rfl) ⟨658580, by rfl⟩ : syracuseStep 3512429 = 1317161) B1317161
theorem B7051373 : Blo 924580 7051373 := bstep (se 3 (by rfl) ⟨1322132, by rfl⟩ : syracuseStep 7051373 = 2644265) B2644265
theorem B1809209 : Blo 924580 1809209 := bstep (se 2 (by rfl) ⟨678453, by rfl⟩ : syracuseStep 1809209 = 1356907) B1356907
theorem B924583 : Blo 924580 924583 := bstep (se 1 (by rfl) ⟨693437, by rfl⟩ : syracuseStep 924583 = 1386875) B1386875
theorem B3513415 : Blo 924580 3513415 := bstep (se 1 (by rfl) ⟨2635061, by rfl⟩ : syracuseStep 3513415 = 5270123) B5270123
theorem B924763 : Blo 924580 924763 := bstep (se 1 (by rfl) ⟨693572, by rfl⟩ : syracuseStep 924763 = 1387145) B1387145
theorem B924879 : Blo 924580 924879 := bstep (se 1 (by rfl) ⟨693659, by rfl⟩ : syracuseStep 924879 = 1387319) B1387319
theorem B924903 : Blo 924580 924903 := bstep (se 1 (by rfl) ⟨693677, by rfl⟩ : syracuseStep 924903 = 1387355) B1387355
theorem B35626229 : Blo 924580 35626229 := bstep (se 5 (by rfl) ⟨1669979, by rfl⟩ : syracuseStep 35626229 = 3339959) B3339959
theorem B924999 : Blo 924580 924999 := bstep (se 1 (by rfl) ⟨693749, by rfl⟩ : syracuseStep 924999 = 1387499) B1387499
theorem B925135 : Blo 924580 925135 := bstep (se 1 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 925135 = 1387703) B1387703
theorem B3120713 : Blo 924580 3120713 := bstep (se 2 (by rfl) ⟨1170267, by rfl⟩ : syracuseStep 3120713 = 2340535) B2340535
theorem B925295 : Blo 924580 925295 := bstep (se 1 (by rfl) ⟨693971, by rfl⟩ : syracuseStep 925295 = 1387943) B1387943
theorem B7904911 : Blo 924580 7904911 := bstep (se 1 (by rfl) ⟨5928683, by rfl⟩ : syracuseStep 7904911 = 11857367) B11857367
theorem B925351 : Blo 924580 925351 := bstep (se 1 (by rfl) ⟨694013, by rfl⟩ : syracuseStep 925351 = 1388027) B1388027
theorem B1318619 : Blo 924580 1318619 := bstep (se 1 (by rfl) ⟨988964, by rfl⟩ : syracuseStep 1318619 = 1977929) B1977929
theorem B925415 : Blo 924580 925415 := bstep (se 1 (by rfl) ⟨694061, by rfl⟩ : syracuseStep 925415 = 1388123) B1388123
theorem B925471 : Blo 924580 925471 := bstep (se 1 (by rfl) ⟨694103, by rfl⟩ : syracuseStep 925471 = 1388207) B1388207
theorem B15048503 : Blo 924580 15048503 := bstep (se 1 (by rfl) ⟨11286377, by rfl⟩ : syracuseStep 15048503 = 22572755) B22572755
theorem B925551 : Blo 924580 925551 := bstep (se 1 (by rfl) ⟨694163, by rfl⟩ : syracuseStep 925551 = 1388327) B1388327
theorem B925607 : Blo 924580 925607 := bstep (se 1 (by rfl) ⟨694205, by rfl⟩ : syracuseStep 925607 = 1388411) B1388411
theorem B925887 : Blo 924580 925887 := bstep (se 1 (by rfl) ⟨694415, by rfl⟩ : syracuseStep 925887 = 1388831) B1388831
theorem B925903 : Blo 924580 925903 := bstep (se 1 (by rfl) ⟨694427, by rfl⟩ : syracuseStep 925903 = 1388855) B1388855
theorem B925951 : Blo 924580 925951 := bstep (se 1 (by rfl) ⟨694463, by rfl⟩ : syracuseStep 925951 = 1388927) B1388927
theorem B925999 : Blo 924580 925999 := bstep (se 1 (by rfl) ⟨694499, by rfl⟩ : syracuseStep 925999 = 1388999) B1388999
theorem B3514691 : Blo 924580 3514691 := bstep (se 1 (by rfl) ⟨2636018, by rfl⟩ : syracuseStep 3514691 = 5272037) B5272037
theorem B3514873 : Blo 924580 3514873 := bstep (se 2 (by rfl) ⟨1318077, by rfl⟩ : syracuseStep 3514873 = 2636155) B2636155
theorem B926235 : Blo 924580 926235 := bstep (se 1 (by rfl) ⟨694676, by rfl⟩ : syracuseStep 926235 = 1389353) B1389353
theorem B926239 : Blo 924580 926239 := bstep (se 1 (by rfl) ⟨694679, by rfl⟩ : syracuseStep 926239 = 1389359) B1389359
theorem B2138707 : Blo 924580 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B926319 : Blo 924580 926319 := bstep (se 1 (by rfl) ⟨694739, by rfl⟩ : syracuseStep 926319 = 1389479) B1389479
theorem B926375 : Blo 924580 926375 := bstep (se 1 (by rfl) ⟨694781, by rfl⟩ : syracuseStep 926375 = 1389563) B1389563
theorem B926415 : Blo 924580 926415 := bstep (se 1 (by rfl) ⟨694811, by rfl⟩ : syracuseStep 926415 = 1389623) B1389623
theorem B926495 : Blo 924580 926495 := bstep (se 1 (by rfl) ⟨694871, by rfl⟩ : syracuseStep 926495 = 1389743) B1389743
theorem B926767 : Blo 924580 926767 := bstep (se 1 (by rfl) ⟨695075, by rfl⟩ : syracuseStep 926767 = 1390151) B1390151
theorem B11281517 : Blo 924580 11281517 := bstep (se 3 (by rfl) ⟨2115284, by rfl⟩ : syracuseStep 11281517 = 4230569) B4230569
theorem B926831 : Blo 924580 926831 := bstep (se 1 (by rfl) ⟨695123, by rfl⟩ : syracuseStep 926831 = 1390247) B1390247
theorem B926887 : Blo 924580 926887 := bstep (se 1 (by rfl) ⟨695165, by rfl⟩ : syracuseStep 926887 = 1390331) B1390331
theorem B926911 : Blo 924580 926911 := bstep (se 1 (by rfl) ⟨695183, by rfl⟩ : syracuseStep 926911 = 1390367) B1390367
theorem B926943 : Blo 924580 926943 := bstep (se 1 (by rfl) ⟨695207, by rfl⟩ : syracuseStep 926943 = 1390415) B1390415
theorem B927023 : Blo 924580 927023 := bstep (se 1 (by rfl) ⟨695267, by rfl⟩ : syracuseStep 927023 = 1390535) B1390535
theorem B12035465 : Blo 924580 12035465 := bstep (se 2 (by rfl) ⟨4513299, by rfl⟩ : syracuseStep 12035465 = 9026599) B9026599
theorem B25404853 : Blo 924580 25404853 := bstep (se 5 (by rfl) ⟨1190852, by rfl⟩ : syracuseStep 25404853 = 2381705) B2381705
theorem B927259 : Blo 924580 927259 := bstep (se 1 (by rfl) ⟨695444, by rfl⟩ : syracuseStep 927259 = 1390889) B1390889
theorem B927263 : Blo 924580 927263 := bstep (se 1 (by rfl) ⟨695447, by rfl⟩ : syracuseStep 927263 = 1390895) B1390895
theorem B1779383 : Blo 924580 1779383 := bstep (se 1 (by rfl) ⟨1334537, by rfl⟩ : syracuseStep 1779383 = 2669075) B2669075
theorem B927423 : Blo 924580 927423 := bstep (se 1 (by rfl) ⟨695567, by rfl⟩ : syracuseStep 927423 = 1391135) B1391135
theorem B11872129 : Blo 924580 11872129 := bstep (se 2 (by rfl) ⟨4452048, by rfl⟩ : syracuseStep 11872129 = 8904097) B8904097
theorem B927679 : Blo 924580 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B927711 : Blo 924580 927711 := bstep (se 1 (by rfl) ⟨695783, by rfl⟩ : syracuseStep 927711 = 1391567) B1391567
theorem B17803273 : Blo 924580 17803273 := bstep (se 2 (by rfl) ⟨6676227, by rfl⟩ : syracuseStep 17803273 = 13352455) B13352455
theorem B927771 : Blo 924580 927771 := bstep (se 1 (by rfl) ⟨695828, by rfl⟩ : syracuseStep 927771 = 1391657) B1391657
theorem B927775 : Blo 924580 927775 := bstep (se 1 (by rfl) ⟨695831, by rfl⟩ : syracuseStep 927775 = 1391663) B1391663
theorem B927791 : Blo 924580 927791 := bstep (se 1 (by rfl) ⟨695843, by rfl⟩ : syracuseStep 927791 = 1391687) B1391687
theorem B3123305 : Blo 924580 3123305 := bstep (se 2 (by rfl) ⟨1171239, by rfl⟩ : syracuseStep 3123305 = 2342479) B2342479
theorem B3516605 : Blo 924580 3516605 := bstep (se 3 (by rfl) ⟨659363, by rfl⟩ : syracuseStep 3516605 = 1318727) B1318727
theorem B927967 : Blo 924580 927967 := bstep (se 1 (by rfl) ⟨695975, by rfl⟩ : syracuseStep 927967 = 1391951) B1391951
theorem B928027 : Blo 924580 928027 := bstep (se 1 (by rfl) ⟨696020, by rfl⟩ : syracuseStep 928027 = 1392041) B1392041
theorem B11413885 : Blo 924580 11413885 := bstep (se 3 (by rfl) ⟨2140103, by rfl⟩ : syracuseStep 11413885 = 4280207) B4280207
theorem B928127 : Blo 924580 928127 := bstep (se 1 (by rfl) ⟨696095, by rfl⟩ : syracuseStep 928127 = 1392191) B1392191
theorem B1387001 : Blo 924580 1387001 := bstep (se 2 (by rfl) ⟨520125, by rfl⟩ : syracuseStep 1387001 = 1040251) B1040251
theorem B1387055 : Blo 924580 1387055 := bstep (se 1 (by rfl) ⟨1040291, by rfl⟩ : syracuseStep 1387055 = 2080583) B2080583
theorem B928303 : Blo 924580 928303 := bstep (se 1 (by rfl) ⟨696227, by rfl⟩ : syracuseStep 928303 = 1392455) B1392455
theorem B7023185 : Blo 924580 7023185 := bstep (se 2 (by rfl) ⟨2633694, by rfl⟩ : syracuseStep 7023185 = 5267389) B5267389
theorem B928359 : Blo 924580 928359 := bstep (se 1 (by rfl) ⟨696269, by rfl⟩ : syracuseStep 928359 = 1392539) B1392539
theorem B13347503 : Blo 924580 13347503 := bstep (se 1 (by rfl) ⟨10010627, by rfl⟩ : syracuseStep 13347503 = 20021255) B20021255
theorem B1387487 : Blo 924580 1387487 := bstep (se 1 (by rfl) ⟨1040615, by rfl⟩ : syracuseStep 1387487 = 2081231) B2081231
theorem B2501761 : Blo 924580 2501761 := bstep (se 2 (by rfl) ⟨938160, by rfl⟩ : syracuseStep 2501761 = 1876321) B1876321
theorem B1977527 : Blo 924580 1977527 := bstep (se 1 (by rfl) ⟨1483145, by rfl⟩ : syracuseStep 1977527 = 2966291) B2966291
theorem B8465741 : Blo 924580 8465741 := bstep (se 3 (by rfl) ⟨1587326, by rfl⟩ : syracuseStep 8465741 = 3174653) B3174653
theorem B3517775 : Blo 924580 3517775 := bstep (se 1 (by rfl) ⟨2638331, by rfl⟩ : syracuseStep 3517775 = 5276663) B5276663
theorem B1387931 : Blo 924580 1387931 := bstep (se 1 (by rfl) ⟨1040948, by rfl⟩ : syracuseStep 1387931 = 2081897) B2081897
theorem B4697513 : Blo 924580 4697513 := bstep (se 2 (by rfl) ⟨1761567, by rfl⟩ : syracuseStep 4697513 = 3523135) B3523135
theorem B2502377 : Blo 924580 2502377 := bstep (se 2 (by rfl) ⟨938391, by rfl⟩ : syracuseStep 2502377 = 1876783) B1876783
theorem B1388351 : Blo 924580 1388351 := bstep (se 1 (by rfl) ⟨1041263, by rfl⟩ : syracuseStep 1388351 = 2082527) B2082527
theorem B13381523 : Blo 924580 13381523 := bstep (se 1 (by rfl) ⟨10036142, by rfl⟩ : syracuseStep 13381523 = 20072285) B20072285
theorem B1388537 : Blo 924580 1388537 := bstep (se 2 (by rfl) ⟨520701, by rfl⟩ : syracuseStep 1388537 = 1041403) B1041403
theorem B1585225 : Blo 924580 1585225 := bstep (se 2 (by rfl) ⟨594459, by rfl⟩ : syracuseStep 1585225 = 1188919) B1188919
theorem B2633867 : Blo 924580 2633867 := bstep (se 1 (by rfl) ⟨1975400, by rfl⟩ : syracuseStep 2633867 = 3950801) B3950801
theorem B5288075 : Blo 924580 5288075 := bstep (se 1 (by rfl) ⟨3966056, by rfl⟩ : syracuseStep 5288075 = 7932113) B7932113
theorem B1388777 : Blo 924580 1388777 := bstep (se 2 (by rfl) ⟨520791, by rfl⟩ : syracuseStep 1388777 = 1041583) B1041583
theorem B1388903 : Blo 924580 1388903 := bstep (se 1 (by rfl) ⟨1041677, by rfl⟩ : syracuseStep 1388903 = 2083355) B2083355
theorem B2503067 : Blo 924580 2503067 := bstep (se 1 (by rfl) ⟨1877300, by rfl⟩ : syracuseStep 2503067 = 3754601) B3754601
theorem B1389449 : Blo 924580 1389449 := bstep (se 2 (by rfl) ⟨521043, by rfl⟩ : syracuseStep 1389449 = 1042087) B1042087
theorem B7025615 : Blo 924580 7025615 := bstep (se 1 (by rfl) ⟨5269211, by rfl⟩ : syracuseStep 7025615 = 10538423) B10538423
theorem B10564667 : Blo 924580 10564667 := bstep (se 1 (by rfl) ⟨7923500, by rfl⟩ : syracuseStep 10564667 = 15847001) B15847001
theorem B7910621 : Blo 924580 7910621 := bstep (se 3 (by rfl) ⟨1483241, by rfl⟩ : syracuseStep 7910621 = 2966483) B2966483
theorem B1389833 : Blo 924580 1389833 := bstep (se 2 (by rfl) ⟨521187, by rfl⟩ : syracuseStep 1389833 = 1042375) B1042375
theorem B1389887 : Blo 924580 1389887 := bstep (se 1 (by rfl) ⟨1042415, by rfl⟩ : syracuseStep 1389887 = 2084831) B2084831
theorem B2504009 : Blo 924580 2504009 := bstep (se 2 (by rfl) ⟨939003, by rfl⟩ : syracuseStep 2504009 = 1878007) B1878007
theorem B1390313 : Blo 924580 1390313 := bstep (se 2 (by rfl) ⟨521367, by rfl⟩ : syracuseStep 1390313 = 1042735) B1042735
theorem B1390319 : Blo 924580 1390319 := bstep (se 1 (by rfl) ⟨1042739, by rfl⟩ : syracuseStep 1390319 = 2085479) B2085479
theorem B3127031 : Blo 924580 3127031 := bstep (se 1 (by rfl) ⟨2345273, by rfl⟩ : syracuseStep 3127031 = 4690547) B4690547
theorem B5715841 : Blo 924580 5715841 := bstep (se 2 (by rfl) ⟨2143440, by rfl⟩ : syracuseStep 5715841 = 4286881) B4286881
theorem B10827769 : Blo 924580 10827769 := bstep (se 2 (by rfl) ⟨4060413, by rfl⟩ : syracuseStep 10827769 = 8120827) B8120827
theorem B1390775 : Blo 924580 1390775 := bstep (se 1 (by rfl) ⟨1043081, by rfl⟩ : syracuseStep 1390775 = 2086163) B2086163
theorem B1390823 : Blo 924580 1390823 := bstep (se 1 (by rfl) ⟨1043117, by rfl⟩ : syracuseStep 1390823 = 2086235) B2086235
theorem B6338845 : Blo 924580 6338845 := bstep (se 3 (by rfl) ⟨1188533, by rfl⟩ : syracuseStep 6338845 = 2377067) B2377067
theorem B1391195 : Blo 924580 1391195 := bstep (se 1 (by rfl) ⟨1043396, by rfl⟩ : syracuseStep 1391195 = 2086793) B2086793
theorem B1981115 : Blo 924580 1981115 := bstep (se 1 (by rfl) ⟨1485836, by rfl⟩ : syracuseStep 1981115 = 2971673) B2971673
theorem B1391339 : Blo 924580 1391339 := bstep (se 1 (by rfl) ⟨1043504, by rfl⟩ : syracuseStep 1391339 = 2087009) B2087009
theorem B1391369 : Blo 924580 1391369 := bstep (se 2 (by rfl) ⟨521763, by rfl⟩ : syracuseStep 1391369 = 1043527) B1043527
theorem B3128111 : Blo 924580 3128111 := bstep (se 1 (by rfl) ⟨2346083, by rfl⟩ : syracuseStep 3128111 = 4692167) B4692167
theorem B2341993 : Blo 924580 2341993 := bstep (se 2 (by rfl) ⟨878247, by rfl⟩ : syracuseStep 2341993 = 1756495) B1756495
theorem B2636999 : Blo 924580 2636999 := bstep (se 1 (by rfl) ⟨1977749, by rfl⟩ : syracuseStep 2636999 = 3955499) B3955499
theorem B1981867 : Blo 924580 1981867 := bstep (se 1 (by rfl) ⟨1486400, by rfl⟩ : syracuseStep 1981867 = 2972801) B2972801
theorem B3128759 : Blo 924580 3128759 := bstep (se 1 (by rfl) ⟨2346569, by rfl⟩ : syracuseStep 3128759 = 4693139) B4693139
theorem B2080367 : Blo 924580 2080367 := bstep (se 1 (by rfl) ⟨1560275, by rfl⟩ : syracuseStep 2080367 = 3120551) B3120551
theorem B1392239 : Blo 924580 1392239 := bstep (se 1 (by rfl) ⟨1044179, by rfl⟩ : syracuseStep 1392239 = 2088359) B2088359
theorem B4505311 : Blo 924580 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B1392359 : Blo 924580 1392359 := bstep (se 1 (by rfl) ⟨1044269, by rfl⟩ : syracuseStep 1392359 = 2088539) B2088539
theorem B2080655 : Blo 924580 2080655 := bstep (se 1 (by rfl) ⟨1560491, by rfl⟩ : syracuseStep 2080655 = 3120983) B3120983
theorem B1392551 : Blo 924580 1392551 := bstep (se 1 (by rfl) ⟨1044413, by rfl⟩ : syracuseStep 1392551 = 2088827) B2088827
theorem B3129299 : Blo 924580 3129299 := bstep (se 1 (by rfl) ⟨2346974, by rfl⟩ : syracuseStep 3129299 = 4693949) B4693949
theorem B16039937 : Blo 924580 16039937 := bstep (se 2 (by rfl) ⟨6014976, by rfl⟩ : syracuseStep 16039937 = 12029953) B12029953
theorem B1982713 : Blo 924580 1982713 := bstep (se 2 (by rfl) ⟨743517, by rfl⟩ : syracuseStep 1982713 = 1487035) B1487035
theorem B7029017 : Blo 924580 7029017 := bstep (se 2 (by rfl) ⟨2635881, by rfl⟩ : syracuseStep 7029017 = 5271763) B5271763
theorem B2081195 : Blo 924580 2081195 := bstep (se 1 (by rfl) ⟨1560896, by rfl⟩ : syracuseStep 2081195 = 3121793) B3121793
theorem B2343431 : Blo 924580 2343431 := bstep (se 1 (by rfl) ⟨1757573, by rfl⟩ : syracuseStep 2343431 = 3515147) B3515147
theorem B2081375 : Blo 924580 2081375 := bstep (se 1 (by rfl) ⟨1561031, by rfl⟩ : syracuseStep 2081375 = 3122063) B3122063
theorem B16892783 : Blo 924580 16892783 := bstep (se 1 (by rfl) ⟨12669587, by rfl⟩ : syracuseStep 16892783 = 25339175) B25339175
theorem B3523439 : Blo 924580 3523439 := bstep (se 1 (by rfl) ⟨2642579, by rfl⟩ : syracuseStep 3523439 = 5285159) B5285159
theorem B2081735 : Blo 924580 2081735 := bstep (se 1 (by rfl) ⟨1561301, by rfl⟩ : syracuseStep 2081735 = 3122603) B3122603
theorem B8897795 : Blo 924580 8897795 := bstep (se 1 (by rfl) ⟨6673346, by rfl⟩ : syracuseStep 8897795 = 13346693) B13346693
theorem B2082095 : Blo 924580 2082095 := bstep (se 1 (by rfl) ⟨1561571, by rfl⟩ : syracuseStep 2082095 = 3123143) B3123143
theorem B3130703 : Blo 924580 3130703 := bstep (se 1 (by rfl) ⟨2348027, by rfl⟩ : syracuseStep 3130703 = 4696055) B4696055
theorem B5948777 : Blo 924580 5948777 := bstep (se 2 (by rfl) ⟨2230791, by rfl⟩ : syracuseStep 5948777 = 4461583) B4461583
theorem B2672029 : Blo 924580 2672029 := bstep (se 3 (by rfl) ⟨501005, by rfl⟩ : syracuseStep 2672029 = 1002011) B1002011
theorem B8570299 : Blo 924580 8570299 := bstep (se 1 (by rfl) ⟨6427724, by rfl⟩ : syracuseStep 8570299 = 12855449) B12855449
theorem B3130811 : Blo 924580 3130811 := bstep (se 1 (by rfl) ⟨2348108, by rfl⟩ : syracuseStep 3130811 = 4696217) B4696217
theorem B3950201 : Blo 924580 3950201 := bstep (se 2 (by rfl) ⟨1481325, by rfl⟩ : syracuseStep 3950201 = 2962651) B2962651
theorem B2082599 : Blo 924580 2082599 := bstep (se 1 (by rfl) ⟨1561949, by rfl⟩ : syracuseStep 2082599 = 3123899) B3123899
theorem B3131351 : Blo 924580 3131351 := bstep (se 1 (by rfl) ⟨2348513, by rfl⟩ : syracuseStep 3131351 = 4697027) B4697027
theorem B2082977 : Blo 924580 2082977 := bstep (se 2 (by rfl) ⟨781116, by rfl⟩ : syracuseStep 2082977 = 1562233) B1562233
theorem B8899145 : Blo 924580 8899145 := bstep (se 2 (by rfl) ⟨3337179, by rfl⟩ : syracuseStep 8899145 = 6674359) B6674359
theorem B1755751 : Blo 924580 1755751 := bstep (se 1 (by rfl) ⟨1316813, by rfl⟩ : syracuseStep 1755751 = 2633627) B2633627
theorem B8440523 : Blo 924580 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B2083625 : Blo 924580 2083625 := bstep (se 2 (by rfl) ⟨781359, by rfl⟩ : syracuseStep 2083625 = 1562719) B1562719
theorem B2345993 : Blo 924580 2345993 := bstep (se 2 (by rfl) ⟨879747, by rfl⟩ : syracuseStep 2345993 = 1759495) B1759495
theorem B2083895 : Blo 924580 2083895 := bstep (se 1 (by rfl) ⟨1562921, by rfl⟩ : syracuseStep 2083895 = 3125843) B3125843
theorem B2968751 : Blo 924580 2968751 := bstep (se 1 (by rfl) ⟨2226563, by rfl⟩ : syracuseStep 2968751 = 4453127) B4453127
theorem B2084327 : Blo 924580 2084327 := bstep (se 1 (by rfl) ⟨1563245, by rfl⟩ : syracuseStep 2084327 = 3126491) B3126491
theorem B4509287 : Blo 924580 4509287 := bstep (se 1 (by rfl) ⟨3381965, by rfl⟩ : syracuseStep 4509287 = 6763931) B6763931
theorem B10702631 : Blo 924580 10702631 := bstep (se 1 (by rfl) ⟨8026973, by rfl⟩ : syracuseStep 10702631 = 16053947) B16053947
theorem B11292605 : Blo 924580 11292605 := bstep (se 3 (by rfl) ⟨2117363, by rfl⟩ : syracuseStep 11292605 = 4234727) B4234727
theorem B1560559 : Blo 924580 1560559 := bstep (se 1 (by rfl) ⟨1170419, by rfl⟩ : syracuseStep 1560559 = 2340839) B2340839
theorem B2084903 : Blo 924580 2084903 := bstep (se 1 (by rfl) ⟨1563677, by rfl⟩ : syracuseStep 2084903 = 3127355) B3127355
theorem B2085083 : Blo 924580 2085083 := bstep (se 1 (by rfl) ⟨1563812, by rfl⟩ : syracuseStep 2085083 = 3127625) B3127625
theorem B2347451 : Blo 924580 2347451 := bstep (se 1 (by rfl) ⟨1760588, by rfl⟩ : syracuseStep 2347451 = 3521177) B3521177
theorem B2085353 : Blo 924580 2085353 := bstep (se 2 (by rfl) ⟨782007, by rfl⟩ : syracuseStep 2085353 = 1564015) B1564015
theorem B2085857 : Blo 924580 2085857 := bstep (se 2 (by rfl) ⟨782196, by rfl⟩ : syracuseStep 2085857 = 1564393) B1564393
theorem B2085983 : Blo 924580 2085983 := bstep (se 1 (by rfl) ⟨1564487, by rfl⟩ : syracuseStep 2085983 = 3128975) B3128975
theorem B4445437 : Blo 924580 4445437 := bstep (se 3 (by rfl) ⟨833519, by rfl⟩ : syracuseStep 4445437 = 1667039) B1667039
theorem B8443187 : Blo 924580 8443187 := bstep (se 1 (by rfl) ⟨6332390, by rfl⟩ : syracuseStep 8443187 = 12664781) B12664781
theorem B7918991 : Blo 924580 7918991 := bstep (se 1 (by rfl) ⟨5939243, by rfl⟩ : syracuseStep 7918991 = 11878487) B11878487
theorem B1562267 : Blo 924580 1562267 := bstep (se 1 (by rfl) ⟨1171700, by rfl⟩ : syracuseStep 1562267 = 2343401) B2343401
theorem B2086739 : Blo 924580 2086739 := bstep (se 1 (by rfl) ⟨1565054, by rfl⟩ : syracuseStep 2086739 = 3130109) B3130109
theorem B2087225 : Blo 924580 2087225 := bstep (se 2 (by rfl) ⟨782709, by rfl⟩ : syracuseStep 2087225 = 1565419) B1565419
theorem B2349395 : Blo 924580 2349395 := bstep (se 1 (by rfl) ⟨1762046, by rfl⟩ : syracuseStep 2349395 = 3524093) B3524093
theorem B75979457 : Blo 924580 75979457 := bstep (se 2 (by rfl) ⟨28492296, by rfl⟩ : syracuseStep 75979457 = 56984593) B56984593
theorem B3169259 : Blo 924580 3169259 := bstep (se 1 (by rfl) ⟨2376944, by rfl⟩ : syracuseStep 3169259 = 4753889) B4753889
theorem B2088143 : Blo 924580 2088143 := bstep (se 1 (by rfl) ⟨1566107, by rfl⟩ : syracuseStep 2088143 = 3132215) B3132215
theorem B3956215 : Blo 924580 3956215 := bstep (se 1 (by rfl) ⟨2967161, by rfl⟩ : syracuseStep 3956215 = 5934323) B5934323
theorem B2088521 : Blo 924580 2088521 := bstep (se 2 (by rfl) ⟨783195, by rfl⟩ : syracuseStep 2088521 = 1566391) B1566391
theorem B1564447 : Blo 924580 1564447 := bstep (se 1 (by rfl) ⟨1173335, by rfl⟩ : syracuseStep 1564447 = 2346671) B2346671
theorem B2678683 : Blo 924580 2678683 := bstep (se 1 (by rfl) ⟨2009012, by rfl⟩ : syracuseStep 2678683 = 4018025) B4018025
theorem B1761257 : Blo 924580 1761257 := bstep (se 2 (by rfl) ⟨660471, by rfl⟩ : syracuseStep 1761257 = 1320943) B1320943
theorem B1564663 : Blo 924580 1564663 := bstep (se 1 (by rfl) ⟨1173497, by rfl⟩ : syracuseStep 1564663 = 2346995) B2346995
theorem B1040575 : Blo 924580 1040575 := bstep (se 1 (by rfl) ⟨780431, by rfl⟩ : syracuseStep 1040575 = 1560863) B1560863
theorem B1564879 : Blo 924580 1564879 := bstep (se 1 (by rfl) ⟨1173659, by rfl⟩ : syracuseStep 1564879 = 2347319) B2347319
theorem B7528733 : Blo 924580 7528733 := bstep (se 3 (by rfl) ⟨1411637, by rfl⟩ : syracuseStep 7528733 = 2823275) B2823275
theorem B3957275 : Blo 924580 3957275 := bstep (se 1 (by rfl) ⟨2967956, by rfl⟩ : syracuseStep 3957275 = 5935913) B5935913
theorem B1041007 : Blo 924580 1041007 := bstep (se 1 (by rfl) ⟨780755, by rfl⟩ : syracuseStep 1041007 = 1561511) B1561511
theorem B1041115 : Blo 924580 1041115 := bstep (se 1 (by rfl) ⟨780836, by rfl⟩ : syracuseStep 1041115 = 1561673) B1561673
theorem B1762145 : Blo 924580 1762145 := bstep (se 2 (by rfl) ⟨660804, by rfl⟩ : syracuseStep 1762145 = 1321609) B1321609
theorem B1565743 : Blo 924580 1565743 := bstep (se 1 (by rfl) ⟨1174307, by rfl⟩ : syracuseStep 1565743 = 2348615) B2348615
theorem B1172647 : Blo 924580 1172647 := bstep (se 1 (by rfl) ⟨879485, by rfl⟩ : syracuseStep 1172647 = 1758971) B1758971
theorem B1762715 : Blo 924580 1762715 := bstep (se 1 (by rfl) ⟨1322036, by rfl⟩ : syracuseStep 1762715 = 2644073) B2644073
theorem B5432903 : Blo 924580 5432903 := bstep (se 1 (by rfl) ⟨4074677, by rfl⟩ : syracuseStep 5432903 = 8149355) B8149355
theorem B9528965 : Blo 924580 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B3958607 : Blo 924580 3958607 := bstep (se 1 (by rfl) ⟨2968955, by rfl⟩ : syracuseStep 3958607 = 5937911) B5937911
theorem B5924765 : Blo 924580 5924765 := bstep (se 3 (by rfl) ⟨1110893, by rfl⟩ : syracuseStep 5924765 = 2221787) B2221787
theorem B5007863 : Blo 924580 5007863 := bstep (se 1 (by rfl) ⟨3755897, by rfl⟩ : syracuseStep 5007863 = 7511795) B7511795
theorem B1043239 : Blo 924580 1043239 := bstep (se 1 (by rfl) ⟨782429, by rfl⟩ : syracuseStep 1043239 = 1564859) B1564859
theorem B9038765 : Blo 924580 9038765 := bstep (se 3 (by rfl) ⟨1694768, by rfl⟩ : syracuseStep 9038765 = 3389537) B3389537
theorem B1174495 : Blo 924580 1174495 := bstep (se 1 (by rfl) ⟨880871, by rfl⟩ : syracuseStep 1174495 = 1761743) B1761743
theorem B3763423 : Blo 924580 3763423 := bstep (se 1 (by rfl) ⟨2822567, by rfl⟩ : syracuseStep 3763423 = 5645135) B5645135
theorem B4680989 : Blo 924580 4680989 := bstep (se 3 (by rfl) ⟨877685, by rfl⟩ : syracuseStep 4680989 = 1755371) B1755371
theorem B3173855 : Blo 924580 3173855 := bstep (se 1 (by rfl) ⟨2380391, by rfl⟩ : syracuseStep 3173855 = 4760783) B4760783
theorem B1044463 : Blo 924580 1044463 := bstep (se 1 (by rfl) ⟨783347, by rfl⟩ : syracuseStep 1044463 = 1566695) B1566695
theorem B1667155 : Blo 924580 1667155 := bstep (se 1 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 1667155 = 2500733) B2500733
theorem B1044607 : Blo 924580 1044607 := bstep (se 1 (by rfl) ⟨783455, by rfl⟩ : syracuseStep 1044607 = 1566911) B1566911
theorem B7041167 : Blo 924580 7041167 := bstep (se 1 (by rfl) ⟨5280875, by rfl⟩ : syracuseStep 7041167 = 10561751) B10561751
theorem B4681961 : Blo 924580 4681961 := bstep (se 2 (by rfl) ⟨1755735, by rfl⟩ : syracuseStep 4681961 = 3511471) B3511471
theorem B2224487 : Blo 924580 2224487 := bstep (se 1 (by rfl) ⟨1668365, by rfl⟩ : syracuseStep 2224487 = 3336731) B3336731
theorem B9498991 : Blo 924580 9498991 := bstep (se 1 (by rfl) ⟨7124243, by rfl⟩ : syracuseStep 9498991 = 14248487) B14248487
theorem B11859007 : Blo 924580 11859007 := bstep (se 1 (by rfl) ⟨8894255, by rfl⟩ : syracuseStep 11859007 = 17788511) B17788511
theorem B3012191 : Blo 924580 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B4519577 : Blo 924580 4519577 := bstep (se 2 (by rfl) ⟨1694841, by rfl⟩ : syracuseStep 4519577 = 3389683) B3389683
theorem B8910557 : Blo 924580 8910557 := bstep (se 3 (by rfl) ⟨1670729, by rfl⟩ : syracuseStep 8910557 = 3341459) B3341459
theorem B5011307 : Blo 924580 5011307 := bstep (se 1 (by rfl) ⟨3758480, by rfl⟩ : syracuseStep 5011307 = 7516961) B7516961
theorem B6027709 : Blo 924580 6027709 := bstep (se 3 (by rfl) ⟨1130195, by rfl⟩ : syracuseStep 6027709 = 2260391) B2260391
theorem B126974827 : Blo 924580 126974827 := bstep (se 1 (by rfl) ⟨95231120, by rfl⟩ : syracuseStep 126974827 = 190462241) B190462241
theorem B8911943 : Blo 924580 8911943 := bstep (se 1 (by rfl) ⟨6683957, by rfl⟩ : syracuseStep 8911943 = 13367915) B13367915
theorem B2817305 : Blo 924580 2817305 := bstep (se 2 (by rfl) ⟨1056489, by rfl⟩ : syracuseStep 2817305 = 2112979) B2112979
theorem B13369063 : Blo 924580 13369063 := bstep (se 1 (by rfl) ⟨10026797, by rfl⟩ : syracuseStep 13369063 = 20053595) B20053595
theorem B4226845 : Blo 924580 4226845 := bstep (se 3 (by rfl) ⟨792533, by rfl⟩ : syracuseStep 4226845 = 1585067) B1585067
theorem B4686011 : Blo 924580 4686011 := bstep (se 1 (by rfl) ⟨3514508, by rfl⟩ : syracuseStep 4686011 = 7029017) B7029017
theorem B4686497 : Blo 924580 4686497 := bstep (se 2 (by rfl) ⟨1757436, by rfl⟩ : syracuseStep 4686497 = 3514873) B3514873
theorem B2851609 : Blo 924580 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B2818871 : Blo 924580 2818871 := bstep (se 1 (by rfl) ⟨2114153, by rfl⟩ : syracuseStep 2818871 = 4228307) B4228307
theorem B5931863 : Blo 924580 5931863 := bstep (se 1 (by rfl) ⟨4448897, by rfl⟩ : syracuseStep 5931863 = 8897795) B8897795
theorem B3965851 : Blo 924580 3965851 := bstep (se 1 (by rfl) ⟨2974388, by rfl⟩ : syracuseStep 3965851 = 5948777) B5948777
theorem B5932763 : Blo 924580 5932763 := bstep (se 1 (by rfl) ⟨4449572, by rfl⟩ : syracuseStep 5932763 = 8899145) B8899145
theorem B15829505 : Blo 924580 15829505 := bstep (se 2 (by rfl) ⟨5936064, by rfl⟩ : syracuseStep 15829505 = 11872129) B11872129
theorem B2231023 : Blo 924580 2231023 := bstep (se 1 (by rfl) ⟨1673267, by rfl⟩ : syracuseStep 2231023 = 3346535) B3346535
theorem B11898373 : Blo 924580 11898373 := bstep (se 4 (by rfl) ⟨1115472, by rfl⟩ : syracuseStep 11898373 = 2230945) B2230945
theorem B5279327 : Blo 924580 5279327 := bstep (se 1 (by rfl) ⟨3959495, by rfl⟩ : syracuseStep 5279327 = 7918991) B7918991
theorem B181080197 : Blo 924580 181080197 := bstep (se 4 (by rfl) ⟨16976268, by rfl⟩ : syracuseStep 181080197 = 33952537) B33952537
theorem B5017897 : Blo 924580 5017897 := bstep (se 2 (by rfl) ⟨1881711, by rfl⟩ : syracuseStep 5017897 = 3763423) B3763423
theorem B33854453 : Blo 924580 33854453 := bstep (se 5 (by rfl) ⟨1586927, by rfl⟩ : syracuseStep 33854453 = 3173855) B3173855
theorem B10032335 : Blo 924580 10032335 := bstep (se 1 (by rfl) ⟨7524251, by rfl⟩ : syracuseStep 10032335 = 15048503) B15048503
theorem B5019155 : Blo 924580 5019155 := bstep (se 1 (by rfl) ⟨3764366, by rfl⟩ : syracuseStep 5019155 = 7528733) B7528733
theorem B1186255 : Blo 924580 1186255 := bstep (se 1 (by rfl) ⟨889691, by rfl⟩ : syracuseStep 1186255 = 1779383) B1779383
theorem B924667 : Blo 924580 924667 := bstep (se 1 (by rfl) ⟨693500, by rfl⟩ : syracuseStep 924667 = 1387001) B1387001
theorem B924703 : Blo 924580 924703 := bstep (se 1 (by rfl) ⟨693527, by rfl⟩ : syracuseStep 924703 = 1387055) B1387055
theorem B924991 : Blo 924580 924991 := bstep (se 1 (by rfl) ⟨693743, by rfl⟩ : syracuseStep 924991 = 1387487) B1387487
theorem B1318351 : Blo 924580 1318351 := bstep (se 1 (by rfl) ⟨988763, by rfl⟩ : syracuseStep 1318351 = 1977527) B1977527
theorem B3120659 : Blo 924580 3120659 := bstep (se 1 (by rfl) ⟨2340494, by rfl⟩ : syracuseStep 3120659 = 4680989) B4680989
theorem B5643827 : Blo 924580 5643827 := bstep (se 1 (by rfl) ⟨4232870, by rfl⟩ : syracuseStep 5643827 = 8465741) B8465741
theorem B925287 : Blo 924580 925287 := bstep (se 1 (by rfl) ⟨693965, by rfl⟩ : syracuseStep 925287 = 1387931) B1387931
theorem B925567 : Blo 924580 925567 := bstep (se 1 (by rfl) ⟨694175, by rfl⟩ : syracuseStep 925567 = 1388351) B1388351
theorem B8921015 : Blo 924580 8921015 := bstep (se 1 (by rfl) ⟨6690761, by rfl⟩ : syracuseStep 8921015 = 13381523) B13381523
theorem B925691 : Blo 924580 925691 := bstep (se 1 (by rfl) ⟨694268, by rfl⟩ : syracuseStep 925691 = 1388537) B1388537
theorem B4694111 : Blo 924580 4694111 := bstep (se 1 (by rfl) ⟨3520583, by rfl⟩ : syracuseStep 4694111 = 7041167) B7041167
theorem B3121307 : Blo 924580 3121307 := bstep (se 1 (by rfl) ⟨2340980, by rfl⟩ : syracuseStep 3121307 = 4681961) B4681961
theorem B925851 : Blo 924580 925851 := bstep (se 1 (by rfl) ⟨694388, by rfl⟩ : syracuseStep 925851 = 1388777) B1388777
theorem B1482991 : Blo 924580 1482991 := bstep (se 1 (by rfl) ⟨1112243, by rfl⟩ : syracuseStep 1482991 = 2224487) B2224487
theorem B925935 : Blo 924580 925935 := bstep (se 1 (by rfl) ⟨694451, by rfl⟩ : syracuseStep 925935 = 1388903) B1388903
theorem B8036945 : Blo 924580 8036945 := bstep (se 2 (by rfl) ⟨3013854, by rfl⟩ : syracuseStep 8036945 = 6027709) B6027709
theorem B926299 : Blo 924580 926299 := bstep (se 1 (by rfl) ⟨694724, by rfl⟩ : syracuseStep 926299 = 1389449) B1389449
theorem B926555 : Blo 924580 926555 := bstep (se 1 (by rfl) ⟨694916, by rfl⟩ : syracuseStep 926555 = 1389833) B1389833
theorem B926591 : Blo 924580 926591 := bstep (se 1 (by rfl) ⟨694943, by rfl⟩ : syracuseStep 926591 = 1389887) B1389887
theorem B2008127 : Blo 924580 2008127 := bstep (se 1 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 2008127 = 3012191) B3012191
theorem B5940371 : Blo 924580 5940371 := bstep (se 1 (by rfl) ⟨4455278, by rfl⟩ : syracuseStep 5940371 = 8910557) B8910557
theorem B926875 : Blo 924580 926875 := bstep (se 1 (by rfl) ⟨695156, by rfl⟩ : syracuseStep 926875 = 1390313) B1390313
theorem B926879 : Blo 924580 926879 := bstep (se 1 (by rfl) ⟨695159, by rfl⟩ : syracuseStep 926879 = 1390319) B1390319
theorem B927183 : Blo 924580 927183 := bstep (se 1 (by rfl) ⟨695387, by rfl⟩ : syracuseStep 927183 = 1390775) B1390775
theorem B3122657 : Blo 924580 3122657 := bstep (se 2 (by rfl) ⟨1170996, by rfl⟩ : syracuseStep 3122657 = 2341993) B2341993
theorem B927215 : Blo 924580 927215 := bstep (se 1 (by rfl) ⟨695411, by rfl⟩ : syracuseStep 927215 = 1390823) B1390823
theorem B927463 : Blo 924580 927463 := bstep (se 1 (by rfl) ⟨695597, by rfl⟩ : syracuseStep 927463 = 1391195) B1391195
theorem B1320743 : Blo 924580 1320743 := bstep (se 1 (by rfl) ⟨990557, by rfl⟩ : syracuseStep 1320743 = 1981115) B1981115
theorem B927559 : Blo 924580 927559 := bstep (se 1 (by rfl) ⟨695669, by rfl⟩ : syracuseStep 927559 = 1391339) B1391339
theorem B927579 : Blo 924580 927579 := bstep (se 1 (by rfl) ⟨695684, by rfl⟩ : syracuseStep 927579 = 1391369) B1391369
theorem B3516317 : Blo 924580 3516317 := bstep (se 3 (by rfl) ⟨659309, by rfl⟩ : syracuseStep 3516317 = 1318619) B1318619
theorem B5941295 : Blo 924580 5941295 := bstep (se 1 (by rfl) ⟨4455971, by rfl⟩ : syracuseStep 5941295 = 8911943) B8911943
theorem B1878203 : Blo 924580 1878203 := bstep (se 1 (by rfl) ⟨1408652, by rfl⟩ : syracuseStep 1878203 = 2817305) B2817305
theorem B6007081 : Blo 924580 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B1386911 : Blo 924580 1386911 := bstep (se 1 (by rfl) ⟨1040183, by rfl⟩ : syracuseStep 1386911 = 2080367) B2080367
theorem B928159 : Blo 924580 928159 := bstep (se 1 (by rfl) ⟨696119, by rfl⟩ : syracuseStep 928159 = 1392239) B1392239
theorem B928239 : Blo 924580 928239 := bstep (se 1 (by rfl) ⟨696179, by rfl⟩ : syracuseStep 928239 = 1392359) B1392359
theorem B1387103 : Blo 924580 1387103 := bstep (se 1 (by rfl) ⟨1040327, by rfl⟩ : syracuseStep 1387103 = 2080655) B2080655
theorem B928367 : Blo 924580 928367 := bstep (se 1 (by rfl) ⟨696275, by rfl⟩ : syracuseStep 928367 = 1392551) B1392551
theorem B10693291 : Blo 924580 10693291 := bstep (se 1 (by rfl) ⟨8019968, by rfl⟩ : syracuseStep 10693291 = 16039937) B16039937
theorem B1387433 : Blo 924580 1387433 := bstep (se 2 (by rfl) ⟨520287, by rfl⟩ : syracuseStep 1387433 = 1040575) B1040575
theorem B1387463 : Blo 924580 1387463 := bstep (se 1 (by rfl) ⟨1040597, by rfl⟩ : syracuseStep 1387463 = 2081195) B2081195
theorem B1387583 : Blo 924580 1387583 := bstep (se 1 (by rfl) ⟨1040687, by rfl⟩ : syracuseStep 1387583 = 2081375) B2081375
theorem B1387823 : Blo 924580 1387823 := bstep (se 1 (by rfl) ⟨1040867, by rfl⟩ : syracuseStep 1387823 = 2081735) B2081735
theorem B1388009 : Blo 924580 1388009 := bstep (se 2 (by rfl) ⟨520503, by rfl⟩ : syracuseStep 1388009 = 1041007) B1041007
theorem B1388063 : Blo 924580 1388063 := bstep (se 1 (by rfl) ⟨1041047, by rfl⟩ : syracuseStep 1388063 = 2082095) B2082095
theorem B1388153 : Blo 924580 1388153 := bstep (se 2 (by rfl) ⟨520557, by rfl⟩ : syracuseStep 1388153 = 1041115) B1041115
theorem B2633467 : Blo 924580 2633467 := bstep (se 1 (by rfl) ⟨1975100, by rfl⟩ : syracuseStep 2633467 = 3950201) B3950201
theorem B10006345 : Blo 924580 10006345 := bstep (se 2 (by rfl) ⟨3752379, by rfl⟩ : syracuseStep 10006345 = 7504759) B7504759
theorem B1388399 : Blo 924580 1388399 := bstep (se 1 (by rfl) ⟨1041299, by rfl⟩ : syracuseStep 1388399 = 2082599) B2082599
theorem B1388651 : Blo 924580 1388651 := bstep (se 1 (by rfl) ⟨1041488, by rfl⟩ : syracuseStep 1388651 = 2082977) B2082977
theorem B11251835 : Blo 924580 11251835 := bstep (se 1 (by rfl) ⟨8438876, by rfl⟩ : syracuseStep 11251835 = 16877753) B16877753
theorem B1389083 : Blo 924580 1389083 := bstep (se 1 (by rfl) ⟨1041812, by rfl⟩ : syracuseStep 1389083 = 2083625) B2083625
theorem B1389263 : Blo 924580 1389263 := bstep (se 1 (by rfl) ⟨1041947, by rfl⟩ : syracuseStep 1389263 = 2083895) B2083895
theorem B1979167 : Blo 924580 1979167 := bstep (se 1 (by rfl) ⟨1484375, by rfl⟩ : syracuseStep 1979167 = 2968751) B2968751
theorem B1389551 : Blo 924580 1389551 := bstep (se 1 (by rfl) ⟨1042163, by rfl⟩ : syracuseStep 1389551 = 2084327) B2084327
theorem B23737697 : Blo 924580 23737697 := bstep (se 2 (by rfl) ⟨8901636, by rfl⟩ : syracuseStep 23737697 = 17803273) B17803273
theorem B1389935 : Blo 924580 1389935 := bstep (se 1 (by rfl) ⟨1042451, by rfl⟩ : syracuseStep 1389935 = 2084903) B2084903
theorem B1390055 : Blo 924580 1390055 := bstep (se 1 (by rfl) ⟨1042541, by rfl⟩ : syracuseStep 1390055 = 2085083) B2085083
theorem B5944859 : Blo 924580 5944859 := bstep (se 1 (by rfl) ⟨4458644, by rfl⟩ : syracuseStep 5944859 = 8917289) B8917289
theorem B1390235 : Blo 924580 1390235 := bstep (se 1 (by rfl) ⟨1042676, by rfl⟩ : syracuseStep 1390235 = 2085353) B2085353
theorem B11908883 : Blo 924580 11908883 := bstep (se 1 (by rfl) ⟨8931662, by rfl⟩ : syracuseStep 11908883 = 17863325) B17863325
theorem B15218513 : Blo 924580 15218513 := bstep (se 2 (by rfl) ⟨5706942, by rfl⟩ : syracuseStep 15218513 = 11413885) B11413885
theorem B1390571 : Blo 924580 1390571 := bstep (se 1 (by rfl) ⟨1042928, by rfl⟩ : syracuseStep 1390571 = 2085857) B2085857
theorem B5945345 : Blo 924580 5945345 := bstep (se 2 (by rfl) ⟨2229504, by rfl⟩ : syracuseStep 5945345 = 4459009) B4459009
theorem B1390655 : Blo 924580 1390655 := bstep (se 1 (by rfl) ⟨1042991, by rfl⟩ : syracuseStep 1390655 = 2085983) B2085983
theorem B2340971 : Blo 924580 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B2341001 : Blo 924580 2341001 := bstep (se 2 (by rfl) ⟨877875, by rfl⟩ : syracuseStep 2341001 = 1755751) B1755751
theorem B1390985 : Blo 924580 1390985 := bstep (se 2 (by rfl) ⟨521619, by rfl⟩ : syracuseStep 1390985 = 1043239) B1043239
theorem B1391159 : Blo 924580 1391159 := bstep (se 1 (by rfl) ⟨1043369, by rfl⟩ : syracuseStep 1391159 = 2086739) B2086739
theorem B2341619 : Blo 924580 2341619 := bstep (se 1 (by rfl) ⟨1756214, by rfl⟩ : syracuseStep 2341619 = 3512429) B3512429
theorem B4700915 : Blo 924580 4700915 := bstep (se 1 (by rfl) ⟨3525686, by rfl⟩ : syracuseStep 4700915 = 7051373) B7051373
theorem B1391483 : Blo 924580 1391483 := bstep (se 1 (by rfl) ⟨1043612, by rfl⟩ : syracuseStep 1391483 = 2087225) B2087225
theorem B10534049 : Blo 924580 10534049 := bstep (se 2 (by rfl) ⟨3950268, by rfl⟩ : syracuseStep 10534049 = 7900537) B7900537
theorem B2112839 : Blo 924580 2112839 := bstep (se 1 (by rfl) ⟨1584629, by rfl⟩ : syracuseStep 2112839 = 3169259) B3169259
theorem B1392095 : Blo 924580 1392095 := bstep (se 1 (by rfl) ⟨1044071, by rfl⟩ : syracuseStep 1392095 = 2088143) B2088143
theorem B2080475 : Blo 924580 2080475 := bstep (se 1 (by rfl) ⟨1560356, by rfl⟩ : syracuseStep 2080475 = 3120713) B3120713
theorem B1392347 : Blo 924580 1392347 := bstep (se 1 (by rfl) ⟨1044260, by rfl⟩ : syracuseStep 1392347 = 2088521) B2088521
theorem B2080745 : Blo 924580 2080745 := bstep (se 2 (by rfl) ⟨780279, by rfl⟩ : syracuseStep 2080745 = 1560559) B1560559
theorem B1392617 : Blo 924580 1392617 := bstep (se 2 (by rfl) ⟨522231, by rfl⟩ : syracuseStep 1392617 = 1044463) B1044463
theorem B2113633 : Blo 924580 2113633 := bstep (se 2 (by rfl) ⟨792612, by rfl⟩ : syracuseStep 2113633 = 1585225) B1585225
theorem B1392809 : Blo 924580 1392809 := bstep (se 2 (by rfl) ⟨522303, by rfl⟩ : syracuseStep 1392809 = 1044607) B1044607
theorem B2343127 : Blo 924580 2343127 := bstep (se 1 (by rfl) ⟨1757345, by rfl⟩ : syracuseStep 2343127 = 3514691) B3514691
theorem B2638183 : Blo 924580 2638183 := bstep (se 1 (by rfl) ⟨1978637, by rfl⟩ : syracuseStep 2638183 = 3957275) B3957275
theorem B12665321 : Blo 924580 12665321 := bstep (se 2 (by rfl) ⟨4749495, by rfl⟩ : syracuseStep 12665321 = 9498991) B9498991
theorem B7521011 : Blo 924580 7521011 := bstep (se 1 (by rfl) ⟨5640758, by rfl⟩ : syracuseStep 7521011 = 11281517) B11281517
theorem B3621935 : Blo 924580 3621935 := bstep (se 1 (by rfl) ⟨2716451, by rfl⟩ : syracuseStep 3621935 = 5432903) B5432903
theorem B2639071 : Blo 924580 2639071 := bstep (se 1 (by rfl) ⟨1979303, by rfl⟩ : syracuseStep 2639071 = 3958607) B3958607
theorem B3949843 : Blo 924580 3949843 := bstep (se 1 (by rfl) ⟨2962382, by rfl⟩ : syracuseStep 3949843 = 5924765) B5924765
theorem B13354301 : Blo 924580 13354301 := bstep (se 3 (by rfl) ⟨2503931, by rfl⟩ : syracuseStep 13354301 = 5007863) B5007863
theorem B2082203 : Blo 924580 2082203 := bstep (se 1 (by rfl) ⟨1561652, by rfl⟩ : syracuseStep 2082203 = 3123305) B3123305
theorem B15812009 : Blo 924580 15812009 := bstep (se 2 (by rfl) ⟨5929503, by rfl⟩ : syracuseStep 15812009 = 11859007) B11859007
theorem B2344403 : Blo 924580 2344403 := bstep (se 1 (by rfl) ⟨1758302, by rfl⟩ : syracuseStep 2344403 = 3516605) B3516605
theorem B8898335 : Blo 924580 8898335 := bstep (se 1 (by rfl) ⟨6673751, by rfl⟩ : syracuseStep 8898335 = 13347503) B13347503
theorem B2345183 : Blo 924580 2345183 := bstep (se 1 (by rfl) ⟨1758887, by rfl⟩ : syracuseStep 2345183 = 3517775) B3517775
theorem B3131675 : Blo 924580 3131675 := bstep (se 1 (by rfl) ⟨2348756, by rfl⟩ : syracuseStep 3131675 = 4697513) B4697513
theorem B7621121 : Blo 924580 7621121 := bstep (se 2 (by rfl) ⟨2857920, by rfl⟩ : syracuseStep 7621121 = 5715841) B5715841
theorem B14437025 : Blo 924580 14437025 := bstep (se 2 (by rfl) ⟨5413884, by rfl⟩ : syracuseStep 14437025 = 10827769) B10827769
theorem B1755911 : Blo 924580 1755911 := bstep (se 1 (by rfl) ⟨1316933, by rfl⟩ : syracuseStep 1755911 = 2633867) B2633867
theorem B3525383 : Blo 924580 3525383 := bstep (se 1 (by rfl) ⟨2644037, by rfl⟩ : syracuseStep 3525383 = 5288075) B5288075
theorem B169299769 : Blo 924580 169299769 := bstep (se 2 (by rfl) ⟨63487413, by rfl⟩ : syracuseStep 169299769 = 126974827) B126974827
theorem B2084687 : Blo 924580 2084687 := bstep (se 1 (by rfl) ⟨1563515, by rfl⟩ : syracuseStep 2084687 = 3127031) B3127031
theorem B2085407 : Blo 924580 2085407 := bstep (se 1 (by rfl) ⟨1564055, by rfl⟩ : syracuseStep 2085407 = 3128111) B3128111
theorem B2642489 : Blo 924580 2642489 := bstep (se 2 (by rfl) ⟨990933, by rfl⟩ : syracuseStep 2642489 = 1981867) B1981867
theorem B1757999 : Blo 924580 1757999 := bstep (se 1 (by rfl) ⟨1318499, by rfl⟩ : syracuseStep 1757999 = 2636999) B2636999
theorem B10539881 : Blo 924580 10539881 := bstep (se 2 (by rfl) ⟨3952455, by rfl⟩ : syracuseStep 10539881 = 7904911) B7904911
theorem B2085839 : Blo 924580 2085839 := bstep (se 1 (by rfl) ⟨1564379, by rfl⟩ : syracuseStep 2085839 = 3128759) B3128759
theorem B2085929 : Blo 924580 2085929 := bstep (se 2 (by rfl) ⟨782223, by rfl⟩ : syracuseStep 2085929 = 1564447) B1564447
theorem B2086199 : Blo 924580 2086199 := bstep (se 1 (by rfl) ⟨1564649, by rfl⟩ : syracuseStep 2086199 = 3129299) B3129299
theorem B2086217 : Blo 924580 2086217 := bstep (se 2 (by rfl) ⟨782331, by rfl⟩ : syracuseStep 2086217 = 1564663) B1564663
theorem B18044315 : Blo 924580 18044315 := bstep (se 1 (by rfl) ⟨13533236, by rfl⟩ : syracuseStep 18044315 = 27066473) B27066473
theorem B2086505 : Blo 924580 2086505 := bstep (se 2 (by rfl) ⟨782439, by rfl⟩ : syracuseStep 2086505 = 1564879) B1564879
theorem B2643617 : Blo 924580 2643617 := bstep (se 2 (by rfl) ⟨991356, by rfl⟩ : syracuseStep 2643617 = 1982713) B1982713
theorem B1562287 : Blo 924580 1562287 := bstep (se 1 (by rfl) ⟨1171715, by rfl⟩ : syracuseStep 1562287 = 2343431) B2343431
theorem B11261855 : Blo 924580 11261855 := bstep (se 1 (by rfl) ⟨8446391, by rfl⟩ : syracuseStep 11261855 = 16892783) B16892783
theorem B2348959 : Blo 924580 2348959 := bstep (se 1 (by rfl) ⟨1761719, by rfl⟩ : syracuseStep 2348959 = 3523439) B3523439
theorem B2087135 : Blo 924580 2087135 := bstep (se 1 (by rfl) ⟨1565351, by rfl⟩ : syracuseStep 2087135 = 3130703) B3130703
theorem B2087207 : Blo 924580 2087207 := bstep (se 1 (by rfl) ⟨1565405, by rfl⟩ : syracuseStep 2087207 = 3130811) B3130811
theorem B6674845 : Blo 924580 6674845 := bstep (se 3 (by rfl) ⟨1251533, by rfl⟩ : syracuseStep 6674845 = 2503067) B2503067
theorem B2087567 : Blo 924580 2087567 := bstep (se 1 (by rfl) ⟨1565675, by rfl⟩ : syracuseStep 2087567 = 3131351) B3131351
theorem B940735 : Blo 924580 940735 := bstep (se 1 (by rfl) ⟨705551, by rfl⟩ : syracuseStep 940735 = 1411103) B1411103
theorem B2087657 : Blo 924580 2087657 := bstep (se 2 (by rfl) ⟨782871, by rfl⟩ : syracuseStep 2087657 = 1565743) B1565743
theorem B1563529 : Blo 924580 1563529 := bstep (se 2 (by rfl) ⟨586323, by rfl⟩ : syracuseStep 1563529 = 1172647) B1172647
theorem B5627015 : Blo 924580 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B3562705 : Blo 924580 3562705 := bstep (se 2 (by rfl) ⟨1336014, by rfl⟩ : syracuseStep 3562705 = 2672029) B2672029
theorem B33873137 : Blo 924580 33873137 := bstep (se 2 (by rfl) ⟨12702426, by rfl⟩ : syracuseStep 33873137 = 25404853) B25404853
theorem B11427065 : Blo 924580 11427065 := bstep (se 2 (by rfl) ⟨4285149, by rfl⟩ : syracuseStep 11427065 = 8570299) B8570299
theorem B1563995 : Blo 924580 1563995 := bstep (se 1 (by rfl) ⟨1172996, by rfl⟩ : syracuseStep 1563995 = 2345993) B2345993
theorem B7822817 : Blo 924580 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B3006191 : Blo 924580 3006191 := bstep (se 1 (by rfl) ⟨2254643, by rfl⟩ : syracuseStep 3006191 = 4509287) B4509287
theorem B7528403 : Blo 924580 7528403 := bstep (se 1 (by rfl) ⟨5646302, by rfl⟩ : syracuseStep 7528403 = 11292605) B11292605
theorem B5267663 : Blo 924580 5267663 := bstep (se 1 (by rfl) ⟨3950747, by rfl⟩ : syracuseStep 5267663 = 7901495) B7901495
theorem B1564967 : Blo 924580 1564967 := bstep (se 1 (by rfl) ⟨1173725, by rfl⟩ : syracuseStep 1564967 = 2347451) B2347451
theorem B5628791 : Blo 924580 5628791 := bstep (se 1 (by rfl) ⟨4221593, by rfl⟩ : syracuseStep 5628791 = 8443187) B8443187
theorem B1041511 : Blo 924580 1041511 := bstep (se 1 (by rfl) ⟨781133, by rfl⟩ : syracuseStep 1041511 = 1562267) B1562267
theorem B1565993 : Blo 924580 1565993 := bstep (se 2 (by rfl) ⟨587247, by rfl⟩ : syracuseStep 1565993 = 1174495) B1174495
theorem B3335681 : Blo 924580 3335681 := bstep (se 2 (by rfl) ⟨1250880, by rfl⟩ : syracuseStep 3335681 = 2501761) B2501761
theorem B1566263 : Blo 924580 1566263 := bstep (se 1 (by rfl) ⟨1174697, by rfl⟩ : syracuseStep 1566263 = 2349395) B2349395
theorem B50652971 : Blo 924580 50652971 := bstep (se 1 (by rfl) ⟨37989728, by rfl⟩ : syracuseStep 50652971 = 75979457) B75979457
theorem B1206139 : Blo 924580 1206139 := bstep (se 1 (by rfl) ⟨904604, by rfl⟩ : syracuseStep 1206139 = 1809209) B1809209
theorem B23750819 : Blo 924580 23750819 := bstep (se 1 (by rfl) ⟨17813114, by rfl⟩ : syracuseStep 23750819 = 35626229) B35626229
theorem B1174171 : Blo 924580 1174171 := bstep (se 1 (by rfl) ⟨880628, by rfl⟩ : syracuseStep 1174171 = 1761257) B1761257
theorem B2222873 : Blo 924580 2222873 := bstep (se 2 (by rfl) ⟨833577, by rfl⟩ : syracuseStep 2222873 = 1667155) B1667155
theorem B1174763 : Blo 924580 1174763 := bstep (se 1 (by rfl) ⟨881072, by rfl⟩ : syracuseStep 1174763 = 1762145) B1762145
theorem B8023643 : Blo 924580 8023643 := bstep (se 1 (by rfl) ⟨6017732, by rfl⟩ : syracuseStep 8023643 = 12035465) B12035465
theorem B1175143 : Blo 924580 1175143 := bstep (se 1 (by rfl) ⟨881357, by rfl⟩ : syracuseStep 1175143 = 1762715) B1762715
theorem B6352643 : Blo 924580 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B5927249 : Blo 924580 5927249 := bstep (se 2 (by rfl) ⟨2222718, by rfl⟩ : syracuseStep 5927249 = 4445437) B4445437
theorem B4682123 : Blo 924580 4682123 := bstep (se 1 (by rfl) ⟨3511592, by rfl⟩ : syracuseStep 4682123 = 7023185) B7023185
theorem B6025843 : Blo 924580 6025843 := bstep (se 1 (by rfl) ⟨4519382, by rfl⟩ : syracuseStep 6025843 = 9038765) B9038765
theorem B1668251 : Blo 924580 1668251 := bstep (se 1 (by rfl) ⟨1251188, by rfl⟩ : syracuseStep 1668251 = 2502377) B2502377
theorem B8451793 : Blo 924580 8451793 := bstep (se 2 (by rfl) ⟨3169422, by rfl⟩ : syracuseStep 8451793 = 6338845) B6338845
theorem B4683743 : Blo 924580 4683743 := bstep (se 1 (by rfl) ⟨3512807, by rfl⟩ : syracuseStep 4683743 = 7025615) B7025615
theorem B7043111 : Blo 924580 7043111 := bstep (se 1 (by rfl) ⟨5282333, by rfl⟩ : syracuseStep 7043111 = 10564667) B10564667
theorem B5273747 : Blo 924580 5273747 := bstep (se 1 (by rfl) ⟨3955310, by rfl⟩ : syracuseStep 5273747 = 7910621) B7910621
theorem B1669339 : Blo 924580 1669339 := bstep (se 1 (by rfl) ⟨1252004, by rfl⟩ : syracuseStep 1669339 = 2504009) B2504009
theorem B3013051 : Blo 924580 3013051 := bstep (se 1 (by rfl) ⟨2259788, by rfl⟩ : syracuseStep 3013051 = 4519577) B4519577
theorem B3340871 : Blo 924580 3340871 := bstep (se 1 (by rfl) ⟨2505653, by rfl⟩ : syracuseStep 3340871 = 5011307) B5011307
theorem B4684553 : Blo 924580 4684553 := bstep (se 2 (by rfl) ⟨1756707, by rfl⟩ : syracuseStep 4684553 = 3513415) B3513415
theorem B5274953 : Blo 924580 5274953 := bstep (se 2 (by rfl) ⟨1978107, by rfl⟩ : syracuseStep 5274953 = 3956215) B3956215
theorem B28540349 : Blo 924580 28540349 := bstep (se 3 (by rfl) ⟨5351315, by rfl⟩ : syracuseStep 28540349 = 10702631) B10702631
theorem B17825417 : Blo 924580 17825417 := bstep (se 2 (by rfl) ⟨6684531, by rfl⟩ : syracuseStep 17825417 = 13369063) B13369063
theorem B5635793 : Blo 924580 5635793 := bstep (se 2 (by rfl) ⟨2113422, by rfl⟩ : syracuseStep 5635793 = 4226845) B4226845
theorem B3571577 : Blo 924580 3571577 := bstep (se 2 (by rfl) ⟨1339341, by rfl⟩ : syracuseStep 3571577 = 2678683) B2678683
theorem B5014007 : Blo 924580 5014007 := bstep (se 1 (by rfl) ⟨3760505, by rfl⟩ : syracuseStep 5014007 = 7521011) B7521011
theorem B11272709 : Blo 924580 11272709 := bstep (se 4 (by rfl) ⟨1056816, by rfl⟩ : syracuseStep 11272709 = 2113633) B2113633
theorem B3802145 : Blo 924580 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B5932223 : Blo 924580 5932223 := bstep (se 1 (by rfl) ⟨4449167, by rfl⟩ : syracuseStep 5932223 = 8898335) B8898335
theorem B10553003 : Blo 924580 10553003 := bstep (se 1 (by rfl) ⟨7914752, by rfl⟩ : syracuseStep 10553003 = 15829505) B15829505
theorem B5080747 : Blo 924580 5080747 := bstep (se 1 (by rfl) ⟨3810560, by rfl⟩ : syracuseStep 5080747 = 7621121) B7621121
theorem B1608185 : Blo 924580 1608185 := bstep (se 2 (by rfl) ⟨603069, by rfl⟩ : syracuseStep 1608185 = 1206139) B1206139
theorem B120720131 : Blo 924580 120720131 := bstep (se 1 (by rfl) ⟨90540098, by rfl⟩ : syracuseStep 120720131 = 181080197) B181080197
theorem B6688223 : Blo 924580 6688223 := bstep (se 1 (by rfl) ⟨5016167, by rfl⟩ : syracuseStep 6688223 = 10032335) B10032335
theorem B14257721 : Blo 924580 14257721 := bstep (se 2 (by rfl) ⟨5346645, by rfl⟩ : syracuseStep 14257721 = 10693291) B10693291
theorem B12029543 : Blo 924580 12029543 := bstep (se 1 (by rfl) ⟨9022157, by rfl⟩ : syracuseStep 12029543 = 18044315) B18044315
theorem B3346103 : Blo 924580 3346103 := bstep (se 1 (by rfl) ⟨2509577, by rfl⟩ : syracuseStep 3346103 = 5019155) B5019155
theorem B7507903 : Blo 924580 7507903 := bstep (se 1 (by rfl) ⟨5630927, by rfl⟩ : syracuseStep 7507903 = 11261855) B11261855
theorem B15864497 : Blo 924580 15864497 := bstep (se 2 (by rfl) ⟨5949186, by rfl⟩ : syracuseStep 15864497 = 11898373) B11898373
theorem B22582091 : Blo 924580 22582091 := bstep (se 1 (by rfl) ⟨16936568, by rfl⟩ : syracuseStep 22582091 = 33873137) B33873137
theorem B5215211 : Blo 924580 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B3511289 : Blo 924580 3511289 := bstep (se 2 (by rfl) ⟨1316733, by rfl⟩ : syracuseStep 3511289 = 2633467) B2633467
theorem B13341793 : Blo 924580 13341793 := bstep (se 2 (by rfl) ⟨5003172, by rfl⟩ : syracuseStep 13341793 = 10006345) B10006345
theorem B5018935 : Blo 924580 5018935 := bstep (se 1 (by rfl) ⟨3764201, by rfl⟩ : syracuseStep 5018935 = 7528403) B7528403
theorem B3511775 : Blo 924580 3511775 := bstep (se 1 (by rfl) ⟨2633831, by rfl⟩ : syracuseStep 3511775 = 5267663) B5267663
theorem B6690529 : Blo 924580 6690529 := bstep (se 2 (by rfl) ⟨2508948, by rfl⟩ : syracuseStep 6690529 = 5017897) B5017897
theorem B15833879 : Blo 924580 15833879 := bstep (se 1 (by rfl) ⟨11875409, by rfl⟩ : syracuseStep 15833879 = 23750819) B23750819
theorem B1252135 : Blo 924580 1252135 := bstep (se 1 (by rfl) ⟨939101, by rfl⟩ : syracuseStep 1252135 = 1878203) B1878203
theorem B924607 : Blo 924580 924607 := bstep (se 1 (by rfl) ⟨693455, by rfl⟩ : syracuseStep 924607 = 1386911) B1386911
theorem B924735 : Blo 924580 924735 := bstep (se 1 (by rfl) ⟨693551, by rfl⟩ : syracuseStep 924735 = 1387103) B1387103
theorem B1481915 : Blo 924580 1481915 := bstep (se 1 (by rfl) ⟨1111436, by rfl⟩ : syracuseStep 1481915 = 2222873) B2222873
theorem B924955 : Blo 924580 924955 := bstep (se 1 (by rfl) ⟨693716, by rfl⟩ : syracuseStep 924955 = 1387433) B1387433
theorem B924975 : Blo 924580 924975 := bstep (se 1 (by rfl) ⟨693731, by rfl⟩ : syracuseStep 924975 = 1387463) B1387463
theorem B925055 : Blo 924580 925055 := bstep (se 1 (by rfl) ⟨693791, by rfl⟩ : syracuseStep 925055 = 1387583) B1387583
theorem B925215 : Blo 924580 925215 := bstep (se 1 (by rfl) ⟨693911, by rfl⟩ : syracuseStep 925215 = 1387823) B1387823
theorem B925339 : Blo 924580 925339 := bstep (se 1 (by rfl) ⟨694004, by rfl⟩ : syracuseStep 925339 = 1388009) B1388009
theorem B925375 : Blo 924580 925375 := bstep (se 1 (by rfl) ⟨694031, by rfl⟩ : syracuseStep 925375 = 1388063) B1388063
theorem B5349095 : Blo 924580 5349095 := bstep (se 1 (by rfl) ⟨4011821, by rfl⟩ : syracuseStep 5349095 = 8023643) B8023643
theorem B925435 : Blo 924580 925435 := bstep (se 1 (by rfl) ⟨694076, by rfl⟩ : syracuseStep 925435 = 1388153) B1388153
theorem B4235095 : Blo 924580 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B925599 : Blo 924580 925599 := bstep (se 1 (by rfl) ⟨694199, by rfl⟩ : syracuseStep 925599 = 1388399) B1388399
theorem B925767 : Blo 924580 925767 := bstep (se 1 (by rfl) ⟨694325, by rfl⟩ : syracuseStep 925767 = 1388651) B1388651
theorem B3121415 : Blo 924580 3121415 := bstep (se 1 (by rfl) ⟨2341061, by rfl⟩ : syracuseStep 3121415 = 4682123) B4682123
theorem B926055 : Blo 924580 926055 := bstep (se 1 (by rfl) ⟨694541, by rfl⟩ : syracuseStep 926055 = 1389083) B1389083
theorem B926175 : Blo 924580 926175 := bstep (se 1 (by rfl) ⟨694631, by rfl⟩ : syracuseStep 926175 = 1389263) B1389263
theorem B1581673 : Blo 924580 1581673 := bstep (se 2 (by rfl) ⟨593127, by rfl⟩ : syracuseStep 1581673 = 1186255) B1186255
theorem B926367 : Blo 924580 926367 := bstep (se 1 (by rfl) ⟨694775, by rfl⟩ : syracuseStep 926367 = 1389551) B1389551
theorem B926623 : Blo 924580 926623 := bstep (se 1 (by rfl) ⟨694967, by rfl⟩ : syracuseStep 926623 = 1389935) B1389935
theorem B1254313 : Blo 924580 1254313 := bstep (se 2 (by rfl) ⟨470367, by rfl⟩ : syracuseStep 1254313 = 940735) B940735
theorem B926703 : Blo 924580 926703 := bstep (se 1 (by rfl) ⟨695027, by rfl⟩ : syracuseStep 926703 = 1390055) B1390055
theorem B926823 : Blo 924580 926823 := bstep (se 1 (by rfl) ⟨695117, by rfl⟩ : syracuseStep 926823 = 1390235) B1390235
theorem B7939255 : Blo 924580 7939255 := bstep (se 1 (by rfl) ⟨5954441, by rfl⟩ : syracuseStep 7939255 = 11908883) B11908883
theorem B3122495 : Blo 924580 3122495 := bstep (se 1 (by rfl) ⟨2341871, by rfl⟩ : syracuseStep 3122495 = 4683743) B4683743
theorem B927047 : Blo 924580 927047 := bstep (se 1 (by rfl) ⟨695285, by rfl⟩ : syracuseStep 927047 = 1390571) B1390571
theorem B4695407 : Blo 924580 4695407 := bstep (se 1 (by rfl) ⟨3521555, by rfl⟩ : syracuseStep 4695407 = 7043111) B7043111
theorem B927103 : Blo 924580 927103 := bstep (se 1 (by rfl) ⟨695327, by rfl⟩ : syracuseStep 927103 = 1390655) B1390655
theorem B3515831 : Blo 924580 3515831 := bstep (se 1 (by rfl) ⟨2636873, by rfl⟩ : syracuseStep 3515831 = 5273747) B5273747
theorem B927323 : Blo 924580 927323 := bstep (se 1 (by rfl) ⟨695492, by rfl⟩ : syracuseStep 927323 = 1390985) B1390985
theorem B927439 : Blo 924580 927439 := bstep (se 1 (by rfl) ⟨695579, by rfl⟩ : syracuseStep 927439 = 1391159) B1391159
theorem B3123035 : Blo 924580 3123035 := bstep (se 1 (by rfl) ⟨2342276, by rfl⟩ : syracuseStep 3123035 = 4684553) B4684553
theorem B927655 : Blo 924580 927655 := bstep (se 1 (by rfl) ⟨695741, by rfl⟩ : syracuseStep 927655 = 1391483) B1391483
theorem B7022699 : Blo 924580 7022699 := bstep (se 1 (by rfl) ⟨5267024, by rfl⟩ : syracuseStep 7022699 = 10534049) B10534049
theorem B3516635 : Blo 924580 3516635 := bstep (se 1 (by rfl) ⟨2637476, by rfl⟩ : syracuseStep 3516635 = 5274953) B5274953
theorem B928063 : Blo 924580 928063 := bstep (se 1 (by rfl) ⟨696047, by rfl⟩ : syracuseStep 928063 = 1392095) B1392095
theorem B1386983 : Blo 924580 1386983 := bstep (se 1 (by rfl) ⟨1040237, by rfl⟩ : syracuseStep 1386983 = 2080475) B2080475
theorem B928231 : Blo 924580 928231 := bstep (se 1 (by rfl) ⟨696173, by rfl⟩ : syracuseStep 928231 = 1392347) B1392347
theorem B1387163 : Blo 924580 1387163 := bstep (se 1 (by rfl) ⟨1040372, by rfl⟩ : syracuseStep 1387163 = 2080745) B2080745
theorem B928411 : Blo 924580 928411 := bstep (se 1 (by rfl) ⟨696308, by rfl⟩ : syracuseStep 928411 = 1392617) B1392617
theorem B928539 : Blo 924580 928539 := bstep (se 1 (by rfl) ⟨696404, by rfl⟩ : syracuseStep 928539 = 1392809) B1392809
theorem B3124007 : Blo 924580 3124007 := bstep (se 1 (by rfl) ⟨2343005, by rfl⟩ : syracuseStep 3124007 = 4686011) B4686011
theorem B3124169 : Blo 924580 3124169 := bstep (se 2 (by rfl) ⟨1171563, by rfl⟩ : syracuseStep 3124169 = 2343127) B2343127
theorem B3124331 : Blo 924580 3124331 := bstep (se 1 (by rfl) ⟨2343248, by rfl⟩ : syracuseStep 3124331 = 4686497) B4686497
theorem B3517577 : Blo 924580 3517577 := bstep (se 2 (by rfl) ⟨1319091, by rfl⟩ : syracuseStep 3517577 = 2638183) B2638183
theorem B1879247 : Blo 924580 1879247 := bstep (se 1 (by rfl) ⟨1409435, by rfl⟩ : syracuseStep 1879247 = 2818871) B2818871
theorem B1388135 : Blo 924580 1388135 := bstep (se 1 (by rfl) ⟨1041101, by rfl⟩ : syracuseStep 1388135 = 2082203) B2082203
theorem B5287801 : Blo 924580 5287801 := bstep (se 2 (by rfl) ⟨1982925, by rfl⟩ : syracuseStep 5287801 = 3965851) B3965851
theorem B7909285 : Blo 924580 7909285 := bstep (se 4 (by rfl) ⟨741495, by rfl⟩ : syracuseStep 7909285 = 1482991) B1482991
theorem B1388681 : Blo 924580 1388681 := bstep (se 2 (by rfl) ⟨520755, by rfl⟩ : syracuseStep 1388681 = 1041511) B1041511
theorem B3518761 : Blo 924580 3518761 := bstep (se 2 (by rfl) ⟨1319535, by rfl⟩ : syracuseStep 3518761 = 2639071) B2639071
theorem B3519551 : Blo 924580 3519551 := bstep (se 1 (by rfl) ⟨2639663, by rfl⟩ : syracuseStep 3519551 = 5279327) B5279327
theorem B1389791 : Blo 924580 1389791 := bstep (se 1 (by rfl) ⟨1042343, by rfl⟩ : syracuseStep 1389791 = 2084687) B2084687
theorem B5355005 : Blo 924580 5355005 := bstep (se 3 (by rfl) ⟨1004063, by rfl⟩ : syracuseStep 5355005 = 2008127) B2008127
theorem B1390271 : Blo 924580 1390271 := bstep (se 1 (by rfl) ⟨1042703, by rfl⟩ : syracuseStep 1390271 = 2085407) B2085407
theorem B8009441 : Blo 924580 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B7026587 : Blo 924580 7026587 := bstep (se 1 (by rfl) ⟨5269940, by rfl⟩ : syracuseStep 7026587 = 10539881) B10539881
theorem B1390559 : Blo 924580 1390559 := bstep (se 1 (by rfl) ⟨1042919, by rfl⟩ : syracuseStep 1390559 = 2085839) B2085839
theorem B1390619 : Blo 924580 1390619 := bstep (se 1 (by rfl) ⟨1042964, by rfl⟩ : syracuseStep 1390619 = 2085929) B2085929
theorem B1390799 : Blo 924580 1390799 := bstep (se 1 (by rfl) ⟨1043099, by rfl⟩ : syracuseStep 1390799 = 2086199) B2086199
theorem B1390811 : Blo 924580 1390811 := bstep (se 1 (by rfl) ⟨1043108, by rfl⟩ : syracuseStep 1390811 = 2086217) B2086217
theorem B1391003 : Blo 924580 1391003 := bstep (se 1 (by rfl) ⟨1043252, by rfl⟩ : syracuseStep 1391003 = 2086505) B2086505
theorem B1391423 : Blo 924580 1391423 := bstep (se 1 (by rfl) ⟨1043567, by rfl⟩ : syracuseStep 1391423 = 2087135) B2087135
theorem B1391471 : Blo 924580 1391471 := bstep (se 1 (by rfl) ⟨1043603, by rfl⟩ : syracuseStep 1391471 = 2087207) B2087207
theorem B1391711 : Blo 924580 1391711 := bstep (se 1 (by rfl) ⟨1043783, by rfl⟩ : syracuseStep 1391711 = 2087567) B2087567
theorem B1391771 : Blo 924580 1391771 := bstep (se 1 (by rfl) ⟨1043828, by rfl⟩ : syracuseStep 1391771 = 2087657) B2087657
theorem B3751343 : Blo 924580 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B3521981 : Blo 924580 3521981 := bstep (se 3 (by rfl) ⟨660371, by rfl⟩ : syracuseStep 3521981 = 1320743) B1320743
theorem B7618043 : Blo 924580 7618043 := bstep (se 1 (by rfl) ⟨5713532, by rfl⟩ : syracuseStep 7618043 = 11427065) B11427065
theorem B2080439 : Blo 924580 2080439 := bstep (se 1 (by rfl) ⟨1560329, by rfl⟩ : syracuseStep 2080439 = 3120659) B3120659
theorem B5947343 : Blo 924580 5947343 := bstep (se 1 (by rfl) ⟨4460507, by rfl⟩ : syracuseStep 5947343 = 8921015) B8921015
theorem B3129407 : Blo 924580 3129407 := bstep (se 1 (by rfl) ⟨2347055, by rfl⟩ : syracuseStep 3129407 = 4694111) B4694111
theorem B2080871 : Blo 924580 2080871 := bstep (se 1 (by rfl) ⟨1560653, by rfl⟩ : syracuseStep 2080871 = 3121307) B3121307
theorem B5357963 : Blo 924580 5357963 := bstep (se 1 (by rfl) ⟨4018472, by rfl⟩ : syracuseStep 5357963 = 8036945) B8036945
theorem B3752527 : Blo 924580 3752527 := bstep (se 1 (by rfl) ⟨2814395, by rfl⟩ : syracuseStep 3752527 = 5628791) B5628791
theorem B2081771 : Blo 924580 2081771 := bstep (se 1 (by rfl) ⟨1561328, by rfl⟩ : syracuseStep 2081771 = 3122657) B3122657
theorem B2638889 : Blo 924580 2638889 := bstep (se 2 (by rfl) ⟨989583, by rfl⟩ : syracuseStep 2638889 = 1979167) B1979167
theorem B33768647 : Blo 924580 33768647 := bstep (se 1 (by rfl) ⟨25326485, by rfl⟩ : syracuseStep 33768647 = 50652971) B50652971
theorem B2344211 : Blo 924580 2344211 := bstep (se 1 (by rfl) ⟨1758158, by rfl⟩ : syracuseStep 2344211 = 3516317) B3516317
theorem B2083049 : Blo 924580 2083049 := bstep (se 2 (by rfl) ⟨781143, by rfl⟩ : syracuseStep 2083049 = 1562287) B1562287
theorem B3131945 : Blo 924580 3131945 := bstep (se 2 (by rfl) ⟨1174479, by rfl⟩ : syracuseStep 3131945 = 2348959) B2348959
theorem B3951499 : Blo 924580 3951499 := bstep (se 1 (by rfl) ⟨2963624, by rfl⟩ : syracuseStep 3951499 = 5927249) B5927249
theorem B8899793 : Blo 924580 8899793 := bstep (se 2 (by rfl) ⟨3337422, by rfl⟩ : syracuseStep 8899793 = 6674845) B6674845
theorem B4017401 : Blo 924580 4017401 := bstep (se 2 (by rfl) ⟨1506525, by rfl⟩ : syracuseStep 4017401 = 3013051) B3013051
theorem B3132701 : Blo 924580 3132701 := bstep (se 3 (by rfl) ⟨587381, by rfl⟩ : syracuseStep 3132701 = 1174763) B1174763
theorem B2084705 : Blo 924580 2084705 := bstep (se 2 (by rfl) ⟨781764, by rfl⟩ : syracuseStep 2084705 = 1563529) B1563529
theorem B10145675 : Blo 924580 10145675 := bstep (se 1 (by rfl) ⟨7609256, by rfl⟩ : syracuseStep 10145675 = 15218513) B15218513
theorem B1560647 : Blo 924580 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B1560667 : Blo 924580 1560667 := bstep (se 1 (by rfl) ⟨1170500, by rfl⟩ : syracuseStep 1560667 = 2341001) B2341001
theorem B1561079 : Blo 924580 1561079 := bstep (se 1 (by rfl) ⟨1170809, by rfl⟩ : syracuseStep 1561079 = 2341619) B2341619
theorem B3133943 : Blo 924580 3133943 := bstep (se 1 (by rfl) ⟨2350457, by rfl⟩ : syracuseStep 3133943 = 4700915) B4700915
theorem B1757801 : Blo 924580 1757801 := bstep (se 2 (by rfl) ⟨659175, by rfl⟩ : syracuseStep 1757801 = 1318351) B1318351
theorem B8016509 : Blo 924580 8016509 := bstep (se 3 (by rfl) ⟨1503095, by rfl⟩ : syracuseStep 8016509 = 3006191) B3006191
theorem B19026899 : Blo 924580 19026899 := bstep (se 1 (by rfl) ⟨14270174, by rfl⟩ : syracuseStep 19026899 = 28540349) B28540349
theorem B11883611 : Blo 924580 11883611 := bstep (se 1 (by rfl) ⟨8912708, by rfl⟩ : syracuseStep 11883611 = 17825417) B17825417
theorem B3757195 : Blo 924580 3757195 := bstep (se 1 (by rfl) ⟨2817896, by rfl⟩ : syracuseStep 3757195 = 5635793) B5635793
theorem B2381051 : Blo 924580 2381051 := bstep (se 1 (by rfl) ⟨1785788, by rfl⟩ : syracuseStep 2381051 = 3571577) B3571577
theorem B8443547 : Blo 924580 8443547 := bstep (se 1 (by rfl) ⟨6332660, by rfl⟩ : syracuseStep 8443547 = 12665321) B12665321
theorem B3954575 : Blo 924580 3954575 := bstep (se 1 (by rfl) ⟨2965931, by rfl⟩ : syracuseStep 3954575 = 5931863) B5931863
theorem B2414623 : Blo 924580 2414623 := bstep (se 1 (by rfl) ⟨1810967, by rfl⟩ : syracuseStep 2414623 = 3621935) B3621935
theorem B8902867 : Blo 924580 8902867 := bstep (se 1 (by rfl) ⟨6677150, by rfl⟩ : syracuseStep 8902867 = 13354301) B13354301
theorem B10541339 : Blo 924580 10541339 := bstep (se 1 (by rfl) ⟨7906004, by rfl⟩ : syracuseStep 10541339 = 15812009) B15812009
theorem B1562935 : Blo 924580 1562935 := bstep (se 1 (by rfl) ⟨1172201, by rfl⟩ : syracuseStep 1562935 = 2344403) B2344403
theorem B8903141 : Blo 924580 8903141 := bstep (se 4 (by rfl) ⟨834669, by rfl⟩ : syracuseStep 8903141 = 1669339) B1669339
theorem B3955175 : Blo 924580 3955175 := bstep (se 1 (by rfl) ⟨2966381, by rfl⟩ : syracuseStep 3955175 = 5932763) B5932763
theorem B1563455 : Blo 924580 1563455 := bstep (se 1 (by rfl) ⟨1172591, by rfl⟩ : syracuseStep 1563455 = 2345183) B2345183
theorem B2087783 : Blo 924580 2087783 := bstep (se 1 (by rfl) ⟨1565837, by rfl⟩ : syracuseStep 2087783 = 3131675) B3131675
theorem B5266457 : Blo 924580 5266457 := bstep (se 2 (by rfl) ⟨1974921, by rfl⟩ : syracuseStep 5266457 = 3949843) B3949843
theorem B9624683 : Blo 924580 9624683 := bstep (se 1 (by rfl) ⟨7218512, by rfl⟩ : syracuseStep 9624683 = 14437025) B14437025
theorem B1170607 : Blo 924580 1170607 := bstep (se 1 (by rfl) ⟨877955, by rfl⟩ : syracuseStep 1170607 = 1755911) B1755911
theorem B2350255 : Blo 924580 2350255 := bstep (se 1 (by rfl) ⟨1762691, by rfl⟩ : syracuseStep 2350255 = 3525383) B3525383
theorem B1761659 : Blo 924580 1761659 := bstep (se 1 (by rfl) ⟨1321244, by rfl⟩ : syracuseStep 1761659 = 2642489) B2642489
theorem B1171999 : Blo 924580 1171999 := bstep (se 1 (by rfl) ⟨878999, by rfl⟩ : syracuseStep 1171999 = 1757999) B1757999
theorem B32137829 : Blo 924580 32137829 := bstep (se 4 (by rfl) ⟨3012921, by rfl⟩ : syracuseStep 32137829 = 6025843) B6025843
theorem B22569635 : Blo 924580 22569635 := bstep (se 1 (by rfl) ⟨16927226, by rfl⟩ : syracuseStep 22569635 = 33854453) B33854453
theorem B1565561 : Blo 924580 1565561 := bstep (se 2 (by rfl) ⟨587085, by rfl⟩ : syracuseStep 1565561 = 1174171) B1174171
theorem B2974697 : Blo 924580 2974697 := bstep (se 2 (by rfl) ⟨1115511, by rfl⟩ : syracuseStep 2974697 = 2231023) B2231023
theorem B1762411 : Blo 924580 1762411 := bstep (se 1 (by rfl) ⟨1321808, by rfl⟩ : syracuseStep 1762411 = 2643617) B2643617
theorem B1566857 : Blo 924580 1566857 := bstep (se 2 (by rfl) ⟨587571, by rfl⟩ : syracuseStep 1566857 = 1175143) B1175143
theorem B1042663 : Blo 924580 1042663 := bstep (se 1 (by rfl) ⟨781997, by rfl⟩ : syracuseStep 1042663 = 1563995) B1563995
theorem B3762551 : Blo 924580 3762551 := bstep (se 1 (by rfl) ⟨2821913, by rfl⟩ : syracuseStep 3762551 = 5643827) B5643827
theorem B225733025 : Blo 924580 225733025 := bstep (se 2 (by rfl) ⟨84649884, by rfl⟩ : syracuseStep 225733025 = 169299769) B169299769
theorem B1043311 : Blo 924580 1043311 := bstep (se 1 (by rfl) ⟨782483, by rfl⟩ : syracuseStep 1043311 = 1564967) B1564967
theorem B3960247 : Blo 924580 3960247 := bstep (se 1 (by rfl) ⟨2970185, by rfl⟩ : syracuseStep 3960247 = 5940371) B5940371
theorem B1043995 : Blo 924580 1043995 := bstep (se 1 (by rfl) ⟨782996, by rfl⟩ : syracuseStep 1043995 = 1565993) B1565993
theorem B2223787 : Blo 924580 2223787 := bstep (se 1 (by rfl) ⟨1667840, by rfl⟩ : syracuseStep 2223787 = 3335681) B3335681
theorem B1044175 : Blo 924580 1044175 := bstep (se 1 (by rfl) ⟨783131, by rfl⟩ : syracuseStep 1044175 = 1566263) B1566263
theorem B3960863 : Blo 924580 3960863 := bstep (se 1 (by rfl) ⟨2970647, by rfl⟩ : syracuseStep 3960863 = 5941295) B5941295
theorem B11269057 : Blo 924580 11269057 := bstep (se 2 (by rfl) ⟨4225896, by rfl⟩ : syracuseStep 11269057 = 8451793) B8451793
theorem B7501223 : Blo 924580 7501223 := bstep (se 1 (by rfl) ⟨5625917, by rfl⟩ : syracuseStep 7501223 = 11251835) B11251835
theorem B1112167 : Blo 924580 1112167 := bstep (se 1 (by rfl) ⟨834125, by rfl⟩ : syracuseStep 1112167 = 1668251) B1668251
theorem B15825131 : Blo 924580 15825131 := bstep (se 1 (by rfl) ⟨11868848, by rfl⟩ : syracuseStep 15825131 = 23737697) B23737697
theorem B3963239 : Blo 924580 3963239 := bstep (se 1 (by rfl) ⟨2972429, by rfl⟩ : syracuseStep 3963239 = 5944859) B5944859
theorem B3963563 : Blo 924580 3963563 := bstep (se 1 (by rfl) ⟨2972672, by rfl⟩ : syracuseStep 3963563 = 5945345) B5945345
theorem B4750273 : Blo 924580 4750273 := bstep (se 2 (by rfl) ⟨1781352, by rfl⟩ : syracuseStep 4750273 = 3562705) B3562705
theorem B2227247 : Blo 924580 2227247 := bstep (se 1 (by rfl) ⟨1670435, by rfl⟩ : syracuseStep 2227247 = 3340871) B3340871
theorem B1408559 : Blo 924580 1408559 := bstep (se 1 (by rfl) ⟨1056419, by rfl⟩ : syracuseStep 1408559 = 2112839) B2112839
theorem B3571975 : Blo 924580 3571975 := bstep (se 1 (by rfl) ⟨2678981, by rfl⟩ : syracuseStep 3571975 = 5357963) B5357963
theorem B3342671 : Blo 924580 3342671 := bstep (se 1 (by rfl) ⟨2507003, by rfl⟩ : syracuseStep 3342671 = 5014007) B5014007
theorem B22512431 : Blo 924580 22512431 := bstep (se 1 (by rfl) ⟨16884323, by rfl⟩ : syracuseStep 22512431 = 33768647) B33768647
theorem B1672417 : Blo 924580 1672417 := bstep (se 2 (by rfl) ⟨627156, by rfl⟩ : syracuseStep 1672417 = 1254313) B1254313
theorem B10585673 : Blo 924580 10585673 := bstep (se 2 (by rfl) ⟨3969627, by rfl⟩ : syracuseStep 10585673 = 7939255) B7939255
theorem B4687469 : Blo 924580 4687469 := bstep (se 3 (by rfl) ⟨878900, by rfl⟩ : syracuseStep 4687469 = 1757801) B1757801
theorem B80480087 : Blo 924580 80480087 := bstep (se 1 (by rfl) ⟨60360065, by rfl⟩ : syracuseStep 80480087 = 120720131) B120720131
theorem B5933195 : Blo 924580 5933195 := bstep (se 1 (by rfl) ⟨4449896, by rfl⟩ : syracuseStep 5933195 = 8899793) B8899793
theorem B4458815 : Blo 924580 4458815 := bstep (se 1 (by rfl) ⟨3344111, by rfl⟩ : syracuseStep 4458815 = 6688223) B6688223
theorem B9505147 : Blo 924580 9505147 := bstep (se 1 (by rfl) ⟨7128860, by rfl⟩ : syracuseStep 9505147 = 14257721) B14257721
theorem B2230735 : Blo 924580 2230735 := bstep (se 1 (by rfl) ⟨1673051, by rfl⟩ : syracuseStep 2230735 = 3346103) B3346103
theorem B12684599 : Blo 924580 12684599 := bstep (se 1 (by rfl) ⟨9513449, by rfl⟩ : syracuseStep 12684599 = 19026899) B19026899
theorem B3476807 : Blo 924580 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B5935427 : Blo 924580 5935427 := bstep (se 1 (by rfl) ⟨4451570, by rfl⟩ : syracuseStep 5935427 = 8903141) B8903141
theorem B10555919 : Blo 924580 10555919 := bstep (se 1 (by rfl) ⟨7916939, by rfl⟩ : syracuseStep 10555919 = 15833879) B15833879
theorem B5280329 : Blo 924580 5280329 := bstep (se 2 (by rfl) ⟨1980123, by rfl⟩ : syracuseStep 5280329 = 3960247) B3960247
theorem B3510971 : Blo 924580 3510971 := bstep (se 1 (by rfl) ⟨2633228, by rfl⟩ : syracuseStep 3510971 = 5266457) B5266457
theorem B25334789 : Blo 924580 25334789 := bstep (se 4 (by rfl) ⟨2375136, by rfl⟩ : syracuseStep 25334789 = 4750273) B4750273
theorem B7050401 : Blo 924580 7050401 := bstep (se 2 (by rfl) ⟨2643900, by rfl⟩ : syracuseStep 7050401 = 5287801) B5287801
theorem B4691681 : Blo 924580 4691681 := bstep (se 2 (by rfl) ⟨1759380, by rfl⟩ : syracuseStep 4691681 = 3518761) B3518761
theorem B601954733 : Blo 924580 601954733 := bstep (se 3 (by rfl) ⟨112866512, by rfl⟩ : syracuseStep 601954733 = 225733025) B225733025
theorem B924655 : Blo 924580 924655 := bstep (se 1 (by rfl) ⟨693491, by rfl⟩ : syracuseStep 924655 = 1386983) B1386983
theorem B6691913 : Blo 924580 6691913 := bstep (se 2 (by rfl) ⟨2509467, by rfl⟩ : syracuseStep 6691913 = 5018935) B5018935
theorem B924775 : Blo 924580 924775 := bstep (se 1 (by rfl) ⟨693581, by rfl⟩ : syracuseStep 924775 = 1387163) B1387163
theorem B1252831 : Blo 924580 1252831 := bstep (se 1 (by rfl) ⟨939623, by rfl⟩ : syracuseStep 1252831 = 1879247) B1879247
theorem B8920705 : Blo 924580 8920705 := bstep (se 2 (by rfl) ⟨3345264, by rfl⟩ : syracuseStep 8920705 = 6690529) B6690529
theorem B925423 : Blo 924580 925423 := bstep (se 1 (by rfl) ⟨694067, by rfl⟩ : syracuseStep 925423 = 1388135) B1388135
theorem B3219497 : Blo 924580 3219497 := bstep (se 2 (by rfl) ⟨1207311, by rfl⟩ : syracuseStep 3219497 = 2414623) B2414623
theorem B925787 : Blo 924580 925787 := bstep (se 1 (by rfl) ⟨694340, by rfl⟩ : syracuseStep 925787 = 1388681) B1388681
theorem B1482889 : Blo 924580 1482889 := bstep (se 2 (by rfl) ⟨556083, by rfl⟩ : syracuseStep 1482889 = 1112167) B1112167
theorem B11870489 : Blo 924580 11870489 := bstep (se 2 (by rfl) ⟨4451433, by rfl⟩ : syracuseStep 11870489 = 8902867) B8902867
theorem B25665821 : Blo 924580 25665821 := bstep (se 3 (by rfl) ⟨4812341, by rfl⟩ : syracuseStep 25665821 = 9624683) B9624683
theorem B926527 : Blo 924580 926527 := bstep (se 1 (by rfl) ⟨694895, by rfl⟩ : syracuseStep 926527 = 1389791) B1389791
theorem B926847 : Blo 924580 926847 := bstep (se 1 (by rfl) ⟨695135, by rfl⟩ : syracuseStep 926847 = 1390271) B1390271
theorem B927039 : Blo 924580 927039 := bstep (se 1 (by rfl) ⟨695279, by rfl⟩ : syracuseStep 927039 = 1390559) B1390559
theorem B927079 : Blo 924580 927079 := bstep (se 1 (by rfl) ⟨695309, by rfl⟩ : syracuseStep 927079 = 1390619) B1390619
theorem B927199 : Blo 924580 927199 := bstep (se 1 (by rfl) ⟨695399, by rfl⟩ : syracuseStep 927199 = 1390799) B1390799
theorem B927207 : Blo 924580 927207 := bstep (se 1 (by rfl) ⟨695405, by rfl⟩ : syracuseStep 927207 = 1390811) B1390811
theorem B927335 : Blo 924580 927335 := bstep (se 1 (by rfl) ⟨695501, by rfl⟩ : syracuseStep 927335 = 1391003) B1391003
theorem B927615 : Blo 924580 927615 := bstep (se 1 (by rfl) ⟨695711, by rfl⟩ : syracuseStep 927615 = 1391423) B1391423
theorem B927647 : Blo 924580 927647 := bstep (se 1 (by rfl) ⟨695735, by rfl⟩ : syracuseStep 927647 = 1391471) B1391471
theorem B1484831 : Blo 924580 1484831 := bstep (se 1 (by rfl) ⟨1113623, by rfl⟩ : syracuseStep 1484831 = 2227247) B2227247
theorem B927807 : Blo 924580 927807 := bstep (se 1 (by rfl) ⟨695855, by rfl⟩ : syracuseStep 927807 = 1391711) B1391711
theorem B927847 : Blo 924580 927847 := bstep (se 1 (by rfl) ⟨695885, by rfl⟩ : syracuseStep 927847 = 1391771) B1391771
theorem B2500895 : Blo 924580 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B5646793 : Blo 924580 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B1386959 : Blo 924580 1386959 := bstep (se 1 (by rfl) ⟨1040219, by rfl⟩ : syracuseStep 1386959 = 2080439) B2080439
theorem B1387247 : Blo 924580 1387247 := bstep (se 1 (by rfl) ⟨1040435, by rfl⟩ : syracuseStep 1387247 = 2080871) B2080871
theorem B1387847 : Blo 924580 1387847 := bstep (se 1 (by rfl) ⟨1040885, by rfl⟩ : syracuseStep 1387847 = 2081771) B2081771
theorem B2108897 : Blo 924580 2108897 := bstep (se 2 (by rfl) ⟨790836, by rfl⟩ : syracuseStep 2108897 = 1581673) B1581673
theorem B30060557 : Blo 924580 30060557 := bstep (se 3 (by rfl) ⟨5636354, by rfl⟩ : syracuseStep 30060557 = 11272709) B11272709
theorem B1388699 : Blo 924580 1388699 := bstep (se 1 (by rfl) ⟨1041524, by rfl⟩ : syracuseStep 1388699 = 2083049) B2083049
theorem B21377357 : Blo 924580 21377357 := bstep (se 3 (by rfl) ⟨4008254, by rfl⟩ : syracuseStep 21377357 = 8016509) B8016509
theorem B1389803 : Blo 924580 1389803 := bstep (se 1 (by rfl) ⟨1042352, by rfl⟩ : syracuseStep 1389803 = 2084705) B2084705
theorem B10139053 : Blo 924580 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B1390217 : Blo 924580 1390217 := bstep (se 2 (by rfl) ⟨521331, by rfl⟩ : syracuseStep 1390217 = 1042663) B1042663
theorem B2340859 : Blo 924580 2340859 := bstep (se 1 (by rfl) ⟨1755644, by rfl⟩ : syracuseStep 2340859 = 3511289) B3511289
theorem B1587367 : Blo 924580 1587367 := bstep (se 1 (by rfl) ⟨1190525, by rfl⟩ : syracuseStep 1587367 = 2381051) B2381051
theorem B2341183 : Blo 924580 2341183 := bstep (se 1 (by rfl) ⟨1755887, by rfl⟩ : syracuseStep 2341183 = 3511775) B3511775
theorem B1391081 : Blo 924580 1391081 := bstep (se 2 (by rfl) ⟨521655, by rfl⟩ : syracuseStep 1391081 = 1043311) B1043311
theorem B2636383 : Blo 924580 2636383 := bstep (se 1 (by rfl) ⟨1977287, by rfl⟩ : syracuseStep 2636383 = 3954575) B3954575
theorem B7027559 : Blo 924580 7027559 := bstep (se 1 (by rfl) ⟨5270669, by rfl⟩ : syracuseStep 7027559 = 10541339) B10541339
theorem B2636783 : Blo 924580 2636783 := bstep (se 1 (by rfl) ⟨1977587, by rfl⟩ : syracuseStep 2636783 = 3955175) B3955175
theorem B1391855 : Blo 924580 1391855 := bstep (se 1 (by rfl) ⟨1043891, by rfl⟩ : syracuseStep 1391855 = 2087783) B2087783
theorem B1391993 : Blo 924580 1391993 := bstep (se 2 (by rfl) ⟨521997, by rfl⟩ : syracuseStep 1391993 = 1043995) B1043995
theorem B2965049 : Blo 924580 2965049 := bstep (se 2 (by rfl) ⟨1111893, by rfl⟩ : syracuseStep 2965049 = 2223787) B2223787
theorem B1392233 : Blo 924580 1392233 := bstep (se 2 (by rfl) ⟨522087, by rfl⟩ : syracuseStep 1392233 = 1044175) B1044175
theorem B10010537 : Blo 924580 10010537 := bstep (se 2 (by rfl) ⟨3753951, by rfl⟩ : syracuseStep 10010537 = 7507903) B7507903
theorem B2080889 : Blo 924580 2080889 := bstep (se 2 (by rfl) ⟨780333, by rfl⟩ : syracuseStep 2080889 = 1560667) B1560667
theorem B2080943 : Blo 924580 2080943 := bstep (se 1 (by rfl) ⟨1560707, by rfl⟩ : syracuseStep 2080943 = 3121415) B3121415
theorem B15024629 : Blo 924580 15024629 := bstep (se 5 (by rfl) ⟨704279, by rfl⟩ : syracuseStep 15024629 = 1408559) B1408559
theorem B1983131 : Blo 924580 1983131 := bstep (se 1 (by rfl) ⟨1487348, by rfl⟩ : syracuseStep 1983131 = 2974697) B2974697
theorem B20038373 : Blo 924580 20038373 := bstep (se 4 (by rfl) ⟨1878597, by rfl⟩ : syracuseStep 20038373 = 3757195) B3757195
theorem B2081663 : Blo 924580 2081663 := bstep (se 1 (by rfl) ⟨1561247, by rfl⟩ : syracuseStep 2081663 = 3122495) B3122495
theorem B3130271 : Blo 924580 3130271 := bstep (se 1 (by rfl) ⟨2347703, by rfl⟩ : syracuseStep 3130271 = 4695407) B4695407
theorem B2343887 : Blo 924580 2343887 := bstep (se 1 (by rfl) ⟨1757915, by rfl⟩ : syracuseStep 2343887 = 3515831) B3515831
theorem B2082023 : Blo 924580 2082023 := bstep (se 1 (by rfl) ⟨1561517, by rfl⟩ : syracuseStep 2082023 = 3123035) B3123035
theorem B15025409 : Blo 924580 15025409 := bstep (se 2 (by rfl) ⟨5634528, by rfl⟩ : syracuseStep 15025409 = 11269057) B11269057
theorem B2344423 : Blo 924580 2344423 := bstep (se 1 (by rfl) ⟨1758317, by rfl⟩ : syracuseStep 2344423 = 3516635) B3516635
theorem B2508367 : Blo 924580 2508367 := bstep (se 1 (by rfl) ⟨1881275, by rfl⟩ : syracuseStep 2508367 = 3762551) B3762551
theorem B2082671 : Blo 924580 2082671 := bstep (se 1 (by rfl) ⟨1562003, by rfl⟩ : syracuseStep 2082671 = 3124007) B3124007
theorem B2082779 : Blo 924580 2082779 := bstep (se 1 (by rfl) ⟨1562084, by rfl⟩ : syracuseStep 2082779 = 3124169) B3124169
theorem B2082887 : Blo 924580 2082887 := bstep (se 1 (by rfl) ⟨1562165, by rfl⟩ : syracuseStep 2082887 = 3124331) B3124331
theorem B2345051 : Blo 924580 2345051 := bstep (se 1 (by rfl) ⟨1758788, by rfl⟩ : syracuseStep 2345051 = 3517577) B3517577
theorem B2640575 : Blo 924580 2640575 := bstep (se 1 (by rfl) ⟨1980431, by rfl⟩ : syracuseStep 2640575 = 3960863) B3960863
theorem B2083913 : Blo 924580 2083913 := bstep (se 2 (by rfl) ⟨781467, by rfl⟩ : syracuseStep 2083913 = 1562935) B1562935
theorem B3951773 : Blo 924580 3951773 := bstep (se 3 (by rfl) ⟨740957, by rfl⟩ : syracuseStep 3951773 = 1481915) B1481915
theorem B2346367 : Blo 924580 2346367 := bstep (se 1 (by rfl) ⟨1759775, by rfl⟩ : syracuseStep 2346367 = 3519551) B3519551
theorem B5000815 : Blo 924580 5000815 := bstep (se 1 (by rfl) ⟨3750611, by rfl⟩ : syracuseStep 5000815 = 7501223) B7501223
theorem B1560809 : Blo 924580 1560809 := bstep (se 2 (by rfl) ⟨585303, by rfl⟩ : syracuseStep 1560809 = 1170607) B1170607
theorem B3133673 : Blo 924580 3133673 := bstep (se 2 (by rfl) ⟨1175127, by rfl⟩ : syracuseStep 3133673 = 2350255) B2350255
theorem B2642159 : Blo 924580 2642159 := bstep (se 1 (by rfl) ⟨1981619, by rfl⟩ : syracuseStep 2642159 = 3963239) B3963239
theorem B2642375 : Blo 924580 2642375 := bstep (se 1 (by rfl) ⟨1981781, by rfl⟩ : syracuseStep 2642375 = 3963563) B3963563
theorem B2347987 : Blo 924580 2347987 := bstep (se 1 (by rfl) ⟨1760990, by rfl⟩ : syracuseStep 2347987 = 3521981) B3521981
theorem B27055133 : Blo 924580 27055133 := bstep (se 3 (by rfl) ⟨5072837, by rfl⟩ : syracuseStep 27055133 = 10145675) B10145675
theorem B2086271 : Blo 924580 2086271 := bstep (se 1 (by rfl) ⟨1564703, by rfl⟩ : syracuseStep 2086271 = 3129407) B3129407
theorem B1759259 : Blo 924580 1759259 := bstep (se 1 (by rfl) ⟨1319444, by rfl⟩ : syracuseStep 1759259 = 2638889) B2638889
theorem B1562665 : Blo 924580 1562665 := bstep (se 2 (by rfl) ⟨585999, by rfl⟩ : syracuseStep 1562665 = 1171999) B1171999
theorem B5003369 : Blo 924580 5003369 := bstep (se 2 (by rfl) ⟨1876263, by rfl⟩ : syracuseStep 5003369 = 3752527) B3752527
theorem B3954815 : Blo 924580 3954815 := bstep (se 1 (by rfl) ⟨2966111, by rfl⟩ : syracuseStep 3954815 = 5932223) B5932223
theorem B1562807 : Blo 924580 1562807 := bstep (se 1 (by rfl) ⟨1172105, by rfl⟩ : syracuseStep 1562807 = 2344211) B2344211
theorem B7035335 : Blo 924580 7035335 := bstep (se 1 (by rfl) ⟨5276501, by rfl⟩ : syracuseStep 7035335 = 10553003) B10553003
theorem B2349881 : Blo 924580 2349881 := bstep (se 2 (by rfl) ⟨881205, by rfl⟩ : syracuseStep 2349881 = 1762411) B1762411
theorem B1072123 : Blo 924580 1072123 := bstep (se 1 (by rfl) ⟨804092, by rfl⟩ : syracuseStep 1072123 = 1608185) B1608185
theorem B2087963 : Blo 924580 2087963 := bstep (se 1 (by rfl) ⟨1565972, by rfl⟩ : syracuseStep 2087963 = 3131945) B3131945
theorem B60185693 : Blo 924580 60185693 := bstep (se 3 (by rfl) ⟨11284817, by rfl⟩ : syracuseStep 60185693 = 22569635) B22569635
theorem B2678267 : Blo 924580 2678267 := bstep (se 1 (by rfl) ⟨2008700, by rfl⟩ : syracuseStep 2678267 = 4017401) B4017401
theorem B2088467 : Blo 924580 2088467 := bstep (se 1 (by rfl) ⟨1566350, by rfl⟩ : syracuseStep 2088467 = 3132701) B3132701
theorem B60218909 : Blo 924580 60218909 := bstep (se 3 (by rfl) ⟨11291045, by rfl⟩ : syracuseStep 60218909 = 22582091) B22582091
theorem B6774329 : Blo 924580 6774329 := bstep (se 2 (by rfl) ⟨2540373, by rfl⟩ : syracuseStep 6774329 = 5080747) B5080747
theorem B8019695 : Blo 924580 8019695 := bstep (se 1 (by rfl) ⟨6014771, by rfl⟩ : syracuseStep 8019695 = 12029543) B12029543
theorem B1040431 : Blo 924580 1040431 := bstep (se 1 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 1040431 = 1560647) B1560647
theorem B1040719 : Blo 924580 1040719 := bstep (se 1 (by rfl) ⟨780539, by rfl⟩ : syracuseStep 1040719 = 1561079) B1561079
theorem B2089295 : Blo 924580 2089295 := bstep (se 1 (by rfl) ⟨1566971, by rfl⟩ : syracuseStep 2089295 = 3133943) B3133943
theorem B10576331 : Blo 924580 10576331 := bstep (se 1 (by rfl) ⟨7932248, by rfl⟩ : syracuseStep 10576331 = 15864497) B15864497
theorem B7922407 : Blo 924580 7922407 := bstep (se 1 (by rfl) ⟨5941805, by rfl⟩ : syracuseStep 7922407 = 11883611) B11883611
theorem B5629031 : Blo 924580 5629031 := bstep (se 1 (by rfl) ⟨4221773, by rfl⟩ : syracuseStep 5629031 = 8443547) B8443547
theorem B5268665 : Blo 924580 5268665 := bstep (se 2 (by rfl) ⟨1975749, by rfl⟩ : syracuseStep 5268665 = 3951499) B3951499
theorem B14280013 : Blo 924580 14280013 := bstep (se 3 (by rfl) ⟨2677502, by rfl⟩ : syracuseStep 14280013 = 5355005) B5355005
theorem B1042303 : Blo 924580 1042303 := bstep (se 1 (by rfl) ⟨781727, by rfl⟩ : syracuseStep 1042303 = 1563455) B1563455
theorem B3566063 : Blo 924580 3566063 := bstep (se 1 (by rfl) ⟨2674547, by rfl⟩ : syracuseStep 3566063 = 5349095) B5349095
theorem B10545713 : Blo 924580 10545713 := bstep (se 2 (by rfl) ⟨3954642, by rfl⟩ : syracuseStep 10545713 = 7909285) B7909285
theorem B1174439 : Blo 924580 1174439 := bstep (se 1 (by rfl) ⟨880829, by rfl⟩ : syracuseStep 1174439 = 1761659) B1761659
theorem B21425219 : Blo 924580 21425219 := bstep (se 1 (by rfl) ⟨16068914, by rfl⟩ : syracuseStep 21425219 = 32137829) B32137829
theorem B1043707 : Blo 924580 1043707 := bstep (se 1 (by rfl) ⟨782780, by rfl⟩ : syracuseStep 1043707 = 1565561) B1565561
theorem B4681799 : Blo 924580 4681799 := bstep (se 1 (by rfl) ⟨3511349, by rfl⟩ : syracuseStep 4681799 = 7022699) B7022699
theorem B1044571 : Blo 924580 1044571 := bstep (se 1 (by rfl) ⟨783428, by rfl⟩ : syracuseStep 1044571 = 1566857) B1566857
theorem B17789057 : Blo 924580 17789057 := bstep (se 2 (by rfl) ⟨6670896, by rfl⟩ : syracuseStep 17789057 = 13341793) B13341793
theorem B1669513 : Blo 924580 1669513 := bstep (se 2 (by rfl) ⟨626067, by rfl⟩ : syracuseStep 1669513 = 1252135) B1252135
theorem B5339627 : Blo 924580 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B4684391 : Blo 924580 4684391 := bstep (se 1 (by rfl) ⟨3513293, by rfl⟩ : syracuseStep 4684391 = 7026587) B7026587
theorem B10550087 : Blo 924580 10550087 := bstep (se 1 (by rfl) ⟨7912565, by rfl⟩ : syracuseStep 10550087 = 15825131) B15825131
theorem B5078695 : Blo 924580 5078695 := bstep (se 1 (by rfl) ⟨3809021, by rfl⟩ : syracuseStep 5078695 = 7618043) B7618043
theorem B3964895 : Blo 924580 3964895 := bstep (se 1 (by rfl) ⟨2973671, by rfl⟩ : syracuseStep 3964895 = 5947343) B5947343
theorem B2228447 : Blo 924580 2228447 := bstep (se 1 (by rfl) ⟨1671335, by rfl⟩ : syracuseStep 2228447 = 3342671) B3342671
theorem B15008287 : Blo 924580 15008287 := bstep (se 1 (by rfl) ⟨11256215, by rfl⟩ : syracuseStep 15008287 = 22512431) B22512431
theorem B19040017 : Blo 924580 19040017 := bstep (se 2 (by rfl) ⟨7140006, by rfl⟩ : syracuseStep 19040017 = 14280013) B14280013
theorem B3344489 : Blo 924580 3344489 := bstep (se 2 (by rfl) ⟨1254183, by rfl⟩ : syracuseStep 3344489 = 2508367) B2508367
theorem B8456399 : Blo 924580 8456399 := bstep (se 1 (by rfl) ⟨6342299, by rfl⟩ : syracuseStep 8456399 = 12684599) B12684599
theorem B4690223 : Blo 924580 4690223 := bstep (se 1 (by rfl) ⟨3517667, by rfl⟩ : syracuseStep 4690223 = 7035335) B7035335
theorem B4461275 : Blo 924580 4461275 := bstep (se 1 (by rfl) ⟨3345956, by rfl⟩ : syracuseStep 4461275 = 6691913) B6691913
theorem B40145939 : Blo 924580 40145939 := bstep (se 1 (by rfl) ⟨30109454, by rfl⟩ : syracuseStep 40145939 = 60218909) B60218909
theorem B4691357 : Blo 924580 4691357 := bstep (se 3 (by rfl) ⟨879629, by rfl⟩ : syracuseStep 4691357 = 1759259) B1759259
theorem B17110547 : Blo 924580 17110547 := bstep (se 1 (by rfl) ⟨12832910, by rfl⟩ : syracuseStep 17110547 = 25665821) B25665821
theorem B7050887 : Blo 924580 7050887 := bstep (se 1 (by rfl) ⟨5288165, by rfl⟩ : syracuseStep 7050887 = 10576331) B10576331
theorem B3512443 : Blo 924580 3512443 := bstep (se 1 (by rfl) ⟨2634332, by rfl⟩ : syracuseStep 3512443 = 5268665) B5268665
theorem B8919557 : Blo 924580 8919557 := bstep (se 4 (by rfl) ⟨836208, by rfl⟩ : syracuseStep 8919557 = 1672417) B1672417
theorem B9509501 : Blo 924580 9509501 := bstep (se 3 (by rfl) ⟨1783031, by rfl⟩ : syracuseStep 9509501 = 3566063) B3566063
theorem B924639 : Blo 924580 924639 := bstep (se 1 (by rfl) ⟨693479, by rfl⟩ : syracuseStep 924639 = 1386959) B1386959
theorem B924831 : Blo 924580 924831 := bstep (se 1 (by rfl) ⟨693623, by rfl⟩ : syracuseStep 924831 = 1387247) B1387247
theorem B925231 : Blo 924580 925231 := bstep (se 1 (by rfl) ⟨693923, by rfl⟩ : syracuseStep 925231 = 1387847) B1387847
theorem B3121145 : Blo 924580 3121145 := bstep (se 2 (by rfl) ⟨1170429, by rfl⟩ : syracuseStep 3121145 = 2340859) B2340859
theorem B3121199 : Blo 924580 3121199 := bstep (se 1 (by rfl) ⟨2340899, by rfl⟩ : syracuseStep 3121199 = 4681799) B4681799
theorem B925799 : Blo 924580 925799 := bstep (se 1 (by rfl) ⟨694349, by rfl⟩ : syracuseStep 925799 = 1388699) B1388699
theorem B3121577 : Blo 924580 3121577 := bstep (se 2 (by rfl) ⟨1170591, by rfl⟩ : syracuseStep 3121577 = 2341183) B2341183
theorem B3515177 : Blo 924580 3515177 := bstep (se 2 (by rfl) ⟨1318191, by rfl⟩ : syracuseStep 3515177 = 2636383) B2636383
theorem B926535 : Blo 924580 926535 := bstep (se 1 (by rfl) ⟨694901, by rfl⟩ : syracuseStep 926535 = 1389803) B1389803
theorem B926811 : Blo 924580 926811 := bstep (se 1 (by rfl) ⟨695108, by rfl⟩ : syracuseStep 926811 = 1390217) B1390217
theorem B927387 : Blo 924580 927387 := bstep (se 1 (by rfl) ⟨695540, by rfl⟩ : syracuseStep 927387 = 1391081) B1391081
theorem B3122927 : Blo 924580 3122927 := bstep (se 1 (by rfl) ⟨2342195, by rfl⟩ : syracuseStep 3122927 = 4684391) B4684391
theorem B927903 : Blo 924580 927903 := bstep (se 1 (by rfl) ⟨695927, by rfl⟩ : syracuseStep 927903 = 1391855) B1391855
theorem B927995 : Blo 924580 927995 := bstep (se 1 (by rfl) ⟨695996, by rfl⟩ : syracuseStep 927995 = 1391993) B1391993
theorem B1976699 : Blo 924580 1976699 := bstep (se 1 (by rfl) ⟨1482524, by rfl⟩ : syracuseStep 1976699 = 2965049) B2965049
theorem B928155 : Blo 924580 928155 := bstep (se 1 (by rfl) ⟨696116, by rfl⟩ : syracuseStep 928155 = 1392233) B1392233
theorem B1387241 : Blo 924580 1387241 := bstep (se 2 (by rfl) ⟨520215, by rfl⟩ : syracuseStep 1387241 = 1040431) B1040431
theorem B1387259 : Blo 924580 1387259 := bstep (se 1 (by rfl) ⟨1040444, by rfl⟩ : syracuseStep 1387259 = 2080889) B2080889
theorem B1387295 : Blo 924580 1387295 := bstep (se 1 (by rfl) ⟨1040471, by rfl⟩ : syracuseStep 1387295 = 2080943) B2080943
theorem B1977185 : Blo 924580 1977185 := bstep (se 2 (by rfl) ⟨741444, by rfl⟩ : syracuseStep 1977185 = 1482889) B1482889
theorem B4762633 : Blo 924580 4762633 := bstep (se 2 (by rfl) ⟨1785987, by rfl⟩ : syracuseStep 4762633 = 3571975) B3571975
theorem B1322087 : Blo 924580 1322087 := bstep (se 1 (by rfl) ⟨991565, by rfl⟩ : syracuseStep 1322087 = 1983131) B1983131
theorem B1387625 : Blo 924580 1387625 := bstep (se 2 (by rfl) ⟨520359, by rfl⟩ : syracuseStep 1387625 = 1040719) B1040719
theorem B1387775 : Blo 924580 1387775 := bstep (se 1 (by rfl) ⟨1040831, by rfl⟩ : syracuseStep 1387775 = 2081663) B2081663
theorem B1388015 : Blo 924580 1388015 := bstep (se 1 (by rfl) ⟨1041011, by rfl⟩ : syracuseStep 1388015 = 2082023) B2082023
theorem B10563209 : Blo 924580 10563209 := bstep (se 2 (by rfl) ⟨3961203, by rfl⟩ : syracuseStep 10563209 = 7922407) B7922407
theorem B7057115 : Blo 924580 7057115 := bstep (se 1 (by rfl) ⟨5292836, by rfl⟩ : syracuseStep 7057115 = 10585673) B10585673
theorem B3124979 : Blo 924580 3124979 := bstep (se 1 (by rfl) ⟨2343734, by rfl⟩ : syracuseStep 3124979 = 4687469) B4687469
theorem B53653391 : Blo 924580 53653391 := bstep (se 1 (by rfl) ⟨40240043, by rfl⟩ : syracuseStep 53653391 = 80480087) B80480087
theorem B1388447 : Blo 924580 1388447 := bstep (se 1 (by rfl) ⟨1041335, by rfl⟩ : syracuseStep 1388447 = 2082671) B2082671
theorem B1388519 : Blo 924580 1388519 := bstep (se 1 (by rfl) ⟨1041389, by rfl⟩ : syracuseStep 1388519 = 2082779) B2082779
theorem B1388591 : Blo 924580 1388591 := bstep (se 1 (by rfl) ⟨1041443, by rfl⟩ : syracuseStep 1388591 = 2082887) B2082887
theorem B3125897 : Blo 924580 3125897 := bstep (se 2 (by rfl) ⟨1172211, by rfl⟩ : syracuseStep 3125897 = 2344423) B2344423
theorem B1389275 : Blo 924580 1389275 := bstep (se 1 (by rfl) ⟨1041956, by rfl⟩ : syracuseStep 1389275 = 2083913) B2083913
theorem B2634515 : Blo 924580 2634515 := bstep (se 1 (by rfl) ⟨1975886, by rfl⟩ : syracuseStep 2634515 = 3951773) B3951773
theorem B1389737 : Blo 924580 1389737 := bstep (se 2 (by rfl) ⟨521151, by rfl⟩ : syracuseStep 1389737 = 1042303) B1042303
theorem B3520219 : Blo 924580 3520219 := bstep (se 1 (by rfl) ⟨2640164, by rfl⟩ : syracuseStep 3520219 = 5280329) B5280329
theorem B2340647 : Blo 924580 2340647 := bstep (se 1 (by rfl) ⟨1755485, by rfl⟩ : syracuseStep 2340647 = 3510971) B3510971
theorem B18036755 : Blo 924580 18036755 := bstep (se 1 (by rfl) ⟨13527566, by rfl⟩ : syracuseStep 18036755 = 27055133) B27055133
theorem B4700267 : Blo 924580 4700267 := bstep (se 1 (by rfl) ⟨3525200, by rfl⟩ : syracuseStep 4700267 = 7050401) B7050401
theorem B1390847 : Blo 924580 1390847 := bstep (se 1 (by rfl) ⟨1043135, by rfl⟩ : syracuseStep 1390847 = 2086271) B2086271
theorem B3127787 : Blo 924580 3127787 := bstep (se 1 (by rfl) ⟨2345840, by rfl⟩ : syracuseStep 3127787 = 4691681) B4691681
theorem B2636543 : Blo 924580 2636543 := bstep (se 1 (by rfl) ⟨1977407, by rfl⟩ : syracuseStep 2636543 = 3954815) B3954815
theorem B1391609 : Blo 924580 1391609 := bstep (se 2 (by rfl) ⟨521853, by rfl⟩ : syracuseStep 1391609 = 1043707) B1043707
theorem B3128489 : Blo 924580 3128489 := bstep (se 2 (by rfl) ⟨1173183, by rfl⟩ : syracuseStep 3128489 = 2346367) B2346367
theorem B1391975 : Blo 924580 1391975 := bstep (se 1 (by rfl) ⟨1043981, by rfl⟩ : syracuseStep 1391975 = 2087963) B2087963
theorem B40123795 : Blo 924580 40123795 := bstep (se 1 (by rfl) ⟨30092846, by rfl⟩ : syracuseStep 40123795 = 60185693) B60185693
theorem B6667753 : Blo 924580 6667753 := bstep (se 2 (by rfl) ⟨2500407, by rfl⟩ : syracuseStep 6667753 = 5000815) B5000815
theorem B1785511 : Blo 924580 1785511 := bstep (se 1 (by rfl) ⟨1339133, by rfl⟩ : syracuseStep 1785511 = 2678267) B2678267
theorem B1392311 : Blo 924580 1392311 := bstep (se 1 (by rfl) ⟨1044233, by rfl⟩ : syracuseStep 1392311 = 2088467) B2088467
theorem B5717989 : Blo 924580 5717989 := bstep (se 4 (by rfl) ⟨536061, by rfl⟩ : syracuseStep 5717989 = 1072123) B1072123
theorem B2146331 : Blo 924580 2146331 := bstep (se 1 (by rfl) ⟨1609748, by rfl⟩ : syracuseStep 2146331 = 3219497) B3219497
theorem B1392761 : Blo 924580 1392761 := bstep (se 2 (by rfl) ⟨522285, by rfl⟩ : syracuseStep 1392761 = 1044571) B1044571
theorem B7913659 : Blo 924580 7913659 := bstep (se 1 (by rfl) ⟨5935244, by rfl⟩ : syracuseStep 7913659 = 11870489) B11870489
theorem B1392863 : Blo 924580 1392863 := bstep (se 1 (by rfl) ⟨1044647, by rfl⟩ : syracuseStep 1392863 = 2089295) B2089295
theorem B3752687 : Blo 924580 3752687 := bstep (se 1 (by rfl) ⟨2814515, by rfl⟩ : syracuseStep 3752687 = 5629031) B5629031
theorem B6669053 : Blo 924580 6669053 := bstep (se 3 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 6669053 = 2500895) B2500895
theorem B3130649 : Blo 924580 3130649 := bstep (se 2 (by rfl) ⟨1173993, by rfl⟩ : syracuseStep 3130649 = 2347987) B2347987
theorem B7030475 : Blo 924580 7030475 := bstep (se 1 (by rfl) ⟨5272856, by rfl⟩ : syracuseStep 7030475 = 10545713) B10545713
theorem B13518737 : Blo 924580 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B3131837 : Blo 924580 3131837 := bstep (se 3 (by rfl) ⟨587219, by rfl⟩ : syracuseStep 3131837 = 1174439) B1174439
theorem B20040371 : Blo 924580 20040371 := bstep (se 1 (by rfl) ⟨15030278, by rfl⟩ : syracuseStep 20040371 = 30060557) B30060557
theorem B2083553 : Blo 924580 2083553 := bstep (se 2 (by rfl) ⟨781332, by rfl⟩ : syracuseStep 2083553 = 1562665) B1562665
theorem B2116489 : Blo 924580 2116489 := bstep (se 2 (by rfl) ⟨793683, by rfl⟩ : syracuseStep 2116489 = 1587367) B1587367
theorem B3559751 : Blo 924580 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B7033391 : Blo 924580 7033391 := bstep (se 1 (by rfl) ⟨5275043, by rfl⟩ : syracuseStep 7033391 = 10550087) B10550087
theorem B21385853 : Blo 924580 21385853 := bstep (se 3 (by rfl) ⟨4009847, by rfl⟩ : syracuseStep 21385853 = 8019695) B8019695
theorem B1757855 : Blo 924580 1757855 := bstep (se 1 (by rfl) ⟨1318391, by rfl⟩ : syracuseStep 1757855 = 2636783) B2636783
theorem B6771593 : Blo 924580 6771593 := bstep (se 2 (by rfl) ⟨2539347, by rfl⟩ : syracuseStep 6771593 = 5078695) B5078695
theorem B6673691 : Blo 924580 6673691 := bstep (se 1 (by rfl) ⟨5005268, by rfl⟩ : syracuseStep 6673691 = 10010537) B10010537
theorem B2643263 : Blo 924580 2643263 := bstep (se 1 (by rfl) ⟨1982447, by rfl⟩ : syracuseStep 2643263 = 3964895) B3964895
theorem B10016419 : Blo 924580 10016419 := bstep (se 1 (by rfl) ⟨7512314, by rfl⟩ : syracuseStep 10016419 = 15024629) B15024629
theorem B13358915 : Blo 924580 13358915 := bstep (se 1 (by rfl) ⟨10019186, by rfl⟩ : syracuseStep 13358915 = 20038373) B20038373
theorem B2086847 : Blo 924580 2086847 := bstep (se 1 (by rfl) ⟨1565135, by rfl⟩ : syracuseStep 2086847 = 3130271) B3130271
theorem B1562591 : Blo 924580 1562591 := bstep (se 1 (by rfl) ⟨1171943, by rfl⟩ : syracuseStep 1562591 = 2343887) B2343887
theorem B10016939 : Blo 924580 10016939 := bstep (se 1 (by rfl) ⟨7512704, by rfl⟩ : syracuseStep 10016939 = 15025409) B15025409
theorem B1563367 : Blo 924580 1563367 := bstep (se 1 (by rfl) ⟨1172525, by rfl⟩ : syracuseStep 1563367 = 2345051) B2345051
theorem B3955463 : Blo 924580 3955463 := bstep (se 1 (by rfl) ⟨2966597, by rfl⟩ : syracuseStep 3955463 = 5933195) B5933195
theorem B2972543 : Blo 924580 2972543 := bstep (se 1 (by rfl) ⟨2229407, by rfl⟩ : syracuseStep 2972543 = 4458815) B4458815
theorem B1760383 : Blo 924580 1760383 := bstep (se 1 (by rfl) ⟨1320287, by rfl⟩ : syracuseStep 1760383 = 2640575) B2640575
theorem B2317871 : Blo 924580 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B67559437 : Blo 924580 67559437 := bstep (se 3 (by rfl) ⟨12667394, by rfl⟩ : syracuseStep 67559437 = 25334789) B25334789
theorem B1040539 : Blo 924580 1040539 := bstep (se 1 (by rfl) ⟨780404, by rfl⟩ : syracuseStep 1040539 = 1560809) B1560809
theorem B2089115 : Blo 924580 2089115 := bstep (se 1 (by rfl) ⟨1566836, by rfl⟩ : syracuseStep 2089115 = 3133673) B3133673
theorem B1761439 : Blo 924580 1761439 := bstep (se 1 (by rfl) ⟨1321079, by rfl⟩ : syracuseStep 1761439 = 2642159) B2642159
theorem B3956951 : Blo 924580 3956951 := bstep (se 1 (by rfl) ⟨2967713, by rfl⟩ : syracuseStep 3956951 = 5935427) B5935427
theorem B1761583 : Blo 924580 1761583 := bstep (se 1 (by rfl) ⟨1321187, by rfl⟩ : syracuseStep 1761583 = 2642375) B2642375
theorem B7037279 : Blo 924580 7037279 := bstep (se 1 (by rfl) ⟨5277959, by rfl⟩ : syracuseStep 7037279 = 10555919) B10555919
theorem B12673529 : Blo 924580 12673529 := bstep (se 2 (by rfl) ⟨4752573, by rfl⟩ : syracuseStep 12673529 = 9505147) B9505147
theorem B7529057 : Blo 924580 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B2974313 : Blo 924580 2974313 := bstep (se 2 (by rfl) ⟨1115367, by rfl⟩ : syracuseStep 2974313 = 2230735) B2230735
theorem B3335579 : Blo 924580 3335579 := bstep (se 1 (by rfl) ⟨2501684, by rfl⟩ : syracuseStep 3335579 = 5003369) B5003369
theorem B1041871 : Blo 924580 1041871 := bstep (se 1 (by rfl) ⟨781403, by rfl⟩ : syracuseStep 1041871 = 1562807) B1562807
theorem B401303155 : Blo 924580 401303155 := bstep (se 1 (by rfl) ⟨300977366, by rfl⟩ : syracuseStep 401303155 = 601954733) B601954733
theorem B1566587 : Blo 924580 1566587 := bstep (se 1 (by rfl) ⟨1174940, by rfl⟩ : syracuseStep 1566587 = 2349881) B2349881
theorem B4516219 : Blo 924580 4516219 := bstep (se 1 (by rfl) ⟨3387164, by rfl⟩ : syracuseStep 4516219 = 6774329) B6774329
theorem B3959549 : Blo 924580 3959549 := bstep (se 3 (by rfl) ⟨742415, by rfl⟩ : syracuseStep 3959549 = 1484831) B1484831
theorem B14283479 : Blo 924580 14283479 := bstep (se 1 (by rfl) ⟨10712609, by rfl⟩ : syracuseStep 14283479 = 21425219) B21425219
theorem B11859371 : Blo 924580 11859371 := bstep (se 1 (by rfl) ⟨8894528, by rfl⟩ : syracuseStep 11859371 = 17789057) B17789057
theorem B14251571 : Blo 924580 14251571 := bstep (se 1 (by rfl) ⟨10688678, by rfl⟩ : syracuseStep 14251571 = 21377357) B21377357
theorem B2226017 : Blo 924580 2226017 := bstep (se 2 (by rfl) ⟨834756, by rfl⟩ : syracuseStep 2226017 = 1669513) B1669513
theorem B89979605 : Blo 924580 89979605 := bstep (se 7 (by rfl) ⟨1054448, by rfl⟩ : syracuseStep 89979605 = 2108897) B2108897
theorem B4685039 : Blo 924580 4685039 := bstep (se 1 (by rfl) ⟨3513779, by rfl⟩ : syracuseStep 4685039 = 7027559) B7027559
theorem B1670441 : Blo 924580 1670441 := bstep (se 2 (by rfl) ⟨626415, by rfl⟩ : syracuseStep 1670441 = 1252831) B1252831
theorem B11894273 : Blo 924580 11894273 := bstep (se 2 (by rfl) ⟨4460352, by rfl⟩ : syracuseStep 11894273 = 8920705) B8920705
theorem B90079249 : Blo 924580 90079249 := bstep (se 2 (by rfl) ⟨33779718, by rfl⟩ : syracuseStep 90079249 = 67559437) B67559437
theorem B10551545 : Blo 924580 10551545 := bstep (se 2 (by rfl) ⟨3956829, by rfl⟩ : syracuseStep 10551545 = 7913659) B7913659
theorem B4686983 : Blo 924580 4686983 := bstep (se 1 (by rfl) ⟨3515237, by rfl⟩ : syracuseStep 4686983 = 7030475) B7030475
theorem B9012491 : Blo 924580 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B2229659 : Blo 924580 2229659 := bstep (se 1 (by rfl) ⟨1672244, by rfl⟩ : syracuseStep 2229659 = 3344489) B3344489
theorem B5637599 : Blo 924580 5637599 := bstep (se 1 (by rfl) ⟨4228199, by rfl⟩ : syracuseStep 5637599 = 8456399) B8456399
theorem B11896733 : Blo 924580 11896733 := bstep (se 3 (by rfl) ⟨2230637, by rfl⟩ : syracuseStep 11896733 = 4461275) B4461275
theorem B24086501 : Blo 924580 24086501 := bstep (se 4 (by rfl) ⟨2258109, by rfl⟩ : syracuseStep 24086501 = 4516219) B4516219
theorem B535070873 : Blo 924580 535070873 := bstep (se 2 (by rfl) ⟨200651577, by rfl⟩ : syracuseStep 535070873 = 401303155) B401303155
theorem B4688927 : Blo 924580 4688927 := bstep (se 1 (by rfl) ⟨3516695, by rfl⟩ : syracuseStep 4688927 = 7033391) B7033391
theorem B14257235 : Blo 924580 14257235 := bstep (se 1 (by rfl) ⟨10692926, by rfl⟩ : syracuseStep 14257235 = 21385853) B21385853
theorem B17796509 : Blo 924580 17796509 := bstep (se 3 (by rfl) ⟨3336845, by rfl⟩ : syracuseStep 17796509 = 6673691) B6673691
theorem B11407031 : Blo 924580 11407031 := bstep (se 1 (by rfl) ⟨8555273, by rfl⟩ : syracuseStep 11407031 = 17110547) B17110547
theorem B2821985 : Blo 924580 2821985 := bstep (se 2 (by rfl) ⟨1058244, by rfl⟩ : syracuseStep 2821985 = 2116489) B2116489
theorem B1545247 : Blo 924580 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B4691519 : Blo 924580 4691519 := bstep (se 1 (by rfl) ⟨3518639, by rfl⟩ : syracuseStep 4691519 = 7037279) B7037279
theorem B5019371 : Blo 924580 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B1317799 : Blo 924580 1317799 := bstep (se 1 (by rfl) ⟨988349, by rfl⟩ : syracuseStep 1317799 = 1976699) B1976699
theorem B924827 : Blo 924580 924827 := bstep (se 1 (by rfl) ⟨693620, by rfl⟩ : syracuseStep 924827 = 1387241) B1387241
theorem B924839 : Blo 924580 924839 := bstep (se 1 (by rfl) ⟨693629, by rfl⟩ : syracuseStep 924839 = 1387259) B1387259
theorem B924863 : Blo 924580 924863 := bstep (se 1 (by rfl) ⟨693647, by rfl⟩ : syracuseStep 924863 = 1387295) B1387295
theorem B1318123 : Blo 924580 1318123 := bstep (se 1 (by rfl) ⟨988592, by rfl⟩ : syracuseStep 1318123 = 1977185) B1977185
theorem B925083 : Blo 924580 925083 := bstep (se 1 (by rfl) ⟨693812, by rfl⟩ : syracuseStep 925083 = 1387625) B1387625
theorem B925183 : Blo 924580 925183 := bstep (se 1 (by rfl) ⟨693887, by rfl⟩ : syracuseStep 925183 = 1387775) B1387775
theorem B4693625 : Blo 924580 4693625 := bstep (se 2 (by rfl) ⟨1760109, by rfl⟩ : syracuseStep 4693625 = 3520219) B3520219
theorem B925343 : Blo 924580 925343 := bstep (se 1 (by rfl) ⟨694007, by rfl⟩ : syracuseStep 925343 = 1388015) B1388015
theorem B925631 : Blo 924580 925631 := bstep (se 1 (by rfl) ⟨694223, by rfl⟩ : syracuseStep 925631 = 1388447) B1388447
theorem B925679 : Blo 924580 925679 := bstep (se 1 (by rfl) ⟨694259, by rfl⟩ : syracuseStep 925679 = 1388519) B1388519
theorem B925727 : Blo 924580 925727 := bstep (se 1 (by rfl) ⟨694295, by rfl⟩ : syracuseStep 925727 = 1388591) B1388591
theorem B926183 : Blo 924580 926183 := bstep (se 1 (by rfl) ⟨694637, by rfl⟩ : syracuseStep 926183 = 1389275) B1389275
theorem B926491 : Blo 924580 926491 := bstep (se 1 (by rfl) ⟨694868, by rfl⟩ : syracuseStep 926491 = 1389737) B1389737
theorem B7906247 : Blo 924580 7906247 := bstep (se 1 (by rfl) ⟨5929685, by rfl⟩ : syracuseStep 7906247 = 11859371) B11859371
theorem B1484011 : Blo 924580 1484011 := bstep (se 1 (by rfl) ⟨1113008, by rfl⟩ : syracuseStep 1484011 = 2226017) B2226017
theorem B927231 : Blo 924580 927231 := bstep (se 1 (by rfl) ⟨695423, by rfl⟩ : syracuseStep 927231 = 1390847) B1390847
theorem B8890337 : Blo 924580 8890337 := bstep (se 2 (by rfl) ⟨3333876, by rfl⟩ : syracuseStep 8890337 = 6667753) B6667753
theorem B927739 : Blo 924580 927739 := bstep (se 1 (by rfl) ⟨695804, by rfl⟩ : syracuseStep 927739 = 1391609) B1391609
theorem B3123359 : Blo 924580 3123359 := bstep (se 1 (by rfl) ⟨2342519, by rfl⟩ : syracuseStep 3123359 = 4685039) B4685039
theorem B927983 : Blo 924580 927983 := bstep (se 1 (by rfl) ⟨695987, by rfl⟩ : syracuseStep 927983 = 1391975) B1391975
theorem B928207 : Blo 924580 928207 := bstep (se 1 (by rfl) ⟨696155, by rfl⟩ : syracuseStep 928207 = 1392311) B1392311
theorem B928507 : Blo 924580 928507 := bstep (se 1 (by rfl) ⟨696380, by rfl⟩ : syracuseStep 928507 = 1392761) B1392761
theorem B1485631 : Blo 924580 1485631 := bstep (se 1 (by rfl) ⟨1114223, by rfl⟩ : syracuseStep 1485631 = 2228447) B2228447
theorem B928575 : Blo 924580 928575 := bstep (se 1 (by rfl) ⟨696431, by rfl⟩ : syracuseStep 928575 = 1392863) B1392863
theorem B1387385 : Blo 924580 1387385 := bstep (se 2 (by rfl) ⟨520269, by rfl⟩ : syracuseStep 1387385 = 1040539) B1040539
theorem B1389035 : Blo 924580 1389035 := bstep (se 1 (by rfl) ⟨1041776, by rfl⟩ : syracuseStep 1389035 = 2083553) B2083553
theorem B1389161 : Blo 924580 1389161 := bstep (se 2 (by rfl) ⟨520935, by rfl⟩ : syracuseStep 1389161 = 1041871) B1041871
theorem B10007165 : Blo 924580 10007165 := bstep (se 3 (by rfl) ⟨1876343, by rfl⟩ : syracuseStep 10007165 = 3752687) B3752687
theorem B3126815 : Blo 924580 3126815 := bstep (se 1 (by rfl) ⟨2345111, by rfl⟩ : syracuseStep 3126815 = 4690223) B4690223
theorem B2373167 : Blo 924580 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B3127571 : Blo 924580 3127571 := bstep (se 1 (by rfl) ⟨2345678, by rfl⟩ : syracuseStep 3127571 = 4691357) B4691357
theorem B4700591 : Blo 924580 4700591 := bstep (se 1 (by rfl) ⟨3525443, by rfl⟩ : syracuseStep 4700591 = 7050887) B7050887
theorem B1391231 : Blo 924580 1391231 := bstep (se 1 (by rfl) ⟨1043423, by rfl⟩ : syracuseStep 1391231 = 2086847) B2086847
theorem B5946371 : Blo 924580 5946371 := bstep (se 1 (by rfl) ⟨4459778, by rfl⟩ : syracuseStep 5946371 = 8919557) B8919557
theorem B6339667 : Blo 924580 6339667 := bstep (se 1 (by rfl) ⟨4754750, by rfl⟩ : syracuseStep 6339667 = 9509501) B9509501
theorem B2636975 : Blo 924580 2636975 := bstep (se 1 (by rfl) ⟨1977731, by rfl⟩ : syracuseStep 2636975 = 3955463) B3955463
theorem B2080763 : Blo 924580 2080763 := bstep (se 1 (by rfl) ⟨1560572, by rfl⟩ : syracuseStep 2080763 = 3121145) B3121145
theorem B2080799 : Blo 924580 2080799 := bstep (se 1 (by rfl) ⟨1560599, by rfl⟩ : syracuseStep 2080799 = 3121199) B3121199
theorem B1392743 : Blo 924580 1392743 := bstep (se 1 (by rfl) ⟨1044557, by rfl⟩ : syracuseStep 1392743 = 2089115) B2089115
theorem B2637967 : Blo 924580 2637967 := bstep (se 1 (by rfl) ⟨1978475, by rfl⟩ : syracuseStep 2637967 = 3956951) B3956951
theorem B2081051 : Blo 924580 2081051 := bstep (se 1 (by rfl) ⟨1560788, by rfl⟩ : syracuseStep 2081051 = 3121577) B3121577
theorem B1982875 : Blo 924580 1982875 := bstep (se 1 (by rfl) ⟨1487156, by rfl⟩ : syracuseStep 1982875 = 2974313) B2974313
theorem B2343451 : Blo 924580 2343451 := bstep (se 1 (by rfl) ⟨1757588, by rfl⟩ : syracuseStep 2343451 = 3515177) B3515177
theorem B2081951 : Blo 924580 2081951 := bstep (se 1 (by rfl) ⟨1561463, by rfl⟩ : syracuseStep 2081951 = 3122927) B3122927
theorem B2639699 : Blo 924580 2639699 := bstep (se 1 (by rfl) ⟨1979774, by rfl⟩ : syracuseStep 2639699 = 3959549) B3959549
theorem B13355225 : Blo 924580 13355225 := bstep (se 2 (by rfl) ⟨5008209, by rfl⟩ : syracuseStep 13355225 = 10016419) B10016419
theorem B4704743 : Blo 924580 4704743 := bstep (se 1 (by rfl) ⟨3528557, by rfl⟩ : syracuseStep 4704743 = 7057115) B7057115
theorem B2083319 : Blo 924580 2083319 := bstep (se 1 (by rfl) ⟨1562489, by rfl⟩ : syracuseStep 2083319 = 3124979) B3124979
theorem B35768927 : Blo 924580 35768927 := bstep (se 1 (by rfl) ⟨26826695, by rfl⟩ : syracuseStep 35768927 = 53653391) B53653391
theorem B3525565 : Blo 924580 3525565 := bstep (se 3 (by rfl) ⟨661043, by rfl⟩ : syracuseStep 3525565 = 1322087) B1322087
theorem B2083931 : Blo 924580 2083931 := bstep (se 1 (by rfl) ⟨1562948, by rfl⟩ : syracuseStep 2083931 = 3125897) B3125897
theorem B9522319 : Blo 924580 9522319 := bstep (se 1 (by rfl) ⟨7141739, by rfl⟩ : syracuseStep 9522319 = 14283479) B14283479
theorem B1756343 : Blo 924580 1756343 := bstep (se 1 (by rfl) ⟨1317257, by rfl⟩ : syracuseStep 1756343 = 2634515) B2634515
theorem B2084489 : Blo 924580 2084489 := bstep (se 2 (by rfl) ⟨781683, by rfl⟩ : syracuseStep 2084489 = 1563367) B1563367
theorem B1560431 : Blo 924580 1560431 := bstep (se 1 (by rfl) ⟨1170323, by rfl⟩ : syracuseStep 1560431 = 2340647) B2340647
theorem B3133511 : Blo 924580 3133511 := bstep (se 1 (by rfl) ⟨2350133, by rfl⟩ : syracuseStep 3133511 = 4700267) B4700267
theorem B2347177 : Blo 924580 2347177 := bstep (se 2 (by rfl) ⟨880191, by rfl⟩ : syracuseStep 2347177 = 1760383) B1760383
theorem B2085191 : Blo 924580 2085191 := bstep (se 1 (by rfl) ⟨1563893, by rfl⟩ : syracuseStep 2085191 = 3127787) B3127787
theorem B59986403 : Blo 924580 59986403 := bstep (se 1 (by rfl) ⟨44989802, by rfl⟩ : syracuseStep 59986403 = 89979605) B89979605
theorem B1757695 : Blo 924580 1757695 := bstep (se 1 (by rfl) ⟨1318271, by rfl⟩ : syracuseStep 1757695 = 2636543) B2636543
theorem B53498393 : Blo 924580 53498393 := bstep (se 2 (by rfl) ⟨20061897, by rfl⟩ : syracuseStep 53498393 = 40123795) B40123795
theorem B2085659 : Blo 924580 2085659 := bstep (se 1 (by rfl) ⟨1564244, by rfl⟩ : syracuseStep 2085659 = 3128489) B3128489
theorem B2380681 : Blo 924580 2380681 := bstep (se 2 (by rfl) ⟨892755, by rfl⟩ : syracuseStep 2380681 = 1785511) B1785511
theorem B7623985 : Blo 924580 7623985 := bstep (se 2 (by rfl) ⟨2858994, by rfl⟩ : syracuseStep 7623985 = 5717989) B5717989
theorem B1430887 : Blo 924580 1430887 := bstep (se 1 (by rfl) ⟨1073165, by rfl⟩ : syracuseStep 1430887 = 2146331) B2146331
theorem B2348585 : Blo 924580 2348585 := bstep (se 2 (by rfl) ⟨880719, by rfl⟩ : syracuseStep 2348585 = 1761439) B1761439
theorem B2348777 : Blo 924580 2348777 := bstep (se 2 (by rfl) ⟨880791, by rfl⟩ : syracuseStep 2348777 = 1761583) B1761583
theorem B4446035 : Blo 924580 4446035 := bstep (se 1 (by rfl) ⟨3334526, by rfl⟩ : syracuseStep 4446035 = 6669053) B6669053
theorem B20011049 : Blo 924580 20011049 := bstep (se 2 (by rfl) ⟨7504143, by rfl⟩ : syracuseStep 20011049 = 15008287) B15008287
theorem B2087099 : Blo 924580 2087099 := bstep (se 1 (by rfl) ⟨1565324, by rfl⟩ : syracuseStep 2087099 = 3130649) B3130649
theorem B2087891 : Blo 924580 2087891 := bstep (se 1 (by rfl) ⟨1565918, by rfl⟩ : syracuseStep 2087891 = 3131837) B3131837
theorem B13360247 : Blo 924580 13360247 := bstep (se 1 (by rfl) ⟨10020185, by rfl⟩ : syracuseStep 13360247 = 20040371) B20040371
theorem B25386689 : Blo 924580 25386689 := bstep (se 2 (by rfl) ⟨9520008, by rfl⟩ : syracuseStep 25386689 = 19040017) B19040017
theorem B1171903 : Blo 924580 1171903 := bstep (se 1 (by rfl) ⟨878927, by rfl⟩ : syracuseStep 1171903 = 1757855) B1757855
theorem B4514395 : Blo 924580 4514395 := bstep (se 1 (by rfl) ⟨3385796, by rfl⟩ : syracuseStep 4514395 = 6771593) B6771593
theorem B26763959 : Blo 924580 26763959 := bstep (se 1 (by rfl) ⟨20072969, by rfl⟩ : syracuseStep 26763959 = 40145939) B40145939
theorem B1762175 : Blo 924580 1762175 := bstep (se 1 (by rfl) ⟨1321631, by rfl⟩ : syracuseStep 1762175 = 2643263) B2643263
theorem B8905943 : Blo 924580 8905943 := bstep (se 1 (by rfl) ⟨6679457, by rfl⟩ : syracuseStep 8905943 = 13358915) B13358915
theorem B1041727 : Blo 924580 1041727 := bstep (se 1 (by rfl) ⟨781295, by rfl⟩ : syracuseStep 1041727 = 1562591) B1562591
theorem B6350177 : Blo 924580 6350177 := bstep (se 2 (by rfl) ⟨2381316, by rfl⟩ : syracuseStep 6350177 = 4762633) B4762633
theorem B6677959 : Blo 924580 6677959 := bstep (se 1 (by rfl) ⟨5008469, by rfl⟩ : syracuseStep 6677959 = 10016939) B10016939
theorem B8449019 : Blo 924580 8449019 := bstep (se 1 (by rfl) ⟨6336764, by rfl⟩ : syracuseStep 8449019 = 12673529) B12673529
theorem B2223719 : Blo 924580 2223719 := bstep (se 1 (by rfl) ⟨1667789, by rfl⟩ : syracuseStep 2223719 = 3335579) B3335579
theorem B1044391 : Blo 924580 1044391 := bstep (se 1 (by rfl) ⟨783293, by rfl⟩ : syracuseStep 1044391 = 1566587) B1566587
theorem B7926781 : Blo 924580 7926781 := bstep (se 3 (by rfl) ⟨1486271, by rfl⟩ : syracuseStep 7926781 = 2972543) B2972543
theorem B7042139 : Blo 924580 7042139 := bstep (se 1 (by rfl) ⟨5281604, by rfl⟩ : syracuseStep 7042139 = 10563209) B10563209
theorem B4683257 : Blo 924580 4683257 := bstep (se 2 (by rfl) ⟨1756221, by rfl⟩ : syracuseStep 4683257 = 3512443) B3512443
theorem B4454509 : Blo 924580 4454509 := bstep (se 3 (by rfl) ⟨835220, by rfl⟩ : syracuseStep 4454509 = 1670441) B1670441
theorem B9501047 : Blo 924580 9501047 := bstep (se 1 (by rfl) ⟨7125785, by rfl⟩ : syracuseStep 9501047 = 14251571) B14251571
theorem B12024503 : Blo 924580 12024503 := bstep (se 1 (by rfl) ⟨9018377, by rfl⟩ : syracuseStep 12024503 = 18036755) B18036755
theorem B7929515 : Blo 924580 7929515 := bstep (se 1 (by rfl) ⟨5947136, by rfl⟩ : syracuseStep 7929515 = 11894273) B11894273
theorem B7931155 : Blo 924580 7931155 := bstep (se 1 (by rfl) ⟨5948366, by rfl⟩ : syracuseStep 7931155 = 11896733) B11896733
theorem B16057667 : Blo 924580 16057667 := bstep (se 1 (by rfl) ⟨12043250, by rfl⟩ : syracuseStep 16057667 = 24086501) B24086501
theorem B9504823 : Blo 924580 9504823 := bstep (se 1 (by rfl) ⟨7128617, by rfl⟩ : syracuseStep 9504823 = 14257235) B14257235
theorem B11864339 : Blo 924580 11864339 := bstep (se 1 (by rfl) ⟨8898254, by rfl⟩ : syracuseStep 11864339 = 17796509) B17796509
theorem B7604687 : Blo 924580 7604687 := bstep (se 1 (by rfl) ⟨5703515, by rfl⟩ : syracuseStep 7604687 = 11407031) B11407031
theorem B3346247 : Blo 924580 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B13340699 : Blo 924580 13340699 := bstep (se 1 (by rfl) ⟨10005524, by rfl⟩ : syracuseStep 13340699 = 20011049) B20011049
theorem B1426855661 : Blo 924580 1426855661 := bstep (se 3 (by rfl) ⟨267535436, by rfl⟩ : syracuseStep 1426855661 = 535070873) B535070873
theorem B5937295 : Blo 924580 5937295 := bstep (se 1 (by rfl) ⟨4452971, by rfl⟩ : syracuseStep 5937295 = 8905943) B8905943
theorem B10165313 : Blo 924580 10165313 := bstep (se 2 (by rfl) ⟨3811992, by rfl⟩ : syracuseStep 10165313 = 7623985) B7623985
theorem B1907849 : Blo 924580 1907849 := bstep (se 2 (by rfl) ⟨715443, by rfl⟩ : syracuseStep 1907849 = 1430887) B1430887
theorem B924923 : Blo 924580 924923 := bstep (se 1 (by rfl) ⟨693692, by rfl⟩ : syracuseStep 924923 = 1387385) B1387385
theorem B1482479 : Blo 924580 1482479 := bstep (se 1 (by rfl) ⟨1111859, by rfl⟩ : syracuseStep 1482479 = 2223719) B2223719
theorem B5939345 : Blo 924580 5939345 := bstep (se 2 (by rfl) ⟨2227254, by rfl⟩ : syracuseStep 5939345 = 4454509) B4454509
theorem B926023 : Blo 924580 926023 := bstep (se 1 (by rfl) ⟨694517, by rfl⟩ : syracuseStep 926023 = 1389035) B1389035
theorem B926107 : Blo 924580 926107 := bstep (se 1 (by rfl) ⟨694580, by rfl⟩ : syracuseStep 926107 = 1389161) B1389161
theorem B4694759 : Blo 924580 4694759 := bstep (se 1 (by rfl) ⟨3521069, by rfl⟩ : syracuseStep 4694759 = 7042139) B7042139
theorem B3122171 : Blo 924580 3122171 := bstep (se 1 (by rfl) ⟨2341628, by rfl⟩ : syracuseStep 3122171 = 4683257) B4683257
theorem B1582111 : Blo 924580 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B6334031 : Blo 924580 6334031 := bstep (se 1 (by rfl) ⟨4750523, by rfl⟩ : syracuseStep 6334031 = 9501047) B9501047
theorem B927487 : Blo 924580 927487 := bstep (se 1 (by rfl) ⟨695615, by rfl⟩ : syracuseStep 927487 = 1391231) B1391231
theorem B5286343 : Blo 924580 5286343 := bstep (se 1 (by rfl) ⟨3964757, by rfl⟩ : syracuseStep 5286343 = 7929515) B7929515
theorem B1387175 : Blo 924580 1387175 := bstep (se 1 (by rfl) ⟨1040381, by rfl⟩ : syracuseStep 1387175 = 2080763) B2080763
theorem B1387199 : Blo 924580 1387199 := bstep (se 1 (by rfl) ⟨1040399, by rfl⟩ : syracuseStep 1387199 = 2080799) B2080799
theorem B120105665 : Blo 924580 120105665 := bstep (se 2 (by rfl) ⟨45039624, by rfl⟩ : syracuseStep 120105665 = 90079249) B90079249
theorem B928495 : Blo 924580 928495 := bstep (se 1 (by rfl) ⟨696371, by rfl⟩ : syracuseStep 928495 = 1392743) B1392743
theorem B1387367 : Blo 924580 1387367 := bstep (se 1 (by rfl) ⟨1040525, by rfl⟩ : syracuseStep 1387367 = 2081051) B2081051
theorem B3517289 : Blo 924580 3517289 := bstep (se 2 (by rfl) ⟨1318983, by rfl⟩ : syracuseStep 3517289 = 2637967) B2637967
theorem B3124601 : Blo 924580 3124601 := bstep (se 2 (by rfl) ⟨1171725, by rfl⟩ : syracuseStep 3124601 = 2343451) B2343451
theorem B3124655 : Blo 924580 3124655 := bstep (se 1 (by rfl) ⟨2343491, by rfl⟩ : syracuseStep 3124655 = 4686983) B4686983
theorem B1387967 : Blo 924580 1387967 := bstep (se 1 (by rfl) ⟨1040975, by rfl⟩ : syracuseStep 1387967 = 2081951) B2081951
theorem B6008327 : Blo 924580 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B1486439 : Blo 924580 1486439 := bstep (se 1 (by rfl) ⟨1114829, by rfl⟩ : syracuseStep 1486439 = 2229659) B2229659
theorem B1978681 : Blo 924580 1978681 := bstep (se 2 (by rfl) ⟨742005, by rfl⟩ : syracuseStep 1978681 = 1484011) B1484011
theorem B26685773 : Blo 924580 26685773 := bstep (se 3 (by rfl) ⟨5003582, by rfl⟩ : syracuseStep 26685773 = 10007165) B10007165
theorem B1388879 : Blo 924580 1388879 := bstep (se 1 (by rfl) ⟨1041659, by rfl⟩ : syracuseStep 1388879 = 2083319) B2083319
theorem B1388969 : Blo 924580 1388969 := bstep (se 2 (by rfl) ⟨520863, by rfl⟩ : syracuseStep 1388969 = 1041727) B1041727
theorem B3125951 : Blo 924580 3125951 := bstep (se 1 (by rfl) ⟨2344463, by rfl⟩ : syracuseStep 3125951 = 4688927) B4688927
theorem B1389287 : Blo 924580 1389287 := bstep (se 1 (by rfl) ⟨1041965, by rfl⟩ : syracuseStep 1389287 = 2083931) B2083931
theorem B4699133 : Blo 924580 4699133 := bstep (se 3 (by rfl) ⟨881087, by rfl⟩ : syracuseStep 4699133 = 1762175) B1762175
theorem B1389659 : Blo 924580 1389659 := bstep (se 1 (by rfl) ⟨1042244, by rfl⟩ : syracuseStep 1389659 = 2084489) B2084489
theorem B1881323 : Blo 924580 1881323 := bstep (se 1 (by rfl) ⟨1410992, by rfl⟩ : syracuseStep 1881323 = 2821985) B2821985
theorem B1390127 : Blo 924580 1390127 := bstep (se 1 (by rfl) ⟨1042595, by rfl⟩ : syracuseStep 1390127 = 2085191) B2085191
theorem B39990935 : Blo 924580 39990935 := bstep (se 1 (by rfl) ⟨29993201, by rfl⟩ : syracuseStep 39990935 = 59986403) B59986403
theorem B35665595 : Blo 924580 35665595 := bstep (se 1 (by rfl) ⟨26749196, by rfl⟩ : syracuseStep 35665595 = 53498393) B53498393
theorem B1390439 : Blo 924580 1390439 := bstep (se 1 (by rfl) ⟨1042829, by rfl⟩ : syracuseStep 1390439 = 2085659) B2085659
theorem B3127679 : Blo 924580 3127679 := bstep (se 1 (by rfl) ⟨2345759, by rfl⟩ : syracuseStep 3127679 = 4691519) B4691519
theorem B2964023 : Blo 924580 2964023 := bstep (se 1 (by rfl) ⟨2223017, by rfl⟩ : syracuseStep 2964023 = 4446035) B4446035
theorem B4700753 : Blo 924580 4700753 := bstep (se 2 (by rfl) ⟨1762782, by rfl⟩ : syracuseStep 4700753 = 3525565) B3525565
theorem B1391399 : Blo 924580 1391399 := bstep (se 1 (by rfl) ⟨1043549, by rfl⟩ : syracuseStep 1391399 = 2087099) B2087099
theorem B12696425 : Blo 924580 12696425 := bstep (se 2 (by rfl) ⟨4761159, by rfl⟩ : syracuseStep 12696425 = 9522319) B9522319
theorem B1391927 : Blo 924580 1391927 := bstep (se 1 (by rfl) ⟨1043945, by rfl⟩ : syracuseStep 1391927 = 2087891) B2087891
theorem B3129083 : Blo 924580 3129083 := bstep (se 1 (by rfl) ⟨2346812, by rfl⟩ : syracuseStep 3129083 = 4693625) B4693625
theorem B16924459 : Blo 924580 16924459 := bstep (se 1 (by rfl) ⟨12693344, by rfl⟩ : syracuseStep 16924459 = 25386689) B25386689
theorem B1392521 : Blo 924580 1392521 := bstep (se 2 (by rfl) ⟨522195, by rfl⟩ : syracuseStep 1392521 = 1044391) B1044391
theorem B3129569 : Blo 924580 3129569 := bstep (se 2 (by rfl) ⟨1173588, by rfl⟩ : syracuseStep 3129569 = 2347177) B2347177
theorem B17842639 : Blo 924580 17842639 := bstep (se 1 (by rfl) ⟨13381979, by rfl⟩ : syracuseStep 17842639 = 26763959) B26763959
theorem B2343593 : Blo 924580 2343593 := bstep (se 2 (by rfl) ⟨878847, by rfl⟩ : syracuseStep 2343593 = 1757695) B1757695
theorem B7029989 : Blo 924580 7029989 := bstep (se 4 (by rfl) ⟨659061, by rfl⟩ : syracuseStep 7029989 = 1318123) B1318123
theorem B10569041 : Blo 924580 10569041 := bstep (se 2 (by rfl) ⟨3963390, by rfl⟩ : syracuseStep 10569041 = 7926781) B7926781
theorem B2082239 : Blo 924580 2082239 := bstep (se 1 (by rfl) ⟨1561679, by rfl⟩ : syracuseStep 2082239 = 3123359) B3123359
theorem B7031933 : Blo 924580 7031933 := bstep (se 3 (by rfl) ⟨1318487, by rfl⟩ : syracuseStep 7031933 = 2636975) B2636975
theorem B2084543 : Blo 924580 2084543 := bstep (se 1 (by rfl) ⟨1563407, by rfl⟩ : syracuseStep 2084543 = 3126815) B3126815
theorem B1757065 : Blo 924580 1757065 := bstep (se 2 (by rfl) ⟨658899, by rfl⟩ : syracuseStep 1757065 = 1317799) B1317799
theorem B2085047 : Blo 924580 2085047 := bstep (se 1 (by rfl) ⟨1563785, by rfl⟩ : syracuseStep 2085047 = 3127571) B3127571
theorem B3133727 : Blo 924580 3133727 := bstep (se 1 (by rfl) ⟨2350295, by rfl⟩ : syracuseStep 3133727 = 4700591) B4700591
theorem B8016335 : Blo 924580 8016335 := bstep (se 1 (by rfl) ⟨6012251, by rfl⟩ : syracuseStep 8016335 = 12024503) B12024503
theorem B7034363 : Blo 924580 7034363 := bstep (se 1 (by rfl) ⟨5275772, by rfl⟩ : syracuseStep 7034363 = 10551545) B10551545
theorem B2643833 : Blo 924580 2643833 := bstep (se 2 (by rfl) ⟨991437, by rfl⟩ : syracuseStep 2643833 = 1982875) B1982875
theorem B1562537 : Blo 924580 1562537 := bstep (se 2 (by rfl) ⟨585951, by rfl⟩ : syracuseStep 1562537 = 1171903) B1171903
theorem B6019193 : Blo 924580 6019193 := bstep (se 2 (by rfl) ⟨2257197, by rfl⟩ : syracuseStep 6019193 = 4514395) B4514395
theorem B3758399 : Blo 924580 3758399 := bstep (se 1 (by rfl) ⟨2818799, by rfl⟩ : syracuseStep 3758399 = 5637599) B5637599
theorem B1759799 : Blo 924580 1759799 := bstep (se 1 (by rfl) ⟨1319849, by rfl⟩ : syracuseStep 1759799 = 2639699) B2639699
theorem B8903483 : Blo 924580 8903483 := bstep (se 1 (by rfl) ⟨6677612, by rfl⟩ : syracuseStep 8903483 = 13355225) B13355225
theorem B3136495 : Blo 924580 3136495 := bstep (se 1 (by rfl) ⟨2352371, by rfl⟩ : syracuseStep 3136495 = 4704743) B4704743
theorem B23845951 : Blo 924580 23845951 := bstep (se 1 (by rfl) ⟨17884463, by rfl⟩ : syracuseStep 23845951 = 35768927) B35768927
theorem B8903945 : Blo 924580 8903945 := bstep (se 2 (by rfl) ⟨3338979, by rfl⟩ : syracuseStep 8903945 = 6677959) B6677959
theorem B1040287 : Blo 924580 1040287 := bstep (se 1 (by rfl) ⟨780215, by rfl⟩ : syracuseStep 1040287 = 1560431) B1560431
theorem B2089007 : Blo 924580 2089007 := bstep (se 1 (by rfl) ⟨1566755, by rfl⟩ : syracuseStep 2089007 = 3133511) B3133511
theorem B16933805 : Blo 924580 16933805 := bstep (se 3 (by rfl) ⟨3175088, by rfl⟩ : syracuseStep 16933805 = 6350177) B6350177
theorem B1565723 : Blo 924580 1565723 := bstep (se 1 (by rfl) ⟨1174292, by rfl⟩ : syracuseStep 1565723 = 2348585) B2348585
theorem B1565851 : Blo 924580 1565851 := bstep (se 1 (by rfl) ⟨1174388, by rfl⟩ : syracuseStep 1565851 = 2348777) B2348777
theorem B7923365 : Blo 924580 7923365 := bstep (se 4 (by rfl) ⟨742815, by rfl⟩ : syracuseStep 7923365 = 1485631) B1485631
theorem B8906831 : Blo 924580 8906831 := bstep (se 1 (by rfl) ⟨6680123, by rfl⟩ : syracuseStep 8906831 = 13360247) B13360247
theorem B5270831 : Blo 924580 5270831 := bstep (se 1 (by rfl) ⟨3953123, by rfl⟩ : syracuseStep 5270831 = 7906247) B7906247
theorem B3174241 : Blo 924580 3174241 := bstep (se 2 (by rfl) ⟨1190340, by rfl⟩ : syracuseStep 3174241 = 2380681) B2380681
theorem B5926891 : Blo 924580 5926891 := bstep (se 1 (by rfl) ⟨4445168, by rfl⟩ : syracuseStep 5926891 = 8890337) B8890337
theorem B2060329 : Blo 924580 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B5632679 : Blo 924580 5632679 := bstep (se 1 (by rfl) ⟨4224509, by rfl⟩ : syracuseStep 5632679 = 8449019) B8449019
theorem B4683581 : Blo 924580 4683581 := bstep (se 3 (by rfl) ⟨878171, by rfl⟩ : syracuseStep 4683581 = 1756343) B1756343
theorem B8452889 : Blo 924580 8452889 := bstep (se 2 (by rfl) ⟨3169833, by rfl⟩ : syracuseStep 8452889 = 6339667) B6339667
theorem B3964247 : Blo 924580 3964247 := bstep (se 1 (by rfl) ⟨2973185, by rfl⟩ : syracuseStep 3964247 = 5946371) B5946371
theorem B23790185 : Blo 924580 23790185 := bstep (se 2 (by rfl) ⟨8921319, by rfl⟩ : syracuseStep 23790185 = 17842639) B17842639
theorem B4686659 : Blo 924580 4686659 := bstep (se 1 (by rfl) ⟨3514994, by rfl⟩ : syracuseStep 4686659 = 7029989) B7029989
theorem B7046027 : Blo 924580 7046027 := bstep (se 1 (by rfl) ⟨5284520, by rfl⟩ : syracuseStep 7046027 = 10569041) B10569041
theorem B4687955 : Blo 924580 4687955 := bstep (se 1 (by rfl) ⟨3515966, by rfl⟩ : syracuseStep 4687955 = 7031933) B7031933
theorem B2230831 : Blo 924580 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B5344223 : Blo 924580 5344223 := bstep (se 1 (by rfl) ⟨4008167, by rfl⟩ : syracuseStep 5344223 = 8016335) B8016335
theorem B7048457 : Blo 924580 7048457 := bstep (se 2 (by rfl) ⟨2643171, by rfl⟩ : syracuseStep 7048457 = 5286343) B5286343
theorem B4689575 : Blo 924580 4689575 := bstep (se 1 (by rfl) ⟨3517181, by rfl⟩ : syracuseStep 4689575 = 7034363) B7034363
theorem B5935655 : Blo 924580 5935655 := bstep (se 1 (by rfl) ⟨4451741, by rfl⟩ : syracuseStep 5935655 = 8903483) B8903483
theorem B5935963 : Blo 924580 5935963 := bstep (se 1 (by rfl) ⟨4451972, by rfl⟩ : syracuseStep 5935963 = 8903945) B8903945
theorem B4232321 : Blo 924580 4232321 := bstep (se 2 (by rfl) ⟨1587120, by rfl⟩ : syracuseStep 4232321 = 3174241) B3174241
theorem B988319 : Blo 924580 988319 := bstep (se 1 (by rfl) ⟨741239, by rfl⟩ : syracuseStep 988319 = 1482479) B1482479
theorem B7902521 : Blo 924580 7902521 := bstep (se 2 (by rfl) ⟨2963445, by rfl⟩ : syracuseStep 7902521 = 5926891) B5926891
theorem B5282243 : Blo 924580 5282243 := bstep (se 1 (by rfl) ⟨3961682, by rfl⟩ : syracuseStep 5282243 = 7923365) B7923365
theorem B5937887 : Blo 924580 5937887 := bstep (se 1 (by rfl) ⟨4453415, by rfl⟩ : syracuseStep 5937887 = 8906831) B8906831
theorem B924783 : Blo 924580 924783 := bstep (se 1 (by rfl) ⟨693587, by rfl⟩ : syracuseStep 924783 = 1387175) B1387175
theorem B924799 : Blo 924580 924799 := bstep (se 1 (by rfl) ⟨693599, by rfl⟩ : syracuseStep 924799 = 1387199) B1387199
theorem B924911 : Blo 924580 924911 := bstep (se 1 (by rfl) ⟨693683, by rfl⟩ : syracuseStep 924911 = 1387367) B1387367
theorem B3513887 : Blo 924580 3513887 := bstep (se 1 (by rfl) ⟨2635415, by rfl⟩ : syracuseStep 3513887 = 5270831) B5270831
theorem B925311 : Blo 924580 925311 := bstep (se 1 (by rfl) ⟨693983, by rfl⟩ : syracuseStep 925311 = 1387967) B1387967
theorem B4005551 : Blo 924580 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B990959 : Blo 924580 990959 := bstep (se 1 (by rfl) ⟨743219, by rfl⟩ : syracuseStep 990959 = 1486439) B1486439
theorem B925919 : Blo 924580 925919 := bstep (se 1 (by rfl) ⟨694439, by rfl⟩ : syracuseStep 925919 = 1388879) B1388879
theorem B925979 : Blo 924580 925979 := bstep (se 1 (by rfl) ⟨694484, by rfl⟩ : syracuseStep 925979 = 1388969) B1388969
theorem B926191 : Blo 924580 926191 := bstep (se 1 (by rfl) ⟨694643, by rfl⟩ : syracuseStep 926191 = 1389287) B1389287
theorem B926439 : Blo 924580 926439 := bstep (se 1 (by rfl) ⟨694829, by rfl⟩ : syracuseStep 926439 = 1389659) B1389659
theorem B1254215 : Blo 924580 1254215 := bstep (se 1 (by rfl) ⟨940661, by rfl⟩ : syracuseStep 1254215 = 1881323) B1881323
theorem B926751 : Blo 924580 926751 := bstep (se 1 (by rfl) ⟨695063, by rfl⟩ : syracuseStep 926751 = 1390127) B1390127
theorem B3122387 : Blo 924580 3122387 := bstep (se 1 (by rfl) ⟨2341790, by rfl⟩ : syracuseStep 3122387 = 4683581) B4683581
theorem B926959 : Blo 924580 926959 := bstep (se 1 (by rfl) ⟨695219, by rfl⟩ : syracuseStep 926959 = 1390439) B1390439
theorem B31794601 : Blo 924580 31794601 := bstep (se 2 (by rfl) ⟨11922975, by rfl⟩ : syracuseStep 31794601 = 23845951) B23845951
theorem B1976015 : Blo 924580 1976015 := bstep (se 1 (by rfl) ⟨1482011, by rfl⟩ : syracuseStep 1976015 = 2964023) B2964023
theorem B927599 : Blo 924580 927599 := bstep (se 1 (by rfl) ⟨695699, by rfl⟩ : syracuseStep 927599 = 1391399) B1391399
theorem B8464283 : Blo 924580 8464283 := bstep (se 1 (by rfl) ⟨6348212, by rfl⟩ : syracuseStep 8464283 = 12696425) B12696425
theorem B927951 : Blo 924580 927951 := bstep (se 1 (by rfl) ⟨695963, by rfl⟩ : syracuseStep 927951 = 1391927) B1391927
theorem B1387049 : Blo 924580 1387049 := bstep (se 2 (by rfl) ⟨520143, by rfl⟩ : syracuseStep 1387049 = 1040287) B1040287
theorem B928347 : Blo 924580 928347 := bstep (se 1 (by rfl) ⟨696260, by rfl⟩ : syracuseStep 928347 = 1392521) B1392521
theorem B15838253 : Blo 924580 15838253 := bstep (se 3 (by rfl) ⟨2969672, by rfl⟩ : syracuseStep 15838253 = 5939345) B5939345
theorem B1388159 : Blo 924580 1388159 := bstep (se 1 (by rfl) ⟨1041119, by rfl⟩ : syracuseStep 1388159 = 2082239) B2082239
theorem B7909559 : Blo 924580 7909559 := bstep (se 1 (by rfl) ⟨5932169, by rfl⟩ : syracuseStep 7909559 = 11864339) B11864339
theorem B15020477 : Blo 924580 15020477 := bstep (se 3 (by rfl) ⟨2816339, by rfl⟩ : syracuseStep 15020477 = 5632679) B5632679
theorem B1389695 : Blo 924580 1389695 := bstep (se 1 (by rfl) ⟨1042271, by rfl⟩ : syracuseStep 1389695 = 2084543) B2084543
theorem B8893799 : Blo 924580 8893799 := bstep (se 1 (by rfl) ⟨6670349, by rfl⟩ : syracuseStep 8893799 = 13340699) B13340699
theorem B1390031 : Blo 924580 1390031 := bstep (se 1 (by rfl) ⟨1042523, by rfl⟩ : syracuseStep 1390031 = 2085047) B2085047
theorem B951237107 : Blo 924580 951237107 := bstep (se 1 (by rfl) ⟨713427830, by rfl⟩ : syracuseStep 951237107 = 1426855661) B1426855661
theorem B4012795 : Blo 924580 4012795 := bstep (se 1 (by rfl) ⟨3009596, by rfl⟩ : syracuseStep 4012795 = 6019193) B6019193
theorem B2505599 : Blo 924580 2505599 := bstep (se 1 (by rfl) ⟨1879199, by rfl⟩ : syracuseStep 2505599 = 3758399) B3758399
theorem B2342753 : Blo 924580 2342753 := bstep (se 2 (by rfl) ⟨878532, by rfl⟩ : syracuseStep 2342753 = 1757065) B1757065
theorem B1392671 : Blo 924580 1392671 := bstep (se 1 (by rfl) ⟨1044503, by rfl⟩ : syracuseStep 1392671 = 2089007) B2089007
theorem B8437925 : Blo 924580 8437925 := bstep (se 4 (by rfl) ⟨791055, by rfl⟩ : syracuseStep 8437925 = 1582111) B1582111
theorem B2638241 : Blo 924580 2638241 := bstep (se 2 (by rfl) ⟨989340, by rfl⟩ : syracuseStep 2638241 = 1978681) B1978681
theorem B3129839 : Blo 924580 3129839 := bstep (se 1 (by rfl) ⟨2347379, by rfl⟩ : syracuseStep 3129839 = 4694759) B4694759
theorem B11289203 : Blo 924580 11289203 := bstep (se 1 (by rfl) ⟨8466902, by rfl⟩ : syracuseStep 11289203 = 16933805) B16933805
theorem B2081447 : Blo 924580 2081447 := bstep (se 1 (by rfl) ⟨1561085, by rfl⟩ : syracuseStep 2081447 = 3122171) B3122171
theorem B80070443 : Blo 924580 80070443 := bstep (se 1 (by rfl) ⟨60052832, by rfl⟩ : syracuseStep 80070443 = 120105665) B120105665
theorem B2344859 : Blo 924580 2344859 := bstep (se 1 (by rfl) ⟨1758644, by rfl⟩ : syracuseStep 2344859 = 3517289) B3517289
theorem B2083067 : Blo 924580 2083067 := bstep (se 1 (by rfl) ⟨1562300, by rfl⟩ : syracuseStep 2083067 = 3124601) B3124601
theorem B2083103 : Blo 924580 2083103 := bstep (se 1 (by rfl) ⟨1562327, by rfl⟩ : syracuseStep 2083103 = 3124655) B3124655
theorem B7916393 : Blo 924580 7916393 := bstep (se 2 (by rfl) ⟨2968647, by rfl⟩ : syracuseStep 7916393 = 5937295) B5937295
theorem B2083967 : Blo 924580 2083967 := bstep (se 1 (by rfl) ⟨1562975, by rfl⟩ : syracuseStep 2083967 = 3125951) B3125951
theorem B3132755 : Blo 924580 3132755 := bstep (se 1 (by rfl) ⟨2349566, by rfl⟩ : syracuseStep 3132755 = 4699133) B4699133
theorem B26660623 : Blo 924580 26660623 := bstep (se 1 (by rfl) ⟨19995467, by rfl⟩ : syracuseStep 26660623 = 39990935) B39990935
theorem B23777063 : Blo 924580 23777063 := bstep (se 1 (by rfl) ⟨17832797, by rfl⟩ : syracuseStep 23777063 = 35665595) B35665595
theorem B4181993 : Blo 924580 4181993 := bstep (se 2 (by rfl) ⟨1568247, by rfl⟩ : syracuseStep 4181993 = 3136495) B3136495
theorem B2085119 : Blo 924580 2085119 := bstep (se 1 (by rfl) ⟨1563839, by rfl⟩ : syracuseStep 2085119 = 3127679) B3127679
theorem B3133835 : Blo 924580 3133835 := bstep (se 1 (by rfl) ⟨2350376, by rfl⟩ : syracuseStep 3133835 = 4700753) B4700753
theorem B2642831 : Blo 924580 2642831 := bstep (se 1 (by rfl) ⟨1982123, by rfl⟩ : syracuseStep 2642831 = 3964247) B3964247
theorem B22565945 : Blo 924580 22565945 := bstep (se 2 (by rfl) ⟨8462229, by rfl⟩ : syracuseStep 22565945 = 16924459) B16924459
theorem B2086055 : Blo 924580 2086055 := bstep (se 1 (by rfl) ⟨1564541, by rfl⟩ : syracuseStep 2086055 = 3129083) B3129083
theorem B2086379 : Blo 924580 2086379 := bstep (se 1 (by rfl) ⟨1564784, by rfl⟩ : syracuseStep 2086379 = 3129569) B3129569
theorem B1562395 : Blo 924580 1562395 := bstep (se 1 (by rfl) ⟨1171796, by rfl⟩ : syracuseStep 1562395 = 2343593) B2343593
theorem B10705111 : Blo 924580 10705111 := bstep (se 1 (by rfl) ⟨8028833, by rfl⟩ : syracuseStep 10705111 = 16057667) B16057667
theorem B2087801 : Blo 924580 2087801 := bstep (se 2 (by rfl) ⟨782925, by rfl⟩ : syracuseStep 2087801 = 1565851) B1565851
theorem B5069791 : Blo 924580 5069791 := bstep (se 1 (by rfl) ⟨3802343, by rfl⟩ : syracuseStep 5069791 = 7604687) B7604687
theorem B10574873 : Blo 924580 10574873 := bstep (se 2 (by rfl) ⟨3965577, by rfl⟩ : syracuseStep 10574873 = 7931155) B7931155
theorem B12673097 : Blo 924580 12673097 := bstep (se 2 (by rfl) ⟨4752411, by rfl⟩ : syracuseStep 12673097 = 9504823) B9504823
theorem B2089151 : Blo 924580 2089151 := bstep (se 1 (by rfl) ⟨1566863, by rfl⟩ : syracuseStep 2089151 = 3133727) B3133727
theorem B1762555 : Blo 924580 1762555 := bstep (se 1 (by rfl) ⟨1321916, by rfl⟩ : syracuseStep 1762555 = 2643833) B2643833
theorem B1041691 : Blo 924580 1041691 := bstep (se 1 (by rfl) ⟨781268, by rfl⟩ : syracuseStep 1041691 = 1562537) B1562537
theorem B1173199 : Blo 924580 1173199 := bstep (se 1 (by rfl) ⟨879899, by rfl⟩ : syracuseStep 1173199 = 1759799) B1759799
theorem B6776875 : Blo 924580 6776875 := bstep (se 1 (by rfl) ⟨5082656, by rfl⟩ : syracuseStep 6776875 = 10165313) B10165313
theorem B1271899 : Blo 924580 1271899 := bstep (se 1 (by rfl) ⟨953924, by rfl⟩ : syracuseStep 1271899 = 1907849) B1907849
theorem B2747105 : Blo 924580 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B1043815 : Blo 924580 1043815 := bstep (se 1 (by rfl) ⟨782861, by rfl⟩ : syracuseStep 1043815 = 1565723) B1565723
theorem B4222687 : Blo 924580 4222687 := bstep (se 1 (by rfl) ⟨3167015, by rfl⟩ : syracuseStep 4222687 = 6334031) B6334031
theorem B17790515 : Blo 924580 17790515 := bstep (se 1 (by rfl) ⟨13342886, by rfl⟩ : syracuseStep 17790515 = 26685773) B26685773
theorem B5635259 : Blo 924580 5635259 := bstep (se 1 (by rfl) ⟨4226444, by rfl⟩ : syracuseStep 5635259 = 8452889) B8452889
theorem B36143333 : Blo 924580 36143333 := bstep (se 4 (by rfl) ⟨3388437, by rfl⟩ : syracuseStep 36143333 = 6776875) B6776875
theorem B15860123 : Blo 924580 15860123 := bstep (se 1 (by rfl) ⟨11895092, by rfl⟩ : syracuseStep 15860123 = 23790185) B23790185
theorem B53380295 : Blo 924580 53380295 := bstep (se 1 (by rfl) ⟨40035221, by rfl⟩ : syracuseStep 53380295 = 80070443) B80070443
theorem B5277595 : Blo 924580 5277595 := bstep (se 1 (by rfl) ⟨3958196, by rfl⟩ : syracuseStep 5277595 = 7916393) B7916393
theorem B3344573 : Blo 924580 3344573 := bstep (se 3 (by rfl) ⟨627107, by rfl⟩ : syracuseStep 3344573 = 1254215) B1254215
theorem B2787995 : Blo 924580 2787995 := bstep (se 1 (by rfl) ⟨2090996, by rfl⟩ : syracuseStep 2787995 = 4181993) B4181993
theorem B15043963 : Blo 924580 15043963 := bstep (se 1 (by rfl) ⟨11282972, by rfl⟩ : syracuseStep 15043963 = 22565945) B22565945
theorem B2821547 : Blo 924580 2821547 := bstep (se 1 (by rfl) ⟨2116160, by rfl⟩ : syracuseStep 2821547 = 4232321) B4232321
theorem B7049915 : Blo 924580 7049915 := bstep (se 1 (by rfl) ⟨5287436, by rfl⟩ : syracuseStep 7049915 = 10574873) B10574873
theorem B5642855 : Blo 924580 5642855 := bstep (se 1 (by rfl) ⟨4232141, by rfl⟩ : syracuseStep 5642855 = 8464283) B8464283
theorem B924699 : Blo 924580 924699 := bstep (se 1 (by rfl) ⟨693524, by rfl⟩ : syracuseStep 924699 = 1387049) B1387049
theorem B10558835 : Blo 924580 10558835 := bstep (se 1 (by rfl) ⟨7919126, by rfl⟩ : syracuseStep 10558835 = 15838253) B15838253
theorem B925439 : Blo 924580 925439 := bstep (se 1 (by rfl) ⟨694079, by rfl⟩ : syracuseStep 925439 = 1388159) B1388159
theorem B926463 : Blo 924580 926463 := bstep (se 1 (by rfl) ⟨694847, by rfl⟩ : syracuseStep 926463 = 1389695) B1389695
theorem B926687 : Blo 924580 926687 := bstep (se 1 (by rfl) ⟨695015, by rfl⟩ : syracuseStep 926687 = 1390031) B1390031
theorem B5350393 : Blo 924580 5350393 := bstep (se 2 (by rfl) ⟨2006397, by rfl⟩ : syracuseStep 5350393 = 4012795) B4012795
theorem B6759721 : Blo 924580 6759721 := bstep (se 2 (by rfl) ⟨2534895, by rfl⟩ : syracuseStep 6759721 = 5069791) B5069791
theorem B928447 : Blo 924580 928447 := bstep (se 1 (by rfl) ⟨696335, by rfl⟩ : syracuseStep 928447 = 1392671) B1392671
theorem B1387631 : Blo 924580 1387631 := bstep (se 1 (by rfl) ⟨1040723, by rfl⟩ : syracuseStep 1387631 = 2081447) B2081447
theorem B3124439 : Blo 924580 3124439 := bstep (se 1 (by rfl) ⟨2343329, by rfl⟩ : syracuseStep 3124439 = 4686659) B4686659
theorem B4697351 : Blo 924580 4697351 := bstep (se 1 (by rfl) ⟨3523013, by rfl⟩ : syracuseStep 4697351 = 7046027) B7046027
theorem B57093925 : Blo 924580 57093925 := bstep (se 4 (by rfl) ⟨5352555, by rfl⟩ : syracuseStep 57093925 = 10705111) B10705111
theorem B3125303 : Blo 924580 3125303 := bstep (se 1 (by rfl) ⟨2343977, by rfl⟩ : syracuseStep 3125303 = 4687955) B4687955
theorem B1388711 : Blo 924580 1388711 := bstep (se 1 (by rfl) ⟨1041533, by rfl⟩ : syracuseStep 1388711 = 2083067) B2083067
theorem B1388735 : Blo 924580 1388735 := bstep (se 1 (by rfl) ⟨1041551, by rfl⟩ : syracuseStep 1388735 = 2083103) B2083103
theorem B1388921 : Blo 924580 1388921 := bstep (se 2 (by rfl) ⟨520845, by rfl⟩ : syracuseStep 1388921 = 1041691) B1041691
theorem B1389311 : Blo 924580 1389311 := bstep (se 1 (by rfl) ⟨1041983, by rfl⟩ : syracuseStep 1389311 = 2083967) B2083967
theorem B4698971 : Blo 924580 4698971 := bstep (se 1 (by rfl) ⟨3524228, by rfl⟩ : syracuseStep 4698971 = 7048457) B7048457
theorem B3126383 : Blo 924580 3126383 := bstep (se 1 (by rfl) ⟨2344787, by rfl⟩ : syracuseStep 3126383 = 4689575) B4689575
theorem B1390079 : Blo 924580 1390079 := bstep (se 1 (by rfl) ⟨1042559, by rfl⟩ : syracuseStep 1390079 = 2085119) B2085119
theorem B2635517 : Blo 924580 2635517 := bstep (se 3 (by rfl) ⟨494159, by rfl⟩ : syracuseStep 2635517 = 988319) B988319
theorem B1390703 : Blo 924580 1390703 := bstep (se 1 (by rfl) ⟨1043027, by rfl⟩ : syracuseStep 1390703 = 2086055) B2086055
theorem B1390919 : Blo 924580 1390919 := bstep (se 1 (by rfl) ⟨1043189, by rfl⟩ : syracuseStep 1390919 = 2086379) B2086379
theorem B3521495 : Blo 924580 3521495 := bstep (se 1 (by rfl) ⟨2641121, by rfl⟩ : syracuseStep 3521495 = 5282243) B5282243
theorem B1391753 : Blo 924580 1391753 := bstep (se 2 (by rfl) ⟨521907, by rfl⟩ : syracuseStep 1391753 = 1043815) B1043815
theorem B1391867 : Blo 924580 1391867 := bstep (se 1 (by rfl) ⟨1043900, by rfl⟩ : syracuseStep 1391867 = 2087801) B2087801
theorem B2342591 : Blo 924580 2342591 := bstep (se 1 (by rfl) ⟨1756943, by rfl⟩ : syracuseStep 2342591 = 3513887) B3513887
theorem B1392767 : Blo 924580 1392767 := bstep (se 1 (by rfl) ⟨1044575, by rfl⟩ : syracuseStep 1392767 = 2089151) B2089151
theorem B2081591 : Blo 924580 2081591 := bstep (se 1 (by rfl) ⟨1561193, by rfl⟩ : syracuseStep 2081591 = 3122387) B3122387
theorem B7914617 : Blo 924580 7914617 := bstep (se 2 (by rfl) ⟨2967981, by rfl⟩ : syracuseStep 7914617 = 5935963) B5935963
theorem B2083193 : Blo 924580 2083193 := bstep (se 2 (by rfl) ⟨781197, by rfl⟩ : syracuseStep 2083193 = 1562395) B1562395
theorem B10013651 : Blo 924580 10013651 := bstep (se 1 (by rfl) ⟨7510238, by rfl⟩ : syracuseStep 10013651 = 15020477) B15020477
theorem B2642557 : Blo 924580 2642557 := bstep (se 3 (by rfl) ⟨495479, by rfl⟩ : syracuseStep 2642557 = 990959) B990959
theorem B3756839 : Blo 924580 3756839 := bstep (se 1 (by rfl) ⟨2817629, by rfl⟩ : syracuseStep 3756839 = 5635259) B5635259
theorem B57005045 : Blo 924580 57005045 := bstep (se 5 (by rfl) ⟨2672111, by rfl⟩ : syracuseStep 57005045 = 5344223) B5344223
theorem B1561835 : Blo 924580 1561835 := bstep (se 1 (by rfl) ⟨1171376, by rfl⟩ : syracuseStep 1561835 = 2342753) B2342753
theorem B5625283 : Blo 924580 5625283 := bstep (se 1 (by rfl) ⟨4218962, by rfl⟩ : syracuseStep 5625283 = 8437925) B8437925
theorem B1758827 : Blo 924580 1758827 := bstep (se 1 (by rfl) ⟨1319120, by rfl⟩ : syracuseStep 1758827 = 2638241) B2638241
theorem B2086559 : Blo 924580 2086559 := bstep (se 1 (by rfl) ⟨1564919, by rfl⟩ : syracuseStep 2086559 = 3129839) B3129839
theorem B7526135 : Blo 924580 7526135 := bstep (se 1 (by rfl) ⟨5644601, by rfl⟩ : syracuseStep 7526135 = 11289203) B11289203
theorem B1563239 : Blo 924580 1563239 := bstep (se 1 (by rfl) ⟨1172429, by rfl⟩ : syracuseStep 1563239 = 2344859) B2344859
theorem B2350073 : Blo 924580 2350073 := bstep (se 2 (by rfl) ⟨881277, by rfl⟩ : syracuseStep 2350073 = 1762555) B1762555
theorem B42392801 : Blo 924580 42392801 := bstep (se 2 (by rfl) ⟨15897300, by rfl⟩ : syracuseStep 42392801 = 31794601) B31794601
theorem B2088503 : Blo 924580 2088503 := bstep (se 1 (by rfl) ⟨1566377, by rfl⟩ : syracuseStep 2088503 = 3132755) B3132755
theorem B1564265 : Blo 924580 1564265 := bstep (se 2 (by rfl) ⟨586599, by rfl⟩ : syracuseStep 1564265 = 1173199) B1173199
theorem B15851375 : Blo 924580 15851375 := bstep (se 1 (by rfl) ⟨11888531, by rfl⟩ : syracuseStep 15851375 = 23777063) B23777063
theorem B1695865 : Blo 924580 1695865 := bstep (se 2 (by rfl) ⟨635949, by rfl⟩ : syracuseStep 1695865 = 1271899) B1271899
theorem B2089223 : Blo 924580 2089223 := bstep (se 1 (by rfl) ⟨1566917, by rfl⟩ : syracuseStep 2089223 = 3133835) B3133835
theorem B3957103 : Blo 924580 3957103 := bstep (se 1 (by rfl) ⟨2967827, by rfl⟩ : syracuseStep 3957103 = 5935655) B5935655
theorem B1761887 : Blo 924580 1761887 := bstep (se 1 (by rfl) ⟨1321415, by rfl⟩ : syracuseStep 1761887 = 2642831) B2642831
theorem B2974441 : Blo 924580 2974441 := bstep (se 2 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 2974441 = 2230831) B2230831
theorem B5268347 : Blo 924580 5268347 := bstep (se 1 (by rfl) ⟨3951260, by rfl⟩ : syracuseStep 5268347 = 7902521) B7902521
theorem B3958591 : Blo 924580 3958591 := bstep (se 1 (by rfl) ⟨2968943, by rfl⟩ : syracuseStep 3958591 = 5937887) B5937887
theorem B5269373 : Blo 924580 5269373 := bstep (se 3 (by rfl) ⟨988007, by rfl⟩ : syracuseStep 5269373 = 1976015) B1976015
theorem B5630249 : Blo 924580 5630249 := bstep (se 2 (by rfl) ⟨2111343, by rfl⟩ : syracuseStep 5630249 = 4222687) B4222687
theorem B35547497 : Blo 924580 35547497 := bstep (se 2 (by rfl) ⟨13330311, by rfl⟩ : syracuseStep 35547497 = 26660623) B26660623
theorem B8448731 : Blo 924580 8448731 := bstep (se 1 (by rfl) ⟨6336548, by rfl⟩ : syracuseStep 8448731 = 12673097) B12673097
theorem B1831403 : Blo 924580 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B5273039 : Blo 924580 5273039 := bstep (se 1 (by rfl) ⟨3954779, by rfl⟩ : syracuseStep 5273039 = 7909559) B7909559
theorem B5929199 : Blo 924580 5929199 := bstep (se 1 (by rfl) ⟨4446899, by rfl⟩ : syracuseStep 5929199 = 8893799) B8893799
theorem B11860343 : Blo 924580 11860343 := bstep (se 1 (by rfl) ⟨8895257, by rfl⟩ : syracuseStep 11860343 = 17790515) B17790515
theorem B634158071 : Blo 924580 634158071 := bstep (se 1 (by rfl) ⟨475618553, by rfl⟩ : syracuseStep 634158071 = 951237107) B951237107
theorem B10681469 : Blo 924580 10681469 := bstep (se 3 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 10681469 = 4005551) B4005551
theorem B1670399 : Blo 924580 1670399 := bstep (se 1 (by rfl) ⟨1252799, by rfl⟩ : syracuseStep 1670399 = 2505599) B2505599
theorem B2261153 : Blo 924580 2261153 := bstep (se 2 (by rfl) ⟨847932, by rfl⟩ : syracuseStep 2261153 = 1695865) B1695865
theorem B5276137 : Blo 924580 5276137 := bstep (se 2 (by rfl) ⟨1978551, by rfl⟩ : syracuseStep 5276137 = 3957103) B3957103
theorem B5276411 : Blo 924580 5276411 := bstep (se 1 (by rfl) ⟨3957308, by rfl⟩ : syracuseStep 5276411 = 7914617) B7914617
theorem B35586863 : Blo 924580 35586863 := bstep (se 1 (by rfl) ⟨26690147, by rfl⟩ : syracuseStep 35586863 = 53380295) B53380295
theorem B3965921 : Blo 924580 3965921 := bstep (se 2 (by rfl) ⟨1487220, by rfl⟩ : syracuseStep 3965921 = 2974441) B2974441
theorem B2229715 : Blo 924580 2229715 := bstep (se 1 (by rfl) ⟨1672286, by rfl⟩ : syracuseStep 2229715 = 3344573) B3344573
theorem B9012961 : Blo 924580 9012961 := bstep (se 2 (by rfl) ⟨3379860, by rfl⟩ : syracuseStep 9012961 = 6759721) B6759721
theorem B5278121 : Blo 924580 5278121 := bstep (se 2 (by rfl) ⟨1979295, by rfl⟩ : syracuseStep 5278121 = 3958591) B3958591
theorem B5017423 : Blo 924580 5017423 := bstep (se 1 (by rfl) ⟨3763067, by rfl⟩ : syracuseStep 5017423 = 7526135) B7526135
theorem B20058617 : Blo 924580 20058617 := bstep (se 2 (by rfl) ⟨7521981, by rfl⟩ : syracuseStep 20058617 = 15043963) B15043963
theorem B76125233 : Blo 924580 76125233 := bstep (se 2 (by rfl) ⟨28546962, by rfl⟩ : syracuseStep 76125233 = 57093925) B57093925
theorem B3512231 : Blo 924580 3512231 := bstep (se 1 (by rfl) ⟨2634173, by rfl⟩ : syracuseStep 3512231 = 5268347) B5268347
theorem B15013997 : Blo 924580 15013997 := bstep (se 3 (by rfl) ⟨2815124, by rfl⟩ : syracuseStep 15013997 = 5630249) B5630249
theorem B3512915 : Blo 924580 3512915 := bstep (se 1 (by rfl) ⟨2634686, by rfl⟩ : syracuseStep 3512915 = 5269373) B5269373
theorem B23698331 : Blo 924580 23698331 := bstep (se 1 (by rfl) ⟨17773748, by rfl⟩ : syracuseStep 23698331 = 35547497) B35547497
theorem B925087 : Blo 924580 925087 := bstep (se 1 (by rfl) ⟨693815, by rfl⟩ : syracuseStep 925087 = 1387631) B1387631
theorem B925807 : Blo 924580 925807 := bstep (se 1 (by rfl) ⟨694355, by rfl⟩ : syracuseStep 925807 = 1388711) B1388711
theorem B925823 : Blo 924580 925823 := bstep (se 1 (by rfl) ⟨694367, by rfl⟩ : syracuseStep 925823 = 1388735) B1388735
theorem B925947 : Blo 924580 925947 := bstep (se 1 (by rfl) ⟨694460, by rfl⟩ : syracuseStep 925947 = 1388921) B1388921
theorem B1220935 : Blo 924580 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B926207 : Blo 924580 926207 := bstep (se 1 (by rfl) ⟨694655, by rfl⟩ : syracuseStep 926207 = 1389311) B1389311
theorem B3515359 : Blo 924580 3515359 := bstep (se 1 (by rfl) ⟨2636519, by rfl⟩ : syracuseStep 3515359 = 5273039) B5273039
theorem B926719 : Blo 924580 926719 := bstep (se 1 (by rfl) ⟨695039, by rfl⟩ : syracuseStep 926719 = 1390079) B1390079
theorem B927135 : Blo 924580 927135 := bstep (se 1 (by rfl) ⟨695351, by rfl⟩ : syracuseStep 927135 = 1390703) B1390703
theorem B927279 : Blo 924580 927279 := bstep (se 1 (by rfl) ⟨695459, by rfl⟩ : syracuseStep 927279 = 1390919) B1390919
theorem B7906895 : Blo 924580 7906895 := bstep (se 1 (by rfl) ⟨5930171, by rfl⟩ : syracuseStep 7906895 = 11860343) B11860343
theorem B7120979 : Blo 924580 7120979 := bstep (se 1 (by rfl) ⟨5340734, by rfl⟩ : syracuseStep 7120979 = 10681469) B10681469
theorem B927835 : Blo 924580 927835 := bstep (se 1 (by rfl) ⟨695876, by rfl⟩ : syracuseStep 927835 = 1391753) B1391753
theorem B927911 : Blo 924580 927911 := bstep (se 1 (by rfl) ⟨695933, by rfl⟩ : syracuseStep 927911 = 1391867) B1391867
theorem B928511 : Blo 924580 928511 := bstep (se 1 (by rfl) ⟨696383, by rfl⟩ : syracuseStep 928511 = 1392767) B1392767
theorem B24095555 : Blo 924580 24095555 := bstep (se 1 (by rfl) ⟨18071666, by rfl⟩ : syracuseStep 24095555 = 36143333) B36143333
theorem B1387727 : Blo 924580 1387727 := bstep (se 1 (by rfl) ⟨1040795, by rfl⟩ : syracuseStep 1387727 = 2081591) B2081591
theorem B1388795 : Blo 924580 1388795 := bstep (se 1 (by rfl) ⟨1041596, by rfl⟩ : syracuseStep 1388795 = 2083193) B2083193
theorem B1881031 : Blo 924580 1881031 := bstep (se 1 (by rfl) ⟨1410773, by rfl⟩ : syracuseStep 1881031 = 2821547) B2821547
theorem B4699943 : Blo 924580 4699943 := bstep (se 1 (by rfl) ⟨3524957, by rfl⟩ : syracuseStep 4699943 = 7049915) B7049915
theorem B1391039 : Blo 924580 1391039 := bstep (se 1 (by rfl) ⟨1043279, by rfl⟩ : syracuseStep 1391039 = 2086559) B2086559
theorem B7028045 : Blo 924580 7028045 := bstep (se 3 (by rfl) ⟨1317758, by rfl⟩ : syracuseStep 7028045 = 2635517) B2635517
theorem B28261867 : Blo 924580 28261867 := bstep (se 1 (by rfl) ⟨21196400, by rfl⟩ : syracuseStep 28261867 = 42392801) B42392801
theorem B1392335 : Blo 924580 1392335 := bstep (se 1 (by rfl) ⟨1044251, by rfl⟩ : syracuseStep 1392335 = 2088503) B2088503
theorem B10567583 : Blo 924580 10567583 := bstep (se 1 (by rfl) ⟨7925687, by rfl⟩ : syracuseStep 10567583 = 15851375) B15851375
theorem B1392815 : Blo 924580 1392815 := bstep (se 1 (by rfl) ⟨1044611, by rfl⟩ : syracuseStep 1392815 = 2089223) B2089223
theorem B3523409 : Blo 924580 3523409 := bstep (se 2 (by rfl) ⟨1321278, by rfl⟩ : syracuseStep 3523409 = 2642557) B2642557
theorem B2082959 : Blo 924580 2082959 := bstep (se 1 (by rfl) ⟨1562219, by rfl⟩ : syracuseStep 2082959 = 3124439) B3124439
theorem B3131567 : Blo 924580 3131567 := bstep (se 1 (by rfl) ⟨2348675, by rfl⟩ : syracuseStep 3131567 = 4697351) B4697351
theorem B2083535 : Blo 924580 2083535 := bstep (se 1 (by rfl) ⟨1562651, by rfl⟩ : syracuseStep 2083535 = 3125303) B3125303
theorem B3132647 : Blo 924580 3132647 := bstep (se 1 (by rfl) ⟨2349485, by rfl⟩ : syracuseStep 3132647 = 4698971) B4698971
theorem B2084255 : Blo 924580 2084255 := bstep (se 1 (by rfl) ⟨1563191, by rfl⟩ : syracuseStep 2084255 = 3126383) B3126383
theorem B3952799 : Blo 924580 3952799 := bstep (se 1 (by rfl) ⟨2964599, by rfl⟩ : syracuseStep 3952799 = 5929199) B5929199
theorem B2347663 : Blo 924580 2347663 := bstep (se 1 (by rfl) ⟨1760747, by rfl⟩ : syracuseStep 2347663 = 3521495) B3521495
theorem B1561727 : Blo 924580 1561727 := bstep (se 1 (by rfl) ⟨1171295, by rfl⟩ : syracuseStep 1561727 = 2342591) B2342591
theorem B10573415 : Blo 924580 10573415 := bstep (se 1 (by rfl) ⟨7930061, by rfl⟩ : syracuseStep 10573415 = 15860123) B15860123
theorem B1858663 : Blo 924580 1858663 := bstep (se 1 (by rfl) ⟨1393997, by rfl⟩ : syracuseStep 1858663 = 2787995) B2787995
theorem B6675767 : Blo 924580 6675767 := bstep (se 1 (by rfl) ⟨5006825, by rfl⟩ : syracuseStep 6675767 = 10013651) B10013651
theorem B10018237 : Blo 924580 10018237 := bstep (se 3 (by rfl) ⟨1878419, by rfl⟩ : syracuseStep 10018237 = 3756839) B3756839
theorem B7036793 : Blo 924580 7036793 := bstep (se 2 (by rfl) ⟨2638797, by rfl⟩ : syracuseStep 7036793 = 5277595) B5277595
theorem B38003363 : Blo 924580 38003363 := bstep (se 1 (by rfl) ⟨28502522, by rfl⟩ : syracuseStep 38003363 = 57005045) B57005045
theorem B1041223 : Blo 924580 1041223 := bstep (se 1 (by rfl) ⟨780917, by rfl⟩ : syracuseStep 1041223 = 1561835) B1561835
theorem B1172551 : Blo 924580 1172551 := bstep (se 1 (by rfl) ⟨879413, by rfl⟩ : syracuseStep 1172551 = 1758827) B1758827
theorem B1042159 : Blo 924580 1042159 := bstep (se 1 (by rfl) ⟨781619, by rfl⟩ : syracuseStep 1042159 = 1563239) B1563239
theorem B3761903 : Blo 924580 3761903 := bstep (se 1 (by rfl) ⟨2821427, by rfl⟩ : syracuseStep 3761903 = 5642855) B5642855
theorem B1566715 : Blo 924580 1566715 := bstep (se 1 (by rfl) ⟨1175036, by rfl⟩ : syracuseStep 1566715 = 2350073) B2350073
theorem B7039223 : Blo 924580 7039223 := bstep (se 1 (by rfl) ⟨5279417, by rfl⟩ : syracuseStep 7039223 = 10558835) B10558835
theorem B1042843 : Blo 924580 1042843 := bstep (se 1 (by rfl) ⟨782132, by rfl⟩ : syracuseStep 1042843 = 1564265) B1564265
theorem B28535429 : Blo 924580 28535429 := bstep (se 4 (by rfl) ⟨2675196, by rfl⟩ : syracuseStep 28535429 = 5350393) B5350393
theorem B1174591 : Blo 924580 1174591 := bstep (se 1 (by rfl) ⟨880943, by rfl⟩ : syracuseStep 1174591 = 1761887) B1761887
theorem B5632487 : Blo 924580 5632487 := bstep (se 1 (by rfl) ⟨4224365, by rfl⟩ : syracuseStep 5632487 = 8448731) B8448731
theorem B7500377 : Blo 924580 7500377 := bstep (se 2 (by rfl) ⟨2812641, by rfl⟩ : syracuseStep 7500377 = 5625283) B5625283
theorem B422772047 : Blo 924580 422772047 := bstep (se 1 (by rfl) ⟨317079035, by rfl⟩ : syracuseStep 422772047 = 634158071) B634158071
theorem B1113599 : Blo 924580 1113599 := bstep (se 1 (by rfl) ⟨835199, by rfl⟩ : syracuseStep 1113599 = 1670399) B1670399
theorem B6029741 : Blo 924580 6029741 := bstep (se 3 (by rfl) ⟨1130576, by rfl⟩ : syracuseStep 6029741 = 2261153) B2261153
theorem B23724575 : Blo 924580 23724575 := bstep (se 1 (by rfl) ⟨17793431, by rfl⟩ : syracuseStep 23724575 = 35586863) B35586863
theorem B4687145 : Blo 924580 4687145 := bstep (se 2 (by rfl) ⟨1757679, by rfl⟩ : syracuseStep 4687145 = 3515359) B3515359
theorem B13372411 : Blo 924580 13372411 := bstep (se 1 (by rfl) ⟨10029308, by rfl⟩ : syracuseStep 13372411 = 20058617) B20058617
theorem B7048943 : Blo 924580 7048943 := bstep (se 1 (by rfl) ⟨5286707, by rfl⟩ : syracuseStep 7048943 = 10573415) B10573415
theorem B15798887 : Blo 924580 15798887 := bstep (se 1 (by rfl) ⟨11849165, by rfl⟩ : syracuseStep 15798887 = 23698331) B23698331
theorem B6689897 : Blo 924580 6689897 := bstep (se 2 (by rfl) ⟨2508711, by rfl⟩ : syracuseStep 6689897 = 5017423) B5017423
theorem B4691195 : Blo 924580 4691195 := bstep (se 1 (by rfl) ⟨3518396, by rfl⟩ : syracuseStep 4691195 = 7036793) B7036793
theorem B25335575 : Blo 924580 25335575 := bstep (se 1 (by rfl) ⟨19001681, by rfl⟩ : syracuseStep 25335575 = 38003363) B38003363
theorem B4692815 : Blo 924580 4692815 := bstep (se 1 (by rfl) ⟨3519611, by rfl⟩ : syracuseStep 4692815 = 7039223) B7039223
theorem B16063703 : Blo 924580 16063703 := bstep (se 1 (by rfl) ⟨12047777, by rfl⟩ : syracuseStep 16063703 = 24095555) B24095555
theorem B925151 : Blo 924580 925151 := bstep (se 1 (by rfl) ⟨693863, by rfl⟩ : syracuseStep 925151 = 1387727) B1387727
theorem B925863 : Blo 924580 925863 := bstep (se 1 (by rfl) ⟨694397, by rfl⟩ : syracuseStep 925863 = 1388795) B1388795
theorem B927359 : Blo 924580 927359 := bstep (se 1 (by rfl) ⟨695519, by rfl⟩ : syracuseStep 927359 = 1391039) B1391039
theorem B281848031 : Blo 924580 281848031 := bstep (se 1 (by rfl) ⟨211386023, by rfl⟩ : syracuseStep 281848031 = 422772047) B422772047
theorem B928223 : Blo 924580 928223 := bstep (se 1 (by rfl) ⟨696167, by rfl⟩ : syracuseStep 928223 = 1392335) B1392335
theorem B928543 : Blo 924580 928543 := bstep (se 1 (by rfl) ⟨696407, by rfl⟩ : syracuseStep 928543 = 1392815) B1392815
theorem B3517607 : Blo 924580 3517607 := bstep (se 1 (by rfl) ⟨2638205, by rfl⟩ : syracuseStep 3517607 = 5276411) B5276411
theorem B1388297 : Blo 924580 1388297 := bstep (se 2 (by rfl) ⟨520611, by rfl⟩ : syracuseStep 1388297 = 1041223) B1041223
theorem B1388639 : Blo 924580 1388639 := bstep (se 1 (by rfl) ⟨1041479, by rfl⟩ : syracuseStep 1388639 = 2082959) B2082959
theorem B20001005 : Blo 924580 20001005 := bstep (se 3 (by rfl) ⟨3750188, by rfl⟩ : syracuseStep 20001005 = 7500377) B7500377
theorem B3518747 : Blo 924580 3518747 := bstep (se 1 (by rfl) ⟨2639060, by rfl⟩ : syracuseStep 3518747 = 5278121) B5278121
theorem B1389023 : Blo 924580 1389023 := bstep (se 1 (by rfl) ⟨1041767, by rfl⟩ : syracuseStep 1389023 = 2083535) B2083535
theorem B1389503 : Blo 924580 1389503 := bstep (se 1 (by rfl) ⟨1042127, by rfl⟩ : syracuseStep 1389503 = 2084255) B2084255
theorem B1389545 : Blo 924580 1389545 := bstep (se 2 (by rfl) ⟨521079, by rfl⟩ : syracuseStep 1389545 = 1042159) B1042159
theorem B2635199 : Blo 924580 2635199 := bstep (se 1 (by rfl) ⟨1976399, by rfl⟩ : syracuseStep 2635199 = 3952799) B3952799
theorem B1390457 : Blo 924580 1390457 := bstep (se 2 (by rfl) ⟨521421, by rfl⟩ : syracuseStep 1390457 = 1042843) B1042843
theorem B2341487 : Blo 924580 2341487 := bstep (se 1 (by rfl) ⟨1756115, by rfl⟩ : syracuseStep 2341487 = 3512231) B3512231
theorem B10009331 : Blo 924580 10009331 := bstep (se 1 (by rfl) ⟨7506998, by rfl⟩ : syracuseStep 10009331 = 15013997) B15013997
theorem B2341943 : Blo 924580 2341943 := bstep (se 1 (by rfl) ⟨1756457, by rfl⟩ : syracuseStep 2341943 = 3512915) B3512915
theorem B3130217 : Blo 924580 3130217 := bstep (se 2 (by rfl) ⟨1173831, by rfl⟩ : syracuseStep 3130217 = 2347663) B2347663
theorem B2507935 : Blo 924580 2507935 := bstep (se 1 (by rfl) ⟨1880951, by rfl⟩ : syracuseStep 2507935 = 3761903) B3761903
theorem B2508041 : Blo 924580 2508041 := bstep (se 2 (by rfl) ⟨940515, by rfl⟩ : syracuseStep 2508041 = 1881031) B1881031
theorem B19023619 : Blo 924580 19023619 := bstep (se 1 (by rfl) ⟨14267714, by rfl⟩ : syracuseStep 19023619 = 28535429) B28535429
theorem B3754991 : Blo 924580 3754991 := bstep (se 1 (by rfl) ⟨2816243, by rfl⟩ : syracuseStep 3754991 = 5632487) B5632487
theorem B3133295 : Blo 924580 3133295 := bstep (se 1 (by rfl) ⟨2349971, by rfl⟩ : syracuseStep 3133295 = 4699943) B4699943
theorem B2969597 : Blo 924580 2969597 := bstep (se 3 (by rfl) ⟨556799, by rfl⟩ : syracuseStep 2969597 = 1113599) B1113599
theorem B2478217 : Blo 924580 2478217 := bstep (se 2 (by rfl) ⟨929331, by rfl⟩ : syracuseStep 2478217 = 1858663) B1858663
theorem B13357649 : Blo 924580 13357649 := bstep (se 2 (by rfl) ⟨5009118, by rfl⟩ : syracuseStep 13357649 = 10018237) B10018237
theorem B1627913 : Blo 924580 1627913 := bstep (se 2 (by rfl) ⟨610467, by rfl⟩ : syracuseStep 1627913 = 1220935) B1220935
theorem B2348939 : Blo 924580 2348939 := bstep (se 1 (by rfl) ⟨1761704, by rfl⟩ : syracuseStep 2348939 = 3523409) B3523409
theorem B7034849 : Blo 924580 7034849 := bstep (se 2 (by rfl) ⟨2638068, by rfl⟩ : syracuseStep 7034849 = 5276137) B5276137
theorem B2643947 : Blo 924580 2643947 := bstep (se 1 (by rfl) ⟨1982960, by rfl⟩ : syracuseStep 2643947 = 3965921) B3965921
theorem B1563401 : Blo 924580 1563401 := bstep (se 2 (by rfl) ⟨586275, by rfl⟩ : syracuseStep 1563401 = 1172551) B1172551
theorem B2087711 : Blo 924580 2087711 := bstep (se 1 (by rfl) ⟨1565783, by rfl⟩ : syracuseStep 2087711 = 3131567) B3131567
theorem B2972953 : Blo 924580 2972953 := bstep (se 2 (by rfl) ⟨1114857, by rfl⟩ : syracuseStep 2972953 = 2229715) B2229715
theorem B2088431 : Blo 924580 2088431 := bstep (se 1 (by rfl) ⟨1566323, by rfl⟩ : syracuseStep 2088431 = 3132647) B3132647
theorem B12017281 : Blo 924580 12017281 := bstep (se 2 (by rfl) ⟨4506480, by rfl⟩ : syracuseStep 12017281 = 9012961) B9012961
theorem B2088953 : Blo 924580 2088953 := bstep (se 2 (by rfl) ⟨783357, by rfl⟩ : syracuseStep 2088953 = 1566715) B1566715
theorem B50750155 : Blo 924580 50750155 := bstep (se 1 (by rfl) ⟨38062616, by rfl⟩ : syracuseStep 50750155 = 76125233) B76125233
theorem B1041151 : Blo 924580 1041151 := bstep (se 1 (by rfl) ⟨780863, by rfl⟩ : syracuseStep 1041151 = 1561727) B1561727
theorem B1566121 : Blo 924580 1566121 := bstep (se 2 (by rfl) ⟨587295, by rfl⟩ : syracuseStep 1566121 = 1174591) B1174591
theorem B4450511 : Blo 924580 4450511 := bstep (se 1 (by rfl) ⟨3337883, by rfl⟩ : syracuseStep 4450511 = 6675767) B6675767
theorem B5271263 : Blo 924580 5271263 := bstep (se 1 (by rfl) ⟨3953447, by rfl⟩ : syracuseStep 5271263 = 7906895) B7906895
theorem B4747319 : Blo 924580 4747319 := bstep (se 1 (by rfl) ⟨3560489, by rfl⟩ : syracuseStep 4747319 = 7120979) B7120979
theorem B37682489 : Blo 924580 37682489 := bstep (se 2 (by rfl) ⟨14130933, by rfl⟩ : syracuseStep 37682489 = 28261867) B28261867
theorem B4685363 : Blo 924580 4685363 := bstep (se 1 (by rfl) ⟨3514022, by rfl⟩ : syracuseStep 4685363 = 7028045) B7028045
theorem B7045055 : Blo 924580 7045055 := bstep (se 1 (by rfl) ⟨5283791, by rfl⟩ : syracuseStep 7045055 = 10567583) B10567583
theorem B67666873 : Blo 924580 67666873 := bstep (se 2 (by rfl) ⟨25375077, by rfl⟩ : syracuseStep 67666873 = 50750155) B50750155
theorem B3343913 : Blo 924580 3343913 := bstep (se 2 (by rfl) ⟨1253967, by rfl⟩ : syracuseStep 3343913 = 2507935) B2507935
theorem B25364825 : Blo 924580 25364825 := bstep (se 2 (by rfl) ⟨9511809, by rfl⟩ : syracuseStep 25364825 = 19023619) B19023619
theorem B6688109 : Blo 924580 6688109 := bstep (se 3 (by rfl) ⟨1254020, by rfl⟩ : syracuseStep 6688109 = 2508041) B2508041
theorem B4459931 : Blo 924580 4459931 := bstep (se 1 (by rfl) ⟨3344948, by rfl⟩ : syracuseStep 4459931 = 6689897) B6689897
theorem B1085275 : Blo 924580 1085275 := bstep (se 1 (by rfl) ⟨813956, by rfl⟩ : syracuseStep 1085275 = 1627913) B1627913
theorem B4689899 : Blo 924580 4689899 := bstep (se 1 (by rfl) ⟨3517424, by rfl⟩ : syracuseStep 4689899 = 7034849) B7034849
theorem B17829881 : Blo 924580 17829881 := bstep (se 2 (by rfl) ⟨6686205, by rfl⟩ : syracuseStep 17829881 = 13372411) B13372411
theorem B11868029 : Blo 924580 11868029 := bstep (se 3 (by rfl) ⟨2225255, by rfl⟩ : syracuseStep 11868029 = 4450511) B4450511
theorem B187898687 : Blo 924580 187898687 := bstep (se 1 (by rfl) ⟨140924015, by rfl⟩ : syracuseStep 187898687 = 281848031) B281848031
theorem B3514175 : Blo 924580 3514175 := bstep (se 1 (by rfl) ⟨2635631, by rfl⟩ : syracuseStep 3514175 = 5271263) B5271263
theorem B925531 : Blo 924580 925531 := bstep (se 1 (by rfl) ⟨694148, by rfl⟩ : syracuseStep 925531 = 1388297) B1388297
theorem B925759 : Blo 924580 925759 := bstep (se 1 (by rfl) ⟨694319, by rfl⟩ : syracuseStep 925759 = 1388639) B1388639
theorem B926015 : Blo 924580 926015 := bstep (se 1 (by rfl) ⟨694511, by rfl⟩ : syracuseStep 926015 = 1389023) B1389023
theorem B926335 : Blo 924580 926335 := bstep (se 1 (by rfl) ⟨694751, by rfl⟩ : syracuseStep 926335 = 1389503) B1389503
theorem B926363 : Blo 924580 926363 := bstep (se 1 (by rfl) ⟨694772, by rfl⟩ : syracuseStep 926363 = 1389545) B1389545
theorem B926971 : Blo 924580 926971 := bstep (se 1 (by rfl) ⟨695228, by rfl⟩ : syracuseStep 926971 = 1390457) B1390457
theorem B3123575 : Blo 924580 3123575 := bstep (se 1 (by rfl) ⟨2342681, by rfl⟩ : syracuseStep 3123575 = 4685363) B4685363
theorem B4696703 : Blo 924580 4696703 := bstep (se 1 (by rfl) ⟨3522527, by rfl⟩ : syracuseStep 4696703 = 7045055) B7045055
theorem B3124763 : Blo 924580 3124763 := bstep (se 1 (by rfl) ⟨2343572, by rfl⟩ : syracuseStep 3124763 = 4687145) B4687145
theorem B1388201 : Blo 924580 1388201 := bstep (se 2 (by rfl) ⟨520575, by rfl⟩ : syracuseStep 1388201 = 1041151) B1041151
theorem B2503327 : Blo 924580 2503327 := bstep (se 1 (by rfl) ⟨1877495, by rfl⟩ : syracuseStep 2503327 = 3754991) B3754991
theorem B4699295 : Blo 924580 4699295 := bstep (se 1 (by rfl) ⟨3524471, by rfl⟩ : syracuseStep 4699295 = 7048943) B7048943
theorem B1979731 : Blo 924580 1979731 := bstep (se 1 (by rfl) ⟨1484798, by rfl⟩ : syracuseStep 1979731 = 2969597) B2969597
theorem B52868629 : Blo 924580 52868629 := bstep (se 6 (by rfl) ⟨1239108, by rfl⟩ : syracuseStep 52868629 = 2478217) B2478217
theorem B10532591 : Blo 924580 10532591 := bstep (se 1 (by rfl) ⟨7899443, by rfl⟩ : syracuseStep 10532591 = 15798887) B15798887
theorem B3127463 : Blo 924580 3127463 := bstep (se 1 (by rfl) ⟨2345597, by rfl⟩ : syracuseStep 3127463 = 4691195) B4691195
theorem B16890383 : Blo 924580 16890383 := bstep (se 1 (by rfl) ⟨12667787, by rfl⟩ : syracuseStep 16890383 = 25335575) B25335575
theorem B1391807 : Blo 924580 1391807 := bstep (se 1 (by rfl) ⟨1043855, by rfl⟩ : syracuseStep 1391807 = 2087711) B2087711
theorem B3128543 : Blo 924580 3128543 := bstep (se 1 (by rfl) ⟨2346407, by rfl⟩ : syracuseStep 3128543 = 4692815) B4692815
theorem B1392287 : Blo 924580 1392287 := bstep (se 1 (by rfl) ⟨1044215, by rfl⟩ : syracuseStep 1392287 = 2088431) B2088431
theorem B1392635 : Blo 924580 1392635 := bstep (se 1 (by rfl) ⟨1044476, by rfl⟩ : syracuseStep 1392635 = 2088953) B2088953
theorem B2345071 : Blo 924580 2345071 := bstep (se 1 (by rfl) ⟨1758803, by rfl⟩ : syracuseStep 2345071 = 3517607) B3517607
theorem B3164879 : Blo 924580 3164879 := bstep (se 1 (by rfl) ⟨2373659, by rfl⟩ : syracuseStep 3164879 = 4747319) B4747319
theorem B2345831 : Blo 924580 2345831 := bstep (se 1 (by rfl) ⟨1759373, by rfl⟩ : syracuseStep 2345831 = 3518747) B3518747
theorem B1756799 : Blo 924580 1756799 := bstep (se 1 (by rfl) ⟨1317599, by rfl⟩ : syracuseStep 1756799 = 2635199) B2635199
theorem B1560991 : Blo 924580 1560991 := bstep (se 1 (by rfl) ⟨1170743, by rfl⟩ : syracuseStep 1560991 = 2341487) B2341487
theorem B6672887 : Blo 924580 6672887 := bstep (se 1 (by rfl) ⟨5004665, by rfl⟩ : syracuseStep 6672887 = 10009331) B10009331
theorem B1561295 : Blo 924580 1561295 := bstep (se 1 (by rfl) ⟨1170971, by rfl⟩ : syracuseStep 1561295 = 2341943) B2341943
theorem B25121659 : Blo 924580 25121659 := bstep (se 1 (by rfl) ⟨18841244, by rfl⟩ : syracuseStep 25121659 = 37682489) B37682489
theorem B4019827 : Blo 924580 4019827 := bstep (se 1 (by rfl) ⟨3014870, by rfl⟩ : syracuseStep 4019827 = 6029741) B6029741
theorem B15816383 : Blo 924580 15816383 := bstep (se 1 (by rfl) ⟨11862287, by rfl⟩ : syracuseStep 15816383 = 23724575) B23724575
theorem B2086811 : Blo 924580 2086811 := bstep (se 1 (by rfl) ⟨1565108, by rfl⟩ : syracuseStep 2086811 = 3130217) B3130217
theorem B2088161 : Blo 924580 2088161 := bstep (se 2 (by rfl) ⟨783060, by rfl⟩ : syracuseStep 2088161 = 1566121) B1566121
theorem B2088863 : Blo 924580 2088863 := bstep (se 1 (by rfl) ⟨1566647, by rfl⟩ : syracuseStep 2088863 = 3133295) B3133295
theorem B8905099 : Blo 924580 8905099 := bstep (se 1 (by rfl) ⟨6678824, by rfl⟩ : syracuseStep 8905099 = 13357649) B13357649
theorem B1565959 : Blo 924580 1565959 := bstep (se 1 (by rfl) ⟨1174469, by rfl⟩ : syracuseStep 1565959 = 2348939) B2348939
theorem B1762631 : Blo 924580 1762631 := bstep (se 1 (by rfl) ⟨1321973, by rfl⟩ : syracuseStep 1762631 = 2643947) B2643947
theorem B1042267 : Blo 924580 1042267 := bstep (se 1 (by rfl) ⟨781700, by rfl⟩ : syracuseStep 1042267 = 1563401) B1563401
theorem B10709135 : Blo 924580 10709135 := bstep (se 1 (by rfl) ⟨8031851, by rfl⟩ : syracuseStep 10709135 = 16063703) B16063703
theorem B15855749 : Blo 924580 15855749 := bstep (se 4 (by rfl) ⟨1486476, by rfl⟩ : syracuseStep 15855749 = 2972953) B2972953
theorem B13334003 : Blo 924580 13334003 := bstep (se 1 (by rfl) ⟨10000502, by rfl⟩ : syracuseStep 13334003 = 20001005) B20001005
theorem B16023041 : Blo 924580 16023041 := bstep (se 2 (by rfl) ⟨6008640, by rfl⟩ : syracuseStep 16023041 = 12017281) B12017281
theorem B2229275 : Blo 924580 2229275 := bstep (se 1 (by rfl) ⟨1671956, by rfl⟩ : syracuseStep 2229275 = 3343913) B3343913
theorem B16909883 : Blo 924580 16909883 := bstep (se 1 (by rfl) ⟨12682412, by rfl⟩ : syracuseStep 16909883 = 25364825) B25364825
theorem B4458739 : Blo 924580 4458739 := bstep (se 1 (by rfl) ⟨3344054, by rfl⟩ : syracuseStep 4458739 = 6688109) B6688109
theorem B1447033 : Blo 924580 1447033 := bstep (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) B1085275
theorem B33495545 : Blo 924580 33495545 := bstep (se 2 (by rfl) ⟨12560829, by rfl⟩ : syracuseStep 33495545 = 25121659) B25121659
theorem B70491505 : Blo 924580 70491505 := bstep (se 2 (by rfl) ⟨26434314, by rfl⟩ : syracuseStep 70491505 = 52868629) B52868629
theorem B925467 : Blo 924580 925467 := bstep (se 1 (by rfl) ⟨694100, by rfl⟩ : syracuseStep 925467 = 1388201) B1388201
theorem B8889335 : Blo 924580 8889335 := bstep (se 1 (by rfl) ⟨6667001, by rfl⟩ : syracuseStep 8889335 = 13334003) B13334003
theorem B7021727 : Blo 924580 7021727 := bstep (se 1 (by rfl) ⟨5266295, by rfl⟩ : syracuseStep 7021727 = 10532591) B10532591
theorem B927871 : Blo 924580 927871 := bstep (se 1 (by rfl) ⟨695903, by rfl⟩ : syracuseStep 927871 = 1391807) B1391807
theorem B928191 : Blo 924580 928191 := bstep (se 1 (by rfl) ⟨696143, by rfl⟩ : syracuseStep 928191 = 1392287) B1392287
theorem B928423 : Blo 924580 928423 := bstep (se 1 (by rfl) ⟨696317, by rfl⟩ : syracuseStep 928423 = 1392635) B1392635
theorem B11873465 : Blo 924580 11873465 := bstep (se 2 (by rfl) ⟨4452549, by rfl⟩ : syracuseStep 11873465 = 8905099) B8905099
theorem B90222497 : Blo 924580 90222497 := bstep (se 2 (by rfl) ⟨33833436, by rfl⟩ : syracuseStep 90222497 = 67666873) B67666873
theorem B1389689 : Blo 924580 1389689 := bstep (se 2 (by rfl) ⟨521133, by rfl⟩ : syracuseStep 1389689 = 1042267) B1042267
theorem B3126599 : Blo 924580 3126599 := bstep (se 1 (by rfl) ⟨2344949, by rfl⟩ : syracuseStep 3126599 = 4689899) B4689899
theorem B3126761 : Blo 924580 3126761 := bstep (se 2 (by rfl) ⟨1172535, by rfl⟩ : syracuseStep 3126761 = 2345071) B2345071
theorem B7912019 : Blo 924580 7912019 := bstep (se 1 (by rfl) ⟨5934014, by rfl⟩ : syracuseStep 7912019 = 11868029) B11868029
theorem B1391207 : Blo 924580 1391207 := bstep (se 1 (by rfl) ⟨1043405, by rfl⟩ : syracuseStep 1391207 = 2086811) B2086811
theorem B1392107 : Blo 924580 1392107 := bstep (se 1 (by rfl) ⟨1044080, by rfl⟩ : syracuseStep 1392107 = 2088161) B2088161
theorem B2342783 : Blo 924580 2342783 := bstep (se 1 (by rfl) ⟨1757087, by rfl⟩ : syracuseStep 2342783 = 3514175) B3514175
theorem B1392575 : Blo 924580 1392575 := bstep (se 1 (by rfl) ⟨1044431, by rfl⟩ : syracuseStep 1392575 = 2088863) B2088863
theorem B2081321 : Blo 924580 2081321 := bstep (se 2 (by rfl) ⟨780495, by rfl⟩ : syracuseStep 2081321 = 1560991) B1560991
theorem B2082383 : Blo 924580 2082383 := bstep (se 1 (by rfl) ⟨1561787, by rfl⟩ : syracuseStep 2082383 = 3123575) B3123575
theorem B3131135 : Blo 924580 3131135 := bstep (se 1 (by rfl) ⟨2348351, by rfl⟩ : syracuseStep 3131135 = 4696703) B4696703
theorem B2639641 : Blo 924580 2639641 := bstep (se 2 (by rfl) ⟨989865, by rfl⟩ : syracuseStep 2639641 = 1979731) B1979731
theorem B8439677 : Blo 924580 8439677 := bstep (se 3 (by rfl) ⟨1582439, by rfl⟩ : syracuseStep 8439677 = 3164879) B3164879
theorem B5359769 : Blo 924580 5359769 := bstep (se 2 (by rfl) ⟨2009913, by rfl⟩ : syracuseStep 5359769 = 4019827) B4019827
theorem B2083175 : Blo 924580 2083175 := bstep (se 1 (by rfl) ⟨1562381, by rfl⟩ : syracuseStep 2083175 = 3124763) B3124763
theorem B10570499 : Blo 924580 10570499 := bstep (se 1 (by rfl) ⟨7927874, by rfl⟩ : syracuseStep 10570499 = 15855749) B15855749
theorem B3132863 : Blo 924580 3132863 := bstep (se 1 (by rfl) ⟨2349647, by rfl⟩ : syracuseStep 3132863 = 4699295) B4699295
theorem B2084975 : Blo 924580 2084975 := bstep (se 1 (by rfl) ⟨1563731, by rfl⟩ : syracuseStep 2084975 = 3127463) B3127463
theorem B11260255 : Blo 924580 11260255 := bstep (se 1 (by rfl) ⟨8445191, by rfl⟩ : syracuseStep 11260255 = 16890383) B16890383
theorem B2085695 : Blo 924580 2085695 := bstep (se 1 (by rfl) ⟨1564271, by rfl⟩ : syracuseStep 2085695 = 3128543) B3128543
theorem B2087945 : Blo 924580 2087945 := bstep (se 2 (by rfl) ⟨782979, by rfl⟩ : syracuseStep 2087945 = 1565959) B1565959
theorem B1563887 : Blo 924580 1563887 := bstep (se 1 (by rfl) ⟨1172915, by rfl⟩ : syracuseStep 1563887 = 2345831) B2345831
theorem B2973287 : Blo 924580 2973287 := bstep (se 1 (by rfl) ⟨2229965, by rfl⟩ : syracuseStep 2973287 = 4459931) B4459931
theorem B1171199 : Blo 924580 1171199 := bstep (se 1 (by rfl) ⟨878399, by rfl⟩ : syracuseStep 1171199 = 1756799) B1756799
theorem B11886587 : Blo 924580 11886587 := bstep (se 1 (by rfl) ⟨8914940, by rfl⟩ : syracuseStep 11886587 = 17829881) B17829881
theorem B4448591 : Blo 924580 4448591 := bstep (se 1 (by rfl) ⟨3336443, by rfl⟩ : syracuseStep 4448591 = 6672887) B6672887
theorem B1040863 : Blo 924580 1040863 := bstep (se 1 (by rfl) ⟨780647, by rfl⟩ : syracuseStep 1040863 = 1561295) B1561295
theorem B10544255 : Blo 924580 10544255 := bstep (se 1 (by rfl) ⟨7908191, by rfl⟩ : syracuseStep 10544255 = 15816383) B15816383
theorem B125265791 : Blo 924580 125265791 := bstep (se 1 (by rfl) ⟨93949343, by rfl⟩ : syracuseStep 125265791 = 187898687) B187898687
theorem B3337769 : Blo 924580 3337769 := bstep (se 2 (by rfl) ⟨1251663, by rfl⟩ : syracuseStep 3337769 = 2503327) B2503327
theorem B1175087 : Blo 924580 1175087 := bstep (se 1 (by rfl) ⟨881315, by rfl⟩ : syracuseStep 1175087 = 1762631) B1762631
theorem B7139423 : Blo 924580 7139423 := bstep (se 1 (by rfl) ⟨5354567, by rfl⟩ : syracuseStep 7139423 = 10709135) B10709135
theorem B10682027 : Blo 924580 10682027 := bstep (se 1 (by rfl) ⟨8011520, by rfl⟩ : syracuseStep 10682027 = 16023041) B16023041
theorem B11273255 : Blo 924580 11273255 := bstep (se 1 (by rfl) ⟨8454941, by rfl⟩ : syracuseStep 11273255 = 16909883) B16909883
theorem B3573179 : Blo 924580 3573179 := bstep (se 1 (by rfl) ⟨2679884, by rfl⟩ : syracuseStep 3573179 = 5359769) B5359769
theorem B7046999 : Blo 924580 7046999 := bstep (se 1 (by rfl) ⟨5285249, by rfl⟩ : syracuseStep 7046999 = 10570499) B10570499
theorem B15013673 : Blo 924580 15013673 := bstep (se 2 (by rfl) ⟨5630127, by rfl⟩ : syracuseStep 15013673 = 11260255) B11260255
theorem B4759615 : Blo 924580 4759615 := bstep (se 1 (by rfl) ⟨3569711, by rfl⟩ : syracuseStep 4759615 = 7139423) B7139423
theorem B926459 : Blo 924580 926459 := bstep (se 1 (by rfl) ⟨694844, by rfl⟩ : syracuseStep 926459 = 1389689) B1389689
theorem B927471 : Blo 924580 927471 := bstep (se 1 (by rfl) ⟨695603, by rfl⟩ : syracuseStep 927471 = 1391207) B1391207
theorem B93988673 : Blo 924580 93988673 := bstep (se 2 (by rfl) ⟨35245752, by rfl⟩ : syracuseStep 93988673 = 70491505) B70491505
theorem B3123197 : Blo 924580 3123197 := bstep (se 3 (by rfl) ⟨585599, by rfl⟩ : syracuseStep 3123197 = 1171199) B1171199
theorem B928071 : Blo 924580 928071 := bstep (se 1 (by rfl) ⟨696053, by rfl⟩ : syracuseStep 928071 = 1392107) B1392107
theorem B7121351 : Blo 924580 7121351 := bstep (se 1 (by rfl) ⟨5341013, by rfl⟩ : syracuseStep 7121351 = 10682027) B10682027
theorem B928383 : Blo 924580 928383 := bstep (se 1 (by rfl) ⟨696287, by rfl⟩ : syracuseStep 928383 = 1392575) B1392575
theorem B1387547 : Blo 924580 1387547 := bstep (se 1 (by rfl) ⟨1040660, by rfl⟩ : syracuseStep 1387547 = 2081321) B2081321
theorem B1387817 : Blo 924580 1387817 := bstep (se 2 (by rfl) ⟨520431, by rfl⟩ : syracuseStep 1387817 = 1040863) B1040863
theorem B1486183 : Blo 924580 1486183 := bstep (se 1 (by rfl) ⟨1114637, by rfl⟩ : syracuseStep 1486183 = 2229275) B2229275
theorem B1388255 : Blo 924580 1388255 := bstep (se 1 (by rfl) ⟨1041191, by rfl⟩ : syracuseStep 1388255 = 2082383) B2082383
theorem B1388783 : Blo 924580 1388783 := bstep (se 1 (by rfl) ⟨1041587, by rfl⟩ : syracuseStep 1388783 = 2083175) B2083175
theorem B3519521 : Blo 924580 3519521 := bstep (se 2 (by rfl) ⟨1319820, by rfl⟩ : syracuseStep 3519521 = 2639641) B2639641
theorem B1389983 : Blo 924580 1389983 := bstep (se 1 (by rfl) ⟨1042487, by rfl⟩ : syracuseStep 1389983 = 2084975) B2084975
theorem B5944985 : Blo 924580 5944985 := bstep (se 2 (by rfl) ⟨2229369, by rfl⟩ : syracuseStep 5944985 = 4458739) B4458739
theorem B1390463 : Blo 924580 1390463 := bstep (se 1 (by rfl) ⟨1042847, by rfl⟩ : syracuseStep 1390463 = 2085695) B2085695
theorem B22330363 : Blo 924580 22330363 := bstep (se 1 (by rfl) ⟨16747772, by rfl⟩ : syracuseStep 22330363 = 33495545) B33495545
theorem B1391963 : Blo 924580 1391963 := bstep (se 1 (by rfl) ⟨1043972, by rfl⟩ : syracuseStep 1391963 = 2087945) B2087945
theorem B2965727 : Blo 924580 2965727 := bstep (se 1 (by rfl) ⟨2224295, by rfl⟩ : syracuseStep 2965727 = 4448591) B4448591
theorem B7029503 : Blo 924580 7029503 := bstep (se 1 (by rfl) ⟨5272127, by rfl⟩ : syracuseStep 7029503 = 10544255) B10544255
theorem B83510527 : Blo 924580 83510527 := bstep (se 1 (by rfl) ⟨62632895, by rfl⟩ : syracuseStep 83510527 = 125265791) B125265791
theorem B7915643 : Blo 924580 7915643 := bstep (se 1 (by rfl) ⟨5936732, by rfl⟩ : syracuseStep 7915643 = 11873465) B11873465
theorem B60148331 : Blo 924580 60148331 := bstep (se 1 (by rfl) ⟨45111248, by rfl⟩ : syracuseStep 60148331 = 90222497) B90222497
theorem B2084399 : Blo 924580 2084399 := bstep (se 1 (by rfl) ⟨1563299, by rfl⟩ : syracuseStep 2084399 = 3126599) B3126599
theorem B2084507 : Blo 924580 2084507 := bstep (se 1 (by rfl) ⟨1563380, by rfl⟩ : syracuseStep 2084507 = 3126761) B3126761
theorem B3133565 : Blo 924580 3133565 := bstep (se 3 (by rfl) ⟨587543, by rfl⟩ : syracuseStep 3133565 = 1175087) B1175087
theorem B1561855 : Blo 924580 1561855 := bstep (se 1 (by rfl) ⟨1171391, by rfl⟩ : syracuseStep 1561855 = 2342783) B2342783
theorem B2087423 : Blo 924580 2087423 := bstep (se 1 (by rfl) ⟨1565567, by rfl⟩ : syracuseStep 2087423 = 3131135) B3131135
theorem B5626451 : Blo 924580 5626451 := bstep (se 1 (by rfl) ⟨4219838, by rfl⟩ : syracuseStep 5626451 = 8439677) B8439677
theorem B2088575 : Blo 924580 2088575 := bstep (se 1 (by rfl) ⟨1566431, by rfl⟩ : syracuseStep 2088575 = 3132863) B3132863
theorem B1042591 : Blo 924580 1042591 := bstep (se 1 (by rfl) ⟨781943, by rfl⟩ : syracuseStep 1042591 = 1563887) B1563887
theorem B7924391 : Blo 924580 7924391 := bstep (se 1 (by rfl) ⟨5943293, by rfl⟩ : syracuseStep 7924391 = 11886587) B11886587
theorem B5926223 : Blo 924580 5926223 := bstep (se 1 (by rfl) ⟨4444667, by rfl⟩ : syracuseStep 5926223 = 8889335) B8889335
theorem B4681151 : Blo 924580 4681151 := bstep (se 1 (by rfl) ⟨3510863, by rfl⟩ : syracuseStep 4681151 = 7021727) B7021727
theorem B1929377 : Blo 924580 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B2225179 : Blo 924580 2225179 := bstep (se 1 (by rfl) ⟨1668884, by rfl⟩ : syracuseStep 2225179 = 3337769) B3337769
theorem B7928765 : Blo 924580 7928765 := bstep (se 3 (by rfl) ⟨1486643, by rfl⟩ : syracuseStep 7928765 = 2973287) B2973287
theorem B5274679 : Blo 924580 5274679 := bstep (se 1 (by rfl) ⟨3956009, by rfl⟩ : syracuseStep 5274679 = 7912019) B7912019
theorem B5145005 : Blo 924580 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B4686335 : Blo 924580 4686335 := bstep (se 1 (by rfl) ⟨3514751, by rfl⟩ : syracuseStep 4686335 = 7029503) B7029503
theorem B5277095 : Blo 924580 5277095 := bstep (se 1 (by rfl) ⟨3957821, by rfl⟩ : syracuseStep 5277095 = 7915643) B7915643
theorem B111347369 : Blo 924580 111347369 := bstep (se 2 (by rfl) ⟨41755263, by rfl⟩ : syracuseStep 111347369 = 83510527) B83510527
theorem B62659115 : Blo 924580 62659115 := bstep (se 1 (by rfl) ⟨46994336, by rfl⟩ : syracuseStep 62659115 = 93988673) B93988673
theorem B5282927 : Blo 924580 5282927 := bstep (se 1 (by rfl) ⟨3962195, by rfl⟩ : syracuseStep 5282927 = 7924391) B7924391
theorem B925031 : Blo 924580 925031 := bstep (se 1 (by rfl) ⟨693773, by rfl⟩ : syracuseStep 925031 = 1387547) B1387547
theorem B925211 : Blo 924580 925211 := bstep (se 1 (by rfl) ⟨693908, by rfl⟩ : syracuseStep 925211 = 1387817) B1387817
theorem B3120767 : Blo 924580 3120767 := bstep (se 1 (by rfl) ⟨2340575, by rfl⟩ : syracuseStep 3120767 = 4681151) B4681151
theorem B925503 : Blo 924580 925503 := bstep (se 1 (by rfl) ⟨694127, by rfl⟩ : syracuseStep 925503 = 1388255) B1388255
theorem B925855 : Blo 924580 925855 := bstep (se 1 (by rfl) ⟨694391, by rfl⟩ : syracuseStep 925855 = 1388783) B1388783
theorem B15803261 : Blo 924580 15803261 := bstep (se 3 (by rfl) ⟨2963111, by rfl⟩ : syracuseStep 15803261 = 5926223) B5926223
theorem B926655 : Blo 924580 926655 := bstep (se 1 (by rfl) ⟨694991, by rfl⟩ : syracuseStep 926655 = 1389983) B1389983
theorem B926975 : Blo 924580 926975 := bstep (se 1 (by rfl) ⟨695231, by rfl⟩ : syracuseStep 926975 = 1390463) B1390463
theorem B5285843 : Blo 924580 5285843 := bstep (se 1 (by rfl) ⟨3964382, by rfl⟩ : syracuseStep 5285843 = 7928765) B7928765
theorem B927975 : Blo 924580 927975 := bstep (se 1 (by rfl) ⟨695981, by rfl⟩ : syracuseStep 927975 = 1391963) B1391963
theorem B1977151 : Blo 924580 1977151 := bstep (se 1 (by rfl) ⟨1482863, by rfl⟩ : syracuseStep 1977151 = 2965727) B2965727
theorem B7515503 : Blo 924580 7515503 := bstep (se 1 (by rfl) ⟨5636627, by rfl⟩ : syracuseStep 7515503 = 11273255) B11273255
theorem B4697999 : Blo 924580 4697999 := bstep (se 1 (by rfl) ⟨3523499, by rfl⟩ : syracuseStep 4697999 = 7046999) B7046999
theorem B1389599 : Blo 924580 1389599 := bstep (se 1 (by rfl) ⟨1042199, by rfl⟩ : syracuseStep 1389599 = 2084399) B2084399
theorem B1389671 : Blo 924580 1389671 := bstep (se 1 (by rfl) ⟨1042253, by rfl⟩ : syracuseStep 1389671 = 2084507) B2084507
theorem B1390121 : Blo 924580 1390121 := bstep (se 2 (by rfl) ⟨521295, by rfl⟩ : syracuseStep 1390121 = 1042591) B1042591
theorem B10009115 : Blo 924580 10009115 := bstep (se 1 (by rfl) ⟨7506836, by rfl⟩ : syracuseStep 10009115 = 15013673) B15013673
theorem B1391615 : Blo 924580 1391615 := bstep (se 1 (by rfl) ⟨1043711, by rfl⟩ : syracuseStep 1391615 = 2087423) B2087423
theorem B3750967 : Blo 924580 3750967 := bstep (se 1 (by rfl) ⟨2813225, by rfl⟩ : syracuseStep 3750967 = 5626451) B5626451
theorem B1981577 : Blo 924580 1981577 := bstep (se 2 (by rfl) ⟨743091, by rfl⟩ : syracuseStep 1981577 = 1486183) B1486183
theorem B1392383 : Blo 924580 1392383 := bstep (se 1 (by rfl) ⟨1044287, by rfl⟩ : syracuseStep 1392383 = 2088575) B2088575
theorem B2082131 : Blo 924580 2082131 := bstep (se 1 (by rfl) ⟨1561598, by rfl⟩ : syracuseStep 2082131 = 3123197) B3123197
theorem B2966905 : Blo 924580 2966905 := bstep (se 2 (by rfl) ⟨1112589, by rfl⟩ : syracuseStep 2966905 = 2225179) B2225179
theorem B2082473 : Blo 924580 2082473 := bstep (se 2 (by rfl) ⟨780927, by rfl⟩ : syracuseStep 2082473 = 1561855) B1561855
theorem B2346347 : Blo 924580 2346347 := bstep (se 1 (by rfl) ⟨1759760, by rfl⟩ : syracuseStep 2346347 = 3519521) B3519521
theorem B29773817 : Blo 924580 29773817 := bstep (se 2 (by rfl) ⟨11165181, by rfl⟩ : syracuseStep 29773817 = 22330363) B22330363
theorem B7032905 : Blo 924580 7032905 := bstep (se 2 (by rfl) ⟨2637339, by rfl⟩ : syracuseStep 7032905 = 5274679) B5274679
theorem B6346153 : Blo 924580 6346153 := bstep (se 2 (by rfl) ⟨2379807, by rfl⟩ : syracuseStep 6346153 = 4759615) B4759615
theorem B2382119 : Blo 924580 2382119 := bstep (se 1 (by rfl) ⟨1786589, by rfl⟩ : syracuseStep 2382119 = 3573179) B3573179
theorem B40098887 : Blo 924580 40098887 := bstep (se 1 (by rfl) ⟨30074165, by rfl⟩ : syracuseStep 40098887 = 60148331) B60148331
theorem B2089043 : Blo 924580 2089043 := bstep (se 1 (by rfl) ⟨1566782, by rfl⟩ : syracuseStep 2089043 = 3133565) B3133565
theorem B4747567 : Blo 924580 4747567 := bstep (se 1 (by rfl) ⟨3560675, by rfl⟩ : syracuseStep 4747567 = 7121351) B7121351
theorem B3963323 : Blo 924580 3963323 := bstep (se 1 (by rfl) ⟨2972492, by rfl⟩ : syracuseStep 3963323 = 5944985) B5944985
theorem B4688603 : Blo 924580 4688603 := bstep (se 1 (by rfl) ⟨3516452, by rfl⟩ : syracuseStep 4688603 = 7032905) B7032905
theorem B6330089 : Blo 924580 6330089 := bstep (se 2 (by rfl) ⟨2373783, by rfl⟩ : syracuseStep 6330089 = 4747567) B4747567
theorem B926399 : Blo 924580 926399 := bstep (se 1 (by rfl) ⟨694799, by rfl⟩ : syracuseStep 926399 = 1389599) B1389599
theorem B926447 : Blo 924580 926447 := bstep (se 1 (by rfl) ⟨694835, by rfl⟩ : syracuseStep 926447 = 1389671) B1389671
theorem B926747 : Blo 924580 926747 := bstep (se 1 (by rfl) ⟨695060, by rfl⟩ : syracuseStep 926747 = 1390121) B1390121
theorem B927743 : Blo 924580 927743 := bstep (se 1 (by rfl) ⟨695807, by rfl⟩ : syracuseStep 927743 = 1391615) B1391615
theorem B1321051 : Blo 924580 1321051 := bstep (se 1 (by rfl) ⟨990788, by rfl⟩ : syracuseStep 1321051 = 1981577) B1981577
theorem B928255 : Blo 924580 928255 := bstep (se 1 (by rfl) ⟨696191, by rfl⟩ : syracuseStep 928255 = 1392383) B1392383
theorem B3124223 : Blo 924580 3124223 := bstep (se 1 (by rfl) ⟨2343167, by rfl⟩ : syracuseStep 3124223 = 4686335) B4686335
theorem B1388087 : Blo 924580 1388087 := bstep (se 1 (by rfl) ⟨1041065, by rfl⟩ : syracuseStep 1388087 = 2082131) B2082131
theorem B3518063 : Blo 924580 3518063 := bstep (se 1 (by rfl) ⟨2638547, by rfl⟩ : syracuseStep 3518063 = 5277095) B5277095
theorem B1388315 : Blo 924580 1388315 := bstep (se 1 (by rfl) ⟨1041236, by rfl⟩ : syracuseStep 1388315 = 2082473) B2082473
theorem B74231579 : Blo 924580 74231579 := bstep (se 1 (by rfl) ⟨55673684, by rfl⟩ : syracuseStep 74231579 = 111347369) B111347369
theorem B2636201 : Blo 924580 2636201 := bstep (se 2 (by rfl) ⟨988575, by rfl⟩ : syracuseStep 2636201 = 1977151) B1977151
theorem B1588079 : Blo 924580 1588079 := bstep (se 1 (by rfl) ⟨1191059, by rfl⟩ : syracuseStep 1588079 = 2382119) B2382119
theorem B3521951 : Blo 924580 3521951 := bstep (se 1 (by rfl) ⟨2641463, by rfl⟩ : syracuseStep 3521951 = 5282927) B5282927
theorem B2080511 : Blo 924580 2080511 := bstep (se 1 (by rfl) ⟨1560383, by rfl⟩ : syracuseStep 2080511 = 3120767) B3120767
theorem B1392695 : Blo 924580 1392695 := bstep (se 1 (by rfl) ⟨1044521, by rfl⟩ : syracuseStep 1392695 = 2089043) B2089043
theorem B20005157 : Blo 924580 20005157 := bstep (se 4 (by rfl) ⟨1875483, by rfl⟩ : syracuseStep 20005157 = 3750967) B3750967
theorem B10535507 : Blo 924580 10535507 := bstep (se 1 (by rfl) ⟨7901630, by rfl⟩ : syracuseStep 10535507 = 15803261) B15803261
theorem B3523895 : Blo 924580 3523895 := bstep (se 1 (by rfl) ⟨2642921, by rfl⟩ : syracuseStep 3523895 = 5285843) B5285843
theorem B3131999 : Blo 924580 3131999 := bstep (se 1 (by rfl) ⟨2348999, by rfl⟩ : syracuseStep 3131999 = 4697999) B4697999
theorem B2642215 : Blo 924580 2642215 := bstep (se 1 (by rfl) ⟨1981661, by rfl⟩ : syracuseStep 2642215 = 3963323) B3963323
theorem B6672743 : Blo 924580 6672743 := bstep (se 1 (by rfl) ⟨5004557, by rfl⟩ : syracuseStep 6672743 = 10009115) B10009115
theorem B13720013 : Blo 924580 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B3955873 : Blo 924580 3955873 := bstep (se 2 (by rfl) ⟨1483452, by rfl⟩ : syracuseStep 3955873 = 2966905) B2966905
theorem B1564231 : Blo 924580 1564231 := bstep (se 1 (by rfl) ⟨1173173, by rfl⟩ : syracuseStep 1564231 = 2346347) B2346347
theorem B19849211 : Blo 924580 19849211 := bstep (se 1 (by rfl) ⟨14886908, by rfl⟩ : syracuseStep 19849211 = 29773817) B29773817
theorem B41772743 : Blo 924580 41772743 := bstep (se 1 (by rfl) ⟨31329557, by rfl⟩ : syracuseStep 41772743 = 62659115) B62659115
theorem B26732591 : Blo 924580 26732591 := bstep (se 1 (by rfl) ⟨20049443, by rfl⟩ : syracuseStep 26732591 = 40098887) B40098887
theorem B33846149 : Blo 924580 33846149 := bstep (se 4 (by rfl) ⟨3173076, by rfl⟩ : syracuseStep 33846149 = 6346153) B6346153
theorem B5010335 : Blo 924580 5010335 := bstep (se 1 (by rfl) ⟨3757751, by rfl⟩ : syracuseStep 5010335 = 7515503) B7515503
theorem B13336771 : Blo 924580 13336771 := bstep (se 1 (by rfl) ⟨10002578, by rfl⟩ : syracuseStep 13336771 = 20005157) B20005157
theorem B9146675 : Blo 924580 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B16880237 : Blo 924580 16880237 := bstep (se 3 (by rfl) ⟨3165044, by rfl⟩ : syracuseStep 16880237 = 6330089) B6330089
theorem B925391 : Blo 924580 925391 := bstep (se 1 (by rfl) ⟨694043, by rfl⟩ : syracuseStep 925391 = 1388087) B1388087
theorem B925543 : Blo 924580 925543 := bstep (se 1 (by rfl) ⟨694157, by rfl⟩ : syracuseStep 925543 = 1388315) B1388315
theorem B1058719 : Blo 924580 1058719 := bstep (se 1 (by rfl) ⟨794039, by rfl⟩ : syracuseStep 1058719 = 1588079) B1588079
theorem B1387007 : Blo 924580 1387007 := bstep (se 1 (by rfl) ⟨1040255, by rfl⟩ : syracuseStep 1387007 = 2080511) B2080511
theorem B928463 : Blo 924580 928463 := bstep (se 1 (by rfl) ⟨696347, by rfl⟩ : syracuseStep 928463 = 1392695) B1392695
theorem B7023671 : Blo 924580 7023671 := bstep (se 1 (by rfl) ⟨5267753, by rfl⟩ : syracuseStep 7023671 = 10535507) B10535507
theorem B3125735 : Blo 924580 3125735 := bstep (se 1 (by rfl) ⟨2344301, by rfl⟩ : syracuseStep 3125735 = 4688603) B4688603
theorem B3522953 : Blo 924580 3522953 := bstep (se 2 (by rfl) ⟨1321107, by rfl⟩ : syracuseStep 3522953 = 2642215) B2642215
theorem B2082815 : Blo 924580 2082815 := bstep (se 1 (by rfl) ⟨1562111, by rfl⟩ : syracuseStep 2082815 = 3124223) B3124223
theorem B2345375 : Blo 924580 2345375 := bstep (se 1 (by rfl) ⟨1759031, by rfl⟩ : syracuseStep 2345375 = 3518063) B3518063
theorem B22564099 : Blo 924580 22564099 := bstep (se 1 (by rfl) ⟨16923074, by rfl⟩ : syracuseStep 22564099 = 33846149) B33846149
theorem B1757467 : Blo 924580 1757467 := bstep (se 1 (by rfl) ⟨1318100, by rfl⟩ : syracuseStep 1757467 = 2636201) B2636201
theorem B2085641 : Blo 924580 2085641 := bstep (se 2 (by rfl) ⟨782115, by rfl⟩ : syracuseStep 2085641 = 1564231) B1564231
theorem B2347967 : Blo 924580 2347967 := bstep (se 1 (by rfl) ⟨1760975, by rfl⟩ : syracuseStep 2347967 = 3521951) B3521951
theorem B2349263 : Blo 924580 2349263 := bstep (se 1 (by rfl) ⟨1761947, by rfl⟩ : syracuseStep 2349263 = 3523895) B3523895
theorem B2087999 : Blo 924580 2087999 := bstep (se 1 (by rfl) ⟨1565999, by rfl⟩ : syracuseStep 2087999 = 3131999) B3131999
theorem B1761401 : Blo 924580 1761401 := bstep (se 2 (by rfl) ⟨660525, by rfl⟩ : syracuseStep 1761401 = 1321051) B1321051
theorem B4448495 : Blo 924580 4448495 := bstep (se 1 (by rfl) ⟨3336371, by rfl⟩ : syracuseStep 4448495 = 6672743) B6672743
theorem B13232807 : Blo 924580 13232807 := bstep (se 1 (by rfl) ⟨9924605, by rfl⟩ : syracuseStep 13232807 = 19849211) B19849211
theorem B27848495 : Blo 924580 27848495 := bstep (se 1 (by rfl) ⟨20886371, by rfl⟩ : syracuseStep 27848495 = 41772743) B41772743
theorem B17821727 : Blo 924580 17821727 := bstep (se 1 (by rfl) ⟨13366295, by rfl⟩ : syracuseStep 17821727 = 26732591) B26732591
theorem B3340223 : Blo 924580 3340223 := bstep (se 1 (by rfl) ⟨2505167, by rfl⟩ : syracuseStep 3340223 = 5010335) B5010335
theorem B5274497 : Blo 924580 5274497 := bstep (se 2 (by rfl) ⟨1977936, by rfl⟩ : syracuseStep 5274497 = 3955873) B3955873
theorem B197950877 : Blo 924580 197950877 := bstep (se 3 (by rfl) ⟨37115789, by rfl⟩ : syracuseStep 197950877 = 74231579) B74231579
theorem B1411625 : Blo 924580 1411625 := bstep (se 2 (by rfl) ⟨529359, by rfl⟩ : syracuseStep 1411625 = 1058719) B1058719
theorem B6097783 : Blo 924580 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B30085465 : Blo 924580 30085465 := bstep (se 2 (by rfl) ⟨11282049, by rfl⟩ : syracuseStep 30085465 = 22564099) B22564099
theorem B924671 : Blo 924580 924671 := bstep (se 1 (by rfl) ⟨693503, by rfl⟩ : syracuseStep 924671 = 1387007) B1387007
theorem B8821871 : Blo 924580 8821871 := bstep (se 1 (by rfl) ⟨6616403, by rfl⟩ : syracuseStep 8821871 = 13232807) B13232807
theorem B3516331 : Blo 924580 3516331 := bstep (se 1 (by rfl) ⟨2637248, by rfl⟩ : syracuseStep 3516331 = 5274497) B5274497
theorem B74262653 : Blo 924580 74262653 := bstep (se 3 (by rfl) ⟨13924247, by rfl⟩ : syracuseStep 74262653 = 27848495) B27848495
theorem B131967251 : Blo 924580 131967251 := bstep (se 1 (by rfl) ⟨98975438, by rfl⟩ : syracuseStep 131967251 = 197950877) B197950877
theorem B1388543 : Blo 924580 1388543 := bstep (se 1 (by rfl) ⟨1041407, by rfl⟩ : syracuseStep 1388543 = 2082815) B2082815
theorem B11253491 : Blo 924580 11253491 := bstep (se 1 (by rfl) ⟨8440118, by rfl⟩ : syracuseStep 11253491 = 16880237) B16880237
theorem B1390427 : Blo 924580 1390427 := bstep (se 1 (by rfl) ⟨1042820, by rfl⟩ : syracuseStep 1390427 = 2085641) B2085641
theorem B1391999 : Blo 924580 1391999 := bstep (se 1 (by rfl) ⟨1043999, by rfl⟩ : syracuseStep 1391999 = 2087999) B2087999
theorem B2965663 : Blo 924580 2965663 := bstep (se 1 (by rfl) ⟨2224247, by rfl⟩ : syracuseStep 2965663 = 4448495) B4448495
theorem B2343289 : Blo 924580 2343289 := bstep (se 2 (by rfl) ⟨878733, by rfl⟩ : syracuseStep 2343289 = 1757467) B1757467
theorem B11881151 : Blo 924580 11881151 := bstep (se 1 (by rfl) ⟨8910863, by rfl⟩ : syracuseStep 11881151 = 17821727) B17821727
theorem B2083823 : Blo 924580 2083823 := bstep (se 1 (by rfl) ⟨1562867, by rfl⟩ : syracuseStep 2083823 = 3125735) B3125735
theorem B17782361 : Blo 924580 17782361 := bstep (se 2 (by rfl) ⟨6668385, by rfl⟩ : syracuseStep 17782361 = 13336771) B13336771
theorem B2348635 : Blo 924580 2348635 := bstep (se 1 (by rfl) ⟨1761476, by rfl⟩ : syracuseStep 2348635 = 3522953) B3522953
theorem B1563583 : Blo 924580 1563583 := bstep (se 1 (by rfl) ⟨1172687, by rfl⟩ : syracuseStep 1563583 = 2345375) B2345375
theorem B1565311 : Blo 924580 1565311 := bstep (se 1 (by rfl) ⟨1173983, by rfl⟩ : syracuseStep 1565311 = 2347967) B2347967
theorem B1566175 : Blo 924580 1566175 := bstep (se 1 (by rfl) ⟨1174631, by rfl⟩ : syracuseStep 1566175 = 2349263) B2349263
theorem B1174267 : Blo 924580 1174267 := bstep (se 1 (by rfl) ⟨880700, by rfl⟩ : syracuseStep 1174267 = 1761401) B1761401
theorem B4682447 : Blo 924580 4682447 := bstep (se 1 (by rfl) ⟨3511835, by rfl⟩ : syracuseStep 4682447 = 7023671) B7023671
theorem B2226815 : Blo 924580 2226815 := bstep (se 1 (by rfl) ⟨1670111, by rfl⟩ : syracuseStep 2226815 = 3340223) B3340223
theorem B4688441 : Blo 924580 4688441 := bstep (se 2 (by rfl) ⟨1758165, by rfl⟩ : syracuseStep 4688441 = 3516331) B3516331
theorem B8130377 : Blo 924580 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B40113953 : Blo 924580 40113953 := bstep (se 2 (by rfl) ⟨15042732, by rfl⟩ : syracuseStep 40113953 = 30085465) B30085465
theorem B925695 : Blo 924580 925695 := bstep (se 1 (by rfl) ⟨694271, by rfl⟩ : syracuseStep 925695 = 1388543) B1388543
theorem B3121631 : Blo 924580 3121631 := bstep (se 1 (by rfl) ⟨2341223, by rfl⟩ : syracuseStep 3121631 = 4682447) B4682447
theorem B926951 : Blo 924580 926951 := bstep (se 1 (by rfl) ⟨695213, by rfl⟩ : syracuseStep 926951 = 1390427) B1390427
theorem B1484543 : Blo 924580 1484543 := bstep (se 1 (by rfl) ⟨1113407, by rfl⟩ : syracuseStep 1484543 = 2226815) B2226815
theorem B927999 : Blo 924580 927999 := bstep (se 1 (by rfl) ⟨695999, by rfl⟩ : syracuseStep 927999 = 1391999) B1391999
theorem B3124385 : Blo 924580 3124385 := bstep (se 2 (by rfl) ⟨1171644, by rfl⟩ : syracuseStep 3124385 = 2343289) B2343289
theorem B1389215 : Blo 924580 1389215 := bstep (se 1 (by rfl) ⟨1041911, by rfl⟩ : syracuseStep 1389215 = 2083823) B2083823
theorem B5881247 : Blo 924580 5881247 := bstep (se 1 (by rfl) ⟨4410935, by rfl⟩ : syracuseStep 5881247 = 8821871) B8821871
theorem B3131513 : Blo 924580 3131513 := bstep (se 2 (by rfl) ⟨1174317, by rfl⟩ : syracuseStep 3131513 = 2348635) B2348635
theorem B2084777 : Blo 924580 2084777 := bstep (se 2 (by rfl) ⟨781791, by rfl⟩ : syracuseStep 2084777 = 1563583) B1563583
theorem B3954217 : Blo 924580 3954217 := bstep (se 2 (by rfl) ⟨1482831, by rfl⟩ : syracuseStep 3954217 = 2965663) B2965663
theorem B2087081 : Blo 924580 2087081 := bstep (se 2 (by rfl) ⟨782655, by rfl⟩ : syracuseStep 2087081 = 1565311) B1565311
theorem B7920767 : Blo 924580 7920767 := bstep (se 1 (by rfl) ⟨5940575, by rfl⟩ : syracuseStep 7920767 = 11881151) B11881151
theorem B2088233 : Blo 924580 2088233 := bstep (se 2 (by rfl) ⟨783087, by rfl⟩ : syracuseStep 2088233 = 1566175) B1566175
theorem B1565689 : Blo 924580 1565689 := bstep (se 2 (by rfl) ⟨587133, by rfl⟩ : syracuseStep 1565689 = 1174267) B1174267
theorem B11854907 : Blo 924580 11854907 := bstep (se 1 (by rfl) ⟨8891180, by rfl⟩ : syracuseStep 11854907 = 17782361) B17782361
theorem B49508435 : Blo 924580 49508435 := bstep (se 1 (by rfl) ⟨37131326, by rfl⟩ : syracuseStep 49508435 = 74262653) B74262653
theorem B3764333 : Blo 924580 3764333 := bstep (se 3 (by rfl) ⟨705812, by rfl⟩ : syracuseStep 3764333 = 1411625) B1411625
theorem B87978167 : Blo 924580 87978167 := bstep (se 1 (by rfl) ⟨65983625, by rfl⟩ : syracuseStep 87978167 = 131967251) B131967251
theorem B7502327 : Blo 924580 7502327 := bstep (se 1 (by rfl) ⟨5626745, by rfl⟩ : syracuseStep 7502327 = 11253491) B11253491
theorem B132022493 : Blo 924580 132022493 := bstep (se 3 (by rfl) ⟨24754217, by rfl⟩ : syracuseStep 132022493 = 49508435) B49508435
theorem B26742635 : Blo 924580 26742635 := bstep (se 1 (by rfl) ⟨20056976, by rfl⟩ : syracuseStep 26742635 = 40113953) B40113953
theorem B5280511 : Blo 924580 5280511 := bstep (se 1 (by rfl) ⟨3960383, by rfl⟩ : syracuseStep 5280511 = 7920767) B7920767
theorem B7903271 : Blo 924580 7903271 := bstep (se 1 (by rfl) ⟨5927453, by rfl⟩ : syracuseStep 7903271 = 11854907) B11854907
theorem B989695 : Blo 924580 989695 := bstep (se 1 (by rfl) ⟨742271, by rfl⟩ : syracuseStep 989695 = 1484543) B1484543
theorem B926143 : Blo 924580 926143 := bstep (se 1 (by rfl) ⟨694607, by rfl⟩ : syracuseStep 926143 = 1389215) B1389215
theorem B3125627 : Blo 924580 3125627 := bstep (se 1 (by rfl) ⟨2344220, by rfl⟩ : syracuseStep 3125627 = 4688441) B4688441
theorem B5420251 : Blo 924580 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B1389851 : Blo 924580 1389851 := bstep (se 1 (by rfl) ⟨1042388, by rfl⟩ : syracuseStep 1389851 = 2084777) B2084777
theorem B1391387 : Blo 924580 1391387 := bstep (se 1 (by rfl) ⟨1043540, by rfl⟩ : syracuseStep 1391387 = 2087081) B2087081
theorem B1392155 : Blo 924580 1392155 := bstep (se 1 (by rfl) ⟨1044116, by rfl⟩ : syracuseStep 1392155 = 2088233) B2088233
theorem B2081087 : Blo 924580 2081087 := bstep (se 1 (by rfl) ⟨1560815, by rfl⟩ : syracuseStep 2081087 = 3121631) B3121631
theorem B2082923 : Blo 924580 2082923 := bstep (se 1 (by rfl) ⟨1562192, by rfl⟩ : syracuseStep 2082923 = 3124385) B3124385
theorem B2509555 : Blo 924580 2509555 := bstep (se 1 (by rfl) ⟨1882166, by rfl⟩ : syracuseStep 2509555 = 3764333) B3764333
theorem B5001551 : Blo 924580 5001551 := bstep (se 1 (by rfl) ⟨3751163, by rfl⟩ : syracuseStep 5001551 = 7502327) B7502327
theorem B3920831 : Blo 924580 3920831 := bstep (se 1 (by rfl) ⟨2940623, by rfl⟩ : syracuseStep 3920831 = 5881247) B5881247
theorem B2087585 : Blo 924580 2087585 := bstep (se 2 (by rfl) ⟨782844, by rfl⟩ : syracuseStep 2087585 = 1565689) B1565689
theorem B2087675 : Blo 924580 2087675 := bstep (se 1 (by rfl) ⟨1565756, by rfl⟩ : syracuseStep 2087675 = 3131513) B3131513
theorem B5272289 : Blo 924580 5272289 := bstep (se 2 (by rfl) ⟨1977108, by rfl⟩ : syracuseStep 5272289 = 3954217) B3954217
theorem B58652111 : Blo 924580 58652111 := bstep (se 1 (by rfl) ⟨43989083, by rfl⟩ : syracuseStep 58652111 = 87978167) B87978167
theorem B88014995 : Blo 924580 88014995 := bstep (se 1 (by rfl) ⟨66011246, by rfl⟩ : syracuseStep 88014995 = 132022493) B132022493
theorem B17828423 : Blo 924580 17828423 := bstep (se 1 (by rfl) ⟨13371317, by rfl⟩ : syracuseStep 17828423 = 26742635) B26742635
theorem B3346073 : Blo 924580 3346073 := bstep (se 2 (by rfl) ⟨1254777, by rfl⟩ : syracuseStep 3346073 = 2509555) B2509555
theorem B156405629 : Blo 924580 156405629 := bstep (se 3 (by rfl) ⟨29326055, by rfl⟩ : syracuseStep 156405629 = 58652111) B58652111
theorem B3514859 : Blo 924580 3514859 := bstep (se 1 (by rfl) ⟨2636144, by rfl⟩ : syracuseStep 3514859 = 5272289) B5272289
theorem B1319593 : Blo 924580 1319593 := bstep (se 2 (by rfl) ⟨494847, by rfl⟩ : syracuseStep 1319593 = 989695) B989695
theorem B926567 : Blo 924580 926567 := bstep (se 1 (by rfl) ⟨694925, by rfl⟩ : syracuseStep 926567 = 1389851) B1389851
theorem B927591 : Blo 924580 927591 := bstep (se 1 (by rfl) ⟨695693, by rfl⟩ : syracuseStep 927591 = 1391387) B1391387
theorem B928103 : Blo 924580 928103 := bstep (se 1 (by rfl) ⟨696077, by rfl⟩ : syracuseStep 928103 = 1392155) B1392155
theorem B1387391 : Blo 924580 1387391 := bstep (se 1 (by rfl) ⟨1040543, by rfl⟩ : syracuseStep 1387391 = 2081087) B2081087
theorem B1388615 : Blo 924580 1388615 := bstep (se 1 (by rfl) ⟨1041461, by rfl⟩ : syracuseStep 1388615 = 2082923) B2082923
theorem B1391723 : Blo 924580 1391723 := bstep (se 1 (by rfl) ⟨1043792, by rfl⟩ : syracuseStep 1391723 = 2087585) B2087585
theorem B1391783 : Blo 924580 1391783 := bstep (se 1 (by rfl) ⟨1043837, by rfl⟩ : syracuseStep 1391783 = 2087675) B2087675
theorem B7227001 : Blo 924580 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B2083751 : Blo 924580 2083751 := bstep (se 1 (by rfl) ⟨1562813, by rfl⟩ : syracuseStep 2083751 = 3125627) B3125627
theorem B3334367 : Blo 924580 3334367 := bstep (se 1 (by rfl) ⟨2500775, by rfl⟩ : syracuseStep 3334367 = 5001551) B5001551
theorem B2613887 : Blo 924580 2613887 := bstep (se 1 (by rfl) ⟨1960415, by rfl⟩ : syracuseStep 2613887 = 3920831) B3920831
theorem B5268847 : Blo 924580 5268847 := bstep (se 1 (by rfl) ⟨3951635, by rfl⟩ : syracuseStep 5268847 = 7903271) B7903271
theorem B7040681 : Blo 924580 7040681 := bstep (se 2 (by rfl) ⟨2640255, by rfl⟩ : syracuseStep 7040681 = 5280511) B5280511
theorem B2230715 : Blo 924580 2230715 := bstep (se 1 (by rfl) ⟨1673036, by rfl⟩ : syracuseStep 2230715 = 3346073) B3346073
theorem B104270419 : Blo 924580 104270419 := bstep (se 1 (by rfl) ⟨78202814, by rfl⟩ : syracuseStep 104270419 = 156405629) B156405629
theorem B1742591 : Blo 924580 1742591 := bstep (se 1 (by rfl) ⟨1306943, by rfl⟩ : syracuseStep 1742591 = 2613887) B2613887
theorem B924927 : Blo 924580 924927 := bstep (se 1 (by rfl) ⟨693695, by rfl⟩ : syracuseStep 924927 = 1387391) B1387391
theorem B4693787 : Blo 924580 4693787 := bstep (se 1 (by rfl) ⟨3520340, by rfl⟩ : syracuseStep 4693787 = 7040681) B7040681
theorem B925743 : Blo 924580 925743 := bstep (se 1 (by rfl) ⟨694307, by rfl⟩ : syracuseStep 925743 = 1388615) B1388615
theorem B38544005 : Blo 924580 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B927815 : Blo 924580 927815 := bstep (se 1 (by rfl) ⟨695861, by rfl⟩ : syracuseStep 927815 = 1391723) B1391723
theorem B927855 : Blo 924580 927855 := bstep (se 1 (by rfl) ⟨695891, by rfl⟩ : syracuseStep 927855 = 1391783) B1391783
theorem B7025129 : Blo 924580 7025129 := bstep (se 2 (by rfl) ⟨2634423, by rfl⟩ : syracuseStep 7025129 = 5268847) B5268847
theorem B1389167 : Blo 924580 1389167 := bstep (se 1 (by rfl) ⟨1041875, by rfl⟩ : syracuseStep 1389167 = 2083751) B2083751
theorem B2343239 : Blo 924580 2343239 := bstep (se 1 (by rfl) ⟨1757429, by rfl⟩ : syracuseStep 2343239 = 3514859) B3514859
theorem B58676663 : Blo 924580 58676663 := bstep (se 1 (by rfl) ⟨44007497, by rfl⟩ : syracuseStep 58676663 = 88014995) B88014995
theorem B1759457 : Blo 924580 1759457 := bstep (se 2 (by rfl) ⟨659796, by rfl⟩ : syracuseStep 1759457 = 1319593) B1319593
theorem B11885615 : Blo 924580 11885615 := bstep (se 1 (by rfl) ⟨8914211, by rfl⟩ : syracuseStep 11885615 = 17828423) B17828423
theorem B2222911 : Blo 924580 2222911 := bstep (se 1 (by rfl) ⟨1667183, by rfl⟩ : syracuseStep 2222911 = 3334367) B3334367
theorem B25696003 : Blo 924580 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B926111 : Blo 924580 926111 := bstep (se 1 (by rfl) ⟨694583, by rfl⟩ : syracuseStep 926111 = 1389167) B1389167
theorem B1487143 : Blo 924580 1487143 := bstep (se 1 (by rfl) ⟨1115357, by rfl⟩ : syracuseStep 1487143 = 2230715) B2230715
theorem B2963881 : Blo 924580 2963881 := bstep (se 2 (by rfl) ⟨1111455, by rfl⟩ : syracuseStep 2963881 = 2222911) B2222911
theorem B3129191 : Blo 924580 3129191 := bstep (se 1 (by rfl) ⟨2346893, by rfl⟩ : syracuseStep 3129191 = 4693787) B4693787
theorem B1562159 : Blo 924580 1562159 := bstep (se 1 (by rfl) ⟨1171619, by rfl⟩ : syracuseStep 1562159 = 2343239) B2343239
theorem B139027225 : Blo 924580 139027225 := bstep (se 2 (by rfl) ⟨52135209, by rfl⟩ : syracuseStep 139027225 = 104270419) B104270419
theorem B39117775 : Blo 924580 39117775 := bstep (se 1 (by rfl) ⟨29338331, by rfl⟩ : syracuseStep 39117775 = 58676663) B58676663
theorem B1172971 : Blo 924580 1172971 := bstep (se 1 (by rfl) ⟨879728, by rfl⟩ : syracuseStep 1172971 = 1759457) B1759457
theorem B4646909 : Blo 924580 4646909 := bstep (se 3 (by rfl) ⟨871295, by rfl⟩ : syracuseStep 4646909 = 1742591) B1742591
theorem B7923743 : Blo 924580 7923743 := bstep (se 1 (by rfl) ⟨5942807, by rfl⟩ : syracuseStep 7923743 = 11885615) B11885615
theorem B4683419 : Blo 924580 4683419 := bstep (se 1 (by rfl) ⟨3512564, by rfl⟩ : syracuseStep 4683419 = 7025129) B7025129
theorem B185369633 : Blo 924580 185369633 := bstep (se 2 (by rfl) ⟨69513612, by rfl⟩ : syracuseStep 185369633 = 139027225) B139027225
theorem B7931429 : Blo 924580 7931429 := bstep (se 4 (by rfl) ⟨743571, by rfl⟩ : syracuseStep 7931429 = 1487143) B1487143
theorem B5282495 : Blo 924580 5282495 := bstep (se 1 (by rfl) ⟨3961871, by rfl⟩ : syracuseStep 5282495 = 7923743) B7923743
theorem B3122279 : Blo 924580 3122279 := bstep (se 1 (by rfl) ⟨2341709, by rfl⟩ : syracuseStep 3122279 = 4683419) B4683419
theorem B3097939 : Blo 924580 3097939 := bstep (se 1 (by rfl) ⟨2323454, by rfl⟩ : syracuseStep 3097939 = 4646909) B4646909
theorem B34261337 : Blo 924580 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B3951841 : Blo 924580 3951841 := bstep (se 2 (by rfl) ⟨1481940, by rfl⟩ : syracuseStep 3951841 = 2963881) B2963881
theorem B2086127 : Blo 924580 2086127 := bstep (se 1 (by rfl) ⟨1564595, by rfl⟩ : syracuseStep 2086127 = 3129191) B3129191
theorem B52157033 : Blo 924580 52157033 := bstep (se 2 (by rfl) ⟨19558887, by rfl⟩ : syracuseStep 52157033 = 39117775) B39117775
theorem B1563961 : Blo 924580 1563961 := bstep (se 2 (by rfl) ⟨586485, by rfl⟩ : syracuseStep 1563961 = 1172971) B1172971
theorem B1041439 : Blo 924580 1041439 := bstep (se 1 (by rfl) ⟨781079, by rfl⟩ : syracuseStep 1041439 = 1562159) B1562159
theorem B4130585 : Blo 924580 4130585 := bstep (se 2 (by rfl) ⟨1548969, by rfl⟩ : syracuseStep 4130585 = 3097939) B3097939
theorem B34771355 : Blo 924580 34771355 := bstep (se 1 (by rfl) ⟨26078516, by rfl⟩ : syracuseStep 34771355 = 52157033) B52157033
theorem B91363565 : Blo 924580 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B123579755 : Blo 924580 123579755 := bstep (se 1 (by rfl) ⟨92684816, by rfl⟩ : syracuseStep 123579755 = 185369633) B185369633
theorem B5287619 : Blo 924580 5287619 := bstep (se 1 (by rfl) ⟨3965714, by rfl⟩ : syracuseStep 5287619 = 7931429) B7931429
theorem B1388585 : Blo 924580 1388585 := bstep (se 2 (by rfl) ⟨520719, by rfl⟩ : syracuseStep 1388585 = 1041439) B1041439
theorem B1390751 : Blo 924580 1390751 := bstep (se 1 (by rfl) ⟨1043063, by rfl⟩ : syracuseStep 1390751 = 2086127) B2086127
theorem B3521663 : Blo 924580 3521663 := bstep (se 1 (by rfl) ⟨2641247, by rfl⟩ : syracuseStep 3521663 = 5282495) B5282495
theorem B2081519 : Blo 924580 2081519 := bstep (se 1 (by rfl) ⟨1561139, by rfl⟩ : syracuseStep 2081519 = 3122279) B3122279
theorem B2085281 : Blo 924580 2085281 := bstep (se 2 (by rfl) ⟨781980, by rfl⟩ : syracuseStep 2085281 = 1563961) B1563961
theorem B5269121 : Blo 924580 5269121 := bstep (se 2 (by rfl) ⟨1975920, by rfl⟩ : syracuseStep 5269121 = 3951841) B3951841
theorem B2753723 : Blo 924580 2753723 := bstep (se 1 (by rfl) ⟨2065292, by rfl⟩ : syracuseStep 2753723 = 4130585) B4130585
theorem B3512747 : Blo 924580 3512747 := bstep (se 1 (by rfl) ⟨2634560, by rfl⟩ : syracuseStep 3512747 = 5269121) B5269121
theorem B82386503 : Blo 924580 82386503 := bstep (se 1 (by rfl) ⟨61789877, by rfl⟩ : syracuseStep 82386503 = 123579755) B123579755
theorem B925723 : Blo 924580 925723 := bstep (se 1 (by rfl) ⟨694292, by rfl⟩ : syracuseStep 925723 = 1388585) B1388585
theorem B927167 : Blo 924580 927167 := bstep (se 1 (by rfl) ⟨695375, by rfl⟩ : syracuseStep 927167 = 1390751) B1390751
theorem B1387679 : Blo 924580 1387679 := bstep (se 1 (by rfl) ⟨1040759, by rfl⟩ : syracuseStep 1387679 = 2081519) B2081519
theorem B23180903 : Blo 924580 23180903 := bstep (se 1 (by rfl) ⟨17385677, by rfl⟩ : syracuseStep 23180903 = 34771355) B34771355
theorem B1390187 : Blo 924580 1390187 := bstep (se 1 (by rfl) ⟨1042640, by rfl⟩ : syracuseStep 1390187 = 2085281) B2085281
theorem B3525079 : Blo 924580 3525079 := bstep (se 1 (by rfl) ⟨2643809, by rfl⟩ : syracuseStep 3525079 = 5287619) B5287619
theorem B2347775 : Blo 924580 2347775 := bstep (se 1 (by rfl) ⟨1760831, by rfl⟩ : syracuseStep 2347775 = 3521663) B3521663
theorem B60909043 : Blo 924580 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B7343261 : Blo 924580 7343261 := bstep (se 3 (by rfl) ⟨1376861, by rfl⟩ : syracuseStep 7343261 = 2753723) B2753723
theorem B54924335 : Blo 924580 54924335 := bstep (se 1 (by rfl) ⟨41193251, by rfl⟩ : syracuseStep 54924335 = 82386503) B82386503
theorem B925119 : Blo 924580 925119 := bstep (se 1 (by rfl) ⟨693839, by rfl⟩ : syracuseStep 925119 = 1387679) B1387679
theorem B926791 : Blo 924580 926791 := bstep (se 1 (by rfl) ⟨695093, by rfl⟩ : syracuseStep 926791 = 1390187) B1390187
theorem B81212057 : Blo 924580 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B4700105 : Blo 924580 4700105 := bstep (se 2 (by rfl) ⟨1762539, by rfl⟩ : syracuseStep 4700105 = 3525079) B3525079
theorem B2341831 : Blo 924580 2341831 := bstep (se 1 (by rfl) ⟨1756373, by rfl⟩ : syracuseStep 2341831 = 3512747) B3512747
theorem B15453935 : Blo 924580 15453935 := bstep (se 1 (by rfl) ⟨11590451, by rfl⟩ : syracuseStep 15453935 = 23180903) B23180903
theorem B1565183 : Blo 924580 1565183 := bstep (se 1 (by rfl) ⟨1173887, by rfl⟩ : syracuseStep 1565183 = 2347775) B2347775
theorem B54141371 : Blo 924580 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B3122441 : Blo 924580 3122441 := bstep (se 2 (by rfl) ⟨1170915, by rfl⟩ : syracuseStep 3122441 = 2341831) B2341831
theorem B4895507 : Blo 924580 4895507 := bstep (se 1 (by rfl) ⟨3671630, by rfl⟩ : syracuseStep 4895507 = 7343261) B7343261
theorem B10302623 : Blo 924580 10302623 := bstep (se 1 (by rfl) ⟨7726967, by rfl⟩ : syracuseStep 10302623 = 15453935) B15453935
theorem B36616223 : Blo 924580 36616223 := bstep (se 1 (by rfl) ⟨27462167, by rfl⟩ : syracuseStep 36616223 = 54924335) B54924335
theorem B3133403 : Blo 924580 3133403 := bstep (se 1 (by rfl) ⟨2350052, by rfl⟩ : syracuseStep 3133403 = 4700105) B4700105
theorem B1043455 : Blo 924580 1043455 := bstep (se 1 (by rfl) ⟨782591, by rfl⟩ : syracuseStep 1043455 = 1565183) B1565183
theorem B1391273 : Blo 924580 1391273 := bstep (se 2 (by rfl) ⟨521727, by rfl⟩ : syracuseStep 1391273 = 1043455) B1043455
theorem B36094247 : Blo 924580 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B2081627 : Blo 924580 2081627 := bstep (se 1 (by rfl) ⟨1561220, by rfl⟩ : syracuseStep 2081627 = 3122441) B3122441
theorem B3263671 : Blo 924580 3263671 := bstep (se 1 (by rfl) ⟨2447753, by rfl⟩ : syracuseStep 3263671 = 4895507) B4895507
theorem B6868415 : Blo 924580 6868415 := bstep (se 1 (by rfl) ⟨5151311, by rfl⟩ : syracuseStep 6868415 = 10302623) B10302623
theorem B2088935 : Blo 924580 2088935 := bstep (se 1 (by rfl) ⟨1566701, by rfl⟩ : syracuseStep 2088935 = 3133403) B3133403
theorem B24410815 : Blo 924580 24410815 := bstep (se 1 (by rfl) ⟨18308111, by rfl⟩ : syracuseStep 24410815 = 36616223) B36616223
theorem B130191013 : Blo 924580 130191013 := bstep (se 4 (by rfl) ⟨12205407, by rfl⟩ : syracuseStep 130191013 = 24410815) B24410815
theorem B17406245 : Blo 924580 17406245 := bstep (se 4 (by rfl) ⟨1631835, by rfl⟩ : syracuseStep 17406245 = 3263671) B3263671
theorem B927515 : Blo 924580 927515 := bstep (se 1 (by rfl) ⟨695636, by rfl⟩ : syracuseStep 927515 = 1391273) B1391273
theorem B24062831 : Blo 924580 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B1387751 : Blo 924580 1387751 := bstep (se 1 (by rfl) ⟨1040813, by rfl⟩ : syracuseStep 1387751 = 2081627) B2081627
theorem B1392623 : Blo 924580 1392623 := bstep (se 1 (by rfl) ⟨1044467, by rfl⟩ : syracuseStep 1392623 = 2088935) B2088935
theorem B18315773 : Blo 924580 18315773 := bstep (se 3 (by rfl) ⟨3434207, by rfl⟩ : syracuseStep 18315773 = 6868415) B6868415
theorem B11604163 : Blo 924580 11604163 := bstep (se 1 (by rfl) ⟨8703122, by rfl⟩ : syracuseStep 11604163 = 17406245) B17406245
theorem B925167 : Blo 924580 925167 := bstep (se 1 (by rfl) ⟨693875, by rfl⟩ : syracuseStep 925167 = 1387751) B1387751
theorem B928415 : Blo 924580 928415 := bstep (se 1 (by rfl) ⟨696311, by rfl⟩ : syracuseStep 928415 = 1392623) B1392623
theorem B173588017 : Blo 924580 173588017 := bstep (se 2 (by rfl) ⟨65095506, by rfl⟩ : syracuseStep 173588017 = 130191013) B130191013
theorem B16041887 : Blo 924580 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B12210515 : Blo 924580 12210515 := bstep (se 1 (by rfl) ⟨9157886, by rfl⟩ : syracuseStep 12210515 = 18315773) B18315773
theorem B15472217 : Blo 924580 15472217 := bstep (se 2 (by rfl) ⟨5802081, by rfl⟩ : syracuseStep 15472217 = 11604163) B11604163
theorem B231450689 : Blo 924580 231450689 := bstep (se 2 (by rfl) ⟨86794008, by rfl⟩ : syracuseStep 231450689 = 173588017) B173588017
theorem B10694591 : Blo 924580 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B8140343 : Blo 924580 8140343 := bstep (se 1 (by rfl) ⟨6105257, by rfl⟩ : syracuseStep 8140343 = 12210515) B12210515
theorem B7129727 : Blo 924580 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B10314811 : Blo 924580 10314811 := bstep (se 1 (by rfl) ⟨7736108, by rfl⟩ : syracuseStep 10314811 = 15472217) B15472217
theorem B86830325 : Blo 924580 86830325 := bstep (se 5 (by rfl) ⟨4070171, by rfl⟩ : syracuseStep 86830325 = 8140343) B8140343
theorem B154300459 : Blo 924580 154300459 := bstep (se 1 (by rfl) ⟨115725344, by rfl⟩ : syracuseStep 154300459 = 231450689) B231450689
theorem B4753151 : Blo 924580 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B205733945 : Blo 924580 205733945 := bstep (se 2 (by rfl) ⟨77150229, by rfl⟩ : syracuseStep 205733945 = 154300459) B154300459
theorem B57886883 : Blo 924580 57886883 := bstep (se 1 (by rfl) ⟨43415162, by rfl⟩ : syracuseStep 57886883 = 86830325) B86830325
theorem B13753081 : Blo 924580 13753081 := bstep (se 2 (by rfl) ⟨5157405, by rfl⟩ : syracuseStep 13753081 = 10314811) B10314811
theorem B18337441 : Blo 924580 18337441 := bstep (se 2 (by rfl) ⟨6876540, by rfl⟩ : syracuseStep 18337441 = 13753081) B13753081
theorem B137155963 : Blo 924580 137155963 := bstep (se 1 (by rfl) ⟨102866972, by rfl⟩ : syracuseStep 137155963 = 205733945) B205733945
theorem B3168767 : Blo 924580 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B38591255 : Blo 924580 38591255 := bstep (se 1 (by rfl) ⟨28943441, by rfl⟩ : syracuseStep 38591255 = 57886883) B57886883
theorem B25727503 : Blo 924580 25727503 := bstep (se 1 (by rfl) ⟨19295627, by rfl⟩ : syracuseStep 25727503 = 38591255) B38591255
theorem B24449921 : Blo 924580 24449921 := bstep (se 2 (by rfl) ⟨9168720, by rfl⟩ : syracuseStep 24449921 = 18337441) B18337441
theorem B8450045 : Blo 924580 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B182874617 : Blo 924580 182874617 := bstep (se 2 (by rfl) ⟨68577981, by rfl⟩ : syracuseStep 182874617 = 137155963) B137155963
theorem B16299947 : Blo 924580 16299947 := bstep (se 1 (by rfl) ⟨12224960, by rfl⟩ : syracuseStep 16299947 = 24449921) B24449921
theorem B121916411 : Blo 924580 121916411 := bstep (se 1 (by rfl) ⟨91437308, by rfl⟩ : syracuseStep 121916411 = 182874617) B182874617
theorem B34303337 : Blo 924580 34303337 := bstep (se 2 (by rfl) ⟨12863751, by rfl⟩ : syracuseStep 34303337 = 25727503) B25727503
theorem B5633363 : Blo 924580 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B81277607 : Blo 924580 81277607 := bstep (se 1 (by rfl) ⟨60958205, by rfl⟩ : syracuseStep 81277607 = 121916411) B121916411
theorem B3755575 : Blo 924580 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B10866631 : Blo 924580 10866631 := bstep (se 1 (by rfl) ⟨8149973, by rfl⟩ : syracuseStep 10866631 = 16299947) B16299947
theorem B22868891 : Blo 924580 22868891 := bstep (se 1 (by rfl) ⟨17151668, by rfl⟩ : syracuseStep 22868891 = 34303337) B34303337
theorem B14488841 : Blo 924580 14488841 := bstep (se 2 (by rfl) ⟨5433315, by rfl⟩ : syracuseStep 14488841 = 10866631) B10866631
theorem B15245927 : Blo 924580 15245927 := bstep (se 1 (by rfl) ⟨11434445, by rfl⟩ : syracuseStep 15245927 = 22868891) B22868891
theorem B54185071 : Blo 924580 54185071 := bstep (se 1 (by rfl) ⟨40638803, by rfl⟩ : syracuseStep 54185071 = 81277607) B81277607
theorem B5007433 : Blo 924580 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B38636909 : Blo 924580 38636909 := bstep (se 3 (by rfl) ⟨7244420, by rfl⟩ : syracuseStep 38636909 = 14488841) B14488841
theorem B10163951 : Blo 924580 10163951 := bstep (se 1 (by rfl) ⟨7622963, by rfl⟩ : syracuseStep 10163951 = 15245927) B15245927
theorem B6676577 : Blo 924580 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B72246761 : Blo 924580 72246761 := bstep (se 2 (by rfl) ⟨27092535, by rfl⟩ : syracuseStep 72246761 = 54185071) B54185071
theorem B25757939 : Blo 924580 25757939 := bstep (se 1 (by rfl) ⟨19318454, by rfl⟩ : syracuseStep 25757939 = 38636909) B38636909
theorem B6775967 : Blo 924580 6775967 := bstep (se 1 (by rfl) ⟨5081975, by rfl⟩ : syracuseStep 6775967 = 10163951) B10163951
theorem B4451051 : Blo 924580 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B48164507 : Blo 924580 48164507 := bstep (se 1 (by rfl) ⟨36123380, by rfl⟩ : syracuseStep 48164507 = 72246761) B72246761
theorem B17171959 : Blo 924580 17171959 := bstep (se 1 (by rfl) ⟨12878969, by rfl⟩ : syracuseStep 17171959 = 25757939) B25757939
theorem B18069245 : Blo 924580 18069245 := bstep (se 3 (by rfl) ⟨3387983, by rfl⟩ : syracuseStep 18069245 = 6775967) B6775967
theorem B2967367 : Blo 924580 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B32109671 : Blo 924580 32109671 := bstep (se 1 (by rfl) ⟨24082253, by rfl⟩ : syracuseStep 32109671 = 48164507) B48164507
theorem B21406447 : Blo 924580 21406447 := bstep (se 1 (by rfl) ⟨16054835, by rfl⟩ : syracuseStep 21406447 = 32109671) B32109671
theorem B12046163 : Blo 924580 12046163 := bstep (se 1 (by rfl) ⟨9034622, by rfl⟩ : syracuseStep 12046163 = 18069245) B18069245
theorem B22895945 : Blo 924580 22895945 := bstep (se 2 (by rfl) ⟨8585979, by rfl⟩ : syracuseStep 22895945 = 17171959) B17171959
theorem B3956489 : Blo 924580 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B28541929 : Blo 924580 28541929 := bstep (se 2 (by rfl) ⟨10703223, by rfl⟩ : syracuseStep 28541929 = 21406447) B21406447
theorem B32123101 : Blo 924580 32123101 := bstep (se 3 (by rfl) ⟨6023081, by rfl⟩ : syracuseStep 32123101 = 12046163) B12046163
theorem B2637659 : Blo 924580 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B15263963 : Blo 924580 15263963 := bstep (se 1 (by rfl) ⟨11447972, by rfl⟩ : syracuseStep 15263963 = 22895945) B22895945
theorem B42830801 : Blo 924580 42830801 := bstep (se 2 (by rfl) ⟨16061550, by rfl⟩ : syracuseStep 42830801 = 32123101) B32123101
theorem B38055905 : Blo 924580 38055905 := bstep (se 2 (by rfl) ⟨14270964, by rfl⟩ : syracuseStep 38055905 = 28541929) B28541929
theorem B10175975 : Blo 924580 10175975 := bstep (se 1 (by rfl) ⟨7631981, by rfl⟩ : syracuseStep 10175975 = 15263963) B15263963
theorem B1758439 : Blo 924580 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B6783983 : Blo 924580 6783983 := bstep (se 1 (by rfl) ⟨5087987, by rfl⟩ : syracuseStep 6783983 = 10175975) B10175975
theorem B25370603 : Blo 924580 25370603 := bstep (se 1 (by rfl) ⟨19027952, by rfl⟩ : syracuseStep 25370603 = 38055905) B38055905
theorem B28553867 : Blo 924580 28553867 := bstep (se 1 (by rfl) ⟨21415400, by rfl⟩ : syracuseStep 28553867 = 42830801) B42830801
theorem B2344585 : Blo 924580 2344585 := bstep (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) B1758439
theorem B4522655 : Blo 924580 4522655 := bstep (se 1 (by rfl) ⟨3391991, by rfl⟩ : syracuseStep 4522655 = 6783983) B6783983
theorem B16913735 : Blo 924580 16913735 := bstep (se 1 (by rfl) ⟨12685301, by rfl⟩ : syracuseStep 16913735 = 25370603) B25370603
theorem B3126113 : Blo 924580 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B19035911 : Blo 924580 19035911 := bstep (se 1 (by rfl) ⟨14276933, by rfl⟩ : syracuseStep 19035911 = 28553867) B28553867
theorem B3015103 : Blo 924580 3015103 := bstep (se 1 (by rfl) ⟨2261327, by rfl⟩ : syracuseStep 3015103 = 4522655) B4522655
theorem B11275823 : Blo 924580 11275823 := bstep (se 1 (by rfl) ⟨8456867, by rfl⟩ : syracuseStep 11275823 = 16913735) B16913735
theorem B12690607 : Blo 924580 12690607 := bstep (se 1 (by rfl) ⟨9517955, by rfl⟩ : syracuseStep 12690607 = 19035911) B19035911
theorem B2084075 : Blo 924580 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B16920809 : Blo 924580 16920809 := bstep (se 2 (by rfl) ⟨6345303, by rfl⟩ : syracuseStep 16920809 = 12690607) B12690607
theorem B1389383 : Blo 924580 1389383 := bstep (se 1 (by rfl) ⟨1042037, by rfl⟩ : syracuseStep 1389383 = 2084075) B2084075
theorem B7517215 : Blo 924580 7517215 := bstep (se 1 (by rfl) ⟨5637911, by rfl⟩ : syracuseStep 7517215 = 11275823) B11275823
theorem B4020137 : Blo 924580 4020137 := bstep (se 2 (by rfl) ⟨1507551, by rfl⟩ : syracuseStep 4020137 = 3015103) B3015103
theorem B11280539 : Blo 924580 11280539 := bstep (se 1 (by rfl) ⟨8460404, by rfl⟩ : syracuseStep 11280539 = 16920809) B16920809
theorem B926255 : Blo 924580 926255 := bstep (se 1 (by rfl) ⟨694691, by rfl⟩ : syracuseStep 926255 = 1389383) B1389383
theorem B2680091 : Blo 924580 2680091 := bstep (se 1 (by rfl) ⟨2010068, by rfl⟩ : syracuseStep 2680091 = 4020137) B4020137
theorem B10022953 : Blo 924580 10022953 := bstep (se 2 (by rfl) ⟨3758607, by rfl⟩ : syracuseStep 10022953 = 7517215) B7517215
theorem B7520359 : Blo 924580 7520359 := bstep (se 1 (by rfl) ⟨5640269, by rfl⟩ : syracuseStep 7520359 = 11280539) B11280539
theorem B1786727 : Blo 924580 1786727 := bstep (se 1 (by rfl) ⟨1340045, by rfl⟩ : syracuseStep 1786727 = 2680091) B2680091
theorem B13363937 : Blo 924580 13363937 := bstep (se 2 (by rfl) ⟨5011476, by rfl⟩ : syracuseStep 13363937 = 10022953) B10022953
theorem B10027145 : Blo 924580 10027145 := bstep (se 2 (by rfl) ⟨3760179, by rfl⟩ : syracuseStep 10027145 = 7520359) B7520359
theorem B1191151 : Blo 924580 1191151 := bstep (se 1 (by rfl) ⟨893363, by rfl⟩ : syracuseStep 1191151 = 1786727) B1786727
theorem B8909291 : Blo 924580 8909291 := bstep (se 1 (by rfl) ⟨6681968, by rfl⟩ : syracuseStep 8909291 = 13363937) B13363937
theorem B6684763 : Blo 924580 6684763 := bstep (se 1 (by rfl) ⟨5013572, by rfl⟩ : syracuseStep 6684763 = 10027145) B10027145
theorem B5939527 : Blo 924580 5939527 := bstep (se 1 (by rfl) ⟨4454645, by rfl⟩ : syracuseStep 5939527 = 8909291) B8909291
theorem B6352805 : Blo 924580 6352805 := bstep (se 4 (by rfl) ⟨595575, by rfl⟩ : syracuseStep 6352805 = 1191151) B1191151
theorem B8913017 : Blo 924580 8913017 := bstep (se 2 (by rfl) ⟨3342381, by rfl⟩ : syracuseStep 8913017 = 6684763) B6684763
theorem B4235203 : Blo 924580 4235203 := bstep (se 1 (by rfl) ⟨3176402, by rfl⟩ : syracuseStep 4235203 = 6352805) B6352805
theorem B7919369 : Blo 924580 7919369 := bstep (se 2 (by rfl) ⟨2969763, by rfl⟩ : syracuseStep 7919369 = 5939527) B5939527
theorem B5279579 : Blo 924580 5279579 := bstep (se 1 (by rfl) ⟨3959684, by rfl⟩ : syracuseStep 5279579 = 7919369) B7919369
theorem B5646937 : Blo 924580 5646937 := bstep (se 2 (by rfl) ⟨2117601, by rfl⟩ : syracuseStep 5646937 = 4235203) B4235203
theorem B5942011 : Blo 924580 5942011 := bstep (se 1 (by rfl) ⟨4456508, by rfl⟩ : syracuseStep 5942011 = 8913017) B8913017
theorem B3519719 : Blo 924580 3519719 := bstep (se 1 (by rfl) ⟨2639789, by rfl⟩ : syracuseStep 3519719 = 5279579) B5279579
theorem B7529249 : Blo 924580 7529249 := bstep (se 2 (by rfl) ⟨2823468, by rfl⟩ : syracuseStep 7529249 = 5646937) B5646937
theorem B7922681 : Blo 924580 7922681 := bstep (se 2 (by rfl) ⟨2971005, by rfl⟩ : syracuseStep 7922681 = 5942011) B5942011
theorem B5019499 : Blo 924580 5019499 := bstep (se 1 (by rfl) ⟨3764624, by rfl⟩ : syracuseStep 5019499 = 7529249) B7529249
theorem B5281787 : Blo 924580 5281787 := bstep (se 1 (by rfl) ⟨3961340, by rfl⟩ : syracuseStep 5281787 = 7922681) B7922681
theorem B2346479 : Blo 924580 2346479 := bstep (se 1 (by rfl) ⟨1759859, by rfl⟩ : syracuseStep 2346479 = 3519719) B3519719
theorem B6692665 : Blo 924580 6692665 := bstep (se 2 (by rfl) ⟨2509749, by rfl⟩ : syracuseStep 6692665 = 5019499) B5019499
theorem B3521191 : Blo 924580 3521191 := bstep (se 1 (by rfl) ⟨2640893, by rfl⟩ : syracuseStep 3521191 = 5281787) B5281787
theorem B1564319 : Blo 924580 1564319 := bstep (se 1 (by rfl) ⟨1173239, by rfl⟩ : syracuseStep 1564319 = 2346479) B2346479
theorem B4694921 : Blo 924580 4694921 := bstep (se 2 (by rfl) ⟨1760595, by rfl⟩ : syracuseStep 4694921 = 3521191) B3521191
theorem B8923553 : Blo 924580 8923553 := bstep (se 2 (by rfl) ⟨3346332, by rfl⟩ : syracuseStep 8923553 = 6692665) B6692665
theorem B1042879 : Blo 924580 1042879 := bstep (se 1 (by rfl) ⟨782159, by rfl⟩ : syracuseStep 1042879 = 1564319) B1564319
theorem B1390505 : Blo 924580 1390505 := bstep (se 2 (by rfl) ⟨521439, by rfl⟩ : syracuseStep 1390505 = 1042879) B1042879
theorem B3129947 : Blo 924580 3129947 := bstep (se 1 (by rfl) ⟨2347460, by rfl⟩ : syracuseStep 3129947 = 4694921) B4694921
theorem B5949035 : Blo 924580 5949035 := bstep (se 1 (by rfl) ⟨4461776, by rfl⟩ : syracuseStep 5949035 = 8923553) B8923553
theorem B3966023 : Blo 924580 3966023 := bstep (se 1 (by rfl) ⟨2974517, by rfl⟩ : syracuseStep 3966023 = 5949035) B5949035
theorem B927003 : Blo 924580 927003 := bstep (se 1 (by rfl) ⟨695252, by rfl⟩ : syracuseStep 927003 = 1390505) B1390505
theorem B2086631 : Blo 924580 2086631 := bstep (se 1 (by rfl) ⟨1564973, by rfl⟩ : syracuseStep 2086631 = 3129947) B3129947
theorem B1391087 : Blo 924580 1391087 := bstep (se 1 (by rfl) ⟨1043315, by rfl⟩ : syracuseStep 1391087 = 2086631) B2086631
theorem B2644015 : Blo 924580 2644015 := bstep (se 1 (by rfl) ⟨1983011, by rfl⟩ : syracuseStep 2644015 = 3966023) B3966023
theorem B927391 : Blo 924580 927391 := bstep (se 1 (by rfl) ⟨695543, by rfl⟩ : syracuseStep 927391 = 1391087) B1391087
theorem B3525353 : Blo 924580 3525353 := bstep (se 2 (by rfl) ⟨1322007, by rfl⟩ : syracuseStep 3525353 = 2644015) B2644015
theorem B2350235 : Blo 924580 2350235 := bstep (se 1 (by rfl) ⟨1762676, by rfl⟩ : syracuseStep 2350235 = 3525353) B3525353
theorem B1566823 : Blo 924580 1566823 := bstep (se 1 (by rfl) ⟨1175117, by rfl⟩ : syracuseStep 1566823 = 2350235) B2350235
theorem B2089097 : Blo 924580 2089097 := bstep (se 2 (by rfl) ⟨783411, by rfl⟩ : syracuseStep 2089097 = 1566823) B1566823
theorem B1392731 : Blo 924580 1392731 := bstep (se 1 (by rfl) ⟨1044548, by rfl⟩ : syracuseStep 1392731 = 2089097) B2089097
theorem B928487 : Blo 924580 928487 := bstep (se 1 (by rfl) ⟨696365, by rfl⟩ : syracuseStep 928487 = 1392731) B1392731

theorem C0 (j : ℕ) (h1 : 231145 ≤ j) (h2 : j ≤ 231844) : Blo 924580 (4 * j + 3) := by
  interval_cases j
  · exact B924583
  · exact B924587
  · exact B924591
  · exact B924595
  · exact B924599
  · exact B924603
  · exact B924607
  · exact B924611
  · exact B924615
  · exact B924619
  · exact B924623
  · exact B924627
  · exact B924631
  · exact B924635
  · exact B924639
  · exact B924643
  · exact B924647
  · exact B924651
  · exact B924655
  · exact B924659
  · exact B924663
  · exact B924667
  · exact B924671
  · exact B924675
  · exact B924679
  · exact B924683
  · exact B924687
  · exact B924691
  · exact B924695
  · exact B924699
  · exact B924703
  · exact B924707
  · exact B924711
  · exact B924715
  · exact B924719
  · exact B924723
  · exact B924727
  · exact B924731
  · exact B924735
  · exact B924739
  · exact B924743
  · exact B924747
  · exact B924751
  · exact B924755
  · exact B924759
  · exact B924763
  · exact B924767
  · exact B924771
  · exact B924775
  · exact B924779
  · exact B924783
  · exact B924787
  · exact B924791
  · exact B924795
  · exact B924799
  · exact B924803
  · exact B924807
  · exact B924811
  · exact B924815
  · exact B924819
  · exact B924823
  · exact B924827
  · exact B924831
  · exact B924835
  · exact B924839
  · exact B924843
  · exact B924847
  · exact B924851
  · exact B924855
  · exact B924859
  · exact B924863
  · exact B924867
  · exact B924871
  · exact B924875
  · exact B924879
  · exact B924883
  · exact B924887
  · exact B924891
  · exact B924895
  · exact B924899
  · exact B924903
  · exact B924907
  · exact B924911
  · exact B924915
  · exact B924919
  · exact B924923
  · exact B924927
  · exact B924931
  · exact B924935
  · exact B924939
  · exact B924943
  · exact B924947
  · exact B924951
  · exact B924955
  · exact B924959
  · exact B924963
  · exact B924967
  · exact B924971
  · exact B924975
  · exact B924979
  · exact B924983
  · exact B924987
  · exact B924991
  · exact B924995
  · exact B924999
  · exact B925003
  · exact B925007
  · exact B925011
  · exact B925015
  · exact B925019
  · exact B925023
  · exact B925027
  · exact B925031
  · exact B925035
  · exact B925039
  · exact B925043
  · exact B925047
  · exact B925051
  · exact B925055
  · exact B925059
  · exact B925063
  · exact B925067
  · exact B925071
  · exact B925075
  · exact B925079
  · exact B925083
  · exact B925087
  · exact B925091
  · exact B925095
  · exact B925099
  · exact B925103
  · exact B925107
  · exact B925111
  · exact B925115
  · exact B925119
  · exact B925123
  · exact B925127
  · exact B925131
  · exact B925135
  · exact B925139
  · exact B925143
  · exact B925147
  · exact B925151
  · exact B925155
  · exact B925159
  · exact B925163
  · exact B925167
  · exact B925171
  · exact B925175
  · exact B925179
  · exact B925183
  · exact B925187
  · exact B925191
  · exact B925195
  · exact B925199
  · exact B925203
  · exact B925207
  · exact B925211
  · exact B925215
  · exact B925219
  · exact B925223
  · exact B925227
  · exact B925231
  · exact B925235
  · exact B925239
  · exact B925243
  · exact B925247
  · exact B925251
  · exact B925255
  · exact B925259
  · exact B925263
  · exact B925267
  · exact B925271
  · exact B925275
  · exact B925279
  · exact B925283
  · exact B925287
  · exact B925291
  · exact B925295
  · exact B925299
  · exact B925303
  · exact B925307
  · exact B925311
  · exact B925315
  · exact B925319
  · exact B925323
  · exact B925327
  · exact B925331
  · exact B925335
  · exact B925339
  · exact B925343
  · exact B925347
  · exact B925351
  · exact B925355
  · exact B925359
  · exact B925363
  · exact B925367
  · exact B925371
  · exact B925375
  · exact B925379
  · exact B925383
  · exact B925387
  · exact B925391
  · exact B925395
  · exact B925399
  · exact B925403
  · exact B925407
  · exact B925411
  · exact B925415
  · exact B925419
  · exact B925423
  · exact B925427
  · exact B925431
  · exact B925435
  · exact B925439
  · exact B925443
  · exact B925447
  · exact B925451
  · exact B925455
  · exact B925459
  · exact B925463
  · exact B925467
  · exact B925471
  · exact B925475
  · exact B925479
  · exact B925483
  · exact B925487
  · exact B925491
  · exact B925495
  · exact B925499
  · exact B925503
  · exact B925507
  · exact B925511
  · exact B925515
  · exact B925519
  · exact B925523
  · exact B925527
  · exact B925531
  · exact B925535
  · exact B925539
  · exact B925543
  · exact B925547
  · exact B925551
  · exact B925555
  · exact B925559
  · exact B925563
  · exact B925567
  · exact B925571
  · exact B925575
  · exact B925579
  · exact B925583
  · exact B925587
  · exact B925591
  · exact B925595
  · exact B925599
  · exact B925603
  · exact B925607
  · exact B925611
  · exact B925615
  · exact B925619
  · exact B925623
  · exact B925627
  · exact B925631
  · exact B925635
  · exact B925639
  · exact B925643
  · exact B925647
  · exact B925651
  · exact B925655
  · exact B925659
  · exact B925663
  · exact B925667
  · exact B925671
  · exact B925675
  · exact B925679
  · exact B925683
  · exact B925687
  · exact B925691
  · exact B925695
  · exact B925699
  · exact B925703
  · exact B925707
  · exact B925711
  · exact B925715
  · exact B925719
  · exact B925723
  · exact B925727
  · exact B925731
  · exact B925735
  · exact B925739
  · exact B925743
  · exact B925747
  · exact B925751
  · exact B925755
  · exact B925759
  · exact B925763
  · exact B925767
  · exact B925771
  · exact B925775
  · exact B925779
  · exact B925783
  · exact B925787
  · exact B925791
  · exact B925795
  · exact B925799
  · exact B925803
  · exact B925807
  · exact B925811
  · exact B925815
  · exact B925819
  · exact B925823
  · exact B925827
  · exact B925831
  · exact B925835
  · exact B925839
  · exact B925843
  · exact B925847
  · exact B925851
  · exact B925855
  · exact B925859
  · exact B925863
  · exact B925867
  · exact B925871
  · exact B925875
  · exact B925879
  · exact B925883
  · exact B925887
  · exact B925891
  · exact B925895
  · exact B925899
  · exact B925903
  · exact B925907
  · exact B925911
  · exact B925915
  · exact B925919
  · exact B925923
  · exact B925927
  · exact B925931
  · exact B925935
  · exact B925939
  · exact B925943
  · exact B925947
  · exact B925951
  · exact B925955
  · exact B925959
  · exact B925963
  · exact B925967
  · exact B925971
  · exact B925975
  · exact B925979
  · exact B925983
  · exact B925987
  · exact B925991
  · exact B925995
  · exact B925999
  · exact B926003
  · exact B926007
  · exact B926011
  · exact B926015
  · exact B926019
  · exact B926023
  · exact B926027
  · exact B926031
  · exact B926035
  · exact B926039
  · exact B926043
  · exact B926047
  · exact B926051
  · exact B926055
  · exact B926059
  · exact B926063
  · exact B926067
  · exact B926071
  · exact B926075
  · exact B926079
  · exact B926083
  · exact B926087
  · exact B926091
  · exact B926095
  · exact B926099
  · exact B926103
  · exact B926107
  · exact B926111
  · exact B926115
  · exact B926119
  · exact B926123
  · exact B926127
  · exact B926131
  · exact B926135
  · exact B926139
  · exact B926143
  · exact B926147
  · exact B926151
  · exact B926155
  · exact B926159
  · exact B926163
  · exact B926167
  · exact B926171
  · exact B926175
  · exact B926179
  · exact B926183
  · exact B926187
  · exact B926191
  · exact B926195
  · exact B926199
  · exact B926203
  · exact B926207
  · exact B926211
  · exact B926215
  · exact B926219
  · exact B926223
  · exact B926227
  · exact B926231
  · exact B926235
  · exact B926239
  · exact B926243
  · exact B926247
  · exact B926251
  · exact B926255
  · exact B926259
  · exact B926263
  · exact B926267
  · exact B926271
  · exact B926275
  · exact B926279
  · exact B926283
  · exact B926287
  · exact B926291
  · exact B926295
  · exact B926299
  · exact B926303
  · exact B926307
  · exact B926311
  · exact B926315
  · exact B926319
  · exact B926323
  · exact B926327
  · exact B926331
  · exact B926335
  · exact B926339
  · exact B926343
  · exact B926347
  · exact B926351
  · exact B926355
  · exact B926359
  · exact B926363
  · exact B926367
  · exact B926371
  · exact B926375
  · exact B926379
  · exact B926383
  · exact B926387
  · exact B926391
  · exact B926395
  · exact B926399
  · exact B926403
  · exact B926407
  · exact B926411
  · exact B926415
  · exact B926419
  · exact B926423
  · exact B926427
  · exact B926431
  · exact B926435
  · exact B926439
  · exact B926443
  · exact B926447
  · exact B926451
  · exact B926455
  · exact B926459
  · exact B926463
  · exact B926467
  · exact B926471
  · exact B926475
  · exact B926479
  · exact B926483
  · exact B926487
  · exact B926491
  · exact B926495
  · exact B926499
  · exact B926503
  · exact B926507
  · exact B926511
  · exact B926515
  · exact B926519
  · exact B926523
  · exact B926527
  · exact B926531
  · exact B926535
  · exact B926539
  · exact B926543
  · exact B926547
  · exact B926551
  · exact B926555
  · exact B926559
  · exact B926563
  · exact B926567
  · exact B926571
  · exact B926575
  · exact B926579
  · exact B926583
  · exact B926587
  · exact B926591
  · exact B926595
  · exact B926599
  · exact B926603
  · exact B926607
  · exact B926611
  · exact B926615
  · exact B926619
  · exact B926623
  · exact B926627
  · exact B926631
  · exact B926635
  · exact B926639
  · exact B926643
  · exact B926647
  · exact B926651
  · exact B926655
  · exact B926659
  · exact B926663
  · exact B926667
  · exact B926671
  · exact B926675
  · exact B926679
  · exact B926683
  · exact B926687
  · exact B926691
  · exact B926695
  · exact B926699
  · exact B926703
  · exact B926707
  · exact B926711
  · exact B926715
  · exact B926719
  · exact B926723
  · exact B926727
  · exact B926731
  · exact B926735
  · exact B926739
  · exact B926743
  · exact B926747
  · exact B926751
  · exact B926755
  · exact B926759
  · exact B926763
  · exact B926767
  · exact B926771
  · exact B926775
  · exact B926779
  · exact B926783
  · exact B926787
  · exact B926791
  · exact B926795
  · exact B926799
  · exact B926803
  · exact B926807
  · exact B926811
  · exact B926815
  · exact B926819
  · exact B926823
  · exact B926827
  · exact B926831
  · exact B926835
  · exact B926839
  · exact B926843
  · exact B926847
  · exact B926851
  · exact B926855
  · exact B926859
  · exact B926863
  · exact B926867
  · exact B926871
  · exact B926875
  · exact B926879
  · exact B926883
  · exact B926887
  · exact B926891
  · exact B926895
  · exact B926899
  · exact B926903
  · exact B926907
  · exact B926911
  · exact B926915
  · exact B926919
  · exact B926923
  · exact B926927
  · exact B926931
  · exact B926935
  · exact B926939
  · exact B926943
  · exact B926947
  · exact B926951
  · exact B926955
  · exact B926959
  · exact B926963
  · exact B926967
  · exact B926971
  · exact B926975
  · exact B926979
  · exact B926983
  · exact B926987
  · exact B926991
  · exact B926995
  · exact B926999
  · exact B927003
  · exact B927007
  · exact B927011
  · exact B927015
  · exact B927019
  · exact B927023
  · exact B927027
  · exact B927031
  · exact B927035
  · exact B927039
  · exact B927043
  · exact B927047
  · exact B927051
  · exact B927055
  · exact B927059
  · exact B927063
  · exact B927067
  · exact B927071
  · exact B927075
  · exact B927079
  · exact B927083
  · exact B927087
  · exact B927091
  · exact B927095
  · exact B927099
  · exact B927103
  · exact B927107
  · exact B927111
  · exact B927115
  · exact B927119
  · exact B927123
  · exact B927127
  · exact B927131
  · exact B927135
  · exact B927139
  · exact B927143
  · exact B927147
  · exact B927151
  · exact B927155
  · exact B927159
  · exact B927163
  · exact B927167
  · exact B927171
  · exact B927175
  · exact B927179
  · exact B927183
  · exact B927187
  · exact B927191
  · exact B927195
  · exact B927199
  · exact B927203
  · exact B927207
  · exact B927211
  · exact B927215
  · exact B927219
  · exact B927223
  · exact B927227
  · exact B927231
  · exact B927235
  · exact B927239
  · exact B927243
  · exact B927247
  · exact B927251
  · exact B927255
  · exact B927259
  · exact B927263
  · exact B927267
  · exact B927271
  · exact B927275
  · exact B927279
  · exact B927283
  · exact B927287
  · exact B927291
  · exact B927295
  · exact B927299
  · exact B927303
  · exact B927307
  · exact B927311
  · exact B927315
  · exact B927319
  · exact B927323
  · exact B927327
  · exact B927331
  · exact B927335
  · exact B927339
  · exact B927343
  · exact B927347
  · exact B927351
  · exact B927355
  · exact B927359
  · exact B927363
  · exact B927367
  · exact B927371
  · exact B927375
  · exact B927379

theorem C1 (j : ℕ) (h1 : 231845 ≤ j) (h2 : j ≤ 232144) : Blo 924580 (4 * j + 3) := by
  interval_cases j
  · exact B927383
  · exact B927387
  · exact B927391
  · exact B927395
  · exact B927399
  · exact B927403
  · exact B927407
  · exact B927411
  · exact B927415
  · exact B927419
  · exact B927423
  · exact B927427
  · exact B927431
  · exact B927435
  · exact B927439
  · exact B927443
  · exact B927447
  · exact B927451
  · exact B927455
  · exact B927459
  · exact B927463
  · exact B927467
  · exact B927471
  · exact B927475
  · exact B927479
  · exact B927483
  · exact B927487
  · exact B927491
  · exact B927495
  · exact B927499
  · exact B927503
  · exact B927507
  · exact B927511
  · exact B927515
  · exact B927519
  · exact B927523
  · exact B927527
  · exact B927531
  · exact B927535
  · exact B927539
  · exact B927543
  · exact B927547
  · exact B927551
  · exact B927555
  · exact B927559
  · exact B927563
  · exact B927567
  · exact B927571
  · exact B927575
  · exact B927579
  · exact B927583
  · exact B927587
  · exact B927591
  · exact B927595
  · exact B927599
  · exact B927603
  · exact B927607
  · exact B927611
  · exact B927615
  · exact B927619
  · exact B927623
  · exact B927627
  · exact B927631
  · exact B927635
  · exact B927639
  · exact B927643
  · exact B927647
  · exact B927651
  · exact B927655
  · exact B927659
  · exact B927663
  · exact B927667
  · exact B927671
  · exact B927675
  · exact B927679
  · exact B927683
  · exact B927687
  · exact B927691
  · exact B927695
  · exact B927699
  · exact B927703
  · exact B927707
  · exact B927711
  · exact B927715
  · exact B927719
  · exact B927723
  · exact B927727
  · exact B927731
  · exact B927735
  · exact B927739
  · exact B927743
  · exact B927747
  · exact B927751
  · exact B927755
  · exact B927759
  · exact B927763
  · exact B927767
  · exact B927771
  · exact B927775
  · exact B927779
  · exact B927783
  · exact B927787
  · exact B927791
  · exact B927795
  · exact B927799
  · exact B927803
  · exact B927807
  · exact B927811
  · exact B927815
  · exact B927819
  · exact B927823
  · exact B927827
  · exact B927831
  · exact B927835
  · exact B927839
  · exact B927843
  · exact B927847
  · exact B927851
  · exact B927855
  · exact B927859
  · exact B927863
  · exact B927867
  · exact B927871
  · exact B927875
  · exact B927879
  · exact B927883
  · exact B927887
  · exact B927891
  · exact B927895
  · exact B927899
  · exact B927903
  · exact B927907
  · exact B927911
  · exact B927915
  · exact B927919
  · exact B927923
  · exact B927927
  · exact B927931
  · exact B927935
  · exact B927939
  · exact B927943
  · exact B927947
  · exact B927951
  · exact B927955
  · exact B927959
  · exact B927963
  · exact B927967
  · exact B927971
  · exact B927975
  · exact B927979
  · exact B927983
  · exact B927987
  · exact B927991
  · exact B927995
  · exact B927999
  · exact B928003
  · exact B928007
  · exact B928011
  · exact B928015
  · exact B928019
  · exact B928023
  · exact B928027
  · exact B928031
  · exact B928035
  · exact B928039
  · exact B928043
  · exact B928047
  · exact B928051
  · exact B928055
  · exact B928059
  · exact B928063
  · exact B928067
  · exact B928071
  · exact B928075
  · exact B928079
  · exact B928083
  · exact B928087
  · exact B928091
  · exact B928095
  · exact B928099
  · exact B928103
  · exact B928107
  · exact B928111
  · exact B928115
  · exact B928119
  · exact B928123
  · exact B928127
  · exact B928131
  · exact B928135
  · exact B928139
  · exact B928143
  · exact B928147
  · exact B928151
  · exact B928155
  · exact B928159
  · exact B928163
  · exact B928167
  · exact B928171
  · exact B928175
  · exact B928179
  · exact B928183
  · exact B928187
  · exact B928191
  · exact B928195
  · exact B928199
  · exact B928203
  · exact B928207
  · exact B928211
  · exact B928215
  · exact B928219
  · exact B928223
  · exact B928227
  · exact B928231
  · exact B928235
  · exact B928239
  · exact B928243
  · exact B928247
  · exact B928251
  · exact B928255
  · exact B928259
  · exact B928263
  · exact B928267
  · exact B928271
  · exact B928275
  · exact B928279
  · exact B928283
  · exact B928287
  · exact B928291
  · exact B928295
  · exact B928299
  · exact B928303
  · exact B928307
  · exact B928311
  · exact B928315
  · exact B928319
  · exact B928323
  · exact B928327
  · exact B928331
  · exact B928335
  · exact B928339
  · exact B928343
  · exact B928347
  · exact B928351
  · exact B928355
  · exact B928359
  · exact B928363
  · exact B928367
  · exact B928371
  · exact B928375
  · exact B928379
  · exact B928383
  · exact B928387
  · exact B928391
  · exact B928395
  · exact B928399
  · exact B928403
  · exact B928407
  · exact B928411
  · exact B928415
  · exact B928419
  · exact B928423
  · exact B928427
  · exact B928431
  · exact B928435
  · exact B928439
  · exact B928443
  · exact B928447
  · exact B928451
  · exact B928455
  · exact B928459
  · exact B928463
  · exact B928467
  · exact B928471
  · exact B928475
  · exact B928479
  · exact B928483
  · exact B928487
  · exact B928491
  · exact B928495
  · exact B928499
  · exact B928503
  · exact B928507
  · exact B928511
  · exact B928515
  · exact B928519
  · exact B928523
  · exact B928527
  · exact B928531
  · exact B928535
  · exact B928539
  · exact B928543
  · exact B928547
  · exact B928551
  · exact B928555
  · exact B928559
  · exact B928563
  · exact B928567
  · exact B928571
  · exact B928575
  · exact B928579

theorem solution (m : ℕ) (hlo : 924580 ≤ m) (hhi : m ≤ 928580) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 231145 ≤ j := by omega
    have hj2 : j ≤ 232144 := by omega
    have hb : Blo 924580 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 231845 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
